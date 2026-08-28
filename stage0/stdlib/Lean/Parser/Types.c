// Lean compiler output
// Module: Lean.Parser.Types
// Imports: public import Lean.Data.Trie public import Lean.DocString.Extension import Init.Data.String.OrderInstances
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
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_string_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_string_utf8_prev(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_shrink___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_instDecidableEqRaw___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_List_eraseRepsBy___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Parser_getNext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_getNext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_maxPrec;
LEAN_EXPORT lean_object* l_Lean_Parser_argPrec;
LEAN_EXPORT lean_object* l_Lean_Parser_leadPrec;
LEAN_EXPORT lean_object* l_Lean_Parser_minPrec;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value;
static const lean_string_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value;
static const lean_string_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value;
static const lean_string_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3_value;
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_0),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_1),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value_aux_2),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4_value;
static const lean_array_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5_value;
static const lean_string_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6_value;
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_0),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_1),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value_aux_2),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7_value;
static const lean_string_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8_value;
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9_value;
static const lean_string_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10_value;
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_0),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_1),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value_aux_2),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11_value;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13;
static const lean_string_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14_value;
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_0),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_1),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value_aux_2),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__14_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15_value;
static const lean_ctor_object l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9_value),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5_value)}};
static const lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16 = (const lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16_value;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29;
static lean_once_cell_t l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30;
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_endPos__valid___autoParam;
static const lean_string_object l_Lean_Parser_instInhabitedInputContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Parser_instInhabitedInputContext___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedInputContext___closed__0_value;
static lean_once_cell_t l_Lean_Parser_instInhabitedInputContext___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__1;
static lean_once_cell_t l_Lean_Parser_instInhabitedInputContext___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instInhabitedInputContext___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedInputContext;
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk___auto__1;
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_atEnd___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_getNext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_getNext___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0;
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instBEqCacheableParserContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instBEqCacheableParserContext___closed__0 = (const lean_object*)&l_Lean_Parser_instBEqCacheableParserContext___closed__0_value;
static const lean_closure_object l_Lean_Parser_instBEqCacheableParserContext___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_instBEqCacheableParserContext___closed__0_value)} };
static const lean_object* l_Lean_Parser_instBEqCacheableParserContext___closed__1 = (const lean_object*)&l_Lean_Parser_instBEqCacheableParserContext___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instBEqCacheableParserContext = (const lean_object*)&l_Lean_Parser_instBEqCacheableParserContext___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_instCoeParserContextInputContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instCoeParserContextInputContext___closed__0 = (const lean_object*)&l_Lean_Parser_instCoeParserContextInputContext___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instCoeParserContextInputContext = (const lean_object*)&l_Lean_Parser_instCoeParserContextInputContext___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Parser_instInhabitedError_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_instInhabitedInputContext___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_instInhabitedError_default___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedError_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedError_default = (const lean_object*)&l_Lean_Parser_instInhabitedError_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedError = (const lean_object*)&l_Lean_Parser_instInhabitedError_default___closed__0_value;
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instBEqError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instBEqError_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instBEqError___closed__0 = (const lean_object*)&l_Lean_Parser_instBEqError___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instBEqError = (const lean_object*)&l_Lean_Parser_instBEqError___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " or "};
static const lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0 = (const lean_object*)&l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0_value;
static const lean_string_object l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1 = (const lean_object*)&l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object*);
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Error_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Lean_Parser_Error_toString___closed__0 = (const lean_object*)&l_Lean_Parser_Error_toString___closed__0_value;
static const lean_string_object l_Lean_Parser_Error_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "expected "};
static const lean_object* l_Lean_Parser_Error_toString___closed__1 = (const lean_object*)&l_Lean_Parser_Error_toString___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_Error_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Error_toString, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_Error_instToString___closed__0 = (const lean_object*)&l_Lean_Parser_Error_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_Error_instToString = (const lean_object*)&l_Lean_Parser_Error_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instBEqParserCacheKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instBEqParserCacheKey_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instBEqParserCacheKey___closed__0 = (const lean_object*)&l_Lean_Parser_instBEqParserCacheKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instBEqParserCacheKey = (const lean_object*)&l_Lean_Parser_instBEqParserCacheKey___closed__0_value;
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_instHashableParserCacheKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instHashableParserCacheKey___closed__0 = (const lean_object*)&l_Lean_Parser_instHashableParserCacheKey___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instHashableParserCacheKey = (const lean_object*)&l_Lean_Parser_instHashableParserCacheKey___closed__0_value;
static lean_once_cell_t l_Lean_Parser_initCacheForInput___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initCacheForInput___closed__0;
static lean_once_cell_t l_Lean_Parser_initCacheForInput___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initCacheForInput___closed__1;
static lean_once_cell_t l_Lean_Parser_initCacheForInput___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_initCacheForInput___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object*);
static const lean_array_object l_Lean_Parser_SyntaxStack_empty___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_SyntaxStack_empty___closed__0 = (const lean_object*)&l_Lean_Parser_SyntaxStack_empty___closed__0_value;
static const lean_ctor_object l_Lean_Parser_SyntaxStack_empty___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_SyntaxStack_empty___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Parser_SyntaxStack_empty___closed__1 = (const lean_object*)&l_Lean_Parser_SyntaxStack_empty___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_SyntaxStack_empty = (const lean_object*)&l_Lean_Parser_SyntaxStack_empty___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object*);
static const lean_string_object l_Lean_Parser_SyntaxStack_back___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Lean.Parser.Types"};
static const lean_object* l_Lean_Parser_SyntaxStack_back___closed__0 = (const lean_object*)&l_Lean_Parser_SyntaxStack_back___closed__0_value;
static const lean_string_object l_Lean_Parser_SyntaxStack_back___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Parser.SyntaxStack.back"};
static const lean_object* l_Lean_Parser_SyntaxStack_back___closed__1 = (const lean_object*)&l_Lean_Parser_SyntaxStack_back___closed__1_value;
static const lean_string_object l_Lean_Parser_SyntaxStack_back___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "SyntaxStack.back: element is inaccessible"};
static const lean_object* l_Lean_Parser_SyntaxStack_back___closed__2 = (const lean_object*)&l_Lean_Parser_SyntaxStack_back___closed__2_value;
static lean_once_cell_t l_Lean_Parser_SyntaxStack_back___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_SyntaxStack_back___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_SyntaxStack_get_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Parser.SyntaxStack.get!"};
static const lean_object* l_Lean_Parser_SyntaxStack_get_x21___closed__0 = (const lean_object*)&l_Lean_Parser_SyntaxStack_get_x21___closed__0_value;
static const lean_string_object l_Lean_Parser_SyntaxStack_get_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "SyntaxStack.get!: element is inaccessible"};
static const lean_object* l_Lean_Parser_SyntaxStack_get_x21___closed__1 = (const lean_object*)&l_Lean_Parser_SyntaxStack_get_x21___closed__1_value;
static lean_once_cell_t l_Lean_Parser_SyntaxStack_get_x21___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_SyntaxStack_get_x21___closed__2;
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0 = (const lean_object*)&l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax = (const lean_object*)&l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Parser_ParserState_allErrors___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_ParserState_allErrors___closed__0 = (const lean_object*)&l_Lean_Parser_ParserState_allErrors___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_ParserState_mkEOIError___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "unexpected end of input"};
static const lean_object* l_Lean_Parser_ParserState_mkEOIError___closed__0 = (const lean_object*)&l_Lean_Parser_ParserState_mkEOIError___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object*);
static const lean_string_object l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0 = (const lean_object*)&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0_value;
static const lean_string_object l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1 = (const lean_object*)&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1_value;
static const lean_string_object l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2 = (const lean_object*)&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2_value;
static lean_once_cell_t l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instInhabitedParserFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instInhabitedParserFn___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instInhabitedParserFn___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedParserFn___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedParserFn = (const lean_object*)&l_Lean_Parser_instInhabitedParserFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedFirstTokens_default;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedFirstTokens;
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0 = (const lean_object*)&l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0_value;
static const lean_string_object l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1 = (const lean_object*)&l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1_value;
static const lean_string_object l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2 = (const lean_object*)&l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object*);
static const lean_string_object l_Lean_Parser_FirstTokens_toStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "epsilon"};
static const lean_object* l_Lean_Parser_FirstTokens_toStr___closed__0 = (const lean_object*)&l_Lean_Parser_FirstTokens_toStr___closed__0_value;
static const lean_string_object l_Lean_Parser_FirstTokens_toStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "unknown"};
static const lean_object* l_Lean_Parser_FirstTokens_toStr___closed__1 = (const lean_object*)&l_Lean_Parser_FirstTokens_toStr___closed__1_value;
static const lean_string_object l_Lean_Parser_FirstTokens_toStr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_Lean_Parser_FirstTokens_toStr___closed__2 = (const lean_object*)&l_Lean_Parser_FirstTokens_toStr___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_FirstTokens_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_FirstTokens_toStr___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_FirstTokens_instToString___closed__0 = (const lean_object*)&l_Lean_Parser_FirstTokens_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_FirstTokens_instToString = (const lean_object*)&l_Lean_Parser_FirstTokens_instToString___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instInhabitedParserInfo_default___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value;
static const lean_closure_object l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instInhabitedParserInfo_default___closed__1 = (const lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value;
static const lean_ctor_object l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value),((lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Parser_instInhabitedParserInfo_default___closed__2 = (const lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedParserInfo_default = (const lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedParserInfo = (const lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value;
static const lean_ctor_object l_Lean_Parser_instInhabitedParser_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value),((lean_object*)&l_Lean_Parser_instInhabitedParserFn___closed__0_value)}};
static const lean_object* l_Lean_Parser_instInhabitedParser_default___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedParser_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedParser_default = (const lean_object*)&l_Lean_Parser_instInhabitedParser_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instInhabitedParser = (const lean_object*)&l_Lean_Parser_instInhabitedParser_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "withCache"};
static const lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0 = (const lean_object*)&l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value;
static const lean_ctor_object l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_1),((lean_object*)&l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 241, 193, 7, 69, 147, 159, 180)}};
static const lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1 = (const lean_object*)&l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value;
static const lean_string_object l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 542, .m_capacity = 542, .m_length = 541, .m_data = "Run `p` and record result in parser cache for any further invocation with this `parserName`, parser context, and parser state.\n`p` cannot access syntax stack elements pushed before the invocation in order to make caching independent of parser history.\nAs this excludes trailing parsers from being cached, we also reset `lhsPrec`, which is not read but set by leading parsers, to 0\nin order to increase cache hits. Finally, `errorMsg` is also reset to `none` as a leading parser should not be called in the first\nplace if there was an error.\n"};
static const lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2 = (const lean_object*)&l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object*);
static const lean_array_object l_Lean_Parser_ParserFn_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Parser_ParserFn_run___closed__0 = (const lean_object*)&l_Lean_Parser_ParserFn_run___closed__0_value;
static const lean_ctor_object l_Lean_Parser_ParserFn_run___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_ParserFn_run___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_ParserFn_run___closed__1 = (const lean_object*)&l_Lean_Parser_ParserFn_run___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_mkAtom(lean_object* v_info_1_, lean_object* v_val_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3_, 0, v_info_1_);
lean_ctor_set(v___x_3_, 1, v_val_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_mkIdent(lean_object* v_info_4_, lean_object* v_rawVal_5_, lean_object* v_val_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_8_, 0, v_info_4_);
lean_ctor_set(v___x_8_, 1, v_rawVal_5_);
lean_ctor_set(v___x_8_, 2, v_val_6_);
lean_ctor_set(v___x_8_, 3, v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_getNext(lean_object* v_input_9_, lean_object* v_pos_10_){
_start:
{
lean_object* v___x_11_; uint32_t v___x_12_; 
v___x_11_ = lean_string_utf8_next(v_input_9_, v_pos_10_);
v___x_12_ = lean_string_utf8_get(v_input_9_, v___x_11_);
lean_dec(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_getNext___boxed(lean_object* v_input_13_, lean_object* v_pos_14_){
_start:
{
uint32_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_Parser_getNext(v_input_13_, v_pos_14_);
lean_dec(v_pos_14_);
lean_dec_ref(v_input_13_);
v_r_16_ = lean_box_uint32(v_res_15_);
return v_r_16_;
}
}
static lean_object* _init_l_Lean_Parser_maxPrec(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(1024u);
return v___x_17_;
}
}
static lean_object* _init_l_Lean_Parser_argPrec(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(1023u);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_Parser_leadPrec(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(1022u);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Parser_minPrec(void){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(10u);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_21_, lean_object* v_x_22_, lean_object* v_x_23_, lean_object* v_x_24_){
_start:
{
lean_object* v_ks_25_; lean_object* v_vs_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_50_; 
v_ks_25_ = lean_ctor_get(v_x_21_, 0);
v_vs_26_ = lean_ctor_get(v_x_21_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_x_21_);
if (v_isSharedCheck_50_ == 0)
{
v___x_28_ = v_x_21_;
v_isShared_29_ = v_isSharedCheck_50_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_vs_26_);
lean_inc(v_ks_25_);
lean_dec(v_x_21_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_50_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
lean_object* v___x_30_; uint8_t v___x_31_; 
v___x_30_ = lean_array_get_size(v_ks_25_);
v___x_31_ = lean_nat_dec_lt(v_x_22_, v___x_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_35_; 
lean_dec(v_x_22_);
v___x_32_ = lean_array_push(v_ks_25_, v_x_23_);
v___x_33_ = lean_array_push(v_vs_26_, v_x_24_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 1, v___x_33_);
lean_ctor_set(v___x_28_, 0, v___x_32_);
v___x_35_ = v___x_28_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v___x_32_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v___x_33_);
v___x_35_ = v_reuseFailAlloc_36_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
return v___x_35_;
}
}
else
{
lean_object* v_k_x27_37_; uint8_t v___x_38_; 
v_k_x27_37_ = lean_array_fget_borrowed(v_ks_25_, v_x_22_);
v___x_38_ = lean_name_eq(v_x_23_, v_k_x27_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_40_; 
if (v_isShared_29_ == 0)
{
v___x_40_ = v___x_28_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v_ks_25_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v_vs_26_);
v___x_40_ = v_reuseFailAlloc_44_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_add(v_x_22_, v___x_41_);
lean_dec(v_x_22_);
v_x_21_ = v___x_40_;
v_x_22_ = v___x_42_;
goto _start;
}
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_48_; 
v___x_45_ = lean_array_fset(v_ks_25_, v_x_22_, v_x_23_);
v___x_46_ = lean_array_fset(v_vs_26_, v_x_22_, v_x_24_);
lean_dec(v_x_22_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 1, v___x_46_);
lean_ctor_set(v___x_28_, 0, v___x_45_);
v___x_48_ = v___x_28_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_45_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_n_51_, lean_object* v_k_52_, lean_object* v_v_53_){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_unsigned_to_nat(0u);
v___x_55_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_51_, v___x_54_, v_k_52_, v_v_53_);
return v___x_55_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(lean_object* v_x_57_, size_t v_x_58_, size_t v_x_59_, lean_object* v_x_60_, lean_object* v_x_61_){
_start:
{
if (lean_obj_tag(v_x_57_) == 0)
{
lean_object* v_es_62_; size_t v___x_63_; size_t v___x_64_; lean_object* v_j_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_es_62_ = lean_ctor_get(v_x_57_, 0);
v___x_63_ = ((size_t)31ULL);
v___x_64_ = lean_usize_land(v_x_58_, v___x_63_);
v_j_65_ = lean_usize_to_nat(v___x_64_);
v___x_66_ = lean_array_get_size(v_es_62_);
v___x_67_ = lean_nat_dec_lt(v_j_65_, v___x_66_);
if (v___x_67_ == 0)
{
lean_dec(v_j_65_);
lean_dec(v_x_61_);
lean_dec(v_x_60_);
return v_x_57_;
}
else
{
lean_object* v___x_69_; uint8_t v_isShared_70_; uint8_t v_isSharedCheck_106_; 
lean_inc_ref(v_es_62_);
v_isSharedCheck_106_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v_x_57_, 0);
lean_dec(v_unused_107_);
v___x_69_ = v_x_57_;
v_isShared_70_ = v_isSharedCheck_106_;
goto v_resetjp_68_;
}
else
{
lean_dec(v_x_57_);
v___x_69_ = lean_box(0);
v_isShared_70_ = v_isSharedCheck_106_;
goto v_resetjp_68_;
}
v_resetjp_68_:
{
lean_object* v_v_71_; lean_object* v___x_72_; lean_object* v_xs_x27_73_; lean_object* v___y_75_; 
v_v_71_ = lean_array_fget(v_es_62_, v_j_65_);
v___x_72_ = lean_box(0);
v_xs_x27_73_ = lean_array_fset(v_es_62_, v_j_65_, v___x_72_);
switch(lean_obj_tag(v_v_71_))
{
case 0:
{
lean_object* v_key_80_; lean_object* v_val_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_91_; 
v_key_80_ = lean_ctor_get(v_v_71_, 0);
v_val_81_ = lean_ctor_get(v_v_71_, 1);
v_isSharedCheck_91_ = !lean_is_exclusive(v_v_71_);
if (v_isSharedCheck_91_ == 0)
{
v___x_83_ = v_v_71_;
v_isShared_84_ = v_isSharedCheck_91_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_val_81_);
lean_inc(v_key_80_);
lean_dec(v_v_71_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_91_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
uint8_t v___x_85_; 
v___x_85_ = lean_name_eq(v_x_60_, v_key_80_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_del_object(v___x_83_);
v___x_86_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_80_, v_val_81_, v_x_60_, v_x_61_);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
v___y_75_ = v___x_87_;
goto v___jp_74_;
}
else
{
lean_object* v___x_89_; 
lean_dec(v_val_81_);
lean_dec(v_key_80_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v_x_61_);
lean_ctor_set(v___x_83_, 0, v_x_60_);
v___x_89_ = v___x_83_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_x_60_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_x_61_);
v___x_89_ = v_reuseFailAlloc_90_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
v___y_75_ = v___x_89_;
goto v___jp_74_;
}
}
}
}
case 1:
{
lean_object* v_node_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_104_; 
v_node_92_ = lean_ctor_get(v_v_71_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v_v_71_);
if (v_isSharedCheck_104_ == 0)
{
v___x_94_ = v_v_71_;
v_isShared_95_ = v_isSharedCheck_104_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_node_92_);
lean_dec(v_v_71_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_104_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
size_t v___x_96_; size_t v___x_97_; size_t v___x_98_; size_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_102_; 
v___x_96_ = ((size_t)5ULL);
v___x_97_ = lean_usize_shift_right(v_x_58_, v___x_96_);
v___x_98_ = ((size_t)1ULL);
v___x_99_ = lean_usize_add(v_x_59_, v___x_98_);
v___x_100_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_node_92_, v___x_97_, v___x_99_, v_x_60_, v_x_61_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_100_);
v___x_102_ = v___x_94_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v___x_100_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
v___y_75_ = v___x_102_;
goto v___jp_74_;
}
}
}
default: 
{
lean_object* v___x_105_; 
v___x_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_105_, 0, v_x_60_);
lean_ctor_set(v___x_105_, 1, v_x_61_);
v___y_75_ = v___x_105_;
goto v___jp_74_;
}
}
v___jp_74_:
{
lean_object* v___x_76_; lean_object* v___x_78_; 
v___x_76_ = lean_array_fset(v_xs_x27_73_, v_j_65_, v___y_75_);
lean_dec(v_j_65_);
if (v_isShared_70_ == 0)
{
lean_ctor_set(v___x_69_, 0, v___x_76_);
v___x_78_ = v___x_69_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_79_; 
v_reuseFailAlloc_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_79_, 0, v___x_76_);
v___x_78_ = v_reuseFailAlloc_79_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
return v___x_78_;
}
}
}
}
}
else
{
lean_object* v_ks_108_; lean_object* v_vs_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_127_; 
v_ks_108_ = lean_ctor_get(v_x_57_, 0);
v_vs_109_ = lean_ctor_get(v_x_57_, 1);
v_isSharedCheck_127_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_127_ == 0)
{
v___x_111_ = v_x_57_;
v_isShared_112_ = v_isSharedCheck_127_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_vs_109_);
lean_inc(v_ks_108_);
lean_dec(v_x_57_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_127_;
goto v_resetjp_110_;
}
v_resetjp_110_:
{
lean_object* v___x_114_; 
if (v_isShared_112_ == 0)
{
v___x_114_ = v___x_111_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_126_; 
v_reuseFailAlloc_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_126_, 0, v_ks_108_);
lean_ctor_set(v_reuseFailAlloc_126_, 1, v_vs_109_);
v___x_114_ = v_reuseFailAlloc_126_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v_newNode_115_; size_t v___x_116_; uint8_t v___x_117_; 
v_newNode_115_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v___x_114_, v_x_60_, v_x_61_);
v___x_116_ = ((size_t)7ULL);
v___x_117_ = lean_usize_dec_le(v___x_116_, v_x_59_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; 
v___x_118_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_115_);
v___x_119_ = lean_unsigned_to_nat(4u);
v___x_120_ = lean_nat_dec_lt(v___x_118_, v___x_119_);
lean_dec(v___x_118_);
if (v___x_120_ == 0)
{
lean_object* v_ks_121_; lean_object* v_vs_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_ks_121_ = lean_ctor_get(v_newNode_115_, 0);
lean_inc_ref(v_ks_121_);
v_vs_122_ = lean_ctor_get(v_newNode_115_, 1);
lean_inc_ref(v_vs_122_);
lean_dec_ref(v_newNode_115_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0);
v___x_125_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_x_59_, v_ks_121_, v_vs_122_, v___x_123_, v___x_124_);
lean_dec_ref(v_vs_122_);
lean_dec_ref(v_ks_121_);
return v___x_125_;
}
else
{
return v_newNode_115_;
}
}
else
{
return v_newNode_115_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_128_, lean_object* v_keys_129_, lean_object* v_vals_130_, lean_object* v_i_131_, lean_object* v_entries_132_){
_start:
{
lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_133_ = lean_array_get_size(v_keys_129_);
v___x_134_ = lean_nat_dec_lt(v_i_131_, v___x_133_);
if (v___x_134_ == 0)
{
lean_dec(v_i_131_);
return v_entries_132_;
}
else
{
lean_object* v_k_135_; lean_object* v_v_136_; uint64_t v___y_138_; 
v_k_135_ = lean_array_fget_borrowed(v_keys_129_, v_i_131_);
v_v_136_ = lean_array_fget_borrowed(v_vals_130_, v_i_131_);
if (lean_obj_tag(v_k_135_) == 0)
{
uint64_t v___x_149_; 
v___x_149_ = 1723ULL;
v___y_138_ = v___x_149_;
goto v___jp_137_;
}
else
{
uint64_t v_hash_150_; 
v_hash_150_ = lean_ctor_get_uint64(v_k_135_, sizeof(void*)*2);
v___y_138_ = v_hash_150_;
goto v___jp_137_;
}
v___jp_137_:
{
size_t v_h_139_; size_t v___x_140_; lean_object* v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v_h_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_h_139_ = lean_uint64_to_usize(v___y_138_);
v___x_140_ = ((size_t)5ULL);
v___x_141_ = lean_unsigned_to_nat(1u);
v___x_142_ = ((size_t)1ULL);
v___x_143_ = lean_usize_sub(v_depth_128_, v___x_142_);
v___x_144_ = lean_usize_mul(v___x_140_, v___x_143_);
v_h_145_ = lean_usize_shift_right(v_h_139_, v___x_144_);
v___x_146_ = lean_nat_add(v_i_131_, v___x_141_);
lean_dec(v_i_131_);
lean_inc(v_v_136_);
lean_inc(v_k_135_);
v___x_147_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_entries_132_, v_h_145_, v_depth_128_, v_k_135_, v_v_136_);
v_i_131_ = v___x_146_;
v_entries_132_ = v___x_147_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_151_, lean_object* v_keys_152_, lean_object* v_vals_153_, lean_object* v_i_154_, lean_object* v_entries_155_){
_start:
{
size_t v_depth_boxed_156_; lean_object* v_res_157_; 
v_depth_boxed_156_ = lean_unbox_usize(v_depth_151_);
lean_dec(v_depth_151_);
v_res_157_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_156_, v_keys_152_, v_vals_153_, v_i_154_, v_entries_155_);
lean_dec_ref(v_vals_153_);
lean_dec_ref(v_keys_152_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
size_t v_x_355__boxed_163_; size_t v_x_356__boxed_164_; lean_object* v_res_165_; 
v_x_355__boxed_163_ = lean_unbox_usize(v_x_159_);
lean_dec(v_x_159_);
v_x_356__boxed_164_ = lean_unbox_usize(v_x_160_);
lean_dec(v_x_160_);
v_res_165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_158_, v_x_355__boxed_163_, v_x_356__boxed_164_, v_x_161_, v_x_162_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(lean_object* v_x_166_, lean_object* v_x_167_, lean_object* v_x_168_){
_start:
{
uint64_t v___y_170_; 
if (lean_obj_tag(v_x_167_) == 0)
{
uint64_t v___x_174_; 
v___x_174_ = 1723ULL;
v___y_170_ = v___x_174_;
goto v___jp_169_;
}
else
{
uint64_t v_hash_175_; 
v_hash_175_ = lean_ctor_get_uint64(v_x_167_, sizeof(void*)*2);
v___y_170_ = v_hash_175_;
goto v___jp_169_;
}
v___jp_169_:
{
size_t v___x_171_; size_t v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_uint64_to_usize(v___y_170_);
v___x_172_ = ((size_t)1ULL);
v___x_173_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_166_, v___x_171_, v___x_172_, v_x_167_, v_x_168_);
return v___x_173_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object* v_s_176_, lean_object* v_k_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_box(0);
v___x_179_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_s_176_, v_k_177_, v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0(lean_object* v_00_u03b2_180_, lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_x_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_x_181_, v_x_182_, v_x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_185_, lean_object* v_x_186_, size_t v_x_187_, size_t v_x_188_, lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_186_, v_x_187_, v_x_188_, v_x_189_, v_x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
size_t v_x_539__boxed_198_; size_t v_x_540__boxed_199_; lean_object* v_res_200_; 
v_x_539__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_x_540__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_res_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(v_00_u03b2_192_, v_x_193_, v_x_539__boxed_198_, v_x_540__boxed_199_, v_x_196_, v_x_197_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_201_, lean_object* v_n_202_, lean_object* v_k_203_, lean_object* v_v_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v_n_202_, v_k_203_, v_v_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_206_, size_t v_depth_207_, lean_object* v_keys_208_, lean_object* v_vals_209_, lean_object* v_heq_210_, lean_object* v_i_211_, lean_object* v_entries_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_207_, v_keys_208_, v_vals_209_, v_i_211_, v_entries_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_214_, lean_object* v_depth_215_, lean_object* v_keys_216_, lean_object* v_vals_217_, lean_object* v_heq_218_, lean_object* v_i_219_, lean_object* v_entries_220_){
_start:
{
size_t v_depth_boxed_221_; lean_object* v_res_222_; 
v_depth_boxed_221_ = lean_unbox_usize(v_depth_215_);
lean_dec(v_depth_215_);
v_res_222_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(v_00_u03b2_214_, v_depth_boxed_221_, v_keys_216_, v_vals_217_, v_heq_218_, v_i_219_, v_entries_220_);
lean_dec_ref(v_vals_217_);
lean_dec_ref(v_keys_216_);
return v_res_222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_223_, lean_object* v_x_224_, lean_object* v_x_225_, lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
lean_object* v___x_228_; 
v___x_228_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_224_, v_x_225_, v_x_226_, v_x_227_);
return v___x_228_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12(void){
_start:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10));
v___x_256_ = l_Lean_mkAtom(v___x_255_);
return v___x_256_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12);
v___x_258_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_259_ = lean_array_push(v___x_258_, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_271_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_272_ = lean_array_push(v___x_271_, v___x_270_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_273_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17);
v___x_274_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15));
v___x_275_ = lean_box(2);
v___x_276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
lean_ctor_set(v___x_276_, 2, v___x_273_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18);
v___x_278_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13);
v___x_279_ = lean_array_push(v___x_278_, v___x_277_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_281_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19);
v___x_282_ = lean_array_push(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_284_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20);
v___x_285_ = lean_array_push(v___x_284_, v___x_283_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_287_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21);
v___x_288_ = lean_array_push(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23(void){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_290_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22);
v___x_291_ = lean_array_push(v___x_290_, v___x_289_);
return v___x_291_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23);
v___x_293_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11));
v___x_294_ = lean_box(2);
v___x_295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
lean_ctor_set(v___x_295_, 2, v___x_292_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24);
v___x_297_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_298_ = lean_array_push(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_299_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25);
v___x_300_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9));
v___x_301_ = lean_box(2);
v___x_302_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_302_, 0, v___x_301_);
lean_ctor_set(v___x_302_, 1, v___x_300_);
lean_ctor_set(v___x_302_, 2, v___x_299_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_303_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26);
v___x_304_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_305_ = lean_array_push(v___x_304_, v___x_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_306_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27);
v___x_307_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7));
v___x_308_ = lean_box(2);
v___x_309_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
lean_ctor_set(v___x_309_, 2, v___x_306_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28);
v___x_311_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_312_ = lean_array_push(v___x_311_, v___x_310_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_313_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29);
v___x_314_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4));
v___x_315_ = lean_box(2);
v___x_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
lean_ctor_set(v___x_316_, 2, v___x_313_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam(void){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__1(void){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_320_ = lean_string_utf8_byte_size(v___x_319_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__2(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_321_ = lean_obj_once(&l_Lean_Parser_instInhabitedInputContext___closed__1, &l_Lean_Parser_instInhabitedInputContext___closed__1_once, _init_l_Lean_Parser_instInhabitedInputContext___closed__1);
v___x_322_ = l_Lean_instInhabitedFileMap_default;
v___x_323_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_324_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
lean_ctor_set(v___x_324_, 2, v___x_322_);
lean_ctor_set(v___x_324_, 3, v___x_321_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext(void){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = lean_obj_once(&l_Lean_Parser_instInhabitedInputContext___closed__2, &l_Lean_Parser_instInhabitedInputContext___closed__2_once, _init_l_Lean_Parser_instInhabitedInputContext___closed__2);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_mk___auto__1(void){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk___redArg(lean_object* v_input_327_, lean_object* v_fileName_328_, lean_object* v_endPos_329_, lean_object* v_fileMap_330_){
_start:
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_331_, 0, v_input_327_);
lean_ctor_set(v___x_331_, 1, v_fileName_328_);
lean_ctor_set(v___x_331_, 2, v_fileMap_330_);
lean_ctor_set(v___x_331_, 3, v_endPos_329_);
return v___x_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk(lean_object* v_input_332_, lean_object* v_fileName_333_, lean_object* v_endPos_334_, lean_object* v_endPos__valid_335_, lean_object* v_fileMap_336_){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_337_, 0, v_input_332_);
lean_ctor_set(v___x_337_, 1, v_fileName_333_);
lean_ctor_set(v___x_337_, 2, v_fileMap_336_);
lean_ctor_set(v___x_337_, 3, v_endPos_334_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input(lean_object* v_c_338_){
_start:
{
lean_object* v_inputString_339_; lean_object* v_endPos_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_inputString_339_ = lean_ctor_get(v_c_338_, 0);
v_endPos_340_ = lean_ctor_get(v_c_338_, 3);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_string_utf8_extract(v_inputString_339_, v___x_341_, v_endPos_340_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input___boxed(lean_object* v_c_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l_Lean_Parser_InputContext_input(v_c_343_);
lean_dec_ref(v_c_343_);
return v_res_344_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_InputContext_atEnd(lean_object* v_c_345_, lean_object* v_p_346_){
_start:
{
lean_object* v_endPos_347_; uint8_t v___x_348_; 
v_endPos_347_ = lean_ctor_get(v_c_345_, 3);
v___x_348_ = lean_nat_dec_le(v_endPos_347_, v_p_346_);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_atEnd___boxed(lean_object* v_c_349_, lean_object* v_p_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Lean_Parser_InputContext_atEnd(v_c_349_, v_p_350_);
lean_dec(v_p_350_);
lean_dec_ref(v_c_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get(lean_object* v_c_353_, lean_object* v_p_354_){
_start:
{
lean_object* v_inputString_355_; uint32_t v___x_356_; 
v_inputString_355_ = lean_ctor_get(v_c_353_, 0);
v___x_356_ = lean_string_utf8_get(v_inputString_355_, v_p_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get___boxed(lean_object* v_c_357_, lean_object* v_p_358_){
_start:
{
uint32_t v_res_359_; lean_object* v_r_360_; 
v_res_359_ = l_Lean_Parser_InputContext_get(v_c_357_, v_p_358_);
lean_dec(v_p_358_);
lean_dec_ref(v_c_357_);
v_r_360_ = lean_box_uint32(v_res_359_);
return v_r_360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_h__1_363_){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_apply_2(v_h__1_363_, v_x_361_, v_x_362_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_h__1_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_apply_2(v_h__1_368_, v_x_366_, v_x_367_);
return v___x_369_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27___redArg(lean_object* v_c_370_, lean_object* v_p_371_){
_start:
{
lean_object* v_inputString_372_; uint32_t v___x_373_; 
v_inputString_372_ = lean_ctor_get(v_c_370_, 0);
v___x_373_ = lean_string_utf8_get_fast(v_inputString_372_, v_p_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___redArg___boxed(lean_object* v_c_374_, lean_object* v_p_375_){
_start:
{
uint32_t v_res_376_; lean_object* v_r_377_; 
v_res_376_ = l_Lean_Parser_InputContext_get_x27___redArg(v_c_374_, v_p_375_);
lean_dec(v_p_375_);
lean_dec_ref(v_c_374_);
v_r_377_ = lean_box_uint32(v_res_376_);
return v_r_377_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27(lean_object* v_c_378_, lean_object* v_p_379_, lean_object* v_h_380_){
_start:
{
lean_object* v_inputString_381_; uint32_t v___x_382_; 
v_inputString_381_ = lean_ctor_get(v_c_378_, 0);
v___x_382_ = lean_string_utf8_get_fast(v_inputString_381_, v_p_379_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___boxed(lean_object* v_c_383_, lean_object* v_p_384_, lean_object* v_h_385_){
_start:
{
uint32_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Lean_Parser_InputContext_get_x27(v_c_383_, v_p_384_, v_h_385_);
lean_dec(v_p_384_);
lean_dec_ref(v_c_383_);
v_r_387_ = lean_box_uint32(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next(lean_object* v_c_388_, lean_object* v_p_389_){
_start:
{
lean_object* v_inputString_390_; lean_object* v___x_391_; 
v_inputString_390_ = lean_ctor_get(v_c_388_, 0);
v___x_391_ = lean_string_utf8_next(v_inputString_390_, v_p_389_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next___boxed(lean_object* v_c_392_, lean_object* v_p_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_Parser_InputContext_next(v_c_392_, v_p_393_);
lean_dec(v_p_393_);
lean_dec_ref(v_c_392_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg(lean_object* v_c_395_, lean_object* v_p_396_){
_start:
{
lean_object* v_inputString_397_; lean_object* v___x_398_; 
v_inputString_397_ = lean_ctor_get(v_c_395_, 0);
v___x_398_ = lean_string_utf8_next_fast(v_inputString_397_, v_p_396_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg___boxed(lean_object* v_c_399_, lean_object* v_p_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Parser_InputContext_next_x27___redArg(v_c_399_, v_p_400_);
lean_dec(v_p_400_);
lean_dec_ref(v_c_399_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27(lean_object* v_c_402_, lean_object* v_p_403_, lean_object* v_h_404_){
_start:
{
lean_object* v_inputString_405_; lean_object* v___x_406_; 
v_inputString_405_ = lean_ctor_get(v_c_402_, 0);
v___x_406_ = lean_string_utf8_next_fast(v_inputString_405_, v_p_403_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___boxed(lean_object* v_c_407_, lean_object* v_p_408_, lean_object* v_h_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Parser_InputContext_next_x27(v_c_407_, v_p_408_, v_h_409_);
lean_dec(v_p_408_);
lean_dec_ref(v_c_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract(lean_object* v_c_411_, lean_object* v_a_412_, lean_object* v_a_413_){
_start:
{
lean_object* v_inputString_414_; lean_object* v___x_415_; 
v_inputString_414_ = lean_ctor_get(v_c_411_, 0);
v___x_415_ = lean_string_utf8_extract(v_inputString_414_, v_a_412_, v_a_413_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract___boxed(lean_object* v_c_416_, lean_object* v_a_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Lean_Parser_InputContext_extract(v_c_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec(v_a_417_);
lean_dec_ref(v_c_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring(lean_object* v_c_420_, lean_object* v_startPos_421_, lean_object* v_stopPos_422_){
_start:
{
lean_object* v_inputString_423_; lean_object* v_endPos_424_; uint8_t v___x_425_; 
v_inputString_423_ = lean_ctor_get(v_c_420_, 0);
v_endPos_424_ = lean_ctor_get(v_c_420_, 3);
v___x_425_ = lean_nat_dec_le(v_stopPos_422_, v_endPos_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; 
lean_dec(v_stopPos_422_);
lean_inc(v_endPos_424_);
lean_inc_ref(v_inputString_423_);
v___x_426_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_426_, 0, v_inputString_423_);
lean_ctor_set(v___x_426_, 1, v_startPos_421_);
lean_ctor_set(v___x_426_, 2, v_endPos_424_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; 
lean_inc_ref(v_inputString_423_);
v___x_427_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_427_, 0, v_inputString_423_);
lean_ctor_set(v___x_427_, 1, v_startPos_421_);
lean_ctor_set(v___x_427_, 2, v_stopPos_422_);
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring___boxed(lean_object* v_c_428_, lean_object* v_startPos_429_, lean_object* v_stopPos_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_Parser_InputContext_substring(v_c_428_, v_startPos_429_, v_stopPos_430_);
lean_dec_ref(v_c_428_);
return v_res_431_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_getNext(lean_object* v_input_432_, lean_object* v_pos_433_){
_start:
{
lean_object* v_inputString_434_; lean_object* v___x_435_; uint32_t v___x_436_; 
v_inputString_434_ = lean_ctor_get(v_input_432_, 0);
v___x_435_ = lean_string_utf8_next(v_inputString_434_, v_pos_433_);
v___x_436_ = lean_string_utf8_get(v_inputString_434_, v___x_435_);
lean_dec(v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_getNext___boxed(lean_object* v_input_437_, lean_object* v_pos_438_){
_start:
{
uint32_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Lean_Parser_InputContext_getNext(v_input_437_, v_pos_438_);
lean_dec(v_pos_438_);
lean_dec_ref(v_input_437_);
v_r_440_ = lean_box_uint32(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev(lean_object* v_c_441_, lean_object* v_pos_442_){
_start:
{
lean_object* v_inputString_443_; lean_object* v___x_444_; 
v_inputString_443_ = lean_ctor_get(v_c_441_, 0);
v___x_444_ = lean_string_utf8_prev(v_inputString_443_, v_pos_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev___boxed(lean_object* v_c_445_, lean_object* v_pos_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Parser_InputContext_prev(v_c_445_, v_pos_446_);
lean_dec(v_pos_446_);
lean_dec_ref(v_c_445_);
return v_res_447_;
}
}
static lean_object* _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0(void){
_start:
{
lean_object* v___x_448_; lean_object* v___f_449_; 
v___x_448_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_449_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_449_, 0, v___x_448_);
return v___f_449_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext___lam__0(lean_object* v___f_450_, lean_object* v_a_451_, lean_object* v_b_452_){
_start:
{
lean_object* v_prec_453_; lean_object* v_quotDepth_454_; uint8_t v_suppressInsideQuot_455_; lean_object* v_savedPos_x3f_456_; lean_object* v_forbiddenTks_457_; lean_object* v_prec_458_; lean_object* v_quotDepth_459_; uint8_t v_suppressInsideQuot_460_; lean_object* v_savedPos_x3f_461_; lean_object* v_forbiddenTks_462_; uint8_t v___x_473_; 
v_prec_453_ = lean_ctor_get(v_a_451_, 0);
lean_inc(v_prec_453_);
v_quotDepth_454_ = lean_ctor_get(v_a_451_, 1);
lean_inc(v_quotDepth_454_);
v_suppressInsideQuot_455_ = lean_ctor_get_uint8(v_a_451_, sizeof(void*)*4);
v_savedPos_x3f_456_ = lean_ctor_get(v_a_451_, 2);
lean_inc(v_savedPos_x3f_456_);
v_forbiddenTks_457_ = lean_ctor_get(v_a_451_, 3);
lean_inc_ref(v_forbiddenTks_457_);
lean_dec_ref(v_a_451_);
v_prec_458_ = lean_ctor_get(v_b_452_, 0);
lean_inc(v_prec_458_);
v_quotDepth_459_ = lean_ctor_get(v_b_452_, 1);
lean_inc(v_quotDepth_459_);
v_suppressInsideQuot_460_ = lean_ctor_get_uint8(v_b_452_, sizeof(void*)*4);
v_savedPos_x3f_461_ = lean_ctor_get(v_b_452_, 2);
lean_inc(v_savedPos_x3f_461_);
v_forbiddenTks_462_ = lean_ctor_get(v_b_452_, 3);
lean_inc_ref(v_forbiddenTks_462_);
lean_dec_ref(v_b_452_);
v___x_473_ = lean_nat_dec_eq(v_prec_453_, v_prec_458_);
lean_dec(v_prec_458_);
lean_dec(v_prec_453_);
if (v___x_473_ == 0)
{
lean_dec_ref(v_forbiddenTks_462_);
lean_dec(v_savedPos_x3f_461_);
lean_dec(v_quotDepth_459_);
lean_dec_ref(v_forbiddenTks_457_);
lean_dec(v_savedPos_x3f_456_);
lean_dec(v_quotDepth_454_);
lean_dec_ref(v___f_450_);
return v___x_473_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = lean_nat_dec_eq(v_quotDepth_454_, v_quotDepth_459_);
lean_dec(v_quotDepth_459_);
lean_dec(v_quotDepth_454_);
if (v___x_474_ == 0)
{
lean_dec_ref(v_forbiddenTks_462_);
lean_dec(v_savedPos_x3f_461_);
lean_dec_ref(v_forbiddenTks_457_);
lean_dec(v_savedPos_x3f_456_);
lean_dec_ref(v___f_450_);
return v___x_474_;
}
else
{
if (v_suppressInsideQuot_460_ == 0)
{
if (v_suppressInsideQuot_455_ == 0)
{
goto v___jp_463_;
}
else
{
lean_dec_ref(v_forbiddenTks_462_);
lean_dec(v_savedPos_x3f_461_);
lean_dec_ref(v_forbiddenTks_457_);
lean_dec(v_savedPos_x3f_456_);
lean_dec_ref(v___f_450_);
return v_suppressInsideQuot_460_;
}
}
else
{
if (v_suppressInsideQuot_455_ == 0)
{
lean_dec_ref(v_forbiddenTks_462_);
lean_dec(v_savedPos_x3f_461_);
lean_dec_ref(v_forbiddenTks_457_);
lean_dec(v_savedPos_x3f_456_);
lean_dec_ref(v___f_450_);
return v_suppressInsideQuot_455_;
}
else
{
goto v___jp_463_;
}
}
}
}
v___jp_463_:
{
lean_object* v___f_464_; uint8_t v___x_465_; 
v___f_464_ = lean_obj_once(&l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0, &l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0_once, _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0);
v___x_465_ = l_Option_instBEq_beq___redArg(v___f_464_, v_savedPos_x3f_456_, v_savedPos_x3f_461_);
if (v___x_465_ == 0)
{
lean_dec_ref(v_forbiddenTks_462_);
lean_dec_ref(v_forbiddenTks_457_);
lean_dec_ref(v___f_450_);
return v___x_465_;
}
else
{
size_t v___x_466_; size_t v___x_467_; uint8_t v___x_468_; 
v___x_466_ = lean_ptr_addr(v_forbiddenTks_457_);
v___x_467_ = lean_ptr_addr(v_forbiddenTks_462_);
v___x_468_ = lean_usize_dec_eq(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; 
v___x_469_ = lean_array_get_size(v_forbiddenTks_457_);
v___x_470_ = lean_array_get_size(v_forbiddenTks_462_);
v___x_471_ = lean_nat_dec_eq(v___x_469_, v___x_470_);
if (v___x_471_ == 0)
{
lean_dec_ref(v_forbiddenTks_462_);
lean_dec_ref(v_forbiddenTks_457_);
lean_dec_ref(v___f_450_);
return v___x_471_;
}
else
{
uint8_t v___x_472_; 
v___x_472_ = l_Array_isEqvAux___redArg(v_forbiddenTks_457_, v_forbiddenTks_462_, v___f_450_, v___x_469_);
lean_dec_ref(v_forbiddenTks_462_);
lean_dec_ref(v_forbiddenTks_457_);
return v___x_472_;
}
}
else
{
lean_dec_ref(v_forbiddenTks_462_);
lean_dec_ref(v_forbiddenTks_457_);
lean_dec_ref(v___f_450_);
return v___x_468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed(lean_object* v___f_475_, lean_object* v_a_476_, lean_object* v_b_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_Lean_Parser_instBEqCacheableParserContext___lam__0(v___f_475_, v_a_476_, v_b_477_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0(lean_object* v_x_484_){
_start:
{
lean_object* v_toInputContext_485_; 
v_toInputContext_485_ = lean_ctor_get(v_x_484_, 0);
lean_inc_ref(v_toInputContext_485_);
return v_toInputContext_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(lean_object* v_x_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_486_);
lean_dec_ref(v_x_486_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos___redArg(lean_object* v_c_490_, lean_object* v_endPos_491_){
_start:
{
lean_object* v_toInputContext_492_; lean_object* v_toParserModuleContext_493_; lean_object* v_toCacheableParserContext_494_; lean_object* v_tokens_495_; lean_object* v___x_497_; uint8_t v_isShared_498_; uint8_t v_isSharedCheck_513_; 
v_toInputContext_492_ = lean_ctor_get(v_c_490_, 0);
v_toParserModuleContext_493_ = lean_ctor_get(v_c_490_, 1);
v_toCacheableParserContext_494_ = lean_ctor_get(v_c_490_, 2);
v_tokens_495_ = lean_ctor_get(v_c_490_, 3);
v_isSharedCheck_513_ = !lean_is_exclusive(v_c_490_);
if (v_isSharedCheck_513_ == 0)
{
v___x_497_ = v_c_490_;
v_isShared_498_ = v_isSharedCheck_513_;
goto v_resetjp_496_;
}
else
{
lean_inc(v_tokens_495_);
lean_inc(v_toCacheableParserContext_494_);
lean_inc(v_toParserModuleContext_493_);
lean_inc(v_toInputContext_492_);
lean_dec(v_c_490_);
v___x_497_ = lean_box(0);
v_isShared_498_ = v_isSharedCheck_513_;
goto v_resetjp_496_;
}
v_resetjp_496_:
{
lean_object* v_inputString_499_; lean_object* v_fileName_500_; lean_object* v_fileMap_501_; lean_object* v___x_503_; uint8_t v_isShared_504_; uint8_t v_isSharedCheck_511_; 
v_inputString_499_ = lean_ctor_get(v_toInputContext_492_, 0);
v_fileName_500_ = lean_ctor_get(v_toInputContext_492_, 1);
v_fileMap_501_ = lean_ctor_get(v_toInputContext_492_, 2);
v_isSharedCheck_511_ = !lean_is_exclusive(v_toInputContext_492_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; 
v_unused_512_ = lean_ctor_get(v_toInputContext_492_, 3);
lean_dec(v_unused_512_);
v___x_503_ = v_toInputContext_492_;
v_isShared_504_ = v_isSharedCheck_511_;
goto v_resetjp_502_;
}
else
{
lean_inc(v_fileMap_501_);
lean_inc(v_fileName_500_);
lean_inc(v_inputString_499_);
lean_dec(v_toInputContext_492_);
v___x_503_ = lean_box(0);
v_isShared_504_ = v_isSharedCheck_511_;
goto v_resetjp_502_;
}
v_resetjp_502_:
{
lean_object* v___x_506_; 
if (v_isShared_504_ == 0)
{
lean_ctor_set(v___x_503_, 3, v_endPos_491_);
v___x_506_ = v___x_503_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_inputString_499_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_fileName_500_);
lean_ctor_set(v_reuseFailAlloc_510_, 2, v_fileMap_501_);
lean_ctor_set(v_reuseFailAlloc_510_, 3, v_endPos_491_);
v___x_506_ = v_reuseFailAlloc_510_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
lean_object* v___x_508_; 
if (v_isShared_498_ == 0)
{
lean_ctor_set(v___x_497_, 0, v___x_506_);
v___x_508_ = v___x_497_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_509_; 
v_reuseFailAlloc_509_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_506_);
lean_ctor_set(v_reuseFailAlloc_509_, 1, v_toParserModuleContext_493_);
lean_ctor_set(v_reuseFailAlloc_509_, 2, v_toCacheableParserContext_494_);
lean_ctor_set(v_reuseFailAlloc_509_, 3, v_tokens_495_);
v___x_508_ = v_reuseFailAlloc_509_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
return v___x_508_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos(lean_object* v_c_514_, lean_object* v_endPos_515_, lean_object* v_endPos__valid_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_514_, v_endPos_515_);
return v___x_517_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
if (lean_obj_tag(v_x_524_) == 0)
{
if (lean_obj_tag(v_x_525_) == 0)
{
uint8_t v___x_526_; 
v___x_526_ = 1;
return v___x_526_;
}
else
{
uint8_t v___x_527_; 
v___x_527_ = 0;
return v___x_527_;
}
}
else
{
if (lean_obj_tag(v_x_525_) == 0)
{
uint8_t v___x_528_; 
v___x_528_ = 0;
return v___x_528_;
}
else
{
lean_object* v_head_529_; lean_object* v_tail_530_; lean_object* v_head_531_; lean_object* v_tail_532_; uint8_t v___x_533_; 
v_head_529_ = lean_ctor_get(v_x_524_, 0);
v_tail_530_ = lean_ctor_get(v_x_524_, 1);
v_head_531_ = lean_ctor_get(v_x_525_, 0);
v_tail_532_ = lean_ctor_get(v_x_525_, 1);
v___x_533_ = lean_string_dec_eq(v_head_529_, v_head_531_);
if (v___x_533_ == 0)
{
return v___x_533_;
}
else
{
v_x_524_ = v_tail_530_;
v_x_525_ = v_tail_532_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(lean_object* v_x_535_, lean_object* v_x_536_){
_start:
{
uint8_t v_res_537_; lean_object* v_r_538_; 
v_res_537_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_535_, v_x_536_);
lean_dec(v_x_536_);
lean_dec(v_x_535_);
v_r_538_ = lean_box(v_res_537_);
return v_r_538_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqError_beq(lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
lean_object* v_unexpectedTk_541_; lean_object* v_unexpected_542_; lean_object* v_expected_543_; lean_object* v_unexpectedTk_544_; lean_object* v_unexpected_545_; lean_object* v_expected_546_; uint8_t v___x_547_; 
v_unexpectedTk_541_ = lean_ctor_get(v_x_539_, 0);
v_unexpected_542_ = lean_ctor_get(v_x_539_, 1);
v_expected_543_ = lean_ctor_get(v_x_539_, 2);
v_unexpectedTk_544_ = lean_ctor_get(v_x_540_, 0);
v_unexpected_545_ = lean_ctor_get(v_x_540_, 1);
v_expected_546_ = lean_ctor_get(v_x_540_, 2);
v___x_547_ = l_Lean_Syntax_structEq(v_unexpectedTk_541_, v_unexpectedTk_544_);
if (v___x_547_ == 0)
{
return v___x_547_;
}
else
{
uint8_t v___x_548_; 
v___x_548_ = lean_string_dec_eq(v_unexpected_542_, v_unexpected_545_);
if (v___x_548_ == 0)
{
return v___x_548_;
}
else
{
uint8_t v___x_549_; 
v___x_549_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_543_, v_expected_546_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
uint8_t v_res_552_; lean_object* v_r_553_; 
v_res_552_ = l_Lean_Parser_instBEqError_beq(v_x_550_, v_x_551_);
lean_dec_ref(v_x_551_);
lean_dec_ref(v_x_550_);
v_r_553_ = lean_box(v_res_552_);
return v_r_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* v_x_558_){
_start:
{
if (lean_obj_tag(v_x_558_) == 0)
{
lean_object* v___x_559_; 
v___x_559_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
return v___x_559_;
}
else
{
lean_object* v_tail_560_; 
v_tail_560_ = lean_ctor_get(v_x_558_, 1);
if (lean_obj_tag(v_tail_560_) == 0)
{
lean_object* v_head_561_; 
v_head_561_ = lean_ctor_get(v_x_558_, 0);
lean_inc(v_head_561_);
lean_dec_ref_known(v_x_558_, 2);
return v_head_561_;
}
else
{
lean_object* v_tail_562_; 
lean_inc_ref(v_tail_560_);
v_tail_562_ = lean_ctor_get(v_tail_560_, 1);
if (lean_obj_tag(v_tail_562_) == 0)
{
lean_object* v_head_563_; lean_object* v_head_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v_head_563_ = lean_ctor_get(v_x_558_, 0);
lean_inc(v_head_563_);
lean_dec_ref_known(v_x_558_, 2);
v_head_564_ = lean_ctor_get(v_tail_560_, 0);
lean_inc(v_head_564_);
lean_dec_ref_known(v_tail_560_, 2);
v___x_565_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0));
v___x_566_ = lean_string_append(v_head_563_, v___x_565_);
v___x_567_ = lean_string_append(v___x_566_, v_head_564_);
lean_dec(v_head_564_);
return v___x_567_;
}
else
{
lean_object* v_head_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_head_568_ = lean_ctor_get(v_x_558_, 0);
lean_inc(v_head_568_);
lean_dec_ref_known(v_x_558_, 2);
v___x_569_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_570_ = lean_string_append(v_head_568_, v___x_569_);
v___x_571_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_tail_560_);
v___x_572_ = lean_string_append(v___x_570_, v___x_571_);
lean_dec_ref(v___x_571_);
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object* v_as_573_){
_start:
{
lean_object* v___f_574_; lean_object* v___x_575_; 
v___f_574_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext___closed__0));
v___x_575_ = l_List_eraseRepsBy___redArg(v___f_574_, v_as_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object* v_hi_576_, lean_object* v_pivot_577_, lean_object* v_as_578_, lean_object* v_i_579_, lean_object* v_k_580_){
_start:
{
uint8_t v___x_581_; 
v___x_581_ = lean_nat_dec_lt(v_k_580_, v_hi_576_);
if (v___x_581_ == 0)
{
lean_object* v___x_582_; lean_object* v___x_583_; 
lean_dec(v_k_580_);
v___x_582_ = lean_array_fswap(v_as_578_, v_i_579_, v_hi_576_);
v___x_583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_583_, 0, v_i_579_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
return v___x_583_;
}
else
{
lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_584_ = lean_array_fget_borrowed(v_as_578_, v_k_580_);
v___x_585_ = lean_string_dec_lt(v___x_584_, v_pivot_577_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = lean_nat_add(v_k_580_, v___x_586_);
lean_dec(v_k_580_);
v_k_580_ = v___x_587_;
goto _start;
}
else
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_589_ = lean_array_fswap(v_as_578_, v_i_579_, v_k_580_);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_add(v_i_579_, v___x_590_);
lean_dec(v_i_579_);
v___x_592_ = lean_nat_add(v_k_580_, v___x_590_);
lean_dec(v_k_580_);
v_as_578_ = v___x_589_;
v_i_579_ = v___x_591_;
v_k_580_ = v___x_592_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object* v_hi_594_, lean_object* v_pivot_595_, lean_object* v_as_596_, lean_object* v_i_597_, lean_object* v_k_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_594_, v_pivot_595_, v_as_596_, v_i_597_, v_k_598_);
lean_dec_ref(v_pivot_595_);
lean_dec(v_hi_594_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_n_600_, lean_object* v_as_601_, lean_object* v_lo_602_, lean_object* v_hi_603_){
_start:
{
lean_object* v___y_605_; uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_lt(v_lo_602_, v_hi_603_);
if (v___x_615_ == 0)
{
lean_dec(v_lo_602_);
return v_as_601_;
}
else
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v_mid_618_; lean_object* v___y_620_; lean_object* v___y_626_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_616_ = lean_nat_add(v_lo_602_, v_hi_603_);
v___x_617_ = lean_unsigned_to_nat(1u);
v_mid_618_ = lean_nat_shiftr(v___x_616_, v___x_617_);
lean_dec(v___x_616_);
v___x_631_ = lean_array_fget_borrowed(v_as_601_, v_mid_618_);
v___x_632_ = lean_array_fget_borrowed(v_as_601_, v_lo_602_);
v___x_633_ = lean_string_dec_lt(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
v___y_626_ = v_as_601_;
goto v___jp_625_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = lean_array_fswap(v_as_601_, v_lo_602_, v_mid_618_);
v___y_626_ = v___x_634_;
goto v___jp_625_;
}
v___jp_619_:
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = lean_array_fget_borrowed(v___y_620_, v_mid_618_);
v___x_622_ = lean_array_fget_borrowed(v___y_620_, v_hi_603_);
v___x_623_ = lean_string_dec_lt(v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
lean_dec(v_mid_618_);
v___y_605_ = v___y_620_;
goto v___jp_604_;
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_array_fswap(v___y_620_, v_mid_618_, v_hi_603_);
lean_dec(v_mid_618_);
v___y_605_ = v___x_624_;
goto v___jp_604_;
}
}
v___jp_625_:
{
lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v___x_627_ = lean_array_fget_borrowed(v___y_626_, v_hi_603_);
v___x_628_ = lean_array_fget_borrowed(v___y_626_, v_lo_602_);
v___x_629_ = lean_string_dec_lt(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
v___y_620_ = v___y_626_;
goto v___jp_619_;
}
else
{
lean_object* v___x_630_; 
v___x_630_ = lean_array_fswap(v___y_626_, v_lo_602_, v_hi_603_);
v___y_620_ = v___x_630_;
goto v___jp_619_;
}
}
}
v___jp_604_:
{
lean_object* v_pivot_606_; lean_object* v___x_607_; lean_object* v_fst_608_; lean_object* v_snd_609_; uint8_t v___x_610_; 
v_pivot_606_ = lean_array_fget(v___y_605_, v_hi_603_);
lean_inc_n(v_lo_602_, 2);
v___x_607_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_603_, v_pivot_606_, v___y_605_, v_lo_602_, v_lo_602_);
lean_dec(v_pivot_606_);
v_fst_608_ = lean_ctor_get(v___x_607_, 0);
lean_inc(v_fst_608_);
v_snd_609_ = lean_ctor_get(v___x_607_, 1);
lean_inc(v_snd_609_);
lean_dec_ref(v___x_607_);
v___x_610_ = lean_nat_dec_le(v_hi_603_, v_fst_608_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_600_, v_snd_609_, v_lo_602_, v_fst_608_);
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = lean_nat_add(v_fst_608_, v___x_612_);
lean_dec(v_fst_608_);
v_as_601_ = v___x_611_;
v_lo_602_ = v___x_613_;
goto _start;
}
else
{
lean_dec(v_fst_608_);
lean_dec(v_lo_602_);
return v_snd_609_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_n_635_, lean_object* v_as_636_, lean_object* v_lo_637_, lean_object* v_hi_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_635_, v_as_636_, v_lo_637_, v_hi_638_);
lean_dec(v_hi_638_);
lean_dec(v_n_635_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_642_){
_start:
{
lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v_unexpected_675_; lean_object* v_expected_676_; lean_object* v___y_678_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_unexpected_675_ = lean_ctor_get(v_e_642_, 1);
lean_inc_ref(v_unexpected_675_);
v_expected_676_ = lean_ctor_get(v_e_642_, 2);
lean_inc(v_expected_676_);
lean_dec_ref(v_e_642_);
v___x_688_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_689_ = lean_string_dec_eq(v_unexpected_675_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_box(0);
v___x_691_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_691_, 0, v_unexpected_675_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
v___y_678_ = v___x_691_;
goto v___jp_677_;
}
else
{
lean_object* v___x_692_; 
lean_dec_ref(v_unexpected_675_);
v___x_692_ = lean_box(0);
v___y_678_ = v___x_692_;
goto v___jp_677_;
}
v___jp_643_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_647_ = l_List_appendTR___redArg(v___y_644_, v___y_645_);
v___x_648_ = l_String_intercalate(v___x_646_, v___x_647_);
return v___x_648_;
}
v___jp_649_:
{
lean_object* v___x_653_; lean_object* v_expected_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_653_ = lean_array_to_list(v___y_652_);
v_expected_654_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_653_);
v___x_655_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_656_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_654_);
v___x_657_ = lean_string_append(v___x_655_, v___x_656_);
lean_dec_ref(v___x_656_);
v___x_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v___y_651_);
v___y_644_ = v___y_650_;
v___y_645_ = v___x_658_;
goto v___jp_643_;
}
v___jp_659_:
{
lean_object* v___x_666_; 
v___x_666_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_664_, v___y_661_, v___y_660_, v___y_665_);
lean_dec(v___y_665_);
lean_dec(v___y_664_);
v___y_650_ = v___y_662_;
v___y_651_ = v___y_663_;
v___y_652_ = v___x_666_;
goto v___jp_649_;
}
v___jp_667_:
{
uint8_t v___x_674_; 
v___x_674_ = lean_nat_dec_le(v___y_673_, v___y_670_);
if (v___x_674_ == 0)
{
lean_dec(v___y_670_);
lean_inc(v___y_673_);
v___y_660_ = v___y_673_;
v___y_661_ = v___y_668_;
v___y_662_ = v___y_669_;
v___y_663_ = v___y_671_;
v___y_664_ = v___y_672_;
v___y_665_ = v___y_673_;
goto v___jp_659_;
}
else
{
v___y_660_ = v___y_673_;
v___y_661_ = v___y_668_;
v___y_662_ = v___y_669_;
v___y_663_ = v___y_671_;
v___y_664_ = v___y_672_;
v___y_665_ = v___y_670_;
goto v___jp_659_;
}
}
v___jp_677_:
{
lean_object* v___x_679_; uint8_t v___x_680_; 
v___x_679_ = lean_box(0);
v___x_680_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_676_, v___x_679_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_681_ = lean_array_mk(v_expected_676_);
v___x_682_ = lean_array_get_size(v___x_681_);
v___x_683_ = lean_unsigned_to_nat(0u);
v___x_684_ = lean_nat_dec_eq(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_685_ = lean_unsigned_to_nat(1u);
v___x_686_ = lean_nat_sub(v___x_682_, v___x_685_);
v___x_687_ = lean_nat_dec_le(v___x_683_, v___x_686_);
if (v___x_687_ == 0)
{
lean_inc(v___x_686_);
v___y_668_ = v___x_681_;
v___y_669_ = v___y_678_;
v___y_670_ = v___x_686_;
v___y_671_ = v___x_679_;
v___y_672_ = v___x_682_;
v___y_673_ = v___x_686_;
goto v___jp_667_;
}
else
{
v___y_668_ = v___x_681_;
v___y_669_ = v___y_678_;
v___y_670_ = v___x_686_;
v___y_671_ = v___x_679_;
v___y_672_ = v___x_682_;
v___y_673_ = v___x_683_;
goto v___jp_667_;
}
}
else
{
v___y_650_ = v___y_678_;
v___y_651_ = v___x_679_;
v___y_652_ = v___x_681_;
goto v___jp_649_;
}
}
else
{
lean_dec(v_expected_676_);
v___y_644_ = v___y_678_;
v___y_645_ = v___x_679_;
goto v___jp_643_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_693_, lean_object* v_as_694_, lean_object* v_lo_695_, lean_object* v_hi_696_, lean_object* v_w_697_, lean_object* v_hlo_698_, lean_object* v_hhi_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_693_, v_as_694_, v_lo_695_, v_hi_696_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_701_, lean_object* v_as_702_, lean_object* v_lo_703_, lean_object* v_hi_704_, lean_object* v_w_705_, lean_object* v_hlo_706_, lean_object* v_hhi_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_701_, v_as_702_, v_lo_703_, v_hi_704_, v_w_705_, v_hlo_706_, v_hhi_707_);
lean_dec(v_hi_704_);
lean_dec(v_n_701_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object* v_n_709_, lean_object* v_lo_710_, lean_object* v_hi_711_, lean_object* v_hhi_712_, lean_object* v_pivot_713_, lean_object* v_as_714_, lean_object* v_i_715_, lean_object* v_k_716_, lean_object* v_ilo_717_, lean_object* v_ik_718_, lean_object* v_w_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_711_, v_pivot_713_, v_as_714_, v_i_715_, v_k_716_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object* v_n_721_, lean_object* v_lo_722_, lean_object* v_hi_723_, lean_object* v_hhi_724_, lean_object* v_pivot_725_, lean_object* v_as_726_, lean_object* v_i_727_, lean_object* v_k_728_, lean_object* v_ilo_729_, lean_object* v_ik_730_, lean_object* v_w_731_){
_start:
{
lean_object* v_res_732_; 
v_res_732_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_721_, v_lo_722_, v_hi_723_, v_hhi_724_, v_pivot_725_, v_as_726_, v_i_727_, v_k_728_, v_ilo_729_, v_ik_730_, v_w_731_);
lean_dec_ref(v_pivot_725_);
lean_dec(v_hi_723_);
lean_dec(v_lo_722_);
lean_dec(v_n_721_);
return v_res_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_735_, lean_object* v_e_u2082_736_){
_start:
{
lean_object* v_unexpectedTk_737_; lean_object* v_unexpected_738_; lean_object* v_expected_739_; lean_object* v___y_741_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_unexpectedTk_737_ = lean_ctor_get(v_e_u2082_736_, 0);
lean_inc(v_unexpectedTk_737_);
v_unexpected_738_ = lean_ctor_get(v_e_u2082_736_, 1);
lean_inc_ref(v_unexpected_738_);
v_expected_739_ = lean_ctor_get(v_e_u2082_736_, 2);
lean_inc(v_expected_739_);
lean_dec_ref(v_e_u2082_736_);
v___x_753_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_754_ = lean_string_dec_eq(v_unexpected_738_, v___x_753_);
if (v___x_754_ == 0)
{
v___y_741_ = v_unexpected_738_;
goto v___jp_740_;
}
else
{
lean_object* v_unexpected_755_; 
lean_dec_ref(v_unexpected_738_);
v_unexpected_755_ = lean_ctor_get(v_e_u2081_735_, 1);
lean_inc_ref(v_unexpected_755_);
v___y_741_ = v_unexpected_755_;
goto v___jp_740_;
}
v___jp_740_:
{
lean_object* v_expected_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_750_; 
v_expected_742_ = lean_ctor_get(v_e_u2081_735_, 2);
v_isSharedCheck_750_ = !lean_is_exclusive(v_e_u2081_735_);
if (v_isSharedCheck_750_ == 0)
{
lean_object* v_unused_751_; lean_object* v_unused_752_; 
v_unused_751_ = lean_ctor_get(v_e_u2081_735_, 1);
lean_dec(v_unused_751_);
v_unused_752_ = lean_ctor_get(v_e_u2081_735_, 0);
lean_dec(v_unused_752_);
v___x_744_ = v_e_u2081_735_;
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_expected_742_);
lean_dec(v_e_u2081_735_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_750_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
v___x_746_ = l_List_appendTR___redArg(v_expected_742_, v_expected_739_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 2, v___x_746_);
lean_ctor_set(v___x_744_, 1, v___y_741_);
lean_ctor_set(v___x_744_, 0, v_unexpectedTk_737_);
v___x_748_ = v___x_744_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_unexpectedTk_737_);
lean_ctor_set(v_reuseFailAlloc_749_, 1, v___y_741_);
lean_ctor_set(v_reuseFailAlloc_749_, 2, v___x_746_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(lean_object* v_x_756_, lean_object* v_x_757_){
_start:
{
if (lean_obj_tag(v_x_756_) == 0)
{
if (lean_obj_tag(v_x_757_) == 0)
{
uint8_t v___x_758_; 
v___x_758_ = 1;
return v___x_758_;
}
else
{
uint8_t v___x_759_; 
v___x_759_ = 0;
return v___x_759_;
}
}
else
{
if (lean_obj_tag(v_x_757_) == 0)
{
uint8_t v___x_760_; 
v___x_760_ = 0;
return v___x_760_;
}
else
{
lean_object* v_val_761_; lean_object* v_val_762_; uint8_t v_decide_763_; 
v_val_761_ = lean_ctor_get(v_x_756_, 0);
v_val_762_ = lean_ctor_get(v_x_757_, 0);
v_decide_763_ = lean_nat_dec_eq(v_val_761_, v_val_762_);
return v_decide_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0___boxed(lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
uint8_t v_res_766_; lean_object* v_r_767_; 
v_res_766_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_x_764_, v_x_765_);
lean_dec(v_x_765_);
lean_dec(v_x_764_);
v_r_767_ = lean_box(v_res_766_);
return v_r_767_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(lean_object* v_xs_768_, lean_object* v_ys_769_, lean_object* v_x_770_){
_start:
{
lean_object* v_zero_771_; uint8_t v_isZero_772_; 
v_zero_771_ = lean_unsigned_to_nat(0u);
v_isZero_772_ = lean_nat_dec_eq(v_x_770_, v_zero_771_);
if (v_isZero_772_ == 1)
{
lean_dec(v_x_770_);
return v_isZero_772_;
}
else
{
lean_object* v_one_773_; lean_object* v_n_774_; lean_object* v___x_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_one_773_ = lean_unsigned_to_nat(1u);
v_n_774_ = lean_nat_sub(v_x_770_, v_one_773_);
lean_dec(v_x_770_);
v___x_775_ = lean_array_fget_borrowed(v_xs_768_, v_n_774_);
v___x_776_ = lean_array_fget_borrowed(v_ys_769_, v_n_774_);
v___x_777_ = lean_string_dec_eq(v___x_775_, v___x_776_);
if (v___x_777_ == 0)
{
lean_dec(v_n_774_);
return v___x_777_;
}
else
{
v_x_770_ = v_n_774_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg___boxed(lean_object* v_xs_779_, lean_object* v_ys_780_, lean_object* v_x_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_779_, v_ys_780_, v_x_781_);
lean_dec_ref(v_ys_780_);
lean_dec_ref(v_xs_779_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
lean_object* v_toCacheableParserContext_786_; lean_object* v_parserName_787_; lean_object* v_pos_788_; lean_object* v_toCacheableParserContext_789_; lean_object* v_parserName_790_; lean_object* v_pos_791_; uint8_t v___y_796_; lean_object* v_prec_797_; lean_object* v_quotDepth_798_; uint8_t v_suppressInsideQuot_799_; lean_object* v_savedPos_x3f_800_; lean_object* v_forbiddenTks_801_; lean_object* v_prec_802_; lean_object* v_quotDepth_803_; uint8_t v_suppressInsideQuot_804_; lean_object* v_savedPos_x3f_805_; lean_object* v_forbiddenTks_806_; uint8_t v___x_816_; 
v_toCacheableParserContext_786_ = lean_ctor_get(v_x_784_, 0);
v_parserName_787_ = lean_ctor_get(v_x_784_, 1);
v_pos_788_ = lean_ctor_get(v_x_784_, 2);
v_toCacheableParserContext_789_ = lean_ctor_get(v_x_785_, 0);
v_parserName_790_ = lean_ctor_get(v_x_785_, 1);
v_pos_791_ = lean_ctor_get(v_x_785_, 2);
v_prec_797_ = lean_ctor_get(v_toCacheableParserContext_786_, 0);
v_quotDepth_798_ = lean_ctor_get(v_toCacheableParserContext_786_, 1);
v_suppressInsideQuot_799_ = lean_ctor_get_uint8(v_toCacheableParserContext_786_, sizeof(void*)*4);
v_savedPos_x3f_800_ = lean_ctor_get(v_toCacheableParserContext_786_, 2);
v_forbiddenTks_801_ = lean_ctor_get(v_toCacheableParserContext_786_, 3);
v_prec_802_ = lean_ctor_get(v_toCacheableParserContext_789_, 0);
v_quotDepth_803_ = lean_ctor_get(v_toCacheableParserContext_789_, 1);
v_suppressInsideQuot_804_ = lean_ctor_get_uint8(v_toCacheableParserContext_789_, sizeof(void*)*4);
v_savedPos_x3f_805_ = lean_ctor_get(v_toCacheableParserContext_789_, 2);
v_forbiddenTks_806_ = lean_ctor_get(v_toCacheableParserContext_789_, 3);
v___x_816_ = lean_nat_dec_eq(v_prec_797_, v_prec_802_);
if (v___x_816_ == 0)
{
return v___x_816_;
}
else
{
uint8_t v___x_817_; 
v___x_817_ = lean_nat_dec_eq(v_quotDepth_798_, v_quotDepth_803_);
if (v___x_817_ == 0)
{
return v___x_817_;
}
else
{
if (v_suppressInsideQuot_804_ == 0)
{
if (v_suppressInsideQuot_799_ == 0)
{
goto v___jp_807_;
}
else
{
return v_suppressInsideQuot_804_;
}
}
else
{
if (v_suppressInsideQuot_799_ == 0)
{
return v_suppressInsideQuot_799_;
}
else
{
goto v___jp_807_;
}
}
}
}
v___jp_792_:
{
uint8_t v___x_793_; 
v___x_793_ = lean_name_eq(v_parserName_787_, v_parserName_790_);
if (v___x_793_ == 0)
{
return v___x_793_;
}
else
{
uint8_t v_decide_794_; 
v_decide_794_ = lean_nat_dec_eq(v_pos_788_, v_pos_791_);
return v_decide_794_;
}
}
v___jp_795_:
{
if (v___y_796_ == 0)
{
return v___y_796_;
}
else
{
goto v___jp_792_;
}
}
v___jp_807_:
{
uint8_t v___x_808_; 
v___x_808_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_savedPos_x3f_800_, v_savedPos_x3f_805_);
if (v___x_808_ == 0)
{
v___y_796_ = v___x_808_;
goto v___jp_795_;
}
else
{
size_t v___x_809_; size_t v___x_810_; uint8_t v___x_811_; 
v___x_809_ = lean_ptr_addr(v_forbiddenTks_801_);
v___x_810_ = lean_ptr_addr(v_forbiddenTks_806_);
v___x_811_ = lean_usize_dec_eq(v___x_809_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_812_ = lean_array_get_size(v_forbiddenTks_801_);
v___x_813_ = lean_array_get_size(v_forbiddenTks_806_);
v___x_814_ = lean_nat_dec_eq(v___x_812_, v___x_813_);
if (v___x_814_ == 0)
{
return v___x_814_;
}
else
{
uint8_t v___x_815_; 
v___x_815_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_forbiddenTks_801_, v_forbiddenTks_806_, v___x_812_);
v___y_796_ = v___x_815_;
goto v___jp_795_;
}
}
else
{
goto v___jp_792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object* v_x_818_, lean_object* v_x_819_){
_start:
{
uint8_t v_res_820_; lean_object* v_r_821_; 
v_res_820_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_818_, v_x_819_);
lean_dec_ref(v_x_819_);
lean_dec_ref(v_x_818_);
v_r_821_ = lean_box(v_res_820_);
return v_r_821_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(lean_object* v_xs_822_, lean_object* v_ys_823_, lean_object* v_hsz_824_, lean_object* v_x_825_, lean_object* v_x_826_){
_start:
{
uint8_t v___x_827_; 
v___x_827_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_822_, v_ys_823_, v_x_825_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___boxed(lean_object* v_xs_828_, lean_object* v_ys_829_, lean_object* v_hsz_830_, lean_object* v_x_831_, lean_object* v_x_832_){
_start:
{
uint8_t v_res_833_; lean_object* v_r_834_; 
v_res_833_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(v_xs_828_, v_ys_829_, v_hsz_830_, v_x_831_, v_x_832_);
lean_dec_ref(v_ys_829_);
lean_dec_ref(v_xs_828_);
v_r_834_ = lean_box(v_res_833_);
return v_r_834_;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* v_k_837_){
_start:
{
lean_object* v_parserName_838_; lean_object* v_pos_839_; uint64_t v___x_840_; 
v_parserName_838_ = lean_ctor_get(v_k_837_, 1);
v_pos_839_ = lean_ctor_get(v_k_837_, 2);
v___x_840_ = l_String_instHashableRaw_hash(v_pos_839_);
if (lean_obj_tag(v_parserName_838_) == 0)
{
uint64_t v___x_841_; uint64_t v___x_842_; 
v___x_841_ = 1723ULL;
v___x_842_ = lean_uint64_mix_hash(v___x_840_, v___x_841_);
return v___x_842_;
}
else
{
uint64_t v_hash_843_; uint64_t v___x_844_; 
v_hash_843_ = lean_ctor_get_uint64(v_parserName_838_, sizeof(void*)*2);
v___x_844_ = lean_uint64_mix_hash(v___x_840_, v_hash_843_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* v_k_845_){
_start:
{
uint64_t v_res_846_; lean_object* v_r_847_; 
v_res_846_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_845_);
lean_dec_ref(v_k_845_);
v_r_847_ = lean_box_uint64(v_res_846_);
return v_r_847_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0(void){
_start:
{
uint32_t v___x_850_; lean_object* v___x_851_; 
v___x_850_ = 32;
v___x_851_ = l_Char_utf8Size(v___x_850_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_box(0);
v___x_853_ = lean_unsigned_to_nat(16u);
v___x_854_ = lean_mk_array(v___x_853_, v___x_852_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__2(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_858_){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_859_ = lean_string_utf8_byte_size(v_input_858_);
v___x_860_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_861_ = lean_nat_add(v___x_859_, v___x_860_);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_box(0);
v___x_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_864_, 0, v___x_861_);
lean_ctor_set(v___x_864_, 1, v___x_862_);
lean_ctor_set(v___x_864_, 2, v___x_863_);
v___x_865_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_864_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Parser_initCacheForInput(v_input_867_);
lean_dec_ref(v_input_867_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_869_){
_start:
{
lean_object* v_raw_870_; lean_object* v_drop_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_raw_870_ = lean_ctor_get(v_stack_869_, 0);
lean_inc_ref(v_raw_870_);
v_drop_871_ = lean_ctor_get(v_stack_869_, 1);
lean_inc(v_drop_871_);
lean_dec_ref(v_stack_869_);
v___x_872_ = lean_array_get_size(v_raw_870_);
v___x_873_ = l_Array_toSubarray___redArg(v_raw_870_, v_drop_871_, v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_880_){
_start:
{
lean_object* v_raw_881_; lean_object* v_drop_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v_raw_881_ = lean_ctor_get(v_stack_880_, 0);
v_drop_882_ = lean_ctor_get(v_stack_880_, 1);
v___x_883_ = lean_array_get_size(v_raw_881_);
v___x_884_ = lean_nat_sub(v___x_883_, v_drop_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Lean_Parser_SyntaxStack_size(v_stack_885_);
lean_dec_ref(v_stack_885_);
return v_res_886_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_887_){
_start:
{
lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v___x_888_ = l_Lean_Parser_SyntaxStack_size(v_stack_887_);
v___x_889_ = lean_unsigned_to_nat(0u);
v___x_890_ = lean_nat_dec_eq(v___x_888_, v___x_889_);
lean_dec(v___x_888_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_891_){
_start:
{
uint8_t v_res_892_; lean_object* v_r_893_; 
v_res_892_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_891_);
lean_dec_ref(v_stack_891_);
v_r_893_ = lean_box(v_res_892_);
return v_r_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_894_, lean_object* v_n_895_){
_start:
{
lean_object* v_raw_896_; lean_object* v_drop_897_; lean_object* v___x_899_; uint8_t v_isShared_900_; uint8_t v_isSharedCheck_906_; 
v_raw_896_ = lean_ctor_get(v_stack_894_, 0);
v_drop_897_ = lean_ctor_get(v_stack_894_, 1);
v_isSharedCheck_906_ = !lean_is_exclusive(v_stack_894_);
if (v_isSharedCheck_906_ == 0)
{
v___x_899_ = v_stack_894_;
v_isShared_900_ = v_isSharedCheck_906_;
goto v_resetjp_898_;
}
else
{
lean_inc(v_drop_897_);
lean_inc(v_raw_896_);
lean_dec(v_stack_894_);
v___x_899_ = lean_box(0);
v_isShared_900_ = v_isSharedCheck_906_;
goto v_resetjp_898_;
}
v_resetjp_898_:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_904_; 
v___x_901_ = lean_nat_add(v_drop_897_, v_n_895_);
v___x_902_ = l_Array_shrink___redArg(v_raw_896_, v___x_901_);
lean_dec(v___x_901_);
if (v_isShared_900_ == 0)
{
lean_ctor_set(v___x_899_, 0, v___x_902_);
v___x_904_ = v___x_899_;
goto v_reusejp_903_;
}
else
{
lean_object* v_reuseFailAlloc_905_; 
v_reuseFailAlloc_905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_902_);
lean_ctor_set(v_reuseFailAlloc_905_, 1, v_drop_897_);
v___x_904_ = v_reuseFailAlloc_905_;
goto v_reusejp_903_;
}
v_reusejp_903_:
{
return v___x_904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_907_, lean_object* v_n_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_907_, v_n_908_);
lean_dec(v_n_908_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_910_, lean_object* v_a_911_){
_start:
{
lean_object* v_raw_912_; lean_object* v_drop_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_921_; 
v_raw_912_ = lean_ctor_get(v_stack_910_, 0);
v_drop_913_ = lean_ctor_get(v_stack_910_, 1);
v_isSharedCheck_921_ = !lean_is_exclusive(v_stack_910_);
if (v_isSharedCheck_921_ == 0)
{
v___x_915_ = v_stack_910_;
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_drop_913_);
lean_inc(v_raw_912_);
lean_dec(v_stack_910_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_921_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_919_; 
v___x_917_ = lean_array_push(v_raw_912_, v_a_911_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_917_);
v___x_919_ = v___x_915_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v___x_917_);
lean_ctor_set(v_reuseFailAlloc_920_, 1, v_drop_913_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_922_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = l_Lean_Parser_SyntaxStack_size(v_stack_922_);
v___x_925_ = lean_nat_dec_lt(v___x_923_, v___x_924_);
lean_dec(v___x_924_);
if (v___x_925_ == 0)
{
return v_stack_922_;
}
else
{
lean_object* v_raw_926_; lean_object* v_drop_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_935_; 
v_raw_926_ = lean_ctor_get(v_stack_922_, 0);
v_drop_927_ = lean_ctor_get(v_stack_922_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_stack_922_);
if (v_isSharedCheck_935_ == 0)
{
v___x_929_ = v_stack_922_;
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_drop_927_);
lean_inc(v_raw_926_);
lean_dec(v_stack_922_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_935_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_931_ = lean_array_pop(v_raw_926_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_931_);
v___x_933_ = v___x_929_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
lean_ctor_set(v_reuseFailAlloc_934_, 1, v_drop_927_);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_936_){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_937_ = lean_box(0);
v___x_938_ = lean_panic_fn_borrowed(v___x_937_, v_msg_936_);
return v___x_938_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; 
v___x_942_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_943_ = lean_unsigned_to_nat(4u);
v___x_944_ = lean_unsigned_to_nat(313u);
v___x_945_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_946_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_947_ = l_mkPanicMessageWithDecl(v___x_946_, v___x_945_, v___x_944_, v___x_943_, v___x_942_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_948_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_949_ = lean_unsigned_to_nat(0u);
v___x_950_ = l_Lean_Parser_SyntaxStack_size(v_stack_948_);
v___x_951_ = lean_nat_dec_lt(v___x_949_, v___x_950_);
lean_dec(v___x_950_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_953_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_952_);
return v___x_953_;
}
else
{
lean_object* v_raw_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v_raw_954_ = lean_ctor_get(v_stack_948_, 0);
v___x_955_ = lean_box(0);
v___x_956_ = lean_array_get_size(v_raw_954_);
v___x_957_ = lean_unsigned_to_nat(1u);
v___x_958_ = lean_nat_sub(v___x_956_, v___x_957_);
v___x_959_ = lean_array_get_borrowed(v___x_955_, v_raw_954_, v___x_958_);
lean_dec(v___x_958_);
lean_inc(v___x_959_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Parser_SyntaxStack_back(v_stack_960_);
lean_dec_ref(v_stack_960_);
return v_res_961_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_964_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_965_ = lean_unsigned_to_nat(4u);
v___x_966_ = lean_unsigned_to_nat(319u);
v___x_967_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_968_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_969_ = l_mkPanicMessageWithDecl(v___x_968_, v___x_967_, v___x_966_, v___x_965_, v___x_964_);
return v___x_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_970_, lean_object* v_i_971_){
_start:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = l_Lean_Parser_SyntaxStack_size(v_stack_970_);
v___x_973_ = lean_nat_dec_lt(v_i_971_, v___x_972_);
lean_dec(v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_975_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_974_);
return v___x_975_;
}
else
{
lean_object* v_raw_976_; lean_object* v_drop_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_raw_976_ = lean_ctor_get(v_stack_970_, 0);
v_drop_977_ = lean_ctor_get(v_stack_970_, 1);
v___x_978_ = lean_box(0);
v___x_979_ = lean_nat_add(v_drop_977_, v_i_971_);
v___x_980_ = lean_array_get_borrowed(v___x_978_, v_raw_976_, v___x_979_);
lean_dec(v___x_979_);
lean_inc(v___x_980_);
return v___x_980_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_981_, lean_object* v_i_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_981_, v_i_982_);
lean_dec(v_i_982_);
lean_dec_ref(v_stack_981_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_984_, lean_object* v_start_985_, lean_object* v_stop_986_){
_start:
{
lean_object* v_raw_987_; lean_object* v_drop_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_raw_987_ = lean_ctor_get(v_stack_984_, 0);
v_drop_988_ = lean_ctor_get(v_stack_984_, 1);
v___x_989_ = lean_nat_add(v_drop_988_, v_start_985_);
v___x_990_ = lean_nat_add(v_drop_988_, v_stop_986_);
v___x_991_ = l_Array_extract___redArg(v_raw_987_, v___x_989_, v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_992_, lean_object* v_start_993_, lean_object* v_stop_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Parser_SyntaxStack_extract(v_stack_992_, v_start_993_, v_stop_994_);
lean_dec(v_stop_994_);
lean_dec(v_start_993_);
lean_dec_ref(v_stack_992_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_996_, lean_object* v_stxs_997_){
_start:
{
lean_object* v_raw_998_; lean_object* v_drop_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1007_; 
v_raw_998_ = lean_ctor_get(v_stack_996_, 0);
v_drop_999_ = lean_ctor_get(v_stack_996_, 1);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_stack_996_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1001_ = v_stack_996_;
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_drop_999_);
lean_inc(v_raw_998_);
lean_dec(v_stack_996_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1007_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1003_ = l_Array_append___redArg(v_raw_998_, v_stxs_997_);
if (v_isShared_1002_ == 0)
{
lean_ctor_set(v___x_1001_, 0, v___x_1003_);
v___x_1005_ = v___x_1001_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_drop_999_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_1008_, lean_object* v_stxs_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_1008_, v_stxs_1009_);
lean_dec_ref(v_stxs_1009_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_1011_, lean_object* v_stxs_1012_){
_start:
{
lean_object* v_raw_1013_; lean_object* v_drop_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_raw_1013_ = lean_ctor_get(v_stack_1011_, 0);
v_drop_1014_ = lean_ctor_get(v_stack_1011_, 1);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_stack_1011_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1016_ = v_stack_1011_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_drop_1014_);
lean_inc(v_raw_1013_);
lean_dec(v_stack_1011_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
v___x_1018_ = l_Array_append___redArg(v_raw_1013_, v_stxs_1012_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_drop_1014_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_1023_, lean_object* v_stxs_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_1023_, v_stxs_1024_);
lean_dec_ref(v_stxs_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_1028_){
_start:
{
lean_object* v_errorMsg_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_errorMsg_1029_ = lean_ctor_get(v_s_1028_, 4);
lean_inc(v_errorMsg_1029_);
lean_dec_ref(v_s_1028_);
v___x_1030_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_1031_ = lean_box(0);
v___x_1032_ = l_Option_instBEq_beq___redArg(v___x_1030_, v_errorMsg_1029_, v___x_1031_);
if (v___x_1032_ == 0)
{
uint8_t v___x_1033_; 
v___x_1033_ = 1;
return v___x_1033_;
}
else
{
uint8_t v___x_1034_; 
v___x_1034_ = 0;
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_1035_){
_start:
{
uint8_t v_res_1036_; lean_object* v_r_1037_; 
v_res_1036_ = l_Lean_Parser_ParserState_hasError(v_s_1035_);
v_r_1037_ = lean_box(v_res_1036_);
return v_r_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_1038_){
_start:
{
lean_object* v_stxStack_1039_; lean_object* v___x_1040_; 
v_stxStack_1039_ = lean_ctor_get(v_s_1038_, 0);
v___x_1040_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1039_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l_Lean_Parser_ParserState_stackSize(v_s_1041_);
lean_dec_ref(v_s_1041_);
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_1043_, lean_object* v_iniStackSz_1044_, lean_object* v_iniPos_1045_){
_start:
{
lean_object* v_stxStack_1046_; lean_object* v_lhsPrec_1047_; lean_object* v_cache_1048_; lean_object* v_recoveredErrors_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1058_; 
v_stxStack_1046_ = lean_ctor_get(v_s_1043_, 0);
v_lhsPrec_1047_ = lean_ctor_get(v_s_1043_, 1);
v_cache_1048_ = lean_ctor_get(v_s_1043_, 3);
v_recoveredErrors_1049_ = lean_ctor_get(v_s_1043_, 5);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_s_1043_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; lean_object* v_unused_1060_; 
v_unused_1059_ = lean_ctor_get(v_s_1043_, 4);
lean_dec(v_unused_1059_);
v_unused_1060_ = lean_ctor_get(v_s_1043_, 2);
lean_dec(v_unused_1060_);
v___x_1051_ = v_s_1043_;
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_recoveredErrors_1049_);
lean_inc(v_cache_1048_);
lean_inc(v_lhsPrec_1047_);
lean_inc(v_stxStack_1046_);
lean_dec(v_s_1043_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1058_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1056_; 
v___x_1053_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1046_, v_iniStackSz_1044_);
v___x_1054_ = lean_box(0);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 4, v___x_1054_);
lean_ctor_set(v___x_1051_, 2, v_iniPos_1045_);
lean_ctor_set(v___x_1051_, 0, v___x_1053_);
v___x_1056_ = v___x_1051_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_lhsPrec_1047_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_iniPos_1045_);
lean_ctor_set(v_reuseFailAlloc_1057_, 3, v_cache_1048_);
lean_ctor_set(v_reuseFailAlloc_1057_, 4, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1057_, 5, v_recoveredErrors_1049_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_1061_, lean_object* v_iniStackSz_1062_, lean_object* v_iniPos_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l_Lean_Parser_ParserState_restore(v_s_1061_, v_iniStackSz_1062_, v_iniPos_1063_);
lean_dec(v_iniStackSz_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_1065_, lean_object* v_pos_1066_){
_start:
{
lean_object* v_stxStack_1067_; lean_object* v_lhsPrec_1068_; lean_object* v_cache_1069_; lean_object* v_errorMsg_1070_; lean_object* v_recoveredErrors_1071_; lean_object* v___x_1073_; uint8_t v_isShared_1074_; uint8_t v_isSharedCheck_1078_; 
v_stxStack_1067_ = lean_ctor_get(v_s_1065_, 0);
v_lhsPrec_1068_ = lean_ctor_get(v_s_1065_, 1);
v_cache_1069_ = lean_ctor_get(v_s_1065_, 3);
v_errorMsg_1070_ = lean_ctor_get(v_s_1065_, 4);
v_recoveredErrors_1071_ = lean_ctor_get(v_s_1065_, 5);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_s_1065_);
if (v_isSharedCheck_1078_ == 0)
{
lean_object* v_unused_1079_; 
v_unused_1079_ = lean_ctor_get(v_s_1065_, 2);
lean_dec(v_unused_1079_);
v___x_1073_ = v_s_1065_;
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
else
{
lean_inc(v_recoveredErrors_1071_);
lean_inc(v_errorMsg_1070_);
lean_inc(v_cache_1069_);
lean_inc(v_lhsPrec_1068_);
lean_inc(v_stxStack_1067_);
lean_dec(v_s_1065_);
v___x_1073_ = lean_box(0);
v_isShared_1074_ = v_isSharedCheck_1078_;
goto v_resetjp_1072_;
}
v_resetjp_1072_:
{
lean_object* v___x_1076_; 
if (v_isShared_1074_ == 0)
{
lean_ctor_set(v___x_1073_, 2, v_pos_1066_);
v___x_1076_ = v___x_1073_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v_stxStack_1067_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_lhsPrec_1068_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_pos_1066_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v_cache_1069_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v_errorMsg_1070_);
lean_ctor_set(v_reuseFailAlloc_1077_, 5, v_recoveredErrors_1071_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_1080_, lean_object* v_cache_1081_){
_start:
{
lean_object* v_stxStack_1082_; lean_object* v_lhsPrec_1083_; lean_object* v_pos_1084_; lean_object* v_errorMsg_1085_; lean_object* v_recoveredErrors_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_stxStack_1082_ = lean_ctor_get(v_s_1080_, 0);
v_lhsPrec_1083_ = lean_ctor_get(v_s_1080_, 1);
v_pos_1084_ = lean_ctor_get(v_s_1080_, 2);
v_errorMsg_1085_ = lean_ctor_get(v_s_1080_, 4);
v_recoveredErrors_1086_ = lean_ctor_get(v_s_1080_, 5);
v_isSharedCheck_1093_ = !lean_is_exclusive(v_s_1080_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v_s_1080_, 3);
lean_dec(v_unused_1094_);
v___x_1088_ = v_s_1080_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_recoveredErrors_1086_);
lean_inc(v_errorMsg_1085_);
lean_inc(v_pos_1084_);
lean_inc(v_lhsPrec_1083_);
lean_inc(v_stxStack_1082_);
lean_dec(v_s_1080_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 3, v_cache_1081_);
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_stxStack_1082_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_lhsPrec_1083_);
lean_ctor_set(v_reuseFailAlloc_1092_, 2, v_pos_1084_);
lean_ctor_set(v_reuseFailAlloc_1092_, 3, v_cache_1081_);
lean_ctor_set(v_reuseFailAlloc_1092_, 4, v_errorMsg_1085_);
lean_ctor_set(v_reuseFailAlloc_1092_, 5, v_recoveredErrors_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_1095_, lean_object* v_n_1096_){
_start:
{
lean_object* v_stxStack_1097_; lean_object* v_lhsPrec_1098_; lean_object* v_pos_1099_; lean_object* v_cache_1100_; lean_object* v_errorMsg_1101_; lean_object* v_recoveredErrors_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1110_; 
v_stxStack_1097_ = lean_ctor_get(v_s_1095_, 0);
v_lhsPrec_1098_ = lean_ctor_get(v_s_1095_, 1);
v_pos_1099_ = lean_ctor_get(v_s_1095_, 2);
v_cache_1100_ = lean_ctor_get(v_s_1095_, 3);
v_errorMsg_1101_ = lean_ctor_get(v_s_1095_, 4);
v_recoveredErrors_1102_ = lean_ctor_get(v_s_1095_, 5);
v_isSharedCheck_1110_ = !lean_is_exclusive(v_s_1095_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1104_ = v_s_1095_;
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_recoveredErrors_1102_);
lean_inc(v_errorMsg_1101_);
lean_inc(v_cache_1100_);
lean_inc(v_pos_1099_);
lean_inc(v_lhsPrec_1098_);
lean_inc(v_stxStack_1097_);
lean_dec(v_s_1095_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1110_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1106_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1097_, v_n_1096_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1106_);
v___x_1108_ = v___x_1104_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v___x_1106_);
lean_ctor_set(v_reuseFailAlloc_1109_, 1, v_lhsPrec_1098_);
lean_ctor_set(v_reuseFailAlloc_1109_, 2, v_pos_1099_);
lean_ctor_set(v_reuseFailAlloc_1109_, 3, v_cache_1100_);
lean_ctor_set(v_reuseFailAlloc_1109_, 4, v_errorMsg_1101_);
lean_ctor_set(v_reuseFailAlloc_1109_, 5, v_recoveredErrors_1102_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1111_){
_start:
{
lean_object* v_stxStack_1112_; lean_object* v_lhsPrec_1113_; lean_object* v_pos_1114_; lean_object* v_cache_1115_; lean_object* v_errorMsg_1116_; lean_object* v_recoveredErrors_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1125_; 
v_stxStack_1112_ = lean_ctor_get(v_s_1111_, 0);
v_lhsPrec_1113_ = lean_ctor_get(v_s_1111_, 1);
v_pos_1114_ = lean_ctor_get(v_s_1111_, 2);
v_cache_1115_ = lean_ctor_get(v_s_1111_, 3);
v_errorMsg_1116_ = lean_ctor_get(v_s_1111_, 4);
v_recoveredErrors_1117_ = lean_ctor_get(v_s_1111_, 5);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_s_1111_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1119_ = v_s_1111_;
v_isShared_1120_ = v_isSharedCheck_1125_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_recoveredErrors_1117_);
lean_inc(v_errorMsg_1116_);
lean_inc(v_cache_1115_);
lean_inc(v_pos_1114_);
lean_inc(v_lhsPrec_1113_);
lean_inc(v_stxStack_1112_);
lean_dec(v_s_1111_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1125_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1121_; lean_object* v___x_1123_; 
v___x_1121_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1112_);
if (v_isShared_1120_ == 0)
{
lean_ctor_set(v___x_1119_, 0, v___x_1121_);
v___x_1123_ = v___x_1119_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
lean_ctor_set(v_reuseFailAlloc_1124_, 1, v_lhsPrec_1113_);
lean_ctor_set(v_reuseFailAlloc_1124_, 2, v_pos_1114_);
lean_ctor_set(v_reuseFailAlloc_1124_, 3, v_cache_1115_);
lean_ctor_set(v_reuseFailAlloc_1124_, 4, v_errorMsg_1116_);
lean_ctor_set(v_reuseFailAlloc_1124_, 5, v_recoveredErrors_1117_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1126_, lean_object* v_iniStackSz_1127_){
_start:
{
lean_object* v_stxStack_1128_; lean_object* v_lhsPrec_1129_; lean_object* v_pos_1130_; lean_object* v_cache_1131_; lean_object* v_errorMsg_1132_; lean_object* v_recoveredErrors_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_stxStack_1128_ = lean_ctor_get(v_s_1126_, 0);
v_lhsPrec_1129_ = lean_ctor_get(v_s_1126_, 1);
v_pos_1130_ = lean_ctor_get(v_s_1126_, 2);
v_cache_1131_ = lean_ctor_get(v_s_1126_, 3);
v_errorMsg_1132_ = lean_ctor_get(v_s_1126_, 4);
v_recoveredErrors_1133_ = lean_ctor_get(v_s_1126_, 5);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_s_1126_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v_s_1126_;
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_recoveredErrors_1133_);
lean_inc(v_errorMsg_1132_);
lean_inc(v_cache_1131_);
lean_inc(v_pos_1130_);
lean_inc(v_lhsPrec_1129_);
lean_inc(v_stxStack_1128_);
lean_dec(v_s_1126_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1128_, v_iniStackSz_1127_);
if (v_isShared_1136_ == 0)
{
lean_ctor_set(v___x_1135_, 0, v___x_1137_);
v___x_1139_ = v___x_1135_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v___x_1137_);
lean_ctor_set(v_reuseFailAlloc_1140_, 1, v_lhsPrec_1129_);
lean_ctor_set(v_reuseFailAlloc_1140_, 2, v_pos_1130_);
lean_ctor_set(v_reuseFailAlloc_1140_, 3, v_cache_1131_);
lean_ctor_set(v_reuseFailAlloc_1140_, 4, v_errorMsg_1132_);
lean_ctor_set(v_reuseFailAlloc_1140_, 5, v_recoveredErrors_1133_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1142_, lean_object* v_iniStackSz_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1142_, v_iniStackSz_1143_);
lean_dec(v_iniStackSz_1143_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1145_, lean_object* v_c_1146_, lean_object* v_pos_1147_){
_start:
{
lean_object* v_toInputContext_1148_; lean_object* v_stxStack_1149_; lean_object* v_lhsPrec_1150_; lean_object* v_cache_1151_; lean_object* v_errorMsg_1152_; lean_object* v_recoveredErrors_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1162_; 
v_toInputContext_1148_ = lean_ctor_get(v_c_1146_, 0);
v_stxStack_1149_ = lean_ctor_get(v_s_1145_, 0);
v_lhsPrec_1150_ = lean_ctor_get(v_s_1145_, 1);
v_cache_1151_ = lean_ctor_get(v_s_1145_, 3);
v_errorMsg_1152_ = lean_ctor_get(v_s_1145_, 4);
v_recoveredErrors_1153_ = lean_ctor_get(v_s_1145_, 5);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_s_1145_);
if (v_isSharedCheck_1162_ == 0)
{
lean_object* v_unused_1163_; 
v_unused_1163_ = lean_ctor_get(v_s_1145_, 2);
lean_dec(v_unused_1163_);
v___x_1155_ = v_s_1145_;
v_isShared_1156_ = v_isSharedCheck_1162_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_recoveredErrors_1153_);
lean_inc(v_errorMsg_1152_);
lean_inc(v_cache_1151_);
lean_inc(v_lhsPrec_1150_);
lean_inc(v_stxStack_1149_);
lean_dec(v_s_1145_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1162_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v_inputString_1157_; lean_object* v___x_1158_; lean_object* v___x_1160_; 
v_inputString_1157_ = lean_ctor_get(v_toInputContext_1148_, 0);
v___x_1158_ = lean_string_utf8_next(v_inputString_1157_, v_pos_1147_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 2, v___x_1158_);
v___x_1160_ = v___x_1155_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_stxStack_1149_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_lhsPrec_1150_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v___x_1158_);
lean_ctor_set(v_reuseFailAlloc_1161_, 3, v_cache_1151_);
lean_ctor_set(v_reuseFailAlloc_1161_, 4, v_errorMsg_1152_);
lean_ctor_set(v_reuseFailAlloc_1161_, 5, v_recoveredErrors_1153_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1164_, lean_object* v_c_1165_, lean_object* v_pos_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l_Lean_Parser_ParserState_next(v_s_1164_, v_c_1165_, v_pos_1166_);
lean_dec(v_pos_1166_);
lean_dec_ref(v_c_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1168_, lean_object* v_c_1169_, lean_object* v_pos_1170_){
_start:
{
lean_object* v_toInputContext_1171_; lean_object* v_stxStack_1172_; lean_object* v_lhsPrec_1173_; lean_object* v_cache_1174_; lean_object* v_errorMsg_1175_; lean_object* v_recoveredErrors_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1185_; 
v_toInputContext_1171_ = lean_ctor_get(v_c_1169_, 0);
v_stxStack_1172_ = lean_ctor_get(v_s_1168_, 0);
v_lhsPrec_1173_ = lean_ctor_get(v_s_1168_, 1);
v_cache_1174_ = lean_ctor_get(v_s_1168_, 3);
v_errorMsg_1175_ = lean_ctor_get(v_s_1168_, 4);
v_recoveredErrors_1176_ = lean_ctor_get(v_s_1168_, 5);
v_isSharedCheck_1185_ = !lean_is_exclusive(v_s_1168_);
if (v_isSharedCheck_1185_ == 0)
{
lean_object* v_unused_1186_; 
v_unused_1186_ = lean_ctor_get(v_s_1168_, 2);
lean_dec(v_unused_1186_);
v___x_1178_ = v_s_1168_;
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_recoveredErrors_1176_);
lean_inc(v_errorMsg_1175_);
lean_inc(v_cache_1174_);
lean_inc(v_lhsPrec_1173_);
lean_inc(v_stxStack_1172_);
lean_dec(v_s_1168_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1185_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v_inputString_1180_; lean_object* v___x_1181_; lean_object* v___x_1183_; 
v_inputString_1180_ = lean_ctor_get(v_toInputContext_1171_, 0);
v___x_1181_ = lean_string_utf8_next_fast(v_inputString_1180_, v_pos_1170_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 2, v___x_1181_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_stxStack_1172_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_lhsPrec_1173_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v___x_1181_);
lean_ctor_set(v_reuseFailAlloc_1184_, 3, v_cache_1174_);
lean_ctor_set(v_reuseFailAlloc_1184_, 4, v_errorMsg_1175_);
lean_ctor_set(v_reuseFailAlloc_1184_, 5, v_recoveredErrors_1176_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1187_, lean_object* v_c_1188_, lean_object* v_pos_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1187_, v_c_1188_, v_pos_1189_);
lean_dec(v_pos_1189_);
lean_dec_ref(v_c_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1191_, lean_object* v_c_1192_, lean_object* v_pos_1193_, lean_object* v_h_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1191_, v_c_1192_, v_pos_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1196_, lean_object* v_c_1197_, lean_object* v_pos_1198_, lean_object* v_h_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_Parser_ParserState_next_x27(v_s_1196_, v_c_1197_, v_pos_1198_, v_h_1199_);
lean_dec(v_pos_1198_);
lean_dec_ref(v_c_1197_);
return v_res_1200_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1201_, lean_object* v_x_1202_){
_start:
{
if (lean_obj_tag(v_x_1201_) == 0)
{
if (lean_obj_tag(v_x_1202_) == 0)
{
uint8_t v___x_1203_; 
v___x_1203_ = 1;
return v___x_1203_;
}
else
{
uint8_t v___x_1204_; 
v___x_1204_ = 0;
return v___x_1204_;
}
}
else
{
if (lean_obj_tag(v_x_1202_) == 0)
{
uint8_t v___x_1205_; 
v___x_1205_ = 0;
return v___x_1205_;
}
else
{
lean_object* v_val_1206_; lean_object* v_val_1207_; uint8_t v___x_1208_; 
v_val_1206_ = lean_ctor_get(v_x_1201_, 0);
v_val_1207_ = lean_ctor_get(v_x_1202_, 0);
v___x_1208_ = l_Lean_Parser_instBEqError_beq(v_val_1206_, v_val_1207_);
return v___x_1208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1209_, lean_object* v_x_1210_){
_start:
{
uint8_t v_res_1211_; lean_object* v_r_1212_; 
v_res_1211_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1209_, v_x_1210_);
lean_dec(v_x_1210_);
lean_dec(v_x_1209_);
v_r_1212_ = lean_box(v_res_1211_);
return v_r_1212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1213_, lean_object* v_k_1214_, lean_object* v_iniStackSz_1215_){
_start:
{
lean_object* v_stxStack_1216_; lean_object* v_lhsPrec_1217_; lean_object* v_pos_1218_; lean_object* v_cache_1219_; lean_object* v_errorMsg_1220_; lean_object* v_recoveredErrors_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1242_; 
v_stxStack_1216_ = lean_ctor_get(v_s_1213_, 0);
v_lhsPrec_1217_ = lean_ctor_get(v_s_1213_, 1);
v_pos_1218_ = lean_ctor_get(v_s_1213_, 2);
v_cache_1219_ = lean_ctor_get(v_s_1213_, 3);
v_errorMsg_1220_ = lean_ctor_get(v_s_1213_, 4);
v_recoveredErrors_1221_ = lean_ctor_get(v_s_1213_, 5);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_s_1213_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1223_ = v_s_1213_;
v_isShared_1224_ = v_isSharedCheck_1242_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_recoveredErrors_1221_);
lean_inc(v_errorMsg_1220_);
lean_inc(v_cache_1219_);
lean_inc(v_pos_1218_);
lean_inc(v_lhsPrec_1217_);
lean_inc(v_stxStack_1216_);
lean_dec(v_s_1213_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1242_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1235_ = lean_box(0);
v___x_1236_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1220_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_object* v___x_1237_; uint8_t v___x_1238_; 
v___x_1237_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1216_);
v___x_1238_ = lean_nat_dec_eq(v___x_1237_, v_iniStackSz_1215_);
lean_dec(v___x_1237_);
if (v___x_1238_ == 0)
{
goto v___jp_1225_;
}
else
{
lean_object* v___x_1239_; lean_object* v_stack_1240_; lean_object* v___x_1241_; 
lean_del_object(v___x_1223_);
lean_dec(v_k_1214_);
v___x_1239_ = lean_box(0);
v_stack_1240_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1216_, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1241_, 0, v_stack_1240_);
lean_ctor_set(v___x_1241_, 1, v_lhsPrec_1217_);
lean_ctor_set(v___x_1241_, 2, v_pos_1218_);
lean_ctor_set(v___x_1241_, 3, v_cache_1219_);
lean_ctor_set(v___x_1241_, 4, v_errorMsg_1220_);
lean_ctor_set(v___x_1241_, 5, v_recoveredErrors_1221_);
return v___x_1241_;
}
}
else
{
goto v___jp_1225_;
}
v___jp_1225_:
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v_newNode_1229_; lean_object* v_stack_1230_; lean_object* v_stack_1231_; lean_object* v___x_1233_; 
v___x_1226_ = lean_box(2);
v___x_1227_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1216_);
v___x_1228_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1216_, v_iniStackSz_1215_, v___x_1227_);
lean_dec(v___x_1227_);
v_newNode_1229_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1229_, 0, v___x_1226_);
lean_ctor_set(v_newNode_1229_, 1, v_k_1214_);
lean_ctor_set(v_newNode_1229_, 2, v___x_1228_);
v_stack_1230_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1216_, v_iniStackSz_1215_);
v_stack_1231_ = l_Lean_Parser_SyntaxStack_push(v_stack_1230_, v_newNode_1229_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 0, v_stack_1231_);
v___x_1233_ = v___x_1223_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_stack_1231_);
lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_lhsPrec_1217_);
lean_ctor_set(v_reuseFailAlloc_1234_, 2, v_pos_1218_);
lean_ctor_set(v_reuseFailAlloc_1234_, 3, v_cache_1219_);
lean_ctor_set(v_reuseFailAlloc_1234_, 4, v_errorMsg_1220_);
lean_ctor_set(v_reuseFailAlloc_1234_, 5, v_recoveredErrors_1221_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1243_, lean_object* v_k_1244_, lean_object* v_iniStackSz_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_Lean_Parser_ParserState_mkNode(v_s_1243_, v_k_1244_, v_iniStackSz_1245_);
lean_dec(v_iniStackSz_1245_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1247_, lean_object* v_k_1248_, lean_object* v_iniStackSz_1249_){
_start:
{
lean_object* v_stxStack_1250_; lean_object* v_lhsPrec_1251_; lean_object* v_pos_1252_; lean_object* v_cache_1253_; lean_object* v_errorMsg_1254_; lean_object* v_recoveredErrors_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1270_; 
v_stxStack_1250_ = lean_ctor_get(v_s_1247_, 0);
v_lhsPrec_1251_ = lean_ctor_get(v_s_1247_, 1);
v_pos_1252_ = lean_ctor_get(v_s_1247_, 2);
v_cache_1253_ = lean_ctor_get(v_s_1247_, 3);
v_errorMsg_1254_ = lean_ctor_get(v_s_1247_, 4);
v_recoveredErrors_1255_ = lean_ctor_get(v_s_1247_, 5);
v_isSharedCheck_1270_ = !lean_is_exclusive(v_s_1247_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1257_ = v_s_1247_;
v_isShared_1258_ = v_isSharedCheck_1270_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_recoveredErrors_1255_);
lean_inc(v_errorMsg_1254_);
lean_inc(v_cache_1253_);
lean_inc(v_pos_1252_);
lean_inc(v_lhsPrec_1251_);
lean_inc(v_stxStack_1250_);
lean_dec(v_s_1247_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1270_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v_newNode_1264_; lean_object* v_stack_1265_; lean_object* v_stack_1266_; lean_object* v___x_1268_; 
v___x_1259_ = lean_box(2);
v___x_1260_ = lean_unsigned_to_nat(1u);
v___x_1261_ = lean_nat_sub(v_iniStackSz_1249_, v___x_1260_);
v___x_1262_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1250_);
v___x_1263_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1250_, v___x_1261_, v___x_1262_);
lean_dec(v___x_1262_);
v_newNode_1264_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1264_, 0, v___x_1259_);
lean_ctor_set(v_newNode_1264_, 1, v_k_1248_);
lean_ctor_set(v_newNode_1264_, 2, v___x_1263_);
v_stack_1265_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1250_, v___x_1261_);
lean_dec(v___x_1261_);
v_stack_1266_ = l_Lean_Parser_SyntaxStack_push(v_stack_1265_, v_newNode_1264_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v_stack_1266_);
v___x_1268_ = v___x_1257_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_stack_1266_);
lean_ctor_set(v_reuseFailAlloc_1269_, 1, v_lhsPrec_1251_);
lean_ctor_set(v_reuseFailAlloc_1269_, 2, v_pos_1252_);
lean_ctor_set(v_reuseFailAlloc_1269_, 3, v_cache_1253_);
lean_ctor_set(v_reuseFailAlloc_1269_, 4, v_errorMsg_1254_);
lean_ctor_set(v_reuseFailAlloc_1269_, 5, v_recoveredErrors_1255_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1271_, lean_object* v_k_1272_, lean_object* v_iniStackSz_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1271_, v_k_1272_, v_iniStackSz_1273_);
lean_dec(v_iniStackSz_1273_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1277_){
_start:
{
lean_object* v_errorMsg_1278_; 
v_errorMsg_1278_ = lean_ctor_get(v_s_1277_, 4);
if (lean_obj_tag(v_errorMsg_1278_) == 0)
{
lean_object* v_recoveredErrors_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_recoveredErrors_1279_ = lean_ctor_get(v_s_1277_, 5);
lean_inc_ref(v_recoveredErrors_1279_);
lean_dec_ref(v_s_1277_);
v___x_1280_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1281_ = l_Array_append___redArg(v_recoveredErrors_1279_, v___x_1280_);
return v___x_1281_;
}
else
{
lean_object* v_stxStack_1282_; lean_object* v_pos_1283_; lean_object* v_recoveredErrors_1284_; lean_object* v_val_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_inc_ref(v_errorMsg_1278_);
v_stxStack_1282_ = lean_ctor_get(v_s_1277_, 0);
lean_inc_ref(v_stxStack_1282_);
v_pos_1283_ = lean_ctor_get(v_s_1277_, 2);
lean_inc(v_pos_1283_);
v_recoveredErrors_1284_ = lean_ctor_get(v_s_1277_, 5);
lean_inc_ref(v_recoveredErrors_1284_);
lean_dec_ref(v_s_1277_);
v_val_1285_ = lean_ctor_get(v_errorMsg_1278_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v_errorMsg_1278_, 1);
v___x_1286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1286_, 0, v_stxStack_1282_);
lean_ctor_set(v___x_1286_, 1, v_val_1285_);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v_pos_1283_);
lean_ctor_set(v___x_1287_, 1, v___x_1286_);
v___x_1288_ = lean_unsigned_to_nat(1u);
v___x_1289_ = lean_mk_empty_array_with_capacity(v___x_1288_);
v___x_1290_ = lean_array_push(v___x_1289_, v___x_1287_);
v___x_1291_ = l_Array_append___redArg(v_recoveredErrors_1284_, v___x_1290_);
lean_dec_ref(v___x_1290_);
return v___x_1291_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1292_, lean_object* v_e_1293_){
_start:
{
lean_object* v_stxStack_1294_; lean_object* v_lhsPrec_1295_; lean_object* v_pos_1296_; lean_object* v_cache_1297_; lean_object* v_recoveredErrors_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1306_; 
v_stxStack_1294_ = lean_ctor_get(v_s_1292_, 0);
v_lhsPrec_1295_ = lean_ctor_get(v_s_1292_, 1);
v_pos_1296_ = lean_ctor_get(v_s_1292_, 2);
v_cache_1297_ = lean_ctor_get(v_s_1292_, 3);
v_recoveredErrors_1298_ = lean_ctor_get(v_s_1292_, 5);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_s_1292_);
if (v_isSharedCheck_1306_ == 0)
{
lean_object* v_unused_1307_; 
v_unused_1307_ = lean_ctor_get(v_s_1292_, 4);
lean_dec(v_unused_1307_);
v___x_1300_ = v_s_1292_;
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_recoveredErrors_1298_);
lean_inc(v_cache_1297_);
lean_inc(v_pos_1296_);
lean_inc(v_lhsPrec_1295_);
lean_inc(v_stxStack_1294_);
lean_dec(v_s_1292_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1306_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_e_1293_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 4, v___x_1302_);
v___x_1304_ = v___x_1300_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_stxStack_1294_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v_lhsPrec_1295_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_pos_1296_);
lean_ctor_set(v_reuseFailAlloc_1305_, 3, v_cache_1297_);
lean_ctor_set(v_reuseFailAlloc_1305_, 4, v___x_1302_);
lean_ctor_set(v_reuseFailAlloc_1305_, 5, v_recoveredErrors_1298_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1308_, lean_object* v_msg_1309_){
_start:
{
lean_object* v_stxStack_1310_; lean_object* v_lhsPrec_1311_; lean_object* v_pos_1312_; lean_object* v_cache_1313_; lean_object* v_recoveredErrors_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1328_; 
v_stxStack_1310_ = lean_ctor_get(v_s_1308_, 0);
v_lhsPrec_1311_ = lean_ctor_get(v_s_1308_, 1);
v_pos_1312_ = lean_ctor_get(v_s_1308_, 2);
v_cache_1313_ = lean_ctor_get(v_s_1308_, 3);
v_recoveredErrors_1314_ = lean_ctor_get(v_s_1308_, 5);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_s_1308_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v_s_1308_, 4);
lean_dec(v_unused_1329_);
v___x_1316_ = v_s_1308_;
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_recoveredErrors_1314_);
lean_inc(v_cache_1313_);
lean_inc(v_pos_1312_);
lean_inc(v_lhsPrec_1311_);
lean_inc(v_stxStack_1310_);
lean_dec(v_s_1308_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1328_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1318_ = lean_box(0);
v___x_1319_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1320_ = lean_box(0);
v___x_1321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1321_, 0, v_msg_1309_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1318_);
lean_ctor_set(v___x_1322_, 1, v___x_1319_);
lean_ctor_set(v___x_1322_, 2, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v___x_1323_);
v___x_1325_ = v___x_1316_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_stxStack_1310_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v_lhsPrec_1311_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_pos_1312_);
lean_ctor_set(v_reuseFailAlloc_1327_, 3, v_cache_1313_);
lean_ctor_set(v_reuseFailAlloc_1327_, 4, v___x_1323_);
lean_ctor_set(v_reuseFailAlloc_1327_, 5, v_recoveredErrors_1314_);
v___x_1325_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
lean_object* v___x_1326_; 
v___x_1326_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1325_, v___x_1318_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1330_, lean_object* v_msg_1331_, lean_object* v_expected_1332_, uint8_t v_pushMissing_1333_){
_start:
{
lean_object* v_stxStack_1334_; lean_object* v_lhsPrec_1335_; lean_object* v_pos_1336_; lean_object* v_cache_1337_; lean_object* v_recoveredErrors_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1349_; 
v_stxStack_1334_ = lean_ctor_get(v_s_1330_, 0);
v_lhsPrec_1335_ = lean_ctor_get(v_s_1330_, 1);
v_pos_1336_ = lean_ctor_get(v_s_1330_, 2);
v_cache_1337_ = lean_ctor_get(v_s_1330_, 3);
v_recoveredErrors_1338_ = lean_ctor_get(v_s_1330_, 5);
v_isSharedCheck_1349_ = !lean_is_exclusive(v_s_1330_);
if (v_isSharedCheck_1349_ == 0)
{
lean_object* v_unused_1350_; 
v_unused_1350_ = lean_ctor_get(v_s_1330_, 4);
lean_dec(v_unused_1350_);
v___x_1340_ = v_s_1330_;
v_isShared_1341_ = v_isSharedCheck_1349_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_recoveredErrors_1338_);
lean_inc(v_cache_1337_);
lean_inc(v_pos_1336_);
lean_inc(v_lhsPrec_1335_);
lean_inc(v_stxStack_1334_);
lean_dec(v_s_1330_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1349_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v_s_1346_; 
v___x_1342_ = lean_box(0);
v___x_1343_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1342_);
lean_ctor_set(v___x_1343_, 1, v_msg_1331_);
lean_ctor_set(v___x_1343_, 2, v_expected_1332_);
v___x_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 4, v___x_1344_);
v_s_1346_ = v___x_1340_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_stxStack_1334_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_lhsPrec_1335_);
lean_ctor_set(v_reuseFailAlloc_1348_, 2, v_pos_1336_);
lean_ctor_set(v_reuseFailAlloc_1348_, 3, v_cache_1337_);
lean_ctor_set(v_reuseFailAlloc_1348_, 4, v___x_1344_);
lean_ctor_set(v_reuseFailAlloc_1348_, 5, v_recoveredErrors_1338_);
v_s_1346_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
if (v_pushMissing_1333_ == 0)
{
return v_s_1346_;
}
else
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1346_, v___x_1342_);
return v___x_1347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1351_, lean_object* v_msg_1352_, lean_object* v_expected_1353_, lean_object* v_pushMissing_1354_){
_start:
{
uint8_t v_pushMissing_boxed_1355_; lean_object* v_res_1356_; 
v_pushMissing_boxed_1355_ = lean_unbox(v_pushMissing_1354_);
v_res_1356_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1351_, v_msg_1352_, v_expected_1353_, v_pushMissing_boxed_1355_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1358_, lean_object* v_expected_1359_){
_start:
{
lean_object* v___x_1360_; uint8_t v___x_1361_; lean_object* v___x_1362_; 
v___x_1360_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1361_ = 1;
v___x_1362_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1358_, v___x_1360_, v_expected_1359_, v___x_1361_);
return v___x_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1363_, lean_object* v_ex_1364_, lean_object* v_pos_1365_, lean_object* v_initStackSz_x3f_1366_){
_start:
{
lean_object* v_s_1368_; lean_object* v_s_1387_; 
v_s_1387_ = l_Lean_Parser_ParserState_setPos(v_s_1363_, v_pos_1365_);
if (lean_obj_tag(v_initStackSz_x3f_1366_) == 1)
{
lean_object* v_val_1388_; lean_object* v_s_1389_; 
v_val_1388_ = lean_ctor_get(v_initStackSz_x3f_1366_, 0);
v_s_1389_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1387_, v_val_1388_);
v_s_1368_ = v_s_1389_;
goto v___jp_1367_;
}
else
{
v_s_1368_ = v_s_1387_;
goto v___jp_1367_;
}
v___jp_1367_:
{
lean_object* v_stxStack_1369_; lean_object* v_lhsPrec_1370_; lean_object* v_pos_1371_; lean_object* v_cache_1372_; lean_object* v_recoveredErrors_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1385_; 
v_stxStack_1369_ = lean_ctor_get(v_s_1368_, 0);
v_lhsPrec_1370_ = lean_ctor_get(v_s_1368_, 1);
v_pos_1371_ = lean_ctor_get(v_s_1368_, 2);
v_cache_1372_ = lean_ctor_get(v_s_1368_, 3);
v_recoveredErrors_1373_ = lean_ctor_get(v_s_1368_, 5);
v_isSharedCheck_1385_ = !lean_is_exclusive(v_s_1368_);
if (v_isSharedCheck_1385_ == 0)
{
lean_object* v_unused_1386_; 
v_unused_1386_ = lean_ctor_get(v_s_1368_, 4);
lean_dec(v_unused_1386_);
v___x_1375_ = v_s_1368_;
v_isShared_1376_ = v_isSharedCheck_1385_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_recoveredErrors_1373_);
lean_inc(v_cache_1372_);
lean_inc(v_pos_1371_);
lean_inc(v_lhsPrec_1370_);
lean_inc(v_stxStack_1369_);
lean_dec(v_s_1368_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1385_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_s_1382_; 
v___x_1377_ = lean_box(0);
v___x_1378_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1379_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
lean_ctor_set(v___x_1379_, 2, v_ex_1364_);
v___x_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1379_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 4, v___x_1380_);
v_s_1382_ = v___x_1375_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1384_; 
v_reuseFailAlloc_1384_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1384_, 0, v_stxStack_1369_);
lean_ctor_set(v_reuseFailAlloc_1384_, 1, v_lhsPrec_1370_);
lean_ctor_set(v_reuseFailAlloc_1384_, 2, v_pos_1371_);
lean_ctor_set(v_reuseFailAlloc_1384_, 3, v_cache_1372_);
lean_ctor_set(v_reuseFailAlloc_1384_, 4, v___x_1380_);
lean_ctor_set(v_reuseFailAlloc_1384_, 5, v_recoveredErrors_1373_);
v_s_1382_ = v_reuseFailAlloc_1384_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1382_, v___x_1377_);
return v___x_1383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1390_, lean_object* v_ex_1391_, lean_object* v_pos_1392_, lean_object* v_initStackSz_x3f_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1390_, v_ex_1391_, v_pos_1392_, v_initStackSz_x3f_1393_);
lean_dec(v_initStackSz_x3f_1393_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1395_, lean_object* v_msg_1396_, lean_object* v_pos_1397_, lean_object* v_initStackSz_x3f_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = lean_box(0);
v___x_1400_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_msg_1396_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1395_, v___x_1400_, v_pos_1397_, v_initStackSz_x3f_1398_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1402_, lean_object* v_msg_1403_, lean_object* v_pos_1404_, lean_object* v_initStackSz_x3f_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1402_, v_msg_1403_, v_pos_1404_, v_initStackSz_x3f_1405_);
lean_dec(v_initStackSz_x3f_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = lean_panic_fn_borrowed(v___x_1408_, v_msg_1407_);
return v___x_1409_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1413_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1414_ = lean_unsigned_to_nat(14u);
v___x_1415_ = lean_unsigned_to_nat(22u);
v___x_1416_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1417_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1418_ = l_mkPanicMessageWithDecl(v___x_1417_, v___x_1416_, v___x_1415_, v___x_1414_, v___x_1413_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1419_, lean_object* v_ex_1420_, lean_object* v_iniPos_1421_){
_start:
{
lean_object* v_stxStack_1422_; lean_object* v_tk_1423_; lean_object* v___y_1425_; lean_object* v___x_1446_; uint8_t v___x_1447_; 
v_stxStack_1422_ = lean_ctor_get(v_s_1419_, 0);
v_tk_1423_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1422_);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_dec_le(v___x_1446_, v_iniPos_1421_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
lean_dec(v_iniPos_1421_);
v___x_1448_ = l_Lean_Syntax_getPos_x3f(v_tk_1423_, v___x_1447_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1450_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1449_);
v___y_1425_ = v___x_1450_;
goto v___jp_1424_;
}
else
{
lean_object* v_val_1451_; 
v_val_1451_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_val_1451_);
lean_dec_ref_known(v___x_1448_, 1);
v___y_1425_ = v_val_1451_;
goto v___jp_1424_;
}
}
else
{
v___y_1425_ = v_iniPos_1421_;
goto v___jp_1424_;
}
v___jp_1424_:
{
lean_object* v_s_1426_; lean_object* v_stxStack_1427_; lean_object* v_lhsPrec_1428_; lean_object* v_pos_1429_; lean_object* v_cache_1430_; lean_object* v_recoveredErrors_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1444_; 
v_s_1426_ = l_Lean_Parser_ParserState_setPos(v_s_1419_, v___y_1425_);
v_stxStack_1427_ = lean_ctor_get(v_s_1426_, 0);
v_lhsPrec_1428_ = lean_ctor_get(v_s_1426_, 1);
v_pos_1429_ = lean_ctor_get(v_s_1426_, 2);
v_cache_1430_ = lean_ctor_get(v_s_1426_, 3);
v_recoveredErrors_1431_ = lean_ctor_get(v_s_1426_, 5);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_s_1426_);
if (v_isSharedCheck_1444_ == 0)
{
lean_object* v_unused_1445_; 
v_unused_1445_ = lean_ctor_get(v_s_1426_, 4);
lean_dec(v_unused_1445_);
v___x_1433_ = v_s_1426_;
v_isShared_1434_ = v_isSharedCheck_1444_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_recoveredErrors_1431_);
lean_inc(v_cache_1430_);
lean_inc(v_pos_1429_);
lean_inc(v_lhsPrec_1428_);
lean_inc(v_stxStack_1427_);
lean_dec(v_s_1426_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1444_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v_s_1439_; 
v___x_1435_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1436_, 0, v_tk_1423_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
lean_ctor_set(v___x_1436_, 2, v_ex_1420_);
v___x_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1436_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 4, v___x_1437_);
v_s_1439_ = v___x_1433_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_stxStack_1427_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_lhsPrec_1428_);
lean_ctor_set(v_reuseFailAlloc_1443_, 2, v_pos_1429_);
lean_ctor_set(v_reuseFailAlloc_1443_, 3, v_cache_1430_);
lean_ctor_set(v_reuseFailAlloc_1443_, 4, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1443_, 5, v_recoveredErrors_1431_);
v_s_1439_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1440_ = l_Lean_Parser_ParserState_popSyntax(v_s_1439_);
v___x_1441_ = lean_box(0);
v___x_1442_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1440_, v___x_1441_);
return v___x_1442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1452_, lean_object* v_msg_1453_, lean_object* v_iniPos_1454_){
_start:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1456_, 0, v_msg_1453_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1452_, v___x_1456_, v_iniPos_1454_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1458_, lean_object* v_msg_1459_, lean_object* v_pos_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; uint8_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1461_ = l_Lean_Parser_ParserState_setPos(v_s_1458_, v_pos_1460_);
v___x_1462_ = lean_box(0);
v___x_1463_ = 1;
v___x_1464_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1461_, v_msg_1459_, v___x_1462_, v___x_1463_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1466_, lean_object* v_as_1467_, size_t v_sz_1468_, size_t v_i_1469_, lean_object* v_b_1470_){
_start:
{
uint8_t v___x_1471_; 
v___x_1471_ = lean_usize_dec_lt(v_i_1469_, v_sz_1468_);
if (v___x_1471_ == 0)
{
lean_dec_ref(v_ctx_1466_);
return v_b_1470_;
}
else
{
lean_object* v_a_1472_; lean_object* v_snd_1473_; lean_object* v_fst_1474_; lean_object* v_snd_1475_; lean_object* v_errStr_1477_; lean_object* v_errStr_1488_; uint8_t v___x_1489_; 
v_a_1472_ = lean_array_uget_borrowed(v_as_1467_, v_i_1469_);
v_snd_1473_ = lean_ctor_get(v_a_1472_, 1);
v_fst_1474_ = lean_ctor_get(v_a_1472_, 0);
v_snd_1475_ = lean_ctor_get(v_snd_1473_, 1);
v_errStr_1488_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1489_ = lean_string_dec_eq(v_b_1470_, v_errStr_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1491_ = lean_string_append(v_b_1470_, v___x_1490_);
v_errStr_1477_ = v___x_1491_;
goto v___jp_1476_;
}
else
{
v_errStr_1477_ = v_b_1470_;
goto v___jp_1476_;
}
v___jp_1476_:
{
lean_object* v_fileName_1478_; lean_object* v_fileMap_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; size_t v___x_1485_; size_t v___x_1486_; 
v_fileName_1478_ = lean_ctor_get(v_ctx_1466_, 1);
v_fileMap_1479_ = lean_ctor_get(v_ctx_1466_, 2);
lean_inc_ref(v_fileMap_1479_);
v___x_1480_ = l_Lean_FileMap_toPosition(v_fileMap_1479_, v_fst_1474_);
lean_inc(v_snd_1475_);
v___x_1481_ = l_Lean_Parser_Error_toString(v_snd_1475_);
v___x_1482_ = lean_box(0);
lean_inc_ref(v_fileName_1478_);
v___x_1483_ = l_Lean_mkErrorStringWithPos(v_fileName_1478_, v___x_1480_, v___x_1481_, v___x_1482_, v___x_1482_, v___x_1482_);
lean_dec_ref(v___x_1481_);
v___x_1484_ = lean_string_append(v_errStr_1477_, v___x_1483_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = ((size_t)1ULL);
v___x_1486_ = lean_usize_add(v_i_1469_, v___x_1485_);
v_i_1469_ = v___x_1486_;
v_b_1470_ = v___x_1484_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1492_, lean_object* v_as_1493_, lean_object* v_sz_1494_, lean_object* v_i_1495_, lean_object* v_b_1496_){
_start:
{
size_t v_sz_boxed_1497_; size_t v_i_boxed_1498_; lean_object* v_res_1499_; 
v_sz_boxed_1497_ = lean_unbox_usize(v_sz_1494_);
lean_dec(v_sz_1494_);
v_i_boxed_1498_ = lean_unbox_usize(v_i_1495_);
lean_dec(v_i_1495_);
v_res_1499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1492_, v_as_1493_, v_sz_boxed_1497_, v_i_boxed_1498_, v_b_1496_);
lean_dec_ref(v_as_1493_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1500_, lean_object* v_s_1501_){
_start:
{
lean_object* v_errStr_1502_; lean_object* v___x_1503_; size_t v_sz_1504_; size_t v___x_1505_; lean_object* v___x_1506_; 
v_errStr_1502_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1503_ = l_Lean_Parser_ParserState_allErrors(v_s_1501_);
v_sz_1504_ = lean_array_size(v___x_1503_);
v___x_1505_ = ((size_t)0ULL);
v___x_1506_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1500_, v___x_1503_, v_sz_1504_, v___x_1505_, v_errStr_1502_);
lean_dec_ref(v___x_1503_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1507_, lean_object* v_s_1508_){
_start:
{
lean_inc_ref(v_s_1508_);
return v_s_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1509_, lean_object* v_s_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1509_, v_s_1510_);
lean_dec_ref(v_s_1510_);
lean_dec_ref(v_x_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx(lean_object* v_x_1514_){
_start:
{
switch(lean_obj_tag(v_x_1514_))
{
case 0:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_unsigned_to_nat(0u);
return v___x_1515_;
}
case 1:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_unsigned_to_nat(1u);
return v___x_1516_;
}
case 2:
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_unsigned_to_nat(2u);
return v___x_1517_;
}
default: 
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_unsigned_to_nat(3u);
return v___x_1518_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___boxed(lean_object* v_x_1519_){
_start:
{
lean_object* v_res_1520_; 
v_res_1520_ = l_Lean_Parser_FirstTokens_ctorIdx(v_x_1519_);
lean_dec(v_x_1519_);
return v_res_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1521_, lean_object* v_k_1522_){
_start:
{
switch(lean_obj_tag(v_t_1521_))
{
case 2:
{
lean_object* v_a_1523_; lean_object* v___x_1524_; 
v_a_1523_ = lean_ctor_get(v_t_1521_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v_t_1521_, 1);
v___x_1524_ = lean_apply_1(v_k_1522_, v_a_1523_);
return v___x_1524_;
}
case 3:
{
lean_object* v_a_1525_; lean_object* v___x_1526_; 
v_a_1525_ = lean_ctor_get(v_t_1521_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v_t_1521_, 1);
v___x_1526_ = lean_apply_1(v_k_1522_, v_a_1525_);
return v___x_1526_;
}
default: 
{
lean_dec(v_t_1521_);
return v_k_1522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1527_, lean_object* v_ctorIdx_1528_, lean_object* v_t_1529_, lean_object* v_h_1530_, lean_object* v_k_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1529_, v_k_1531_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1533_, lean_object* v_ctorIdx_1534_, lean_object* v_t_1535_, lean_object* v_h_1536_, lean_object* v_k_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1533_, v_ctorIdx_1534_, v_t_1535_, v_h_1536_, v_k_1537_);
lean_dec(v_ctorIdx_1534_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1539_, lean_object* v_epsilon_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1539_, v_epsilon_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1542_, lean_object* v_t_1543_, lean_object* v_h_1544_, lean_object* v_epsilon_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1543_, v_epsilon_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1547_, lean_object* v_unknown_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1547_, v_unknown_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1550_, lean_object* v_t_1551_, lean_object* v_h_1552_, lean_object* v_unknown_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1551_, v_unknown_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1555_, lean_object* v_tokens_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1555_, v_tokens_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1558_, lean_object* v_t_1559_, lean_object* v_h_1560_, lean_object* v_tokens_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1559_, v_tokens_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1563_, lean_object* v_optTokens_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1563_, v_optTokens_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1566_, lean_object* v_t_1567_, lean_object* v_h_1568_, lean_object* v_optTokens_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1567_, v_optTokens_1569_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = lean_box(0);
return v___x_1571_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = lean_box(0);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1573_, lean_object* v_x_1574_){
_start:
{
switch(lean_obj_tag(v_x_1573_))
{
case 0:
{
return v_x_1574_;
}
case 3:
{
switch(lean_obj_tag(v_x_1574_))
{
case 3:
{
lean_object* v_a_1575_; lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1584_; 
v_a_1575_ = lean_ctor_get(v_x_1573_, 0);
lean_inc(v_a_1575_);
lean_dec_ref_known(v_x_1573_, 1);
v_a_1576_ = lean_ctor_get(v_x_1574_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_x_1574_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1578_ = v_x_1574_;
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v_x_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1584_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1580_; lean_object* v___x_1582_; 
v___x_1580_ = l_List_appendTR___redArg(v_a_1575_, v_a_1576_);
if (v_isShared_1579_ == 0)
{
lean_ctor_set(v___x_1578_, 0, v___x_1580_);
v___x_1582_ = v___x_1578_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v___x_1580_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
case 2:
{
lean_object* v_a_1585_; lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1594_; 
v_a_1585_ = lean_ctor_get(v_x_1573_, 0);
lean_inc(v_a_1585_);
lean_dec_ref_known(v_x_1573_, 1);
v_a_1586_ = lean_ctor_get(v_x_1574_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_x_1574_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1588_ = v_x_1574_;
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v_x_1574_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1594_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; lean_object* v___x_1592_; 
v___x_1590_ = l_List_appendTR___redArg(v_a_1585_, v_a_1586_);
if (v_isShared_1589_ == 0)
{
lean_ctor_set(v___x_1588_, 0, v___x_1590_);
v___x_1592_ = v___x_1588_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1590_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
case 1:
{
lean_dec_ref_known(v_x_1573_, 1);
return v_x_1574_;
}
default: 
{
lean_dec(v_x_1574_);
return v_x_1573_;
}
}
}
default: 
{
lean_dec(v_x_1574_);
return v_x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1595_){
_start:
{
if (lean_obj_tag(v_x_1595_) == 2)
{
lean_object* v_a_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1603_; 
v_a_1596_ = lean_ctor_get(v_x_1595_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_x_1595_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1598_ = v_x_1595_;
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_a_1596_);
lean_dec(v_x_1595_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1603_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1601_; 
if (v_isShared_1599_ == 0)
{
lean_ctor_set_tag(v___x_1598_, 3);
v___x_1601_ = v___x_1598_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_a_1596_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
else
{
return v_x_1595_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
lean_object* v_s_u2081_1607_; lean_object* v_s_u2082_1608_; 
switch(lean_obj_tag(v_x_1604_))
{
case 0:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1605_);
return v___x_1611_;
}
case 2:
{
switch(lean_obj_tag(v_x_1605_))
{
case 0:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1604_);
return v___x_1612_;
}
case 2:
{
lean_object* v_a_1613_; lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1622_; 
v_a_1613_ = lean_ctor_get(v_x_1604_, 0);
lean_inc(v_a_1613_);
lean_dec_ref_known(v_x_1604_, 1);
v_a_1614_ = lean_ctor_get(v_x_1605_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v_x_1605_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1616_ = v_x_1605_;
v_isShared_1617_ = v_isSharedCheck_1622_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v_x_1605_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1622_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1618_ = l_List_appendTR___redArg(v_a_1613_, v_a_1614_);
if (v_isShared_1617_ == 0)
{
lean_ctor_set(v___x_1616_, 0, v___x_1618_);
v___x_1620_ = v___x_1616_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
case 3:
{
lean_object* v_a_1623_; lean_object* v_a_1624_; 
v_a_1623_ = lean_ctor_get(v_x_1604_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v_x_1604_, 1);
v_a_1624_ = lean_ctor_get(v_x_1605_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v_x_1605_, 1);
v_s_u2081_1607_ = v_a_1623_;
v_s_u2082_1608_ = v_a_1624_;
goto v___jp_1606_;
}
default: 
{
lean_object* v___x_1625_; 
lean_dec_ref_known(v_x_1604_, 1);
lean_dec(v_x_1605_);
v___x_1625_ = lean_box(1);
return v___x_1625_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1605_))
{
case 0:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1604_);
return v___x_1626_;
}
case 3:
{
lean_object* v_a_1627_; lean_object* v_a_1628_; 
v_a_1627_ = lean_ctor_get(v_x_1604_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v_x_1604_, 1);
v_a_1628_ = lean_ctor_get(v_x_1605_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v_x_1605_, 1);
v_s_u2081_1607_ = v_a_1627_;
v_s_u2082_1608_ = v_a_1628_;
goto v___jp_1606_;
}
case 2:
{
lean_object* v_a_1629_; lean_object* v_a_1630_; 
v_a_1629_ = lean_ctor_get(v_x_1604_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v_x_1604_, 1);
v_a_1630_ = lean_ctor_get(v_x_1605_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v_x_1605_, 1);
v_s_u2081_1607_ = v_a_1629_;
v_s_u2082_1608_ = v_a_1630_;
goto v___jp_1606_;
}
default: 
{
lean_object* v___x_1631_; 
lean_dec_ref_known(v_x_1604_, 1);
lean_dec(v_x_1605_);
v___x_1631_ = lean_box(1);
return v___x_1631_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1605_) == 0)
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1604_);
return v___x_1632_;
}
else
{
lean_object* v___x_1633_; 
lean_dec(v_x_1605_);
lean_dec(v_x_1604_);
v___x_1633_ = lean_box(1);
return v___x_1633_;
}
}
}
v___jp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
v___x_1609_ = l_List_appendTR___redArg(v_s_u2081_1607_, v_s_u2082_1608_);
v___x_1610_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
if (lean_obj_tag(v_x_1635_) == 0)
{
return v_x_1634_;
}
else
{
lean_object* v_head_1636_; lean_object* v_tail_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_head_1636_ = lean_ctor_get(v_x_1635_, 0);
v_tail_1637_ = lean_ctor_get(v_x_1635_, 1);
v___x_1638_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1639_ = lean_string_append(v_x_1634_, v___x_1638_);
v___x_1640_ = lean_string_append(v___x_1639_, v_head_1636_);
v_x_1634_ = v___x_1640_;
v_x_1635_ = v_tail_1637_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1642_, lean_object* v_x_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1642_, v_x_1643_);
lean_dec(v_x_1643_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1648_){
_start:
{
if (lean_obj_tag(v_x_1648_) == 0)
{
lean_object* v___x_1649_; 
v___x_1649_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1649_;
}
else
{
lean_object* v_tail_1650_; 
v_tail_1650_ = lean_ctor_get(v_x_1648_, 1);
if (lean_obj_tag(v_tail_1650_) == 0)
{
lean_object* v_head_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v_head_1651_ = lean_ctor_get(v_x_1648_, 0);
v___x_1652_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1653_ = lean_string_append(v___x_1652_, v_head_1651_);
v___x_1654_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1655_ = lean_string_append(v___x_1653_, v___x_1654_);
return v___x_1655_;
}
else
{
lean_object* v_head_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; uint32_t v___x_1660_; lean_object* v___x_1661_; 
v_head_1656_ = lean_ctor_get(v_x_1648_, 0);
v___x_1657_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1658_ = lean_string_append(v___x_1657_, v_head_1656_);
v___x_1659_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1658_, v_tail_1650_);
v___x_1660_ = 93;
v___x_1661_ = lean_string_push(v___x_1659_, v___x_1660_);
return v___x_1661_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1662_);
lean_dec(v_x_1662_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1667_){
_start:
{
switch(lean_obj_tag(v_x_1667_))
{
case 0:
{
lean_object* v___x_1668_; 
v___x_1668_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1668_;
}
case 1:
{
lean_object* v___x_1669_; 
v___x_1669_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1669_;
}
case 2:
{
lean_object* v_a_1670_; lean_object* v___x_1671_; 
v_a_1670_ = lean_ctor_get(v_x_1667_, 0);
v___x_1671_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1670_);
return v___x_1671_;
}
default: 
{
lean_object* v_a_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
v_a_1672_ = lean_ctor_get(v_x_1667_, 0);
v___x_1673_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1674_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1672_);
v___x_1675_ = lean_string_append(v___x_1673_, v___x_1674_);
lean_dec_ref(v___x_1674_);
return v___x_1675_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Lean_Parser_FirstTokens_toStr(v_x_1676_);
lean_dec(v_x_1676_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v___y_1680_){
_start:
{
lean_inc(v___y_1680_);
return v___y_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v___y_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_1681_);
lean_dec(v___y_1681_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v___y_1683_){
_start:
{
lean_inc_ref(v___y_1683_);
return v___y_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_1684_);
lean_dec_ref(v___y_1684_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1699_, lean_object* v_p_1700_){
_start:
{
lean_object* v_info_1701_; lean_object* v_fn_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1710_; 
v_info_1701_ = lean_ctor_get(v_p_1700_, 0);
v_fn_1702_ = lean_ctor_get(v_p_1700_, 1);
v_isSharedCheck_1710_ = !lean_is_exclusive(v_p_1700_);
if (v_isSharedCheck_1710_ == 0)
{
v___x_1704_ = v_p_1700_;
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_fn_1702_);
lean_inc(v_info_1701_);
lean_dec(v_p_1700_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1710_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v___x_1706_; lean_object* v___x_1708_; 
v___x_1706_ = lean_apply_1(v_f_1699_, v_fn_1702_);
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 1, v___x_1706_);
v___x_1708_ = v___x_1704_;
goto v_reusejp_1707_;
}
else
{
lean_object* v_reuseFailAlloc_1709_; 
v_reuseFailAlloc_1709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1709_, 0, v_info_1701_);
lean_ctor_set(v_reuseFailAlloc_1709_, 1, v___x_1706_);
v___x_1708_ = v_reuseFailAlloc_1709_;
goto v_reusejp_1707_;
}
v_reusejp_1707_:
{
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1711_, lean_object* v_p_1712_, lean_object* v_c_1713_, lean_object* v_s_1714_){
_start:
{
lean_object* v_toInputContext_1715_; lean_object* v_toParserModuleContext_1716_; lean_object* v_toCacheableParserContext_1717_; lean_object* v_tokens_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1727_; 
v_toInputContext_1715_ = lean_ctor_get(v_c_1713_, 0);
v_toParserModuleContext_1716_ = lean_ctor_get(v_c_1713_, 1);
v_toCacheableParserContext_1717_ = lean_ctor_get(v_c_1713_, 2);
v_tokens_1718_ = lean_ctor_get(v_c_1713_, 3);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_c_1713_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1720_ = v_c_1713_;
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_tokens_1718_);
lean_inc(v_toCacheableParserContext_1717_);
lean_inc(v_toParserModuleContext_1716_);
lean_inc(v_toInputContext_1715_);
lean_dec(v_c_1713_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1727_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = lean_apply_1(v_f_1711_, v_toCacheableParserContext_1717_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 2, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_toInputContext_1715_);
lean_ctor_set(v_reuseFailAlloc_1726_, 1, v_toParserModuleContext_1716_);
lean_ctor_set(v_reuseFailAlloc_1726_, 2, v___x_1722_);
lean_ctor_set(v_reuseFailAlloc_1726_, 3, v_tokens_1718_);
v___x_1724_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
lean_object* v___x_1725_; 
v___x_1725_ = lean_apply_2(v_p_1712_, v___x_1724_, v_s_1714_);
return v___x_1725_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1728_, lean_object* v_p_1729_){
_start:
{
lean_object* v_info_1730_; lean_object* v_fn_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1739_; 
v_info_1730_ = lean_ctor_get(v_p_1729_, 0);
v_fn_1731_ = lean_ctor_get(v_p_1729_, 1);
v_isSharedCheck_1739_ = !lean_is_exclusive(v_p_1729_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1733_ = v_p_1729_;
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_fn_1731_);
lean_inc(v_info_1730_);
lean_dec(v_p_1729_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1739_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1735_; lean_object* v___x_1737_; 
v___x_1735_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1735_, 0, v_f_1728_);
lean_closure_set(v___x_1735_, 1, v_fn_1731_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v___x_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_info_1730_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v___x_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1740_, lean_object* v_p_1741_, lean_object* v_c_1742_, lean_object* v_s_1743_){
_start:
{
lean_object* v_stxStack_1744_; lean_object* v_lhsPrec_1745_; lean_object* v_pos_1746_; lean_object* v_cache_1747_; lean_object* v_errorMsg_1748_; lean_object* v_recoveredErrors_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1788_; 
v_stxStack_1744_ = lean_ctor_get(v_s_1743_, 0);
v_lhsPrec_1745_ = lean_ctor_get(v_s_1743_, 1);
v_pos_1746_ = lean_ctor_get(v_s_1743_, 2);
v_cache_1747_ = lean_ctor_get(v_s_1743_, 3);
v_errorMsg_1748_ = lean_ctor_get(v_s_1743_, 4);
v_recoveredErrors_1749_ = lean_ctor_get(v_s_1743_, 5);
v_isSharedCheck_1788_ = !lean_is_exclusive(v_s_1743_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1751_ = v_s_1743_;
v_isShared_1752_ = v_isSharedCheck_1788_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_recoveredErrors_1749_);
lean_inc(v_errorMsg_1748_);
lean_inc(v_cache_1747_);
lean_inc(v_pos_1746_);
lean_inc(v_lhsPrec_1745_);
lean_inc(v_stxStack_1744_);
lean_dec(v_s_1743_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1788_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v_raw_1753_; lean_object* v_drop_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1787_; 
v_raw_1753_ = lean_ctor_get(v_stxStack_1744_, 0);
v_drop_1754_ = lean_ctor_get(v_stxStack_1744_, 1);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_stxStack_1744_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1756_ = v_stxStack_1744_;
v_isShared_1757_ = v_isSharedCheck_1787_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_drop_1754_);
lean_inc(v_raw_1753_);
lean_dec(v_stxStack_1744_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1787_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 1, v_drop_1740_);
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_raw_1753_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_drop_1740_);
v___x_1759_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v___x_1761_; 
if (v_isShared_1752_ == 0)
{
lean_ctor_set(v___x_1751_, 0, v___x_1759_);
v___x_1761_ = v___x_1751_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1759_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_lhsPrec_1745_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_pos_1746_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_cache_1747_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v_errorMsg_1748_);
lean_ctor_set(v_reuseFailAlloc_1785_, 5, v_recoveredErrors_1749_);
v___x_1761_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v_s_1762_; lean_object* v_stxStack_1763_; lean_object* v_lhsPrec_1764_; lean_object* v_pos_1765_; lean_object* v_cache_1766_; lean_object* v_errorMsg_1767_; lean_object* v_recoveredErrors_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1784_; 
v_s_1762_ = lean_apply_2(v_p_1741_, v_c_1742_, v___x_1761_);
v_stxStack_1763_ = lean_ctor_get(v_s_1762_, 0);
v_lhsPrec_1764_ = lean_ctor_get(v_s_1762_, 1);
v_pos_1765_ = lean_ctor_get(v_s_1762_, 2);
v_cache_1766_ = lean_ctor_get(v_s_1762_, 3);
v_errorMsg_1767_ = lean_ctor_get(v_s_1762_, 4);
v_recoveredErrors_1768_ = lean_ctor_get(v_s_1762_, 5);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_s_1762_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1770_ = v_s_1762_;
v_isShared_1771_ = v_isSharedCheck_1784_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_recoveredErrors_1768_);
lean_inc(v_errorMsg_1767_);
lean_inc(v_cache_1766_);
lean_inc(v_pos_1765_);
lean_inc(v_lhsPrec_1764_);
lean_inc(v_stxStack_1763_);
lean_dec(v_s_1762_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1784_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v_raw_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1782_; 
v_raw_1772_ = lean_ctor_get(v_stxStack_1763_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_stxStack_1763_);
if (v_isSharedCheck_1782_ == 0)
{
lean_object* v_unused_1783_; 
v_unused_1783_ = lean_ctor_get(v_stxStack_1763_, 1);
lean_dec(v_unused_1783_);
v___x_1774_ = v_stxStack_1763_;
v_isShared_1775_ = v_isSharedCheck_1782_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_raw_1772_);
lean_dec(v_stxStack_1763_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1782_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
lean_ctor_set(v___x_1774_, 1, v_drop_1754_);
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_raw_1772_);
lean_ctor_set(v_reuseFailAlloc_1781_, 1, v_drop_1754_);
v___x_1777_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v___x_1779_; 
if (v_isShared_1771_ == 0)
{
lean_ctor_set(v___x_1770_, 0, v___x_1777_);
v___x_1779_ = v___x_1770_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v___x_1777_);
lean_ctor_set(v_reuseFailAlloc_1780_, 1, v_lhsPrec_1764_);
lean_ctor_set(v_reuseFailAlloc_1780_, 2, v_pos_1765_);
lean_ctor_set(v_reuseFailAlloc_1780_, 3, v_cache_1766_);
lean_ctor_set(v_reuseFailAlloc_1780_, 4, v_errorMsg_1767_);
lean_ctor_set(v_reuseFailAlloc_1780_, 5, v_recoveredErrors_1768_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1789_, lean_object* v_c_1790_, lean_object* v_s_1791_){
_start:
{
lean_object* v_cache_1792_; lean_object* v_stxStack_1793_; lean_object* v_lhsPrec_1794_; lean_object* v_pos_1795_; lean_object* v_errorMsg_1796_; lean_object* v_recoveredErrors_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1837_; 
v_cache_1792_ = lean_ctor_get(v_s_1791_, 3);
v_stxStack_1793_ = lean_ctor_get(v_s_1791_, 0);
v_lhsPrec_1794_ = lean_ctor_get(v_s_1791_, 1);
v_pos_1795_ = lean_ctor_get(v_s_1791_, 2);
v_errorMsg_1796_ = lean_ctor_get(v_s_1791_, 4);
v_recoveredErrors_1797_ = lean_ctor_get(v_s_1791_, 5);
v_isSharedCheck_1837_ = !lean_is_exclusive(v_s_1791_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1799_ = v_s_1791_;
v_isShared_1800_ = v_isSharedCheck_1837_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_recoveredErrors_1797_);
lean_inc(v_errorMsg_1796_);
lean_inc(v_cache_1792_);
lean_inc(v_pos_1795_);
lean_inc(v_lhsPrec_1794_);
lean_inc(v_stxStack_1793_);
lean_dec(v_s_1791_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1837_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v_tokenCache_1801_; lean_object* v_parserCache_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1836_; 
v_tokenCache_1801_ = lean_ctor_get(v_cache_1792_, 0);
v_parserCache_1802_ = lean_ctor_get(v_cache_1792_, 1);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_cache_1792_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1804_ = v_cache_1792_;
v_isShared_1805_ = v_isSharedCheck_1836_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_parserCache_1802_);
lean_inc(v_tokenCache_1801_);
lean_dec(v_cache_1792_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1836_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v___x_1806_; lean_object* v___x_1808_; 
v___x_1806_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 1, v___x_1806_);
v___x_1808_ = v___x_1804_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_tokenCache_1801_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v___x_1806_);
v___x_1808_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v___x_1810_; 
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 3, v___x_1808_);
v___x_1810_ = v___x_1799_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_stxStack_1793_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_lhsPrec_1794_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_pos_1795_);
lean_ctor_set(v_reuseFailAlloc_1834_, 3, v___x_1808_);
lean_ctor_set(v_reuseFailAlloc_1834_, 4, v_errorMsg_1796_);
lean_ctor_set(v_reuseFailAlloc_1834_, 5, v_recoveredErrors_1797_);
v___x_1810_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v_s_x27_1811_; lean_object* v_cache_1812_; lean_object* v_stxStack_1813_; lean_object* v_lhsPrec_1814_; lean_object* v_pos_1815_; lean_object* v_errorMsg_1816_; lean_object* v_recoveredErrors_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1833_; 
v_s_x27_1811_ = lean_apply_2(v_p_1789_, v_c_1790_, v___x_1810_);
v_cache_1812_ = lean_ctor_get(v_s_x27_1811_, 3);
v_stxStack_1813_ = lean_ctor_get(v_s_x27_1811_, 0);
v_lhsPrec_1814_ = lean_ctor_get(v_s_x27_1811_, 1);
v_pos_1815_ = lean_ctor_get(v_s_x27_1811_, 2);
v_errorMsg_1816_ = lean_ctor_get(v_s_x27_1811_, 4);
v_recoveredErrors_1817_ = lean_ctor_get(v_s_x27_1811_, 5);
v_isSharedCheck_1833_ = !lean_is_exclusive(v_s_x27_1811_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1819_ = v_s_x27_1811_;
v_isShared_1820_ = v_isSharedCheck_1833_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_recoveredErrors_1817_);
lean_inc(v_errorMsg_1816_);
lean_inc(v_cache_1812_);
lean_inc(v_pos_1815_);
lean_inc(v_lhsPrec_1814_);
lean_inc(v_stxStack_1813_);
lean_dec(v_s_x27_1811_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1833_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_tokenCache_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1831_; 
v_tokenCache_1821_ = lean_ctor_get(v_cache_1812_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_cache_1812_);
if (v_isSharedCheck_1831_ == 0)
{
lean_object* v_unused_1832_; 
v_unused_1832_ = lean_ctor_get(v_cache_1812_, 1);
lean_dec(v_unused_1832_);
v___x_1823_ = v_cache_1812_;
v_isShared_1824_ = v_isSharedCheck_1831_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_tokenCache_1821_);
lean_dec(v_cache_1812_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1831_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v___x_1826_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 1, v_parserCache_1802_);
v___x_1826_ = v___x_1823_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_tokenCache_1821_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v_parserCache_1802_);
v___x_1826_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1828_; 
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 3, v___x_1826_);
v___x_1828_ = v___x_1819_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_stxStack_1813_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v_lhsPrec_1814_);
lean_ctor_set(v_reuseFailAlloc_1829_, 2, v_pos_1815_);
lean_ctor_set(v_reuseFailAlloc_1829_, 3, v___x_1826_);
lean_ctor_set(v_reuseFailAlloc_1829_, 4, v_errorMsg_1816_);
lean_ctor_set(v_reuseFailAlloc_1829_, 5, v_recoveredErrors_1817_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_){
_start:
{
lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___f_1841_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1841_, 0, v_p_1838_);
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1842_, v___f_1841_, v_a_1839_, v_a_1840_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1844_){
_start:
{
lean_object* v_info_1845_; lean_object* v_fn_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1854_; 
v_info_1845_ = lean_ctor_get(v_p_1844_, 0);
v_fn_1846_ = lean_ctor_get(v_p_1844_, 1);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_p_1844_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1848_ = v_p_1844_;
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_fn_1846_);
lean_inc(v_info_1845_);
lean_dec(v_p_1844_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1850_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1850_, 0, v_fn_1846_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 1, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_info_1845_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1855_, lean_object* v_p_1856_, lean_object* v_c_1857_, lean_object* v_s_1858_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = lean_apply_1(v_f_1855_, v_c_1857_);
v___x_1860_ = lean_apply_2(v_p_1856_, v___x_1859_, v_s_1858_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1861_, lean_object* v_p_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v___f_1865_; lean_object* v___x_1866_; 
v___f_1865_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1865_, 0, v_f_1861_);
lean_closure_set(v___f_1865_, 1, v_p_1862_);
v___x_1866_ = l_Lean_Parser_withResetCacheFn(v___f_1865_, v_a_1863_, v_a_1864_);
return v___x_1866_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1867_, lean_object* v_x_1868_){
_start:
{
if (lean_obj_tag(v_x_1868_) == 0)
{
uint8_t v___x_1869_; 
v___x_1869_ = 0;
return v___x_1869_;
}
else
{
lean_object* v_key_1870_; lean_object* v_tail_1871_; uint8_t v___x_1872_; 
v_key_1870_ = lean_ctor_get(v_x_1868_, 0);
v_tail_1871_ = lean_ctor_get(v_x_1868_, 2);
v___x_1872_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1870_, v_a_1867_);
if (v___x_1872_ == 0)
{
v_x_1868_ = v_tail_1871_;
goto _start;
}
else
{
return v___x_1872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1874_, lean_object* v_x_1875_){
_start:
{
uint8_t v_res_1876_; lean_object* v_r_1877_; 
v_res_1876_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1874_, v_x_1875_);
lean_dec(v_x_1875_);
lean_dec_ref(v_a_1874_);
v_r_1877_ = lean_box(v_res_1876_);
return v_r_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
return v_x_1878_;
}
else
{
lean_object* v_key_1880_; lean_object* v_value_1881_; lean_object* v_tail_1882_; lean_object* v___x_1884_; uint8_t v_isShared_1885_; uint8_t v_isSharedCheck_1912_; 
v_key_1880_ = lean_ctor_get(v_x_1879_, 0);
v_value_1881_ = lean_ctor_get(v_x_1879_, 1);
v_tail_1882_ = lean_ctor_get(v_x_1879_, 2);
v_isSharedCheck_1912_ = !lean_is_exclusive(v_x_1879_);
if (v_isSharedCheck_1912_ == 0)
{
v___x_1884_ = v_x_1879_;
v_isShared_1885_ = v_isSharedCheck_1912_;
goto v_resetjp_1883_;
}
else
{
lean_inc(v_tail_1882_);
lean_inc(v_value_1881_);
lean_inc(v_key_1880_);
lean_dec(v_x_1879_);
v___x_1884_ = lean_box(0);
v_isShared_1885_ = v_isSharedCheck_1912_;
goto v_resetjp_1883_;
}
v_resetjp_1883_:
{
lean_object* v_parserName_1886_; lean_object* v_pos_1887_; lean_object* v___x_1888_; uint64_t v___x_1889_; uint64_t v___y_1891_; 
v_parserName_1886_ = lean_ctor_get(v_key_1880_, 1);
v_pos_1887_ = lean_ctor_get(v_key_1880_, 2);
v___x_1888_ = lean_array_get_size(v_x_1878_);
v___x_1889_ = l_String_instHashableRaw_hash(v_pos_1887_);
if (lean_obj_tag(v_parserName_1886_) == 0)
{
uint64_t v___x_1910_; 
v___x_1910_ = 1723ULL;
v___y_1891_ = v___x_1910_;
goto v___jp_1890_;
}
else
{
uint64_t v_hash_1911_; 
v_hash_1911_ = lean_ctor_get_uint64(v_parserName_1886_, sizeof(void*)*2);
v___y_1891_ = v_hash_1911_;
goto v___jp_1890_;
}
v___jp_1890_:
{
uint64_t v___x_1892_; uint64_t v___x_1893_; uint64_t v___x_1894_; uint64_t v_fold_1895_; uint64_t v___x_1896_; uint64_t v___x_1897_; uint64_t v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; size_t v___x_1901_; size_t v___x_1902_; size_t v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v___x_1892_ = lean_uint64_mix_hash(v___x_1889_, v___y_1891_);
v___x_1893_ = 32ULL;
v___x_1894_ = lean_uint64_shift_right(v___x_1892_, v___x_1893_);
v_fold_1895_ = lean_uint64_xor(v___x_1892_, v___x_1894_);
v___x_1896_ = 16ULL;
v___x_1897_ = lean_uint64_shift_right(v_fold_1895_, v___x_1896_);
v___x_1898_ = lean_uint64_xor(v_fold_1895_, v___x_1897_);
v___x_1899_ = lean_uint64_to_usize(v___x_1898_);
v___x_1900_ = lean_usize_of_nat(v___x_1888_);
v___x_1901_ = ((size_t)1ULL);
v___x_1902_ = lean_usize_sub(v___x_1900_, v___x_1901_);
v___x_1903_ = lean_usize_land(v___x_1899_, v___x_1902_);
v___x_1904_ = lean_array_uget_borrowed(v_x_1878_, v___x_1903_);
lean_inc(v___x_1904_);
if (v_isShared_1885_ == 0)
{
lean_ctor_set(v___x_1884_, 2, v___x_1904_);
v___x_1906_ = v___x_1884_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_key_1880_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_value_1881_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_array_uset(v_x_1878_, v___x_1903_, v___x_1906_);
v_x_1878_ = v___x_1907_;
v_x_1879_ = v_tail_1882_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1913_, lean_object* v_source_1914_, lean_object* v_target_1915_){
_start:
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = lean_array_get_size(v_source_1914_);
v___x_1917_ = lean_nat_dec_lt(v_i_1913_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_dec_ref(v_source_1914_);
lean_dec(v_i_1913_);
return v_target_1915_;
}
else
{
lean_object* v_es_1918_; lean_object* v___x_1919_; lean_object* v_source_1920_; lean_object* v_target_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v_es_1918_ = lean_array_fget(v_source_1914_, v_i_1913_);
v___x_1919_ = lean_box(0);
v_source_1920_ = lean_array_fset(v_source_1914_, v_i_1913_, v___x_1919_);
v_target_1921_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1915_, v_es_1918_);
v___x_1922_ = lean_unsigned_to_nat(1u);
v___x_1923_ = lean_nat_add(v_i_1913_, v___x_1922_);
lean_dec(v_i_1913_);
v_i_1913_ = v___x_1923_;
v_source_1914_ = v_source_1920_;
v_target_1915_ = v_target_1921_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1925_){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v_nbuckets_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1926_ = lean_array_get_size(v_data_1925_);
v___x_1927_ = lean_unsigned_to_nat(2u);
v_nbuckets_1928_ = lean_nat_mul(v___x_1926_, v___x_1927_);
v___x_1929_ = lean_unsigned_to_nat(0u);
v___x_1930_ = lean_box(0);
v___x_1931_ = lean_mk_array(v_nbuckets_1928_, v___x_1930_);
v___x_1932_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1929_, v_data_1925_, v___x_1931_);
return v___x_1932_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1933_, lean_object* v_b_1934_, lean_object* v_x_1935_){
_start:
{
if (lean_obj_tag(v_x_1935_) == 0)
{
lean_dec(v_b_1934_);
lean_dec_ref(v_a_1933_);
return v_x_1935_;
}
else
{
lean_object* v_key_1936_; lean_object* v_value_1937_; lean_object* v_tail_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1950_; 
v_key_1936_ = lean_ctor_get(v_x_1935_, 0);
v_value_1937_ = lean_ctor_get(v_x_1935_, 1);
v_tail_1938_ = lean_ctor_get(v_x_1935_, 2);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_x_1935_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1940_ = v_x_1935_;
v_isShared_1941_ = v_isSharedCheck_1950_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_tail_1938_);
lean_inc(v_value_1937_);
lean_inc(v_key_1936_);
lean_dec(v_x_1935_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1950_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
uint8_t v___x_1942_; 
v___x_1942_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1936_, v_a_1933_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1933_, v_b_1934_, v_tail_1938_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 2, v___x_1943_);
v___x_1945_ = v___x_1940_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_key_1936_);
lean_ctor_set(v_reuseFailAlloc_1946_, 1, v_value_1937_);
lean_ctor_set(v_reuseFailAlloc_1946_, 2, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
else
{
lean_object* v___x_1948_; 
lean_dec(v_value_1937_);
lean_dec(v_key_1936_);
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 1, v_b_1934_);
lean_ctor_set(v___x_1940_, 0, v_a_1933_);
v___x_1948_ = v___x_1940_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1933_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_b_1934_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v_tail_1938_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1951_, lean_object* v_a_1952_, lean_object* v_b_1953_){
_start:
{
lean_object* v_size_1954_; lean_object* v_buckets_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2005_; 
v_size_1954_ = lean_ctor_get(v_m_1951_, 0);
v_buckets_1955_ = lean_ctor_get(v_m_1951_, 1);
v_isSharedCheck_2005_ = !lean_is_exclusive(v_m_1951_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1957_ = v_m_1951_;
v_isShared_1958_ = v_isSharedCheck_2005_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_buckets_1955_);
lean_inc(v_size_1954_);
lean_dec(v_m_1951_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2005_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v_parserName_1959_; lean_object* v_pos_1960_; lean_object* v___x_1961_; uint64_t v___x_1962_; uint64_t v___y_1964_; 
v_parserName_1959_ = lean_ctor_get(v_a_1952_, 1);
v_pos_1960_ = lean_ctor_get(v_a_1952_, 2);
v___x_1961_ = lean_array_get_size(v_buckets_1955_);
v___x_1962_ = l_String_instHashableRaw_hash(v_pos_1960_);
if (lean_obj_tag(v_parserName_1959_) == 0)
{
uint64_t v___x_2003_; 
v___x_2003_ = 1723ULL;
v___y_1964_ = v___x_2003_;
goto v___jp_1963_;
}
else
{
uint64_t v_hash_2004_; 
v_hash_2004_ = lean_ctor_get_uint64(v_parserName_1959_, sizeof(void*)*2);
v___y_1964_ = v_hash_2004_;
goto v___jp_1963_;
}
v___jp_1963_:
{
uint64_t v___x_1965_; uint64_t v___x_1966_; uint64_t v___x_1967_; uint64_t v_fold_1968_; uint64_t v___x_1969_; uint64_t v___x_1970_; uint64_t v___x_1971_; size_t v___x_1972_; size_t v___x_1973_; size_t v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; lean_object* v_bkt_1977_; uint8_t v___x_1978_; 
v___x_1965_ = lean_uint64_mix_hash(v___x_1962_, v___y_1964_);
v___x_1966_ = 32ULL;
v___x_1967_ = lean_uint64_shift_right(v___x_1965_, v___x_1966_);
v_fold_1968_ = lean_uint64_xor(v___x_1965_, v___x_1967_);
v___x_1969_ = 16ULL;
v___x_1970_ = lean_uint64_shift_right(v_fold_1968_, v___x_1969_);
v___x_1971_ = lean_uint64_xor(v_fold_1968_, v___x_1970_);
v___x_1972_ = lean_uint64_to_usize(v___x_1971_);
v___x_1973_ = lean_usize_of_nat(v___x_1961_);
v___x_1974_ = ((size_t)1ULL);
v___x_1975_ = lean_usize_sub(v___x_1973_, v___x_1974_);
v___x_1976_ = lean_usize_land(v___x_1972_, v___x_1975_);
v_bkt_1977_ = lean_array_uget_borrowed(v_buckets_1955_, v___x_1976_);
v___x_1978_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1952_, v_bkt_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; lean_object* v_size_x27_1980_; lean_object* v___x_1981_; lean_object* v_buckets_x27_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1979_ = lean_unsigned_to_nat(1u);
v_size_x27_1980_ = lean_nat_add(v_size_1954_, v___x_1979_);
lean_dec(v_size_1954_);
lean_inc(v_bkt_1977_);
v___x_1981_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1981_, 0, v_a_1952_);
lean_ctor_set(v___x_1981_, 1, v_b_1953_);
lean_ctor_set(v___x_1981_, 2, v_bkt_1977_);
v_buckets_x27_1982_ = lean_array_uset(v_buckets_1955_, v___x_1976_, v___x_1981_);
v___x_1983_ = lean_unsigned_to_nat(4u);
v___x_1984_ = lean_nat_mul(v_size_x27_1980_, v___x_1983_);
v___x_1985_ = lean_unsigned_to_nat(3u);
v___x_1986_ = lean_nat_div(v___x_1984_, v___x_1985_);
lean_dec(v___x_1984_);
v___x_1987_ = lean_array_get_size(v_buckets_x27_1982_);
v___x_1988_ = lean_nat_dec_le(v___x_1986_, v___x_1987_);
lean_dec(v___x_1986_);
if (v___x_1988_ == 0)
{
lean_object* v_val_1989_; lean_object* v___x_1991_; 
v_val_1989_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_1982_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_val_1989_);
lean_ctor_set(v___x_1957_, 0, v_size_x27_1980_);
v___x_1991_ = v___x_1957_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_size_x27_1980_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_val_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
else
{
lean_object* v___x_1994_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_buckets_x27_1982_);
lean_ctor_set(v___x_1957_, 0, v_size_x27_1980_);
v___x_1994_ = v___x_1957_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_size_x27_1980_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_buckets_x27_1982_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
else
{
lean_object* v___x_1996_; lean_object* v_buckets_x27_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2001_; 
lean_inc(v_bkt_1977_);
v___x_1996_ = lean_box(0);
v_buckets_x27_1997_ = lean_array_uset(v_buckets_1955_, v___x_1976_, v___x_1996_);
v___x_1998_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1952_, v_b_1953_, v_bkt_1977_);
v___x_1999_ = lean_array_uset(v_buckets_x27_1997_, v___x_1976_, v___x_1998_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v___x_1999_);
v___x_2001_ = v___x_1957_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_size_1954_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v___x_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_2006_, lean_object* v_x_2007_){
_start:
{
if (lean_obj_tag(v_x_2007_) == 0)
{
lean_object* v___x_2008_; 
v___x_2008_ = lean_box(0);
return v___x_2008_;
}
else
{
lean_object* v_key_2009_; lean_object* v_value_2010_; lean_object* v_tail_2011_; uint8_t v___x_2012_; 
v_key_2009_ = lean_ctor_get(v_x_2007_, 0);
v_value_2010_ = lean_ctor_get(v_x_2007_, 1);
v_tail_2011_ = lean_ctor_get(v_x_2007_, 2);
v___x_2012_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_2009_, v_a_2006_);
if (v___x_2012_ == 0)
{
v_x_2007_ = v_tail_2011_;
goto _start;
}
else
{
lean_object* v___x_2014_; 
lean_inc(v_value_2010_);
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_value_2010_);
return v___x_2014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_2015_, lean_object* v_x_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2015_, v_x_2016_);
lean_dec(v_x_2016_);
lean_dec_ref(v_a_2015_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v_buckets_2020_; lean_object* v_parserName_2021_; lean_object* v_pos_2022_; lean_object* v___x_2023_; uint64_t v___x_2024_; uint64_t v___y_2026_; 
v_buckets_2020_ = lean_ctor_get(v_m_2018_, 1);
v_parserName_2021_ = lean_ctor_get(v_a_2019_, 1);
v_pos_2022_ = lean_ctor_get(v_a_2019_, 2);
v___x_2023_ = lean_array_get_size(v_buckets_2020_);
v___x_2024_ = l_String_instHashableRaw_hash(v_pos_2022_);
if (lean_obj_tag(v_parserName_2021_) == 0)
{
uint64_t v___x_2041_; 
v___x_2041_ = 1723ULL;
v___y_2026_ = v___x_2041_;
goto v___jp_2025_;
}
else
{
uint64_t v_hash_2042_; 
v_hash_2042_ = lean_ctor_get_uint64(v_parserName_2021_, sizeof(void*)*2);
v___y_2026_ = v_hash_2042_;
goto v___jp_2025_;
}
v___jp_2025_:
{
uint64_t v___x_2027_; uint64_t v___x_2028_; uint64_t v___x_2029_; uint64_t v_fold_2030_; uint64_t v___x_2031_; uint64_t v___x_2032_; uint64_t v___x_2033_; size_t v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; size_t v___x_2037_; size_t v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2027_ = lean_uint64_mix_hash(v___x_2024_, v___y_2026_);
v___x_2028_ = 32ULL;
v___x_2029_ = lean_uint64_shift_right(v___x_2027_, v___x_2028_);
v_fold_2030_ = lean_uint64_xor(v___x_2027_, v___x_2029_);
v___x_2031_ = 16ULL;
v___x_2032_ = lean_uint64_shift_right(v_fold_2030_, v___x_2031_);
v___x_2033_ = lean_uint64_xor(v_fold_2030_, v___x_2032_);
v___x_2034_ = lean_uint64_to_usize(v___x_2033_);
v___x_2035_ = lean_usize_of_nat(v___x_2023_);
v___x_2036_ = ((size_t)1ULL);
v___x_2037_ = lean_usize_sub(v___x_2035_, v___x_2036_);
v___x_2038_ = lean_usize_land(v___x_2034_, v___x_2037_);
v___x_2039_ = lean_array_uget_borrowed(v_buckets_2020_, v___x_2038_);
v___x_2040_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2019_, v___x_2039_);
return v___x_2040_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2043_, v_a_2044_);
lean_dec_ref(v_a_2044_);
lean_dec_ref(v_m_2043_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_2046_, lean_object* v_p_2047_, lean_object* v_c_2048_, lean_object* v_s_2049_){
_start:
{
lean_object* v_cache_2050_; lean_object* v_toCacheableParserContext_2051_; lean_object* v_stxStack_2052_; lean_object* v_pos_2053_; lean_object* v_recoveredErrors_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2103_; 
v_cache_2050_ = lean_ctor_get(v_s_2049_, 3);
lean_inc_ref(v_cache_2050_);
v_toCacheableParserContext_2051_ = lean_ctor_get(v_c_2048_, 2);
v_stxStack_2052_ = lean_ctor_get(v_s_2049_, 0);
v_pos_2053_ = lean_ctor_get(v_s_2049_, 2);
v_recoveredErrors_2054_ = lean_ctor_get(v_s_2049_, 5);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_s_2049_);
if (v_isSharedCheck_2103_ == 0)
{
lean_object* v_unused_2104_; lean_object* v_unused_2105_; lean_object* v_unused_2106_; 
v_unused_2104_ = lean_ctor_get(v_s_2049_, 4);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_s_2049_, 3);
lean_dec(v_unused_2105_);
v_unused_2106_ = lean_ctor_get(v_s_2049_, 1);
lean_dec(v_unused_2106_);
v___x_2056_ = v_s_2049_;
v_isShared_2057_ = v_isSharedCheck_2103_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_recoveredErrors_2054_);
lean_inc(v_pos_2053_);
lean_inc(v_stxStack_2052_);
lean_dec(v_s_2049_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2103_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v_parserCache_2058_; lean_object* v_key_2059_; lean_object* v___x_2060_; 
v_parserCache_2058_ = lean_ctor_get(v_cache_2050_, 1);
lean_inc(v_pos_2053_);
lean_inc_ref(v_toCacheableParserContext_2051_);
v_key_2059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_2059_, 0, v_toCacheableParserContext_2051_);
lean_ctor_set(v_key_2059_, 1, v_parserName_2046_);
lean_ctor_set(v_key_2059_, 2, v_pos_2053_);
v___x_2060_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_2058_, v_key_2059_);
if (lean_obj_tag(v___x_2060_) == 1)
{
lean_object* v_val_2061_; lean_object* v_stx_2062_; lean_object* v_lhsPrec_2063_; lean_object* v_newPos_2064_; lean_object* v_errorMsg_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
lean_dec_ref_known(v_key_2059_, 3);
lean_dec(v_pos_2053_);
lean_dec_ref(v_c_2048_);
lean_dec_ref(v_p_2047_);
v_val_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_val_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v_stx_2062_ = lean_ctor_get(v_val_2061_, 0);
lean_inc(v_stx_2062_);
v_lhsPrec_2063_ = lean_ctor_get(v_val_2061_, 1);
lean_inc(v_lhsPrec_2063_);
v_newPos_2064_ = lean_ctor_get(v_val_2061_, 2);
lean_inc(v_newPos_2064_);
v_errorMsg_2065_ = lean_ctor_get(v_val_2061_, 3);
lean_inc(v_errorMsg_2065_);
lean_dec(v_val_2061_);
v___x_2066_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_2052_, v_stx_2062_);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 4, v_errorMsg_2065_);
lean_ctor_set(v___x_2056_, 2, v_newPos_2064_);
lean_ctor_set(v___x_2056_, 1, v_lhsPrec_2063_);
lean_ctor_set(v___x_2056_, 0, v___x_2066_);
v___x_2068_ = v___x_2056_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v_lhsPrec_2063_);
lean_ctor_set(v_reuseFailAlloc_2069_, 2, v_newPos_2064_);
lean_ctor_set(v_reuseFailAlloc_2069_, 3, v_cache_2050_);
lean_ctor_set(v_reuseFailAlloc_2069_, 4, v_errorMsg_2065_);
lean_ctor_set(v_reuseFailAlloc_2069_, 5, v_recoveredErrors_2054_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
else
{
lean_object* v_raw_2070_; lean_object* v_initStackSz_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; 
lean_dec(v___x_2060_);
v_raw_2070_ = lean_ctor_get(v_stxStack_2052_, 0);
v_initStackSz_2071_ = lean_array_get_size(v_raw_2070_);
v___x_2072_ = lean_unsigned_to_nat(0u);
v___x_2073_ = lean_box(0);
if (v_isShared_2057_ == 0)
{
lean_ctor_set(v___x_2056_, 4, v___x_2073_);
lean_ctor_set(v___x_2056_, 1, v___x_2072_);
v___x_2075_ = v___x_2056_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_stxStack_2052_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2102_, 2, v_pos_2053_);
lean_ctor_set(v_reuseFailAlloc_2102_, 3, v_cache_2050_);
lean_ctor_set(v_reuseFailAlloc_2102_, 4, v___x_2073_);
lean_ctor_set(v_reuseFailAlloc_2102_, 5, v_recoveredErrors_2054_);
v___x_2075_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
lean_object* v_s_2076_; lean_object* v_cache_2077_; lean_object* v_stxStack_2078_; lean_object* v_lhsPrec_2079_; lean_object* v_pos_2080_; lean_object* v_errorMsg_2081_; lean_object* v_recoveredErrors_2082_; lean_object* v___x_2084_; uint8_t v_isShared_2085_; uint8_t v_isSharedCheck_2101_; 
v_s_2076_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_2071_, v_p_2047_, v_c_2048_, v___x_2075_);
v_cache_2077_ = lean_ctor_get(v_s_2076_, 3);
v_stxStack_2078_ = lean_ctor_get(v_s_2076_, 0);
v_lhsPrec_2079_ = lean_ctor_get(v_s_2076_, 1);
v_pos_2080_ = lean_ctor_get(v_s_2076_, 2);
v_errorMsg_2081_ = lean_ctor_get(v_s_2076_, 4);
v_recoveredErrors_2082_ = lean_ctor_get(v_s_2076_, 5);
v_isSharedCheck_2101_ = !lean_is_exclusive(v_s_2076_);
if (v_isSharedCheck_2101_ == 0)
{
v___x_2084_ = v_s_2076_;
v_isShared_2085_ = v_isSharedCheck_2101_;
goto v_resetjp_2083_;
}
else
{
lean_inc(v_recoveredErrors_2082_);
lean_inc(v_errorMsg_2081_);
lean_inc(v_cache_2077_);
lean_inc(v_pos_2080_);
lean_inc(v_lhsPrec_2079_);
lean_inc(v_stxStack_2078_);
lean_dec(v_s_2076_);
v___x_2084_ = lean_box(0);
v_isShared_2085_ = v_isSharedCheck_2101_;
goto v_resetjp_2083_;
}
v_resetjp_2083_:
{
lean_object* v_tokenCache_2086_; lean_object* v_parserCache_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2100_; 
v_tokenCache_2086_ = lean_ctor_get(v_cache_2077_, 0);
v_parserCache_2087_ = lean_ctor_get(v_cache_2077_, 1);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_cache_2077_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2089_ = v_cache_2077_;
v_isShared_2090_ = v_isSharedCheck_2100_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_parserCache_2087_);
lean_inc(v_tokenCache_2086_);
lean_dec(v_cache_2077_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2100_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2091_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2078_);
lean_inc(v_errorMsg_2081_);
lean_inc(v_pos_2080_);
lean_inc(v_lhsPrec_2079_);
v___x_2092_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v_lhsPrec_2079_);
lean_ctor_set(v___x_2092_, 2, v_pos_2080_);
lean_ctor_set(v___x_2092_, 3, v_errorMsg_2081_);
v___x_2093_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_2087_, v_key_2059_, v___x_2092_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v___x_2093_);
v___x_2095_ = v___x_2089_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_tokenCache_2086_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v___x_2093_);
v___x_2095_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2097_; 
if (v_isShared_2085_ == 0)
{
lean_ctor_set(v___x_2084_, 3, v___x_2095_);
v___x_2097_ = v___x_2084_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_stxStack_2078_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_lhsPrec_2079_);
lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_pos_2080_);
lean_ctor_set(v_reuseFailAlloc_2098_, 3, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2098_, 4, v_errorMsg_2081_);
lean_ctor_set(v_reuseFailAlloc_2098_, 5, v_recoveredErrors_2082_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2107_, lean_object* v_m_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2108_, v_a_2109_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2111_, lean_object* v_m_2112_, lean_object* v_a_2113_){
_start:
{
lean_object* v_res_2114_; 
v_res_2114_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2111_, v_m_2112_, v_a_2113_);
lean_dec_ref(v_a_2113_);
lean_dec_ref(v_m_2112_);
return v_res_2114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2115_, lean_object* v_m_2116_, lean_object* v_a_2117_, lean_object* v_b_2118_){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2116_, v_a_2117_, v_b_2118_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2120_, lean_object* v_a_2121_, lean_object* v_x_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2121_, v_x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2124_, lean_object* v_a_2125_, lean_object* v_x_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2124_, v_a_2125_, v_x_2126_);
lean_dec(v_x_2126_);
lean_dec_ref(v_a_2125_);
return v_res_2127_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2128_, lean_object* v_a_2129_, lean_object* v_x_2130_){
_start:
{
uint8_t v___x_2131_; 
v___x_2131_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2129_, v_x_2130_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2132_, lean_object* v_a_2133_, lean_object* v_x_2134_){
_start:
{
uint8_t v_res_2135_; lean_object* v_r_2136_; 
v_res_2135_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2132_, v_a_2133_, v_x_2134_);
lean_dec(v_x_2134_);
lean_dec_ref(v_a_2133_);
v_r_2136_ = lean_box(v_res_2135_);
return v_r_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2137_, lean_object* v_data_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2140_, lean_object* v_a_2141_, lean_object* v_b_2142_, lean_object* v_x_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2141_, v_b_2142_, v_x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2145_, lean_object* v_i_2146_, lean_object* v_source_2147_, lean_object* v_target_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2146_, v_source_2147_, v_target_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2151_, v_x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2154_, lean_object* v_p_2155_){
_start:
{
lean_object* v_info_2156_; lean_object* v_fn_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2165_; 
v_info_2156_ = lean_ctor_get(v_p_2155_, 0);
v_fn_2157_ = lean_ctor_get(v_p_2155_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_p_2155_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2159_ = v_p_2155_;
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_fn_2157_);
lean_inc(v_info_2156_);
lean_dec(v_p_2155_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2165_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2161_, 0, v_parserName_2154_);
lean_closure_set(v___x_2161_, 1, v_fn_2157_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 1, v___x_2161_);
v___x_2163_ = v___x_2159_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_info_2156_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2174_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2175_ = l_Lean_addBuiltinDocString(v___x_2173_, v___x_2174_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2185_, lean_object* v_ictx_2186_, lean_object* v_pmctx_2187_, lean_object* v_tokens_2188_, lean_object* v_s_2189_){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__1));
v___x_2191_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2191_, 0, v_ictx_2186_);
lean_ctor_set(v___x_2191_, 1, v_pmctx_2187_);
lean_ctor_set(v___x_2191_, 2, v___x_2190_);
lean_ctor_set(v___x_2191_, 3, v_tokens_2188_);
v___x_2192_ = lean_apply_2(v_p_2185_, v___x_2191_, v_s_2189_);
return v___x_2192_;
}
}
lean_object* runtime_initialize_Lean_Data_Trie(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Data_Trie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_maxPrec = _init_l_Lean_Parser_maxPrec();
lean_mark_persistent(l_Lean_Parser_maxPrec);
l_Lean_Parser_argPrec = _init_l_Lean_Parser_argPrec();
lean_mark_persistent(l_Lean_Parser_argPrec);
l_Lean_Parser_leadPrec = _init_l_Lean_Parser_leadPrec();
lean_mark_persistent(l_Lean_Parser_leadPrec);
l_Lean_Parser_minPrec = _init_l_Lean_Parser_minPrec();
lean_mark_persistent(l_Lean_Parser_minPrec);
l_Lean_Parser_instInhabitedInputContext = _init_l_Lean_Parser_instInhabitedInputContext();
lean_mark_persistent(l_Lean_Parser_instInhabitedInputContext);
l_Lean_Parser_instInhabitedFirstTokens_default = _init_l_Lean_Parser_instInhabitedFirstTokens_default();
lean_mark_persistent(l_Lean_Parser_instInhabitedFirstTokens_default);
l_Lean_Parser_instInhabitedFirstTokens = _init_l_Lean_Parser_instInhabitedFirstTokens();
lean_mark_persistent(l_Lean_Parser_instInhabitedFirstTokens);
res = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Parser_Types(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Lean_Parser_InputContext_endPos__valid___autoParam = _init_l_Lean_Parser_InputContext_endPos__valid___autoParam();
lean_mark_persistent(l_Lean_Parser_InputContext_endPos__valid___autoParam);
l_Lean_Parser_InputContext_mk___auto__1 = _init_l_Lean_Parser_InputContext_mk___auto__1();
lean_mark_persistent(l_Lean_Parser_InputContext_mk___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Data_Trie(uint8_t builtin);
lean_object* initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Parser_Types(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Trie(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Extension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Parser_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Parser_Types(builtin);
}
#ifdef __cplusplus
}
#endif
