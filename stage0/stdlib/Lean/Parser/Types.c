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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
lean_object* v_ks_108_; lean_object* v_vs_109_; lean_object* v___x_111_; uint8_t v_isShared_112_; uint8_t v_isSharedCheck_129_; 
v_ks_108_ = lean_ctor_get(v_x_57_, 0);
v_vs_109_ = lean_ctor_get(v_x_57_, 1);
v_isSharedCheck_129_ = !lean_is_exclusive(v_x_57_);
if (v_isSharedCheck_129_ == 0)
{
v___x_111_ = v_x_57_;
v_isShared_112_ = v_isSharedCheck_129_;
goto v_resetjp_110_;
}
else
{
lean_inc(v_vs_109_);
lean_inc(v_ks_108_);
lean_dec(v_x_57_);
v___x_111_ = lean_box(0);
v_isShared_112_ = v_isSharedCheck_129_;
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
lean_object* v_reuseFailAlloc_128_; 
v_reuseFailAlloc_128_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_128_, 0, v_ks_108_);
lean_ctor_set(v_reuseFailAlloc_128_, 1, v_vs_109_);
v___x_114_ = v_reuseFailAlloc_128_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
lean_object* v_newNode_115_; uint8_t v___y_117_; size_t v___x_123_; uint8_t v___x_124_; 
v_newNode_115_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v___x_114_, v_x_60_, v_x_61_);
v___x_123_ = ((size_t)7ULL);
v___x_124_ = lean_usize_dec_le(v___x_123_, v_x_59_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_125_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_115_);
v___x_126_ = lean_unsigned_to_nat(4u);
v___x_127_ = lean_nat_dec_lt(v___x_125_, v___x_126_);
lean_dec(v___x_125_);
v___y_117_ = v___x_127_;
goto v___jp_116_;
}
else
{
v___y_117_ = v___x_124_;
goto v___jp_116_;
}
v___jp_116_:
{
if (v___y_117_ == 0)
{
lean_object* v_ks_118_; lean_object* v_vs_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_ks_118_ = lean_ctor_get(v_newNode_115_, 0);
lean_inc_ref(v_ks_118_);
v_vs_119_ = lean_ctor_get(v_newNode_115_, 1);
lean_inc_ref(v_vs_119_);
lean_dec_ref(v_newNode_115_);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0);
v___x_122_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_x_59_, v_ks_118_, v_vs_119_, v___x_120_, v___x_121_);
lean_dec_ref(v_vs_119_);
lean_dec_ref(v_ks_118_);
return v___x_122_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_130_, lean_object* v_keys_131_, lean_object* v_vals_132_, lean_object* v_i_133_, lean_object* v_entries_134_){
_start:
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = lean_array_get_size(v_keys_131_);
v___x_136_ = lean_nat_dec_lt(v_i_133_, v___x_135_);
if (v___x_136_ == 0)
{
lean_dec(v_i_133_);
return v_entries_134_;
}
else
{
lean_object* v_k_137_; lean_object* v_v_138_; uint64_t v___y_140_; 
v_k_137_ = lean_array_fget_borrowed(v_keys_131_, v_i_133_);
v_v_138_ = lean_array_fget_borrowed(v_vals_132_, v_i_133_);
if (lean_obj_tag(v_k_137_) == 0)
{
uint64_t v___x_151_; 
v___x_151_ = 1723ULL;
v___y_140_ = v___x_151_;
goto v___jp_139_;
}
else
{
uint64_t v_hash_152_; 
v_hash_152_ = lean_ctor_get_uint64(v_k_137_, sizeof(void*)*2);
v___y_140_ = v_hash_152_;
goto v___jp_139_;
}
v___jp_139_:
{
size_t v_h_141_; size_t v___x_142_; lean_object* v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v_h_147_; lean_object* v___x_148_; lean_object* v___x_149_; 
v_h_141_ = lean_uint64_to_usize(v___y_140_);
v___x_142_ = ((size_t)5ULL);
v___x_143_ = lean_unsigned_to_nat(1u);
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_sub(v_depth_130_, v___x_144_);
v___x_146_ = lean_usize_mul(v___x_142_, v___x_145_);
v_h_147_ = lean_usize_shift_right(v_h_141_, v___x_146_);
v___x_148_ = lean_nat_add(v_i_133_, v___x_143_);
lean_dec(v_i_133_);
lean_inc(v_v_138_);
lean_inc(v_k_137_);
v___x_149_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_entries_134_, v_h_147_, v_depth_130_, v_k_137_, v_v_138_);
v_i_133_ = v___x_148_;
v_entries_134_ = v___x_149_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_153_, lean_object* v_keys_154_, lean_object* v_vals_155_, lean_object* v_i_156_, lean_object* v_entries_157_){
_start:
{
size_t v_depth_boxed_158_; lean_object* v_res_159_; 
v_depth_boxed_158_ = lean_unbox_usize(v_depth_153_);
lean_dec(v_depth_153_);
v_res_159_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_158_, v_keys_154_, v_vals_155_, v_i_156_, v_entries_157_);
lean_dec_ref(v_vals_155_);
lean_dec_ref(v_keys_154_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_){
_start:
{
size_t v_x_351__boxed_165_; size_t v_x_352__boxed_166_; lean_object* v_res_167_; 
v_x_351__boxed_165_ = lean_unbox_usize(v_x_161_);
lean_dec(v_x_161_);
v_x_352__boxed_166_ = lean_unbox_usize(v_x_162_);
lean_dec(v_x_162_);
v_res_167_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_160_, v_x_351__boxed_165_, v_x_352__boxed_166_, v_x_163_, v_x_164_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(lean_object* v_x_168_, lean_object* v_x_169_, lean_object* v_x_170_){
_start:
{
uint64_t v___y_172_; 
if (lean_obj_tag(v_x_169_) == 0)
{
uint64_t v___x_176_; 
v___x_176_ = 1723ULL;
v___y_172_ = v___x_176_;
goto v___jp_171_;
}
else
{
uint64_t v_hash_177_; 
v_hash_177_ = lean_ctor_get_uint64(v_x_169_, sizeof(void*)*2);
v___y_172_ = v_hash_177_;
goto v___jp_171_;
}
v___jp_171_:
{
size_t v___x_173_; size_t v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_uint64_to_usize(v___y_172_);
v___x_174_ = ((size_t)1ULL);
v___x_175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_168_, v___x_173_, v___x_174_, v_x_169_, v_x_170_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object* v_s_178_, lean_object* v_k_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_box(0);
v___x_181_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_s_178_, v_k_179_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0(lean_object* v_00_u03b2_182_, lean_object* v_x_183_, lean_object* v_x_184_, lean_object* v_x_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_x_183_, v_x_184_, v_x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_187_, lean_object* v_x_188_, size_t v_x_189_, size_t v_x_190_, lean_object* v_x_191_, lean_object* v_x_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_188_, v_x_189_, v_x_190_, v_x_191_, v_x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_194_, lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
size_t v_x_539__boxed_200_; size_t v_x_540__boxed_201_; lean_object* v_res_202_; 
v_x_539__boxed_200_ = lean_unbox_usize(v_x_196_);
lean_dec(v_x_196_);
v_x_540__boxed_201_ = lean_unbox_usize(v_x_197_);
lean_dec(v_x_197_);
v_res_202_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(v_00_u03b2_194_, v_x_195_, v_x_539__boxed_200_, v_x_540__boxed_201_, v_x_198_, v_x_199_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_203_, lean_object* v_n_204_, lean_object* v_k_205_, lean_object* v_v_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v_n_204_, v_k_205_, v_v_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_208_, size_t v_depth_209_, lean_object* v_keys_210_, lean_object* v_vals_211_, lean_object* v_heq_212_, lean_object* v_i_213_, lean_object* v_entries_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_209_, v_keys_210_, v_vals_211_, v_i_213_, v_entries_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_216_, lean_object* v_depth_217_, lean_object* v_keys_218_, lean_object* v_vals_219_, lean_object* v_heq_220_, lean_object* v_i_221_, lean_object* v_entries_222_){
_start:
{
size_t v_depth_boxed_223_; lean_object* v_res_224_; 
v_depth_boxed_223_ = lean_unbox_usize(v_depth_217_);
lean_dec(v_depth_217_);
v_res_224_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(v_00_u03b2_216_, v_depth_boxed_223_, v_keys_218_, v_vals_219_, v_heq_220_, v_i_221_, v_entries_222_);
lean_dec_ref(v_vals_219_);
lean_dec_ref(v_keys_218_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_225_, lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_226_, v_x_227_, v_x_228_, v_x_229_);
return v___x_230_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10));
v___x_258_ = l_Lean_mkAtom(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_259_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12);
v___x_260_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_261_ = lean_array_push(v___x_260_, v___x_259_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17(void){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_273_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_274_ = lean_array_push(v___x_273_, v___x_272_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_275_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17);
v___x_276_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15));
v___x_277_ = lean_box(2);
v___x_278_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
lean_ctor_set(v___x_278_, 2, v___x_275_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18);
v___x_280_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13);
v___x_281_ = lean_array_push(v___x_280_, v___x_279_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_283_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19);
v___x_284_ = lean_array_push(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_286_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20);
v___x_287_ = lean_array_push(v___x_286_, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_289_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21);
v___x_290_ = lean_array_push(v___x_289_, v___x_288_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_292_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22);
v___x_293_ = lean_array_push(v___x_292_, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v___x_294_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23);
v___x_295_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11));
v___x_296_ = lean_box(2);
v___x_297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
lean_ctor_set(v___x_297_, 1, v___x_295_);
lean_ctor_set(v___x_297_, 2, v___x_294_);
return v___x_297_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24);
v___x_299_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_300_ = lean_array_push(v___x_299_, v___x_298_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_301_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25);
v___x_302_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9));
v___x_303_ = lean_box(2);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
lean_ctor_set(v___x_304_, 2, v___x_301_);
return v___x_304_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27(void){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_305_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26);
v___x_306_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_307_ = lean_array_push(v___x_306_, v___x_305_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_308_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27);
v___x_309_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7));
v___x_310_ = lean_box(2);
v___x_311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v___x_309_);
lean_ctor_set(v___x_311_, 2, v___x_308_);
return v___x_311_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_312_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28);
v___x_313_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_314_ = lean_array_push(v___x_313_, v___x_312_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29);
v___x_316_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4));
v___x_317_ = lean_box(2);
v___x_318_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
lean_ctor_set(v___x_318_, 2, v___x_315_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__1(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_322_ = lean_string_utf8_byte_size(v___x_321_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__2(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_323_ = lean_obj_once(&l_Lean_Parser_instInhabitedInputContext___closed__1, &l_Lean_Parser_instInhabitedInputContext___closed__1_once, _init_l_Lean_Parser_instInhabitedInputContext___closed__1);
v___x_324_ = l_Lean_instInhabitedFileMap_default;
v___x_325_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_326_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
lean_ctor_set(v___x_326_, 2, v___x_324_);
lean_ctor_set(v___x_326_, 3, v___x_323_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Lean_Parser_instInhabitedInputContext___closed__2, &l_Lean_Parser_instInhabitedInputContext___closed__2_once, _init_l_Lean_Parser_instInhabitedInputContext___closed__2);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_mk___auto__1(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk___redArg(lean_object* v_input_329_, lean_object* v_fileName_330_, lean_object* v_endPos_331_, lean_object* v_fileMap_332_){
_start:
{
lean_object* v___x_333_; 
v___x_333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_333_, 0, v_input_329_);
lean_ctor_set(v___x_333_, 1, v_fileName_330_);
lean_ctor_set(v___x_333_, 2, v_fileMap_332_);
lean_ctor_set(v___x_333_, 3, v_endPos_331_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk(lean_object* v_input_334_, lean_object* v_fileName_335_, lean_object* v_endPos_336_, lean_object* v_endPos__valid_337_, lean_object* v_fileMap_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_339_, 0, v_input_334_);
lean_ctor_set(v___x_339_, 1, v_fileName_335_);
lean_ctor_set(v___x_339_, 2, v_fileMap_338_);
lean_ctor_set(v___x_339_, 3, v_endPos_336_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input(lean_object* v_c_340_){
_start:
{
lean_object* v_inputString_341_; lean_object* v_endPos_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_inputString_341_ = lean_ctor_get(v_c_340_, 0);
v_endPos_342_ = lean_ctor_get(v_c_340_, 3);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_string_utf8_extract(v_inputString_341_, v___x_343_, v_endPos_342_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input___boxed(lean_object* v_c_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_Parser_InputContext_input(v_c_345_);
lean_dec_ref(v_c_345_);
return v_res_346_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_InputContext_atEnd(lean_object* v_c_347_, lean_object* v_p_348_){
_start:
{
lean_object* v_endPos_349_; uint8_t v___x_350_; 
v_endPos_349_ = lean_ctor_get(v_c_347_, 3);
v___x_350_ = lean_nat_dec_le(v_endPos_349_, v_p_348_);
return v___x_350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_atEnd___boxed(lean_object* v_c_351_, lean_object* v_p_352_){
_start:
{
uint8_t v_res_353_; lean_object* v_r_354_; 
v_res_353_ = l_Lean_Parser_InputContext_atEnd(v_c_351_, v_p_352_);
lean_dec(v_p_352_);
lean_dec_ref(v_c_351_);
v_r_354_ = lean_box(v_res_353_);
return v_r_354_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get(lean_object* v_c_355_, lean_object* v_p_356_){
_start:
{
lean_object* v_inputString_357_; uint32_t v___x_358_; 
v_inputString_357_ = lean_ctor_get(v_c_355_, 0);
v___x_358_ = lean_string_utf8_get(v_inputString_357_, v_p_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get___boxed(lean_object* v_c_359_, lean_object* v_p_360_){
_start:
{
uint32_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Lean_Parser_InputContext_get(v_c_359_, v_p_360_);
lean_dec(v_p_360_);
lean_dec_ref(v_c_359_);
v_r_362_ = lean_box_uint32(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_363_, lean_object* v_x_364_, lean_object* v_h__1_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_apply_2(v_h__1_365_, v_x_363_, v_x_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_367_, lean_object* v_x_368_, lean_object* v_x_369_, lean_object* v_h__1_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_apply_2(v_h__1_370_, v_x_368_, v_x_369_);
return v___x_371_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27___redArg(lean_object* v_c_372_, lean_object* v_p_373_){
_start:
{
lean_object* v_inputString_374_; uint32_t v___x_375_; 
v_inputString_374_ = lean_ctor_get(v_c_372_, 0);
v___x_375_ = lean_string_utf8_get_fast(v_inputString_374_, v_p_373_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___redArg___boxed(lean_object* v_c_376_, lean_object* v_p_377_){
_start:
{
uint32_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_Lean_Parser_InputContext_get_x27___redArg(v_c_376_, v_p_377_);
lean_dec(v_p_377_);
lean_dec_ref(v_c_376_);
v_r_379_ = lean_box_uint32(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27(lean_object* v_c_380_, lean_object* v_p_381_, lean_object* v_h_382_){
_start:
{
lean_object* v_inputString_383_; uint32_t v___x_384_; 
v_inputString_383_ = lean_ctor_get(v_c_380_, 0);
v___x_384_ = lean_string_utf8_get_fast(v_inputString_383_, v_p_381_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___boxed(lean_object* v_c_385_, lean_object* v_p_386_, lean_object* v_h_387_){
_start:
{
uint32_t v_res_388_; lean_object* v_r_389_; 
v_res_388_ = l_Lean_Parser_InputContext_get_x27(v_c_385_, v_p_386_, v_h_387_);
lean_dec(v_p_386_);
lean_dec_ref(v_c_385_);
v_r_389_ = lean_box_uint32(v_res_388_);
return v_r_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next(lean_object* v_c_390_, lean_object* v_p_391_){
_start:
{
lean_object* v_inputString_392_; lean_object* v___x_393_; 
v_inputString_392_ = lean_ctor_get(v_c_390_, 0);
v___x_393_ = lean_string_utf8_next(v_inputString_392_, v_p_391_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next___boxed(lean_object* v_c_394_, lean_object* v_p_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Parser_InputContext_next(v_c_394_, v_p_395_);
lean_dec(v_p_395_);
lean_dec_ref(v_c_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg(lean_object* v_c_397_, lean_object* v_p_398_){
_start:
{
lean_object* v_inputString_399_; lean_object* v___x_400_; 
v_inputString_399_ = lean_ctor_get(v_c_397_, 0);
v___x_400_ = lean_string_utf8_next_fast(v_inputString_399_, v_p_398_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg___boxed(lean_object* v_c_401_, lean_object* v_p_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_Parser_InputContext_next_x27___redArg(v_c_401_, v_p_402_);
lean_dec(v_p_402_);
lean_dec_ref(v_c_401_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27(lean_object* v_c_404_, lean_object* v_p_405_, lean_object* v_h_406_){
_start:
{
lean_object* v_inputString_407_; lean_object* v___x_408_; 
v_inputString_407_ = lean_ctor_get(v_c_404_, 0);
v___x_408_ = lean_string_utf8_next_fast(v_inputString_407_, v_p_405_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___boxed(lean_object* v_c_409_, lean_object* v_p_410_, lean_object* v_h_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Lean_Parser_InputContext_next_x27(v_c_409_, v_p_410_, v_h_411_);
lean_dec(v_p_410_);
lean_dec_ref(v_c_409_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract(lean_object* v_c_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_inputString_416_; lean_object* v___x_417_; 
v_inputString_416_ = lean_ctor_get(v_c_413_, 0);
v___x_417_ = lean_string_utf8_extract(v_inputString_416_, v_a_414_, v_a_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract___boxed(lean_object* v_c_418_, lean_object* v_a_419_, lean_object* v_a_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Parser_InputContext_extract(v_c_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_c_418_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring(lean_object* v_c_422_, lean_object* v_startPos_423_, lean_object* v_stopPos_424_){
_start:
{
lean_object* v_inputString_425_; lean_object* v_endPos_426_; uint8_t v___x_427_; 
v_inputString_425_ = lean_ctor_get(v_c_422_, 0);
v_endPos_426_ = lean_ctor_get(v_c_422_, 3);
v___x_427_ = lean_nat_dec_le(v_stopPos_424_, v_endPos_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; 
lean_dec(v_stopPos_424_);
lean_inc(v_endPos_426_);
lean_inc_ref(v_inputString_425_);
v___x_428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_428_, 0, v_inputString_425_);
lean_ctor_set(v___x_428_, 1, v_startPos_423_);
lean_ctor_set(v___x_428_, 2, v_endPos_426_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; 
lean_inc_ref(v_inputString_425_);
v___x_429_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_429_, 0, v_inputString_425_);
lean_ctor_set(v___x_429_, 1, v_startPos_423_);
lean_ctor_set(v___x_429_, 2, v_stopPos_424_);
return v___x_429_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring___boxed(lean_object* v_c_430_, lean_object* v_startPos_431_, lean_object* v_stopPos_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Lean_Parser_InputContext_substring(v_c_430_, v_startPos_431_, v_stopPos_432_);
lean_dec_ref(v_c_430_);
return v_res_433_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_getNext(lean_object* v_input_434_, lean_object* v_pos_435_){
_start:
{
lean_object* v_inputString_436_; lean_object* v___x_437_; uint32_t v___x_438_; 
v_inputString_436_ = lean_ctor_get(v_input_434_, 0);
v___x_437_ = lean_string_utf8_next(v_inputString_436_, v_pos_435_);
v___x_438_ = lean_string_utf8_get(v_inputString_436_, v___x_437_);
lean_dec(v___x_437_);
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_getNext___boxed(lean_object* v_input_439_, lean_object* v_pos_440_){
_start:
{
uint32_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l_Lean_Parser_InputContext_getNext(v_input_439_, v_pos_440_);
lean_dec(v_pos_440_);
lean_dec_ref(v_input_439_);
v_r_442_ = lean_box_uint32(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev(lean_object* v_c_443_, lean_object* v_pos_444_){
_start:
{
lean_object* v_inputString_445_; lean_object* v___x_446_; 
v_inputString_445_ = lean_ctor_get(v_c_443_, 0);
v___x_446_ = lean_string_utf8_prev(v_inputString_445_, v_pos_444_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev___boxed(lean_object* v_c_447_, lean_object* v_pos_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Parser_InputContext_prev(v_c_447_, v_pos_448_);
lean_dec(v_pos_448_);
lean_dec_ref(v_c_447_);
return v_res_449_;
}
}
static lean_object* _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0(void){
_start:
{
lean_object* v___x_450_; lean_object* v___f_451_; 
v___x_450_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_451_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_451_, 0, v___x_450_);
return v___f_451_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext___lam__0(lean_object* v___f_452_, lean_object* v_a_453_, lean_object* v_b_454_){
_start:
{
lean_object* v_prec_455_; lean_object* v_quotDepth_456_; uint8_t v_suppressInsideQuot_457_; lean_object* v_savedPos_x3f_458_; lean_object* v_forbiddenTks_459_; lean_object* v_prec_460_; lean_object* v_quotDepth_461_; uint8_t v_suppressInsideQuot_462_; lean_object* v_savedPos_x3f_463_; lean_object* v_forbiddenTks_464_; uint8_t v___x_475_; 
v_prec_455_ = lean_ctor_get(v_a_453_, 0);
lean_inc(v_prec_455_);
v_quotDepth_456_ = lean_ctor_get(v_a_453_, 1);
lean_inc(v_quotDepth_456_);
v_suppressInsideQuot_457_ = lean_ctor_get_uint8(v_a_453_, sizeof(void*)*4);
v_savedPos_x3f_458_ = lean_ctor_get(v_a_453_, 2);
lean_inc(v_savedPos_x3f_458_);
v_forbiddenTks_459_ = lean_ctor_get(v_a_453_, 3);
lean_inc_ref(v_forbiddenTks_459_);
lean_dec_ref(v_a_453_);
v_prec_460_ = lean_ctor_get(v_b_454_, 0);
lean_inc(v_prec_460_);
v_quotDepth_461_ = lean_ctor_get(v_b_454_, 1);
lean_inc(v_quotDepth_461_);
v_suppressInsideQuot_462_ = lean_ctor_get_uint8(v_b_454_, sizeof(void*)*4);
v_savedPos_x3f_463_ = lean_ctor_get(v_b_454_, 2);
lean_inc(v_savedPos_x3f_463_);
v_forbiddenTks_464_ = lean_ctor_get(v_b_454_, 3);
lean_inc_ref(v_forbiddenTks_464_);
lean_dec_ref(v_b_454_);
v___x_475_ = lean_nat_dec_eq(v_prec_455_, v_prec_460_);
lean_dec(v_prec_460_);
lean_dec(v_prec_455_);
if (v___x_475_ == 0)
{
lean_dec_ref(v_forbiddenTks_464_);
lean_dec(v_savedPos_x3f_463_);
lean_dec(v_quotDepth_461_);
lean_dec_ref(v_forbiddenTks_459_);
lean_dec(v_savedPos_x3f_458_);
lean_dec(v_quotDepth_456_);
lean_dec_ref(v___f_452_);
return v___x_475_;
}
else
{
uint8_t v___x_476_; 
v___x_476_ = lean_nat_dec_eq(v_quotDepth_456_, v_quotDepth_461_);
lean_dec(v_quotDepth_461_);
lean_dec(v_quotDepth_456_);
if (v___x_476_ == 0)
{
lean_dec_ref(v_forbiddenTks_464_);
lean_dec(v_savedPos_x3f_463_);
lean_dec_ref(v_forbiddenTks_459_);
lean_dec(v_savedPos_x3f_458_);
lean_dec_ref(v___f_452_);
return v___x_476_;
}
else
{
if (v_suppressInsideQuot_457_ == 0)
{
if (v_suppressInsideQuot_462_ == 0)
{
goto v___jp_465_;
}
else
{
lean_dec_ref(v_forbiddenTks_464_);
lean_dec(v_savedPos_x3f_463_);
lean_dec_ref(v_forbiddenTks_459_);
lean_dec(v_savedPos_x3f_458_);
lean_dec_ref(v___f_452_);
return v_suppressInsideQuot_457_;
}
}
else
{
if (v_suppressInsideQuot_462_ == 0)
{
lean_dec_ref(v_forbiddenTks_464_);
lean_dec(v_savedPos_x3f_463_);
lean_dec_ref(v_forbiddenTks_459_);
lean_dec(v_savedPos_x3f_458_);
lean_dec_ref(v___f_452_);
return v_suppressInsideQuot_462_;
}
else
{
goto v___jp_465_;
}
}
}
}
v___jp_465_:
{
lean_object* v___f_466_; uint8_t v___x_467_; 
v___f_466_ = lean_obj_once(&l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0, &l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0_once, _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0);
v___x_467_ = l_Option_instBEq_beq___redArg(v___f_466_, v_savedPos_x3f_458_, v_savedPos_x3f_463_);
if (v___x_467_ == 0)
{
lean_dec_ref(v_forbiddenTks_464_);
lean_dec_ref(v_forbiddenTks_459_);
lean_dec_ref(v___f_452_);
return v___x_467_;
}
else
{
size_t v___x_468_; size_t v___x_469_; uint8_t v___x_470_; 
v___x_468_ = lean_ptr_addr(v_forbiddenTks_459_);
v___x_469_ = lean_ptr_addr(v_forbiddenTks_464_);
v___x_470_ = lean_usize_dec_eq(v___x_468_, v___x_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_471_ = lean_array_get_size(v_forbiddenTks_459_);
v___x_472_ = lean_array_get_size(v_forbiddenTks_464_);
v___x_473_ = lean_nat_dec_eq(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_dec_ref(v_forbiddenTks_464_);
lean_dec_ref(v_forbiddenTks_459_);
lean_dec_ref(v___f_452_);
return v___x_470_;
}
else
{
uint8_t v___x_474_; 
v___x_474_ = l_Array_isEqvAux___redArg(v_forbiddenTks_459_, v_forbiddenTks_464_, v___f_452_, v___x_471_);
lean_dec_ref(v_forbiddenTks_464_);
lean_dec_ref(v_forbiddenTks_459_);
return v___x_474_;
}
}
else
{
lean_dec_ref(v_forbiddenTks_464_);
lean_dec_ref(v_forbiddenTks_459_);
lean_dec_ref(v___f_452_);
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed(lean_object* v___f_477_, lean_object* v_a_478_, lean_object* v_b_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Lean_Parser_instBEqCacheableParserContext___lam__0(v___f_477_, v_a_478_, v_b_479_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0(lean_object* v_x_486_){
_start:
{
lean_object* v_toInputContext_487_; 
v_toInputContext_487_ = lean_ctor_get(v_x_486_, 0);
lean_inc_ref(v_toInputContext_487_);
return v_toInputContext_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(lean_object* v_x_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_488_);
lean_dec_ref(v_x_488_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos___redArg(lean_object* v_c_492_, lean_object* v_endPos_493_){
_start:
{
lean_object* v_toInputContext_494_; lean_object* v_toParserModuleContext_495_; lean_object* v_toCacheableParserContext_496_; lean_object* v_tokens_497_; lean_object* v___x_499_; uint8_t v_isShared_500_; uint8_t v_isSharedCheck_515_; 
v_toInputContext_494_ = lean_ctor_get(v_c_492_, 0);
v_toParserModuleContext_495_ = lean_ctor_get(v_c_492_, 1);
v_toCacheableParserContext_496_ = lean_ctor_get(v_c_492_, 2);
v_tokens_497_ = lean_ctor_get(v_c_492_, 3);
v_isSharedCheck_515_ = !lean_is_exclusive(v_c_492_);
if (v_isSharedCheck_515_ == 0)
{
v___x_499_ = v_c_492_;
v_isShared_500_ = v_isSharedCheck_515_;
goto v_resetjp_498_;
}
else
{
lean_inc(v_tokens_497_);
lean_inc(v_toCacheableParserContext_496_);
lean_inc(v_toParserModuleContext_495_);
lean_inc(v_toInputContext_494_);
lean_dec(v_c_492_);
v___x_499_ = lean_box(0);
v_isShared_500_ = v_isSharedCheck_515_;
goto v_resetjp_498_;
}
v_resetjp_498_:
{
lean_object* v_inputString_501_; lean_object* v_fileName_502_; lean_object* v_fileMap_503_; lean_object* v___x_505_; uint8_t v_isShared_506_; uint8_t v_isSharedCheck_513_; 
v_inputString_501_ = lean_ctor_get(v_toInputContext_494_, 0);
v_fileName_502_ = lean_ctor_get(v_toInputContext_494_, 1);
v_fileMap_503_ = lean_ctor_get(v_toInputContext_494_, 2);
v_isSharedCheck_513_ = !lean_is_exclusive(v_toInputContext_494_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v_toInputContext_494_, 3);
lean_dec(v_unused_514_);
v___x_505_ = v_toInputContext_494_;
v_isShared_506_ = v_isSharedCheck_513_;
goto v_resetjp_504_;
}
else
{
lean_inc(v_fileMap_503_);
lean_inc(v_fileName_502_);
lean_inc(v_inputString_501_);
lean_dec(v_toInputContext_494_);
v___x_505_ = lean_box(0);
v_isShared_506_ = v_isSharedCheck_513_;
goto v_resetjp_504_;
}
v_resetjp_504_:
{
lean_object* v___x_508_; 
if (v_isShared_506_ == 0)
{
lean_ctor_set(v___x_505_, 3, v_endPos_493_);
v___x_508_ = v___x_505_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_inputString_501_);
lean_ctor_set(v_reuseFailAlloc_512_, 1, v_fileName_502_);
lean_ctor_set(v_reuseFailAlloc_512_, 2, v_fileMap_503_);
lean_ctor_set(v_reuseFailAlloc_512_, 3, v_endPos_493_);
v___x_508_ = v_reuseFailAlloc_512_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_510_; 
if (v_isShared_500_ == 0)
{
lean_ctor_set(v___x_499_, 0, v___x_508_);
v___x_510_ = v___x_499_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
lean_ctor_set(v_reuseFailAlloc_511_, 1, v_toParserModuleContext_495_);
lean_ctor_set(v_reuseFailAlloc_511_, 2, v_toCacheableParserContext_496_);
lean_ctor_set(v_reuseFailAlloc_511_, 3, v_tokens_497_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos(lean_object* v_c_516_, lean_object* v_endPos_517_, lean_object* v_endPos__valid_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_516_, v_endPos_517_);
return v___x_519_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(lean_object* v_x_526_, lean_object* v_x_527_){
_start:
{
if (lean_obj_tag(v_x_526_) == 0)
{
if (lean_obj_tag(v_x_527_) == 0)
{
uint8_t v___x_528_; 
v___x_528_ = 1;
return v___x_528_;
}
else
{
uint8_t v___x_529_; 
v___x_529_ = 0;
return v___x_529_;
}
}
else
{
if (lean_obj_tag(v_x_527_) == 0)
{
uint8_t v___x_530_; 
v___x_530_ = 0;
return v___x_530_;
}
else
{
lean_object* v_head_531_; lean_object* v_tail_532_; lean_object* v_head_533_; lean_object* v_tail_534_; uint8_t v___x_535_; 
v_head_531_ = lean_ctor_get(v_x_526_, 0);
v_tail_532_ = lean_ctor_get(v_x_526_, 1);
v_head_533_ = lean_ctor_get(v_x_527_, 0);
v_tail_534_ = lean_ctor_get(v_x_527_, 1);
v___x_535_ = lean_string_dec_eq(v_head_531_, v_head_533_);
if (v___x_535_ == 0)
{
return v___x_535_;
}
else
{
v_x_526_ = v_tail_532_;
v_x_527_ = v_tail_534_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(lean_object* v_x_537_, lean_object* v_x_538_){
_start:
{
uint8_t v_res_539_; lean_object* v_r_540_; 
v_res_539_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_537_, v_x_538_);
lean_dec(v_x_538_);
lean_dec(v_x_537_);
v_r_540_ = lean_box(v_res_539_);
return v_r_540_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqError_beq(lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v_unexpectedTk_543_; lean_object* v_unexpected_544_; lean_object* v_expected_545_; lean_object* v_unexpectedTk_546_; lean_object* v_unexpected_547_; lean_object* v_expected_548_; uint8_t v___x_549_; 
v_unexpectedTk_543_ = lean_ctor_get(v_x_541_, 0);
v_unexpected_544_ = lean_ctor_get(v_x_541_, 1);
v_expected_545_ = lean_ctor_get(v_x_541_, 2);
v_unexpectedTk_546_ = lean_ctor_get(v_x_542_, 0);
v_unexpected_547_ = lean_ctor_get(v_x_542_, 1);
v_expected_548_ = lean_ctor_get(v_x_542_, 2);
v___x_549_ = l_Lean_Syntax_structEq(v_unexpectedTk_543_, v_unexpectedTk_546_);
if (v___x_549_ == 0)
{
return v___x_549_;
}
else
{
uint8_t v___x_550_; 
v___x_550_ = lean_string_dec_eq(v_unexpected_544_, v_unexpected_547_);
if (v___x_550_ == 0)
{
return v___x_550_;
}
else
{
uint8_t v___x_551_; 
v___x_551_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_545_, v_expected_548_);
return v___x_551_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object* v_x_552_, lean_object* v_x_553_){
_start:
{
uint8_t v_res_554_; lean_object* v_r_555_; 
v_res_554_ = l_Lean_Parser_instBEqError_beq(v_x_552_, v_x_553_);
lean_dec_ref(v_x_553_);
lean_dec_ref(v_x_552_);
v_r_555_ = lean_box(v_res_554_);
return v_r_555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* v_x_560_){
_start:
{
if (lean_obj_tag(v_x_560_) == 0)
{
lean_object* v___x_561_; 
v___x_561_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
return v___x_561_;
}
else
{
lean_object* v_tail_562_; 
v_tail_562_ = lean_ctor_get(v_x_560_, 1);
if (lean_obj_tag(v_tail_562_) == 0)
{
lean_object* v_head_563_; 
v_head_563_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_head_563_);
lean_dec_ref_known(v_x_560_, 2);
return v_head_563_;
}
else
{
lean_object* v_tail_564_; 
lean_inc_ref(v_tail_562_);
v_tail_564_ = lean_ctor_get(v_tail_562_, 1);
if (lean_obj_tag(v_tail_564_) == 0)
{
lean_object* v_head_565_; lean_object* v_head_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v_head_565_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_head_565_);
lean_dec_ref_known(v_x_560_, 2);
v_head_566_ = lean_ctor_get(v_tail_562_, 0);
lean_inc(v_head_566_);
lean_dec_ref_known(v_tail_562_, 2);
v___x_567_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0));
v___x_568_ = lean_string_append(v_head_565_, v___x_567_);
v___x_569_ = lean_string_append(v___x_568_, v_head_566_);
lean_dec(v_head_566_);
return v___x_569_;
}
else
{
lean_object* v_head_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_head_570_ = lean_ctor_get(v_x_560_, 0);
lean_inc(v_head_570_);
lean_dec_ref_known(v_x_560_, 2);
v___x_571_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_572_ = lean_string_append(v_head_570_, v___x_571_);
v___x_573_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_tail_562_);
v___x_574_ = lean_string_append(v___x_572_, v___x_573_);
lean_dec_ref(v___x_573_);
return v___x_574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object* v_as_575_){
_start:
{
lean_object* v___f_576_; lean_object* v___x_577_; 
v___f_576_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext___closed__0));
v___x_577_ = l_List_eraseRepsBy___redArg(v___f_576_, v_as_575_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object* v_hi_578_, lean_object* v_pivot_579_, lean_object* v_as_580_, lean_object* v_i_581_, lean_object* v_k_582_){
_start:
{
uint8_t v___x_583_; 
v___x_583_ = lean_nat_dec_lt(v_k_582_, v_hi_578_);
if (v___x_583_ == 0)
{
lean_object* v___x_584_; lean_object* v___x_585_; 
lean_dec(v_k_582_);
v___x_584_ = lean_array_fswap(v_as_580_, v_i_581_, v_hi_578_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_i_581_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
return v___x_585_;
}
else
{
lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_586_ = lean_array_fget_borrowed(v_as_580_, v_k_582_);
v___x_587_ = lean_string_dec_lt(v___x_586_, v_pivot_579_);
if (v___x_587_ == 0)
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(1u);
v___x_589_ = lean_nat_add(v_k_582_, v___x_588_);
lean_dec(v_k_582_);
v_k_582_ = v___x_589_;
goto _start;
}
else
{
lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_591_ = lean_array_fswap(v_as_580_, v_i_581_, v_k_582_);
v___x_592_ = lean_unsigned_to_nat(1u);
v___x_593_ = lean_nat_add(v_i_581_, v___x_592_);
lean_dec(v_i_581_);
v___x_594_ = lean_nat_add(v_k_582_, v___x_592_);
lean_dec(v_k_582_);
v_as_580_ = v___x_591_;
v_i_581_ = v___x_593_;
v_k_582_ = v___x_594_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object* v_hi_596_, lean_object* v_pivot_597_, lean_object* v_as_598_, lean_object* v_i_599_, lean_object* v_k_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_596_, v_pivot_597_, v_as_598_, v_i_599_, v_k_600_);
lean_dec_ref(v_pivot_597_);
lean_dec(v_hi_596_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_n_602_, lean_object* v_as_603_, lean_object* v_lo_604_, lean_object* v_hi_605_){
_start:
{
lean_object* v___y_607_; uint8_t v___x_617_; 
v___x_617_ = lean_nat_dec_lt(v_lo_604_, v_hi_605_);
if (v___x_617_ == 0)
{
lean_dec(v_lo_604_);
return v_as_603_;
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v_mid_620_; lean_object* v___y_622_; lean_object* v___y_628_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_618_ = lean_nat_add(v_lo_604_, v_hi_605_);
v___x_619_ = lean_unsigned_to_nat(1u);
v_mid_620_ = lean_nat_shiftr(v___x_618_, v___x_619_);
lean_dec(v___x_618_);
v___x_633_ = lean_array_fget_borrowed(v_as_603_, v_mid_620_);
v___x_634_ = lean_array_fget_borrowed(v_as_603_, v_lo_604_);
v___x_635_ = lean_string_dec_lt(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
v___y_628_ = v_as_603_;
goto v___jp_627_;
}
else
{
lean_object* v___x_636_; 
v___x_636_ = lean_array_fswap(v_as_603_, v_lo_604_, v_mid_620_);
v___y_628_ = v___x_636_;
goto v___jp_627_;
}
v___jp_621_:
{
lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_623_ = lean_array_fget_borrowed(v___y_622_, v_mid_620_);
v___x_624_ = lean_array_fget_borrowed(v___y_622_, v_hi_605_);
v___x_625_ = lean_string_dec_lt(v___x_623_, v___x_624_);
if (v___x_625_ == 0)
{
lean_dec(v_mid_620_);
v___y_607_ = v___y_622_;
goto v___jp_606_;
}
else
{
lean_object* v___x_626_; 
v___x_626_ = lean_array_fswap(v___y_622_, v_mid_620_, v_hi_605_);
lean_dec(v_mid_620_);
v___y_607_ = v___x_626_;
goto v___jp_606_;
}
}
v___jp_627_:
{
lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_629_ = lean_array_fget_borrowed(v___y_628_, v_hi_605_);
v___x_630_ = lean_array_fget_borrowed(v___y_628_, v_lo_604_);
v___x_631_ = lean_string_dec_lt(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
v___y_622_ = v___y_628_;
goto v___jp_621_;
}
else
{
lean_object* v___x_632_; 
v___x_632_ = lean_array_fswap(v___y_628_, v_lo_604_, v_hi_605_);
v___y_622_ = v___x_632_;
goto v___jp_621_;
}
}
}
v___jp_606_:
{
lean_object* v_pivot_608_; lean_object* v___x_609_; lean_object* v_fst_610_; lean_object* v_snd_611_; uint8_t v___x_612_; 
v_pivot_608_ = lean_array_fget(v___y_607_, v_hi_605_);
lean_inc_n(v_lo_604_, 2);
v___x_609_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_605_, v_pivot_608_, v___y_607_, v_lo_604_, v_lo_604_);
lean_dec(v_pivot_608_);
v_fst_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_fst_610_);
v_snd_611_ = lean_ctor_get(v___x_609_, 1);
lean_inc(v_snd_611_);
lean_dec_ref(v___x_609_);
v___x_612_ = lean_nat_dec_le(v_hi_605_, v_fst_610_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_602_, v_snd_611_, v_lo_604_, v_fst_610_);
v___x_614_ = lean_unsigned_to_nat(1u);
v___x_615_ = lean_nat_add(v_fst_610_, v___x_614_);
lean_dec(v_fst_610_);
v_as_603_ = v___x_613_;
v_lo_604_ = v___x_615_;
goto _start;
}
else
{
lean_dec(v_fst_610_);
lean_dec(v_lo_604_);
return v_snd_611_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_n_637_, lean_object* v_as_638_, lean_object* v_lo_639_, lean_object* v_hi_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_637_, v_as_638_, v_lo_639_, v_hi_640_);
lean_dec(v_hi_640_);
lean_dec(v_n_637_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_644_){
_start:
{
lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v_unexpected_677_; lean_object* v_expected_678_; lean_object* v___y_680_; lean_object* v___x_690_; uint8_t v___x_691_; 
v_unexpected_677_ = lean_ctor_get(v_e_644_, 1);
lean_inc_ref(v_unexpected_677_);
v_expected_678_ = lean_ctor_get(v_e_644_, 2);
lean_inc(v_expected_678_);
lean_dec_ref(v_e_644_);
v___x_690_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_691_ = lean_string_dec_eq(v_unexpected_677_, v___x_690_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_box(0);
v___x_693_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_693_, 0, v_unexpected_677_);
lean_ctor_set(v___x_693_, 1, v___x_692_);
v___y_680_ = v___x_693_;
goto v___jp_679_;
}
else
{
lean_object* v___x_694_; 
lean_dec_ref(v_unexpected_677_);
v___x_694_ = lean_box(0);
v___y_680_ = v___x_694_;
goto v___jp_679_;
}
v___jp_645_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_649_ = l_List_appendTR___redArg(v___y_646_, v___y_647_);
v___x_650_ = l_String_intercalate(v___x_648_, v___x_649_);
return v___x_650_;
}
v___jp_651_:
{
lean_object* v___x_655_; lean_object* v_expected_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_655_ = lean_array_to_list(v___y_654_);
v_expected_656_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_655_);
v___x_657_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_658_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_656_);
v___x_659_ = lean_string_append(v___x_657_, v___x_658_);
lean_dec_ref(v___x_658_);
v___x_660_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_660_, 0, v___x_659_);
lean_ctor_set(v___x_660_, 1, v___y_652_);
v___y_646_ = v___y_653_;
v___y_647_ = v___x_660_;
goto v___jp_645_;
}
v___jp_661_:
{
lean_object* v___x_668_; 
v___x_668_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_665_, v___y_663_, v___y_664_, v___y_667_);
lean_dec(v___y_667_);
lean_dec(v___y_665_);
v___y_652_ = v___y_662_;
v___y_653_ = v___y_666_;
v___y_654_ = v___x_668_;
goto v___jp_651_;
}
v___jp_669_:
{
uint8_t v___x_676_; 
v___x_676_ = lean_nat_dec_le(v___y_675_, v___y_670_);
if (v___x_676_ == 0)
{
lean_dec(v___y_670_);
lean_inc(v___y_675_);
v___y_662_ = v___y_672_;
v___y_663_ = v___y_671_;
v___y_664_ = v___y_675_;
v___y_665_ = v___y_673_;
v___y_666_ = v___y_674_;
v___y_667_ = v___y_675_;
goto v___jp_661_;
}
else
{
v___y_662_ = v___y_672_;
v___y_663_ = v___y_671_;
v___y_664_ = v___y_675_;
v___y_665_ = v___y_673_;
v___y_666_ = v___y_674_;
v___y_667_ = v___y_670_;
goto v___jp_661_;
}
}
v___jp_679_:
{
lean_object* v___x_681_; uint8_t v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_678_, v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v___x_683_ = lean_array_mk(v_expected_678_);
v___x_684_ = lean_array_get_size(v___x_683_);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_nat_dec_eq(v___x_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_687_ = lean_unsigned_to_nat(1u);
v___x_688_ = lean_nat_sub(v___x_684_, v___x_687_);
v___x_689_ = lean_nat_dec_le(v___x_685_, v___x_688_);
if (v___x_689_ == 0)
{
lean_inc(v___x_688_);
v___y_670_ = v___x_688_;
v___y_671_ = v___x_683_;
v___y_672_ = v___x_681_;
v___y_673_ = v___x_684_;
v___y_674_ = v___y_680_;
v___y_675_ = v___x_688_;
goto v___jp_669_;
}
else
{
v___y_670_ = v___x_688_;
v___y_671_ = v___x_683_;
v___y_672_ = v___x_681_;
v___y_673_ = v___x_684_;
v___y_674_ = v___y_680_;
v___y_675_ = v___x_685_;
goto v___jp_669_;
}
}
else
{
v___y_652_ = v___x_681_;
v___y_653_ = v___y_680_;
v___y_654_ = v___x_683_;
goto v___jp_651_;
}
}
else
{
lean_dec(v_expected_678_);
v___y_646_ = v___y_680_;
v___y_647_ = v___x_681_;
goto v___jp_645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_695_, lean_object* v_as_696_, lean_object* v_lo_697_, lean_object* v_hi_698_, lean_object* v_w_699_, lean_object* v_hlo_700_, lean_object* v_hhi_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_695_, v_as_696_, v_lo_697_, v_hi_698_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_703_, lean_object* v_as_704_, lean_object* v_lo_705_, lean_object* v_hi_706_, lean_object* v_w_707_, lean_object* v_hlo_708_, lean_object* v_hhi_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_703_, v_as_704_, v_lo_705_, v_hi_706_, v_w_707_, v_hlo_708_, v_hhi_709_);
lean_dec(v_hi_706_);
lean_dec(v_n_703_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object* v_n_711_, lean_object* v_lo_712_, lean_object* v_hi_713_, lean_object* v_hhi_714_, lean_object* v_pivot_715_, lean_object* v_as_716_, lean_object* v_i_717_, lean_object* v_k_718_, lean_object* v_ilo_719_, lean_object* v_ik_720_, lean_object* v_w_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_713_, v_pivot_715_, v_as_716_, v_i_717_, v_k_718_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object* v_n_723_, lean_object* v_lo_724_, lean_object* v_hi_725_, lean_object* v_hhi_726_, lean_object* v_pivot_727_, lean_object* v_as_728_, lean_object* v_i_729_, lean_object* v_k_730_, lean_object* v_ilo_731_, lean_object* v_ik_732_, lean_object* v_w_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_723_, v_lo_724_, v_hi_725_, v_hhi_726_, v_pivot_727_, v_as_728_, v_i_729_, v_k_730_, v_ilo_731_, v_ik_732_, v_w_733_);
lean_dec_ref(v_pivot_727_);
lean_dec(v_hi_725_);
lean_dec(v_lo_724_);
lean_dec(v_n_723_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_737_, lean_object* v_e_u2082_738_){
_start:
{
lean_object* v_unexpectedTk_739_; lean_object* v_unexpected_740_; lean_object* v_expected_741_; lean_object* v___y_743_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_unexpectedTk_739_ = lean_ctor_get(v_e_u2082_738_, 0);
lean_inc(v_unexpectedTk_739_);
v_unexpected_740_ = lean_ctor_get(v_e_u2082_738_, 1);
lean_inc_ref(v_unexpected_740_);
v_expected_741_ = lean_ctor_get(v_e_u2082_738_, 2);
lean_inc(v_expected_741_);
lean_dec_ref(v_e_u2082_738_);
v___x_755_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_756_ = lean_string_dec_eq(v_unexpected_740_, v___x_755_);
if (v___x_756_ == 0)
{
v___y_743_ = v_unexpected_740_;
goto v___jp_742_;
}
else
{
lean_object* v_unexpected_757_; 
lean_dec_ref(v_unexpected_740_);
v_unexpected_757_ = lean_ctor_get(v_e_u2081_737_, 1);
lean_inc_ref(v_unexpected_757_);
v___y_743_ = v_unexpected_757_;
goto v___jp_742_;
}
v___jp_742_:
{
lean_object* v_expected_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_expected_744_ = lean_ctor_get(v_e_u2081_737_, 2);
v_isSharedCheck_752_ = !lean_is_exclusive(v_e_u2081_737_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; lean_object* v_unused_754_; 
v_unused_753_ = lean_ctor_get(v_e_u2081_737_, 1);
lean_dec(v_unused_753_);
v_unused_754_ = lean_ctor_get(v_e_u2081_737_, 0);
lean_dec(v_unused_754_);
v___x_746_ = v_e_u2081_737_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_expected_744_);
lean_dec(v_e_u2081_737_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = l_List_appendTR___redArg(v_expected_744_, v_expected_741_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 2, v___x_748_);
lean_ctor_set(v___x_746_, 1, v___y_743_);
lean_ctor_set(v___x_746_, 0, v_unexpectedTk_739_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_unexpectedTk_739_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v___y_743_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(lean_object* v_x_758_, lean_object* v_x_759_){
_start:
{
if (lean_obj_tag(v_x_758_) == 0)
{
if (lean_obj_tag(v_x_759_) == 0)
{
uint8_t v___x_760_; 
v___x_760_ = 1;
return v___x_760_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = 0;
return v___x_761_;
}
}
else
{
if (lean_obj_tag(v_x_759_) == 0)
{
uint8_t v___x_762_; 
v___x_762_ = 0;
return v___x_762_;
}
else
{
lean_object* v_val_763_; lean_object* v_val_764_; uint8_t v___x_765_; 
v_val_763_ = lean_ctor_get(v_x_758_, 0);
v_val_764_ = lean_ctor_get(v_x_759_, 0);
v___x_765_ = lean_nat_dec_eq(v_val_763_, v_val_764_);
return v___x_765_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0___boxed(lean_object* v_x_766_, lean_object* v_x_767_){
_start:
{
uint8_t v_res_768_; lean_object* v_r_769_; 
v_res_768_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_x_766_, v_x_767_);
lean_dec(v_x_767_);
lean_dec(v_x_766_);
v_r_769_ = lean_box(v_res_768_);
return v_r_769_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(lean_object* v_xs_770_, lean_object* v_ys_771_, lean_object* v_x_772_){
_start:
{
lean_object* v_zero_773_; uint8_t v_isZero_774_; 
v_zero_773_ = lean_unsigned_to_nat(0u);
v_isZero_774_ = lean_nat_dec_eq(v_x_772_, v_zero_773_);
if (v_isZero_774_ == 1)
{
lean_dec(v_x_772_);
return v_isZero_774_;
}
else
{
lean_object* v_one_775_; lean_object* v_n_776_; lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v_one_775_ = lean_unsigned_to_nat(1u);
v_n_776_ = lean_nat_sub(v_x_772_, v_one_775_);
lean_dec(v_x_772_);
v___x_777_ = lean_array_fget_borrowed(v_xs_770_, v_n_776_);
v___x_778_ = lean_array_fget_borrowed(v_ys_771_, v_n_776_);
v___x_779_ = lean_string_dec_eq(v___x_777_, v___x_778_);
if (v___x_779_ == 0)
{
lean_dec(v_n_776_);
return v___x_779_;
}
else
{
v_x_772_ = v_n_776_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg___boxed(lean_object* v_xs_781_, lean_object* v_ys_782_, lean_object* v_x_783_){
_start:
{
uint8_t v_res_784_; lean_object* v_r_785_; 
v_res_784_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_781_, v_ys_782_, v_x_783_);
lean_dec_ref(v_ys_782_);
lean_dec_ref(v_xs_781_);
v_r_785_ = lean_box(v_res_784_);
return v_r_785_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_786_, lean_object* v_x_787_){
_start:
{
lean_object* v_toCacheableParserContext_788_; lean_object* v_parserName_789_; lean_object* v_pos_790_; lean_object* v_toCacheableParserContext_791_; lean_object* v_parserName_792_; lean_object* v_pos_793_; uint8_t v___y_795_; lean_object* v_prec_798_; lean_object* v_quotDepth_799_; uint8_t v_suppressInsideQuot_800_; lean_object* v_savedPos_x3f_801_; lean_object* v_forbiddenTks_802_; lean_object* v_prec_803_; lean_object* v_quotDepth_804_; uint8_t v_suppressInsideQuot_805_; lean_object* v_savedPos_x3f_806_; lean_object* v_forbiddenTks_807_; uint8_t v___y_818_; uint8_t v___x_819_; 
v_toCacheableParserContext_788_ = lean_ctor_get(v_x_786_, 0);
v_parserName_789_ = lean_ctor_get(v_x_786_, 1);
v_pos_790_ = lean_ctor_get(v_x_786_, 2);
v_toCacheableParserContext_791_ = lean_ctor_get(v_x_787_, 0);
v_parserName_792_ = lean_ctor_get(v_x_787_, 1);
v_pos_793_ = lean_ctor_get(v_x_787_, 2);
v_prec_798_ = lean_ctor_get(v_toCacheableParserContext_788_, 0);
v_quotDepth_799_ = lean_ctor_get(v_toCacheableParserContext_788_, 1);
v_suppressInsideQuot_800_ = lean_ctor_get_uint8(v_toCacheableParserContext_788_, sizeof(void*)*4);
v_savedPos_x3f_801_ = lean_ctor_get(v_toCacheableParserContext_788_, 2);
v_forbiddenTks_802_ = lean_ctor_get(v_toCacheableParserContext_788_, 3);
v_prec_803_ = lean_ctor_get(v_toCacheableParserContext_791_, 0);
v_quotDepth_804_ = lean_ctor_get(v_toCacheableParserContext_791_, 1);
v_suppressInsideQuot_805_ = lean_ctor_get_uint8(v_toCacheableParserContext_791_, sizeof(void*)*4);
v_savedPos_x3f_806_ = lean_ctor_get(v_toCacheableParserContext_791_, 2);
v_forbiddenTks_807_ = lean_ctor_get(v_toCacheableParserContext_791_, 3);
v___x_819_ = lean_nat_dec_eq(v_prec_798_, v_prec_803_);
if (v___x_819_ == 0)
{
v___y_818_ = v___x_819_;
goto v___jp_817_;
}
else
{
uint8_t v___x_820_; 
v___x_820_ = lean_nat_dec_eq(v_quotDepth_799_, v_quotDepth_804_);
v___y_818_ = v___x_820_;
goto v___jp_817_;
}
v___jp_794_:
{
if (v___y_795_ == 0)
{
return v___y_795_;
}
else
{
uint8_t v___x_796_; 
v___x_796_ = lean_name_eq(v_parserName_789_, v_parserName_792_);
if (v___x_796_ == 0)
{
return v___x_796_;
}
else
{
uint8_t v___x_797_; 
v___x_797_ = lean_nat_dec_eq(v_pos_790_, v_pos_793_);
return v___x_797_;
}
}
}
v___jp_808_:
{
uint8_t v___x_809_; 
v___x_809_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_savedPos_x3f_801_, v_savedPos_x3f_806_);
if (v___x_809_ == 0)
{
v___y_795_ = v___x_809_;
goto v___jp_794_;
}
else
{
size_t v___x_810_; size_t v___x_811_; uint8_t v___x_812_; 
v___x_810_ = lean_ptr_addr(v_forbiddenTks_802_);
v___x_811_ = lean_ptr_addr(v_forbiddenTks_807_);
v___x_812_ = lean_usize_dec_eq(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
lean_object* v___x_813_; lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_813_ = lean_array_get_size(v_forbiddenTks_802_);
v___x_814_ = lean_array_get_size(v_forbiddenTks_807_);
v___x_815_ = lean_nat_dec_eq(v___x_813_, v___x_814_);
if (v___x_815_ == 0)
{
v___y_795_ = v___x_812_;
goto v___jp_794_;
}
else
{
uint8_t v___x_816_; 
v___x_816_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_forbiddenTks_802_, v_forbiddenTks_807_, v___x_813_);
v___y_795_ = v___x_816_;
goto v___jp_794_;
}
}
else
{
v___y_795_ = v___x_812_;
goto v___jp_794_;
}
}
}
v___jp_817_:
{
if (v___y_818_ == 0)
{
return v___y_818_;
}
else
{
if (v_suppressInsideQuot_800_ == 0)
{
if (v_suppressInsideQuot_805_ == 0)
{
goto v___jp_808_;
}
else
{
return v_suppressInsideQuot_800_;
}
}
else
{
if (v_suppressInsideQuot_805_ == 0)
{
return v_suppressInsideQuot_805_;
}
else
{
goto v___jp_808_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
uint8_t v_res_823_; lean_object* v_r_824_; 
v_res_823_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_821_, v_x_822_);
lean_dec_ref(v_x_822_);
lean_dec_ref(v_x_821_);
v_r_824_ = lean_box(v_res_823_);
return v_r_824_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(lean_object* v_xs_825_, lean_object* v_ys_826_, lean_object* v_hsz_827_, lean_object* v_x_828_, lean_object* v_x_829_){
_start:
{
uint8_t v___x_830_; 
v___x_830_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_825_, v_ys_826_, v_x_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___boxed(lean_object* v_xs_831_, lean_object* v_ys_832_, lean_object* v_hsz_833_, lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(v_xs_831_, v_ys_832_, v_hsz_833_, v_x_834_, v_x_835_);
lean_dec_ref(v_ys_832_);
lean_dec_ref(v_xs_831_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* v_k_840_){
_start:
{
lean_object* v_parserName_841_; lean_object* v_pos_842_; uint64_t v___x_843_; 
v_parserName_841_ = lean_ctor_get(v_k_840_, 1);
v_pos_842_ = lean_ctor_get(v_k_840_, 2);
v___x_843_ = l_String_instHashableRaw_hash(v_pos_842_);
if (lean_obj_tag(v_parserName_841_) == 0)
{
uint64_t v___x_844_; uint64_t v___x_845_; 
v___x_844_ = 1723ULL;
v___x_845_ = lean_uint64_mix_hash(v___x_843_, v___x_844_);
return v___x_845_;
}
else
{
uint64_t v_hash_846_; uint64_t v___x_847_; 
v_hash_846_ = lean_ctor_get_uint64(v_parserName_841_, sizeof(void*)*2);
v___x_847_ = lean_uint64_mix_hash(v___x_843_, v_hash_846_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* v_k_848_){
_start:
{
uint64_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_848_);
lean_dec_ref(v_k_848_);
v_r_850_ = lean_box_uint64(v_res_849_);
return v_r_850_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0(void){
_start:
{
uint32_t v___x_853_; lean_object* v___x_854_; 
v___x_853_ = 32;
v___x_854_ = l_Char_utf8Size(v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_box(0);
v___x_856_ = lean_unsigned_to_nat(16u);
v___x_857_ = lean_mk_array(v___x_856_, v___x_855_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__2(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_858_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_858_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_862_ = lean_string_utf8_byte_size(v_input_861_);
v___x_863_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_864_ = lean_nat_add(v___x_862_, v___x_863_);
v___x_865_ = lean_unsigned_to_nat(0u);
v___x_866_ = lean_box(0);
v___x_867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_867_, 0, v___x_864_);
lean_ctor_set(v___x_867_, 1, v___x_865_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
v___x_868_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_867_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Parser_initCacheForInput(v_input_870_);
lean_dec_ref(v_input_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_872_){
_start:
{
lean_object* v_raw_873_; lean_object* v_drop_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_raw_873_ = lean_ctor_get(v_stack_872_, 0);
lean_inc_ref(v_raw_873_);
v_drop_874_ = lean_ctor_get(v_stack_872_, 1);
lean_inc(v_drop_874_);
lean_dec_ref(v_stack_872_);
v___x_875_ = lean_array_get_size(v_raw_873_);
v___x_876_ = l_Array_toSubarray___redArg(v_raw_873_, v_drop_874_, v___x_875_);
return v___x_876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_883_){
_start:
{
lean_object* v_raw_884_; lean_object* v_drop_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_raw_884_ = lean_ctor_get(v_stack_883_, 0);
v_drop_885_ = lean_ctor_get(v_stack_883_, 1);
v___x_886_ = lean_array_get_size(v_raw_884_);
v___x_887_ = lean_nat_sub(v___x_886_, v_drop_885_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lean_Parser_SyntaxStack_size(v_stack_888_);
lean_dec_ref(v_stack_888_);
return v_res_889_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_890_){
_start:
{
lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_891_ = l_Lean_Parser_SyntaxStack_size(v_stack_890_);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_nat_dec_eq(v___x_891_, v___x_892_);
lean_dec(v___x_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_894_){
_start:
{
uint8_t v_res_895_; lean_object* v_r_896_; 
v_res_895_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_894_);
lean_dec_ref(v_stack_894_);
v_r_896_ = lean_box(v_res_895_);
return v_r_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_897_, lean_object* v_n_898_){
_start:
{
lean_object* v_raw_899_; lean_object* v_drop_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_909_; 
v_raw_899_ = lean_ctor_get(v_stack_897_, 0);
v_drop_900_ = lean_ctor_get(v_stack_897_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_stack_897_);
if (v_isSharedCheck_909_ == 0)
{
v___x_902_ = v_stack_897_;
v_isShared_903_ = v_isSharedCheck_909_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_drop_900_);
lean_inc(v_raw_899_);
lean_dec(v_stack_897_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_909_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_907_; 
v___x_904_ = lean_nat_add(v_drop_900_, v_n_898_);
v___x_905_ = l_Array_shrink___redArg(v_raw_899_, v___x_904_);
lean_dec(v___x_904_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_905_);
v___x_907_ = v___x_902_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_905_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_drop_900_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_910_, lean_object* v_n_911_){
_start:
{
lean_object* v_res_912_; 
v_res_912_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_910_, v_n_911_);
lean_dec(v_n_911_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_913_, lean_object* v_a_914_){
_start:
{
lean_object* v_raw_915_; lean_object* v_drop_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_924_; 
v_raw_915_ = lean_ctor_get(v_stack_913_, 0);
v_drop_916_ = lean_ctor_get(v_stack_913_, 1);
v_isSharedCheck_924_ = !lean_is_exclusive(v_stack_913_);
if (v_isSharedCheck_924_ == 0)
{
v___x_918_ = v_stack_913_;
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_drop_916_);
lean_inc(v_raw_915_);
lean_dec(v_stack_913_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_924_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_920_ = lean_array_push(v_raw_915_, v_a_914_);
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_920_);
v___x_922_ = v___x_918_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
lean_ctor_set(v_reuseFailAlloc_923_, 1, v_drop_916_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_925_){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = l_Lean_Parser_SyntaxStack_size(v_stack_925_);
v___x_928_ = lean_nat_dec_lt(v___x_926_, v___x_927_);
lean_dec(v___x_927_);
if (v___x_928_ == 0)
{
return v_stack_925_;
}
else
{
lean_object* v_raw_929_; lean_object* v_drop_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_938_; 
v_raw_929_ = lean_ctor_get(v_stack_925_, 0);
v_drop_930_ = lean_ctor_get(v_stack_925_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_stack_925_);
if (v_isSharedCheck_938_ == 0)
{
v___x_932_ = v_stack_925_;
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_drop_930_);
lean_inc(v_raw_929_);
lean_dec(v_stack_925_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = lean_array_pop(v_raw_929_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_936_ = v___x_932_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_drop_930_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_939_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = lean_box(0);
v___x_941_ = lean_panic_fn_borrowed(v___x_940_, v_msg_939_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_945_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_946_ = lean_unsigned_to_nat(4u);
v___x_947_ = lean_unsigned_to_nat(313u);
v___x_948_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_949_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_950_ = l_mkPanicMessageWithDecl(v___x_949_, v___x_948_, v___x_947_, v___x_946_, v___x_945_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_951_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = l_Lean_Parser_SyntaxStack_size(v_stack_951_);
v___x_954_ = lean_nat_dec_lt(v___x_952_, v___x_953_);
lean_dec(v___x_953_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_956_; 
v___x_955_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_956_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_955_);
return v___x_956_;
}
else
{
lean_object* v_raw_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_raw_957_ = lean_ctor_get(v_stack_951_, 0);
v___x_958_ = lean_box(0);
v___x_959_ = lean_array_get_size(v_raw_957_);
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_sub(v___x_959_, v___x_960_);
v___x_962_ = lean_array_get_borrowed(v___x_958_, v_raw_957_, v___x_961_);
lean_dec(v___x_961_);
lean_inc(v___x_962_);
return v___x_962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_Parser_SyntaxStack_back(v_stack_963_);
lean_dec_ref(v_stack_963_);
return v_res_964_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_967_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_968_ = lean_unsigned_to_nat(4u);
v___x_969_ = lean_unsigned_to_nat(319u);
v___x_970_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_971_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_972_ = l_mkPanicMessageWithDecl(v___x_971_, v___x_970_, v___x_969_, v___x_968_, v___x_967_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_973_, lean_object* v_i_974_){
_start:
{
lean_object* v___x_975_; uint8_t v___x_976_; 
v___x_975_ = l_Lean_Parser_SyntaxStack_size(v_stack_973_);
v___x_976_ = lean_nat_dec_lt(v_i_974_, v___x_975_);
lean_dec(v___x_975_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; lean_object* v___x_978_; 
v___x_977_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_978_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_977_);
return v___x_978_;
}
else
{
lean_object* v_raw_979_; lean_object* v_drop_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_raw_979_ = lean_ctor_get(v_stack_973_, 0);
v_drop_980_ = lean_ctor_get(v_stack_973_, 1);
v___x_981_ = lean_box(0);
v___x_982_ = lean_nat_add(v_drop_980_, v_i_974_);
v___x_983_ = lean_array_get_borrowed(v___x_981_, v_raw_979_, v___x_982_);
lean_dec(v___x_982_);
lean_inc(v___x_983_);
return v___x_983_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_984_, lean_object* v_i_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_984_, v_i_985_);
lean_dec(v_i_985_);
lean_dec_ref(v_stack_984_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_987_, lean_object* v_start_988_, lean_object* v_stop_989_){
_start:
{
lean_object* v_raw_990_; lean_object* v_drop_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v_raw_990_ = lean_ctor_get(v_stack_987_, 0);
v_drop_991_ = lean_ctor_get(v_stack_987_, 1);
v___x_992_ = lean_nat_add(v_drop_991_, v_start_988_);
v___x_993_ = lean_nat_add(v_drop_991_, v_stop_989_);
v___x_994_ = l_Array_extract___redArg(v_raw_990_, v___x_992_, v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_995_, lean_object* v_start_996_, lean_object* v_stop_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Parser_SyntaxStack_extract(v_stack_995_, v_start_996_, v_stop_997_);
lean_dec(v_stop_997_);
lean_dec(v_start_996_);
lean_dec_ref(v_stack_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_999_, lean_object* v_stxs_1000_){
_start:
{
lean_object* v_raw_1001_; lean_object* v_drop_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1010_; 
v_raw_1001_ = lean_ctor_get(v_stack_999_, 0);
v_drop_1002_ = lean_ctor_get(v_stack_999_, 1);
v_isSharedCheck_1010_ = !lean_is_exclusive(v_stack_999_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1004_ = v_stack_999_;
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_drop_1002_);
lean_inc(v_raw_1001_);
lean_dec(v_stack_999_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1010_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1006_ = l_Array_append___redArg(v_raw_1001_, v_stxs_1000_);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1006_);
v___x_1008_ = v___x_1004_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1009_, 1, v_drop_1002_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_1011_, lean_object* v_stxs_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_1011_, v_stxs_1012_);
lean_dec_ref(v_stxs_1012_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_1014_, lean_object* v_stxs_1015_){
_start:
{
lean_object* v_raw_1016_; lean_object* v_drop_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1025_; 
v_raw_1016_ = lean_ctor_get(v_stack_1014_, 0);
v_drop_1017_ = lean_ctor_get(v_stack_1014_, 1);
v_isSharedCheck_1025_ = !lean_is_exclusive(v_stack_1014_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1019_ = v_stack_1014_;
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_drop_1017_);
lean_inc(v_raw_1016_);
lean_dec(v_stack_1014_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1025_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = l_Array_append___redArg(v_raw_1016_, v_stxs_1015_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 0, v___x_1021_);
v___x_1023_ = v___x_1019_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v_drop_1017_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_1026_, lean_object* v_stxs_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_1026_, v_stxs_1027_);
lean_dec_ref(v_stxs_1027_);
return v_res_1028_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_1031_){
_start:
{
lean_object* v_errorMsg_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_errorMsg_1032_ = lean_ctor_get(v_s_1031_, 4);
lean_inc(v_errorMsg_1032_);
lean_dec_ref(v_s_1031_);
v___x_1033_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_1034_ = lean_box(0);
v___x_1035_ = l_Option_instBEq_beq___redArg(v___x_1033_, v_errorMsg_1032_, v___x_1034_);
if (v___x_1035_ == 0)
{
uint8_t v___x_1036_; 
v___x_1036_ = 1;
return v___x_1036_;
}
else
{
uint8_t v___x_1037_; 
v___x_1037_ = 0;
return v___x_1037_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_1038_){
_start:
{
uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_res_1039_ = l_Lean_Parser_ParserState_hasError(v_s_1038_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_1041_){
_start:
{
lean_object* v_stxStack_1042_; lean_object* v___x_1043_; 
v_stxStack_1042_ = lean_ctor_get(v_s_1041_, 0);
v___x_1043_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1042_);
return v___x_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Parser_ParserState_stackSize(v_s_1044_);
lean_dec_ref(v_s_1044_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_1046_, lean_object* v_iniStackSz_1047_, lean_object* v_iniPos_1048_){
_start:
{
lean_object* v_stxStack_1049_; lean_object* v_lhsPrec_1050_; lean_object* v_cache_1051_; lean_object* v_recoveredErrors_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1061_; 
v_stxStack_1049_ = lean_ctor_get(v_s_1046_, 0);
v_lhsPrec_1050_ = lean_ctor_get(v_s_1046_, 1);
v_cache_1051_ = lean_ctor_get(v_s_1046_, 3);
v_recoveredErrors_1052_ = lean_ctor_get(v_s_1046_, 5);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_s_1046_);
if (v_isSharedCheck_1061_ == 0)
{
lean_object* v_unused_1062_; lean_object* v_unused_1063_; 
v_unused_1062_ = lean_ctor_get(v_s_1046_, 4);
lean_dec(v_unused_1062_);
v_unused_1063_ = lean_ctor_get(v_s_1046_, 2);
lean_dec(v_unused_1063_);
v___x_1054_ = v_s_1046_;
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_recoveredErrors_1052_);
lean_inc(v_cache_1051_);
lean_inc(v_lhsPrec_1050_);
lean_inc(v_stxStack_1049_);
lean_dec(v_s_1046_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1061_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1056_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1049_, v_iniStackSz_1047_);
v___x_1057_ = lean_box(0);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 4, v___x_1057_);
lean_ctor_set(v___x_1054_, 2, v_iniPos_1048_);
lean_ctor_set(v___x_1054_, 0, v___x_1056_);
v___x_1059_ = v___x_1054_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1056_);
lean_ctor_set(v_reuseFailAlloc_1060_, 1, v_lhsPrec_1050_);
lean_ctor_set(v_reuseFailAlloc_1060_, 2, v_iniPos_1048_);
lean_ctor_set(v_reuseFailAlloc_1060_, 3, v_cache_1051_);
lean_ctor_set(v_reuseFailAlloc_1060_, 4, v___x_1057_);
lean_ctor_set(v_reuseFailAlloc_1060_, 5, v_recoveredErrors_1052_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_1064_, lean_object* v_iniStackSz_1065_, lean_object* v_iniPos_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Parser_ParserState_restore(v_s_1064_, v_iniStackSz_1065_, v_iniPos_1066_);
lean_dec(v_iniStackSz_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_1068_, lean_object* v_pos_1069_){
_start:
{
lean_object* v_stxStack_1070_; lean_object* v_lhsPrec_1071_; lean_object* v_cache_1072_; lean_object* v_errorMsg_1073_; lean_object* v_recoveredErrors_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
v_stxStack_1070_ = lean_ctor_get(v_s_1068_, 0);
v_lhsPrec_1071_ = lean_ctor_get(v_s_1068_, 1);
v_cache_1072_ = lean_ctor_get(v_s_1068_, 3);
v_errorMsg_1073_ = lean_ctor_get(v_s_1068_, 4);
v_recoveredErrors_1074_ = lean_ctor_get(v_s_1068_, 5);
v_isSharedCheck_1081_ = !lean_is_exclusive(v_s_1068_);
if (v_isSharedCheck_1081_ == 0)
{
lean_object* v_unused_1082_; 
v_unused_1082_ = lean_ctor_get(v_s_1068_, 2);
lean_dec(v_unused_1082_);
v___x_1076_ = v_s_1068_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_recoveredErrors_1074_);
lean_inc(v_errorMsg_1073_);
lean_inc(v_cache_1072_);
lean_inc(v_lhsPrec_1071_);
lean_inc(v_stxStack_1070_);
lean_dec(v_s_1068_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 2, v_pos_1069_);
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_stxStack_1070_);
lean_ctor_set(v_reuseFailAlloc_1080_, 1, v_lhsPrec_1071_);
lean_ctor_set(v_reuseFailAlloc_1080_, 2, v_pos_1069_);
lean_ctor_set(v_reuseFailAlloc_1080_, 3, v_cache_1072_);
lean_ctor_set(v_reuseFailAlloc_1080_, 4, v_errorMsg_1073_);
lean_ctor_set(v_reuseFailAlloc_1080_, 5, v_recoveredErrors_1074_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_1083_, lean_object* v_cache_1084_){
_start:
{
lean_object* v_stxStack_1085_; lean_object* v_lhsPrec_1086_; lean_object* v_pos_1087_; lean_object* v_errorMsg_1088_; lean_object* v_recoveredErrors_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_stxStack_1085_ = lean_ctor_get(v_s_1083_, 0);
v_lhsPrec_1086_ = lean_ctor_get(v_s_1083_, 1);
v_pos_1087_ = lean_ctor_get(v_s_1083_, 2);
v_errorMsg_1088_ = lean_ctor_get(v_s_1083_, 4);
v_recoveredErrors_1089_ = lean_ctor_get(v_s_1083_, 5);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_s_1083_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_s_1083_, 3);
lean_dec(v_unused_1097_);
v___x_1091_ = v_s_1083_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_recoveredErrors_1089_);
lean_inc(v_errorMsg_1088_);
lean_inc(v_pos_1087_);
lean_inc(v_lhsPrec_1086_);
lean_inc(v_stxStack_1085_);
lean_dec(v_s_1083_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 3, v_cache_1084_);
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_stxStack_1085_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_lhsPrec_1086_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v_pos_1087_);
lean_ctor_set(v_reuseFailAlloc_1095_, 3, v_cache_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 4, v_errorMsg_1088_);
lean_ctor_set(v_reuseFailAlloc_1095_, 5, v_recoveredErrors_1089_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_1098_, lean_object* v_n_1099_){
_start:
{
lean_object* v_stxStack_1100_; lean_object* v_lhsPrec_1101_; lean_object* v_pos_1102_; lean_object* v_cache_1103_; lean_object* v_errorMsg_1104_; lean_object* v_recoveredErrors_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1113_; 
v_stxStack_1100_ = lean_ctor_get(v_s_1098_, 0);
v_lhsPrec_1101_ = lean_ctor_get(v_s_1098_, 1);
v_pos_1102_ = lean_ctor_get(v_s_1098_, 2);
v_cache_1103_ = lean_ctor_get(v_s_1098_, 3);
v_errorMsg_1104_ = lean_ctor_get(v_s_1098_, 4);
v_recoveredErrors_1105_ = lean_ctor_get(v_s_1098_, 5);
v_isSharedCheck_1113_ = !lean_is_exclusive(v_s_1098_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1107_ = v_s_1098_;
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_recoveredErrors_1105_);
lean_inc(v_errorMsg_1104_);
lean_inc(v_cache_1103_);
lean_inc(v_pos_1102_);
lean_inc(v_lhsPrec_1101_);
lean_inc(v_stxStack_1100_);
lean_dec(v_s_1098_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1113_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1111_; 
v___x_1109_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1100_, v_n_1099_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v___x_1109_);
v___x_1111_ = v___x_1107_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_lhsPrec_1101_);
lean_ctor_set(v_reuseFailAlloc_1112_, 2, v_pos_1102_);
lean_ctor_set(v_reuseFailAlloc_1112_, 3, v_cache_1103_);
lean_ctor_set(v_reuseFailAlloc_1112_, 4, v_errorMsg_1104_);
lean_ctor_set(v_reuseFailAlloc_1112_, 5, v_recoveredErrors_1105_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1114_){
_start:
{
lean_object* v_stxStack_1115_; lean_object* v_lhsPrec_1116_; lean_object* v_pos_1117_; lean_object* v_cache_1118_; lean_object* v_errorMsg_1119_; lean_object* v_recoveredErrors_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1128_; 
v_stxStack_1115_ = lean_ctor_get(v_s_1114_, 0);
v_lhsPrec_1116_ = lean_ctor_get(v_s_1114_, 1);
v_pos_1117_ = lean_ctor_get(v_s_1114_, 2);
v_cache_1118_ = lean_ctor_get(v_s_1114_, 3);
v_errorMsg_1119_ = lean_ctor_get(v_s_1114_, 4);
v_recoveredErrors_1120_ = lean_ctor_get(v_s_1114_, 5);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_s_1114_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1122_ = v_s_1114_;
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_recoveredErrors_1120_);
lean_inc(v_errorMsg_1119_);
lean_inc(v_cache_1118_);
lean_inc(v_pos_1117_);
lean_inc(v_lhsPrec_1116_);
lean_inc(v_stxStack_1115_);
lean_dec(v_s_1114_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1128_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1126_; 
v___x_1124_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1115_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1124_);
v___x_1126_ = v___x_1122_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_lhsPrec_1116_);
lean_ctor_set(v_reuseFailAlloc_1127_, 2, v_pos_1117_);
lean_ctor_set(v_reuseFailAlloc_1127_, 3, v_cache_1118_);
lean_ctor_set(v_reuseFailAlloc_1127_, 4, v_errorMsg_1119_);
lean_ctor_set(v_reuseFailAlloc_1127_, 5, v_recoveredErrors_1120_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1129_, lean_object* v_iniStackSz_1130_){
_start:
{
lean_object* v_stxStack_1131_; lean_object* v_lhsPrec_1132_; lean_object* v_pos_1133_; lean_object* v_cache_1134_; lean_object* v_errorMsg_1135_; lean_object* v_recoveredErrors_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1144_; 
v_stxStack_1131_ = lean_ctor_get(v_s_1129_, 0);
v_lhsPrec_1132_ = lean_ctor_get(v_s_1129_, 1);
v_pos_1133_ = lean_ctor_get(v_s_1129_, 2);
v_cache_1134_ = lean_ctor_get(v_s_1129_, 3);
v_errorMsg_1135_ = lean_ctor_get(v_s_1129_, 4);
v_recoveredErrors_1136_ = lean_ctor_get(v_s_1129_, 5);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_s_1129_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1138_ = v_s_1129_;
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_recoveredErrors_1136_);
lean_inc(v_errorMsg_1135_);
lean_inc(v_cache_1134_);
lean_inc(v_pos_1133_);
lean_inc(v_lhsPrec_1132_);
lean_inc(v_stxStack_1131_);
lean_dec(v_s_1129_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1144_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; lean_object* v___x_1142_; 
v___x_1140_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1131_, v_iniStackSz_1130_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 0, v___x_1140_);
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_lhsPrec_1132_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v_pos_1133_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_cache_1134_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_errorMsg_1135_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v_recoveredErrors_1136_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1145_, lean_object* v_iniStackSz_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1145_, v_iniStackSz_1146_);
lean_dec(v_iniStackSz_1146_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1148_, lean_object* v_c_1149_, lean_object* v_pos_1150_){
_start:
{
lean_object* v_toInputContext_1151_; lean_object* v_stxStack_1152_; lean_object* v_lhsPrec_1153_; lean_object* v_cache_1154_; lean_object* v_errorMsg_1155_; lean_object* v_recoveredErrors_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1165_; 
v_toInputContext_1151_ = lean_ctor_get(v_c_1149_, 0);
v_stxStack_1152_ = lean_ctor_get(v_s_1148_, 0);
v_lhsPrec_1153_ = lean_ctor_get(v_s_1148_, 1);
v_cache_1154_ = lean_ctor_get(v_s_1148_, 3);
v_errorMsg_1155_ = lean_ctor_get(v_s_1148_, 4);
v_recoveredErrors_1156_ = lean_ctor_get(v_s_1148_, 5);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_s_1148_);
if (v_isSharedCheck_1165_ == 0)
{
lean_object* v_unused_1166_; 
v_unused_1166_ = lean_ctor_get(v_s_1148_, 2);
lean_dec(v_unused_1166_);
v___x_1158_ = v_s_1148_;
v_isShared_1159_ = v_isSharedCheck_1165_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_recoveredErrors_1156_);
lean_inc(v_errorMsg_1155_);
lean_inc(v_cache_1154_);
lean_inc(v_lhsPrec_1153_);
lean_inc(v_stxStack_1152_);
lean_dec(v_s_1148_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1165_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v_inputString_1160_; lean_object* v___x_1161_; lean_object* v___x_1163_; 
v_inputString_1160_ = lean_ctor_get(v_toInputContext_1151_, 0);
v___x_1161_ = lean_string_utf8_next(v_inputString_1160_, v_pos_1150_);
if (v_isShared_1159_ == 0)
{
lean_ctor_set(v___x_1158_, 2, v___x_1161_);
v___x_1163_ = v___x_1158_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_stxStack_1152_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_lhsPrec_1153_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_cache_1154_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_errorMsg_1155_);
lean_ctor_set(v_reuseFailAlloc_1164_, 5, v_recoveredErrors_1156_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1167_, lean_object* v_c_1168_, lean_object* v_pos_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Lean_Parser_ParserState_next(v_s_1167_, v_c_1168_, v_pos_1169_);
lean_dec(v_pos_1169_);
lean_dec_ref(v_c_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1171_, lean_object* v_c_1172_, lean_object* v_pos_1173_){
_start:
{
lean_object* v_toInputContext_1174_; lean_object* v_stxStack_1175_; lean_object* v_lhsPrec_1176_; lean_object* v_cache_1177_; lean_object* v_errorMsg_1178_; lean_object* v_recoveredErrors_1179_; lean_object* v___x_1181_; uint8_t v_isShared_1182_; uint8_t v_isSharedCheck_1188_; 
v_toInputContext_1174_ = lean_ctor_get(v_c_1172_, 0);
v_stxStack_1175_ = lean_ctor_get(v_s_1171_, 0);
v_lhsPrec_1176_ = lean_ctor_get(v_s_1171_, 1);
v_cache_1177_ = lean_ctor_get(v_s_1171_, 3);
v_errorMsg_1178_ = lean_ctor_get(v_s_1171_, 4);
v_recoveredErrors_1179_ = lean_ctor_get(v_s_1171_, 5);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_s_1171_);
if (v_isSharedCheck_1188_ == 0)
{
lean_object* v_unused_1189_; 
v_unused_1189_ = lean_ctor_get(v_s_1171_, 2);
lean_dec(v_unused_1189_);
v___x_1181_ = v_s_1171_;
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
else
{
lean_inc(v_recoveredErrors_1179_);
lean_inc(v_errorMsg_1178_);
lean_inc(v_cache_1177_);
lean_inc(v_lhsPrec_1176_);
lean_inc(v_stxStack_1175_);
lean_dec(v_s_1171_);
v___x_1181_ = lean_box(0);
v_isShared_1182_ = v_isSharedCheck_1188_;
goto v_resetjp_1180_;
}
v_resetjp_1180_:
{
lean_object* v_inputString_1183_; lean_object* v___x_1184_; lean_object* v___x_1186_; 
v_inputString_1183_ = lean_ctor_get(v_toInputContext_1174_, 0);
v___x_1184_ = lean_string_utf8_next_fast(v_inputString_1183_, v_pos_1173_);
if (v_isShared_1182_ == 0)
{
lean_ctor_set(v___x_1181_, 2, v___x_1184_);
v___x_1186_ = v___x_1181_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_stxStack_1175_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_lhsPrec_1176_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v___x_1184_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_cache_1177_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v_errorMsg_1178_);
lean_ctor_set(v_reuseFailAlloc_1187_, 5, v_recoveredErrors_1179_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1190_, lean_object* v_c_1191_, lean_object* v_pos_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1190_, v_c_1191_, v_pos_1192_);
lean_dec(v_pos_1192_);
lean_dec_ref(v_c_1191_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1194_, lean_object* v_c_1195_, lean_object* v_pos_1196_, lean_object* v_h_1197_){
_start:
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1194_, v_c_1195_, v_pos_1196_);
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1199_, lean_object* v_c_1200_, lean_object* v_pos_1201_, lean_object* v_h_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Lean_Parser_ParserState_next_x27(v_s_1199_, v_c_1200_, v_pos_1201_, v_h_1202_);
lean_dec(v_pos_1201_);
lean_dec_ref(v_c_1200_);
return v_res_1203_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1204_, lean_object* v_x_1205_){
_start:
{
if (lean_obj_tag(v_x_1204_) == 0)
{
if (lean_obj_tag(v_x_1205_) == 0)
{
uint8_t v___x_1206_; 
v___x_1206_ = 1;
return v___x_1206_;
}
else
{
uint8_t v___x_1207_; 
v___x_1207_ = 0;
return v___x_1207_;
}
}
else
{
if (lean_obj_tag(v_x_1205_) == 0)
{
uint8_t v___x_1208_; 
v___x_1208_ = 0;
return v___x_1208_;
}
else
{
lean_object* v_val_1209_; lean_object* v_val_1210_; uint8_t v___x_1211_; 
v_val_1209_ = lean_ctor_get(v_x_1204_, 0);
v_val_1210_ = lean_ctor_get(v_x_1205_, 0);
v___x_1211_ = l_Lean_Parser_instBEqError_beq(v_val_1209_, v_val_1210_);
return v___x_1211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1212_, lean_object* v_x_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1212_, v_x_1213_);
lean_dec(v_x_1213_);
lean_dec(v_x_1212_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1216_, lean_object* v_k_1217_, lean_object* v_iniStackSz_1218_){
_start:
{
lean_object* v_stxStack_1219_; lean_object* v_lhsPrec_1220_; lean_object* v_pos_1221_; lean_object* v_cache_1222_; lean_object* v_errorMsg_1223_; lean_object* v_recoveredErrors_1224_; lean_object* v___x_1226_; uint8_t v_isShared_1227_; uint8_t v_isSharedCheck_1245_; 
v_stxStack_1219_ = lean_ctor_get(v_s_1216_, 0);
v_lhsPrec_1220_ = lean_ctor_get(v_s_1216_, 1);
v_pos_1221_ = lean_ctor_get(v_s_1216_, 2);
v_cache_1222_ = lean_ctor_get(v_s_1216_, 3);
v_errorMsg_1223_ = lean_ctor_get(v_s_1216_, 4);
v_recoveredErrors_1224_ = lean_ctor_get(v_s_1216_, 5);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_s_1216_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1226_ = v_s_1216_;
v_isShared_1227_ = v_isSharedCheck_1245_;
goto v_resetjp_1225_;
}
else
{
lean_inc(v_recoveredErrors_1224_);
lean_inc(v_errorMsg_1223_);
lean_inc(v_cache_1222_);
lean_inc(v_pos_1221_);
lean_inc(v_lhsPrec_1220_);
lean_inc(v_stxStack_1219_);
lean_dec(v_s_1216_);
v___x_1226_ = lean_box(0);
v_isShared_1227_ = v_isSharedCheck_1245_;
goto v_resetjp_1225_;
}
v_resetjp_1225_:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_box(0);
v___x_1239_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1223_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1219_);
v___x_1241_ = lean_nat_dec_eq(v___x_1240_, v_iniStackSz_1218_);
lean_dec(v___x_1240_);
if (v___x_1241_ == 0)
{
goto v___jp_1228_;
}
else
{
lean_object* v___x_1242_; lean_object* v_stack_1243_; lean_object* v___x_1244_; 
lean_del_object(v___x_1226_);
lean_dec(v_k_1217_);
v___x_1242_ = lean_box(0);
v_stack_1243_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1219_, v___x_1242_);
v___x_1244_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1244_, 0, v_stack_1243_);
lean_ctor_set(v___x_1244_, 1, v_lhsPrec_1220_);
lean_ctor_set(v___x_1244_, 2, v_pos_1221_);
lean_ctor_set(v___x_1244_, 3, v_cache_1222_);
lean_ctor_set(v___x_1244_, 4, v_errorMsg_1223_);
lean_ctor_set(v___x_1244_, 5, v_recoveredErrors_1224_);
return v___x_1244_;
}
}
else
{
goto v___jp_1228_;
}
v___jp_1228_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v_newNode_1232_; lean_object* v_stack_1233_; lean_object* v_stack_1234_; lean_object* v___x_1236_; 
v___x_1229_ = lean_box(2);
v___x_1230_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1219_);
v___x_1231_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1219_, v_iniStackSz_1218_, v___x_1230_);
lean_dec(v___x_1230_);
v_newNode_1232_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1232_, 0, v___x_1229_);
lean_ctor_set(v_newNode_1232_, 1, v_k_1217_);
lean_ctor_set(v_newNode_1232_, 2, v___x_1231_);
v_stack_1233_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1219_, v_iniStackSz_1218_);
v_stack_1234_ = l_Lean_Parser_SyntaxStack_push(v_stack_1233_, v_newNode_1232_);
if (v_isShared_1227_ == 0)
{
lean_ctor_set(v___x_1226_, 0, v_stack_1234_);
v___x_1236_ = v___x_1226_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_stack_1234_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_lhsPrec_1220_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_pos_1221_);
lean_ctor_set(v_reuseFailAlloc_1237_, 3, v_cache_1222_);
lean_ctor_set(v_reuseFailAlloc_1237_, 4, v_errorMsg_1223_);
lean_ctor_set(v_reuseFailAlloc_1237_, 5, v_recoveredErrors_1224_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1246_, lean_object* v_k_1247_, lean_object* v_iniStackSz_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_Parser_ParserState_mkNode(v_s_1246_, v_k_1247_, v_iniStackSz_1248_);
lean_dec(v_iniStackSz_1248_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1250_, lean_object* v_k_1251_, lean_object* v_iniStackSz_1252_){
_start:
{
lean_object* v_stxStack_1253_; lean_object* v_lhsPrec_1254_; lean_object* v_pos_1255_; lean_object* v_cache_1256_; lean_object* v_errorMsg_1257_; lean_object* v_recoveredErrors_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1273_; 
v_stxStack_1253_ = lean_ctor_get(v_s_1250_, 0);
v_lhsPrec_1254_ = lean_ctor_get(v_s_1250_, 1);
v_pos_1255_ = lean_ctor_get(v_s_1250_, 2);
v_cache_1256_ = lean_ctor_get(v_s_1250_, 3);
v_errorMsg_1257_ = lean_ctor_get(v_s_1250_, 4);
v_recoveredErrors_1258_ = lean_ctor_get(v_s_1250_, 5);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_s_1250_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1260_ = v_s_1250_;
v_isShared_1261_ = v_isSharedCheck_1273_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_recoveredErrors_1258_);
lean_inc(v_errorMsg_1257_);
lean_inc(v_cache_1256_);
lean_inc(v_pos_1255_);
lean_inc(v_lhsPrec_1254_);
lean_inc(v_stxStack_1253_);
lean_dec(v_s_1250_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1273_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_newNode_1267_; lean_object* v_stack_1268_; lean_object* v_stack_1269_; lean_object* v___x_1271_; 
v___x_1262_ = lean_box(2);
v___x_1263_ = lean_unsigned_to_nat(1u);
v___x_1264_ = lean_nat_sub(v_iniStackSz_1252_, v___x_1263_);
v___x_1265_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1253_);
v___x_1266_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1253_, v___x_1264_, v___x_1265_);
lean_dec(v___x_1265_);
v_newNode_1267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1267_, 0, v___x_1262_);
lean_ctor_set(v_newNode_1267_, 1, v_k_1251_);
lean_ctor_set(v_newNode_1267_, 2, v___x_1266_);
v_stack_1268_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1253_, v___x_1264_);
lean_dec(v___x_1264_);
v_stack_1269_ = l_Lean_Parser_SyntaxStack_push(v_stack_1268_, v_newNode_1267_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v_stack_1269_);
v___x_1271_ = v___x_1260_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_stack_1269_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v_lhsPrec_1254_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_pos_1255_);
lean_ctor_set(v_reuseFailAlloc_1272_, 3, v_cache_1256_);
lean_ctor_set(v_reuseFailAlloc_1272_, 4, v_errorMsg_1257_);
lean_ctor_set(v_reuseFailAlloc_1272_, 5, v_recoveredErrors_1258_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1274_, lean_object* v_k_1275_, lean_object* v_iniStackSz_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1274_, v_k_1275_, v_iniStackSz_1276_);
lean_dec(v_iniStackSz_1276_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1280_){
_start:
{
lean_object* v_errorMsg_1281_; 
v_errorMsg_1281_ = lean_ctor_get(v_s_1280_, 4);
if (lean_obj_tag(v_errorMsg_1281_) == 0)
{
lean_object* v_recoveredErrors_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; 
v_recoveredErrors_1282_ = lean_ctor_get(v_s_1280_, 5);
lean_inc_ref(v_recoveredErrors_1282_);
lean_dec_ref(v_s_1280_);
v___x_1283_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1284_ = l_Array_append___redArg(v_recoveredErrors_1282_, v___x_1283_);
return v___x_1284_;
}
else
{
lean_object* v_stxStack_1285_; lean_object* v_pos_1286_; lean_object* v_recoveredErrors_1287_; lean_object* v_val_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_inc_ref(v_errorMsg_1281_);
v_stxStack_1285_ = lean_ctor_get(v_s_1280_, 0);
lean_inc_ref(v_stxStack_1285_);
v_pos_1286_ = lean_ctor_get(v_s_1280_, 2);
lean_inc(v_pos_1286_);
v_recoveredErrors_1287_ = lean_ctor_get(v_s_1280_, 5);
lean_inc_ref(v_recoveredErrors_1287_);
lean_dec_ref(v_s_1280_);
v_val_1288_ = lean_ctor_get(v_errorMsg_1281_, 0);
lean_inc(v_val_1288_);
lean_dec_ref_known(v_errorMsg_1281_, 1);
v___x_1289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1289_, 0, v_stxStack_1285_);
lean_ctor_set(v___x_1289_, 1, v_val_1288_);
v___x_1290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1290_, 0, v_pos_1286_);
lean_ctor_set(v___x_1290_, 1, v___x_1289_);
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_mk_empty_array_with_capacity(v___x_1291_);
v___x_1293_ = lean_array_push(v___x_1292_, v___x_1290_);
v___x_1294_ = l_Array_append___redArg(v_recoveredErrors_1287_, v___x_1293_);
lean_dec_ref(v___x_1293_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1295_, lean_object* v_e_1296_){
_start:
{
lean_object* v_stxStack_1297_; lean_object* v_lhsPrec_1298_; lean_object* v_pos_1299_; lean_object* v_cache_1300_; lean_object* v_recoveredErrors_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1309_; 
v_stxStack_1297_ = lean_ctor_get(v_s_1295_, 0);
v_lhsPrec_1298_ = lean_ctor_get(v_s_1295_, 1);
v_pos_1299_ = lean_ctor_get(v_s_1295_, 2);
v_cache_1300_ = lean_ctor_get(v_s_1295_, 3);
v_recoveredErrors_1301_ = lean_ctor_get(v_s_1295_, 5);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_s_1295_);
if (v_isSharedCheck_1309_ == 0)
{
lean_object* v_unused_1310_; 
v_unused_1310_ = lean_ctor_get(v_s_1295_, 4);
lean_dec(v_unused_1310_);
v___x_1303_ = v_s_1295_;
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_recoveredErrors_1301_);
lean_inc(v_cache_1300_);
lean_inc(v_pos_1299_);
lean_inc(v_lhsPrec_1298_);
lean_inc(v_stxStack_1297_);
lean_dec(v_s_1295_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1309_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1305_, 0, v_e_1296_);
if (v_isShared_1304_ == 0)
{
lean_ctor_set(v___x_1303_, 4, v___x_1305_);
v___x_1307_ = v___x_1303_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_stxStack_1297_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_lhsPrec_1298_);
lean_ctor_set(v_reuseFailAlloc_1308_, 2, v_pos_1299_);
lean_ctor_set(v_reuseFailAlloc_1308_, 3, v_cache_1300_);
lean_ctor_set(v_reuseFailAlloc_1308_, 4, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1308_, 5, v_recoveredErrors_1301_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1311_, lean_object* v_msg_1312_){
_start:
{
lean_object* v_stxStack_1313_; lean_object* v_lhsPrec_1314_; lean_object* v_pos_1315_; lean_object* v_cache_1316_; lean_object* v_recoveredErrors_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1331_; 
v_stxStack_1313_ = lean_ctor_get(v_s_1311_, 0);
v_lhsPrec_1314_ = lean_ctor_get(v_s_1311_, 1);
v_pos_1315_ = lean_ctor_get(v_s_1311_, 2);
v_cache_1316_ = lean_ctor_get(v_s_1311_, 3);
v_recoveredErrors_1317_ = lean_ctor_get(v_s_1311_, 5);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_s_1311_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v_s_1311_, 4);
lean_dec(v_unused_1332_);
v___x_1319_ = v_s_1311_;
v_isShared_1320_ = v_isSharedCheck_1331_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_recoveredErrors_1317_);
lean_inc(v_cache_1316_);
lean_inc(v_pos_1315_);
lean_inc(v_lhsPrec_1314_);
lean_inc(v_stxStack_1313_);
lean_dec(v_s_1311_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1331_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1321_ = lean_box(0);
v___x_1322_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1323_ = lean_box(0);
v___x_1324_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_msg_1312_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1321_);
lean_ctor_set(v___x_1325_, 1, v___x_1322_);
lean_ctor_set(v___x_1325_, 2, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set(v___x_1319_, 4, v___x_1326_);
v___x_1328_ = v___x_1319_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_stxStack_1313_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_lhsPrec_1314_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_pos_1315_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_cache_1316_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1330_, 5, v_recoveredErrors_1317_);
v___x_1328_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1328_, v___x_1321_);
return v___x_1329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1333_, lean_object* v_msg_1334_, lean_object* v_expected_1335_, uint8_t v_pushMissing_1336_){
_start:
{
lean_object* v_stxStack_1337_; lean_object* v_lhsPrec_1338_; lean_object* v_pos_1339_; lean_object* v_cache_1340_; lean_object* v_recoveredErrors_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1352_; 
v_stxStack_1337_ = lean_ctor_get(v_s_1333_, 0);
v_lhsPrec_1338_ = lean_ctor_get(v_s_1333_, 1);
v_pos_1339_ = lean_ctor_get(v_s_1333_, 2);
v_cache_1340_ = lean_ctor_get(v_s_1333_, 3);
v_recoveredErrors_1341_ = lean_ctor_get(v_s_1333_, 5);
v_isSharedCheck_1352_ = !lean_is_exclusive(v_s_1333_);
if (v_isSharedCheck_1352_ == 0)
{
lean_object* v_unused_1353_; 
v_unused_1353_ = lean_ctor_get(v_s_1333_, 4);
lean_dec(v_unused_1353_);
v___x_1343_ = v_s_1333_;
v_isShared_1344_ = v_isSharedCheck_1352_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_recoveredErrors_1341_);
lean_inc(v_cache_1340_);
lean_inc(v_pos_1339_);
lean_inc(v_lhsPrec_1338_);
lean_inc(v_stxStack_1337_);
lean_dec(v_s_1333_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1352_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v_s_1349_; 
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v_msg_1334_);
lean_ctor_set(v___x_1346_, 2, v_expected_1335_);
v___x_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1346_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v___x_1347_);
v_s_1349_ = v___x_1343_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_stxStack_1337_);
lean_ctor_set(v_reuseFailAlloc_1351_, 1, v_lhsPrec_1338_);
lean_ctor_set(v_reuseFailAlloc_1351_, 2, v_pos_1339_);
lean_ctor_set(v_reuseFailAlloc_1351_, 3, v_cache_1340_);
lean_ctor_set(v_reuseFailAlloc_1351_, 4, v___x_1347_);
lean_ctor_set(v_reuseFailAlloc_1351_, 5, v_recoveredErrors_1341_);
v_s_1349_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
if (v_pushMissing_1336_ == 0)
{
return v_s_1349_;
}
else
{
lean_object* v___x_1350_; 
v___x_1350_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1349_, v___x_1345_);
return v___x_1350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1354_, lean_object* v_msg_1355_, lean_object* v_expected_1356_, lean_object* v_pushMissing_1357_){
_start:
{
uint8_t v_pushMissing_boxed_1358_; lean_object* v_res_1359_; 
v_pushMissing_boxed_1358_ = lean_unbox(v_pushMissing_1357_);
v_res_1359_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1354_, v_msg_1355_, v_expected_1356_, v_pushMissing_boxed_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1361_, lean_object* v_expected_1362_){
_start:
{
lean_object* v___x_1363_; uint8_t v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1364_ = 1;
v___x_1365_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1361_, v___x_1363_, v_expected_1362_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1366_, lean_object* v_ex_1367_, lean_object* v_pos_1368_, lean_object* v_initStackSz_x3f_1369_){
_start:
{
lean_object* v_s_1371_; lean_object* v_s_1390_; 
v_s_1390_ = l_Lean_Parser_ParserState_setPos(v_s_1366_, v_pos_1368_);
if (lean_obj_tag(v_initStackSz_x3f_1369_) == 1)
{
lean_object* v_val_1391_; lean_object* v_s_1392_; 
v_val_1391_ = lean_ctor_get(v_initStackSz_x3f_1369_, 0);
v_s_1392_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1390_, v_val_1391_);
v_s_1371_ = v_s_1392_;
goto v___jp_1370_;
}
else
{
v_s_1371_ = v_s_1390_;
goto v___jp_1370_;
}
v___jp_1370_:
{
lean_object* v_stxStack_1372_; lean_object* v_lhsPrec_1373_; lean_object* v_pos_1374_; lean_object* v_cache_1375_; lean_object* v_recoveredErrors_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1388_; 
v_stxStack_1372_ = lean_ctor_get(v_s_1371_, 0);
v_lhsPrec_1373_ = lean_ctor_get(v_s_1371_, 1);
v_pos_1374_ = lean_ctor_get(v_s_1371_, 2);
v_cache_1375_ = lean_ctor_get(v_s_1371_, 3);
v_recoveredErrors_1376_ = lean_ctor_get(v_s_1371_, 5);
v_isSharedCheck_1388_ = !lean_is_exclusive(v_s_1371_);
if (v_isSharedCheck_1388_ == 0)
{
lean_object* v_unused_1389_; 
v_unused_1389_ = lean_ctor_get(v_s_1371_, 4);
lean_dec(v_unused_1389_);
v___x_1378_ = v_s_1371_;
v_isShared_1379_ = v_isSharedCheck_1388_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_recoveredErrors_1376_);
lean_inc(v_cache_1375_);
lean_inc(v_pos_1374_);
lean_inc(v_lhsPrec_1373_);
lean_inc(v_stxStack_1372_);
lean_dec(v_s_1371_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1388_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v_s_1385_; 
v___x_1380_ = lean_box(0);
v___x_1381_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1382_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1380_);
lean_ctor_set(v___x_1382_, 1, v___x_1381_);
lean_ctor_set(v___x_1382_, 2, v_ex_1367_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
if (v_isShared_1379_ == 0)
{
lean_ctor_set(v___x_1378_, 4, v___x_1383_);
v_s_1385_ = v___x_1378_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_stxStack_1372_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v_lhsPrec_1373_);
lean_ctor_set(v_reuseFailAlloc_1387_, 2, v_pos_1374_);
lean_ctor_set(v_reuseFailAlloc_1387_, 3, v_cache_1375_);
lean_ctor_set(v_reuseFailAlloc_1387_, 4, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1387_, 5, v_recoveredErrors_1376_);
v_s_1385_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1385_, v___x_1380_);
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1393_, lean_object* v_ex_1394_, lean_object* v_pos_1395_, lean_object* v_initStackSz_x3f_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1393_, v_ex_1394_, v_pos_1395_, v_initStackSz_x3f_1396_);
lean_dec(v_initStackSz_x3f_1396_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1398_, lean_object* v_msg_1399_, lean_object* v_pos_1400_, lean_object* v_initStackSz_x3f_1401_){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
v___x_1402_ = lean_box(0);
v___x_1403_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_msg_1399_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1398_, v___x_1403_, v_pos_1400_, v_initStackSz_x3f_1401_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1405_, lean_object* v_msg_1406_, lean_object* v_pos_1407_, lean_object* v_initStackSz_x3f_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1405_, v_msg_1406_, v_pos_1407_, v_initStackSz_x3f_1408_);
lean_dec(v_initStackSz_x3f_1408_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; 
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = lean_panic_fn_borrowed(v___x_1411_, v_msg_1410_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1416_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1417_ = lean_unsigned_to_nat(14u);
v___x_1418_ = lean_unsigned_to_nat(22u);
v___x_1419_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1420_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1421_ = l_mkPanicMessageWithDecl(v___x_1420_, v___x_1419_, v___x_1418_, v___x_1417_, v___x_1416_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1422_, lean_object* v_ex_1423_, lean_object* v_iniPos_1424_){
_start:
{
lean_object* v_stxStack_1425_; lean_object* v_tk_1426_; lean_object* v___y_1428_; lean_object* v___x_1449_; uint8_t v___x_1450_; 
v_stxStack_1425_ = lean_ctor_get(v_s_1422_, 0);
v_tk_1426_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1425_);
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = lean_nat_dec_lt(v___x_1449_, v_iniPos_1424_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1451_; 
lean_dec(v_iniPos_1424_);
v___x_1451_ = l_Lean_Syntax_getPos_x3f(v_tk_1426_, v___x_1450_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1452_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1453_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1452_);
v___y_1428_ = v___x_1453_;
goto v___jp_1427_;
}
else
{
lean_object* v_val_1454_; 
v_val_1454_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_val_1454_);
lean_dec_ref_known(v___x_1451_, 1);
v___y_1428_ = v_val_1454_;
goto v___jp_1427_;
}
}
else
{
v___y_1428_ = v_iniPos_1424_;
goto v___jp_1427_;
}
v___jp_1427_:
{
lean_object* v_s_1429_; lean_object* v_stxStack_1430_; lean_object* v_lhsPrec_1431_; lean_object* v_pos_1432_; lean_object* v_cache_1433_; lean_object* v_recoveredErrors_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1447_; 
v_s_1429_ = l_Lean_Parser_ParserState_setPos(v_s_1422_, v___y_1428_);
v_stxStack_1430_ = lean_ctor_get(v_s_1429_, 0);
v_lhsPrec_1431_ = lean_ctor_get(v_s_1429_, 1);
v_pos_1432_ = lean_ctor_get(v_s_1429_, 2);
v_cache_1433_ = lean_ctor_get(v_s_1429_, 3);
v_recoveredErrors_1434_ = lean_ctor_get(v_s_1429_, 5);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_s_1429_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; 
v_unused_1448_ = lean_ctor_get(v_s_1429_, 4);
lean_dec(v_unused_1448_);
v___x_1436_ = v_s_1429_;
v_isShared_1437_ = v_isSharedCheck_1447_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_recoveredErrors_1434_);
lean_inc(v_cache_1433_);
lean_inc(v_pos_1432_);
lean_inc(v_lhsPrec_1431_);
lean_inc(v_stxStack_1430_);
lean_dec(v_s_1429_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1447_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v_s_1442_; 
v___x_1438_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1439_, 0, v_tk_1426_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
lean_ctor_set(v___x_1439_, 2, v_ex_1423_);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 4, v___x_1440_);
v_s_1442_ = v___x_1436_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_stxStack_1430_);
lean_ctor_set(v_reuseFailAlloc_1446_, 1, v_lhsPrec_1431_);
lean_ctor_set(v_reuseFailAlloc_1446_, 2, v_pos_1432_);
lean_ctor_set(v_reuseFailAlloc_1446_, 3, v_cache_1433_);
lean_ctor_set(v_reuseFailAlloc_1446_, 4, v___x_1440_);
lean_ctor_set(v_reuseFailAlloc_1446_, 5, v_recoveredErrors_1434_);
v_s_1442_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1443_ = l_Lean_Parser_ParserState_popSyntax(v_s_1442_);
v___x_1444_ = lean_box(0);
v___x_1445_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1443_, v___x_1444_);
return v___x_1445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1455_, lean_object* v_msg_1456_, lean_object* v_iniPos_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_box(0);
v___x_1459_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1459_, 0, v_msg_1456_);
lean_ctor_set(v___x_1459_, 1, v___x_1458_);
v___x_1460_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1455_, v___x_1459_, v_iniPos_1457_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1461_, lean_object* v_msg_1462_, lean_object* v_pos_1463_){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; lean_object* v___x_1467_; 
v___x_1464_ = l_Lean_Parser_ParserState_setPos(v_s_1461_, v_pos_1463_);
v___x_1465_ = lean_box(0);
v___x_1466_ = 1;
v___x_1467_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1464_, v_msg_1462_, v___x_1465_, v___x_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1469_, lean_object* v_as_1470_, size_t v_sz_1471_, size_t v_i_1472_, lean_object* v_b_1473_){
_start:
{
uint8_t v___x_1474_; 
v___x_1474_ = lean_usize_dec_lt(v_i_1472_, v_sz_1471_);
if (v___x_1474_ == 0)
{
lean_dec_ref(v_ctx_1469_);
return v_b_1473_;
}
else
{
lean_object* v_a_1475_; lean_object* v_snd_1476_; lean_object* v_fst_1477_; lean_object* v_snd_1478_; lean_object* v_errStr_1480_; lean_object* v_errStr_1491_; uint8_t v___x_1492_; 
v_a_1475_ = lean_array_uget_borrowed(v_as_1470_, v_i_1472_);
v_snd_1476_ = lean_ctor_get(v_a_1475_, 1);
v_fst_1477_ = lean_ctor_get(v_a_1475_, 0);
v_snd_1478_ = lean_ctor_get(v_snd_1476_, 1);
v_errStr_1491_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1492_ = lean_string_dec_eq(v_b_1473_, v_errStr_1491_);
if (v___x_1492_ == 0)
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1494_ = lean_string_append(v_b_1473_, v___x_1493_);
v_errStr_1480_ = v___x_1494_;
goto v___jp_1479_;
}
else
{
v_errStr_1480_ = v_b_1473_;
goto v___jp_1479_;
}
v___jp_1479_:
{
lean_object* v_fileName_1481_; lean_object* v_fileMap_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; size_t v___x_1488_; size_t v___x_1489_; 
v_fileName_1481_ = lean_ctor_get(v_ctx_1469_, 1);
v_fileMap_1482_ = lean_ctor_get(v_ctx_1469_, 2);
lean_inc_ref(v_fileMap_1482_);
v___x_1483_ = l_Lean_FileMap_toPosition(v_fileMap_1482_, v_fst_1477_);
lean_inc(v_snd_1478_);
v___x_1484_ = l_Lean_Parser_Error_toString(v_snd_1478_);
v___x_1485_ = lean_box(0);
lean_inc_ref(v_fileName_1481_);
v___x_1486_ = l_Lean_mkErrorStringWithPos(v_fileName_1481_, v___x_1483_, v___x_1484_, v___x_1485_, v___x_1485_, v___x_1485_);
lean_dec_ref(v___x_1484_);
v___x_1487_ = lean_string_append(v_errStr_1480_, v___x_1486_);
lean_dec_ref(v___x_1486_);
v___x_1488_ = ((size_t)1ULL);
v___x_1489_ = lean_usize_add(v_i_1472_, v___x_1488_);
v_i_1472_ = v___x_1489_;
v_b_1473_ = v___x_1487_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1495_, lean_object* v_as_1496_, lean_object* v_sz_1497_, lean_object* v_i_1498_, lean_object* v_b_1499_){
_start:
{
size_t v_sz_boxed_1500_; size_t v_i_boxed_1501_; lean_object* v_res_1502_; 
v_sz_boxed_1500_ = lean_unbox_usize(v_sz_1497_);
lean_dec(v_sz_1497_);
v_i_boxed_1501_ = lean_unbox_usize(v_i_1498_);
lean_dec(v_i_1498_);
v_res_1502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1495_, v_as_1496_, v_sz_boxed_1500_, v_i_boxed_1501_, v_b_1499_);
lean_dec_ref(v_as_1496_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1503_, lean_object* v_s_1504_){
_start:
{
lean_object* v_errStr_1505_; lean_object* v___x_1506_; size_t v_sz_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
v_errStr_1505_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1506_ = l_Lean_Parser_ParserState_allErrors(v_s_1504_);
v_sz_1507_ = lean_array_size(v___x_1506_);
v___x_1508_ = ((size_t)0ULL);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1503_, v___x_1506_, v_sz_1507_, v___x_1508_, v_errStr_1505_);
lean_dec_ref(v___x_1506_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1510_, lean_object* v_s_1511_){
_start:
{
lean_inc_ref(v_s_1511_);
return v_s_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1512_, lean_object* v_s_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1512_, v_s_1513_);
lean_dec_ref(v_s_1513_);
lean_dec_ref(v_x_1512_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx(lean_object* v_x_1517_){
_start:
{
switch(lean_obj_tag(v_x_1517_))
{
case 0:
{
lean_object* v___x_1518_; 
v___x_1518_ = lean_unsigned_to_nat(0u);
return v___x_1518_;
}
case 1:
{
lean_object* v___x_1519_; 
v___x_1519_ = lean_unsigned_to_nat(1u);
return v___x_1519_;
}
case 2:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_unsigned_to_nat(2u);
return v___x_1520_;
}
default: 
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_unsigned_to_nat(3u);
return v___x_1521_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___boxed(lean_object* v_x_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Parser_FirstTokens_ctorIdx(v_x_1522_);
lean_dec(v_x_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1524_, lean_object* v_k_1525_){
_start:
{
switch(lean_obj_tag(v_t_1524_))
{
case 2:
{
lean_object* v_a_1526_; lean_object* v___x_1527_; 
v_a_1526_ = lean_ctor_get(v_t_1524_, 0);
lean_inc(v_a_1526_);
lean_dec_ref_known(v_t_1524_, 1);
v___x_1527_ = lean_apply_1(v_k_1525_, v_a_1526_);
return v___x_1527_;
}
case 3:
{
lean_object* v_a_1528_; lean_object* v___x_1529_; 
v_a_1528_ = lean_ctor_get(v_t_1524_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v_t_1524_, 1);
v___x_1529_ = lean_apply_1(v_k_1525_, v_a_1528_);
return v___x_1529_;
}
default: 
{
lean_dec(v_t_1524_);
return v_k_1525_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1530_, lean_object* v_ctorIdx_1531_, lean_object* v_t_1532_, lean_object* v_h_1533_, lean_object* v_k_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1532_, v_k_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1536_, lean_object* v_ctorIdx_1537_, lean_object* v_t_1538_, lean_object* v_h_1539_, lean_object* v_k_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1536_, v_ctorIdx_1537_, v_t_1538_, v_h_1539_, v_k_1540_);
lean_dec(v_ctorIdx_1537_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1542_, lean_object* v_epsilon_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1542_, v_epsilon_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1545_, lean_object* v_t_1546_, lean_object* v_h_1547_, lean_object* v_epsilon_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1546_, v_epsilon_1548_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1550_, lean_object* v_unknown_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1550_, v_unknown_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1553_, lean_object* v_t_1554_, lean_object* v_h_1555_, lean_object* v_unknown_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1554_, v_unknown_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1558_, lean_object* v_tokens_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1558_, v_tokens_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1561_, lean_object* v_t_1562_, lean_object* v_h_1563_, lean_object* v_tokens_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1562_, v_tokens_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1566_, lean_object* v_optTokens_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1566_, v_optTokens_1567_);
return v___x_1568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1569_, lean_object* v_t_1570_, lean_object* v_h_1571_, lean_object* v_optTokens_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1570_, v_optTokens_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = lean_box(0);
return v___x_1574_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = lean_box(0);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1576_, lean_object* v_x_1577_){
_start:
{
switch(lean_obj_tag(v_x_1576_))
{
case 0:
{
return v_x_1577_;
}
case 3:
{
switch(lean_obj_tag(v_x_1577_))
{
case 3:
{
lean_object* v_a_1578_; lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1587_; 
v_a_1578_ = lean_ctor_get(v_x_1576_, 0);
lean_inc(v_a_1578_);
lean_dec_ref_known(v_x_1576_, 1);
v_a_1579_ = lean_ctor_get(v_x_1577_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_x_1577_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1581_ = v_x_1577_;
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v_x_1577_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1587_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1583_ = l_List_appendTR___redArg(v_a_1578_, v_a_1579_);
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1585_ = v___x_1581_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
case 2:
{
lean_object* v_a_1588_; lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1597_; 
v_a_1588_ = lean_ctor_get(v_x_1576_, 0);
lean_inc(v_a_1588_);
lean_dec_ref_known(v_x_1576_, 1);
v_a_1589_ = lean_ctor_get(v_x_1577_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_x_1577_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1591_ = v_x_1577_;
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v_x_1577_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1597_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1593_ = l_List_appendTR___redArg(v_a_1588_, v_a_1589_);
if (v_isShared_1592_ == 0)
{
lean_ctor_set(v___x_1591_, 0, v___x_1593_);
v___x_1595_ = v___x_1591_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
return v___x_1595_;
}
}
}
case 1:
{
lean_dec_ref_known(v_x_1576_, 1);
return v_x_1577_;
}
default: 
{
lean_dec(v_x_1577_);
return v_x_1576_;
}
}
}
default: 
{
lean_dec(v_x_1577_);
return v_x_1576_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1598_){
_start:
{
if (lean_obj_tag(v_x_1598_) == 2)
{
lean_object* v_a_1599_; lean_object* v___x_1601_; uint8_t v_isShared_1602_; uint8_t v_isSharedCheck_1606_; 
v_a_1599_ = lean_ctor_get(v_x_1598_, 0);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_x_1598_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1601_ = v_x_1598_;
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
else
{
lean_inc(v_a_1599_);
lean_dec(v_x_1598_);
v___x_1601_ = lean_box(0);
v_isShared_1602_ = v_isSharedCheck_1606_;
goto v_resetjp_1600_;
}
v_resetjp_1600_:
{
lean_object* v___x_1604_; 
if (v_isShared_1602_ == 0)
{
lean_ctor_set_tag(v___x_1601_, 3);
v___x_1604_ = v___x_1601_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_a_1599_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
else
{
return v_x_1598_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
lean_object* v_s_u2081_1610_; lean_object* v_s_u2082_1611_; 
switch(lean_obj_tag(v_x_1607_))
{
case 0:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1608_);
return v___x_1614_;
}
case 2:
{
switch(lean_obj_tag(v_x_1608_))
{
case 0:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1607_);
return v___x_1615_;
}
case 2:
{
lean_object* v_a_1616_; lean_object* v_a_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1625_; 
v_a_1616_ = lean_ctor_get(v_x_1607_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v_x_1607_, 1);
v_a_1617_ = lean_ctor_get(v_x_1608_, 0);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_x_1608_);
if (v_isSharedCheck_1625_ == 0)
{
v___x_1619_ = v_x_1608_;
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_a_1617_);
lean_dec(v_x_1608_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = l_List_appendTR___redArg(v_a_1616_, v_a_1617_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 0, v___x_1621_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
case 3:
{
lean_object* v_a_1626_; lean_object* v_a_1627_; 
v_a_1626_ = lean_ctor_get(v_x_1607_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v_x_1607_, 1);
v_a_1627_ = lean_ctor_get(v_x_1608_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v_x_1608_, 1);
v_s_u2081_1610_ = v_a_1626_;
v_s_u2082_1611_ = v_a_1627_;
goto v___jp_1609_;
}
default: 
{
lean_object* v___x_1628_; 
lean_dec_ref_known(v_x_1607_, 1);
lean_dec(v_x_1608_);
v___x_1628_ = lean_box(1);
return v___x_1628_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1608_))
{
case 0:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1607_);
return v___x_1629_;
}
case 3:
{
lean_object* v_a_1630_; lean_object* v_a_1631_; 
v_a_1630_ = lean_ctor_get(v_x_1607_, 0);
lean_inc(v_a_1630_);
lean_dec_ref_known(v_x_1607_, 1);
v_a_1631_ = lean_ctor_get(v_x_1608_, 0);
lean_inc(v_a_1631_);
lean_dec_ref_known(v_x_1608_, 1);
v_s_u2081_1610_ = v_a_1630_;
v_s_u2082_1611_ = v_a_1631_;
goto v___jp_1609_;
}
case 2:
{
lean_object* v_a_1632_; lean_object* v_a_1633_; 
v_a_1632_ = lean_ctor_get(v_x_1607_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v_x_1607_, 1);
v_a_1633_ = lean_ctor_get(v_x_1608_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v_x_1608_, 1);
v_s_u2081_1610_ = v_a_1632_;
v_s_u2082_1611_ = v_a_1633_;
goto v___jp_1609_;
}
default: 
{
lean_object* v___x_1634_; 
lean_dec_ref_known(v_x_1607_, 1);
lean_dec(v_x_1608_);
v___x_1634_ = lean_box(1);
return v___x_1634_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1608_) == 0)
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1607_);
return v___x_1635_;
}
else
{
lean_object* v___x_1636_; 
lean_dec(v_x_1608_);
lean_dec(v_x_1607_);
v___x_1636_ = lean_box(1);
return v___x_1636_;
}
}
}
v___jp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = l_List_appendTR___redArg(v_s_u2081_1610_, v_s_u2082_1611_);
v___x_1613_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
return v___x_1613_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1637_, lean_object* v_x_1638_){
_start:
{
if (lean_obj_tag(v_x_1638_) == 0)
{
return v_x_1637_;
}
else
{
lean_object* v_head_1639_; lean_object* v_tail_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v_head_1639_ = lean_ctor_get(v_x_1638_, 0);
v_tail_1640_ = lean_ctor_get(v_x_1638_, 1);
v___x_1641_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1642_ = lean_string_append(v_x_1637_, v___x_1641_);
v___x_1643_ = lean_string_append(v___x_1642_, v_head_1639_);
v_x_1637_ = v___x_1643_;
v_x_1638_ = v_tail_1640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1645_, lean_object* v_x_1646_){
_start:
{
lean_object* v_res_1647_; 
v_res_1647_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1645_, v_x_1646_);
lean_dec(v_x_1646_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1651_){
_start:
{
if (lean_obj_tag(v_x_1651_) == 0)
{
lean_object* v___x_1652_; 
v___x_1652_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1652_;
}
else
{
lean_object* v_tail_1653_; 
v_tail_1653_ = lean_ctor_get(v_x_1651_, 1);
if (lean_obj_tag(v_tail_1653_) == 0)
{
lean_object* v_head_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v_head_1654_ = lean_ctor_get(v_x_1651_, 0);
v___x_1655_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1656_ = lean_string_append(v___x_1655_, v_head_1654_);
v___x_1657_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1658_ = lean_string_append(v___x_1656_, v___x_1657_);
return v___x_1658_;
}
else
{
lean_object* v_head_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint32_t v___x_1663_; lean_object* v___x_1664_; 
v_head_1659_ = lean_ctor_get(v_x_1651_, 0);
v___x_1660_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1661_ = lean_string_append(v___x_1660_, v_head_1659_);
v___x_1662_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1661_, v_tail_1653_);
v___x_1663_ = 93;
v___x_1664_ = lean_string_push(v___x_1662_, v___x_1663_);
return v___x_1664_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1665_);
lean_dec(v_x_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1670_){
_start:
{
switch(lean_obj_tag(v_x_1670_))
{
case 0:
{
lean_object* v___x_1671_; 
v___x_1671_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1671_;
}
case 1:
{
lean_object* v___x_1672_; 
v___x_1672_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1672_;
}
case 2:
{
lean_object* v_a_1673_; lean_object* v___x_1674_; 
v_a_1673_ = lean_ctor_get(v_x_1670_, 0);
v___x_1674_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1673_);
return v___x_1674_;
}
default: 
{
lean_object* v_a_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v_a_1675_ = lean_ctor_get(v_x_1670_, 0);
v___x_1676_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1677_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1675_);
v___x_1678_ = lean_string_append(v___x_1676_, v___x_1677_);
lean_dec_ref(v___x_1677_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_Parser_FirstTokens_toStr(v_x_1679_);
lean_dec(v_x_1679_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v___y_1683_){
_start:
{
lean_inc(v___y_1683_);
return v___y_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v___y_1684_){
_start:
{
lean_object* v_res_1685_; 
v_res_1685_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_1684_);
lean_dec(v___y_1684_);
return v_res_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v___y_1686_){
_start:
{
lean_inc_ref(v___y_1686_);
return v___y_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_1687_);
lean_dec_ref(v___y_1687_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1702_, lean_object* v_p_1703_){
_start:
{
lean_object* v_info_1704_; lean_object* v_fn_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1713_; 
v_info_1704_ = lean_ctor_get(v_p_1703_, 0);
v_fn_1705_ = lean_ctor_get(v_p_1703_, 1);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_p_1703_);
if (v_isSharedCheck_1713_ == 0)
{
v___x_1707_ = v_p_1703_;
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_fn_1705_);
lean_inc(v_info_1704_);
lean_dec(v_p_1703_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1713_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1709_; lean_object* v___x_1711_; 
v___x_1709_ = lean_apply_1(v_f_1702_, v_fn_1705_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 1, v___x_1709_);
v___x_1711_ = v___x_1707_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v_info_1704_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
return v___x_1711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1714_, lean_object* v_p_1715_, lean_object* v_c_1716_, lean_object* v_s_1717_){
_start:
{
lean_object* v_toInputContext_1718_; lean_object* v_toParserModuleContext_1719_; lean_object* v_toCacheableParserContext_1720_; lean_object* v_tokens_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1730_; 
v_toInputContext_1718_ = lean_ctor_get(v_c_1716_, 0);
v_toParserModuleContext_1719_ = lean_ctor_get(v_c_1716_, 1);
v_toCacheableParserContext_1720_ = lean_ctor_get(v_c_1716_, 2);
v_tokens_1721_ = lean_ctor_get(v_c_1716_, 3);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_c_1716_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1723_ = v_c_1716_;
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_tokens_1721_);
lean_inc(v_toCacheableParserContext_1720_);
lean_inc(v_toParserModuleContext_1719_);
lean_inc(v_toInputContext_1718_);
lean_dec(v_c_1716_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1730_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1725_; lean_object* v___x_1727_; 
v___x_1725_ = lean_apply_1(v_f_1714_, v_toCacheableParserContext_1720_);
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 2, v___x_1725_);
v___x_1727_ = v___x_1723_;
goto v_reusejp_1726_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_toInputContext_1718_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_toParserModuleContext_1719_);
lean_ctor_set(v_reuseFailAlloc_1729_, 2, v___x_1725_);
lean_ctor_set(v_reuseFailAlloc_1729_, 3, v_tokens_1721_);
v___x_1727_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1726_;
}
v_reusejp_1726_:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_apply_2(v_p_1715_, v___x_1727_, v_s_1717_);
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1731_, lean_object* v_p_1732_){
_start:
{
lean_object* v_info_1733_; lean_object* v_fn_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1742_; 
v_info_1733_ = lean_ctor_get(v_p_1732_, 0);
v_fn_1734_ = lean_ctor_get(v_p_1732_, 1);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_p_1732_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1736_ = v_p_1732_;
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_fn_1734_);
lean_inc(v_info_1733_);
lean_dec(v_p_1732_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1742_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1738_, 0, v_f_1731_);
lean_closure_set(v___x_1738_, 1, v_fn_1734_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 1, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_info_1733_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1738_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1743_, lean_object* v_p_1744_, lean_object* v_c_1745_, lean_object* v_s_1746_){
_start:
{
lean_object* v_stxStack_1747_; lean_object* v_lhsPrec_1748_; lean_object* v_pos_1749_; lean_object* v_cache_1750_; lean_object* v_errorMsg_1751_; lean_object* v_recoveredErrors_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1791_; 
v_stxStack_1747_ = lean_ctor_get(v_s_1746_, 0);
v_lhsPrec_1748_ = lean_ctor_get(v_s_1746_, 1);
v_pos_1749_ = lean_ctor_get(v_s_1746_, 2);
v_cache_1750_ = lean_ctor_get(v_s_1746_, 3);
v_errorMsg_1751_ = lean_ctor_get(v_s_1746_, 4);
v_recoveredErrors_1752_ = lean_ctor_get(v_s_1746_, 5);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_s_1746_);
if (v_isSharedCheck_1791_ == 0)
{
v___x_1754_ = v_s_1746_;
v_isShared_1755_ = v_isSharedCheck_1791_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_recoveredErrors_1752_);
lean_inc(v_errorMsg_1751_);
lean_inc(v_cache_1750_);
lean_inc(v_pos_1749_);
lean_inc(v_lhsPrec_1748_);
lean_inc(v_stxStack_1747_);
lean_dec(v_s_1746_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1791_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v_raw_1756_; lean_object* v_drop_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1790_; 
v_raw_1756_ = lean_ctor_get(v_stxStack_1747_, 0);
v_drop_1757_ = lean_ctor_get(v_stxStack_1747_, 1);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_stxStack_1747_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1759_ = v_stxStack_1747_;
v_isShared_1760_ = v_isSharedCheck_1790_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_drop_1757_);
lean_inc(v_raw_1756_);
lean_dec(v_stxStack_1747_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1790_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 1, v_drop_1743_);
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_raw_1756_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_drop_1743_);
v___x_1762_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
lean_object* v___x_1764_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1762_);
v___x_1764_ = v___x_1754_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v___x_1762_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_lhsPrec_1748_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_pos_1749_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v_cache_1750_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v_errorMsg_1751_);
lean_ctor_set(v_reuseFailAlloc_1788_, 5, v_recoveredErrors_1752_);
v___x_1764_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v_s_1765_; lean_object* v_stxStack_1766_; lean_object* v_lhsPrec_1767_; lean_object* v_pos_1768_; lean_object* v_cache_1769_; lean_object* v_errorMsg_1770_; lean_object* v_recoveredErrors_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1787_; 
v_s_1765_ = lean_apply_2(v_p_1744_, v_c_1745_, v___x_1764_);
v_stxStack_1766_ = lean_ctor_get(v_s_1765_, 0);
v_lhsPrec_1767_ = lean_ctor_get(v_s_1765_, 1);
v_pos_1768_ = lean_ctor_get(v_s_1765_, 2);
v_cache_1769_ = lean_ctor_get(v_s_1765_, 3);
v_errorMsg_1770_ = lean_ctor_get(v_s_1765_, 4);
v_recoveredErrors_1771_ = lean_ctor_get(v_s_1765_, 5);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_s_1765_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1773_ = v_s_1765_;
v_isShared_1774_ = v_isSharedCheck_1787_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_recoveredErrors_1771_);
lean_inc(v_errorMsg_1770_);
lean_inc(v_cache_1769_);
lean_inc(v_pos_1768_);
lean_inc(v_lhsPrec_1767_);
lean_inc(v_stxStack_1766_);
lean_dec(v_s_1765_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1787_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v_raw_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1785_; 
v_raw_1775_ = lean_ctor_get(v_stxStack_1766_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_stxStack_1766_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; 
v_unused_1786_ = lean_ctor_get(v_stxStack_1766_, 1);
lean_dec(v_unused_1786_);
v___x_1777_ = v_stxStack_1766_;
v_isShared_1778_ = v_isSharedCheck_1785_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_raw_1775_);
lean_dec(v_stxStack_1766_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1785_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v_drop_1757_);
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_raw_1775_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_drop_1757_);
v___x_1780_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1782_; 
if (v_isShared_1774_ == 0)
{
lean_ctor_set(v___x_1773_, 0, v___x_1780_);
v___x_1782_ = v___x_1773_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1780_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_lhsPrec_1767_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_pos_1768_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v_cache_1769_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_errorMsg_1770_);
lean_ctor_set(v_reuseFailAlloc_1783_, 5, v_recoveredErrors_1771_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1792_, lean_object* v_c_1793_, lean_object* v_s_1794_){
_start:
{
lean_object* v_cache_1795_; lean_object* v_stxStack_1796_; lean_object* v_lhsPrec_1797_; lean_object* v_pos_1798_; lean_object* v_errorMsg_1799_; lean_object* v_recoveredErrors_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1840_; 
v_cache_1795_ = lean_ctor_get(v_s_1794_, 3);
v_stxStack_1796_ = lean_ctor_get(v_s_1794_, 0);
v_lhsPrec_1797_ = lean_ctor_get(v_s_1794_, 1);
v_pos_1798_ = lean_ctor_get(v_s_1794_, 2);
v_errorMsg_1799_ = lean_ctor_get(v_s_1794_, 4);
v_recoveredErrors_1800_ = lean_ctor_get(v_s_1794_, 5);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_s_1794_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1802_ = v_s_1794_;
v_isShared_1803_ = v_isSharedCheck_1840_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_recoveredErrors_1800_);
lean_inc(v_errorMsg_1799_);
lean_inc(v_cache_1795_);
lean_inc(v_pos_1798_);
lean_inc(v_lhsPrec_1797_);
lean_inc(v_stxStack_1796_);
lean_dec(v_s_1794_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1840_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_tokenCache_1804_; lean_object* v_parserCache_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1839_; 
v_tokenCache_1804_ = lean_ctor_get(v_cache_1795_, 0);
v_parserCache_1805_ = lean_ctor_get(v_cache_1795_, 1);
v_isSharedCheck_1839_ = !lean_is_exclusive(v_cache_1795_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1807_ = v_cache_1795_;
v_isShared_1808_ = v_isSharedCheck_1839_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_parserCache_1805_);
lean_inc(v_tokenCache_1804_);
lean_dec(v_cache_1795_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1839_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v___x_1809_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_tokenCache_1804_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 3, v___x_1811_);
v___x_1813_ = v___x_1802_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_stxStack_1796_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_lhsPrec_1797_);
lean_ctor_set(v_reuseFailAlloc_1837_, 2, v_pos_1798_);
lean_ctor_set(v_reuseFailAlloc_1837_, 3, v___x_1811_);
lean_ctor_set(v_reuseFailAlloc_1837_, 4, v_errorMsg_1799_);
lean_ctor_set(v_reuseFailAlloc_1837_, 5, v_recoveredErrors_1800_);
v___x_1813_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v_s_x27_1814_; lean_object* v_cache_1815_; lean_object* v_stxStack_1816_; lean_object* v_lhsPrec_1817_; lean_object* v_pos_1818_; lean_object* v_errorMsg_1819_; lean_object* v_recoveredErrors_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1836_; 
v_s_x27_1814_ = lean_apply_2(v_p_1792_, v_c_1793_, v___x_1813_);
v_cache_1815_ = lean_ctor_get(v_s_x27_1814_, 3);
v_stxStack_1816_ = lean_ctor_get(v_s_x27_1814_, 0);
v_lhsPrec_1817_ = lean_ctor_get(v_s_x27_1814_, 1);
v_pos_1818_ = lean_ctor_get(v_s_x27_1814_, 2);
v_errorMsg_1819_ = lean_ctor_get(v_s_x27_1814_, 4);
v_recoveredErrors_1820_ = lean_ctor_get(v_s_x27_1814_, 5);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_s_x27_1814_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1822_ = v_s_x27_1814_;
v_isShared_1823_ = v_isSharedCheck_1836_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_recoveredErrors_1820_);
lean_inc(v_errorMsg_1819_);
lean_inc(v_cache_1815_);
lean_inc(v_pos_1818_);
lean_inc(v_lhsPrec_1817_);
lean_inc(v_stxStack_1816_);
lean_dec(v_s_x27_1814_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1836_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v_tokenCache_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1834_; 
v_tokenCache_1824_ = lean_ctor_get(v_cache_1815_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_cache_1815_);
if (v_isSharedCheck_1834_ == 0)
{
lean_object* v_unused_1835_; 
v_unused_1835_ = lean_ctor_get(v_cache_1815_, 1);
lean_dec(v_unused_1835_);
v___x_1826_ = v_cache_1815_;
v_isShared_1827_ = v_isSharedCheck_1834_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_tokenCache_1824_);
lean_dec(v_cache_1815_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1834_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v_parserCache_1805_);
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_tokenCache_1824_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_parserCache_1805_);
v___x_1829_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1831_; 
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 3, v___x_1829_);
v___x_1831_ = v___x_1822_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_stxStack_1816_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_lhsPrec_1817_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_pos_1818_);
lean_ctor_set(v_reuseFailAlloc_1832_, 3, v___x_1829_);
lean_ctor_set(v_reuseFailAlloc_1832_, 4, v_errorMsg_1819_);
lean_ctor_set(v_reuseFailAlloc_1832_, 5, v_recoveredErrors_1820_);
v___x_1831_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
return v___x_1831_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1841_, lean_object* v_a_1842_, lean_object* v_a_1843_){
_start:
{
lean_object* v___f_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___f_1844_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1844_, 0, v_p_1841_);
v___x_1845_ = lean_unsigned_to_nat(0u);
v___x_1846_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1845_, v___f_1844_, v_a_1842_, v_a_1843_);
return v___x_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1847_){
_start:
{
lean_object* v_info_1848_; lean_object* v_fn_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
v_info_1848_ = lean_ctor_get(v_p_1847_, 0);
v_fn_1849_ = lean_ctor_get(v_p_1847_, 1);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_p_1847_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1851_ = v_p_1847_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_fn_1849_);
lean_inc(v_info_1848_);
lean_dec(v_p_1847_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1853_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1853_, 0, v_fn_1849_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v___x_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_info_1848_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1858_, lean_object* v_p_1859_, lean_object* v_c_1860_, lean_object* v_s_1861_){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; 
v___x_1862_ = lean_apply_1(v_f_1858_, v_c_1860_);
v___x_1863_ = lean_apply_2(v_p_1859_, v___x_1862_, v_s_1861_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1864_, lean_object* v_p_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v___f_1868_; lean_object* v___x_1869_; 
v___f_1868_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1868_, 0, v_f_1864_);
lean_closure_set(v___f_1868_, 1, v_p_1865_);
v___x_1869_ = l_Lean_Parser_withResetCacheFn(v___f_1868_, v_a_1866_, v_a_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1870_, lean_object* v_x_1871_){
_start:
{
if (lean_obj_tag(v_x_1871_) == 0)
{
uint8_t v___x_1872_; 
v___x_1872_ = 0;
return v___x_1872_;
}
else
{
lean_object* v_key_1873_; lean_object* v_tail_1874_; uint8_t v___x_1875_; 
v_key_1873_ = lean_ctor_get(v_x_1871_, 0);
v_tail_1874_ = lean_ctor_get(v_x_1871_, 2);
v___x_1875_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1873_, v_a_1870_);
if (v___x_1875_ == 0)
{
v_x_1871_ = v_tail_1874_;
goto _start;
}
else
{
return v___x_1875_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1877_, lean_object* v_x_1878_){
_start:
{
uint8_t v_res_1879_; lean_object* v_r_1880_; 
v_res_1879_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1877_, v_x_1878_);
lean_dec(v_x_1878_);
lean_dec_ref(v_a_1877_);
v_r_1880_ = lean_box(v_res_1879_);
return v_r_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
if (lean_obj_tag(v_x_1882_) == 0)
{
return v_x_1881_;
}
else
{
lean_object* v_key_1883_; lean_object* v_value_1884_; lean_object* v_tail_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1915_; 
v_key_1883_ = lean_ctor_get(v_x_1882_, 0);
v_value_1884_ = lean_ctor_get(v_x_1882_, 1);
v_tail_1885_ = lean_ctor_get(v_x_1882_, 2);
v_isSharedCheck_1915_ = !lean_is_exclusive(v_x_1882_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1887_ = v_x_1882_;
v_isShared_1888_ = v_isSharedCheck_1915_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_tail_1885_);
lean_inc(v_value_1884_);
lean_inc(v_key_1883_);
lean_dec(v_x_1882_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1915_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_parserName_1889_; lean_object* v_pos_1890_; lean_object* v___x_1891_; uint64_t v___x_1892_; uint64_t v___y_1894_; 
v_parserName_1889_ = lean_ctor_get(v_key_1883_, 1);
v_pos_1890_ = lean_ctor_get(v_key_1883_, 2);
v___x_1891_ = lean_array_get_size(v_x_1881_);
v___x_1892_ = l_String_instHashableRaw_hash(v_pos_1890_);
if (lean_obj_tag(v_parserName_1889_) == 0)
{
uint64_t v___x_1913_; 
v___x_1913_ = 1723ULL;
v___y_1894_ = v___x_1913_;
goto v___jp_1893_;
}
else
{
uint64_t v_hash_1914_; 
v_hash_1914_ = lean_ctor_get_uint64(v_parserName_1889_, sizeof(void*)*2);
v___y_1894_ = v_hash_1914_;
goto v___jp_1893_;
}
v___jp_1893_:
{
uint64_t v___x_1895_; uint64_t v___x_1896_; uint64_t v___x_1897_; uint64_t v_fold_1898_; uint64_t v___x_1899_; uint64_t v___x_1900_; uint64_t v___x_1901_; size_t v___x_1902_; size_t v___x_1903_; size_t v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v___x_1895_ = lean_uint64_mix_hash(v___x_1892_, v___y_1894_);
v___x_1896_ = 32ULL;
v___x_1897_ = lean_uint64_shift_right(v___x_1895_, v___x_1896_);
v_fold_1898_ = lean_uint64_xor(v___x_1895_, v___x_1897_);
v___x_1899_ = 16ULL;
v___x_1900_ = lean_uint64_shift_right(v_fold_1898_, v___x_1899_);
v___x_1901_ = lean_uint64_xor(v_fold_1898_, v___x_1900_);
v___x_1902_ = lean_uint64_to_usize(v___x_1901_);
v___x_1903_ = lean_usize_of_nat(v___x_1891_);
v___x_1904_ = ((size_t)1ULL);
v___x_1905_ = lean_usize_sub(v___x_1903_, v___x_1904_);
v___x_1906_ = lean_usize_land(v___x_1902_, v___x_1905_);
v___x_1907_ = lean_array_uget_borrowed(v_x_1881_, v___x_1906_);
lean_inc(v___x_1907_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 2, v___x_1907_);
v___x_1909_ = v___x_1887_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_key_1883_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_value_1884_);
lean_ctor_set(v_reuseFailAlloc_1912_, 2, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_array_uset(v_x_1881_, v___x_1906_, v___x_1909_);
v_x_1881_ = v___x_1910_;
v_x_1882_ = v_tail_1885_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1916_, lean_object* v_source_1917_, lean_object* v_target_1918_){
_start:
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = lean_array_get_size(v_source_1917_);
v___x_1920_ = lean_nat_dec_lt(v_i_1916_, v___x_1919_);
if (v___x_1920_ == 0)
{
lean_dec_ref(v_source_1917_);
lean_dec(v_i_1916_);
return v_target_1918_;
}
else
{
lean_object* v_es_1921_; lean_object* v___x_1922_; lean_object* v_source_1923_; lean_object* v_target_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v_es_1921_ = lean_array_fget(v_source_1917_, v_i_1916_);
v___x_1922_ = lean_box(0);
v_source_1923_ = lean_array_fset(v_source_1917_, v_i_1916_, v___x_1922_);
v_target_1924_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1918_, v_es_1921_);
v___x_1925_ = lean_unsigned_to_nat(1u);
v___x_1926_ = lean_nat_add(v_i_1916_, v___x_1925_);
lean_dec(v_i_1916_);
v_i_1916_ = v___x_1926_;
v_source_1917_ = v_source_1923_;
v_target_1918_ = v_target_1924_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1928_){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v_nbuckets_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1929_ = lean_array_get_size(v_data_1928_);
v___x_1930_ = lean_unsigned_to_nat(2u);
v_nbuckets_1931_ = lean_nat_mul(v___x_1929_, v___x_1930_);
v___x_1932_ = lean_unsigned_to_nat(0u);
v___x_1933_ = lean_box(0);
v___x_1934_ = lean_mk_array(v_nbuckets_1931_, v___x_1933_);
v___x_1935_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1932_, v_data_1928_, v___x_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1936_, lean_object* v_b_1937_, lean_object* v_x_1938_){
_start:
{
if (lean_obj_tag(v_x_1938_) == 0)
{
lean_dec(v_b_1937_);
lean_dec_ref(v_a_1936_);
return v_x_1938_;
}
else
{
lean_object* v_key_1939_; lean_object* v_value_1940_; lean_object* v_tail_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1953_; 
v_key_1939_ = lean_ctor_get(v_x_1938_, 0);
v_value_1940_ = lean_ctor_get(v_x_1938_, 1);
v_tail_1941_ = lean_ctor_get(v_x_1938_, 2);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_x_1938_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1943_ = v_x_1938_;
v_isShared_1944_ = v_isSharedCheck_1953_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_tail_1941_);
lean_inc(v_value_1940_);
lean_inc(v_key_1939_);
lean_dec(v_x_1938_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1953_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
uint8_t v___x_1945_; 
v___x_1945_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1939_, v_a_1936_);
if (v___x_1945_ == 0)
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1936_, v_b_1937_, v_tail_1941_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 2, v___x_1946_);
v___x_1948_ = v___x_1943_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_key_1939_);
lean_ctor_set(v_reuseFailAlloc_1949_, 1, v_value_1940_);
lean_ctor_set(v_reuseFailAlloc_1949_, 2, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
else
{
lean_object* v___x_1951_; 
lean_dec(v_value_1940_);
lean_dec(v_key_1939_);
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 1, v_b_1937_);
lean_ctor_set(v___x_1943_, 0, v_a_1936_);
v___x_1951_ = v___x_1943_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1936_);
lean_ctor_set(v_reuseFailAlloc_1952_, 1, v_b_1937_);
lean_ctor_set(v_reuseFailAlloc_1952_, 2, v_tail_1941_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1954_, lean_object* v_a_1955_, lean_object* v_b_1956_){
_start:
{
lean_object* v_size_1957_; lean_object* v_buckets_1958_; lean_object* v___x_1960_; uint8_t v_isShared_1961_; uint8_t v_isSharedCheck_2008_; 
v_size_1957_ = lean_ctor_get(v_m_1954_, 0);
v_buckets_1958_ = lean_ctor_get(v_m_1954_, 1);
v_isSharedCheck_2008_ = !lean_is_exclusive(v_m_1954_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_1960_ = v_m_1954_;
v_isShared_1961_ = v_isSharedCheck_2008_;
goto v_resetjp_1959_;
}
else
{
lean_inc(v_buckets_1958_);
lean_inc(v_size_1957_);
lean_dec(v_m_1954_);
v___x_1960_ = lean_box(0);
v_isShared_1961_ = v_isSharedCheck_2008_;
goto v_resetjp_1959_;
}
v_resetjp_1959_:
{
lean_object* v_parserName_1962_; lean_object* v_pos_1963_; lean_object* v___x_1964_; uint64_t v___x_1965_; uint64_t v___y_1967_; 
v_parserName_1962_ = lean_ctor_get(v_a_1955_, 1);
v_pos_1963_ = lean_ctor_get(v_a_1955_, 2);
v___x_1964_ = lean_array_get_size(v_buckets_1958_);
v___x_1965_ = l_String_instHashableRaw_hash(v_pos_1963_);
if (lean_obj_tag(v_parserName_1962_) == 0)
{
uint64_t v___x_2006_; 
v___x_2006_ = 1723ULL;
v___y_1967_ = v___x_2006_;
goto v___jp_1966_;
}
else
{
uint64_t v_hash_2007_; 
v_hash_2007_ = lean_ctor_get_uint64(v_parserName_1962_, sizeof(void*)*2);
v___y_1967_ = v_hash_2007_;
goto v___jp_1966_;
}
v___jp_1966_:
{
uint64_t v___x_1968_; uint64_t v___x_1969_; uint64_t v___x_1970_; uint64_t v_fold_1971_; uint64_t v___x_1972_; uint64_t v___x_1973_; uint64_t v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; size_t v___x_1977_; size_t v___x_1978_; size_t v___x_1979_; lean_object* v_bkt_1980_; uint8_t v___x_1981_; 
v___x_1968_ = lean_uint64_mix_hash(v___x_1965_, v___y_1967_);
v___x_1969_ = 32ULL;
v___x_1970_ = lean_uint64_shift_right(v___x_1968_, v___x_1969_);
v_fold_1971_ = lean_uint64_xor(v___x_1968_, v___x_1970_);
v___x_1972_ = 16ULL;
v___x_1973_ = lean_uint64_shift_right(v_fold_1971_, v___x_1972_);
v___x_1974_ = lean_uint64_xor(v_fold_1971_, v___x_1973_);
v___x_1975_ = lean_uint64_to_usize(v___x_1974_);
v___x_1976_ = lean_usize_of_nat(v___x_1964_);
v___x_1977_ = ((size_t)1ULL);
v___x_1978_ = lean_usize_sub(v___x_1976_, v___x_1977_);
v___x_1979_ = lean_usize_land(v___x_1975_, v___x_1978_);
v_bkt_1980_ = lean_array_uget_borrowed(v_buckets_1958_, v___x_1979_);
v___x_1981_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1955_, v_bkt_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v_size_x27_1983_; lean_object* v___x_1984_; lean_object* v_buckets_x27_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; uint8_t v___x_1991_; 
v___x_1982_ = lean_unsigned_to_nat(1u);
v_size_x27_1983_ = lean_nat_add(v_size_1957_, v___x_1982_);
lean_dec(v_size_1957_);
lean_inc(v_bkt_1980_);
v___x_1984_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1984_, 0, v_a_1955_);
lean_ctor_set(v___x_1984_, 1, v_b_1956_);
lean_ctor_set(v___x_1984_, 2, v_bkt_1980_);
v_buckets_x27_1985_ = lean_array_uset(v_buckets_1958_, v___x_1979_, v___x_1984_);
v___x_1986_ = lean_unsigned_to_nat(4u);
v___x_1987_ = lean_nat_mul(v_size_x27_1983_, v___x_1986_);
v___x_1988_ = lean_unsigned_to_nat(3u);
v___x_1989_ = lean_nat_div(v___x_1987_, v___x_1988_);
lean_dec(v___x_1987_);
v___x_1990_ = lean_array_get_size(v_buckets_x27_1985_);
v___x_1991_ = lean_nat_dec_le(v___x_1989_, v___x_1990_);
lean_dec(v___x_1989_);
if (v___x_1991_ == 0)
{
lean_object* v_val_1992_; lean_object* v___x_1994_; 
v_val_1992_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_1985_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v_val_1992_);
lean_ctor_set(v___x_1960_, 0, v_size_x27_1983_);
v___x_1994_ = v___x_1960_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_size_x27_1983_);
lean_ctor_set(v_reuseFailAlloc_1995_, 1, v_val_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
else
{
lean_object* v___x_1997_; 
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v_buckets_x27_1985_);
lean_ctor_set(v___x_1960_, 0, v_size_x27_1983_);
v___x_1997_ = v___x_1960_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_1998_; 
v_reuseFailAlloc_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_size_x27_1983_);
lean_ctor_set(v_reuseFailAlloc_1998_, 1, v_buckets_x27_1985_);
v___x_1997_ = v_reuseFailAlloc_1998_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
return v___x_1997_;
}
}
}
else
{
lean_object* v___x_1999_; lean_object* v_buckets_x27_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2004_; 
lean_inc(v_bkt_1980_);
v___x_1999_ = lean_box(0);
v_buckets_x27_2000_ = lean_array_uset(v_buckets_1958_, v___x_1979_, v___x_1999_);
v___x_2001_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1955_, v_b_1956_, v_bkt_1980_);
v___x_2002_ = lean_array_uset(v_buckets_x27_2000_, v___x_1979_, v___x_2001_);
if (v_isShared_1961_ == 0)
{
lean_ctor_set(v___x_1960_, 1, v___x_2002_);
v___x_2004_ = v___x_1960_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_size_1957_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_2009_, lean_object* v_x_2010_){
_start:
{
if (lean_obj_tag(v_x_2010_) == 0)
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_box(0);
return v___x_2011_;
}
else
{
lean_object* v_key_2012_; lean_object* v_value_2013_; lean_object* v_tail_2014_; uint8_t v___x_2015_; 
v_key_2012_ = lean_ctor_get(v_x_2010_, 0);
v_value_2013_ = lean_ctor_get(v_x_2010_, 1);
v_tail_2014_ = lean_ctor_get(v_x_2010_, 2);
v___x_2015_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_2012_, v_a_2009_);
if (v___x_2015_ == 0)
{
v_x_2010_ = v_tail_2014_;
goto _start;
}
else
{
lean_object* v___x_2017_; 
lean_inc(v_value_2013_);
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v_value_2013_);
return v___x_2017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_2018_, lean_object* v_x_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2018_, v_x_2019_);
lean_dec(v_x_2019_);
lean_dec_ref(v_a_2018_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_buckets_2023_; lean_object* v_parserName_2024_; lean_object* v_pos_2025_; lean_object* v___x_2026_; uint64_t v___x_2027_; uint64_t v___y_2029_; 
v_buckets_2023_ = lean_ctor_get(v_m_2021_, 1);
v_parserName_2024_ = lean_ctor_get(v_a_2022_, 1);
v_pos_2025_ = lean_ctor_get(v_a_2022_, 2);
v___x_2026_ = lean_array_get_size(v_buckets_2023_);
v___x_2027_ = l_String_instHashableRaw_hash(v_pos_2025_);
if (lean_obj_tag(v_parserName_2024_) == 0)
{
uint64_t v___x_2044_; 
v___x_2044_ = 1723ULL;
v___y_2029_ = v___x_2044_;
goto v___jp_2028_;
}
else
{
uint64_t v_hash_2045_; 
v_hash_2045_ = lean_ctor_get_uint64(v_parserName_2024_, sizeof(void*)*2);
v___y_2029_ = v_hash_2045_;
goto v___jp_2028_;
}
v___jp_2028_:
{
uint64_t v___x_2030_; uint64_t v___x_2031_; uint64_t v___x_2032_; uint64_t v_fold_2033_; uint64_t v___x_2034_; uint64_t v___x_2035_; uint64_t v___x_2036_; size_t v___x_2037_; size_t v___x_2038_; size_t v___x_2039_; size_t v___x_2040_; size_t v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2030_ = lean_uint64_mix_hash(v___x_2027_, v___y_2029_);
v___x_2031_ = 32ULL;
v___x_2032_ = lean_uint64_shift_right(v___x_2030_, v___x_2031_);
v_fold_2033_ = lean_uint64_xor(v___x_2030_, v___x_2032_);
v___x_2034_ = 16ULL;
v___x_2035_ = lean_uint64_shift_right(v_fold_2033_, v___x_2034_);
v___x_2036_ = lean_uint64_xor(v_fold_2033_, v___x_2035_);
v___x_2037_ = lean_uint64_to_usize(v___x_2036_);
v___x_2038_ = lean_usize_of_nat(v___x_2026_);
v___x_2039_ = ((size_t)1ULL);
v___x_2040_ = lean_usize_sub(v___x_2038_, v___x_2039_);
v___x_2041_ = lean_usize_land(v___x_2037_, v___x_2040_);
v___x_2042_ = lean_array_uget_borrowed(v_buckets_2023_, v___x_2041_);
v___x_2043_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2022_, v___x_2042_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2046_, v_a_2047_);
lean_dec_ref(v_a_2047_);
lean_dec_ref(v_m_2046_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_2049_, lean_object* v_p_2050_, lean_object* v_c_2051_, lean_object* v_s_2052_){
_start:
{
lean_object* v_cache_2053_; lean_object* v_toCacheableParserContext_2054_; lean_object* v_stxStack_2055_; lean_object* v_pos_2056_; lean_object* v_recoveredErrors_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2106_; 
v_cache_2053_ = lean_ctor_get(v_s_2052_, 3);
lean_inc_ref(v_cache_2053_);
v_toCacheableParserContext_2054_ = lean_ctor_get(v_c_2051_, 2);
v_stxStack_2055_ = lean_ctor_get(v_s_2052_, 0);
v_pos_2056_ = lean_ctor_get(v_s_2052_, 2);
v_recoveredErrors_2057_ = lean_ctor_get(v_s_2052_, 5);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_s_2052_);
if (v_isSharedCheck_2106_ == 0)
{
lean_object* v_unused_2107_; lean_object* v_unused_2108_; lean_object* v_unused_2109_; 
v_unused_2107_ = lean_ctor_get(v_s_2052_, 4);
lean_dec(v_unused_2107_);
v_unused_2108_ = lean_ctor_get(v_s_2052_, 3);
lean_dec(v_unused_2108_);
v_unused_2109_ = lean_ctor_get(v_s_2052_, 1);
lean_dec(v_unused_2109_);
v___x_2059_ = v_s_2052_;
v_isShared_2060_ = v_isSharedCheck_2106_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_recoveredErrors_2057_);
lean_inc(v_pos_2056_);
lean_inc(v_stxStack_2055_);
lean_dec(v_s_2052_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2106_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_parserCache_2061_; lean_object* v_key_2062_; lean_object* v___x_2063_; 
v_parserCache_2061_ = lean_ctor_get(v_cache_2053_, 1);
lean_inc(v_pos_2056_);
lean_inc_ref(v_toCacheableParserContext_2054_);
v_key_2062_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_2062_, 0, v_toCacheableParserContext_2054_);
lean_ctor_set(v_key_2062_, 1, v_parserName_2049_);
lean_ctor_set(v_key_2062_, 2, v_pos_2056_);
v___x_2063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_2061_, v_key_2062_);
if (lean_obj_tag(v___x_2063_) == 1)
{
lean_object* v_val_2064_; lean_object* v_stx_2065_; lean_object* v_lhsPrec_2066_; lean_object* v_newPos_2067_; lean_object* v_errorMsg_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
lean_dec_ref_known(v_key_2062_, 3);
lean_dec(v_pos_2056_);
lean_dec_ref(v_c_2051_);
lean_dec_ref(v_p_2050_);
v_val_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_val_2064_);
lean_dec_ref_known(v___x_2063_, 1);
v_stx_2065_ = lean_ctor_get(v_val_2064_, 0);
lean_inc(v_stx_2065_);
v_lhsPrec_2066_ = lean_ctor_get(v_val_2064_, 1);
lean_inc(v_lhsPrec_2066_);
v_newPos_2067_ = lean_ctor_get(v_val_2064_, 2);
lean_inc(v_newPos_2067_);
v_errorMsg_2068_ = lean_ctor_get(v_val_2064_, 3);
lean_inc(v_errorMsg_2068_);
lean_dec(v_val_2064_);
v___x_2069_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_2055_, v_stx_2065_);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v_errorMsg_2068_);
lean_ctor_set(v___x_2059_, 2, v_newPos_2067_);
lean_ctor_set(v___x_2059_, 1, v_lhsPrec_2066_);
lean_ctor_set(v___x_2059_, 0, v___x_2069_);
v___x_2071_ = v___x_2059_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_lhsPrec_2066_);
lean_ctor_set(v_reuseFailAlloc_2072_, 2, v_newPos_2067_);
lean_ctor_set(v_reuseFailAlloc_2072_, 3, v_cache_2053_);
lean_ctor_set(v_reuseFailAlloc_2072_, 4, v_errorMsg_2068_);
lean_ctor_set(v_reuseFailAlloc_2072_, 5, v_recoveredErrors_2057_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
else
{
lean_object* v_raw_2073_; lean_object* v_initStackSz_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_dec(v___x_2063_);
v_raw_2073_ = lean_ctor_get(v_stxStack_2055_, 0);
v_initStackSz_2074_ = lean_array_get_size(v_raw_2073_);
v___x_2075_ = lean_unsigned_to_nat(0u);
v___x_2076_ = lean_box(0);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 4, v___x_2076_);
lean_ctor_set(v___x_2059_, 1, v___x_2075_);
v___x_2078_ = v___x_2059_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_stxStack_2055_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2105_, 2, v_pos_2056_);
lean_ctor_set(v_reuseFailAlloc_2105_, 3, v_cache_2053_);
lean_ctor_set(v_reuseFailAlloc_2105_, 4, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2105_, 5, v_recoveredErrors_2057_);
v___x_2078_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v_s_2079_; lean_object* v_cache_2080_; lean_object* v_stxStack_2081_; lean_object* v_lhsPrec_2082_; lean_object* v_pos_2083_; lean_object* v_errorMsg_2084_; lean_object* v_recoveredErrors_2085_; lean_object* v___x_2087_; uint8_t v_isShared_2088_; uint8_t v_isSharedCheck_2104_; 
v_s_2079_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_2074_, v_p_2050_, v_c_2051_, v___x_2078_);
v_cache_2080_ = lean_ctor_get(v_s_2079_, 3);
v_stxStack_2081_ = lean_ctor_get(v_s_2079_, 0);
v_lhsPrec_2082_ = lean_ctor_get(v_s_2079_, 1);
v_pos_2083_ = lean_ctor_get(v_s_2079_, 2);
v_errorMsg_2084_ = lean_ctor_get(v_s_2079_, 4);
v_recoveredErrors_2085_ = lean_ctor_get(v_s_2079_, 5);
v_isSharedCheck_2104_ = !lean_is_exclusive(v_s_2079_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2087_ = v_s_2079_;
v_isShared_2088_ = v_isSharedCheck_2104_;
goto v_resetjp_2086_;
}
else
{
lean_inc(v_recoveredErrors_2085_);
lean_inc(v_errorMsg_2084_);
lean_inc(v_cache_2080_);
lean_inc(v_pos_2083_);
lean_inc(v_lhsPrec_2082_);
lean_inc(v_stxStack_2081_);
lean_dec(v_s_2079_);
v___x_2087_ = lean_box(0);
v_isShared_2088_ = v_isSharedCheck_2104_;
goto v_resetjp_2086_;
}
v_resetjp_2086_:
{
lean_object* v_tokenCache_2089_; lean_object* v_parserCache_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2103_; 
v_tokenCache_2089_ = lean_ctor_get(v_cache_2080_, 0);
v_parserCache_2090_ = lean_ctor_get(v_cache_2080_, 1);
v_isSharedCheck_2103_ = !lean_is_exclusive(v_cache_2080_);
if (v_isSharedCheck_2103_ == 0)
{
v___x_2092_ = v_cache_2080_;
v_isShared_2093_ = v_isSharedCheck_2103_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_parserCache_2090_);
lean_inc(v_tokenCache_2089_);
lean_dec(v_cache_2080_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2103_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2098_; 
v___x_2094_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2081_);
lean_inc(v_errorMsg_2084_);
lean_inc(v_pos_2083_);
lean_inc(v_lhsPrec_2082_);
v___x_2095_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
lean_ctor_set(v___x_2095_, 1, v_lhsPrec_2082_);
lean_ctor_set(v___x_2095_, 2, v_pos_2083_);
lean_ctor_set(v___x_2095_, 3, v_errorMsg_2084_);
v___x_2096_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_2090_, v_key_2062_, v___x_2095_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v___x_2096_);
v___x_2098_ = v___x_2092_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2102_; 
v_reuseFailAlloc_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_tokenCache_2089_);
lean_ctor_set(v_reuseFailAlloc_2102_, 1, v___x_2096_);
v___x_2098_ = v_reuseFailAlloc_2102_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
lean_object* v___x_2100_; 
if (v_isShared_2088_ == 0)
{
lean_ctor_set(v___x_2087_, 3, v___x_2098_);
v___x_2100_ = v___x_2087_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_stxStack_2081_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_lhsPrec_2082_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v_pos_2083_);
lean_ctor_set(v_reuseFailAlloc_2101_, 3, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2101_, 4, v_errorMsg_2084_);
lean_ctor_set(v_reuseFailAlloc_2101_, 5, v_recoveredErrors_2085_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2110_, lean_object* v_m_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2111_, v_a_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2114_, lean_object* v_m_2115_, lean_object* v_a_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2114_, v_m_2115_, v_a_2116_);
lean_dec_ref(v_a_2116_);
lean_dec_ref(v_m_2115_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2118_, lean_object* v_m_2119_, lean_object* v_a_2120_, lean_object* v_b_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2119_, v_a_2120_, v_b_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2123_, lean_object* v_a_2124_, lean_object* v_x_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2124_, v_x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2127_, lean_object* v_a_2128_, lean_object* v_x_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2127_, v_a_2128_, v_x_2129_);
lean_dec(v_x_2129_);
lean_dec_ref(v_a_2128_);
return v_res_2130_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2131_, lean_object* v_a_2132_, lean_object* v_x_2133_){
_start:
{
uint8_t v___x_2134_; 
v___x_2134_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2132_, v_x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2135_, lean_object* v_a_2136_, lean_object* v_x_2137_){
_start:
{
uint8_t v_res_2138_; lean_object* v_r_2139_; 
v_res_2138_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2135_, v_a_2136_, v_x_2137_);
lean_dec(v_x_2137_);
lean_dec_ref(v_a_2136_);
v_r_2139_ = lean_box(v_res_2138_);
return v_r_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2140_, lean_object* v_data_2141_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2143_, lean_object* v_a_2144_, lean_object* v_b_2145_, lean_object* v_x_2146_){
_start:
{
lean_object* v___x_2147_; 
v___x_2147_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2144_, v_b_2145_, v_x_2146_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2148_, lean_object* v_i_2149_, lean_object* v_source_2150_, lean_object* v_target_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2149_, v_source_2150_, v_target_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2154_, v_x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2157_, lean_object* v_p_2158_){
_start:
{
lean_object* v_info_2159_; lean_object* v_fn_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2168_; 
v_info_2159_ = lean_ctor_get(v_p_2158_, 0);
v_fn_2160_ = lean_ctor_get(v_p_2158_, 1);
v_isSharedCheck_2168_ = !lean_is_exclusive(v_p_2158_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2162_ = v_p_2158_;
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_fn_2160_);
lean_inc(v_info_2159_);
lean_dec(v_p_2158_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2168_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2164_, 0, v_parserName_2157_);
lean_closure_set(v___x_2164_, 1, v_fn_2160_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 1, v___x_2164_);
v___x_2166_ = v___x_2162_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_info_2159_);
lean_ctor_set(v_reuseFailAlloc_2167_, 1, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2177_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2178_ = l_Lean_addBuiltinDocString(v___x_2176_, v___x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2188_, lean_object* v_ictx_2189_, lean_object* v_pmctx_2190_, lean_object* v_tokens_2191_, lean_object* v_s_2192_){
_start:
{
lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2193_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__1));
v___x_2194_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2194_, 0, v_ictx_2189_);
lean_ctor_set(v___x_2194_, 1, v_pmctx_2190_);
lean_ctor_set(v___x_2194_, 2, v___x_2193_);
lean_ctor_set(v___x_2194_, 3, v_tokens_2191_);
v___x_2195_ = lean_apply_2(v_p_2188_, v___x_2194_, v_s_2192_);
return v___x_2195_;
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
