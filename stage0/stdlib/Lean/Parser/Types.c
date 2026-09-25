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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0 = (const lean_object*)&l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext_unsafe__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0;
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instBEqCacheableParserContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0_value)} };
static const lean_object* l_Lean_Parser_instBEqCacheableParserContext___closed__0 = (const lean_object*)&l_Lean_Parser_instBEqCacheableParserContext___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Parser_instBEqCacheableParserContext = (const lean_object*)&l_Lean_Parser_instBEqCacheableParserContext___closed__0_value;
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
static const lean_string_object l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 541, .m_capacity = 541, .m_length = 540, .m_data = "Run `p` and record result in parser cache for any further invocation with this `parserName`, parser context, and parser state.\n`p` cannot access syntax stack elements pushed before the invocation in order to make caching independent of parser history.\nAs this excludes trailing parsers from being cached, we also reset `lhsPrec`, which is not read but set by leading parsers, to 0\nin order to increase cache hits. Finally, `errorMsg` is also reset to `none` as a leading parser should not be called in the first\nplace if there was an error."};
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
v___x_56_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_358__boxed_163_; size_t v_x_359__boxed_164_; lean_object* v_res_165_; 
v_x_358__boxed_163_ = lean_unbox_usize(v_x_159_);
lean_dec(v_x_159_);
v_x_359__boxed_164_ = lean_unbox_usize(v_x_160_);
lean_dec(v_x_160_);
v_res_165_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_158_, v_x_358__boxed_163_, v_x_359__boxed_164_, v_x_161_, v_x_162_);
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
size_t v_x_542__boxed_198_; size_t v_x_543__boxed_199_; lean_object* v_res_200_; 
v_x_542__boxed_198_ = lean_unbox_usize(v_x_194_);
lean_dec(v_x_194_);
v_x_543__boxed_199_ = lean_unbox_usize(v_x_195_);
lean_dec(v_x_195_);
v_res_200_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(v_00_u03b2_192_, v_x_193_, v_x_542__boxed_198_, v_x_543__boxed_199_, v_x_196_, v_x_197_);
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
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext_unsafe__2(lean_object* v_a_449_, lean_object* v_b_450_){
_start:
{
lean_object* v_forbiddenTks_451_; lean_object* v_forbiddenTks_452_; size_t v___x_453_; size_t v___x_454_; uint8_t v___x_455_; 
v_forbiddenTks_451_ = lean_ctor_get(v_a_449_, 3);
v_forbiddenTks_452_ = lean_ctor_get(v_b_450_, 3);
v___x_453_ = lean_ptr_addr(v_forbiddenTks_451_);
v___x_454_ = lean_ptr_addr(v_forbiddenTks_452_);
v___x_455_ = lean_usize_dec_eq(v___x_453_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_456_ = lean_array_get_size(v_forbiddenTks_451_);
v___x_457_ = lean_array_get_size(v_forbiddenTks_452_);
v___x_458_ = lean_nat_dec_eq(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
return v___x_458_;
}
else
{
lean_object* v___f_459_; uint8_t v___x_460_; 
v___f_459_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0));
v___x_460_ = l_Array_isEqvAux___redArg(v_forbiddenTks_451_, v_forbiddenTks_452_, v___f_459_, v___x_456_);
return v___x_460_;
}
}
else
{
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___boxed(lean_object* v_a_461_, lean_object* v_b_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l_Lean_Parser_instBEqCacheableParserContext_unsafe__2(v_a_461_, v_b_462_);
lean_dec_ref(v_b_462_);
lean_dec_ref(v_a_461_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
static lean_object* _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0(void){
_start:
{
lean_object* v___x_465_; lean_object* v___f_466_; 
v___x_465_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_466_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_466_, 0, v___x_465_);
return v___f_466_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext___lam__0(lean_object* v___f_467_, lean_object* v_a_468_, lean_object* v_b_469_){
_start:
{
lean_object* v_prec_470_; lean_object* v_quotDepth_471_; uint8_t v_suppressInsideQuot_472_; lean_object* v_savedPos_x3f_473_; lean_object* v_forbiddenTks_474_; lean_object* v_prec_475_; lean_object* v_quotDepth_476_; uint8_t v_suppressInsideQuot_477_; lean_object* v_savedPos_x3f_478_; lean_object* v_forbiddenTks_479_; uint8_t v___x_490_; 
v_prec_470_ = lean_ctor_get(v_a_468_, 0);
lean_inc(v_prec_470_);
v_quotDepth_471_ = lean_ctor_get(v_a_468_, 1);
lean_inc(v_quotDepth_471_);
v_suppressInsideQuot_472_ = lean_ctor_get_uint8(v_a_468_, sizeof(void*)*4);
v_savedPos_x3f_473_ = lean_ctor_get(v_a_468_, 2);
lean_inc(v_savedPos_x3f_473_);
v_forbiddenTks_474_ = lean_ctor_get(v_a_468_, 3);
lean_inc_ref(v_forbiddenTks_474_);
lean_dec_ref(v_a_468_);
v_prec_475_ = lean_ctor_get(v_b_469_, 0);
lean_inc(v_prec_475_);
v_quotDepth_476_ = lean_ctor_get(v_b_469_, 1);
lean_inc(v_quotDepth_476_);
v_suppressInsideQuot_477_ = lean_ctor_get_uint8(v_b_469_, sizeof(void*)*4);
v_savedPos_x3f_478_ = lean_ctor_get(v_b_469_, 2);
lean_inc(v_savedPos_x3f_478_);
v_forbiddenTks_479_ = lean_ctor_get(v_b_469_, 3);
lean_inc_ref(v_forbiddenTks_479_);
lean_dec_ref(v_b_469_);
v___x_490_ = lean_nat_dec_eq(v_prec_470_, v_prec_475_);
lean_dec(v_prec_475_);
lean_dec(v_prec_470_);
if (v___x_490_ == 0)
{
lean_dec_ref(v_forbiddenTks_479_);
lean_dec(v_savedPos_x3f_478_);
lean_dec(v_quotDepth_476_);
lean_dec_ref(v_forbiddenTks_474_);
lean_dec(v_savedPos_x3f_473_);
lean_dec(v_quotDepth_471_);
lean_dec_ref(v___f_467_);
return v___x_490_;
}
else
{
uint8_t v___x_491_; 
v___x_491_ = lean_nat_dec_eq(v_quotDepth_471_, v_quotDepth_476_);
lean_dec(v_quotDepth_476_);
lean_dec(v_quotDepth_471_);
if (v___x_491_ == 0)
{
lean_dec_ref(v_forbiddenTks_479_);
lean_dec(v_savedPos_x3f_478_);
lean_dec_ref(v_forbiddenTks_474_);
lean_dec(v_savedPos_x3f_473_);
lean_dec_ref(v___f_467_);
return v___x_491_;
}
else
{
if (v_suppressInsideQuot_477_ == 0)
{
if (v_suppressInsideQuot_472_ == 0)
{
goto v___jp_480_;
}
else
{
lean_dec_ref(v_forbiddenTks_479_);
lean_dec(v_savedPos_x3f_478_);
lean_dec_ref(v_forbiddenTks_474_);
lean_dec(v_savedPos_x3f_473_);
lean_dec_ref(v___f_467_);
return v_suppressInsideQuot_477_;
}
}
else
{
if (v_suppressInsideQuot_472_ == 0)
{
lean_dec_ref(v_forbiddenTks_479_);
lean_dec(v_savedPos_x3f_478_);
lean_dec_ref(v_forbiddenTks_474_);
lean_dec(v_savedPos_x3f_473_);
lean_dec_ref(v___f_467_);
return v_suppressInsideQuot_472_;
}
else
{
goto v___jp_480_;
}
}
}
}
v___jp_480_:
{
lean_object* v___f_481_; uint8_t v___x_482_; 
v___f_481_ = lean_obj_once(&l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0, &l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0_once, _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0);
v___x_482_ = l_Option_instBEq_beq___redArg(v___f_481_, v_savedPos_x3f_473_, v_savedPos_x3f_478_);
if (v___x_482_ == 0)
{
lean_dec_ref(v_forbiddenTks_479_);
lean_dec_ref(v_forbiddenTks_474_);
lean_dec_ref(v___f_467_);
return v___x_482_;
}
else
{
size_t v___x_483_; size_t v___x_484_; uint8_t v___x_485_; 
v___x_483_ = lean_ptr_addr(v_forbiddenTks_474_);
v___x_484_ = lean_ptr_addr(v_forbiddenTks_479_);
v___x_485_ = lean_usize_dec_eq(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_object* v___x_486_; lean_object* v___x_487_; uint8_t v___x_488_; 
v___x_486_ = lean_array_get_size(v_forbiddenTks_474_);
v___x_487_ = lean_array_get_size(v_forbiddenTks_479_);
v___x_488_ = lean_nat_dec_eq(v___x_486_, v___x_487_);
if (v___x_488_ == 0)
{
lean_dec_ref(v_forbiddenTks_479_);
lean_dec_ref(v_forbiddenTks_474_);
lean_dec_ref(v___f_467_);
return v___x_488_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = l_Array_isEqvAux___redArg(v_forbiddenTks_474_, v_forbiddenTks_479_, v___f_467_, v___x_486_);
lean_dec_ref(v_forbiddenTks_479_);
lean_dec_ref(v_forbiddenTks_474_);
return v___x_489_;
}
}
else
{
lean_dec_ref(v_forbiddenTks_479_);
lean_dec_ref(v_forbiddenTks_474_);
lean_dec_ref(v___f_467_);
return v___x_485_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed(lean_object* v___f_492_, lean_object* v_a_493_, lean_object* v_b_494_){
_start:
{
uint8_t v_res_495_; lean_object* v_r_496_; 
v_res_495_ = l_Lean_Parser_instBEqCacheableParserContext___lam__0(v___f_492_, v_a_493_, v_b_494_);
v_r_496_ = lean_box(v_res_495_);
return v_r_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0(lean_object* v_x_500_){
_start:
{
lean_object* v_toInputContext_501_; 
v_toInputContext_501_ = lean_ctor_get(v_x_500_, 0);
lean_inc_ref(v_toInputContext_501_);
return v_toInputContext_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(lean_object* v_x_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_502_);
lean_dec_ref(v_x_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos___redArg(lean_object* v_c_506_, lean_object* v_endPos_507_){
_start:
{
lean_object* v_toInputContext_508_; lean_object* v_toParserModuleContext_509_; lean_object* v_toCacheableParserContext_510_; lean_object* v_tokens_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_529_; 
v_toInputContext_508_ = lean_ctor_get(v_c_506_, 0);
v_toParserModuleContext_509_ = lean_ctor_get(v_c_506_, 1);
v_toCacheableParserContext_510_ = lean_ctor_get(v_c_506_, 2);
v_tokens_511_ = lean_ctor_get(v_c_506_, 3);
v_isSharedCheck_529_ = !lean_is_exclusive(v_c_506_);
if (v_isSharedCheck_529_ == 0)
{
v___x_513_ = v_c_506_;
v_isShared_514_ = v_isSharedCheck_529_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_tokens_511_);
lean_inc(v_toCacheableParserContext_510_);
lean_inc(v_toParserModuleContext_509_);
lean_inc(v_toInputContext_508_);
lean_dec(v_c_506_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_529_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
lean_object* v_inputString_515_; lean_object* v_fileName_516_; lean_object* v_fileMap_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_527_; 
v_inputString_515_ = lean_ctor_get(v_toInputContext_508_, 0);
v_fileName_516_ = lean_ctor_get(v_toInputContext_508_, 1);
v_fileMap_517_ = lean_ctor_get(v_toInputContext_508_, 2);
v_isSharedCheck_527_ = !lean_is_exclusive(v_toInputContext_508_);
if (v_isSharedCheck_527_ == 0)
{
lean_object* v_unused_528_; 
v_unused_528_ = lean_ctor_get(v_toInputContext_508_, 3);
lean_dec(v_unused_528_);
v___x_519_ = v_toInputContext_508_;
v_isShared_520_ = v_isSharedCheck_527_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_fileMap_517_);
lean_inc(v_fileName_516_);
lean_inc(v_inputString_515_);
lean_dec(v_toInputContext_508_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_527_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v___x_522_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 3, v_endPos_507_);
v___x_522_ = v___x_519_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_inputString_515_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_fileName_516_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_fileMap_517_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v_endPos_507_);
v___x_522_ = v_reuseFailAlloc_526_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
lean_object* v___x_524_; 
if (v_isShared_514_ == 0)
{
lean_ctor_set(v___x_513_, 0, v___x_522_);
v___x_524_ = v___x_513_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
lean_ctor_set(v_reuseFailAlloc_525_, 1, v_toParserModuleContext_509_);
lean_ctor_set(v_reuseFailAlloc_525_, 2, v_toCacheableParserContext_510_);
lean_ctor_set(v_reuseFailAlloc_525_, 3, v_tokens_511_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos(lean_object* v_c_530_, lean_object* v_endPos_531_, lean_object* v_endPos__valid_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_530_, v_endPos_531_);
return v___x_533_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
if (lean_obj_tag(v_x_541_) == 0)
{
uint8_t v___x_542_; 
v___x_542_ = 1;
return v___x_542_;
}
else
{
uint8_t v___x_543_; 
v___x_543_ = 0;
return v___x_543_;
}
}
else
{
if (lean_obj_tag(v_x_541_) == 0)
{
uint8_t v___x_544_; 
v___x_544_ = 0;
return v___x_544_;
}
else
{
lean_object* v_head_545_; lean_object* v_tail_546_; lean_object* v_head_547_; lean_object* v_tail_548_; uint8_t v___x_549_; 
v_head_545_ = lean_ctor_get(v_x_540_, 0);
v_tail_546_ = lean_ctor_get(v_x_540_, 1);
v_head_547_ = lean_ctor_get(v_x_541_, 0);
v_tail_548_ = lean_ctor_get(v_x_541_, 1);
v___x_549_ = lean_string_dec_eq(v_head_545_, v_head_547_);
if (v___x_549_ == 0)
{
return v___x_549_;
}
else
{
v_x_540_ = v_tail_546_;
v_x_541_ = v_tail_548_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(lean_object* v_x_551_, lean_object* v_x_552_){
_start:
{
uint8_t v_res_553_; lean_object* v_r_554_; 
v_res_553_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_551_, v_x_552_);
lean_dec(v_x_552_);
lean_dec(v_x_551_);
v_r_554_ = lean_box(v_res_553_);
return v_r_554_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqError_beq(lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
lean_object* v_unexpectedTk_557_; lean_object* v_unexpected_558_; lean_object* v_expected_559_; lean_object* v_unexpectedTk_560_; lean_object* v_unexpected_561_; lean_object* v_expected_562_; uint8_t v___x_563_; 
v_unexpectedTk_557_ = lean_ctor_get(v_x_555_, 0);
v_unexpected_558_ = lean_ctor_get(v_x_555_, 1);
v_expected_559_ = lean_ctor_get(v_x_555_, 2);
v_unexpectedTk_560_ = lean_ctor_get(v_x_556_, 0);
v_unexpected_561_ = lean_ctor_get(v_x_556_, 1);
v_expected_562_ = lean_ctor_get(v_x_556_, 2);
v___x_563_ = l_Lean_Syntax_structEq(v_unexpectedTk_557_, v_unexpectedTk_560_);
if (v___x_563_ == 0)
{
return v___x_563_;
}
else
{
uint8_t v___x_564_; 
v___x_564_ = lean_string_dec_eq(v_unexpected_558_, v_unexpected_561_);
if (v___x_564_ == 0)
{
return v___x_564_;
}
else
{
uint8_t v___x_565_; 
v___x_565_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_559_, v_expected_562_);
return v___x_565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object* v_x_566_, lean_object* v_x_567_){
_start:
{
uint8_t v_res_568_; lean_object* v_r_569_; 
v_res_568_ = l_Lean_Parser_instBEqError_beq(v_x_566_, v_x_567_);
lean_dec_ref(v_x_567_);
lean_dec_ref(v_x_566_);
v_r_569_ = lean_box(v_res_568_);
return v_r_569_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* v_x_574_){
_start:
{
if (lean_obj_tag(v_x_574_) == 0)
{
lean_object* v___x_575_; 
v___x_575_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
return v___x_575_;
}
else
{
lean_object* v_tail_576_; 
v_tail_576_ = lean_ctor_get(v_x_574_, 1);
if (lean_obj_tag(v_tail_576_) == 0)
{
lean_object* v_head_577_; 
v_head_577_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_head_577_);
lean_dec_ref_known(v_x_574_, 2);
return v_head_577_;
}
else
{
lean_object* v_tail_578_; 
lean_inc_ref(v_tail_576_);
v_tail_578_ = lean_ctor_get(v_tail_576_, 1);
if (lean_obj_tag(v_tail_578_) == 0)
{
lean_object* v_head_579_; lean_object* v_head_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v_head_579_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_head_579_);
lean_dec_ref_known(v_x_574_, 2);
v_head_580_ = lean_ctor_get(v_tail_576_, 0);
lean_inc(v_head_580_);
lean_dec_ref_known(v_tail_576_, 2);
v___x_581_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0));
v___x_582_ = lean_string_append(v_head_579_, v___x_581_);
v___x_583_ = lean_string_append(v___x_582_, v_head_580_);
lean_dec(v_head_580_);
return v___x_583_;
}
else
{
lean_object* v_head_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v_head_584_ = lean_ctor_get(v_x_574_, 0);
lean_inc(v_head_584_);
lean_dec_ref_known(v_x_574_, 2);
v___x_585_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_586_ = lean_string_append(v_head_584_, v___x_585_);
v___x_587_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_tail_576_);
v___x_588_ = lean_string_append(v___x_586_, v___x_587_);
lean_dec_ref(v___x_587_);
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object* v_as_589_){
_start:
{
lean_object* v___f_590_; lean_object* v___x_591_; 
v___f_590_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0));
v___x_591_ = l_List_eraseRepsBy___redArg(v___f_590_, v_as_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object* v_hi_592_, lean_object* v_pivot_593_, lean_object* v_as_594_, lean_object* v_i_595_, lean_object* v_k_596_){
_start:
{
uint8_t v___x_597_; 
v___x_597_ = lean_nat_dec_lt(v_k_596_, v_hi_592_);
if (v___x_597_ == 0)
{
lean_object* v___x_598_; lean_object* v___x_599_; 
lean_dec(v_k_596_);
v___x_598_ = lean_array_fswap(v_as_594_, v_i_595_, v_hi_592_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v_i_595_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
return v___x_599_;
}
else
{
lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_600_ = lean_array_fget_borrowed(v_as_594_, v_k_596_);
v___x_601_ = lean_string_dec_lt(v___x_600_, v_pivot_593_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_602_ = lean_unsigned_to_nat(1u);
v___x_603_ = lean_nat_add(v_k_596_, v___x_602_);
lean_dec(v_k_596_);
v_k_596_ = v___x_603_;
goto _start;
}
else
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v___x_605_ = lean_array_fswap(v_as_594_, v_i_595_, v_k_596_);
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_i_595_, v___x_606_);
lean_dec(v_i_595_);
v___x_608_ = lean_nat_add(v_k_596_, v___x_606_);
lean_dec(v_k_596_);
v_as_594_ = v___x_605_;
v_i_595_ = v___x_607_;
v_k_596_ = v___x_608_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object* v_hi_610_, lean_object* v_pivot_611_, lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_k_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_610_, v_pivot_611_, v_as_612_, v_i_613_, v_k_614_);
lean_dec_ref(v_pivot_611_);
lean_dec(v_hi_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_n_616_, lean_object* v_as_617_, lean_object* v_lo_618_, lean_object* v_hi_619_){
_start:
{
lean_object* v___y_621_; uint8_t v___x_631_; 
v___x_631_ = lean_nat_dec_lt(v_lo_618_, v_hi_619_);
if (v___x_631_ == 0)
{
lean_dec(v_lo_618_);
return v_as_617_;
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v_mid_634_; lean_object* v___y_636_; lean_object* v___y_642_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_632_ = lean_nat_add(v_lo_618_, v_hi_619_);
v___x_633_ = lean_unsigned_to_nat(1u);
v_mid_634_ = lean_nat_shiftr(v___x_632_, v___x_633_);
lean_dec(v___x_632_);
v___x_647_ = lean_array_fget_borrowed(v_as_617_, v_mid_634_);
v___x_648_ = lean_array_fget_borrowed(v_as_617_, v_lo_618_);
v___x_649_ = lean_string_dec_lt(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
v___y_642_ = v_as_617_;
goto v___jp_641_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_array_fswap(v_as_617_, v_lo_618_, v_mid_634_);
v___y_642_ = v___x_650_;
goto v___jp_641_;
}
v___jp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_637_ = lean_array_fget_borrowed(v___y_636_, v_mid_634_);
v___x_638_ = lean_array_fget_borrowed(v___y_636_, v_hi_619_);
v___x_639_ = lean_string_dec_lt(v___x_637_, v___x_638_);
if (v___x_639_ == 0)
{
lean_dec(v_mid_634_);
v___y_621_ = v___y_636_;
goto v___jp_620_;
}
else
{
lean_object* v___x_640_; 
v___x_640_ = lean_array_fswap(v___y_636_, v_mid_634_, v_hi_619_);
lean_dec(v_mid_634_);
v___y_621_ = v___x_640_;
goto v___jp_620_;
}
}
v___jp_641_:
{
lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v___x_643_ = lean_array_fget_borrowed(v___y_642_, v_hi_619_);
v___x_644_ = lean_array_fget_borrowed(v___y_642_, v_lo_618_);
v___x_645_ = lean_string_dec_lt(v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
v___y_636_ = v___y_642_;
goto v___jp_635_;
}
else
{
lean_object* v___x_646_; 
v___x_646_ = lean_array_fswap(v___y_642_, v_lo_618_, v_hi_619_);
v___y_636_ = v___x_646_;
goto v___jp_635_;
}
}
}
v___jp_620_:
{
lean_object* v_pivot_622_; lean_object* v___x_623_; lean_object* v_fst_624_; lean_object* v_snd_625_; uint8_t v___x_626_; 
v_pivot_622_ = lean_array_fget(v___y_621_, v_hi_619_);
lean_inc_n(v_lo_618_, 2);
v___x_623_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_619_, v_pivot_622_, v___y_621_, v_lo_618_, v_lo_618_);
lean_dec(v_pivot_622_);
v_fst_624_ = lean_ctor_get(v___x_623_, 0);
lean_inc(v_fst_624_);
v_snd_625_ = lean_ctor_get(v___x_623_, 1);
lean_inc(v_snd_625_);
lean_dec_ref(v___x_623_);
v___x_626_ = lean_nat_dec_le(v_hi_619_, v_fst_624_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_627_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_616_, v_snd_625_, v_lo_618_, v_fst_624_);
v___x_628_ = lean_unsigned_to_nat(1u);
v___x_629_ = lean_nat_add(v_fst_624_, v___x_628_);
lean_dec(v_fst_624_);
v_as_617_ = v___x_627_;
v_lo_618_ = v___x_629_;
goto _start;
}
else
{
lean_dec(v_fst_624_);
lean_dec(v_lo_618_);
return v_snd_625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_n_651_, lean_object* v_as_652_, lean_object* v_lo_653_, lean_object* v_hi_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_651_, v_as_652_, v_lo_653_, v_hi_654_);
lean_dec(v_hi_654_);
lean_dec(v_n_651_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_658_){
_start:
{
lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v_unexpected_691_; lean_object* v_expected_692_; lean_object* v___y_694_; lean_object* v___x_704_; uint8_t v___x_705_; 
v_unexpected_691_ = lean_ctor_get(v_e_658_, 1);
lean_inc_ref(v_unexpected_691_);
v_expected_692_ = lean_ctor_get(v_e_658_, 2);
lean_inc(v_expected_692_);
lean_dec_ref(v_e_658_);
v___x_704_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_705_ = lean_string_dec_eq(v_unexpected_691_, v___x_704_);
if (v___x_705_ == 0)
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_box(0);
v___x_707_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_707_, 0, v_unexpected_691_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
v___y_694_ = v___x_707_;
goto v___jp_693_;
}
else
{
lean_object* v___x_708_; 
lean_dec_ref(v_unexpected_691_);
v___x_708_ = lean_box(0);
v___y_694_ = v___x_708_;
goto v___jp_693_;
}
v___jp_659_:
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_662_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_663_ = l_List_appendTR___redArg(v___y_660_, v___y_661_);
v___x_664_ = l_String_intercalate(v___x_662_, v___x_663_);
return v___x_664_;
}
v___jp_665_:
{
lean_object* v___x_669_; lean_object* v_expected_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_669_ = lean_array_to_list(v___y_668_);
v_expected_670_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_669_);
v___x_671_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_672_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_670_);
v___x_673_ = lean_string_append(v___x_671_, v___x_672_);
lean_dec_ref(v___x_672_);
v___x_674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v___y_666_);
v___y_660_ = v___y_667_;
v___y_661_ = v___x_674_;
goto v___jp_659_;
}
v___jp_675_:
{
lean_object* v___x_682_; 
v___x_682_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_680_, v___y_677_, v___y_678_, v___y_681_);
lean_dec(v___y_681_);
lean_dec(v___y_680_);
v___y_666_ = v___y_676_;
v___y_667_ = v___y_679_;
v___y_668_ = v___x_682_;
goto v___jp_665_;
}
v___jp_683_:
{
uint8_t v___x_690_; 
v___x_690_ = lean_nat_dec_le(v___y_689_, v___y_686_);
if (v___x_690_ == 0)
{
lean_dec(v___y_686_);
lean_inc(v___y_689_);
v___y_676_ = v___y_684_;
v___y_677_ = v___y_685_;
v___y_678_ = v___y_689_;
v___y_679_ = v___y_687_;
v___y_680_ = v___y_688_;
v___y_681_ = v___y_689_;
goto v___jp_675_;
}
else
{
v___y_676_ = v___y_684_;
v___y_677_ = v___y_685_;
v___y_678_ = v___y_689_;
v___y_679_ = v___y_687_;
v___y_680_ = v___y_688_;
v___y_681_ = v___y_686_;
goto v___jp_675_;
}
}
v___jp_693_:
{
lean_object* v___x_695_; uint8_t v___x_696_; 
v___x_695_ = lean_box(0);
v___x_696_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_692_, v___x_695_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_697_ = lean_array_mk(v_expected_692_);
v___x_698_ = lean_array_get_size(v___x_697_);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_nat_dec_eq(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = lean_nat_sub(v___x_698_, v___x_701_);
v___x_703_ = lean_nat_dec_le(v___x_699_, v___x_702_);
if (v___x_703_ == 0)
{
lean_inc(v___x_702_);
v___y_684_ = v___x_695_;
v___y_685_ = v___x_697_;
v___y_686_ = v___x_702_;
v___y_687_ = v___y_694_;
v___y_688_ = v___x_698_;
v___y_689_ = v___x_702_;
goto v___jp_683_;
}
else
{
v___y_684_ = v___x_695_;
v___y_685_ = v___x_697_;
v___y_686_ = v___x_702_;
v___y_687_ = v___y_694_;
v___y_688_ = v___x_698_;
v___y_689_ = v___x_699_;
goto v___jp_683_;
}
}
else
{
v___y_666_ = v___x_695_;
v___y_667_ = v___y_694_;
v___y_668_ = v___x_697_;
goto v___jp_665_;
}
}
else
{
lean_dec(v_expected_692_);
v___y_660_ = v___y_694_;
v___y_661_ = v___x_695_;
goto v___jp_659_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_709_, lean_object* v_as_710_, lean_object* v_lo_711_, lean_object* v_hi_712_, lean_object* v_w_713_, lean_object* v_hlo_714_, lean_object* v_hhi_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_709_, v_as_710_, v_lo_711_, v_hi_712_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_717_, lean_object* v_as_718_, lean_object* v_lo_719_, lean_object* v_hi_720_, lean_object* v_w_721_, lean_object* v_hlo_722_, lean_object* v_hhi_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_717_, v_as_718_, v_lo_719_, v_hi_720_, v_w_721_, v_hlo_722_, v_hhi_723_);
lean_dec(v_hi_720_);
lean_dec(v_n_717_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object* v_n_725_, lean_object* v_lo_726_, lean_object* v_hi_727_, lean_object* v_hhi_728_, lean_object* v_pivot_729_, lean_object* v_as_730_, lean_object* v_i_731_, lean_object* v_k_732_, lean_object* v_ilo_733_, lean_object* v_ik_734_, lean_object* v_w_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_727_, v_pivot_729_, v_as_730_, v_i_731_, v_k_732_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object* v_n_737_, lean_object* v_lo_738_, lean_object* v_hi_739_, lean_object* v_hhi_740_, lean_object* v_pivot_741_, lean_object* v_as_742_, lean_object* v_i_743_, lean_object* v_k_744_, lean_object* v_ilo_745_, lean_object* v_ik_746_, lean_object* v_w_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_737_, v_lo_738_, v_hi_739_, v_hhi_740_, v_pivot_741_, v_as_742_, v_i_743_, v_k_744_, v_ilo_745_, v_ik_746_, v_w_747_);
lean_dec_ref(v_pivot_741_);
lean_dec(v_hi_739_);
lean_dec(v_lo_738_);
lean_dec(v_n_737_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_751_, lean_object* v_e_u2082_752_){
_start:
{
lean_object* v_unexpectedTk_753_; lean_object* v_unexpected_754_; lean_object* v_expected_755_; lean_object* v___y_757_; lean_object* v___x_769_; uint8_t v___x_770_; 
v_unexpectedTk_753_ = lean_ctor_get(v_e_u2082_752_, 0);
lean_inc(v_unexpectedTk_753_);
v_unexpected_754_ = lean_ctor_get(v_e_u2082_752_, 1);
lean_inc_ref(v_unexpected_754_);
v_expected_755_ = lean_ctor_get(v_e_u2082_752_, 2);
lean_inc(v_expected_755_);
lean_dec_ref(v_e_u2082_752_);
v___x_769_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_770_ = lean_string_dec_eq(v_unexpected_754_, v___x_769_);
if (v___x_770_ == 0)
{
v___y_757_ = v_unexpected_754_;
goto v___jp_756_;
}
else
{
lean_object* v_unexpected_771_; 
lean_dec_ref(v_unexpected_754_);
v_unexpected_771_ = lean_ctor_get(v_e_u2081_751_, 1);
lean_inc_ref(v_unexpected_771_);
v___y_757_ = v_unexpected_771_;
goto v___jp_756_;
}
v___jp_756_:
{
lean_object* v_expected_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_766_; 
v_expected_758_ = lean_ctor_get(v_e_u2081_751_, 2);
v_isSharedCheck_766_ = !lean_is_exclusive(v_e_u2081_751_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; lean_object* v_unused_768_; 
v_unused_767_ = lean_ctor_get(v_e_u2081_751_, 1);
lean_dec(v_unused_767_);
v_unused_768_ = lean_ctor_get(v_e_u2081_751_, 0);
lean_dec(v_unused_768_);
v___x_760_ = v_e_u2081_751_;
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_expected_758_);
lean_dec(v_e_u2081_751_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_766_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_762_; lean_object* v___x_764_; 
v___x_762_ = l_List_appendTR___redArg(v_expected_758_, v_expected_755_);
if (v_isShared_761_ == 0)
{
lean_ctor_set(v___x_760_, 2, v___x_762_);
lean_ctor_set(v___x_760_, 1, v___y_757_);
lean_ctor_set(v___x_760_, 0, v_unexpectedTk_753_);
v___x_764_ = v___x_760_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_unexpectedTk_753_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v___y_757_);
lean_ctor_set(v_reuseFailAlloc_765_, 2, v___x_762_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(lean_object* v_x_772_, lean_object* v_x_773_){
_start:
{
if (lean_obj_tag(v_x_772_) == 0)
{
if (lean_obj_tag(v_x_773_) == 0)
{
uint8_t v___x_774_; 
v___x_774_ = 1;
return v___x_774_;
}
else
{
uint8_t v___x_775_; 
v___x_775_ = 0;
return v___x_775_;
}
}
else
{
if (lean_obj_tag(v_x_773_) == 0)
{
uint8_t v___x_776_; 
v___x_776_ = 0;
return v___x_776_;
}
else
{
lean_object* v_val_777_; lean_object* v_val_778_; uint8_t v_decide_779_; 
v_val_777_ = lean_ctor_get(v_x_772_, 0);
v_val_778_ = lean_ctor_get(v_x_773_, 0);
v_decide_779_ = lean_nat_dec_eq(v_val_777_, v_val_778_);
return v_decide_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0___boxed(lean_object* v_x_780_, lean_object* v_x_781_){
_start:
{
uint8_t v_res_782_; lean_object* v_r_783_; 
v_res_782_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_x_780_, v_x_781_);
lean_dec(v_x_781_);
lean_dec(v_x_780_);
v_r_783_ = lean_box(v_res_782_);
return v_r_783_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(lean_object* v_xs_784_, lean_object* v_ys_785_, lean_object* v_x_786_){
_start:
{
lean_object* v_zero_787_; uint8_t v_isZero_788_; 
v_zero_787_ = lean_unsigned_to_nat(0u);
v_isZero_788_ = lean_nat_dec_eq(v_x_786_, v_zero_787_);
if (v_isZero_788_ == 1)
{
lean_dec(v_x_786_);
return v_isZero_788_;
}
else
{
lean_object* v_one_789_; lean_object* v_n_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_one_789_ = lean_unsigned_to_nat(1u);
v_n_790_ = lean_nat_sub(v_x_786_, v_one_789_);
lean_dec(v_x_786_);
v___x_791_ = lean_array_fget_borrowed(v_xs_784_, v_n_790_);
v___x_792_ = lean_array_fget_borrowed(v_ys_785_, v_n_790_);
v___x_793_ = lean_string_dec_eq(v___x_791_, v___x_792_);
if (v___x_793_ == 0)
{
lean_dec(v_n_790_);
return v___x_793_;
}
else
{
v_x_786_ = v_n_790_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg___boxed(lean_object* v_xs_795_, lean_object* v_ys_796_, lean_object* v_x_797_){
_start:
{
uint8_t v_res_798_; lean_object* v_r_799_; 
v_res_798_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_795_, v_ys_796_, v_x_797_);
lean_dec_ref(v_ys_796_);
lean_dec_ref(v_xs_795_);
v_r_799_ = lean_box(v_res_798_);
return v_r_799_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_800_, lean_object* v_x_801_){
_start:
{
lean_object* v_toCacheableParserContext_802_; lean_object* v_parserName_803_; lean_object* v_pos_804_; lean_object* v_toCacheableParserContext_805_; lean_object* v_parserName_806_; lean_object* v_pos_807_; uint8_t v___y_812_; lean_object* v_prec_813_; lean_object* v_quotDepth_814_; uint8_t v_suppressInsideQuot_815_; lean_object* v_savedPos_x3f_816_; lean_object* v_forbiddenTks_817_; lean_object* v_prec_818_; lean_object* v_quotDepth_819_; uint8_t v_suppressInsideQuot_820_; lean_object* v_savedPos_x3f_821_; lean_object* v_forbiddenTks_822_; uint8_t v___x_832_; 
v_toCacheableParserContext_802_ = lean_ctor_get(v_x_800_, 0);
v_parserName_803_ = lean_ctor_get(v_x_800_, 1);
v_pos_804_ = lean_ctor_get(v_x_800_, 2);
v_toCacheableParserContext_805_ = lean_ctor_get(v_x_801_, 0);
v_parserName_806_ = lean_ctor_get(v_x_801_, 1);
v_pos_807_ = lean_ctor_get(v_x_801_, 2);
v_prec_813_ = lean_ctor_get(v_toCacheableParserContext_802_, 0);
v_quotDepth_814_ = lean_ctor_get(v_toCacheableParserContext_802_, 1);
v_suppressInsideQuot_815_ = lean_ctor_get_uint8(v_toCacheableParserContext_802_, sizeof(void*)*4);
v_savedPos_x3f_816_ = lean_ctor_get(v_toCacheableParserContext_802_, 2);
v_forbiddenTks_817_ = lean_ctor_get(v_toCacheableParserContext_802_, 3);
v_prec_818_ = lean_ctor_get(v_toCacheableParserContext_805_, 0);
v_quotDepth_819_ = lean_ctor_get(v_toCacheableParserContext_805_, 1);
v_suppressInsideQuot_820_ = lean_ctor_get_uint8(v_toCacheableParserContext_805_, sizeof(void*)*4);
v_savedPos_x3f_821_ = lean_ctor_get(v_toCacheableParserContext_805_, 2);
v_forbiddenTks_822_ = lean_ctor_get(v_toCacheableParserContext_805_, 3);
v___x_832_ = lean_nat_dec_eq(v_prec_813_, v_prec_818_);
if (v___x_832_ == 0)
{
return v___x_832_;
}
else
{
uint8_t v___x_833_; 
v___x_833_ = lean_nat_dec_eq(v_quotDepth_814_, v_quotDepth_819_);
if (v___x_833_ == 0)
{
return v___x_833_;
}
else
{
if (v_suppressInsideQuot_820_ == 0)
{
if (v_suppressInsideQuot_815_ == 0)
{
goto v___jp_823_;
}
else
{
return v_suppressInsideQuot_820_;
}
}
else
{
if (v_suppressInsideQuot_815_ == 0)
{
return v_suppressInsideQuot_815_;
}
else
{
goto v___jp_823_;
}
}
}
}
v___jp_808_:
{
uint8_t v___x_809_; 
v___x_809_ = lean_name_eq(v_parserName_803_, v_parserName_806_);
if (v___x_809_ == 0)
{
return v___x_809_;
}
else
{
uint8_t v_decide_810_; 
v_decide_810_ = lean_nat_dec_eq(v_pos_804_, v_pos_807_);
return v_decide_810_;
}
}
v___jp_811_:
{
if (v___y_812_ == 0)
{
return v___y_812_;
}
else
{
goto v___jp_808_;
}
}
v___jp_823_:
{
uint8_t v___x_824_; 
v___x_824_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_savedPos_x3f_816_, v_savedPos_x3f_821_);
if (v___x_824_ == 0)
{
v___y_812_ = v___x_824_;
goto v___jp_811_;
}
else
{
size_t v___x_825_; size_t v___x_826_; uint8_t v___x_827_; 
v___x_825_ = lean_ptr_addr(v_forbiddenTks_817_);
v___x_826_ = lean_ptr_addr(v_forbiddenTks_822_);
v___x_827_ = lean_usize_dec_eq(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_828_ = lean_array_get_size(v_forbiddenTks_817_);
v___x_829_ = lean_array_get_size(v_forbiddenTks_822_);
v___x_830_ = lean_nat_dec_eq(v___x_828_, v___x_829_);
if (v___x_830_ == 0)
{
return v___x_830_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_forbiddenTks_817_, v_forbiddenTks_822_, v___x_828_);
v___y_812_ = v___x_831_;
goto v___jp_811_;
}
}
else
{
goto v___jp_808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object* v_x_834_, lean_object* v_x_835_){
_start:
{
uint8_t v_res_836_; lean_object* v_r_837_; 
v_res_836_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_834_, v_x_835_);
lean_dec_ref(v_x_835_);
lean_dec_ref(v_x_834_);
v_r_837_ = lean_box(v_res_836_);
return v_r_837_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(lean_object* v_xs_838_, lean_object* v_ys_839_, lean_object* v_hsz_840_, lean_object* v_x_841_, lean_object* v_x_842_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_838_, v_ys_839_, v_x_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___boxed(lean_object* v_xs_844_, lean_object* v_ys_845_, lean_object* v_hsz_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
uint8_t v_res_849_; lean_object* v_r_850_; 
v_res_849_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(v_xs_844_, v_ys_845_, v_hsz_846_, v_x_847_, v_x_848_);
lean_dec_ref(v_ys_845_);
lean_dec_ref(v_xs_844_);
v_r_850_ = lean_box(v_res_849_);
return v_r_850_;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* v_k_853_){
_start:
{
lean_object* v_parserName_854_; lean_object* v_pos_855_; uint64_t v___x_856_; 
v_parserName_854_ = lean_ctor_get(v_k_853_, 1);
v_pos_855_ = lean_ctor_get(v_k_853_, 2);
v___x_856_ = l_String_instHashableRaw_hash(v_pos_855_);
if (lean_obj_tag(v_parserName_854_) == 0)
{
uint64_t v___x_857_; uint64_t v___x_858_; 
v___x_857_ = 1723ULL;
v___x_858_ = lean_uint64_mix_hash(v___x_856_, v___x_857_);
return v___x_858_;
}
else
{
uint64_t v_hash_859_; uint64_t v___x_860_; 
v_hash_859_ = lean_ctor_get_uint64(v_parserName_854_, sizeof(void*)*2);
v___x_860_ = lean_uint64_mix_hash(v___x_856_, v_hash_859_);
return v___x_860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* v_k_861_){
_start:
{
uint64_t v_res_862_; lean_object* v_r_863_; 
v_res_862_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_861_);
lean_dec_ref(v_k_861_);
v_r_863_ = lean_box_uint64(v_res_862_);
return v_r_863_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0(void){
_start:
{
uint32_t v___x_866_; lean_object* v___x_867_; 
v___x_866_ = 32;
v___x_867_ = l_Char_utf8Size(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = lean_box(0);
v___x_869_ = lean_unsigned_to_nat(16u);
v___x_870_ = lean_mk_array(v___x_869_, v___x_868_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__2(void){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_871_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_872_ = lean_unsigned_to_nat(0u);
v___x_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v___x_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_874_){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_875_ = lean_string_utf8_byte_size(v_input_874_);
v___x_876_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_877_ = lean_nat_add(v___x_875_, v___x_876_);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_box(0);
v___x_880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_880_, 0, v___x_877_);
lean_ctor_set(v___x_880_, 1, v___x_878_);
lean_ctor_set(v___x_880_, 2, v___x_879_);
v___x_881_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_880_);
lean_ctor_set(v___x_882_, 1, v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Parser_initCacheForInput(v_input_883_);
lean_dec_ref(v_input_883_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_885_){
_start:
{
lean_object* v_raw_886_; lean_object* v_drop_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_raw_886_ = lean_ctor_get(v_stack_885_, 0);
lean_inc_ref(v_raw_886_);
v_drop_887_ = lean_ctor_get(v_stack_885_, 1);
lean_inc(v_drop_887_);
lean_dec_ref(v_stack_885_);
v___x_888_ = lean_array_get_size(v_raw_886_);
v___x_889_ = l_Array_toSubarray___redArg(v_raw_886_, v_drop_887_, v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_896_){
_start:
{
lean_object* v_raw_897_; lean_object* v_drop_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_raw_897_ = lean_ctor_get(v_stack_896_, 0);
v_drop_898_ = lean_ctor_get(v_stack_896_, 1);
v___x_899_ = lean_array_get_size(v_raw_897_);
v___x_900_ = lean_nat_sub(v___x_899_, v_drop_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Lean_Parser_SyntaxStack_size(v_stack_901_);
lean_dec_ref(v_stack_901_);
return v_res_902_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_903_){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v___x_904_ = l_Lean_Parser_SyntaxStack_size(v_stack_903_);
v___x_905_ = lean_unsigned_to_nat(0u);
v___x_906_ = lean_nat_dec_eq(v___x_904_, v___x_905_);
lean_dec(v___x_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_907_){
_start:
{
uint8_t v_res_908_; lean_object* v_r_909_; 
v_res_908_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_907_);
lean_dec_ref(v_stack_907_);
v_r_909_ = lean_box(v_res_908_);
return v_r_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_910_, lean_object* v_n_911_){
_start:
{
lean_object* v_raw_912_; lean_object* v_drop_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_922_; 
v_raw_912_ = lean_ctor_get(v_stack_910_, 0);
v_drop_913_ = lean_ctor_get(v_stack_910_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_stack_910_);
if (v_isSharedCheck_922_ == 0)
{
v___x_915_ = v_stack_910_;
v_isShared_916_ = v_isSharedCheck_922_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_drop_913_);
lean_inc(v_raw_912_);
lean_dec(v_stack_910_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_922_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_917_ = lean_nat_add(v_drop_913_, v_n_911_);
v___x_918_ = l_Array_shrink___redArg(v_raw_912_, v___x_917_);
lean_dec(v___x_917_);
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 0, v___x_918_);
v___x_920_ = v___x_915_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_drop_913_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_923_, lean_object* v_n_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_923_, v_n_924_);
lean_dec(v_n_924_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_926_, lean_object* v_a_927_){
_start:
{
lean_object* v_raw_928_; lean_object* v_drop_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_937_; 
v_raw_928_ = lean_ctor_get(v_stack_926_, 0);
v_drop_929_ = lean_ctor_get(v_stack_926_, 1);
v_isSharedCheck_937_ = !lean_is_exclusive(v_stack_926_);
if (v_isSharedCheck_937_ == 0)
{
v___x_931_ = v_stack_926_;
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_drop_929_);
lean_inc(v_raw_928_);
lean_dec(v_stack_926_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_937_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_933_ = lean_array_push(v_raw_928_, v_a_927_);
if (v_isShared_932_ == 0)
{
lean_ctor_set(v___x_931_, 0, v___x_933_);
v___x_935_ = v___x_931_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_936_, 1, v_drop_929_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_938_){
_start:
{
lean_object* v___x_939_; lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_939_ = lean_unsigned_to_nat(0u);
v___x_940_ = l_Lean_Parser_SyntaxStack_size(v_stack_938_);
v___x_941_ = lean_nat_dec_lt(v___x_939_, v___x_940_);
lean_dec(v___x_940_);
if (v___x_941_ == 0)
{
return v_stack_938_;
}
else
{
lean_object* v_raw_942_; lean_object* v_drop_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_951_; 
v_raw_942_ = lean_ctor_get(v_stack_938_, 0);
v_drop_943_ = lean_ctor_get(v_stack_938_, 1);
v_isSharedCheck_951_ = !lean_is_exclusive(v_stack_938_);
if (v_isSharedCheck_951_ == 0)
{
v___x_945_ = v_stack_938_;
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_drop_943_);
lean_inc(v_raw_942_);
lean_dec(v_stack_938_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_951_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_949_; 
v___x_947_ = lean_array_pop(v_raw_942_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 0, v___x_947_);
v___x_949_ = v___x_945_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v_drop_943_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_952_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_box(0);
v___x_954_ = lean_panic_fn_borrowed(v___x_953_, v_msg_952_);
return v___x_954_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_958_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_959_ = lean_unsigned_to_nat(4u);
v___x_960_ = lean_unsigned_to_nat(315u);
v___x_961_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_962_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_963_ = l_mkPanicMessageWithDecl(v___x_962_, v___x_961_, v___x_960_, v___x_959_, v___x_958_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_964_){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = l_Lean_Parser_SyntaxStack_size(v_stack_964_);
v___x_967_ = lean_nat_dec_lt(v___x_965_, v___x_966_);
lean_dec(v___x_966_);
if (v___x_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_968_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_969_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_968_);
return v___x_969_;
}
else
{
lean_object* v_raw_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_raw_970_ = lean_ctor_get(v_stack_964_, 0);
v___x_971_ = lean_box(0);
v___x_972_ = lean_array_get_size(v_raw_970_);
v___x_973_ = lean_unsigned_to_nat(1u);
v___x_974_ = lean_nat_sub(v___x_972_, v___x_973_);
v___x_975_ = lean_array_get_borrowed(v___x_971_, v_raw_970_, v___x_974_);
lean_dec(v___x_974_);
lean_inc(v___x_975_);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Lean_Parser_SyntaxStack_back(v_stack_976_);
lean_dec_ref(v_stack_976_);
return v_res_977_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_980_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_981_ = lean_unsigned_to_nat(4u);
v___x_982_ = lean_unsigned_to_nat(321u);
v___x_983_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_984_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_985_ = l_mkPanicMessageWithDecl(v___x_984_, v___x_983_, v___x_982_, v___x_981_, v___x_980_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_986_, lean_object* v_i_987_){
_start:
{
lean_object* v___x_988_; uint8_t v___x_989_; 
v___x_988_ = l_Lean_Parser_SyntaxStack_size(v_stack_986_);
v___x_989_ = lean_nat_dec_lt(v_i_987_, v___x_988_);
lean_dec(v___x_988_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_991_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_990_);
return v___x_991_;
}
else
{
lean_object* v_raw_992_; lean_object* v_drop_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_raw_992_ = lean_ctor_get(v_stack_986_, 0);
v_drop_993_ = lean_ctor_get(v_stack_986_, 1);
v___x_994_ = lean_box(0);
v___x_995_ = lean_nat_add(v_drop_993_, v_i_987_);
v___x_996_ = lean_array_get_borrowed(v___x_994_, v_raw_992_, v___x_995_);
lean_dec(v___x_995_);
lean_inc(v___x_996_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_997_, lean_object* v_i_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_997_, v_i_998_);
lean_dec(v_i_998_);
lean_dec_ref(v_stack_997_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_1000_, lean_object* v_start_1001_, lean_object* v_stop_1002_){
_start:
{
lean_object* v_raw_1003_; lean_object* v_drop_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_raw_1003_ = lean_ctor_get(v_stack_1000_, 0);
v_drop_1004_ = lean_ctor_get(v_stack_1000_, 1);
v___x_1005_ = lean_nat_add(v_drop_1004_, v_start_1001_);
v___x_1006_ = lean_nat_add(v_drop_1004_, v_stop_1002_);
v___x_1007_ = l_Array_extract___redArg(v_raw_1003_, v___x_1005_, v___x_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_1008_, lean_object* v_start_1009_, lean_object* v_stop_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Parser_SyntaxStack_extract(v_stack_1008_, v_start_1009_, v_stop_1010_);
lean_dec(v_stop_1010_);
lean_dec(v_start_1009_);
lean_dec_ref(v_stack_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_1012_, lean_object* v_stxs_1013_){
_start:
{
lean_object* v_raw_1014_; lean_object* v_drop_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1023_; 
v_raw_1014_ = lean_ctor_get(v_stack_1012_, 0);
v_drop_1015_ = lean_ctor_get(v_stack_1012_, 1);
v_isSharedCheck_1023_ = !lean_is_exclusive(v_stack_1012_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1017_ = v_stack_1012_;
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_drop_1015_);
lean_inc(v_raw_1014_);
lean_dec(v_stack_1012_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1019_ = l_Array_append___redArg(v_raw_1014_, v_stxs_1013_);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1019_);
v___x_1021_ = v___x_1017_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1022_, 1, v_drop_1015_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_1024_, lean_object* v_stxs_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_1024_, v_stxs_1025_);
lean_dec_ref(v_stxs_1025_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_1027_, lean_object* v_stxs_1028_){
_start:
{
lean_object* v_raw_1029_; lean_object* v_drop_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
v_raw_1029_ = lean_ctor_get(v_stack_1027_, 0);
v_drop_1030_ = lean_ctor_get(v_stack_1027_, 1);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_stack_1027_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1032_ = v_stack_1027_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_drop_1030_);
lean_inc(v_raw_1029_);
lean_dec(v_stack_1027_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
v___x_1034_ = l_Array_append___redArg(v_raw_1029_, v_stxs_1028_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1034_);
v___x_1036_ = v___x_1032_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_drop_1030_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_1039_, lean_object* v_stxs_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_1039_, v_stxs_1040_);
lean_dec_ref(v_stxs_1040_);
return v_res_1041_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_1044_){
_start:
{
lean_object* v_errorMsg_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_errorMsg_1045_ = lean_ctor_get(v_s_1044_, 4);
lean_inc(v_errorMsg_1045_);
lean_dec_ref(v_s_1044_);
v___x_1046_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_1047_ = lean_box(0);
v___x_1048_ = l_Option_instBEq_beq___redArg(v___x_1046_, v_errorMsg_1045_, v___x_1047_);
if (v___x_1048_ == 0)
{
uint8_t v___x_1049_; 
v___x_1049_ = 1;
return v___x_1049_;
}
else
{
uint8_t v___x_1050_; 
v___x_1050_ = 0;
return v___x_1050_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_1051_){
_start:
{
uint8_t v_res_1052_; lean_object* v_r_1053_; 
v_res_1052_ = l_Lean_Parser_ParserState_hasError(v_s_1051_);
v_r_1053_ = lean_box(v_res_1052_);
return v_r_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_1054_){
_start:
{
lean_object* v_stxStack_1055_; lean_object* v___x_1056_; 
v_stxStack_1055_ = lean_ctor_get(v_s_1054_, 0);
v___x_1056_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Lean_Parser_ParserState_stackSize(v_s_1057_);
lean_dec_ref(v_s_1057_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_1059_, lean_object* v_iniStackSz_1060_, lean_object* v_iniPos_1061_){
_start:
{
lean_object* v_stxStack_1062_; lean_object* v_lhsPrec_1063_; lean_object* v_cache_1064_; lean_object* v_recoveredErrors_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1074_; 
v_stxStack_1062_ = lean_ctor_get(v_s_1059_, 0);
v_lhsPrec_1063_ = lean_ctor_get(v_s_1059_, 1);
v_cache_1064_ = lean_ctor_get(v_s_1059_, 3);
v_recoveredErrors_1065_ = lean_ctor_get(v_s_1059_, 5);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_s_1059_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; lean_object* v_unused_1076_; 
v_unused_1075_ = lean_ctor_get(v_s_1059_, 4);
lean_dec(v_unused_1075_);
v_unused_1076_ = lean_ctor_get(v_s_1059_, 2);
lean_dec(v_unused_1076_);
v___x_1067_ = v_s_1059_;
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_recoveredErrors_1065_);
lean_inc(v_cache_1064_);
lean_inc(v_lhsPrec_1063_);
lean_inc(v_stxStack_1062_);
lean_dec(v_s_1059_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v___x_1069_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1062_, v_iniStackSz_1060_);
v___x_1070_ = lean_box(0);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 4, v___x_1070_);
lean_ctor_set(v___x_1067_, 2, v_iniPos_1061_);
lean_ctor_set(v___x_1067_, 0, v___x_1069_);
v___x_1072_ = v___x_1067_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v___x_1069_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_lhsPrec_1063_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v_iniPos_1061_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_cache_1064_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1073_, 5, v_recoveredErrors_1065_);
v___x_1072_ = v_reuseFailAlloc_1073_;
goto v_reusejp_1071_;
}
v_reusejp_1071_:
{
return v___x_1072_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_1077_, lean_object* v_iniStackSz_1078_, lean_object* v_iniPos_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_Parser_ParserState_restore(v_s_1077_, v_iniStackSz_1078_, v_iniPos_1079_);
lean_dec(v_iniStackSz_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_1081_, lean_object* v_pos_1082_){
_start:
{
lean_object* v_stxStack_1083_; lean_object* v_lhsPrec_1084_; lean_object* v_cache_1085_; lean_object* v_errorMsg_1086_; lean_object* v_recoveredErrors_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_stxStack_1083_ = lean_ctor_get(v_s_1081_, 0);
v_lhsPrec_1084_ = lean_ctor_get(v_s_1081_, 1);
v_cache_1085_ = lean_ctor_get(v_s_1081_, 3);
v_errorMsg_1086_ = lean_ctor_get(v_s_1081_, 4);
v_recoveredErrors_1087_ = lean_ctor_get(v_s_1081_, 5);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_s_1081_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v_s_1081_, 2);
lean_dec(v_unused_1095_);
v___x_1089_ = v_s_1081_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_recoveredErrors_1087_);
lean_inc(v_errorMsg_1086_);
lean_inc(v_cache_1085_);
lean_inc(v_lhsPrec_1084_);
lean_inc(v_stxStack_1083_);
lean_dec(v_s_1081_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 2, v_pos_1082_);
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_stxStack_1083_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_lhsPrec_1084_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_pos_1082_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_cache_1085_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v_errorMsg_1086_);
lean_ctor_set(v_reuseFailAlloc_1093_, 5, v_recoveredErrors_1087_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_1096_, lean_object* v_cache_1097_){
_start:
{
lean_object* v_stxStack_1098_; lean_object* v_lhsPrec_1099_; lean_object* v_pos_1100_; lean_object* v_errorMsg_1101_; lean_object* v_recoveredErrors_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
v_stxStack_1098_ = lean_ctor_get(v_s_1096_, 0);
v_lhsPrec_1099_ = lean_ctor_get(v_s_1096_, 1);
v_pos_1100_ = lean_ctor_get(v_s_1096_, 2);
v_errorMsg_1101_ = lean_ctor_get(v_s_1096_, 4);
v_recoveredErrors_1102_ = lean_ctor_get(v_s_1096_, 5);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_s_1096_);
if (v_isSharedCheck_1109_ == 0)
{
lean_object* v_unused_1110_; 
v_unused_1110_ = lean_ctor_get(v_s_1096_, 3);
lean_dec(v_unused_1110_);
v___x_1104_ = v_s_1096_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_recoveredErrors_1102_);
lean_inc(v_errorMsg_1101_);
lean_inc(v_pos_1100_);
lean_inc(v_lhsPrec_1099_);
lean_inc(v_stxStack_1098_);
lean_dec(v_s_1096_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 3, v_cache_1097_);
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_stxStack_1098_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_lhsPrec_1099_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v_pos_1100_);
lean_ctor_set(v_reuseFailAlloc_1108_, 3, v_cache_1097_);
lean_ctor_set(v_reuseFailAlloc_1108_, 4, v_errorMsg_1101_);
lean_ctor_set(v_reuseFailAlloc_1108_, 5, v_recoveredErrors_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_1111_, lean_object* v_n_1112_){
_start:
{
lean_object* v_stxStack_1113_; lean_object* v_lhsPrec_1114_; lean_object* v_pos_1115_; lean_object* v_cache_1116_; lean_object* v_errorMsg_1117_; lean_object* v_recoveredErrors_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1126_; 
v_stxStack_1113_ = lean_ctor_get(v_s_1111_, 0);
v_lhsPrec_1114_ = lean_ctor_get(v_s_1111_, 1);
v_pos_1115_ = lean_ctor_get(v_s_1111_, 2);
v_cache_1116_ = lean_ctor_get(v_s_1111_, 3);
v_errorMsg_1117_ = lean_ctor_get(v_s_1111_, 4);
v_recoveredErrors_1118_ = lean_ctor_get(v_s_1111_, 5);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_s_1111_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1120_ = v_s_1111_;
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_recoveredErrors_1118_);
lean_inc(v_errorMsg_1117_);
lean_inc(v_cache_1116_);
lean_inc(v_pos_1115_);
lean_inc(v_lhsPrec_1114_);
lean_inc(v_stxStack_1113_);
lean_dec(v_s_1111_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1113_, v_n_1112_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1122_);
v___x_1124_ = v___x_1120_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v___x_1122_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_lhsPrec_1114_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v_pos_1115_);
lean_ctor_set(v_reuseFailAlloc_1125_, 3, v_cache_1116_);
lean_ctor_set(v_reuseFailAlloc_1125_, 4, v_errorMsg_1117_);
lean_ctor_set(v_reuseFailAlloc_1125_, 5, v_recoveredErrors_1118_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1127_){
_start:
{
lean_object* v_stxStack_1128_; lean_object* v_lhsPrec_1129_; lean_object* v_pos_1130_; lean_object* v_cache_1131_; lean_object* v_errorMsg_1132_; lean_object* v_recoveredErrors_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1141_; 
v_stxStack_1128_ = lean_ctor_get(v_s_1127_, 0);
v_lhsPrec_1129_ = lean_ctor_get(v_s_1127_, 1);
v_pos_1130_ = lean_ctor_get(v_s_1127_, 2);
v_cache_1131_ = lean_ctor_get(v_s_1127_, 3);
v_errorMsg_1132_ = lean_ctor_get(v_s_1127_, 4);
v_recoveredErrors_1133_ = lean_ctor_get(v_s_1127_, 5);
v_isSharedCheck_1141_ = !lean_is_exclusive(v_s_1127_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1135_ = v_s_1127_;
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
lean_dec(v_s_1127_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1141_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1137_; lean_object* v___x_1139_; 
v___x_1137_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1128_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1142_, lean_object* v_iniStackSz_1143_){
_start:
{
lean_object* v_stxStack_1144_; lean_object* v_lhsPrec_1145_; lean_object* v_pos_1146_; lean_object* v_cache_1147_; lean_object* v_errorMsg_1148_; lean_object* v_recoveredErrors_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1157_; 
v_stxStack_1144_ = lean_ctor_get(v_s_1142_, 0);
v_lhsPrec_1145_ = lean_ctor_get(v_s_1142_, 1);
v_pos_1146_ = lean_ctor_get(v_s_1142_, 2);
v_cache_1147_ = lean_ctor_get(v_s_1142_, 3);
v_errorMsg_1148_ = lean_ctor_get(v_s_1142_, 4);
v_recoveredErrors_1149_ = lean_ctor_get(v_s_1142_, 5);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_s_1142_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1151_ = v_s_1142_;
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_recoveredErrors_1149_);
lean_inc(v_errorMsg_1148_);
lean_inc(v_cache_1147_);
lean_inc(v_pos_1146_);
lean_inc(v_lhsPrec_1145_);
lean_inc(v_stxStack_1144_);
lean_dec(v_s_1142_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1157_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1153_; lean_object* v___x_1155_; 
v___x_1153_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1144_, v_iniStackSz_1143_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1153_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_lhsPrec_1145_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_pos_1146_);
lean_ctor_set(v_reuseFailAlloc_1156_, 3, v_cache_1147_);
lean_ctor_set(v_reuseFailAlloc_1156_, 4, v_errorMsg_1148_);
lean_ctor_set(v_reuseFailAlloc_1156_, 5, v_recoveredErrors_1149_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1158_, lean_object* v_iniStackSz_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1158_, v_iniStackSz_1159_);
lean_dec(v_iniStackSz_1159_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1161_, lean_object* v_c_1162_, lean_object* v_pos_1163_){
_start:
{
lean_object* v_toInputContext_1164_; lean_object* v_stxStack_1165_; lean_object* v_lhsPrec_1166_; lean_object* v_cache_1167_; lean_object* v_errorMsg_1168_; lean_object* v_recoveredErrors_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1178_; 
v_toInputContext_1164_ = lean_ctor_get(v_c_1162_, 0);
v_stxStack_1165_ = lean_ctor_get(v_s_1161_, 0);
v_lhsPrec_1166_ = lean_ctor_get(v_s_1161_, 1);
v_cache_1167_ = lean_ctor_get(v_s_1161_, 3);
v_errorMsg_1168_ = lean_ctor_get(v_s_1161_, 4);
v_recoveredErrors_1169_ = lean_ctor_get(v_s_1161_, 5);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_s_1161_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v_s_1161_, 2);
lean_dec(v_unused_1179_);
v___x_1171_ = v_s_1161_;
v_isShared_1172_ = v_isSharedCheck_1178_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_recoveredErrors_1169_);
lean_inc(v_errorMsg_1168_);
lean_inc(v_cache_1167_);
lean_inc(v_lhsPrec_1166_);
lean_inc(v_stxStack_1165_);
lean_dec(v_s_1161_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1178_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v_inputString_1173_; lean_object* v___x_1174_; lean_object* v___x_1176_; 
v_inputString_1173_ = lean_ctor_get(v_toInputContext_1164_, 0);
v___x_1174_ = lean_string_utf8_next(v_inputString_1173_, v_pos_1163_);
if (v_isShared_1172_ == 0)
{
lean_ctor_set(v___x_1171_, 2, v___x_1174_);
v___x_1176_ = v___x_1171_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_stxStack_1165_);
lean_ctor_set(v_reuseFailAlloc_1177_, 1, v_lhsPrec_1166_);
lean_ctor_set(v_reuseFailAlloc_1177_, 2, v___x_1174_);
lean_ctor_set(v_reuseFailAlloc_1177_, 3, v_cache_1167_);
lean_ctor_set(v_reuseFailAlloc_1177_, 4, v_errorMsg_1168_);
lean_ctor_set(v_reuseFailAlloc_1177_, 5, v_recoveredErrors_1169_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1180_, lean_object* v_c_1181_, lean_object* v_pos_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_Parser_ParserState_next(v_s_1180_, v_c_1181_, v_pos_1182_);
lean_dec(v_pos_1182_);
lean_dec_ref(v_c_1181_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1184_, lean_object* v_c_1185_, lean_object* v_pos_1186_){
_start:
{
lean_object* v_toInputContext_1187_; lean_object* v_stxStack_1188_; lean_object* v_lhsPrec_1189_; lean_object* v_cache_1190_; lean_object* v_errorMsg_1191_; lean_object* v_recoveredErrors_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1201_; 
v_toInputContext_1187_ = lean_ctor_get(v_c_1185_, 0);
v_stxStack_1188_ = lean_ctor_get(v_s_1184_, 0);
v_lhsPrec_1189_ = lean_ctor_get(v_s_1184_, 1);
v_cache_1190_ = lean_ctor_get(v_s_1184_, 3);
v_errorMsg_1191_ = lean_ctor_get(v_s_1184_, 4);
v_recoveredErrors_1192_ = lean_ctor_get(v_s_1184_, 5);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_s_1184_);
if (v_isSharedCheck_1201_ == 0)
{
lean_object* v_unused_1202_; 
v_unused_1202_ = lean_ctor_get(v_s_1184_, 2);
lean_dec(v_unused_1202_);
v___x_1194_ = v_s_1184_;
v_isShared_1195_ = v_isSharedCheck_1201_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_recoveredErrors_1192_);
lean_inc(v_errorMsg_1191_);
lean_inc(v_cache_1190_);
lean_inc(v_lhsPrec_1189_);
lean_inc(v_stxStack_1188_);
lean_dec(v_s_1184_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1201_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_inputString_1196_; lean_object* v___x_1197_; lean_object* v___x_1199_; 
v_inputString_1196_ = lean_ctor_get(v_toInputContext_1187_, 0);
v___x_1197_ = lean_string_utf8_next_fast(v_inputString_1196_, v_pos_1186_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 2, v___x_1197_);
v___x_1199_ = v___x_1194_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_stxStack_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_lhsPrec_1189_);
lean_ctor_set(v_reuseFailAlloc_1200_, 2, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1200_, 3, v_cache_1190_);
lean_ctor_set(v_reuseFailAlloc_1200_, 4, v_errorMsg_1191_);
lean_ctor_set(v_reuseFailAlloc_1200_, 5, v_recoveredErrors_1192_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1203_, lean_object* v_c_1204_, lean_object* v_pos_1205_){
_start:
{
lean_object* v_res_1206_; 
v_res_1206_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1203_, v_c_1204_, v_pos_1205_);
lean_dec(v_pos_1205_);
lean_dec_ref(v_c_1204_);
return v_res_1206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1207_, lean_object* v_c_1208_, lean_object* v_pos_1209_, lean_object* v_h_1210_){
_start:
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1207_, v_c_1208_, v_pos_1209_);
return v___x_1211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1212_, lean_object* v_c_1213_, lean_object* v_pos_1214_, lean_object* v_h_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_Parser_ParserState_next_x27(v_s_1212_, v_c_1213_, v_pos_1214_, v_h_1215_);
lean_dec(v_pos_1214_);
lean_dec_ref(v_c_1213_);
return v_res_1216_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1217_, lean_object* v_x_1218_){
_start:
{
if (lean_obj_tag(v_x_1217_) == 0)
{
if (lean_obj_tag(v_x_1218_) == 0)
{
uint8_t v___x_1219_; 
v___x_1219_ = 1;
return v___x_1219_;
}
else
{
uint8_t v___x_1220_; 
v___x_1220_ = 0;
return v___x_1220_;
}
}
else
{
if (lean_obj_tag(v_x_1218_) == 0)
{
uint8_t v___x_1221_; 
v___x_1221_ = 0;
return v___x_1221_;
}
else
{
lean_object* v_val_1222_; lean_object* v_val_1223_; uint8_t v___x_1224_; 
v_val_1222_ = lean_ctor_get(v_x_1217_, 0);
v_val_1223_ = lean_ctor_get(v_x_1218_, 0);
v___x_1224_ = l_Lean_Parser_instBEqError_beq(v_val_1222_, v_val_1223_);
return v___x_1224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1225_, lean_object* v_x_1226_){
_start:
{
uint8_t v_res_1227_; lean_object* v_r_1228_; 
v_res_1227_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1225_, v_x_1226_);
lean_dec(v_x_1226_);
lean_dec(v_x_1225_);
v_r_1228_ = lean_box(v_res_1227_);
return v_r_1228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1229_, lean_object* v_k_1230_, lean_object* v_iniStackSz_1231_){
_start:
{
lean_object* v_stxStack_1232_; lean_object* v_lhsPrec_1233_; lean_object* v_pos_1234_; lean_object* v_cache_1235_; lean_object* v_errorMsg_1236_; lean_object* v_recoveredErrors_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1258_; 
v_stxStack_1232_ = lean_ctor_get(v_s_1229_, 0);
v_lhsPrec_1233_ = lean_ctor_get(v_s_1229_, 1);
v_pos_1234_ = lean_ctor_get(v_s_1229_, 2);
v_cache_1235_ = lean_ctor_get(v_s_1229_, 3);
v_errorMsg_1236_ = lean_ctor_get(v_s_1229_, 4);
v_recoveredErrors_1237_ = lean_ctor_get(v_s_1229_, 5);
v_isSharedCheck_1258_ = !lean_is_exclusive(v_s_1229_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1239_ = v_s_1229_;
v_isShared_1240_ = v_isSharedCheck_1258_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_recoveredErrors_1237_);
lean_inc(v_errorMsg_1236_);
lean_inc(v_cache_1235_);
lean_inc(v_pos_1234_);
lean_inc(v_lhsPrec_1233_);
lean_inc(v_stxStack_1232_);
lean_dec(v_s_1229_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1258_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1251_; uint8_t v___x_1252_; 
v___x_1251_ = lean_box(0);
v___x_1252_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1236_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; uint8_t v___x_1254_; 
v___x_1253_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1232_);
v___x_1254_ = lean_nat_dec_eq(v___x_1253_, v_iniStackSz_1231_);
lean_dec(v___x_1253_);
if (v___x_1254_ == 0)
{
goto v___jp_1241_;
}
else
{
lean_object* v___x_1255_; lean_object* v_stack_1256_; lean_object* v___x_1257_; 
lean_del_object(v___x_1239_);
lean_dec(v_k_1230_);
v___x_1255_ = lean_box(0);
v_stack_1256_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1232_, v___x_1255_);
v___x_1257_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1257_, 0, v_stack_1256_);
lean_ctor_set(v___x_1257_, 1, v_lhsPrec_1233_);
lean_ctor_set(v___x_1257_, 2, v_pos_1234_);
lean_ctor_set(v___x_1257_, 3, v_cache_1235_);
lean_ctor_set(v___x_1257_, 4, v_errorMsg_1236_);
lean_ctor_set(v___x_1257_, 5, v_recoveredErrors_1237_);
return v___x_1257_;
}
}
else
{
goto v___jp_1241_;
}
v___jp_1241_:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v_newNode_1245_; lean_object* v_stack_1246_; lean_object* v_stack_1247_; lean_object* v___x_1249_; 
v___x_1242_ = lean_box(2);
v___x_1243_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1232_);
v___x_1244_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1232_, v_iniStackSz_1231_, v___x_1243_);
lean_dec(v___x_1243_);
v_newNode_1245_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1245_, 0, v___x_1242_);
lean_ctor_set(v_newNode_1245_, 1, v_k_1230_);
lean_ctor_set(v_newNode_1245_, 2, v___x_1244_);
v_stack_1246_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1232_, v_iniStackSz_1231_);
v_stack_1247_ = l_Lean_Parser_SyntaxStack_push(v_stack_1246_, v_newNode_1245_);
if (v_isShared_1240_ == 0)
{
lean_ctor_set(v___x_1239_, 0, v_stack_1247_);
v___x_1249_ = v___x_1239_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_stack_1247_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v_lhsPrec_1233_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_pos_1234_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v_cache_1235_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v_errorMsg_1236_);
lean_ctor_set(v_reuseFailAlloc_1250_, 5, v_recoveredErrors_1237_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1259_, lean_object* v_k_1260_, lean_object* v_iniStackSz_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Parser_ParserState_mkNode(v_s_1259_, v_k_1260_, v_iniStackSz_1261_);
lean_dec(v_iniStackSz_1261_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1263_, lean_object* v_k_1264_, lean_object* v_iniStackSz_1265_){
_start:
{
lean_object* v_stxStack_1266_; lean_object* v_lhsPrec_1267_; lean_object* v_pos_1268_; lean_object* v_cache_1269_; lean_object* v_errorMsg_1270_; lean_object* v_recoveredErrors_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1286_; 
v_stxStack_1266_ = lean_ctor_get(v_s_1263_, 0);
v_lhsPrec_1267_ = lean_ctor_get(v_s_1263_, 1);
v_pos_1268_ = lean_ctor_get(v_s_1263_, 2);
v_cache_1269_ = lean_ctor_get(v_s_1263_, 3);
v_errorMsg_1270_ = lean_ctor_get(v_s_1263_, 4);
v_recoveredErrors_1271_ = lean_ctor_get(v_s_1263_, 5);
v_isSharedCheck_1286_ = !lean_is_exclusive(v_s_1263_);
if (v_isSharedCheck_1286_ == 0)
{
v___x_1273_ = v_s_1263_;
v_isShared_1274_ = v_isSharedCheck_1286_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_recoveredErrors_1271_);
lean_inc(v_errorMsg_1270_);
lean_inc(v_cache_1269_);
lean_inc(v_pos_1268_);
lean_inc(v_lhsPrec_1267_);
lean_inc(v_stxStack_1266_);
lean_dec(v_s_1263_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1286_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v_newNode_1280_; lean_object* v_stack_1281_; lean_object* v_stack_1282_; lean_object* v___x_1284_; 
v___x_1275_ = lean_box(2);
v___x_1276_ = lean_unsigned_to_nat(1u);
v___x_1277_ = lean_nat_sub(v_iniStackSz_1265_, v___x_1276_);
v___x_1278_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1266_);
v___x_1279_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1266_, v___x_1277_, v___x_1278_);
lean_dec(v___x_1278_);
v_newNode_1280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1280_, 0, v___x_1275_);
lean_ctor_set(v_newNode_1280_, 1, v_k_1264_);
lean_ctor_set(v_newNode_1280_, 2, v___x_1279_);
v_stack_1281_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1266_, v___x_1277_);
lean_dec(v___x_1277_);
v_stack_1282_ = l_Lean_Parser_SyntaxStack_push(v_stack_1281_, v_newNode_1280_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v_stack_1282_);
v___x_1284_ = v___x_1273_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v_stack_1282_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_lhsPrec_1267_);
lean_ctor_set(v_reuseFailAlloc_1285_, 2, v_pos_1268_);
lean_ctor_set(v_reuseFailAlloc_1285_, 3, v_cache_1269_);
lean_ctor_set(v_reuseFailAlloc_1285_, 4, v_errorMsg_1270_);
lean_ctor_set(v_reuseFailAlloc_1285_, 5, v_recoveredErrors_1271_);
v___x_1284_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
return v___x_1284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1287_, lean_object* v_k_1288_, lean_object* v_iniStackSz_1289_){
_start:
{
lean_object* v_res_1290_; 
v_res_1290_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1287_, v_k_1288_, v_iniStackSz_1289_);
lean_dec(v_iniStackSz_1289_);
return v_res_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1293_){
_start:
{
lean_object* v_errorMsg_1294_; 
v_errorMsg_1294_ = lean_ctor_get(v_s_1293_, 4);
if (lean_obj_tag(v_errorMsg_1294_) == 0)
{
lean_object* v_recoveredErrors_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
v_recoveredErrors_1295_ = lean_ctor_get(v_s_1293_, 5);
lean_inc_ref(v_recoveredErrors_1295_);
lean_dec_ref(v_s_1293_);
v___x_1296_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1297_ = l_Array_append___redArg(v_recoveredErrors_1295_, v___x_1296_);
return v___x_1297_;
}
else
{
lean_object* v_stxStack_1298_; lean_object* v_pos_1299_; lean_object* v_recoveredErrors_1300_; lean_object* v_val_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_inc_ref(v_errorMsg_1294_);
v_stxStack_1298_ = lean_ctor_get(v_s_1293_, 0);
lean_inc_ref(v_stxStack_1298_);
v_pos_1299_ = lean_ctor_get(v_s_1293_, 2);
lean_inc(v_pos_1299_);
v_recoveredErrors_1300_ = lean_ctor_get(v_s_1293_, 5);
lean_inc_ref(v_recoveredErrors_1300_);
lean_dec_ref(v_s_1293_);
v_val_1301_ = lean_ctor_get(v_errorMsg_1294_, 0);
lean_inc(v_val_1301_);
lean_dec_ref_known(v_errorMsg_1294_, 1);
v___x_1302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_stxStack_1298_);
lean_ctor_set(v___x_1302_, 1, v_val_1301_);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v_pos_1299_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = lean_unsigned_to_nat(1u);
v___x_1305_ = lean_mk_empty_array_with_capacity(v___x_1304_);
v___x_1306_ = lean_array_push(v___x_1305_, v___x_1303_);
v___x_1307_ = l_Array_append___redArg(v_recoveredErrors_1300_, v___x_1306_);
lean_dec_ref(v___x_1306_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1308_, lean_object* v_e_1309_){
_start:
{
lean_object* v_stxStack_1310_; lean_object* v_lhsPrec_1311_; lean_object* v_pos_1312_; lean_object* v_cache_1313_; lean_object* v_recoveredErrors_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1322_; 
v_stxStack_1310_ = lean_ctor_get(v_s_1308_, 0);
v_lhsPrec_1311_ = lean_ctor_get(v_s_1308_, 1);
v_pos_1312_ = lean_ctor_get(v_s_1308_, 2);
v_cache_1313_ = lean_ctor_get(v_s_1308_, 3);
v_recoveredErrors_1314_ = lean_ctor_get(v_s_1308_, 5);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_s_1308_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v_s_1308_, 4);
lean_dec(v_unused_1323_);
v___x_1316_ = v_s_1308_;
v_isShared_1317_ = v_isSharedCheck_1322_;
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
v_isShared_1317_ = v_isSharedCheck_1322_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
v___x_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1318_, 0, v_e_1309_);
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 4, v___x_1318_);
v___x_1320_ = v___x_1316_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_stxStack_1310_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_lhsPrec_1311_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_pos_1312_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_cache_1313_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v_recoveredErrors_1314_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1324_, lean_object* v_msg_1325_){
_start:
{
lean_object* v_stxStack_1326_; lean_object* v_lhsPrec_1327_; lean_object* v_pos_1328_; lean_object* v_cache_1329_; lean_object* v_recoveredErrors_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1344_; 
v_stxStack_1326_ = lean_ctor_get(v_s_1324_, 0);
v_lhsPrec_1327_ = lean_ctor_get(v_s_1324_, 1);
v_pos_1328_ = lean_ctor_get(v_s_1324_, 2);
v_cache_1329_ = lean_ctor_get(v_s_1324_, 3);
v_recoveredErrors_1330_ = lean_ctor_get(v_s_1324_, 5);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_s_1324_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v_s_1324_, 4);
lean_dec(v_unused_1345_);
v___x_1332_ = v_s_1324_;
v_isShared_1333_ = v_isSharedCheck_1344_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_recoveredErrors_1330_);
lean_inc(v_cache_1329_);
lean_inc(v_pos_1328_);
lean_inc(v_lhsPrec_1327_);
lean_inc(v_stxStack_1326_);
lean_dec(v_s_1324_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1344_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1341_; 
v___x_1334_ = lean_box(0);
v___x_1335_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1336_ = lean_box(0);
v___x_1337_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_msg_1325_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1334_);
lean_ctor_set(v___x_1338_, 1, v___x_1335_);
lean_ctor_set(v___x_1338_, 2, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 4, v___x_1339_);
v___x_1341_ = v___x_1332_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_stxStack_1326_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_lhsPrec_1327_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_pos_1328_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_cache_1329_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1343_, 5, v_recoveredErrors_1330_);
v___x_1341_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1341_, v___x_1334_);
return v___x_1342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1346_, lean_object* v_msg_1347_, lean_object* v_expected_1348_, uint8_t v_pushMissing_1349_){
_start:
{
lean_object* v_stxStack_1350_; lean_object* v_lhsPrec_1351_; lean_object* v_pos_1352_; lean_object* v_cache_1353_; lean_object* v_recoveredErrors_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1365_; 
v_stxStack_1350_ = lean_ctor_get(v_s_1346_, 0);
v_lhsPrec_1351_ = lean_ctor_get(v_s_1346_, 1);
v_pos_1352_ = lean_ctor_get(v_s_1346_, 2);
v_cache_1353_ = lean_ctor_get(v_s_1346_, 3);
v_recoveredErrors_1354_ = lean_ctor_get(v_s_1346_, 5);
v_isSharedCheck_1365_ = !lean_is_exclusive(v_s_1346_);
if (v_isSharedCheck_1365_ == 0)
{
lean_object* v_unused_1366_; 
v_unused_1366_ = lean_ctor_get(v_s_1346_, 4);
lean_dec(v_unused_1366_);
v___x_1356_ = v_s_1346_;
v_isShared_1357_ = v_isSharedCheck_1365_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_recoveredErrors_1354_);
lean_inc(v_cache_1353_);
lean_inc(v_pos_1352_);
lean_inc(v_lhsPrec_1351_);
lean_inc(v_stxStack_1350_);
lean_dec(v_s_1346_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1365_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v_s_1362_; 
v___x_1358_ = lean_box(0);
v___x_1359_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v_msg_1347_);
lean_ctor_set(v___x_1359_, 2, v_expected_1348_);
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1359_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set(v___x_1356_, 4, v___x_1360_);
v_s_1362_ = v___x_1356_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_stxStack_1350_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v_lhsPrec_1351_);
lean_ctor_set(v_reuseFailAlloc_1364_, 2, v_pos_1352_);
lean_ctor_set(v_reuseFailAlloc_1364_, 3, v_cache_1353_);
lean_ctor_set(v_reuseFailAlloc_1364_, 4, v___x_1360_);
lean_ctor_set(v_reuseFailAlloc_1364_, 5, v_recoveredErrors_1354_);
v_s_1362_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
if (v_pushMissing_1349_ == 0)
{
return v_s_1362_;
}
else
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1362_, v___x_1358_);
return v___x_1363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1367_, lean_object* v_msg_1368_, lean_object* v_expected_1369_, lean_object* v_pushMissing_1370_){
_start:
{
uint8_t v_pushMissing_boxed_1371_; lean_object* v_res_1372_; 
v_pushMissing_boxed_1371_ = lean_unbox(v_pushMissing_1370_);
v_res_1372_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1367_, v_msg_1368_, v_expected_1369_, v_pushMissing_boxed_1371_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1374_, lean_object* v_expected_1375_){
_start:
{
lean_object* v___x_1376_; uint8_t v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1377_ = 1;
v___x_1378_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1374_, v___x_1376_, v_expected_1375_, v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1379_, lean_object* v_ex_1380_, lean_object* v_pos_1381_, lean_object* v_initStackSz_x3f_1382_){
_start:
{
lean_object* v_s_1384_; lean_object* v_s_1403_; 
v_s_1403_ = l_Lean_Parser_ParserState_setPos(v_s_1379_, v_pos_1381_);
if (lean_obj_tag(v_initStackSz_x3f_1382_) == 1)
{
lean_object* v_val_1404_; lean_object* v_s_1405_; 
v_val_1404_ = lean_ctor_get(v_initStackSz_x3f_1382_, 0);
v_s_1405_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1403_, v_val_1404_);
v_s_1384_ = v_s_1405_;
goto v___jp_1383_;
}
else
{
v_s_1384_ = v_s_1403_;
goto v___jp_1383_;
}
v___jp_1383_:
{
lean_object* v_stxStack_1385_; lean_object* v_lhsPrec_1386_; lean_object* v_pos_1387_; lean_object* v_cache_1388_; lean_object* v_recoveredErrors_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1401_; 
v_stxStack_1385_ = lean_ctor_get(v_s_1384_, 0);
v_lhsPrec_1386_ = lean_ctor_get(v_s_1384_, 1);
v_pos_1387_ = lean_ctor_get(v_s_1384_, 2);
v_cache_1388_ = lean_ctor_get(v_s_1384_, 3);
v_recoveredErrors_1389_ = lean_ctor_get(v_s_1384_, 5);
v_isSharedCheck_1401_ = !lean_is_exclusive(v_s_1384_);
if (v_isSharedCheck_1401_ == 0)
{
lean_object* v_unused_1402_; 
v_unused_1402_ = lean_ctor_get(v_s_1384_, 4);
lean_dec(v_unused_1402_);
v___x_1391_ = v_s_1384_;
v_isShared_1392_ = v_isSharedCheck_1401_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_recoveredErrors_1389_);
lean_inc(v_cache_1388_);
lean_inc(v_pos_1387_);
lean_inc(v_lhsPrec_1386_);
lean_inc(v_stxStack_1385_);
lean_dec(v_s_1384_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1401_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_s_1398_; 
v___x_1393_ = lean_box(0);
v___x_1394_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1393_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
lean_ctor_set(v___x_1395_, 2, v_ex_1380_);
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set(v___x_1391_, 4, v___x_1396_);
v_s_1398_ = v___x_1391_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v_stxStack_1385_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v_lhsPrec_1386_);
lean_ctor_set(v_reuseFailAlloc_1400_, 2, v_pos_1387_);
lean_ctor_set(v_reuseFailAlloc_1400_, 3, v_cache_1388_);
lean_ctor_set(v_reuseFailAlloc_1400_, 4, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1400_, 5, v_recoveredErrors_1389_);
v_s_1398_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1398_, v___x_1393_);
return v___x_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1406_, lean_object* v_ex_1407_, lean_object* v_pos_1408_, lean_object* v_initStackSz_x3f_1409_){
_start:
{
lean_object* v_res_1410_; 
v_res_1410_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1406_, v_ex_1407_, v_pos_1408_, v_initStackSz_x3f_1409_);
lean_dec(v_initStackSz_x3f_1409_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1411_, lean_object* v_msg_1412_, lean_object* v_pos_1413_, lean_object* v_initStackSz_x3f_1414_){
_start:
{
lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; 
v___x_1415_ = lean_box(0);
v___x_1416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1416_, 0, v_msg_1412_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1411_, v___x_1416_, v_pos_1413_, v_initStackSz_x3f_1414_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1418_, lean_object* v_msg_1419_, lean_object* v_pos_1420_, lean_object* v_initStackSz_x3f_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1418_, v_msg_1419_, v_pos_1420_, v_initStackSz_x3f_1421_);
lean_dec(v_initStackSz_x3f_1421_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1423_){
_start:
{
lean_object* v___x_1424_; lean_object* v___x_1425_; 
v___x_1424_ = lean_unsigned_to_nat(0u);
v___x_1425_ = lean_panic_fn_borrowed(v___x_1424_, v_msg_1423_);
return v___x_1425_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1429_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1430_ = lean_unsigned_to_nat(14u);
v___x_1431_ = lean_unsigned_to_nat(22u);
v___x_1432_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1433_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1434_ = l_mkPanicMessageWithDecl(v___x_1433_, v___x_1432_, v___x_1431_, v___x_1430_, v___x_1429_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1435_, lean_object* v_ex_1436_, lean_object* v_iniPos_1437_){
_start:
{
lean_object* v_stxStack_1438_; lean_object* v_tk_1439_; lean_object* v___y_1441_; lean_object* v___x_1462_; uint8_t v___x_1463_; 
v_stxStack_1438_ = lean_ctor_get(v_s_1435_, 0);
v_tk_1439_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1438_);
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_dec_le(v___x_1462_, v_iniPos_1437_);
if (v___x_1463_ == 0)
{
lean_object* v___x_1464_; 
lean_dec(v_iniPos_1437_);
v___x_1464_ = l_Lean_Syntax_getPos_x3f(v_tk_1439_, v___x_1463_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v___x_1465_; lean_object* v___x_1466_; 
v___x_1465_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1466_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1465_);
v___y_1441_ = v___x_1466_;
goto v___jp_1440_;
}
else
{
lean_object* v_val_1467_; 
v_val_1467_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_val_1467_);
lean_dec_ref_known(v___x_1464_, 1);
v___y_1441_ = v_val_1467_;
goto v___jp_1440_;
}
}
else
{
v___y_1441_ = v_iniPos_1437_;
goto v___jp_1440_;
}
v___jp_1440_:
{
lean_object* v_s_1442_; lean_object* v_stxStack_1443_; lean_object* v_lhsPrec_1444_; lean_object* v_pos_1445_; lean_object* v_cache_1446_; lean_object* v_recoveredErrors_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1460_; 
v_s_1442_ = l_Lean_Parser_ParserState_setPos(v_s_1435_, v___y_1441_);
v_stxStack_1443_ = lean_ctor_get(v_s_1442_, 0);
v_lhsPrec_1444_ = lean_ctor_get(v_s_1442_, 1);
v_pos_1445_ = lean_ctor_get(v_s_1442_, 2);
v_cache_1446_ = lean_ctor_get(v_s_1442_, 3);
v_recoveredErrors_1447_ = lean_ctor_get(v_s_1442_, 5);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_s_1442_);
if (v_isSharedCheck_1460_ == 0)
{
lean_object* v_unused_1461_; 
v_unused_1461_ = lean_ctor_get(v_s_1442_, 4);
lean_dec(v_unused_1461_);
v___x_1449_ = v_s_1442_;
v_isShared_1450_ = v_isSharedCheck_1460_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_recoveredErrors_1447_);
lean_inc(v_cache_1446_);
lean_inc(v_pos_1445_);
lean_inc(v_lhsPrec_1444_);
lean_inc(v_stxStack_1443_);
lean_dec(v_s_1442_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1460_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v_s_1455_; 
v___x_1451_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1452_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1452_, 0, v_tk_1439_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
lean_ctor_set(v___x_1452_, 2, v_ex_1436_);
v___x_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
if (v_isShared_1450_ == 0)
{
lean_ctor_set(v___x_1449_, 4, v___x_1453_);
v_s_1455_ = v___x_1449_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1459_; 
v_reuseFailAlloc_1459_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1459_, 0, v_stxStack_1443_);
lean_ctor_set(v_reuseFailAlloc_1459_, 1, v_lhsPrec_1444_);
lean_ctor_set(v_reuseFailAlloc_1459_, 2, v_pos_1445_);
lean_ctor_set(v_reuseFailAlloc_1459_, 3, v_cache_1446_);
lean_ctor_set(v_reuseFailAlloc_1459_, 4, v___x_1453_);
lean_ctor_set(v_reuseFailAlloc_1459_, 5, v_recoveredErrors_1447_);
v_s_1455_ = v_reuseFailAlloc_1459_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = l_Lean_Parser_ParserState_popSyntax(v_s_1455_);
v___x_1457_ = lean_box(0);
v___x_1458_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1456_, v___x_1457_);
return v___x_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1468_, lean_object* v_msg_1469_, lean_object* v_iniPos_1470_){
_start:
{
lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1471_ = lean_box(0);
v___x_1472_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1472_, 0, v_msg_1469_);
lean_ctor_set(v___x_1472_, 1, v___x_1471_);
v___x_1473_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1468_, v___x_1472_, v_iniPos_1470_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1474_, lean_object* v_msg_1475_, lean_object* v_pos_1476_){
_start:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; uint8_t v___x_1479_; lean_object* v___x_1480_; 
v___x_1477_ = l_Lean_Parser_ParserState_setPos(v_s_1474_, v_pos_1476_);
v___x_1478_ = lean_box(0);
v___x_1479_ = 1;
v___x_1480_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1477_, v_msg_1475_, v___x_1478_, v___x_1479_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1482_, lean_object* v_as_1483_, size_t v_sz_1484_, size_t v_i_1485_, lean_object* v_b_1486_){
_start:
{
uint8_t v___x_1487_; 
v___x_1487_ = lean_usize_dec_lt(v_i_1485_, v_sz_1484_);
if (v___x_1487_ == 0)
{
lean_dec_ref(v_ctx_1482_);
return v_b_1486_;
}
else
{
lean_object* v_a_1488_; lean_object* v_snd_1489_; lean_object* v_fst_1490_; lean_object* v_snd_1491_; lean_object* v_errStr_1493_; lean_object* v_errStr_1504_; uint8_t v___x_1505_; 
v_a_1488_ = lean_array_uget_borrowed(v_as_1483_, v_i_1485_);
v_snd_1489_ = lean_ctor_get(v_a_1488_, 1);
v_fst_1490_ = lean_ctor_get(v_a_1488_, 0);
v_snd_1491_ = lean_ctor_get(v_snd_1489_, 1);
v_errStr_1504_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1505_ = lean_string_dec_eq(v_b_1486_, v_errStr_1504_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1507_ = lean_string_append(v_b_1486_, v___x_1506_);
v_errStr_1493_ = v___x_1507_;
goto v___jp_1492_;
}
else
{
v_errStr_1493_ = v_b_1486_;
goto v___jp_1492_;
}
v___jp_1492_:
{
lean_object* v_fileName_1494_; lean_object* v_fileMap_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; size_t v___x_1501_; size_t v___x_1502_; 
v_fileName_1494_ = lean_ctor_get(v_ctx_1482_, 1);
v_fileMap_1495_ = lean_ctor_get(v_ctx_1482_, 2);
lean_inc_ref(v_fileMap_1495_);
v___x_1496_ = l_Lean_FileMap_toPosition(v_fileMap_1495_, v_fst_1490_);
lean_inc(v_snd_1491_);
v___x_1497_ = l_Lean_Parser_Error_toString(v_snd_1491_);
v___x_1498_ = lean_box(0);
lean_inc_ref(v_fileName_1494_);
v___x_1499_ = l_Lean_mkErrorStringWithPos(v_fileName_1494_, v___x_1496_, v___x_1497_, v___x_1498_, v___x_1498_, v___x_1498_);
lean_dec_ref(v___x_1497_);
v___x_1500_ = lean_string_append(v_errStr_1493_, v___x_1499_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = ((size_t)1ULL);
v___x_1502_ = lean_usize_add(v_i_1485_, v___x_1501_);
v_i_1485_ = v___x_1502_;
v_b_1486_ = v___x_1500_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1508_, lean_object* v_as_1509_, lean_object* v_sz_1510_, lean_object* v_i_1511_, lean_object* v_b_1512_){
_start:
{
size_t v_sz_boxed_1513_; size_t v_i_boxed_1514_; lean_object* v_res_1515_; 
v_sz_boxed_1513_ = lean_unbox_usize(v_sz_1510_);
lean_dec(v_sz_1510_);
v_i_boxed_1514_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_res_1515_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1508_, v_as_1509_, v_sz_boxed_1513_, v_i_boxed_1514_, v_b_1512_);
lean_dec_ref(v_as_1509_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1516_, lean_object* v_s_1517_){
_start:
{
lean_object* v_errStr_1518_; lean_object* v___x_1519_; size_t v_sz_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v_errStr_1518_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1519_ = l_Lean_Parser_ParserState_allErrors(v_s_1517_);
v_sz_1520_ = lean_array_size(v___x_1519_);
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1516_, v___x_1519_, v_sz_1520_, v___x_1521_, v_errStr_1518_);
lean_dec_ref(v___x_1519_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1523_, lean_object* v_s_1524_){
_start:
{
lean_inc_ref(v_s_1524_);
return v_s_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1525_, lean_object* v_s_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1525_, v_s_1526_);
lean_dec_ref(v_s_1526_);
lean_dec_ref(v_x_1525_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx(lean_object* v_x_1530_){
_start:
{
switch(lean_obj_tag(v_x_1530_))
{
case 0:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_unsigned_to_nat(0u);
return v___x_1531_;
}
case 1:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_unsigned_to_nat(1u);
return v___x_1532_;
}
case 2:
{
lean_object* v___x_1533_; 
v___x_1533_ = lean_unsigned_to_nat(2u);
return v___x_1533_;
}
default: 
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_unsigned_to_nat(3u);
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___boxed(lean_object* v_x_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_Parser_FirstTokens_ctorIdx(v_x_1535_);
lean_dec(v_x_1535_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1537_, lean_object* v_k_1538_){
_start:
{
switch(lean_obj_tag(v_t_1537_))
{
case 2:
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_ctor_get(v_t_1537_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v_t_1537_, 1);
v___x_1540_ = lean_apply_1(v_k_1538_, v_a_1539_);
return v___x_1540_;
}
case 3:
{
lean_object* v_a_1541_; lean_object* v___x_1542_; 
v_a_1541_ = lean_ctor_get(v_t_1537_, 0);
lean_inc(v_a_1541_);
lean_dec_ref_known(v_t_1537_, 1);
v___x_1542_ = lean_apply_1(v_k_1538_, v_a_1541_);
return v___x_1542_;
}
default: 
{
lean_dec(v_t_1537_);
return v_k_1538_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1543_, lean_object* v_ctorIdx_1544_, lean_object* v_t_1545_, lean_object* v_h_1546_, lean_object* v_k_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1545_, v_k_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1549_, lean_object* v_ctorIdx_1550_, lean_object* v_t_1551_, lean_object* v_h_1552_, lean_object* v_k_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1549_, v_ctorIdx_1550_, v_t_1551_, v_h_1552_, v_k_1553_);
lean_dec(v_ctorIdx_1550_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1555_, lean_object* v_epsilon_1556_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1555_, v_epsilon_1556_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1558_, lean_object* v_t_1559_, lean_object* v_h_1560_, lean_object* v_epsilon_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1559_, v_epsilon_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1563_, lean_object* v_unknown_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1563_, v_unknown_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1566_, lean_object* v_t_1567_, lean_object* v_h_1568_, lean_object* v_unknown_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1567_, v_unknown_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1571_, lean_object* v_tokens_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1571_, v_tokens_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_tokens_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1575_, v_tokens_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1579_, lean_object* v_optTokens_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1579_, v_optTokens_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1582_, lean_object* v_t_1583_, lean_object* v_h_1584_, lean_object* v_optTokens_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1583_, v_optTokens_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_box(0);
return v___x_1587_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_box(0);
return v___x_1588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1589_, lean_object* v_x_1590_){
_start:
{
switch(lean_obj_tag(v_x_1589_))
{
case 0:
{
return v_x_1590_;
}
case 3:
{
switch(lean_obj_tag(v_x_1590_))
{
case 3:
{
lean_object* v_a_1591_; lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1600_; 
v_a_1591_ = lean_ctor_get(v_x_1589_, 0);
lean_inc(v_a_1591_);
lean_dec_ref_known(v_x_1589_, 1);
v_a_1592_ = lean_ctor_get(v_x_1590_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_x_1590_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1594_ = v_x_1590_;
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v_x_1590_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1596_ = l_List_appendTR___redArg(v_a_1591_, v_a_1592_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 0, v___x_1596_);
v___x_1598_ = v___x_1594_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
case 2:
{
lean_object* v_a_1601_; lean_object* v_a_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1610_; 
v_a_1601_ = lean_ctor_get(v_x_1589_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v_x_1589_, 1);
v_a_1602_ = lean_ctor_get(v_x_1590_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_x_1590_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1604_ = v_x_1590_;
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_a_1602_);
lean_dec(v_x_1590_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1610_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1606_; lean_object* v___x_1608_; 
v___x_1606_ = l_List_appendTR___redArg(v_a_1601_, v_a_1602_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1606_);
v___x_1608_ = v___x_1604_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1606_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
case 1:
{
lean_dec_ref_known(v_x_1589_, 1);
return v_x_1590_;
}
default: 
{
lean_dec(v_x_1590_);
return v_x_1589_;
}
}
}
default: 
{
lean_dec(v_x_1590_);
return v_x_1589_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1611_){
_start:
{
if (lean_obj_tag(v_x_1611_) == 2)
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
v_a_1612_ = lean_ctor_get(v_x_1611_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_x_1611_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v_x_1611_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v_x_1611_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
lean_ctor_set_tag(v___x_1614_, 3);
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
else
{
return v_x_1611_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1620_, lean_object* v_x_1621_){
_start:
{
lean_object* v_s_u2081_1623_; lean_object* v_s_u2082_1624_; 
switch(lean_obj_tag(v_x_1620_))
{
case 0:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1621_);
return v___x_1627_;
}
case 2:
{
switch(lean_obj_tag(v_x_1621_))
{
case 0:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1620_);
return v___x_1628_;
}
case 2:
{
lean_object* v_a_1629_; lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1638_; 
v_a_1629_ = lean_ctor_get(v_x_1620_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v_x_1620_, 1);
v_a_1630_ = lean_ctor_get(v_x_1621_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v_x_1621_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1632_ = v_x_1621_;
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v_x_1621_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1638_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1634_ = l_List_appendTR___redArg(v_a_1629_, v_a_1630_);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v___x_1634_);
v___x_1636_ = v___x_1632_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
case 3:
{
lean_object* v_a_1639_; lean_object* v_a_1640_; 
v_a_1639_ = lean_ctor_get(v_x_1620_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v_x_1620_, 1);
v_a_1640_ = lean_ctor_get(v_x_1621_, 0);
lean_inc(v_a_1640_);
lean_dec_ref_known(v_x_1621_, 1);
v_s_u2081_1623_ = v_a_1639_;
v_s_u2082_1624_ = v_a_1640_;
goto v___jp_1622_;
}
default: 
{
lean_object* v___x_1641_; 
lean_dec_ref_known(v_x_1620_, 1);
lean_dec(v_x_1621_);
v___x_1641_ = lean_box(1);
return v___x_1641_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1621_))
{
case 0:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1620_);
return v___x_1642_;
}
case 3:
{
lean_object* v_a_1643_; lean_object* v_a_1644_; 
v_a_1643_ = lean_ctor_get(v_x_1620_, 0);
lean_inc(v_a_1643_);
lean_dec_ref_known(v_x_1620_, 1);
v_a_1644_ = lean_ctor_get(v_x_1621_, 0);
lean_inc(v_a_1644_);
lean_dec_ref_known(v_x_1621_, 1);
v_s_u2081_1623_ = v_a_1643_;
v_s_u2082_1624_ = v_a_1644_;
goto v___jp_1622_;
}
case 2:
{
lean_object* v_a_1645_; lean_object* v_a_1646_; 
v_a_1645_ = lean_ctor_get(v_x_1620_, 0);
lean_inc(v_a_1645_);
lean_dec_ref_known(v_x_1620_, 1);
v_a_1646_ = lean_ctor_get(v_x_1621_, 0);
lean_inc(v_a_1646_);
lean_dec_ref_known(v_x_1621_, 1);
v_s_u2081_1623_ = v_a_1645_;
v_s_u2082_1624_ = v_a_1646_;
goto v___jp_1622_;
}
default: 
{
lean_object* v___x_1647_; 
lean_dec_ref_known(v_x_1620_, 1);
lean_dec(v_x_1621_);
v___x_1647_ = lean_box(1);
return v___x_1647_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1621_) == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1620_);
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; 
lean_dec(v_x_1621_);
lean_dec(v_x_1620_);
v___x_1649_ = lean_box(1);
return v___x_1649_;
}
}
}
v___jp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = l_List_appendTR___redArg(v_s_u2081_1623_, v_s_u2082_1624_);
v___x_1626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
return v___x_1626_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
if (lean_obj_tag(v_x_1651_) == 0)
{
return v_x_1650_;
}
else
{
lean_object* v_head_1652_; lean_object* v_tail_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v_head_1652_ = lean_ctor_get(v_x_1651_, 0);
v_tail_1653_ = lean_ctor_get(v_x_1651_, 1);
v___x_1654_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1655_ = lean_string_append(v_x_1650_, v___x_1654_);
v___x_1656_ = lean_string_append(v___x_1655_, v_head_1652_);
v_x_1650_ = v___x_1656_;
v_x_1651_ = v_tail_1653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1658_, v_x_1659_);
lean_dec(v_x_1659_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1664_){
_start:
{
if (lean_obj_tag(v_x_1664_) == 0)
{
lean_object* v___x_1665_; 
v___x_1665_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1665_;
}
else
{
lean_object* v_tail_1666_; 
v_tail_1666_ = lean_ctor_get(v_x_1664_, 1);
if (lean_obj_tag(v_tail_1666_) == 0)
{
lean_object* v_head_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v_head_1667_ = lean_ctor_get(v_x_1664_, 0);
v___x_1668_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1669_ = lean_string_append(v___x_1668_, v_head_1667_);
v___x_1670_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1671_ = lean_string_append(v___x_1669_, v___x_1670_);
return v___x_1671_;
}
else
{
lean_object* v_head_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint32_t v___x_1676_; lean_object* v___x_1677_; 
v_head_1672_ = lean_ctor_get(v_x_1664_, 0);
v___x_1673_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1674_ = lean_string_append(v___x_1673_, v_head_1672_);
v___x_1675_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1674_, v_tail_1666_);
v___x_1676_ = 93;
v___x_1677_ = lean_string_push(v___x_1675_, v___x_1676_);
return v___x_1677_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1678_);
lean_dec(v_x_1678_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1683_){
_start:
{
switch(lean_obj_tag(v_x_1683_))
{
case 0:
{
lean_object* v___x_1684_; 
v___x_1684_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1684_;
}
case 1:
{
lean_object* v___x_1685_; 
v___x_1685_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1685_;
}
case 2:
{
lean_object* v_a_1686_; lean_object* v___x_1687_; 
v_a_1686_ = lean_ctor_get(v_x_1683_, 0);
v___x_1687_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1686_);
return v___x_1687_;
}
default: 
{
lean_object* v_a_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_a_1688_ = lean_ctor_get(v_x_1683_, 0);
v___x_1689_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1690_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1688_);
v___x_1691_ = lean_string_append(v___x_1689_, v___x_1690_);
lean_dec_ref(v___x_1690_);
return v___x_1691_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Lean_Parser_FirstTokens_toStr(v_x_1692_);
lean_dec(v_x_1692_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v___y_1696_){
_start:
{
lean_inc(v___y_1696_);
return v___y_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v___y_1697_){
_start:
{
lean_object* v_res_1698_; 
v_res_1698_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_1697_);
lean_dec(v___y_1697_);
return v_res_1698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v___y_1699_){
_start:
{
lean_inc_ref(v___y_1699_);
return v___y_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_1700_);
lean_dec_ref(v___y_1700_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1715_, lean_object* v_p_1716_){
_start:
{
lean_object* v_info_1717_; lean_object* v_fn_1718_; lean_object* v___x_1720_; uint8_t v_isShared_1721_; uint8_t v_isSharedCheck_1726_; 
v_info_1717_ = lean_ctor_get(v_p_1716_, 0);
v_fn_1718_ = lean_ctor_get(v_p_1716_, 1);
v_isSharedCheck_1726_ = !lean_is_exclusive(v_p_1716_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1720_ = v_p_1716_;
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
else
{
lean_inc(v_fn_1718_);
lean_inc(v_info_1717_);
lean_dec(v_p_1716_);
v___x_1720_ = lean_box(0);
v_isShared_1721_ = v_isSharedCheck_1726_;
goto v_resetjp_1719_;
}
v_resetjp_1719_:
{
lean_object* v___x_1722_; lean_object* v___x_1724_; 
v___x_1722_ = lean_apply_1(v_f_1715_, v_fn_1718_);
if (v_isShared_1721_ == 0)
{
lean_ctor_set(v___x_1720_, 1, v___x_1722_);
v___x_1724_ = v___x_1720_;
goto v_reusejp_1723_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v_info_1717_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v___x_1722_);
v___x_1724_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1723_;
}
v_reusejp_1723_:
{
return v___x_1724_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1727_, lean_object* v_p_1728_, lean_object* v_c_1729_, lean_object* v_s_1730_){
_start:
{
lean_object* v_toInputContext_1731_; lean_object* v_toParserModuleContext_1732_; lean_object* v_toCacheableParserContext_1733_; lean_object* v_tokens_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1743_; 
v_toInputContext_1731_ = lean_ctor_get(v_c_1729_, 0);
v_toParserModuleContext_1732_ = lean_ctor_get(v_c_1729_, 1);
v_toCacheableParserContext_1733_ = lean_ctor_get(v_c_1729_, 2);
v_tokens_1734_ = lean_ctor_get(v_c_1729_, 3);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_c_1729_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1736_ = v_c_1729_;
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_tokens_1734_);
lean_inc(v_toCacheableParserContext_1733_);
lean_inc(v_toParserModuleContext_1732_);
lean_inc(v_toInputContext_1731_);
lean_dec(v_c_1729_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1743_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = lean_apply_1(v_f_1727_, v_toCacheableParserContext_1733_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 2, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_toInputContext_1731_);
lean_ctor_set(v_reuseFailAlloc_1742_, 1, v_toParserModuleContext_1732_);
lean_ctor_set(v_reuseFailAlloc_1742_, 2, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1742_, 3, v_tokens_1734_);
v___x_1740_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1741_; 
v___x_1741_ = lean_apply_2(v_p_1728_, v___x_1740_, v_s_1730_);
return v___x_1741_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1744_, lean_object* v_p_1745_){
_start:
{
lean_object* v_info_1746_; lean_object* v_fn_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1755_; 
v_info_1746_ = lean_ctor_get(v_p_1745_, 0);
v_fn_1747_ = lean_ctor_get(v_p_1745_, 1);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_p_1745_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1749_ = v_p_1745_;
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_fn_1747_);
lean_inc(v_info_1746_);
lean_dec(v_p_1745_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1755_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1751_; lean_object* v___x_1753_; 
v___x_1751_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1751_, 0, v_f_1744_);
lean_closure_set(v___x_1751_, 1, v_fn_1747_);
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 1, v___x_1751_);
v___x_1753_ = v___x_1749_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_info_1746_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v___x_1751_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1756_, lean_object* v_p_1757_, lean_object* v_c_1758_, lean_object* v_s_1759_){
_start:
{
lean_object* v_stxStack_1760_; lean_object* v_lhsPrec_1761_; lean_object* v_pos_1762_; lean_object* v_cache_1763_; lean_object* v_errorMsg_1764_; lean_object* v_recoveredErrors_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1804_; 
v_stxStack_1760_ = lean_ctor_get(v_s_1759_, 0);
v_lhsPrec_1761_ = lean_ctor_get(v_s_1759_, 1);
v_pos_1762_ = lean_ctor_get(v_s_1759_, 2);
v_cache_1763_ = lean_ctor_get(v_s_1759_, 3);
v_errorMsg_1764_ = lean_ctor_get(v_s_1759_, 4);
v_recoveredErrors_1765_ = lean_ctor_get(v_s_1759_, 5);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_s_1759_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1767_ = v_s_1759_;
v_isShared_1768_ = v_isSharedCheck_1804_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_recoveredErrors_1765_);
lean_inc(v_errorMsg_1764_);
lean_inc(v_cache_1763_);
lean_inc(v_pos_1762_);
lean_inc(v_lhsPrec_1761_);
lean_inc(v_stxStack_1760_);
lean_dec(v_s_1759_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1804_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v_raw_1769_; lean_object* v_drop_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1803_; 
v_raw_1769_ = lean_ctor_get(v_stxStack_1760_, 0);
v_drop_1770_ = lean_ctor_get(v_stxStack_1760_, 1);
v_isSharedCheck_1803_ = !lean_is_exclusive(v_stxStack_1760_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1772_ = v_stxStack_1760_;
v_isShared_1773_ = v_isSharedCheck_1803_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_drop_1770_);
lean_inc(v_raw_1769_);
lean_dec(v_stxStack_1760_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1803_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v_drop_1756_);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_raw_1769_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_drop_1756_);
v___x_1775_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1775_);
v___x_1777_ = v___x_1767_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_lhsPrec_1761_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_pos_1762_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_cache_1763_);
lean_ctor_set(v_reuseFailAlloc_1801_, 4, v_errorMsg_1764_);
lean_ctor_set(v_reuseFailAlloc_1801_, 5, v_recoveredErrors_1765_);
v___x_1777_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
lean_object* v_s_1778_; lean_object* v_stxStack_1779_; lean_object* v_lhsPrec_1780_; lean_object* v_pos_1781_; lean_object* v_cache_1782_; lean_object* v_errorMsg_1783_; lean_object* v_recoveredErrors_1784_; lean_object* v___x_1786_; uint8_t v_isShared_1787_; uint8_t v_isSharedCheck_1800_; 
v_s_1778_ = lean_apply_2(v_p_1757_, v_c_1758_, v___x_1777_);
v_stxStack_1779_ = lean_ctor_get(v_s_1778_, 0);
v_lhsPrec_1780_ = lean_ctor_get(v_s_1778_, 1);
v_pos_1781_ = lean_ctor_get(v_s_1778_, 2);
v_cache_1782_ = lean_ctor_get(v_s_1778_, 3);
v_errorMsg_1783_ = lean_ctor_get(v_s_1778_, 4);
v_recoveredErrors_1784_ = lean_ctor_get(v_s_1778_, 5);
v_isSharedCheck_1800_ = !lean_is_exclusive(v_s_1778_);
if (v_isSharedCheck_1800_ == 0)
{
v___x_1786_ = v_s_1778_;
v_isShared_1787_ = v_isSharedCheck_1800_;
goto v_resetjp_1785_;
}
else
{
lean_inc(v_recoveredErrors_1784_);
lean_inc(v_errorMsg_1783_);
lean_inc(v_cache_1782_);
lean_inc(v_pos_1781_);
lean_inc(v_lhsPrec_1780_);
lean_inc(v_stxStack_1779_);
lean_dec(v_s_1778_);
v___x_1786_ = lean_box(0);
v_isShared_1787_ = v_isSharedCheck_1800_;
goto v_resetjp_1785_;
}
v_resetjp_1785_:
{
lean_object* v_raw_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1798_; 
v_raw_1788_ = lean_ctor_get(v_stxStack_1779_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v_stxStack_1779_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; 
v_unused_1799_ = lean_ctor_get(v_stxStack_1779_, 1);
lean_dec(v_unused_1799_);
v___x_1790_ = v_stxStack_1779_;
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_raw_1788_);
lean_dec(v_stxStack_1779_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1798_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 1, v_drop_1770_);
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_raw_1788_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_drop_1770_);
v___x_1793_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
lean_object* v___x_1795_; 
if (v_isShared_1787_ == 0)
{
lean_ctor_set(v___x_1786_, 0, v___x_1793_);
v___x_1795_ = v___x_1786_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_lhsPrec_1780_);
lean_ctor_set(v_reuseFailAlloc_1796_, 2, v_pos_1781_);
lean_ctor_set(v_reuseFailAlloc_1796_, 3, v_cache_1782_);
lean_ctor_set(v_reuseFailAlloc_1796_, 4, v_errorMsg_1783_);
lean_ctor_set(v_reuseFailAlloc_1796_, 5, v_recoveredErrors_1784_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1805_, lean_object* v_c_1806_, lean_object* v_s_1807_){
_start:
{
lean_object* v_cache_1808_; lean_object* v_stxStack_1809_; lean_object* v_lhsPrec_1810_; lean_object* v_pos_1811_; lean_object* v_errorMsg_1812_; lean_object* v_recoveredErrors_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1853_; 
v_cache_1808_ = lean_ctor_get(v_s_1807_, 3);
v_stxStack_1809_ = lean_ctor_get(v_s_1807_, 0);
v_lhsPrec_1810_ = lean_ctor_get(v_s_1807_, 1);
v_pos_1811_ = lean_ctor_get(v_s_1807_, 2);
v_errorMsg_1812_ = lean_ctor_get(v_s_1807_, 4);
v_recoveredErrors_1813_ = lean_ctor_get(v_s_1807_, 5);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_s_1807_);
if (v_isSharedCheck_1853_ == 0)
{
v___x_1815_ = v_s_1807_;
v_isShared_1816_ = v_isSharedCheck_1853_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_recoveredErrors_1813_);
lean_inc(v_errorMsg_1812_);
lean_inc(v_cache_1808_);
lean_inc(v_pos_1811_);
lean_inc(v_lhsPrec_1810_);
lean_inc(v_stxStack_1809_);
lean_dec(v_s_1807_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1853_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_tokenCache_1817_; lean_object* v_parserCache_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1852_; 
v_tokenCache_1817_ = lean_ctor_get(v_cache_1808_, 0);
v_parserCache_1818_ = lean_ctor_get(v_cache_1808_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_cache_1808_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1820_ = v_cache_1808_;
v_isShared_1821_ = v_isSharedCheck_1852_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_parserCache_1818_);
lean_inc(v_tokenCache_1817_);
lean_dec(v_cache_1808_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1852_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 1, v___x_1822_);
v___x_1824_ = v___x_1820_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_tokenCache_1817_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 3, v___x_1824_);
v___x_1826_ = v___x_1815_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v_stxStack_1809_);
lean_ctor_set(v_reuseFailAlloc_1850_, 1, v_lhsPrec_1810_);
lean_ctor_set(v_reuseFailAlloc_1850_, 2, v_pos_1811_);
lean_ctor_set(v_reuseFailAlloc_1850_, 3, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1850_, 4, v_errorMsg_1812_);
lean_ctor_set(v_reuseFailAlloc_1850_, 5, v_recoveredErrors_1813_);
v___x_1826_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v_s_x27_1827_; lean_object* v_cache_1828_; lean_object* v_stxStack_1829_; lean_object* v_lhsPrec_1830_; lean_object* v_pos_1831_; lean_object* v_errorMsg_1832_; lean_object* v_recoveredErrors_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1849_; 
v_s_x27_1827_ = lean_apply_2(v_p_1805_, v_c_1806_, v___x_1826_);
v_cache_1828_ = lean_ctor_get(v_s_x27_1827_, 3);
v_stxStack_1829_ = lean_ctor_get(v_s_x27_1827_, 0);
v_lhsPrec_1830_ = lean_ctor_get(v_s_x27_1827_, 1);
v_pos_1831_ = lean_ctor_get(v_s_x27_1827_, 2);
v_errorMsg_1832_ = lean_ctor_get(v_s_x27_1827_, 4);
v_recoveredErrors_1833_ = lean_ctor_get(v_s_x27_1827_, 5);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_s_x27_1827_);
if (v_isSharedCheck_1849_ == 0)
{
v___x_1835_ = v_s_x27_1827_;
v_isShared_1836_ = v_isSharedCheck_1849_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_recoveredErrors_1833_);
lean_inc(v_errorMsg_1832_);
lean_inc(v_cache_1828_);
lean_inc(v_pos_1831_);
lean_inc(v_lhsPrec_1830_);
lean_inc(v_stxStack_1829_);
lean_dec(v_s_x27_1827_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1849_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v_tokenCache_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1847_; 
v_tokenCache_1837_ = lean_ctor_get(v_cache_1828_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v_cache_1828_);
if (v_isSharedCheck_1847_ == 0)
{
lean_object* v_unused_1848_; 
v_unused_1848_ = lean_ctor_get(v_cache_1828_, 1);
lean_dec(v_unused_1848_);
v___x_1839_ = v_cache_1828_;
v_isShared_1840_ = v_isSharedCheck_1847_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_tokenCache_1837_);
lean_dec(v_cache_1828_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1847_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 1, v_parserCache_1818_);
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_tokenCache_1837_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v_parserCache_1818_);
v___x_1842_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
lean_object* v___x_1844_; 
if (v_isShared_1836_ == 0)
{
lean_ctor_set(v___x_1835_, 3, v___x_1842_);
v___x_1844_ = v___x_1835_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_stxStack_1829_);
lean_ctor_set(v_reuseFailAlloc_1845_, 1, v_lhsPrec_1830_);
lean_ctor_set(v_reuseFailAlloc_1845_, 2, v_pos_1831_);
lean_ctor_set(v_reuseFailAlloc_1845_, 3, v___x_1842_);
lean_ctor_set(v_reuseFailAlloc_1845_, 4, v_errorMsg_1832_);
lean_ctor_set(v_reuseFailAlloc_1845_, 5, v_recoveredErrors_1833_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v___f_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___f_1857_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1857_, 0, v_p_1854_);
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1858_, v___f_1857_, v_a_1855_, v_a_1856_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1860_){
_start:
{
lean_object* v_info_1861_; lean_object* v_fn_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1870_; 
v_info_1861_ = lean_ctor_get(v_p_1860_, 0);
v_fn_1862_ = lean_ctor_get(v_p_1860_, 1);
v_isSharedCheck_1870_ = !lean_is_exclusive(v_p_1860_);
if (v_isSharedCheck_1870_ == 0)
{
v___x_1864_ = v_p_1860_;
v_isShared_1865_ = v_isSharedCheck_1870_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_fn_1862_);
lean_inc(v_info_1861_);
lean_dec(v_p_1860_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1870_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
lean_object* v___x_1866_; lean_object* v___x_1868_; 
v___x_1866_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1866_, 0, v_fn_1862_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 1, v___x_1866_);
v___x_1868_ = v___x_1864_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_info_1861_);
lean_ctor_set(v_reuseFailAlloc_1869_, 1, v___x_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1871_, lean_object* v_p_1872_, lean_object* v_c_1873_, lean_object* v_s_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_apply_1(v_f_1871_, v_c_1873_);
v___x_1876_ = lean_apply_2(v_p_1872_, v___x_1875_, v_s_1874_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1877_, lean_object* v_p_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___f_1881_; lean_object* v___x_1882_; 
v___f_1881_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1881_, 0, v_f_1877_);
lean_closure_set(v___f_1881_, 1, v_p_1878_);
v___x_1882_ = l_Lean_Parser_withResetCacheFn(v___f_1881_, v_a_1879_, v_a_1880_);
return v___x_1882_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1883_, lean_object* v_x_1884_){
_start:
{
if (lean_obj_tag(v_x_1884_) == 0)
{
uint8_t v___x_1885_; 
v___x_1885_ = 0;
return v___x_1885_;
}
else
{
lean_object* v_key_1886_; lean_object* v_tail_1887_; uint8_t v___x_1888_; 
v_key_1886_ = lean_ctor_get(v_x_1884_, 0);
v_tail_1887_ = lean_ctor_get(v_x_1884_, 2);
v___x_1888_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1886_, v_a_1883_);
if (v___x_1888_ == 0)
{
v_x_1884_ = v_tail_1887_;
goto _start;
}
else
{
return v___x_1888_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1890_, lean_object* v_x_1891_){
_start:
{
uint8_t v_res_1892_; lean_object* v_r_1893_; 
v_res_1892_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1890_, v_x_1891_);
lean_dec(v_x_1891_);
lean_dec_ref(v_a_1890_);
v_r_1893_ = lean_box(v_res_1892_);
return v_r_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1894_, lean_object* v_x_1895_){
_start:
{
if (lean_obj_tag(v_x_1895_) == 0)
{
return v_x_1894_;
}
else
{
lean_object* v_key_1896_; lean_object* v_value_1897_; lean_object* v_tail_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1928_; 
v_key_1896_ = lean_ctor_get(v_x_1895_, 0);
v_value_1897_ = lean_ctor_get(v_x_1895_, 1);
v_tail_1898_ = lean_ctor_get(v_x_1895_, 2);
v_isSharedCheck_1928_ = !lean_is_exclusive(v_x_1895_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1900_ = v_x_1895_;
v_isShared_1901_ = v_isSharedCheck_1928_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_tail_1898_);
lean_inc(v_value_1897_);
lean_inc(v_key_1896_);
lean_dec(v_x_1895_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1928_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v_parserName_1902_; lean_object* v_pos_1903_; lean_object* v___x_1904_; uint64_t v___x_1905_; uint64_t v___y_1907_; 
v_parserName_1902_ = lean_ctor_get(v_key_1896_, 1);
v_pos_1903_ = lean_ctor_get(v_key_1896_, 2);
v___x_1904_ = lean_array_get_size(v_x_1894_);
v___x_1905_ = l_String_instHashableRaw_hash(v_pos_1903_);
if (lean_obj_tag(v_parserName_1902_) == 0)
{
uint64_t v___x_1926_; 
v___x_1926_ = 1723ULL;
v___y_1907_ = v___x_1926_;
goto v___jp_1906_;
}
else
{
uint64_t v_hash_1927_; 
v_hash_1927_ = lean_ctor_get_uint64(v_parserName_1902_, sizeof(void*)*2);
v___y_1907_ = v_hash_1927_;
goto v___jp_1906_;
}
v___jp_1906_:
{
uint64_t v___x_1908_; uint64_t v___x_1909_; uint64_t v___x_1910_; uint64_t v_fold_1911_; uint64_t v___x_1912_; uint64_t v___x_1913_; uint64_t v___x_1914_; size_t v___x_1915_; size_t v___x_1916_; size_t v___x_1917_; size_t v___x_1918_; size_t v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1922_; 
v___x_1908_ = lean_uint64_mix_hash(v___x_1905_, v___y_1907_);
v___x_1909_ = 32ULL;
v___x_1910_ = lean_uint64_shift_right(v___x_1908_, v___x_1909_);
v_fold_1911_ = lean_uint64_xor(v___x_1908_, v___x_1910_);
v___x_1912_ = 16ULL;
v___x_1913_ = lean_uint64_shift_right(v_fold_1911_, v___x_1912_);
v___x_1914_ = lean_uint64_xor(v_fold_1911_, v___x_1913_);
v___x_1915_ = lean_uint64_to_usize(v___x_1914_);
v___x_1916_ = lean_usize_of_nat(v___x_1904_);
v___x_1917_ = ((size_t)1ULL);
v___x_1918_ = lean_usize_sub(v___x_1916_, v___x_1917_);
v___x_1919_ = lean_usize_land(v___x_1915_, v___x_1918_);
v___x_1920_ = lean_array_uget_borrowed(v_x_1894_, v___x_1919_);
lean_inc(v___x_1920_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 2, v___x_1920_);
v___x_1922_ = v___x_1900_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_key_1896_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_value_1897_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v___x_1920_);
v___x_1922_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_array_uset(v_x_1894_, v___x_1919_, v___x_1922_);
v_x_1894_ = v___x_1923_;
v_x_1895_ = v_tail_1898_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1929_, lean_object* v_source_1930_, lean_object* v_target_1931_){
_start:
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = lean_array_get_size(v_source_1930_);
v___x_1933_ = lean_nat_dec_lt(v_i_1929_, v___x_1932_);
if (v___x_1933_ == 0)
{
lean_dec_ref(v_source_1930_);
lean_dec(v_i_1929_);
return v_target_1931_;
}
else
{
lean_object* v_es_1934_; lean_object* v___x_1935_; lean_object* v_source_1936_; lean_object* v_target_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v_es_1934_ = lean_array_fget(v_source_1930_, v_i_1929_);
v___x_1935_ = lean_box(0);
v_source_1936_ = lean_array_fset(v_source_1930_, v_i_1929_, v___x_1935_);
v_target_1937_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1931_, v_es_1934_);
v___x_1938_ = lean_unsigned_to_nat(1u);
v___x_1939_ = lean_nat_add(v_i_1929_, v___x_1938_);
lean_dec(v_i_1929_);
v_i_1929_ = v___x_1939_;
v_source_1930_ = v_source_1936_;
v_target_1931_ = v_target_1937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1941_){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v_nbuckets_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1942_ = lean_array_get_size(v_data_1941_);
v___x_1943_ = lean_unsigned_to_nat(2u);
v_nbuckets_1944_ = lean_nat_mul(v___x_1942_, v___x_1943_);
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = lean_box(0);
v___x_1947_ = lean_mk_array(v_nbuckets_1944_, v___x_1946_);
v___x_1948_ = lean_array_propagate_mark(v_data_1941_, v___x_1947_);
v___x_1949_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1945_, v_data_1941_, v___x_1948_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1950_, lean_object* v_b_1951_, lean_object* v_x_1952_){
_start:
{
if (lean_obj_tag(v_x_1952_) == 0)
{
lean_dec(v_b_1951_);
lean_dec_ref(v_a_1950_);
return v_x_1952_;
}
else
{
lean_object* v_key_1953_; lean_object* v_value_1954_; lean_object* v_tail_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1967_; 
v_key_1953_ = lean_ctor_get(v_x_1952_, 0);
v_value_1954_ = lean_ctor_get(v_x_1952_, 1);
v_tail_1955_ = lean_ctor_get(v_x_1952_, 2);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_x_1952_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1957_ = v_x_1952_;
v_isShared_1958_ = v_isSharedCheck_1967_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_tail_1955_);
lean_inc(v_value_1954_);
lean_inc(v_key_1953_);
lean_dec(v_x_1952_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1967_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
uint8_t v___x_1959_; 
v___x_1959_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1953_, v_a_1950_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1960_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1950_, v_b_1951_, v_tail_1955_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 2, v___x_1960_);
v___x_1962_ = v___x_1957_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v_key_1953_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_value_1954_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
else
{
lean_object* v___x_1965_; 
lean_dec(v_value_1954_);
lean_dec(v_key_1953_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 1, v_b_1951_);
lean_ctor_set(v___x_1957_, 0, v_a_1950_);
v___x_1965_ = v___x_1957_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1950_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_b_1951_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v_tail_1955_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1968_, lean_object* v_a_1969_, lean_object* v_b_1970_){
_start:
{
lean_object* v_size_1971_; lean_object* v_buckets_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2022_; 
v_size_1971_ = lean_ctor_get(v_m_1968_, 0);
v_buckets_1972_ = lean_ctor_get(v_m_1968_, 1);
v_isSharedCheck_2022_ = !lean_is_exclusive(v_m_1968_);
if (v_isSharedCheck_2022_ == 0)
{
v___x_1974_ = v_m_1968_;
v_isShared_1975_ = v_isSharedCheck_2022_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_buckets_1972_);
lean_inc(v_size_1971_);
lean_dec(v_m_1968_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2022_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
lean_object* v_parserName_1976_; lean_object* v_pos_1977_; lean_object* v___x_1978_; uint64_t v___x_1979_; uint64_t v___y_1981_; 
v_parserName_1976_ = lean_ctor_get(v_a_1969_, 1);
v_pos_1977_ = lean_ctor_get(v_a_1969_, 2);
v___x_1978_ = lean_array_get_size(v_buckets_1972_);
v___x_1979_ = l_String_instHashableRaw_hash(v_pos_1977_);
if (lean_obj_tag(v_parserName_1976_) == 0)
{
uint64_t v___x_2020_; 
v___x_2020_ = 1723ULL;
v___y_1981_ = v___x_2020_;
goto v___jp_1980_;
}
else
{
uint64_t v_hash_2021_; 
v_hash_2021_ = lean_ctor_get_uint64(v_parserName_1976_, sizeof(void*)*2);
v___y_1981_ = v_hash_2021_;
goto v___jp_1980_;
}
v___jp_1980_:
{
uint64_t v___x_1982_; uint64_t v___x_1983_; uint64_t v___x_1984_; uint64_t v_fold_1985_; uint64_t v___x_1986_; uint64_t v___x_1987_; uint64_t v___x_1988_; size_t v___x_1989_; size_t v___x_1990_; size_t v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; lean_object* v_bkt_1994_; uint8_t v___x_1995_; 
v___x_1982_ = lean_uint64_mix_hash(v___x_1979_, v___y_1981_);
v___x_1983_ = 32ULL;
v___x_1984_ = lean_uint64_shift_right(v___x_1982_, v___x_1983_);
v_fold_1985_ = lean_uint64_xor(v___x_1982_, v___x_1984_);
v___x_1986_ = 16ULL;
v___x_1987_ = lean_uint64_shift_right(v_fold_1985_, v___x_1986_);
v___x_1988_ = lean_uint64_xor(v_fold_1985_, v___x_1987_);
v___x_1989_ = lean_uint64_to_usize(v___x_1988_);
v___x_1990_ = lean_usize_of_nat(v___x_1978_);
v___x_1991_ = ((size_t)1ULL);
v___x_1992_ = lean_usize_sub(v___x_1990_, v___x_1991_);
v___x_1993_ = lean_usize_land(v___x_1989_, v___x_1992_);
v_bkt_1994_ = lean_array_uget_borrowed(v_buckets_1972_, v___x_1993_);
v___x_1995_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1969_, v_bkt_1994_);
if (v___x_1995_ == 0)
{
lean_object* v___x_1996_; lean_object* v_size_x27_1997_; lean_object* v___x_1998_; lean_object* v_buckets_x27_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; uint8_t v___x_2005_; 
v___x_1996_ = lean_unsigned_to_nat(1u);
v_size_x27_1997_ = lean_nat_add(v_size_1971_, v___x_1996_);
lean_dec(v_size_1971_);
lean_inc(v_bkt_1994_);
v___x_1998_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1998_, 0, v_a_1969_);
lean_ctor_set(v___x_1998_, 1, v_b_1970_);
lean_ctor_set(v___x_1998_, 2, v_bkt_1994_);
v_buckets_x27_1999_ = lean_array_uset(v_buckets_1972_, v___x_1993_, v___x_1998_);
v___x_2000_ = lean_unsigned_to_nat(4u);
v___x_2001_ = lean_nat_mul(v_size_x27_1997_, v___x_2000_);
v___x_2002_ = lean_unsigned_to_nat(3u);
v___x_2003_ = lean_nat_div(v___x_2001_, v___x_2002_);
lean_dec(v___x_2001_);
v___x_2004_ = lean_array_get_size(v_buckets_x27_1999_);
v___x_2005_ = lean_nat_dec_le(v___x_2003_, v___x_2004_);
lean_dec(v___x_2003_);
if (v___x_2005_ == 0)
{
lean_object* v_val_2006_; lean_object* v___x_2008_; 
v_val_2006_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_1999_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 1, v_val_2006_);
lean_ctor_set(v___x_1974_, 0, v_size_x27_1997_);
v___x_2008_ = v___x_1974_;
goto v_reusejp_2007_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_size_x27_1997_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_val_2006_);
v___x_2008_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2007_;
}
v_reusejp_2007_:
{
return v___x_2008_;
}
}
else
{
lean_object* v___x_2011_; 
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 1, v_buckets_x27_1999_);
lean_ctor_set(v___x_1974_, 0, v_size_x27_1997_);
v___x_2011_ = v___x_1974_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_size_x27_1997_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v_buckets_x27_1999_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
else
{
lean_object* v___x_2013_; lean_object* v_buckets_x27_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; 
lean_inc(v_bkt_1994_);
v___x_2013_ = lean_box(0);
v_buckets_x27_2014_ = lean_array_uset(v_buckets_1972_, v___x_1993_, v___x_2013_);
v___x_2015_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1969_, v_b_1970_, v_bkt_1994_);
v___x_2016_ = lean_array_uset(v_buckets_x27_2014_, v___x_1993_, v___x_2015_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 1, v___x_2016_);
v___x_2018_ = v___x_1974_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_size_1971_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v___x_2016_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_2023_, lean_object* v_x_2024_){
_start:
{
if (lean_obj_tag(v_x_2024_) == 0)
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_box(0);
return v___x_2025_;
}
else
{
lean_object* v_key_2026_; lean_object* v_value_2027_; lean_object* v_tail_2028_; uint8_t v___x_2029_; 
v_key_2026_ = lean_ctor_get(v_x_2024_, 0);
v_value_2027_ = lean_ctor_get(v_x_2024_, 1);
v_tail_2028_ = lean_ctor_get(v_x_2024_, 2);
v___x_2029_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_2026_, v_a_2023_);
if (v___x_2029_ == 0)
{
v_x_2024_ = v_tail_2028_;
goto _start;
}
else
{
lean_object* v___x_2031_; 
lean_inc(v_value_2027_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v_value_2027_);
return v___x_2031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_2032_, lean_object* v_x_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2032_, v_x_2033_);
lean_dec(v_x_2033_);
lean_dec_ref(v_a_2032_);
return v_res_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v_buckets_2037_; lean_object* v_parserName_2038_; lean_object* v_pos_2039_; lean_object* v___x_2040_; uint64_t v___x_2041_; uint64_t v___y_2043_; 
v_buckets_2037_ = lean_ctor_get(v_m_2035_, 1);
v_parserName_2038_ = lean_ctor_get(v_a_2036_, 1);
v_pos_2039_ = lean_ctor_get(v_a_2036_, 2);
v___x_2040_ = lean_array_get_size(v_buckets_2037_);
v___x_2041_ = l_String_instHashableRaw_hash(v_pos_2039_);
if (lean_obj_tag(v_parserName_2038_) == 0)
{
uint64_t v___x_2058_; 
v___x_2058_ = 1723ULL;
v___y_2043_ = v___x_2058_;
goto v___jp_2042_;
}
else
{
uint64_t v_hash_2059_; 
v_hash_2059_ = lean_ctor_get_uint64(v_parserName_2038_, sizeof(void*)*2);
v___y_2043_ = v_hash_2059_;
goto v___jp_2042_;
}
v___jp_2042_:
{
uint64_t v___x_2044_; uint64_t v___x_2045_; uint64_t v___x_2046_; uint64_t v_fold_2047_; uint64_t v___x_2048_; uint64_t v___x_2049_; uint64_t v___x_2050_; size_t v___x_2051_; size_t v___x_2052_; size_t v___x_2053_; size_t v___x_2054_; size_t v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2044_ = lean_uint64_mix_hash(v___x_2041_, v___y_2043_);
v___x_2045_ = 32ULL;
v___x_2046_ = lean_uint64_shift_right(v___x_2044_, v___x_2045_);
v_fold_2047_ = lean_uint64_xor(v___x_2044_, v___x_2046_);
v___x_2048_ = 16ULL;
v___x_2049_ = lean_uint64_shift_right(v_fold_2047_, v___x_2048_);
v___x_2050_ = lean_uint64_xor(v_fold_2047_, v___x_2049_);
v___x_2051_ = lean_uint64_to_usize(v___x_2050_);
v___x_2052_ = lean_usize_of_nat(v___x_2040_);
v___x_2053_ = ((size_t)1ULL);
v___x_2054_ = lean_usize_sub(v___x_2052_, v___x_2053_);
v___x_2055_ = lean_usize_land(v___x_2051_, v___x_2054_);
v___x_2056_ = lean_array_uget_borrowed(v_buckets_2037_, v___x_2055_);
v___x_2057_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2036_, v___x_2056_);
return v___x_2057_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_2060_, lean_object* v_a_2061_){
_start:
{
lean_object* v_res_2062_; 
v_res_2062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2060_, v_a_2061_);
lean_dec_ref(v_a_2061_);
lean_dec_ref(v_m_2060_);
return v_res_2062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_2063_, lean_object* v_p_2064_, lean_object* v_c_2065_, lean_object* v_s_2066_){
_start:
{
lean_object* v_cache_2067_; lean_object* v_toCacheableParserContext_2068_; lean_object* v_stxStack_2069_; lean_object* v_pos_2070_; lean_object* v_recoveredErrors_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2120_; 
v_cache_2067_ = lean_ctor_get(v_s_2066_, 3);
lean_inc_ref(v_cache_2067_);
v_toCacheableParserContext_2068_ = lean_ctor_get(v_c_2065_, 2);
v_stxStack_2069_ = lean_ctor_get(v_s_2066_, 0);
v_pos_2070_ = lean_ctor_get(v_s_2066_, 2);
v_recoveredErrors_2071_ = lean_ctor_get(v_s_2066_, 5);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_s_2066_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; lean_object* v_unused_2122_; lean_object* v_unused_2123_; 
v_unused_2121_ = lean_ctor_get(v_s_2066_, 4);
lean_dec(v_unused_2121_);
v_unused_2122_ = lean_ctor_get(v_s_2066_, 3);
lean_dec(v_unused_2122_);
v_unused_2123_ = lean_ctor_get(v_s_2066_, 1);
lean_dec(v_unused_2123_);
v___x_2073_ = v_s_2066_;
v_isShared_2074_ = v_isSharedCheck_2120_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_recoveredErrors_2071_);
lean_inc(v_pos_2070_);
lean_inc(v_stxStack_2069_);
lean_dec(v_s_2066_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2120_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v_parserCache_2075_; lean_object* v_key_2076_; lean_object* v___x_2077_; 
v_parserCache_2075_ = lean_ctor_get(v_cache_2067_, 1);
lean_inc(v_pos_2070_);
lean_inc_ref(v_toCacheableParserContext_2068_);
v_key_2076_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_2076_, 0, v_toCacheableParserContext_2068_);
lean_ctor_set(v_key_2076_, 1, v_parserName_2063_);
lean_ctor_set(v_key_2076_, 2, v_pos_2070_);
v___x_2077_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_2075_, v_key_2076_);
if (lean_obj_tag(v___x_2077_) == 1)
{
lean_object* v_val_2078_; lean_object* v_stx_2079_; lean_object* v_lhsPrec_2080_; lean_object* v_newPos_2081_; lean_object* v_errorMsg_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
lean_dec_ref_known(v_key_2076_, 3);
lean_dec(v_pos_2070_);
lean_dec_ref(v_c_2065_);
lean_dec_ref(v_p_2064_);
v_val_2078_ = lean_ctor_get(v___x_2077_, 0);
lean_inc(v_val_2078_);
lean_dec_ref_known(v___x_2077_, 1);
v_stx_2079_ = lean_ctor_get(v_val_2078_, 0);
lean_inc(v_stx_2079_);
v_lhsPrec_2080_ = lean_ctor_get(v_val_2078_, 1);
lean_inc(v_lhsPrec_2080_);
v_newPos_2081_ = lean_ctor_get(v_val_2078_, 2);
lean_inc(v_newPos_2081_);
v_errorMsg_2082_ = lean_ctor_get(v_val_2078_, 3);
lean_inc(v_errorMsg_2082_);
lean_dec(v_val_2078_);
v___x_2083_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_2069_, v_stx_2079_);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v_errorMsg_2082_);
lean_ctor_set(v___x_2073_, 2, v_newPos_2081_);
lean_ctor_set(v___x_2073_, 1, v_lhsPrec_2080_);
lean_ctor_set(v___x_2073_, 0, v___x_2083_);
v___x_2085_ = v___x_2073_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_lhsPrec_2080_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_newPos_2081_);
lean_ctor_set(v_reuseFailAlloc_2086_, 3, v_cache_2067_);
lean_ctor_set(v_reuseFailAlloc_2086_, 4, v_errorMsg_2082_);
lean_ctor_set(v_reuseFailAlloc_2086_, 5, v_recoveredErrors_2071_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
else
{
lean_object* v_raw_2087_; lean_object* v_initStackSz_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2092_; 
lean_dec(v___x_2077_);
v_raw_2087_ = lean_ctor_get(v_stxStack_2069_, 0);
v_initStackSz_2088_ = lean_array_get_size(v_raw_2087_);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_box(0);
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 4, v___x_2090_);
lean_ctor_set(v___x_2073_, 1, v___x_2089_);
v___x_2092_ = v___x_2073_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_stxStack_2069_);
lean_ctor_set(v_reuseFailAlloc_2119_, 1, v___x_2089_);
lean_ctor_set(v_reuseFailAlloc_2119_, 2, v_pos_2070_);
lean_ctor_set(v_reuseFailAlloc_2119_, 3, v_cache_2067_);
lean_ctor_set(v_reuseFailAlloc_2119_, 4, v___x_2090_);
lean_ctor_set(v_reuseFailAlloc_2119_, 5, v_recoveredErrors_2071_);
v___x_2092_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
lean_object* v_s_2093_; lean_object* v_cache_2094_; lean_object* v_stxStack_2095_; lean_object* v_lhsPrec_2096_; lean_object* v_pos_2097_; lean_object* v_errorMsg_2098_; lean_object* v_recoveredErrors_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2118_; 
v_s_2093_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_2088_, v_p_2064_, v_c_2065_, v___x_2092_);
v_cache_2094_ = lean_ctor_get(v_s_2093_, 3);
v_stxStack_2095_ = lean_ctor_get(v_s_2093_, 0);
v_lhsPrec_2096_ = lean_ctor_get(v_s_2093_, 1);
v_pos_2097_ = lean_ctor_get(v_s_2093_, 2);
v_errorMsg_2098_ = lean_ctor_get(v_s_2093_, 4);
v_recoveredErrors_2099_ = lean_ctor_get(v_s_2093_, 5);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_s_2093_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2101_ = v_s_2093_;
v_isShared_2102_ = v_isSharedCheck_2118_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_recoveredErrors_2099_);
lean_inc(v_errorMsg_2098_);
lean_inc(v_cache_2094_);
lean_inc(v_pos_2097_);
lean_inc(v_lhsPrec_2096_);
lean_inc(v_stxStack_2095_);
lean_dec(v_s_2093_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2118_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_tokenCache_2103_; lean_object* v_parserCache_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2117_; 
v_tokenCache_2103_ = lean_ctor_get(v_cache_2094_, 0);
v_parserCache_2104_ = lean_ctor_get(v_cache_2094_, 1);
v_isSharedCheck_2117_ = !lean_is_exclusive(v_cache_2094_);
if (v_isSharedCheck_2117_ == 0)
{
v___x_2106_ = v_cache_2094_;
v_isShared_2107_ = v_isSharedCheck_2117_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_parserCache_2104_);
lean_inc(v_tokenCache_2103_);
lean_dec(v_cache_2094_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2117_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2108_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2095_);
lean_inc(v_errorMsg_2098_);
lean_inc(v_pos_2097_);
lean_inc(v_lhsPrec_2096_);
v___x_2109_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v_lhsPrec_2096_);
lean_ctor_set(v___x_2109_, 2, v_pos_2097_);
lean_ctor_set(v___x_2109_, 3, v_errorMsg_2098_);
v___x_2110_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_2104_, v_key_2076_, v___x_2109_);
if (v_isShared_2107_ == 0)
{
lean_ctor_set(v___x_2106_, 1, v___x_2110_);
v___x_2112_ = v___x_2106_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2116_; 
v_reuseFailAlloc_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2116_, 0, v_tokenCache_2103_);
lean_ctor_set(v_reuseFailAlloc_2116_, 1, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2116_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
lean_object* v___x_2114_; 
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 3, v___x_2112_);
v___x_2114_ = v___x_2101_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_stxStack_2095_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_lhsPrec_2096_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_pos_2097_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v___x_2112_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v_errorMsg_2098_);
lean_ctor_set(v_reuseFailAlloc_2115_, 5, v_recoveredErrors_2099_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2124_, lean_object* v_m_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2125_, v_a_2126_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2128_, lean_object* v_m_2129_, lean_object* v_a_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2128_, v_m_2129_, v_a_2130_);
lean_dec_ref(v_a_2130_);
lean_dec_ref(v_m_2129_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2132_, lean_object* v_m_2133_, lean_object* v_a_2134_, lean_object* v_b_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2133_, v_a_2134_, v_b_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2137_, lean_object* v_a_2138_, lean_object* v_x_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2138_, v_x_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2141_, lean_object* v_a_2142_, lean_object* v_x_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2141_, v_a_2142_, v_x_2143_);
lean_dec(v_x_2143_);
lean_dec_ref(v_a_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2145_, lean_object* v_a_2146_, lean_object* v_x_2147_){
_start:
{
uint8_t v___x_2148_; 
v___x_2148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2146_, v_x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2149_, lean_object* v_a_2150_, lean_object* v_x_2151_){
_start:
{
uint8_t v_res_2152_; lean_object* v_r_2153_; 
v_res_2152_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2149_, v_a_2150_, v_x_2151_);
lean_dec(v_x_2151_);
lean_dec_ref(v_a_2150_);
v_r_2153_ = lean_box(v_res_2152_);
return v_r_2153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2154_, lean_object* v_data_2155_){
_start:
{
lean_object* v___x_2156_; 
v___x_2156_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2157_, lean_object* v_a_2158_, lean_object* v_b_2159_, lean_object* v_x_2160_){
_start:
{
lean_object* v___x_2161_; 
v___x_2161_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2158_, v_b_2159_, v_x_2160_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2162_, lean_object* v_i_2163_, lean_object* v_source_2164_, lean_object* v_target_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2163_, v_source_2164_, v_target_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2167_, lean_object* v_x_2168_, lean_object* v_x_2169_){
_start:
{
lean_object* v___x_2170_; 
v___x_2170_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2168_, v_x_2169_);
return v___x_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2171_, lean_object* v_p_2172_){
_start:
{
lean_object* v_info_2173_; lean_object* v_fn_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2182_; 
v_info_2173_ = lean_ctor_get(v_p_2172_, 0);
v_fn_2174_ = lean_ctor_get(v_p_2172_, 1);
v_isSharedCheck_2182_ = !lean_is_exclusive(v_p_2172_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2176_ = v_p_2172_;
v_isShared_2177_ = v_isSharedCheck_2182_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_fn_2174_);
lean_inc(v_info_2173_);
lean_dec(v_p_2172_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2182_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2178_; lean_object* v___x_2180_; 
v___x_2178_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2178_, 0, v_parserName_2171_);
lean_closure_set(v___x_2178_, 1, v_fn_2174_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v___x_2178_);
v___x_2180_ = v___x_2176_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_info_2173_);
lean_ctor_set(v_reuseFailAlloc_2181_, 1, v___x_2178_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; 
v___x_2190_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2191_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2192_ = l_Lean_addBuiltinDocString(v___x_2190_, v___x_2191_);
return v___x_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2202_, lean_object* v_ictx_2203_, lean_object* v_pmctx_2204_, lean_object* v_tokens_2205_, lean_object* v_s_2206_){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__1));
v___x_2208_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2208_, 0, v_ictx_2203_);
lean_ctor_set(v___x_2208_, 1, v_pmctx_2204_);
lean_ctor_set(v___x_2208_, 2, v___x_2207_);
lean_ctor_set(v___x_2208_, 3, v_tokens_2205_);
v___x_2209_ = lean_apply_2(v_p_2202_, v___x_2208_, v_s_2206_);
return v___x_2209_;
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
