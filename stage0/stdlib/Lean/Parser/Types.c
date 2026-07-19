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
uint64_t lean_uint64_of_nat(lean_object*);
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
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_decEq___boxed(lean_object*, lean_object*);
lean_object* l_List_eraseRepsBy___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0;
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext_beq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Parser_instBEqCacheableParserContext___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instBEqCacheableParserContext_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decEq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0 = (const lean_object*)&l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0_value;
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
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object*, lean_object*);
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
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_56_; uint64_t v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(1723u);
v___x_57_ = lean_uint64_of_nat(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(lean_object* v_x_59_, size_t v_x_60_, size_t v_x_61_, lean_object* v_x_62_, lean_object* v_x_63_){
_start:
{
if (lean_obj_tag(v_x_59_) == 0)
{
lean_object* v_es_64_; size_t v___x_65_; size_t v___x_66_; lean_object* v_j_67_; lean_object* v___x_68_; uint8_t v___x_69_; 
v_es_64_ = lean_ctor_get(v_x_59_, 0);
v___x_65_ = ((size_t)31ULL);
v___x_66_ = lean_usize_land(v_x_60_, v___x_65_);
v_j_67_ = lean_usize_to_nat(v___x_66_);
v___x_68_ = lean_array_get_size(v_es_64_);
v___x_69_ = lean_nat_dec_lt(v_j_67_, v___x_68_);
if (v___x_69_ == 0)
{
lean_dec(v_j_67_);
lean_dec(v_x_63_);
lean_dec(v_x_62_);
return v_x_59_;
}
else
{
lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_108_; 
lean_inc_ref(v_es_64_);
v_isSharedCheck_108_ = !lean_is_exclusive(v_x_59_);
if (v_isSharedCheck_108_ == 0)
{
lean_object* v_unused_109_; 
v_unused_109_ = lean_ctor_get(v_x_59_, 0);
lean_dec(v_unused_109_);
v___x_71_ = v_x_59_;
v_isShared_72_ = v_isSharedCheck_108_;
goto v_resetjp_70_;
}
else
{
lean_dec(v_x_59_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_108_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_v_73_; lean_object* v___x_74_; lean_object* v_xs_x27_75_; lean_object* v___y_77_; 
v_v_73_ = lean_array_fget(v_es_64_, v_j_67_);
v___x_74_ = lean_box(0);
v_xs_x27_75_ = lean_array_fset(v_es_64_, v_j_67_, v___x_74_);
switch(lean_obj_tag(v_v_73_))
{
case 0:
{
lean_object* v_key_82_; lean_object* v_val_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_93_; 
v_key_82_ = lean_ctor_get(v_v_73_, 0);
v_val_83_ = lean_ctor_get(v_v_73_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v_v_73_);
if (v_isSharedCheck_93_ == 0)
{
v___x_85_ = v_v_73_;
v_isShared_86_ = v_isSharedCheck_93_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_val_83_);
lean_inc(v_key_82_);
lean_dec(v_v_73_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_93_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
uint8_t v___x_87_; 
v___x_87_ = lean_name_eq(v_x_62_, v_key_82_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_89_; 
lean_del_object(v___x_85_);
v___x_88_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_82_, v_val_83_, v_x_62_, v_x_63_);
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
v___y_77_ = v___x_89_;
goto v___jp_76_;
}
else
{
lean_object* v___x_91_; 
lean_dec(v_val_83_);
lean_dec(v_key_82_);
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v_x_63_);
lean_ctor_set(v___x_85_, 0, v_x_62_);
v___x_91_ = v___x_85_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_x_62_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_x_63_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
v___y_77_ = v___x_91_;
goto v___jp_76_;
}
}
}
}
case 1:
{
lean_object* v_node_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_106_; 
v_node_94_ = lean_ctor_get(v_v_73_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v_v_73_);
if (v_isSharedCheck_106_ == 0)
{
v___x_96_ = v_v_73_;
v_isShared_97_ = v_isSharedCheck_106_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_node_94_);
lean_dec(v_v_73_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_106_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; size_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_98_ = ((size_t)5ULL);
v___x_99_ = lean_usize_shift_right(v_x_60_, v___x_98_);
v___x_100_ = ((size_t)1ULL);
v___x_101_ = lean_usize_add(v_x_61_, v___x_100_);
v___x_102_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_node_94_, v___x_99_, v___x_101_, v_x_62_, v_x_63_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_102_);
v___x_104_ = v___x_96_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v___x_102_);
v___x_104_ = v_reuseFailAlloc_105_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
v___y_77_ = v___x_104_;
goto v___jp_76_;
}
}
}
default: 
{
lean_object* v___x_107_; 
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v_x_62_);
lean_ctor_set(v___x_107_, 1, v_x_63_);
v___y_77_ = v___x_107_;
goto v___jp_76_;
}
}
v___jp_76_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = lean_array_fset(v_xs_x27_75_, v_j_67_, v___y_77_);
lean_dec(v_j_67_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 0, v___x_78_);
v___x_80_ = v___x_71_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
else
{
lean_object* v_ks_110_; lean_object* v_vs_111_; lean_object* v___x_113_; uint8_t v_isShared_114_; uint8_t v_isSharedCheck_131_; 
v_ks_110_ = lean_ctor_get(v_x_59_, 0);
v_vs_111_ = lean_ctor_get(v_x_59_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_x_59_);
if (v_isSharedCheck_131_ == 0)
{
v___x_113_ = v_x_59_;
v_isShared_114_ = v_isSharedCheck_131_;
goto v_resetjp_112_;
}
else
{
lean_inc(v_vs_111_);
lean_inc(v_ks_110_);
lean_dec(v_x_59_);
v___x_113_ = lean_box(0);
v_isShared_114_ = v_isSharedCheck_131_;
goto v_resetjp_112_;
}
v_resetjp_112_:
{
lean_object* v___x_116_; 
if (v_isShared_114_ == 0)
{
v___x_116_ = v___x_113_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_ks_110_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_vs_111_);
v___x_116_ = v_reuseFailAlloc_130_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
lean_object* v_newNode_117_; uint8_t v___y_119_; size_t v___x_125_; uint8_t v___x_126_; 
v_newNode_117_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v___x_116_, v_x_62_, v_x_63_);
v___x_125_ = ((size_t)7ULL);
v___x_126_ = lean_usize_dec_le(v___x_125_, v_x_61_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_127_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_117_);
v___x_128_ = lean_unsigned_to_nat(4u);
v___x_129_ = lean_nat_dec_lt(v___x_127_, v___x_128_);
lean_dec(v___x_127_);
v___y_119_ = v___x_129_;
goto v___jp_118_;
}
else
{
v___y_119_ = v___x_126_;
goto v___jp_118_;
}
v___jp_118_:
{
if (v___y_119_ == 0)
{
lean_object* v_ks_120_; lean_object* v_vs_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_ks_120_ = lean_ctor_get(v_newNode_117_, 0);
lean_inc_ref(v_ks_120_);
v_vs_121_ = lean_ctor_get(v_newNode_117_, 1);
lean_inc_ref(v_vs_121_);
lean_dec_ref(v_newNode_117_);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0);
v___x_124_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_x_61_, v_ks_120_, v_vs_121_, v___x_122_, v___x_123_);
lean_dec_ref(v_vs_121_);
lean_dec_ref(v_ks_120_);
return v___x_124_;
}
else
{
return v_newNode_117_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_132_, lean_object* v_keys_133_, lean_object* v_vals_134_, lean_object* v_i_135_, lean_object* v_entries_136_){
_start:
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = lean_array_get_size(v_keys_133_);
v___x_138_ = lean_nat_dec_lt(v_i_135_, v___x_137_);
if (v___x_138_ == 0)
{
lean_dec(v_i_135_);
return v_entries_136_;
}
else
{
lean_object* v_k_139_; lean_object* v_v_140_; uint64_t v___y_142_; 
v_k_139_ = lean_array_fget_borrowed(v_keys_133_, v_i_135_);
v_v_140_ = lean_array_fget_borrowed(v_vals_134_, v_i_135_);
if (lean_obj_tag(v_k_139_) == 0)
{
uint64_t v___x_153_; 
v___x_153_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_142_ = v___x_153_;
goto v___jp_141_;
}
else
{
uint64_t v_hash_154_; 
v_hash_154_ = lean_ctor_get_uint64(v_k_139_, sizeof(void*)*2);
v___y_142_ = v_hash_154_;
goto v___jp_141_;
}
v___jp_141_:
{
size_t v_h_143_; size_t v___x_144_; lean_object* v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v_h_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_h_143_ = lean_uint64_to_usize(v___y_142_);
v___x_144_ = ((size_t)5ULL);
v___x_145_ = lean_unsigned_to_nat(1u);
v___x_146_ = ((size_t)1ULL);
v___x_147_ = lean_usize_sub(v_depth_132_, v___x_146_);
v___x_148_ = lean_usize_mul(v___x_144_, v___x_147_);
v_h_149_ = lean_usize_shift_right(v_h_143_, v___x_148_);
v___x_150_ = lean_nat_add(v_i_135_, v___x_145_);
lean_dec(v_i_135_);
lean_inc(v_v_140_);
lean_inc(v_k_139_);
v___x_151_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_entries_136_, v_h_149_, v_depth_132_, v_k_139_, v_v_140_);
v_i_135_ = v___x_150_;
v_entries_136_ = v___x_151_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_155_, lean_object* v_keys_156_, lean_object* v_vals_157_, lean_object* v_i_158_, lean_object* v_entries_159_){
_start:
{
size_t v_depth_boxed_160_; lean_object* v_res_161_; 
v_depth_boxed_160_ = lean_unbox_usize(v_depth_155_);
lean_dec(v_depth_155_);
v_res_161_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_160_, v_keys_156_, v_vals_157_, v_i_158_, v_entries_159_);
lean_dec_ref(v_vals_157_);
lean_dec_ref(v_keys_156_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_, lean_object* v_x_166_){
_start:
{
size_t v_x_357__boxed_167_; size_t v_x_358__boxed_168_; lean_object* v_res_169_; 
v_x_357__boxed_167_ = lean_unbox_usize(v_x_163_);
lean_dec(v_x_163_);
v_x_358__boxed_168_ = lean_unbox_usize(v_x_164_);
lean_dec(v_x_164_);
v_res_169_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_162_, v_x_357__boxed_167_, v_x_358__boxed_168_, v_x_165_, v_x_166_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
uint64_t v___y_174_; 
if (lean_obj_tag(v_x_171_) == 0)
{
uint64_t v___x_178_; 
v___x_178_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_174_ = v___x_178_;
goto v___jp_173_;
}
else
{
uint64_t v_hash_179_; 
v_hash_179_ = lean_ctor_get_uint64(v_x_171_, sizeof(void*)*2);
v___y_174_ = v_hash_179_;
goto v___jp_173_;
}
v___jp_173_:
{
size_t v___x_175_; size_t v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_uint64_to_usize(v___y_174_);
v___x_176_ = ((size_t)1ULL);
v___x_177_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_170_, v___x_175_, v___x_176_, v_x_171_, v_x_172_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object* v_s_180_, lean_object* v_k_181_){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = lean_box(0);
v___x_183_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_s_180_, v_k_181_, v___x_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0(lean_object* v_00_u03b2_184_, lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_x_185_, v_x_186_, v_x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_189_, lean_object* v_x_190_, size_t v_x_191_, size_t v_x_192_, lean_object* v_x_193_, lean_object* v_x_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_190_, v_x_191_, v_x_192_, v_x_193_, v_x_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_196_, lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
size_t v_x_550__boxed_202_; size_t v_x_551__boxed_203_; lean_object* v_res_204_; 
v_x_550__boxed_202_ = lean_unbox_usize(v_x_198_);
lean_dec(v_x_198_);
v_x_551__boxed_203_ = lean_unbox_usize(v_x_199_);
lean_dec(v_x_199_);
v_res_204_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(v_00_u03b2_196_, v_x_197_, v_x_550__boxed_202_, v_x_551__boxed_203_, v_x_200_, v_x_201_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_205_, lean_object* v_n_206_, lean_object* v_k_207_, lean_object* v_v_208_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v_n_206_, v_k_207_, v_v_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_210_, size_t v_depth_211_, lean_object* v_keys_212_, lean_object* v_vals_213_, lean_object* v_heq_214_, lean_object* v_i_215_, lean_object* v_entries_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_211_, v_keys_212_, v_vals_213_, v_i_215_, v_entries_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_218_, lean_object* v_depth_219_, lean_object* v_keys_220_, lean_object* v_vals_221_, lean_object* v_heq_222_, lean_object* v_i_223_, lean_object* v_entries_224_){
_start:
{
size_t v_depth_boxed_225_; lean_object* v_res_226_; 
v_depth_boxed_225_ = lean_unbox_usize(v_depth_219_);
lean_dec(v_depth_219_);
v_res_226_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(v_00_u03b2_218_, v_depth_boxed_225_, v_keys_220_, v_vals_221_, v_heq_222_, v_i_223_, v_entries_224_);
lean_dec_ref(v_vals_221_);
lean_dec_ref(v_keys_220_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_228_, v_x_229_, v_x_230_, v_x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10));
v___x_260_ = l_Lean_mkAtom(v___x_259_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_261_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12);
v___x_262_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_263_ = lean_array_push(v___x_262_, v___x_261_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_274_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_275_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_276_ = lean_array_push(v___x_275_, v___x_274_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_277_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17);
v___x_278_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15));
v___x_279_ = lean_box(2);
v___x_280_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
lean_ctor_set(v___x_280_, 2, v___x_277_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_281_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18);
v___x_282_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13);
v___x_283_ = lean_array_push(v___x_282_, v___x_281_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_285_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19);
v___x_286_ = lean_array_push(v___x_285_, v___x_284_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_288_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20);
v___x_289_ = lean_array_push(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_291_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21);
v___x_292_ = lean_array_push(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_294_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22);
v___x_295_ = lean_array_push(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_296_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23);
v___x_297_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11));
v___x_298_ = lean_box(2);
v___x_299_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
lean_ctor_set(v___x_299_, 2, v___x_296_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24);
v___x_301_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_302_ = lean_array_push(v___x_301_, v___x_300_);
return v___x_302_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26(void){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_303_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25);
v___x_304_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9));
v___x_305_ = lean_box(2);
v___x_306_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
lean_ctor_set(v___x_306_, 2, v___x_303_);
return v___x_306_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26);
v___x_308_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_309_ = lean_array_push(v___x_308_, v___x_307_);
return v___x_309_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_310_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27);
v___x_311_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7));
v___x_312_ = lean_box(2);
v___x_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
lean_ctor_set(v___x_313_, 2, v___x_310_);
return v___x_313_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_314_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28);
v___x_315_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_316_ = lean_array_push(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_317_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29);
v___x_318_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4));
v___x_319_ = lean_box(2);
v___x_320_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_318_);
lean_ctor_set(v___x_320_, 2, v___x_317_);
return v___x_320_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam(void){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__1(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_324_ = lean_string_utf8_byte_size(v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__2(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_325_ = lean_obj_once(&l_Lean_Parser_instInhabitedInputContext___closed__1, &l_Lean_Parser_instInhabitedInputContext___closed__1_once, _init_l_Lean_Parser_instInhabitedInputContext___closed__1);
v___x_326_ = l_Lean_instInhabitedFileMap_default;
v___x_327_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_328_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
lean_ctor_set(v___x_328_, 2, v___x_326_);
lean_ctor_set(v___x_328_, 3, v___x_325_);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext(void){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_obj_once(&l_Lean_Parser_instInhabitedInputContext___closed__2, &l_Lean_Parser_instInhabitedInputContext___closed__2_once, _init_l_Lean_Parser_instInhabitedInputContext___closed__2);
return v___x_329_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_mk___auto__1(void){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk___redArg(lean_object* v_input_331_, lean_object* v_fileName_332_, lean_object* v_endPos_333_, lean_object* v_fileMap_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_335_, 0, v_input_331_);
lean_ctor_set(v___x_335_, 1, v_fileName_332_);
lean_ctor_set(v___x_335_, 2, v_fileMap_334_);
lean_ctor_set(v___x_335_, 3, v_endPos_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk(lean_object* v_input_336_, lean_object* v_fileName_337_, lean_object* v_endPos_338_, lean_object* v_endPos__valid_339_, lean_object* v_fileMap_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_341_, 0, v_input_336_);
lean_ctor_set(v___x_341_, 1, v_fileName_337_);
lean_ctor_set(v___x_341_, 2, v_fileMap_340_);
lean_ctor_set(v___x_341_, 3, v_endPos_338_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input(lean_object* v_c_342_){
_start:
{
lean_object* v_inputString_343_; lean_object* v_endPos_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_inputString_343_ = lean_ctor_get(v_c_342_, 0);
v_endPos_344_ = lean_ctor_get(v_c_342_, 3);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_string_utf8_extract(v_inputString_343_, v___x_345_, v_endPos_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input___boxed(lean_object* v_c_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Parser_InputContext_input(v_c_347_);
lean_dec_ref(v_c_347_);
return v_res_348_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_InputContext_atEnd(lean_object* v_c_349_, lean_object* v_p_350_){
_start:
{
lean_object* v_endPos_351_; uint8_t v___x_352_; 
v_endPos_351_ = lean_ctor_get(v_c_349_, 3);
v___x_352_ = lean_nat_dec_le(v_endPos_351_, v_p_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_atEnd___boxed(lean_object* v_c_353_, lean_object* v_p_354_){
_start:
{
uint8_t v_res_355_; lean_object* v_r_356_; 
v_res_355_ = l_Lean_Parser_InputContext_atEnd(v_c_353_, v_p_354_);
lean_dec(v_p_354_);
lean_dec_ref(v_c_353_);
v_r_356_ = lean_box(v_res_355_);
return v_r_356_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get(lean_object* v_c_357_, lean_object* v_p_358_){
_start:
{
lean_object* v_inputString_359_; uint32_t v___x_360_; 
v_inputString_359_ = lean_ctor_get(v_c_357_, 0);
v___x_360_ = lean_string_utf8_get(v_inputString_359_, v_p_358_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get___boxed(lean_object* v_c_361_, lean_object* v_p_362_){
_start:
{
uint32_t v_res_363_; lean_object* v_r_364_; 
v_res_363_ = l_Lean_Parser_InputContext_get(v_c_361_, v_p_362_);
lean_dec(v_p_362_);
lean_dec_ref(v_c_361_);
v_r_364_ = lean_box_uint32(v_res_363_);
return v_r_364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_365_, lean_object* v_x_366_, lean_object* v_h__1_367_){
_start:
{
lean_object* v___x_368_; 
v___x_368_ = lean_apply_2(v_h__1_367_, v_x_365_, v_x_366_);
return v___x_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_369_, lean_object* v_x_370_, lean_object* v_x_371_, lean_object* v_h__1_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_apply_2(v_h__1_372_, v_x_370_, v_x_371_);
return v___x_373_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27___redArg(lean_object* v_c_374_, lean_object* v_p_375_){
_start:
{
lean_object* v_inputString_376_; uint32_t v___x_377_; 
v_inputString_376_ = lean_ctor_get(v_c_374_, 0);
v___x_377_ = lean_string_utf8_get_fast(v_inputString_376_, v_p_375_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___redArg___boxed(lean_object* v_c_378_, lean_object* v_p_379_){
_start:
{
uint32_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l_Lean_Parser_InputContext_get_x27___redArg(v_c_378_, v_p_379_);
lean_dec(v_p_379_);
lean_dec_ref(v_c_378_);
v_r_381_ = lean_box_uint32(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27(lean_object* v_c_382_, lean_object* v_p_383_, lean_object* v_h_384_){
_start:
{
lean_object* v_inputString_385_; uint32_t v___x_386_; 
v_inputString_385_ = lean_ctor_get(v_c_382_, 0);
v___x_386_ = lean_string_utf8_get_fast(v_inputString_385_, v_p_383_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___boxed(lean_object* v_c_387_, lean_object* v_p_388_, lean_object* v_h_389_){
_start:
{
uint32_t v_res_390_; lean_object* v_r_391_; 
v_res_390_ = l_Lean_Parser_InputContext_get_x27(v_c_387_, v_p_388_, v_h_389_);
lean_dec(v_p_388_);
lean_dec_ref(v_c_387_);
v_r_391_ = lean_box_uint32(v_res_390_);
return v_r_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next(lean_object* v_c_392_, lean_object* v_p_393_){
_start:
{
lean_object* v_inputString_394_; lean_object* v___x_395_; 
v_inputString_394_ = lean_ctor_get(v_c_392_, 0);
v___x_395_ = lean_string_utf8_next(v_inputString_394_, v_p_393_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next___boxed(lean_object* v_c_396_, lean_object* v_p_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Parser_InputContext_next(v_c_396_, v_p_397_);
lean_dec(v_p_397_);
lean_dec_ref(v_c_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg(lean_object* v_c_399_, lean_object* v_p_400_){
_start:
{
lean_object* v_inputString_401_; lean_object* v___x_402_; 
v_inputString_401_ = lean_ctor_get(v_c_399_, 0);
v___x_402_ = lean_string_utf8_next_fast(v_inputString_401_, v_p_400_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg___boxed(lean_object* v_c_403_, lean_object* v_p_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Lean_Parser_InputContext_next_x27___redArg(v_c_403_, v_p_404_);
lean_dec(v_p_404_);
lean_dec_ref(v_c_403_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27(lean_object* v_c_406_, lean_object* v_p_407_, lean_object* v_h_408_){
_start:
{
lean_object* v_inputString_409_; lean_object* v___x_410_; 
v_inputString_409_ = lean_ctor_get(v_c_406_, 0);
v___x_410_ = lean_string_utf8_next_fast(v_inputString_409_, v_p_407_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___boxed(lean_object* v_c_411_, lean_object* v_p_412_, lean_object* v_h_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Lean_Parser_InputContext_next_x27(v_c_411_, v_p_412_, v_h_413_);
lean_dec(v_p_412_);
lean_dec_ref(v_c_411_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract(lean_object* v_c_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_inputString_418_; lean_object* v___x_419_; 
v_inputString_418_ = lean_ctor_get(v_c_415_, 0);
v___x_419_ = lean_string_utf8_extract(v_inputString_418_, v_a_416_, v_a_417_);
return v___x_419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract___boxed(lean_object* v_c_420_, lean_object* v_a_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Parser_InputContext_extract(v_c_420_, v_a_421_, v_a_422_);
lean_dec(v_a_422_);
lean_dec(v_a_421_);
lean_dec_ref(v_c_420_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring(lean_object* v_c_424_, lean_object* v_startPos_425_, lean_object* v_stopPos_426_){
_start:
{
lean_object* v_inputString_427_; lean_object* v_endPos_428_; uint8_t v___x_429_; 
v_inputString_427_ = lean_ctor_get(v_c_424_, 0);
v_endPos_428_ = lean_ctor_get(v_c_424_, 3);
v___x_429_ = lean_nat_dec_le(v_stopPos_426_, v_endPos_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
lean_dec(v_stopPos_426_);
lean_inc(v_endPos_428_);
lean_inc_ref(v_inputString_427_);
v___x_430_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_430_, 0, v_inputString_427_);
lean_ctor_set(v___x_430_, 1, v_startPos_425_);
lean_ctor_set(v___x_430_, 2, v_endPos_428_);
return v___x_430_;
}
else
{
lean_object* v___x_431_; 
lean_inc_ref(v_inputString_427_);
v___x_431_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_431_, 0, v_inputString_427_);
lean_ctor_set(v___x_431_, 1, v_startPos_425_);
lean_ctor_set(v___x_431_, 2, v_stopPos_426_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring___boxed(lean_object* v_c_432_, lean_object* v_startPos_433_, lean_object* v_stopPos_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Lean_Parser_InputContext_substring(v_c_432_, v_startPos_433_, v_stopPos_434_);
lean_dec_ref(v_c_432_);
return v_res_435_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_getNext(lean_object* v_input_436_, lean_object* v_pos_437_){
_start:
{
lean_object* v_inputString_438_; lean_object* v___x_439_; uint32_t v___x_440_; 
v_inputString_438_ = lean_ctor_get(v_input_436_, 0);
v___x_439_ = lean_string_utf8_next(v_inputString_438_, v_pos_437_);
v___x_440_ = lean_string_utf8_get(v_inputString_438_, v___x_439_);
lean_dec(v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_getNext___boxed(lean_object* v_input_441_, lean_object* v_pos_442_){
_start:
{
uint32_t v_res_443_; lean_object* v_r_444_; 
v_res_443_ = l_Lean_Parser_InputContext_getNext(v_input_441_, v_pos_442_);
lean_dec(v_pos_442_);
lean_dec_ref(v_input_441_);
v_r_444_ = lean_box_uint32(v_res_443_);
return v_r_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev(lean_object* v_c_445_, lean_object* v_pos_446_){
_start:
{
lean_object* v_inputString_447_; lean_object* v___x_448_; 
v_inputString_447_ = lean_ctor_get(v_c_445_, 0);
v___x_448_ = lean_string_utf8_prev(v_inputString_447_, v_pos_446_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev___boxed(lean_object* v_c_449_, lean_object* v_pos_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Lean_Parser_InputContext_prev(v_c_449_, v_pos_450_);
lean_dec(v_pos_450_);
lean_dec_ref(v_c_449_);
return v_res_451_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(lean_object* v_x_452_, lean_object* v_x_453_){
_start:
{
if (lean_obj_tag(v_x_452_) == 0)
{
if (lean_obj_tag(v_x_453_) == 0)
{
uint8_t v___x_454_; 
v___x_454_ = 1;
return v___x_454_;
}
else
{
uint8_t v___x_455_; 
v___x_455_ = 0;
return v___x_455_;
}
}
else
{
if (lean_obj_tag(v_x_453_) == 0)
{
uint8_t v___x_456_; 
v___x_456_ = 0;
return v___x_456_;
}
else
{
lean_object* v_val_457_; lean_object* v_val_458_; uint8_t v___x_459_; 
v_val_457_ = lean_ctor_get(v_x_452_, 0);
v_val_458_ = lean_ctor_get(v_x_453_, 0);
v___x_459_ = lean_nat_dec_eq(v_val_457_, v_val_458_);
return v___x_459_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0___boxed(lean_object* v_x_460_, lean_object* v_x_461_){
_start:
{
uint8_t v_res_462_; lean_object* v_r_463_; 
v_res_462_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(v_x_460_, v_x_461_);
lean_dec(v_x_461_);
lean_dec(v_x_460_);
v_r_463_ = lean_box(v_res_462_);
return v_r_463_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___redArg(lean_object* v_xs_464_, lean_object* v_ys_465_, lean_object* v_x_466_){
_start:
{
lean_object* v_zero_467_; uint8_t v_isZero_468_; 
v_zero_467_ = lean_unsigned_to_nat(0u);
v_isZero_468_ = lean_nat_dec_eq(v_x_466_, v_zero_467_);
if (v_isZero_468_ == 1)
{
lean_dec(v_x_466_);
return v_isZero_468_;
}
else
{
lean_object* v_one_469_; lean_object* v_n_470_; lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_one_469_ = lean_unsigned_to_nat(1u);
v_n_470_ = lean_nat_sub(v_x_466_, v_one_469_);
lean_dec(v_x_466_);
v___x_471_ = lean_array_fget_borrowed(v_xs_464_, v_n_470_);
v___x_472_ = lean_array_fget_borrowed(v_ys_465_, v_n_470_);
v___x_473_ = lean_string_dec_eq(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_dec(v_n_470_);
return v___x_473_;
}
else
{
v_x_466_ = v_n_470_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___redArg___boxed(lean_object* v_xs_475_, lean_object* v_ys_476_, lean_object* v_x_477_){
_start:
{
uint8_t v_res_478_; lean_object* v_r_479_; 
v_res_478_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___redArg(v_xs_475_, v_ys_476_, v_x_477_);
lean_dec_ref(v_ys_476_);
lean_dec_ref(v_xs_475_);
v_r_479_ = lean_box(v_res_478_);
return v_r_479_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext_beq(lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_prec_482_; lean_object* v_quotDepth_483_; uint8_t v_suppressInsideQuot_484_; lean_object* v_savedPos_x3f_485_; lean_object* v_forbiddenTks_486_; lean_object* v_prec_487_; lean_object* v_quotDepth_488_; uint8_t v_suppressInsideQuot_489_; lean_object* v_savedPos_x3f_490_; lean_object* v_forbiddenTks_491_; uint8_t v___y_493_; uint8_t v___x_499_; 
v_prec_482_ = lean_ctor_get(v_x_480_, 0);
v_quotDepth_483_ = lean_ctor_get(v_x_480_, 1);
v_suppressInsideQuot_484_ = lean_ctor_get_uint8(v_x_480_, sizeof(void*)*4);
v_savedPos_x3f_485_ = lean_ctor_get(v_x_480_, 2);
v_forbiddenTks_486_ = lean_ctor_get(v_x_480_, 3);
v_prec_487_ = lean_ctor_get(v_x_481_, 0);
v_quotDepth_488_ = lean_ctor_get(v_x_481_, 1);
v_suppressInsideQuot_489_ = lean_ctor_get_uint8(v_x_481_, sizeof(void*)*4);
v_savedPos_x3f_490_ = lean_ctor_get(v_x_481_, 2);
v_forbiddenTks_491_ = lean_ctor_get(v_x_481_, 3);
v___x_499_ = lean_nat_dec_eq(v_prec_482_, v_prec_487_);
if (v___x_499_ == 0)
{
return v___x_499_;
}
else
{
uint8_t v___x_500_; 
v___x_500_ = lean_nat_dec_eq(v_quotDepth_483_, v_quotDepth_488_);
if (v___x_500_ == 0)
{
return v___x_500_;
}
else
{
if (v_suppressInsideQuot_484_ == 0)
{
if (v_suppressInsideQuot_489_ == 0)
{
v___y_493_ = v___x_500_;
goto v___jp_492_;
}
else
{
return v_suppressInsideQuot_484_;
}
}
else
{
v___y_493_ = v_suppressInsideQuot_489_;
goto v___jp_492_;
}
}
}
v___jp_492_:
{
if (v___y_493_ == 0)
{
return v___y_493_;
}
else
{
uint8_t v___x_494_; 
v___x_494_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(v_savedPos_x3f_485_, v_savedPos_x3f_490_);
if (v___x_494_ == 0)
{
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_495_ = lean_array_get_size(v_forbiddenTks_486_);
v___x_496_ = lean_array_get_size(v_forbiddenTks_491_);
v___x_497_ = lean_nat_dec_eq(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
return v___x_497_;
}
else
{
uint8_t v___x_498_; 
v___x_498_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___redArg(v_forbiddenTks_486_, v_forbiddenTks_491_, v___x_495_);
return v___x_498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext_beq___boxed(lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
uint8_t v_res_503_; lean_object* v_r_504_; 
v_res_503_ = l_Lean_Parser_instBEqCacheableParserContext_beq(v_x_501_, v_x_502_);
lean_dec_ref(v_x_502_);
lean_dec_ref(v_x_501_);
v_r_504_ = lean_box(v_res_503_);
return v_r_504_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(lean_object* v_xs_505_, lean_object* v_ys_506_, lean_object* v_hsz_507_, lean_object* v_x_508_, lean_object* v_x_509_){
_start:
{
uint8_t v___x_510_; 
v___x_510_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___redArg(v_xs_505_, v_ys_506_, v_x_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___boxed(lean_object* v_xs_511_, lean_object* v_ys_512_, lean_object* v_hsz_513_, lean_object* v_x_514_, lean_object* v_x_515_){
_start:
{
uint8_t v_res_516_; lean_object* v_r_517_; 
v_res_516_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(v_xs_511_, v_ys_512_, v_hsz_513_, v_x_514_, v_x_515_);
lean_dec_ref(v_ys_512_);
lean_dec_ref(v_xs_511_);
v_r_517_ = lean_box(v_res_516_);
return v_r_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0(lean_object* v_x_520_){
_start:
{
lean_object* v_toInputContext_521_; 
v_toInputContext_521_ = lean_ctor_get(v_x_520_, 0);
lean_inc_ref(v_toInputContext_521_);
return v_toInputContext_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(lean_object* v_x_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_522_);
lean_dec_ref(v_x_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos___redArg(lean_object* v_c_526_, lean_object* v_endPos_527_){
_start:
{
lean_object* v_toInputContext_528_; lean_object* v_toParserModuleContext_529_; lean_object* v_toCacheableParserContext_530_; lean_object* v_tokens_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_549_; 
v_toInputContext_528_ = lean_ctor_get(v_c_526_, 0);
v_toParserModuleContext_529_ = lean_ctor_get(v_c_526_, 1);
v_toCacheableParserContext_530_ = lean_ctor_get(v_c_526_, 2);
v_tokens_531_ = lean_ctor_get(v_c_526_, 3);
v_isSharedCheck_549_ = !lean_is_exclusive(v_c_526_);
if (v_isSharedCheck_549_ == 0)
{
v___x_533_ = v_c_526_;
v_isShared_534_ = v_isSharedCheck_549_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_tokens_531_);
lean_inc(v_toCacheableParserContext_530_);
lean_inc(v_toParserModuleContext_529_);
lean_inc(v_toInputContext_528_);
lean_dec(v_c_526_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_549_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_inputString_535_; lean_object* v_fileName_536_; lean_object* v_fileMap_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_547_; 
v_inputString_535_ = lean_ctor_get(v_toInputContext_528_, 0);
v_fileName_536_ = lean_ctor_get(v_toInputContext_528_, 1);
v_fileMap_537_ = lean_ctor_get(v_toInputContext_528_, 2);
v_isSharedCheck_547_ = !lean_is_exclusive(v_toInputContext_528_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; 
v_unused_548_ = lean_ctor_get(v_toInputContext_528_, 3);
lean_dec(v_unused_548_);
v___x_539_ = v_toInputContext_528_;
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_fileMap_537_);
lean_inc(v_fileName_536_);
lean_inc(v_inputString_535_);
lean_dec(v_toInputContext_528_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_547_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 3, v_endPos_527_);
v___x_542_ = v___x_539_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_inputString_535_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_fileName_536_);
lean_ctor_set(v_reuseFailAlloc_546_, 2, v_fileMap_537_);
lean_ctor_set(v_reuseFailAlloc_546_, 3, v_endPos_527_);
v___x_542_ = v_reuseFailAlloc_546_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_544_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_542_);
v___x_544_ = v___x_533_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_toParserModuleContext_529_);
lean_ctor_set(v_reuseFailAlloc_545_, 2, v_toCacheableParserContext_530_);
lean_ctor_set(v_reuseFailAlloc_545_, 3, v_tokens_531_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos(lean_object* v_c_550_, lean_object* v_endPos_551_, lean_object* v_endPos__valid_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_550_, v_endPos_551_);
return v___x_553_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(lean_object* v_x_560_, lean_object* v_x_561_){
_start:
{
if (lean_obj_tag(v_x_560_) == 0)
{
if (lean_obj_tag(v_x_561_) == 0)
{
uint8_t v___x_562_; 
v___x_562_ = 1;
return v___x_562_;
}
else
{
uint8_t v___x_563_; 
v___x_563_ = 0;
return v___x_563_;
}
}
else
{
if (lean_obj_tag(v_x_561_) == 0)
{
uint8_t v___x_564_; 
v___x_564_ = 0;
return v___x_564_;
}
else
{
lean_object* v_head_565_; lean_object* v_tail_566_; lean_object* v_head_567_; lean_object* v_tail_568_; uint8_t v___x_569_; 
v_head_565_ = lean_ctor_get(v_x_560_, 0);
v_tail_566_ = lean_ctor_get(v_x_560_, 1);
v_head_567_ = lean_ctor_get(v_x_561_, 0);
v_tail_568_ = lean_ctor_get(v_x_561_, 1);
v___x_569_ = lean_string_dec_eq(v_head_565_, v_head_567_);
if (v___x_569_ == 0)
{
return v___x_569_;
}
else
{
v_x_560_ = v_tail_566_;
v_x_561_ = v_tail_568_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(lean_object* v_x_571_, lean_object* v_x_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_571_, v_x_572_);
lean_dec(v_x_572_);
lean_dec(v_x_571_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqError_beq(lean_object* v_x_575_, lean_object* v_x_576_){
_start:
{
lean_object* v_unexpectedTk_577_; lean_object* v_unexpected_578_; lean_object* v_expected_579_; lean_object* v_unexpectedTk_580_; lean_object* v_unexpected_581_; lean_object* v_expected_582_; uint8_t v___x_583_; 
v_unexpectedTk_577_ = lean_ctor_get(v_x_575_, 0);
v_unexpected_578_ = lean_ctor_get(v_x_575_, 1);
v_expected_579_ = lean_ctor_get(v_x_575_, 2);
v_unexpectedTk_580_ = lean_ctor_get(v_x_576_, 0);
v_unexpected_581_ = lean_ctor_get(v_x_576_, 1);
v_expected_582_ = lean_ctor_get(v_x_576_, 2);
v___x_583_ = l_Lean_Syntax_structEq(v_unexpectedTk_577_, v_unexpectedTk_580_);
if (v___x_583_ == 0)
{
return v___x_583_;
}
else
{
uint8_t v___x_584_; 
v___x_584_ = lean_string_dec_eq(v_unexpected_578_, v_unexpected_581_);
if (v___x_584_ == 0)
{
return v___x_584_;
}
else
{
uint8_t v___x_585_; 
v___x_585_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_579_, v_expected_582_);
return v___x_585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
uint8_t v_res_588_; lean_object* v_r_589_; 
v_res_588_ = l_Lean_Parser_instBEqError_beq(v_x_586_, v_x_587_);
lean_dec_ref(v_x_587_);
lean_dec_ref(v_x_586_);
v_r_589_ = lean_box(v_res_588_);
return v_r_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* v_x_594_){
_start:
{
if (lean_obj_tag(v_x_594_) == 0)
{
lean_object* v___x_595_; 
v___x_595_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
return v___x_595_;
}
else
{
lean_object* v_tail_596_; 
v_tail_596_ = lean_ctor_get(v_x_594_, 1);
if (lean_obj_tag(v_tail_596_) == 0)
{
lean_object* v_head_597_; 
v_head_597_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_head_597_);
lean_dec_ref_known(v_x_594_, 2);
return v_head_597_;
}
else
{
lean_object* v_tail_598_; 
lean_inc_ref(v_tail_596_);
v_tail_598_ = lean_ctor_get(v_tail_596_, 1);
if (lean_obj_tag(v_tail_598_) == 0)
{
lean_object* v_head_599_; lean_object* v_head_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v_head_599_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_head_599_);
lean_dec_ref_known(v_x_594_, 2);
v_head_600_ = lean_ctor_get(v_tail_596_, 0);
lean_inc(v_head_600_);
lean_dec_ref_known(v_tail_596_, 2);
v___x_601_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0));
v___x_602_ = lean_string_append(v_head_599_, v___x_601_);
v___x_603_ = lean_string_append(v___x_602_, v_head_600_);
lean_dec(v_head_600_);
return v___x_603_;
}
else
{
lean_object* v_head_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_head_604_ = lean_ctor_get(v_x_594_, 0);
lean_inc(v_head_604_);
lean_dec_ref_known(v_x_594_, 2);
v___x_605_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_606_ = lean_string_append(v_head_604_, v___x_605_);
v___x_607_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_tail_596_);
v___x_608_ = lean_string_append(v___x_606_, v___x_607_);
lean_dec_ref(v___x_607_);
return v___x_608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object* v_as_610_){
_start:
{
lean_object* v___f_611_; lean_object* v___x_612_; 
v___f_611_ = ((lean_object*)(l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0));
v___x_612_ = l_List_eraseRepsBy___redArg(v___f_611_, v_as_610_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object* v_hi_613_, lean_object* v_pivot_614_, lean_object* v_as_615_, lean_object* v_i_616_, lean_object* v_k_617_){
_start:
{
uint8_t v___x_618_; 
v___x_618_ = lean_nat_dec_lt(v_k_617_, v_hi_613_);
if (v___x_618_ == 0)
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v_k_617_);
v___x_619_ = lean_array_fswap(v_as_615_, v_i_616_, v_hi_613_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v_i_616_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; uint8_t v___x_622_; 
v___x_621_ = lean_array_fget_borrowed(v_as_615_, v_k_617_);
v___x_622_ = lean_string_dec_lt(v___x_621_, v_pivot_614_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = lean_unsigned_to_nat(1u);
v___x_624_ = lean_nat_add(v_k_617_, v___x_623_);
lean_dec(v_k_617_);
v_k_617_ = v___x_624_;
goto _start;
}
else
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_626_ = lean_array_fswap(v_as_615_, v_i_616_, v_k_617_);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_i_616_, v___x_627_);
lean_dec(v_i_616_);
v___x_629_ = lean_nat_add(v_k_617_, v___x_627_);
lean_dec(v_k_617_);
v_as_615_ = v___x_626_;
v_i_616_ = v___x_628_;
v_k_617_ = v___x_629_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object* v_hi_631_, lean_object* v_pivot_632_, lean_object* v_as_633_, lean_object* v_i_634_, lean_object* v_k_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_631_, v_pivot_632_, v_as_633_, v_i_634_, v_k_635_);
lean_dec_ref(v_pivot_632_);
lean_dec(v_hi_631_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_n_637_, lean_object* v_as_638_, lean_object* v_lo_639_, lean_object* v_hi_640_){
_start:
{
lean_object* v___y_642_; uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_lt(v_lo_639_, v_hi_640_);
if (v___x_652_ == 0)
{
lean_dec(v_lo_639_);
return v_as_638_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v_mid_655_; lean_object* v___y_657_; lean_object* v___y_663_; lean_object* v___x_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v___x_653_ = lean_nat_add(v_lo_639_, v_hi_640_);
v___x_654_ = lean_unsigned_to_nat(1u);
v_mid_655_ = lean_nat_shiftr(v___x_653_, v___x_654_);
lean_dec(v___x_653_);
v___x_668_ = lean_array_fget_borrowed(v_as_638_, v_mid_655_);
v___x_669_ = lean_array_fget_borrowed(v_as_638_, v_lo_639_);
v___x_670_ = lean_string_dec_lt(v___x_668_, v___x_669_);
if (v___x_670_ == 0)
{
v___y_663_ = v_as_638_;
goto v___jp_662_;
}
else
{
lean_object* v___x_671_; 
v___x_671_ = lean_array_fswap(v_as_638_, v_lo_639_, v_mid_655_);
v___y_663_ = v___x_671_;
goto v___jp_662_;
}
v___jp_656_:
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_array_fget_borrowed(v___y_657_, v_mid_655_);
v___x_659_ = lean_array_fget_borrowed(v___y_657_, v_hi_640_);
v___x_660_ = lean_string_dec_lt(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_dec(v_mid_655_);
v___y_642_ = v___y_657_;
goto v___jp_641_;
}
else
{
lean_object* v___x_661_; 
v___x_661_ = lean_array_fswap(v___y_657_, v_mid_655_, v_hi_640_);
lean_dec(v_mid_655_);
v___y_642_ = v___x_661_;
goto v___jp_641_;
}
}
v___jp_662_:
{
lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v___x_664_ = lean_array_fget_borrowed(v___y_663_, v_hi_640_);
v___x_665_ = lean_array_fget_borrowed(v___y_663_, v_lo_639_);
v___x_666_ = lean_string_dec_lt(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
v___y_657_ = v___y_663_;
goto v___jp_656_;
}
else
{
lean_object* v___x_667_; 
v___x_667_ = lean_array_fswap(v___y_663_, v_lo_639_, v_hi_640_);
v___y_657_ = v___x_667_;
goto v___jp_656_;
}
}
}
v___jp_641_:
{
lean_object* v_pivot_643_; lean_object* v___x_644_; lean_object* v_fst_645_; lean_object* v_snd_646_; uint8_t v___x_647_; 
v_pivot_643_ = lean_array_fget(v___y_642_, v_hi_640_);
lean_inc_n(v_lo_639_, 2);
v___x_644_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_640_, v_pivot_643_, v___y_642_, v_lo_639_, v_lo_639_);
lean_dec(v_pivot_643_);
v_fst_645_ = lean_ctor_get(v___x_644_, 0);
lean_inc(v_fst_645_);
v_snd_646_ = lean_ctor_get(v___x_644_, 1);
lean_inc(v_snd_646_);
lean_dec_ref(v___x_644_);
v___x_647_ = lean_nat_dec_le(v_hi_640_, v_fst_645_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_637_, v_snd_646_, v_lo_639_, v_fst_645_);
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_fst_645_, v___x_649_);
lean_dec(v_fst_645_);
v_as_638_ = v___x_648_;
v_lo_639_ = v___x_650_;
goto _start;
}
else
{
lean_dec(v_fst_645_);
lean_dec(v_lo_639_);
return v_snd_646_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_n_672_, lean_object* v_as_673_, lean_object* v_lo_674_, lean_object* v_hi_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_672_, v_as_673_, v_lo_674_, v_hi_675_);
lean_dec(v_hi_675_);
lean_dec(v_n_672_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_679_){
_start:
{
lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v_unexpected_712_; lean_object* v_expected_713_; lean_object* v___y_715_; lean_object* v___x_725_; uint8_t v___x_726_; 
v_unexpected_712_ = lean_ctor_get(v_e_679_, 1);
lean_inc_ref(v_unexpected_712_);
v_expected_713_ = lean_ctor_get(v_e_679_, 2);
lean_inc(v_expected_713_);
lean_dec_ref(v_e_679_);
v___x_725_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_726_ = lean_string_dec_eq(v_unexpected_712_, v___x_725_);
if (v___x_726_ == 0)
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_box(0);
v___x_728_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_728_, 0, v_unexpected_712_);
lean_ctor_set(v___x_728_, 1, v___x_727_);
v___y_715_ = v___x_728_;
goto v___jp_714_;
}
else
{
lean_object* v___x_729_; 
lean_dec_ref(v_unexpected_712_);
v___x_729_ = lean_box(0);
v___y_715_ = v___x_729_;
goto v___jp_714_;
}
v___jp_680_:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_683_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_684_ = l_List_appendTR___redArg(v___y_681_, v___y_682_);
v___x_685_ = l_String_intercalate(v___x_683_, v___x_684_);
return v___x_685_;
}
v___jp_686_:
{
lean_object* v___x_690_; lean_object* v_expected_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_690_ = lean_array_to_list(v___y_689_);
v_expected_691_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_690_);
v___x_692_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_693_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_691_);
v___x_694_ = lean_string_append(v___x_692_, v___x_693_);
lean_dec_ref(v___x_693_);
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___y_688_);
v___y_681_ = v___y_687_;
v___y_682_ = v___x_695_;
goto v___jp_680_;
}
v___jp_696_:
{
lean_object* v___x_703_; 
v___x_703_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_699_, v___y_701_, v___y_700_, v___y_702_);
lean_dec(v___y_702_);
lean_dec(v___y_699_);
v___y_687_ = v___y_697_;
v___y_688_ = v___y_698_;
v___y_689_ = v___x_703_;
goto v___jp_686_;
}
v___jp_704_:
{
uint8_t v___x_711_; 
v___x_711_ = lean_nat_dec_le(v___y_710_, v___y_707_);
if (v___x_711_ == 0)
{
lean_dec(v___y_707_);
lean_inc(v___y_710_);
v___y_697_ = v___y_705_;
v___y_698_ = v___y_706_;
v___y_699_ = v___y_708_;
v___y_700_ = v___y_710_;
v___y_701_ = v___y_709_;
v___y_702_ = v___y_710_;
goto v___jp_696_;
}
else
{
v___y_697_ = v___y_705_;
v___y_698_ = v___y_706_;
v___y_699_ = v___y_708_;
v___y_700_ = v___y_710_;
v___y_701_ = v___y_709_;
v___y_702_ = v___y_707_;
goto v___jp_696_;
}
}
v___jp_714_:
{
lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_716_ = lean_box(0);
v___x_717_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_713_, v___x_716_);
if (v___x_717_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_718_ = lean_array_mk(v_expected_713_);
v___x_719_ = lean_array_get_size(v___x_718_);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_nat_dec_eq(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_object* v___x_722_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_722_ = lean_unsigned_to_nat(1u);
v___x_723_ = lean_nat_sub(v___x_719_, v___x_722_);
v___x_724_ = lean_nat_dec_le(v___x_720_, v___x_723_);
if (v___x_724_ == 0)
{
lean_inc(v___x_723_);
v___y_705_ = v___y_715_;
v___y_706_ = v___x_716_;
v___y_707_ = v___x_723_;
v___y_708_ = v___x_719_;
v___y_709_ = v___x_718_;
v___y_710_ = v___x_723_;
goto v___jp_704_;
}
else
{
v___y_705_ = v___y_715_;
v___y_706_ = v___x_716_;
v___y_707_ = v___x_723_;
v___y_708_ = v___x_719_;
v___y_709_ = v___x_718_;
v___y_710_ = v___x_720_;
goto v___jp_704_;
}
}
else
{
v___y_687_ = v___y_715_;
v___y_688_ = v___x_716_;
v___y_689_ = v___x_718_;
goto v___jp_686_;
}
}
else
{
lean_dec(v_expected_713_);
v___y_681_ = v___y_715_;
v___y_682_ = v___x_716_;
goto v___jp_680_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_730_, lean_object* v_as_731_, lean_object* v_lo_732_, lean_object* v_hi_733_, lean_object* v_w_734_, lean_object* v_hlo_735_, lean_object* v_hhi_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_730_, v_as_731_, v_lo_732_, v_hi_733_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_738_, lean_object* v_as_739_, lean_object* v_lo_740_, lean_object* v_hi_741_, lean_object* v_w_742_, lean_object* v_hlo_743_, lean_object* v_hhi_744_){
_start:
{
lean_object* v_res_745_; 
v_res_745_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_738_, v_as_739_, v_lo_740_, v_hi_741_, v_w_742_, v_hlo_743_, v_hhi_744_);
lean_dec(v_hi_741_);
lean_dec(v_n_738_);
return v_res_745_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object* v_n_746_, lean_object* v_lo_747_, lean_object* v_hi_748_, lean_object* v_hhi_749_, lean_object* v_pivot_750_, lean_object* v_as_751_, lean_object* v_i_752_, lean_object* v_k_753_, lean_object* v_ilo_754_, lean_object* v_ik_755_, lean_object* v_w_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_748_, v_pivot_750_, v_as_751_, v_i_752_, v_k_753_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object* v_n_758_, lean_object* v_lo_759_, lean_object* v_hi_760_, lean_object* v_hhi_761_, lean_object* v_pivot_762_, lean_object* v_as_763_, lean_object* v_i_764_, lean_object* v_k_765_, lean_object* v_ilo_766_, lean_object* v_ik_767_, lean_object* v_w_768_){
_start:
{
lean_object* v_res_769_; 
v_res_769_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_758_, v_lo_759_, v_hi_760_, v_hhi_761_, v_pivot_762_, v_as_763_, v_i_764_, v_k_765_, v_ilo_766_, v_ik_767_, v_w_768_);
lean_dec_ref(v_pivot_762_);
lean_dec(v_hi_760_);
lean_dec(v_lo_759_);
lean_dec(v_n_758_);
return v_res_769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_772_, lean_object* v_e_u2082_773_){
_start:
{
lean_object* v_unexpectedTk_774_; lean_object* v_unexpected_775_; lean_object* v_expected_776_; lean_object* v___y_778_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_unexpectedTk_774_ = lean_ctor_get(v_e_u2082_773_, 0);
lean_inc(v_unexpectedTk_774_);
v_unexpected_775_ = lean_ctor_get(v_e_u2082_773_, 1);
lean_inc_ref(v_unexpected_775_);
v_expected_776_ = lean_ctor_get(v_e_u2082_773_, 2);
lean_inc(v_expected_776_);
lean_dec_ref(v_e_u2082_773_);
v___x_790_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_791_ = lean_string_dec_eq(v_unexpected_775_, v___x_790_);
if (v___x_791_ == 0)
{
v___y_778_ = v_unexpected_775_;
goto v___jp_777_;
}
else
{
lean_object* v_unexpected_792_; 
lean_dec_ref(v_unexpected_775_);
v_unexpected_792_ = lean_ctor_get(v_e_u2081_772_, 1);
lean_inc_ref(v_unexpected_792_);
v___y_778_ = v_unexpected_792_;
goto v___jp_777_;
}
v___jp_777_:
{
lean_object* v_expected_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_787_; 
v_expected_779_ = lean_ctor_get(v_e_u2081_772_, 2);
v_isSharedCheck_787_ = !lean_is_exclusive(v_e_u2081_772_);
if (v_isSharedCheck_787_ == 0)
{
lean_object* v_unused_788_; lean_object* v_unused_789_; 
v_unused_788_ = lean_ctor_get(v_e_u2081_772_, 1);
lean_dec(v_unused_788_);
v_unused_789_ = lean_ctor_get(v_e_u2081_772_, 0);
lean_dec(v_unused_789_);
v___x_781_ = v_e_u2081_772_;
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_expected_779_);
lean_dec(v_e_u2081_772_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_787_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
v___x_783_ = l_List_appendTR___redArg(v_expected_779_, v_expected_776_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 2, v___x_783_);
lean_ctor_set(v___x_781_, 1, v___y_778_);
lean_ctor_set(v___x_781_, 0, v_unexpectedTk_774_);
v___x_785_ = v___x_781_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_786_; 
v_reuseFailAlloc_786_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_786_, 0, v_unexpectedTk_774_);
lean_ctor_set(v_reuseFailAlloc_786_, 1, v___y_778_);
lean_ctor_set(v_reuseFailAlloc_786_, 2, v___x_783_);
v___x_785_ = v_reuseFailAlloc_786_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
return v___x_785_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_793_, lean_object* v_x_794_){
_start:
{
lean_object* v_toCacheableParserContext_795_; lean_object* v_parserName_796_; lean_object* v_pos_797_; lean_object* v_toCacheableParserContext_798_; lean_object* v_parserName_799_; lean_object* v_pos_800_; uint8_t v___x_801_; 
v_toCacheableParserContext_795_ = lean_ctor_get(v_x_793_, 0);
v_parserName_796_ = lean_ctor_get(v_x_793_, 1);
v_pos_797_ = lean_ctor_get(v_x_793_, 2);
v_toCacheableParserContext_798_ = lean_ctor_get(v_x_794_, 0);
v_parserName_799_ = lean_ctor_get(v_x_794_, 1);
v_pos_800_ = lean_ctor_get(v_x_794_, 2);
v___x_801_ = l_Lean_Parser_instBEqCacheableParserContext_beq(v_toCacheableParserContext_795_, v_toCacheableParserContext_798_);
if (v___x_801_ == 0)
{
return v___x_801_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = lean_name_eq(v_parserName_796_, v_parserName_799_);
if (v___x_802_ == 0)
{
return v___x_802_;
}
else
{
uint8_t v___x_803_; 
v___x_803_ = lean_nat_dec_eq(v_pos_797_, v_pos_800_);
return v___x_803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object* v_x_804_, lean_object* v_x_805_){
_start:
{
uint8_t v_res_806_; lean_object* v_r_807_; 
v_res_806_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_804_, v_x_805_);
lean_dec_ref(v_x_805_);
lean_dec_ref(v_x_804_);
v_r_807_ = lean_box(v_res_806_);
return v_r_807_;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* v_k_810_){
_start:
{
lean_object* v_parserName_811_; lean_object* v_pos_812_; uint64_t v___x_813_; 
v_parserName_811_ = lean_ctor_get(v_k_810_, 1);
v_pos_812_ = lean_ctor_get(v_k_810_, 2);
v___x_813_ = l_String_instHashableRaw_hash(v_pos_812_);
if (lean_obj_tag(v_parserName_811_) == 0)
{
uint64_t v___x_814_; uint64_t v___x_815_; 
v___x_814_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_815_ = lean_uint64_mix_hash(v___x_813_, v___x_814_);
return v___x_815_;
}
else
{
uint64_t v_hash_816_; uint64_t v___x_817_; 
v_hash_816_ = lean_ctor_get_uint64(v_parserName_811_, sizeof(void*)*2);
v___x_817_ = lean_uint64_mix_hash(v___x_813_, v_hash_816_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* v_k_818_){
_start:
{
uint64_t v_res_819_; lean_object* v_r_820_; 
v_res_819_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_818_);
lean_dec_ref(v_k_818_);
v_r_820_ = lean_box_uint64(v_res_819_);
return v_r_820_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0(void){
_start:
{
uint32_t v___x_823_; lean_object* v___x_824_; 
v___x_823_ = 32;
v___x_824_ = l_Char_utf8Size(v___x_823_);
return v___x_824_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_box(0);
v___x_826_ = lean_unsigned_to_nat(16u);
v___x_827_ = lean_mk_array(v___x_826_, v___x_825_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__2(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_828_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_829_);
lean_ctor_set(v___x_830_, 1, v___x_828_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_831_){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_832_ = lean_string_utf8_byte_size(v_input_831_);
v___x_833_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_834_ = lean_nat_add(v___x_832_, v___x_833_);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_box(0);
v___x_837_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_837_, 0, v___x_834_);
lean_ctor_set(v___x_837_, 1, v___x_835_);
lean_ctor_set(v___x_837_, 2, v___x_836_);
v___x_838_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_837_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Parser_initCacheForInput(v_input_840_);
lean_dec_ref(v_input_840_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_842_){
_start:
{
lean_object* v_raw_843_; lean_object* v_drop_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_raw_843_ = lean_ctor_get(v_stack_842_, 0);
lean_inc_ref(v_raw_843_);
v_drop_844_ = lean_ctor_get(v_stack_842_, 1);
lean_inc(v_drop_844_);
lean_dec_ref(v_stack_842_);
v___x_845_ = lean_array_get_size(v_raw_843_);
v___x_846_ = l_Array_toSubarray___redArg(v_raw_843_, v_drop_844_, v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_853_){
_start:
{
lean_object* v_raw_854_; lean_object* v_drop_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_raw_854_ = lean_ctor_get(v_stack_853_, 0);
v_drop_855_ = lean_ctor_get(v_stack_853_, 1);
v___x_856_ = lean_array_get_size(v_raw_854_);
v___x_857_ = lean_nat_sub(v___x_856_, v_drop_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Parser_SyntaxStack_size(v_stack_858_);
lean_dec_ref(v_stack_858_);
return v_res_859_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_861_ = l_Lean_Parser_SyntaxStack_size(v_stack_860_);
v___x_862_ = lean_unsigned_to_nat(0u);
v___x_863_ = lean_nat_dec_eq(v___x_861_, v___x_862_);
lean_dec(v___x_861_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_864_){
_start:
{
uint8_t v_res_865_; lean_object* v_r_866_; 
v_res_865_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_864_);
lean_dec_ref(v_stack_864_);
v_r_866_ = lean_box(v_res_865_);
return v_r_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_867_, lean_object* v_n_868_){
_start:
{
lean_object* v_raw_869_; lean_object* v_drop_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_879_; 
v_raw_869_ = lean_ctor_get(v_stack_867_, 0);
v_drop_870_ = lean_ctor_get(v_stack_867_, 1);
v_isSharedCheck_879_ = !lean_is_exclusive(v_stack_867_);
if (v_isSharedCheck_879_ == 0)
{
v___x_872_ = v_stack_867_;
v_isShared_873_ = v_isSharedCheck_879_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_drop_870_);
lean_inc(v_raw_869_);
lean_dec(v_stack_867_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_879_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_877_; 
v___x_874_ = lean_nat_add(v_drop_870_, v_n_868_);
v___x_875_ = l_Array_shrink___redArg(v_raw_869_, v___x_874_);
lean_dec(v___x_874_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_875_);
v___x_877_ = v___x_872_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_878_, 1, v_drop_870_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_880_, lean_object* v_n_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_880_, v_n_881_);
lean_dec(v_n_881_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_raw_885_; lean_object* v_drop_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_894_; 
v_raw_885_ = lean_ctor_get(v_stack_883_, 0);
v_drop_886_ = lean_ctor_get(v_stack_883_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_stack_883_);
if (v_isSharedCheck_894_ == 0)
{
v___x_888_ = v_stack_883_;
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_drop_886_);
lean_inc(v_raw_885_);
lean_dec(v_stack_883_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_array_push(v_raw_885_, v_a_884_);
if (v_isShared_889_ == 0)
{
lean_ctor_set(v___x_888_, 0, v___x_890_);
v___x_892_ = v___x_888_;
goto v_reusejp_891_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_890_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v_drop_886_);
v___x_892_ = v_reuseFailAlloc_893_;
goto v_reusejp_891_;
}
v_reusejp_891_:
{
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_895_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = l_Lean_Parser_SyntaxStack_size(v_stack_895_);
v___x_898_ = lean_nat_dec_lt(v___x_896_, v___x_897_);
lean_dec(v___x_897_);
if (v___x_898_ == 0)
{
return v_stack_895_;
}
else
{
lean_object* v_raw_899_; lean_object* v_drop_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_908_; 
v_raw_899_ = lean_ctor_get(v_stack_895_, 0);
v_drop_900_ = lean_ctor_get(v_stack_895_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_stack_895_);
if (v_isSharedCheck_908_ == 0)
{
v___x_902_ = v_stack_895_;
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_drop_900_);
lean_inc(v_raw_899_);
lean_dec(v_stack_895_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_908_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_904_; lean_object* v___x_906_; 
v___x_904_ = lean_array_pop(v_raw_899_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_904_);
v___x_906_ = v___x_902_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_907_; 
v_reuseFailAlloc_907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
lean_ctor_set(v_reuseFailAlloc_907_, 1, v_drop_900_);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_909_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_box(0);
v___x_911_ = lean_panic_fn_borrowed(v___x_910_, v_msg_909_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_915_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_916_ = lean_unsigned_to_nat(4u);
v___x_917_ = lean_unsigned_to_nat(305u);
v___x_918_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_919_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_920_ = l_mkPanicMessageWithDecl(v___x_919_, v___x_918_, v___x_917_, v___x_916_, v___x_915_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_921_){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v___x_922_ = lean_unsigned_to_nat(0u);
v___x_923_ = l_Lean_Parser_SyntaxStack_size(v_stack_921_);
v___x_924_ = lean_nat_dec_lt(v___x_922_, v___x_923_);
lean_dec(v___x_923_);
if (v___x_924_ == 0)
{
lean_object* v___x_925_; lean_object* v___x_926_; 
v___x_925_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_926_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_925_);
return v___x_926_;
}
else
{
lean_object* v_raw_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v_raw_927_ = lean_ctor_get(v_stack_921_, 0);
v___x_928_ = lean_box(0);
v___x_929_ = lean_array_get_size(v_raw_927_);
v___x_930_ = lean_unsigned_to_nat(1u);
v___x_931_ = lean_nat_sub(v___x_929_, v___x_930_);
v___x_932_ = lean_array_get_borrowed(v___x_928_, v_raw_927_, v___x_931_);
lean_dec(v___x_931_);
lean_inc(v___x_932_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l_Lean_Parser_SyntaxStack_back(v_stack_933_);
lean_dec_ref(v_stack_933_);
return v_res_934_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; 
v___x_937_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_938_ = lean_unsigned_to_nat(4u);
v___x_939_ = lean_unsigned_to_nat(311u);
v___x_940_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_941_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_942_ = l_mkPanicMessageWithDecl(v___x_941_, v___x_940_, v___x_939_, v___x_938_, v___x_937_);
return v___x_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_943_, lean_object* v_i_944_){
_start:
{
lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_945_ = l_Lean_Parser_SyntaxStack_size(v_stack_943_);
v___x_946_ = lean_nat_dec_lt(v_i_944_, v___x_945_);
lean_dec(v___x_945_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_947_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_948_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_947_);
return v___x_948_;
}
else
{
lean_object* v_raw_949_; lean_object* v_drop_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; 
v_raw_949_ = lean_ctor_get(v_stack_943_, 0);
v_drop_950_ = lean_ctor_get(v_stack_943_, 1);
v___x_951_ = lean_box(0);
v___x_952_ = lean_nat_add(v_drop_950_, v_i_944_);
v___x_953_ = lean_array_get_borrowed(v___x_951_, v_raw_949_, v___x_952_);
lean_dec(v___x_952_);
lean_inc(v___x_953_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_954_, lean_object* v_i_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_954_, v_i_955_);
lean_dec(v_i_955_);
lean_dec_ref(v_stack_954_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_957_, lean_object* v_start_958_, lean_object* v_stop_959_){
_start:
{
lean_object* v_raw_960_; lean_object* v_drop_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_raw_960_ = lean_ctor_get(v_stack_957_, 0);
v_drop_961_ = lean_ctor_get(v_stack_957_, 1);
v___x_962_ = lean_nat_add(v_drop_961_, v_start_958_);
v___x_963_ = lean_nat_add(v_drop_961_, v_stop_959_);
v___x_964_ = l_Array_extract___redArg(v_raw_960_, v___x_962_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_965_, lean_object* v_start_966_, lean_object* v_stop_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Parser_SyntaxStack_extract(v_stack_965_, v_start_966_, v_stop_967_);
lean_dec(v_stop_967_);
lean_dec(v_start_966_);
lean_dec_ref(v_stack_965_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_969_, lean_object* v_stxs_970_){
_start:
{
lean_object* v_raw_971_; lean_object* v_drop_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_980_; 
v_raw_971_ = lean_ctor_get(v_stack_969_, 0);
v_drop_972_ = lean_ctor_get(v_stack_969_, 1);
v_isSharedCheck_980_ = !lean_is_exclusive(v_stack_969_);
if (v_isSharedCheck_980_ == 0)
{
v___x_974_ = v_stack_969_;
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_drop_972_);
lean_inc(v_raw_971_);
lean_dec(v_stack_969_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_980_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; lean_object* v___x_978_; 
v___x_976_ = l_Array_append___redArg(v_raw_971_, v_stxs_970_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_976_);
v___x_978_ = v___x_974_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v___x_976_);
lean_ctor_set(v_reuseFailAlloc_979_, 1, v_drop_972_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_981_, lean_object* v_stxs_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_981_, v_stxs_982_);
lean_dec_ref(v_stxs_982_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_984_, lean_object* v_stxs_985_){
_start:
{
lean_object* v_raw_986_; lean_object* v_drop_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_995_; 
v_raw_986_ = lean_ctor_get(v_stack_984_, 0);
v_drop_987_ = lean_ctor_get(v_stack_984_, 1);
v_isSharedCheck_995_ = !lean_is_exclusive(v_stack_984_);
if (v_isSharedCheck_995_ == 0)
{
v___x_989_ = v_stack_984_;
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_drop_987_);
lean_inc(v_raw_986_);
lean_dec(v_stack_984_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_995_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Array_append___redArg(v_raw_986_, v_stxs_985_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 0, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_994_, 1, v_drop_987_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_996_, lean_object* v_stxs_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_996_, v_stxs_997_);
lean_dec_ref(v_stxs_997_);
return v_res_998_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_1001_){
_start:
{
lean_object* v_errorMsg_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v_errorMsg_1002_ = lean_ctor_get(v_s_1001_, 4);
lean_inc(v_errorMsg_1002_);
lean_dec_ref(v_s_1001_);
v___x_1003_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_1004_ = lean_box(0);
v___x_1005_ = l_Option_instBEq_beq___redArg(v___x_1003_, v_errorMsg_1002_, v___x_1004_);
if (v___x_1005_ == 0)
{
uint8_t v___x_1006_; 
v___x_1006_ = 1;
return v___x_1006_;
}
else
{
uint8_t v___x_1007_; 
v___x_1007_ = 0;
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Lean_Parser_ParserState_hasError(v_s_1008_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_1011_){
_start:
{
lean_object* v_stxStack_1012_; lean_object* v___x_1013_; 
v_stxStack_1012_ = lean_ctor_get(v_s_1011_, 0);
v___x_1013_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Parser_ParserState_stackSize(v_s_1014_);
lean_dec_ref(v_s_1014_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_1016_, lean_object* v_iniStackSz_1017_, lean_object* v_iniPos_1018_){
_start:
{
lean_object* v_stxStack_1019_; lean_object* v_lhsPrec_1020_; lean_object* v_cache_1021_; lean_object* v_recoveredErrors_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1031_; 
v_stxStack_1019_ = lean_ctor_get(v_s_1016_, 0);
v_lhsPrec_1020_ = lean_ctor_get(v_s_1016_, 1);
v_cache_1021_ = lean_ctor_get(v_s_1016_, 3);
v_recoveredErrors_1022_ = lean_ctor_get(v_s_1016_, 5);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_s_1016_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; lean_object* v_unused_1033_; 
v_unused_1032_ = lean_ctor_get(v_s_1016_, 4);
lean_dec(v_unused_1032_);
v_unused_1033_ = lean_ctor_get(v_s_1016_, 2);
lean_dec(v_unused_1033_);
v___x_1024_ = v_s_1016_;
v_isShared_1025_ = v_isSharedCheck_1031_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_recoveredErrors_1022_);
lean_inc(v_cache_1021_);
lean_inc(v_lhsPrec_1020_);
lean_inc(v_stxStack_1019_);
lean_dec(v_s_1016_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1031_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1029_; 
v___x_1026_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1019_, v_iniStackSz_1017_);
v___x_1027_ = lean_box(0);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 4, v___x_1027_);
lean_ctor_set(v___x_1024_, 2, v_iniPos_1018_);
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1029_ = v___x_1024_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_lhsPrec_1020_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_iniPos_1018_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_cache_1021_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v___x_1027_);
lean_ctor_set(v_reuseFailAlloc_1030_, 5, v_recoveredErrors_1022_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_1034_, lean_object* v_iniStackSz_1035_, lean_object* v_iniPos_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Parser_ParserState_restore(v_s_1034_, v_iniStackSz_1035_, v_iniPos_1036_);
lean_dec(v_iniStackSz_1035_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_1038_, lean_object* v_pos_1039_){
_start:
{
lean_object* v_stxStack_1040_; lean_object* v_lhsPrec_1041_; lean_object* v_cache_1042_; lean_object* v_errorMsg_1043_; lean_object* v_recoveredErrors_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
v_stxStack_1040_ = lean_ctor_get(v_s_1038_, 0);
v_lhsPrec_1041_ = lean_ctor_get(v_s_1038_, 1);
v_cache_1042_ = lean_ctor_get(v_s_1038_, 3);
v_errorMsg_1043_ = lean_ctor_get(v_s_1038_, 4);
v_recoveredErrors_1044_ = lean_ctor_get(v_s_1038_, 5);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_s_1038_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v_s_1038_, 2);
lean_dec(v_unused_1052_);
v___x_1046_ = v_s_1038_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_recoveredErrors_1044_);
lean_inc(v_errorMsg_1043_);
lean_inc(v_cache_1042_);
lean_inc(v_lhsPrec_1041_);
lean_inc(v_stxStack_1040_);
lean_dec(v_s_1038_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 2, v_pos_1039_);
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_stxStack_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_lhsPrec_1041_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v_pos_1039_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_cache_1042_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_errorMsg_1043_);
lean_ctor_set(v_reuseFailAlloc_1050_, 5, v_recoveredErrors_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_1053_, lean_object* v_cache_1054_){
_start:
{
lean_object* v_stxStack_1055_; lean_object* v_lhsPrec_1056_; lean_object* v_pos_1057_; lean_object* v_errorMsg_1058_; lean_object* v_recoveredErrors_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
v_stxStack_1055_ = lean_ctor_get(v_s_1053_, 0);
v_lhsPrec_1056_ = lean_ctor_get(v_s_1053_, 1);
v_pos_1057_ = lean_ctor_get(v_s_1053_, 2);
v_errorMsg_1058_ = lean_ctor_get(v_s_1053_, 4);
v_recoveredErrors_1059_ = lean_ctor_get(v_s_1053_, 5);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_s_1053_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v_s_1053_, 3);
lean_dec(v_unused_1067_);
v___x_1061_ = v_s_1053_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_recoveredErrors_1059_);
lean_inc(v_errorMsg_1058_);
lean_inc(v_pos_1057_);
lean_inc(v_lhsPrec_1056_);
lean_inc(v_stxStack_1055_);
lean_dec(v_s_1053_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 3, v_cache_1054_);
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_stxStack_1055_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_lhsPrec_1056_);
lean_ctor_set(v_reuseFailAlloc_1065_, 2, v_pos_1057_);
lean_ctor_set(v_reuseFailAlloc_1065_, 3, v_cache_1054_);
lean_ctor_set(v_reuseFailAlloc_1065_, 4, v_errorMsg_1058_);
lean_ctor_set(v_reuseFailAlloc_1065_, 5, v_recoveredErrors_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_1068_, lean_object* v_n_1069_){
_start:
{
lean_object* v_stxStack_1070_; lean_object* v_lhsPrec_1071_; lean_object* v_pos_1072_; lean_object* v_cache_1073_; lean_object* v_errorMsg_1074_; lean_object* v_recoveredErrors_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1083_; 
v_stxStack_1070_ = lean_ctor_get(v_s_1068_, 0);
v_lhsPrec_1071_ = lean_ctor_get(v_s_1068_, 1);
v_pos_1072_ = lean_ctor_get(v_s_1068_, 2);
v_cache_1073_ = lean_ctor_get(v_s_1068_, 3);
v_errorMsg_1074_ = lean_ctor_get(v_s_1068_, 4);
v_recoveredErrors_1075_ = lean_ctor_get(v_s_1068_, 5);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_s_1068_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1077_ = v_s_1068_;
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_recoveredErrors_1075_);
lean_inc(v_errorMsg_1074_);
lean_inc(v_cache_1073_);
lean_inc(v_pos_1072_);
lean_inc(v_lhsPrec_1071_);
lean_inc(v_stxStack_1070_);
lean_dec(v_s_1068_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1083_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; lean_object* v___x_1081_; 
v___x_1079_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1070_, v_n_1069_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 0, v___x_1079_);
v___x_1081_ = v___x_1077_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_lhsPrec_1071_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_pos_1072_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_cache_1073_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v_errorMsg_1074_);
lean_ctor_set(v_reuseFailAlloc_1082_, 5, v_recoveredErrors_1075_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1084_){
_start:
{
lean_object* v_stxStack_1085_; lean_object* v_lhsPrec_1086_; lean_object* v_pos_1087_; lean_object* v_cache_1088_; lean_object* v_errorMsg_1089_; lean_object* v_recoveredErrors_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1098_; 
v_stxStack_1085_ = lean_ctor_get(v_s_1084_, 0);
v_lhsPrec_1086_ = lean_ctor_get(v_s_1084_, 1);
v_pos_1087_ = lean_ctor_get(v_s_1084_, 2);
v_cache_1088_ = lean_ctor_get(v_s_1084_, 3);
v_errorMsg_1089_ = lean_ctor_get(v_s_1084_, 4);
v_recoveredErrors_1090_ = lean_ctor_get(v_s_1084_, 5);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_s_1084_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1092_ = v_s_1084_;
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_recoveredErrors_1090_);
lean_inc(v_errorMsg_1089_);
lean_inc(v_cache_1088_);
lean_inc(v_pos_1087_);
lean_inc(v_lhsPrec_1086_);
lean_inc(v_stxStack_1085_);
lean_dec(v_s_1084_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1085_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_lhsPrec_1086_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_pos_1087_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_cache_1088_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_errorMsg_1089_);
lean_ctor_set(v_reuseFailAlloc_1097_, 5, v_recoveredErrors_1090_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1099_, lean_object* v_iniStackSz_1100_){
_start:
{
lean_object* v_stxStack_1101_; lean_object* v_lhsPrec_1102_; lean_object* v_pos_1103_; lean_object* v_cache_1104_; lean_object* v_errorMsg_1105_; lean_object* v_recoveredErrors_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1114_; 
v_stxStack_1101_ = lean_ctor_get(v_s_1099_, 0);
v_lhsPrec_1102_ = lean_ctor_get(v_s_1099_, 1);
v_pos_1103_ = lean_ctor_get(v_s_1099_, 2);
v_cache_1104_ = lean_ctor_get(v_s_1099_, 3);
v_errorMsg_1105_ = lean_ctor_get(v_s_1099_, 4);
v_recoveredErrors_1106_ = lean_ctor_get(v_s_1099_, 5);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_s_1099_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1108_ = v_s_1099_;
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_recoveredErrors_1106_);
lean_inc(v_errorMsg_1105_);
lean_inc(v_cache_1104_);
lean_inc(v_pos_1103_);
lean_inc(v_lhsPrec_1102_);
lean_inc(v_stxStack_1101_);
lean_dec(v_s_1099_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1114_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1110_; lean_object* v___x_1112_; 
v___x_1110_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1101_, v_iniStackSz_1100_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v___x_1110_);
v___x_1112_ = v___x_1108_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_lhsPrec_1102_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_pos_1103_);
lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_cache_1104_);
lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_errorMsg_1105_);
lean_ctor_set(v_reuseFailAlloc_1113_, 5, v_recoveredErrors_1106_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1115_, lean_object* v_iniStackSz_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1115_, v_iniStackSz_1116_);
lean_dec(v_iniStackSz_1116_);
return v_res_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1118_, lean_object* v_c_1119_, lean_object* v_pos_1120_){
_start:
{
lean_object* v_toInputContext_1121_; lean_object* v_stxStack_1122_; lean_object* v_lhsPrec_1123_; lean_object* v_cache_1124_; lean_object* v_errorMsg_1125_; lean_object* v_recoveredErrors_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1135_; 
v_toInputContext_1121_ = lean_ctor_get(v_c_1119_, 0);
v_stxStack_1122_ = lean_ctor_get(v_s_1118_, 0);
v_lhsPrec_1123_ = lean_ctor_get(v_s_1118_, 1);
v_cache_1124_ = lean_ctor_get(v_s_1118_, 3);
v_errorMsg_1125_ = lean_ctor_get(v_s_1118_, 4);
v_recoveredErrors_1126_ = lean_ctor_get(v_s_1118_, 5);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_s_1118_);
if (v_isSharedCheck_1135_ == 0)
{
lean_object* v_unused_1136_; 
v_unused_1136_ = lean_ctor_get(v_s_1118_, 2);
lean_dec(v_unused_1136_);
v___x_1128_ = v_s_1118_;
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_recoveredErrors_1126_);
lean_inc(v_errorMsg_1125_);
lean_inc(v_cache_1124_);
lean_inc(v_lhsPrec_1123_);
lean_inc(v_stxStack_1122_);
lean_dec(v_s_1118_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1135_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v_inputString_1130_; lean_object* v___x_1131_; lean_object* v___x_1133_; 
v_inputString_1130_ = lean_ctor_get(v_toInputContext_1121_, 0);
v___x_1131_ = lean_string_utf8_next(v_inputString_1130_, v_pos_1120_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 2, v___x_1131_);
v___x_1133_ = v___x_1128_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_stxStack_1122_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_lhsPrec_1123_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v___x_1131_);
lean_ctor_set(v_reuseFailAlloc_1134_, 3, v_cache_1124_);
lean_ctor_set(v_reuseFailAlloc_1134_, 4, v_errorMsg_1125_);
lean_ctor_set(v_reuseFailAlloc_1134_, 5, v_recoveredErrors_1126_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1137_, lean_object* v_c_1138_, lean_object* v_pos_1139_){
_start:
{
lean_object* v_res_1140_; 
v_res_1140_ = l_Lean_Parser_ParserState_next(v_s_1137_, v_c_1138_, v_pos_1139_);
lean_dec(v_pos_1139_);
lean_dec_ref(v_c_1138_);
return v_res_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1141_, lean_object* v_c_1142_, lean_object* v_pos_1143_){
_start:
{
lean_object* v_toInputContext_1144_; lean_object* v_stxStack_1145_; lean_object* v_lhsPrec_1146_; lean_object* v_cache_1147_; lean_object* v_errorMsg_1148_; lean_object* v_recoveredErrors_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1158_; 
v_toInputContext_1144_ = lean_ctor_get(v_c_1142_, 0);
v_stxStack_1145_ = lean_ctor_get(v_s_1141_, 0);
v_lhsPrec_1146_ = lean_ctor_get(v_s_1141_, 1);
v_cache_1147_ = lean_ctor_get(v_s_1141_, 3);
v_errorMsg_1148_ = lean_ctor_get(v_s_1141_, 4);
v_recoveredErrors_1149_ = lean_ctor_get(v_s_1141_, 5);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_s_1141_);
if (v_isSharedCheck_1158_ == 0)
{
lean_object* v_unused_1159_; 
v_unused_1159_ = lean_ctor_get(v_s_1141_, 2);
lean_dec(v_unused_1159_);
v___x_1151_ = v_s_1141_;
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_recoveredErrors_1149_);
lean_inc(v_errorMsg_1148_);
lean_inc(v_cache_1147_);
lean_inc(v_lhsPrec_1146_);
lean_inc(v_stxStack_1145_);
lean_dec(v_s_1141_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_inputString_1153_; lean_object* v___x_1154_; lean_object* v___x_1156_; 
v_inputString_1153_ = lean_ctor_get(v_toInputContext_1144_, 0);
v___x_1154_ = lean_string_utf8_next_fast(v_inputString_1153_, v_pos_1143_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 2, v___x_1154_);
v___x_1156_ = v___x_1151_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_stxStack_1145_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_lhsPrec_1146_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v___x_1154_);
lean_ctor_set(v_reuseFailAlloc_1157_, 3, v_cache_1147_);
lean_ctor_set(v_reuseFailAlloc_1157_, 4, v_errorMsg_1148_);
lean_ctor_set(v_reuseFailAlloc_1157_, 5, v_recoveredErrors_1149_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1160_, lean_object* v_c_1161_, lean_object* v_pos_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1160_, v_c_1161_, v_pos_1162_);
lean_dec(v_pos_1162_);
lean_dec_ref(v_c_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1164_, lean_object* v_c_1165_, lean_object* v_pos_1166_, lean_object* v_h_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1164_, v_c_1165_, v_pos_1166_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1169_, lean_object* v_c_1170_, lean_object* v_pos_1171_, lean_object* v_h_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Parser_ParserState_next_x27(v_s_1169_, v_c_1170_, v_pos_1171_, v_h_1172_);
lean_dec(v_pos_1171_);
lean_dec_ref(v_c_1170_);
return v_res_1173_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
if (lean_obj_tag(v_x_1174_) == 0)
{
if (lean_obj_tag(v_x_1175_) == 0)
{
uint8_t v___x_1176_; 
v___x_1176_ = 1;
return v___x_1176_;
}
else
{
uint8_t v___x_1177_; 
v___x_1177_ = 0;
return v___x_1177_;
}
}
else
{
if (lean_obj_tag(v_x_1175_) == 0)
{
uint8_t v___x_1178_; 
v___x_1178_ = 0;
return v___x_1178_;
}
else
{
lean_object* v_val_1179_; lean_object* v_val_1180_; uint8_t v___x_1181_; 
v_val_1179_ = lean_ctor_get(v_x_1174_, 0);
v_val_1180_ = lean_ctor_get(v_x_1175_, 0);
v___x_1181_ = l_Lean_Parser_instBEqError_beq(v_val_1179_, v_val_1180_);
return v___x_1181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1182_, lean_object* v_x_1183_){
_start:
{
uint8_t v_res_1184_; lean_object* v_r_1185_; 
v_res_1184_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1182_, v_x_1183_);
lean_dec(v_x_1183_);
lean_dec(v_x_1182_);
v_r_1185_ = lean_box(v_res_1184_);
return v_r_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1186_, lean_object* v_k_1187_, lean_object* v_iniStackSz_1188_){
_start:
{
lean_object* v_stxStack_1189_; lean_object* v_lhsPrec_1190_; lean_object* v_pos_1191_; lean_object* v_cache_1192_; lean_object* v_errorMsg_1193_; lean_object* v_recoveredErrors_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1215_; 
v_stxStack_1189_ = lean_ctor_get(v_s_1186_, 0);
v_lhsPrec_1190_ = lean_ctor_get(v_s_1186_, 1);
v_pos_1191_ = lean_ctor_get(v_s_1186_, 2);
v_cache_1192_ = lean_ctor_get(v_s_1186_, 3);
v_errorMsg_1193_ = lean_ctor_get(v_s_1186_, 4);
v_recoveredErrors_1194_ = lean_ctor_get(v_s_1186_, 5);
v_isSharedCheck_1215_ = !lean_is_exclusive(v_s_1186_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1196_ = v_s_1186_;
v_isShared_1197_ = v_isSharedCheck_1215_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_recoveredErrors_1194_);
lean_inc(v_errorMsg_1193_);
lean_inc(v_cache_1192_);
lean_inc(v_pos_1191_);
lean_inc(v_lhsPrec_1190_);
lean_inc(v_stxStack_1189_);
lean_dec(v_s_1186_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1215_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = lean_box(0);
v___x_1209_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1193_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1189_);
v___x_1211_ = lean_nat_dec_eq(v___x_1210_, v_iniStackSz_1188_);
lean_dec(v___x_1210_);
if (v___x_1211_ == 0)
{
goto v___jp_1198_;
}
else
{
lean_object* v___x_1212_; lean_object* v_stack_1213_; lean_object* v___x_1214_; 
lean_del_object(v___x_1196_);
lean_dec(v_k_1187_);
v___x_1212_ = lean_box(0);
v_stack_1213_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1189_, v___x_1212_);
v___x_1214_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1214_, 0, v_stack_1213_);
lean_ctor_set(v___x_1214_, 1, v_lhsPrec_1190_);
lean_ctor_set(v___x_1214_, 2, v_pos_1191_);
lean_ctor_set(v___x_1214_, 3, v_cache_1192_);
lean_ctor_set(v___x_1214_, 4, v_errorMsg_1193_);
lean_ctor_set(v___x_1214_, 5, v_recoveredErrors_1194_);
return v___x_1214_;
}
}
else
{
goto v___jp_1198_;
}
v___jp_1198_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v_newNode_1202_; lean_object* v_stack_1203_; lean_object* v_stack_1204_; lean_object* v___x_1206_; 
v___x_1199_ = lean_box(2);
v___x_1200_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1189_);
v___x_1201_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1189_, v_iniStackSz_1188_, v___x_1200_);
lean_dec(v___x_1200_);
v_newNode_1202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1202_, 0, v___x_1199_);
lean_ctor_set(v_newNode_1202_, 1, v_k_1187_);
lean_ctor_set(v_newNode_1202_, 2, v___x_1201_);
v_stack_1203_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1189_, v_iniStackSz_1188_);
v_stack_1204_ = l_Lean_Parser_SyntaxStack_push(v_stack_1203_, v_newNode_1202_);
if (v_isShared_1197_ == 0)
{
lean_ctor_set(v___x_1196_, 0, v_stack_1204_);
v___x_1206_ = v___x_1196_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_stack_1204_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_lhsPrec_1190_);
lean_ctor_set(v_reuseFailAlloc_1207_, 2, v_pos_1191_);
lean_ctor_set(v_reuseFailAlloc_1207_, 3, v_cache_1192_);
lean_ctor_set(v_reuseFailAlloc_1207_, 4, v_errorMsg_1193_);
lean_ctor_set(v_reuseFailAlloc_1207_, 5, v_recoveredErrors_1194_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1216_, lean_object* v_k_1217_, lean_object* v_iniStackSz_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Lean_Parser_ParserState_mkNode(v_s_1216_, v_k_1217_, v_iniStackSz_1218_);
lean_dec(v_iniStackSz_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1220_, lean_object* v_k_1221_, lean_object* v_iniStackSz_1222_){
_start:
{
lean_object* v_stxStack_1223_; lean_object* v_lhsPrec_1224_; lean_object* v_pos_1225_; lean_object* v_cache_1226_; lean_object* v_errorMsg_1227_; lean_object* v_recoveredErrors_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1243_; 
v_stxStack_1223_ = lean_ctor_get(v_s_1220_, 0);
v_lhsPrec_1224_ = lean_ctor_get(v_s_1220_, 1);
v_pos_1225_ = lean_ctor_get(v_s_1220_, 2);
v_cache_1226_ = lean_ctor_get(v_s_1220_, 3);
v_errorMsg_1227_ = lean_ctor_get(v_s_1220_, 4);
v_recoveredErrors_1228_ = lean_ctor_get(v_s_1220_, 5);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_s_1220_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1230_ = v_s_1220_;
v_isShared_1231_ = v_isSharedCheck_1243_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_recoveredErrors_1228_);
lean_inc(v_errorMsg_1227_);
lean_inc(v_cache_1226_);
lean_inc(v_pos_1225_);
lean_inc(v_lhsPrec_1224_);
lean_inc(v_stxStack_1223_);
lean_dec(v_s_1220_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1243_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v_newNode_1237_; lean_object* v_stack_1238_; lean_object* v_stack_1239_; lean_object* v___x_1241_; 
v___x_1232_ = lean_box(2);
v___x_1233_ = lean_unsigned_to_nat(1u);
v___x_1234_ = lean_nat_sub(v_iniStackSz_1222_, v___x_1233_);
v___x_1235_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1223_);
v___x_1236_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1223_, v___x_1234_, v___x_1235_);
lean_dec(v___x_1235_);
v_newNode_1237_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1237_, 0, v___x_1232_);
lean_ctor_set(v_newNode_1237_, 1, v_k_1221_);
lean_ctor_set(v_newNode_1237_, 2, v___x_1236_);
v_stack_1238_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1223_, v___x_1234_);
lean_dec(v___x_1234_);
v_stack_1239_ = l_Lean_Parser_SyntaxStack_push(v_stack_1238_, v_newNode_1237_);
if (v_isShared_1231_ == 0)
{
lean_ctor_set(v___x_1230_, 0, v_stack_1239_);
v___x_1241_ = v___x_1230_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_stack_1239_);
lean_ctor_set(v_reuseFailAlloc_1242_, 1, v_lhsPrec_1224_);
lean_ctor_set(v_reuseFailAlloc_1242_, 2, v_pos_1225_);
lean_ctor_set(v_reuseFailAlloc_1242_, 3, v_cache_1226_);
lean_ctor_set(v_reuseFailAlloc_1242_, 4, v_errorMsg_1227_);
lean_ctor_set(v_reuseFailAlloc_1242_, 5, v_recoveredErrors_1228_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1244_, lean_object* v_k_1245_, lean_object* v_iniStackSz_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1244_, v_k_1245_, v_iniStackSz_1246_);
lean_dec(v_iniStackSz_1246_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1250_){
_start:
{
lean_object* v_errorMsg_1251_; 
v_errorMsg_1251_ = lean_ctor_get(v_s_1250_, 4);
if (lean_obj_tag(v_errorMsg_1251_) == 0)
{
lean_object* v_recoveredErrors_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
v_recoveredErrors_1252_ = lean_ctor_get(v_s_1250_, 5);
lean_inc_ref(v_recoveredErrors_1252_);
lean_dec_ref(v_s_1250_);
v___x_1253_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1254_ = l_Array_append___redArg(v_recoveredErrors_1252_, v___x_1253_);
return v___x_1254_;
}
else
{
lean_object* v_stxStack_1255_; lean_object* v_pos_1256_; lean_object* v_recoveredErrors_1257_; lean_object* v_val_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_inc_ref(v_errorMsg_1251_);
v_stxStack_1255_ = lean_ctor_get(v_s_1250_, 0);
lean_inc_ref(v_stxStack_1255_);
v_pos_1256_ = lean_ctor_get(v_s_1250_, 2);
lean_inc(v_pos_1256_);
v_recoveredErrors_1257_ = lean_ctor_get(v_s_1250_, 5);
lean_inc_ref(v_recoveredErrors_1257_);
lean_dec_ref(v_s_1250_);
v_val_1258_ = lean_ctor_get(v_errorMsg_1251_, 0);
lean_inc(v_val_1258_);
lean_dec_ref_known(v_errorMsg_1251_, 1);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_stxStack_1255_);
lean_ctor_set(v___x_1259_, 1, v_val_1258_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_pos_1256_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = lean_mk_empty_array_with_capacity(v___x_1261_);
v___x_1263_ = lean_array_push(v___x_1262_, v___x_1260_);
v___x_1264_ = l_Array_append___redArg(v_recoveredErrors_1257_, v___x_1263_);
lean_dec_ref(v___x_1263_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1265_, lean_object* v_e_1266_){
_start:
{
lean_object* v_stxStack_1267_; lean_object* v_lhsPrec_1268_; lean_object* v_pos_1269_; lean_object* v_cache_1270_; lean_object* v_recoveredErrors_1271_; lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1279_; 
v_stxStack_1267_ = lean_ctor_get(v_s_1265_, 0);
v_lhsPrec_1268_ = lean_ctor_get(v_s_1265_, 1);
v_pos_1269_ = lean_ctor_get(v_s_1265_, 2);
v_cache_1270_ = lean_ctor_get(v_s_1265_, 3);
v_recoveredErrors_1271_ = lean_ctor_get(v_s_1265_, 5);
v_isSharedCheck_1279_ = !lean_is_exclusive(v_s_1265_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v_s_1265_, 4);
lean_dec(v_unused_1280_);
v___x_1273_ = v_s_1265_;
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
else
{
lean_inc(v_recoveredErrors_1271_);
lean_inc(v_cache_1270_);
lean_inc(v_pos_1269_);
lean_inc(v_lhsPrec_1268_);
lean_inc(v_stxStack_1267_);
lean_dec(v_s_1265_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1275_, 0, v_e_1266_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 4, v___x_1275_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_stxStack_1267_);
lean_ctor_set(v_reuseFailAlloc_1278_, 1, v_lhsPrec_1268_);
lean_ctor_set(v_reuseFailAlloc_1278_, 2, v_pos_1269_);
lean_ctor_set(v_reuseFailAlloc_1278_, 3, v_cache_1270_);
lean_ctor_set(v_reuseFailAlloc_1278_, 4, v___x_1275_);
lean_ctor_set(v_reuseFailAlloc_1278_, 5, v_recoveredErrors_1271_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1281_, lean_object* v_msg_1282_){
_start:
{
lean_object* v_stxStack_1283_; lean_object* v_lhsPrec_1284_; lean_object* v_pos_1285_; lean_object* v_cache_1286_; lean_object* v_recoveredErrors_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1301_; 
v_stxStack_1283_ = lean_ctor_get(v_s_1281_, 0);
v_lhsPrec_1284_ = lean_ctor_get(v_s_1281_, 1);
v_pos_1285_ = lean_ctor_get(v_s_1281_, 2);
v_cache_1286_ = lean_ctor_get(v_s_1281_, 3);
v_recoveredErrors_1287_ = lean_ctor_get(v_s_1281_, 5);
v_isSharedCheck_1301_ = !lean_is_exclusive(v_s_1281_);
if (v_isSharedCheck_1301_ == 0)
{
lean_object* v_unused_1302_; 
v_unused_1302_ = lean_ctor_get(v_s_1281_, 4);
lean_dec(v_unused_1302_);
v___x_1289_ = v_s_1281_;
v_isShared_1290_ = v_isSharedCheck_1301_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_recoveredErrors_1287_);
lean_inc(v_cache_1286_);
lean_inc(v_pos_1285_);
lean_inc(v_lhsPrec_1284_);
lean_inc(v_stxStack_1283_);
lean_dec(v_s_1281_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1301_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1291_ = lean_box(0);
v___x_1292_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1293_ = lean_box(0);
v___x_1294_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1294_, 0, v_msg_1282_);
lean_ctor_set(v___x_1294_, 1, v___x_1293_);
v___x_1295_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1291_);
lean_ctor_set(v___x_1295_, 1, v___x_1292_);
lean_ctor_set(v___x_1295_, 2, v___x_1294_);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 4, v___x_1296_);
v___x_1298_ = v___x_1289_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_stxStack_1283_);
lean_ctor_set(v_reuseFailAlloc_1300_, 1, v_lhsPrec_1284_);
lean_ctor_set(v_reuseFailAlloc_1300_, 2, v_pos_1285_);
lean_ctor_set(v_reuseFailAlloc_1300_, 3, v_cache_1286_);
lean_ctor_set(v_reuseFailAlloc_1300_, 4, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1300_, 5, v_recoveredErrors_1287_);
v___x_1298_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1298_, v___x_1291_);
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1303_, lean_object* v_msg_1304_, lean_object* v_expected_1305_, uint8_t v_pushMissing_1306_){
_start:
{
lean_object* v_stxStack_1307_; lean_object* v_lhsPrec_1308_; lean_object* v_pos_1309_; lean_object* v_cache_1310_; lean_object* v_recoveredErrors_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1322_; 
v_stxStack_1307_ = lean_ctor_get(v_s_1303_, 0);
v_lhsPrec_1308_ = lean_ctor_get(v_s_1303_, 1);
v_pos_1309_ = lean_ctor_get(v_s_1303_, 2);
v_cache_1310_ = lean_ctor_get(v_s_1303_, 3);
v_recoveredErrors_1311_ = lean_ctor_get(v_s_1303_, 5);
v_isSharedCheck_1322_ = !lean_is_exclusive(v_s_1303_);
if (v_isSharedCheck_1322_ == 0)
{
lean_object* v_unused_1323_; 
v_unused_1323_ = lean_ctor_get(v_s_1303_, 4);
lean_dec(v_unused_1323_);
v___x_1313_ = v_s_1303_;
v_isShared_1314_ = v_isSharedCheck_1322_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_recoveredErrors_1311_);
lean_inc(v_cache_1310_);
lean_inc(v_pos_1309_);
lean_inc(v_lhsPrec_1308_);
lean_inc(v_stxStack_1307_);
lean_dec(v_s_1303_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1322_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_s_1319_; 
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v_msg_1304_);
lean_ctor_set(v___x_1316_, 2, v_expected_1305_);
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 4, v___x_1317_);
v_s_1319_ = v___x_1313_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_stxStack_1307_);
lean_ctor_set(v_reuseFailAlloc_1321_, 1, v_lhsPrec_1308_);
lean_ctor_set(v_reuseFailAlloc_1321_, 2, v_pos_1309_);
lean_ctor_set(v_reuseFailAlloc_1321_, 3, v_cache_1310_);
lean_ctor_set(v_reuseFailAlloc_1321_, 4, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1321_, 5, v_recoveredErrors_1311_);
v_s_1319_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
if (v_pushMissing_1306_ == 0)
{
return v_s_1319_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1319_, v___x_1315_);
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1324_, lean_object* v_msg_1325_, lean_object* v_expected_1326_, lean_object* v_pushMissing_1327_){
_start:
{
uint8_t v_pushMissing_boxed_1328_; lean_object* v_res_1329_; 
v_pushMissing_boxed_1328_ = lean_unbox(v_pushMissing_1327_);
v_res_1329_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1324_, v_msg_1325_, v_expected_1326_, v_pushMissing_boxed_1328_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1331_, lean_object* v_expected_1332_){
_start:
{
lean_object* v___x_1333_; uint8_t v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1334_ = 1;
v___x_1335_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1331_, v___x_1333_, v_expected_1332_, v___x_1334_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1336_, lean_object* v_ex_1337_, lean_object* v_pos_1338_, lean_object* v_initStackSz_x3f_1339_){
_start:
{
lean_object* v_s_1341_; lean_object* v_s_1360_; 
v_s_1360_ = l_Lean_Parser_ParserState_setPos(v_s_1336_, v_pos_1338_);
if (lean_obj_tag(v_initStackSz_x3f_1339_) == 1)
{
lean_object* v_val_1361_; lean_object* v_s_1362_; 
v_val_1361_ = lean_ctor_get(v_initStackSz_x3f_1339_, 0);
v_s_1362_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1360_, v_val_1361_);
v_s_1341_ = v_s_1362_;
goto v___jp_1340_;
}
else
{
v_s_1341_ = v_s_1360_;
goto v___jp_1340_;
}
v___jp_1340_:
{
lean_object* v_stxStack_1342_; lean_object* v_lhsPrec_1343_; lean_object* v_pos_1344_; lean_object* v_cache_1345_; lean_object* v_recoveredErrors_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1358_; 
v_stxStack_1342_ = lean_ctor_get(v_s_1341_, 0);
v_lhsPrec_1343_ = lean_ctor_get(v_s_1341_, 1);
v_pos_1344_ = lean_ctor_get(v_s_1341_, 2);
v_cache_1345_ = lean_ctor_get(v_s_1341_, 3);
v_recoveredErrors_1346_ = lean_ctor_get(v_s_1341_, 5);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_s_1341_);
if (v_isSharedCheck_1358_ == 0)
{
lean_object* v_unused_1359_; 
v_unused_1359_ = lean_ctor_get(v_s_1341_, 4);
lean_dec(v_unused_1359_);
v___x_1348_ = v_s_1341_;
v_isShared_1349_ = v_isSharedCheck_1358_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_recoveredErrors_1346_);
lean_inc(v_cache_1345_);
lean_inc(v_pos_1344_);
lean_inc(v_lhsPrec_1343_);
lean_inc(v_stxStack_1342_);
lean_dec(v_s_1341_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1358_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v_s_1355_; 
v___x_1350_ = lean_box(0);
v___x_1351_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
lean_ctor_set(v___x_1352_, 2, v_ex_1337_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 4, v___x_1353_);
v_s_1355_ = v___x_1348_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_stxStack_1342_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v_lhsPrec_1343_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_pos_1344_);
lean_ctor_set(v_reuseFailAlloc_1357_, 3, v_cache_1345_);
lean_ctor_set(v_reuseFailAlloc_1357_, 4, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1357_, 5, v_recoveredErrors_1346_);
v_s_1355_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
v___x_1356_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1355_, v___x_1350_);
return v___x_1356_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1363_, lean_object* v_ex_1364_, lean_object* v_pos_1365_, lean_object* v_initStackSz_x3f_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1363_, v_ex_1364_, v_pos_1365_, v_initStackSz_x3f_1366_);
lean_dec(v_initStackSz_x3f_1366_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1368_, lean_object* v_msg_1369_, lean_object* v_pos_1370_, lean_object* v_initStackSz_x3f_1371_){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_msg_1369_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1368_, v___x_1373_, v_pos_1370_, v_initStackSz_x3f_1371_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1375_, lean_object* v_msg_1376_, lean_object* v_pos_1377_, lean_object* v_initStackSz_x3f_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1375_, v_msg_1376_, v_pos_1377_, v_initStackSz_x3f_1378_);
lean_dec(v_initStackSz_x3f_1378_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1380_){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___x_1382_ = lean_panic_fn_borrowed(v___x_1381_, v_msg_1380_);
return v___x_1382_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1386_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1387_ = lean_unsigned_to_nat(14u);
v___x_1388_ = lean_unsigned_to_nat(22u);
v___x_1389_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1390_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1391_ = l_mkPanicMessageWithDecl(v___x_1390_, v___x_1389_, v___x_1388_, v___x_1387_, v___x_1386_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1392_, lean_object* v_ex_1393_, lean_object* v_iniPos_1394_){
_start:
{
lean_object* v_stxStack_1395_; lean_object* v_tk_1396_; lean_object* v___y_1398_; lean_object* v___x_1419_; uint8_t v___x_1420_; 
v_stxStack_1395_ = lean_ctor_get(v_s_1392_, 0);
v_tk_1396_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1395_);
v___x_1419_ = lean_unsigned_to_nat(0u);
v___x_1420_ = lean_nat_dec_lt(v___x_1419_, v_iniPos_1394_);
if (v___x_1420_ == 0)
{
lean_object* v___x_1421_; 
lean_dec(v_iniPos_1394_);
v___x_1421_ = l_Lean_Syntax_getPos_x3f(v_tk_1396_, v___x_1420_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1423_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1422_);
v___y_1398_ = v___x_1423_;
goto v___jp_1397_;
}
else
{
lean_object* v_val_1424_; 
v_val_1424_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_val_1424_);
lean_dec_ref_known(v___x_1421_, 1);
v___y_1398_ = v_val_1424_;
goto v___jp_1397_;
}
}
else
{
v___y_1398_ = v_iniPos_1394_;
goto v___jp_1397_;
}
v___jp_1397_:
{
lean_object* v_s_1399_; lean_object* v_stxStack_1400_; lean_object* v_lhsPrec_1401_; lean_object* v_pos_1402_; lean_object* v_cache_1403_; lean_object* v_recoveredErrors_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1417_; 
v_s_1399_ = l_Lean_Parser_ParserState_setPos(v_s_1392_, v___y_1398_);
v_stxStack_1400_ = lean_ctor_get(v_s_1399_, 0);
v_lhsPrec_1401_ = lean_ctor_get(v_s_1399_, 1);
v_pos_1402_ = lean_ctor_get(v_s_1399_, 2);
v_cache_1403_ = lean_ctor_get(v_s_1399_, 3);
v_recoveredErrors_1404_ = lean_ctor_get(v_s_1399_, 5);
v_isSharedCheck_1417_ = !lean_is_exclusive(v_s_1399_);
if (v_isSharedCheck_1417_ == 0)
{
lean_object* v_unused_1418_; 
v_unused_1418_ = lean_ctor_get(v_s_1399_, 4);
lean_dec(v_unused_1418_);
v___x_1406_ = v_s_1399_;
v_isShared_1407_ = v_isSharedCheck_1417_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_recoveredErrors_1404_);
lean_inc(v_cache_1403_);
lean_inc(v_pos_1402_);
lean_inc(v_lhsPrec_1401_);
lean_inc(v_stxStack_1400_);
lean_dec(v_s_1399_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1417_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_s_1412_; 
v___x_1408_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1409_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1409_, 0, v_tk_1396_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
lean_ctor_set(v___x_1409_, 2, v_ex_1393_);
v___x_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 4, v___x_1410_);
v_s_1412_ = v___x_1406_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_stxStack_1400_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v_lhsPrec_1401_);
lean_ctor_set(v_reuseFailAlloc_1416_, 2, v_pos_1402_);
lean_ctor_set(v_reuseFailAlloc_1416_, 3, v_cache_1403_);
lean_ctor_set(v_reuseFailAlloc_1416_, 4, v___x_1410_);
lean_ctor_set(v_reuseFailAlloc_1416_, 5, v_recoveredErrors_1404_);
v_s_1412_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1413_ = l_Lean_Parser_ParserState_popSyntax(v_s_1412_);
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1413_, v___x_1414_);
return v___x_1415_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1425_, lean_object* v_msg_1426_, lean_object* v_iniPos_1427_){
_start:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1428_ = lean_box(0);
v___x_1429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_msg_1426_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1425_, v___x_1429_, v_iniPos_1427_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1431_, lean_object* v_msg_1432_, lean_object* v_pos_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; lean_object* v___x_1437_; 
v___x_1434_ = l_Lean_Parser_ParserState_setPos(v_s_1431_, v_pos_1433_);
v___x_1435_ = lean_box(0);
v___x_1436_ = 1;
v___x_1437_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1434_, v_msg_1432_, v___x_1435_, v___x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1439_, lean_object* v_as_1440_, size_t v_sz_1441_, size_t v_i_1442_, lean_object* v_b_1443_){
_start:
{
uint8_t v___x_1444_; 
v___x_1444_ = lean_usize_dec_lt(v_i_1442_, v_sz_1441_);
if (v___x_1444_ == 0)
{
lean_dec_ref(v_ctx_1439_);
return v_b_1443_;
}
else
{
lean_object* v_a_1445_; lean_object* v_snd_1446_; lean_object* v_fst_1447_; lean_object* v_snd_1448_; lean_object* v_errStr_1450_; lean_object* v_errStr_1461_; uint8_t v___x_1462_; 
v_a_1445_ = lean_array_uget_borrowed(v_as_1440_, v_i_1442_);
v_snd_1446_ = lean_ctor_get(v_a_1445_, 1);
v_fst_1447_ = lean_ctor_get(v_a_1445_, 0);
v_snd_1448_ = lean_ctor_get(v_snd_1446_, 1);
v_errStr_1461_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1462_ = lean_string_dec_eq(v_b_1443_, v_errStr_1461_);
if (v___x_1462_ == 0)
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1464_ = lean_string_append(v_b_1443_, v___x_1463_);
v_errStr_1450_ = v___x_1464_;
goto v___jp_1449_;
}
else
{
v_errStr_1450_ = v_b_1443_;
goto v___jp_1449_;
}
v___jp_1449_:
{
lean_object* v_fileName_1451_; lean_object* v_fileMap_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; size_t v___x_1458_; size_t v___x_1459_; 
v_fileName_1451_ = lean_ctor_get(v_ctx_1439_, 1);
v_fileMap_1452_ = lean_ctor_get(v_ctx_1439_, 2);
lean_inc_ref(v_fileMap_1452_);
v___x_1453_ = l_Lean_FileMap_toPosition(v_fileMap_1452_, v_fst_1447_);
lean_inc(v_snd_1448_);
v___x_1454_ = l_Lean_Parser_Error_toString(v_snd_1448_);
v___x_1455_ = lean_box(0);
lean_inc_ref(v_fileName_1451_);
v___x_1456_ = l_Lean_mkErrorStringWithPos(v_fileName_1451_, v___x_1453_, v___x_1454_, v___x_1455_, v___x_1455_, v___x_1455_);
lean_dec_ref(v___x_1454_);
v___x_1457_ = lean_string_append(v_errStr_1450_, v___x_1456_);
lean_dec_ref(v___x_1456_);
v___x_1458_ = ((size_t)1ULL);
v___x_1459_ = lean_usize_add(v_i_1442_, v___x_1458_);
v_i_1442_ = v___x_1459_;
v_b_1443_ = v___x_1457_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1465_, lean_object* v_as_1466_, lean_object* v_sz_1467_, lean_object* v_i_1468_, lean_object* v_b_1469_){
_start:
{
size_t v_sz_boxed_1470_; size_t v_i_boxed_1471_; lean_object* v_res_1472_; 
v_sz_boxed_1470_ = lean_unbox_usize(v_sz_1467_);
lean_dec(v_sz_1467_);
v_i_boxed_1471_ = lean_unbox_usize(v_i_1468_);
lean_dec(v_i_1468_);
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1465_, v_as_1466_, v_sz_boxed_1470_, v_i_boxed_1471_, v_b_1469_);
lean_dec_ref(v_as_1466_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1473_, lean_object* v_s_1474_){
_start:
{
lean_object* v_errStr_1475_; lean_object* v___x_1476_; size_t v_sz_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
v_errStr_1475_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1476_ = l_Lean_Parser_ParserState_allErrors(v_s_1474_);
v_sz_1477_ = lean_array_size(v___x_1476_);
v___x_1478_ = ((size_t)0ULL);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1473_, v___x_1476_, v_sz_1477_, v___x_1478_, v_errStr_1475_);
lean_dec_ref(v___x_1476_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1480_, lean_object* v_s_1481_){
_start:
{
lean_inc_ref(v_s_1481_);
return v_s_1481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1482_, lean_object* v_s_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1482_, v_s_1483_);
lean_dec_ref(v_s_1483_);
lean_dec_ref(v_x_1482_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx(lean_object* v_x_1487_){
_start:
{
switch(lean_obj_tag(v_x_1487_))
{
case 0:
{
lean_object* v___x_1488_; 
v___x_1488_ = lean_unsigned_to_nat(0u);
return v___x_1488_;
}
case 1:
{
lean_object* v___x_1489_; 
v___x_1489_ = lean_unsigned_to_nat(1u);
return v___x_1489_;
}
case 2:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_unsigned_to_nat(2u);
return v___x_1490_;
}
default: 
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_unsigned_to_nat(3u);
return v___x_1491_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___boxed(lean_object* v_x_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_Lean_Parser_FirstTokens_ctorIdx(v_x_1492_);
lean_dec(v_x_1492_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1494_, lean_object* v_k_1495_){
_start:
{
switch(lean_obj_tag(v_t_1494_))
{
case 2:
{
lean_object* v_a_1496_; lean_object* v___x_1497_; 
v_a_1496_ = lean_ctor_get(v_t_1494_, 0);
lean_inc(v_a_1496_);
lean_dec_ref_known(v_t_1494_, 1);
v___x_1497_ = lean_apply_1(v_k_1495_, v_a_1496_);
return v___x_1497_;
}
case 3:
{
lean_object* v_a_1498_; lean_object* v___x_1499_; 
v_a_1498_ = lean_ctor_get(v_t_1494_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v_t_1494_, 1);
v___x_1499_ = lean_apply_1(v_k_1495_, v_a_1498_);
return v___x_1499_;
}
default: 
{
lean_dec(v_t_1494_);
return v_k_1495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1500_, lean_object* v_ctorIdx_1501_, lean_object* v_t_1502_, lean_object* v_h_1503_, lean_object* v_k_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1502_, v_k_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1506_, lean_object* v_ctorIdx_1507_, lean_object* v_t_1508_, lean_object* v_h_1509_, lean_object* v_k_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1506_, v_ctorIdx_1507_, v_t_1508_, v_h_1509_, v_k_1510_);
lean_dec(v_ctorIdx_1507_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1512_, lean_object* v_epsilon_1513_){
_start:
{
lean_object* v___x_1514_; 
v___x_1514_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1512_, v_epsilon_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1515_, lean_object* v_t_1516_, lean_object* v_h_1517_, lean_object* v_epsilon_1518_){
_start:
{
lean_object* v___x_1519_; 
v___x_1519_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1516_, v_epsilon_1518_);
return v___x_1519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1520_, lean_object* v_unknown_1521_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1520_, v_unknown_1521_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1523_, lean_object* v_t_1524_, lean_object* v_h_1525_, lean_object* v_unknown_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1524_, v_unknown_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1528_, lean_object* v_tokens_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1528_, v_tokens_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1531_, lean_object* v_t_1532_, lean_object* v_h_1533_, lean_object* v_tokens_1534_){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1532_, v_tokens_1534_);
return v___x_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1536_, lean_object* v_optTokens_1537_){
_start:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1536_, v_optTokens_1537_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1539_, lean_object* v_t_1540_, lean_object* v_h_1541_, lean_object* v_optTokens_1542_){
_start:
{
lean_object* v___x_1543_; 
v___x_1543_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1540_, v_optTokens_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = lean_box(0);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_box(0);
return v___x_1545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1546_, lean_object* v_x_1547_){
_start:
{
switch(lean_obj_tag(v_x_1546_))
{
case 0:
{
return v_x_1547_;
}
case 3:
{
switch(lean_obj_tag(v_x_1547_))
{
case 3:
{
lean_object* v_a_1548_; lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1557_; 
v_a_1548_ = lean_ctor_get(v_x_1546_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v_x_1546_, 1);
v_a_1549_ = lean_ctor_get(v_x_1547_, 0);
v_isSharedCheck_1557_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1557_ == 0)
{
v___x_1551_ = v_x_1547_;
v_isShared_1552_ = v_isSharedCheck_1557_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v_x_1547_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1557_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
v___x_1553_ = l_List_appendTR___redArg(v_a_1548_, v_a_1549_);
if (v_isShared_1552_ == 0)
{
lean_ctor_set(v___x_1551_, 0, v___x_1553_);
v___x_1555_ = v___x_1551_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1556_; 
v_reuseFailAlloc_1556_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1556_, 0, v___x_1553_);
v___x_1555_ = v_reuseFailAlloc_1556_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
return v___x_1555_;
}
}
}
case 2:
{
lean_object* v_a_1558_; lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1567_; 
v_a_1558_ = lean_ctor_get(v_x_1546_, 0);
lean_inc(v_a_1558_);
lean_dec_ref_known(v_x_1546_, 1);
v_a_1559_ = lean_ctor_get(v_x_1547_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v_x_1547_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1561_ = v_x_1547_;
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v_x_1547_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1567_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = l_List_appendTR___redArg(v_a_1558_, v_a_1559_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1563_);
v___x_1565_ = v___x_1561_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v___x_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
case 1:
{
lean_dec_ref_known(v_x_1546_, 1);
return v_x_1547_;
}
default: 
{
lean_dec(v_x_1547_);
return v_x_1546_;
}
}
}
default: 
{
lean_dec(v_x_1547_);
return v_x_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1568_){
_start:
{
if (lean_obj_tag(v_x_1568_) == 2)
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
v_a_1569_ = lean_ctor_get(v_x_1568_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_x_1568_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v_x_1568_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v_x_1568_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 3);
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
else
{
return v_x_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v_s_u2081_1580_; lean_object* v_s_u2082_1581_; 
switch(lean_obj_tag(v_x_1577_))
{
case 0:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1578_);
return v___x_1584_;
}
case 2:
{
switch(lean_obj_tag(v_x_1578_))
{
case 0:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1577_);
return v___x_1585_;
}
case 2:
{
lean_object* v_a_1586_; lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1595_; 
v_a_1586_ = lean_ctor_get(v_x_1577_, 0);
lean_inc(v_a_1586_);
lean_dec_ref_known(v_x_1577_, 1);
v_a_1587_ = lean_ctor_get(v_x_1578_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1578_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1589_ = v_x_1578_;
v_isShared_1590_ = v_isSharedCheck_1595_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v_x_1578_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1595_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = l_List_appendTR___redArg(v_a_1586_, v_a_1587_);
if (v_isShared_1590_ == 0)
{
lean_ctor_set(v___x_1589_, 0, v___x_1591_);
v___x_1593_ = v___x_1589_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
case 3:
{
lean_object* v_a_1596_; lean_object* v_a_1597_; 
v_a_1596_ = lean_ctor_get(v_x_1577_, 0);
lean_inc(v_a_1596_);
lean_dec_ref_known(v_x_1577_, 1);
v_a_1597_ = lean_ctor_get(v_x_1578_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v_x_1578_, 1);
v_s_u2081_1580_ = v_a_1596_;
v_s_u2082_1581_ = v_a_1597_;
goto v___jp_1579_;
}
default: 
{
lean_object* v___x_1598_; 
lean_dec_ref_known(v_x_1577_, 1);
lean_dec(v_x_1578_);
v___x_1598_ = lean_box(1);
return v___x_1598_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1578_))
{
case 0:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1577_);
return v___x_1599_;
}
case 3:
{
lean_object* v_a_1600_; lean_object* v_a_1601_; 
v_a_1600_ = lean_ctor_get(v_x_1577_, 0);
lean_inc(v_a_1600_);
lean_dec_ref_known(v_x_1577_, 1);
v_a_1601_ = lean_ctor_get(v_x_1578_, 0);
lean_inc(v_a_1601_);
lean_dec_ref_known(v_x_1578_, 1);
v_s_u2081_1580_ = v_a_1600_;
v_s_u2082_1581_ = v_a_1601_;
goto v___jp_1579_;
}
case 2:
{
lean_object* v_a_1602_; lean_object* v_a_1603_; 
v_a_1602_ = lean_ctor_get(v_x_1577_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v_x_1577_, 1);
v_a_1603_ = lean_ctor_get(v_x_1578_, 0);
lean_inc(v_a_1603_);
lean_dec_ref_known(v_x_1578_, 1);
v_s_u2081_1580_ = v_a_1602_;
v_s_u2082_1581_ = v_a_1603_;
goto v___jp_1579_;
}
default: 
{
lean_object* v___x_1604_; 
lean_dec_ref_known(v_x_1577_, 1);
lean_dec(v_x_1578_);
v___x_1604_ = lean_box(1);
return v___x_1604_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1578_) == 0)
{
lean_object* v___x_1605_; 
v___x_1605_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1577_);
return v___x_1605_;
}
else
{
lean_object* v___x_1606_; 
lean_dec(v_x_1578_);
lean_dec(v_x_1577_);
v___x_1606_ = lean_box(1);
return v___x_1606_;
}
}
}
v___jp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = l_List_appendTR___redArg(v_s_u2081_1580_, v_s_u2082_1581_);
v___x_1583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
return v___x_1583_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
if (lean_obj_tag(v_x_1608_) == 0)
{
return v_x_1607_;
}
else
{
lean_object* v_head_1609_; lean_object* v_tail_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; 
v_head_1609_ = lean_ctor_get(v_x_1608_, 0);
v_tail_1610_ = lean_ctor_get(v_x_1608_, 1);
v___x_1611_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1612_ = lean_string_append(v_x_1607_, v___x_1611_);
v___x_1613_ = lean_string_append(v___x_1612_, v_head_1609_);
v_x_1607_ = v___x_1613_;
v_x_1608_ = v_tail_1610_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1615_, lean_object* v_x_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1615_, v_x_1616_);
lean_dec(v_x_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1621_){
_start:
{
if (lean_obj_tag(v_x_1621_) == 0)
{
lean_object* v___x_1622_; 
v___x_1622_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1622_;
}
else
{
lean_object* v_tail_1623_; 
v_tail_1623_ = lean_ctor_get(v_x_1621_, 1);
if (lean_obj_tag(v_tail_1623_) == 0)
{
lean_object* v_head_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_head_1624_ = lean_ctor_get(v_x_1621_, 0);
v___x_1625_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1626_ = lean_string_append(v___x_1625_, v_head_1624_);
v___x_1627_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1628_ = lean_string_append(v___x_1626_, v___x_1627_);
return v___x_1628_;
}
else
{
lean_object* v_head_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint32_t v___x_1633_; lean_object* v___x_1634_; 
v_head_1629_ = lean_ctor_get(v_x_1621_, 0);
v___x_1630_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1631_ = lean_string_append(v___x_1630_, v_head_1629_);
v___x_1632_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1631_, v_tail_1623_);
v___x_1633_ = 93;
v___x_1634_ = lean_string_push(v___x_1632_, v___x_1633_);
return v___x_1634_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1635_);
lean_dec(v_x_1635_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1640_){
_start:
{
switch(lean_obj_tag(v_x_1640_))
{
case 0:
{
lean_object* v___x_1641_; 
v___x_1641_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1641_;
}
case 1:
{
lean_object* v___x_1642_; 
v___x_1642_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1642_;
}
case 2:
{
lean_object* v_a_1643_; lean_object* v___x_1644_; 
v_a_1643_ = lean_ctor_get(v_x_1640_, 0);
v___x_1644_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1643_);
return v___x_1644_;
}
default: 
{
lean_object* v_a_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; 
v_a_1645_ = lean_ctor_get(v_x_1640_, 0);
v___x_1646_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1647_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1645_);
v___x_1648_ = lean_string_append(v___x_1646_, v___x_1647_);
lean_dec_ref(v___x_1647_);
return v___x_1648_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Lean_Parser_FirstTokens_toStr(v_x_1649_);
lean_dec(v_x_1649_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v___y_1653_){
_start:
{
lean_inc(v___y_1653_);
return v___y_1653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v___y_1654_){
_start:
{
lean_object* v_res_1655_; 
v_res_1655_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_1654_);
lean_dec(v___y_1654_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v___y_1656_){
_start:
{
lean_inc_ref(v___y_1656_);
return v___y_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v___y_1657_){
_start:
{
lean_object* v_res_1658_; 
v_res_1658_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_1657_);
lean_dec_ref(v___y_1657_);
return v_res_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1672_, lean_object* v_p_1673_){
_start:
{
lean_object* v_info_1674_; lean_object* v_fn_1675_; lean_object* v___x_1677_; uint8_t v_isShared_1678_; uint8_t v_isSharedCheck_1683_; 
v_info_1674_ = lean_ctor_get(v_p_1673_, 0);
v_fn_1675_ = lean_ctor_get(v_p_1673_, 1);
v_isSharedCheck_1683_ = !lean_is_exclusive(v_p_1673_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1677_ = v_p_1673_;
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
else
{
lean_inc(v_fn_1675_);
lean_inc(v_info_1674_);
lean_dec(v_p_1673_);
v___x_1677_ = lean_box(0);
v_isShared_1678_ = v_isSharedCheck_1683_;
goto v_resetjp_1676_;
}
v_resetjp_1676_:
{
lean_object* v___x_1679_; lean_object* v___x_1681_; 
v___x_1679_ = lean_apply_1(v_f_1672_, v_fn_1675_);
if (v_isShared_1678_ == 0)
{
lean_ctor_set(v___x_1677_, 1, v___x_1679_);
v___x_1681_ = v___x_1677_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v_info_1674_);
lean_ctor_set(v_reuseFailAlloc_1682_, 1, v___x_1679_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1684_, lean_object* v_p_1685_, lean_object* v_c_1686_, lean_object* v_s_1687_){
_start:
{
lean_object* v_toInputContext_1688_; lean_object* v_toParserModuleContext_1689_; lean_object* v_toCacheableParserContext_1690_; lean_object* v_tokens_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1700_; 
v_toInputContext_1688_ = lean_ctor_get(v_c_1686_, 0);
v_toParserModuleContext_1689_ = lean_ctor_get(v_c_1686_, 1);
v_toCacheableParserContext_1690_ = lean_ctor_get(v_c_1686_, 2);
v_tokens_1691_ = lean_ctor_get(v_c_1686_, 3);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_c_1686_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1693_ = v_c_1686_;
v_isShared_1694_ = v_isSharedCheck_1700_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_tokens_1691_);
lean_inc(v_toCacheableParserContext_1690_);
lean_inc(v_toParserModuleContext_1689_);
lean_inc(v_toInputContext_1688_);
lean_dec(v_c_1686_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1700_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
v___x_1695_ = lean_apply_1(v_f_1684_, v_toCacheableParserContext_1690_);
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 2, v___x_1695_);
v___x_1697_ = v___x_1693_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_toInputContext_1688_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_toParserModuleContext_1689_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v___x_1695_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_tokens_1691_);
v___x_1697_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_apply_2(v_p_1685_, v___x_1697_, v_s_1687_);
return v___x_1698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1701_, lean_object* v_p_1702_){
_start:
{
lean_object* v_info_1703_; lean_object* v_fn_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1712_; 
v_info_1703_ = lean_ctor_get(v_p_1702_, 0);
v_fn_1704_ = lean_ctor_get(v_p_1702_, 1);
v_isSharedCheck_1712_ = !lean_is_exclusive(v_p_1702_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1706_ = v_p_1702_;
v_isShared_1707_ = v_isSharedCheck_1712_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_fn_1704_);
lean_inc(v_info_1703_);
lean_dec(v_p_1702_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1712_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
v___x_1708_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1708_, 0, v_f_1701_);
lean_closure_set(v___x_1708_, 1, v_fn_1704_);
if (v_isShared_1707_ == 0)
{
lean_ctor_set(v___x_1706_, 1, v___x_1708_);
v___x_1710_ = v___x_1706_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_info_1703_);
lean_ctor_set(v_reuseFailAlloc_1711_, 1, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1713_, lean_object* v_p_1714_, lean_object* v_c_1715_, lean_object* v_s_1716_){
_start:
{
lean_object* v_stxStack_1717_; lean_object* v_lhsPrec_1718_; lean_object* v_pos_1719_; lean_object* v_cache_1720_; lean_object* v_errorMsg_1721_; lean_object* v_recoveredErrors_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1761_; 
v_stxStack_1717_ = lean_ctor_get(v_s_1716_, 0);
v_lhsPrec_1718_ = lean_ctor_get(v_s_1716_, 1);
v_pos_1719_ = lean_ctor_get(v_s_1716_, 2);
v_cache_1720_ = lean_ctor_get(v_s_1716_, 3);
v_errorMsg_1721_ = lean_ctor_get(v_s_1716_, 4);
v_recoveredErrors_1722_ = lean_ctor_get(v_s_1716_, 5);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_s_1716_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1724_ = v_s_1716_;
v_isShared_1725_ = v_isSharedCheck_1761_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_recoveredErrors_1722_);
lean_inc(v_errorMsg_1721_);
lean_inc(v_cache_1720_);
lean_inc(v_pos_1719_);
lean_inc(v_lhsPrec_1718_);
lean_inc(v_stxStack_1717_);
lean_dec(v_s_1716_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1761_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_raw_1726_; lean_object* v_drop_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1760_; 
v_raw_1726_ = lean_ctor_get(v_stxStack_1717_, 0);
v_drop_1727_ = lean_ctor_get(v_stxStack_1717_, 1);
v_isSharedCheck_1760_ = !lean_is_exclusive(v_stxStack_1717_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1729_ = v_stxStack_1717_;
v_isShared_1730_ = v_isSharedCheck_1760_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_drop_1727_);
lean_inc(v_raw_1726_);
lean_dec(v_stxStack_1717_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1760_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 1, v_drop_1713_);
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_raw_1726_);
lean_ctor_set(v_reuseFailAlloc_1759_, 1, v_drop_1713_);
v___x_1732_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
lean_object* v___x_1734_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1732_);
v___x_1734_ = v___x_1724_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1758_; 
v_reuseFailAlloc_1758_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1758_, 0, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1758_, 1, v_lhsPrec_1718_);
lean_ctor_set(v_reuseFailAlloc_1758_, 2, v_pos_1719_);
lean_ctor_set(v_reuseFailAlloc_1758_, 3, v_cache_1720_);
lean_ctor_set(v_reuseFailAlloc_1758_, 4, v_errorMsg_1721_);
lean_ctor_set(v_reuseFailAlloc_1758_, 5, v_recoveredErrors_1722_);
v___x_1734_ = v_reuseFailAlloc_1758_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v_s_1735_; lean_object* v_stxStack_1736_; lean_object* v_lhsPrec_1737_; lean_object* v_pos_1738_; lean_object* v_cache_1739_; lean_object* v_errorMsg_1740_; lean_object* v_recoveredErrors_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1757_; 
v_s_1735_ = lean_apply_2(v_p_1714_, v_c_1715_, v___x_1734_);
v_stxStack_1736_ = lean_ctor_get(v_s_1735_, 0);
v_lhsPrec_1737_ = lean_ctor_get(v_s_1735_, 1);
v_pos_1738_ = lean_ctor_get(v_s_1735_, 2);
v_cache_1739_ = lean_ctor_get(v_s_1735_, 3);
v_errorMsg_1740_ = lean_ctor_get(v_s_1735_, 4);
v_recoveredErrors_1741_ = lean_ctor_get(v_s_1735_, 5);
v_isSharedCheck_1757_ = !lean_is_exclusive(v_s_1735_);
if (v_isSharedCheck_1757_ == 0)
{
v___x_1743_ = v_s_1735_;
v_isShared_1744_ = v_isSharedCheck_1757_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_recoveredErrors_1741_);
lean_inc(v_errorMsg_1740_);
lean_inc(v_cache_1739_);
lean_inc(v_pos_1738_);
lean_inc(v_lhsPrec_1737_);
lean_inc(v_stxStack_1736_);
lean_dec(v_s_1735_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1757_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v_raw_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1755_; 
v_raw_1745_ = lean_ctor_get(v_stxStack_1736_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v_stxStack_1736_);
if (v_isSharedCheck_1755_ == 0)
{
lean_object* v_unused_1756_; 
v_unused_1756_ = lean_ctor_get(v_stxStack_1736_, 1);
lean_dec(v_unused_1756_);
v___x_1747_ = v_stxStack_1736_;
v_isShared_1748_ = v_isSharedCheck_1755_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_raw_1745_);
lean_dec(v_stxStack_1736_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1755_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
lean_ctor_set(v___x_1747_, 1, v_drop_1727_);
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_raw_1745_);
lean_ctor_set(v_reuseFailAlloc_1754_, 1, v_drop_1727_);
v___x_1750_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
lean_object* v___x_1752_; 
if (v_isShared_1744_ == 0)
{
lean_ctor_set(v___x_1743_, 0, v___x_1750_);
v___x_1752_ = v___x_1743_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
lean_ctor_set(v_reuseFailAlloc_1753_, 1, v_lhsPrec_1737_);
lean_ctor_set(v_reuseFailAlloc_1753_, 2, v_pos_1738_);
lean_ctor_set(v_reuseFailAlloc_1753_, 3, v_cache_1739_);
lean_ctor_set(v_reuseFailAlloc_1753_, 4, v_errorMsg_1740_);
lean_ctor_set(v_reuseFailAlloc_1753_, 5, v_recoveredErrors_1741_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1762_, lean_object* v_c_1763_, lean_object* v_s_1764_){
_start:
{
lean_object* v_cache_1765_; lean_object* v_stxStack_1766_; lean_object* v_lhsPrec_1767_; lean_object* v_pos_1768_; lean_object* v_errorMsg_1769_; lean_object* v_recoveredErrors_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1810_; 
v_cache_1765_ = lean_ctor_get(v_s_1764_, 3);
v_stxStack_1766_ = lean_ctor_get(v_s_1764_, 0);
v_lhsPrec_1767_ = lean_ctor_get(v_s_1764_, 1);
v_pos_1768_ = lean_ctor_get(v_s_1764_, 2);
v_errorMsg_1769_ = lean_ctor_get(v_s_1764_, 4);
v_recoveredErrors_1770_ = lean_ctor_get(v_s_1764_, 5);
v_isSharedCheck_1810_ = !lean_is_exclusive(v_s_1764_);
if (v_isSharedCheck_1810_ == 0)
{
v___x_1772_ = v_s_1764_;
v_isShared_1773_ = v_isSharedCheck_1810_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_recoveredErrors_1770_);
lean_inc(v_errorMsg_1769_);
lean_inc(v_cache_1765_);
lean_inc(v_pos_1768_);
lean_inc(v_lhsPrec_1767_);
lean_inc(v_stxStack_1766_);
lean_dec(v_s_1764_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1810_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_tokenCache_1774_; lean_object* v_parserCache_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1809_; 
v_tokenCache_1774_ = lean_ctor_get(v_cache_1765_, 0);
v_parserCache_1775_ = lean_ctor_get(v_cache_1765_, 1);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_cache_1765_);
if (v_isSharedCheck_1809_ == 0)
{
v___x_1777_ = v_cache_1765_;
v_isShared_1778_ = v_isSharedCheck_1809_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_parserCache_1775_);
lean_inc(v_tokenCache_1774_);
lean_dec(v_cache_1765_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1809_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1779_; lean_object* v___x_1781_; 
v___x_1779_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
if (v_isShared_1778_ == 0)
{
lean_ctor_set(v___x_1777_, 1, v___x_1779_);
v___x_1781_ = v___x_1777_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_tokenCache_1774_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v___x_1779_);
v___x_1781_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
lean_object* v___x_1783_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 3, v___x_1781_);
v___x_1783_ = v___x_1772_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_stxStack_1766_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_lhsPrec_1767_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_pos_1768_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v___x_1781_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_errorMsg_1769_);
lean_ctor_set(v_reuseFailAlloc_1807_, 5, v_recoveredErrors_1770_);
v___x_1783_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v_s_x27_1784_; lean_object* v_cache_1785_; lean_object* v_stxStack_1786_; lean_object* v_lhsPrec_1787_; lean_object* v_pos_1788_; lean_object* v_errorMsg_1789_; lean_object* v_recoveredErrors_1790_; lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1806_; 
v_s_x27_1784_ = lean_apply_2(v_p_1762_, v_c_1763_, v___x_1783_);
v_cache_1785_ = lean_ctor_get(v_s_x27_1784_, 3);
v_stxStack_1786_ = lean_ctor_get(v_s_x27_1784_, 0);
v_lhsPrec_1787_ = lean_ctor_get(v_s_x27_1784_, 1);
v_pos_1788_ = lean_ctor_get(v_s_x27_1784_, 2);
v_errorMsg_1789_ = lean_ctor_get(v_s_x27_1784_, 4);
v_recoveredErrors_1790_ = lean_ctor_get(v_s_x27_1784_, 5);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_s_x27_1784_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1792_ = v_s_x27_1784_;
v_isShared_1793_ = v_isSharedCheck_1806_;
goto v_resetjp_1791_;
}
else
{
lean_inc(v_recoveredErrors_1790_);
lean_inc(v_errorMsg_1789_);
lean_inc(v_cache_1785_);
lean_inc(v_pos_1788_);
lean_inc(v_lhsPrec_1787_);
lean_inc(v_stxStack_1786_);
lean_dec(v_s_x27_1784_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1806_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
lean_object* v_tokenCache_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1804_; 
v_tokenCache_1794_ = lean_ctor_get(v_cache_1785_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_cache_1785_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; 
v_unused_1805_ = lean_ctor_get(v_cache_1785_, 1);
lean_dec(v_unused_1805_);
v___x_1796_ = v_cache_1785_;
v_isShared_1797_ = v_isSharedCheck_1804_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_tokenCache_1794_);
lean_dec(v_cache_1785_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1804_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1799_; 
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 1, v_parserCache_1775_);
v___x_1799_ = v___x_1796_;
goto v_reusejp_1798_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_tokenCache_1794_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_parserCache_1775_);
v___x_1799_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1798_;
}
v_reusejp_1798_:
{
lean_object* v___x_1801_; 
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 3, v___x_1799_);
v___x_1801_ = v___x_1792_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_stxStack_1786_);
lean_ctor_set(v_reuseFailAlloc_1802_, 1, v_lhsPrec_1787_);
lean_ctor_set(v_reuseFailAlloc_1802_, 2, v_pos_1788_);
lean_ctor_set(v_reuseFailAlloc_1802_, 3, v___x_1799_);
lean_ctor_set(v_reuseFailAlloc_1802_, 4, v_errorMsg_1789_);
lean_ctor_set(v_reuseFailAlloc_1802_, 5, v_recoveredErrors_1790_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___f_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___f_1814_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1814_, 0, v_p_1811_);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1815_, v___f_1814_, v_a_1812_, v_a_1813_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1817_){
_start:
{
lean_object* v_info_1818_; lean_object* v_fn_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1827_; 
v_info_1818_ = lean_ctor_get(v_p_1817_, 0);
v_fn_1819_ = lean_ctor_get(v_p_1817_, 1);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_p_1817_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1821_ = v_p_1817_;
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_fn_1819_);
lean_inc(v_info_1818_);
lean_dec(v_p_1817_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1827_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1823_, 0, v_fn_1819_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_info_1818_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1828_, lean_object* v_p_1829_, lean_object* v_c_1830_, lean_object* v_s_1831_){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
v___x_1832_ = lean_apply_1(v_f_1828_, v_c_1830_);
v___x_1833_ = lean_apply_2(v_p_1829_, v___x_1832_, v_s_1831_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1834_, lean_object* v_p_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___f_1838_; lean_object* v___x_1839_; 
v___f_1838_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1838_, 0, v_f_1834_);
lean_closure_set(v___f_1838_, 1, v_p_1835_);
v___x_1839_ = l_Lean_Parser_withResetCacheFn(v___f_1838_, v_a_1836_, v_a_1837_);
return v___x_1839_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1840_, lean_object* v_x_1841_){
_start:
{
if (lean_obj_tag(v_x_1841_) == 0)
{
uint8_t v___x_1842_; 
v___x_1842_ = 0;
return v___x_1842_;
}
else
{
lean_object* v_key_1843_; lean_object* v_tail_1844_; uint8_t v___x_1845_; 
v_key_1843_ = lean_ctor_get(v_x_1841_, 0);
v_tail_1844_ = lean_ctor_get(v_x_1841_, 2);
v___x_1845_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1843_, v_a_1840_);
if (v___x_1845_ == 0)
{
v_x_1841_ = v_tail_1844_;
goto _start;
}
else
{
return v___x_1845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1847_, lean_object* v_x_1848_){
_start:
{
uint8_t v_res_1849_; lean_object* v_r_1850_; 
v_res_1849_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1847_, v_x_1848_);
lean_dec(v_x_1848_);
lean_dec_ref(v_a_1847_);
v_r_1850_ = lean_box(v_res_1849_);
return v_r_1850_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1851_, lean_object* v_x_1852_){
_start:
{
if (lean_obj_tag(v_x_1852_) == 0)
{
return v_x_1851_;
}
else
{
lean_object* v_key_1853_; lean_object* v_value_1854_; lean_object* v_tail_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1885_; 
v_key_1853_ = lean_ctor_get(v_x_1852_, 0);
v_value_1854_ = lean_ctor_get(v_x_1852_, 1);
v_tail_1855_ = lean_ctor_get(v_x_1852_, 2);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_x_1852_);
if (v_isSharedCheck_1885_ == 0)
{
v___x_1857_ = v_x_1852_;
v_isShared_1858_ = v_isSharedCheck_1885_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_tail_1855_);
lean_inc(v_value_1854_);
lean_inc(v_key_1853_);
lean_dec(v_x_1852_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1885_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v_parserName_1859_; lean_object* v_pos_1860_; lean_object* v___x_1861_; uint64_t v___x_1862_; uint64_t v___y_1864_; 
v_parserName_1859_ = lean_ctor_get(v_key_1853_, 1);
v_pos_1860_ = lean_ctor_get(v_key_1853_, 2);
v___x_1861_ = lean_array_get_size(v_x_1851_);
v___x_1862_ = l_String_instHashableRaw_hash(v_pos_1860_);
if (lean_obj_tag(v_parserName_1859_) == 0)
{
uint64_t v___x_1883_; 
v___x_1883_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1864_ = v___x_1883_;
goto v___jp_1863_;
}
else
{
uint64_t v_hash_1884_; 
v_hash_1884_ = lean_ctor_get_uint64(v_parserName_1859_, sizeof(void*)*2);
v___y_1864_ = v_hash_1884_;
goto v___jp_1863_;
}
v___jp_1863_:
{
uint64_t v___x_1865_; uint64_t v___x_1866_; uint64_t v___x_1867_; uint64_t v_fold_1868_; uint64_t v___x_1869_; uint64_t v___x_1870_; uint64_t v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; size_t v___x_1874_; size_t v___x_1875_; size_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1865_ = lean_uint64_mix_hash(v___x_1862_, v___y_1864_);
v___x_1866_ = 32ULL;
v___x_1867_ = lean_uint64_shift_right(v___x_1865_, v___x_1866_);
v_fold_1868_ = lean_uint64_xor(v___x_1865_, v___x_1867_);
v___x_1869_ = 16ULL;
v___x_1870_ = lean_uint64_shift_right(v_fold_1868_, v___x_1869_);
v___x_1871_ = lean_uint64_xor(v_fold_1868_, v___x_1870_);
v___x_1872_ = lean_uint64_to_usize(v___x_1871_);
v___x_1873_ = lean_usize_of_nat(v___x_1861_);
v___x_1874_ = ((size_t)1ULL);
v___x_1875_ = lean_usize_sub(v___x_1873_, v___x_1874_);
v___x_1876_ = lean_usize_land(v___x_1872_, v___x_1875_);
v___x_1877_ = lean_array_uget_borrowed(v_x_1851_, v___x_1876_);
lean_inc(v___x_1877_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 2, v___x_1877_);
v___x_1879_ = v___x_1857_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1882_; 
v_reuseFailAlloc_1882_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_key_1853_);
lean_ctor_set(v_reuseFailAlloc_1882_, 1, v_value_1854_);
lean_ctor_set(v_reuseFailAlloc_1882_, 2, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1882_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
lean_object* v___x_1880_; 
v___x_1880_ = lean_array_uset(v_x_1851_, v___x_1876_, v___x_1879_);
v_x_1851_ = v___x_1880_;
v_x_1852_ = v_tail_1855_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1886_, lean_object* v_source_1887_, lean_object* v_target_1888_){
_start:
{
lean_object* v___x_1889_; uint8_t v___x_1890_; 
v___x_1889_ = lean_array_get_size(v_source_1887_);
v___x_1890_ = lean_nat_dec_lt(v_i_1886_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_dec_ref(v_source_1887_);
lean_dec(v_i_1886_);
return v_target_1888_;
}
else
{
lean_object* v_es_1891_; lean_object* v___x_1892_; lean_object* v_source_1893_; lean_object* v_target_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v_es_1891_ = lean_array_fget(v_source_1887_, v_i_1886_);
v___x_1892_ = lean_box(0);
v_source_1893_ = lean_array_fset(v_source_1887_, v_i_1886_, v___x_1892_);
v_target_1894_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1888_, v_es_1891_);
v___x_1895_ = lean_unsigned_to_nat(1u);
v___x_1896_ = lean_nat_add(v_i_1886_, v___x_1895_);
lean_dec(v_i_1886_);
v_i_1886_ = v___x_1896_;
v_source_1887_ = v_source_1893_;
v_target_1888_ = v_target_1894_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1898_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v_nbuckets_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1899_ = lean_array_get_size(v_data_1898_);
v___x_1900_ = lean_unsigned_to_nat(2u);
v_nbuckets_1901_ = lean_nat_mul(v___x_1899_, v___x_1900_);
v___x_1902_ = lean_unsigned_to_nat(0u);
v___x_1903_ = lean_box(0);
v___x_1904_ = lean_mk_array(v_nbuckets_1901_, v___x_1903_);
v___x_1905_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1902_, v_data_1898_, v___x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1906_, lean_object* v_b_1907_, lean_object* v_x_1908_){
_start:
{
if (lean_obj_tag(v_x_1908_) == 0)
{
lean_dec(v_b_1907_);
lean_dec_ref(v_a_1906_);
return v_x_1908_;
}
else
{
lean_object* v_key_1909_; lean_object* v_value_1910_; lean_object* v_tail_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1923_; 
v_key_1909_ = lean_ctor_get(v_x_1908_, 0);
v_value_1910_ = lean_ctor_get(v_x_1908_, 1);
v_tail_1911_ = lean_ctor_get(v_x_1908_, 2);
v_isSharedCheck_1923_ = !lean_is_exclusive(v_x_1908_);
if (v_isSharedCheck_1923_ == 0)
{
v___x_1913_ = v_x_1908_;
v_isShared_1914_ = v_isSharedCheck_1923_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_tail_1911_);
lean_inc(v_value_1910_);
lean_inc(v_key_1909_);
lean_dec(v_x_1908_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1923_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
uint8_t v___x_1915_; 
v___x_1915_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1909_, v_a_1906_);
if (v___x_1915_ == 0)
{
lean_object* v___x_1916_; lean_object* v___x_1918_; 
v___x_1916_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1906_, v_b_1907_, v_tail_1911_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 2, v___x_1916_);
v___x_1918_ = v___x_1913_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_key_1909_);
lean_ctor_set(v_reuseFailAlloc_1919_, 1, v_value_1910_);
lean_ctor_set(v_reuseFailAlloc_1919_, 2, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1919_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
return v___x_1918_;
}
}
else
{
lean_object* v___x_1921_; 
lean_dec(v_value_1910_);
lean_dec(v_key_1909_);
if (v_isShared_1914_ == 0)
{
lean_ctor_set(v___x_1913_, 1, v_b_1907_);
lean_ctor_set(v___x_1913_, 0, v_a_1906_);
v___x_1921_ = v___x_1913_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_a_1906_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_b_1907_);
lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_tail_1911_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1924_, lean_object* v_a_1925_, lean_object* v_b_1926_){
_start:
{
lean_object* v_size_1927_; lean_object* v_buckets_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1978_; 
v_size_1927_ = lean_ctor_get(v_m_1924_, 0);
v_buckets_1928_ = lean_ctor_get(v_m_1924_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_m_1924_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1930_ = v_m_1924_;
v_isShared_1931_ = v_isSharedCheck_1978_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_buckets_1928_);
lean_inc(v_size_1927_);
lean_dec(v_m_1924_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1978_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v_parserName_1932_; lean_object* v_pos_1933_; lean_object* v___x_1934_; uint64_t v___x_1935_; uint64_t v___y_1937_; 
v_parserName_1932_ = lean_ctor_get(v_a_1925_, 1);
v_pos_1933_ = lean_ctor_get(v_a_1925_, 2);
v___x_1934_ = lean_array_get_size(v_buckets_1928_);
v___x_1935_ = l_String_instHashableRaw_hash(v_pos_1933_);
if (lean_obj_tag(v_parserName_1932_) == 0)
{
uint64_t v___x_1976_; 
v___x_1976_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1937_ = v___x_1976_;
goto v___jp_1936_;
}
else
{
uint64_t v_hash_1977_; 
v_hash_1977_ = lean_ctor_get_uint64(v_parserName_1932_, sizeof(void*)*2);
v___y_1937_ = v_hash_1977_;
goto v___jp_1936_;
}
v___jp_1936_:
{
uint64_t v___x_1938_; uint64_t v___x_1939_; uint64_t v___x_1940_; uint64_t v_fold_1941_; uint64_t v___x_1942_; uint64_t v___x_1943_; uint64_t v___x_1944_; size_t v___x_1945_; size_t v___x_1946_; size_t v___x_1947_; size_t v___x_1948_; size_t v___x_1949_; lean_object* v_bkt_1950_; uint8_t v___x_1951_; 
v___x_1938_ = lean_uint64_mix_hash(v___x_1935_, v___y_1937_);
v___x_1939_ = 32ULL;
v___x_1940_ = lean_uint64_shift_right(v___x_1938_, v___x_1939_);
v_fold_1941_ = lean_uint64_xor(v___x_1938_, v___x_1940_);
v___x_1942_ = 16ULL;
v___x_1943_ = lean_uint64_shift_right(v_fold_1941_, v___x_1942_);
v___x_1944_ = lean_uint64_xor(v_fold_1941_, v___x_1943_);
v___x_1945_ = lean_uint64_to_usize(v___x_1944_);
v___x_1946_ = lean_usize_of_nat(v___x_1934_);
v___x_1947_ = ((size_t)1ULL);
v___x_1948_ = lean_usize_sub(v___x_1946_, v___x_1947_);
v___x_1949_ = lean_usize_land(v___x_1945_, v___x_1948_);
v_bkt_1950_ = lean_array_uget_borrowed(v_buckets_1928_, v___x_1949_);
v___x_1951_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1925_, v_bkt_1950_);
if (v___x_1951_ == 0)
{
lean_object* v___x_1952_; lean_object* v_size_x27_1953_; lean_object* v___x_1954_; lean_object* v_buckets_x27_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; uint8_t v___x_1961_; 
v___x_1952_ = lean_unsigned_to_nat(1u);
v_size_x27_1953_ = lean_nat_add(v_size_1927_, v___x_1952_);
lean_dec(v_size_1927_);
lean_inc(v_bkt_1950_);
v___x_1954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1954_, 0, v_a_1925_);
lean_ctor_set(v___x_1954_, 1, v_b_1926_);
lean_ctor_set(v___x_1954_, 2, v_bkt_1950_);
v_buckets_x27_1955_ = lean_array_uset(v_buckets_1928_, v___x_1949_, v___x_1954_);
v___x_1956_ = lean_unsigned_to_nat(4u);
v___x_1957_ = lean_nat_mul(v_size_x27_1953_, v___x_1956_);
v___x_1958_ = lean_unsigned_to_nat(3u);
v___x_1959_ = lean_nat_div(v___x_1957_, v___x_1958_);
lean_dec(v___x_1957_);
v___x_1960_ = lean_array_get_size(v_buckets_x27_1955_);
v___x_1961_ = lean_nat_dec_le(v___x_1959_, v___x_1960_);
lean_dec(v___x_1959_);
if (v___x_1961_ == 0)
{
lean_object* v_val_1962_; lean_object* v___x_1964_; 
v_val_1962_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_1955_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v_val_1962_);
lean_ctor_set(v___x_1930_, 0, v_size_x27_1953_);
v___x_1964_ = v___x_1930_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_size_x27_1953_);
lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_val_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
else
{
lean_object* v___x_1967_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v_buckets_x27_1955_);
lean_ctor_set(v___x_1930_, 0, v_size_x27_1953_);
v___x_1967_ = v___x_1930_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_size_x27_1953_);
lean_ctor_set(v_reuseFailAlloc_1968_, 1, v_buckets_x27_1955_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
else
{
lean_object* v___x_1969_; lean_object* v_buckets_x27_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1974_; 
lean_inc(v_bkt_1950_);
v___x_1969_ = lean_box(0);
v_buckets_x27_1970_ = lean_array_uset(v_buckets_1928_, v___x_1949_, v___x_1969_);
v___x_1971_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1925_, v_b_1926_, v_bkt_1950_);
v___x_1972_ = lean_array_uset(v_buckets_x27_1970_, v___x_1949_, v___x_1971_);
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 1, v___x_1972_);
v___x_1974_ = v___x_1930_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_size_1927_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v___x_1972_);
v___x_1974_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1973_;
}
v_reusejp_1973_:
{
return v___x_1974_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_1979_, lean_object* v_x_1980_){
_start:
{
if (lean_obj_tag(v_x_1980_) == 0)
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_box(0);
return v___x_1981_;
}
else
{
lean_object* v_key_1982_; lean_object* v_value_1983_; lean_object* v_tail_1984_; uint8_t v___x_1985_; 
v_key_1982_ = lean_ctor_get(v_x_1980_, 0);
v_value_1983_ = lean_ctor_get(v_x_1980_, 1);
v_tail_1984_ = lean_ctor_get(v_x_1980_, 2);
v___x_1985_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1982_, v_a_1979_);
if (v___x_1985_ == 0)
{
v_x_1980_ = v_tail_1984_;
goto _start;
}
else
{
lean_object* v___x_1987_; 
lean_inc(v_value_1983_);
v___x_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1987_, 0, v_value_1983_);
return v___x_1987_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_1988_, lean_object* v_x_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_1988_, v_x_1989_);
lean_dec(v_x_1989_);
lean_dec_ref(v_a_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v_buckets_1993_; lean_object* v_parserName_1994_; lean_object* v_pos_1995_; lean_object* v___x_1996_; uint64_t v___x_1997_; uint64_t v___y_1999_; 
v_buckets_1993_ = lean_ctor_get(v_m_1991_, 1);
v_parserName_1994_ = lean_ctor_get(v_a_1992_, 1);
v_pos_1995_ = lean_ctor_get(v_a_1992_, 2);
v___x_1996_ = lean_array_get_size(v_buckets_1993_);
v___x_1997_ = l_String_instHashableRaw_hash(v_pos_1995_);
if (lean_obj_tag(v_parserName_1994_) == 0)
{
uint64_t v___x_2014_; 
v___x_2014_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1999_ = v___x_2014_;
goto v___jp_1998_;
}
else
{
uint64_t v_hash_2015_; 
v_hash_2015_ = lean_ctor_get_uint64(v_parserName_1994_, sizeof(void*)*2);
v___y_1999_ = v_hash_2015_;
goto v___jp_1998_;
}
v___jp_1998_:
{
uint64_t v___x_2000_; uint64_t v___x_2001_; uint64_t v___x_2002_; uint64_t v_fold_2003_; uint64_t v___x_2004_; uint64_t v___x_2005_; uint64_t v___x_2006_; size_t v___x_2007_; size_t v___x_2008_; size_t v___x_2009_; size_t v___x_2010_; size_t v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2000_ = lean_uint64_mix_hash(v___x_1997_, v___y_1999_);
v___x_2001_ = 32ULL;
v___x_2002_ = lean_uint64_shift_right(v___x_2000_, v___x_2001_);
v_fold_2003_ = lean_uint64_xor(v___x_2000_, v___x_2002_);
v___x_2004_ = 16ULL;
v___x_2005_ = lean_uint64_shift_right(v_fold_2003_, v___x_2004_);
v___x_2006_ = lean_uint64_xor(v_fold_2003_, v___x_2005_);
v___x_2007_ = lean_uint64_to_usize(v___x_2006_);
v___x_2008_ = lean_usize_of_nat(v___x_1996_);
v___x_2009_ = ((size_t)1ULL);
v___x_2010_ = lean_usize_sub(v___x_2008_, v___x_2009_);
v___x_2011_ = lean_usize_land(v___x_2007_, v___x_2010_);
v___x_2012_ = lean_array_uget_borrowed(v_buckets_1993_, v___x_2011_);
v___x_2013_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_1992_, v___x_2012_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_2016_, lean_object* v_a_2017_){
_start:
{
lean_object* v_res_2018_; 
v_res_2018_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2016_, v_a_2017_);
lean_dec_ref(v_a_2017_);
lean_dec_ref(v_m_2016_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_2019_, lean_object* v_p_2020_, lean_object* v_c_2021_, lean_object* v_s_2022_){
_start:
{
lean_object* v_cache_2023_; lean_object* v_toCacheableParserContext_2024_; lean_object* v_stxStack_2025_; lean_object* v_pos_2026_; lean_object* v_recoveredErrors_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2076_; 
v_cache_2023_ = lean_ctor_get(v_s_2022_, 3);
lean_inc_ref(v_cache_2023_);
v_toCacheableParserContext_2024_ = lean_ctor_get(v_c_2021_, 2);
v_stxStack_2025_ = lean_ctor_get(v_s_2022_, 0);
v_pos_2026_ = lean_ctor_get(v_s_2022_, 2);
v_recoveredErrors_2027_ = lean_ctor_get(v_s_2022_, 5);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_s_2022_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; lean_object* v_unused_2078_; lean_object* v_unused_2079_; 
v_unused_2077_ = lean_ctor_get(v_s_2022_, 4);
lean_dec(v_unused_2077_);
v_unused_2078_ = lean_ctor_get(v_s_2022_, 3);
lean_dec(v_unused_2078_);
v_unused_2079_ = lean_ctor_get(v_s_2022_, 1);
lean_dec(v_unused_2079_);
v___x_2029_ = v_s_2022_;
v_isShared_2030_ = v_isSharedCheck_2076_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_recoveredErrors_2027_);
lean_inc(v_pos_2026_);
lean_inc(v_stxStack_2025_);
lean_dec(v_s_2022_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2076_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v_parserCache_2031_; lean_object* v_key_2032_; lean_object* v___x_2033_; 
v_parserCache_2031_ = lean_ctor_get(v_cache_2023_, 1);
lean_inc(v_pos_2026_);
lean_inc_ref(v_toCacheableParserContext_2024_);
v_key_2032_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_2032_, 0, v_toCacheableParserContext_2024_);
lean_ctor_set(v_key_2032_, 1, v_parserName_2019_);
lean_ctor_set(v_key_2032_, 2, v_pos_2026_);
v___x_2033_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_2031_, v_key_2032_);
if (lean_obj_tag(v___x_2033_) == 1)
{
lean_object* v_val_2034_; lean_object* v_stx_2035_; lean_object* v_lhsPrec_2036_; lean_object* v_newPos_2037_; lean_object* v_errorMsg_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
lean_dec_ref_known(v_key_2032_, 3);
lean_dec(v_pos_2026_);
lean_dec_ref(v_c_2021_);
lean_dec_ref(v_p_2020_);
v_val_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_val_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v_stx_2035_ = lean_ctor_get(v_val_2034_, 0);
lean_inc(v_stx_2035_);
v_lhsPrec_2036_ = lean_ctor_get(v_val_2034_, 1);
lean_inc(v_lhsPrec_2036_);
v_newPos_2037_ = lean_ctor_get(v_val_2034_, 2);
lean_inc(v_newPos_2037_);
v_errorMsg_2038_ = lean_ctor_get(v_val_2034_, 3);
lean_inc(v_errorMsg_2038_);
lean_dec(v_val_2034_);
v___x_2039_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_2025_, v_stx_2035_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v_errorMsg_2038_);
lean_ctor_set(v___x_2029_, 2, v_newPos_2037_);
lean_ctor_set(v___x_2029_, 1, v_lhsPrec_2036_);
lean_ctor_set(v___x_2029_, 0, v___x_2039_);
v___x_2041_ = v___x_2029_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
lean_ctor_set(v_reuseFailAlloc_2042_, 1, v_lhsPrec_2036_);
lean_ctor_set(v_reuseFailAlloc_2042_, 2, v_newPos_2037_);
lean_ctor_set(v_reuseFailAlloc_2042_, 3, v_cache_2023_);
lean_ctor_set(v_reuseFailAlloc_2042_, 4, v_errorMsg_2038_);
lean_ctor_set(v_reuseFailAlloc_2042_, 5, v_recoveredErrors_2027_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
else
{
lean_object* v_raw_2043_; lean_object* v_initStackSz_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
lean_dec(v___x_2033_);
v_raw_2043_ = lean_ctor_get(v_stxStack_2025_, 0);
v_initStackSz_2044_ = lean_array_get_size(v_raw_2043_);
v___x_2045_ = lean_unsigned_to_nat(0u);
v___x_2046_ = lean_box(0);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 4, v___x_2046_);
lean_ctor_set(v___x_2029_, 1, v___x_2045_);
v___x_2048_ = v___x_2029_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_stxStack_2025_);
lean_ctor_set(v_reuseFailAlloc_2075_, 1, v___x_2045_);
lean_ctor_set(v_reuseFailAlloc_2075_, 2, v_pos_2026_);
lean_ctor_set(v_reuseFailAlloc_2075_, 3, v_cache_2023_);
lean_ctor_set(v_reuseFailAlloc_2075_, 4, v___x_2046_);
lean_ctor_set(v_reuseFailAlloc_2075_, 5, v_recoveredErrors_2027_);
v___x_2048_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v_s_2049_; lean_object* v_cache_2050_; lean_object* v_stxStack_2051_; lean_object* v_lhsPrec_2052_; lean_object* v_pos_2053_; lean_object* v_errorMsg_2054_; lean_object* v_recoveredErrors_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2074_; 
v_s_2049_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_2044_, v_p_2020_, v_c_2021_, v___x_2048_);
v_cache_2050_ = lean_ctor_get(v_s_2049_, 3);
v_stxStack_2051_ = lean_ctor_get(v_s_2049_, 0);
v_lhsPrec_2052_ = lean_ctor_get(v_s_2049_, 1);
v_pos_2053_ = lean_ctor_get(v_s_2049_, 2);
v_errorMsg_2054_ = lean_ctor_get(v_s_2049_, 4);
v_recoveredErrors_2055_ = lean_ctor_get(v_s_2049_, 5);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_s_2049_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2057_ = v_s_2049_;
v_isShared_2058_ = v_isSharedCheck_2074_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_recoveredErrors_2055_);
lean_inc(v_errorMsg_2054_);
lean_inc(v_cache_2050_);
lean_inc(v_pos_2053_);
lean_inc(v_lhsPrec_2052_);
lean_inc(v_stxStack_2051_);
lean_dec(v_s_2049_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2074_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v_tokenCache_2059_; lean_object* v_parserCache_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2073_; 
v_tokenCache_2059_ = lean_ctor_get(v_cache_2050_, 0);
v_parserCache_2060_ = lean_ctor_get(v_cache_2050_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_cache_2050_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2062_ = v_cache_2050_;
v_isShared_2063_ = v_isSharedCheck_2073_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_parserCache_2060_);
lean_inc(v_tokenCache_2059_);
lean_dec(v_cache_2050_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2073_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2064_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2051_);
lean_inc(v_errorMsg_2054_);
lean_inc(v_pos_2053_);
lean_inc(v_lhsPrec_2052_);
v___x_2065_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v_lhsPrec_2052_);
lean_ctor_set(v___x_2065_, 2, v_pos_2053_);
lean_ctor_set(v___x_2065_, 3, v_errorMsg_2054_);
v___x_2066_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_2060_, v_key_2032_, v___x_2065_);
if (v_isShared_2063_ == 0)
{
lean_ctor_set(v___x_2062_, 1, v___x_2066_);
v___x_2068_ = v___x_2062_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_tokenCache_2059_);
lean_ctor_set(v_reuseFailAlloc_2072_, 1, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2070_; 
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 3, v___x_2068_);
v___x_2070_ = v___x_2057_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_stxStack_2051_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_lhsPrec_2052_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_pos_2053_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_errorMsg_2054_);
lean_ctor_set(v_reuseFailAlloc_2071_, 5, v_recoveredErrors_2055_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2080_, lean_object* v_m_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2081_, v_a_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2084_, lean_object* v_m_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_res_2087_; 
v_res_2087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2084_, v_m_2085_, v_a_2086_);
lean_dec_ref(v_a_2086_);
lean_dec_ref(v_m_2085_);
return v_res_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2088_, lean_object* v_m_2089_, lean_object* v_a_2090_, lean_object* v_b_2091_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2089_, v_a_2090_, v_b_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2093_, lean_object* v_a_2094_, lean_object* v_x_2095_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2094_, v_x_2095_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2097_, lean_object* v_a_2098_, lean_object* v_x_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2097_, v_a_2098_, v_x_2099_);
lean_dec(v_x_2099_);
lean_dec_ref(v_a_2098_);
return v_res_2100_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2101_, lean_object* v_a_2102_, lean_object* v_x_2103_){
_start:
{
uint8_t v___x_2104_; 
v___x_2104_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2102_, v_x_2103_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2105_, lean_object* v_a_2106_, lean_object* v_x_2107_){
_start:
{
uint8_t v_res_2108_; lean_object* v_r_2109_; 
v_res_2108_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2105_, v_a_2106_, v_x_2107_);
lean_dec(v_x_2107_);
lean_dec_ref(v_a_2106_);
v_r_2109_ = lean_box(v_res_2108_);
return v_r_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2110_, lean_object* v_data_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2113_, lean_object* v_a_2114_, lean_object* v_b_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2114_, v_b_2115_, v_x_2116_);
return v___x_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2118_, lean_object* v_i_2119_, lean_object* v_source_2120_, lean_object* v_target_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2119_, v_source_2120_, v_target_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2123_, lean_object* v_x_2124_, lean_object* v_x_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2124_, v_x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2127_, lean_object* v_p_2128_){
_start:
{
lean_object* v_info_2129_; lean_object* v_fn_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2138_; 
v_info_2129_ = lean_ctor_get(v_p_2128_, 0);
v_fn_2130_ = lean_ctor_get(v_p_2128_, 1);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_p_2128_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2132_ = v_p_2128_;
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_fn_2130_);
lean_inc(v_info_2129_);
lean_dec(v_p_2128_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2138_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2134_; lean_object* v___x_2136_; 
v___x_2134_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2134_, 0, v_parserName_2127_);
lean_closure_set(v___x_2134_, 1, v_fn_2130_);
if (v_isShared_2133_ == 0)
{
lean_ctor_set(v___x_2132_, 1, v___x_2134_);
v___x_2136_ = v___x_2132_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_info_2129_);
lean_ctor_set(v_reuseFailAlloc_2137_, 1, v___x_2134_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2147_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2148_ = l_Lean_addBuiltinDocString(v___x_2146_, v___x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2150_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2158_, lean_object* v_ictx_2159_, lean_object* v_pmctx_2160_, lean_object* v_tokens_2161_, lean_object* v_s_2162_){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__1));
v___x_2164_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2164_, 0, v_ictx_2159_);
lean_ctor_set(v___x_2164_, 1, v_pmctx_2160_);
lean_ctor_set(v___x_2164_, 2, v___x_2163_);
lean_ctor_set(v___x_2164_, 3, v_tokens_2161_);
v___x_2165_ = lean_apply_2(v_p_2158_, v___x_2164_, v_s_2162_);
return v___x_2165_;
}
}
lean_object* runtime_initialize_Lean_Data_Trie(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Extension(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Parser_Types(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
