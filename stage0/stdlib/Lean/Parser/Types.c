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
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext_beq___boxed(lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Parser_ParserFn_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Parser_ParserFn_run___closed__0 = (const lean_object*)&l_Lean_Parser_ParserFn_run___closed__0_value;
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
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
if (lean_obj_tag(v_x_464_) == 0)
{
if (lean_obj_tag(v_x_465_) == 0)
{
uint8_t v___x_466_; 
v___x_466_ = 1;
return v___x_466_;
}
else
{
uint8_t v___x_467_; 
v___x_467_ = 0;
return v___x_467_;
}
}
else
{
if (lean_obj_tag(v_x_465_) == 0)
{
uint8_t v___x_468_; 
v___x_468_ = 0;
return v___x_468_;
}
else
{
lean_object* v_val_469_; lean_object* v_val_470_; uint8_t v___x_471_; 
v_val_469_ = lean_ctor_get(v_x_464_, 0);
v_val_470_ = lean_ctor_get(v_x_465_, 0);
v___x_471_ = lean_string_dec_eq(v_val_469_, v_val_470_);
return v___x_471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___boxed(lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
uint8_t v_res_474_; lean_object* v_r_475_; 
v_res_474_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(v_x_472_, v_x_473_);
lean_dec(v_x_473_);
lean_dec(v_x_472_);
v_r_475_ = lean_box(v_res_474_);
return v_r_475_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext_beq(lean_object* v_x_476_, lean_object* v_x_477_){
_start:
{
lean_object* v_prec_478_; lean_object* v_quotDepth_479_; uint8_t v_suppressInsideQuot_480_; lean_object* v_savedPos_x3f_481_; lean_object* v_forbiddenTk_x3f_482_; lean_object* v_prec_483_; lean_object* v_quotDepth_484_; uint8_t v_suppressInsideQuot_485_; lean_object* v_savedPos_x3f_486_; lean_object* v_forbiddenTk_x3f_487_; uint8_t v___y_489_; uint8_t v___x_492_; 
v_prec_478_ = lean_ctor_get(v_x_476_, 0);
v_quotDepth_479_ = lean_ctor_get(v_x_476_, 1);
v_suppressInsideQuot_480_ = lean_ctor_get_uint8(v_x_476_, sizeof(void*)*4);
v_savedPos_x3f_481_ = lean_ctor_get(v_x_476_, 2);
v_forbiddenTk_x3f_482_ = lean_ctor_get(v_x_476_, 3);
v_prec_483_ = lean_ctor_get(v_x_477_, 0);
v_quotDepth_484_ = lean_ctor_get(v_x_477_, 1);
v_suppressInsideQuot_485_ = lean_ctor_get_uint8(v_x_477_, sizeof(void*)*4);
v_savedPos_x3f_486_ = lean_ctor_get(v_x_477_, 2);
v_forbiddenTk_x3f_487_ = lean_ctor_get(v_x_477_, 3);
v___x_492_ = lean_nat_dec_eq(v_prec_478_, v_prec_483_);
if (v___x_492_ == 0)
{
return v___x_492_;
}
else
{
uint8_t v___x_493_; 
v___x_493_ = lean_nat_dec_eq(v_quotDepth_479_, v_quotDepth_484_);
if (v___x_493_ == 0)
{
return v___x_493_;
}
else
{
if (v_suppressInsideQuot_480_ == 0)
{
if (v_suppressInsideQuot_485_ == 0)
{
v___y_489_ = v___x_493_;
goto v___jp_488_;
}
else
{
return v_suppressInsideQuot_480_;
}
}
else
{
v___y_489_ = v_suppressInsideQuot_485_;
goto v___jp_488_;
}
}
}
v___jp_488_:
{
if (v___y_489_ == 0)
{
return v___y_489_;
}
else
{
uint8_t v___x_490_; 
v___x_490_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(v_savedPos_x3f_481_, v_savedPos_x3f_486_);
if (v___x_490_ == 0)
{
return v___x_490_;
}
else
{
uint8_t v___x_491_; 
v___x_491_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(v_forbiddenTk_x3f_482_, v_forbiddenTk_x3f_487_);
return v___x_491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext_beq___boxed(lean_object* v_x_494_, lean_object* v_x_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Lean_Parser_instBEqCacheableParserContext_beq(v_x_494_, v_x_495_);
lean_dec_ref(v_x_495_);
lean_dec_ref(v_x_494_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
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
lean_inc(v_unexpectedTk_557_);
v_unexpected_558_ = lean_ctor_get(v_x_555_, 1);
lean_inc_ref(v_unexpected_558_);
v_expected_559_ = lean_ctor_get(v_x_555_, 2);
lean_inc(v_expected_559_);
lean_dec_ref(v_x_555_);
v_unexpectedTk_560_ = lean_ctor_get(v_x_556_, 0);
lean_inc(v_unexpectedTk_560_);
v_unexpected_561_ = lean_ctor_get(v_x_556_, 1);
lean_inc_ref(v_unexpected_561_);
v_expected_562_ = lean_ctor_get(v_x_556_, 2);
lean_inc(v_expected_562_);
lean_dec_ref(v_x_556_);
v___x_563_ = l_Lean_Syntax_structEq(v_unexpectedTk_557_, v_unexpectedTk_560_);
if (v___x_563_ == 0)
{
lean_dec(v_expected_562_);
lean_dec_ref(v_unexpected_561_);
lean_dec(v_expected_559_);
lean_dec_ref(v_unexpected_558_);
return v___x_563_;
}
else
{
uint8_t v___x_564_; 
v___x_564_ = lean_string_dec_eq(v_unexpected_558_, v_unexpected_561_);
lean_dec_ref(v_unexpected_561_);
lean_dec_ref(v_unexpected_558_);
if (v___x_564_ == 0)
{
lean_dec(v_expected_562_);
lean_dec(v_expected_559_);
return v___x_564_;
}
else
{
uint8_t v___x_565_; 
v___x_565_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_559_, v_expected_562_);
lean_dec(v_expected_562_);
lean_dec(v_expected_559_);
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
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object* v_as_590_){
_start:
{
lean_object* v___f_591_; lean_object* v___x_592_; 
v___f_591_ = ((lean_object*)(l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0));
v___x_592_ = l_List_eraseRepsBy___redArg(v___f_591_, v_as_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object* v_hi_593_, lean_object* v_pivot_594_, lean_object* v_as_595_, lean_object* v_i_596_, lean_object* v_k_597_){
_start:
{
uint8_t v___x_598_; 
v___x_598_ = lean_nat_dec_lt(v_k_597_, v_hi_593_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; lean_object* v___x_600_; 
lean_dec(v_k_597_);
v___x_599_ = lean_array_fswap(v_as_595_, v_i_596_, v_hi_593_);
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v_i_596_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; uint8_t v___x_602_; 
v___x_601_ = lean_array_fget_borrowed(v_as_595_, v_k_597_);
v___x_602_ = lean_string_dec_lt(v___x_601_, v_pivot_594_);
if (v___x_602_ == 0)
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_add(v_k_597_, v___x_603_);
lean_dec(v_k_597_);
v_k_597_ = v___x_604_;
goto _start;
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_606_ = lean_array_fswap(v_as_595_, v_i_596_, v_k_597_);
v___x_607_ = lean_unsigned_to_nat(1u);
v___x_608_ = lean_nat_add(v_i_596_, v___x_607_);
lean_dec(v_i_596_);
v___x_609_ = lean_nat_add(v_k_597_, v___x_607_);
lean_dec(v_k_597_);
v_as_595_ = v___x_606_;
v_i_596_ = v___x_608_;
v_k_597_ = v___x_609_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object* v_hi_611_, lean_object* v_pivot_612_, lean_object* v_as_613_, lean_object* v_i_614_, lean_object* v_k_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_611_, v_pivot_612_, v_as_613_, v_i_614_, v_k_615_);
lean_dec_ref(v_pivot_612_);
lean_dec(v_hi_611_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_n_617_, lean_object* v_as_618_, lean_object* v_lo_619_, lean_object* v_hi_620_){
_start:
{
lean_object* v___y_622_; uint8_t v___x_632_; 
v___x_632_ = lean_nat_dec_lt(v_lo_619_, v_hi_620_);
if (v___x_632_ == 0)
{
lean_dec(v_lo_619_);
return v_as_618_;
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_mid_635_; lean_object* v___y_637_; lean_object* v___y_643_; lean_object* v___x_648_; lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_633_ = lean_nat_add(v_lo_619_, v_hi_620_);
v___x_634_ = lean_unsigned_to_nat(1u);
v_mid_635_ = lean_nat_shiftr(v___x_633_, v___x_634_);
lean_dec(v___x_633_);
v___x_648_ = lean_array_fget_borrowed(v_as_618_, v_mid_635_);
v___x_649_ = lean_array_fget_borrowed(v_as_618_, v_lo_619_);
v___x_650_ = lean_string_dec_lt(v___x_648_, v___x_649_);
if (v___x_650_ == 0)
{
v___y_643_ = v_as_618_;
goto v___jp_642_;
}
else
{
lean_object* v___x_651_; 
v___x_651_ = lean_array_fswap(v_as_618_, v_lo_619_, v_mid_635_);
v___y_643_ = v___x_651_;
goto v___jp_642_;
}
v___jp_636_:
{
lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_638_ = lean_array_fget_borrowed(v___y_637_, v_mid_635_);
v___x_639_ = lean_array_fget_borrowed(v___y_637_, v_hi_620_);
v___x_640_ = lean_string_dec_lt(v___x_638_, v___x_639_);
if (v___x_640_ == 0)
{
lean_dec(v_mid_635_);
v___y_622_ = v___y_637_;
goto v___jp_621_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = lean_array_fswap(v___y_637_, v_mid_635_, v_hi_620_);
lean_dec(v_mid_635_);
v___y_622_ = v___x_641_;
goto v___jp_621_;
}
}
v___jp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_644_ = lean_array_fget_borrowed(v___y_643_, v_hi_620_);
v___x_645_ = lean_array_fget_borrowed(v___y_643_, v_lo_619_);
v___x_646_ = lean_string_dec_lt(v___x_644_, v___x_645_);
if (v___x_646_ == 0)
{
v___y_637_ = v___y_643_;
goto v___jp_636_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_array_fswap(v___y_643_, v_lo_619_, v_hi_620_);
v___y_637_ = v___x_647_;
goto v___jp_636_;
}
}
}
v___jp_621_:
{
lean_object* v_pivot_623_; lean_object* v___x_624_; lean_object* v_fst_625_; lean_object* v_snd_626_; uint8_t v___x_627_; 
v_pivot_623_ = lean_array_fget(v___y_622_, v_hi_620_);
lean_inc_n(v_lo_619_, 2);
v___x_624_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_620_, v_pivot_623_, v___y_622_, v_lo_619_, v_lo_619_);
lean_dec(v_pivot_623_);
v_fst_625_ = lean_ctor_get(v___x_624_, 0);
lean_inc(v_fst_625_);
v_snd_626_ = lean_ctor_get(v___x_624_, 1);
lean_inc(v_snd_626_);
lean_dec_ref(v___x_624_);
v___x_627_ = lean_nat_dec_le(v_hi_620_, v_fst_625_);
if (v___x_627_ == 0)
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_617_, v_snd_626_, v_lo_619_, v_fst_625_);
v___x_629_ = lean_unsigned_to_nat(1u);
v___x_630_ = lean_nat_add(v_fst_625_, v___x_629_);
lean_dec(v_fst_625_);
v_as_618_ = v___x_628_;
v_lo_619_ = v___x_630_;
goto _start;
}
else
{
lean_dec(v_fst_625_);
lean_dec(v_lo_619_);
return v_snd_626_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_n_652_, lean_object* v_as_653_, lean_object* v_lo_654_, lean_object* v_hi_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_652_, v_as_653_, v_lo_654_, v_hi_655_);
lean_dec(v_hi_655_);
lean_dec(v_n_652_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_659_){
_start:
{
lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v_unexpected_692_; lean_object* v_expected_693_; lean_object* v___y_695_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_unexpected_692_ = lean_ctor_get(v_e_659_, 1);
lean_inc_ref(v_unexpected_692_);
v_expected_693_ = lean_ctor_get(v_e_659_, 2);
lean_inc(v_expected_693_);
lean_dec_ref(v_e_659_);
v___x_705_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_706_ = lean_string_dec_eq(v_unexpected_692_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; 
v___x_707_ = lean_box(0);
v___x_708_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_708_, 0, v_unexpected_692_);
lean_ctor_set(v___x_708_, 1, v___x_707_);
v___y_695_ = v___x_708_;
goto v___jp_694_;
}
else
{
lean_object* v___x_709_; 
lean_dec_ref(v_unexpected_692_);
v___x_709_ = lean_box(0);
v___y_695_ = v___x_709_;
goto v___jp_694_;
}
v___jp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_663_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_664_ = l_List_appendTR___redArg(v___y_661_, v___y_662_);
v___x_665_ = l_String_intercalate(v___x_663_, v___x_664_);
return v___x_665_;
}
v___jp_666_:
{
lean_object* v___x_670_; lean_object* v_expected_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_670_ = lean_array_to_list(v___y_669_);
v_expected_671_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_670_);
v___x_672_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_673_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_671_);
v___x_674_ = lean_string_append(v___x_672_, v___x_673_);
lean_dec_ref(v___x_673_);
v___x_675_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
lean_ctor_set(v___x_675_, 1, v___y_667_);
v___y_661_ = v___y_668_;
v___y_662_ = v___x_675_;
goto v___jp_660_;
}
v___jp_676_:
{
lean_object* v___x_683_; 
v___x_683_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_678_, v___y_679_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec(v___y_678_);
v___y_667_ = v___y_677_;
v___y_668_ = v___y_680_;
v___y_669_ = v___x_683_;
goto v___jp_666_;
}
v___jp_684_:
{
uint8_t v___x_691_; 
v___x_691_ = lean_nat_dec_le(v___y_690_, v___y_689_);
if (v___x_691_ == 0)
{
lean_dec(v___y_689_);
lean_inc(v___y_690_);
v___y_677_ = v___y_685_;
v___y_678_ = v___y_686_;
v___y_679_ = v___y_687_;
v___y_680_ = v___y_688_;
v___y_681_ = v___y_690_;
v___y_682_ = v___y_690_;
goto v___jp_676_;
}
else
{
v___y_677_ = v___y_685_;
v___y_678_ = v___y_686_;
v___y_679_ = v___y_687_;
v___y_680_ = v___y_688_;
v___y_681_ = v___y_690_;
v___y_682_ = v___y_689_;
goto v___jp_676_;
}
}
v___jp_694_:
{
lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_696_ = lean_box(0);
v___x_697_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_693_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_698_ = lean_array_mk(v_expected_693_);
v___x_699_ = lean_array_get_size(v___x_698_);
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_nat_dec_eq(v___x_699_, v___x_700_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; 
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_sub(v___x_699_, v___x_702_);
v___x_704_ = lean_nat_dec_le(v___x_700_, v___x_703_);
if (v___x_704_ == 0)
{
lean_inc(v___x_703_);
v___y_685_ = v___x_696_;
v___y_686_ = v___x_699_;
v___y_687_ = v___x_698_;
v___y_688_ = v___y_695_;
v___y_689_ = v___x_703_;
v___y_690_ = v___x_703_;
goto v___jp_684_;
}
else
{
v___y_685_ = v___x_696_;
v___y_686_ = v___x_699_;
v___y_687_ = v___x_698_;
v___y_688_ = v___y_695_;
v___y_689_ = v___x_703_;
v___y_690_ = v___x_700_;
goto v___jp_684_;
}
}
else
{
v___y_667_ = v___x_696_;
v___y_668_ = v___y_695_;
v___y_669_ = v___x_698_;
goto v___jp_666_;
}
}
else
{
lean_dec(v_expected_693_);
v___y_661_ = v___y_695_;
v___y_662_ = v___x_696_;
goto v___jp_660_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_710_, lean_object* v_as_711_, lean_object* v_lo_712_, lean_object* v_hi_713_, lean_object* v_w_714_, lean_object* v_hlo_715_, lean_object* v_hhi_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_710_, v_as_711_, v_lo_712_, v_hi_713_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_718_, lean_object* v_as_719_, lean_object* v_lo_720_, lean_object* v_hi_721_, lean_object* v_w_722_, lean_object* v_hlo_723_, lean_object* v_hhi_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_718_, v_as_719_, v_lo_720_, v_hi_721_, v_w_722_, v_hlo_723_, v_hhi_724_);
lean_dec(v_hi_721_);
lean_dec(v_n_718_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object* v_n_726_, lean_object* v_lo_727_, lean_object* v_hi_728_, lean_object* v_hhi_729_, lean_object* v_pivot_730_, lean_object* v_as_731_, lean_object* v_i_732_, lean_object* v_k_733_, lean_object* v_ilo_734_, lean_object* v_ik_735_, lean_object* v_w_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_728_, v_pivot_730_, v_as_731_, v_i_732_, v_k_733_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object* v_n_738_, lean_object* v_lo_739_, lean_object* v_hi_740_, lean_object* v_hhi_741_, lean_object* v_pivot_742_, lean_object* v_as_743_, lean_object* v_i_744_, lean_object* v_k_745_, lean_object* v_ilo_746_, lean_object* v_ik_747_, lean_object* v_w_748_){
_start:
{
lean_object* v_res_749_; 
v_res_749_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_738_, v_lo_739_, v_hi_740_, v_hhi_741_, v_pivot_742_, v_as_743_, v_i_744_, v_k_745_, v_ilo_746_, v_ik_747_, v_w_748_);
lean_dec_ref(v_pivot_742_);
lean_dec(v_hi_740_);
lean_dec(v_lo_739_);
lean_dec(v_n_738_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_752_, lean_object* v_e_u2082_753_){
_start:
{
lean_object* v_unexpectedTk_754_; lean_object* v_unexpected_755_; lean_object* v_expected_756_; lean_object* v___y_758_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_unexpectedTk_754_ = lean_ctor_get(v_e_u2082_753_, 0);
lean_inc(v_unexpectedTk_754_);
v_unexpected_755_ = lean_ctor_get(v_e_u2082_753_, 1);
lean_inc_ref(v_unexpected_755_);
v_expected_756_ = lean_ctor_get(v_e_u2082_753_, 2);
lean_inc(v_expected_756_);
lean_dec_ref(v_e_u2082_753_);
v___x_770_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_771_ = lean_string_dec_eq(v_unexpected_755_, v___x_770_);
if (v___x_771_ == 0)
{
v___y_758_ = v_unexpected_755_;
goto v___jp_757_;
}
else
{
lean_object* v_unexpected_772_; 
lean_dec_ref(v_unexpected_755_);
v_unexpected_772_ = lean_ctor_get(v_e_u2081_752_, 1);
lean_inc_ref(v_unexpected_772_);
v___y_758_ = v_unexpected_772_;
goto v___jp_757_;
}
v___jp_757_:
{
lean_object* v_expected_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_767_; 
v_expected_759_ = lean_ctor_get(v_e_u2081_752_, 2);
v_isSharedCheck_767_ = !lean_is_exclusive(v_e_u2081_752_);
if (v_isSharedCheck_767_ == 0)
{
lean_object* v_unused_768_; lean_object* v_unused_769_; 
v_unused_768_ = lean_ctor_get(v_e_u2081_752_, 1);
lean_dec(v_unused_768_);
v_unused_769_ = lean_ctor_get(v_e_u2081_752_, 0);
lean_dec(v_unused_769_);
v___x_761_ = v_e_u2081_752_;
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_expected_759_);
lean_dec(v_e_u2081_752_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_767_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v___x_765_; 
v___x_763_ = l_List_appendTR___redArg(v_expected_759_, v_expected_756_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 2, v___x_763_);
lean_ctor_set(v___x_761_, 1, v___y_758_);
lean_ctor_set(v___x_761_, 0, v_unexpectedTk_754_);
v___x_765_ = v___x_761_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_unexpectedTk_754_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v___y_758_);
lean_ctor_set(v_reuseFailAlloc_766_, 2, v___x_763_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_773_, lean_object* v_x_774_){
_start:
{
lean_object* v_toCacheableParserContext_775_; lean_object* v_parserName_776_; lean_object* v_pos_777_; lean_object* v_toCacheableParserContext_778_; lean_object* v_parserName_779_; lean_object* v_pos_780_; uint8_t v___x_781_; 
v_toCacheableParserContext_775_ = lean_ctor_get(v_x_773_, 0);
v_parserName_776_ = lean_ctor_get(v_x_773_, 1);
v_pos_777_ = lean_ctor_get(v_x_773_, 2);
v_toCacheableParserContext_778_ = lean_ctor_get(v_x_774_, 0);
v_parserName_779_ = lean_ctor_get(v_x_774_, 1);
v_pos_780_ = lean_ctor_get(v_x_774_, 2);
v___x_781_ = l_Lean_Parser_instBEqCacheableParserContext_beq(v_toCacheableParserContext_775_, v_toCacheableParserContext_778_);
if (v___x_781_ == 0)
{
return v___x_781_;
}
else
{
uint8_t v___x_782_; 
v___x_782_ = lean_name_eq(v_parserName_776_, v_parserName_779_);
if (v___x_782_ == 0)
{
return v___x_782_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = lean_nat_dec_eq(v_pos_777_, v_pos_780_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_784_, v_x_785_);
lean_dec_ref(v_x_785_);
lean_dec_ref(v_x_784_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* v_k_790_){
_start:
{
lean_object* v_parserName_791_; lean_object* v_pos_792_; uint64_t v___x_793_; 
v_parserName_791_ = lean_ctor_get(v_k_790_, 1);
v_pos_792_ = lean_ctor_get(v_k_790_, 2);
v___x_793_ = l_String_instHashableRaw_hash(v_pos_792_);
if (lean_obj_tag(v_parserName_791_) == 0)
{
uint64_t v___x_794_; uint64_t v___x_795_; 
v___x_794_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_795_ = lean_uint64_mix_hash(v___x_793_, v___x_794_);
return v___x_795_;
}
else
{
uint64_t v_hash_796_; uint64_t v___x_797_; 
v_hash_796_ = lean_ctor_get_uint64(v_parserName_791_, sizeof(void*)*2);
v___x_797_ = lean_uint64_mix_hash(v___x_793_, v_hash_796_);
return v___x_797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* v_k_798_){
_start:
{
uint64_t v_res_799_; lean_object* v_r_800_; 
v_res_799_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_798_);
lean_dec_ref(v_k_798_);
v_r_800_ = lean_box_uint64(v_res_799_);
return v_r_800_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0(void){
_start:
{
uint32_t v___x_803_; lean_object* v___x_804_; 
v___x_803_ = 32;
v___x_804_ = l_Char_utf8Size(v___x_803_);
return v___x_804_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = lean_box(0);
v___x_806_ = lean_unsigned_to_nat(16u);
v___x_807_ = lean_mk_array(v___x_806_, v___x_805_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__2(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_809_ = lean_unsigned_to_nat(0u);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_809_);
lean_ctor_set(v___x_810_, 1, v___x_808_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_812_ = lean_string_utf8_byte_size(v_input_811_);
v___x_813_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_814_ = lean_nat_add(v___x_812_, v___x_813_);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_box(0);
v___x_817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_817_, 0, v___x_814_);
lean_ctor_set(v___x_817_, 1, v___x_815_);
lean_ctor_set(v___x_817_, 2, v___x_816_);
v___x_818_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_817_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l_Lean_Parser_initCacheForInput(v_input_820_);
lean_dec_ref(v_input_820_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_822_){
_start:
{
lean_object* v_raw_823_; lean_object* v_drop_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_raw_823_ = lean_ctor_get(v_stack_822_, 0);
lean_inc_ref(v_raw_823_);
v_drop_824_ = lean_ctor_get(v_stack_822_, 1);
lean_inc(v_drop_824_);
lean_dec_ref(v_stack_822_);
v___x_825_ = lean_array_get_size(v_raw_823_);
v___x_826_ = l_Array_toSubarray___redArg(v_raw_823_, v_drop_824_, v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_833_){
_start:
{
lean_object* v_raw_834_; lean_object* v_drop_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_raw_834_ = lean_ctor_get(v_stack_833_, 0);
v_drop_835_ = lean_ctor_get(v_stack_833_, 1);
v___x_836_ = lean_array_get_size(v_raw_834_);
v___x_837_ = lean_nat_sub(v___x_836_, v_drop_835_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Parser_SyntaxStack_size(v_stack_838_);
lean_dec_ref(v_stack_838_);
return v_res_839_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_840_){
_start:
{
lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_841_ = l_Lean_Parser_SyntaxStack_size(v_stack_840_);
v___x_842_ = lean_unsigned_to_nat(0u);
v___x_843_ = lean_nat_dec_eq(v___x_841_, v___x_842_);
lean_dec(v___x_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_844_){
_start:
{
uint8_t v_res_845_; lean_object* v_r_846_; 
v_res_845_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_844_);
lean_dec_ref(v_stack_844_);
v_r_846_ = lean_box(v_res_845_);
return v_r_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_847_, lean_object* v_n_848_){
_start:
{
lean_object* v_raw_849_; lean_object* v_drop_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_859_; 
v_raw_849_ = lean_ctor_get(v_stack_847_, 0);
v_drop_850_ = lean_ctor_get(v_stack_847_, 1);
v_isSharedCheck_859_ = !lean_is_exclusive(v_stack_847_);
if (v_isSharedCheck_859_ == 0)
{
v___x_852_ = v_stack_847_;
v_isShared_853_ = v_isSharedCheck_859_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_drop_850_);
lean_inc(v_raw_849_);
lean_dec(v_stack_847_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_859_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_857_; 
v___x_854_ = lean_nat_add(v_drop_850_, v_n_848_);
v___x_855_ = l_Array_shrink___redArg(v_raw_849_, v___x_854_);
lean_dec(v___x_854_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_855_);
v___x_857_ = v___x_852_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_858_, 1, v_drop_850_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_860_, lean_object* v_n_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_860_, v_n_861_);
lean_dec(v_n_861_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_863_, lean_object* v_a_864_){
_start:
{
lean_object* v_raw_865_; lean_object* v_drop_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_874_; 
v_raw_865_ = lean_ctor_get(v_stack_863_, 0);
v_drop_866_ = lean_ctor_get(v_stack_863_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v_stack_863_);
if (v_isSharedCheck_874_ == 0)
{
v___x_868_ = v_stack_863_;
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_drop_866_);
lean_inc(v_raw_865_);
lean_dec(v_stack_863_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_874_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_array_push(v_raw_865_, v_a_864_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_870_);
v___x_872_ = v___x_868_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_drop_866_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_875_){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_876_ = lean_unsigned_to_nat(0u);
v___x_877_ = l_Lean_Parser_SyntaxStack_size(v_stack_875_);
v___x_878_ = lean_nat_dec_lt(v___x_876_, v___x_877_);
lean_dec(v___x_877_);
if (v___x_878_ == 0)
{
return v_stack_875_;
}
else
{
lean_object* v_raw_879_; lean_object* v_drop_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_888_; 
v_raw_879_ = lean_ctor_get(v_stack_875_, 0);
v_drop_880_ = lean_ctor_get(v_stack_875_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_stack_875_);
if (v_isSharedCheck_888_ == 0)
{
v___x_882_ = v_stack_875_;
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_drop_880_);
lean_inc(v_raw_879_);
lean_dec(v_stack_875_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_888_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_884_ = lean_array_pop(v_raw_879_);
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 0, v___x_884_);
v___x_886_ = v___x_882_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_drop_880_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_889_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = lean_box(0);
v___x_891_ = lean_panic_fn_borrowed(v___x_890_, v_msg_889_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_895_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_896_ = lean_unsigned_to_nat(4u);
v___x_897_ = lean_unsigned_to_nat(305u);
v___x_898_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_899_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_900_ = l_mkPanicMessageWithDecl(v___x_899_, v___x_898_, v___x_897_, v___x_896_, v___x_895_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_901_){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = l_Lean_Parser_SyntaxStack_size(v_stack_901_);
v___x_904_ = lean_nat_dec_lt(v___x_902_, v___x_903_);
lean_dec(v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_906_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_905_);
return v___x_906_;
}
else
{
lean_object* v_raw_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_raw_907_ = lean_ctor_get(v_stack_901_, 0);
v___x_908_ = lean_box(0);
v___x_909_ = lean_array_get_size(v_raw_907_);
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_sub(v___x_909_, v___x_910_);
v___x_912_ = lean_array_get_borrowed(v___x_908_, v_raw_907_, v___x_911_);
lean_dec(v___x_911_);
lean_inc(v___x_912_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Parser_SyntaxStack_back(v_stack_913_);
lean_dec_ref(v_stack_913_);
return v_res_914_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_917_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_918_ = lean_unsigned_to_nat(4u);
v___x_919_ = lean_unsigned_to_nat(311u);
v___x_920_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_921_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_922_ = l_mkPanicMessageWithDecl(v___x_921_, v___x_920_, v___x_919_, v___x_918_, v___x_917_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_923_, lean_object* v_i_924_){
_start:
{
lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_925_ = l_Lean_Parser_SyntaxStack_size(v_stack_923_);
v___x_926_ = lean_nat_dec_lt(v_i_924_, v___x_925_);
lean_dec(v___x_925_);
if (v___x_926_ == 0)
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_928_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_927_);
return v___x_928_;
}
else
{
lean_object* v_raw_929_; lean_object* v_drop_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v_raw_929_ = lean_ctor_get(v_stack_923_, 0);
v_drop_930_ = lean_ctor_get(v_stack_923_, 1);
v___x_931_ = lean_box(0);
v___x_932_ = lean_nat_add(v_drop_930_, v_i_924_);
v___x_933_ = lean_array_get_borrowed(v___x_931_, v_raw_929_, v___x_932_);
lean_dec(v___x_932_);
lean_inc(v___x_933_);
return v___x_933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_934_, lean_object* v_i_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_934_, v_i_935_);
lean_dec(v_i_935_);
lean_dec_ref(v_stack_934_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_937_, lean_object* v_start_938_, lean_object* v_stop_939_){
_start:
{
lean_object* v_raw_940_; lean_object* v_drop_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v_raw_940_ = lean_ctor_get(v_stack_937_, 0);
v_drop_941_ = lean_ctor_get(v_stack_937_, 1);
v___x_942_ = lean_nat_add(v_drop_941_, v_start_938_);
v___x_943_ = lean_nat_add(v_drop_941_, v_stop_939_);
v___x_944_ = l_Array_extract___redArg(v_raw_940_, v___x_942_, v___x_943_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_945_, lean_object* v_start_946_, lean_object* v_stop_947_){
_start:
{
lean_object* v_res_948_; 
v_res_948_ = l_Lean_Parser_SyntaxStack_extract(v_stack_945_, v_start_946_, v_stop_947_);
lean_dec(v_stop_947_);
lean_dec(v_start_946_);
lean_dec_ref(v_stack_945_);
return v_res_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_949_, lean_object* v_stxs_950_){
_start:
{
lean_object* v_raw_951_; lean_object* v_drop_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_960_; 
v_raw_951_ = lean_ctor_get(v_stack_949_, 0);
v_drop_952_ = lean_ctor_get(v_stack_949_, 1);
v_isSharedCheck_960_ = !lean_is_exclusive(v_stack_949_);
if (v_isSharedCheck_960_ == 0)
{
v___x_954_ = v_stack_949_;
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_drop_952_);
lean_inc(v_raw_951_);
lean_dec(v_stack_949_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_960_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_956_; lean_object* v___x_958_; 
v___x_956_ = l_Array_append___redArg(v_raw_951_, v_stxs_950_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_956_);
v___x_958_ = v___x_954_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
lean_ctor_set(v_reuseFailAlloc_959_, 1, v_drop_952_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_961_, lean_object* v_stxs_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_961_, v_stxs_962_);
lean_dec_ref(v_stxs_962_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_964_, lean_object* v_stxs_965_){
_start:
{
lean_object* v_raw_966_; lean_object* v_drop_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_975_; 
v_raw_966_ = lean_ctor_get(v_stack_964_, 0);
v_drop_967_ = lean_ctor_get(v_stack_964_, 1);
v_isSharedCheck_975_ = !lean_is_exclusive(v_stack_964_);
if (v_isSharedCheck_975_ == 0)
{
v___x_969_ = v_stack_964_;
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_drop_967_);
lean_inc(v_raw_966_);
lean_dec(v_stack_964_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_975_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_971_; lean_object* v___x_973_; 
v___x_971_ = l_Array_append___redArg(v_raw_966_, v_stxs_965_);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_971_);
v___x_973_ = v___x_969_;
goto v_reusejp_972_;
}
else
{
lean_object* v_reuseFailAlloc_974_; 
v_reuseFailAlloc_974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_971_);
lean_ctor_set(v_reuseFailAlloc_974_, 1, v_drop_967_);
v___x_973_ = v_reuseFailAlloc_974_;
goto v_reusejp_972_;
}
v_reusejp_972_:
{
return v___x_973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_976_, lean_object* v_stxs_977_){
_start:
{
lean_object* v_res_978_; 
v_res_978_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_976_, v_stxs_977_);
lean_dec_ref(v_stxs_977_);
return v_res_978_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_981_){
_start:
{
lean_object* v_errorMsg_982_; lean_object* v___x_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v_errorMsg_982_ = lean_ctor_get(v_s_981_, 4);
lean_inc(v_errorMsg_982_);
lean_dec_ref(v_s_981_);
v___x_983_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_984_ = lean_box(0);
v___x_985_ = l_Option_instBEq_beq___redArg(v___x_983_, v_errorMsg_982_, v___x_984_);
if (v___x_985_ == 0)
{
uint8_t v___x_986_; 
v___x_986_ = 1;
return v___x_986_;
}
else
{
uint8_t v___x_987_; 
v___x_987_ = 0;
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_988_){
_start:
{
uint8_t v_res_989_; lean_object* v_r_990_; 
v_res_989_ = l_Lean_Parser_ParserState_hasError(v_s_988_);
v_r_990_ = lean_box(v_res_989_);
return v_r_990_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_991_){
_start:
{
lean_object* v_stxStack_992_; lean_object* v___x_993_; 
v_stxStack_992_ = lean_ctor_get(v_s_991_, 0);
v___x_993_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Parser_ParserState_stackSize(v_s_994_);
lean_dec_ref(v_s_994_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_996_, lean_object* v_iniStackSz_997_, lean_object* v_iniPos_998_){
_start:
{
lean_object* v_stxStack_999_; lean_object* v_lhsPrec_1000_; lean_object* v_cache_1001_; lean_object* v_recoveredErrors_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1011_; 
v_stxStack_999_ = lean_ctor_get(v_s_996_, 0);
v_lhsPrec_1000_ = lean_ctor_get(v_s_996_, 1);
v_cache_1001_ = lean_ctor_get(v_s_996_, 3);
v_recoveredErrors_1002_ = lean_ctor_get(v_s_996_, 5);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_s_996_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; lean_object* v_unused_1013_; 
v_unused_1012_ = lean_ctor_get(v_s_996_, 4);
lean_dec(v_unused_1012_);
v_unused_1013_ = lean_ctor_get(v_s_996_, 2);
lean_dec(v_unused_1013_);
v___x_1004_ = v_s_996_;
v_isShared_1005_ = v_isSharedCheck_1011_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_recoveredErrors_1002_);
lean_inc(v_cache_1001_);
lean_inc(v_lhsPrec_1000_);
lean_inc(v_stxStack_999_);
lean_dec(v_s_996_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1011_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1006_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_999_, v_iniStackSz_997_);
v___x_1007_ = lean_box(0);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 4, v___x_1007_);
lean_ctor_set(v___x_1004_, 2, v_iniPos_998_);
lean_ctor_set(v___x_1004_, 0, v___x_1006_);
v___x_1009_ = v___x_1004_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1006_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_lhsPrec_1000_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_iniPos_998_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v_cache_1001_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1010_, 5, v_recoveredErrors_1002_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_1014_, lean_object* v_iniStackSz_1015_, lean_object* v_iniPos_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Parser_ParserState_restore(v_s_1014_, v_iniStackSz_1015_, v_iniPos_1016_);
lean_dec(v_iniStackSz_1015_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_1018_, lean_object* v_pos_1019_){
_start:
{
lean_object* v_stxStack_1020_; lean_object* v_lhsPrec_1021_; lean_object* v_cache_1022_; lean_object* v_errorMsg_1023_; lean_object* v_recoveredErrors_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
v_stxStack_1020_ = lean_ctor_get(v_s_1018_, 0);
v_lhsPrec_1021_ = lean_ctor_get(v_s_1018_, 1);
v_cache_1022_ = lean_ctor_get(v_s_1018_, 3);
v_errorMsg_1023_ = lean_ctor_get(v_s_1018_, 4);
v_recoveredErrors_1024_ = lean_ctor_get(v_s_1018_, 5);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_s_1018_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v_s_1018_, 2);
lean_dec(v_unused_1032_);
v___x_1026_ = v_s_1018_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_recoveredErrors_1024_);
lean_inc(v_errorMsg_1023_);
lean_inc(v_cache_1022_);
lean_inc(v_lhsPrec_1021_);
lean_inc(v_stxStack_1020_);
lean_dec(v_s_1018_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
lean_ctor_set(v___x_1026_, 2, v_pos_1019_);
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_stxStack_1020_);
lean_ctor_set(v_reuseFailAlloc_1030_, 1, v_lhsPrec_1021_);
lean_ctor_set(v_reuseFailAlloc_1030_, 2, v_pos_1019_);
lean_ctor_set(v_reuseFailAlloc_1030_, 3, v_cache_1022_);
lean_ctor_set(v_reuseFailAlloc_1030_, 4, v_errorMsg_1023_);
lean_ctor_set(v_reuseFailAlloc_1030_, 5, v_recoveredErrors_1024_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_1033_, lean_object* v_cache_1034_){
_start:
{
lean_object* v_stxStack_1035_; lean_object* v_lhsPrec_1036_; lean_object* v_pos_1037_; lean_object* v_errorMsg_1038_; lean_object* v_recoveredErrors_1039_; lean_object* v___x_1041_; uint8_t v_isShared_1042_; uint8_t v_isSharedCheck_1046_; 
v_stxStack_1035_ = lean_ctor_get(v_s_1033_, 0);
v_lhsPrec_1036_ = lean_ctor_get(v_s_1033_, 1);
v_pos_1037_ = lean_ctor_get(v_s_1033_, 2);
v_errorMsg_1038_ = lean_ctor_get(v_s_1033_, 4);
v_recoveredErrors_1039_ = lean_ctor_get(v_s_1033_, 5);
v_isSharedCheck_1046_ = !lean_is_exclusive(v_s_1033_);
if (v_isSharedCheck_1046_ == 0)
{
lean_object* v_unused_1047_; 
v_unused_1047_ = lean_ctor_get(v_s_1033_, 3);
lean_dec(v_unused_1047_);
v___x_1041_ = v_s_1033_;
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
else
{
lean_inc(v_recoveredErrors_1039_);
lean_inc(v_errorMsg_1038_);
lean_inc(v_pos_1037_);
lean_inc(v_lhsPrec_1036_);
lean_inc(v_stxStack_1035_);
lean_dec(v_s_1033_);
v___x_1041_ = lean_box(0);
v_isShared_1042_ = v_isSharedCheck_1046_;
goto v_resetjp_1040_;
}
v_resetjp_1040_:
{
lean_object* v___x_1044_; 
if (v_isShared_1042_ == 0)
{
lean_ctor_set(v___x_1041_, 3, v_cache_1034_);
v___x_1044_ = v___x_1041_;
goto v_reusejp_1043_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_stxStack_1035_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_lhsPrec_1036_);
lean_ctor_set(v_reuseFailAlloc_1045_, 2, v_pos_1037_);
lean_ctor_set(v_reuseFailAlloc_1045_, 3, v_cache_1034_);
lean_ctor_set(v_reuseFailAlloc_1045_, 4, v_errorMsg_1038_);
lean_ctor_set(v_reuseFailAlloc_1045_, 5, v_recoveredErrors_1039_);
v___x_1044_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1043_;
}
v_reusejp_1043_:
{
return v___x_1044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_1048_, lean_object* v_n_1049_){
_start:
{
lean_object* v_stxStack_1050_; lean_object* v_lhsPrec_1051_; lean_object* v_pos_1052_; lean_object* v_cache_1053_; lean_object* v_errorMsg_1054_; lean_object* v_recoveredErrors_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1063_; 
v_stxStack_1050_ = lean_ctor_get(v_s_1048_, 0);
v_lhsPrec_1051_ = lean_ctor_get(v_s_1048_, 1);
v_pos_1052_ = lean_ctor_get(v_s_1048_, 2);
v_cache_1053_ = lean_ctor_get(v_s_1048_, 3);
v_errorMsg_1054_ = lean_ctor_get(v_s_1048_, 4);
v_recoveredErrors_1055_ = lean_ctor_get(v_s_1048_, 5);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_s_1048_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1057_ = v_s_1048_;
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_recoveredErrors_1055_);
lean_inc(v_errorMsg_1054_);
lean_inc(v_cache_1053_);
lean_inc(v_pos_1052_);
lean_inc(v_lhsPrec_1051_);
lean_inc(v_stxStack_1050_);
lean_dec(v_s_1048_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1063_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1059_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1050_, v_n_1049_);
if (v_isShared_1058_ == 0)
{
lean_ctor_set(v___x_1057_, 0, v___x_1059_);
v___x_1061_ = v___x_1057_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_lhsPrec_1051_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_pos_1052_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_cache_1053_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v_errorMsg_1054_);
lean_ctor_set(v_reuseFailAlloc_1062_, 5, v_recoveredErrors_1055_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1064_){
_start:
{
lean_object* v_stxStack_1065_; lean_object* v_lhsPrec_1066_; lean_object* v_pos_1067_; lean_object* v_cache_1068_; lean_object* v_errorMsg_1069_; lean_object* v_recoveredErrors_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1078_; 
v_stxStack_1065_ = lean_ctor_get(v_s_1064_, 0);
v_lhsPrec_1066_ = lean_ctor_get(v_s_1064_, 1);
v_pos_1067_ = lean_ctor_get(v_s_1064_, 2);
v_cache_1068_ = lean_ctor_get(v_s_1064_, 3);
v_errorMsg_1069_ = lean_ctor_get(v_s_1064_, 4);
v_recoveredErrors_1070_ = lean_ctor_get(v_s_1064_, 5);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_s_1064_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1072_ = v_s_1064_;
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_recoveredErrors_1070_);
lean_inc(v_errorMsg_1069_);
lean_inc(v_cache_1068_);
lean_inc(v_pos_1067_);
lean_inc(v_lhsPrec_1066_);
lean_inc(v_stxStack_1065_);
lean_dec(v_s_1064_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1078_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1065_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 0, v___x_1074_);
v___x_1076_ = v___x_1072_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
lean_ctor_set(v_reuseFailAlloc_1077_, 1, v_lhsPrec_1066_);
lean_ctor_set(v_reuseFailAlloc_1077_, 2, v_pos_1067_);
lean_ctor_set(v_reuseFailAlloc_1077_, 3, v_cache_1068_);
lean_ctor_set(v_reuseFailAlloc_1077_, 4, v_errorMsg_1069_);
lean_ctor_set(v_reuseFailAlloc_1077_, 5, v_recoveredErrors_1070_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1079_, lean_object* v_iniStackSz_1080_){
_start:
{
lean_object* v_stxStack_1081_; lean_object* v_lhsPrec_1082_; lean_object* v_pos_1083_; lean_object* v_cache_1084_; lean_object* v_errorMsg_1085_; lean_object* v_recoveredErrors_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1094_; 
v_stxStack_1081_ = lean_ctor_get(v_s_1079_, 0);
v_lhsPrec_1082_ = lean_ctor_get(v_s_1079_, 1);
v_pos_1083_ = lean_ctor_get(v_s_1079_, 2);
v_cache_1084_ = lean_ctor_get(v_s_1079_, 3);
v_errorMsg_1085_ = lean_ctor_get(v_s_1079_, 4);
v_recoveredErrors_1086_ = lean_ctor_get(v_s_1079_, 5);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_s_1079_);
if (v_isSharedCheck_1094_ == 0)
{
v___x_1088_ = v_s_1079_;
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_recoveredErrors_1086_);
lean_inc(v_errorMsg_1085_);
lean_inc(v_cache_1084_);
lean_inc(v_pos_1083_);
lean_inc(v_lhsPrec_1082_);
lean_inc(v_stxStack_1081_);
lean_dec(v_s_1079_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1094_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1092_; 
v___x_1090_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1081_, v_iniStackSz_1080_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 0, v___x_1090_);
v___x_1092_ = v___x_1088_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_lhsPrec_1082_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_pos_1083_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_cache_1084_);
lean_ctor_set(v_reuseFailAlloc_1093_, 4, v_errorMsg_1085_);
lean_ctor_set(v_reuseFailAlloc_1093_, 5, v_recoveredErrors_1086_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1095_, lean_object* v_iniStackSz_1096_){
_start:
{
lean_object* v_res_1097_; 
v_res_1097_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1095_, v_iniStackSz_1096_);
lean_dec(v_iniStackSz_1096_);
return v_res_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1098_, lean_object* v_c_1099_, lean_object* v_pos_1100_){
_start:
{
lean_object* v_toInputContext_1101_; lean_object* v_stxStack_1102_; lean_object* v_lhsPrec_1103_; lean_object* v_cache_1104_; lean_object* v_errorMsg_1105_; lean_object* v_recoveredErrors_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1115_; 
v_toInputContext_1101_ = lean_ctor_get(v_c_1099_, 0);
v_stxStack_1102_ = lean_ctor_get(v_s_1098_, 0);
v_lhsPrec_1103_ = lean_ctor_get(v_s_1098_, 1);
v_cache_1104_ = lean_ctor_get(v_s_1098_, 3);
v_errorMsg_1105_ = lean_ctor_get(v_s_1098_, 4);
v_recoveredErrors_1106_ = lean_ctor_get(v_s_1098_, 5);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_s_1098_);
if (v_isSharedCheck_1115_ == 0)
{
lean_object* v_unused_1116_; 
v_unused_1116_ = lean_ctor_get(v_s_1098_, 2);
lean_dec(v_unused_1116_);
v___x_1108_ = v_s_1098_;
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_recoveredErrors_1106_);
lean_inc(v_errorMsg_1105_);
lean_inc(v_cache_1104_);
lean_inc(v_lhsPrec_1103_);
lean_inc(v_stxStack_1102_);
lean_dec(v_s_1098_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1115_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v_inputString_1110_; lean_object* v___x_1111_; lean_object* v___x_1113_; 
v_inputString_1110_ = lean_ctor_get(v_toInputContext_1101_, 0);
v___x_1111_ = lean_string_utf8_next(v_inputString_1110_, v_pos_1100_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 2, v___x_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_stxStack_1102_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_lhsPrec_1103_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_cache_1104_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_errorMsg_1105_);
lean_ctor_set(v_reuseFailAlloc_1114_, 5, v_recoveredErrors_1106_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1117_, lean_object* v_c_1118_, lean_object* v_pos_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l_Lean_Parser_ParserState_next(v_s_1117_, v_c_1118_, v_pos_1119_);
lean_dec(v_pos_1119_);
lean_dec_ref(v_c_1118_);
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1121_, lean_object* v_c_1122_, lean_object* v_pos_1123_){
_start:
{
lean_object* v_toInputContext_1124_; lean_object* v_stxStack_1125_; lean_object* v_lhsPrec_1126_; lean_object* v_cache_1127_; lean_object* v_errorMsg_1128_; lean_object* v_recoveredErrors_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1138_; 
v_toInputContext_1124_ = lean_ctor_get(v_c_1122_, 0);
v_stxStack_1125_ = lean_ctor_get(v_s_1121_, 0);
v_lhsPrec_1126_ = lean_ctor_get(v_s_1121_, 1);
v_cache_1127_ = lean_ctor_get(v_s_1121_, 3);
v_errorMsg_1128_ = lean_ctor_get(v_s_1121_, 4);
v_recoveredErrors_1129_ = lean_ctor_get(v_s_1121_, 5);
v_isSharedCheck_1138_ = !lean_is_exclusive(v_s_1121_);
if (v_isSharedCheck_1138_ == 0)
{
lean_object* v_unused_1139_; 
v_unused_1139_ = lean_ctor_get(v_s_1121_, 2);
lean_dec(v_unused_1139_);
v___x_1131_ = v_s_1121_;
v_isShared_1132_ = v_isSharedCheck_1138_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_recoveredErrors_1129_);
lean_inc(v_errorMsg_1128_);
lean_inc(v_cache_1127_);
lean_inc(v_lhsPrec_1126_);
lean_inc(v_stxStack_1125_);
lean_dec(v_s_1121_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1138_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v_inputString_1133_; lean_object* v___x_1134_; lean_object* v___x_1136_; 
v_inputString_1133_ = lean_ctor_get(v_toInputContext_1124_, 0);
v___x_1134_ = lean_string_utf8_next_fast(v_inputString_1133_, v_pos_1123_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 2, v___x_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_stxStack_1125_);
lean_ctor_set(v_reuseFailAlloc_1137_, 1, v_lhsPrec_1126_);
lean_ctor_set(v_reuseFailAlloc_1137_, 2, v___x_1134_);
lean_ctor_set(v_reuseFailAlloc_1137_, 3, v_cache_1127_);
lean_ctor_set(v_reuseFailAlloc_1137_, 4, v_errorMsg_1128_);
lean_ctor_set(v_reuseFailAlloc_1137_, 5, v_recoveredErrors_1129_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1140_, lean_object* v_c_1141_, lean_object* v_pos_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1140_, v_c_1141_, v_pos_1142_);
lean_dec(v_pos_1142_);
lean_dec_ref(v_c_1141_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1144_, lean_object* v_c_1145_, lean_object* v_pos_1146_, lean_object* v_h_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1144_, v_c_1145_, v_pos_1146_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1149_, lean_object* v_c_1150_, lean_object* v_pos_1151_, lean_object* v_h_1152_){
_start:
{
lean_object* v_res_1153_; 
v_res_1153_ = l_Lean_Parser_ParserState_next_x27(v_s_1149_, v_c_1150_, v_pos_1151_, v_h_1152_);
lean_dec(v_pos_1151_);
lean_dec_ref(v_c_1150_);
return v_res_1153_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1154_, lean_object* v_x_1155_){
_start:
{
if (lean_obj_tag(v_x_1154_) == 0)
{
if (lean_obj_tag(v_x_1155_) == 0)
{
uint8_t v___x_1156_; 
v___x_1156_ = 1;
return v___x_1156_;
}
else
{
uint8_t v___x_1157_; 
lean_dec_ref_known(v_x_1155_, 1);
v___x_1157_ = 0;
return v___x_1157_;
}
}
else
{
if (lean_obj_tag(v_x_1155_) == 0)
{
uint8_t v___x_1158_; 
lean_dec_ref_known(v_x_1154_, 1);
v___x_1158_ = 0;
return v___x_1158_;
}
else
{
lean_object* v_val_1159_; lean_object* v_val_1160_; uint8_t v___x_1161_; 
v_val_1159_ = lean_ctor_get(v_x_1154_, 0);
lean_inc(v_val_1159_);
lean_dec_ref_known(v_x_1154_, 1);
v_val_1160_ = lean_ctor_get(v_x_1155_, 0);
lean_inc(v_val_1160_);
lean_dec_ref_known(v_x_1155_, 1);
v___x_1161_ = l_Lean_Parser_instBEqError_beq(v_val_1159_, v_val_1160_);
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1162_, lean_object* v_x_1163_){
_start:
{
uint8_t v_res_1164_; lean_object* v_r_1165_; 
v_res_1164_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1162_, v_x_1163_);
v_r_1165_ = lean_box(v_res_1164_);
return v_r_1165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1166_, lean_object* v_k_1167_, lean_object* v_iniStackSz_1168_){
_start:
{
lean_object* v_stxStack_1169_; lean_object* v_lhsPrec_1170_; lean_object* v_pos_1171_; lean_object* v_cache_1172_; lean_object* v_errorMsg_1173_; lean_object* v_recoveredErrors_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1195_; 
v_stxStack_1169_ = lean_ctor_get(v_s_1166_, 0);
v_lhsPrec_1170_ = lean_ctor_get(v_s_1166_, 1);
v_pos_1171_ = lean_ctor_get(v_s_1166_, 2);
v_cache_1172_ = lean_ctor_get(v_s_1166_, 3);
v_errorMsg_1173_ = lean_ctor_get(v_s_1166_, 4);
v_recoveredErrors_1174_ = lean_ctor_get(v_s_1166_, 5);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_s_1166_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1176_ = v_s_1166_;
v_isShared_1177_ = v_isSharedCheck_1195_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_recoveredErrors_1174_);
lean_inc(v_errorMsg_1173_);
lean_inc(v_cache_1172_);
lean_inc(v_pos_1171_);
lean_inc(v_lhsPrec_1170_);
lean_inc(v_stxStack_1169_);
lean_dec(v_s_1166_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1195_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_box(0);
lean_inc(v_errorMsg_1173_);
v___x_1189_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1173_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; uint8_t v___x_1191_; 
v___x_1190_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1169_);
v___x_1191_ = lean_nat_dec_eq(v___x_1190_, v_iniStackSz_1168_);
lean_dec(v___x_1190_);
if (v___x_1191_ == 0)
{
goto v___jp_1178_;
}
else
{
lean_object* v___x_1192_; lean_object* v_stack_1193_; lean_object* v___x_1194_; 
lean_del_object(v___x_1176_);
lean_dec(v_k_1167_);
v___x_1192_ = lean_box(0);
v_stack_1193_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1169_, v___x_1192_);
v___x_1194_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1194_, 0, v_stack_1193_);
lean_ctor_set(v___x_1194_, 1, v_lhsPrec_1170_);
lean_ctor_set(v___x_1194_, 2, v_pos_1171_);
lean_ctor_set(v___x_1194_, 3, v_cache_1172_);
lean_ctor_set(v___x_1194_, 4, v_errorMsg_1173_);
lean_ctor_set(v___x_1194_, 5, v_recoveredErrors_1174_);
return v___x_1194_;
}
}
else
{
goto v___jp_1178_;
}
v___jp_1178_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v_newNode_1182_; lean_object* v_stack_1183_; lean_object* v_stack_1184_; lean_object* v___x_1186_; 
v___x_1179_ = lean_box(2);
v___x_1180_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1169_);
v___x_1181_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1169_, v_iniStackSz_1168_, v___x_1180_);
lean_dec(v___x_1180_);
v_newNode_1182_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1182_, 0, v___x_1179_);
lean_ctor_set(v_newNode_1182_, 1, v_k_1167_);
lean_ctor_set(v_newNode_1182_, 2, v___x_1181_);
v_stack_1183_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1169_, v_iniStackSz_1168_);
v_stack_1184_ = l_Lean_Parser_SyntaxStack_push(v_stack_1183_, v_newNode_1182_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 0, v_stack_1184_);
v___x_1186_ = v___x_1176_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_stack_1184_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_lhsPrec_1170_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_pos_1171_);
lean_ctor_set(v_reuseFailAlloc_1187_, 3, v_cache_1172_);
lean_ctor_set(v_reuseFailAlloc_1187_, 4, v_errorMsg_1173_);
lean_ctor_set(v_reuseFailAlloc_1187_, 5, v_recoveredErrors_1174_);
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
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1196_, lean_object* v_k_1197_, lean_object* v_iniStackSz_1198_){
_start:
{
lean_object* v_res_1199_; 
v_res_1199_ = l_Lean_Parser_ParserState_mkNode(v_s_1196_, v_k_1197_, v_iniStackSz_1198_);
lean_dec(v_iniStackSz_1198_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1200_, lean_object* v_k_1201_, lean_object* v_iniStackSz_1202_){
_start:
{
lean_object* v_stxStack_1203_; lean_object* v_lhsPrec_1204_; lean_object* v_pos_1205_; lean_object* v_cache_1206_; lean_object* v_errorMsg_1207_; lean_object* v_recoveredErrors_1208_; lean_object* v___x_1210_; uint8_t v_isShared_1211_; uint8_t v_isSharedCheck_1223_; 
v_stxStack_1203_ = lean_ctor_get(v_s_1200_, 0);
v_lhsPrec_1204_ = lean_ctor_get(v_s_1200_, 1);
v_pos_1205_ = lean_ctor_get(v_s_1200_, 2);
v_cache_1206_ = lean_ctor_get(v_s_1200_, 3);
v_errorMsg_1207_ = lean_ctor_get(v_s_1200_, 4);
v_recoveredErrors_1208_ = lean_ctor_get(v_s_1200_, 5);
v_isSharedCheck_1223_ = !lean_is_exclusive(v_s_1200_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1210_ = v_s_1200_;
v_isShared_1211_ = v_isSharedCheck_1223_;
goto v_resetjp_1209_;
}
else
{
lean_inc(v_recoveredErrors_1208_);
lean_inc(v_errorMsg_1207_);
lean_inc(v_cache_1206_);
lean_inc(v_pos_1205_);
lean_inc(v_lhsPrec_1204_);
lean_inc(v_stxStack_1203_);
lean_dec(v_s_1200_);
v___x_1210_ = lean_box(0);
v_isShared_1211_ = v_isSharedCheck_1223_;
goto v_resetjp_1209_;
}
v_resetjp_1209_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v_newNode_1217_; lean_object* v_stack_1218_; lean_object* v_stack_1219_; lean_object* v___x_1221_; 
v___x_1212_ = lean_box(2);
v___x_1213_ = lean_unsigned_to_nat(1u);
v___x_1214_ = lean_nat_sub(v_iniStackSz_1202_, v___x_1213_);
v___x_1215_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1203_);
v___x_1216_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1203_, v___x_1214_, v___x_1215_);
lean_dec(v___x_1215_);
v_newNode_1217_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1217_, 0, v___x_1212_);
lean_ctor_set(v_newNode_1217_, 1, v_k_1201_);
lean_ctor_set(v_newNode_1217_, 2, v___x_1216_);
v_stack_1218_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1203_, v___x_1214_);
lean_dec(v___x_1214_);
v_stack_1219_ = l_Lean_Parser_SyntaxStack_push(v_stack_1218_, v_newNode_1217_);
if (v_isShared_1211_ == 0)
{
lean_ctor_set(v___x_1210_, 0, v_stack_1219_);
v___x_1221_ = v___x_1210_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_stack_1219_);
lean_ctor_set(v_reuseFailAlloc_1222_, 1, v_lhsPrec_1204_);
lean_ctor_set(v_reuseFailAlloc_1222_, 2, v_pos_1205_);
lean_ctor_set(v_reuseFailAlloc_1222_, 3, v_cache_1206_);
lean_ctor_set(v_reuseFailAlloc_1222_, 4, v_errorMsg_1207_);
lean_ctor_set(v_reuseFailAlloc_1222_, 5, v_recoveredErrors_1208_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1224_, lean_object* v_k_1225_, lean_object* v_iniStackSz_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1224_, v_k_1225_, v_iniStackSz_1226_);
lean_dec(v_iniStackSz_1226_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1230_){
_start:
{
lean_object* v_errorMsg_1231_; 
v_errorMsg_1231_ = lean_ctor_get(v_s_1230_, 4);
if (lean_obj_tag(v_errorMsg_1231_) == 0)
{
lean_object* v_recoveredErrors_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; 
v_recoveredErrors_1232_ = lean_ctor_get(v_s_1230_, 5);
lean_inc_ref(v_recoveredErrors_1232_);
lean_dec_ref(v_s_1230_);
v___x_1233_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1234_ = l_Array_append___redArg(v_recoveredErrors_1232_, v___x_1233_);
return v___x_1234_;
}
else
{
lean_object* v_stxStack_1235_; lean_object* v_pos_1236_; lean_object* v_recoveredErrors_1237_; lean_object* v_val_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_inc_ref(v_errorMsg_1231_);
v_stxStack_1235_ = lean_ctor_get(v_s_1230_, 0);
lean_inc_ref(v_stxStack_1235_);
v_pos_1236_ = lean_ctor_get(v_s_1230_, 2);
lean_inc(v_pos_1236_);
v_recoveredErrors_1237_ = lean_ctor_get(v_s_1230_, 5);
lean_inc_ref(v_recoveredErrors_1237_);
lean_dec_ref(v_s_1230_);
v_val_1238_ = lean_ctor_get(v_errorMsg_1231_, 0);
lean_inc(v_val_1238_);
lean_dec_ref_known(v_errorMsg_1231_, 1);
v___x_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1239_, 0, v_stxStack_1235_);
lean_ctor_set(v___x_1239_, 1, v_val_1238_);
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_pos_1236_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = lean_unsigned_to_nat(1u);
v___x_1242_ = lean_mk_empty_array_with_capacity(v___x_1241_);
v___x_1243_ = lean_array_push(v___x_1242_, v___x_1240_);
v___x_1244_ = l_Array_append___redArg(v_recoveredErrors_1237_, v___x_1243_);
lean_dec_ref(v___x_1243_);
return v___x_1244_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1245_, lean_object* v_e_1246_){
_start:
{
lean_object* v_stxStack_1247_; lean_object* v_lhsPrec_1248_; lean_object* v_pos_1249_; lean_object* v_cache_1250_; lean_object* v_recoveredErrors_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1259_; 
v_stxStack_1247_ = lean_ctor_get(v_s_1245_, 0);
v_lhsPrec_1248_ = lean_ctor_get(v_s_1245_, 1);
v_pos_1249_ = lean_ctor_get(v_s_1245_, 2);
v_cache_1250_ = lean_ctor_get(v_s_1245_, 3);
v_recoveredErrors_1251_ = lean_ctor_get(v_s_1245_, 5);
v_isSharedCheck_1259_ = !lean_is_exclusive(v_s_1245_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v_s_1245_, 4);
lean_dec(v_unused_1260_);
v___x_1253_ = v_s_1245_;
v_isShared_1254_ = v_isSharedCheck_1259_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_recoveredErrors_1251_);
lean_inc(v_cache_1250_);
lean_inc(v_pos_1249_);
lean_inc(v_lhsPrec_1248_);
lean_inc(v_stxStack_1247_);
lean_dec(v_s_1245_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1259_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1255_, 0, v_e_1246_);
if (v_isShared_1254_ == 0)
{
lean_ctor_set(v___x_1253_, 4, v___x_1255_);
v___x_1257_ = v___x_1253_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_stxStack_1247_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v_lhsPrec_1248_);
lean_ctor_set(v_reuseFailAlloc_1258_, 2, v_pos_1249_);
lean_ctor_set(v_reuseFailAlloc_1258_, 3, v_cache_1250_);
lean_ctor_set(v_reuseFailAlloc_1258_, 4, v___x_1255_);
lean_ctor_set(v_reuseFailAlloc_1258_, 5, v_recoveredErrors_1251_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1261_, lean_object* v_msg_1262_){
_start:
{
lean_object* v_stxStack_1263_; lean_object* v_lhsPrec_1264_; lean_object* v_pos_1265_; lean_object* v_cache_1266_; lean_object* v_recoveredErrors_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1281_; 
v_stxStack_1263_ = lean_ctor_get(v_s_1261_, 0);
v_lhsPrec_1264_ = lean_ctor_get(v_s_1261_, 1);
v_pos_1265_ = lean_ctor_get(v_s_1261_, 2);
v_cache_1266_ = lean_ctor_get(v_s_1261_, 3);
v_recoveredErrors_1267_ = lean_ctor_get(v_s_1261_, 5);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_s_1261_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v_s_1261_, 4);
lean_dec(v_unused_1282_);
v___x_1269_ = v_s_1261_;
v_isShared_1270_ = v_isSharedCheck_1281_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_recoveredErrors_1267_);
lean_inc(v_cache_1266_);
lean_inc(v_pos_1265_);
lean_inc(v_lhsPrec_1264_);
lean_inc(v_stxStack_1263_);
lean_dec(v_s_1261_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1281_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1271_ = lean_box(0);
v___x_1272_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1273_ = lean_box(0);
v___x_1274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1274_, 0, v_msg_1262_);
lean_ctor_set(v___x_1274_, 1, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1271_);
lean_ctor_set(v___x_1275_, 1, v___x_1272_);
lean_ctor_set(v___x_1275_, 2, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 4, v___x_1276_);
v___x_1278_ = v___x_1269_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v_stxStack_1263_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_lhsPrec_1264_);
lean_ctor_set(v_reuseFailAlloc_1280_, 2, v_pos_1265_);
lean_ctor_set(v_reuseFailAlloc_1280_, 3, v_cache_1266_);
lean_ctor_set(v_reuseFailAlloc_1280_, 4, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1280_, 5, v_recoveredErrors_1267_);
v___x_1278_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1278_, v___x_1271_);
return v___x_1279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1283_, lean_object* v_msg_1284_, lean_object* v_expected_1285_, uint8_t v_pushMissing_1286_){
_start:
{
lean_object* v_stxStack_1287_; lean_object* v_lhsPrec_1288_; lean_object* v_pos_1289_; lean_object* v_cache_1290_; lean_object* v_recoveredErrors_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1302_; 
v_stxStack_1287_ = lean_ctor_get(v_s_1283_, 0);
v_lhsPrec_1288_ = lean_ctor_get(v_s_1283_, 1);
v_pos_1289_ = lean_ctor_get(v_s_1283_, 2);
v_cache_1290_ = lean_ctor_get(v_s_1283_, 3);
v_recoveredErrors_1291_ = lean_ctor_get(v_s_1283_, 5);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_s_1283_);
if (v_isSharedCheck_1302_ == 0)
{
lean_object* v_unused_1303_; 
v_unused_1303_ = lean_ctor_get(v_s_1283_, 4);
lean_dec(v_unused_1303_);
v___x_1293_ = v_s_1283_;
v_isShared_1294_ = v_isSharedCheck_1302_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_recoveredErrors_1291_);
lean_inc(v_cache_1290_);
lean_inc(v_pos_1289_);
lean_inc(v_lhsPrec_1288_);
lean_inc(v_stxStack_1287_);
lean_dec(v_s_1283_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1302_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v_s_1299_; 
v___x_1295_ = lean_box(0);
v___x_1296_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1296_, 0, v___x_1295_);
lean_ctor_set(v___x_1296_, 1, v_msg_1284_);
lean_ctor_set(v___x_1296_, 2, v_expected_1285_);
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 4, v___x_1297_);
v_s_1299_ = v___x_1293_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_stxStack_1287_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v_lhsPrec_1288_);
lean_ctor_set(v_reuseFailAlloc_1301_, 2, v_pos_1289_);
lean_ctor_set(v_reuseFailAlloc_1301_, 3, v_cache_1290_);
lean_ctor_set(v_reuseFailAlloc_1301_, 4, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1301_, 5, v_recoveredErrors_1291_);
v_s_1299_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
if (v_pushMissing_1286_ == 0)
{
return v_s_1299_;
}
else
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1299_, v___x_1295_);
return v___x_1300_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1304_, lean_object* v_msg_1305_, lean_object* v_expected_1306_, lean_object* v_pushMissing_1307_){
_start:
{
uint8_t v_pushMissing_boxed_1308_; lean_object* v_res_1309_; 
v_pushMissing_boxed_1308_ = lean_unbox(v_pushMissing_1307_);
v_res_1309_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1304_, v_msg_1305_, v_expected_1306_, v_pushMissing_boxed_1308_);
return v_res_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1311_, lean_object* v_expected_1312_){
_start:
{
lean_object* v___x_1313_; uint8_t v___x_1314_; lean_object* v___x_1315_; 
v___x_1313_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1314_ = 1;
v___x_1315_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1311_, v___x_1313_, v_expected_1312_, v___x_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1316_, lean_object* v_ex_1317_, lean_object* v_pos_1318_, lean_object* v_initStackSz_x3f_1319_){
_start:
{
lean_object* v_s_1321_; lean_object* v_s_1340_; 
v_s_1340_ = l_Lean_Parser_ParserState_setPos(v_s_1316_, v_pos_1318_);
if (lean_obj_tag(v_initStackSz_x3f_1319_) == 1)
{
lean_object* v_val_1341_; lean_object* v_s_1342_; 
v_val_1341_ = lean_ctor_get(v_initStackSz_x3f_1319_, 0);
v_s_1342_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1340_, v_val_1341_);
v_s_1321_ = v_s_1342_;
goto v___jp_1320_;
}
else
{
v_s_1321_ = v_s_1340_;
goto v___jp_1320_;
}
v___jp_1320_:
{
lean_object* v_stxStack_1322_; lean_object* v_lhsPrec_1323_; lean_object* v_pos_1324_; lean_object* v_cache_1325_; lean_object* v_recoveredErrors_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1338_; 
v_stxStack_1322_ = lean_ctor_get(v_s_1321_, 0);
v_lhsPrec_1323_ = lean_ctor_get(v_s_1321_, 1);
v_pos_1324_ = lean_ctor_get(v_s_1321_, 2);
v_cache_1325_ = lean_ctor_get(v_s_1321_, 3);
v_recoveredErrors_1326_ = lean_ctor_get(v_s_1321_, 5);
v_isSharedCheck_1338_ = !lean_is_exclusive(v_s_1321_);
if (v_isSharedCheck_1338_ == 0)
{
lean_object* v_unused_1339_; 
v_unused_1339_ = lean_ctor_get(v_s_1321_, 4);
lean_dec(v_unused_1339_);
v___x_1328_ = v_s_1321_;
v_isShared_1329_ = v_isSharedCheck_1338_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_recoveredErrors_1326_);
lean_inc(v_cache_1325_);
lean_inc(v_pos_1324_);
lean_inc(v_lhsPrec_1323_);
lean_inc(v_stxStack_1322_);
lean_dec(v_s_1321_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1338_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v_s_1335_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
lean_ctor_set(v___x_1332_, 2, v_ex_1317_);
v___x_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 4, v___x_1333_);
v_s_1335_ = v___x_1328_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_stxStack_1322_);
lean_ctor_set(v_reuseFailAlloc_1337_, 1, v_lhsPrec_1323_);
lean_ctor_set(v_reuseFailAlloc_1337_, 2, v_pos_1324_);
lean_ctor_set(v_reuseFailAlloc_1337_, 3, v_cache_1325_);
lean_ctor_set(v_reuseFailAlloc_1337_, 4, v___x_1333_);
lean_ctor_set(v_reuseFailAlloc_1337_, 5, v_recoveredErrors_1326_);
v_s_1335_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1335_, v___x_1330_);
return v___x_1336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1343_, lean_object* v_ex_1344_, lean_object* v_pos_1345_, lean_object* v_initStackSz_x3f_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1343_, v_ex_1344_, v_pos_1345_, v_initStackSz_x3f_1346_);
lean_dec(v_initStackSz_x3f_1346_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1348_, lean_object* v_msg_1349_, lean_object* v_pos_1350_, lean_object* v_initStackSz_x3f_1351_){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_msg_1349_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1348_, v___x_1353_, v_pos_1350_, v_initStackSz_x3f_1351_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1355_, lean_object* v_msg_1356_, lean_object* v_pos_1357_, lean_object* v_initStackSz_x3f_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1355_, v_msg_1356_, v_pos_1357_, v_initStackSz_x3f_1358_);
lean_dec(v_initStackSz_x3f_1358_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1360_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_panic_fn_borrowed(v___x_1361_, v_msg_1360_);
return v___x_1362_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1366_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1367_ = lean_unsigned_to_nat(14u);
v___x_1368_ = lean_unsigned_to_nat(22u);
v___x_1369_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1370_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1371_ = l_mkPanicMessageWithDecl(v___x_1370_, v___x_1369_, v___x_1368_, v___x_1367_, v___x_1366_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1372_, lean_object* v_ex_1373_, lean_object* v_iniPos_1374_){
_start:
{
lean_object* v_stxStack_1375_; lean_object* v_tk_1376_; lean_object* v___y_1378_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v_stxStack_1375_ = lean_ctor_get(v_s_1372_, 0);
v_tk_1376_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1375_);
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = lean_nat_dec_lt(v___x_1399_, v_iniPos_1374_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; 
lean_dec(v_iniPos_1374_);
v___x_1401_ = l_Lean_Syntax_getPos_x3f(v_tk_1376_, v___x_1400_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1403_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1402_);
v___y_1378_ = v___x_1403_;
goto v___jp_1377_;
}
else
{
lean_object* v_val_1404_; 
v_val_1404_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_val_1404_);
lean_dec_ref_known(v___x_1401_, 1);
v___y_1378_ = v_val_1404_;
goto v___jp_1377_;
}
}
else
{
v___y_1378_ = v_iniPos_1374_;
goto v___jp_1377_;
}
v___jp_1377_:
{
lean_object* v_s_1379_; lean_object* v_stxStack_1380_; lean_object* v_lhsPrec_1381_; lean_object* v_pos_1382_; lean_object* v_cache_1383_; lean_object* v_recoveredErrors_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1397_; 
v_s_1379_ = l_Lean_Parser_ParserState_setPos(v_s_1372_, v___y_1378_);
v_stxStack_1380_ = lean_ctor_get(v_s_1379_, 0);
v_lhsPrec_1381_ = lean_ctor_get(v_s_1379_, 1);
v_pos_1382_ = lean_ctor_get(v_s_1379_, 2);
v_cache_1383_ = lean_ctor_get(v_s_1379_, 3);
v_recoveredErrors_1384_ = lean_ctor_get(v_s_1379_, 5);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_s_1379_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v_s_1379_, 4);
lean_dec(v_unused_1398_);
v___x_1386_ = v_s_1379_;
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_recoveredErrors_1384_);
lean_inc(v_cache_1383_);
lean_inc(v_pos_1382_);
lean_inc(v_lhsPrec_1381_);
lean_inc(v_stxStack_1380_);
lean_dec(v_s_1379_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1397_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v_s_1392_; 
v___x_1388_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1389_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1389_, 0, v_tk_1376_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
lean_ctor_set(v___x_1389_, 2, v_ex_1373_);
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 4, v___x_1390_);
v_s_1392_ = v___x_1386_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_stxStack_1380_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_lhsPrec_1381_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_pos_1382_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_cache_1383_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v___x_1390_);
lean_ctor_set(v_reuseFailAlloc_1396_, 5, v_recoveredErrors_1384_);
v_s_1392_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1393_ = l_Lean_Parser_ParserState_popSyntax(v_s_1392_);
v___x_1394_ = lean_box(0);
v___x_1395_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1393_, v___x_1394_);
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1405_, lean_object* v_msg_1406_, lean_object* v_iniPos_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = lean_box(0);
v___x_1409_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1409_, 0, v_msg_1406_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1405_, v___x_1409_, v_iniPos_1407_);
return v___x_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1411_, lean_object* v_msg_1412_, lean_object* v_pos_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; lean_object* v___x_1417_; 
v___x_1414_ = l_Lean_Parser_ParserState_setPos(v_s_1411_, v_pos_1413_);
v___x_1415_ = lean_box(0);
v___x_1416_ = 1;
v___x_1417_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1414_, v_msg_1412_, v___x_1415_, v___x_1416_);
return v___x_1417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1419_, lean_object* v_as_1420_, size_t v_sz_1421_, size_t v_i_1422_, lean_object* v_b_1423_){
_start:
{
uint8_t v___x_1424_; 
v___x_1424_ = lean_usize_dec_lt(v_i_1422_, v_sz_1421_);
if (v___x_1424_ == 0)
{
lean_dec_ref(v_ctx_1419_);
return v_b_1423_;
}
else
{
lean_object* v_a_1425_; lean_object* v_snd_1426_; lean_object* v_fst_1427_; lean_object* v_snd_1428_; lean_object* v_errStr_1430_; lean_object* v_errStr_1441_; uint8_t v___x_1442_; 
v_a_1425_ = lean_array_uget_borrowed(v_as_1420_, v_i_1422_);
v_snd_1426_ = lean_ctor_get(v_a_1425_, 1);
v_fst_1427_ = lean_ctor_get(v_a_1425_, 0);
v_snd_1428_ = lean_ctor_get(v_snd_1426_, 1);
v_errStr_1441_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1442_ = lean_string_dec_eq(v_b_1423_, v_errStr_1441_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1444_ = lean_string_append(v_b_1423_, v___x_1443_);
v_errStr_1430_ = v___x_1444_;
goto v___jp_1429_;
}
else
{
v_errStr_1430_ = v_b_1423_;
goto v___jp_1429_;
}
v___jp_1429_:
{
lean_object* v_fileName_1431_; lean_object* v_fileMap_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; size_t v___x_1438_; size_t v___x_1439_; 
v_fileName_1431_ = lean_ctor_get(v_ctx_1419_, 1);
v_fileMap_1432_ = lean_ctor_get(v_ctx_1419_, 2);
lean_inc_ref(v_fileMap_1432_);
v___x_1433_ = l_Lean_FileMap_toPosition(v_fileMap_1432_, v_fst_1427_);
lean_inc(v_snd_1428_);
v___x_1434_ = l_Lean_Parser_Error_toString(v_snd_1428_);
v___x_1435_ = lean_box(0);
lean_inc_ref(v_fileName_1431_);
v___x_1436_ = l_Lean_mkErrorStringWithPos(v_fileName_1431_, v___x_1433_, v___x_1434_, v___x_1435_, v___x_1435_, v___x_1435_);
lean_dec_ref(v___x_1434_);
v___x_1437_ = lean_string_append(v_errStr_1430_, v___x_1436_);
lean_dec_ref(v___x_1436_);
v___x_1438_ = ((size_t)1ULL);
v___x_1439_ = lean_usize_add(v_i_1422_, v___x_1438_);
v_i_1422_ = v___x_1439_;
v_b_1423_ = v___x_1437_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1445_, lean_object* v_as_1446_, lean_object* v_sz_1447_, lean_object* v_i_1448_, lean_object* v_b_1449_){
_start:
{
size_t v_sz_boxed_1450_; size_t v_i_boxed_1451_; lean_object* v_res_1452_; 
v_sz_boxed_1450_ = lean_unbox_usize(v_sz_1447_);
lean_dec(v_sz_1447_);
v_i_boxed_1451_ = lean_unbox_usize(v_i_1448_);
lean_dec(v_i_1448_);
v_res_1452_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1445_, v_as_1446_, v_sz_boxed_1450_, v_i_boxed_1451_, v_b_1449_);
lean_dec_ref(v_as_1446_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1453_, lean_object* v_s_1454_){
_start:
{
lean_object* v_errStr_1455_; lean_object* v___x_1456_; size_t v_sz_1457_; size_t v___x_1458_; lean_object* v___x_1459_; 
v_errStr_1455_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1456_ = l_Lean_Parser_ParserState_allErrors(v_s_1454_);
v_sz_1457_ = lean_array_size(v___x_1456_);
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1453_, v___x_1456_, v_sz_1457_, v___x_1458_, v_errStr_1455_);
lean_dec_ref(v___x_1456_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1460_, lean_object* v_s_1461_){
_start:
{
lean_inc_ref(v_s_1461_);
return v_s_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1462_, lean_object* v_s_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1462_, v_s_1463_);
lean_dec_ref(v_s_1463_);
lean_dec_ref(v_x_1462_);
return v_res_1464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx(lean_object* v_x_1467_){
_start:
{
switch(lean_obj_tag(v_x_1467_))
{
case 0:
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_unsigned_to_nat(0u);
return v___x_1468_;
}
case 1:
{
lean_object* v___x_1469_; 
v___x_1469_ = lean_unsigned_to_nat(1u);
return v___x_1469_;
}
case 2:
{
lean_object* v___x_1470_; 
v___x_1470_ = lean_unsigned_to_nat(2u);
return v___x_1470_;
}
default: 
{
lean_object* v___x_1471_; 
v___x_1471_ = lean_unsigned_to_nat(3u);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___boxed(lean_object* v_x_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Lean_Parser_FirstTokens_ctorIdx(v_x_1472_);
lean_dec(v_x_1472_);
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1474_, lean_object* v_k_1475_){
_start:
{
switch(lean_obj_tag(v_t_1474_))
{
case 2:
{
lean_object* v_a_1476_; lean_object* v___x_1477_; 
v_a_1476_ = lean_ctor_get(v_t_1474_, 0);
lean_inc(v_a_1476_);
lean_dec_ref_known(v_t_1474_, 1);
v___x_1477_ = lean_apply_1(v_k_1475_, v_a_1476_);
return v___x_1477_;
}
case 3:
{
lean_object* v_a_1478_; lean_object* v___x_1479_; 
v_a_1478_ = lean_ctor_get(v_t_1474_, 0);
lean_inc(v_a_1478_);
lean_dec_ref_known(v_t_1474_, 1);
v___x_1479_ = lean_apply_1(v_k_1475_, v_a_1478_);
return v___x_1479_;
}
default: 
{
lean_dec(v_t_1474_);
return v_k_1475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1480_, lean_object* v_ctorIdx_1481_, lean_object* v_t_1482_, lean_object* v_h_1483_, lean_object* v_k_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1482_, v_k_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1486_, lean_object* v_ctorIdx_1487_, lean_object* v_t_1488_, lean_object* v_h_1489_, lean_object* v_k_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1486_, v_ctorIdx_1487_, v_t_1488_, v_h_1489_, v_k_1490_);
lean_dec(v_ctorIdx_1487_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1492_, lean_object* v_epsilon_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1492_, v_epsilon_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1495_, lean_object* v_t_1496_, lean_object* v_h_1497_, lean_object* v_epsilon_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1496_, v_epsilon_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1500_, lean_object* v_unknown_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1500_, v_unknown_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1503_, lean_object* v_t_1504_, lean_object* v_h_1505_, lean_object* v_unknown_1506_){
_start:
{
lean_object* v___x_1507_; 
v___x_1507_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1504_, v_unknown_1506_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1508_, lean_object* v_tokens_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1508_, v_tokens_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1511_, lean_object* v_t_1512_, lean_object* v_h_1513_, lean_object* v_tokens_1514_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1512_, v_tokens_1514_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1516_, lean_object* v_optTokens_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1516_, v_optTokens_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1519_, lean_object* v_t_1520_, lean_object* v_h_1521_, lean_object* v_optTokens_1522_){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1520_, v_optTokens_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_box(0);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = lean_box(0);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1526_, lean_object* v_x_1527_){
_start:
{
switch(lean_obj_tag(v_x_1526_))
{
case 0:
{
return v_x_1527_;
}
case 3:
{
switch(lean_obj_tag(v_x_1527_))
{
case 3:
{
lean_object* v_a_1528_; lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1537_; 
v_a_1528_ = lean_ctor_get(v_x_1526_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v_x_1526_, 1);
v_a_1529_ = lean_ctor_get(v_x_1527_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v_x_1527_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1531_ = v_x_1527_;
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v_x_1527_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1537_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1533_; lean_object* v___x_1535_; 
v___x_1533_ = l_List_appendTR___redArg(v_a_1528_, v_a_1529_);
if (v_isShared_1532_ == 0)
{
lean_ctor_set(v___x_1531_, 0, v___x_1533_);
v___x_1535_ = v___x_1531_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v___x_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
case 2:
{
lean_object* v_a_1538_; lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1547_; 
v_a_1538_ = lean_ctor_get(v_x_1526_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v_x_1526_, 1);
v_a_1539_ = lean_ctor_get(v_x_1527_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v_x_1527_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1541_ = v_x_1527_;
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v_x_1527_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1547_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
lean_object* v___x_1543_; lean_object* v___x_1545_; 
v___x_1543_ = l_List_appendTR___redArg(v_a_1538_, v_a_1539_);
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1543_);
v___x_1545_ = v___x_1541_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v___x_1543_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
case 1:
{
lean_dec_ref_known(v_x_1526_, 1);
return v_x_1527_;
}
default: 
{
lean_dec(v_x_1527_);
return v_x_1526_;
}
}
}
default: 
{
lean_dec(v_x_1527_);
return v_x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1548_){
_start:
{
if (lean_obj_tag(v_x_1548_) == 2)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
v_a_1549_ = lean_ctor_get(v_x_1548_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_x_1548_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v_x_1548_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_a_1549_);
lean_dec(v_x_1548_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 3);
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
else
{
return v_x_1548_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1557_, lean_object* v_x_1558_){
_start:
{
lean_object* v_s_u2081_1560_; lean_object* v_s_u2082_1561_; 
switch(lean_obj_tag(v_x_1557_))
{
case 0:
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1558_);
return v___x_1564_;
}
case 2:
{
switch(lean_obj_tag(v_x_1558_))
{
case 0:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1557_);
return v___x_1565_;
}
case 2:
{
lean_object* v_a_1566_; lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1575_; 
v_a_1566_ = lean_ctor_get(v_x_1557_, 0);
lean_inc(v_a_1566_);
lean_dec_ref_known(v_x_1557_, 1);
v_a_1567_ = lean_ctor_get(v_x_1558_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_x_1558_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1569_ = v_x_1558_;
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v_x_1558_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = l_List_appendTR___redArg(v_a_1566_, v_a_1567_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 0, v___x_1571_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
case 3:
{
lean_object* v_a_1576_; lean_object* v_a_1577_; 
v_a_1576_ = lean_ctor_get(v_x_1557_, 0);
lean_inc(v_a_1576_);
lean_dec_ref_known(v_x_1557_, 1);
v_a_1577_ = lean_ctor_get(v_x_1558_, 0);
lean_inc(v_a_1577_);
lean_dec_ref_known(v_x_1558_, 1);
v_s_u2081_1560_ = v_a_1576_;
v_s_u2082_1561_ = v_a_1577_;
goto v___jp_1559_;
}
default: 
{
lean_object* v___x_1578_; 
lean_dec_ref_known(v_x_1557_, 1);
lean_dec(v_x_1558_);
v___x_1578_ = lean_box(1);
return v___x_1578_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1558_))
{
case 0:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1557_);
return v___x_1579_;
}
case 3:
{
lean_object* v_a_1580_; lean_object* v_a_1581_; 
v_a_1580_ = lean_ctor_get(v_x_1557_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v_x_1557_, 1);
v_a_1581_ = lean_ctor_get(v_x_1558_, 0);
lean_inc(v_a_1581_);
lean_dec_ref_known(v_x_1558_, 1);
v_s_u2081_1560_ = v_a_1580_;
v_s_u2082_1561_ = v_a_1581_;
goto v___jp_1559_;
}
case 2:
{
lean_object* v_a_1582_; lean_object* v_a_1583_; 
v_a_1582_ = lean_ctor_get(v_x_1557_, 0);
lean_inc(v_a_1582_);
lean_dec_ref_known(v_x_1557_, 1);
v_a_1583_ = lean_ctor_get(v_x_1558_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v_x_1558_, 1);
v_s_u2081_1560_ = v_a_1582_;
v_s_u2082_1561_ = v_a_1583_;
goto v___jp_1559_;
}
default: 
{
lean_object* v___x_1584_; 
lean_dec_ref_known(v_x_1557_, 1);
lean_dec(v_x_1558_);
v___x_1584_ = lean_box(1);
return v___x_1584_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1558_) == 0)
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1557_);
return v___x_1585_;
}
else
{
lean_object* v___x_1586_; 
lean_dec(v_x_1558_);
lean_dec(v_x_1557_);
v___x_1586_ = lean_box(1);
return v___x_1586_;
}
}
}
v___jp_1559_:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1562_ = l_List_appendTR___redArg(v_s_u2081_1560_, v_s_u2082_1561_);
v___x_1563_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1562_);
return v___x_1563_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1587_, lean_object* v_x_1588_){
_start:
{
if (lean_obj_tag(v_x_1588_) == 0)
{
return v_x_1587_;
}
else
{
lean_object* v_head_1589_; lean_object* v_tail_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_head_1589_ = lean_ctor_get(v_x_1588_, 0);
v_tail_1590_ = lean_ctor_get(v_x_1588_, 1);
v___x_1591_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1592_ = lean_string_append(v_x_1587_, v___x_1591_);
v___x_1593_ = lean_string_append(v___x_1592_, v_head_1589_);
v_x_1587_ = v___x_1593_;
v_x_1588_ = v_tail_1590_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1595_, v_x_1596_);
lean_dec(v_x_1596_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1601_){
_start:
{
if (lean_obj_tag(v_x_1601_) == 0)
{
lean_object* v___x_1602_; 
v___x_1602_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1602_;
}
else
{
lean_object* v_tail_1603_; 
v_tail_1603_ = lean_ctor_get(v_x_1601_, 1);
if (lean_obj_tag(v_tail_1603_) == 0)
{
lean_object* v_head_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v_head_1604_ = lean_ctor_get(v_x_1601_, 0);
v___x_1605_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1606_ = lean_string_append(v___x_1605_, v_head_1604_);
v___x_1607_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1608_ = lean_string_append(v___x_1606_, v___x_1607_);
return v___x_1608_;
}
else
{
lean_object* v_head_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint32_t v___x_1613_; lean_object* v___x_1614_; 
v_head_1609_ = lean_ctor_get(v_x_1601_, 0);
v___x_1610_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1611_ = lean_string_append(v___x_1610_, v_head_1609_);
v___x_1612_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1611_, v_tail_1603_);
v___x_1613_ = 93;
v___x_1614_ = lean_string_push(v___x_1612_, v___x_1613_);
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1615_);
lean_dec(v_x_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1620_){
_start:
{
switch(lean_obj_tag(v_x_1620_))
{
case 0:
{
lean_object* v___x_1621_; 
v___x_1621_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1621_;
}
case 1:
{
lean_object* v___x_1622_; 
v___x_1622_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1622_;
}
case 2:
{
lean_object* v_a_1623_; lean_object* v___x_1624_; 
v_a_1623_ = lean_ctor_get(v_x_1620_, 0);
v___x_1624_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1623_);
return v___x_1624_;
}
default: 
{
lean_object* v_a_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v_a_1625_ = lean_ctor_get(v_x_1620_, 0);
v___x_1626_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1627_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1625_);
v___x_1628_ = lean_string_append(v___x_1626_, v___x_1627_);
lean_dec_ref(v___x_1627_);
return v___x_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Lean_Parser_FirstTokens_toStr(v_x_1629_);
lean_dec(v_x_1629_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v___y_1633_){
_start:
{
lean_inc(v___y_1633_);
return v___y_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v___y_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_1634_);
lean_dec(v___y_1634_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v___y_1636_){
_start:
{
lean_inc_ref(v___y_1636_);
return v___y_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v___y_1637_){
_start:
{
lean_object* v_res_1638_; 
v_res_1638_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_1637_);
lean_dec_ref(v___y_1637_);
return v_res_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1652_, lean_object* v_p_1653_){
_start:
{
lean_object* v_info_1654_; lean_object* v_fn_1655_; lean_object* v___x_1657_; uint8_t v_isShared_1658_; uint8_t v_isSharedCheck_1663_; 
v_info_1654_ = lean_ctor_get(v_p_1653_, 0);
v_fn_1655_ = lean_ctor_get(v_p_1653_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_p_1653_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1657_ = v_p_1653_;
v_isShared_1658_ = v_isSharedCheck_1663_;
goto v_resetjp_1656_;
}
else
{
lean_inc(v_fn_1655_);
lean_inc(v_info_1654_);
lean_dec(v_p_1653_);
v___x_1657_ = lean_box(0);
v_isShared_1658_ = v_isSharedCheck_1663_;
goto v_resetjp_1656_;
}
v_resetjp_1656_:
{
lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1659_ = lean_apply_1(v_f_1652_, v_fn_1655_);
if (v_isShared_1658_ == 0)
{
lean_ctor_set(v___x_1657_, 1, v___x_1659_);
v___x_1661_ = v___x_1657_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_info_1654_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v___x_1659_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1664_, lean_object* v_p_1665_, lean_object* v_c_1666_, lean_object* v_s_1667_){
_start:
{
lean_object* v_toInputContext_1668_; lean_object* v_toParserModuleContext_1669_; lean_object* v_toCacheableParserContext_1670_; lean_object* v_tokens_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1680_; 
v_toInputContext_1668_ = lean_ctor_get(v_c_1666_, 0);
v_toParserModuleContext_1669_ = lean_ctor_get(v_c_1666_, 1);
v_toCacheableParserContext_1670_ = lean_ctor_get(v_c_1666_, 2);
v_tokens_1671_ = lean_ctor_get(v_c_1666_, 3);
v_isSharedCheck_1680_ = !lean_is_exclusive(v_c_1666_);
if (v_isSharedCheck_1680_ == 0)
{
v___x_1673_ = v_c_1666_;
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_tokens_1671_);
lean_inc(v_toCacheableParserContext_1670_);
lean_inc(v_toParserModuleContext_1669_);
lean_inc(v_toInputContext_1668_);
lean_dec(v_c_1666_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1680_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1675_; lean_object* v___x_1677_; 
v___x_1675_ = lean_apply_1(v_f_1664_, v_toCacheableParserContext_1670_);
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 2, v___x_1675_);
v___x_1677_ = v___x_1673_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v_toInputContext_1668_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_toParserModuleContext_1669_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v___x_1675_);
lean_ctor_set(v_reuseFailAlloc_1679_, 3, v_tokens_1671_);
v___x_1677_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
lean_object* v___x_1678_; 
v___x_1678_ = lean_apply_2(v_p_1665_, v___x_1677_, v_s_1667_);
return v___x_1678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1681_, lean_object* v_p_1682_){
_start:
{
lean_object* v_info_1683_; lean_object* v_fn_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1692_; 
v_info_1683_ = lean_ctor_get(v_p_1682_, 0);
v_fn_1684_ = lean_ctor_get(v_p_1682_, 1);
v_isSharedCheck_1692_ = !lean_is_exclusive(v_p_1682_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1686_ = v_p_1682_;
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_fn_1684_);
lean_inc(v_info_1683_);
lean_dec(v_p_1682_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1692_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1688_; lean_object* v___x_1690_; 
v___x_1688_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1688_, 0, v_f_1681_);
lean_closure_set(v___x_1688_, 1, v_fn_1684_);
if (v_isShared_1687_ == 0)
{
lean_ctor_set(v___x_1686_, 1, v___x_1688_);
v___x_1690_ = v___x_1686_;
goto v_reusejp_1689_;
}
else
{
lean_object* v_reuseFailAlloc_1691_; 
v_reuseFailAlloc_1691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1691_, 0, v_info_1683_);
lean_ctor_set(v_reuseFailAlloc_1691_, 1, v___x_1688_);
v___x_1690_ = v_reuseFailAlloc_1691_;
goto v_reusejp_1689_;
}
v_reusejp_1689_:
{
return v___x_1690_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1693_, lean_object* v_p_1694_, lean_object* v_c_1695_, lean_object* v_s_1696_){
_start:
{
lean_object* v_stxStack_1697_; lean_object* v_lhsPrec_1698_; lean_object* v_pos_1699_; lean_object* v_cache_1700_; lean_object* v_errorMsg_1701_; lean_object* v_recoveredErrors_1702_; lean_object* v___x_1704_; uint8_t v_isShared_1705_; uint8_t v_isSharedCheck_1741_; 
v_stxStack_1697_ = lean_ctor_get(v_s_1696_, 0);
v_lhsPrec_1698_ = lean_ctor_get(v_s_1696_, 1);
v_pos_1699_ = lean_ctor_get(v_s_1696_, 2);
v_cache_1700_ = lean_ctor_get(v_s_1696_, 3);
v_errorMsg_1701_ = lean_ctor_get(v_s_1696_, 4);
v_recoveredErrors_1702_ = lean_ctor_get(v_s_1696_, 5);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_s_1696_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1704_ = v_s_1696_;
v_isShared_1705_ = v_isSharedCheck_1741_;
goto v_resetjp_1703_;
}
else
{
lean_inc(v_recoveredErrors_1702_);
lean_inc(v_errorMsg_1701_);
lean_inc(v_cache_1700_);
lean_inc(v_pos_1699_);
lean_inc(v_lhsPrec_1698_);
lean_inc(v_stxStack_1697_);
lean_dec(v_s_1696_);
v___x_1704_ = lean_box(0);
v_isShared_1705_ = v_isSharedCheck_1741_;
goto v_resetjp_1703_;
}
v_resetjp_1703_:
{
lean_object* v_raw_1706_; lean_object* v_drop_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1740_; 
v_raw_1706_ = lean_ctor_get(v_stxStack_1697_, 0);
v_drop_1707_ = lean_ctor_get(v_stxStack_1697_, 1);
v_isSharedCheck_1740_ = !lean_is_exclusive(v_stxStack_1697_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1709_ = v_stxStack_1697_;
v_isShared_1710_ = v_isSharedCheck_1740_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_drop_1707_);
lean_inc(v_raw_1706_);
lean_dec(v_stxStack_1697_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1740_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 1, v_drop_1693_);
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_raw_1706_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_drop_1693_);
v___x_1712_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
lean_object* v___x_1714_; 
if (v_isShared_1705_ == 0)
{
lean_ctor_set(v___x_1704_, 0, v___x_1712_);
v___x_1714_ = v___x_1704_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v___x_1712_);
lean_ctor_set(v_reuseFailAlloc_1738_, 1, v_lhsPrec_1698_);
lean_ctor_set(v_reuseFailAlloc_1738_, 2, v_pos_1699_);
lean_ctor_set(v_reuseFailAlloc_1738_, 3, v_cache_1700_);
lean_ctor_set(v_reuseFailAlloc_1738_, 4, v_errorMsg_1701_);
lean_ctor_set(v_reuseFailAlloc_1738_, 5, v_recoveredErrors_1702_);
v___x_1714_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
lean_object* v_s_1715_; lean_object* v_stxStack_1716_; lean_object* v_lhsPrec_1717_; lean_object* v_pos_1718_; lean_object* v_cache_1719_; lean_object* v_errorMsg_1720_; lean_object* v_recoveredErrors_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1737_; 
v_s_1715_ = lean_apply_2(v_p_1694_, v_c_1695_, v___x_1714_);
v_stxStack_1716_ = lean_ctor_get(v_s_1715_, 0);
v_lhsPrec_1717_ = lean_ctor_get(v_s_1715_, 1);
v_pos_1718_ = lean_ctor_get(v_s_1715_, 2);
v_cache_1719_ = lean_ctor_get(v_s_1715_, 3);
v_errorMsg_1720_ = lean_ctor_get(v_s_1715_, 4);
v_recoveredErrors_1721_ = lean_ctor_get(v_s_1715_, 5);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_s_1715_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1723_ = v_s_1715_;
v_isShared_1724_ = v_isSharedCheck_1737_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_recoveredErrors_1721_);
lean_inc(v_errorMsg_1720_);
lean_inc(v_cache_1719_);
lean_inc(v_pos_1718_);
lean_inc(v_lhsPrec_1717_);
lean_inc(v_stxStack_1716_);
lean_dec(v_s_1715_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1737_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v_raw_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1735_; 
v_raw_1725_ = lean_ctor_get(v_stxStack_1716_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_stxStack_1716_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v_stxStack_1716_, 1);
lean_dec(v_unused_1736_);
v___x_1727_ = v_stxStack_1716_;
v_isShared_1728_ = v_isSharedCheck_1735_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_raw_1725_);
lean_dec(v_stxStack_1716_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1735_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v___x_1730_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 1, v_drop_1707_);
v___x_1730_ = v___x_1727_;
goto v_reusejp_1729_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_raw_1725_);
lean_ctor_set(v_reuseFailAlloc_1734_, 1, v_drop_1707_);
v___x_1730_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1729_;
}
v_reusejp_1729_:
{
lean_object* v___x_1732_; 
if (v_isShared_1724_ == 0)
{
lean_ctor_set(v___x_1723_, 0, v___x_1730_);
v___x_1732_ = v___x_1723_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v_lhsPrec_1717_);
lean_ctor_set(v_reuseFailAlloc_1733_, 2, v_pos_1718_);
lean_ctor_set(v_reuseFailAlloc_1733_, 3, v_cache_1719_);
lean_ctor_set(v_reuseFailAlloc_1733_, 4, v_errorMsg_1720_);
lean_ctor_set(v_reuseFailAlloc_1733_, 5, v_recoveredErrors_1721_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1742_, lean_object* v_c_1743_, lean_object* v_s_1744_){
_start:
{
lean_object* v_cache_1745_; lean_object* v_stxStack_1746_; lean_object* v_lhsPrec_1747_; lean_object* v_pos_1748_; lean_object* v_errorMsg_1749_; lean_object* v_recoveredErrors_1750_; lean_object* v___x_1752_; uint8_t v_isShared_1753_; uint8_t v_isSharedCheck_1790_; 
v_cache_1745_ = lean_ctor_get(v_s_1744_, 3);
v_stxStack_1746_ = lean_ctor_get(v_s_1744_, 0);
v_lhsPrec_1747_ = lean_ctor_get(v_s_1744_, 1);
v_pos_1748_ = lean_ctor_get(v_s_1744_, 2);
v_errorMsg_1749_ = lean_ctor_get(v_s_1744_, 4);
v_recoveredErrors_1750_ = lean_ctor_get(v_s_1744_, 5);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_s_1744_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1752_ = v_s_1744_;
v_isShared_1753_ = v_isSharedCheck_1790_;
goto v_resetjp_1751_;
}
else
{
lean_inc(v_recoveredErrors_1750_);
lean_inc(v_errorMsg_1749_);
lean_inc(v_cache_1745_);
lean_inc(v_pos_1748_);
lean_inc(v_lhsPrec_1747_);
lean_inc(v_stxStack_1746_);
lean_dec(v_s_1744_);
v___x_1752_ = lean_box(0);
v_isShared_1753_ = v_isSharedCheck_1790_;
goto v_resetjp_1751_;
}
v_resetjp_1751_:
{
lean_object* v_tokenCache_1754_; lean_object* v_parserCache_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1789_; 
v_tokenCache_1754_ = lean_ctor_get(v_cache_1745_, 0);
v_parserCache_1755_ = lean_ctor_get(v_cache_1745_, 1);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_cache_1745_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1757_ = v_cache_1745_;
v_isShared_1758_ = v_isSharedCheck_1789_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_parserCache_1755_);
lean_inc(v_tokenCache_1754_);
lean_dec(v_cache_1745_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1789_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v___x_1759_);
v___x_1761_ = v___x_1757_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_tokenCache_1754_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
lean_object* v___x_1763_; 
if (v_isShared_1753_ == 0)
{
lean_ctor_set(v___x_1752_, 3, v___x_1761_);
v___x_1763_ = v___x_1752_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_stxStack_1746_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_lhsPrec_1747_);
lean_ctor_set(v_reuseFailAlloc_1787_, 2, v_pos_1748_);
lean_ctor_set(v_reuseFailAlloc_1787_, 3, v___x_1761_);
lean_ctor_set(v_reuseFailAlloc_1787_, 4, v_errorMsg_1749_);
lean_ctor_set(v_reuseFailAlloc_1787_, 5, v_recoveredErrors_1750_);
v___x_1763_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
lean_object* v_s_x27_1764_; lean_object* v_cache_1765_; lean_object* v_stxStack_1766_; lean_object* v_lhsPrec_1767_; lean_object* v_pos_1768_; lean_object* v_errorMsg_1769_; lean_object* v_recoveredErrors_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1786_; 
v_s_x27_1764_ = lean_apply_2(v_p_1742_, v_c_1743_, v___x_1763_);
v_cache_1765_ = lean_ctor_get(v_s_x27_1764_, 3);
v_stxStack_1766_ = lean_ctor_get(v_s_x27_1764_, 0);
v_lhsPrec_1767_ = lean_ctor_get(v_s_x27_1764_, 1);
v_pos_1768_ = lean_ctor_get(v_s_x27_1764_, 2);
v_errorMsg_1769_ = lean_ctor_get(v_s_x27_1764_, 4);
v_recoveredErrors_1770_ = lean_ctor_get(v_s_x27_1764_, 5);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_s_x27_1764_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1772_ = v_s_x27_1764_;
v_isShared_1773_ = v_isSharedCheck_1786_;
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
lean_dec(v_s_x27_1764_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1786_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_tokenCache_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1784_; 
v_tokenCache_1774_ = lean_ctor_get(v_cache_1765_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_cache_1765_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v_cache_1765_, 1);
lean_dec(v_unused_1785_);
v___x_1776_ = v_cache_1765_;
v_isShared_1777_ = v_isSharedCheck_1784_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_tokenCache_1774_);
lean_dec(v_cache_1765_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1784_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 1, v_parserCache_1755_);
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_tokenCache_1774_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_parserCache_1755_);
v___x_1779_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
lean_object* v___x_1781_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 3, v___x_1779_);
v___x_1781_ = v___x_1772_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_stxStack_1766_);
lean_ctor_set(v_reuseFailAlloc_1782_, 1, v_lhsPrec_1767_);
lean_ctor_set(v_reuseFailAlloc_1782_, 2, v_pos_1768_);
lean_ctor_set(v_reuseFailAlloc_1782_, 3, v___x_1779_);
lean_ctor_set(v_reuseFailAlloc_1782_, 4, v_errorMsg_1769_);
lean_ctor_set(v_reuseFailAlloc_1782_, 5, v_recoveredErrors_1770_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v___f_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___f_1794_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1794_, 0, v_p_1791_);
v___x_1795_ = lean_unsigned_to_nat(0u);
v___x_1796_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1795_, v___f_1794_, v_a_1792_, v_a_1793_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1797_){
_start:
{
lean_object* v_info_1798_; lean_object* v_fn_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1807_; 
v_info_1798_ = lean_ctor_get(v_p_1797_, 0);
v_fn_1799_ = lean_ctor_get(v_p_1797_, 1);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_p_1797_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1801_ = v_p_1797_;
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_fn_1799_);
lean_inc(v_info_1798_);
lean_dec(v_p_1797_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1807_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; lean_object* v___x_1805_; 
v___x_1803_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1803_, 0, v_fn_1799_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v___x_1803_);
v___x_1805_ = v___x_1801_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_info_1798_);
lean_ctor_set(v_reuseFailAlloc_1806_, 1, v___x_1803_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1808_, lean_object* v_p_1809_, lean_object* v_c_1810_, lean_object* v_s_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_apply_1(v_f_1808_, v_c_1810_);
v___x_1813_ = lean_apply_2(v_p_1809_, v___x_1812_, v_s_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1814_, lean_object* v_p_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
lean_object* v___f_1818_; lean_object* v___x_1819_; 
v___f_1818_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1818_, 0, v_f_1814_);
lean_closure_set(v___f_1818_, 1, v_p_1815_);
v___x_1819_ = l_Lean_Parser_withResetCacheFn(v___f_1818_, v_a_1816_, v_a_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1820_, lean_object* v_x_1821_){
_start:
{
if (lean_obj_tag(v_x_1821_) == 0)
{
uint8_t v___x_1822_; 
v___x_1822_ = 0;
return v___x_1822_;
}
else
{
lean_object* v_key_1823_; lean_object* v_tail_1824_; uint8_t v___x_1825_; 
v_key_1823_ = lean_ctor_get(v_x_1821_, 0);
v_tail_1824_ = lean_ctor_get(v_x_1821_, 2);
v___x_1825_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1823_, v_a_1820_);
if (v___x_1825_ == 0)
{
v_x_1821_ = v_tail_1824_;
goto _start;
}
else
{
return v___x_1825_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1827_, lean_object* v_x_1828_){
_start:
{
uint8_t v_res_1829_; lean_object* v_r_1830_; 
v_res_1829_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1827_, v_x_1828_);
lean_dec(v_x_1828_);
lean_dec_ref(v_a_1827_);
v_r_1830_ = lean_box(v_res_1829_);
return v_r_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1831_, lean_object* v_x_1832_){
_start:
{
if (lean_obj_tag(v_x_1832_) == 0)
{
return v_x_1831_;
}
else
{
lean_object* v_key_1833_; lean_object* v_value_1834_; lean_object* v_tail_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1865_; 
v_key_1833_ = lean_ctor_get(v_x_1832_, 0);
v_value_1834_ = lean_ctor_get(v_x_1832_, 1);
v_tail_1835_ = lean_ctor_get(v_x_1832_, 2);
v_isSharedCheck_1865_ = !lean_is_exclusive(v_x_1832_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1837_ = v_x_1832_;
v_isShared_1838_ = v_isSharedCheck_1865_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_tail_1835_);
lean_inc(v_value_1834_);
lean_inc(v_key_1833_);
lean_dec(v_x_1832_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1865_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v_parserName_1839_; lean_object* v_pos_1840_; lean_object* v___x_1841_; uint64_t v___x_1842_; uint64_t v___y_1844_; 
v_parserName_1839_ = lean_ctor_get(v_key_1833_, 1);
v_pos_1840_ = lean_ctor_get(v_key_1833_, 2);
v___x_1841_ = lean_array_get_size(v_x_1831_);
v___x_1842_ = l_String_instHashableRaw_hash(v_pos_1840_);
if (lean_obj_tag(v_parserName_1839_) == 0)
{
uint64_t v___x_1863_; 
v___x_1863_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1844_ = v___x_1863_;
goto v___jp_1843_;
}
else
{
uint64_t v_hash_1864_; 
v_hash_1864_ = lean_ctor_get_uint64(v_parserName_1839_, sizeof(void*)*2);
v___y_1844_ = v_hash_1864_;
goto v___jp_1843_;
}
v___jp_1843_:
{
uint64_t v___x_1845_; uint64_t v___x_1846_; uint64_t v___x_1847_; uint64_t v_fold_1848_; uint64_t v___x_1849_; uint64_t v___x_1850_; uint64_t v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1845_ = lean_uint64_mix_hash(v___x_1842_, v___y_1844_);
v___x_1846_ = 32ULL;
v___x_1847_ = lean_uint64_shift_right(v___x_1845_, v___x_1846_);
v_fold_1848_ = lean_uint64_xor(v___x_1845_, v___x_1847_);
v___x_1849_ = 16ULL;
v___x_1850_ = lean_uint64_shift_right(v_fold_1848_, v___x_1849_);
v___x_1851_ = lean_uint64_xor(v_fold_1848_, v___x_1850_);
v___x_1852_ = lean_uint64_to_usize(v___x_1851_);
v___x_1853_ = lean_usize_of_nat(v___x_1841_);
v___x_1854_ = ((size_t)1ULL);
v___x_1855_ = lean_usize_sub(v___x_1853_, v___x_1854_);
v___x_1856_ = lean_usize_land(v___x_1852_, v___x_1855_);
v___x_1857_ = lean_array_uget_borrowed(v_x_1831_, v___x_1856_);
lean_inc(v___x_1857_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 2, v___x_1857_);
v___x_1859_ = v___x_1837_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_key_1833_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v_value_1834_);
lean_ctor_set(v_reuseFailAlloc_1862_, 2, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
lean_object* v___x_1860_; 
v___x_1860_ = lean_array_uset(v_x_1831_, v___x_1856_, v___x_1859_);
v_x_1831_ = v___x_1860_;
v_x_1832_ = v_tail_1835_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1866_, lean_object* v_source_1867_, lean_object* v_target_1868_){
_start:
{
lean_object* v___x_1869_; uint8_t v___x_1870_; 
v___x_1869_ = lean_array_get_size(v_source_1867_);
v___x_1870_ = lean_nat_dec_lt(v_i_1866_, v___x_1869_);
if (v___x_1870_ == 0)
{
lean_dec_ref(v_source_1867_);
lean_dec(v_i_1866_);
return v_target_1868_;
}
else
{
lean_object* v_es_1871_; lean_object* v___x_1872_; lean_object* v_source_1873_; lean_object* v_target_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; 
v_es_1871_ = lean_array_fget(v_source_1867_, v_i_1866_);
v___x_1872_ = lean_box(0);
v_source_1873_ = lean_array_fset(v_source_1867_, v_i_1866_, v___x_1872_);
v_target_1874_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1868_, v_es_1871_);
v___x_1875_ = lean_unsigned_to_nat(1u);
v___x_1876_ = lean_nat_add(v_i_1866_, v___x_1875_);
lean_dec(v_i_1866_);
v_i_1866_ = v___x_1876_;
v_source_1867_ = v_source_1873_;
v_target_1868_ = v_target_1874_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1878_){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v_nbuckets_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1879_ = lean_array_get_size(v_data_1878_);
v___x_1880_ = lean_unsigned_to_nat(2u);
v_nbuckets_1881_ = lean_nat_mul(v___x_1879_, v___x_1880_);
v___x_1882_ = lean_unsigned_to_nat(0u);
v___x_1883_ = lean_box(0);
v___x_1884_ = lean_mk_array(v_nbuckets_1881_, v___x_1883_);
v___x_1885_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1882_, v_data_1878_, v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1886_, lean_object* v_b_1887_, lean_object* v_x_1888_){
_start:
{
if (lean_obj_tag(v_x_1888_) == 0)
{
lean_dec(v_b_1887_);
lean_dec_ref(v_a_1886_);
return v_x_1888_;
}
else
{
lean_object* v_key_1889_; lean_object* v_value_1890_; lean_object* v_tail_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1903_; 
v_key_1889_ = lean_ctor_get(v_x_1888_, 0);
v_value_1890_ = lean_ctor_get(v_x_1888_, 1);
v_tail_1891_ = lean_ctor_get(v_x_1888_, 2);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_x_1888_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1893_ = v_x_1888_;
v_isShared_1894_ = v_isSharedCheck_1903_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_tail_1891_);
lean_inc(v_value_1890_);
lean_inc(v_key_1889_);
lean_dec(v_x_1888_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1903_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
uint8_t v___x_1895_; 
v___x_1895_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1889_, v_a_1886_);
if (v___x_1895_ == 0)
{
lean_object* v___x_1896_; lean_object* v___x_1898_; 
v___x_1896_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1886_, v_b_1887_, v_tail_1891_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 2, v___x_1896_);
v___x_1898_ = v___x_1893_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_key_1889_);
lean_ctor_set(v_reuseFailAlloc_1899_, 1, v_value_1890_);
lean_ctor_set(v_reuseFailAlloc_1899_, 2, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
else
{
lean_object* v___x_1901_; 
lean_dec(v_value_1890_);
lean_dec(v_key_1889_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 1, v_b_1887_);
lean_ctor_set(v___x_1893_, 0, v_a_1886_);
v___x_1901_ = v___x_1893_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1886_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_b_1887_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_tail_1891_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1904_, lean_object* v_a_1905_, lean_object* v_b_1906_){
_start:
{
lean_object* v_size_1907_; lean_object* v_buckets_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1958_; 
v_size_1907_ = lean_ctor_get(v_m_1904_, 0);
v_buckets_1908_ = lean_ctor_get(v_m_1904_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v_m_1904_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1910_ = v_m_1904_;
v_isShared_1911_ = v_isSharedCheck_1958_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_buckets_1908_);
lean_inc(v_size_1907_);
lean_dec(v_m_1904_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1958_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v_parserName_1912_; lean_object* v_pos_1913_; lean_object* v___x_1914_; uint64_t v___x_1915_; uint64_t v___y_1917_; 
v_parserName_1912_ = lean_ctor_get(v_a_1905_, 1);
v_pos_1913_ = lean_ctor_get(v_a_1905_, 2);
v___x_1914_ = lean_array_get_size(v_buckets_1908_);
v___x_1915_ = l_String_instHashableRaw_hash(v_pos_1913_);
if (lean_obj_tag(v_parserName_1912_) == 0)
{
uint64_t v___x_1956_; 
v___x_1956_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1917_ = v___x_1956_;
goto v___jp_1916_;
}
else
{
uint64_t v_hash_1957_; 
v_hash_1957_ = lean_ctor_get_uint64(v_parserName_1912_, sizeof(void*)*2);
v___y_1917_ = v_hash_1957_;
goto v___jp_1916_;
}
v___jp_1916_:
{
uint64_t v___x_1918_; uint64_t v___x_1919_; uint64_t v___x_1920_; uint64_t v_fold_1921_; uint64_t v___x_1922_; uint64_t v___x_1923_; uint64_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; lean_object* v_bkt_1930_; uint8_t v___x_1931_; 
v___x_1918_ = lean_uint64_mix_hash(v___x_1915_, v___y_1917_);
v___x_1919_ = 32ULL;
v___x_1920_ = lean_uint64_shift_right(v___x_1918_, v___x_1919_);
v_fold_1921_ = lean_uint64_xor(v___x_1918_, v___x_1920_);
v___x_1922_ = 16ULL;
v___x_1923_ = lean_uint64_shift_right(v_fold_1921_, v___x_1922_);
v___x_1924_ = lean_uint64_xor(v_fold_1921_, v___x_1923_);
v___x_1925_ = lean_uint64_to_usize(v___x_1924_);
v___x_1926_ = lean_usize_of_nat(v___x_1914_);
v___x_1927_ = ((size_t)1ULL);
v___x_1928_ = lean_usize_sub(v___x_1926_, v___x_1927_);
v___x_1929_ = lean_usize_land(v___x_1925_, v___x_1928_);
v_bkt_1930_ = lean_array_uget_borrowed(v_buckets_1908_, v___x_1929_);
v___x_1931_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1905_, v_bkt_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v_size_x27_1933_; lean_object* v___x_1934_; lean_object* v_buckets_x27_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v___x_1932_ = lean_unsigned_to_nat(1u);
v_size_x27_1933_ = lean_nat_add(v_size_1907_, v___x_1932_);
lean_dec(v_size_1907_);
lean_inc(v_bkt_1930_);
v___x_1934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1934_, 0, v_a_1905_);
lean_ctor_set(v___x_1934_, 1, v_b_1906_);
lean_ctor_set(v___x_1934_, 2, v_bkt_1930_);
v_buckets_x27_1935_ = lean_array_uset(v_buckets_1908_, v___x_1929_, v___x_1934_);
v___x_1936_ = lean_unsigned_to_nat(4u);
v___x_1937_ = lean_nat_mul(v_size_x27_1933_, v___x_1936_);
v___x_1938_ = lean_unsigned_to_nat(3u);
v___x_1939_ = lean_nat_div(v___x_1937_, v___x_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_array_get_size(v_buckets_x27_1935_);
v___x_1941_ = lean_nat_dec_le(v___x_1939_, v___x_1940_);
lean_dec(v___x_1939_);
if (v___x_1941_ == 0)
{
lean_object* v_val_1942_; lean_object* v___x_1944_; 
v_val_1942_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_1935_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v_val_1942_);
lean_ctor_set(v___x_1910_, 0, v_size_x27_1933_);
v___x_1944_ = v___x_1910_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_size_x27_1933_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_val_1942_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
else
{
lean_object* v___x_1947_; 
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v_buckets_x27_1935_);
lean_ctor_set(v___x_1910_, 0, v_size_x27_1933_);
v___x_1947_ = v___x_1910_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_size_x27_1933_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_buckets_x27_1935_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
else
{
lean_object* v___x_1949_; lean_object* v_buckets_x27_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
lean_inc(v_bkt_1930_);
v___x_1949_ = lean_box(0);
v_buckets_x27_1950_ = lean_array_uset(v_buckets_1908_, v___x_1929_, v___x_1949_);
v___x_1951_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1905_, v_b_1906_, v_bkt_1930_);
v___x_1952_ = lean_array_uset(v_buckets_x27_1950_, v___x_1929_, v___x_1951_);
if (v_isShared_1911_ == 0)
{
lean_ctor_set(v___x_1910_, 1, v___x_1952_);
v___x_1954_ = v___x_1910_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1955_; 
v_reuseFailAlloc_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_size_1907_);
lean_ctor_set(v_reuseFailAlloc_1955_, 1, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1955_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
return v___x_1954_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_1959_, lean_object* v_x_1960_){
_start:
{
if (lean_obj_tag(v_x_1960_) == 0)
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_box(0);
return v___x_1961_;
}
else
{
lean_object* v_key_1962_; lean_object* v_value_1963_; lean_object* v_tail_1964_; uint8_t v___x_1965_; 
v_key_1962_ = lean_ctor_get(v_x_1960_, 0);
v_value_1963_ = lean_ctor_get(v_x_1960_, 1);
v_tail_1964_ = lean_ctor_get(v_x_1960_, 2);
v___x_1965_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1962_, v_a_1959_);
if (v___x_1965_ == 0)
{
v_x_1960_ = v_tail_1964_;
goto _start;
}
else
{
lean_object* v___x_1967_; 
lean_inc(v_value_1963_);
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_value_1963_);
return v___x_1967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_1968_, lean_object* v_x_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_1968_, v_x_1969_);
lean_dec(v_x_1969_);
lean_dec_ref(v_a_1968_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v_buckets_1973_; lean_object* v_parserName_1974_; lean_object* v_pos_1975_; lean_object* v___x_1976_; uint64_t v___x_1977_; uint64_t v___y_1979_; 
v_buckets_1973_ = lean_ctor_get(v_m_1971_, 1);
v_parserName_1974_ = lean_ctor_get(v_a_1972_, 1);
v_pos_1975_ = lean_ctor_get(v_a_1972_, 2);
v___x_1976_ = lean_array_get_size(v_buckets_1973_);
v___x_1977_ = l_String_instHashableRaw_hash(v_pos_1975_);
if (lean_obj_tag(v_parserName_1974_) == 0)
{
uint64_t v___x_1994_; 
v___x_1994_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1979_ = v___x_1994_;
goto v___jp_1978_;
}
else
{
uint64_t v_hash_1995_; 
v_hash_1995_ = lean_ctor_get_uint64(v_parserName_1974_, sizeof(void*)*2);
v___y_1979_ = v_hash_1995_;
goto v___jp_1978_;
}
v___jp_1978_:
{
uint64_t v___x_1980_; uint64_t v___x_1981_; uint64_t v___x_1982_; uint64_t v_fold_1983_; uint64_t v___x_1984_; uint64_t v___x_1985_; uint64_t v___x_1986_; size_t v___x_1987_; size_t v___x_1988_; size_t v___x_1989_; size_t v___x_1990_; size_t v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1980_ = lean_uint64_mix_hash(v___x_1977_, v___y_1979_);
v___x_1981_ = 32ULL;
v___x_1982_ = lean_uint64_shift_right(v___x_1980_, v___x_1981_);
v_fold_1983_ = lean_uint64_xor(v___x_1980_, v___x_1982_);
v___x_1984_ = 16ULL;
v___x_1985_ = lean_uint64_shift_right(v_fold_1983_, v___x_1984_);
v___x_1986_ = lean_uint64_xor(v_fold_1983_, v___x_1985_);
v___x_1987_ = lean_uint64_to_usize(v___x_1986_);
v___x_1988_ = lean_usize_of_nat(v___x_1976_);
v___x_1989_ = ((size_t)1ULL);
v___x_1990_ = lean_usize_sub(v___x_1988_, v___x_1989_);
v___x_1991_ = lean_usize_land(v___x_1987_, v___x_1990_);
v___x_1992_ = lean_array_uget_borrowed(v_buckets_1973_, v___x_1991_);
v___x_1993_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_1972_, v___x_1992_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_1996_, lean_object* v_a_1997_){
_start:
{
lean_object* v_res_1998_; 
v_res_1998_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_1996_, v_a_1997_);
lean_dec_ref(v_a_1997_);
lean_dec_ref(v_m_1996_);
return v_res_1998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_1999_, lean_object* v_p_2000_, lean_object* v_c_2001_, lean_object* v_s_2002_){
_start:
{
lean_object* v_cache_2003_; lean_object* v_toCacheableParserContext_2004_; lean_object* v_stxStack_2005_; lean_object* v_pos_2006_; lean_object* v_recoveredErrors_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2056_; 
v_cache_2003_ = lean_ctor_get(v_s_2002_, 3);
lean_inc_ref(v_cache_2003_);
v_toCacheableParserContext_2004_ = lean_ctor_get(v_c_2001_, 2);
v_stxStack_2005_ = lean_ctor_get(v_s_2002_, 0);
v_pos_2006_ = lean_ctor_get(v_s_2002_, 2);
v_recoveredErrors_2007_ = lean_ctor_get(v_s_2002_, 5);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_s_2002_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; lean_object* v_unused_2058_; lean_object* v_unused_2059_; 
v_unused_2057_ = lean_ctor_get(v_s_2002_, 4);
lean_dec(v_unused_2057_);
v_unused_2058_ = lean_ctor_get(v_s_2002_, 3);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_s_2002_, 1);
lean_dec(v_unused_2059_);
v___x_2009_ = v_s_2002_;
v_isShared_2010_ = v_isSharedCheck_2056_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_recoveredErrors_2007_);
lean_inc(v_pos_2006_);
lean_inc(v_stxStack_2005_);
lean_dec(v_s_2002_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2056_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_parserCache_2011_; lean_object* v_key_2012_; lean_object* v___x_2013_; 
v_parserCache_2011_ = lean_ctor_get(v_cache_2003_, 1);
lean_inc(v_pos_2006_);
lean_inc_ref(v_toCacheableParserContext_2004_);
v_key_2012_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_2012_, 0, v_toCacheableParserContext_2004_);
lean_ctor_set(v_key_2012_, 1, v_parserName_1999_);
lean_ctor_set(v_key_2012_, 2, v_pos_2006_);
v___x_2013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_2011_, v_key_2012_);
if (lean_obj_tag(v___x_2013_) == 1)
{
lean_object* v_val_2014_; lean_object* v_stx_2015_; lean_object* v_lhsPrec_2016_; lean_object* v_newPos_2017_; lean_object* v_errorMsg_2018_; lean_object* v___x_2019_; lean_object* v___x_2021_; 
lean_dec_ref_known(v_key_2012_, 3);
lean_dec(v_pos_2006_);
lean_dec_ref(v_c_2001_);
lean_dec_ref(v_p_2000_);
v_val_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_val_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v_stx_2015_ = lean_ctor_get(v_val_2014_, 0);
lean_inc(v_stx_2015_);
v_lhsPrec_2016_ = lean_ctor_get(v_val_2014_, 1);
lean_inc(v_lhsPrec_2016_);
v_newPos_2017_ = lean_ctor_get(v_val_2014_, 2);
lean_inc(v_newPos_2017_);
v_errorMsg_2018_ = lean_ctor_get(v_val_2014_, 3);
lean_inc(v_errorMsg_2018_);
lean_dec(v_val_2014_);
v___x_2019_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_2005_, v_stx_2015_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v_errorMsg_2018_);
lean_ctor_set(v___x_2009_, 2, v_newPos_2017_);
lean_ctor_set(v___x_2009_, 1, v_lhsPrec_2016_);
lean_ctor_set(v___x_2009_, 0, v___x_2019_);
v___x_2021_ = v___x_2009_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_lhsPrec_2016_);
lean_ctor_set(v_reuseFailAlloc_2022_, 2, v_newPos_2017_);
lean_ctor_set(v_reuseFailAlloc_2022_, 3, v_cache_2003_);
lean_ctor_set(v_reuseFailAlloc_2022_, 4, v_errorMsg_2018_);
lean_ctor_set(v_reuseFailAlloc_2022_, 5, v_recoveredErrors_2007_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
else
{
lean_object* v_raw_2023_; lean_object* v_initStackSz_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
lean_dec(v___x_2013_);
v_raw_2023_ = lean_ctor_get(v_stxStack_2005_, 0);
v_initStackSz_2024_ = lean_array_get_size(v_raw_2023_);
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = lean_box(0);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 4, v___x_2026_);
lean_ctor_set(v___x_2009_, 1, v___x_2025_);
v___x_2028_ = v___x_2009_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_stxStack_2005_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2055_, 2, v_pos_2006_);
lean_ctor_set(v_reuseFailAlloc_2055_, 3, v_cache_2003_);
lean_ctor_set(v_reuseFailAlloc_2055_, 4, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2055_, 5, v_recoveredErrors_2007_);
v___x_2028_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
lean_object* v_s_2029_; lean_object* v_cache_2030_; lean_object* v_stxStack_2031_; lean_object* v_lhsPrec_2032_; lean_object* v_pos_2033_; lean_object* v_errorMsg_2034_; lean_object* v_recoveredErrors_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2054_; 
v_s_2029_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_2024_, v_p_2000_, v_c_2001_, v___x_2028_);
v_cache_2030_ = lean_ctor_get(v_s_2029_, 3);
v_stxStack_2031_ = lean_ctor_get(v_s_2029_, 0);
v_lhsPrec_2032_ = lean_ctor_get(v_s_2029_, 1);
v_pos_2033_ = lean_ctor_get(v_s_2029_, 2);
v_errorMsg_2034_ = lean_ctor_get(v_s_2029_, 4);
v_recoveredErrors_2035_ = lean_ctor_get(v_s_2029_, 5);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_s_2029_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2037_ = v_s_2029_;
v_isShared_2038_ = v_isSharedCheck_2054_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_recoveredErrors_2035_);
lean_inc(v_errorMsg_2034_);
lean_inc(v_cache_2030_);
lean_inc(v_pos_2033_);
lean_inc(v_lhsPrec_2032_);
lean_inc(v_stxStack_2031_);
lean_dec(v_s_2029_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2054_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v_tokenCache_2039_; lean_object* v_parserCache_2040_; lean_object* v___x_2042_; uint8_t v_isShared_2043_; uint8_t v_isSharedCheck_2053_; 
v_tokenCache_2039_ = lean_ctor_get(v_cache_2030_, 0);
v_parserCache_2040_ = lean_ctor_get(v_cache_2030_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_cache_2030_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2042_ = v_cache_2030_;
v_isShared_2043_ = v_isSharedCheck_2053_;
goto v_resetjp_2041_;
}
else
{
lean_inc(v_parserCache_2040_);
lean_inc(v_tokenCache_2039_);
lean_dec(v_cache_2030_);
v___x_2042_ = lean_box(0);
v_isShared_2043_ = v_isSharedCheck_2053_;
goto v_resetjp_2041_;
}
v_resetjp_2041_:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2044_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2031_);
lean_inc(v_errorMsg_2034_);
lean_inc(v_pos_2033_);
lean_inc(v_lhsPrec_2032_);
v___x_2045_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2045_, 0, v___x_2044_);
lean_ctor_set(v___x_2045_, 1, v_lhsPrec_2032_);
lean_ctor_set(v___x_2045_, 2, v_pos_2033_);
lean_ctor_set(v___x_2045_, 3, v_errorMsg_2034_);
v___x_2046_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_2040_, v_key_2012_, v___x_2045_);
if (v_isShared_2043_ == 0)
{
lean_ctor_set(v___x_2042_, 1, v___x_2046_);
v___x_2048_ = v___x_2042_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_tokenCache_2039_);
lean_ctor_set(v_reuseFailAlloc_2052_, 1, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
lean_object* v___x_2050_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set(v___x_2037_, 3, v___x_2048_);
v___x_2050_ = v___x_2037_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_stxStack_2031_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_lhsPrec_2032_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v_pos_2033_);
lean_ctor_set(v_reuseFailAlloc_2051_, 3, v___x_2048_);
lean_ctor_set(v_reuseFailAlloc_2051_, 4, v_errorMsg_2034_);
lean_ctor_set(v_reuseFailAlloc_2051_, 5, v_recoveredErrors_2035_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2060_, lean_object* v_m_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2061_, v_a_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2064_, lean_object* v_m_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2064_, v_m_2065_, v_a_2066_);
lean_dec_ref(v_a_2066_);
lean_dec_ref(v_m_2065_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2068_, lean_object* v_m_2069_, lean_object* v_a_2070_, lean_object* v_b_2071_){
_start:
{
lean_object* v___x_2072_; 
v___x_2072_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2069_, v_a_2070_, v_b_2071_);
return v___x_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2073_, lean_object* v_a_2074_, lean_object* v_x_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2074_, v_x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2077_, lean_object* v_a_2078_, lean_object* v_x_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2077_, v_a_2078_, v_x_2079_);
lean_dec(v_x_2079_);
lean_dec_ref(v_a_2078_);
return v_res_2080_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2081_, lean_object* v_a_2082_, lean_object* v_x_2083_){
_start:
{
uint8_t v___x_2084_; 
v___x_2084_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2082_, v_x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2085_, lean_object* v_a_2086_, lean_object* v_x_2087_){
_start:
{
uint8_t v_res_2088_; lean_object* v_r_2089_; 
v_res_2088_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2085_, v_a_2086_, v_x_2087_);
lean_dec(v_x_2087_);
lean_dec_ref(v_a_2086_);
v_r_2089_ = lean_box(v_res_2088_);
return v_r_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2090_, lean_object* v_data_2091_){
_start:
{
lean_object* v___x_2092_; 
v___x_2092_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2091_);
return v___x_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2093_, lean_object* v_a_2094_, lean_object* v_b_2095_, lean_object* v_x_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2094_, v_b_2095_, v_x_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2098_, lean_object* v_i_2099_, lean_object* v_source_2100_, lean_object* v_target_2101_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2099_, v_source_2100_, v_target_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2104_, v_x_2105_);
return v___x_2106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2107_, lean_object* v_p_2108_){
_start:
{
lean_object* v_info_2109_; lean_object* v_fn_2110_; lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2118_; 
v_info_2109_ = lean_ctor_get(v_p_2108_, 0);
v_fn_2110_ = lean_ctor_get(v_p_2108_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_p_2108_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2112_ = v_p_2108_;
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
else
{
lean_inc(v_fn_2110_);
lean_inc(v_info_2109_);
lean_dec(v_p_2108_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2118_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2116_; 
v___x_2114_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2114_, 0, v_parserName_2107_);
lean_closure_set(v___x_2114_, 1, v_fn_2110_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 1, v___x_2114_);
v___x_2116_ = v___x_2112_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_info_2109_);
lean_ctor_set(v_reuseFailAlloc_2117_, 1, v___x_2114_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2127_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2128_ = l_Lean_addBuiltinDocString(v___x_2126_, v___x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2135_, lean_object* v_ictx_2136_, lean_object* v_pmctx_2137_, lean_object* v_tokens_2138_, lean_object* v_s_2139_){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__0));
v___x_2141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2141_, 0, v_ictx_2136_);
lean_ctor_set(v___x_2141_, 1, v_pmctx_2137_);
lean_ctor_set(v___x_2141_, 2, v___x_2140_);
lean_ctor_set(v___x_2141_, 3, v_tokens_2138_);
v___x_2142_ = lean_apply_2(v_p_2135_, v___x_2141_, v_s_2139_);
return v___x_2142_;
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
