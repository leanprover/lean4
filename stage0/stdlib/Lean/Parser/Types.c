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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2;
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
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
size_t v___x_58_; size_t v___x_59_; size_t v___x_60_; 
v___x_58_ = ((size_t)5ULL);
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_shift_left(v___x_59_, v___x_58_);
return v___x_60_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1(void){
_start:
{
size_t v___x_61_; size_t v___x_62_; size_t v___x_63_; 
v___x_61_ = ((size_t)1ULL);
v___x_62_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0);
v___x_63_ = lean_usize_sub(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_64_; 
v___x_64_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(lean_object* v_x_65_, size_t v_x_66_, size_t v_x_67_, lean_object* v_x_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_65_) == 0)
{
lean_object* v_es_70_; size_t v___x_71_; size_t v___x_72_; size_t v___x_73_; size_t v___x_74_; lean_object* v_j_75_; lean_object* v___x_76_; uint8_t v___x_77_; 
v_es_70_ = lean_ctor_get(v_x_65_, 0);
v___x_71_ = ((size_t)5ULL);
v___x_72_ = ((size_t)1ULL);
v___x_73_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__1);
v___x_74_ = lean_usize_land(v_x_66_, v___x_73_);
v_j_75_ = lean_usize_to_nat(v___x_74_);
v___x_76_ = lean_array_get_size(v_es_70_);
v___x_77_ = lean_nat_dec_lt(v_j_75_, v___x_76_);
if (v___x_77_ == 0)
{
lean_dec(v_j_75_);
lean_dec(v_x_69_);
lean_dec(v_x_68_);
return v_x_65_;
}
else
{
lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_114_; 
lean_inc_ref(v_es_70_);
v_isSharedCheck_114_ = !lean_is_exclusive(v_x_65_);
if (v_isSharedCheck_114_ == 0)
{
lean_object* v_unused_115_; 
v_unused_115_ = lean_ctor_get(v_x_65_, 0);
lean_dec(v_unused_115_);
v___x_79_ = v_x_65_;
v_isShared_80_ = v_isSharedCheck_114_;
goto v_resetjp_78_;
}
else
{
lean_dec(v_x_65_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_114_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v_v_81_; lean_object* v___x_82_; lean_object* v_xs_x27_83_; lean_object* v___y_85_; 
v_v_81_ = lean_array_fget(v_es_70_, v_j_75_);
v___x_82_ = lean_box(0);
v_xs_x27_83_ = lean_array_fset(v_es_70_, v_j_75_, v___x_82_);
switch(lean_obj_tag(v_v_81_))
{
case 0:
{
lean_object* v_key_90_; lean_object* v_val_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_101_; 
v_key_90_ = lean_ctor_get(v_v_81_, 0);
v_val_91_ = lean_ctor_get(v_v_81_, 1);
v_isSharedCheck_101_ = !lean_is_exclusive(v_v_81_);
if (v_isSharedCheck_101_ == 0)
{
v___x_93_ = v_v_81_;
v_isShared_94_ = v_isSharedCheck_101_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_val_91_);
lean_inc(v_key_90_);
lean_dec(v_v_81_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_101_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
uint8_t v___x_95_; 
v___x_95_ = lean_name_eq(v_x_68_, v_key_90_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; 
lean_del_object(v___x_93_);
v___x_96_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_90_, v_val_91_, v_x_68_, v_x_69_);
v___x_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
v___y_85_ = v___x_97_;
goto v___jp_84_;
}
else
{
lean_object* v___x_99_; 
lean_dec(v_val_91_);
lean_dec(v_key_90_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 1, v_x_69_);
lean_ctor_set(v___x_93_, 0, v_x_68_);
v___x_99_ = v___x_93_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_x_68_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_x_69_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
v___y_85_ = v___x_99_;
goto v___jp_84_;
}
}
}
}
case 1:
{
lean_object* v_node_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_112_; 
v_node_102_ = lean_ctor_get(v_v_81_, 0);
v_isSharedCheck_112_ = !lean_is_exclusive(v_v_81_);
if (v_isSharedCheck_112_ == 0)
{
v___x_104_ = v_v_81_;
v_isShared_105_ = v_isSharedCheck_112_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_node_102_);
lean_dec(v_v_81_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_112_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
size_t v___x_106_; size_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_106_ = lean_usize_shift_right(v_x_66_, v___x_71_);
v___x_107_ = lean_usize_add(v_x_67_, v___x_72_);
v___x_108_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_node_102_, v___x_106_, v___x_107_, v_x_68_, v_x_69_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 0, v___x_108_);
v___x_110_ = v___x_104_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
v___y_85_ = v___x_110_;
goto v___jp_84_;
}
}
}
default: 
{
lean_object* v___x_113_; 
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v_x_68_);
lean_ctor_set(v___x_113_, 1, v_x_69_);
v___y_85_ = v___x_113_;
goto v___jp_84_;
}
}
v___jp_84_:
{
lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_86_ = lean_array_fset(v_xs_x27_83_, v_j_75_, v___y_85_);
lean_dec(v_j_75_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_86_);
v___x_88_ = v___x_79_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v___x_86_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
}
}
}
else
{
lean_object* v_ks_116_; lean_object* v_vs_117_; lean_object* v___x_119_; uint8_t v_isShared_120_; uint8_t v_isSharedCheck_137_; 
v_ks_116_ = lean_ctor_get(v_x_65_, 0);
v_vs_117_ = lean_ctor_get(v_x_65_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_65_);
if (v_isSharedCheck_137_ == 0)
{
v___x_119_ = v_x_65_;
v_isShared_120_ = v_isSharedCheck_137_;
goto v_resetjp_118_;
}
else
{
lean_inc(v_vs_117_);
lean_inc(v_ks_116_);
lean_dec(v_x_65_);
v___x_119_ = lean_box(0);
v_isShared_120_ = v_isSharedCheck_137_;
goto v_resetjp_118_;
}
v_resetjp_118_:
{
lean_object* v___x_122_; 
if (v_isShared_120_ == 0)
{
v___x_122_ = v___x_119_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v_ks_116_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v_vs_117_);
v___x_122_ = v_reuseFailAlloc_136_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
lean_object* v_newNode_123_; uint8_t v___y_125_; size_t v___x_131_; uint8_t v___x_132_; 
v_newNode_123_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v___x_122_, v_x_68_, v_x_69_);
v___x_131_ = ((size_t)7ULL);
v___x_132_ = lean_usize_dec_le(v___x_131_, v_x_67_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_133_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_123_);
v___x_134_ = lean_unsigned_to_nat(4u);
v___x_135_ = lean_nat_dec_lt(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
v___y_125_ = v___x_135_;
goto v___jp_124_;
}
else
{
v___y_125_ = v___x_132_;
goto v___jp_124_;
}
v___jp_124_:
{
if (v___y_125_ == 0)
{
lean_object* v_ks_126_; lean_object* v_vs_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_ks_126_ = lean_ctor_get(v_newNode_123_, 0);
lean_inc_ref(v_ks_126_);
v_vs_127_ = lean_ctor_get(v_newNode_123_, 1);
lean_inc_ref(v_vs_127_);
lean_dec_ref(v_newNode_123_);
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__2);
v___x_130_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_x_67_, v_ks_126_, v_vs_127_, v___x_128_, v___x_129_);
lean_dec_ref(v_vs_127_);
lean_dec_ref(v_ks_126_);
return v___x_130_;
}
else
{
return v_newNode_123_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_138_, lean_object* v_keys_139_, lean_object* v_vals_140_, lean_object* v_i_141_, lean_object* v_entries_142_){
_start:
{
lean_object* v___x_143_; uint8_t v___x_144_; 
v___x_143_ = lean_array_get_size(v_keys_139_);
v___x_144_ = lean_nat_dec_lt(v_i_141_, v___x_143_);
if (v___x_144_ == 0)
{
lean_dec(v_i_141_);
return v_entries_142_;
}
else
{
lean_object* v_k_145_; lean_object* v_v_146_; uint64_t v___y_148_; 
v_k_145_ = lean_array_fget_borrowed(v_keys_139_, v_i_141_);
v_v_146_ = lean_array_fget_borrowed(v_vals_140_, v_i_141_);
if (lean_obj_tag(v_k_145_) == 0)
{
uint64_t v___x_159_; 
v___x_159_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_148_ = v___x_159_;
goto v___jp_147_;
}
else
{
uint64_t v_hash_160_; 
v_hash_160_ = lean_ctor_get_uint64(v_k_145_, sizeof(void*)*2);
v___y_148_ = v_hash_160_;
goto v___jp_147_;
}
v___jp_147_:
{
size_t v_h_149_; size_t v___x_150_; lean_object* v___x_151_; size_t v___x_152_; size_t v___x_153_; size_t v___x_154_; size_t v_h_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v_h_149_ = lean_uint64_to_usize(v___y_148_);
v___x_150_ = ((size_t)5ULL);
v___x_151_ = lean_unsigned_to_nat(1u);
v___x_152_ = ((size_t)1ULL);
v___x_153_ = lean_usize_sub(v_depth_138_, v___x_152_);
v___x_154_ = lean_usize_mul(v___x_150_, v___x_153_);
v_h_155_ = lean_usize_shift_right(v_h_149_, v___x_154_);
v___x_156_ = lean_nat_add(v_i_141_, v___x_151_);
lean_dec(v_i_141_);
lean_inc(v_v_146_);
lean_inc(v_k_145_);
v___x_157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_entries_142_, v_h_155_, v_depth_138_, v_k_145_, v_v_146_);
v_i_141_ = v___x_156_;
v_entries_142_ = v___x_157_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_161_, lean_object* v_keys_162_, lean_object* v_vals_163_, lean_object* v_i_164_, lean_object* v_entries_165_){
_start:
{
size_t v_depth_boxed_166_; lean_object* v_res_167_; 
v_depth_boxed_166_ = lean_unbox_usize(v_depth_161_);
lean_dec(v_depth_161_);
v_res_167_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_166_, v_keys_162_, v_vals_163_, v_i_164_, v_entries_165_);
lean_dec_ref(v_vals_163_);
lean_dec_ref(v_keys_162_);
return v_res_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_168_, lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_, lean_object* v_x_172_){
_start:
{
size_t v_x_371__boxed_173_; size_t v_x_372__boxed_174_; lean_object* v_res_175_; 
v_x_371__boxed_173_ = lean_unbox_usize(v_x_169_);
lean_dec(v_x_169_);
v_x_372__boxed_174_ = lean_unbox_usize(v_x_170_);
lean_dec(v_x_170_);
v_res_175_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_168_, v_x_371__boxed_173_, v_x_372__boxed_174_, v_x_171_, v_x_172_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(lean_object* v_x_176_, lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
uint64_t v___y_180_; 
if (lean_obj_tag(v_x_177_) == 0)
{
uint64_t v___x_184_; 
v___x_184_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_180_ = v___x_184_;
goto v___jp_179_;
}
else
{
uint64_t v_hash_185_; 
v_hash_185_ = lean_ctor_get_uint64(v_x_177_, sizeof(void*)*2);
v___y_180_ = v_hash_185_;
goto v___jp_179_;
}
v___jp_179_:
{
size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_uint64_to_usize(v___y_180_);
v___x_182_ = ((size_t)1ULL);
v___x_183_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_176_, v___x_181_, v___x_182_, v_x_177_, v_x_178_);
return v___x_183_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object* v_s_186_, lean_object* v_k_187_){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_box(0);
v___x_189_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_s_186_, v_k_187_, v___x_188_);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0(lean_object* v_00_u03b2_190_, lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_x_191_, v_x_192_, v_x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_195_, lean_object* v_x_196_, size_t v_x_197_, size_t v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_196_, v_x_197_, v_x_198_, v_x_199_, v_x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_202_, lean_object* v_x_203_, lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
size_t v_x_570__boxed_208_; size_t v_x_571__boxed_209_; lean_object* v_res_210_; 
v_x_570__boxed_208_ = lean_unbox_usize(v_x_204_);
lean_dec(v_x_204_);
v_x_571__boxed_209_ = lean_unbox_usize(v_x_205_);
lean_dec(v_x_205_);
v_res_210_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(v_00_u03b2_202_, v_x_203_, v_x_570__boxed_208_, v_x_571__boxed_209_, v_x_206_, v_x_207_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_211_, lean_object* v_n_212_, lean_object* v_k_213_, lean_object* v_v_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v_n_212_, v_k_213_, v_v_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_216_, size_t v_depth_217_, lean_object* v_keys_218_, lean_object* v_vals_219_, lean_object* v_heq_220_, lean_object* v_i_221_, lean_object* v_entries_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_217_, v_keys_218_, v_vals_219_, v_i_221_, v_entries_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_224_, lean_object* v_depth_225_, lean_object* v_keys_226_, lean_object* v_vals_227_, lean_object* v_heq_228_, lean_object* v_i_229_, lean_object* v_entries_230_){
_start:
{
size_t v_depth_boxed_231_; lean_object* v_res_232_; 
v_depth_boxed_231_ = lean_unbox_usize(v_depth_225_);
lean_dec(v_depth_225_);
v_res_232_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(v_00_u03b2_224_, v_depth_boxed_231_, v_keys_226_, v_vals_227_, v_heq_228_, v_i_229_, v_entries_230_);
lean_dec_ref(v_vals_227_);
lean_dec_ref(v_keys_226_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_233_, lean_object* v_x_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_234_, v_x_235_, v_x_236_, v_x_237_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10));
v___x_266_ = l_Lean_mkAtom(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12);
v___x_268_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_269_ = lean_array_push(v___x_268_, v___x_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_281_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_282_ = lean_array_push(v___x_281_, v___x_280_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_283_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17);
v___x_284_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15));
v___x_285_ = lean_box(2);
v___x_286_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_284_);
lean_ctor_set(v___x_286_, 2, v___x_283_);
return v___x_286_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19(void){
_start:
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_287_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18);
v___x_288_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13);
v___x_289_ = lean_array_push(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20(void){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_290_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_291_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19);
v___x_292_ = lean_array_push(v___x_291_, v___x_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21(void){
_start:
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_293_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_294_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20);
v___x_295_ = lean_array_push(v___x_294_, v___x_293_);
return v___x_295_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_297_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21);
v___x_298_ = lean_array_push(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_300_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22);
v___x_301_ = lean_array_push(v___x_300_, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_302_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23);
v___x_303_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11));
v___x_304_ = lean_box(2);
v___x_305_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_305_, 0, v___x_304_);
lean_ctor_set(v___x_305_, 1, v___x_303_);
lean_ctor_set(v___x_305_, 2, v___x_302_);
return v___x_305_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_306_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24);
v___x_307_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_308_ = lean_array_push(v___x_307_, v___x_306_);
return v___x_308_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_309_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25);
v___x_310_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9));
v___x_311_ = lean_box(2);
v___x_312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_312_, 0, v___x_311_);
lean_ctor_set(v___x_312_, 1, v___x_310_);
lean_ctor_set(v___x_312_, 2, v___x_309_);
return v___x_312_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_313_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26);
v___x_314_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_315_ = lean_array_push(v___x_314_, v___x_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28(void){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_316_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27);
v___x_317_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7));
v___x_318_ = lean_box(2);
v___x_319_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v___x_317_);
lean_ctor_set(v___x_319_, 2, v___x_316_);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28);
v___x_321_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_322_ = lean_array_push(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_323_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29);
v___x_324_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4));
v___x_325_ = lean_box(2);
v___x_326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
lean_ctor_set(v___x_326_, 2, v___x_323_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam(void){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__1(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_330_ = lean_string_utf8_byte_size(v___x_329_);
return v___x_330_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__2(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = lean_obj_once(&l_Lean_Parser_instInhabitedInputContext___closed__1, &l_Lean_Parser_instInhabitedInputContext___closed__1_once, _init_l_Lean_Parser_instInhabitedInputContext___closed__1);
v___x_332_ = l_Lean_instInhabitedFileMap_default;
v___x_333_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
lean_ctor_set(v___x_334_, 2, v___x_332_);
lean_ctor_set(v___x_334_, 3, v___x_331_);
return v___x_334_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext(void){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_obj_once(&l_Lean_Parser_instInhabitedInputContext___closed__2, &l_Lean_Parser_instInhabitedInputContext___closed__2_once, _init_l_Lean_Parser_instInhabitedInputContext___closed__2);
return v___x_335_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_mk___auto__1(void){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk___redArg(lean_object* v_input_337_, lean_object* v_fileName_338_, lean_object* v_endPos_339_, lean_object* v_fileMap_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_341_, 0, v_input_337_);
lean_ctor_set(v___x_341_, 1, v_fileName_338_);
lean_ctor_set(v___x_341_, 2, v_fileMap_340_);
lean_ctor_set(v___x_341_, 3, v_endPos_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk(lean_object* v_input_342_, lean_object* v_fileName_343_, lean_object* v_endPos_344_, lean_object* v_endPos__valid_345_, lean_object* v_fileMap_346_){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_347_, 0, v_input_342_);
lean_ctor_set(v___x_347_, 1, v_fileName_343_);
lean_ctor_set(v___x_347_, 2, v_fileMap_346_);
lean_ctor_set(v___x_347_, 3, v_endPos_344_);
return v___x_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input(lean_object* v_c_348_){
_start:
{
lean_object* v_inputString_349_; lean_object* v_endPos_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_inputString_349_ = lean_ctor_get(v_c_348_, 0);
v_endPos_350_ = lean_ctor_get(v_c_348_, 3);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_string_utf8_extract(v_inputString_349_, v___x_351_, v_endPos_350_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input___boxed(lean_object* v_c_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Parser_InputContext_input(v_c_353_);
lean_dec_ref(v_c_353_);
return v_res_354_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_InputContext_atEnd(lean_object* v_c_355_, lean_object* v_p_356_){
_start:
{
lean_object* v_endPos_357_; uint8_t v___x_358_; 
v_endPos_357_ = lean_ctor_get(v_c_355_, 3);
v___x_358_ = lean_nat_dec_le(v_endPos_357_, v_p_356_);
return v___x_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_atEnd___boxed(lean_object* v_c_359_, lean_object* v_p_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Lean_Parser_InputContext_atEnd(v_c_359_, v_p_360_);
lean_dec(v_p_360_);
lean_dec_ref(v_c_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get(lean_object* v_c_363_, lean_object* v_p_364_){
_start:
{
lean_object* v_inputString_365_; uint32_t v___x_366_; 
v_inputString_365_ = lean_ctor_get(v_c_363_, 0);
v___x_366_ = lean_string_utf8_get(v_inputString_365_, v_p_364_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get___boxed(lean_object* v_c_367_, lean_object* v_p_368_){
_start:
{
uint32_t v_res_369_; lean_object* v_r_370_; 
v_res_369_ = l_Lean_Parser_InputContext_get(v_c_367_, v_p_368_);
lean_dec(v_p_368_);
lean_dec_ref(v_c_367_);
v_r_370_ = lean_box_uint32(v_res_369_);
return v_r_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_h__1_373_){
_start:
{
lean_object* v___x_374_; 
v___x_374_ = lean_apply_2(v_h__1_373_, v_x_371_, v_x_372_);
return v___x_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_375_, lean_object* v_x_376_, lean_object* v_x_377_, lean_object* v_h__1_378_){
_start:
{
lean_object* v___x_379_; 
v___x_379_ = lean_apply_2(v_h__1_378_, v_x_376_, v_x_377_);
return v___x_379_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27___redArg(lean_object* v_c_380_, lean_object* v_p_381_){
_start:
{
lean_object* v_inputString_382_; uint32_t v___x_383_; 
v_inputString_382_ = lean_ctor_get(v_c_380_, 0);
v___x_383_ = lean_string_utf8_get_fast(v_inputString_382_, v_p_381_);
return v___x_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___redArg___boxed(lean_object* v_c_384_, lean_object* v_p_385_){
_start:
{
uint32_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Lean_Parser_InputContext_get_x27___redArg(v_c_384_, v_p_385_);
lean_dec(v_p_385_);
lean_dec_ref(v_c_384_);
v_r_387_ = lean_box_uint32(v_res_386_);
return v_r_387_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27(lean_object* v_c_388_, lean_object* v_p_389_, lean_object* v_h_390_){
_start:
{
lean_object* v_inputString_391_; uint32_t v___x_392_; 
v_inputString_391_ = lean_ctor_get(v_c_388_, 0);
v___x_392_ = lean_string_utf8_get_fast(v_inputString_391_, v_p_389_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___boxed(lean_object* v_c_393_, lean_object* v_p_394_, lean_object* v_h_395_){
_start:
{
uint32_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Lean_Parser_InputContext_get_x27(v_c_393_, v_p_394_, v_h_395_);
lean_dec(v_p_394_);
lean_dec_ref(v_c_393_);
v_r_397_ = lean_box_uint32(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next(lean_object* v_c_398_, lean_object* v_p_399_){
_start:
{
lean_object* v_inputString_400_; lean_object* v___x_401_; 
v_inputString_400_ = lean_ctor_get(v_c_398_, 0);
v___x_401_ = lean_string_utf8_next(v_inputString_400_, v_p_399_);
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next___boxed(lean_object* v_c_402_, lean_object* v_p_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Parser_InputContext_next(v_c_402_, v_p_403_);
lean_dec(v_p_403_);
lean_dec_ref(v_c_402_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg(lean_object* v_c_405_, lean_object* v_p_406_){
_start:
{
lean_object* v_inputString_407_; lean_object* v___x_408_; 
v_inputString_407_ = lean_ctor_get(v_c_405_, 0);
v___x_408_ = lean_string_utf8_next_fast(v_inputString_407_, v_p_406_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg___boxed(lean_object* v_c_409_, lean_object* v_p_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Lean_Parser_InputContext_next_x27___redArg(v_c_409_, v_p_410_);
lean_dec(v_p_410_);
lean_dec_ref(v_c_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27(lean_object* v_c_412_, lean_object* v_p_413_, lean_object* v_h_414_){
_start:
{
lean_object* v_inputString_415_; lean_object* v___x_416_; 
v_inputString_415_ = lean_ctor_get(v_c_412_, 0);
v___x_416_ = lean_string_utf8_next_fast(v_inputString_415_, v_p_413_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___boxed(lean_object* v_c_417_, lean_object* v_p_418_, lean_object* v_h_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Parser_InputContext_next_x27(v_c_417_, v_p_418_, v_h_419_);
lean_dec(v_p_418_);
lean_dec_ref(v_c_417_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract(lean_object* v_c_421_, lean_object* v_a_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_inputString_424_; lean_object* v___x_425_; 
v_inputString_424_ = lean_ctor_get(v_c_421_, 0);
v___x_425_ = lean_string_utf8_extract(v_inputString_424_, v_a_422_, v_a_423_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract___boxed(lean_object* v_c_426_, lean_object* v_a_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Parser_InputContext_extract(v_c_426_, v_a_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_c_426_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring(lean_object* v_c_430_, lean_object* v_startPos_431_, lean_object* v_stopPos_432_){
_start:
{
lean_object* v_inputString_433_; lean_object* v_endPos_434_; uint8_t v___x_435_; 
v_inputString_433_ = lean_ctor_get(v_c_430_, 0);
v_endPos_434_ = lean_ctor_get(v_c_430_, 3);
v___x_435_ = lean_nat_dec_le(v_stopPos_432_, v_endPos_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_436_; 
lean_dec(v_stopPos_432_);
lean_inc(v_endPos_434_);
lean_inc_ref(v_inputString_433_);
v___x_436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_436_, 0, v_inputString_433_);
lean_ctor_set(v___x_436_, 1, v_startPos_431_);
lean_ctor_set(v___x_436_, 2, v_endPos_434_);
return v___x_436_;
}
else
{
lean_object* v___x_437_; 
lean_inc_ref(v_inputString_433_);
v___x_437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_437_, 0, v_inputString_433_);
lean_ctor_set(v___x_437_, 1, v_startPos_431_);
lean_ctor_set(v___x_437_, 2, v_stopPos_432_);
return v___x_437_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring___boxed(lean_object* v_c_438_, lean_object* v_startPos_439_, lean_object* v_stopPos_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Lean_Parser_InputContext_substring(v_c_438_, v_startPos_439_, v_stopPos_440_);
lean_dec_ref(v_c_438_);
return v_res_441_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_getNext(lean_object* v_input_442_, lean_object* v_pos_443_){
_start:
{
lean_object* v_inputString_444_; lean_object* v___x_445_; uint32_t v___x_446_; 
v_inputString_444_ = lean_ctor_get(v_input_442_, 0);
v___x_445_ = lean_string_utf8_next(v_inputString_444_, v_pos_443_);
v___x_446_ = lean_string_utf8_get(v_inputString_444_, v___x_445_);
lean_dec(v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_getNext___boxed(lean_object* v_input_447_, lean_object* v_pos_448_){
_start:
{
uint32_t v_res_449_; lean_object* v_r_450_; 
v_res_449_ = l_Lean_Parser_InputContext_getNext(v_input_447_, v_pos_448_);
lean_dec(v_pos_448_);
lean_dec_ref(v_input_447_);
v_r_450_ = lean_box_uint32(v_res_449_);
return v_r_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev(lean_object* v_c_451_, lean_object* v_pos_452_){
_start:
{
lean_object* v_inputString_453_; lean_object* v___x_454_; 
v_inputString_453_ = lean_ctor_get(v_c_451_, 0);
v___x_454_ = lean_string_utf8_prev(v_inputString_453_, v_pos_452_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev___boxed(lean_object* v_c_455_, lean_object* v_pos_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_Parser_InputContext_prev(v_c_455_, v_pos_456_);
lean_dec(v_pos_456_);
lean_dec_ref(v_c_455_);
return v_res_457_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(lean_object* v_x_458_, lean_object* v_x_459_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
if (lean_obj_tag(v_x_459_) == 0)
{
uint8_t v___x_460_; 
v___x_460_ = 1;
return v___x_460_;
}
else
{
uint8_t v___x_461_; 
v___x_461_ = 0;
return v___x_461_;
}
}
else
{
if (lean_obj_tag(v_x_459_) == 0)
{
uint8_t v___x_462_; 
v___x_462_ = 0;
return v___x_462_;
}
else
{
lean_object* v_val_463_; lean_object* v_val_464_; uint8_t v___x_465_; 
v_val_463_ = lean_ctor_get(v_x_458_, 0);
v_val_464_ = lean_ctor_get(v_x_459_, 0);
v___x_465_ = lean_nat_dec_eq(v_val_463_, v_val_464_);
return v___x_465_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0___boxed(lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
uint8_t v_res_468_; lean_object* v_r_469_; 
v_res_468_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(v_x_466_, v_x_467_);
lean_dec(v_x_467_);
lean_dec(v_x_466_);
v_r_469_ = lean_box(v_res_468_);
return v_r_469_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(lean_object* v_x_470_, lean_object* v_x_471_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
if (lean_obj_tag(v_x_471_) == 0)
{
uint8_t v___x_472_; 
v___x_472_ = 1;
return v___x_472_;
}
else
{
uint8_t v___x_473_; 
v___x_473_ = 0;
return v___x_473_;
}
}
else
{
if (lean_obj_tag(v_x_471_) == 0)
{
uint8_t v___x_474_; 
v___x_474_ = 0;
return v___x_474_;
}
else
{
lean_object* v_val_475_; lean_object* v_val_476_; uint8_t v___x_477_; 
v_val_475_ = lean_ctor_get(v_x_470_, 0);
v_val_476_ = lean_ctor_get(v_x_471_, 0);
v___x_477_ = lean_string_dec_eq(v_val_475_, v_val_476_);
return v___x_477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1___boxed(lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(v_x_478_, v_x_479_);
lean_dec(v_x_479_);
lean_dec(v_x_478_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext_beq(lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v_prec_484_; lean_object* v_quotDepth_485_; uint8_t v_suppressInsideQuot_486_; lean_object* v_savedPos_x3f_487_; lean_object* v_forbiddenTk_x3f_488_; lean_object* v_prec_489_; lean_object* v_quotDepth_490_; uint8_t v_suppressInsideQuot_491_; lean_object* v_savedPos_x3f_492_; lean_object* v_forbiddenTk_x3f_493_; uint8_t v___y_495_; uint8_t v___x_498_; 
v_prec_484_ = lean_ctor_get(v_x_482_, 0);
v_quotDepth_485_ = lean_ctor_get(v_x_482_, 1);
v_suppressInsideQuot_486_ = lean_ctor_get_uint8(v_x_482_, sizeof(void*)*4);
v_savedPos_x3f_487_ = lean_ctor_get(v_x_482_, 2);
v_forbiddenTk_x3f_488_ = lean_ctor_get(v_x_482_, 3);
v_prec_489_ = lean_ctor_get(v_x_483_, 0);
v_quotDepth_490_ = lean_ctor_get(v_x_483_, 1);
v_suppressInsideQuot_491_ = lean_ctor_get_uint8(v_x_483_, sizeof(void*)*4);
v_savedPos_x3f_492_ = lean_ctor_get(v_x_483_, 2);
v_forbiddenTk_x3f_493_ = lean_ctor_get(v_x_483_, 3);
v___x_498_ = lean_nat_dec_eq(v_prec_484_, v_prec_489_);
if (v___x_498_ == 0)
{
return v___x_498_;
}
else
{
uint8_t v___x_499_; 
v___x_499_ = lean_nat_dec_eq(v_quotDepth_485_, v_quotDepth_490_);
if (v___x_499_ == 0)
{
return v___x_499_;
}
else
{
if (v_suppressInsideQuot_486_ == 0)
{
if (v_suppressInsideQuot_491_ == 0)
{
v___y_495_ = v___x_499_;
goto v___jp_494_;
}
else
{
return v_suppressInsideQuot_486_;
}
}
else
{
v___y_495_ = v_suppressInsideQuot_491_;
goto v___jp_494_;
}
}
}
v___jp_494_:
{
if (v___y_495_ == 0)
{
return v___y_495_;
}
else
{
uint8_t v___x_496_; 
v___x_496_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__0(v_savedPos_x3f_487_, v_savedPos_x3f_492_);
if (v___x_496_ == 0)
{
return v___x_496_;
}
else
{
uint8_t v___x_497_; 
v___x_497_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqCacheableParserContext_beq_spec__1(v_forbiddenTk_x3f_488_, v_forbiddenTk_x3f_493_);
return v___x_497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext_beq___boxed(lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
uint8_t v_res_502_; lean_object* v_r_503_; 
v_res_502_ = l_Lean_Parser_instBEqCacheableParserContext_beq(v_x_500_, v_x_501_);
lean_dec_ref(v_x_501_);
lean_dec_ref(v_x_500_);
v_r_503_ = lean_box(v_res_502_);
return v_r_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0(lean_object* v_x_506_){
_start:
{
lean_object* v_toInputContext_507_; 
v_toInputContext_507_ = lean_ctor_get(v_x_506_, 0);
lean_inc_ref(v_toInputContext_507_);
return v_toInputContext_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(lean_object* v_x_508_){
_start:
{
lean_object* v_res_509_; 
v_res_509_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_508_);
lean_dec_ref(v_x_508_);
return v_res_509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos___redArg(lean_object* v_c_512_, lean_object* v_endPos_513_){
_start:
{
lean_object* v_toInputContext_514_; lean_object* v_toParserModuleContext_515_; lean_object* v_toCacheableParserContext_516_; lean_object* v_tokens_517_; lean_object* v___x_519_; uint8_t v_isShared_520_; uint8_t v_isSharedCheck_535_; 
v_toInputContext_514_ = lean_ctor_get(v_c_512_, 0);
v_toParserModuleContext_515_ = lean_ctor_get(v_c_512_, 1);
v_toCacheableParserContext_516_ = lean_ctor_get(v_c_512_, 2);
v_tokens_517_ = lean_ctor_get(v_c_512_, 3);
v_isSharedCheck_535_ = !lean_is_exclusive(v_c_512_);
if (v_isSharedCheck_535_ == 0)
{
v___x_519_ = v_c_512_;
v_isShared_520_ = v_isSharedCheck_535_;
goto v_resetjp_518_;
}
else
{
lean_inc(v_tokens_517_);
lean_inc(v_toCacheableParserContext_516_);
lean_inc(v_toParserModuleContext_515_);
lean_inc(v_toInputContext_514_);
lean_dec(v_c_512_);
v___x_519_ = lean_box(0);
v_isShared_520_ = v_isSharedCheck_535_;
goto v_resetjp_518_;
}
v_resetjp_518_:
{
lean_object* v_inputString_521_; lean_object* v_fileName_522_; lean_object* v_fileMap_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_533_; 
v_inputString_521_ = lean_ctor_get(v_toInputContext_514_, 0);
v_fileName_522_ = lean_ctor_get(v_toInputContext_514_, 1);
v_fileMap_523_ = lean_ctor_get(v_toInputContext_514_, 2);
v_isSharedCheck_533_ = !lean_is_exclusive(v_toInputContext_514_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v_toInputContext_514_, 3);
lean_dec(v_unused_534_);
v___x_525_ = v_toInputContext_514_;
v_isShared_526_ = v_isSharedCheck_533_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_fileMap_523_);
lean_inc(v_fileName_522_);
lean_inc(v_inputString_521_);
lean_dec(v_toInputContext_514_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_533_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 3, v_endPos_513_);
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_inputString_521_);
lean_ctor_set(v_reuseFailAlloc_532_, 1, v_fileName_522_);
lean_ctor_set(v_reuseFailAlloc_532_, 2, v_fileMap_523_);
lean_ctor_set(v_reuseFailAlloc_532_, 3, v_endPos_513_);
v___x_528_ = v_reuseFailAlloc_532_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_530_; 
if (v_isShared_520_ == 0)
{
lean_ctor_set(v___x_519_, 0, v___x_528_);
v___x_530_ = v___x_519_;
goto v_reusejp_529_;
}
else
{
lean_object* v_reuseFailAlloc_531_; 
v_reuseFailAlloc_531_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_531_, 0, v___x_528_);
lean_ctor_set(v_reuseFailAlloc_531_, 1, v_toParserModuleContext_515_);
lean_ctor_set(v_reuseFailAlloc_531_, 2, v_toCacheableParserContext_516_);
lean_ctor_set(v_reuseFailAlloc_531_, 3, v_tokens_517_);
v___x_530_ = v_reuseFailAlloc_531_;
goto v_reusejp_529_;
}
v_reusejp_529_:
{
return v___x_530_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos(lean_object* v_c_536_, lean_object* v_endPos_537_, lean_object* v_endPos__valid_538_){
_start:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_536_, v_endPos_537_);
return v___x_539_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
if (lean_obj_tag(v_x_546_) == 0)
{
if (lean_obj_tag(v_x_547_) == 0)
{
uint8_t v___x_548_; 
v___x_548_ = 1;
return v___x_548_;
}
else
{
uint8_t v___x_549_; 
v___x_549_ = 0;
return v___x_549_;
}
}
else
{
if (lean_obj_tag(v_x_547_) == 0)
{
uint8_t v___x_550_; 
v___x_550_ = 0;
return v___x_550_;
}
else
{
lean_object* v_head_551_; lean_object* v_tail_552_; lean_object* v_head_553_; lean_object* v_tail_554_; uint8_t v___x_555_; 
v_head_551_ = lean_ctor_get(v_x_546_, 0);
v_tail_552_ = lean_ctor_get(v_x_546_, 1);
v_head_553_ = lean_ctor_get(v_x_547_, 0);
v_tail_554_ = lean_ctor_get(v_x_547_, 1);
v___x_555_ = lean_string_dec_eq(v_head_551_, v_head_553_);
if (v___x_555_ == 0)
{
return v___x_555_;
}
else
{
v_x_546_ = v_tail_552_;
v_x_547_ = v_tail_554_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
uint8_t v_res_559_; lean_object* v_r_560_; 
v_res_559_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_557_, v_x_558_);
lean_dec(v_x_558_);
lean_dec(v_x_557_);
v_r_560_ = lean_box(v_res_559_);
return v_r_560_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqError_beq(lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
lean_object* v_unexpectedTk_563_; lean_object* v_unexpected_564_; lean_object* v_expected_565_; lean_object* v_unexpectedTk_566_; lean_object* v_unexpected_567_; lean_object* v_expected_568_; uint8_t v___x_569_; 
v_unexpectedTk_563_ = lean_ctor_get(v_x_561_, 0);
lean_inc(v_unexpectedTk_563_);
v_unexpected_564_ = lean_ctor_get(v_x_561_, 1);
lean_inc_ref(v_unexpected_564_);
v_expected_565_ = lean_ctor_get(v_x_561_, 2);
lean_inc(v_expected_565_);
lean_dec_ref(v_x_561_);
v_unexpectedTk_566_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_unexpectedTk_566_);
v_unexpected_567_ = lean_ctor_get(v_x_562_, 1);
lean_inc_ref(v_unexpected_567_);
v_expected_568_ = lean_ctor_get(v_x_562_, 2);
lean_inc(v_expected_568_);
lean_dec_ref(v_x_562_);
v___x_569_ = l_Lean_Syntax_structEq(v_unexpectedTk_563_, v_unexpectedTk_566_);
if (v___x_569_ == 0)
{
lean_dec(v_expected_568_);
lean_dec_ref(v_unexpected_567_);
lean_dec(v_expected_565_);
lean_dec_ref(v_unexpected_564_);
return v___x_569_;
}
else
{
uint8_t v___x_570_; 
v___x_570_ = lean_string_dec_eq(v_unexpected_564_, v_unexpected_567_);
lean_dec_ref(v_unexpected_567_);
lean_dec_ref(v_unexpected_564_);
if (v___x_570_ == 0)
{
lean_dec(v_expected_568_);
lean_dec(v_expected_565_);
return v___x_570_;
}
else
{
uint8_t v___x_571_; 
v___x_571_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_565_, v_expected_568_);
lean_dec(v_expected_568_);
lean_dec(v_expected_565_);
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
uint8_t v_res_574_; lean_object* v_r_575_; 
v_res_574_ = l_Lean_Parser_instBEqError_beq(v_x_572_, v_x_573_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* v_x_580_){
_start:
{
if (lean_obj_tag(v_x_580_) == 0)
{
lean_object* v___x_581_; 
v___x_581_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
return v___x_581_;
}
else
{
lean_object* v_tail_582_; 
v_tail_582_ = lean_ctor_get(v_x_580_, 1);
if (lean_obj_tag(v_tail_582_) == 0)
{
lean_object* v_head_583_; 
v_head_583_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_head_583_);
lean_dec_ref(v_x_580_);
return v_head_583_;
}
else
{
lean_object* v_tail_584_; 
lean_inc_ref(v_tail_582_);
v_tail_584_ = lean_ctor_get(v_tail_582_, 1);
if (lean_obj_tag(v_tail_584_) == 0)
{
lean_object* v_head_585_; lean_object* v_head_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; 
v_head_585_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_head_585_);
lean_dec_ref(v_x_580_);
v_head_586_ = lean_ctor_get(v_tail_582_, 0);
lean_inc(v_head_586_);
lean_dec_ref(v_tail_582_);
v___x_587_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0));
v___x_588_ = lean_string_append(v_head_585_, v___x_587_);
v___x_589_ = lean_string_append(v___x_588_, v_head_586_);
lean_dec(v_head_586_);
return v___x_589_;
}
else
{
lean_object* v_head_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; 
v_head_590_ = lean_ctor_get(v_x_580_, 0);
lean_inc(v_head_590_);
lean_dec_ref(v_x_580_);
v___x_591_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_592_ = lean_string_append(v_head_590_, v___x_591_);
v___x_593_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_tail_582_);
v___x_594_ = lean_string_append(v___x_592_, v___x_593_);
lean_dec_ref(v___x_593_);
return v___x_594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object* v_as_596_){
_start:
{
lean_object* v___f_597_; lean_object* v___x_598_; 
v___f_597_ = ((lean_object*)(l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0___closed__0));
v___x_598_ = l_List_eraseRepsBy___redArg(v___f_597_, v_as_596_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object* v_hi_599_, lean_object* v_pivot_600_, lean_object* v_as_601_, lean_object* v_i_602_, lean_object* v_k_603_){
_start:
{
uint8_t v___x_604_; 
v___x_604_ = lean_nat_dec_lt(v_k_603_, v_hi_599_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
lean_dec(v_k_603_);
v___x_605_ = lean_array_fswap(v_as_601_, v_i_602_, v_hi_599_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v_i_602_);
lean_ctor_set(v___x_606_, 1, v___x_605_);
return v___x_606_;
}
else
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = lean_array_fget_borrowed(v_as_601_, v_k_603_);
v___x_608_ = lean_string_dec_lt(v___x_607_, v_pivot_600_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_k_603_, v___x_609_);
lean_dec(v_k_603_);
v_k_603_ = v___x_610_;
goto _start;
}
else
{
lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_612_ = lean_array_fswap(v_as_601_, v_i_602_, v_k_603_);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v_i_602_, v___x_613_);
lean_dec(v_i_602_);
v___x_615_ = lean_nat_add(v_k_603_, v___x_613_);
lean_dec(v_k_603_);
v_as_601_ = v___x_612_;
v_i_602_ = v___x_614_;
v_k_603_ = v___x_615_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object* v_hi_617_, lean_object* v_pivot_618_, lean_object* v_as_619_, lean_object* v_i_620_, lean_object* v_k_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_617_, v_pivot_618_, v_as_619_, v_i_620_, v_k_621_);
lean_dec_ref(v_pivot_618_);
lean_dec(v_hi_617_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_n_623_, lean_object* v_as_624_, lean_object* v_lo_625_, lean_object* v_hi_626_){
_start:
{
lean_object* v___y_628_; uint8_t v___x_638_; 
v___x_638_ = lean_nat_dec_lt(v_lo_625_, v_hi_626_);
if (v___x_638_ == 0)
{
lean_dec(v_lo_625_);
return v_as_624_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v_mid_641_; lean_object* v___y_643_; lean_object* v___y_649_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_639_ = lean_nat_add(v_lo_625_, v_hi_626_);
v___x_640_ = lean_unsigned_to_nat(1u);
v_mid_641_ = lean_nat_shiftr(v___x_639_, v___x_640_);
lean_dec(v___x_639_);
v___x_654_ = lean_array_fget_borrowed(v_as_624_, v_mid_641_);
v___x_655_ = lean_array_fget_borrowed(v_as_624_, v_lo_625_);
v___x_656_ = lean_string_dec_lt(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
v___y_649_ = v_as_624_;
goto v___jp_648_;
}
else
{
lean_object* v___x_657_; 
v___x_657_ = lean_array_fswap(v_as_624_, v_lo_625_, v_mid_641_);
v___y_649_ = v___x_657_;
goto v___jp_648_;
}
v___jp_642_:
{
lean_object* v___x_644_; lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_644_ = lean_array_fget_borrowed(v___y_643_, v_mid_641_);
v___x_645_ = lean_array_fget_borrowed(v___y_643_, v_hi_626_);
v___x_646_ = lean_string_dec_lt(v___x_644_, v___x_645_);
if (v___x_646_ == 0)
{
lean_dec(v_mid_641_);
v___y_628_ = v___y_643_;
goto v___jp_627_;
}
else
{
lean_object* v___x_647_; 
v___x_647_ = lean_array_fswap(v___y_643_, v_mid_641_, v_hi_626_);
lean_dec(v_mid_641_);
v___y_628_ = v___x_647_;
goto v___jp_627_;
}
}
v___jp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_650_ = lean_array_fget_borrowed(v___y_649_, v_hi_626_);
v___x_651_ = lean_array_fget_borrowed(v___y_649_, v_lo_625_);
v___x_652_ = lean_string_dec_lt(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
v___y_643_ = v___y_649_;
goto v___jp_642_;
}
else
{
lean_object* v___x_653_; 
v___x_653_ = lean_array_fswap(v___y_649_, v_lo_625_, v_hi_626_);
v___y_643_ = v___x_653_;
goto v___jp_642_;
}
}
}
v___jp_627_:
{
lean_object* v_pivot_629_; lean_object* v___x_630_; lean_object* v_fst_631_; lean_object* v_snd_632_; uint8_t v___x_633_; 
v_pivot_629_ = lean_array_fget(v___y_628_, v_hi_626_);
lean_inc_n(v_lo_625_, 2);
v___x_630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_626_, v_pivot_629_, v___y_628_, v_lo_625_, v_lo_625_);
lean_dec(v_pivot_629_);
v_fst_631_ = lean_ctor_get(v___x_630_, 0);
lean_inc(v_fst_631_);
v_snd_632_ = lean_ctor_get(v___x_630_, 1);
lean_inc(v_snd_632_);
lean_dec_ref(v___x_630_);
v___x_633_ = lean_nat_dec_le(v_hi_626_, v_fst_631_);
if (v___x_633_ == 0)
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_623_, v_snd_632_, v_lo_625_, v_fst_631_);
v___x_635_ = lean_unsigned_to_nat(1u);
v___x_636_ = lean_nat_add(v_fst_631_, v___x_635_);
lean_dec(v_fst_631_);
v_as_624_ = v___x_634_;
v_lo_625_ = v___x_636_;
goto _start;
}
else
{
lean_dec(v_fst_631_);
lean_dec(v_lo_625_);
return v_snd_632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_n_658_, lean_object* v_as_659_, lean_object* v_lo_660_, lean_object* v_hi_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_658_, v_as_659_, v_lo_660_, v_hi_661_);
lean_dec(v_hi_661_);
lean_dec(v_n_658_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_665_){
_start:
{
lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v_unexpected_698_; lean_object* v_expected_699_; lean_object* v___y_701_; lean_object* v___x_711_; uint8_t v___x_712_; 
v_unexpected_698_ = lean_ctor_get(v_e_665_, 1);
lean_inc_ref(v_unexpected_698_);
v_expected_699_ = lean_ctor_get(v_e_665_, 2);
lean_inc(v_expected_699_);
lean_dec_ref(v_e_665_);
v___x_711_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_712_ = lean_string_dec_eq(v_unexpected_698_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
v___x_713_ = lean_box(0);
v___x_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_714_, 0, v_unexpected_698_);
lean_ctor_set(v___x_714_, 1, v___x_713_);
v___y_701_ = v___x_714_;
goto v___jp_700_;
}
else
{
lean_object* v___x_715_; 
lean_dec_ref(v_unexpected_698_);
v___x_715_ = lean_box(0);
v___y_701_ = v___x_715_;
goto v___jp_700_;
}
v___jp_666_:
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_669_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_670_ = l_List_appendTR___redArg(v___y_667_, v___y_668_);
v___x_671_ = l_String_intercalate(v___x_669_, v___x_670_);
return v___x_671_;
}
v___jp_672_:
{
lean_object* v___x_676_; lean_object* v_expected_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_676_ = lean_array_to_list(v___y_675_);
v_expected_677_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_676_);
v___x_678_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_679_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_677_);
v___x_680_ = lean_string_append(v___x_678_, v___x_679_);
lean_dec_ref(v___x_679_);
v___x_681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_681_, 0, v___x_680_);
lean_ctor_set(v___x_681_, 1, v___y_674_);
v___y_667_ = v___y_673_;
v___y_668_ = v___x_681_;
goto v___jp_666_;
}
v___jp_682_:
{
lean_object* v___x_689_; 
v___x_689_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_687_, v___y_685_, v___y_683_, v___y_688_);
lean_dec(v___y_688_);
lean_dec(v___y_687_);
v___y_673_ = v___y_684_;
v___y_674_ = v___y_686_;
v___y_675_ = v___x_689_;
goto v___jp_672_;
}
v___jp_690_:
{
uint8_t v___x_697_; 
v___x_697_ = lean_nat_dec_le(v___y_696_, v___y_693_);
if (v___x_697_ == 0)
{
lean_dec(v___y_693_);
lean_inc(v___y_696_);
v___y_683_ = v___y_696_;
v___y_684_ = v___y_691_;
v___y_685_ = v___y_692_;
v___y_686_ = v___y_694_;
v___y_687_ = v___y_695_;
v___y_688_ = v___y_696_;
goto v___jp_682_;
}
else
{
v___y_683_ = v___y_696_;
v___y_684_ = v___y_691_;
v___y_685_ = v___y_692_;
v___y_686_ = v___y_694_;
v___y_687_ = v___y_695_;
v___y_688_ = v___y_693_;
goto v___jp_682_;
}
}
v___jp_700_:
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_box(0);
v___x_703_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_699_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_704_ = lean_array_mk(v_expected_699_);
v___x_705_ = lean_array_get_size(v___x_704_);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_nat_dec_eq(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v___x_708_ = lean_unsigned_to_nat(1u);
v___x_709_ = lean_nat_sub(v___x_705_, v___x_708_);
v___x_710_ = lean_nat_dec_le(v___x_706_, v___x_709_);
if (v___x_710_ == 0)
{
lean_inc(v___x_709_);
v___y_691_ = v___y_701_;
v___y_692_ = v___x_704_;
v___y_693_ = v___x_709_;
v___y_694_ = v___x_702_;
v___y_695_ = v___x_705_;
v___y_696_ = v___x_709_;
goto v___jp_690_;
}
else
{
v___y_691_ = v___y_701_;
v___y_692_ = v___x_704_;
v___y_693_ = v___x_709_;
v___y_694_ = v___x_702_;
v___y_695_ = v___x_705_;
v___y_696_ = v___x_706_;
goto v___jp_690_;
}
}
else
{
v___y_673_ = v___y_701_;
v___y_674_ = v___x_702_;
v___y_675_ = v___x_704_;
goto v___jp_672_;
}
}
else
{
lean_dec(v_expected_699_);
v___y_667_ = v___y_701_;
v___y_668_ = v___x_702_;
goto v___jp_666_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_716_, lean_object* v_as_717_, lean_object* v_lo_718_, lean_object* v_hi_719_, lean_object* v_w_720_, lean_object* v_hlo_721_, lean_object* v_hhi_722_){
_start:
{
lean_object* v___x_723_; 
v___x_723_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_716_, v_as_717_, v_lo_718_, v_hi_719_);
return v___x_723_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_724_, lean_object* v_as_725_, lean_object* v_lo_726_, lean_object* v_hi_727_, lean_object* v_w_728_, lean_object* v_hlo_729_, lean_object* v_hhi_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_724_, v_as_725_, v_lo_726_, v_hi_727_, v_w_728_, v_hlo_729_, v_hhi_730_);
lean_dec(v_hi_727_);
lean_dec(v_n_724_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object* v_n_732_, lean_object* v_lo_733_, lean_object* v_hi_734_, lean_object* v_hhi_735_, lean_object* v_pivot_736_, lean_object* v_as_737_, lean_object* v_i_738_, lean_object* v_k_739_, lean_object* v_ilo_740_, lean_object* v_ik_741_, lean_object* v_w_742_){
_start:
{
lean_object* v___x_743_; 
v___x_743_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_734_, v_pivot_736_, v_as_737_, v_i_738_, v_k_739_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object* v_n_744_, lean_object* v_lo_745_, lean_object* v_hi_746_, lean_object* v_hhi_747_, lean_object* v_pivot_748_, lean_object* v_as_749_, lean_object* v_i_750_, lean_object* v_k_751_, lean_object* v_ilo_752_, lean_object* v_ik_753_, lean_object* v_w_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_744_, v_lo_745_, v_hi_746_, v_hhi_747_, v_pivot_748_, v_as_749_, v_i_750_, v_k_751_, v_ilo_752_, v_ik_753_, v_w_754_);
lean_dec_ref(v_pivot_748_);
lean_dec(v_hi_746_);
lean_dec(v_lo_745_);
lean_dec(v_n_744_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_758_, lean_object* v_e_u2082_759_){
_start:
{
lean_object* v_unexpectedTk_760_; lean_object* v_unexpected_761_; lean_object* v_expected_762_; lean_object* v___y_764_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_unexpectedTk_760_ = lean_ctor_get(v_e_u2082_759_, 0);
lean_inc(v_unexpectedTk_760_);
v_unexpected_761_ = lean_ctor_get(v_e_u2082_759_, 1);
lean_inc_ref(v_unexpected_761_);
v_expected_762_ = lean_ctor_get(v_e_u2082_759_, 2);
lean_inc(v_expected_762_);
lean_dec_ref(v_e_u2082_759_);
v___x_776_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_777_ = lean_string_dec_eq(v_unexpected_761_, v___x_776_);
if (v___x_777_ == 0)
{
v___y_764_ = v_unexpected_761_;
goto v___jp_763_;
}
else
{
lean_object* v_unexpected_778_; 
lean_dec_ref(v_unexpected_761_);
v_unexpected_778_ = lean_ctor_get(v_e_u2081_758_, 1);
lean_inc_ref(v_unexpected_778_);
v___y_764_ = v_unexpected_778_;
goto v___jp_763_;
}
v___jp_763_:
{
lean_object* v_expected_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_773_; 
v_expected_765_ = lean_ctor_get(v_e_u2081_758_, 2);
v_isSharedCheck_773_ = !lean_is_exclusive(v_e_u2081_758_);
if (v_isSharedCheck_773_ == 0)
{
lean_object* v_unused_774_; lean_object* v_unused_775_; 
v_unused_774_ = lean_ctor_get(v_e_u2081_758_, 1);
lean_dec(v_unused_774_);
v_unused_775_ = lean_ctor_get(v_e_u2081_758_, 0);
lean_dec(v_unused_775_);
v___x_767_ = v_e_u2081_758_;
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_expected_765_);
lean_dec(v_e_u2081_758_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_773_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_769_; lean_object* v___x_771_; 
v___x_769_ = l_List_appendTR___redArg(v_expected_765_, v_expected_762_);
if (v_isShared_768_ == 0)
{
lean_ctor_set(v___x_767_, 2, v___x_769_);
lean_ctor_set(v___x_767_, 1, v___y_764_);
lean_ctor_set(v___x_767_, 0, v_unexpectedTk_760_);
v___x_771_ = v___x_767_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_unexpectedTk_760_);
lean_ctor_set(v_reuseFailAlloc_772_, 1, v___y_764_);
lean_ctor_set(v_reuseFailAlloc_772_, 2, v___x_769_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
lean_object* v_toCacheableParserContext_781_; lean_object* v_parserName_782_; lean_object* v_pos_783_; lean_object* v_toCacheableParserContext_784_; lean_object* v_parserName_785_; lean_object* v_pos_786_; uint8_t v___x_787_; 
v_toCacheableParserContext_781_ = lean_ctor_get(v_x_779_, 0);
v_parserName_782_ = lean_ctor_get(v_x_779_, 1);
v_pos_783_ = lean_ctor_get(v_x_779_, 2);
v_toCacheableParserContext_784_ = lean_ctor_get(v_x_780_, 0);
v_parserName_785_ = lean_ctor_get(v_x_780_, 1);
v_pos_786_ = lean_ctor_get(v_x_780_, 2);
v___x_787_ = l_Lean_Parser_instBEqCacheableParserContext_beq(v_toCacheableParserContext_781_, v_toCacheableParserContext_784_);
if (v___x_787_ == 0)
{
return v___x_787_;
}
else
{
uint8_t v___x_788_; 
v___x_788_ = lean_name_eq(v_parserName_782_, v_parserName_785_);
if (v___x_788_ == 0)
{
return v___x_788_;
}
else
{
uint8_t v___x_789_; 
v___x_789_ = lean_nat_dec_eq(v_pos_783_, v_pos_786_);
return v___x_789_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
uint8_t v_res_792_; lean_object* v_r_793_; 
v_res_792_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_790_, v_x_791_);
lean_dec_ref(v_x_791_);
lean_dec_ref(v_x_790_);
v_r_793_ = lean_box(v_res_792_);
return v_r_793_;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* v_k_796_){
_start:
{
lean_object* v_parserName_797_; lean_object* v_pos_798_; uint64_t v___x_799_; 
v_parserName_797_ = lean_ctor_get(v_k_796_, 1);
v_pos_798_ = lean_ctor_get(v_k_796_, 2);
v___x_799_ = l_String_instHashableRaw_hash(v_pos_798_);
if (lean_obj_tag(v_parserName_797_) == 0)
{
uint64_t v___x_800_; uint64_t v___x_801_; 
v___x_800_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_801_ = lean_uint64_mix_hash(v___x_799_, v___x_800_);
return v___x_801_;
}
else
{
uint64_t v_hash_802_; uint64_t v___x_803_; 
v_hash_802_ = lean_ctor_get_uint64(v_parserName_797_, sizeof(void*)*2);
v___x_803_ = lean_uint64_mix_hash(v___x_799_, v_hash_802_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* v_k_804_){
_start:
{
uint64_t v_res_805_; lean_object* v_r_806_; 
v_res_805_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_804_);
lean_dec_ref(v_k_804_);
v_r_806_ = lean_box_uint64(v_res_805_);
return v_r_806_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0(void){
_start:
{
uint32_t v___x_809_; lean_object* v___x_810_; 
v___x_809_ = 32;
v___x_810_ = l_Char_utf8Size(v___x_809_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v___x_811_ = lean_box(0);
v___x_812_ = lean_unsigned_to_nat(16u);
v___x_813_ = lean_mk_array(v___x_812_, v___x_811_);
return v___x_813_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__2(void){
_start:
{
lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_814_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_816_, 0, v___x_815_);
lean_ctor_set(v___x_816_, 1, v___x_814_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_817_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_818_ = lean_string_utf8_byte_size(v_input_817_);
v___x_819_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_820_ = lean_nat_add(v___x_818_, v___x_819_);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_box(0);
v___x_823_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_823_, 0, v___x_820_);
lean_ctor_set(v___x_823_, 1, v___x_821_);
lean_ctor_set(v___x_823_, 2, v___x_822_);
v___x_824_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_823_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Lean_Parser_initCacheForInput(v_input_826_);
lean_dec_ref(v_input_826_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_828_){
_start:
{
lean_object* v_raw_829_; lean_object* v_drop_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v_raw_829_ = lean_ctor_get(v_stack_828_, 0);
lean_inc_ref(v_raw_829_);
v_drop_830_ = lean_ctor_get(v_stack_828_, 1);
lean_inc(v_drop_830_);
lean_dec_ref(v_stack_828_);
v___x_831_ = lean_array_get_size(v_raw_829_);
v___x_832_ = l_Array_toSubarray___redArg(v_raw_829_, v_drop_830_, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_839_){
_start:
{
lean_object* v_raw_840_; lean_object* v_drop_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_raw_840_ = lean_ctor_get(v_stack_839_, 0);
v_drop_841_ = lean_ctor_get(v_stack_839_, 1);
v___x_842_ = lean_array_get_size(v_raw_840_);
v___x_843_ = lean_nat_sub(v___x_842_, v_drop_841_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Parser_SyntaxStack_size(v_stack_844_);
lean_dec_ref(v_stack_844_);
return v_res_845_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_847_ = l_Lean_Parser_SyntaxStack_size(v_stack_846_);
v___x_848_ = lean_unsigned_to_nat(0u);
v___x_849_ = lean_nat_dec_eq(v___x_847_, v___x_848_);
lean_dec(v___x_847_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_850_){
_start:
{
uint8_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_850_);
lean_dec_ref(v_stack_850_);
v_r_852_ = lean_box(v_res_851_);
return v_r_852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_853_, lean_object* v_n_854_){
_start:
{
lean_object* v_raw_855_; lean_object* v_drop_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_865_; 
v_raw_855_ = lean_ctor_get(v_stack_853_, 0);
v_drop_856_ = lean_ctor_get(v_stack_853_, 1);
v_isSharedCheck_865_ = !lean_is_exclusive(v_stack_853_);
if (v_isSharedCheck_865_ == 0)
{
v___x_858_ = v_stack_853_;
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_drop_856_);
lean_inc(v_raw_855_);
lean_dec(v_stack_853_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_865_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_860_ = lean_nat_add(v_drop_856_, v_n_854_);
v___x_861_ = l_Array_shrink___redArg(v_raw_855_, v___x_860_);
lean_dec(v___x_860_);
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_drop_856_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_866_, lean_object* v_n_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_866_, v_n_867_);
lean_dec(v_n_867_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_raw_871_; lean_object* v_drop_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_880_; 
v_raw_871_ = lean_ctor_get(v_stack_869_, 0);
v_drop_872_ = lean_ctor_get(v_stack_869_, 1);
v_isSharedCheck_880_ = !lean_is_exclusive(v_stack_869_);
if (v_isSharedCheck_880_ == 0)
{
v___x_874_ = v_stack_869_;
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_drop_872_);
lean_inc(v_raw_871_);
lean_dec(v_stack_869_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_880_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; lean_object* v___x_878_; 
v___x_876_ = lean_array_push(v_raw_871_, v_a_870_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 0, v___x_876_);
v___x_878_ = v___x_874_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_876_);
lean_ctor_set(v_reuseFailAlloc_879_, 1, v_drop_872_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_881_){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v___x_882_ = lean_unsigned_to_nat(0u);
v___x_883_ = l_Lean_Parser_SyntaxStack_size(v_stack_881_);
v___x_884_ = lean_nat_dec_lt(v___x_882_, v___x_883_);
lean_dec(v___x_883_);
if (v___x_884_ == 0)
{
return v_stack_881_;
}
else
{
lean_object* v_raw_885_; lean_object* v_drop_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_894_; 
v_raw_885_ = lean_ctor_get(v_stack_881_, 0);
v_drop_886_ = lean_ctor_get(v_stack_881_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_stack_881_);
if (v_isSharedCheck_894_ == 0)
{
v___x_888_ = v_stack_881_;
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_drop_886_);
lean_inc(v_raw_885_);
lean_dec(v_stack_881_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_894_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_890_; lean_object* v___x_892_; 
v___x_890_ = lean_array_pop(v_raw_885_);
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
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_895_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = lean_box(0);
v___x_897_ = lean_panic_fn_borrowed(v___x_896_, v_msg_895_);
return v___x_897_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_901_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_902_ = lean_unsigned_to_nat(4u);
v___x_903_ = lean_unsigned_to_nat(305u);
v___x_904_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_905_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_906_ = l_mkPanicMessageWithDecl(v___x_905_, v___x_904_, v___x_903_, v___x_902_, v___x_901_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_907_){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; uint8_t v___x_910_; 
v___x_908_ = lean_unsigned_to_nat(0u);
v___x_909_ = l_Lean_Parser_SyntaxStack_size(v_stack_907_);
v___x_910_ = lean_nat_dec_lt(v___x_908_, v___x_909_);
lean_dec(v___x_909_);
if (v___x_910_ == 0)
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_912_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_911_);
return v___x_912_;
}
else
{
lean_object* v_raw_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v_raw_913_ = lean_ctor_get(v_stack_907_, 0);
v___x_914_ = lean_box(0);
v___x_915_ = lean_array_get_size(v_raw_913_);
v___x_916_ = lean_unsigned_to_nat(1u);
v___x_917_ = lean_nat_sub(v___x_915_, v___x_916_);
v___x_918_ = lean_array_get_borrowed(v___x_914_, v_raw_913_, v___x_917_);
lean_dec(v___x_917_);
lean_inc(v___x_918_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l_Lean_Parser_SyntaxStack_back(v_stack_919_);
lean_dec_ref(v_stack_919_);
return v_res_920_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_923_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_924_ = lean_unsigned_to_nat(4u);
v___x_925_ = lean_unsigned_to_nat(311u);
v___x_926_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_927_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_928_ = l_mkPanicMessageWithDecl(v___x_927_, v___x_926_, v___x_925_, v___x_924_, v___x_923_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_929_, lean_object* v_i_930_){
_start:
{
lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_931_ = l_Lean_Parser_SyntaxStack_size(v_stack_929_);
v___x_932_ = lean_nat_dec_lt(v_i_930_, v___x_931_);
lean_dec(v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_934_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_933_);
return v___x_934_;
}
else
{
lean_object* v_raw_935_; lean_object* v_drop_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; 
v_raw_935_ = lean_ctor_get(v_stack_929_, 0);
v_drop_936_ = lean_ctor_get(v_stack_929_, 1);
v___x_937_ = lean_box(0);
v___x_938_ = lean_nat_add(v_drop_936_, v_i_930_);
v___x_939_ = lean_array_get_borrowed(v___x_937_, v_raw_935_, v___x_938_);
lean_dec(v___x_938_);
lean_inc(v___x_939_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_940_, lean_object* v_i_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_940_, v_i_941_);
lean_dec(v_i_941_);
lean_dec_ref(v_stack_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_943_, lean_object* v_start_944_, lean_object* v_stop_945_){
_start:
{
lean_object* v_raw_946_; lean_object* v_drop_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
v_raw_946_ = lean_ctor_get(v_stack_943_, 0);
v_drop_947_ = lean_ctor_get(v_stack_943_, 1);
v___x_948_ = lean_nat_add(v_drop_947_, v_start_944_);
v___x_949_ = lean_nat_add(v_drop_947_, v_stop_945_);
v___x_950_ = l_Array_extract___redArg(v_raw_946_, v___x_948_, v___x_949_);
return v___x_950_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_951_, lean_object* v_start_952_, lean_object* v_stop_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Parser_SyntaxStack_extract(v_stack_951_, v_start_952_, v_stop_953_);
lean_dec(v_stop_953_);
lean_dec(v_start_952_);
lean_dec_ref(v_stack_951_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_955_, lean_object* v_stxs_956_){
_start:
{
lean_object* v_raw_957_; lean_object* v_drop_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_966_; 
v_raw_957_ = lean_ctor_get(v_stack_955_, 0);
v_drop_958_ = lean_ctor_get(v_stack_955_, 1);
v_isSharedCheck_966_ = !lean_is_exclusive(v_stack_955_);
if (v_isSharedCheck_966_ == 0)
{
v___x_960_ = v_stack_955_;
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_drop_958_);
lean_inc(v_raw_957_);
lean_dec(v_stack_955_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_966_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_962_; lean_object* v___x_964_; 
v___x_962_ = l_Array_append___redArg(v_raw_957_, v_stxs_956_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_962_);
v___x_964_ = v___x_960_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
lean_ctor_set(v_reuseFailAlloc_965_, 1, v_drop_958_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_967_, lean_object* v_stxs_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_967_, v_stxs_968_);
lean_dec_ref(v_stxs_968_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_970_, lean_object* v_stxs_971_){
_start:
{
lean_object* v_raw_972_; lean_object* v_drop_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_981_; 
v_raw_972_ = lean_ctor_get(v_stack_970_, 0);
v_drop_973_ = lean_ctor_get(v_stack_970_, 1);
v_isSharedCheck_981_ = !lean_is_exclusive(v_stack_970_);
if (v_isSharedCheck_981_ == 0)
{
v___x_975_ = v_stack_970_;
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_drop_973_);
lean_inc(v_raw_972_);
lean_dec(v_stack_970_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_981_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_979_; 
v___x_977_ = l_Array_append___redArg(v_raw_972_, v_stxs_971_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_977_);
v___x_979_ = v___x_975_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v___x_977_);
lean_ctor_set(v_reuseFailAlloc_980_, 1, v_drop_973_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_982_, lean_object* v_stxs_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_982_, v_stxs_983_);
lean_dec_ref(v_stxs_983_);
return v_res_984_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_987_){
_start:
{
lean_object* v_errorMsg_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_errorMsg_988_ = lean_ctor_get(v_s_987_, 4);
lean_inc(v_errorMsg_988_);
lean_dec_ref(v_s_987_);
v___x_989_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_990_ = lean_box(0);
v___x_991_ = l_Option_instBEq_beq___redArg(v___x_989_, v_errorMsg_988_, v___x_990_);
if (v___x_991_ == 0)
{
uint8_t v___x_992_; 
v___x_992_ = 1;
return v___x_992_;
}
else
{
uint8_t v___x_993_; 
v___x_993_ = 0;
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_994_){
_start:
{
uint8_t v_res_995_; lean_object* v_r_996_; 
v_res_995_ = l_Lean_Parser_ParserState_hasError(v_s_994_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_997_){
_start:
{
lean_object* v_stxStack_998_; lean_object* v___x_999_; 
v_stxStack_998_ = lean_ctor_get(v_s_997_, 0);
v___x_999_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_998_);
return v___x_999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_Parser_ParserState_stackSize(v_s_1000_);
lean_dec_ref(v_s_1000_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_1002_, lean_object* v_iniStackSz_1003_, lean_object* v_iniPos_1004_){
_start:
{
lean_object* v_stxStack_1005_; lean_object* v_lhsPrec_1006_; lean_object* v_cache_1007_; lean_object* v_recoveredErrors_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1017_; 
v_stxStack_1005_ = lean_ctor_get(v_s_1002_, 0);
v_lhsPrec_1006_ = lean_ctor_get(v_s_1002_, 1);
v_cache_1007_ = lean_ctor_get(v_s_1002_, 3);
v_recoveredErrors_1008_ = lean_ctor_get(v_s_1002_, 5);
v_isSharedCheck_1017_ = !lean_is_exclusive(v_s_1002_);
if (v_isSharedCheck_1017_ == 0)
{
lean_object* v_unused_1018_; lean_object* v_unused_1019_; 
v_unused_1018_ = lean_ctor_get(v_s_1002_, 4);
lean_dec(v_unused_1018_);
v_unused_1019_ = lean_ctor_get(v_s_1002_, 2);
lean_dec(v_unused_1019_);
v___x_1010_ = v_s_1002_;
v_isShared_1011_ = v_isSharedCheck_1017_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_recoveredErrors_1008_);
lean_inc(v_cache_1007_);
lean_inc(v_lhsPrec_1006_);
lean_inc(v_stxStack_1005_);
lean_dec(v_s_1002_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1017_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1012_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1005_, v_iniStackSz_1003_);
v___x_1013_ = lean_box(0);
if (v_isShared_1011_ == 0)
{
lean_ctor_set(v___x_1010_, 4, v___x_1013_);
lean_ctor_set(v___x_1010_, 2, v_iniPos_1004_);
lean_ctor_set(v___x_1010_, 0, v___x_1012_);
v___x_1015_ = v___x_1010_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1016_, 1, v_lhsPrec_1006_);
lean_ctor_set(v_reuseFailAlloc_1016_, 2, v_iniPos_1004_);
lean_ctor_set(v_reuseFailAlloc_1016_, 3, v_cache_1007_);
lean_ctor_set(v_reuseFailAlloc_1016_, 4, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1016_, 5, v_recoveredErrors_1008_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_1020_, lean_object* v_iniStackSz_1021_, lean_object* v_iniPos_1022_){
_start:
{
lean_object* v_res_1023_; 
v_res_1023_ = l_Lean_Parser_ParserState_restore(v_s_1020_, v_iniStackSz_1021_, v_iniPos_1022_);
lean_dec(v_iniStackSz_1021_);
return v_res_1023_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_1024_, lean_object* v_pos_1025_){
_start:
{
lean_object* v_stxStack_1026_; lean_object* v_lhsPrec_1027_; lean_object* v_cache_1028_; lean_object* v_errorMsg_1029_; lean_object* v_recoveredErrors_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
v_stxStack_1026_ = lean_ctor_get(v_s_1024_, 0);
v_lhsPrec_1027_ = lean_ctor_get(v_s_1024_, 1);
v_cache_1028_ = lean_ctor_get(v_s_1024_, 3);
v_errorMsg_1029_ = lean_ctor_get(v_s_1024_, 4);
v_recoveredErrors_1030_ = lean_ctor_get(v_s_1024_, 5);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_s_1024_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_s_1024_, 2);
lean_dec(v_unused_1038_);
v___x_1032_ = v_s_1024_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_recoveredErrors_1030_);
lean_inc(v_errorMsg_1029_);
lean_inc(v_cache_1028_);
lean_inc(v_lhsPrec_1027_);
lean_inc(v_stxStack_1026_);
lean_dec(v_s_1024_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 2, v_pos_1025_);
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_stxStack_1026_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_lhsPrec_1027_);
lean_ctor_set(v_reuseFailAlloc_1036_, 2, v_pos_1025_);
lean_ctor_set(v_reuseFailAlloc_1036_, 3, v_cache_1028_);
lean_ctor_set(v_reuseFailAlloc_1036_, 4, v_errorMsg_1029_);
lean_ctor_set(v_reuseFailAlloc_1036_, 5, v_recoveredErrors_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_1039_, lean_object* v_cache_1040_){
_start:
{
lean_object* v_stxStack_1041_; lean_object* v_lhsPrec_1042_; lean_object* v_pos_1043_; lean_object* v_errorMsg_1044_; lean_object* v_recoveredErrors_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
v_stxStack_1041_ = lean_ctor_get(v_s_1039_, 0);
v_lhsPrec_1042_ = lean_ctor_get(v_s_1039_, 1);
v_pos_1043_ = lean_ctor_get(v_s_1039_, 2);
v_errorMsg_1044_ = lean_ctor_get(v_s_1039_, 4);
v_recoveredErrors_1045_ = lean_ctor_get(v_s_1039_, 5);
v_isSharedCheck_1052_ = !lean_is_exclusive(v_s_1039_);
if (v_isSharedCheck_1052_ == 0)
{
lean_object* v_unused_1053_; 
v_unused_1053_ = lean_ctor_get(v_s_1039_, 3);
lean_dec(v_unused_1053_);
v___x_1047_ = v_s_1039_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_recoveredErrors_1045_);
lean_inc(v_errorMsg_1044_);
lean_inc(v_pos_1043_);
lean_inc(v_lhsPrec_1042_);
lean_inc(v_stxStack_1041_);
lean_dec(v_s_1039_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 3, v_cache_1040_);
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_stxStack_1041_);
lean_ctor_set(v_reuseFailAlloc_1051_, 1, v_lhsPrec_1042_);
lean_ctor_set(v_reuseFailAlloc_1051_, 2, v_pos_1043_);
lean_ctor_set(v_reuseFailAlloc_1051_, 3, v_cache_1040_);
lean_ctor_set(v_reuseFailAlloc_1051_, 4, v_errorMsg_1044_);
lean_ctor_set(v_reuseFailAlloc_1051_, 5, v_recoveredErrors_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_1054_, lean_object* v_n_1055_){
_start:
{
lean_object* v_stxStack_1056_; lean_object* v_lhsPrec_1057_; lean_object* v_pos_1058_; lean_object* v_cache_1059_; lean_object* v_errorMsg_1060_; lean_object* v_recoveredErrors_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1069_; 
v_stxStack_1056_ = lean_ctor_get(v_s_1054_, 0);
v_lhsPrec_1057_ = lean_ctor_get(v_s_1054_, 1);
v_pos_1058_ = lean_ctor_get(v_s_1054_, 2);
v_cache_1059_ = lean_ctor_get(v_s_1054_, 3);
v_errorMsg_1060_ = lean_ctor_get(v_s_1054_, 4);
v_recoveredErrors_1061_ = lean_ctor_get(v_s_1054_, 5);
v_isSharedCheck_1069_ = !lean_is_exclusive(v_s_1054_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1063_ = v_s_1054_;
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_recoveredErrors_1061_);
lean_inc(v_errorMsg_1060_);
lean_inc(v_cache_1059_);
lean_inc(v_pos_1058_);
lean_inc(v_lhsPrec_1057_);
lean_inc(v_stxStack_1056_);
lean_dec(v_s_1054_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1069_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1067_; 
v___x_1065_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1056_, v_n_1055_);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1067_ = v___x_1063_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1068_, 1, v_lhsPrec_1057_);
lean_ctor_set(v_reuseFailAlloc_1068_, 2, v_pos_1058_);
lean_ctor_set(v_reuseFailAlloc_1068_, 3, v_cache_1059_);
lean_ctor_set(v_reuseFailAlloc_1068_, 4, v_errorMsg_1060_);
lean_ctor_set(v_reuseFailAlloc_1068_, 5, v_recoveredErrors_1061_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1070_){
_start:
{
lean_object* v_stxStack_1071_; lean_object* v_lhsPrec_1072_; lean_object* v_pos_1073_; lean_object* v_cache_1074_; lean_object* v_errorMsg_1075_; lean_object* v_recoveredErrors_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1084_; 
v_stxStack_1071_ = lean_ctor_get(v_s_1070_, 0);
v_lhsPrec_1072_ = lean_ctor_get(v_s_1070_, 1);
v_pos_1073_ = lean_ctor_get(v_s_1070_, 2);
v_cache_1074_ = lean_ctor_get(v_s_1070_, 3);
v_errorMsg_1075_ = lean_ctor_get(v_s_1070_, 4);
v_recoveredErrors_1076_ = lean_ctor_get(v_s_1070_, 5);
v_isSharedCheck_1084_ = !lean_is_exclusive(v_s_1070_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1078_ = v_s_1070_;
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_recoveredErrors_1076_);
lean_inc(v_errorMsg_1075_);
lean_inc(v_cache_1074_);
lean_inc(v_pos_1073_);
lean_inc(v_lhsPrec_1072_);
lean_inc(v_stxStack_1071_);
lean_dec(v_s_1070_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1084_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1080_; lean_object* v___x_1082_; 
v___x_1080_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1071_);
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 0, v___x_1080_);
v___x_1082_ = v___x_1078_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
lean_ctor_set(v_reuseFailAlloc_1083_, 1, v_lhsPrec_1072_);
lean_ctor_set(v_reuseFailAlloc_1083_, 2, v_pos_1073_);
lean_ctor_set(v_reuseFailAlloc_1083_, 3, v_cache_1074_);
lean_ctor_set(v_reuseFailAlloc_1083_, 4, v_errorMsg_1075_);
lean_ctor_set(v_reuseFailAlloc_1083_, 5, v_recoveredErrors_1076_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1085_, lean_object* v_iniStackSz_1086_){
_start:
{
lean_object* v_stxStack_1087_; lean_object* v_lhsPrec_1088_; lean_object* v_pos_1089_; lean_object* v_cache_1090_; lean_object* v_errorMsg_1091_; lean_object* v_recoveredErrors_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1100_; 
v_stxStack_1087_ = lean_ctor_get(v_s_1085_, 0);
v_lhsPrec_1088_ = lean_ctor_get(v_s_1085_, 1);
v_pos_1089_ = lean_ctor_get(v_s_1085_, 2);
v_cache_1090_ = lean_ctor_get(v_s_1085_, 3);
v_errorMsg_1091_ = lean_ctor_get(v_s_1085_, 4);
v_recoveredErrors_1092_ = lean_ctor_get(v_s_1085_, 5);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_s_1085_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1094_ = v_s_1085_;
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_recoveredErrors_1092_);
lean_inc(v_errorMsg_1091_);
lean_inc(v_cache_1090_);
lean_inc(v_pos_1089_);
lean_inc(v_lhsPrec_1088_);
lean_inc(v_stxStack_1087_);
lean_dec(v_s_1085_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1100_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1096_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1087_, v_iniStackSz_1086_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 0, v___x_1096_);
v___x_1098_ = v___x_1094_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v_lhsPrec_1088_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v_pos_1089_);
lean_ctor_set(v_reuseFailAlloc_1099_, 3, v_cache_1090_);
lean_ctor_set(v_reuseFailAlloc_1099_, 4, v_errorMsg_1091_);
lean_ctor_set(v_reuseFailAlloc_1099_, 5, v_recoveredErrors_1092_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1101_, lean_object* v_iniStackSz_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1101_, v_iniStackSz_1102_);
lean_dec(v_iniStackSz_1102_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1104_, lean_object* v_c_1105_, lean_object* v_pos_1106_){
_start:
{
lean_object* v_toInputContext_1107_; lean_object* v_stxStack_1108_; lean_object* v_lhsPrec_1109_; lean_object* v_cache_1110_; lean_object* v_errorMsg_1111_; lean_object* v_recoveredErrors_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1121_; 
v_toInputContext_1107_ = lean_ctor_get(v_c_1105_, 0);
v_stxStack_1108_ = lean_ctor_get(v_s_1104_, 0);
v_lhsPrec_1109_ = lean_ctor_get(v_s_1104_, 1);
v_cache_1110_ = lean_ctor_get(v_s_1104_, 3);
v_errorMsg_1111_ = lean_ctor_get(v_s_1104_, 4);
v_recoveredErrors_1112_ = lean_ctor_get(v_s_1104_, 5);
v_isSharedCheck_1121_ = !lean_is_exclusive(v_s_1104_);
if (v_isSharedCheck_1121_ == 0)
{
lean_object* v_unused_1122_; 
v_unused_1122_ = lean_ctor_get(v_s_1104_, 2);
lean_dec(v_unused_1122_);
v___x_1114_ = v_s_1104_;
v_isShared_1115_ = v_isSharedCheck_1121_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_recoveredErrors_1112_);
lean_inc(v_errorMsg_1111_);
lean_inc(v_cache_1110_);
lean_inc(v_lhsPrec_1109_);
lean_inc(v_stxStack_1108_);
lean_dec(v_s_1104_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1121_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_inputString_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v_inputString_1116_ = lean_ctor_get(v_toInputContext_1107_, 0);
v___x_1117_ = lean_string_utf8_next(v_inputString_1116_, v_pos_1106_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 2, v___x_1117_);
v___x_1119_ = v___x_1114_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_stxStack_1108_);
lean_ctor_set(v_reuseFailAlloc_1120_, 1, v_lhsPrec_1109_);
lean_ctor_set(v_reuseFailAlloc_1120_, 2, v___x_1117_);
lean_ctor_set(v_reuseFailAlloc_1120_, 3, v_cache_1110_);
lean_ctor_set(v_reuseFailAlloc_1120_, 4, v_errorMsg_1111_);
lean_ctor_set(v_reuseFailAlloc_1120_, 5, v_recoveredErrors_1112_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1123_, lean_object* v_c_1124_, lean_object* v_pos_1125_){
_start:
{
lean_object* v_res_1126_; 
v_res_1126_ = l_Lean_Parser_ParserState_next(v_s_1123_, v_c_1124_, v_pos_1125_);
lean_dec(v_pos_1125_);
lean_dec_ref(v_c_1124_);
return v_res_1126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1127_, lean_object* v_c_1128_, lean_object* v_pos_1129_){
_start:
{
lean_object* v_toInputContext_1130_; lean_object* v_stxStack_1131_; lean_object* v_lhsPrec_1132_; lean_object* v_cache_1133_; lean_object* v_errorMsg_1134_; lean_object* v_recoveredErrors_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1144_; 
v_toInputContext_1130_ = lean_ctor_get(v_c_1128_, 0);
v_stxStack_1131_ = lean_ctor_get(v_s_1127_, 0);
v_lhsPrec_1132_ = lean_ctor_get(v_s_1127_, 1);
v_cache_1133_ = lean_ctor_get(v_s_1127_, 3);
v_errorMsg_1134_ = lean_ctor_get(v_s_1127_, 4);
v_recoveredErrors_1135_ = lean_ctor_get(v_s_1127_, 5);
v_isSharedCheck_1144_ = !lean_is_exclusive(v_s_1127_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v_s_1127_, 2);
lean_dec(v_unused_1145_);
v___x_1137_ = v_s_1127_;
v_isShared_1138_ = v_isSharedCheck_1144_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_recoveredErrors_1135_);
lean_inc(v_errorMsg_1134_);
lean_inc(v_cache_1133_);
lean_inc(v_lhsPrec_1132_);
lean_inc(v_stxStack_1131_);
lean_dec(v_s_1127_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1144_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v_inputString_1139_; lean_object* v___x_1140_; lean_object* v___x_1142_; 
v_inputString_1139_ = lean_ctor_get(v_toInputContext_1130_, 0);
v___x_1140_ = lean_string_utf8_next_fast(v_inputString_1139_, v_pos_1129_);
if (v_isShared_1138_ == 0)
{
lean_ctor_set(v___x_1137_, 2, v___x_1140_);
v___x_1142_ = v___x_1137_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_stxStack_1131_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_lhsPrec_1132_);
lean_ctor_set(v_reuseFailAlloc_1143_, 2, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1143_, 3, v_cache_1133_);
lean_ctor_set(v_reuseFailAlloc_1143_, 4, v_errorMsg_1134_);
lean_ctor_set(v_reuseFailAlloc_1143_, 5, v_recoveredErrors_1135_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1146_, lean_object* v_c_1147_, lean_object* v_pos_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1146_, v_c_1147_, v_pos_1148_);
lean_dec(v_pos_1148_);
lean_dec_ref(v_c_1147_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1150_, lean_object* v_c_1151_, lean_object* v_pos_1152_, lean_object* v_h_1153_){
_start:
{
lean_object* v___x_1154_; 
v___x_1154_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1150_, v_c_1151_, v_pos_1152_);
return v___x_1154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1155_, lean_object* v_c_1156_, lean_object* v_pos_1157_, lean_object* v_h_1158_){
_start:
{
lean_object* v_res_1159_; 
v_res_1159_ = l_Lean_Parser_ParserState_next_x27(v_s_1155_, v_c_1156_, v_pos_1157_, v_h_1158_);
lean_dec(v_pos_1157_);
lean_dec_ref(v_c_1156_);
return v_res_1159_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1160_, lean_object* v_x_1161_){
_start:
{
if (lean_obj_tag(v_x_1160_) == 0)
{
if (lean_obj_tag(v_x_1161_) == 0)
{
uint8_t v___x_1162_; 
v___x_1162_ = 1;
return v___x_1162_;
}
else
{
uint8_t v___x_1163_; 
lean_dec_ref(v_x_1161_);
v___x_1163_ = 0;
return v___x_1163_;
}
}
else
{
if (lean_obj_tag(v_x_1161_) == 0)
{
uint8_t v___x_1164_; 
lean_dec_ref(v_x_1160_);
v___x_1164_ = 0;
return v___x_1164_;
}
else
{
lean_object* v_val_1165_; lean_object* v_val_1166_; uint8_t v___x_1167_; 
v_val_1165_ = lean_ctor_get(v_x_1160_, 0);
lean_inc(v_val_1165_);
lean_dec_ref(v_x_1160_);
v_val_1166_ = lean_ctor_get(v_x_1161_, 0);
lean_inc(v_val_1166_);
lean_dec_ref(v_x_1161_);
v___x_1167_ = l_Lean_Parser_instBEqError_beq(v_val_1165_, v_val_1166_);
return v___x_1167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1168_, lean_object* v_x_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1168_, v_x_1169_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1172_, lean_object* v_k_1173_, lean_object* v_iniStackSz_1174_){
_start:
{
lean_object* v_stxStack_1175_; lean_object* v_lhsPrec_1176_; lean_object* v_pos_1177_; lean_object* v_cache_1178_; lean_object* v_errorMsg_1179_; lean_object* v_recoveredErrors_1180_; lean_object* v___x_1182_; uint8_t v_isShared_1183_; uint8_t v_isSharedCheck_1201_; 
v_stxStack_1175_ = lean_ctor_get(v_s_1172_, 0);
v_lhsPrec_1176_ = lean_ctor_get(v_s_1172_, 1);
v_pos_1177_ = lean_ctor_get(v_s_1172_, 2);
v_cache_1178_ = lean_ctor_get(v_s_1172_, 3);
v_errorMsg_1179_ = lean_ctor_get(v_s_1172_, 4);
v_recoveredErrors_1180_ = lean_ctor_get(v_s_1172_, 5);
v_isSharedCheck_1201_ = !lean_is_exclusive(v_s_1172_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1182_ = v_s_1172_;
v_isShared_1183_ = v_isSharedCheck_1201_;
goto v_resetjp_1181_;
}
else
{
lean_inc(v_recoveredErrors_1180_);
lean_inc(v_errorMsg_1179_);
lean_inc(v_cache_1178_);
lean_inc(v_pos_1177_);
lean_inc(v_lhsPrec_1176_);
lean_inc(v_stxStack_1175_);
lean_dec(v_s_1172_);
v___x_1182_ = lean_box(0);
v_isShared_1183_ = v_isSharedCheck_1201_;
goto v_resetjp_1181_;
}
v_resetjp_1181_:
{
lean_object* v___x_1194_; uint8_t v___x_1195_; 
v___x_1194_ = lean_box(0);
lean_inc(v_errorMsg_1179_);
v___x_1195_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1179_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1196_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1175_);
v___x_1197_ = lean_nat_dec_eq(v___x_1196_, v_iniStackSz_1174_);
lean_dec(v___x_1196_);
if (v___x_1197_ == 0)
{
goto v___jp_1184_;
}
else
{
lean_object* v___x_1198_; lean_object* v_stack_1199_; lean_object* v___x_1200_; 
lean_del_object(v___x_1182_);
lean_dec(v_k_1173_);
v___x_1198_ = lean_box(0);
v_stack_1199_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1175_, v___x_1198_);
v___x_1200_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1200_, 0, v_stack_1199_);
lean_ctor_set(v___x_1200_, 1, v_lhsPrec_1176_);
lean_ctor_set(v___x_1200_, 2, v_pos_1177_);
lean_ctor_set(v___x_1200_, 3, v_cache_1178_);
lean_ctor_set(v___x_1200_, 4, v_errorMsg_1179_);
lean_ctor_set(v___x_1200_, 5, v_recoveredErrors_1180_);
return v___x_1200_;
}
}
else
{
goto v___jp_1184_;
}
v___jp_1184_:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v_newNode_1188_; lean_object* v_stack_1189_; lean_object* v_stack_1190_; lean_object* v___x_1192_; 
v___x_1185_ = lean_box(2);
v___x_1186_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1175_);
v___x_1187_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1175_, v_iniStackSz_1174_, v___x_1186_);
lean_dec(v___x_1186_);
v_newNode_1188_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1188_, 0, v___x_1185_);
lean_ctor_set(v_newNode_1188_, 1, v_k_1173_);
lean_ctor_set(v_newNode_1188_, 2, v___x_1187_);
v_stack_1189_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1175_, v_iniStackSz_1174_);
v_stack_1190_ = l_Lean_Parser_SyntaxStack_push(v_stack_1189_, v_newNode_1188_);
if (v_isShared_1183_ == 0)
{
lean_ctor_set(v___x_1182_, 0, v_stack_1190_);
v___x_1192_ = v___x_1182_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_stack_1190_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v_lhsPrec_1176_);
lean_ctor_set(v_reuseFailAlloc_1193_, 2, v_pos_1177_);
lean_ctor_set(v_reuseFailAlloc_1193_, 3, v_cache_1178_);
lean_ctor_set(v_reuseFailAlloc_1193_, 4, v_errorMsg_1179_);
lean_ctor_set(v_reuseFailAlloc_1193_, 5, v_recoveredErrors_1180_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1202_, lean_object* v_k_1203_, lean_object* v_iniStackSz_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Parser_ParserState_mkNode(v_s_1202_, v_k_1203_, v_iniStackSz_1204_);
lean_dec(v_iniStackSz_1204_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1206_, lean_object* v_k_1207_, lean_object* v_iniStackSz_1208_){
_start:
{
lean_object* v_stxStack_1209_; lean_object* v_lhsPrec_1210_; lean_object* v_pos_1211_; lean_object* v_cache_1212_; lean_object* v_errorMsg_1213_; lean_object* v_recoveredErrors_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1229_; 
v_stxStack_1209_ = lean_ctor_get(v_s_1206_, 0);
v_lhsPrec_1210_ = lean_ctor_get(v_s_1206_, 1);
v_pos_1211_ = lean_ctor_get(v_s_1206_, 2);
v_cache_1212_ = lean_ctor_get(v_s_1206_, 3);
v_errorMsg_1213_ = lean_ctor_get(v_s_1206_, 4);
v_recoveredErrors_1214_ = lean_ctor_get(v_s_1206_, 5);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_s_1206_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1216_ = v_s_1206_;
v_isShared_1217_ = v_isSharedCheck_1229_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_recoveredErrors_1214_);
lean_inc(v_errorMsg_1213_);
lean_inc(v_cache_1212_);
lean_inc(v_pos_1211_);
lean_inc(v_lhsPrec_1210_);
lean_inc(v_stxStack_1209_);
lean_dec(v_s_1206_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1229_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v_newNode_1223_; lean_object* v_stack_1224_; lean_object* v_stack_1225_; lean_object* v___x_1227_; 
v___x_1218_ = lean_box(2);
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = lean_nat_sub(v_iniStackSz_1208_, v___x_1219_);
v___x_1221_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1209_);
v___x_1222_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1209_, v___x_1220_, v___x_1221_);
lean_dec(v___x_1221_);
v_newNode_1223_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1223_, 0, v___x_1218_);
lean_ctor_set(v_newNode_1223_, 1, v_k_1207_);
lean_ctor_set(v_newNode_1223_, 2, v___x_1222_);
v_stack_1224_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1209_, v___x_1220_);
lean_dec(v___x_1220_);
v_stack_1225_ = l_Lean_Parser_SyntaxStack_push(v_stack_1224_, v_newNode_1223_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v_stack_1225_);
v___x_1227_ = v___x_1216_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_stack_1225_);
lean_ctor_set(v_reuseFailAlloc_1228_, 1, v_lhsPrec_1210_);
lean_ctor_set(v_reuseFailAlloc_1228_, 2, v_pos_1211_);
lean_ctor_set(v_reuseFailAlloc_1228_, 3, v_cache_1212_);
lean_ctor_set(v_reuseFailAlloc_1228_, 4, v_errorMsg_1213_);
lean_ctor_set(v_reuseFailAlloc_1228_, 5, v_recoveredErrors_1214_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1230_, lean_object* v_k_1231_, lean_object* v_iniStackSz_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1230_, v_k_1231_, v_iniStackSz_1232_);
lean_dec(v_iniStackSz_1232_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1236_){
_start:
{
lean_object* v_errorMsg_1237_; 
v_errorMsg_1237_ = lean_ctor_get(v_s_1236_, 4);
if (lean_obj_tag(v_errorMsg_1237_) == 0)
{
lean_object* v_recoveredErrors_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; 
v_recoveredErrors_1238_ = lean_ctor_get(v_s_1236_, 5);
lean_inc_ref(v_recoveredErrors_1238_);
lean_dec_ref(v_s_1236_);
v___x_1239_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1240_ = l_Array_append___redArg(v_recoveredErrors_1238_, v___x_1239_);
return v___x_1240_;
}
else
{
lean_object* v_stxStack_1241_; lean_object* v_pos_1242_; lean_object* v_recoveredErrors_1243_; lean_object* v_val_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
lean_inc_ref(v_errorMsg_1237_);
v_stxStack_1241_ = lean_ctor_get(v_s_1236_, 0);
lean_inc_ref(v_stxStack_1241_);
v_pos_1242_ = lean_ctor_get(v_s_1236_, 2);
lean_inc(v_pos_1242_);
v_recoveredErrors_1243_ = lean_ctor_get(v_s_1236_, 5);
lean_inc_ref(v_recoveredErrors_1243_);
lean_dec_ref(v_s_1236_);
v_val_1244_ = lean_ctor_get(v_errorMsg_1237_, 0);
lean_inc(v_val_1244_);
lean_dec_ref(v_errorMsg_1237_);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v_stxStack_1241_);
lean_ctor_set(v___x_1245_, 1, v_val_1244_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_pos_1242_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_unsigned_to_nat(1u);
v___x_1248_ = lean_mk_empty_array_with_capacity(v___x_1247_);
v___x_1249_ = lean_array_push(v___x_1248_, v___x_1246_);
v___x_1250_ = l_Array_append___redArg(v_recoveredErrors_1243_, v___x_1249_);
lean_dec_ref(v___x_1249_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1251_, lean_object* v_e_1252_){
_start:
{
lean_object* v_stxStack_1253_; lean_object* v_lhsPrec_1254_; lean_object* v_pos_1255_; lean_object* v_cache_1256_; lean_object* v_recoveredErrors_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1265_; 
v_stxStack_1253_ = lean_ctor_get(v_s_1251_, 0);
v_lhsPrec_1254_ = lean_ctor_get(v_s_1251_, 1);
v_pos_1255_ = lean_ctor_get(v_s_1251_, 2);
v_cache_1256_ = lean_ctor_get(v_s_1251_, 3);
v_recoveredErrors_1257_ = lean_ctor_get(v_s_1251_, 5);
v_isSharedCheck_1265_ = !lean_is_exclusive(v_s_1251_);
if (v_isSharedCheck_1265_ == 0)
{
lean_object* v_unused_1266_; 
v_unused_1266_ = lean_ctor_get(v_s_1251_, 4);
lean_dec(v_unused_1266_);
v___x_1259_ = v_s_1251_;
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_recoveredErrors_1257_);
lean_inc(v_cache_1256_);
lean_inc(v_pos_1255_);
lean_inc(v_lhsPrec_1254_);
lean_inc(v_stxStack_1253_);
lean_dec(v_s_1251_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1265_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1263_; 
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v_e_1252_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 4, v___x_1261_);
v___x_1263_ = v___x_1259_;
goto v_reusejp_1262_;
}
else
{
lean_object* v_reuseFailAlloc_1264_; 
v_reuseFailAlloc_1264_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1264_, 0, v_stxStack_1253_);
lean_ctor_set(v_reuseFailAlloc_1264_, 1, v_lhsPrec_1254_);
lean_ctor_set(v_reuseFailAlloc_1264_, 2, v_pos_1255_);
lean_ctor_set(v_reuseFailAlloc_1264_, 3, v_cache_1256_);
lean_ctor_set(v_reuseFailAlloc_1264_, 4, v___x_1261_);
lean_ctor_set(v_reuseFailAlloc_1264_, 5, v_recoveredErrors_1257_);
v___x_1263_ = v_reuseFailAlloc_1264_;
goto v_reusejp_1262_;
}
v_reusejp_1262_:
{
return v___x_1263_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1267_, lean_object* v_msg_1268_){
_start:
{
lean_object* v_stxStack_1269_; lean_object* v_lhsPrec_1270_; lean_object* v_pos_1271_; lean_object* v_cache_1272_; lean_object* v_recoveredErrors_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1287_; 
v_stxStack_1269_ = lean_ctor_get(v_s_1267_, 0);
v_lhsPrec_1270_ = lean_ctor_get(v_s_1267_, 1);
v_pos_1271_ = lean_ctor_get(v_s_1267_, 2);
v_cache_1272_ = lean_ctor_get(v_s_1267_, 3);
v_recoveredErrors_1273_ = lean_ctor_get(v_s_1267_, 5);
v_isSharedCheck_1287_ = !lean_is_exclusive(v_s_1267_);
if (v_isSharedCheck_1287_ == 0)
{
lean_object* v_unused_1288_; 
v_unused_1288_ = lean_ctor_get(v_s_1267_, 4);
lean_dec(v_unused_1288_);
v___x_1275_ = v_s_1267_;
v_isShared_1276_ = v_isSharedCheck_1287_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_recoveredErrors_1273_);
lean_inc(v_cache_1272_);
lean_inc(v_pos_1271_);
lean_inc(v_lhsPrec_1270_);
lean_inc(v_stxStack_1269_);
lean_dec(v_s_1267_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1287_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
v___x_1277_ = lean_box(0);
v___x_1278_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_msg_1268_);
lean_ctor_set(v___x_1280_, 1, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1277_);
lean_ctor_set(v___x_1281_, 1, v___x_1278_);
lean_ctor_set(v___x_1281_, 2, v___x_1280_);
v___x_1282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 4, v___x_1282_);
v___x_1284_ = v___x_1275_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_stxStack_1269_);
lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_lhsPrec_1270_);
lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_pos_1271_);
lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_cache_1272_);
lean_ctor_set(v_reuseFailAlloc_1286_, 4, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1286_, 5, v_recoveredErrors_1273_);
v___x_1284_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1284_, v___x_1277_);
return v___x_1285_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1289_, lean_object* v_msg_1290_, lean_object* v_expected_1291_, uint8_t v_pushMissing_1292_){
_start:
{
lean_object* v_stxStack_1293_; lean_object* v_lhsPrec_1294_; lean_object* v_pos_1295_; lean_object* v_cache_1296_; lean_object* v_recoveredErrors_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1308_; 
v_stxStack_1293_ = lean_ctor_get(v_s_1289_, 0);
v_lhsPrec_1294_ = lean_ctor_get(v_s_1289_, 1);
v_pos_1295_ = lean_ctor_get(v_s_1289_, 2);
v_cache_1296_ = lean_ctor_get(v_s_1289_, 3);
v_recoveredErrors_1297_ = lean_ctor_get(v_s_1289_, 5);
v_isSharedCheck_1308_ = !lean_is_exclusive(v_s_1289_);
if (v_isSharedCheck_1308_ == 0)
{
lean_object* v_unused_1309_; 
v_unused_1309_ = lean_ctor_get(v_s_1289_, 4);
lean_dec(v_unused_1309_);
v___x_1299_ = v_s_1289_;
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_recoveredErrors_1297_);
lean_inc(v_cache_1296_);
lean_inc(v_pos_1295_);
lean_inc(v_lhsPrec_1294_);
lean_inc(v_stxStack_1293_);
lean_dec(v_s_1289_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1308_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v_s_1305_; 
v___x_1301_ = lean_box(0);
v___x_1302_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v_msg_1290_);
lean_ctor_set(v___x_1302_, 2, v_expected_1291_);
v___x_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1302_);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 4, v___x_1303_);
v_s_1305_ = v___x_1299_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_stxStack_1293_);
lean_ctor_set(v_reuseFailAlloc_1307_, 1, v_lhsPrec_1294_);
lean_ctor_set(v_reuseFailAlloc_1307_, 2, v_pos_1295_);
lean_ctor_set(v_reuseFailAlloc_1307_, 3, v_cache_1296_);
lean_ctor_set(v_reuseFailAlloc_1307_, 4, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1307_, 5, v_recoveredErrors_1297_);
v_s_1305_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
if (v_pushMissing_1292_ == 0)
{
return v_s_1305_;
}
else
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1305_, v___x_1301_);
return v___x_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1310_, lean_object* v_msg_1311_, lean_object* v_expected_1312_, lean_object* v_pushMissing_1313_){
_start:
{
uint8_t v_pushMissing_boxed_1314_; lean_object* v_res_1315_; 
v_pushMissing_boxed_1314_ = lean_unbox(v_pushMissing_1313_);
v_res_1315_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1310_, v_msg_1311_, v_expected_1312_, v_pushMissing_boxed_1314_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1317_, lean_object* v_expected_1318_){
_start:
{
lean_object* v___x_1319_; uint8_t v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1320_ = 1;
v___x_1321_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1317_, v___x_1319_, v_expected_1318_, v___x_1320_);
return v___x_1321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1322_, lean_object* v_ex_1323_, lean_object* v_pos_1324_, lean_object* v_initStackSz_x3f_1325_){
_start:
{
lean_object* v_s_1327_; lean_object* v_s_1346_; 
v_s_1346_ = l_Lean_Parser_ParserState_setPos(v_s_1322_, v_pos_1324_);
if (lean_obj_tag(v_initStackSz_x3f_1325_) == 1)
{
lean_object* v_val_1347_; lean_object* v_s_1348_; 
v_val_1347_ = lean_ctor_get(v_initStackSz_x3f_1325_, 0);
v_s_1348_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1346_, v_val_1347_);
v_s_1327_ = v_s_1348_;
goto v___jp_1326_;
}
else
{
v_s_1327_ = v_s_1346_;
goto v___jp_1326_;
}
v___jp_1326_:
{
lean_object* v_stxStack_1328_; lean_object* v_lhsPrec_1329_; lean_object* v_pos_1330_; lean_object* v_cache_1331_; lean_object* v_recoveredErrors_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1344_; 
v_stxStack_1328_ = lean_ctor_get(v_s_1327_, 0);
v_lhsPrec_1329_ = lean_ctor_get(v_s_1327_, 1);
v_pos_1330_ = lean_ctor_get(v_s_1327_, 2);
v_cache_1331_ = lean_ctor_get(v_s_1327_, 3);
v_recoveredErrors_1332_ = lean_ctor_get(v_s_1327_, 5);
v_isSharedCheck_1344_ = !lean_is_exclusive(v_s_1327_);
if (v_isSharedCheck_1344_ == 0)
{
lean_object* v_unused_1345_; 
v_unused_1345_ = lean_ctor_get(v_s_1327_, 4);
lean_dec(v_unused_1345_);
v___x_1334_ = v_s_1327_;
v_isShared_1335_ = v_isSharedCheck_1344_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_recoveredErrors_1332_);
lean_inc(v_cache_1331_);
lean_inc(v_pos_1330_);
lean_inc(v_lhsPrec_1329_);
lean_inc(v_stxStack_1328_);
lean_dec(v_s_1327_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1344_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v_s_1341_; 
v___x_1336_ = lean_box(0);
v___x_1337_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1338_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
lean_ctor_set(v___x_1338_, 2, v_ex_1323_);
v___x_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1338_);
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 4, v___x_1339_);
v_s_1341_ = v___x_1334_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_stxStack_1328_);
lean_ctor_set(v_reuseFailAlloc_1343_, 1, v_lhsPrec_1329_);
lean_ctor_set(v_reuseFailAlloc_1343_, 2, v_pos_1330_);
lean_ctor_set(v_reuseFailAlloc_1343_, 3, v_cache_1331_);
lean_ctor_set(v_reuseFailAlloc_1343_, 4, v___x_1339_);
lean_ctor_set(v_reuseFailAlloc_1343_, 5, v_recoveredErrors_1332_);
v_s_1341_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1341_, v___x_1336_);
return v___x_1342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1349_, lean_object* v_ex_1350_, lean_object* v_pos_1351_, lean_object* v_initStackSz_x3f_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1349_, v_ex_1350_, v_pos_1351_, v_initStackSz_x3f_1352_);
lean_dec(v_initStackSz_x3f_1352_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1354_, lean_object* v_msg_1355_, lean_object* v_pos_1356_, lean_object* v_initStackSz_x3f_1357_){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = lean_box(0);
v___x_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1359_, 0, v_msg_1355_);
lean_ctor_set(v___x_1359_, 1, v___x_1358_);
v___x_1360_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1354_, v___x_1359_, v_pos_1356_, v_initStackSz_x3f_1357_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1361_, lean_object* v_msg_1362_, lean_object* v_pos_1363_, lean_object* v_initStackSz_x3f_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1361_, v_msg_1362_, v_pos_1363_, v_initStackSz_x3f_1364_);
lean_dec(v_initStackSz_x3f_1364_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1366_){
_start:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_panic_fn_borrowed(v___x_1367_, v_msg_1366_);
return v___x_1368_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1372_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1373_ = lean_unsigned_to_nat(14u);
v___x_1374_ = lean_unsigned_to_nat(22u);
v___x_1375_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1376_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1377_ = l_mkPanicMessageWithDecl(v___x_1376_, v___x_1375_, v___x_1374_, v___x_1373_, v___x_1372_);
return v___x_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1378_, lean_object* v_ex_1379_, lean_object* v_iniPos_1380_){
_start:
{
lean_object* v_stxStack_1381_; lean_object* v_tk_1382_; lean_object* v___y_1384_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v_stxStack_1381_ = lean_ctor_get(v_s_1378_, 0);
v_tk_1382_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1381_);
v___x_1405_ = lean_unsigned_to_nat(0u);
v___x_1406_ = lean_nat_dec_lt(v___x_1405_, v_iniPos_1380_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; 
lean_dec(v_iniPos_1380_);
v___x_1407_ = l_Lean_Syntax_getPos_x3f(v_tk_1382_, v___x_1406_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1409_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1408_);
v___y_1384_ = v___x_1409_;
goto v___jp_1383_;
}
else
{
lean_object* v_val_1410_; 
v_val_1410_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_val_1410_);
lean_dec_ref(v___x_1407_);
v___y_1384_ = v_val_1410_;
goto v___jp_1383_;
}
}
else
{
v___y_1384_ = v_iniPos_1380_;
goto v___jp_1383_;
}
v___jp_1383_:
{
lean_object* v_s_1385_; lean_object* v_stxStack_1386_; lean_object* v_lhsPrec_1387_; lean_object* v_pos_1388_; lean_object* v_cache_1389_; lean_object* v_recoveredErrors_1390_; lean_object* v___x_1392_; uint8_t v_isShared_1393_; uint8_t v_isSharedCheck_1403_; 
v_s_1385_ = l_Lean_Parser_ParserState_setPos(v_s_1378_, v___y_1384_);
v_stxStack_1386_ = lean_ctor_get(v_s_1385_, 0);
v_lhsPrec_1387_ = lean_ctor_get(v_s_1385_, 1);
v_pos_1388_ = lean_ctor_get(v_s_1385_, 2);
v_cache_1389_ = lean_ctor_get(v_s_1385_, 3);
v_recoveredErrors_1390_ = lean_ctor_get(v_s_1385_, 5);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_s_1385_);
if (v_isSharedCheck_1403_ == 0)
{
lean_object* v_unused_1404_; 
v_unused_1404_ = lean_ctor_get(v_s_1385_, 4);
lean_dec(v_unused_1404_);
v___x_1392_ = v_s_1385_;
v_isShared_1393_ = v_isSharedCheck_1403_;
goto v_resetjp_1391_;
}
else
{
lean_inc(v_recoveredErrors_1390_);
lean_inc(v_cache_1389_);
lean_inc(v_pos_1388_);
lean_inc(v_lhsPrec_1387_);
lean_inc(v_stxStack_1386_);
lean_dec(v_s_1385_);
v___x_1392_ = lean_box(0);
v_isShared_1393_ = v_isSharedCheck_1403_;
goto v_resetjp_1391_;
}
v_resetjp_1391_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v_s_1398_; 
v___x_1394_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1395_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1395_, 0, v_tk_1382_);
lean_ctor_set(v___x_1395_, 1, v___x_1394_);
lean_ctor_set(v___x_1395_, 2, v_ex_1379_);
v___x_1396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
if (v_isShared_1393_ == 0)
{
lean_ctor_set(v___x_1392_, 4, v___x_1396_);
v_s_1398_ = v___x_1392_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_stxStack_1386_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v_lhsPrec_1387_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_pos_1388_);
lean_ctor_set(v_reuseFailAlloc_1402_, 3, v_cache_1389_);
lean_ctor_set(v_reuseFailAlloc_1402_, 4, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1402_, 5, v_recoveredErrors_1390_);
v_s_1398_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1399_ = l_Lean_Parser_ParserState_popSyntax(v_s_1398_);
v___x_1400_ = lean_box(0);
v___x_1401_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1399_, v___x_1400_);
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1411_, lean_object* v_msg_1412_, lean_object* v_iniPos_1413_){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1414_ = lean_box(0);
v___x_1415_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1415_, 0, v_msg_1412_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1411_, v___x_1415_, v_iniPos_1413_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1417_, lean_object* v_msg_1418_, lean_object* v_pos_1419_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; lean_object* v___x_1423_; 
v___x_1420_ = l_Lean_Parser_ParserState_setPos(v_s_1417_, v_pos_1419_);
v___x_1421_ = lean_box(0);
v___x_1422_ = 1;
v___x_1423_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1420_, v_msg_1418_, v___x_1421_, v___x_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1425_, lean_object* v_as_1426_, size_t v_sz_1427_, size_t v_i_1428_, lean_object* v_b_1429_){
_start:
{
uint8_t v___x_1430_; 
v___x_1430_ = lean_usize_dec_lt(v_i_1428_, v_sz_1427_);
if (v___x_1430_ == 0)
{
lean_dec_ref(v_ctx_1425_);
return v_b_1429_;
}
else
{
lean_object* v_a_1431_; lean_object* v_snd_1432_; lean_object* v_fst_1433_; lean_object* v_snd_1434_; lean_object* v_errStr_1436_; lean_object* v_errStr_1447_; uint8_t v___x_1448_; 
v_a_1431_ = lean_array_uget_borrowed(v_as_1426_, v_i_1428_);
v_snd_1432_ = lean_ctor_get(v_a_1431_, 1);
v_fst_1433_ = lean_ctor_get(v_a_1431_, 0);
v_snd_1434_ = lean_ctor_get(v_snd_1432_, 1);
v_errStr_1447_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1448_ = lean_string_dec_eq(v_b_1429_, v_errStr_1447_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1450_ = lean_string_append(v_b_1429_, v___x_1449_);
v_errStr_1436_ = v___x_1450_;
goto v___jp_1435_;
}
else
{
v_errStr_1436_ = v_b_1429_;
goto v___jp_1435_;
}
v___jp_1435_:
{
lean_object* v_fileName_1437_; lean_object* v_fileMap_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; size_t v___x_1444_; size_t v___x_1445_; 
v_fileName_1437_ = lean_ctor_get(v_ctx_1425_, 1);
v_fileMap_1438_ = lean_ctor_get(v_ctx_1425_, 2);
lean_inc_ref(v_fileMap_1438_);
v___x_1439_ = l_Lean_FileMap_toPosition(v_fileMap_1438_, v_fst_1433_);
lean_inc(v_snd_1434_);
v___x_1440_ = l_Lean_Parser_Error_toString(v_snd_1434_);
v___x_1441_ = lean_box(0);
lean_inc_ref(v_fileName_1437_);
v___x_1442_ = l_Lean_mkErrorStringWithPos(v_fileName_1437_, v___x_1439_, v___x_1440_, v___x_1441_, v___x_1441_, v___x_1441_);
lean_dec_ref(v___x_1440_);
v___x_1443_ = lean_string_append(v_errStr_1436_, v___x_1442_);
lean_dec_ref(v___x_1442_);
v___x_1444_ = ((size_t)1ULL);
v___x_1445_ = lean_usize_add(v_i_1428_, v___x_1444_);
v_i_1428_ = v___x_1445_;
v_b_1429_ = v___x_1443_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1451_, lean_object* v_as_1452_, lean_object* v_sz_1453_, lean_object* v_i_1454_, lean_object* v_b_1455_){
_start:
{
size_t v_sz_boxed_1456_; size_t v_i_boxed_1457_; lean_object* v_res_1458_; 
v_sz_boxed_1456_ = lean_unbox_usize(v_sz_1453_);
lean_dec(v_sz_1453_);
v_i_boxed_1457_ = lean_unbox_usize(v_i_1454_);
lean_dec(v_i_1454_);
v_res_1458_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1451_, v_as_1452_, v_sz_boxed_1456_, v_i_boxed_1457_, v_b_1455_);
lean_dec_ref(v_as_1452_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1459_, lean_object* v_s_1460_){
_start:
{
lean_object* v_errStr_1461_; lean_object* v___x_1462_; size_t v_sz_1463_; size_t v___x_1464_; lean_object* v___x_1465_; 
v_errStr_1461_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1462_ = l_Lean_Parser_ParserState_allErrors(v_s_1460_);
v_sz_1463_ = lean_array_size(v___x_1462_);
v___x_1464_ = ((size_t)0ULL);
v___x_1465_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1459_, v___x_1462_, v_sz_1463_, v___x_1464_, v_errStr_1461_);
lean_dec_ref(v___x_1462_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1466_, lean_object* v_s_1467_){
_start:
{
lean_inc_ref(v_s_1467_);
return v_s_1467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1468_, lean_object* v_s_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1468_, v_s_1469_);
lean_dec_ref(v_s_1469_);
lean_dec_ref(v_x_1468_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx(lean_object* v_x_1473_){
_start:
{
switch(lean_obj_tag(v_x_1473_))
{
case 0:
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_unsigned_to_nat(0u);
return v___x_1474_;
}
case 1:
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_unsigned_to_nat(1u);
return v___x_1475_;
}
case 2:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_unsigned_to_nat(2u);
return v___x_1476_;
}
default: 
{
lean_object* v___x_1477_; 
v___x_1477_ = lean_unsigned_to_nat(3u);
return v___x_1477_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___boxed(lean_object* v_x_1478_){
_start:
{
lean_object* v_res_1479_; 
v_res_1479_ = l_Lean_Parser_FirstTokens_ctorIdx(v_x_1478_);
lean_dec(v_x_1478_);
return v_res_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1480_, lean_object* v_k_1481_){
_start:
{
switch(lean_obj_tag(v_t_1480_))
{
case 2:
{
lean_object* v_a_1482_; lean_object* v___x_1483_; 
v_a_1482_ = lean_ctor_get(v_t_1480_, 0);
lean_inc(v_a_1482_);
lean_dec_ref(v_t_1480_);
v___x_1483_ = lean_apply_1(v_k_1481_, v_a_1482_);
return v___x_1483_;
}
case 3:
{
lean_object* v_a_1484_; lean_object* v___x_1485_; 
v_a_1484_ = lean_ctor_get(v_t_1480_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v_t_1480_);
v___x_1485_ = lean_apply_1(v_k_1481_, v_a_1484_);
return v___x_1485_;
}
default: 
{
lean_dec(v_t_1480_);
return v_k_1481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1486_, lean_object* v_ctorIdx_1487_, lean_object* v_t_1488_, lean_object* v_h_1489_, lean_object* v_k_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1488_, v_k_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1492_, lean_object* v_ctorIdx_1493_, lean_object* v_t_1494_, lean_object* v_h_1495_, lean_object* v_k_1496_){
_start:
{
lean_object* v_res_1497_; 
v_res_1497_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1492_, v_ctorIdx_1493_, v_t_1494_, v_h_1495_, v_k_1496_);
lean_dec(v_ctorIdx_1493_);
return v_res_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1498_, lean_object* v_epsilon_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1498_, v_epsilon_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1501_, lean_object* v_t_1502_, lean_object* v_h_1503_, lean_object* v_epsilon_1504_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1502_, v_epsilon_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1506_, lean_object* v_unknown_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1506_, v_unknown_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1509_, lean_object* v_t_1510_, lean_object* v_h_1511_, lean_object* v_unknown_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1510_, v_unknown_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1514_, lean_object* v_tokens_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1514_, v_tokens_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1517_, lean_object* v_t_1518_, lean_object* v_h_1519_, lean_object* v_tokens_1520_){
_start:
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1518_, v_tokens_1520_);
return v___x_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1522_, lean_object* v_optTokens_1523_){
_start:
{
lean_object* v___x_1524_; 
v___x_1524_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1522_, v_optTokens_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1525_, lean_object* v_t_1526_, lean_object* v_h_1527_, lean_object* v_optTokens_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1526_, v_optTokens_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = lean_box(0);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_box(0);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1532_, lean_object* v_x_1533_){
_start:
{
switch(lean_obj_tag(v_x_1532_))
{
case 0:
{
return v_x_1533_;
}
case 3:
{
switch(lean_obj_tag(v_x_1533_))
{
case 3:
{
lean_object* v_a_1534_; lean_object* v_a_1535_; lean_object* v___x_1537_; uint8_t v_isShared_1538_; uint8_t v_isSharedCheck_1543_; 
v_a_1534_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_a_1534_);
lean_dec_ref(v_x_1532_);
v_a_1535_ = lean_ctor_get(v_x_1533_, 0);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_x_1533_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1537_ = v_x_1533_;
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
else
{
lean_inc(v_a_1535_);
lean_dec(v_x_1533_);
v___x_1537_ = lean_box(0);
v_isShared_1538_ = v_isSharedCheck_1543_;
goto v_resetjp_1536_;
}
v_resetjp_1536_:
{
lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1539_ = l_List_appendTR___redArg(v_a_1534_, v_a_1535_);
if (v_isShared_1538_ == 0)
{
lean_ctor_set(v___x_1537_, 0, v___x_1539_);
v___x_1541_ = v___x_1537_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
case 2:
{
lean_object* v_a_1544_; lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1553_; 
v_a_1544_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v_x_1532_);
v_a_1545_ = lean_ctor_get(v_x_1533_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v_x_1533_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1547_ = v_x_1533_;
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v_x_1533_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1553_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
lean_object* v___x_1549_; lean_object* v___x_1551_; 
v___x_1549_ = l_List_appendTR___redArg(v_a_1544_, v_a_1545_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v___x_1549_);
v___x_1551_ = v___x_1547_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
case 1:
{
lean_dec_ref(v_x_1532_);
return v_x_1533_;
}
default: 
{
lean_dec(v_x_1533_);
return v_x_1532_;
}
}
}
default: 
{
lean_dec(v_x_1533_);
return v_x_1532_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1554_){
_start:
{
if (lean_obj_tag(v_x_1554_) == 2)
{
lean_object* v_a_1555_; lean_object* v___x_1557_; uint8_t v_isShared_1558_; uint8_t v_isSharedCheck_1562_; 
v_a_1555_ = lean_ctor_get(v_x_1554_, 0);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_x_1554_);
if (v_isSharedCheck_1562_ == 0)
{
v___x_1557_ = v_x_1554_;
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
else
{
lean_inc(v_a_1555_);
lean_dec(v_x_1554_);
v___x_1557_ = lean_box(0);
v_isShared_1558_ = v_isSharedCheck_1562_;
goto v_resetjp_1556_;
}
v_resetjp_1556_:
{
lean_object* v___x_1560_; 
if (v_isShared_1558_ == 0)
{
lean_ctor_set_tag(v___x_1557_, 3);
v___x_1560_ = v___x_1557_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_a_1555_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
else
{
return v_x_1554_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1563_, lean_object* v_x_1564_){
_start:
{
lean_object* v_s_u2081_1566_; lean_object* v_s_u2082_1567_; 
switch(lean_obj_tag(v_x_1563_))
{
case 0:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1564_);
return v___x_1570_;
}
case 2:
{
switch(lean_obj_tag(v_x_1564_))
{
case 0:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1563_);
return v___x_1571_;
}
case 2:
{
lean_object* v_a_1572_; lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1581_; 
v_a_1572_ = lean_ctor_get(v_x_1563_, 0);
lean_inc(v_a_1572_);
lean_dec_ref(v_x_1563_);
v_a_1573_ = lean_ctor_get(v_x_1564_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v_x_1564_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1575_ = v_x_1564_;
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v_x_1564_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1581_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1577_; lean_object* v___x_1579_; 
v___x_1577_ = l_List_appendTR___redArg(v_a_1572_, v_a_1573_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1577_);
v___x_1579_ = v___x_1575_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1577_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
case 3:
{
lean_object* v_a_1582_; lean_object* v_a_1583_; 
v_a_1582_ = lean_ctor_get(v_x_1563_, 0);
lean_inc(v_a_1582_);
lean_dec_ref(v_x_1563_);
v_a_1583_ = lean_ctor_get(v_x_1564_, 0);
lean_inc(v_a_1583_);
lean_dec_ref(v_x_1564_);
v_s_u2081_1566_ = v_a_1582_;
v_s_u2082_1567_ = v_a_1583_;
goto v___jp_1565_;
}
default: 
{
lean_object* v___x_1584_; 
lean_dec_ref(v_x_1563_);
lean_dec(v_x_1564_);
v___x_1584_ = lean_box(1);
return v___x_1584_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1564_))
{
case 0:
{
lean_object* v___x_1585_; 
v___x_1585_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1563_);
return v___x_1585_;
}
case 3:
{
lean_object* v_a_1586_; lean_object* v_a_1587_; 
v_a_1586_ = lean_ctor_get(v_x_1563_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v_x_1563_);
v_a_1587_ = lean_ctor_get(v_x_1564_, 0);
lean_inc(v_a_1587_);
lean_dec_ref(v_x_1564_);
v_s_u2081_1566_ = v_a_1586_;
v_s_u2082_1567_ = v_a_1587_;
goto v___jp_1565_;
}
case 2:
{
lean_object* v_a_1588_; lean_object* v_a_1589_; 
v_a_1588_ = lean_ctor_get(v_x_1563_, 0);
lean_inc(v_a_1588_);
lean_dec_ref(v_x_1563_);
v_a_1589_ = lean_ctor_get(v_x_1564_, 0);
lean_inc(v_a_1589_);
lean_dec_ref(v_x_1564_);
v_s_u2081_1566_ = v_a_1588_;
v_s_u2082_1567_ = v_a_1589_;
goto v___jp_1565_;
}
default: 
{
lean_object* v___x_1590_; 
lean_dec_ref(v_x_1563_);
lean_dec(v_x_1564_);
v___x_1590_ = lean_box(1);
return v___x_1590_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1564_) == 0)
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1563_);
return v___x_1591_;
}
else
{
lean_object* v___x_1592_; 
lean_dec(v_x_1564_);
lean_dec(v_x_1563_);
v___x_1592_ = lean_box(1);
return v___x_1592_;
}
}
}
v___jp_1565_:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = l_List_appendTR___redArg(v_s_u2081_1566_, v_s_u2082_1567_);
v___x_1569_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1569_, 0, v___x_1568_);
return v___x_1569_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1593_, lean_object* v_x_1594_){
_start:
{
if (lean_obj_tag(v_x_1594_) == 0)
{
return v_x_1593_;
}
else
{
lean_object* v_head_1595_; lean_object* v_tail_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v_head_1595_ = lean_ctor_get(v_x_1594_, 0);
v_tail_1596_ = lean_ctor_get(v_x_1594_, 1);
v___x_1597_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1598_ = lean_string_append(v_x_1593_, v___x_1597_);
v___x_1599_ = lean_string_append(v___x_1598_, v_head_1595_);
v_x_1593_ = v___x_1599_;
v_x_1594_ = v_tail_1596_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1601_, lean_object* v_x_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1601_, v_x_1602_);
lean_dec(v_x_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1607_){
_start:
{
if (lean_obj_tag(v_x_1607_) == 0)
{
lean_object* v___x_1608_; 
v___x_1608_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1608_;
}
else
{
lean_object* v_tail_1609_; 
v_tail_1609_ = lean_ctor_get(v_x_1607_, 1);
if (lean_obj_tag(v_tail_1609_) == 0)
{
lean_object* v_head_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_head_1610_ = lean_ctor_get(v_x_1607_, 0);
v___x_1611_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1612_ = lean_string_append(v___x_1611_, v_head_1610_);
v___x_1613_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1614_ = lean_string_append(v___x_1612_, v___x_1613_);
return v___x_1614_;
}
else
{
lean_object* v_head_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; uint32_t v___x_1619_; lean_object* v___x_1620_; 
v_head_1615_ = lean_ctor_get(v_x_1607_, 0);
v___x_1616_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1617_ = lean_string_append(v___x_1616_, v_head_1615_);
v___x_1618_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1617_, v_tail_1609_);
v___x_1619_ = 93;
v___x_1620_ = lean_string_push(v___x_1618_, v___x_1619_);
return v___x_1620_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1621_);
lean_dec(v_x_1621_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1626_){
_start:
{
switch(lean_obj_tag(v_x_1626_))
{
case 0:
{
lean_object* v___x_1627_; 
v___x_1627_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1627_;
}
case 1:
{
lean_object* v___x_1628_; 
v___x_1628_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1628_;
}
case 2:
{
lean_object* v_a_1629_; lean_object* v___x_1630_; 
v_a_1629_ = lean_ctor_get(v_x_1626_, 0);
v___x_1630_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1629_);
return v___x_1630_;
}
default: 
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v_a_1631_ = lean_ctor_get(v_x_1626_, 0);
v___x_1632_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1633_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1631_);
v___x_1634_ = lean_string_append(v___x_1632_, v___x_1633_);
lean_dec_ref(v___x_1633_);
return v___x_1634_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1635_){
_start:
{
lean_object* v_res_1636_; 
v_res_1636_ = l_Lean_Parser_FirstTokens_toStr(v_x_1635_);
lean_dec(v_x_1635_);
return v_res_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v___y_1639_){
_start:
{
lean_inc(v___y_1639_);
return v___y_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_1640_);
lean_dec(v___y_1640_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v___y_1642_){
_start:
{
lean_inc_ref(v___y_1642_);
return v___y_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v___y_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_1643_);
lean_dec_ref(v___y_1643_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1658_, lean_object* v_p_1659_){
_start:
{
lean_object* v_info_1660_; lean_object* v_fn_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1669_; 
v_info_1660_ = lean_ctor_get(v_p_1659_, 0);
v_fn_1661_ = lean_ctor_get(v_p_1659_, 1);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_p_1659_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1663_ = v_p_1659_;
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
else
{
lean_inc(v_fn_1661_);
lean_inc(v_info_1660_);
lean_dec(v_p_1659_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = lean_apply_1(v_f_1658_, v_fn_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 1, v___x_1665_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_info_1660_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1670_, lean_object* v_p_1671_, lean_object* v_c_1672_, lean_object* v_s_1673_){
_start:
{
lean_object* v_toInputContext_1674_; lean_object* v_toParserModuleContext_1675_; lean_object* v_toCacheableParserContext_1676_; lean_object* v_tokens_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1686_; 
v_toInputContext_1674_ = lean_ctor_get(v_c_1672_, 0);
v_toParserModuleContext_1675_ = lean_ctor_get(v_c_1672_, 1);
v_toCacheableParserContext_1676_ = lean_ctor_get(v_c_1672_, 2);
v_tokens_1677_ = lean_ctor_get(v_c_1672_, 3);
v_isSharedCheck_1686_ = !lean_is_exclusive(v_c_1672_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1679_ = v_c_1672_;
v_isShared_1680_ = v_isSharedCheck_1686_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_tokens_1677_);
lean_inc(v_toCacheableParserContext_1676_);
lean_inc(v_toParserModuleContext_1675_);
lean_inc(v_toInputContext_1674_);
lean_dec(v_c_1672_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1686_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_apply_1(v_f_1670_, v_toCacheableParserContext_1676_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 2, v___x_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_toInputContext_1674_);
lean_ctor_set(v_reuseFailAlloc_1685_, 1, v_toParserModuleContext_1675_);
lean_ctor_set(v_reuseFailAlloc_1685_, 2, v___x_1681_);
lean_ctor_set(v_reuseFailAlloc_1685_, 3, v_tokens_1677_);
v___x_1683_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
lean_object* v___x_1684_; 
v___x_1684_ = lean_apply_2(v_p_1671_, v___x_1683_, v_s_1673_);
return v___x_1684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1687_, lean_object* v_p_1688_){
_start:
{
lean_object* v_info_1689_; lean_object* v_fn_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1698_; 
v_info_1689_ = lean_ctor_get(v_p_1688_, 0);
v_fn_1690_ = lean_ctor_get(v_p_1688_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_p_1688_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1692_ = v_p_1688_;
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_fn_1690_);
lean_inc(v_info_1689_);
lean_dec(v_p_1688_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1698_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1696_; 
v___x_1694_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1694_, 0, v_f_1687_);
lean_closure_set(v___x_1694_, 1, v_fn_1690_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 1, v___x_1694_);
v___x_1696_ = v___x_1692_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_info_1689_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v___x_1694_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1699_, lean_object* v_p_1700_, lean_object* v_c_1701_, lean_object* v_s_1702_){
_start:
{
lean_object* v_stxStack_1703_; lean_object* v_lhsPrec_1704_; lean_object* v_pos_1705_; lean_object* v_cache_1706_; lean_object* v_errorMsg_1707_; lean_object* v_recoveredErrors_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1747_; 
v_stxStack_1703_ = lean_ctor_get(v_s_1702_, 0);
v_lhsPrec_1704_ = lean_ctor_get(v_s_1702_, 1);
v_pos_1705_ = lean_ctor_get(v_s_1702_, 2);
v_cache_1706_ = lean_ctor_get(v_s_1702_, 3);
v_errorMsg_1707_ = lean_ctor_get(v_s_1702_, 4);
v_recoveredErrors_1708_ = lean_ctor_get(v_s_1702_, 5);
v_isSharedCheck_1747_ = !lean_is_exclusive(v_s_1702_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1710_ = v_s_1702_;
v_isShared_1711_ = v_isSharedCheck_1747_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_recoveredErrors_1708_);
lean_inc(v_errorMsg_1707_);
lean_inc(v_cache_1706_);
lean_inc(v_pos_1705_);
lean_inc(v_lhsPrec_1704_);
lean_inc(v_stxStack_1703_);
lean_dec(v_s_1702_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1747_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v_raw_1712_; lean_object* v_drop_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1746_; 
v_raw_1712_ = lean_ctor_get(v_stxStack_1703_, 0);
v_drop_1713_ = lean_ctor_get(v_stxStack_1703_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_stxStack_1703_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1715_ = v_stxStack_1703_;
v_isShared_1716_ = v_isSharedCheck_1746_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_drop_1713_);
lean_inc(v_raw_1712_);
lean_dec(v_stxStack_1703_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1746_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1718_; 
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v_drop_1699_);
v___x_1718_ = v___x_1715_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_raw_1712_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_drop_1699_);
v___x_1718_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
lean_object* v___x_1720_; 
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1718_);
v___x_1720_ = v___x_1710_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1744_; 
v_reuseFailAlloc_1744_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1744_, 0, v___x_1718_);
lean_ctor_set(v_reuseFailAlloc_1744_, 1, v_lhsPrec_1704_);
lean_ctor_set(v_reuseFailAlloc_1744_, 2, v_pos_1705_);
lean_ctor_set(v_reuseFailAlloc_1744_, 3, v_cache_1706_);
lean_ctor_set(v_reuseFailAlloc_1744_, 4, v_errorMsg_1707_);
lean_ctor_set(v_reuseFailAlloc_1744_, 5, v_recoveredErrors_1708_);
v___x_1720_ = v_reuseFailAlloc_1744_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v_s_1721_; lean_object* v_stxStack_1722_; lean_object* v_lhsPrec_1723_; lean_object* v_pos_1724_; lean_object* v_cache_1725_; lean_object* v_errorMsg_1726_; lean_object* v_recoveredErrors_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1743_; 
v_s_1721_ = lean_apply_2(v_p_1700_, v_c_1701_, v___x_1720_);
v_stxStack_1722_ = lean_ctor_get(v_s_1721_, 0);
v_lhsPrec_1723_ = lean_ctor_get(v_s_1721_, 1);
v_pos_1724_ = lean_ctor_get(v_s_1721_, 2);
v_cache_1725_ = lean_ctor_get(v_s_1721_, 3);
v_errorMsg_1726_ = lean_ctor_get(v_s_1721_, 4);
v_recoveredErrors_1727_ = lean_ctor_get(v_s_1721_, 5);
v_isSharedCheck_1743_ = !lean_is_exclusive(v_s_1721_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1729_ = v_s_1721_;
v_isShared_1730_ = v_isSharedCheck_1743_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_recoveredErrors_1727_);
lean_inc(v_errorMsg_1726_);
lean_inc(v_cache_1725_);
lean_inc(v_pos_1724_);
lean_inc(v_lhsPrec_1723_);
lean_inc(v_stxStack_1722_);
lean_dec(v_s_1721_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1743_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v_raw_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1741_; 
v_raw_1731_ = lean_ctor_get(v_stxStack_1722_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_stxStack_1722_);
if (v_isSharedCheck_1741_ == 0)
{
lean_object* v_unused_1742_; 
v_unused_1742_ = lean_ctor_get(v_stxStack_1722_, 1);
lean_dec(v_unused_1742_);
v___x_1733_ = v_stxStack_1722_;
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_raw_1731_);
lean_dec(v_stxStack_1722_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v_drop_1713_);
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_raw_1731_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_drop_1713_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1738_; 
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 0, v___x_1736_);
v___x_1738_ = v___x_1729_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v___x_1736_);
lean_ctor_set(v_reuseFailAlloc_1739_, 1, v_lhsPrec_1723_);
lean_ctor_set(v_reuseFailAlloc_1739_, 2, v_pos_1724_);
lean_ctor_set(v_reuseFailAlloc_1739_, 3, v_cache_1725_);
lean_ctor_set(v_reuseFailAlloc_1739_, 4, v_errorMsg_1726_);
lean_ctor_set(v_reuseFailAlloc_1739_, 5, v_recoveredErrors_1727_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1748_, lean_object* v_c_1749_, lean_object* v_s_1750_){
_start:
{
lean_object* v_cache_1751_; lean_object* v_stxStack_1752_; lean_object* v_lhsPrec_1753_; lean_object* v_pos_1754_; lean_object* v_errorMsg_1755_; lean_object* v_recoveredErrors_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1796_; 
v_cache_1751_ = lean_ctor_get(v_s_1750_, 3);
v_stxStack_1752_ = lean_ctor_get(v_s_1750_, 0);
v_lhsPrec_1753_ = lean_ctor_get(v_s_1750_, 1);
v_pos_1754_ = lean_ctor_get(v_s_1750_, 2);
v_errorMsg_1755_ = lean_ctor_get(v_s_1750_, 4);
v_recoveredErrors_1756_ = lean_ctor_get(v_s_1750_, 5);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_s_1750_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1758_ = v_s_1750_;
v_isShared_1759_ = v_isSharedCheck_1796_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_recoveredErrors_1756_);
lean_inc(v_errorMsg_1755_);
lean_inc(v_cache_1751_);
lean_inc(v_pos_1754_);
lean_inc(v_lhsPrec_1753_);
lean_inc(v_stxStack_1752_);
lean_dec(v_s_1750_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1796_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v_tokenCache_1760_; lean_object* v_parserCache_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1795_; 
v_tokenCache_1760_ = lean_ctor_get(v_cache_1751_, 0);
v_parserCache_1761_ = lean_ctor_get(v_cache_1751_, 1);
v_isSharedCheck_1795_ = !lean_is_exclusive(v_cache_1751_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1763_ = v_cache_1751_;
v_isShared_1764_ = v_isSharedCheck_1795_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_parserCache_1761_);
lean_inc(v_tokenCache_1760_);
lean_dec(v_cache_1751_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1795_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1765_; lean_object* v___x_1767_; 
v___x_1765_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
if (v_isShared_1764_ == 0)
{
lean_ctor_set(v___x_1763_, 1, v___x_1765_);
v___x_1767_ = v___x_1763_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_tokenCache_1760_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v___x_1765_);
v___x_1767_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
lean_object* v___x_1769_; 
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 3, v___x_1767_);
v___x_1769_ = v___x_1758_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_stxStack_1752_);
lean_ctor_set(v_reuseFailAlloc_1793_, 1, v_lhsPrec_1753_);
lean_ctor_set(v_reuseFailAlloc_1793_, 2, v_pos_1754_);
lean_ctor_set(v_reuseFailAlloc_1793_, 3, v___x_1767_);
lean_ctor_set(v_reuseFailAlloc_1793_, 4, v_errorMsg_1755_);
lean_ctor_set(v_reuseFailAlloc_1793_, 5, v_recoveredErrors_1756_);
v___x_1769_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
lean_object* v_s_x27_1770_; lean_object* v_cache_1771_; lean_object* v_stxStack_1772_; lean_object* v_lhsPrec_1773_; lean_object* v_pos_1774_; lean_object* v_errorMsg_1775_; lean_object* v_recoveredErrors_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1792_; 
v_s_x27_1770_ = lean_apply_2(v_p_1748_, v_c_1749_, v___x_1769_);
v_cache_1771_ = lean_ctor_get(v_s_x27_1770_, 3);
v_stxStack_1772_ = lean_ctor_get(v_s_x27_1770_, 0);
v_lhsPrec_1773_ = lean_ctor_get(v_s_x27_1770_, 1);
v_pos_1774_ = lean_ctor_get(v_s_x27_1770_, 2);
v_errorMsg_1775_ = lean_ctor_get(v_s_x27_1770_, 4);
v_recoveredErrors_1776_ = lean_ctor_get(v_s_x27_1770_, 5);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_s_x27_1770_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1778_ = v_s_x27_1770_;
v_isShared_1779_ = v_isSharedCheck_1792_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_recoveredErrors_1776_);
lean_inc(v_errorMsg_1775_);
lean_inc(v_cache_1771_);
lean_inc(v_pos_1774_);
lean_inc(v_lhsPrec_1773_);
lean_inc(v_stxStack_1772_);
lean_dec(v_s_x27_1770_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1792_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v_tokenCache_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1790_; 
v_tokenCache_1780_ = lean_ctor_get(v_cache_1771_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v_cache_1771_);
if (v_isSharedCheck_1790_ == 0)
{
lean_object* v_unused_1791_; 
v_unused_1791_ = lean_ctor_get(v_cache_1771_, 1);
lean_dec(v_unused_1791_);
v___x_1782_ = v_cache_1771_;
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_tokenCache_1780_);
lean_dec(v_cache_1771_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1790_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
lean_ctor_set(v___x_1782_, 1, v_parserCache_1761_);
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_tokenCache_1780_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_parserCache_1761_);
v___x_1785_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v___x_1787_; 
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 3, v___x_1785_);
v___x_1787_ = v___x_1778_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_stxStack_1772_);
lean_ctor_set(v_reuseFailAlloc_1788_, 1, v_lhsPrec_1773_);
lean_ctor_set(v_reuseFailAlloc_1788_, 2, v_pos_1774_);
lean_ctor_set(v_reuseFailAlloc_1788_, 3, v___x_1785_);
lean_ctor_set(v_reuseFailAlloc_1788_, 4, v_errorMsg_1775_);
lean_ctor_set(v_reuseFailAlloc_1788_, 5, v_recoveredErrors_1776_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
lean_object* v___f_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___f_1800_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1800_, 0, v_p_1797_);
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1801_, v___f_1800_, v_a_1798_, v_a_1799_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1803_){
_start:
{
lean_object* v_info_1804_; lean_object* v_fn_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1813_; 
v_info_1804_ = lean_ctor_get(v_p_1803_, 0);
v_fn_1805_ = lean_ctor_get(v_p_1803_, 1);
v_isSharedCheck_1813_ = !lean_is_exclusive(v_p_1803_);
if (v_isSharedCheck_1813_ == 0)
{
v___x_1807_ = v_p_1803_;
v_isShared_1808_ = v_isSharedCheck_1813_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_fn_1805_);
lean_inc(v_info_1804_);
lean_dec(v_p_1803_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1813_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1809_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1809_, 0, v_fn_1805_);
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v___x_1809_);
v___x_1811_ = v___x_1807_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1812_; 
v_reuseFailAlloc_1812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1812_, 0, v_info_1804_);
lean_ctor_set(v_reuseFailAlloc_1812_, 1, v___x_1809_);
v___x_1811_ = v_reuseFailAlloc_1812_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
return v___x_1811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1814_, lean_object* v_p_1815_, lean_object* v_c_1816_, lean_object* v_s_1817_){
_start:
{
lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1818_ = lean_apply_1(v_f_1814_, v_c_1816_);
v___x_1819_ = lean_apply_2(v_p_1815_, v___x_1818_, v_s_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1820_, lean_object* v_p_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___f_1824_; lean_object* v___x_1825_; 
v___f_1824_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1824_, 0, v_f_1820_);
lean_closure_set(v___f_1824_, 1, v_p_1821_);
v___x_1825_ = l_Lean_Parser_withResetCacheFn(v___f_1824_, v_a_1822_, v_a_1823_);
return v___x_1825_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1826_, lean_object* v_x_1827_){
_start:
{
if (lean_obj_tag(v_x_1827_) == 0)
{
uint8_t v___x_1828_; 
v___x_1828_ = 0;
return v___x_1828_;
}
else
{
lean_object* v_key_1829_; lean_object* v_tail_1830_; uint8_t v___x_1831_; 
v_key_1829_ = lean_ctor_get(v_x_1827_, 0);
v_tail_1830_ = lean_ctor_get(v_x_1827_, 2);
v___x_1831_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1829_, v_a_1826_);
if (v___x_1831_ == 0)
{
v_x_1827_ = v_tail_1830_;
goto _start;
}
else
{
return v___x_1831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1833_, lean_object* v_x_1834_){
_start:
{
uint8_t v_res_1835_; lean_object* v_r_1836_; 
v_res_1835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1833_, v_x_1834_);
lean_dec(v_x_1834_);
lean_dec_ref(v_a_1833_);
v_r_1836_ = lean_box(v_res_1835_);
return v_r_1836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1837_, lean_object* v_x_1838_){
_start:
{
if (lean_obj_tag(v_x_1838_) == 0)
{
return v_x_1837_;
}
else
{
lean_object* v_key_1839_; lean_object* v_value_1840_; lean_object* v_tail_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1871_; 
v_key_1839_ = lean_ctor_get(v_x_1838_, 0);
v_value_1840_ = lean_ctor_get(v_x_1838_, 1);
v_tail_1841_ = lean_ctor_get(v_x_1838_, 2);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_x_1838_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1843_ = v_x_1838_;
v_isShared_1844_ = v_isSharedCheck_1871_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_tail_1841_);
lean_inc(v_value_1840_);
lean_inc(v_key_1839_);
lean_dec(v_x_1838_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1871_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_parserName_1845_; lean_object* v_pos_1846_; lean_object* v___x_1847_; uint64_t v___x_1848_; uint64_t v___y_1850_; 
v_parserName_1845_ = lean_ctor_get(v_key_1839_, 1);
v_pos_1846_ = lean_ctor_get(v_key_1839_, 2);
v___x_1847_ = lean_array_get_size(v_x_1837_);
v___x_1848_ = l_String_instHashableRaw_hash(v_pos_1846_);
if (lean_obj_tag(v_parserName_1845_) == 0)
{
uint64_t v___x_1869_; 
v___x_1869_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1850_ = v___x_1869_;
goto v___jp_1849_;
}
else
{
uint64_t v_hash_1870_; 
v_hash_1870_ = lean_ctor_get_uint64(v_parserName_1845_, sizeof(void*)*2);
v___y_1850_ = v_hash_1870_;
goto v___jp_1849_;
}
v___jp_1849_:
{
uint64_t v___x_1851_; uint64_t v___x_1852_; uint64_t v___x_1853_; uint64_t v_fold_1854_; uint64_t v___x_1855_; uint64_t v___x_1856_; uint64_t v___x_1857_; size_t v___x_1858_; size_t v___x_1859_; size_t v___x_1860_; size_t v___x_1861_; size_t v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1851_ = lean_uint64_mix_hash(v___x_1848_, v___y_1850_);
v___x_1852_ = 32ULL;
v___x_1853_ = lean_uint64_shift_right(v___x_1851_, v___x_1852_);
v_fold_1854_ = lean_uint64_xor(v___x_1851_, v___x_1853_);
v___x_1855_ = 16ULL;
v___x_1856_ = lean_uint64_shift_right(v_fold_1854_, v___x_1855_);
v___x_1857_ = lean_uint64_xor(v_fold_1854_, v___x_1856_);
v___x_1858_ = lean_uint64_to_usize(v___x_1857_);
v___x_1859_ = lean_usize_of_nat(v___x_1847_);
v___x_1860_ = ((size_t)1ULL);
v___x_1861_ = lean_usize_sub(v___x_1859_, v___x_1860_);
v___x_1862_ = lean_usize_land(v___x_1858_, v___x_1861_);
v___x_1863_ = lean_array_uget_borrowed(v_x_1837_, v___x_1862_);
lean_inc(v___x_1863_);
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 2, v___x_1863_);
v___x_1865_ = v___x_1843_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v_key_1839_);
lean_ctor_set(v_reuseFailAlloc_1868_, 1, v_value_1840_);
lean_ctor_set(v_reuseFailAlloc_1868_, 2, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
lean_object* v___x_1866_; 
v___x_1866_ = lean_array_uset(v_x_1837_, v___x_1862_, v___x_1865_);
v_x_1837_ = v___x_1866_;
v_x_1838_ = v_tail_1841_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1872_, lean_object* v_source_1873_, lean_object* v_target_1874_){
_start:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = lean_array_get_size(v_source_1873_);
v___x_1876_ = lean_nat_dec_lt(v_i_1872_, v___x_1875_);
if (v___x_1876_ == 0)
{
lean_dec_ref(v_source_1873_);
lean_dec(v_i_1872_);
return v_target_1874_;
}
else
{
lean_object* v_es_1877_; lean_object* v___x_1878_; lean_object* v_source_1879_; lean_object* v_target_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v_es_1877_ = lean_array_fget(v_source_1873_, v_i_1872_);
v___x_1878_ = lean_box(0);
v_source_1879_ = lean_array_fset(v_source_1873_, v_i_1872_, v___x_1878_);
v_target_1880_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1874_, v_es_1877_);
v___x_1881_ = lean_unsigned_to_nat(1u);
v___x_1882_ = lean_nat_add(v_i_1872_, v___x_1881_);
lean_dec(v_i_1872_);
v_i_1872_ = v___x_1882_;
v_source_1873_ = v_source_1879_;
v_target_1874_ = v_target_1880_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1884_){
_start:
{
lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v_nbuckets_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1885_ = lean_array_get_size(v_data_1884_);
v___x_1886_ = lean_unsigned_to_nat(2u);
v_nbuckets_1887_ = lean_nat_mul(v___x_1885_, v___x_1886_);
v___x_1888_ = lean_unsigned_to_nat(0u);
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_mk_array(v_nbuckets_1887_, v___x_1889_);
v___x_1891_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1888_, v_data_1884_, v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1892_, lean_object* v_b_1893_, lean_object* v_x_1894_){
_start:
{
if (lean_obj_tag(v_x_1894_) == 0)
{
lean_dec(v_b_1893_);
lean_dec_ref(v_a_1892_);
return v_x_1894_;
}
else
{
lean_object* v_key_1895_; lean_object* v_value_1896_; lean_object* v_tail_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1909_; 
v_key_1895_ = lean_ctor_get(v_x_1894_, 0);
v_value_1896_ = lean_ctor_get(v_x_1894_, 1);
v_tail_1897_ = lean_ctor_get(v_x_1894_, 2);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_x_1894_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1899_ = v_x_1894_;
v_isShared_1900_ = v_isSharedCheck_1909_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_tail_1897_);
lean_inc(v_value_1896_);
lean_inc(v_key_1895_);
lean_dec(v_x_1894_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1909_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
uint8_t v___x_1901_; 
v___x_1901_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1895_, v_a_1892_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1902_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1892_, v_b_1893_, v_tail_1897_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 2, v___x_1902_);
v___x_1904_ = v___x_1899_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1905_; 
v_reuseFailAlloc_1905_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1905_, 0, v_key_1895_);
lean_ctor_set(v_reuseFailAlloc_1905_, 1, v_value_1896_);
lean_ctor_set(v_reuseFailAlloc_1905_, 2, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1905_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
return v___x_1904_;
}
}
else
{
lean_object* v___x_1907_; 
lean_dec(v_value_1896_);
lean_dec(v_key_1895_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 1, v_b_1893_);
lean_ctor_set(v___x_1899_, 0, v_a_1892_);
v___x_1907_ = v___x_1899_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1892_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_b_1893_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v_tail_1897_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1910_, lean_object* v_a_1911_, lean_object* v_b_1912_){
_start:
{
lean_object* v_size_1913_; lean_object* v_buckets_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1964_; 
v_size_1913_ = lean_ctor_get(v_m_1910_, 0);
v_buckets_1914_ = lean_ctor_get(v_m_1910_, 1);
v_isSharedCheck_1964_ = !lean_is_exclusive(v_m_1910_);
if (v_isSharedCheck_1964_ == 0)
{
v___x_1916_ = v_m_1910_;
v_isShared_1917_ = v_isSharedCheck_1964_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_buckets_1914_);
lean_inc(v_size_1913_);
lean_dec(v_m_1910_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1964_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v_parserName_1918_; lean_object* v_pos_1919_; lean_object* v___x_1920_; uint64_t v___x_1921_; uint64_t v___y_1923_; 
v_parserName_1918_ = lean_ctor_get(v_a_1911_, 1);
v_pos_1919_ = lean_ctor_get(v_a_1911_, 2);
v___x_1920_ = lean_array_get_size(v_buckets_1914_);
v___x_1921_ = l_String_instHashableRaw_hash(v_pos_1919_);
if (lean_obj_tag(v_parserName_1918_) == 0)
{
uint64_t v___x_1962_; 
v___x_1962_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1923_ = v___x_1962_;
goto v___jp_1922_;
}
else
{
uint64_t v_hash_1963_; 
v_hash_1963_ = lean_ctor_get_uint64(v_parserName_1918_, sizeof(void*)*2);
v___y_1923_ = v_hash_1963_;
goto v___jp_1922_;
}
v___jp_1922_:
{
uint64_t v___x_1924_; uint64_t v___x_1925_; uint64_t v___x_1926_; uint64_t v_fold_1927_; uint64_t v___x_1928_; uint64_t v___x_1929_; uint64_t v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; size_t v___x_1933_; size_t v___x_1934_; size_t v___x_1935_; lean_object* v_bkt_1936_; uint8_t v___x_1937_; 
v___x_1924_ = lean_uint64_mix_hash(v___x_1921_, v___y_1923_);
v___x_1925_ = 32ULL;
v___x_1926_ = lean_uint64_shift_right(v___x_1924_, v___x_1925_);
v_fold_1927_ = lean_uint64_xor(v___x_1924_, v___x_1926_);
v___x_1928_ = 16ULL;
v___x_1929_ = lean_uint64_shift_right(v_fold_1927_, v___x_1928_);
v___x_1930_ = lean_uint64_xor(v_fold_1927_, v___x_1929_);
v___x_1931_ = lean_uint64_to_usize(v___x_1930_);
v___x_1932_ = lean_usize_of_nat(v___x_1920_);
v___x_1933_ = ((size_t)1ULL);
v___x_1934_ = lean_usize_sub(v___x_1932_, v___x_1933_);
v___x_1935_ = lean_usize_land(v___x_1931_, v___x_1934_);
v_bkt_1936_ = lean_array_uget_borrowed(v_buckets_1914_, v___x_1935_);
v___x_1937_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1911_, v_bkt_1936_);
if (v___x_1937_ == 0)
{
lean_object* v___x_1938_; lean_object* v_size_x27_1939_; lean_object* v___x_1940_; lean_object* v_buckets_x27_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1938_ = lean_unsigned_to_nat(1u);
v_size_x27_1939_ = lean_nat_add(v_size_1913_, v___x_1938_);
lean_dec(v_size_1913_);
lean_inc(v_bkt_1936_);
v___x_1940_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1940_, 0, v_a_1911_);
lean_ctor_set(v___x_1940_, 1, v_b_1912_);
lean_ctor_set(v___x_1940_, 2, v_bkt_1936_);
v_buckets_x27_1941_ = lean_array_uset(v_buckets_1914_, v___x_1935_, v___x_1940_);
v___x_1942_ = lean_unsigned_to_nat(4u);
v___x_1943_ = lean_nat_mul(v_size_x27_1939_, v___x_1942_);
v___x_1944_ = lean_unsigned_to_nat(3u);
v___x_1945_ = lean_nat_div(v___x_1943_, v___x_1944_);
lean_dec(v___x_1943_);
v___x_1946_ = lean_array_get_size(v_buckets_x27_1941_);
v___x_1947_ = lean_nat_dec_le(v___x_1945_, v___x_1946_);
lean_dec(v___x_1945_);
if (v___x_1947_ == 0)
{
lean_object* v_val_1948_; lean_object* v___x_1950_; 
v_val_1948_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_1941_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v_val_1948_);
lean_ctor_set(v___x_1916_, 0, v_size_x27_1939_);
v___x_1950_ = v___x_1916_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_size_x27_1939_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_val_1948_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
else
{
lean_object* v___x_1953_; 
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v_buckets_x27_1941_);
lean_ctor_set(v___x_1916_, 0, v_size_x27_1939_);
v___x_1953_ = v___x_1916_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_size_x27_1939_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_buckets_x27_1941_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
else
{
lean_object* v___x_1955_; lean_object* v_buckets_x27_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1960_; 
lean_inc(v_bkt_1936_);
v___x_1955_ = lean_box(0);
v_buckets_x27_1956_ = lean_array_uset(v_buckets_1914_, v___x_1935_, v___x_1955_);
v___x_1957_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1911_, v_b_1912_, v_bkt_1936_);
v___x_1958_ = lean_array_uset(v_buckets_x27_1956_, v___x_1935_, v___x_1957_);
if (v_isShared_1917_ == 0)
{
lean_ctor_set(v___x_1916_, 1, v___x_1958_);
v___x_1960_ = v___x_1916_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_size_1913_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_1965_, lean_object* v_x_1966_){
_start:
{
if (lean_obj_tag(v_x_1966_) == 0)
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_box(0);
return v___x_1967_;
}
else
{
lean_object* v_key_1968_; lean_object* v_value_1969_; lean_object* v_tail_1970_; uint8_t v___x_1971_; 
v_key_1968_ = lean_ctor_get(v_x_1966_, 0);
v_value_1969_ = lean_ctor_get(v_x_1966_, 1);
v_tail_1970_ = lean_ctor_get(v_x_1966_, 2);
v___x_1971_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1968_, v_a_1965_);
if (v___x_1971_ == 0)
{
v_x_1966_ = v_tail_1970_;
goto _start;
}
else
{
lean_object* v___x_1973_; 
lean_inc(v_value_1969_);
v___x_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1973_, 0, v_value_1969_);
return v___x_1973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_1974_, lean_object* v_x_1975_){
_start:
{
lean_object* v_res_1976_; 
v_res_1976_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_1974_, v_x_1975_);
lean_dec(v_x_1975_);
lean_dec_ref(v_a_1974_);
return v_res_1976_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_1977_, lean_object* v_a_1978_){
_start:
{
lean_object* v_buckets_1979_; lean_object* v_parserName_1980_; lean_object* v_pos_1981_; lean_object* v___x_1982_; uint64_t v___x_1983_; uint64_t v___y_1985_; 
v_buckets_1979_ = lean_ctor_get(v_m_1977_, 1);
v_parserName_1980_ = lean_ctor_get(v_a_1978_, 1);
v_pos_1981_ = lean_ctor_get(v_a_1978_, 2);
v___x_1982_ = lean_array_get_size(v_buckets_1979_);
v___x_1983_ = l_String_instHashableRaw_hash(v_pos_1981_);
if (lean_obj_tag(v_parserName_1980_) == 0)
{
uint64_t v___x_2000_; 
v___x_2000_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1985_ = v___x_2000_;
goto v___jp_1984_;
}
else
{
uint64_t v_hash_2001_; 
v_hash_2001_ = lean_ctor_get_uint64(v_parserName_1980_, sizeof(void*)*2);
v___y_1985_ = v_hash_2001_;
goto v___jp_1984_;
}
v___jp_1984_:
{
uint64_t v___x_1986_; uint64_t v___x_1987_; uint64_t v___x_1988_; uint64_t v_fold_1989_; uint64_t v___x_1990_; uint64_t v___x_1991_; uint64_t v___x_1992_; size_t v___x_1993_; size_t v___x_1994_; size_t v___x_1995_; size_t v___x_1996_; size_t v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1986_ = lean_uint64_mix_hash(v___x_1983_, v___y_1985_);
v___x_1987_ = 32ULL;
v___x_1988_ = lean_uint64_shift_right(v___x_1986_, v___x_1987_);
v_fold_1989_ = lean_uint64_xor(v___x_1986_, v___x_1988_);
v___x_1990_ = 16ULL;
v___x_1991_ = lean_uint64_shift_right(v_fold_1989_, v___x_1990_);
v___x_1992_ = lean_uint64_xor(v_fold_1989_, v___x_1991_);
v___x_1993_ = lean_uint64_to_usize(v___x_1992_);
v___x_1994_ = lean_usize_of_nat(v___x_1982_);
v___x_1995_ = ((size_t)1ULL);
v___x_1996_ = lean_usize_sub(v___x_1994_, v___x_1995_);
v___x_1997_ = lean_usize_land(v___x_1993_, v___x_1996_);
v___x_1998_ = lean_array_uget_borrowed(v_buckets_1979_, v___x_1997_);
v___x_1999_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_1978_, v___x_1998_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2002_, v_a_2003_);
lean_dec_ref(v_a_2003_);
lean_dec_ref(v_m_2002_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_2005_, lean_object* v_p_2006_, lean_object* v_c_2007_, lean_object* v_s_2008_){
_start:
{
lean_object* v_cache_2009_; lean_object* v_toCacheableParserContext_2010_; lean_object* v_stxStack_2011_; lean_object* v_pos_2012_; lean_object* v_recoveredErrors_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2062_; 
v_cache_2009_ = lean_ctor_get(v_s_2008_, 3);
lean_inc_ref(v_cache_2009_);
v_toCacheableParserContext_2010_ = lean_ctor_get(v_c_2007_, 2);
v_stxStack_2011_ = lean_ctor_get(v_s_2008_, 0);
v_pos_2012_ = lean_ctor_get(v_s_2008_, 2);
v_recoveredErrors_2013_ = lean_ctor_get(v_s_2008_, 5);
v_isSharedCheck_2062_ = !lean_is_exclusive(v_s_2008_);
if (v_isSharedCheck_2062_ == 0)
{
lean_object* v_unused_2063_; lean_object* v_unused_2064_; lean_object* v_unused_2065_; 
v_unused_2063_ = lean_ctor_get(v_s_2008_, 4);
lean_dec(v_unused_2063_);
v_unused_2064_ = lean_ctor_get(v_s_2008_, 3);
lean_dec(v_unused_2064_);
v_unused_2065_ = lean_ctor_get(v_s_2008_, 1);
lean_dec(v_unused_2065_);
v___x_2015_ = v_s_2008_;
v_isShared_2016_ = v_isSharedCheck_2062_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_recoveredErrors_2013_);
lean_inc(v_pos_2012_);
lean_inc(v_stxStack_2011_);
lean_dec(v_s_2008_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2062_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_parserCache_2017_; lean_object* v_key_2018_; lean_object* v___x_2019_; 
v_parserCache_2017_ = lean_ctor_get(v_cache_2009_, 1);
lean_inc(v_pos_2012_);
lean_inc_ref(v_toCacheableParserContext_2010_);
v_key_2018_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_2018_, 0, v_toCacheableParserContext_2010_);
lean_ctor_set(v_key_2018_, 1, v_parserName_2005_);
lean_ctor_set(v_key_2018_, 2, v_pos_2012_);
v___x_2019_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_2017_, v_key_2018_);
if (lean_obj_tag(v___x_2019_) == 1)
{
lean_object* v_val_2020_; lean_object* v_stx_2021_; lean_object* v_lhsPrec_2022_; lean_object* v_newPos_2023_; lean_object* v_errorMsg_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_dec_ref(v_key_2018_);
lean_dec(v_pos_2012_);
lean_dec_ref(v_c_2007_);
lean_dec_ref(v_p_2006_);
v_val_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_val_2020_);
lean_dec_ref(v___x_2019_);
v_stx_2021_ = lean_ctor_get(v_val_2020_, 0);
lean_inc(v_stx_2021_);
v_lhsPrec_2022_ = lean_ctor_get(v_val_2020_, 1);
lean_inc(v_lhsPrec_2022_);
v_newPos_2023_ = lean_ctor_get(v_val_2020_, 2);
lean_inc(v_newPos_2023_);
v_errorMsg_2024_ = lean_ctor_get(v_val_2020_, 3);
lean_inc(v_errorMsg_2024_);
lean_dec(v_val_2020_);
v___x_2025_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_2011_, v_stx_2021_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 4, v_errorMsg_2024_);
lean_ctor_set(v___x_2015_, 2, v_newPos_2023_);
lean_ctor_set(v___x_2015_, 1, v_lhsPrec_2022_);
lean_ctor_set(v___x_2015_, 0, v___x_2025_);
v___x_2027_ = v___x_2015_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_lhsPrec_2022_);
lean_ctor_set(v_reuseFailAlloc_2028_, 2, v_newPos_2023_);
lean_ctor_set(v_reuseFailAlloc_2028_, 3, v_cache_2009_);
lean_ctor_set(v_reuseFailAlloc_2028_, 4, v_errorMsg_2024_);
lean_ctor_set(v_reuseFailAlloc_2028_, 5, v_recoveredErrors_2013_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
else
{
lean_object* v_raw_2029_; lean_object* v_initStackSz_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
lean_dec(v___x_2019_);
v_raw_2029_ = lean_ctor_get(v_stxStack_2011_, 0);
v_initStackSz_2030_ = lean_array_get_size(v_raw_2029_);
v___x_2031_ = lean_unsigned_to_nat(0u);
v___x_2032_ = lean_box(0);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 4, v___x_2032_);
lean_ctor_set(v___x_2015_, 1, v___x_2031_);
v___x_2034_ = v___x_2015_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_stxStack_2011_);
lean_ctor_set(v_reuseFailAlloc_2061_, 1, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2061_, 2, v_pos_2012_);
lean_ctor_set(v_reuseFailAlloc_2061_, 3, v_cache_2009_);
lean_ctor_set(v_reuseFailAlloc_2061_, 4, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2061_, 5, v_recoveredErrors_2013_);
v___x_2034_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v_s_2035_; lean_object* v_cache_2036_; lean_object* v_stxStack_2037_; lean_object* v_lhsPrec_2038_; lean_object* v_pos_2039_; lean_object* v_errorMsg_2040_; lean_object* v_recoveredErrors_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2060_; 
v_s_2035_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_2030_, v_p_2006_, v_c_2007_, v___x_2034_);
v_cache_2036_ = lean_ctor_get(v_s_2035_, 3);
v_stxStack_2037_ = lean_ctor_get(v_s_2035_, 0);
v_lhsPrec_2038_ = lean_ctor_get(v_s_2035_, 1);
v_pos_2039_ = lean_ctor_get(v_s_2035_, 2);
v_errorMsg_2040_ = lean_ctor_get(v_s_2035_, 4);
v_recoveredErrors_2041_ = lean_ctor_get(v_s_2035_, 5);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_s_2035_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2043_ = v_s_2035_;
v_isShared_2044_ = v_isSharedCheck_2060_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_recoveredErrors_2041_);
lean_inc(v_errorMsg_2040_);
lean_inc(v_cache_2036_);
lean_inc(v_pos_2039_);
lean_inc(v_lhsPrec_2038_);
lean_inc(v_stxStack_2037_);
lean_dec(v_s_2035_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2060_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v_tokenCache_2045_; lean_object* v_parserCache_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2059_; 
v_tokenCache_2045_ = lean_ctor_get(v_cache_2036_, 0);
v_parserCache_2046_ = lean_ctor_get(v_cache_2036_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_cache_2036_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2048_ = v_cache_2036_;
v_isShared_2049_ = v_isSharedCheck_2059_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_parserCache_2046_);
lean_inc(v_tokenCache_2045_);
lean_dec(v_cache_2036_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2059_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2054_; 
v___x_2050_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2037_);
lean_inc(v_errorMsg_2040_);
lean_inc(v_pos_2039_);
lean_inc(v_lhsPrec_2038_);
v___x_2051_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v_lhsPrec_2038_);
lean_ctor_set(v___x_2051_, 2, v_pos_2039_);
lean_ctor_set(v___x_2051_, 3, v_errorMsg_2040_);
v___x_2052_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_2046_, v_key_2018_, v___x_2051_);
if (v_isShared_2049_ == 0)
{
lean_ctor_set(v___x_2048_, 1, v___x_2052_);
v___x_2054_ = v___x_2048_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_tokenCache_2045_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v___x_2052_);
v___x_2054_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
lean_object* v___x_2056_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 3, v___x_2054_);
v___x_2056_ = v___x_2043_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_stxStack_2037_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_lhsPrec_2038_);
lean_ctor_set(v_reuseFailAlloc_2057_, 2, v_pos_2039_);
lean_ctor_set(v_reuseFailAlloc_2057_, 3, v___x_2054_);
lean_ctor_set(v_reuseFailAlloc_2057_, 4, v_errorMsg_2040_);
lean_ctor_set(v_reuseFailAlloc_2057_, 5, v_recoveredErrors_2041_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2066_, lean_object* v_m_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2067_, v_a_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2070_, lean_object* v_m_2071_, lean_object* v_a_2072_){
_start:
{
lean_object* v_res_2073_; 
v_res_2073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2070_, v_m_2071_, v_a_2072_);
lean_dec_ref(v_a_2072_);
lean_dec_ref(v_m_2071_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2074_, lean_object* v_m_2075_, lean_object* v_a_2076_, lean_object* v_b_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2075_, v_a_2076_, v_b_2077_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2079_, lean_object* v_a_2080_, lean_object* v_x_2081_){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2080_, v_x_2081_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2083_, lean_object* v_a_2084_, lean_object* v_x_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2083_, v_a_2084_, v_x_2085_);
lean_dec(v_x_2085_);
lean_dec_ref(v_a_2084_);
return v_res_2086_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2087_, lean_object* v_a_2088_, lean_object* v_x_2089_){
_start:
{
uint8_t v___x_2090_; 
v___x_2090_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2088_, v_x_2089_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2091_, lean_object* v_a_2092_, lean_object* v_x_2093_){
_start:
{
uint8_t v_res_2094_; lean_object* v_r_2095_; 
v_res_2094_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2091_, v_a_2092_, v_x_2093_);
lean_dec(v_x_2093_);
lean_dec_ref(v_a_2092_);
v_r_2095_ = lean_box(v_res_2094_);
return v_r_2095_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2096_, lean_object* v_data_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2099_, lean_object* v_a_2100_, lean_object* v_b_2101_, lean_object* v_x_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2100_, v_b_2101_, v_x_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2104_, lean_object* v_i_2105_, lean_object* v_source_2106_, lean_object* v_target_2107_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2105_, v_source_2106_, v_target_2107_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2109_, lean_object* v_x_2110_, lean_object* v_x_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2110_, v_x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2113_, lean_object* v_p_2114_){
_start:
{
lean_object* v_info_2115_; lean_object* v_fn_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2124_; 
v_info_2115_ = lean_ctor_get(v_p_2114_, 0);
v_fn_2116_ = lean_ctor_get(v_p_2114_, 1);
v_isSharedCheck_2124_ = !lean_is_exclusive(v_p_2114_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2118_ = v_p_2114_;
v_isShared_2119_ = v_isSharedCheck_2124_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_fn_2116_);
lean_inc(v_info_2115_);
lean_dec(v_p_2114_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2124_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2120_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2120_, 0, v_parserName_2113_);
lean_closure_set(v___x_2120_, 1, v_fn_2116_);
if (v_isShared_2119_ == 0)
{
lean_ctor_set(v___x_2118_, 1, v___x_2120_);
v___x_2122_ = v___x_2118_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_info_2115_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2133_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2134_ = l_Lean_addBuiltinDocString(v___x_2132_, v___x_2133_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2141_, lean_object* v_ictx_2142_, lean_object* v_pmctx_2143_, lean_object* v_tokens_2144_, lean_object* v_s_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2146_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__0));
v___x_2147_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2147_, 0, v_ictx_2142_);
lean_ctor_set(v___x_2147_, 1, v_pmctx_2143_);
lean_ctor_set(v___x_2147_, 2, v___x_2146_);
lean_ctor_set(v___x_2147_, 3, v_tokens_2144_);
v___x_2148_ = lean_apply_2(v_p_2141_, v___x_2147_, v_s_2145_);
return v___x_2148_;
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
