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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_String_decidableLT___boxed(lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
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
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* l_Lean_mkErrorStringWithPos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
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
static const lean_closure_object l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_decidableLT___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Parser_Error_toString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "; "};
static const lean_object* l_Lean_Parser_Error_toString___closed__0 = (const lean_object*)&l_Lean_Parser_Error_toString___closed__0_value;
static const lean_string_object l_Lean_Parser_Error_toString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "expected "};
static const lean_object* l_Lean_Parser_Error_toString___closed__1 = (const lean_object*)&l_Lean_Parser_Error_toString___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__0;
static lean_once_cell_t l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instInhabitedParserInfo_default___closed__0 = (const lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value;
static const lean_closure_object l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Parser_instInhabitedParserInfo_default___closed__1 = (const lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value;
static const lean_ctor_object l_Lean_Parser_instInhabitedParserInfo_default___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__0_value),((lean_object*)&l_Lean_Parser_instInhabitedParserInfo_default___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
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
static const lean_string_object l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "withCache"};
static const lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0 = (const lean_object*)&l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value;
static const lean_ctor_object l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(25, 241, 193, 7, 69, 147, 159, 180)}};
static const lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1 = (const lean_object*)&l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1_value;
static const lean_string_object l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 542, .m_capacity = 542, .m_length = 541, .m_data = "Run `p` and record result in parser cache for any further invocation with this `parserName`, parser context, and parser state.\n`p` cannot access syntax stack elements pushed before the invocation in order to make caching independent of parser history.\nAs this excludes trailing parsers from being cached, we also reset `lhsPrec`, which is not read but set by leading parsers, to 0\nin order to increase cache hits. Finally, `errorMsg` is also reset to `none` as a leading parser should not be called in the first\nplace if there was an error.\n"};
static const lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2 = (const lean_object*)&l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
LEAN_EXPORT lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_as_600_, lean_object* v_lo_601_, lean_object* v_hi_602_){
_start:
{
uint8_t v___x_603_; 
v___x_603_ = lean_nat_dec_lt(v_lo_601_, v_hi_602_);
if (v___x_603_ == 0)
{
lean_dec(v_lo_601_);
return v_as_600_;
}
else
{
lean_object* v___f_604_; lean_object* v___x_605_; lean_object* v_fst_606_; lean_object* v_snd_607_; uint8_t v___x_608_; 
v___f_604_ = ((lean_object*)(l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___closed__0));
lean_inc(v_lo_601_);
v___x_605_ = l_Array_qpartition___redArg(v_as_600_, v___f_604_, v_lo_601_, v_hi_602_);
v_fst_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_fst_606_);
v_snd_607_ = lean_ctor_get(v___x_605_, 1);
lean_inc(v_snd_607_);
lean_dec_ref(v___x_605_);
v___x_608_ = lean_nat_dec_le(v_hi_602_, v_fst_606_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_snd_607_, v_lo_601_, v_fst_606_);
v___x_610_ = lean_unsigned_to_nat(1u);
v___x_611_ = lean_nat_add(v_fst_606_, v___x_610_);
lean_dec(v_fst_606_);
v_as_600_ = v___x_609_;
v_lo_601_ = v___x_611_;
goto _start;
}
else
{
lean_dec(v_fst_606_);
lean_dec(v_lo_601_);
return v_snd_607_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_as_613_, lean_object* v_lo_614_, lean_object* v_hi_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_as_613_, v_lo_614_, v_hi_615_);
lean_dec(v_hi_615_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_619_){
_start:
{
lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v_unexpected_652_; lean_object* v_expected_653_; lean_object* v___y_655_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_unexpected_652_ = lean_ctor_get(v_e_619_, 1);
lean_inc_ref(v_unexpected_652_);
v_expected_653_ = lean_ctor_get(v_e_619_, 2);
lean_inc(v_expected_653_);
lean_dec_ref(v_e_619_);
v___x_665_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_666_ = lean_string_dec_eq(v_unexpected_652_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_667_ = lean_box(0);
v___x_668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_668_, 0, v_unexpected_652_);
lean_ctor_set(v___x_668_, 1, v___x_667_);
v___y_655_ = v___x_668_;
goto v___jp_654_;
}
else
{
lean_object* v___x_669_; 
lean_dec_ref(v_unexpected_652_);
v___x_669_ = lean_box(0);
v___y_655_ = v___x_669_;
goto v___jp_654_;
}
v___jp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_624_ = l_List_appendTR___redArg(v___y_621_, v___y_622_);
v___x_625_ = l_String_intercalate(v___x_623_, v___x_624_);
return v___x_625_;
}
v___jp_626_:
{
lean_object* v___x_630_; lean_object* v_expected_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_630_ = lean_array_to_list(v___y_629_);
v_expected_631_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_630_);
v___x_632_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_633_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_631_);
v___x_634_ = lean_string_append(v___x_632_, v___x_633_);
lean_dec_ref(v___x_633_);
v___x_635_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_635_, 0, v___x_634_);
lean_ctor_set(v___x_635_, 1, v___y_627_);
v___y_621_ = v___y_628_;
v___y_622_ = v___x_635_;
goto v___jp_620_;
}
v___jp_636_:
{
lean_object* v___x_643_; 
lean_dec(v___y_641_);
v___x_643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_639_, v___y_637_, v___y_642_);
lean_dec(v___y_642_);
v___y_627_ = v___y_638_;
v___y_628_ = v___y_640_;
v___y_629_ = v___x_643_;
goto v___jp_626_;
}
v___jp_644_:
{
uint8_t v___x_651_; 
v___x_651_ = lean_nat_dec_le(v___y_650_, v___y_645_);
if (v___x_651_ == 0)
{
lean_dec(v___y_645_);
lean_inc(v___y_650_);
v___y_637_ = v___y_650_;
v___y_638_ = v___y_646_;
v___y_639_ = v___y_647_;
v___y_640_ = v___y_648_;
v___y_641_ = v___y_649_;
v___y_642_ = v___y_650_;
goto v___jp_636_;
}
else
{
v___y_637_ = v___y_650_;
v___y_638_ = v___y_646_;
v___y_639_ = v___y_647_;
v___y_640_ = v___y_648_;
v___y_641_ = v___y_649_;
v___y_642_ = v___y_645_;
goto v___jp_636_;
}
}
v___jp_654_:
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = lean_box(0);
v___x_657_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_653_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_658_ = lean_array_mk(v_expected_653_);
v___x_659_ = lean_array_get_size(v___x_658_);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_nat_dec_eq(v___x_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_662_ = lean_unsigned_to_nat(1u);
v___x_663_ = lean_nat_sub(v___x_659_, v___x_662_);
v___x_664_ = lean_nat_dec_le(v___x_660_, v___x_663_);
if (v___x_664_ == 0)
{
lean_inc(v___x_663_);
v___y_645_ = v___x_663_;
v___y_646_ = v___x_656_;
v___y_647_ = v___x_658_;
v___y_648_ = v___y_655_;
v___y_649_ = v___x_659_;
v___y_650_ = v___x_663_;
goto v___jp_644_;
}
else
{
v___y_645_ = v___x_663_;
v___y_646_ = v___x_656_;
v___y_647_ = v___x_658_;
v___y_648_ = v___y_655_;
v___y_649_ = v___x_659_;
v___y_650_ = v___x_660_;
goto v___jp_644_;
}
}
else
{
v___y_627_ = v___x_656_;
v___y_628_ = v___y_655_;
v___y_629_ = v___x_658_;
goto v___jp_626_;
}
}
else
{
lean_dec(v_expected_653_);
v___y_621_ = v___y_655_;
v___y_622_ = v___x_656_;
goto v___jp_620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_670_, lean_object* v_as_671_, lean_object* v_lo_672_, lean_object* v_hi_673_, lean_object* v_w_674_, lean_object* v_hlo_675_, lean_object* v_hhi_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_as_671_, v_lo_672_, v_hi_673_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_678_, lean_object* v_as_679_, lean_object* v_lo_680_, lean_object* v_hi_681_, lean_object* v_w_682_, lean_object* v_hlo_683_, lean_object* v_hhi_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_678_, v_as_679_, v_lo_680_, v_hi_681_, v_w_682_, v_hlo_683_, v_hhi_684_);
lean_dec(v_hi_681_);
lean_dec(v_n_678_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_688_, lean_object* v_e_u2082_689_){
_start:
{
lean_object* v_unexpectedTk_690_; lean_object* v_unexpected_691_; lean_object* v_expected_692_; lean_object* v___y_694_; lean_object* v___x_706_; uint8_t v___x_707_; 
v_unexpectedTk_690_ = lean_ctor_get(v_e_u2082_689_, 0);
lean_inc(v_unexpectedTk_690_);
v_unexpected_691_ = lean_ctor_get(v_e_u2082_689_, 1);
lean_inc_ref(v_unexpected_691_);
v_expected_692_ = lean_ctor_get(v_e_u2082_689_, 2);
lean_inc(v_expected_692_);
lean_dec_ref(v_e_u2082_689_);
v___x_706_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_707_ = lean_string_dec_eq(v_unexpected_691_, v___x_706_);
if (v___x_707_ == 0)
{
v___y_694_ = v_unexpected_691_;
goto v___jp_693_;
}
else
{
lean_object* v_unexpected_708_; 
lean_dec_ref(v_unexpected_691_);
v_unexpected_708_ = lean_ctor_get(v_e_u2081_688_, 1);
lean_inc_ref(v_unexpected_708_);
v___y_694_ = v_unexpected_708_;
goto v___jp_693_;
}
v___jp_693_:
{
lean_object* v_expected_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_703_; 
v_expected_695_ = lean_ctor_get(v_e_u2081_688_, 2);
v_isSharedCheck_703_ = !lean_is_exclusive(v_e_u2081_688_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; lean_object* v_unused_705_; 
v_unused_704_ = lean_ctor_get(v_e_u2081_688_, 1);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v_e_u2081_688_, 0);
lean_dec(v_unused_705_);
v___x_697_ = v_e_u2081_688_;
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_expected_695_);
lean_dec(v_e_u2081_688_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_703_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
v___x_699_ = l_List_appendTR___redArg(v_expected_695_, v_expected_692_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 2, v___x_699_);
lean_ctor_set(v___x_697_, 1, v___y_694_);
lean_ctor_set(v___x_697_, 0, v_unexpectedTk_690_);
v___x_701_ = v___x_697_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_unexpectedTk_690_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v___y_694_);
lean_ctor_set(v_reuseFailAlloc_702_, 2, v___x_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_709_, lean_object* v_x_710_){
_start:
{
lean_object* v_toCacheableParserContext_711_; lean_object* v_parserName_712_; lean_object* v_pos_713_; lean_object* v_toCacheableParserContext_714_; lean_object* v_parserName_715_; lean_object* v_pos_716_; uint8_t v___x_717_; 
v_toCacheableParserContext_711_ = lean_ctor_get(v_x_709_, 0);
v_parserName_712_ = lean_ctor_get(v_x_709_, 1);
v_pos_713_ = lean_ctor_get(v_x_709_, 2);
v_toCacheableParserContext_714_ = lean_ctor_get(v_x_710_, 0);
v_parserName_715_ = lean_ctor_get(v_x_710_, 1);
v_pos_716_ = lean_ctor_get(v_x_710_, 2);
v___x_717_ = l_Lean_Parser_instBEqCacheableParserContext_beq(v_toCacheableParserContext_711_, v_toCacheableParserContext_714_);
if (v___x_717_ == 0)
{
return v___x_717_;
}
else
{
uint8_t v___x_718_; 
v___x_718_ = lean_name_eq(v_parserName_712_, v_parserName_715_);
if (v___x_718_ == 0)
{
return v___x_718_;
}
else
{
uint8_t v___x_719_; 
v___x_719_ = lean_nat_dec_eq(v_pos_713_, v_pos_716_);
return v___x_719_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
uint8_t v_res_722_; lean_object* v_r_723_; 
v_res_722_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_720_, v_x_721_);
lean_dec_ref(v_x_721_);
lean_dec_ref(v_x_720_);
v_r_723_ = lean_box(v_res_722_);
return v_r_723_;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* v_k_726_){
_start:
{
lean_object* v_parserName_727_; lean_object* v_pos_728_; uint64_t v___x_729_; 
v_parserName_727_ = lean_ctor_get(v_k_726_, 1);
v_pos_728_ = lean_ctor_get(v_k_726_, 2);
v___x_729_ = l_String_instHashableRaw_hash(v_pos_728_);
if (lean_obj_tag(v_parserName_727_) == 0)
{
uint64_t v___x_730_; uint64_t v___x_731_; 
v___x_730_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_731_ = lean_uint64_mix_hash(v___x_729_, v___x_730_);
return v___x_731_;
}
else
{
uint64_t v_hash_732_; uint64_t v___x_733_; 
v_hash_732_ = lean_ctor_get_uint64(v_parserName_727_, sizeof(void*)*2);
v___x_733_ = lean_uint64_mix_hash(v___x_729_, v_hash_732_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* v_k_734_){
_start:
{
uint64_t v_res_735_; lean_object* v_r_736_; 
v_res_735_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_734_);
lean_dec_ref(v_k_734_);
v_r_736_ = lean_box_uint64(v_res_735_);
return v_r_736_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0(void){
_start:
{
uint32_t v___x_739_; lean_object* v___x_740_; 
v___x_739_ = 32;
v___x_740_ = l_Char_utf8Size(v___x_739_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_741_ = lean_box(0);
v___x_742_ = lean_unsigned_to_nat(16u);
v___x_743_ = lean_mk_array(v___x_742_, v___x_741_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__2(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_747_){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v___x_748_ = lean_string_utf8_byte_size(v_input_747_);
v___x_749_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_750_ = lean_nat_add(v___x_748_, v___x_749_);
v___x_751_ = lean_unsigned_to_nat(0u);
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_753_, 0, v___x_750_);
lean_ctor_set(v___x_753_, 1, v___x_751_);
lean_ctor_set(v___x_753_, 2, v___x_752_);
v___x_754_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___x_753_);
lean_ctor_set(v___x_755_, 1, v___x_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Parser_initCacheForInput(v_input_756_);
lean_dec_ref(v_input_756_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_758_){
_start:
{
lean_object* v_raw_759_; lean_object* v_drop_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v_raw_759_ = lean_ctor_get(v_stack_758_, 0);
lean_inc_ref(v_raw_759_);
v_drop_760_ = lean_ctor_get(v_stack_758_, 1);
lean_inc(v_drop_760_);
lean_dec_ref(v_stack_758_);
v___x_761_ = lean_array_get_size(v_raw_759_);
v___x_762_ = l_Array_toSubarray___redArg(v_raw_759_, v_drop_760_, v___x_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_769_){
_start:
{
lean_object* v_raw_770_; lean_object* v_drop_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v_raw_770_ = lean_ctor_get(v_stack_769_, 0);
v_drop_771_ = lean_ctor_get(v_stack_769_, 1);
v___x_772_ = lean_array_get_size(v_raw_770_);
v___x_773_ = lean_nat_sub(v___x_772_, v_drop_771_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Parser_SyntaxStack_size(v_stack_774_);
lean_dec_ref(v_stack_774_);
return v_res_775_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_776_){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; uint8_t v___x_779_; 
v___x_777_ = l_Lean_Parser_SyntaxStack_size(v_stack_776_);
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_nat_dec_eq(v___x_777_, v___x_778_);
lean_dec(v___x_777_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_780_){
_start:
{
uint8_t v_res_781_; lean_object* v_r_782_; 
v_res_781_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_780_);
lean_dec_ref(v_stack_780_);
v_r_782_ = lean_box(v_res_781_);
return v_r_782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_783_, lean_object* v_n_784_){
_start:
{
lean_object* v_raw_785_; lean_object* v_drop_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_795_; 
v_raw_785_ = lean_ctor_get(v_stack_783_, 0);
v_drop_786_ = lean_ctor_get(v_stack_783_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_stack_783_);
if (v_isSharedCheck_795_ == 0)
{
v___x_788_ = v_stack_783_;
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_drop_786_);
lean_inc(v_raw_785_);
lean_dec(v_stack_783_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_795_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_793_; 
v___x_790_ = lean_nat_add(v_drop_786_, v_n_784_);
v___x_791_ = l_Array_shrink___redArg(v_raw_785_, v___x_790_);
lean_dec(v___x_790_);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_791_);
v___x_793_ = v___x_788_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_794_; 
v_reuseFailAlloc_794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_794_, 0, v___x_791_);
lean_ctor_set(v_reuseFailAlloc_794_, 1, v_drop_786_);
v___x_793_ = v_reuseFailAlloc_794_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
return v___x_793_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_796_, lean_object* v_n_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_796_, v_n_797_);
lean_dec(v_n_797_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_raw_801_; lean_object* v_drop_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_810_; 
v_raw_801_ = lean_ctor_get(v_stack_799_, 0);
v_drop_802_ = lean_ctor_get(v_stack_799_, 1);
v_isSharedCheck_810_ = !lean_is_exclusive(v_stack_799_);
if (v_isSharedCheck_810_ == 0)
{
v___x_804_ = v_stack_799_;
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_drop_802_);
lean_inc(v_raw_801_);
lean_dec(v_stack_799_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_810_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v___x_806_; lean_object* v___x_808_; 
v___x_806_ = lean_array_push(v_raw_801_, v_a_800_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_806_);
v___x_808_ = v___x_804_;
goto v_reusejp_807_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_806_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_drop_802_);
v___x_808_ = v_reuseFailAlloc_809_;
goto v_reusejp_807_;
}
v_reusejp_807_:
{
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_811_){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = l_Lean_Parser_SyntaxStack_size(v_stack_811_);
v___x_814_ = lean_nat_dec_lt(v___x_812_, v___x_813_);
lean_dec(v___x_813_);
if (v___x_814_ == 0)
{
return v_stack_811_;
}
else
{
lean_object* v_raw_815_; lean_object* v_drop_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_824_; 
v_raw_815_ = lean_ctor_get(v_stack_811_, 0);
v_drop_816_ = lean_ctor_get(v_stack_811_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_stack_811_);
if (v_isSharedCheck_824_ == 0)
{
v___x_818_ = v_stack_811_;
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_drop_816_);
lean_inc(v_raw_815_);
lean_dec(v_stack_811_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_824_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_820_; lean_object* v___x_822_; 
v___x_820_ = lean_array_pop(v_raw_815_);
if (v_isShared_819_ == 0)
{
lean_ctor_set(v___x_818_, 0, v___x_820_);
v___x_822_ = v___x_818_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v___x_820_);
lean_ctor_set(v_reuseFailAlloc_823_, 1, v_drop_816_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_825_){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = lean_box(0);
v___x_827_ = lean_panic_fn(v___x_826_, v_msg_825_);
return v___x_827_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_831_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_832_ = lean_unsigned_to_nat(4u);
v___x_833_ = lean_unsigned_to_nat(305u);
v___x_834_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_835_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_836_ = l_mkPanicMessageWithDecl(v___x_835_, v___x_834_, v___x_833_, v___x_832_, v___x_831_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_837_){
_start:
{
lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = l_Lean_Parser_SyntaxStack_size(v_stack_837_);
v___x_840_ = lean_nat_dec_lt(v___x_838_, v___x_839_);
lean_dec(v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; 
v___x_841_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_842_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_841_);
return v___x_842_;
}
else
{
lean_object* v_raw_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_raw_843_ = lean_ctor_get(v_stack_837_, 0);
v___x_844_ = lean_box(0);
v___x_845_ = lean_array_get_size(v_raw_843_);
v___x_846_ = lean_unsigned_to_nat(1u);
v___x_847_ = lean_nat_sub(v___x_845_, v___x_846_);
v___x_848_ = lean_array_get_borrowed(v___x_844_, v_raw_843_, v___x_847_);
lean_dec(v___x_847_);
lean_inc(v___x_848_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Lean_Parser_SyntaxStack_back(v_stack_849_);
lean_dec_ref(v_stack_849_);
return v_res_850_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_853_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_854_ = lean_unsigned_to_nat(4u);
v___x_855_ = lean_unsigned_to_nat(311u);
v___x_856_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_857_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_858_ = l_mkPanicMessageWithDecl(v___x_857_, v___x_856_, v___x_855_, v___x_854_, v___x_853_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_859_, lean_object* v_i_860_){
_start:
{
lean_object* v___x_861_; uint8_t v___x_862_; 
v___x_861_ = l_Lean_Parser_SyntaxStack_size(v_stack_859_);
v___x_862_ = lean_nat_dec_lt(v_i_860_, v___x_861_);
lean_dec(v___x_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_864_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_863_);
return v___x_864_;
}
else
{
lean_object* v_raw_865_; lean_object* v_drop_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_raw_865_ = lean_ctor_get(v_stack_859_, 0);
v_drop_866_ = lean_ctor_get(v_stack_859_, 1);
v___x_867_ = lean_box(0);
v___x_868_ = lean_nat_add(v_drop_866_, v_i_860_);
v___x_869_ = lean_array_get_borrowed(v___x_867_, v_raw_865_, v___x_868_);
lean_dec(v___x_868_);
lean_inc(v___x_869_);
return v___x_869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_870_, lean_object* v_i_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_870_, v_i_871_);
lean_dec(v_i_871_);
lean_dec_ref(v_stack_870_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_873_, lean_object* v_start_874_, lean_object* v_stop_875_){
_start:
{
lean_object* v_raw_876_; lean_object* v_drop_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_raw_876_ = lean_ctor_get(v_stack_873_, 0);
v_drop_877_ = lean_ctor_get(v_stack_873_, 1);
v___x_878_ = lean_nat_add(v_drop_877_, v_start_874_);
v___x_879_ = lean_nat_add(v_drop_877_, v_stop_875_);
v___x_880_ = l_Array_extract___redArg(v_raw_876_, v___x_878_, v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_881_, lean_object* v_start_882_, lean_object* v_stop_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Lean_Parser_SyntaxStack_extract(v_stack_881_, v_start_882_, v_stop_883_);
lean_dec(v_stop_883_);
lean_dec(v_start_882_);
lean_dec_ref(v_stack_881_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_885_, lean_object* v_stxs_886_){
_start:
{
lean_object* v_raw_887_; lean_object* v_drop_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_896_; 
v_raw_887_ = lean_ctor_get(v_stack_885_, 0);
v_drop_888_ = lean_ctor_get(v_stack_885_, 1);
v_isSharedCheck_896_ = !lean_is_exclusive(v_stack_885_);
if (v_isSharedCheck_896_ == 0)
{
v___x_890_ = v_stack_885_;
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_drop_888_);
lean_inc(v_raw_887_);
lean_dec(v_stack_885_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_896_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_892_; lean_object* v___x_894_; 
v___x_892_ = l_Array_append___redArg(v_raw_887_, v_stxs_886_);
if (v_isShared_891_ == 0)
{
lean_ctor_set(v___x_890_, 0, v___x_892_);
v___x_894_ = v___x_890_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_drop_888_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_897_, lean_object* v_stxs_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_897_, v_stxs_898_);
lean_dec_ref(v_stxs_898_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_900_, lean_object* v_stxs_901_){
_start:
{
lean_object* v_raw_902_; lean_object* v_drop_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_911_; 
v_raw_902_ = lean_ctor_get(v_stack_900_, 0);
v_drop_903_ = lean_ctor_get(v_stack_900_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_stack_900_);
if (v_isSharedCheck_911_ == 0)
{
v___x_905_ = v_stack_900_;
v_isShared_906_ = v_isSharedCheck_911_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_drop_903_);
lean_inc(v_raw_902_);
lean_dec(v_stack_900_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_911_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_907_ = l_Array_append___redArg(v_raw_902_, v_stxs_901_);
if (v_isShared_906_ == 0)
{
lean_ctor_set(v___x_905_, 0, v___x_907_);
v___x_909_ = v___x_905_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_drop_903_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_912_, lean_object* v_stxs_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_912_, v_stxs_913_);
lean_dec_ref(v_stxs_913_);
return v_res_914_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_917_){
_start:
{
lean_object* v_errorMsg_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_errorMsg_918_ = lean_ctor_get(v_s_917_, 4);
lean_inc(v_errorMsg_918_);
lean_dec_ref(v_s_917_);
v___x_919_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_920_ = lean_box(0);
v___x_921_ = l_Option_instBEq_beq___redArg(v___x_919_, v_errorMsg_918_, v___x_920_);
if (v___x_921_ == 0)
{
uint8_t v___x_922_; 
v___x_922_ = 1;
return v___x_922_;
}
else
{
uint8_t v___x_923_; 
v___x_923_ = 0;
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_924_){
_start:
{
uint8_t v_res_925_; lean_object* v_r_926_; 
v_res_925_ = l_Lean_Parser_ParserState_hasError(v_s_924_);
v_r_926_ = lean_box(v_res_925_);
return v_r_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_927_){
_start:
{
lean_object* v_stxStack_928_; lean_object* v___x_929_; 
v_stxStack_928_ = lean_ctor_get(v_s_927_, 0);
v___x_929_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_928_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Lean_Parser_ParserState_stackSize(v_s_930_);
lean_dec_ref(v_s_930_);
return v_res_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_932_, lean_object* v_iniStackSz_933_, lean_object* v_iniPos_934_){
_start:
{
lean_object* v_stxStack_935_; lean_object* v_lhsPrec_936_; lean_object* v_cache_937_; lean_object* v_recoveredErrors_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_947_; 
v_stxStack_935_ = lean_ctor_get(v_s_932_, 0);
v_lhsPrec_936_ = lean_ctor_get(v_s_932_, 1);
v_cache_937_ = lean_ctor_get(v_s_932_, 3);
v_recoveredErrors_938_ = lean_ctor_get(v_s_932_, 5);
v_isSharedCheck_947_ = !lean_is_exclusive(v_s_932_);
if (v_isSharedCheck_947_ == 0)
{
lean_object* v_unused_948_; lean_object* v_unused_949_; 
v_unused_948_ = lean_ctor_get(v_s_932_, 4);
lean_dec(v_unused_948_);
v_unused_949_ = lean_ctor_get(v_s_932_, 2);
lean_dec(v_unused_949_);
v___x_940_ = v_s_932_;
v_isShared_941_ = v_isSharedCheck_947_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_recoveredErrors_938_);
lean_inc(v_cache_937_);
lean_inc(v_lhsPrec_936_);
lean_inc(v_stxStack_935_);
lean_dec(v_s_932_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_947_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_942_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_935_, v_iniStackSz_933_);
v___x_943_ = lean_box(0);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 4, v___x_943_);
lean_ctor_set(v___x_940_, 2, v_iniPos_934_);
lean_ctor_set(v___x_940_, 0, v___x_942_);
v___x_945_ = v___x_940_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_lhsPrec_936_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v_iniPos_934_);
lean_ctor_set(v_reuseFailAlloc_946_, 3, v_cache_937_);
lean_ctor_set(v_reuseFailAlloc_946_, 4, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_946_, 5, v_recoveredErrors_938_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_950_, lean_object* v_iniStackSz_951_, lean_object* v_iniPos_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_Parser_ParserState_restore(v_s_950_, v_iniStackSz_951_, v_iniPos_952_);
lean_dec(v_iniStackSz_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_954_, lean_object* v_pos_955_){
_start:
{
lean_object* v_stxStack_956_; lean_object* v_lhsPrec_957_; lean_object* v_cache_958_; lean_object* v_errorMsg_959_; lean_object* v_recoveredErrors_960_; lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_967_; 
v_stxStack_956_ = lean_ctor_get(v_s_954_, 0);
v_lhsPrec_957_ = lean_ctor_get(v_s_954_, 1);
v_cache_958_ = lean_ctor_get(v_s_954_, 3);
v_errorMsg_959_ = lean_ctor_get(v_s_954_, 4);
v_recoveredErrors_960_ = lean_ctor_get(v_s_954_, 5);
v_isSharedCheck_967_ = !lean_is_exclusive(v_s_954_);
if (v_isSharedCheck_967_ == 0)
{
lean_object* v_unused_968_; 
v_unused_968_ = lean_ctor_get(v_s_954_, 2);
lean_dec(v_unused_968_);
v___x_962_ = v_s_954_;
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
else
{
lean_inc(v_recoveredErrors_960_);
lean_inc(v_errorMsg_959_);
lean_inc(v_cache_958_);
lean_inc(v_lhsPrec_957_);
lean_inc(v_stxStack_956_);
lean_dec(v_s_954_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_967_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v___x_965_; 
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 2, v_pos_955_);
v___x_965_ = v___x_962_;
goto v_reusejp_964_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_stxStack_956_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_lhsPrec_957_);
lean_ctor_set(v_reuseFailAlloc_966_, 2, v_pos_955_);
lean_ctor_set(v_reuseFailAlloc_966_, 3, v_cache_958_);
lean_ctor_set(v_reuseFailAlloc_966_, 4, v_errorMsg_959_);
lean_ctor_set(v_reuseFailAlloc_966_, 5, v_recoveredErrors_960_);
v___x_965_ = v_reuseFailAlloc_966_;
goto v_reusejp_964_;
}
v_reusejp_964_:
{
return v___x_965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_969_, lean_object* v_cache_970_){
_start:
{
lean_object* v_stxStack_971_; lean_object* v_lhsPrec_972_; lean_object* v_pos_973_; lean_object* v_errorMsg_974_; lean_object* v_recoveredErrors_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
v_stxStack_971_ = lean_ctor_get(v_s_969_, 0);
v_lhsPrec_972_ = lean_ctor_get(v_s_969_, 1);
v_pos_973_ = lean_ctor_get(v_s_969_, 2);
v_errorMsg_974_ = lean_ctor_get(v_s_969_, 4);
v_recoveredErrors_975_ = lean_ctor_get(v_s_969_, 5);
v_isSharedCheck_982_ = !lean_is_exclusive(v_s_969_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_s_969_, 3);
lean_dec(v_unused_983_);
v___x_977_ = v_s_969_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_recoveredErrors_975_);
lean_inc(v_errorMsg_974_);
lean_inc(v_pos_973_);
lean_inc(v_lhsPrec_972_);
lean_inc(v_stxStack_971_);
lean_dec(v_s_969_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 3, v_cache_970_);
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_stxStack_971_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_lhsPrec_972_);
lean_ctor_set(v_reuseFailAlloc_981_, 2, v_pos_973_);
lean_ctor_set(v_reuseFailAlloc_981_, 3, v_cache_970_);
lean_ctor_set(v_reuseFailAlloc_981_, 4, v_errorMsg_974_);
lean_ctor_set(v_reuseFailAlloc_981_, 5, v_recoveredErrors_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_984_, lean_object* v_n_985_){
_start:
{
lean_object* v_stxStack_986_; lean_object* v_lhsPrec_987_; lean_object* v_pos_988_; lean_object* v_cache_989_; lean_object* v_errorMsg_990_; lean_object* v_recoveredErrors_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_999_; 
v_stxStack_986_ = lean_ctor_get(v_s_984_, 0);
v_lhsPrec_987_ = lean_ctor_get(v_s_984_, 1);
v_pos_988_ = lean_ctor_get(v_s_984_, 2);
v_cache_989_ = lean_ctor_get(v_s_984_, 3);
v_errorMsg_990_ = lean_ctor_get(v_s_984_, 4);
v_recoveredErrors_991_ = lean_ctor_get(v_s_984_, 5);
v_isSharedCheck_999_ = !lean_is_exclusive(v_s_984_);
if (v_isSharedCheck_999_ == 0)
{
v___x_993_ = v_s_984_;
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_recoveredErrors_991_);
lean_inc(v_errorMsg_990_);
lean_inc(v_cache_989_);
lean_inc(v_pos_988_);
lean_inc(v_lhsPrec_987_);
lean_inc(v_stxStack_986_);
lean_dec(v_s_984_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_999_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_986_, v_n_985_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_998_, 1, v_lhsPrec_987_);
lean_ctor_set(v_reuseFailAlloc_998_, 2, v_pos_988_);
lean_ctor_set(v_reuseFailAlloc_998_, 3, v_cache_989_);
lean_ctor_set(v_reuseFailAlloc_998_, 4, v_errorMsg_990_);
lean_ctor_set(v_reuseFailAlloc_998_, 5, v_recoveredErrors_991_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1000_){
_start:
{
lean_object* v_stxStack_1001_; lean_object* v_lhsPrec_1002_; lean_object* v_pos_1003_; lean_object* v_cache_1004_; lean_object* v_errorMsg_1005_; lean_object* v_recoveredErrors_1006_; lean_object* v___x_1008_; uint8_t v_isShared_1009_; uint8_t v_isSharedCheck_1014_; 
v_stxStack_1001_ = lean_ctor_get(v_s_1000_, 0);
v_lhsPrec_1002_ = lean_ctor_get(v_s_1000_, 1);
v_pos_1003_ = lean_ctor_get(v_s_1000_, 2);
v_cache_1004_ = lean_ctor_get(v_s_1000_, 3);
v_errorMsg_1005_ = lean_ctor_get(v_s_1000_, 4);
v_recoveredErrors_1006_ = lean_ctor_get(v_s_1000_, 5);
v_isSharedCheck_1014_ = !lean_is_exclusive(v_s_1000_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1008_ = v_s_1000_;
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
else
{
lean_inc(v_recoveredErrors_1006_);
lean_inc(v_errorMsg_1005_);
lean_inc(v_cache_1004_);
lean_inc(v_pos_1003_);
lean_inc(v_lhsPrec_1002_);
lean_inc(v_stxStack_1001_);
lean_dec(v_s_1000_);
v___x_1008_ = lean_box(0);
v_isShared_1009_ = v_isSharedCheck_1014_;
goto v_resetjp_1007_;
}
v_resetjp_1007_:
{
lean_object* v___x_1010_; lean_object* v___x_1012_; 
v___x_1010_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1001_);
if (v_isShared_1009_ == 0)
{
lean_ctor_set(v___x_1008_, 0, v___x_1010_);
v___x_1012_ = v___x_1008_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v___x_1010_);
lean_ctor_set(v_reuseFailAlloc_1013_, 1, v_lhsPrec_1002_);
lean_ctor_set(v_reuseFailAlloc_1013_, 2, v_pos_1003_);
lean_ctor_set(v_reuseFailAlloc_1013_, 3, v_cache_1004_);
lean_ctor_set(v_reuseFailAlloc_1013_, 4, v_errorMsg_1005_);
lean_ctor_set(v_reuseFailAlloc_1013_, 5, v_recoveredErrors_1006_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1015_, lean_object* v_iniStackSz_1016_){
_start:
{
lean_object* v_stxStack_1017_; lean_object* v_lhsPrec_1018_; lean_object* v_pos_1019_; lean_object* v_cache_1020_; lean_object* v_errorMsg_1021_; lean_object* v_recoveredErrors_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_stxStack_1017_ = lean_ctor_get(v_s_1015_, 0);
v_lhsPrec_1018_ = lean_ctor_get(v_s_1015_, 1);
v_pos_1019_ = lean_ctor_get(v_s_1015_, 2);
v_cache_1020_ = lean_ctor_get(v_s_1015_, 3);
v_errorMsg_1021_ = lean_ctor_get(v_s_1015_, 4);
v_recoveredErrors_1022_ = lean_ctor_get(v_s_1015_, 5);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_s_1015_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v_s_1015_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_recoveredErrors_1022_);
lean_inc(v_errorMsg_1021_);
lean_inc(v_cache_1020_);
lean_inc(v_pos_1019_);
lean_inc(v_lhsPrec_1018_);
lean_inc(v_stxStack_1017_);
lean_dec(v_s_1015_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1017_, v_iniStackSz_1016_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_lhsPrec_1018_);
lean_ctor_set(v_reuseFailAlloc_1029_, 2, v_pos_1019_);
lean_ctor_set(v_reuseFailAlloc_1029_, 3, v_cache_1020_);
lean_ctor_set(v_reuseFailAlloc_1029_, 4, v_errorMsg_1021_);
lean_ctor_set(v_reuseFailAlloc_1029_, 5, v_recoveredErrors_1022_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1031_, lean_object* v_iniStackSz_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1031_, v_iniStackSz_1032_);
lean_dec(v_iniStackSz_1032_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1034_, lean_object* v_c_1035_, lean_object* v_pos_1036_){
_start:
{
lean_object* v_toInputContext_1037_; lean_object* v_stxStack_1038_; lean_object* v_lhsPrec_1039_; lean_object* v_cache_1040_; lean_object* v_errorMsg_1041_; lean_object* v_recoveredErrors_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1051_; 
v_toInputContext_1037_ = lean_ctor_get(v_c_1035_, 0);
v_stxStack_1038_ = lean_ctor_get(v_s_1034_, 0);
v_lhsPrec_1039_ = lean_ctor_get(v_s_1034_, 1);
v_cache_1040_ = lean_ctor_get(v_s_1034_, 3);
v_errorMsg_1041_ = lean_ctor_get(v_s_1034_, 4);
v_recoveredErrors_1042_ = lean_ctor_get(v_s_1034_, 5);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_s_1034_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v_s_1034_, 2);
lean_dec(v_unused_1052_);
v___x_1044_ = v_s_1034_;
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_recoveredErrors_1042_);
lean_inc(v_errorMsg_1041_);
lean_inc(v_cache_1040_);
lean_inc(v_lhsPrec_1039_);
lean_inc(v_stxStack_1038_);
lean_dec(v_s_1034_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1051_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v_inputString_1046_; lean_object* v___x_1047_; lean_object* v___x_1049_; 
v_inputString_1046_ = lean_ctor_get(v_toInputContext_1037_, 0);
v___x_1047_ = lean_string_utf8_next(v_inputString_1046_, v_pos_1036_);
if (v_isShared_1045_ == 0)
{
lean_ctor_set(v___x_1044_, 2, v___x_1047_);
v___x_1049_ = v___x_1044_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_stxStack_1038_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_lhsPrec_1039_);
lean_ctor_set(v_reuseFailAlloc_1050_, 2, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1050_, 3, v_cache_1040_);
lean_ctor_set(v_reuseFailAlloc_1050_, 4, v_errorMsg_1041_);
lean_ctor_set(v_reuseFailAlloc_1050_, 5, v_recoveredErrors_1042_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1053_, lean_object* v_c_1054_, lean_object* v_pos_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Parser_ParserState_next(v_s_1053_, v_c_1054_, v_pos_1055_);
lean_dec(v_pos_1055_);
lean_dec_ref(v_c_1054_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1057_, lean_object* v_c_1058_, lean_object* v_pos_1059_){
_start:
{
lean_object* v_toInputContext_1060_; lean_object* v_stxStack_1061_; lean_object* v_lhsPrec_1062_; lean_object* v_cache_1063_; lean_object* v_errorMsg_1064_; lean_object* v_recoveredErrors_1065_; lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1074_; 
v_toInputContext_1060_ = lean_ctor_get(v_c_1058_, 0);
v_stxStack_1061_ = lean_ctor_get(v_s_1057_, 0);
v_lhsPrec_1062_ = lean_ctor_get(v_s_1057_, 1);
v_cache_1063_ = lean_ctor_get(v_s_1057_, 3);
v_errorMsg_1064_ = lean_ctor_get(v_s_1057_, 4);
v_recoveredErrors_1065_ = lean_ctor_get(v_s_1057_, 5);
v_isSharedCheck_1074_ = !lean_is_exclusive(v_s_1057_);
if (v_isSharedCheck_1074_ == 0)
{
lean_object* v_unused_1075_; 
v_unused_1075_ = lean_ctor_get(v_s_1057_, 2);
lean_dec(v_unused_1075_);
v___x_1067_ = v_s_1057_;
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
else
{
lean_inc(v_recoveredErrors_1065_);
lean_inc(v_errorMsg_1064_);
lean_inc(v_cache_1063_);
lean_inc(v_lhsPrec_1062_);
lean_inc(v_stxStack_1061_);
lean_dec(v_s_1057_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1074_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_inputString_1069_; lean_object* v___x_1070_; lean_object* v___x_1072_; 
v_inputString_1069_ = lean_ctor_get(v_toInputContext_1060_, 0);
v___x_1070_ = lean_string_utf8_next_fast(v_inputString_1069_, v_pos_1059_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 2, v___x_1070_);
v___x_1072_ = v___x_1067_;
goto v_reusejp_1071_;
}
else
{
lean_object* v_reuseFailAlloc_1073_; 
v_reuseFailAlloc_1073_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1073_, 0, v_stxStack_1061_);
lean_ctor_set(v_reuseFailAlloc_1073_, 1, v_lhsPrec_1062_);
lean_ctor_set(v_reuseFailAlloc_1073_, 2, v___x_1070_);
lean_ctor_set(v_reuseFailAlloc_1073_, 3, v_cache_1063_);
lean_ctor_set(v_reuseFailAlloc_1073_, 4, v_errorMsg_1064_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1076_, lean_object* v_c_1077_, lean_object* v_pos_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1076_, v_c_1077_, v_pos_1078_);
lean_dec(v_pos_1078_);
lean_dec_ref(v_c_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1080_, lean_object* v_c_1081_, lean_object* v_pos_1082_, lean_object* v_h_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1080_, v_c_1081_, v_pos_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1085_, lean_object* v_c_1086_, lean_object* v_pos_1087_, lean_object* v_h_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Lean_Parser_ParserState_next_x27(v_s_1085_, v_c_1086_, v_pos_1087_, v_h_1088_);
lean_dec(v_pos_1087_);
lean_dec_ref(v_c_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1090_, lean_object* v_x_1091_){
_start:
{
if (lean_obj_tag(v_x_1090_) == 0)
{
if (lean_obj_tag(v_x_1091_) == 0)
{
uint8_t v___x_1092_; 
v___x_1092_ = 1;
return v___x_1092_;
}
else
{
uint8_t v___x_1093_; 
lean_dec_ref(v_x_1091_);
v___x_1093_ = 0;
return v___x_1093_;
}
}
else
{
if (lean_obj_tag(v_x_1091_) == 0)
{
uint8_t v___x_1094_; 
lean_dec_ref(v_x_1090_);
v___x_1094_ = 0;
return v___x_1094_;
}
else
{
lean_object* v_val_1095_; lean_object* v_val_1096_; uint8_t v___x_1097_; 
v_val_1095_ = lean_ctor_get(v_x_1090_, 0);
lean_inc(v_val_1095_);
lean_dec_ref(v_x_1090_);
v_val_1096_ = lean_ctor_get(v_x_1091_, 0);
lean_inc(v_val_1096_);
lean_dec_ref(v_x_1091_);
v___x_1097_ = l_Lean_Parser_instBEqError_beq(v_val_1095_, v_val_1096_);
return v___x_1097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1098_, lean_object* v_x_1099_){
_start:
{
uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_res_1100_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1098_, v_x_1099_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1102_, lean_object* v_k_1103_, lean_object* v_iniStackSz_1104_){
_start:
{
lean_object* v_stxStack_1105_; lean_object* v_lhsPrec_1106_; lean_object* v_pos_1107_; lean_object* v_cache_1108_; lean_object* v_errorMsg_1109_; lean_object* v_recoveredErrors_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1131_; 
v_stxStack_1105_ = lean_ctor_get(v_s_1102_, 0);
v_lhsPrec_1106_ = lean_ctor_get(v_s_1102_, 1);
v_pos_1107_ = lean_ctor_get(v_s_1102_, 2);
v_cache_1108_ = lean_ctor_get(v_s_1102_, 3);
v_errorMsg_1109_ = lean_ctor_get(v_s_1102_, 4);
v_recoveredErrors_1110_ = lean_ctor_get(v_s_1102_, 5);
v_isSharedCheck_1131_ = !lean_is_exclusive(v_s_1102_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1112_ = v_s_1102_;
v_isShared_1113_ = v_isSharedCheck_1131_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_recoveredErrors_1110_);
lean_inc(v_errorMsg_1109_);
lean_inc(v_cache_1108_);
lean_inc(v_pos_1107_);
lean_inc(v_lhsPrec_1106_);
lean_inc(v_stxStack_1105_);
lean_dec(v_s_1102_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1131_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = lean_box(0);
lean_inc(v_errorMsg_1109_);
v___x_1125_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1109_, v___x_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1126_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1105_);
v___x_1127_ = lean_nat_dec_eq(v___x_1126_, v_iniStackSz_1104_);
lean_dec(v___x_1126_);
if (v___x_1127_ == 0)
{
goto v___jp_1114_;
}
else
{
lean_object* v___x_1128_; lean_object* v_stack_1129_; lean_object* v___x_1130_; 
lean_del_object(v___x_1112_);
lean_dec(v_k_1103_);
v___x_1128_ = lean_box(0);
v_stack_1129_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1105_, v___x_1128_);
v___x_1130_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1130_, 0, v_stack_1129_);
lean_ctor_set(v___x_1130_, 1, v_lhsPrec_1106_);
lean_ctor_set(v___x_1130_, 2, v_pos_1107_);
lean_ctor_set(v___x_1130_, 3, v_cache_1108_);
lean_ctor_set(v___x_1130_, 4, v_errorMsg_1109_);
lean_ctor_set(v___x_1130_, 5, v_recoveredErrors_1110_);
return v___x_1130_;
}
}
else
{
goto v___jp_1114_;
}
v___jp_1114_:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v_newNode_1118_; lean_object* v_stack_1119_; lean_object* v_stack_1120_; lean_object* v___x_1122_; 
v___x_1115_ = lean_box(2);
v___x_1116_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1105_);
v___x_1117_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1105_, v_iniStackSz_1104_, v___x_1116_);
lean_dec(v___x_1116_);
v_newNode_1118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1118_, 0, v___x_1115_);
lean_ctor_set(v_newNode_1118_, 1, v_k_1103_);
lean_ctor_set(v_newNode_1118_, 2, v___x_1117_);
v_stack_1119_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1105_, v_iniStackSz_1104_);
v_stack_1120_ = l_Lean_Parser_SyntaxStack_push(v_stack_1119_, v_newNode_1118_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v_stack_1120_);
v___x_1122_ = v___x_1112_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_stack_1120_);
lean_ctor_set(v_reuseFailAlloc_1123_, 1, v_lhsPrec_1106_);
lean_ctor_set(v_reuseFailAlloc_1123_, 2, v_pos_1107_);
lean_ctor_set(v_reuseFailAlloc_1123_, 3, v_cache_1108_);
lean_ctor_set(v_reuseFailAlloc_1123_, 4, v_errorMsg_1109_);
lean_ctor_set(v_reuseFailAlloc_1123_, 5, v_recoveredErrors_1110_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1132_, lean_object* v_k_1133_, lean_object* v_iniStackSz_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Lean_Parser_ParserState_mkNode(v_s_1132_, v_k_1133_, v_iniStackSz_1134_);
lean_dec(v_iniStackSz_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1136_, lean_object* v_k_1137_, lean_object* v_iniStackSz_1138_){
_start:
{
lean_object* v_stxStack_1139_; lean_object* v_lhsPrec_1140_; lean_object* v_pos_1141_; lean_object* v_cache_1142_; lean_object* v_errorMsg_1143_; lean_object* v_recoveredErrors_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1159_; 
v_stxStack_1139_ = lean_ctor_get(v_s_1136_, 0);
v_lhsPrec_1140_ = lean_ctor_get(v_s_1136_, 1);
v_pos_1141_ = lean_ctor_get(v_s_1136_, 2);
v_cache_1142_ = lean_ctor_get(v_s_1136_, 3);
v_errorMsg_1143_ = lean_ctor_get(v_s_1136_, 4);
v_recoveredErrors_1144_ = lean_ctor_get(v_s_1136_, 5);
v_isSharedCheck_1159_ = !lean_is_exclusive(v_s_1136_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1146_ = v_s_1136_;
v_isShared_1147_ = v_isSharedCheck_1159_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_recoveredErrors_1144_);
lean_inc(v_errorMsg_1143_);
lean_inc(v_cache_1142_);
lean_inc(v_pos_1141_);
lean_inc(v_lhsPrec_1140_);
lean_inc(v_stxStack_1139_);
lean_dec(v_s_1136_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1159_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v_newNode_1153_; lean_object* v_stack_1154_; lean_object* v_stack_1155_; lean_object* v___x_1157_; 
v___x_1148_ = lean_box(2);
v___x_1149_ = lean_unsigned_to_nat(1u);
v___x_1150_ = lean_nat_sub(v_iniStackSz_1138_, v___x_1149_);
v___x_1151_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1139_);
v___x_1152_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1139_, v___x_1150_, v___x_1151_);
lean_dec(v___x_1151_);
v_newNode_1153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1153_, 0, v___x_1148_);
lean_ctor_set(v_newNode_1153_, 1, v_k_1137_);
lean_ctor_set(v_newNode_1153_, 2, v___x_1152_);
v_stack_1154_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1139_, v___x_1150_);
lean_dec(v___x_1150_);
v_stack_1155_ = l_Lean_Parser_SyntaxStack_push(v_stack_1154_, v_newNode_1153_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_stack_1155_);
v___x_1157_ = v___x_1146_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_stack_1155_);
lean_ctor_set(v_reuseFailAlloc_1158_, 1, v_lhsPrec_1140_);
lean_ctor_set(v_reuseFailAlloc_1158_, 2, v_pos_1141_);
lean_ctor_set(v_reuseFailAlloc_1158_, 3, v_cache_1142_);
lean_ctor_set(v_reuseFailAlloc_1158_, 4, v_errorMsg_1143_);
lean_ctor_set(v_reuseFailAlloc_1158_, 5, v_recoveredErrors_1144_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1160_, lean_object* v_k_1161_, lean_object* v_iniStackSz_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1160_, v_k_1161_, v_iniStackSz_1162_);
lean_dec(v_iniStackSz_1162_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1166_){
_start:
{
lean_object* v_errorMsg_1167_; 
v_errorMsg_1167_ = lean_ctor_get(v_s_1166_, 4);
if (lean_obj_tag(v_errorMsg_1167_) == 0)
{
lean_object* v_recoveredErrors_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v_recoveredErrors_1168_ = lean_ctor_get(v_s_1166_, 5);
lean_inc_ref(v_recoveredErrors_1168_);
lean_dec_ref(v_s_1166_);
v___x_1169_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1170_ = l_Array_append___redArg(v_recoveredErrors_1168_, v___x_1169_);
return v___x_1170_;
}
else
{
lean_object* v_stxStack_1171_; lean_object* v_pos_1172_; lean_object* v_recoveredErrors_1173_; lean_object* v_val_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_inc_ref(v_errorMsg_1167_);
v_stxStack_1171_ = lean_ctor_get(v_s_1166_, 0);
lean_inc_ref(v_stxStack_1171_);
v_pos_1172_ = lean_ctor_get(v_s_1166_, 2);
lean_inc(v_pos_1172_);
v_recoveredErrors_1173_ = lean_ctor_get(v_s_1166_, 5);
lean_inc_ref(v_recoveredErrors_1173_);
lean_dec_ref(v_s_1166_);
v_val_1174_ = lean_ctor_get(v_errorMsg_1167_, 0);
lean_inc(v_val_1174_);
lean_dec_ref(v_errorMsg_1167_);
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_stxStack_1171_);
lean_ctor_set(v___x_1175_, 1, v_val_1174_);
v___x_1176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1176_, 0, v_pos_1172_);
lean_ctor_set(v___x_1176_, 1, v___x_1175_);
v___x_1177_ = lean_unsigned_to_nat(1u);
v___x_1178_ = lean_mk_empty_array_with_capacity(v___x_1177_);
v___x_1179_ = lean_array_push(v___x_1178_, v___x_1176_);
v___x_1180_ = l_Array_append___redArg(v_recoveredErrors_1173_, v___x_1179_);
lean_dec_ref(v___x_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1181_, lean_object* v_e_1182_){
_start:
{
lean_object* v_stxStack_1183_; lean_object* v_lhsPrec_1184_; lean_object* v_pos_1185_; lean_object* v_cache_1186_; lean_object* v_recoveredErrors_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1195_; 
v_stxStack_1183_ = lean_ctor_get(v_s_1181_, 0);
v_lhsPrec_1184_ = lean_ctor_get(v_s_1181_, 1);
v_pos_1185_ = lean_ctor_get(v_s_1181_, 2);
v_cache_1186_ = lean_ctor_get(v_s_1181_, 3);
v_recoveredErrors_1187_ = lean_ctor_get(v_s_1181_, 5);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_s_1181_);
if (v_isSharedCheck_1195_ == 0)
{
lean_object* v_unused_1196_; 
v_unused_1196_ = lean_ctor_get(v_s_1181_, 4);
lean_dec(v_unused_1196_);
v___x_1189_ = v_s_1181_;
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_recoveredErrors_1187_);
lean_inc(v_cache_1186_);
lean_inc(v_pos_1185_);
lean_inc(v_lhsPrec_1184_);
lean_inc(v_stxStack_1183_);
lean_dec(v_s_1181_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1195_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; lean_object* v___x_1193_; 
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_e_1182_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 4, v___x_1191_);
v___x_1193_ = v___x_1189_;
goto v_reusejp_1192_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_stxStack_1183_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v_lhsPrec_1184_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_pos_1185_);
lean_ctor_set(v_reuseFailAlloc_1194_, 3, v_cache_1186_);
lean_ctor_set(v_reuseFailAlloc_1194_, 4, v___x_1191_);
lean_ctor_set(v_reuseFailAlloc_1194_, 5, v_recoveredErrors_1187_);
v___x_1193_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1192_;
}
v_reusejp_1192_:
{
return v___x_1193_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1197_, lean_object* v_msg_1198_){
_start:
{
lean_object* v_stxStack_1199_; lean_object* v_lhsPrec_1200_; lean_object* v_pos_1201_; lean_object* v_cache_1202_; lean_object* v_recoveredErrors_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1217_; 
v_stxStack_1199_ = lean_ctor_get(v_s_1197_, 0);
v_lhsPrec_1200_ = lean_ctor_get(v_s_1197_, 1);
v_pos_1201_ = lean_ctor_get(v_s_1197_, 2);
v_cache_1202_ = lean_ctor_get(v_s_1197_, 3);
v_recoveredErrors_1203_ = lean_ctor_get(v_s_1197_, 5);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_s_1197_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_s_1197_, 4);
lean_dec(v_unused_1218_);
v___x_1205_ = v_s_1197_;
v_isShared_1206_ = v_isSharedCheck_1217_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_recoveredErrors_1203_);
lean_inc(v_cache_1202_);
lean_inc(v_pos_1201_);
lean_inc(v_lhsPrec_1200_);
lean_inc(v_stxStack_1199_);
lean_dec(v_s_1197_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1217_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
v___x_1207_ = lean_box(0);
v___x_1208_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1209_ = lean_box(0);
v___x_1210_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1210_, 0, v_msg_1198_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1207_);
lean_ctor_set(v___x_1211_, 1, v___x_1208_);
lean_ctor_set(v___x_1211_, 2, v___x_1210_);
v___x_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 4, v___x_1212_);
v___x_1214_ = v___x_1205_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_stxStack_1199_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_lhsPrec_1200_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_pos_1201_);
lean_ctor_set(v_reuseFailAlloc_1216_, 3, v_cache_1202_);
lean_ctor_set(v_reuseFailAlloc_1216_, 4, v___x_1212_);
lean_ctor_set(v_reuseFailAlloc_1216_, 5, v_recoveredErrors_1203_);
v___x_1214_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1214_, v___x_1207_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1219_, lean_object* v_msg_1220_, lean_object* v_expected_1221_, uint8_t v_pushMissing_1222_){
_start:
{
lean_object* v_stxStack_1223_; lean_object* v_lhsPrec_1224_; lean_object* v_pos_1225_; lean_object* v_cache_1226_; lean_object* v_recoveredErrors_1227_; lean_object* v___x_1229_; uint8_t v_isShared_1230_; uint8_t v_isSharedCheck_1238_; 
v_stxStack_1223_ = lean_ctor_get(v_s_1219_, 0);
v_lhsPrec_1224_ = lean_ctor_get(v_s_1219_, 1);
v_pos_1225_ = lean_ctor_get(v_s_1219_, 2);
v_cache_1226_ = lean_ctor_get(v_s_1219_, 3);
v_recoveredErrors_1227_ = lean_ctor_get(v_s_1219_, 5);
v_isSharedCheck_1238_ = !lean_is_exclusive(v_s_1219_);
if (v_isSharedCheck_1238_ == 0)
{
lean_object* v_unused_1239_; 
v_unused_1239_ = lean_ctor_get(v_s_1219_, 4);
lean_dec(v_unused_1239_);
v___x_1229_ = v_s_1219_;
v_isShared_1230_ = v_isSharedCheck_1238_;
goto v_resetjp_1228_;
}
else
{
lean_inc(v_recoveredErrors_1227_);
lean_inc(v_cache_1226_);
lean_inc(v_pos_1225_);
lean_inc(v_lhsPrec_1224_);
lean_inc(v_stxStack_1223_);
lean_dec(v_s_1219_);
v___x_1229_ = lean_box(0);
v_isShared_1230_ = v_isSharedCheck_1238_;
goto v_resetjp_1228_;
}
v_resetjp_1228_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_s_1235_; 
v___x_1231_ = lean_box(0);
v___x_1232_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1231_);
lean_ctor_set(v___x_1232_, 1, v_msg_1220_);
lean_ctor_set(v___x_1232_, 2, v_expected_1221_);
v___x_1233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
if (v_isShared_1230_ == 0)
{
lean_ctor_set(v___x_1229_, 4, v___x_1233_);
v_s_1235_ = v___x_1229_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_stxStack_1223_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_lhsPrec_1224_);
lean_ctor_set(v_reuseFailAlloc_1237_, 2, v_pos_1225_);
lean_ctor_set(v_reuseFailAlloc_1237_, 3, v_cache_1226_);
lean_ctor_set(v_reuseFailAlloc_1237_, 4, v___x_1233_);
lean_ctor_set(v_reuseFailAlloc_1237_, 5, v_recoveredErrors_1227_);
v_s_1235_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
if (v_pushMissing_1222_ == 0)
{
return v_s_1235_;
}
else
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1235_, v___x_1231_);
return v___x_1236_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1240_, lean_object* v_msg_1241_, lean_object* v_expected_1242_, lean_object* v_pushMissing_1243_){
_start:
{
uint8_t v_pushMissing_boxed_1244_; lean_object* v_res_1245_; 
v_pushMissing_boxed_1244_ = lean_unbox(v_pushMissing_1243_);
v_res_1245_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1240_, v_msg_1241_, v_expected_1242_, v_pushMissing_boxed_1244_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1247_, lean_object* v_expected_1248_){
_start:
{
lean_object* v___x_1249_; uint8_t v___x_1250_; lean_object* v___x_1251_; 
v___x_1249_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1250_ = 1;
v___x_1251_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1247_, v___x_1249_, v_expected_1248_, v___x_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1252_, lean_object* v_ex_1253_, lean_object* v_pos_1254_, lean_object* v_initStackSz_x3f_1255_){
_start:
{
lean_object* v_s_1257_; lean_object* v_s_1276_; 
v_s_1276_ = l_Lean_Parser_ParserState_setPos(v_s_1252_, v_pos_1254_);
if (lean_obj_tag(v_initStackSz_x3f_1255_) == 1)
{
lean_object* v_val_1277_; lean_object* v_s_1278_; 
v_val_1277_ = lean_ctor_get(v_initStackSz_x3f_1255_, 0);
v_s_1278_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1276_, v_val_1277_);
v_s_1257_ = v_s_1278_;
goto v___jp_1256_;
}
else
{
v_s_1257_ = v_s_1276_;
goto v___jp_1256_;
}
v___jp_1256_:
{
lean_object* v_stxStack_1258_; lean_object* v_lhsPrec_1259_; lean_object* v_pos_1260_; lean_object* v_cache_1261_; lean_object* v_recoveredErrors_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1274_; 
v_stxStack_1258_ = lean_ctor_get(v_s_1257_, 0);
v_lhsPrec_1259_ = lean_ctor_get(v_s_1257_, 1);
v_pos_1260_ = lean_ctor_get(v_s_1257_, 2);
v_cache_1261_ = lean_ctor_get(v_s_1257_, 3);
v_recoveredErrors_1262_ = lean_ctor_get(v_s_1257_, 5);
v_isSharedCheck_1274_ = !lean_is_exclusive(v_s_1257_);
if (v_isSharedCheck_1274_ == 0)
{
lean_object* v_unused_1275_; 
v_unused_1275_ = lean_ctor_get(v_s_1257_, 4);
lean_dec(v_unused_1275_);
v___x_1264_ = v_s_1257_;
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_recoveredErrors_1262_);
lean_inc(v_cache_1261_);
lean_inc(v_pos_1260_);
lean_inc(v_lhsPrec_1259_);
lean_inc(v_stxStack_1258_);
lean_dec(v_s_1257_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1274_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v_s_1271_; 
v___x_1266_ = lean_box(0);
v___x_1267_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1268_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1266_);
lean_ctor_set(v___x_1268_, 1, v___x_1267_);
lean_ctor_set(v___x_1268_, 2, v_ex_1253_);
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 4, v___x_1269_);
v_s_1271_ = v___x_1264_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v_stxStack_1258_);
lean_ctor_set(v_reuseFailAlloc_1273_, 1, v_lhsPrec_1259_);
lean_ctor_set(v_reuseFailAlloc_1273_, 2, v_pos_1260_);
lean_ctor_set(v_reuseFailAlloc_1273_, 3, v_cache_1261_);
lean_ctor_set(v_reuseFailAlloc_1273_, 4, v___x_1269_);
lean_ctor_set(v_reuseFailAlloc_1273_, 5, v_recoveredErrors_1262_);
v_s_1271_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
lean_object* v___x_1272_; 
v___x_1272_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1271_, v___x_1266_);
return v___x_1272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1279_, lean_object* v_ex_1280_, lean_object* v_pos_1281_, lean_object* v_initStackSz_x3f_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1279_, v_ex_1280_, v_pos_1281_, v_initStackSz_x3f_1282_);
lean_dec(v_initStackSz_x3f_1282_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1284_, lean_object* v_msg_1285_, lean_object* v_pos_1286_, lean_object* v_initStackSz_x3f_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1289_, 0, v_msg_1285_);
lean_ctor_set(v___x_1289_, 1, v___x_1288_);
v___x_1290_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1284_, v___x_1289_, v_pos_1286_, v_initStackSz_x3f_1287_);
return v___x_1290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1291_, lean_object* v_msg_1292_, lean_object* v_pos_1293_, lean_object* v_initStackSz_x3f_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1291_, v_msg_1292_, v_pos_1293_, v_initStackSz_x3f_1294_);
lean_dec(v_initStackSz_x3f_1294_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_panic_fn(v___x_1297_, v_msg_1296_);
return v___x_1298_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1302_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1303_ = lean_unsigned_to_nat(14u);
v___x_1304_ = lean_unsigned_to_nat(22u);
v___x_1305_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1306_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1307_ = l_mkPanicMessageWithDecl(v___x_1306_, v___x_1305_, v___x_1304_, v___x_1303_, v___x_1302_);
return v___x_1307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1308_, lean_object* v_ex_1309_, lean_object* v_iniPos_1310_){
_start:
{
lean_object* v_stxStack_1311_; lean_object* v_tk_1312_; lean_object* v___y_1314_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_stxStack_1311_ = lean_ctor_get(v_s_1308_, 0);
v_tk_1312_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1311_);
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = lean_nat_dec_lt(v___x_1335_, v_iniPos_1310_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; 
lean_dec(v_iniPos_1310_);
v___x_1337_ = l_Lean_Syntax_getPos_x3f(v_tk_1312_, v___x_1336_);
if (lean_obj_tag(v___x_1337_) == 0)
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1339_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1338_);
v___y_1314_ = v___x_1339_;
goto v___jp_1313_;
}
else
{
lean_object* v_val_1340_; 
v_val_1340_ = lean_ctor_get(v___x_1337_, 0);
lean_inc(v_val_1340_);
lean_dec_ref(v___x_1337_);
v___y_1314_ = v_val_1340_;
goto v___jp_1313_;
}
}
else
{
v___y_1314_ = v_iniPos_1310_;
goto v___jp_1313_;
}
v___jp_1313_:
{
lean_object* v_s_1315_; lean_object* v_stxStack_1316_; lean_object* v_lhsPrec_1317_; lean_object* v_pos_1318_; lean_object* v_cache_1319_; lean_object* v_recoveredErrors_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1333_; 
v_s_1315_ = l_Lean_Parser_ParserState_setPos(v_s_1308_, v___y_1314_);
v_stxStack_1316_ = lean_ctor_get(v_s_1315_, 0);
v_lhsPrec_1317_ = lean_ctor_get(v_s_1315_, 1);
v_pos_1318_ = lean_ctor_get(v_s_1315_, 2);
v_cache_1319_ = lean_ctor_get(v_s_1315_, 3);
v_recoveredErrors_1320_ = lean_ctor_get(v_s_1315_, 5);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_s_1315_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_s_1315_, 4);
lean_dec(v_unused_1334_);
v___x_1322_ = v_s_1315_;
v_isShared_1323_ = v_isSharedCheck_1333_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_recoveredErrors_1320_);
lean_inc(v_cache_1319_);
lean_inc(v_pos_1318_);
lean_inc(v_lhsPrec_1317_);
lean_inc(v_stxStack_1316_);
lean_dec(v_s_1315_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1333_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v_s_1328_; 
v___x_1324_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1325_, 0, v_tk_1312_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
lean_ctor_set(v___x_1325_, 2, v_ex_1309_);
v___x_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 4, v___x_1326_);
v_s_1328_ = v___x_1322_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_stxStack_1316_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_lhsPrec_1317_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_pos_1318_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_cache_1319_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1332_, 5, v_recoveredErrors_1320_);
v_s_1328_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = l_Lean_Parser_ParserState_popSyntax(v_s_1328_);
v___x_1330_ = lean_box(0);
v___x_1331_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1329_, v___x_1330_);
return v___x_1331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1341_, lean_object* v_msg_1342_, lean_object* v_iniPos_1343_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = lean_box(0);
v___x_1345_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_msg_1342_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1341_, v___x_1345_, v_iniPos_1343_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1347_, lean_object* v_msg_1348_, lean_object* v_pos_1349_){
_start:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; lean_object* v___x_1353_; 
v___x_1350_ = l_Lean_Parser_ParserState_setPos(v_s_1347_, v_pos_1349_);
v___x_1351_ = lean_box(0);
v___x_1352_ = 1;
v___x_1353_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1350_, v_msg_1348_, v___x_1351_, v___x_1352_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1355_, lean_object* v_as_1356_, size_t v_sz_1357_, size_t v_i_1358_, lean_object* v_b_1359_){
_start:
{
uint8_t v___x_1360_; 
v___x_1360_ = lean_usize_dec_lt(v_i_1358_, v_sz_1357_);
if (v___x_1360_ == 0)
{
lean_dec_ref(v_ctx_1355_);
return v_b_1359_;
}
else
{
lean_object* v_a_1361_; lean_object* v_snd_1362_; lean_object* v_fst_1363_; lean_object* v_snd_1364_; lean_object* v_errStr_1366_; lean_object* v_errStr_1377_; uint8_t v___x_1378_; 
v_a_1361_ = lean_array_uget_borrowed(v_as_1356_, v_i_1358_);
v_snd_1362_ = lean_ctor_get(v_a_1361_, 1);
v_fst_1363_ = lean_ctor_get(v_a_1361_, 0);
v_snd_1364_ = lean_ctor_get(v_snd_1362_, 1);
v_errStr_1377_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1378_ = lean_string_dec_eq(v_b_1359_, v_errStr_1377_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; lean_object* v___x_1380_; 
v___x_1379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1380_ = lean_string_append(v_b_1359_, v___x_1379_);
v_errStr_1366_ = v___x_1380_;
goto v___jp_1365_;
}
else
{
v_errStr_1366_ = v_b_1359_;
goto v___jp_1365_;
}
v___jp_1365_:
{
lean_object* v_fileName_1367_; lean_object* v_fileMap_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; size_t v___x_1374_; size_t v___x_1375_; 
v_fileName_1367_ = lean_ctor_get(v_ctx_1355_, 1);
v_fileMap_1368_ = lean_ctor_get(v_ctx_1355_, 2);
lean_inc_ref(v_fileMap_1368_);
v___x_1369_ = l_Lean_FileMap_toPosition(v_fileMap_1368_, v_fst_1363_);
lean_inc(v_snd_1364_);
v___x_1370_ = l_Lean_Parser_Error_toString(v_snd_1364_);
v___x_1371_ = lean_box(0);
lean_inc_ref(v_fileName_1367_);
v___x_1372_ = l_Lean_mkErrorStringWithPos(v_fileName_1367_, v___x_1369_, v___x_1370_, v___x_1371_, v___x_1371_, v___x_1371_);
lean_dec_ref(v___x_1370_);
v___x_1373_ = lean_string_append(v_errStr_1366_, v___x_1372_);
lean_dec_ref(v___x_1372_);
v___x_1374_ = ((size_t)1ULL);
v___x_1375_ = lean_usize_add(v_i_1358_, v___x_1374_);
v_i_1358_ = v___x_1375_;
v_b_1359_ = v___x_1373_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1381_, lean_object* v_as_1382_, lean_object* v_sz_1383_, lean_object* v_i_1384_, lean_object* v_b_1385_){
_start:
{
size_t v_sz_boxed_1386_; size_t v_i_boxed_1387_; lean_object* v_res_1388_; 
v_sz_boxed_1386_ = lean_unbox_usize(v_sz_1383_);
lean_dec(v_sz_1383_);
v_i_boxed_1387_ = lean_unbox_usize(v_i_1384_);
lean_dec(v_i_1384_);
v_res_1388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1381_, v_as_1382_, v_sz_boxed_1386_, v_i_boxed_1387_, v_b_1385_);
lean_dec_ref(v_as_1382_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1389_, lean_object* v_s_1390_){
_start:
{
lean_object* v_errStr_1391_; lean_object* v___x_1392_; size_t v_sz_1393_; size_t v___x_1394_; lean_object* v___x_1395_; 
v_errStr_1391_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1392_ = l_Lean_Parser_ParserState_allErrors(v_s_1390_);
v_sz_1393_ = lean_array_size(v___x_1392_);
v___x_1394_ = ((size_t)0ULL);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1389_, v___x_1392_, v_sz_1393_, v___x_1394_, v_errStr_1391_);
lean_dec_ref(v___x_1392_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1396_, lean_object* v_s_1397_){
_start:
{
lean_inc_ref(v_s_1397_);
return v_s_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1398_, lean_object* v_s_1399_){
_start:
{
lean_object* v_res_1400_; 
v_res_1400_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1398_, v_s_1399_);
lean_dec_ref(v_s_1399_);
lean_dec_ref(v_x_1398_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx(lean_object* v_x_1403_){
_start:
{
switch(lean_obj_tag(v_x_1403_))
{
case 0:
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_unsigned_to_nat(0u);
return v___x_1404_;
}
case 1:
{
lean_object* v___x_1405_; 
v___x_1405_ = lean_unsigned_to_nat(1u);
return v___x_1405_;
}
case 2:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_unsigned_to_nat(2u);
return v___x_1406_;
}
default: 
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_unsigned_to_nat(3u);
return v___x_1407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___boxed(lean_object* v_x_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Parser_FirstTokens_ctorIdx(v_x_1408_);
lean_dec(v_x_1408_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1410_, lean_object* v_k_1411_){
_start:
{
switch(lean_obj_tag(v_t_1410_))
{
case 2:
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_ctor_get(v_t_1410_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v_t_1410_);
v___x_1413_ = lean_apply_1(v_k_1411_, v_a_1412_);
return v___x_1413_;
}
case 3:
{
lean_object* v_a_1414_; lean_object* v___x_1415_; 
v_a_1414_ = lean_ctor_get(v_t_1410_, 0);
lean_inc(v_a_1414_);
lean_dec_ref(v_t_1410_);
v___x_1415_ = lean_apply_1(v_k_1411_, v_a_1414_);
return v___x_1415_;
}
default: 
{
lean_dec(v_t_1410_);
return v_k_1411_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1416_, lean_object* v_ctorIdx_1417_, lean_object* v_t_1418_, lean_object* v_h_1419_, lean_object* v_k_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1418_, v_k_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1422_, lean_object* v_ctorIdx_1423_, lean_object* v_t_1424_, lean_object* v_h_1425_, lean_object* v_k_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1422_, v_ctorIdx_1423_, v_t_1424_, v_h_1425_, v_k_1426_);
lean_dec(v_ctorIdx_1423_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1428_, lean_object* v_epsilon_1429_){
_start:
{
lean_object* v___x_1430_; 
v___x_1430_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1428_, v_epsilon_1429_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1431_, lean_object* v_t_1432_, lean_object* v_h_1433_, lean_object* v_epsilon_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1432_, v_epsilon_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1436_, lean_object* v_unknown_1437_){
_start:
{
lean_object* v___x_1438_; 
v___x_1438_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1436_, v_unknown_1437_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1439_, lean_object* v_t_1440_, lean_object* v_h_1441_, lean_object* v_unknown_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1440_, v_unknown_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1444_, lean_object* v_tokens_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1444_, v_tokens_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1447_, lean_object* v_t_1448_, lean_object* v_h_1449_, lean_object* v_tokens_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1448_, v_tokens_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1452_, lean_object* v_optTokens_1453_){
_start:
{
lean_object* v___x_1454_; 
v___x_1454_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1452_, v_optTokens_1453_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1455_, lean_object* v_t_1456_, lean_object* v_h_1457_, lean_object* v_optTokens_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1456_, v_optTokens_1458_);
return v___x_1459_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_box(0);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1461_; 
v___x_1461_ = lean_box(0);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1462_, lean_object* v_x_1463_){
_start:
{
switch(lean_obj_tag(v_x_1462_))
{
case 0:
{
return v_x_1463_;
}
case 3:
{
switch(lean_obj_tag(v_x_1463_))
{
case 3:
{
lean_object* v_a_1464_; lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1473_; 
v_a_1464_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_a_1464_);
lean_dec_ref(v_x_1462_);
v_a_1465_ = lean_ctor_get(v_x_1463_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v_x_1463_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1467_ = v_x_1463_;
v_isShared_1468_ = v_isSharedCheck_1473_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v_x_1463_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1473_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1469_; lean_object* v___x_1471_; 
v___x_1469_ = l_List_appendTR___redArg(v_a_1464_, v_a_1465_);
if (v_isShared_1468_ == 0)
{
lean_ctor_set(v___x_1467_, 0, v___x_1469_);
v___x_1471_ = v___x_1467_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
case 2:
{
lean_object* v_a_1474_; lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1483_; 
v_a_1474_ = lean_ctor_get(v_x_1462_, 0);
lean_inc(v_a_1474_);
lean_dec_ref(v_x_1462_);
v_a_1475_ = lean_ctor_get(v_x_1463_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v_x_1463_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1477_ = v_x_1463_;
v_isShared_1478_ = v_isSharedCheck_1483_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v_x_1463_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1483_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1479_ = l_List_appendTR___redArg(v_a_1474_, v_a_1475_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1479_);
v___x_1481_ = v___x_1477_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1479_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
default: 
{
lean_dec(v_x_1463_);
return v_x_1462_;
}
}
}
default: 
{
lean_dec(v_x_1463_);
return v_x_1462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1484_){
_start:
{
if (lean_obj_tag(v_x_1484_) == 2)
{
lean_object* v_a_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1492_; 
v_a_1485_ = lean_ctor_get(v_x_1484_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_x_1484_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1487_ = v_x_1484_;
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_a_1485_);
lean_dec(v_x_1484_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1492_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set_tag(v___x_1487_, 3);
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_a_1485_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
return v_x_1484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1493_, lean_object* v_x_1494_){
_start:
{
lean_object* v_s_u2081_1496_; lean_object* v_s_u2082_1497_; 
switch(lean_obj_tag(v_x_1493_))
{
case 0:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1494_);
return v___x_1500_;
}
case 2:
{
switch(lean_obj_tag(v_x_1494_))
{
case 0:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1493_);
return v___x_1501_;
}
case 2:
{
lean_object* v_a_1502_; lean_object* v_a_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1511_; 
v_a_1502_ = lean_ctor_get(v_x_1493_, 0);
lean_inc(v_a_1502_);
lean_dec_ref(v_x_1493_);
v_a_1503_ = lean_ctor_get(v_x_1494_, 0);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_x_1494_);
if (v_isSharedCheck_1511_ == 0)
{
v___x_1505_ = v_x_1494_;
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
else
{
lean_inc(v_a_1503_);
lean_dec(v_x_1494_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1507_ = l_List_appendTR___redArg(v_a_1502_, v_a_1503_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 0, v___x_1507_);
v___x_1509_ = v___x_1505_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
case 3:
{
lean_object* v_a_1512_; lean_object* v_a_1513_; 
v_a_1512_ = lean_ctor_get(v_x_1493_, 0);
lean_inc(v_a_1512_);
lean_dec_ref(v_x_1493_);
v_a_1513_ = lean_ctor_get(v_x_1494_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v_x_1494_);
v_s_u2081_1496_ = v_a_1512_;
v_s_u2082_1497_ = v_a_1513_;
goto v___jp_1495_;
}
default: 
{
lean_object* v___x_1514_; 
lean_dec_ref(v_x_1493_);
lean_dec(v_x_1494_);
v___x_1514_ = lean_box(1);
return v___x_1514_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1494_))
{
case 0:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1493_);
return v___x_1515_;
}
case 3:
{
lean_object* v_a_1516_; lean_object* v_a_1517_; 
v_a_1516_ = lean_ctor_get(v_x_1493_, 0);
lean_inc(v_a_1516_);
lean_dec_ref(v_x_1493_);
v_a_1517_ = lean_ctor_get(v_x_1494_, 0);
lean_inc(v_a_1517_);
lean_dec_ref(v_x_1494_);
v_s_u2081_1496_ = v_a_1516_;
v_s_u2082_1497_ = v_a_1517_;
goto v___jp_1495_;
}
case 2:
{
lean_object* v_a_1518_; lean_object* v_a_1519_; 
v_a_1518_ = lean_ctor_get(v_x_1493_, 0);
lean_inc(v_a_1518_);
lean_dec_ref(v_x_1493_);
v_a_1519_ = lean_ctor_get(v_x_1494_, 0);
lean_inc(v_a_1519_);
lean_dec_ref(v_x_1494_);
v_s_u2081_1496_ = v_a_1518_;
v_s_u2082_1497_ = v_a_1519_;
goto v___jp_1495_;
}
default: 
{
lean_object* v___x_1520_; 
lean_dec_ref(v_x_1493_);
lean_dec(v_x_1494_);
v___x_1520_ = lean_box(1);
return v___x_1520_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1494_) == 0)
{
lean_object* v___x_1521_; 
v___x_1521_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1493_);
return v___x_1521_;
}
else
{
lean_object* v___x_1522_; 
lean_dec(v_x_1494_);
lean_dec(v_x_1493_);
v___x_1522_ = lean_box(1);
return v___x_1522_;
}
}
}
v___jp_1495_:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = l_List_appendTR___redArg(v_s_u2081_1496_, v_s_u2082_1497_);
v___x_1499_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
return v___x_1499_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1523_, lean_object* v_x_1524_){
_start:
{
if (lean_obj_tag(v_x_1524_) == 0)
{
return v_x_1523_;
}
else
{
lean_object* v_head_1525_; lean_object* v_tail_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v_head_1525_ = lean_ctor_get(v_x_1524_, 0);
v_tail_1526_ = lean_ctor_get(v_x_1524_, 1);
v___x_1527_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1528_ = lean_string_append(v_x_1523_, v___x_1527_);
v___x_1529_ = lean_string_append(v___x_1528_, v_head_1525_);
v_x_1523_ = v___x_1529_;
v_x_1524_ = v_tail_1526_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1531_, lean_object* v_x_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1531_, v_x_1532_);
lean_dec(v_x_1532_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1537_){
_start:
{
if (lean_obj_tag(v_x_1537_) == 0)
{
lean_object* v___x_1538_; 
v___x_1538_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1538_;
}
else
{
lean_object* v_tail_1539_; 
v_tail_1539_ = lean_ctor_get(v_x_1537_, 1);
if (lean_obj_tag(v_tail_1539_) == 0)
{
lean_object* v_head_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v_head_1540_ = lean_ctor_get(v_x_1537_, 0);
v___x_1541_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1542_ = lean_string_append(v___x_1541_, v_head_1540_);
v___x_1543_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1544_ = lean_string_append(v___x_1542_, v___x_1543_);
return v___x_1544_;
}
else
{
lean_object* v_head_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; uint32_t v___x_1549_; lean_object* v___x_1550_; 
v_head_1545_ = lean_ctor_get(v_x_1537_, 0);
v___x_1546_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1547_ = lean_string_append(v___x_1546_, v_head_1545_);
v___x_1548_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1547_, v_tail_1539_);
v___x_1549_ = 93;
v___x_1550_ = lean_string_push(v___x_1548_, v___x_1549_);
return v___x_1550_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1551_);
lean_dec(v_x_1551_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1556_){
_start:
{
switch(lean_obj_tag(v_x_1556_))
{
case 0:
{
lean_object* v___x_1557_; 
v___x_1557_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1557_;
}
case 1:
{
lean_object* v___x_1558_; 
v___x_1558_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1558_;
}
case 2:
{
lean_object* v_a_1559_; lean_object* v___x_1560_; 
v_a_1559_ = lean_ctor_get(v_x_1556_, 0);
v___x_1560_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1559_);
return v___x_1560_;
}
default: 
{
lean_object* v_a_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v_a_1561_ = lean_ctor_get(v_x_1556_, 0);
v___x_1562_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1563_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1561_);
v___x_1564_ = lean_string_append(v___x_1562_, v___x_1563_);
lean_dec_ref(v___x_1563_);
return v___x_1564_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1565_){
_start:
{
lean_object* v_res_1566_; 
v_res_1566_ = l_Lean_Parser_FirstTokens_toStr(v_x_1565_);
lean_dec(v_x_1565_);
return v_res_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v_x_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_box(0);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v_x_1571_){
_start:
{
lean_object* v_res_1572_; 
v_res_1572_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v_x_1571_);
lean_dec(v_x_1571_);
return v_res_1572_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__0(void){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1573_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__1(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__0, &l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__0_once, _init_l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__0);
v___x_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v_x_1576_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_obj_once(&l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__1, &l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__1_once, _init_l_Lean_Parser_instInhabitedParserInfo_default___lam__1___closed__1);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v_x_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v_x_1578_);
lean_dec_ref(v_x_1578_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1593_, lean_object* v_p_1594_){
_start:
{
lean_object* v_info_1595_; lean_object* v_fn_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1604_; 
v_info_1595_ = lean_ctor_get(v_p_1594_, 0);
v_fn_1596_ = lean_ctor_get(v_p_1594_, 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_p_1594_);
if (v_isSharedCheck_1604_ == 0)
{
v___x_1598_ = v_p_1594_;
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_fn_1596_);
lean_inc(v_info_1595_);
lean_dec(v_p_1594_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1604_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1600_ = lean_apply_1(v_f_1593_, v_fn_1596_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v___x_1600_);
v___x_1602_ = v___x_1598_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v_info_1595_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1605_, lean_object* v_p_1606_, lean_object* v_c_1607_, lean_object* v_s_1608_){
_start:
{
lean_object* v_toInputContext_1609_; lean_object* v_toParserModuleContext_1610_; lean_object* v_toCacheableParserContext_1611_; lean_object* v_tokens_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1621_; 
v_toInputContext_1609_ = lean_ctor_get(v_c_1607_, 0);
v_toParserModuleContext_1610_ = lean_ctor_get(v_c_1607_, 1);
v_toCacheableParserContext_1611_ = lean_ctor_get(v_c_1607_, 2);
v_tokens_1612_ = lean_ctor_get(v_c_1607_, 3);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_c_1607_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1614_ = v_c_1607_;
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_tokens_1612_);
lean_inc(v_toCacheableParserContext_1611_);
lean_inc(v_toParserModuleContext_1610_);
lean_inc(v_toInputContext_1609_);
lean_dec(v_c_1607_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1621_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = lean_apply_1(v_f_1605_, v_toCacheableParserContext_1611_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 2, v___x_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_toInputContext_1609_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_toParserModuleContext_1610_);
lean_ctor_set(v_reuseFailAlloc_1620_, 2, v___x_1616_);
lean_ctor_set(v_reuseFailAlloc_1620_, 3, v_tokens_1612_);
v___x_1618_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_apply_2(v_p_1606_, v___x_1618_, v_s_1608_);
return v___x_1619_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1622_, lean_object* v_p_1623_){
_start:
{
lean_object* v_info_1624_; lean_object* v_fn_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1633_; 
v_info_1624_ = lean_ctor_get(v_p_1623_, 0);
v_fn_1625_ = lean_ctor_get(v_p_1623_, 1);
v_isSharedCheck_1633_ = !lean_is_exclusive(v_p_1623_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1627_ = v_p_1623_;
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_fn_1625_);
lean_inc(v_info_1624_);
lean_dec(v_p_1623_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1633_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1629_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1629_, 0, v_f_1622_);
lean_closure_set(v___x_1629_, 1, v_fn_1625_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1629_);
v___x_1631_ = v___x_1627_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_info_1624_);
lean_ctor_set(v_reuseFailAlloc_1632_, 1, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1634_, lean_object* v_p_1635_, lean_object* v_c_1636_, lean_object* v_s_1637_){
_start:
{
lean_object* v_stxStack_1638_; lean_object* v_lhsPrec_1639_; lean_object* v_pos_1640_; lean_object* v_cache_1641_; lean_object* v_errorMsg_1642_; lean_object* v_recoveredErrors_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1682_; 
v_stxStack_1638_ = lean_ctor_get(v_s_1637_, 0);
v_lhsPrec_1639_ = lean_ctor_get(v_s_1637_, 1);
v_pos_1640_ = lean_ctor_get(v_s_1637_, 2);
v_cache_1641_ = lean_ctor_get(v_s_1637_, 3);
v_errorMsg_1642_ = lean_ctor_get(v_s_1637_, 4);
v_recoveredErrors_1643_ = lean_ctor_get(v_s_1637_, 5);
v_isSharedCheck_1682_ = !lean_is_exclusive(v_s_1637_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1645_ = v_s_1637_;
v_isShared_1646_ = v_isSharedCheck_1682_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_recoveredErrors_1643_);
lean_inc(v_errorMsg_1642_);
lean_inc(v_cache_1641_);
lean_inc(v_pos_1640_);
lean_inc(v_lhsPrec_1639_);
lean_inc(v_stxStack_1638_);
lean_dec(v_s_1637_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1682_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v_raw_1647_; lean_object* v_drop_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1681_; 
v_raw_1647_ = lean_ctor_get(v_stxStack_1638_, 0);
v_drop_1648_ = lean_ctor_get(v_stxStack_1638_, 1);
v_isSharedCheck_1681_ = !lean_is_exclusive(v_stxStack_1638_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1650_ = v_stxStack_1638_;
v_isShared_1651_ = v_isSharedCheck_1681_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_drop_1648_);
lean_inc(v_raw_1647_);
lean_dec(v_stxStack_1638_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1681_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
lean_ctor_set(v___x_1650_, 1, v_drop_1634_);
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v_raw_1647_);
lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_drop_1634_);
v___x_1653_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1655_; 
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1653_);
v___x_1655_ = v___x_1645_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1679_; 
v_reuseFailAlloc_1679_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1679_, 0, v___x_1653_);
lean_ctor_set(v_reuseFailAlloc_1679_, 1, v_lhsPrec_1639_);
lean_ctor_set(v_reuseFailAlloc_1679_, 2, v_pos_1640_);
lean_ctor_set(v_reuseFailAlloc_1679_, 3, v_cache_1641_);
lean_ctor_set(v_reuseFailAlloc_1679_, 4, v_errorMsg_1642_);
lean_ctor_set(v_reuseFailAlloc_1679_, 5, v_recoveredErrors_1643_);
v___x_1655_ = v_reuseFailAlloc_1679_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v_s_1656_; lean_object* v_stxStack_1657_; lean_object* v_lhsPrec_1658_; lean_object* v_pos_1659_; lean_object* v_cache_1660_; lean_object* v_errorMsg_1661_; lean_object* v_recoveredErrors_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1678_; 
v_s_1656_ = lean_apply_2(v_p_1635_, v_c_1636_, v___x_1655_);
v_stxStack_1657_ = lean_ctor_get(v_s_1656_, 0);
v_lhsPrec_1658_ = lean_ctor_get(v_s_1656_, 1);
v_pos_1659_ = lean_ctor_get(v_s_1656_, 2);
v_cache_1660_ = lean_ctor_get(v_s_1656_, 3);
v_errorMsg_1661_ = lean_ctor_get(v_s_1656_, 4);
v_recoveredErrors_1662_ = lean_ctor_get(v_s_1656_, 5);
v_isSharedCheck_1678_ = !lean_is_exclusive(v_s_1656_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1664_ = v_s_1656_;
v_isShared_1665_ = v_isSharedCheck_1678_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_recoveredErrors_1662_);
lean_inc(v_errorMsg_1661_);
lean_inc(v_cache_1660_);
lean_inc(v_pos_1659_);
lean_inc(v_lhsPrec_1658_);
lean_inc(v_stxStack_1657_);
lean_dec(v_s_1656_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1678_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v_raw_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1676_; 
v_raw_1666_ = lean_ctor_get(v_stxStack_1657_, 0);
v_isSharedCheck_1676_ = !lean_is_exclusive(v_stxStack_1657_);
if (v_isSharedCheck_1676_ == 0)
{
lean_object* v_unused_1677_; 
v_unused_1677_ = lean_ctor_get(v_stxStack_1657_, 1);
lean_dec(v_unused_1677_);
v___x_1668_ = v_stxStack_1657_;
v_isShared_1669_ = v_isSharedCheck_1676_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_raw_1666_);
lean_dec(v_stxStack_1657_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1676_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
lean_ctor_set(v___x_1668_, 1, v_drop_1648_);
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1675_; 
v_reuseFailAlloc_1675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1675_, 0, v_raw_1666_);
lean_ctor_set(v_reuseFailAlloc_1675_, 1, v_drop_1648_);
v___x_1671_ = v_reuseFailAlloc_1675_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
lean_object* v___x_1673_; 
if (v_isShared_1665_ == 0)
{
lean_ctor_set(v___x_1664_, 0, v___x_1671_);
v___x_1673_ = v___x_1664_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v___x_1671_);
lean_ctor_set(v_reuseFailAlloc_1674_, 1, v_lhsPrec_1658_);
lean_ctor_set(v_reuseFailAlloc_1674_, 2, v_pos_1659_);
lean_ctor_set(v_reuseFailAlloc_1674_, 3, v_cache_1660_);
lean_ctor_set(v_reuseFailAlloc_1674_, 4, v_errorMsg_1661_);
lean_ctor_set(v_reuseFailAlloc_1674_, 5, v_recoveredErrors_1662_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1683_, lean_object* v_c_1684_, lean_object* v_s_1685_){
_start:
{
lean_object* v_cache_1686_; lean_object* v_stxStack_1687_; lean_object* v_lhsPrec_1688_; lean_object* v_pos_1689_; lean_object* v_errorMsg_1690_; lean_object* v_recoveredErrors_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1731_; 
v_cache_1686_ = lean_ctor_get(v_s_1685_, 3);
v_stxStack_1687_ = lean_ctor_get(v_s_1685_, 0);
v_lhsPrec_1688_ = lean_ctor_get(v_s_1685_, 1);
v_pos_1689_ = lean_ctor_get(v_s_1685_, 2);
v_errorMsg_1690_ = lean_ctor_get(v_s_1685_, 4);
v_recoveredErrors_1691_ = lean_ctor_get(v_s_1685_, 5);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_s_1685_);
if (v_isSharedCheck_1731_ == 0)
{
v___x_1693_ = v_s_1685_;
v_isShared_1694_ = v_isSharedCheck_1731_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_recoveredErrors_1691_);
lean_inc(v_errorMsg_1690_);
lean_inc(v_cache_1686_);
lean_inc(v_pos_1689_);
lean_inc(v_lhsPrec_1688_);
lean_inc(v_stxStack_1687_);
lean_dec(v_s_1685_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1731_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v_tokenCache_1695_; lean_object* v_parserCache_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1730_; 
v_tokenCache_1695_ = lean_ctor_get(v_cache_1686_, 0);
v_parserCache_1696_ = lean_ctor_get(v_cache_1686_, 1);
v_isSharedCheck_1730_ = !lean_is_exclusive(v_cache_1686_);
if (v_isSharedCheck_1730_ == 0)
{
v___x_1698_ = v_cache_1686_;
v_isShared_1699_ = v_isSharedCheck_1730_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_parserCache_1696_);
lean_inc(v_tokenCache_1695_);
lean_dec(v_cache_1686_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1730_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1702_; 
v___x_1700_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v___x_1700_);
v___x_1702_ = v___x_1698_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v_tokenCache_1695_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v___x_1700_);
v___x_1702_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
lean_object* v___x_1704_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 3, v___x_1702_);
v___x_1704_ = v___x_1693_;
goto v_reusejp_1703_;
}
else
{
lean_object* v_reuseFailAlloc_1728_; 
v_reuseFailAlloc_1728_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1728_, 0, v_stxStack_1687_);
lean_ctor_set(v_reuseFailAlloc_1728_, 1, v_lhsPrec_1688_);
lean_ctor_set(v_reuseFailAlloc_1728_, 2, v_pos_1689_);
lean_ctor_set(v_reuseFailAlloc_1728_, 3, v___x_1702_);
lean_ctor_set(v_reuseFailAlloc_1728_, 4, v_errorMsg_1690_);
lean_ctor_set(v_reuseFailAlloc_1728_, 5, v_recoveredErrors_1691_);
v___x_1704_ = v_reuseFailAlloc_1728_;
goto v_reusejp_1703_;
}
v_reusejp_1703_:
{
lean_object* v_s_x27_1705_; lean_object* v_cache_1706_; lean_object* v_stxStack_1707_; lean_object* v_lhsPrec_1708_; lean_object* v_pos_1709_; lean_object* v_errorMsg_1710_; lean_object* v_recoveredErrors_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1727_; 
v_s_x27_1705_ = lean_apply_2(v_p_1683_, v_c_1684_, v___x_1704_);
v_cache_1706_ = lean_ctor_get(v_s_x27_1705_, 3);
v_stxStack_1707_ = lean_ctor_get(v_s_x27_1705_, 0);
v_lhsPrec_1708_ = lean_ctor_get(v_s_x27_1705_, 1);
v_pos_1709_ = lean_ctor_get(v_s_x27_1705_, 2);
v_errorMsg_1710_ = lean_ctor_get(v_s_x27_1705_, 4);
v_recoveredErrors_1711_ = lean_ctor_get(v_s_x27_1705_, 5);
v_isSharedCheck_1727_ = !lean_is_exclusive(v_s_x27_1705_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1713_ = v_s_x27_1705_;
v_isShared_1714_ = v_isSharedCheck_1727_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_recoveredErrors_1711_);
lean_inc(v_errorMsg_1710_);
lean_inc(v_cache_1706_);
lean_inc(v_pos_1709_);
lean_inc(v_lhsPrec_1708_);
lean_inc(v_stxStack_1707_);
lean_dec(v_s_x27_1705_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1727_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_tokenCache_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1725_; 
v_tokenCache_1715_ = lean_ctor_get(v_cache_1706_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_cache_1706_);
if (v_isSharedCheck_1725_ == 0)
{
lean_object* v_unused_1726_; 
v_unused_1726_ = lean_ctor_get(v_cache_1706_, 1);
lean_dec(v_unused_1726_);
v___x_1717_ = v_cache_1706_;
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_tokenCache_1715_);
lean_dec(v_cache_1706_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1725_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 1, v_parserCache_1696_);
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_tokenCache_1715_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_parserCache_1696_);
v___x_1720_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
lean_object* v___x_1722_; 
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 3, v___x_1720_);
v___x_1722_ = v___x_1713_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_stxStack_1707_);
lean_ctor_set(v_reuseFailAlloc_1723_, 1, v_lhsPrec_1708_);
lean_ctor_set(v_reuseFailAlloc_1723_, 2, v_pos_1709_);
lean_ctor_set(v_reuseFailAlloc_1723_, 3, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1723_, 4, v_errorMsg_1710_);
lean_ctor_set(v_reuseFailAlloc_1723_, 5, v_recoveredErrors_1711_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1732_, lean_object* v_a_1733_, lean_object* v_a_1734_){
_start:
{
lean_object* v___f_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
v___f_1735_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1735_, 0, v_p_1732_);
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1736_, v___f_1735_, v_a_1733_, v_a_1734_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1738_){
_start:
{
lean_object* v_info_1739_; lean_object* v_fn_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1748_; 
v_info_1739_ = lean_ctor_get(v_p_1738_, 0);
v_fn_1740_ = lean_ctor_get(v_p_1738_, 1);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_p_1738_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1742_ = v_p_1738_;
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_fn_1740_);
lean_inc(v_info_1739_);
lean_dec(v_p_1738_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1748_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1744_; lean_object* v___x_1746_; 
v___x_1744_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1744_, 0, v_fn_1740_);
if (v_isShared_1743_ == 0)
{
lean_ctor_set(v___x_1742_, 1, v___x_1744_);
v___x_1746_ = v___x_1742_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_info_1739_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v___x_1744_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1749_, lean_object* v_p_1750_, lean_object* v_c_1751_, lean_object* v_s_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_apply_1(v_f_1749_, v_c_1751_);
v___x_1754_ = lean_apply_2(v_p_1750_, v___x_1753_, v_s_1752_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1755_, lean_object* v_p_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_){
_start:
{
lean_object* v___f_1759_; lean_object* v___x_1760_; 
v___f_1759_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1759_, 0, v_f_1755_);
lean_closure_set(v___f_1759_, 1, v_p_1756_);
v___x_1760_ = l_Lean_Parser_withResetCacheFn(v___f_1759_, v_a_1757_, v_a_1758_);
return v___x_1760_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1761_, lean_object* v_x_1762_){
_start:
{
if (lean_obj_tag(v_x_1762_) == 0)
{
uint8_t v___x_1763_; 
v___x_1763_ = 0;
return v___x_1763_;
}
else
{
lean_object* v_key_1764_; lean_object* v_tail_1765_; uint8_t v___x_1766_; 
v_key_1764_ = lean_ctor_get(v_x_1762_, 0);
v_tail_1765_ = lean_ctor_get(v_x_1762_, 2);
v___x_1766_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1764_, v_a_1761_);
if (v___x_1766_ == 0)
{
v_x_1762_ = v_tail_1765_;
goto _start;
}
else
{
return v___x_1766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1768_, lean_object* v_x_1769_){
_start:
{
uint8_t v_res_1770_; lean_object* v_r_1771_; 
v_res_1770_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1768_, v_x_1769_);
lean_dec(v_x_1769_);
lean_dec_ref(v_a_1768_);
v_r_1771_ = lean_box(v_res_1770_);
return v_r_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1772_, lean_object* v_x_1773_){
_start:
{
if (lean_obj_tag(v_x_1773_) == 0)
{
return v_x_1772_;
}
else
{
lean_object* v_key_1774_; lean_object* v_value_1775_; lean_object* v_tail_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1806_; 
v_key_1774_ = lean_ctor_get(v_x_1773_, 0);
v_value_1775_ = lean_ctor_get(v_x_1773_, 1);
v_tail_1776_ = lean_ctor_get(v_x_1773_, 2);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_x_1773_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1778_ = v_x_1773_;
v_isShared_1779_ = v_isSharedCheck_1806_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_tail_1776_);
lean_inc(v_value_1775_);
lean_inc(v_key_1774_);
lean_dec(v_x_1773_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1806_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v_parserName_1780_; lean_object* v_pos_1781_; lean_object* v___x_1782_; uint64_t v___x_1783_; uint64_t v___y_1785_; 
v_parserName_1780_ = lean_ctor_get(v_key_1774_, 1);
v_pos_1781_ = lean_ctor_get(v_key_1774_, 2);
v___x_1782_ = lean_array_get_size(v_x_1772_);
v___x_1783_ = l_String_instHashableRaw_hash(v_pos_1781_);
if (lean_obj_tag(v_parserName_1780_) == 0)
{
uint64_t v___x_1804_; 
v___x_1804_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1785_ = v___x_1804_;
goto v___jp_1784_;
}
else
{
uint64_t v_hash_1805_; 
v_hash_1805_ = lean_ctor_get_uint64(v_parserName_1780_, sizeof(void*)*2);
v___y_1785_ = v_hash_1805_;
goto v___jp_1784_;
}
v___jp_1784_:
{
uint64_t v___x_1786_; uint64_t v___x_1787_; uint64_t v___x_1788_; uint64_t v_fold_1789_; uint64_t v___x_1790_; uint64_t v___x_1791_; uint64_t v___x_1792_; size_t v___x_1793_; size_t v___x_1794_; size_t v___x_1795_; size_t v___x_1796_; size_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1786_ = lean_uint64_mix_hash(v___x_1783_, v___y_1785_);
v___x_1787_ = 32ULL;
v___x_1788_ = lean_uint64_shift_right(v___x_1786_, v___x_1787_);
v_fold_1789_ = lean_uint64_xor(v___x_1786_, v___x_1788_);
v___x_1790_ = 16ULL;
v___x_1791_ = lean_uint64_shift_right(v_fold_1789_, v___x_1790_);
v___x_1792_ = lean_uint64_xor(v_fold_1789_, v___x_1791_);
v___x_1793_ = lean_uint64_to_usize(v___x_1792_);
v___x_1794_ = lean_usize_of_nat(v___x_1782_);
v___x_1795_ = ((size_t)1ULL);
v___x_1796_ = lean_usize_sub(v___x_1794_, v___x_1795_);
v___x_1797_ = lean_usize_land(v___x_1793_, v___x_1796_);
v___x_1798_ = lean_array_uget_borrowed(v_x_1772_, v___x_1797_);
lean_inc(v___x_1798_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 2, v___x_1798_);
v___x_1800_ = v___x_1778_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_key_1774_);
lean_ctor_set(v_reuseFailAlloc_1803_, 1, v_value_1775_);
lean_ctor_set(v_reuseFailAlloc_1803_, 2, v___x_1798_);
v___x_1800_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_array_uset(v_x_1772_, v___x_1797_, v___x_1800_);
v_x_1772_ = v___x_1801_;
v_x_1773_ = v_tail_1776_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1807_, lean_object* v_source_1808_, lean_object* v_target_1809_){
_start:
{
lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1810_ = lean_array_get_size(v_source_1808_);
v___x_1811_ = lean_nat_dec_lt(v_i_1807_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_dec_ref(v_source_1808_);
lean_dec(v_i_1807_);
return v_target_1809_;
}
else
{
lean_object* v_es_1812_; lean_object* v___x_1813_; lean_object* v_source_1814_; lean_object* v_target_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v_es_1812_ = lean_array_fget(v_source_1808_, v_i_1807_);
v___x_1813_ = lean_box(0);
v_source_1814_ = lean_array_fset(v_source_1808_, v_i_1807_, v___x_1813_);
v_target_1815_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1809_, v_es_1812_);
v___x_1816_ = lean_unsigned_to_nat(1u);
v___x_1817_ = lean_nat_add(v_i_1807_, v___x_1816_);
lean_dec(v_i_1807_);
v_i_1807_ = v___x_1817_;
v_source_1808_ = v_source_1814_;
v_target_1809_ = v_target_1815_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1819_){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v_nbuckets_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1820_ = lean_array_get_size(v_data_1819_);
v___x_1821_ = lean_unsigned_to_nat(2u);
v_nbuckets_1822_ = lean_nat_mul(v___x_1820_, v___x_1821_);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = lean_box(0);
v___x_1825_ = lean_mk_array(v_nbuckets_1822_, v___x_1824_);
v___x_1826_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1823_, v_data_1819_, v___x_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1827_, lean_object* v_b_1828_, lean_object* v_x_1829_){
_start:
{
if (lean_obj_tag(v_x_1829_) == 0)
{
lean_dec(v_b_1828_);
lean_dec_ref(v_a_1827_);
return v_x_1829_;
}
else
{
lean_object* v_key_1830_; lean_object* v_value_1831_; lean_object* v_tail_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1844_; 
v_key_1830_ = lean_ctor_get(v_x_1829_, 0);
v_value_1831_ = lean_ctor_get(v_x_1829_, 1);
v_tail_1832_ = lean_ctor_get(v_x_1829_, 2);
v_isSharedCheck_1844_ = !lean_is_exclusive(v_x_1829_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1834_ = v_x_1829_;
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_tail_1832_);
lean_inc(v_value_1831_);
lean_inc(v_key_1830_);
lean_dec(v_x_1829_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1844_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
uint8_t v___x_1836_; 
v___x_1836_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1830_, v_a_1827_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
v___x_1837_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1827_, v_b_1828_, v_tail_1832_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 2, v___x_1837_);
v___x_1839_ = v___x_1834_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_key_1830_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_value_1831_);
lean_ctor_set(v_reuseFailAlloc_1840_, 2, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
lean_object* v___x_1842_; 
lean_dec(v_value_1831_);
lean_dec(v_key_1830_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v_b_1828_);
lean_ctor_set(v___x_1834_, 0, v_a_1827_);
v___x_1842_ = v___x_1834_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1827_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_b_1828_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_tail_1832_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1845_, lean_object* v_a_1846_, lean_object* v_b_1847_){
_start:
{
lean_object* v_size_1848_; lean_object* v_buckets_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1899_; 
v_size_1848_ = lean_ctor_get(v_m_1845_, 0);
v_buckets_1849_ = lean_ctor_get(v_m_1845_, 1);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_m_1845_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1851_ = v_m_1845_;
v_isShared_1852_ = v_isSharedCheck_1899_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_buckets_1849_);
lean_inc(v_size_1848_);
lean_dec(v_m_1845_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1899_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v_parserName_1853_; lean_object* v_pos_1854_; lean_object* v___x_1855_; uint64_t v___x_1856_; uint64_t v___y_1858_; 
v_parserName_1853_ = lean_ctor_get(v_a_1846_, 1);
v_pos_1854_ = lean_ctor_get(v_a_1846_, 2);
v___x_1855_ = lean_array_get_size(v_buckets_1849_);
v___x_1856_ = l_String_instHashableRaw_hash(v_pos_1854_);
if (lean_obj_tag(v_parserName_1853_) == 0)
{
uint64_t v___x_1897_; 
v___x_1897_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1858_ = v___x_1897_;
goto v___jp_1857_;
}
else
{
uint64_t v_hash_1898_; 
v_hash_1898_ = lean_ctor_get_uint64(v_parserName_1853_, sizeof(void*)*2);
v___y_1858_ = v_hash_1898_;
goto v___jp_1857_;
}
v___jp_1857_:
{
uint64_t v___x_1859_; uint64_t v___x_1860_; uint64_t v___x_1861_; uint64_t v_fold_1862_; uint64_t v___x_1863_; uint64_t v___x_1864_; uint64_t v___x_1865_; size_t v___x_1866_; size_t v___x_1867_; size_t v___x_1868_; size_t v___x_1869_; size_t v___x_1870_; lean_object* v_bkt_1871_; uint8_t v___x_1872_; 
v___x_1859_ = lean_uint64_mix_hash(v___x_1856_, v___y_1858_);
v___x_1860_ = 32ULL;
v___x_1861_ = lean_uint64_shift_right(v___x_1859_, v___x_1860_);
v_fold_1862_ = lean_uint64_xor(v___x_1859_, v___x_1861_);
v___x_1863_ = 16ULL;
v___x_1864_ = lean_uint64_shift_right(v_fold_1862_, v___x_1863_);
v___x_1865_ = lean_uint64_xor(v_fold_1862_, v___x_1864_);
v___x_1866_ = lean_uint64_to_usize(v___x_1865_);
v___x_1867_ = lean_usize_of_nat(v___x_1855_);
v___x_1868_ = ((size_t)1ULL);
v___x_1869_ = lean_usize_sub(v___x_1867_, v___x_1868_);
v___x_1870_ = lean_usize_land(v___x_1866_, v___x_1869_);
v_bkt_1871_ = lean_array_uget_borrowed(v_buckets_1849_, v___x_1870_);
v___x_1872_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1846_, v_bkt_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; lean_object* v_size_x27_1874_; lean_object* v___x_1875_; lean_object* v_buckets_x27_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; uint8_t v___x_1882_; 
v___x_1873_ = lean_unsigned_to_nat(1u);
v_size_x27_1874_ = lean_nat_add(v_size_1848_, v___x_1873_);
lean_dec(v_size_1848_);
lean_inc(v_bkt_1871_);
v___x_1875_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1875_, 0, v_a_1846_);
lean_ctor_set(v___x_1875_, 1, v_b_1847_);
lean_ctor_set(v___x_1875_, 2, v_bkt_1871_);
v_buckets_x27_1876_ = lean_array_uset(v_buckets_1849_, v___x_1870_, v___x_1875_);
v___x_1877_ = lean_unsigned_to_nat(4u);
v___x_1878_ = lean_nat_mul(v_size_x27_1874_, v___x_1877_);
v___x_1879_ = lean_unsigned_to_nat(3u);
v___x_1880_ = lean_nat_div(v___x_1878_, v___x_1879_);
lean_dec(v___x_1878_);
v___x_1881_ = lean_array_get_size(v_buckets_x27_1876_);
v___x_1882_ = lean_nat_dec_le(v___x_1880_, v___x_1881_);
lean_dec(v___x_1880_);
if (v___x_1882_ == 0)
{
lean_object* v_val_1883_; lean_object* v___x_1885_; 
v_val_1883_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_1876_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v_val_1883_);
lean_ctor_set(v___x_1851_, 0, v_size_x27_1874_);
v___x_1885_ = v___x_1851_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_size_x27_1874_);
lean_ctor_set(v_reuseFailAlloc_1886_, 1, v_val_1883_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
else
{
lean_object* v___x_1888_; 
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v_buckets_x27_1876_);
lean_ctor_set(v___x_1851_, 0, v_size_x27_1874_);
v___x_1888_ = v___x_1851_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_size_x27_1874_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v_buckets_x27_1876_);
v___x_1888_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
return v___x_1888_;
}
}
}
else
{
lean_object* v___x_1890_; lean_object* v_buckets_x27_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1895_; 
lean_inc(v_bkt_1871_);
v___x_1890_ = lean_box(0);
v_buckets_x27_1891_ = lean_array_uset(v_buckets_1849_, v___x_1870_, v___x_1890_);
v___x_1892_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1846_, v_b_1847_, v_bkt_1871_);
v___x_1893_ = lean_array_uset(v_buckets_x27_1891_, v___x_1870_, v___x_1892_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 1, v___x_1893_);
v___x_1895_ = v___x_1851_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_size_1848_);
lean_ctor_set(v_reuseFailAlloc_1896_, 1, v___x_1893_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_1900_, lean_object* v_x_1901_){
_start:
{
if (lean_obj_tag(v_x_1901_) == 0)
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_box(0);
return v___x_1902_;
}
else
{
lean_object* v_key_1903_; lean_object* v_value_1904_; lean_object* v_tail_1905_; uint8_t v___x_1906_; 
v_key_1903_ = lean_ctor_get(v_x_1901_, 0);
v_value_1904_ = lean_ctor_get(v_x_1901_, 1);
v_tail_1905_ = lean_ctor_get(v_x_1901_, 2);
v___x_1906_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1903_, v_a_1900_);
if (v___x_1906_ == 0)
{
v_x_1901_ = v_tail_1905_;
goto _start;
}
else
{
lean_object* v___x_1908_; 
lean_inc(v_value_1904_);
v___x_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1908_, 0, v_value_1904_);
return v___x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_1909_, lean_object* v_x_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_1909_, v_x_1910_);
lean_dec(v_x_1910_);
lean_dec_ref(v_a_1909_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v_buckets_1914_; lean_object* v_parserName_1915_; lean_object* v_pos_1916_; lean_object* v___x_1917_; uint64_t v___x_1918_; uint64_t v___y_1920_; 
v_buckets_1914_ = lean_ctor_get(v_m_1912_, 1);
v_parserName_1915_ = lean_ctor_get(v_a_1913_, 1);
v_pos_1916_ = lean_ctor_get(v_a_1913_, 2);
v___x_1917_ = lean_array_get_size(v_buckets_1914_);
v___x_1918_ = l_String_instHashableRaw_hash(v_pos_1916_);
if (lean_obj_tag(v_parserName_1915_) == 0)
{
uint64_t v___x_1935_; 
v___x_1935_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1920_ = v___x_1935_;
goto v___jp_1919_;
}
else
{
uint64_t v_hash_1936_; 
v_hash_1936_ = lean_ctor_get_uint64(v_parserName_1915_, sizeof(void*)*2);
v___y_1920_ = v_hash_1936_;
goto v___jp_1919_;
}
v___jp_1919_:
{
uint64_t v___x_1921_; uint64_t v___x_1922_; uint64_t v___x_1923_; uint64_t v_fold_1924_; uint64_t v___x_1925_; uint64_t v___x_1926_; uint64_t v___x_1927_; size_t v___x_1928_; size_t v___x_1929_; size_t v___x_1930_; size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1921_ = lean_uint64_mix_hash(v___x_1918_, v___y_1920_);
v___x_1922_ = 32ULL;
v___x_1923_ = lean_uint64_shift_right(v___x_1921_, v___x_1922_);
v_fold_1924_ = lean_uint64_xor(v___x_1921_, v___x_1923_);
v___x_1925_ = 16ULL;
v___x_1926_ = lean_uint64_shift_right(v_fold_1924_, v___x_1925_);
v___x_1927_ = lean_uint64_xor(v_fold_1924_, v___x_1926_);
v___x_1928_ = lean_uint64_to_usize(v___x_1927_);
v___x_1929_ = lean_usize_of_nat(v___x_1917_);
v___x_1930_ = ((size_t)1ULL);
v___x_1931_ = lean_usize_sub(v___x_1929_, v___x_1930_);
v___x_1932_ = lean_usize_land(v___x_1928_, v___x_1931_);
v___x_1933_ = lean_array_uget_borrowed(v_buckets_1914_, v___x_1932_);
v___x_1934_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_1913_, v___x_1933_);
return v___x_1934_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_1937_, lean_object* v_a_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_1937_, v_a_1938_);
lean_dec_ref(v_a_1938_);
lean_dec_ref(v_m_1937_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_1940_, lean_object* v_p_1941_, lean_object* v_c_1942_, lean_object* v_s_1943_){
_start:
{
lean_object* v_cache_1944_; lean_object* v_toCacheableParserContext_1945_; lean_object* v_stxStack_1946_; lean_object* v_pos_1947_; lean_object* v_recoveredErrors_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1997_; 
v_cache_1944_ = lean_ctor_get(v_s_1943_, 3);
lean_inc_ref(v_cache_1944_);
v_toCacheableParserContext_1945_ = lean_ctor_get(v_c_1942_, 2);
v_stxStack_1946_ = lean_ctor_get(v_s_1943_, 0);
v_pos_1947_ = lean_ctor_get(v_s_1943_, 2);
v_recoveredErrors_1948_ = lean_ctor_get(v_s_1943_, 5);
v_isSharedCheck_1997_ = !lean_is_exclusive(v_s_1943_);
if (v_isSharedCheck_1997_ == 0)
{
lean_object* v_unused_1998_; lean_object* v_unused_1999_; lean_object* v_unused_2000_; 
v_unused_1998_ = lean_ctor_get(v_s_1943_, 4);
lean_dec(v_unused_1998_);
v_unused_1999_ = lean_ctor_get(v_s_1943_, 3);
lean_dec(v_unused_1999_);
v_unused_2000_ = lean_ctor_get(v_s_1943_, 1);
lean_dec(v_unused_2000_);
v___x_1950_ = v_s_1943_;
v_isShared_1951_ = v_isSharedCheck_1997_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_recoveredErrors_1948_);
lean_inc(v_pos_1947_);
lean_inc(v_stxStack_1946_);
lean_dec(v_s_1943_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1997_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
lean_object* v_parserCache_1952_; lean_object* v_key_1953_; lean_object* v___x_1954_; 
v_parserCache_1952_ = lean_ctor_get(v_cache_1944_, 1);
lean_inc(v_pos_1947_);
lean_inc_ref(v_toCacheableParserContext_1945_);
v_key_1953_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_1953_, 0, v_toCacheableParserContext_1945_);
lean_ctor_set(v_key_1953_, 1, v_parserName_1940_);
lean_ctor_set(v_key_1953_, 2, v_pos_1947_);
v___x_1954_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_1952_, v_key_1953_);
if (lean_obj_tag(v___x_1954_) == 1)
{
lean_object* v_val_1955_; lean_object* v_stx_1956_; lean_object* v_lhsPrec_1957_; lean_object* v_newPos_1958_; lean_object* v_errorMsg_1959_; lean_object* v___x_1960_; lean_object* v___x_1962_; 
lean_dec_ref(v_key_1953_);
lean_dec(v_pos_1947_);
lean_dec_ref(v_c_1942_);
lean_dec_ref(v_p_1941_);
v_val_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_val_1955_);
lean_dec_ref(v___x_1954_);
v_stx_1956_ = lean_ctor_get(v_val_1955_, 0);
lean_inc(v_stx_1956_);
v_lhsPrec_1957_ = lean_ctor_get(v_val_1955_, 1);
lean_inc(v_lhsPrec_1957_);
v_newPos_1958_ = lean_ctor_get(v_val_1955_, 2);
lean_inc(v_newPos_1958_);
v_errorMsg_1959_ = lean_ctor_get(v_val_1955_, 3);
lean_inc(v_errorMsg_1959_);
lean_dec(v_val_1955_);
v___x_1960_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1946_, v_stx_1956_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 4, v_errorMsg_1959_);
lean_ctor_set(v___x_1950_, 2, v_newPos_1958_);
lean_ctor_set(v___x_1950_, 1, v_lhsPrec_1957_);
lean_ctor_set(v___x_1950_, 0, v___x_1960_);
v___x_1962_ = v___x_1950_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
lean_ctor_set(v_reuseFailAlloc_1963_, 1, v_lhsPrec_1957_);
lean_ctor_set(v_reuseFailAlloc_1963_, 2, v_newPos_1958_);
lean_ctor_set(v_reuseFailAlloc_1963_, 3, v_cache_1944_);
lean_ctor_set(v_reuseFailAlloc_1963_, 4, v_errorMsg_1959_);
lean_ctor_set(v_reuseFailAlloc_1963_, 5, v_recoveredErrors_1948_);
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
lean_object* v_raw_1964_; lean_object* v_initStackSz_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
lean_dec(v___x_1954_);
v_raw_1964_ = lean_ctor_get(v_stxStack_1946_, 0);
v_initStackSz_1965_ = lean_array_get_size(v_raw_1964_);
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = lean_box(0);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 4, v___x_1967_);
lean_ctor_set(v___x_1950_, 1, v___x_1966_);
v___x_1969_ = v___x_1950_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1996_; 
v_reuseFailAlloc_1996_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_stxStack_1946_);
lean_ctor_set(v_reuseFailAlloc_1996_, 1, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1996_, 2, v_pos_1947_);
lean_ctor_set(v_reuseFailAlloc_1996_, 3, v_cache_1944_);
lean_ctor_set(v_reuseFailAlloc_1996_, 4, v___x_1967_);
lean_ctor_set(v_reuseFailAlloc_1996_, 5, v_recoveredErrors_1948_);
v___x_1969_ = v_reuseFailAlloc_1996_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v_s_1970_; lean_object* v_cache_1971_; lean_object* v_stxStack_1972_; lean_object* v_lhsPrec_1973_; lean_object* v_pos_1974_; lean_object* v_errorMsg_1975_; lean_object* v_recoveredErrors_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1995_; 
v_s_1970_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_1965_, v_p_1941_, v_c_1942_, v___x_1969_);
v_cache_1971_ = lean_ctor_get(v_s_1970_, 3);
v_stxStack_1972_ = lean_ctor_get(v_s_1970_, 0);
v_lhsPrec_1973_ = lean_ctor_get(v_s_1970_, 1);
v_pos_1974_ = lean_ctor_get(v_s_1970_, 2);
v_errorMsg_1975_ = lean_ctor_get(v_s_1970_, 4);
v_recoveredErrors_1976_ = lean_ctor_get(v_s_1970_, 5);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_s_1970_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1978_ = v_s_1970_;
v_isShared_1979_ = v_isSharedCheck_1995_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_recoveredErrors_1976_);
lean_inc(v_errorMsg_1975_);
lean_inc(v_cache_1971_);
lean_inc(v_pos_1974_);
lean_inc(v_lhsPrec_1973_);
lean_inc(v_stxStack_1972_);
lean_dec(v_s_1970_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1995_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v_tokenCache_1980_; lean_object* v_parserCache_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1994_; 
v_tokenCache_1980_ = lean_ctor_get(v_cache_1971_, 0);
v_parserCache_1981_ = lean_ctor_get(v_cache_1971_, 1);
v_isSharedCheck_1994_ = !lean_is_exclusive(v_cache_1971_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1983_ = v_cache_1971_;
v_isShared_1984_ = v_isSharedCheck_1994_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_parserCache_1981_);
lean_inc(v_tokenCache_1980_);
lean_dec(v_cache_1971_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1994_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1985_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1972_);
lean_inc(v_errorMsg_1975_);
lean_inc(v_pos_1974_);
lean_inc(v_lhsPrec_1973_);
v___x_1986_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1986_, 0, v___x_1985_);
lean_ctor_set(v___x_1986_, 1, v_lhsPrec_1973_);
lean_ctor_set(v___x_1986_, 2, v_pos_1974_);
lean_ctor_set(v___x_1986_, 3, v_errorMsg_1975_);
v___x_1987_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_1981_, v_key_1953_, v___x_1986_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 1, v___x_1987_);
v___x_1989_ = v___x_1983_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_tokenCache_1980_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
lean_object* v___x_1991_; 
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 3, v___x_1989_);
v___x_1991_ = v___x_1978_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_stxStack_1972_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_lhsPrec_1973_);
lean_ctor_set(v_reuseFailAlloc_1992_, 2, v_pos_1974_);
lean_ctor_set(v_reuseFailAlloc_1992_, 3, v___x_1989_);
lean_ctor_set(v_reuseFailAlloc_1992_, 4, v_errorMsg_1975_);
lean_ctor_set(v_reuseFailAlloc_1992_, 5, v_recoveredErrors_1976_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2001_, lean_object* v_m_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2002_, v_a_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2005_, lean_object* v_m_2006_, lean_object* v_a_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2005_, v_m_2006_, v_a_2007_);
lean_dec_ref(v_a_2007_);
lean_dec_ref(v_m_2006_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2009_, lean_object* v_m_2010_, lean_object* v_a_2011_, lean_object* v_b_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2010_, v_a_2011_, v_b_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2014_, lean_object* v_a_2015_, lean_object* v_x_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2015_, v_x_2016_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2018_, lean_object* v_a_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2018_, v_a_2019_, v_x_2020_);
lean_dec(v_x_2020_);
lean_dec_ref(v_a_2019_);
return v_res_2021_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2022_, lean_object* v_a_2023_, lean_object* v_x_2024_){
_start:
{
uint8_t v___x_2025_; 
v___x_2025_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2023_, v_x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2026_, lean_object* v_a_2027_, lean_object* v_x_2028_){
_start:
{
uint8_t v_res_2029_; lean_object* v_r_2030_; 
v_res_2029_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2026_, v_a_2027_, v_x_2028_);
lean_dec(v_x_2028_);
lean_dec_ref(v_a_2027_);
v_r_2030_ = lean_box(v_res_2029_);
return v_r_2030_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2031_, lean_object* v_data_2032_){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2032_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2034_, lean_object* v_a_2035_, lean_object* v_b_2036_, lean_object* v_x_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2035_, v_b_2036_, v_x_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2039_, lean_object* v_i_2040_, lean_object* v_source_2041_, lean_object* v_target_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2040_, v_source_2041_, v_target_2042_);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2044_, lean_object* v_x_2045_, lean_object* v_x_2046_){
_start:
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2045_, v_x_2046_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2048_, lean_object* v_p_2049_){
_start:
{
lean_object* v_info_2050_; lean_object* v_fn_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2059_; 
v_info_2050_ = lean_ctor_get(v_p_2049_, 0);
v_fn_2051_ = lean_ctor_get(v_p_2049_, 1);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_p_2049_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_2053_ = v_p_2049_;
v_isShared_2054_ = v_isSharedCheck_2059_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_fn_2051_);
lean_inc(v_info_2050_);
lean_dec(v_p_2049_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2059_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2055_, 0, v_parserName_2048_);
lean_closure_set(v___x_2055_, 1, v_fn_2051_);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 1, v___x_2055_);
v___x_2057_ = v___x_2053_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_info_2050_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = ((lean_object*)(l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2068_ = ((lean_object*)(l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2069_ = l_Lean_addBuiltinDocString(v___x_2067_, v___x_2068_);
return v___x_2069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2076_, lean_object* v_ictx_2077_, lean_object* v_pmctx_2078_, lean_object* v_tokens_2079_, lean_object* v_s_2080_){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__0));
v___x_2082_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2082_, 0, v_ictx_2077_);
lean_ctor_set(v___x_2082_, 1, v_pmctx_2078_);
lean_ctor_set(v___x_2082_, 2, v___x_2081_);
lean_ctor_set(v___x_2082_, 3, v_tokens_2079_);
v___x_2083_ = lean_apply_2(v_p_2076_, v___x_2082_, v_s_2080_);
return v___x_2083_;
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
res = l_Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
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
