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
static lean_object* _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0(void){
_start:
{
lean_object* v___x_452_; lean_object* v___f_453_; 
v___x_452_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_453_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_453_, 0, v___x_452_);
return v___f_453_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext___lam__0(lean_object* v___f_454_, lean_object* v_a_455_, lean_object* v_b_456_){
_start:
{
lean_object* v_prec_457_; lean_object* v_quotDepth_458_; uint8_t v_suppressInsideQuot_459_; lean_object* v_savedPos_x3f_460_; lean_object* v_forbiddenTks_461_; lean_object* v_prec_462_; lean_object* v_quotDepth_463_; uint8_t v_suppressInsideQuot_464_; lean_object* v_savedPos_x3f_465_; lean_object* v_forbiddenTks_466_; uint8_t v___x_477_; 
v_prec_457_ = lean_ctor_get(v_a_455_, 0);
lean_inc(v_prec_457_);
v_quotDepth_458_ = lean_ctor_get(v_a_455_, 1);
lean_inc(v_quotDepth_458_);
v_suppressInsideQuot_459_ = lean_ctor_get_uint8(v_a_455_, sizeof(void*)*4);
v_savedPos_x3f_460_ = lean_ctor_get(v_a_455_, 2);
lean_inc(v_savedPos_x3f_460_);
v_forbiddenTks_461_ = lean_ctor_get(v_a_455_, 3);
lean_inc_ref(v_forbiddenTks_461_);
lean_dec_ref(v_a_455_);
v_prec_462_ = lean_ctor_get(v_b_456_, 0);
lean_inc(v_prec_462_);
v_quotDepth_463_ = lean_ctor_get(v_b_456_, 1);
lean_inc(v_quotDepth_463_);
v_suppressInsideQuot_464_ = lean_ctor_get_uint8(v_b_456_, sizeof(void*)*4);
v_savedPos_x3f_465_ = lean_ctor_get(v_b_456_, 2);
lean_inc(v_savedPos_x3f_465_);
v_forbiddenTks_466_ = lean_ctor_get(v_b_456_, 3);
lean_inc_ref(v_forbiddenTks_466_);
lean_dec_ref(v_b_456_);
v___x_477_ = lean_nat_dec_eq(v_prec_457_, v_prec_462_);
lean_dec(v_prec_462_);
lean_dec(v_prec_457_);
if (v___x_477_ == 0)
{
lean_dec_ref(v_forbiddenTks_466_);
lean_dec(v_savedPos_x3f_465_);
lean_dec(v_quotDepth_463_);
lean_dec_ref(v_forbiddenTks_461_);
lean_dec(v_savedPos_x3f_460_);
lean_dec(v_quotDepth_458_);
lean_dec_ref(v___f_454_);
return v___x_477_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = lean_nat_dec_eq(v_quotDepth_458_, v_quotDepth_463_);
lean_dec(v_quotDepth_463_);
lean_dec(v_quotDepth_458_);
if (v___x_478_ == 0)
{
lean_dec_ref(v_forbiddenTks_466_);
lean_dec(v_savedPos_x3f_465_);
lean_dec_ref(v_forbiddenTks_461_);
lean_dec(v_savedPos_x3f_460_);
lean_dec_ref(v___f_454_);
return v___x_478_;
}
else
{
if (v_suppressInsideQuot_459_ == 0)
{
if (v_suppressInsideQuot_464_ == 0)
{
goto v___jp_467_;
}
else
{
lean_dec_ref(v_forbiddenTks_466_);
lean_dec(v_savedPos_x3f_465_);
lean_dec_ref(v_forbiddenTks_461_);
lean_dec(v_savedPos_x3f_460_);
lean_dec_ref(v___f_454_);
return v_suppressInsideQuot_459_;
}
}
else
{
if (v_suppressInsideQuot_464_ == 0)
{
lean_dec_ref(v_forbiddenTks_466_);
lean_dec(v_savedPos_x3f_465_);
lean_dec_ref(v_forbiddenTks_461_);
lean_dec(v_savedPos_x3f_460_);
lean_dec_ref(v___f_454_);
return v_suppressInsideQuot_464_;
}
else
{
goto v___jp_467_;
}
}
}
}
v___jp_467_:
{
lean_object* v___f_468_; uint8_t v___x_469_; 
v___f_468_ = lean_obj_once(&l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0, &l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0_once, _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0);
v___x_469_ = l_Option_instBEq_beq___redArg(v___f_468_, v_savedPos_x3f_460_, v_savedPos_x3f_465_);
if (v___x_469_ == 0)
{
lean_dec_ref(v_forbiddenTks_466_);
lean_dec_ref(v_forbiddenTks_461_);
lean_dec_ref(v___f_454_);
return v___x_469_;
}
else
{
size_t v___x_470_; size_t v___x_471_; uint8_t v___x_472_; 
v___x_470_ = lean_ptr_addr(v_forbiddenTks_461_);
v___x_471_ = lean_ptr_addr(v_forbiddenTks_466_);
v___x_472_ = lean_usize_dec_eq(v___x_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v___x_473_ = lean_array_get_size(v_forbiddenTks_461_);
v___x_474_ = lean_array_get_size(v_forbiddenTks_466_);
v___x_475_ = lean_nat_dec_eq(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_dec_ref(v_forbiddenTks_466_);
lean_dec_ref(v_forbiddenTks_461_);
lean_dec_ref(v___f_454_);
return v___x_472_;
}
else
{
uint8_t v___x_476_; 
v___x_476_ = l_Array_isEqvAux___redArg(v_forbiddenTks_461_, v_forbiddenTks_466_, v___f_454_, v___x_473_);
lean_dec_ref(v_forbiddenTks_466_);
lean_dec_ref(v_forbiddenTks_461_);
return v___x_476_;
}
}
else
{
lean_dec_ref(v_forbiddenTks_466_);
lean_dec_ref(v_forbiddenTks_461_);
lean_dec_ref(v___f_454_);
return v___x_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed(lean_object* v___f_479_, lean_object* v_a_480_, lean_object* v_b_481_){
_start:
{
uint8_t v_res_482_; lean_object* v_r_483_; 
v_res_482_ = l_Lean_Parser_instBEqCacheableParserContext___lam__0(v___f_479_, v_a_480_, v_b_481_);
v_r_483_ = lean_box(v_res_482_);
return v_r_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0(lean_object* v_x_488_){
_start:
{
lean_object* v_toInputContext_489_; 
v_toInputContext_489_ = lean_ctor_get(v_x_488_, 0);
lean_inc_ref(v_toInputContext_489_);
return v_toInputContext_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(lean_object* v_x_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_490_);
lean_dec_ref(v_x_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos___redArg(lean_object* v_c_494_, lean_object* v_endPos_495_){
_start:
{
lean_object* v_toInputContext_496_; lean_object* v_toParserModuleContext_497_; lean_object* v_toCacheableParserContext_498_; lean_object* v_tokens_499_; lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_517_; 
v_toInputContext_496_ = lean_ctor_get(v_c_494_, 0);
v_toParserModuleContext_497_ = lean_ctor_get(v_c_494_, 1);
v_toCacheableParserContext_498_ = lean_ctor_get(v_c_494_, 2);
v_tokens_499_ = lean_ctor_get(v_c_494_, 3);
v_isSharedCheck_517_ = !lean_is_exclusive(v_c_494_);
if (v_isSharedCheck_517_ == 0)
{
v___x_501_ = v_c_494_;
v_isShared_502_ = v_isSharedCheck_517_;
goto v_resetjp_500_;
}
else
{
lean_inc(v_tokens_499_);
lean_inc(v_toCacheableParserContext_498_);
lean_inc(v_toParserModuleContext_497_);
lean_inc(v_toInputContext_496_);
lean_dec(v_c_494_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_517_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_inputString_503_; lean_object* v_fileName_504_; lean_object* v_fileMap_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
v_inputString_503_ = lean_ctor_get(v_toInputContext_496_, 0);
v_fileName_504_ = lean_ctor_get(v_toInputContext_496_, 1);
v_fileMap_505_ = lean_ctor_get(v_toInputContext_496_, 2);
v_isSharedCheck_515_ = !lean_is_exclusive(v_toInputContext_496_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; 
v_unused_516_ = lean_ctor_get(v_toInputContext_496_, 3);
lean_dec(v_unused_516_);
v___x_507_ = v_toInputContext_496_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_fileMap_505_);
lean_inc(v_fileName_504_);
lean_inc(v_inputString_503_);
lean_dec(v_toInputContext_496_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 3, v_endPos_495_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_inputString_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_fileName_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_fileMap_505_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_endPos_495_);
v___x_510_ = v_reuseFailAlloc_514_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_510_);
v___x_512_ = v___x_501_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___x_510_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_toParserModuleContext_497_);
lean_ctor_set(v_reuseFailAlloc_513_, 2, v_toCacheableParserContext_498_);
lean_ctor_set(v_reuseFailAlloc_513_, 3, v_tokens_499_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos(lean_object* v_c_518_, lean_object* v_endPos_519_, lean_object* v_endPos__valid_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_518_, v_endPos_519_);
return v___x_521_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(lean_object* v_x_528_, lean_object* v_x_529_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
if (lean_obj_tag(v_x_529_) == 0)
{
uint8_t v___x_530_; 
v___x_530_ = 1;
return v___x_530_;
}
else
{
uint8_t v___x_531_; 
v___x_531_ = 0;
return v___x_531_;
}
}
else
{
if (lean_obj_tag(v_x_529_) == 0)
{
uint8_t v___x_532_; 
v___x_532_ = 0;
return v___x_532_;
}
else
{
lean_object* v_head_533_; lean_object* v_tail_534_; lean_object* v_head_535_; lean_object* v_tail_536_; uint8_t v___x_537_; 
v_head_533_ = lean_ctor_get(v_x_528_, 0);
v_tail_534_ = lean_ctor_get(v_x_528_, 1);
v_head_535_ = lean_ctor_get(v_x_529_, 0);
v_tail_536_ = lean_ctor_get(v_x_529_, 1);
v___x_537_ = lean_string_dec_eq(v_head_533_, v_head_535_);
if (v___x_537_ == 0)
{
return v___x_537_;
}
else
{
v_x_528_ = v_tail_534_;
v_x_529_ = v_tail_536_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(lean_object* v_x_539_, lean_object* v_x_540_){
_start:
{
uint8_t v_res_541_; lean_object* v_r_542_; 
v_res_541_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_539_, v_x_540_);
lean_dec(v_x_540_);
lean_dec(v_x_539_);
v_r_542_ = lean_box(v_res_541_);
return v_r_542_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqError_beq(lean_object* v_x_543_, lean_object* v_x_544_){
_start:
{
lean_object* v_unexpectedTk_545_; lean_object* v_unexpected_546_; lean_object* v_expected_547_; lean_object* v_unexpectedTk_548_; lean_object* v_unexpected_549_; lean_object* v_expected_550_; uint8_t v___x_551_; 
v_unexpectedTk_545_ = lean_ctor_get(v_x_543_, 0);
v_unexpected_546_ = lean_ctor_get(v_x_543_, 1);
v_expected_547_ = lean_ctor_get(v_x_543_, 2);
v_unexpectedTk_548_ = lean_ctor_get(v_x_544_, 0);
v_unexpected_549_ = lean_ctor_get(v_x_544_, 1);
v_expected_550_ = lean_ctor_get(v_x_544_, 2);
v___x_551_ = l_Lean_Syntax_structEq(v_unexpectedTk_545_, v_unexpectedTk_548_);
if (v___x_551_ == 0)
{
return v___x_551_;
}
else
{
uint8_t v___x_552_; 
v___x_552_ = lean_string_dec_eq(v_unexpected_546_, v_unexpected_549_);
if (v___x_552_ == 0)
{
return v___x_552_;
}
else
{
uint8_t v___x_553_; 
v___x_553_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_547_, v_expected_550_);
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object* v_x_554_, lean_object* v_x_555_){
_start:
{
uint8_t v_res_556_; lean_object* v_r_557_; 
v_res_556_ = l_Lean_Parser_instBEqError_beq(v_x_554_, v_x_555_);
lean_dec_ref(v_x_555_);
lean_dec_ref(v_x_554_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* v_x_562_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
lean_object* v___x_563_; 
v___x_563_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
return v___x_563_;
}
else
{
lean_object* v_tail_564_; 
v_tail_564_ = lean_ctor_get(v_x_562_, 1);
if (lean_obj_tag(v_tail_564_) == 0)
{
lean_object* v_head_565_; 
v_head_565_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_head_565_);
lean_dec_ref_known(v_x_562_, 2);
return v_head_565_;
}
else
{
lean_object* v_tail_566_; 
lean_inc_ref(v_tail_564_);
v_tail_566_ = lean_ctor_get(v_tail_564_, 1);
if (lean_obj_tag(v_tail_566_) == 0)
{
lean_object* v_head_567_; lean_object* v_head_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_head_567_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_head_567_);
lean_dec_ref_known(v_x_562_, 2);
v_head_568_ = lean_ctor_get(v_tail_564_, 0);
lean_inc(v_head_568_);
lean_dec_ref_known(v_tail_564_, 2);
v___x_569_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0));
v___x_570_ = lean_string_append(v_head_567_, v___x_569_);
v___x_571_ = lean_string_append(v___x_570_, v_head_568_);
lean_dec(v_head_568_);
return v___x_571_;
}
else
{
lean_object* v_head_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_head_572_ = lean_ctor_get(v_x_562_, 0);
lean_inc(v_head_572_);
lean_dec_ref_known(v_x_562_, 2);
v___x_573_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_574_ = lean_string_append(v_head_572_, v___x_573_);
v___x_575_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_tail_564_);
v___x_576_ = lean_string_append(v___x_574_, v___x_575_);
lean_dec_ref(v___x_575_);
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object* v_as_577_){
_start:
{
lean_object* v___f_578_; lean_object* v___x_579_; 
v___f_578_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext___closed__0));
v___x_579_ = l_List_eraseRepsBy___redArg(v___f_578_, v_as_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object* v_hi_580_, lean_object* v_pivot_581_, lean_object* v_as_582_, lean_object* v_i_583_, lean_object* v_k_584_){
_start:
{
uint8_t v___x_585_; 
v___x_585_ = lean_nat_dec_lt(v_k_584_, v_hi_580_);
if (v___x_585_ == 0)
{
lean_object* v___x_586_; lean_object* v___x_587_; 
lean_dec(v_k_584_);
v___x_586_ = lean_array_fswap(v_as_582_, v_i_583_, v_hi_580_);
v___x_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_587_, 0, v_i_583_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
return v___x_587_;
}
else
{
lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_588_ = lean_array_fget_borrowed(v_as_582_, v_k_584_);
v___x_589_ = lean_string_dec_lt(v___x_588_, v_pivot_581_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_add(v_k_584_, v___x_590_);
lean_dec(v_k_584_);
v_k_584_ = v___x_591_;
goto _start;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_593_ = lean_array_fswap(v_as_582_, v_i_583_, v_k_584_);
v___x_594_ = lean_unsigned_to_nat(1u);
v___x_595_ = lean_nat_add(v_i_583_, v___x_594_);
lean_dec(v_i_583_);
v___x_596_ = lean_nat_add(v_k_584_, v___x_594_);
lean_dec(v_k_584_);
v_as_582_ = v___x_593_;
v_i_583_ = v___x_595_;
v_k_584_ = v___x_596_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object* v_hi_598_, lean_object* v_pivot_599_, lean_object* v_as_600_, lean_object* v_i_601_, lean_object* v_k_602_){
_start:
{
lean_object* v_res_603_; 
v_res_603_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_598_, v_pivot_599_, v_as_600_, v_i_601_, v_k_602_);
lean_dec_ref(v_pivot_599_);
lean_dec(v_hi_598_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_n_604_, lean_object* v_as_605_, lean_object* v_lo_606_, lean_object* v_hi_607_){
_start:
{
lean_object* v___y_609_; uint8_t v___x_619_; 
v___x_619_ = lean_nat_dec_lt(v_lo_606_, v_hi_607_);
if (v___x_619_ == 0)
{
lean_dec(v_lo_606_);
return v_as_605_;
}
else
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v_mid_622_; lean_object* v___y_624_; lean_object* v___y_630_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_620_ = lean_nat_add(v_lo_606_, v_hi_607_);
v___x_621_ = lean_unsigned_to_nat(1u);
v_mid_622_ = lean_nat_shiftr(v___x_620_, v___x_621_);
lean_dec(v___x_620_);
v___x_635_ = lean_array_fget_borrowed(v_as_605_, v_mid_622_);
v___x_636_ = lean_array_fget_borrowed(v_as_605_, v_lo_606_);
v___x_637_ = lean_string_dec_lt(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
v___y_630_ = v_as_605_;
goto v___jp_629_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_array_fswap(v_as_605_, v_lo_606_, v_mid_622_);
v___y_630_ = v___x_638_;
goto v___jp_629_;
}
v___jp_623_:
{
lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; 
v___x_625_ = lean_array_fget_borrowed(v___y_624_, v_mid_622_);
v___x_626_ = lean_array_fget_borrowed(v___y_624_, v_hi_607_);
v___x_627_ = lean_string_dec_lt(v___x_625_, v___x_626_);
if (v___x_627_ == 0)
{
lean_dec(v_mid_622_);
v___y_609_ = v___y_624_;
goto v___jp_608_;
}
else
{
lean_object* v___x_628_; 
v___x_628_ = lean_array_fswap(v___y_624_, v_mid_622_, v_hi_607_);
lean_dec(v_mid_622_);
v___y_609_ = v___x_628_;
goto v___jp_608_;
}
}
v___jp_629_:
{
lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v___x_631_ = lean_array_fget_borrowed(v___y_630_, v_hi_607_);
v___x_632_ = lean_array_fget_borrowed(v___y_630_, v_lo_606_);
v___x_633_ = lean_string_dec_lt(v___x_631_, v___x_632_);
if (v___x_633_ == 0)
{
v___y_624_ = v___y_630_;
goto v___jp_623_;
}
else
{
lean_object* v___x_634_; 
v___x_634_ = lean_array_fswap(v___y_630_, v_lo_606_, v_hi_607_);
v___y_624_ = v___x_634_;
goto v___jp_623_;
}
}
}
v___jp_608_:
{
lean_object* v_pivot_610_; lean_object* v___x_611_; lean_object* v_fst_612_; lean_object* v_snd_613_; uint8_t v___x_614_; 
v_pivot_610_ = lean_array_fget(v___y_609_, v_hi_607_);
lean_inc_n(v_lo_606_, 2);
v___x_611_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_607_, v_pivot_610_, v___y_609_, v_lo_606_, v_lo_606_);
lean_dec(v_pivot_610_);
v_fst_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_fst_612_);
v_snd_613_ = lean_ctor_get(v___x_611_, 1);
lean_inc(v_snd_613_);
lean_dec_ref(v___x_611_);
v___x_614_ = lean_nat_dec_le(v_hi_607_, v_fst_612_);
if (v___x_614_ == 0)
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_604_, v_snd_613_, v_lo_606_, v_fst_612_);
v___x_616_ = lean_unsigned_to_nat(1u);
v___x_617_ = lean_nat_add(v_fst_612_, v___x_616_);
lean_dec(v_fst_612_);
v_as_605_ = v___x_615_;
v_lo_606_ = v___x_617_;
goto _start;
}
else
{
lean_dec(v_fst_612_);
lean_dec(v_lo_606_);
return v_snd_613_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_n_639_, lean_object* v_as_640_, lean_object* v_lo_641_, lean_object* v_hi_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_639_, v_as_640_, v_lo_641_, v_hi_642_);
lean_dec(v_hi_642_);
lean_dec(v_n_639_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_646_){
_start:
{
lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v_unexpected_679_; lean_object* v_expected_680_; lean_object* v___y_682_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_unexpected_679_ = lean_ctor_get(v_e_646_, 1);
lean_inc_ref(v_unexpected_679_);
v_expected_680_ = lean_ctor_get(v_e_646_, 2);
lean_inc(v_expected_680_);
lean_dec_ref(v_e_646_);
v___x_692_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_693_ = lean_string_dec_eq(v_unexpected_679_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_box(0);
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v_unexpected_679_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___y_682_ = v___x_695_;
goto v___jp_681_;
}
else
{
lean_object* v___x_696_; 
lean_dec_ref(v_unexpected_679_);
v___x_696_ = lean_box(0);
v___y_682_ = v___x_696_;
goto v___jp_681_;
}
v___jp_647_:
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_650_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_651_ = l_List_appendTR___redArg(v___y_648_, v___y_649_);
v___x_652_ = l_String_intercalate(v___x_650_, v___x_651_);
return v___x_652_;
}
v___jp_653_:
{
lean_object* v___x_657_; lean_object* v_expected_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_657_ = lean_array_to_list(v___y_656_);
v_expected_658_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_657_);
v___x_659_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_660_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_658_);
v___x_661_ = lean_string_append(v___x_659_, v___x_660_);
lean_dec_ref(v___x_660_);
v___x_662_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_662_, 0, v___x_661_);
lean_ctor_set(v___x_662_, 1, v___y_654_);
v___y_648_ = v___y_655_;
v___y_649_ = v___x_662_;
goto v___jp_647_;
}
v___jp_663_:
{
lean_object* v___x_670_; 
v___x_670_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_667_, v___y_665_, v___y_666_, v___y_669_);
lean_dec(v___y_669_);
lean_dec(v___y_667_);
v___y_654_ = v___y_664_;
v___y_655_ = v___y_668_;
v___y_656_ = v___x_670_;
goto v___jp_653_;
}
v___jp_671_:
{
uint8_t v___x_678_; 
v___x_678_ = lean_nat_dec_le(v___y_677_, v___y_672_);
if (v___x_678_ == 0)
{
lean_dec(v___y_672_);
lean_inc(v___y_677_);
v___y_664_ = v___y_674_;
v___y_665_ = v___y_673_;
v___y_666_ = v___y_677_;
v___y_667_ = v___y_675_;
v___y_668_ = v___y_676_;
v___y_669_ = v___y_677_;
goto v___jp_663_;
}
else
{
v___y_664_ = v___y_674_;
v___y_665_ = v___y_673_;
v___y_666_ = v___y_677_;
v___y_667_ = v___y_675_;
v___y_668_ = v___y_676_;
v___y_669_ = v___y_672_;
goto v___jp_663_;
}
}
v___jp_681_:
{
lean_object* v___x_683_; uint8_t v___x_684_; 
v___x_683_ = lean_box(0);
v___x_684_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_680_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v___x_685_ = lean_array_mk(v_expected_680_);
v___x_686_ = lean_array_get_size(v___x_685_);
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = lean_nat_dec_eq(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_689_ = lean_unsigned_to_nat(1u);
v___x_690_ = lean_nat_sub(v___x_686_, v___x_689_);
v___x_691_ = lean_nat_dec_le(v___x_687_, v___x_690_);
if (v___x_691_ == 0)
{
lean_inc(v___x_690_);
v___y_672_ = v___x_690_;
v___y_673_ = v___x_685_;
v___y_674_ = v___x_683_;
v___y_675_ = v___x_686_;
v___y_676_ = v___y_682_;
v___y_677_ = v___x_690_;
goto v___jp_671_;
}
else
{
v___y_672_ = v___x_690_;
v___y_673_ = v___x_685_;
v___y_674_ = v___x_683_;
v___y_675_ = v___x_686_;
v___y_676_ = v___y_682_;
v___y_677_ = v___x_687_;
goto v___jp_671_;
}
}
else
{
v___y_654_ = v___x_683_;
v___y_655_ = v___y_682_;
v___y_656_ = v___x_685_;
goto v___jp_653_;
}
}
else
{
lean_dec(v_expected_680_);
v___y_648_ = v___y_682_;
v___y_649_ = v___x_683_;
goto v___jp_647_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_697_, lean_object* v_as_698_, lean_object* v_lo_699_, lean_object* v_hi_700_, lean_object* v_w_701_, lean_object* v_hlo_702_, lean_object* v_hhi_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_697_, v_as_698_, v_lo_699_, v_hi_700_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_705_, lean_object* v_as_706_, lean_object* v_lo_707_, lean_object* v_hi_708_, lean_object* v_w_709_, lean_object* v_hlo_710_, lean_object* v_hhi_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_705_, v_as_706_, v_lo_707_, v_hi_708_, v_w_709_, v_hlo_710_, v_hhi_711_);
lean_dec(v_hi_708_);
lean_dec(v_n_705_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object* v_n_713_, lean_object* v_lo_714_, lean_object* v_hi_715_, lean_object* v_hhi_716_, lean_object* v_pivot_717_, lean_object* v_as_718_, lean_object* v_i_719_, lean_object* v_k_720_, lean_object* v_ilo_721_, lean_object* v_ik_722_, lean_object* v_w_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_715_, v_pivot_717_, v_as_718_, v_i_719_, v_k_720_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object* v_n_725_, lean_object* v_lo_726_, lean_object* v_hi_727_, lean_object* v_hhi_728_, lean_object* v_pivot_729_, lean_object* v_as_730_, lean_object* v_i_731_, lean_object* v_k_732_, lean_object* v_ilo_733_, lean_object* v_ik_734_, lean_object* v_w_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_725_, v_lo_726_, v_hi_727_, v_hhi_728_, v_pivot_729_, v_as_730_, v_i_731_, v_k_732_, v_ilo_733_, v_ik_734_, v_w_735_);
lean_dec_ref(v_pivot_729_);
lean_dec(v_hi_727_);
lean_dec(v_lo_726_);
lean_dec(v_n_725_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_739_, lean_object* v_e_u2082_740_){
_start:
{
lean_object* v_unexpectedTk_741_; lean_object* v_unexpected_742_; lean_object* v_expected_743_; lean_object* v___y_745_; lean_object* v___x_757_; uint8_t v___x_758_; 
v_unexpectedTk_741_ = lean_ctor_get(v_e_u2082_740_, 0);
lean_inc(v_unexpectedTk_741_);
v_unexpected_742_ = lean_ctor_get(v_e_u2082_740_, 1);
lean_inc_ref(v_unexpected_742_);
v_expected_743_ = lean_ctor_get(v_e_u2082_740_, 2);
lean_inc(v_expected_743_);
lean_dec_ref(v_e_u2082_740_);
v___x_757_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_758_ = lean_string_dec_eq(v_unexpected_742_, v___x_757_);
if (v___x_758_ == 0)
{
v___y_745_ = v_unexpected_742_;
goto v___jp_744_;
}
else
{
lean_object* v_unexpected_759_; 
lean_dec_ref(v_unexpected_742_);
v_unexpected_759_ = lean_ctor_get(v_e_u2081_739_, 1);
lean_inc_ref(v_unexpected_759_);
v___y_745_ = v_unexpected_759_;
goto v___jp_744_;
}
v___jp_744_:
{
lean_object* v_expected_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_754_; 
v_expected_746_ = lean_ctor_get(v_e_u2081_739_, 2);
v_isSharedCheck_754_ = !lean_is_exclusive(v_e_u2081_739_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; lean_object* v_unused_756_; 
v_unused_755_ = lean_ctor_get(v_e_u2081_739_, 1);
lean_dec(v_unused_755_);
v_unused_756_ = lean_ctor_get(v_e_u2081_739_, 0);
lean_dec(v_unused_756_);
v___x_748_ = v_e_u2081_739_;
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_expected_746_);
lean_dec(v_e_u2081_739_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_754_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_750_; lean_object* v___x_752_; 
v___x_750_ = l_List_appendTR___redArg(v_expected_746_, v_expected_743_);
if (v_isShared_749_ == 0)
{
lean_ctor_set(v___x_748_, 2, v___x_750_);
lean_ctor_set(v___x_748_, 1, v___y_745_);
lean_ctor_set(v___x_748_, 0, v_unexpectedTk_741_);
v___x_752_ = v___x_748_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_unexpectedTk_741_);
lean_ctor_set(v_reuseFailAlloc_753_, 1, v___y_745_);
lean_ctor_set(v_reuseFailAlloc_753_, 2, v___x_750_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(lean_object* v_x_760_, lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_760_) == 0)
{
if (lean_obj_tag(v_x_761_) == 0)
{
uint8_t v___x_762_; 
v___x_762_ = 1;
return v___x_762_;
}
else
{
uint8_t v___x_763_; 
v___x_763_ = 0;
return v___x_763_;
}
}
else
{
if (lean_obj_tag(v_x_761_) == 0)
{
uint8_t v___x_764_; 
v___x_764_ = 0;
return v___x_764_;
}
else
{
lean_object* v_val_765_; lean_object* v_val_766_; uint8_t v___x_767_; 
v_val_765_ = lean_ctor_get(v_x_760_, 0);
v_val_766_ = lean_ctor_get(v_x_761_, 0);
v___x_767_ = lean_nat_dec_eq(v_val_765_, v_val_766_);
return v___x_767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0___boxed(lean_object* v_x_768_, lean_object* v_x_769_){
_start:
{
uint8_t v_res_770_; lean_object* v_r_771_; 
v_res_770_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_x_768_, v_x_769_);
lean_dec(v_x_769_);
lean_dec(v_x_768_);
v_r_771_ = lean_box(v_res_770_);
return v_r_771_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(lean_object* v_xs_772_, lean_object* v_ys_773_, lean_object* v_x_774_){
_start:
{
lean_object* v_zero_775_; uint8_t v_isZero_776_; 
v_zero_775_ = lean_unsigned_to_nat(0u);
v_isZero_776_ = lean_nat_dec_eq(v_x_774_, v_zero_775_);
if (v_isZero_776_ == 1)
{
lean_dec(v_x_774_);
return v_isZero_776_;
}
else
{
lean_object* v_one_777_; lean_object* v_n_778_; lean_object* v___x_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_one_777_ = lean_unsigned_to_nat(1u);
v_n_778_ = lean_nat_sub(v_x_774_, v_one_777_);
lean_dec(v_x_774_);
v___x_779_ = lean_array_fget_borrowed(v_xs_772_, v_n_778_);
v___x_780_ = lean_array_fget_borrowed(v_ys_773_, v_n_778_);
v___x_781_ = lean_string_dec_eq(v___x_779_, v___x_780_);
if (v___x_781_ == 0)
{
lean_dec(v_n_778_);
return v___x_781_;
}
else
{
v_x_774_ = v_n_778_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg___boxed(lean_object* v_xs_783_, lean_object* v_ys_784_, lean_object* v_x_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_783_, v_ys_784_, v_x_785_);
lean_dec_ref(v_ys_784_);
lean_dec_ref(v_xs_783_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_788_, lean_object* v_x_789_){
_start:
{
lean_object* v_toCacheableParserContext_790_; lean_object* v_parserName_791_; lean_object* v_pos_792_; lean_object* v_toCacheableParserContext_793_; lean_object* v_parserName_794_; lean_object* v_pos_795_; uint8_t v___y_797_; lean_object* v_prec_800_; lean_object* v_quotDepth_801_; uint8_t v_suppressInsideQuot_802_; lean_object* v_savedPos_x3f_803_; lean_object* v_forbiddenTks_804_; lean_object* v_prec_805_; lean_object* v_quotDepth_806_; uint8_t v_suppressInsideQuot_807_; lean_object* v_savedPos_x3f_808_; lean_object* v_forbiddenTks_809_; uint8_t v___y_820_; uint8_t v___x_821_; 
v_toCacheableParserContext_790_ = lean_ctor_get(v_x_788_, 0);
v_parserName_791_ = lean_ctor_get(v_x_788_, 1);
v_pos_792_ = lean_ctor_get(v_x_788_, 2);
v_toCacheableParserContext_793_ = lean_ctor_get(v_x_789_, 0);
v_parserName_794_ = lean_ctor_get(v_x_789_, 1);
v_pos_795_ = lean_ctor_get(v_x_789_, 2);
v_prec_800_ = lean_ctor_get(v_toCacheableParserContext_790_, 0);
v_quotDepth_801_ = lean_ctor_get(v_toCacheableParserContext_790_, 1);
v_suppressInsideQuot_802_ = lean_ctor_get_uint8(v_toCacheableParserContext_790_, sizeof(void*)*4);
v_savedPos_x3f_803_ = lean_ctor_get(v_toCacheableParserContext_790_, 2);
v_forbiddenTks_804_ = lean_ctor_get(v_toCacheableParserContext_790_, 3);
v_prec_805_ = lean_ctor_get(v_toCacheableParserContext_793_, 0);
v_quotDepth_806_ = lean_ctor_get(v_toCacheableParserContext_793_, 1);
v_suppressInsideQuot_807_ = lean_ctor_get_uint8(v_toCacheableParserContext_793_, sizeof(void*)*4);
v_savedPos_x3f_808_ = lean_ctor_get(v_toCacheableParserContext_793_, 2);
v_forbiddenTks_809_ = lean_ctor_get(v_toCacheableParserContext_793_, 3);
v___x_821_ = lean_nat_dec_eq(v_prec_800_, v_prec_805_);
if (v___x_821_ == 0)
{
v___y_820_ = v___x_821_;
goto v___jp_819_;
}
else
{
uint8_t v___x_822_; 
v___x_822_ = lean_nat_dec_eq(v_quotDepth_801_, v_quotDepth_806_);
v___y_820_ = v___x_822_;
goto v___jp_819_;
}
v___jp_796_:
{
if (v___y_797_ == 0)
{
return v___y_797_;
}
else
{
uint8_t v___x_798_; 
v___x_798_ = lean_name_eq(v_parserName_791_, v_parserName_794_);
if (v___x_798_ == 0)
{
return v___x_798_;
}
else
{
uint8_t v___x_799_; 
v___x_799_ = lean_nat_dec_eq(v_pos_792_, v_pos_795_);
return v___x_799_;
}
}
}
v___jp_810_:
{
uint8_t v___x_811_; 
v___x_811_ = l_Option_instBEq_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_savedPos_x3f_803_, v_savedPos_x3f_808_);
if (v___x_811_ == 0)
{
v___y_797_ = v___x_811_;
goto v___jp_796_;
}
else
{
size_t v___x_812_; size_t v___x_813_; uint8_t v___x_814_; 
v___x_812_ = lean_ptr_addr(v_forbiddenTks_804_);
v___x_813_ = lean_ptr_addr(v_forbiddenTks_809_);
v___x_814_ = lean_usize_dec_eq(v___x_812_, v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_815_ = lean_array_get_size(v_forbiddenTks_804_);
v___x_816_ = lean_array_get_size(v_forbiddenTks_809_);
v___x_817_ = lean_nat_dec_eq(v___x_815_, v___x_816_);
if (v___x_817_ == 0)
{
v___y_797_ = v___x_814_;
goto v___jp_796_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_forbiddenTks_804_, v_forbiddenTks_809_, v___x_815_);
v___y_797_ = v___x_818_;
goto v___jp_796_;
}
}
else
{
v___y_797_ = v___x_814_;
goto v___jp_796_;
}
}
}
v___jp_819_:
{
if (v___y_820_ == 0)
{
return v___y_820_;
}
else
{
if (v_suppressInsideQuot_802_ == 0)
{
if (v_suppressInsideQuot_807_ == 0)
{
goto v___jp_810_;
}
else
{
return v_suppressInsideQuot_802_;
}
}
else
{
if (v_suppressInsideQuot_807_ == 0)
{
return v_suppressInsideQuot_807_;
}
else
{
goto v___jp_810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object* v_x_823_, lean_object* v_x_824_){
_start:
{
uint8_t v_res_825_; lean_object* v_r_826_; 
v_res_825_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_823_, v_x_824_);
lean_dec_ref(v_x_824_);
lean_dec_ref(v_x_823_);
v_r_826_ = lean_box(v_res_825_);
return v_r_826_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(lean_object* v_xs_827_, lean_object* v_ys_828_, lean_object* v_hsz_829_, lean_object* v_x_830_, lean_object* v_x_831_){
_start:
{
uint8_t v___x_832_; 
v___x_832_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_827_, v_ys_828_, v_x_830_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___boxed(lean_object* v_xs_833_, lean_object* v_ys_834_, lean_object* v_hsz_835_, lean_object* v_x_836_, lean_object* v_x_837_){
_start:
{
uint8_t v_res_838_; lean_object* v_r_839_; 
v_res_838_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(v_xs_833_, v_ys_834_, v_hsz_835_, v_x_836_, v_x_837_);
lean_dec_ref(v_ys_834_);
lean_dec_ref(v_xs_833_);
v_r_839_ = lean_box(v_res_838_);
return v_r_839_;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* v_k_842_){
_start:
{
lean_object* v_parserName_843_; lean_object* v_pos_844_; uint64_t v___x_845_; 
v_parserName_843_ = lean_ctor_get(v_k_842_, 1);
v_pos_844_ = lean_ctor_get(v_k_842_, 2);
v___x_845_ = l_String_instHashableRaw_hash(v_pos_844_);
if (lean_obj_tag(v_parserName_843_) == 0)
{
uint64_t v___x_846_; uint64_t v___x_847_; 
v___x_846_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_847_ = lean_uint64_mix_hash(v___x_845_, v___x_846_);
return v___x_847_;
}
else
{
uint64_t v_hash_848_; uint64_t v___x_849_; 
v_hash_848_ = lean_ctor_get_uint64(v_parserName_843_, sizeof(void*)*2);
v___x_849_ = lean_uint64_mix_hash(v___x_845_, v_hash_848_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* v_k_850_){
_start:
{
uint64_t v_res_851_; lean_object* v_r_852_; 
v_res_851_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_850_);
lean_dec_ref(v_k_850_);
v_r_852_ = lean_box_uint64(v_res_851_);
return v_r_852_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0(void){
_start:
{
uint32_t v___x_855_; lean_object* v___x_856_; 
v___x_855_ = 32;
v___x_856_ = l_Char_utf8Size(v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_857_ = lean_box(0);
v___x_858_ = lean_unsigned_to_nat(16u);
v___x_859_ = lean_mk_array(v___x_858_, v___x_857_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__2(void){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_860_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_861_);
lean_ctor_set(v___x_862_, 1, v___x_860_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_863_){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_864_ = lean_string_utf8_byte_size(v_input_863_);
v___x_865_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_866_ = lean_nat_add(v___x_864_, v___x_865_);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_box(0);
v___x_869_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_869_, 0, v___x_866_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
lean_ctor_set(v___x_869_, 2, v___x_868_);
v___x_870_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
v___x_871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_871_, 0, v___x_869_);
lean_ctor_set(v___x_871_, 1, v___x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Parser_initCacheForInput(v_input_872_);
lean_dec_ref(v_input_872_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_874_){
_start:
{
lean_object* v_raw_875_; lean_object* v_drop_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_raw_875_ = lean_ctor_get(v_stack_874_, 0);
lean_inc_ref(v_raw_875_);
v_drop_876_ = lean_ctor_get(v_stack_874_, 1);
lean_inc(v_drop_876_);
lean_dec_ref(v_stack_874_);
v___x_877_ = lean_array_get_size(v_raw_875_);
v___x_878_ = l_Array_toSubarray___redArg(v_raw_875_, v_drop_876_, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_885_){
_start:
{
lean_object* v_raw_886_; lean_object* v_drop_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_raw_886_ = lean_ctor_get(v_stack_885_, 0);
v_drop_887_ = lean_ctor_get(v_stack_885_, 1);
v___x_888_ = lean_array_get_size(v_raw_886_);
v___x_889_ = lean_nat_sub(v___x_888_, v_drop_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Parser_SyntaxStack_size(v_stack_890_);
lean_dec_ref(v_stack_890_);
return v_res_891_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_892_){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; uint8_t v___x_895_; 
v___x_893_ = l_Lean_Parser_SyntaxStack_size(v_stack_892_);
v___x_894_ = lean_unsigned_to_nat(0u);
v___x_895_ = lean_nat_dec_eq(v___x_893_, v___x_894_);
lean_dec(v___x_893_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_896_){
_start:
{
uint8_t v_res_897_; lean_object* v_r_898_; 
v_res_897_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_896_);
lean_dec_ref(v_stack_896_);
v_r_898_ = lean_box(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_899_, lean_object* v_n_900_){
_start:
{
lean_object* v_raw_901_; lean_object* v_drop_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_911_; 
v_raw_901_ = lean_ctor_get(v_stack_899_, 0);
v_drop_902_ = lean_ctor_get(v_stack_899_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_stack_899_);
if (v_isSharedCheck_911_ == 0)
{
v___x_904_ = v_stack_899_;
v_isShared_905_ = v_isSharedCheck_911_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_drop_902_);
lean_inc(v_raw_901_);
lean_dec(v_stack_899_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_911_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v___x_906_ = lean_nat_add(v_drop_902_, v_n_900_);
v___x_907_ = l_Array_shrink___redArg(v_raw_901_, v___x_906_);
lean_dec(v___x_906_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_907_);
v___x_909_ = v___x_904_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v_drop_902_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_912_, lean_object* v_n_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_912_, v_n_913_);
lean_dec(v_n_913_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_915_, lean_object* v_a_916_){
_start:
{
lean_object* v_raw_917_; lean_object* v_drop_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_926_; 
v_raw_917_ = lean_ctor_get(v_stack_915_, 0);
v_drop_918_ = lean_ctor_get(v_stack_915_, 1);
v_isSharedCheck_926_ = !lean_is_exclusive(v_stack_915_);
if (v_isSharedCheck_926_ == 0)
{
v___x_920_ = v_stack_915_;
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_drop_918_);
lean_inc(v_raw_917_);
lean_dec(v_stack_915_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_926_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_922_; lean_object* v___x_924_; 
v___x_922_ = lean_array_push(v_raw_917_, v_a_916_);
if (v_isShared_921_ == 0)
{
lean_ctor_set(v___x_920_, 0, v___x_922_);
v___x_924_ = v___x_920_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v___x_922_);
lean_ctor_set(v_reuseFailAlloc_925_, 1, v_drop_918_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = l_Lean_Parser_SyntaxStack_size(v_stack_927_);
v___x_930_ = lean_nat_dec_lt(v___x_928_, v___x_929_);
lean_dec(v___x_929_);
if (v___x_930_ == 0)
{
return v_stack_927_;
}
else
{
lean_object* v_raw_931_; lean_object* v_drop_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
v_raw_931_ = lean_ctor_get(v_stack_927_, 0);
v_drop_932_ = lean_ctor_get(v_stack_927_, 1);
v_isSharedCheck_940_ = !lean_is_exclusive(v_stack_927_);
if (v_isSharedCheck_940_ == 0)
{
v___x_934_ = v_stack_927_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_drop_932_);
lean_inc(v_raw_931_);
lean_dec(v_stack_927_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = lean_array_pop(v_raw_931_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_drop_932_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_941_){
_start:
{
lean_object* v___x_942_; lean_object* v___x_943_; 
v___x_942_ = lean_box(0);
v___x_943_ = lean_panic_fn_borrowed(v___x_942_, v_msg_941_);
return v___x_943_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_947_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_948_ = lean_unsigned_to_nat(4u);
v___x_949_ = lean_unsigned_to_nat(313u);
v___x_950_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_951_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_952_ = l_mkPanicMessageWithDecl(v___x_951_, v___x_950_, v___x_949_, v___x_948_, v___x_947_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_953_){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = l_Lean_Parser_SyntaxStack_size(v_stack_953_);
v___x_956_ = lean_nat_dec_lt(v___x_954_, v___x_955_);
lean_dec(v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_958_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_957_);
return v___x_958_;
}
else
{
lean_object* v_raw_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_raw_959_ = lean_ctor_get(v_stack_953_, 0);
v___x_960_ = lean_box(0);
v___x_961_ = lean_array_get_size(v_raw_959_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_nat_sub(v___x_961_, v___x_962_);
v___x_964_ = lean_array_get_borrowed(v___x_960_, v_raw_959_, v___x_963_);
lean_dec(v___x_963_);
lean_inc(v___x_964_);
return v___x_964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_Parser_SyntaxStack_back(v_stack_965_);
lean_dec_ref(v_stack_965_);
return v_res_966_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_969_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_970_ = lean_unsigned_to_nat(4u);
v___x_971_ = lean_unsigned_to_nat(319u);
v___x_972_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_973_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_974_ = l_mkPanicMessageWithDecl(v___x_973_, v___x_972_, v___x_971_, v___x_970_, v___x_969_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_975_, lean_object* v_i_976_){
_start:
{
lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_977_ = l_Lean_Parser_SyntaxStack_size(v_stack_975_);
v___x_978_ = lean_nat_dec_lt(v_i_976_, v___x_977_);
lean_dec(v___x_977_);
if (v___x_978_ == 0)
{
lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_979_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_980_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_979_);
return v___x_980_;
}
else
{
lean_object* v_raw_981_; lean_object* v_drop_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_raw_981_ = lean_ctor_get(v_stack_975_, 0);
v_drop_982_ = lean_ctor_get(v_stack_975_, 1);
v___x_983_ = lean_box(0);
v___x_984_ = lean_nat_add(v_drop_982_, v_i_976_);
v___x_985_ = lean_array_get_borrowed(v___x_983_, v_raw_981_, v___x_984_);
lean_dec(v___x_984_);
lean_inc(v___x_985_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_986_, lean_object* v_i_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_986_, v_i_987_);
lean_dec(v_i_987_);
lean_dec_ref(v_stack_986_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_989_, lean_object* v_start_990_, lean_object* v_stop_991_){
_start:
{
lean_object* v_raw_992_; lean_object* v_drop_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_raw_992_ = lean_ctor_get(v_stack_989_, 0);
v_drop_993_ = lean_ctor_get(v_stack_989_, 1);
v___x_994_ = lean_nat_add(v_drop_993_, v_start_990_);
v___x_995_ = lean_nat_add(v_drop_993_, v_stop_991_);
v___x_996_ = l_Array_extract___redArg(v_raw_992_, v___x_994_, v___x_995_);
return v___x_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_997_, lean_object* v_start_998_, lean_object* v_stop_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Lean_Parser_SyntaxStack_extract(v_stack_997_, v_start_998_, v_stop_999_);
lean_dec(v_stop_999_);
lean_dec(v_start_998_);
lean_dec_ref(v_stack_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_1001_, lean_object* v_stxs_1002_){
_start:
{
lean_object* v_raw_1003_; lean_object* v_drop_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1012_; 
v_raw_1003_ = lean_ctor_get(v_stack_1001_, 0);
v_drop_1004_ = lean_ctor_get(v_stack_1001_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_stack_1001_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1006_ = v_stack_1001_;
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_drop_1004_);
lean_inc(v_raw_1003_);
lean_dec(v_stack_1001_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1012_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = l_Array_append___redArg(v_raw_1003_, v_stxs_1002_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1008_);
v___x_1010_ = v___x_1006_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_drop_1004_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_1013_, lean_object* v_stxs_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_1013_, v_stxs_1014_);
lean_dec_ref(v_stxs_1014_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_1016_, lean_object* v_stxs_1017_){
_start:
{
lean_object* v_raw_1018_; lean_object* v_drop_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1027_; 
v_raw_1018_ = lean_ctor_get(v_stack_1016_, 0);
v_drop_1019_ = lean_ctor_get(v_stack_1016_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_stack_1016_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_1021_ = v_stack_1016_;
v_isShared_1022_ = v_isSharedCheck_1027_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_drop_1019_);
lean_inc(v_raw_1018_);
lean_dec(v_stack_1016_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1027_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1023_; lean_object* v___x_1025_; 
v___x_1023_ = l_Array_append___redArg(v_raw_1018_, v_stxs_1017_);
if (v_isShared_1022_ == 0)
{
lean_ctor_set(v___x_1021_, 0, v___x_1023_);
v___x_1025_ = v___x_1021_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1026_; 
v_reuseFailAlloc_1026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1026_, 0, v___x_1023_);
lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_drop_1019_);
v___x_1025_ = v_reuseFailAlloc_1026_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
return v___x_1025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_1028_, lean_object* v_stxs_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_1028_, v_stxs_1029_);
lean_dec_ref(v_stxs_1029_);
return v_res_1030_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_1033_){
_start:
{
lean_object* v_errorMsg_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_errorMsg_1034_ = lean_ctor_get(v_s_1033_, 4);
lean_inc(v_errorMsg_1034_);
lean_dec_ref(v_s_1033_);
v___x_1035_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_1036_ = lean_box(0);
v___x_1037_ = l_Option_instBEq_beq___redArg(v___x_1035_, v_errorMsg_1034_, v___x_1036_);
if (v___x_1037_ == 0)
{
uint8_t v___x_1038_; 
v___x_1038_ = 1;
return v___x_1038_;
}
else
{
uint8_t v___x_1039_; 
v___x_1039_ = 0;
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_1040_){
_start:
{
uint8_t v_res_1041_; lean_object* v_r_1042_; 
v_res_1041_ = l_Lean_Parser_ParserState_hasError(v_s_1040_);
v_r_1042_ = lean_box(v_res_1041_);
return v_r_1042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_1043_){
_start:
{
lean_object* v_stxStack_1044_; lean_object* v___x_1045_; 
v_stxStack_1044_ = lean_ctor_get(v_s_1043_, 0);
v___x_1045_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1044_);
return v___x_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l_Lean_Parser_ParserState_stackSize(v_s_1046_);
lean_dec_ref(v_s_1046_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_1048_, lean_object* v_iniStackSz_1049_, lean_object* v_iniPos_1050_){
_start:
{
lean_object* v_stxStack_1051_; lean_object* v_lhsPrec_1052_; lean_object* v_cache_1053_; lean_object* v_recoveredErrors_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1063_; 
v_stxStack_1051_ = lean_ctor_get(v_s_1048_, 0);
v_lhsPrec_1052_ = lean_ctor_get(v_s_1048_, 1);
v_cache_1053_ = lean_ctor_get(v_s_1048_, 3);
v_recoveredErrors_1054_ = lean_ctor_get(v_s_1048_, 5);
v_isSharedCheck_1063_ = !lean_is_exclusive(v_s_1048_);
if (v_isSharedCheck_1063_ == 0)
{
lean_object* v_unused_1064_; lean_object* v_unused_1065_; 
v_unused_1064_ = lean_ctor_get(v_s_1048_, 4);
lean_dec(v_unused_1064_);
v_unused_1065_ = lean_ctor_get(v_s_1048_, 2);
lean_dec(v_unused_1065_);
v___x_1056_ = v_s_1048_;
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_recoveredErrors_1054_);
lean_inc(v_cache_1053_);
lean_inc(v_lhsPrec_1052_);
lean_inc(v_stxStack_1051_);
lean_dec(v_s_1048_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1063_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1061_; 
v___x_1058_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1051_, v_iniStackSz_1049_);
v___x_1059_ = lean_box(0);
if (v_isShared_1057_ == 0)
{
lean_ctor_set(v___x_1056_, 4, v___x_1059_);
lean_ctor_set(v___x_1056_, 2, v_iniPos_1050_);
lean_ctor_set(v___x_1056_, 0, v___x_1058_);
v___x_1061_ = v___x_1056_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v___x_1058_);
lean_ctor_set(v_reuseFailAlloc_1062_, 1, v_lhsPrec_1052_);
lean_ctor_set(v_reuseFailAlloc_1062_, 2, v_iniPos_1050_);
lean_ctor_set(v_reuseFailAlloc_1062_, 3, v_cache_1053_);
lean_ctor_set(v_reuseFailAlloc_1062_, 4, v___x_1059_);
lean_ctor_set(v_reuseFailAlloc_1062_, 5, v_recoveredErrors_1054_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_1066_, lean_object* v_iniStackSz_1067_, lean_object* v_iniPos_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l_Lean_Parser_ParserState_restore(v_s_1066_, v_iniStackSz_1067_, v_iniPos_1068_);
lean_dec(v_iniStackSz_1067_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_1070_, lean_object* v_pos_1071_){
_start:
{
lean_object* v_stxStack_1072_; lean_object* v_lhsPrec_1073_; lean_object* v_cache_1074_; lean_object* v_errorMsg_1075_; lean_object* v_recoveredErrors_1076_; lean_object* v___x_1078_; uint8_t v_isShared_1079_; uint8_t v_isSharedCheck_1083_; 
v_stxStack_1072_ = lean_ctor_get(v_s_1070_, 0);
v_lhsPrec_1073_ = lean_ctor_get(v_s_1070_, 1);
v_cache_1074_ = lean_ctor_get(v_s_1070_, 3);
v_errorMsg_1075_ = lean_ctor_get(v_s_1070_, 4);
v_recoveredErrors_1076_ = lean_ctor_get(v_s_1070_, 5);
v_isSharedCheck_1083_ = !lean_is_exclusive(v_s_1070_);
if (v_isSharedCheck_1083_ == 0)
{
lean_object* v_unused_1084_; 
v_unused_1084_ = lean_ctor_get(v_s_1070_, 2);
lean_dec(v_unused_1084_);
v___x_1078_ = v_s_1070_;
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
else
{
lean_inc(v_recoveredErrors_1076_);
lean_inc(v_errorMsg_1075_);
lean_inc(v_cache_1074_);
lean_inc(v_lhsPrec_1073_);
lean_inc(v_stxStack_1072_);
lean_dec(v_s_1070_);
v___x_1078_ = lean_box(0);
v_isShared_1079_ = v_isSharedCheck_1083_;
goto v_resetjp_1077_;
}
v_resetjp_1077_:
{
lean_object* v___x_1081_; 
if (v_isShared_1079_ == 0)
{
lean_ctor_set(v___x_1078_, 2, v_pos_1071_);
v___x_1081_ = v___x_1078_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_stxStack_1072_);
lean_ctor_set(v_reuseFailAlloc_1082_, 1, v_lhsPrec_1073_);
lean_ctor_set(v_reuseFailAlloc_1082_, 2, v_pos_1071_);
lean_ctor_set(v_reuseFailAlloc_1082_, 3, v_cache_1074_);
lean_ctor_set(v_reuseFailAlloc_1082_, 4, v_errorMsg_1075_);
lean_ctor_set(v_reuseFailAlloc_1082_, 5, v_recoveredErrors_1076_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_1085_, lean_object* v_cache_1086_){
_start:
{
lean_object* v_stxStack_1087_; lean_object* v_lhsPrec_1088_; lean_object* v_pos_1089_; lean_object* v_errorMsg_1090_; lean_object* v_recoveredErrors_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_stxStack_1087_ = lean_ctor_get(v_s_1085_, 0);
v_lhsPrec_1088_ = lean_ctor_get(v_s_1085_, 1);
v_pos_1089_ = lean_ctor_get(v_s_1085_, 2);
v_errorMsg_1090_ = lean_ctor_get(v_s_1085_, 4);
v_recoveredErrors_1091_ = lean_ctor_get(v_s_1085_, 5);
v_isSharedCheck_1098_ = !lean_is_exclusive(v_s_1085_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v_s_1085_, 3);
lean_dec(v_unused_1099_);
v___x_1093_ = v_s_1085_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_recoveredErrors_1091_);
lean_inc(v_errorMsg_1090_);
lean_inc(v_pos_1089_);
lean_inc(v_lhsPrec_1088_);
lean_inc(v_stxStack_1087_);
lean_dec(v_s_1085_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 3, v_cache_1086_);
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_stxStack_1087_);
lean_ctor_set(v_reuseFailAlloc_1097_, 1, v_lhsPrec_1088_);
lean_ctor_set(v_reuseFailAlloc_1097_, 2, v_pos_1089_);
lean_ctor_set(v_reuseFailAlloc_1097_, 3, v_cache_1086_);
lean_ctor_set(v_reuseFailAlloc_1097_, 4, v_errorMsg_1090_);
lean_ctor_set(v_reuseFailAlloc_1097_, 5, v_recoveredErrors_1091_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_1100_, lean_object* v_n_1101_){
_start:
{
lean_object* v_stxStack_1102_; lean_object* v_lhsPrec_1103_; lean_object* v_pos_1104_; lean_object* v_cache_1105_; lean_object* v_errorMsg_1106_; lean_object* v_recoveredErrors_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1115_; 
v_stxStack_1102_ = lean_ctor_get(v_s_1100_, 0);
v_lhsPrec_1103_ = lean_ctor_get(v_s_1100_, 1);
v_pos_1104_ = lean_ctor_get(v_s_1100_, 2);
v_cache_1105_ = lean_ctor_get(v_s_1100_, 3);
v_errorMsg_1106_ = lean_ctor_get(v_s_1100_, 4);
v_recoveredErrors_1107_ = lean_ctor_get(v_s_1100_, 5);
v_isSharedCheck_1115_ = !lean_is_exclusive(v_s_1100_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1109_ = v_s_1100_;
v_isShared_1110_ = v_isSharedCheck_1115_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_recoveredErrors_1107_);
lean_inc(v_errorMsg_1106_);
lean_inc(v_cache_1105_);
lean_inc(v_pos_1104_);
lean_inc(v_lhsPrec_1103_);
lean_inc(v_stxStack_1102_);
lean_dec(v_s_1100_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1115_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1111_; lean_object* v___x_1113_; 
v___x_1111_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1102_, v_n_1101_);
if (v_isShared_1110_ == 0)
{
lean_ctor_set(v___x_1109_, 0, v___x_1111_);
v___x_1113_ = v___x_1109_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v___x_1111_);
lean_ctor_set(v_reuseFailAlloc_1114_, 1, v_lhsPrec_1103_);
lean_ctor_set(v_reuseFailAlloc_1114_, 2, v_pos_1104_);
lean_ctor_set(v_reuseFailAlloc_1114_, 3, v_cache_1105_);
lean_ctor_set(v_reuseFailAlloc_1114_, 4, v_errorMsg_1106_);
lean_ctor_set(v_reuseFailAlloc_1114_, 5, v_recoveredErrors_1107_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1116_){
_start:
{
lean_object* v_stxStack_1117_; lean_object* v_lhsPrec_1118_; lean_object* v_pos_1119_; lean_object* v_cache_1120_; lean_object* v_errorMsg_1121_; lean_object* v_recoveredErrors_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1130_; 
v_stxStack_1117_ = lean_ctor_get(v_s_1116_, 0);
v_lhsPrec_1118_ = lean_ctor_get(v_s_1116_, 1);
v_pos_1119_ = lean_ctor_get(v_s_1116_, 2);
v_cache_1120_ = lean_ctor_get(v_s_1116_, 3);
v_errorMsg_1121_ = lean_ctor_get(v_s_1116_, 4);
v_recoveredErrors_1122_ = lean_ctor_get(v_s_1116_, 5);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_s_1116_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1124_ = v_s_1116_;
v_isShared_1125_ = v_isSharedCheck_1130_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_recoveredErrors_1122_);
lean_inc(v_errorMsg_1121_);
lean_inc(v_cache_1120_);
lean_inc(v_pos_1119_);
lean_inc(v_lhsPrec_1118_);
lean_inc(v_stxStack_1117_);
lean_dec(v_s_1116_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1130_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1128_; 
v___x_1126_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1117_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1126_);
v___x_1128_ = v___x_1124_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1126_);
lean_ctor_set(v_reuseFailAlloc_1129_, 1, v_lhsPrec_1118_);
lean_ctor_set(v_reuseFailAlloc_1129_, 2, v_pos_1119_);
lean_ctor_set(v_reuseFailAlloc_1129_, 3, v_cache_1120_);
lean_ctor_set(v_reuseFailAlloc_1129_, 4, v_errorMsg_1121_);
lean_ctor_set(v_reuseFailAlloc_1129_, 5, v_recoveredErrors_1122_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1131_, lean_object* v_iniStackSz_1132_){
_start:
{
lean_object* v_stxStack_1133_; lean_object* v_lhsPrec_1134_; lean_object* v_pos_1135_; lean_object* v_cache_1136_; lean_object* v_errorMsg_1137_; lean_object* v_recoveredErrors_1138_; lean_object* v___x_1140_; uint8_t v_isShared_1141_; uint8_t v_isSharedCheck_1146_; 
v_stxStack_1133_ = lean_ctor_get(v_s_1131_, 0);
v_lhsPrec_1134_ = lean_ctor_get(v_s_1131_, 1);
v_pos_1135_ = lean_ctor_get(v_s_1131_, 2);
v_cache_1136_ = lean_ctor_get(v_s_1131_, 3);
v_errorMsg_1137_ = lean_ctor_get(v_s_1131_, 4);
v_recoveredErrors_1138_ = lean_ctor_get(v_s_1131_, 5);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_s_1131_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1140_ = v_s_1131_;
v_isShared_1141_ = v_isSharedCheck_1146_;
goto v_resetjp_1139_;
}
else
{
lean_inc(v_recoveredErrors_1138_);
lean_inc(v_errorMsg_1137_);
lean_inc(v_cache_1136_);
lean_inc(v_pos_1135_);
lean_inc(v_lhsPrec_1134_);
lean_inc(v_stxStack_1133_);
lean_dec(v_s_1131_);
v___x_1140_ = lean_box(0);
v_isShared_1141_ = v_isSharedCheck_1146_;
goto v_resetjp_1139_;
}
v_resetjp_1139_:
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1133_, v_iniStackSz_1132_);
if (v_isShared_1141_ == 0)
{
lean_ctor_set(v___x_1140_, 0, v___x_1142_);
v___x_1144_ = v___x_1140_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_lhsPrec_1134_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v_pos_1135_);
lean_ctor_set(v_reuseFailAlloc_1145_, 3, v_cache_1136_);
lean_ctor_set(v_reuseFailAlloc_1145_, 4, v_errorMsg_1137_);
lean_ctor_set(v_reuseFailAlloc_1145_, 5, v_recoveredErrors_1138_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1147_, lean_object* v_iniStackSz_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1147_, v_iniStackSz_1148_);
lean_dec(v_iniStackSz_1148_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1150_, lean_object* v_c_1151_, lean_object* v_pos_1152_){
_start:
{
lean_object* v_toInputContext_1153_; lean_object* v_stxStack_1154_; lean_object* v_lhsPrec_1155_; lean_object* v_cache_1156_; lean_object* v_errorMsg_1157_; lean_object* v_recoveredErrors_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1167_; 
v_toInputContext_1153_ = lean_ctor_get(v_c_1151_, 0);
v_stxStack_1154_ = lean_ctor_get(v_s_1150_, 0);
v_lhsPrec_1155_ = lean_ctor_get(v_s_1150_, 1);
v_cache_1156_ = lean_ctor_get(v_s_1150_, 3);
v_errorMsg_1157_ = lean_ctor_get(v_s_1150_, 4);
v_recoveredErrors_1158_ = lean_ctor_get(v_s_1150_, 5);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_s_1150_);
if (v_isSharedCheck_1167_ == 0)
{
lean_object* v_unused_1168_; 
v_unused_1168_ = lean_ctor_get(v_s_1150_, 2);
lean_dec(v_unused_1168_);
v___x_1160_ = v_s_1150_;
v_isShared_1161_ = v_isSharedCheck_1167_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_recoveredErrors_1158_);
lean_inc(v_errorMsg_1157_);
lean_inc(v_cache_1156_);
lean_inc(v_lhsPrec_1155_);
lean_inc(v_stxStack_1154_);
lean_dec(v_s_1150_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1167_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_inputString_1162_; lean_object* v___x_1163_; lean_object* v___x_1165_; 
v_inputString_1162_ = lean_ctor_get(v_toInputContext_1153_, 0);
v___x_1163_ = lean_string_utf8_next(v_inputString_1162_, v_pos_1152_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 2, v___x_1163_);
v___x_1165_ = v___x_1160_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_stxStack_1154_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_lhsPrec_1155_);
lean_ctor_set(v_reuseFailAlloc_1166_, 2, v___x_1163_);
lean_ctor_set(v_reuseFailAlloc_1166_, 3, v_cache_1156_);
lean_ctor_set(v_reuseFailAlloc_1166_, 4, v_errorMsg_1157_);
lean_ctor_set(v_reuseFailAlloc_1166_, 5, v_recoveredErrors_1158_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1169_, lean_object* v_c_1170_, lean_object* v_pos_1171_){
_start:
{
lean_object* v_res_1172_; 
v_res_1172_ = l_Lean_Parser_ParserState_next(v_s_1169_, v_c_1170_, v_pos_1171_);
lean_dec(v_pos_1171_);
lean_dec_ref(v_c_1170_);
return v_res_1172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1173_, lean_object* v_c_1174_, lean_object* v_pos_1175_){
_start:
{
lean_object* v_toInputContext_1176_; lean_object* v_stxStack_1177_; lean_object* v_lhsPrec_1178_; lean_object* v_cache_1179_; lean_object* v_errorMsg_1180_; lean_object* v_recoveredErrors_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1190_; 
v_toInputContext_1176_ = lean_ctor_get(v_c_1174_, 0);
v_stxStack_1177_ = lean_ctor_get(v_s_1173_, 0);
v_lhsPrec_1178_ = lean_ctor_get(v_s_1173_, 1);
v_cache_1179_ = lean_ctor_get(v_s_1173_, 3);
v_errorMsg_1180_ = lean_ctor_get(v_s_1173_, 4);
v_recoveredErrors_1181_ = lean_ctor_get(v_s_1173_, 5);
v_isSharedCheck_1190_ = !lean_is_exclusive(v_s_1173_);
if (v_isSharedCheck_1190_ == 0)
{
lean_object* v_unused_1191_; 
v_unused_1191_ = lean_ctor_get(v_s_1173_, 2);
lean_dec(v_unused_1191_);
v___x_1183_ = v_s_1173_;
v_isShared_1184_ = v_isSharedCheck_1190_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_recoveredErrors_1181_);
lean_inc(v_errorMsg_1180_);
lean_inc(v_cache_1179_);
lean_inc(v_lhsPrec_1178_);
lean_inc(v_stxStack_1177_);
lean_dec(v_s_1173_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1190_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v_inputString_1185_; lean_object* v___x_1186_; lean_object* v___x_1188_; 
v_inputString_1185_ = lean_ctor_get(v_toInputContext_1176_, 0);
v___x_1186_ = lean_string_utf8_next_fast(v_inputString_1185_, v_pos_1175_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 2, v___x_1186_);
v___x_1188_ = v___x_1183_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_stxStack_1177_);
lean_ctor_set(v_reuseFailAlloc_1189_, 1, v_lhsPrec_1178_);
lean_ctor_set(v_reuseFailAlloc_1189_, 2, v___x_1186_);
lean_ctor_set(v_reuseFailAlloc_1189_, 3, v_cache_1179_);
lean_ctor_set(v_reuseFailAlloc_1189_, 4, v_errorMsg_1180_);
lean_ctor_set(v_reuseFailAlloc_1189_, 5, v_recoveredErrors_1181_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1192_, lean_object* v_c_1193_, lean_object* v_pos_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1192_, v_c_1193_, v_pos_1194_);
lean_dec(v_pos_1194_);
lean_dec_ref(v_c_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1196_, lean_object* v_c_1197_, lean_object* v_pos_1198_, lean_object* v_h_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1196_, v_c_1197_, v_pos_1198_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1201_, lean_object* v_c_1202_, lean_object* v_pos_1203_, lean_object* v_h_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Parser_ParserState_next_x27(v_s_1201_, v_c_1202_, v_pos_1203_, v_h_1204_);
lean_dec(v_pos_1203_);
lean_dec_ref(v_c_1202_);
return v_res_1205_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1206_, lean_object* v_x_1207_){
_start:
{
if (lean_obj_tag(v_x_1206_) == 0)
{
if (lean_obj_tag(v_x_1207_) == 0)
{
uint8_t v___x_1208_; 
v___x_1208_ = 1;
return v___x_1208_;
}
else
{
uint8_t v___x_1209_; 
v___x_1209_ = 0;
return v___x_1209_;
}
}
else
{
if (lean_obj_tag(v_x_1207_) == 0)
{
uint8_t v___x_1210_; 
v___x_1210_ = 0;
return v___x_1210_;
}
else
{
lean_object* v_val_1211_; lean_object* v_val_1212_; uint8_t v___x_1213_; 
v_val_1211_ = lean_ctor_get(v_x_1206_, 0);
v_val_1212_ = lean_ctor_get(v_x_1207_, 0);
v___x_1213_ = l_Lean_Parser_instBEqError_beq(v_val_1211_, v_val_1212_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1214_, lean_object* v_x_1215_){
_start:
{
uint8_t v_res_1216_; lean_object* v_r_1217_; 
v_res_1216_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1214_, v_x_1215_);
lean_dec(v_x_1215_);
lean_dec(v_x_1214_);
v_r_1217_ = lean_box(v_res_1216_);
return v_r_1217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1218_, lean_object* v_k_1219_, lean_object* v_iniStackSz_1220_){
_start:
{
lean_object* v_stxStack_1221_; lean_object* v_lhsPrec_1222_; lean_object* v_pos_1223_; lean_object* v_cache_1224_; lean_object* v_errorMsg_1225_; lean_object* v_recoveredErrors_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1247_; 
v_stxStack_1221_ = lean_ctor_get(v_s_1218_, 0);
v_lhsPrec_1222_ = lean_ctor_get(v_s_1218_, 1);
v_pos_1223_ = lean_ctor_get(v_s_1218_, 2);
v_cache_1224_ = lean_ctor_get(v_s_1218_, 3);
v_errorMsg_1225_ = lean_ctor_get(v_s_1218_, 4);
v_recoveredErrors_1226_ = lean_ctor_get(v_s_1218_, 5);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_s_1218_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1228_ = v_s_1218_;
v_isShared_1229_ = v_isSharedCheck_1247_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_recoveredErrors_1226_);
lean_inc(v_errorMsg_1225_);
lean_inc(v_cache_1224_);
lean_inc(v_pos_1223_);
lean_inc(v_lhsPrec_1222_);
lean_inc(v_stxStack_1221_);
lean_dec(v_s_1218_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1247_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1240_; uint8_t v___x_1241_; 
v___x_1240_ = lean_box(0);
v___x_1241_ = l_Option_instBEq_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1225_, v___x_1240_);
if (v___x_1241_ == 0)
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1221_);
v___x_1243_ = lean_nat_dec_eq(v___x_1242_, v_iniStackSz_1220_);
lean_dec(v___x_1242_);
if (v___x_1243_ == 0)
{
goto v___jp_1230_;
}
else
{
lean_object* v___x_1244_; lean_object* v_stack_1245_; lean_object* v___x_1246_; 
lean_del_object(v___x_1228_);
lean_dec(v_k_1219_);
v___x_1244_ = lean_box(0);
v_stack_1245_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1221_, v___x_1244_);
v___x_1246_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1246_, 0, v_stack_1245_);
lean_ctor_set(v___x_1246_, 1, v_lhsPrec_1222_);
lean_ctor_set(v___x_1246_, 2, v_pos_1223_);
lean_ctor_set(v___x_1246_, 3, v_cache_1224_);
lean_ctor_set(v___x_1246_, 4, v_errorMsg_1225_);
lean_ctor_set(v___x_1246_, 5, v_recoveredErrors_1226_);
return v___x_1246_;
}
}
else
{
goto v___jp_1230_;
}
v___jp_1230_:
{
lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v_newNode_1234_; lean_object* v_stack_1235_; lean_object* v_stack_1236_; lean_object* v___x_1238_; 
v___x_1231_ = lean_box(2);
v___x_1232_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1221_);
v___x_1233_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1221_, v_iniStackSz_1220_, v___x_1232_);
lean_dec(v___x_1232_);
v_newNode_1234_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1234_, 0, v___x_1231_);
lean_ctor_set(v_newNode_1234_, 1, v_k_1219_);
lean_ctor_set(v_newNode_1234_, 2, v___x_1233_);
v_stack_1235_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1221_, v_iniStackSz_1220_);
v_stack_1236_ = l_Lean_Parser_SyntaxStack_push(v_stack_1235_, v_newNode_1234_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 0, v_stack_1236_);
v___x_1238_ = v___x_1228_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_stack_1236_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v_lhsPrec_1222_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v_pos_1223_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v_cache_1224_);
lean_ctor_set(v_reuseFailAlloc_1239_, 4, v_errorMsg_1225_);
lean_ctor_set(v_reuseFailAlloc_1239_, 5, v_recoveredErrors_1226_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1248_, lean_object* v_k_1249_, lean_object* v_iniStackSz_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l_Lean_Parser_ParserState_mkNode(v_s_1248_, v_k_1249_, v_iniStackSz_1250_);
lean_dec(v_iniStackSz_1250_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1252_, lean_object* v_k_1253_, lean_object* v_iniStackSz_1254_){
_start:
{
lean_object* v_stxStack_1255_; lean_object* v_lhsPrec_1256_; lean_object* v_pos_1257_; lean_object* v_cache_1258_; lean_object* v_errorMsg_1259_; lean_object* v_recoveredErrors_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1275_; 
v_stxStack_1255_ = lean_ctor_get(v_s_1252_, 0);
v_lhsPrec_1256_ = lean_ctor_get(v_s_1252_, 1);
v_pos_1257_ = lean_ctor_get(v_s_1252_, 2);
v_cache_1258_ = lean_ctor_get(v_s_1252_, 3);
v_errorMsg_1259_ = lean_ctor_get(v_s_1252_, 4);
v_recoveredErrors_1260_ = lean_ctor_get(v_s_1252_, 5);
v_isSharedCheck_1275_ = !lean_is_exclusive(v_s_1252_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1262_ = v_s_1252_;
v_isShared_1263_ = v_isSharedCheck_1275_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_recoveredErrors_1260_);
lean_inc(v_errorMsg_1259_);
lean_inc(v_cache_1258_);
lean_inc(v_pos_1257_);
lean_inc(v_lhsPrec_1256_);
lean_inc(v_stxStack_1255_);
lean_dec(v_s_1252_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1275_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v_newNode_1269_; lean_object* v_stack_1270_; lean_object* v_stack_1271_; lean_object* v___x_1273_; 
v___x_1264_ = lean_box(2);
v___x_1265_ = lean_unsigned_to_nat(1u);
v___x_1266_ = lean_nat_sub(v_iniStackSz_1254_, v___x_1265_);
v___x_1267_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1255_);
v___x_1268_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1255_, v___x_1266_, v___x_1267_);
lean_dec(v___x_1267_);
v_newNode_1269_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1269_, 0, v___x_1264_);
lean_ctor_set(v_newNode_1269_, 1, v_k_1253_);
lean_ctor_set(v_newNode_1269_, 2, v___x_1268_);
v_stack_1270_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1255_, v___x_1266_);
lean_dec(v___x_1266_);
v_stack_1271_ = l_Lean_Parser_SyntaxStack_push(v_stack_1270_, v_newNode_1269_);
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v_stack_1271_);
v___x_1273_ = v___x_1262_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_stack_1271_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_lhsPrec_1256_);
lean_ctor_set(v_reuseFailAlloc_1274_, 2, v_pos_1257_);
lean_ctor_set(v_reuseFailAlloc_1274_, 3, v_cache_1258_);
lean_ctor_set(v_reuseFailAlloc_1274_, 4, v_errorMsg_1259_);
lean_ctor_set(v_reuseFailAlloc_1274_, 5, v_recoveredErrors_1260_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1276_, lean_object* v_k_1277_, lean_object* v_iniStackSz_1278_){
_start:
{
lean_object* v_res_1279_; 
v_res_1279_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1276_, v_k_1277_, v_iniStackSz_1278_);
lean_dec(v_iniStackSz_1278_);
return v_res_1279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1282_){
_start:
{
lean_object* v_errorMsg_1283_; 
v_errorMsg_1283_ = lean_ctor_get(v_s_1282_, 4);
if (lean_obj_tag(v_errorMsg_1283_) == 0)
{
lean_object* v_recoveredErrors_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v_recoveredErrors_1284_ = lean_ctor_get(v_s_1282_, 5);
lean_inc_ref(v_recoveredErrors_1284_);
lean_dec_ref(v_s_1282_);
v___x_1285_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1286_ = l_Array_append___redArg(v_recoveredErrors_1284_, v___x_1285_);
return v___x_1286_;
}
else
{
lean_object* v_stxStack_1287_; lean_object* v_pos_1288_; lean_object* v_recoveredErrors_1289_; lean_object* v_val_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_inc_ref(v_errorMsg_1283_);
v_stxStack_1287_ = lean_ctor_get(v_s_1282_, 0);
lean_inc_ref(v_stxStack_1287_);
v_pos_1288_ = lean_ctor_get(v_s_1282_, 2);
lean_inc(v_pos_1288_);
v_recoveredErrors_1289_ = lean_ctor_get(v_s_1282_, 5);
lean_inc_ref(v_recoveredErrors_1289_);
lean_dec_ref(v_s_1282_);
v_val_1290_ = lean_ctor_get(v_errorMsg_1283_, 0);
lean_inc(v_val_1290_);
lean_dec_ref_known(v_errorMsg_1283_, 1);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v_stxStack_1287_);
lean_ctor_set(v___x_1291_, 1, v_val_1290_);
v___x_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1292_, 0, v_pos_1288_);
lean_ctor_set(v___x_1292_, 1, v___x_1291_);
v___x_1293_ = lean_unsigned_to_nat(1u);
v___x_1294_ = lean_mk_empty_array_with_capacity(v___x_1293_);
v___x_1295_ = lean_array_push(v___x_1294_, v___x_1292_);
v___x_1296_ = l_Array_append___redArg(v_recoveredErrors_1289_, v___x_1295_);
lean_dec_ref(v___x_1295_);
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1297_, lean_object* v_e_1298_){
_start:
{
lean_object* v_stxStack_1299_; lean_object* v_lhsPrec_1300_; lean_object* v_pos_1301_; lean_object* v_cache_1302_; lean_object* v_recoveredErrors_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1311_; 
v_stxStack_1299_ = lean_ctor_get(v_s_1297_, 0);
v_lhsPrec_1300_ = lean_ctor_get(v_s_1297_, 1);
v_pos_1301_ = lean_ctor_get(v_s_1297_, 2);
v_cache_1302_ = lean_ctor_get(v_s_1297_, 3);
v_recoveredErrors_1303_ = lean_ctor_get(v_s_1297_, 5);
v_isSharedCheck_1311_ = !lean_is_exclusive(v_s_1297_);
if (v_isSharedCheck_1311_ == 0)
{
lean_object* v_unused_1312_; 
v_unused_1312_ = lean_ctor_get(v_s_1297_, 4);
lean_dec(v_unused_1312_);
v___x_1305_ = v_s_1297_;
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_recoveredErrors_1303_);
lean_inc(v_cache_1302_);
lean_inc(v_pos_1301_);
lean_inc(v_lhsPrec_1300_);
lean_inc(v_stxStack_1299_);
lean_dec(v_s_1297_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1311_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
v___x_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_e_1298_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set(v___x_1305_, 4, v___x_1307_);
v___x_1309_ = v___x_1305_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_stxStack_1299_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v_lhsPrec_1300_);
lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_pos_1301_);
lean_ctor_set(v_reuseFailAlloc_1310_, 3, v_cache_1302_);
lean_ctor_set(v_reuseFailAlloc_1310_, 4, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1310_, 5, v_recoveredErrors_1303_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1313_, lean_object* v_msg_1314_){
_start:
{
lean_object* v_stxStack_1315_; lean_object* v_lhsPrec_1316_; lean_object* v_pos_1317_; lean_object* v_cache_1318_; lean_object* v_recoveredErrors_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1333_; 
v_stxStack_1315_ = lean_ctor_get(v_s_1313_, 0);
v_lhsPrec_1316_ = lean_ctor_get(v_s_1313_, 1);
v_pos_1317_ = lean_ctor_get(v_s_1313_, 2);
v_cache_1318_ = lean_ctor_get(v_s_1313_, 3);
v_recoveredErrors_1319_ = lean_ctor_get(v_s_1313_, 5);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_s_1313_);
if (v_isSharedCheck_1333_ == 0)
{
lean_object* v_unused_1334_; 
v_unused_1334_ = lean_ctor_get(v_s_1313_, 4);
lean_dec(v_unused_1334_);
v___x_1321_ = v_s_1313_;
v_isShared_1322_ = v_isSharedCheck_1333_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_recoveredErrors_1319_);
lean_inc(v_cache_1318_);
lean_inc(v_pos_1317_);
lean_inc(v_lhsPrec_1316_);
lean_inc(v_stxStack_1315_);
lean_dec(v_s_1313_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1333_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1323_ = lean_box(0);
v___x_1324_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1325_ = lean_box(0);
v___x_1326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1326_, 0, v_msg_1314_);
lean_ctor_set(v___x_1326_, 1, v___x_1325_);
v___x_1327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1323_);
lean_ctor_set(v___x_1327_, 1, v___x_1324_);
lean_ctor_set(v___x_1327_, 2, v___x_1326_);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 4, v___x_1328_);
v___x_1330_ = v___x_1321_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_stxStack_1315_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v_lhsPrec_1316_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_pos_1317_);
lean_ctor_set(v_reuseFailAlloc_1332_, 3, v_cache_1318_);
lean_ctor_set(v_reuseFailAlloc_1332_, 4, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1332_, 5, v_recoveredErrors_1319_);
v___x_1330_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1330_, v___x_1323_);
return v___x_1331_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1335_, lean_object* v_msg_1336_, lean_object* v_expected_1337_, uint8_t v_pushMissing_1338_){
_start:
{
lean_object* v_stxStack_1339_; lean_object* v_lhsPrec_1340_; lean_object* v_pos_1341_; lean_object* v_cache_1342_; lean_object* v_recoveredErrors_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1354_; 
v_stxStack_1339_ = lean_ctor_get(v_s_1335_, 0);
v_lhsPrec_1340_ = lean_ctor_get(v_s_1335_, 1);
v_pos_1341_ = lean_ctor_get(v_s_1335_, 2);
v_cache_1342_ = lean_ctor_get(v_s_1335_, 3);
v_recoveredErrors_1343_ = lean_ctor_get(v_s_1335_, 5);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_s_1335_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v_s_1335_, 4);
lean_dec(v_unused_1355_);
v___x_1345_ = v_s_1335_;
v_isShared_1346_ = v_isSharedCheck_1354_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_recoveredErrors_1343_);
lean_inc(v_cache_1342_);
lean_inc(v_pos_1341_);
lean_inc(v_lhsPrec_1340_);
lean_inc(v_stxStack_1339_);
lean_dec(v_s_1335_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1354_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v_s_1351_; 
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v_msg_1336_);
lean_ctor_set(v___x_1348_, 2, v_expected_1337_);
v___x_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
if (v_isShared_1346_ == 0)
{
lean_ctor_set(v___x_1345_, 4, v___x_1349_);
v_s_1351_ = v___x_1345_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_stxStack_1339_);
lean_ctor_set(v_reuseFailAlloc_1353_, 1, v_lhsPrec_1340_);
lean_ctor_set(v_reuseFailAlloc_1353_, 2, v_pos_1341_);
lean_ctor_set(v_reuseFailAlloc_1353_, 3, v_cache_1342_);
lean_ctor_set(v_reuseFailAlloc_1353_, 4, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1353_, 5, v_recoveredErrors_1343_);
v_s_1351_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
if (v_pushMissing_1338_ == 0)
{
return v_s_1351_;
}
else
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1351_, v___x_1347_);
return v___x_1352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1356_, lean_object* v_msg_1357_, lean_object* v_expected_1358_, lean_object* v_pushMissing_1359_){
_start:
{
uint8_t v_pushMissing_boxed_1360_; lean_object* v_res_1361_; 
v_pushMissing_boxed_1360_ = lean_unbox(v_pushMissing_1359_);
v_res_1361_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1356_, v_msg_1357_, v_expected_1358_, v_pushMissing_boxed_1360_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1363_, lean_object* v_expected_1364_){
_start:
{
lean_object* v___x_1365_; uint8_t v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1366_ = 1;
v___x_1367_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1363_, v___x_1365_, v_expected_1364_, v___x_1366_);
return v___x_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1368_, lean_object* v_ex_1369_, lean_object* v_pos_1370_, lean_object* v_initStackSz_x3f_1371_){
_start:
{
lean_object* v_s_1373_; lean_object* v_s_1392_; 
v_s_1392_ = l_Lean_Parser_ParserState_setPos(v_s_1368_, v_pos_1370_);
if (lean_obj_tag(v_initStackSz_x3f_1371_) == 1)
{
lean_object* v_val_1393_; lean_object* v_s_1394_; 
v_val_1393_ = lean_ctor_get(v_initStackSz_x3f_1371_, 0);
v_s_1394_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1392_, v_val_1393_);
v_s_1373_ = v_s_1394_;
goto v___jp_1372_;
}
else
{
v_s_1373_ = v_s_1392_;
goto v___jp_1372_;
}
v___jp_1372_:
{
lean_object* v_stxStack_1374_; lean_object* v_lhsPrec_1375_; lean_object* v_pos_1376_; lean_object* v_cache_1377_; lean_object* v_recoveredErrors_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1390_; 
v_stxStack_1374_ = lean_ctor_get(v_s_1373_, 0);
v_lhsPrec_1375_ = lean_ctor_get(v_s_1373_, 1);
v_pos_1376_ = lean_ctor_get(v_s_1373_, 2);
v_cache_1377_ = lean_ctor_get(v_s_1373_, 3);
v_recoveredErrors_1378_ = lean_ctor_get(v_s_1373_, 5);
v_isSharedCheck_1390_ = !lean_is_exclusive(v_s_1373_);
if (v_isSharedCheck_1390_ == 0)
{
lean_object* v_unused_1391_; 
v_unused_1391_ = lean_ctor_get(v_s_1373_, 4);
lean_dec(v_unused_1391_);
v___x_1380_ = v_s_1373_;
v_isShared_1381_ = v_isSharedCheck_1390_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_recoveredErrors_1378_);
lean_inc(v_cache_1377_);
lean_inc(v_pos_1376_);
lean_inc(v_lhsPrec_1375_);
lean_inc(v_stxStack_1374_);
lean_dec(v_s_1373_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1390_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_s_1387_; 
v___x_1382_ = lean_box(0);
v___x_1383_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1384_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1382_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
lean_ctor_set(v___x_1384_, 2, v_ex_1369_);
v___x_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 4, v___x_1385_);
v_s_1387_ = v___x_1380_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_stxStack_1374_);
lean_ctor_set(v_reuseFailAlloc_1389_, 1, v_lhsPrec_1375_);
lean_ctor_set(v_reuseFailAlloc_1389_, 2, v_pos_1376_);
lean_ctor_set(v_reuseFailAlloc_1389_, 3, v_cache_1377_);
lean_ctor_set(v_reuseFailAlloc_1389_, 4, v___x_1385_);
lean_ctor_set(v_reuseFailAlloc_1389_, 5, v_recoveredErrors_1378_);
v_s_1387_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
lean_object* v___x_1388_; 
v___x_1388_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1387_, v___x_1382_);
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1395_, lean_object* v_ex_1396_, lean_object* v_pos_1397_, lean_object* v_initStackSz_x3f_1398_){
_start:
{
lean_object* v_res_1399_; 
v_res_1399_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1395_, v_ex_1396_, v_pos_1397_, v_initStackSz_x3f_1398_);
lean_dec(v_initStackSz_x3f_1398_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1400_, lean_object* v_msg_1401_, lean_object* v_pos_1402_, lean_object* v_initStackSz_x3f_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_box(0);
v___x_1405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1405_, 0, v_msg_1401_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
v___x_1406_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1400_, v___x_1405_, v_pos_1402_, v_initStackSz_x3f_1403_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1407_, lean_object* v_msg_1408_, lean_object* v_pos_1409_, lean_object* v_initStackSz_x3f_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1407_, v_msg_1408_, v_pos_1409_, v_initStackSz_x3f_1410_);
lean_dec(v_initStackSz_x3f_1410_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1412_){
_start:
{
lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = lean_panic_fn_borrowed(v___x_1413_, v_msg_1412_);
return v___x_1414_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1418_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1419_ = lean_unsigned_to_nat(14u);
v___x_1420_ = lean_unsigned_to_nat(22u);
v___x_1421_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1422_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1423_ = l_mkPanicMessageWithDecl(v___x_1422_, v___x_1421_, v___x_1420_, v___x_1419_, v___x_1418_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1424_, lean_object* v_ex_1425_, lean_object* v_iniPos_1426_){
_start:
{
lean_object* v_stxStack_1427_; lean_object* v_tk_1428_; lean_object* v___y_1430_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_stxStack_1427_ = lean_ctor_get(v_s_1424_, 0);
v_tk_1428_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1427_);
v___x_1451_ = lean_unsigned_to_nat(0u);
v___x_1452_ = lean_nat_dec_lt(v___x_1451_, v_iniPos_1426_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; 
lean_dec(v_iniPos_1426_);
v___x_1453_ = l_Lean_Syntax_getPos_x3f(v_tk_1428_, v___x_1452_);
if (lean_obj_tag(v___x_1453_) == 0)
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1455_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1454_);
v___y_1430_ = v___x_1455_;
goto v___jp_1429_;
}
else
{
lean_object* v_val_1456_; 
v_val_1456_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_val_1456_);
lean_dec_ref_known(v___x_1453_, 1);
v___y_1430_ = v_val_1456_;
goto v___jp_1429_;
}
}
else
{
v___y_1430_ = v_iniPos_1426_;
goto v___jp_1429_;
}
v___jp_1429_:
{
lean_object* v_s_1431_; lean_object* v_stxStack_1432_; lean_object* v_lhsPrec_1433_; lean_object* v_pos_1434_; lean_object* v_cache_1435_; lean_object* v_recoveredErrors_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1449_; 
v_s_1431_ = l_Lean_Parser_ParserState_setPos(v_s_1424_, v___y_1430_);
v_stxStack_1432_ = lean_ctor_get(v_s_1431_, 0);
v_lhsPrec_1433_ = lean_ctor_get(v_s_1431_, 1);
v_pos_1434_ = lean_ctor_get(v_s_1431_, 2);
v_cache_1435_ = lean_ctor_get(v_s_1431_, 3);
v_recoveredErrors_1436_ = lean_ctor_get(v_s_1431_, 5);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_s_1431_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; 
v_unused_1450_ = lean_ctor_get(v_s_1431_, 4);
lean_dec(v_unused_1450_);
v___x_1438_ = v_s_1431_;
v_isShared_1439_ = v_isSharedCheck_1449_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_recoveredErrors_1436_);
lean_inc(v_cache_1435_);
lean_inc(v_pos_1434_);
lean_inc(v_lhsPrec_1433_);
lean_inc(v_stxStack_1432_);
lean_dec(v_s_1431_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1449_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v_s_1444_; 
v___x_1440_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1441_, 0, v_tk_1428_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_ctor_set(v___x_1441_, 2, v_ex_1425_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
if (v_isShared_1439_ == 0)
{
lean_ctor_set(v___x_1438_, 4, v___x_1442_);
v_s_1444_ = v___x_1438_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_stxStack_1432_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_lhsPrec_1433_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_pos_1434_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v_cache_1435_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1448_, 5, v_recoveredErrors_1436_);
v_s_1444_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1445_ = l_Lean_Parser_ParserState_popSyntax(v_s_1444_);
v___x_1446_ = lean_box(0);
v___x_1447_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1445_, v___x_1446_);
return v___x_1447_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1457_, lean_object* v_msg_1458_, lean_object* v_iniPos_1459_){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1460_ = lean_box(0);
v___x_1461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1461_, 0, v_msg_1458_);
lean_ctor_set(v___x_1461_, 1, v___x_1460_);
v___x_1462_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1457_, v___x_1461_, v_iniPos_1459_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1463_, lean_object* v_msg_1464_, lean_object* v_pos_1465_){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; lean_object* v___x_1469_; 
v___x_1466_ = l_Lean_Parser_ParserState_setPos(v_s_1463_, v_pos_1465_);
v___x_1467_ = lean_box(0);
v___x_1468_ = 1;
v___x_1469_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1466_, v_msg_1464_, v___x_1467_, v___x_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1471_, lean_object* v_as_1472_, size_t v_sz_1473_, size_t v_i_1474_, lean_object* v_b_1475_){
_start:
{
uint8_t v___x_1476_; 
v___x_1476_ = lean_usize_dec_lt(v_i_1474_, v_sz_1473_);
if (v___x_1476_ == 0)
{
lean_dec_ref(v_ctx_1471_);
return v_b_1475_;
}
else
{
lean_object* v_a_1477_; lean_object* v_snd_1478_; lean_object* v_fst_1479_; lean_object* v_snd_1480_; lean_object* v_errStr_1482_; lean_object* v_errStr_1493_; uint8_t v___x_1494_; 
v_a_1477_ = lean_array_uget_borrowed(v_as_1472_, v_i_1474_);
v_snd_1478_ = lean_ctor_get(v_a_1477_, 1);
v_fst_1479_ = lean_ctor_get(v_a_1477_, 0);
v_snd_1480_ = lean_ctor_get(v_snd_1478_, 1);
v_errStr_1493_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1494_ = lean_string_dec_eq(v_b_1475_, v_errStr_1493_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1496_ = lean_string_append(v_b_1475_, v___x_1495_);
v_errStr_1482_ = v___x_1496_;
goto v___jp_1481_;
}
else
{
v_errStr_1482_ = v_b_1475_;
goto v___jp_1481_;
}
v___jp_1481_:
{
lean_object* v_fileName_1483_; lean_object* v_fileMap_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; size_t v___x_1490_; size_t v___x_1491_; 
v_fileName_1483_ = lean_ctor_get(v_ctx_1471_, 1);
v_fileMap_1484_ = lean_ctor_get(v_ctx_1471_, 2);
lean_inc_ref(v_fileMap_1484_);
v___x_1485_ = l_Lean_FileMap_toPosition(v_fileMap_1484_, v_fst_1479_);
lean_inc(v_snd_1480_);
v___x_1486_ = l_Lean_Parser_Error_toString(v_snd_1480_);
v___x_1487_ = lean_box(0);
lean_inc_ref(v_fileName_1483_);
v___x_1488_ = l_Lean_mkErrorStringWithPos(v_fileName_1483_, v___x_1485_, v___x_1486_, v___x_1487_, v___x_1487_, v___x_1487_);
lean_dec_ref(v___x_1486_);
v___x_1489_ = lean_string_append(v_errStr_1482_, v___x_1488_);
lean_dec_ref(v___x_1488_);
v___x_1490_ = ((size_t)1ULL);
v___x_1491_ = lean_usize_add(v_i_1474_, v___x_1490_);
v_i_1474_ = v___x_1491_;
v_b_1475_ = v___x_1489_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1497_, lean_object* v_as_1498_, lean_object* v_sz_1499_, lean_object* v_i_1500_, lean_object* v_b_1501_){
_start:
{
size_t v_sz_boxed_1502_; size_t v_i_boxed_1503_; lean_object* v_res_1504_; 
v_sz_boxed_1502_ = lean_unbox_usize(v_sz_1499_);
lean_dec(v_sz_1499_);
v_i_boxed_1503_ = lean_unbox_usize(v_i_1500_);
lean_dec(v_i_1500_);
v_res_1504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1497_, v_as_1498_, v_sz_boxed_1502_, v_i_boxed_1503_, v_b_1501_);
lean_dec_ref(v_as_1498_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1505_, lean_object* v_s_1506_){
_start:
{
lean_object* v_errStr_1507_; lean_object* v___x_1508_; size_t v_sz_1509_; size_t v___x_1510_; lean_object* v___x_1511_; 
v_errStr_1507_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1508_ = l_Lean_Parser_ParserState_allErrors(v_s_1506_);
v_sz_1509_ = lean_array_size(v___x_1508_);
v___x_1510_ = ((size_t)0ULL);
v___x_1511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1505_, v___x_1508_, v_sz_1509_, v___x_1510_, v_errStr_1507_);
lean_dec_ref(v___x_1508_);
return v___x_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1512_, lean_object* v_s_1513_){
_start:
{
lean_inc_ref(v_s_1513_);
return v_s_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1514_, lean_object* v_s_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1514_, v_s_1515_);
lean_dec_ref(v_s_1515_);
lean_dec_ref(v_x_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx(lean_object* v_x_1519_){
_start:
{
switch(lean_obj_tag(v_x_1519_))
{
case 0:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
return v___x_1520_;
}
case 1:
{
lean_object* v___x_1521_; 
v___x_1521_ = lean_unsigned_to_nat(1u);
return v___x_1521_;
}
case 2:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_unsigned_to_nat(2u);
return v___x_1522_;
}
default: 
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_unsigned_to_nat(3u);
return v___x_1523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___boxed(lean_object* v_x_1524_){
_start:
{
lean_object* v_res_1525_; 
v_res_1525_ = l_Lean_Parser_FirstTokens_ctorIdx(v_x_1524_);
lean_dec(v_x_1524_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1526_, lean_object* v_k_1527_){
_start:
{
switch(lean_obj_tag(v_t_1526_))
{
case 2:
{
lean_object* v_a_1528_; lean_object* v___x_1529_; 
v_a_1528_ = lean_ctor_get(v_t_1526_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v_t_1526_, 1);
v___x_1529_ = lean_apply_1(v_k_1527_, v_a_1528_);
return v___x_1529_;
}
case 3:
{
lean_object* v_a_1530_; lean_object* v___x_1531_; 
v_a_1530_ = lean_ctor_get(v_t_1526_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v_t_1526_, 1);
v___x_1531_ = lean_apply_1(v_k_1527_, v_a_1530_);
return v___x_1531_;
}
default: 
{
lean_dec(v_t_1526_);
return v_k_1527_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1532_, lean_object* v_ctorIdx_1533_, lean_object* v_t_1534_, lean_object* v_h_1535_, lean_object* v_k_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1534_, v_k_1536_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1538_, lean_object* v_ctorIdx_1539_, lean_object* v_t_1540_, lean_object* v_h_1541_, lean_object* v_k_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1538_, v_ctorIdx_1539_, v_t_1540_, v_h_1541_, v_k_1542_);
lean_dec(v_ctorIdx_1539_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1544_, lean_object* v_epsilon_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1544_, v_epsilon_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1547_, lean_object* v_t_1548_, lean_object* v_h_1549_, lean_object* v_epsilon_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1548_, v_epsilon_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1552_, lean_object* v_unknown_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1552_, v_unknown_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1555_, lean_object* v_t_1556_, lean_object* v_h_1557_, lean_object* v_unknown_1558_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1556_, v_unknown_1558_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1560_, lean_object* v_tokens_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1560_, v_tokens_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1563_, lean_object* v_t_1564_, lean_object* v_h_1565_, lean_object* v_tokens_1566_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1564_, v_tokens_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1568_, lean_object* v_optTokens_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1568_, v_optTokens_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1571_, lean_object* v_t_1572_, lean_object* v_h_1573_, lean_object* v_optTokens_1574_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1572_, v_optTokens_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_box(0);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = lean_box(0);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1578_, lean_object* v_x_1579_){
_start:
{
switch(lean_obj_tag(v_x_1578_))
{
case 0:
{
return v_x_1579_;
}
case 3:
{
switch(lean_obj_tag(v_x_1579_))
{
case 3:
{
lean_object* v_a_1580_; lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1589_; 
v_a_1580_ = lean_ctor_get(v_x_1578_, 0);
lean_inc(v_a_1580_);
lean_dec_ref_known(v_x_1578_, 1);
v_a_1581_ = lean_ctor_get(v_x_1579_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_x_1579_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1583_ = v_x_1579_;
v_isShared_1584_ = v_isSharedCheck_1589_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v_x_1579_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1589_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = l_List_appendTR___redArg(v_a_1580_, v_a_1581_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 0, v___x_1585_);
v___x_1587_ = v___x_1583_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v___x_1585_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
case 2:
{
lean_object* v_a_1590_; lean_object* v_a_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1599_; 
v_a_1590_ = lean_ctor_get(v_x_1578_, 0);
lean_inc(v_a_1590_);
lean_dec_ref_known(v_x_1578_, 1);
v_a_1591_ = lean_ctor_get(v_x_1579_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_x_1579_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1593_ = v_x_1579_;
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_a_1591_);
lean_dec(v_x_1579_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = l_List_appendTR___redArg(v_a_1590_, v_a_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 0, v___x_1595_);
v___x_1597_ = v___x_1593_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
case 1:
{
lean_dec_ref_known(v_x_1578_, 1);
return v_x_1579_;
}
default: 
{
lean_dec(v_x_1579_);
return v_x_1578_;
}
}
}
default: 
{
lean_dec(v_x_1579_);
return v_x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1600_){
_start:
{
if (lean_obj_tag(v_x_1600_) == 2)
{
lean_object* v_a_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1608_; 
v_a_1601_ = lean_ctor_get(v_x_1600_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_x_1600_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1603_ = v_x_1600_;
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_a_1601_);
lean_dec(v_x_1600_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1608_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
lean_ctor_set_tag(v___x_1603_, 3);
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1601_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
else
{
return v_x_1600_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1609_, lean_object* v_x_1610_){
_start:
{
lean_object* v_s_u2081_1612_; lean_object* v_s_u2082_1613_; 
switch(lean_obj_tag(v_x_1609_))
{
case 0:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1610_);
return v___x_1616_;
}
case 2:
{
switch(lean_obj_tag(v_x_1610_))
{
case 0:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1609_);
return v___x_1617_;
}
case 2:
{
lean_object* v_a_1618_; lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1627_; 
v_a_1618_ = lean_ctor_get(v_x_1609_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v_x_1609_, 1);
v_a_1619_ = lean_ctor_get(v_x_1610_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_x_1610_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1621_ = v_x_1610_;
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v_x_1610_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1627_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1625_; 
v___x_1623_ = l_List_appendTR___redArg(v_a_1618_, v_a_1619_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1623_);
v___x_1625_ = v___x_1621_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v___x_1623_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
case 3:
{
lean_object* v_a_1628_; lean_object* v_a_1629_; 
v_a_1628_ = lean_ctor_get(v_x_1609_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v_x_1609_, 1);
v_a_1629_ = lean_ctor_get(v_x_1610_, 0);
lean_inc(v_a_1629_);
lean_dec_ref_known(v_x_1610_, 1);
v_s_u2081_1612_ = v_a_1628_;
v_s_u2082_1613_ = v_a_1629_;
goto v___jp_1611_;
}
default: 
{
lean_object* v___x_1630_; 
lean_dec_ref_known(v_x_1609_, 1);
lean_dec(v_x_1610_);
v___x_1630_ = lean_box(1);
return v___x_1630_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1610_))
{
case 0:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1609_);
return v___x_1631_;
}
case 3:
{
lean_object* v_a_1632_; lean_object* v_a_1633_; 
v_a_1632_ = lean_ctor_get(v_x_1609_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v_x_1609_, 1);
v_a_1633_ = lean_ctor_get(v_x_1610_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v_x_1610_, 1);
v_s_u2081_1612_ = v_a_1632_;
v_s_u2082_1613_ = v_a_1633_;
goto v___jp_1611_;
}
case 2:
{
lean_object* v_a_1634_; lean_object* v_a_1635_; 
v_a_1634_ = lean_ctor_get(v_x_1609_, 0);
lean_inc(v_a_1634_);
lean_dec_ref_known(v_x_1609_, 1);
v_a_1635_ = lean_ctor_get(v_x_1610_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v_x_1610_, 1);
v_s_u2081_1612_ = v_a_1634_;
v_s_u2082_1613_ = v_a_1635_;
goto v___jp_1611_;
}
default: 
{
lean_object* v___x_1636_; 
lean_dec_ref_known(v_x_1609_, 1);
lean_dec(v_x_1610_);
v___x_1636_ = lean_box(1);
return v___x_1636_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1610_) == 0)
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1609_);
return v___x_1637_;
}
else
{
lean_object* v___x_1638_; 
lean_dec(v_x_1610_);
lean_dec(v_x_1609_);
v___x_1638_ = lean_box(1);
return v___x_1638_;
}
}
}
v___jp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = l_List_appendTR___redArg(v_s_u2081_1612_, v_s_u2082_1613_);
v___x_1615_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
return v___x_1615_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
if (lean_obj_tag(v_x_1640_) == 0)
{
return v_x_1639_;
}
else
{
lean_object* v_head_1641_; lean_object* v_tail_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; 
v_head_1641_ = lean_ctor_get(v_x_1640_, 0);
v_tail_1642_ = lean_ctor_get(v_x_1640_, 1);
v___x_1643_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1644_ = lean_string_append(v_x_1639_, v___x_1643_);
v___x_1645_ = lean_string_append(v___x_1644_, v_head_1641_);
v_x_1639_ = v___x_1645_;
v_x_1640_ = v_tail_1642_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1647_, v_x_1648_);
lean_dec(v_x_1648_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1653_){
_start:
{
if (lean_obj_tag(v_x_1653_) == 0)
{
lean_object* v___x_1654_; 
v___x_1654_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1654_;
}
else
{
lean_object* v_tail_1655_; 
v_tail_1655_ = lean_ctor_get(v_x_1653_, 1);
if (lean_obj_tag(v_tail_1655_) == 0)
{
lean_object* v_head_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_head_1656_ = lean_ctor_get(v_x_1653_, 0);
v___x_1657_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1658_ = lean_string_append(v___x_1657_, v_head_1656_);
v___x_1659_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1660_ = lean_string_append(v___x_1658_, v___x_1659_);
return v___x_1660_;
}
else
{
lean_object* v_head_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; uint32_t v___x_1665_; lean_object* v___x_1666_; 
v_head_1661_ = lean_ctor_get(v_x_1653_, 0);
v___x_1662_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1663_ = lean_string_append(v___x_1662_, v_head_1661_);
v___x_1664_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1663_, v_tail_1655_);
v___x_1665_ = 93;
v___x_1666_ = lean_string_push(v___x_1664_, v___x_1665_);
return v___x_1666_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1667_);
lean_dec(v_x_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1672_){
_start:
{
switch(lean_obj_tag(v_x_1672_))
{
case 0:
{
lean_object* v___x_1673_; 
v___x_1673_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1673_;
}
case 1:
{
lean_object* v___x_1674_; 
v___x_1674_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1674_;
}
case 2:
{
lean_object* v_a_1675_; lean_object* v___x_1676_; 
v_a_1675_ = lean_ctor_get(v_x_1672_, 0);
v___x_1676_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1675_);
return v___x_1676_;
}
default: 
{
lean_object* v_a_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v_a_1677_ = lean_ctor_get(v_x_1672_, 0);
v___x_1678_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1679_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1677_);
v___x_1680_ = lean_string_append(v___x_1678_, v___x_1679_);
lean_dec_ref(v___x_1679_);
return v___x_1680_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_Lean_Parser_FirstTokens_toStr(v_x_1681_);
lean_dec(v_x_1681_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v___y_1685_){
_start:
{
lean_inc(v___y_1685_);
return v___y_1685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v___y_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_1686_);
lean_dec(v___y_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v___y_1688_){
_start:
{
lean_inc_ref(v___y_1688_);
return v___y_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_1689_);
lean_dec_ref(v___y_1689_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1704_, lean_object* v_p_1705_){
_start:
{
lean_object* v_info_1706_; lean_object* v_fn_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1715_; 
v_info_1706_ = lean_ctor_get(v_p_1705_, 0);
v_fn_1707_ = lean_ctor_get(v_p_1705_, 1);
v_isSharedCheck_1715_ = !lean_is_exclusive(v_p_1705_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1709_ = v_p_1705_;
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_fn_1707_);
lean_inc(v_info_1706_);
lean_dec(v_p_1705_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1715_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1711_ = lean_apply_1(v_f_1704_, v_fn_1707_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 1, v___x_1711_);
v___x_1713_ = v___x_1709_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_info_1706_);
lean_ctor_set(v_reuseFailAlloc_1714_, 1, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1716_, lean_object* v_p_1717_, lean_object* v_c_1718_, lean_object* v_s_1719_){
_start:
{
lean_object* v_toInputContext_1720_; lean_object* v_toParserModuleContext_1721_; lean_object* v_toCacheableParserContext_1722_; lean_object* v_tokens_1723_; lean_object* v___x_1725_; uint8_t v_isShared_1726_; uint8_t v_isSharedCheck_1732_; 
v_toInputContext_1720_ = lean_ctor_get(v_c_1718_, 0);
v_toParserModuleContext_1721_ = lean_ctor_get(v_c_1718_, 1);
v_toCacheableParserContext_1722_ = lean_ctor_get(v_c_1718_, 2);
v_tokens_1723_ = lean_ctor_get(v_c_1718_, 3);
v_isSharedCheck_1732_ = !lean_is_exclusive(v_c_1718_);
if (v_isSharedCheck_1732_ == 0)
{
v___x_1725_ = v_c_1718_;
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
else
{
lean_inc(v_tokens_1723_);
lean_inc(v_toCacheableParserContext_1722_);
lean_inc(v_toParserModuleContext_1721_);
lean_inc(v_toInputContext_1720_);
lean_dec(v_c_1718_);
v___x_1725_ = lean_box(0);
v_isShared_1726_ = v_isSharedCheck_1732_;
goto v_resetjp_1724_;
}
v_resetjp_1724_:
{
lean_object* v___x_1727_; lean_object* v___x_1729_; 
v___x_1727_ = lean_apply_1(v_f_1716_, v_toCacheableParserContext_1722_);
if (v_isShared_1726_ == 0)
{
lean_ctor_set(v___x_1725_, 2, v___x_1727_);
v___x_1729_ = v___x_1725_;
goto v_reusejp_1728_;
}
else
{
lean_object* v_reuseFailAlloc_1731_; 
v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_toInputContext_1720_);
lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_toParserModuleContext_1721_);
lean_ctor_set(v_reuseFailAlloc_1731_, 2, v___x_1727_);
lean_ctor_set(v_reuseFailAlloc_1731_, 3, v_tokens_1723_);
v___x_1729_ = v_reuseFailAlloc_1731_;
goto v_reusejp_1728_;
}
v_reusejp_1728_:
{
lean_object* v___x_1730_; 
v___x_1730_ = lean_apply_2(v_p_1717_, v___x_1729_, v_s_1719_);
return v___x_1730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1733_, lean_object* v_p_1734_){
_start:
{
lean_object* v_info_1735_; lean_object* v_fn_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1744_; 
v_info_1735_ = lean_ctor_get(v_p_1734_, 0);
v_fn_1736_ = lean_ctor_get(v_p_1734_, 1);
v_isSharedCheck_1744_ = !lean_is_exclusive(v_p_1734_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1738_ = v_p_1734_;
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_fn_1736_);
lean_inc(v_info_1735_);
lean_dec(v_p_1734_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1744_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1740_; lean_object* v___x_1742_; 
v___x_1740_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1740_, 0, v_f_1733_);
lean_closure_set(v___x_1740_, 1, v_fn_1736_);
if (v_isShared_1739_ == 0)
{
lean_ctor_set(v___x_1738_, 1, v___x_1740_);
v___x_1742_ = v___x_1738_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_info_1735_);
lean_ctor_set(v_reuseFailAlloc_1743_, 1, v___x_1740_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1745_, lean_object* v_p_1746_, lean_object* v_c_1747_, lean_object* v_s_1748_){
_start:
{
lean_object* v_stxStack_1749_; lean_object* v_lhsPrec_1750_; lean_object* v_pos_1751_; lean_object* v_cache_1752_; lean_object* v_errorMsg_1753_; lean_object* v_recoveredErrors_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1793_; 
v_stxStack_1749_ = lean_ctor_get(v_s_1748_, 0);
v_lhsPrec_1750_ = lean_ctor_get(v_s_1748_, 1);
v_pos_1751_ = lean_ctor_get(v_s_1748_, 2);
v_cache_1752_ = lean_ctor_get(v_s_1748_, 3);
v_errorMsg_1753_ = lean_ctor_get(v_s_1748_, 4);
v_recoveredErrors_1754_ = lean_ctor_get(v_s_1748_, 5);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_s_1748_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1756_ = v_s_1748_;
v_isShared_1757_ = v_isSharedCheck_1793_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_recoveredErrors_1754_);
lean_inc(v_errorMsg_1753_);
lean_inc(v_cache_1752_);
lean_inc(v_pos_1751_);
lean_inc(v_lhsPrec_1750_);
lean_inc(v_stxStack_1749_);
lean_dec(v_s_1748_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1793_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v_raw_1758_; lean_object* v_drop_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1792_; 
v_raw_1758_ = lean_ctor_get(v_stxStack_1749_, 0);
v_drop_1759_ = lean_ctor_get(v_stxStack_1749_, 1);
v_isSharedCheck_1792_ = !lean_is_exclusive(v_stxStack_1749_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1761_ = v_stxStack_1749_;
v_isShared_1762_ = v_isSharedCheck_1792_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_drop_1759_);
lean_inc(v_raw_1758_);
lean_dec(v_stxStack_1749_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1792_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 1, v_drop_1745_);
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_raw_1758_);
lean_ctor_set(v_reuseFailAlloc_1791_, 1, v_drop_1745_);
v___x_1764_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v___x_1766_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set(v___x_1756_, 0, v___x_1764_);
v___x_1766_ = v___x_1756_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v___x_1764_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_lhsPrec_1750_);
lean_ctor_set(v_reuseFailAlloc_1790_, 2, v_pos_1751_);
lean_ctor_set(v_reuseFailAlloc_1790_, 3, v_cache_1752_);
lean_ctor_set(v_reuseFailAlloc_1790_, 4, v_errorMsg_1753_);
lean_ctor_set(v_reuseFailAlloc_1790_, 5, v_recoveredErrors_1754_);
v___x_1766_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
lean_object* v_s_1767_; lean_object* v_stxStack_1768_; lean_object* v_lhsPrec_1769_; lean_object* v_pos_1770_; lean_object* v_cache_1771_; lean_object* v_errorMsg_1772_; lean_object* v_recoveredErrors_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1789_; 
v_s_1767_ = lean_apply_2(v_p_1746_, v_c_1747_, v___x_1766_);
v_stxStack_1768_ = lean_ctor_get(v_s_1767_, 0);
v_lhsPrec_1769_ = lean_ctor_get(v_s_1767_, 1);
v_pos_1770_ = lean_ctor_get(v_s_1767_, 2);
v_cache_1771_ = lean_ctor_get(v_s_1767_, 3);
v_errorMsg_1772_ = lean_ctor_get(v_s_1767_, 4);
v_recoveredErrors_1773_ = lean_ctor_get(v_s_1767_, 5);
v_isSharedCheck_1789_ = !lean_is_exclusive(v_s_1767_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1775_ = v_s_1767_;
v_isShared_1776_ = v_isSharedCheck_1789_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_recoveredErrors_1773_);
lean_inc(v_errorMsg_1772_);
lean_inc(v_cache_1771_);
lean_inc(v_pos_1770_);
lean_inc(v_lhsPrec_1769_);
lean_inc(v_stxStack_1768_);
lean_dec(v_s_1767_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1789_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_raw_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1787_; 
v_raw_1777_ = lean_ctor_get(v_stxStack_1768_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v_stxStack_1768_);
if (v_isSharedCheck_1787_ == 0)
{
lean_object* v_unused_1788_; 
v_unused_1788_ = lean_ctor_get(v_stxStack_1768_, 1);
lean_dec(v_unused_1788_);
v___x_1779_ = v_stxStack_1768_;
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_raw_1777_);
lean_dec(v_stxStack_1768_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1787_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 1, v_drop_1759_);
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_raw_1777_);
lean_ctor_set(v_reuseFailAlloc_1786_, 1, v_drop_1759_);
v___x_1782_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
lean_object* v___x_1784_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1782_);
v___x_1784_ = v___x_1775_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v___x_1782_);
lean_ctor_set(v_reuseFailAlloc_1785_, 1, v_lhsPrec_1769_);
lean_ctor_set(v_reuseFailAlloc_1785_, 2, v_pos_1770_);
lean_ctor_set(v_reuseFailAlloc_1785_, 3, v_cache_1771_);
lean_ctor_set(v_reuseFailAlloc_1785_, 4, v_errorMsg_1772_);
lean_ctor_set(v_reuseFailAlloc_1785_, 5, v_recoveredErrors_1773_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1794_, lean_object* v_c_1795_, lean_object* v_s_1796_){
_start:
{
lean_object* v_cache_1797_; lean_object* v_stxStack_1798_; lean_object* v_lhsPrec_1799_; lean_object* v_pos_1800_; lean_object* v_errorMsg_1801_; lean_object* v_recoveredErrors_1802_; lean_object* v___x_1804_; uint8_t v_isShared_1805_; uint8_t v_isSharedCheck_1842_; 
v_cache_1797_ = lean_ctor_get(v_s_1796_, 3);
v_stxStack_1798_ = lean_ctor_get(v_s_1796_, 0);
v_lhsPrec_1799_ = lean_ctor_get(v_s_1796_, 1);
v_pos_1800_ = lean_ctor_get(v_s_1796_, 2);
v_errorMsg_1801_ = lean_ctor_get(v_s_1796_, 4);
v_recoveredErrors_1802_ = lean_ctor_get(v_s_1796_, 5);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_s_1796_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1804_ = v_s_1796_;
v_isShared_1805_ = v_isSharedCheck_1842_;
goto v_resetjp_1803_;
}
else
{
lean_inc(v_recoveredErrors_1802_);
lean_inc(v_errorMsg_1801_);
lean_inc(v_cache_1797_);
lean_inc(v_pos_1800_);
lean_inc(v_lhsPrec_1799_);
lean_inc(v_stxStack_1798_);
lean_dec(v_s_1796_);
v___x_1804_ = lean_box(0);
v_isShared_1805_ = v_isSharedCheck_1842_;
goto v_resetjp_1803_;
}
v_resetjp_1803_:
{
lean_object* v_tokenCache_1806_; lean_object* v_parserCache_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1841_; 
v_tokenCache_1806_ = lean_ctor_get(v_cache_1797_, 0);
v_parserCache_1807_ = lean_ctor_get(v_cache_1797_, 1);
v_isSharedCheck_1841_ = !lean_is_exclusive(v_cache_1797_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1809_ = v_cache_1797_;
v_isShared_1810_ = v_isSharedCheck_1841_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_parserCache_1807_);
lean_inc(v_tokenCache_1806_);
lean_dec(v_cache_1797_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1841_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
v___x_1811_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__2, &l_Lean_Parser_initCacheForInput___closed__2_once, _init_l_Lean_Parser_initCacheForInput___closed__2);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 1, v___x_1811_);
v___x_1813_ = v___x_1809_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_tokenCache_1806_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1815_; 
if (v_isShared_1805_ == 0)
{
lean_ctor_set(v___x_1804_, 3, v___x_1813_);
v___x_1815_ = v___x_1804_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_stxStack_1798_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_lhsPrec_1799_);
lean_ctor_set(v_reuseFailAlloc_1839_, 2, v_pos_1800_);
lean_ctor_set(v_reuseFailAlloc_1839_, 3, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1839_, 4, v_errorMsg_1801_);
lean_ctor_set(v_reuseFailAlloc_1839_, 5, v_recoveredErrors_1802_);
v___x_1815_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v_s_x27_1816_; lean_object* v_cache_1817_; lean_object* v_stxStack_1818_; lean_object* v_lhsPrec_1819_; lean_object* v_pos_1820_; lean_object* v_errorMsg_1821_; lean_object* v_recoveredErrors_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1838_; 
v_s_x27_1816_ = lean_apply_2(v_p_1794_, v_c_1795_, v___x_1815_);
v_cache_1817_ = lean_ctor_get(v_s_x27_1816_, 3);
v_stxStack_1818_ = lean_ctor_get(v_s_x27_1816_, 0);
v_lhsPrec_1819_ = lean_ctor_get(v_s_x27_1816_, 1);
v_pos_1820_ = lean_ctor_get(v_s_x27_1816_, 2);
v_errorMsg_1821_ = lean_ctor_get(v_s_x27_1816_, 4);
v_recoveredErrors_1822_ = lean_ctor_get(v_s_x27_1816_, 5);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_s_x27_1816_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1824_ = v_s_x27_1816_;
v_isShared_1825_ = v_isSharedCheck_1838_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_recoveredErrors_1822_);
lean_inc(v_errorMsg_1821_);
lean_inc(v_cache_1817_);
lean_inc(v_pos_1820_);
lean_inc(v_lhsPrec_1819_);
lean_inc(v_stxStack_1818_);
lean_dec(v_s_x27_1816_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1838_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v_tokenCache_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1836_; 
v_tokenCache_1826_ = lean_ctor_get(v_cache_1817_, 0);
v_isSharedCheck_1836_ = !lean_is_exclusive(v_cache_1817_);
if (v_isSharedCheck_1836_ == 0)
{
lean_object* v_unused_1837_; 
v_unused_1837_ = lean_ctor_get(v_cache_1817_, 1);
lean_dec(v_unused_1837_);
v___x_1828_ = v_cache_1817_;
v_isShared_1829_ = v_isSharedCheck_1836_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_tokenCache_1826_);
lean_dec(v_cache_1817_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1836_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1831_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v_parserCache_1807_);
v___x_1831_ = v___x_1828_;
goto v_reusejp_1830_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_tokenCache_1826_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_parserCache_1807_);
v___x_1831_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1830_;
}
v_reusejp_1830_:
{
lean_object* v___x_1833_; 
if (v_isShared_1825_ == 0)
{
lean_ctor_set(v___x_1824_, 3, v___x_1831_);
v___x_1833_ = v___x_1824_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_stxStack_1818_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_lhsPrec_1819_);
lean_ctor_set(v_reuseFailAlloc_1834_, 2, v_pos_1820_);
lean_ctor_set(v_reuseFailAlloc_1834_, 3, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1834_, 4, v_errorMsg_1821_);
lean_ctor_set(v_reuseFailAlloc_1834_, 5, v_recoveredErrors_1822_);
v___x_1833_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
return v___x_1833_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1843_, lean_object* v_a_1844_, lean_object* v_a_1845_){
_start:
{
lean_object* v___f_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___f_1846_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1846_, 0, v_p_1843_);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1847_, v___f_1846_, v_a_1844_, v_a_1845_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1849_){
_start:
{
lean_object* v_info_1850_; lean_object* v_fn_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1859_; 
v_info_1850_ = lean_ctor_get(v_p_1849_, 0);
v_fn_1851_ = lean_ctor_get(v_p_1849_, 1);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_p_1849_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1853_ = v_p_1849_;
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_fn_1851_);
lean_inc(v_info_1850_);
lean_dec(v_p_1849_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1859_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
v___x_1855_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1855_, 0, v_fn_1851_);
if (v_isShared_1854_ == 0)
{
lean_ctor_set(v___x_1853_, 1, v___x_1855_);
v___x_1857_ = v___x_1853_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_info_1850_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1860_, lean_object* v_p_1861_, lean_object* v_c_1862_, lean_object* v_s_1863_){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_apply_1(v_f_1860_, v_c_1862_);
v___x_1865_ = lean_apply_2(v_p_1861_, v___x_1864_, v_s_1863_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1866_, lean_object* v_p_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_){
_start:
{
lean_object* v___f_1870_; lean_object* v___x_1871_; 
v___f_1870_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1870_, 0, v_f_1866_);
lean_closure_set(v___f_1870_, 1, v_p_1867_);
v___x_1871_ = l_Lean_Parser_withResetCacheFn(v___f_1870_, v_a_1868_, v_a_1869_);
return v___x_1871_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1872_, lean_object* v_x_1873_){
_start:
{
if (lean_obj_tag(v_x_1873_) == 0)
{
uint8_t v___x_1874_; 
v___x_1874_ = 0;
return v___x_1874_;
}
else
{
lean_object* v_key_1875_; lean_object* v_tail_1876_; uint8_t v___x_1877_; 
v_key_1875_ = lean_ctor_get(v_x_1873_, 0);
v_tail_1876_ = lean_ctor_get(v_x_1873_, 2);
v___x_1877_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1875_, v_a_1872_);
if (v___x_1877_ == 0)
{
v_x_1873_ = v_tail_1876_;
goto _start;
}
else
{
return v___x_1877_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1879_, lean_object* v_x_1880_){
_start:
{
uint8_t v_res_1881_; lean_object* v_r_1882_; 
v_res_1881_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1879_, v_x_1880_);
lean_dec(v_x_1880_);
lean_dec_ref(v_a_1879_);
v_r_1882_ = lean_box(v_res_1881_);
return v_r_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
if (lean_obj_tag(v_x_1884_) == 0)
{
return v_x_1883_;
}
else
{
lean_object* v_key_1885_; lean_object* v_value_1886_; lean_object* v_tail_1887_; lean_object* v___x_1889_; uint8_t v_isShared_1890_; uint8_t v_isSharedCheck_1917_; 
v_key_1885_ = lean_ctor_get(v_x_1884_, 0);
v_value_1886_ = lean_ctor_get(v_x_1884_, 1);
v_tail_1887_ = lean_ctor_get(v_x_1884_, 2);
v_isSharedCheck_1917_ = !lean_is_exclusive(v_x_1884_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1889_ = v_x_1884_;
v_isShared_1890_ = v_isSharedCheck_1917_;
goto v_resetjp_1888_;
}
else
{
lean_inc(v_tail_1887_);
lean_inc(v_value_1886_);
lean_inc(v_key_1885_);
lean_dec(v_x_1884_);
v___x_1889_ = lean_box(0);
v_isShared_1890_ = v_isSharedCheck_1917_;
goto v_resetjp_1888_;
}
v_resetjp_1888_:
{
lean_object* v_parserName_1891_; lean_object* v_pos_1892_; lean_object* v___x_1893_; uint64_t v___x_1894_; uint64_t v___y_1896_; 
v_parserName_1891_ = lean_ctor_get(v_key_1885_, 1);
v_pos_1892_ = lean_ctor_get(v_key_1885_, 2);
v___x_1893_ = lean_array_get_size(v_x_1883_);
v___x_1894_ = l_String_instHashableRaw_hash(v_pos_1892_);
if (lean_obj_tag(v_parserName_1891_) == 0)
{
uint64_t v___x_1915_; 
v___x_1915_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1896_ = v___x_1915_;
goto v___jp_1895_;
}
else
{
uint64_t v_hash_1916_; 
v_hash_1916_ = lean_ctor_get_uint64(v_parserName_1891_, sizeof(void*)*2);
v___y_1896_ = v_hash_1916_;
goto v___jp_1895_;
}
v___jp_1895_:
{
uint64_t v___x_1897_; uint64_t v___x_1898_; uint64_t v___x_1899_; uint64_t v_fold_1900_; uint64_t v___x_1901_; uint64_t v___x_1902_; uint64_t v___x_1903_; size_t v___x_1904_; size_t v___x_1905_; size_t v___x_1906_; size_t v___x_1907_; size_t v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1897_ = lean_uint64_mix_hash(v___x_1894_, v___y_1896_);
v___x_1898_ = 32ULL;
v___x_1899_ = lean_uint64_shift_right(v___x_1897_, v___x_1898_);
v_fold_1900_ = lean_uint64_xor(v___x_1897_, v___x_1899_);
v___x_1901_ = 16ULL;
v___x_1902_ = lean_uint64_shift_right(v_fold_1900_, v___x_1901_);
v___x_1903_ = lean_uint64_xor(v_fold_1900_, v___x_1902_);
v___x_1904_ = lean_uint64_to_usize(v___x_1903_);
v___x_1905_ = lean_usize_of_nat(v___x_1893_);
v___x_1906_ = ((size_t)1ULL);
v___x_1907_ = lean_usize_sub(v___x_1905_, v___x_1906_);
v___x_1908_ = lean_usize_land(v___x_1904_, v___x_1907_);
v___x_1909_ = lean_array_uget_borrowed(v_x_1883_, v___x_1908_);
lean_inc(v___x_1909_);
if (v_isShared_1890_ == 0)
{
lean_ctor_set(v___x_1889_, 2, v___x_1909_);
v___x_1911_ = v___x_1889_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_key_1885_);
lean_ctor_set(v_reuseFailAlloc_1914_, 1, v_value_1886_);
lean_ctor_set(v_reuseFailAlloc_1914_, 2, v___x_1909_);
v___x_1911_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_array_uset(v_x_1883_, v___x_1908_, v___x_1911_);
v_x_1883_ = v___x_1912_;
v_x_1884_ = v_tail_1887_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1918_, lean_object* v_source_1919_, lean_object* v_target_1920_){
_start:
{
lean_object* v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = lean_array_get_size(v_source_1919_);
v___x_1922_ = lean_nat_dec_lt(v_i_1918_, v___x_1921_);
if (v___x_1922_ == 0)
{
lean_dec_ref(v_source_1919_);
lean_dec(v_i_1918_);
return v_target_1920_;
}
else
{
lean_object* v_es_1923_; lean_object* v___x_1924_; lean_object* v_source_1925_; lean_object* v_target_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_es_1923_ = lean_array_fget(v_source_1919_, v_i_1918_);
v___x_1924_ = lean_box(0);
v_source_1925_ = lean_array_fset(v_source_1919_, v_i_1918_, v___x_1924_);
v_target_1926_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1920_, v_es_1923_);
v___x_1927_ = lean_unsigned_to_nat(1u);
v___x_1928_ = lean_nat_add(v_i_1918_, v___x_1927_);
lean_dec(v_i_1918_);
v_i_1918_ = v___x_1928_;
v_source_1919_ = v_source_1925_;
v_target_1920_ = v_target_1926_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1930_){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v_nbuckets_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1931_ = lean_array_get_size(v_data_1930_);
v___x_1932_ = lean_unsigned_to_nat(2u);
v_nbuckets_1933_ = lean_nat_mul(v___x_1931_, v___x_1932_);
v___x_1934_ = lean_unsigned_to_nat(0u);
v___x_1935_ = lean_box(0);
v___x_1936_ = lean_mk_array(v_nbuckets_1933_, v___x_1935_);
v___x_1937_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1934_, v_data_1930_, v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1938_, lean_object* v_b_1939_, lean_object* v_x_1940_){
_start:
{
if (lean_obj_tag(v_x_1940_) == 0)
{
lean_dec(v_b_1939_);
lean_dec_ref(v_a_1938_);
return v_x_1940_;
}
else
{
lean_object* v_key_1941_; lean_object* v_value_1942_; lean_object* v_tail_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1955_; 
v_key_1941_ = lean_ctor_get(v_x_1940_, 0);
v_value_1942_ = lean_ctor_get(v_x_1940_, 1);
v_tail_1943_ = lean_ctor_get(v_x_1940_, 2);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_x_1940_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1945_ = v_x_1940_;
v_isShared_1946_ = v_isSharedCheck_1955_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_tail_1943_);
lean_inc(v_value_1942_);
lean_inc(v_key_1941_);
lean_dec(v_x_1940_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1955_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
uint8_t v___x_1947_; 
v___x_1947_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1941_, v_a_1938_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1950_; 
v___x_1948_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1938_, v_b_1939_, v_tail_1943_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 2, v___x_1948_);
v___x_1950_ = v___x_1945_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_key_1941_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_value_1942_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v___x_1948_);
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
lean_dec(v_value_1942_);
lean_dec(v_key_1941_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v_b_1939_);
lean_ctor_set(v___x_1945_, 0, v_a_1938_);
v___x_1953_ = v___x_1945_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_a_1938_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_b_1939_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_tail_1943_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1956_, lean_object* v_a_1957_, lean_object* v_b_1958_){
_start:
{
lean_object* v_size_1959_; lean_object* v_buckets_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_2010_; 
v_size_1959_ = lean_ctor_get(v_m_1956_, 0);
v_buckets_1960_ = lean_ctor_get(v_m_1956_, 1);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_m_1956_);
if (v_isSharedCheck_2010_ == 0)
{
v___x_1962_ = v_m_1956_;
v_isShared_1963_ = v_isSharedCheck_2010_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_buckets_1960_);
lean_inc(v_size_1959_);
lean_dec(v_m_1956_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_2010_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v_parserName_1964_; lean_object* v_pos_1965_; lean_object* v___x_1966_; uint64_t v___x_1967_; uint64_t v___y_1969_; 
v_parserName_1964_ = lean_ctor_get(v_a_1957_, 1);
v_pos_1965_ = lean_ctor_get(v_a_1957_, 2);
v___x_1966_ = lean_array_get_size(v_buckets_1960_);
v___x_1967_ = l_String_instHashableRaw_hash(v_pos_1965_);
if (lean_obj_tag(v_parserName_1964_) == 0)
{
uint64_t v___x_2008_; 
v___x_2008_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_1969_ = v___x_2008_;
goto v___jp_1968_;
}
else
{
uint64_t v_hash_2009_; 
v_hash_2009_ = lean_ctor_get_uint64(v_parserName_1964_, sizeof(void*)*2);
v___y_1969_ = v_hash_2009_;
goto v___jp_1968_;
}
v___jp_1968_:
{
uint64_t v___x_1970_; uint64_t v___x_1971_; uint64_t v___x_1972_; uint64_t v_fold_1973_; uint64_t v___x_1974_; uint64_t v___x_1975_; uint64_t v___x_1976_; size_t v___x_1977_; size_t v___x_1978_; size_t v___x_1979_; size_t v___x_1980_; size_t v___x_1981_; lean_object* v_bkt_1982_; uint8_t v___x_1983_; 
v___x_1970_ = lean_uint64_mix_hash(v___x_1967_, v___y_1969_);
v___x_1971_ = 32ULL;
v___x_1972_ = lean_uint64_shift_right(v___x_1970_, v___x_1971_);
v_fold_1973_ = lean_uint64_xor(v___x_1970_, v___x_1972_);
v___x_1974_ = 16ULL;
v___x_1975_ = lean_uint64_shift_right(v_fold_1973_, v___x_1974_);
v___x_1976_ = lean_uint64_xor(v_fold_1973_, v___x_1975_);
v___x_1977_ = lean_uint64_to_usize(v___x_1976_);
v___x_1978_ = lean_usize_of_nat(v___x_1966_);
v___x_1979_ = ((size_t)1ULL);
v___x_1980_ = lean_usize_sub(v___x_1978_, v___x_1979_);
v___x_1981_ = lean_usize_land(v___x_1977_, v___x_1980_);
v_bkt_1982_ = lean_array_uget_borrowed(v_buckets_1960_, v___x_1981_);
v___x_1983_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1957_, v_bkt_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; lean_object* v_size_x27_1985_; lean_object* v___x_1986_; lean_object* v_buckets_x27_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1984_ = lean_unsigned_to_nat(1u);
v_size_x27_1985_ = lean_nat_add(v_size_1959_, v___x_1984_);
lean_dec(v_size_1959_);
lean_inc(v_bkt_1982_);
v___x_1986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1986_, 0, v_a_1957_);
lean_ctor_set(v___x_1986_, 1, v_b_1958_);
lean_ctor_set(v___x_1986_, 2, v_bkt_1982_);
v_buckets_x27_1987_ = lean_array_uset(v_buckets_1960_, v___x_1981_, v___x_1986_);
v___x_1988_ = lean_unsigned_to_nat(4u);
v___x_1989_ = lean_nat_mul(v_size_x27_1985_, v___x_1988_);
v___x_1990_ = lean_unsigned_to_nat(3u);
v___x_1991_ = lean_nat_div(v___x_1989_, v___x_1990_);
lean_dec(v___x_1989_);
v___x_1992_ = lean_array_get_size(v_buckets_x27_1987_);
v___x_1993_ = lean_nat_dec_le(v___x_1991_, v___x_1992_);
lean_dec(v___x_1991_);
if (v___x_1993_ == 0)
{
lean_object* v_val_1994_; lean_object* v___x_1996_; 
v_val_1994_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_1987_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v_val_1994_);
lean_ctor_set(v___x_1962_, 0, v_size_x27_1985_);
v___x_1996_ = v___x_1962_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_size_x27_1985_);
lean_ctor_set(v_reuseFailAlloc_1997_, 1, v_val_1994_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
else
{
lean_object* v___x_1999_; 
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v_buckets_x27_1987_);
lean_ctor_set(v___x_1962_, 0, v_size_x27_1985_);
v___x_1999_ = v___x_1962_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_size_x27_1985_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_buckets_x27_1987_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
else
{
lean_object* v___x_2001_; lean_object* v_buckets_x27_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2006_; 
lean_inc(v_bkt_1982_);
v___x_2001_ = lean_box(0);
v_buckets_x27_2002_ = lean_array_uset(v_buckets_1960_, v___x_1981_, v___x_2001_);
v___x_2003_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1957_, v_b_1958_, v_bkt_1982_);
v___x_2004_ = lean_array_uset(v_buckets_x27_2002_, v___x_1981_, v___x_2003_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v___x_2004_);
v___x_2006_ = v___x_1962_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_size_1959_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___x_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_2011_, lean_object* v_x_2012_){
_start:
{
if (lean_obj_tag(v_x_2012_) == 0)
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_box(0);
return v___x_2013_;
}
else
{
lean_object* v_key_2014_; lean_object* v_value_2015_; lean_object* v_tail_2016_; uint8_t v___x_2017_; 
v_key_2014_ = lean_ctor_get(v_x_2012_, 0);
v_value_2015_ = lean_ctor_get(v_x_2012_, 1);
v_tail_2016_ = lean_ctor_get(v_x_2012_, 2);
v___x_2017_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_2014_, v_a_2011_);
if (v___x_2017_ == 0)
{
v_x_2012_ = v_tail_2016_;
goto _start;
}
else
{
lean_object* v___x_2019_; 
lean_inc(v_value_2015_);
v___x_2019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_value_2015_);
return v___x_2019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_2020_, lean_object* v_x_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2020_, v_x_2021_);
lean_dec(v_x_2021_);
lean_dec_ref(v_a_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_buckets_2025_; lean_object* v_parserName_2026_; lean_object* v_pos_2027_; lean_object* v___x_2028_; uint64_t v___x_2029_; uint64_t v___y_2031_; 
v_buckets_2025_ = lean_ctor_get(v_m_2023_, 1);
v_parserName_2026_ = lean_ctor_get(v_a_2024_, 1);
v_pos_2027_ = lean_ctor_get(v_a_2024_, 2);
v___x_2028_ = lean_array_get_size(v_buckets_2025_);
v___x_2029_ = l_String_instHashableRaw_hash(v_pos_2027_);
if (lean_obj_tag(v_parserName_2026_) == 0)
{
uint64_t v___x_2046_; 
v___x_2046_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___closed__0);
v___y_2031_ = v___x_2046_;
goto v___jp_2030_;
}
else
{
uint64_t v_hash_2047_; 
v_hash_2047_ = lean_ctor_get_uint64(v_parserName_2026_, sizeof(void*)*2);
v___y_2031_ = v_hash_2047_;
goto v___jp_2030_;
}
v___jp_2030_:
{
uint64_t v___x_2032_; uint64_t v___x_2033_; uint64_t v___x_2034_; uint64_t v_fold_2035_; uint64_t v___x_2036_; uint64_t v___x_2037_; uint64_t v___x_2038_; size_t v___x_2039_; size_t v___x_2040_; size_t v___x_2041_; size_t v___x_2042_; size_t v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; 
v___x_2032_ = lean_uint64_mix_hash(v___x_2029_, v___y_2031_);
v___x_2033_ = 32ULL;
v___x_2034_ = lean_uint64_shift_right(v___x_2032_, v___x_2033_);
v_fold_2035_ = lean_uint64_xor(v___x_2032_, v___x_2034_);
v___x_2036_ = 16ULL;
v___x_2037_ = lean_uint64_shift_right(v_fold_2035_, v___x_2036_);
v___x_2038_ = lean_uint64_xor(v_fold_2035_, v___x_2037_);
v___x_2039_ = lean_uint64_to_usize(v___x_2038_);
v___x_2040_ = lean_usize_of_nat(v___x_2028_);
v___x_2041_ = ((size_t)1ULL);
v___x_2042_ = lean_usize_sub(v___x_2040_, v___x_2041_);
v___x_2043_ = lean_usize_land(v___x_2039_, v___x_2042_);
v___x_2044_ = lean_array_uget_borrowed(v_buckets_2025_, v___x_2043_);
v___x_2045_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2024_, v___x_2044_);
return v___x_2045_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_2048_, lean_object* v_a_2049_){
_start:
{
lean_object* v_res_2050_; 
v_res_2050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2048_, v_a_2049_);
lean_dec_ref(v_a_2049_);
lean_dec_ref(v_m_2048_);
return v_res_2050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_2051_, lean_object* v_p_2052_, lean_object* v_c_2053_, lean_object* v_s_2054_){
_start:
{
lean_object* v_cache_2055_; lean_object* v_toCacheableParserContext_2056_; lean_object* v_stxStack_2057_; lean_object* v_pos_2058_; lean_object* v_recoveredErrors_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2108_; 
v_cache_2055_ = lean_ctor_get(v_s_2054_, 3);
lean_inc_ref(v_cache_2055_);
v_toCacheableParserContext_2056_ = lean_ctor_get(v_c_2053_, 2);
v_stxStack_2057_ = lean_ctor_get(v_s_2054_, 0);
v_pos_2058_ = lean_ctor_get(v_s_2054_, 2);
v_recoveredErrors_2059_ = lean_ctor_get(v_s_2054_, 5);
v_isSharedCheck_2108_ = !lean_is_exclusive(v_s_2054_);
if (v_isSharedCheck_2108_ == 0)
{
lean_object* v_unused_2109_; lean_object* v_unused_2110_; lean_object* v_unused_2111_; 
v_unused_2109_ = lean_ctor_get(v_s_2054_, 4);
lean_dec(v_unused_2109_);
v_unused_2110_ = lean_ctor_get(v_s_2054_, 3);
lean_dec(v_unused_2110_);
v_unused_2111_ = lean_ctor_get(v_s_2054_, 1);
lean_dec(v_unused_2111_);
v___x_2061_ = v_s_2054_;
v_isShared_2062_ = v_isSharedCheck_2108_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_recoveredErrors_2059_);
lean_inc(v_pos_2058_);
lean_inc(v_stxStack_2057_);
lean_dec(v_s_2054_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2108_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v_parserCache_2063_; lean_object* v_key_2064_; lean_object* v___x_2065_; 
v_parserCache_2063_ = lean_ctor_get(v_cache_2055_, 1);
lean_inc(v_pos_2058_);
lean_inc_ref(v_toCacheableParserContext_2056_);
v_key_2064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_2064_, 0, v_toCacheableParserContext_2056_);
lean_ctor_set(v_key_2064_, 1, v_parserName_2051_);
lean_ctor_set(v_key_2064_, 2, v_pos_2058_);
v___x_2065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_2063_, v_key_2064_);
if (lean_obj_tag(v___x_2065_) == 1)
{
lean_object* v_val_2066_; lean_object* v_stx_2067_; lean_object* v_lhsPrec_2068_; lean_object* v_newPos_2069_; lean_object* v_errorMsg_2070_; lean_object* v___x_2071_; lean_object* v___x_2073_; 
lean_dec_ref_known(v_key_2064_, 3);
lean_dec(v_pos_2058_);
lean_dec_ref(v_c_2053_);
lean_dec_ref(v_p_2052_);
v_val_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_val_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v_stx_2067_ = lean_ctor_get(v_val_2066_, 0);
lean_inc(v_stx_2067_);
v_lhsPrec_2068_ = lean_ctor_get(v_val_2066_, 1);
lean_inc(v_lhsPrec_2068_);
v_newPos_2069_ = lean_ctor_get(v_val_2066_, 2);
lean_inc(v_newPos_2069_);
v_errorMsg_2070_ = lean_ctor_get(v_val_2066_, 3);
lean_inc(v_errorMsg_2070_);
lean_dec(v_val_2066_);
v___x_2071_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_2057_, v_stx_2067_);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v_errorMsg_2070_);
lean_ctor_set(v___x_2061_, 2, v_newPos_2069_);
lean_ctor_set(v___x_2061_, 1, v_lhsPrec_2068_);
lean_ctor_set(v___x_2061_, 0, v___x_2071_);
v___x_2073_ = v___x_2061_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2074_, 1, v_lhsPrec_2068_);
lean_ctor_set(v_reuseFailAlloc_2074_, 2, v_newPos_2069_);
lean_ctor_set(v_reuseFailAlloc_2074_, 3, v_cache_2055_);
lean_ctor_set(v_reuseFailAlloc_2074_, 4, v_errorMsg_2070_);
lean_ctor_set(v_reuseFailAlloc_2074_, 5, v_recoveredErrors_2059_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
else
{
lean_object* v_raw_2075_; lean_object* v_initStackSz_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2080_; 
lean_dec(v___x_2065_);
v_raw_2075_ = lean_ctor_get(v_stxStack_2057_, 0);
v_initStackSz_2076_ = lean_array_get_size(v_raw_2075_);
v___x_2077_ = lean_unsigned_to_nat(0u);
v___x_2078_ = lean_box(0);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 4, v___x_2078_);
lean_ctor_set(v___x_2061_, 1, v___x_2077_);
v___x_2080_ = v___x_2061_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_stxStack_2057_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2077_);
lean_ctor_set(v_reuseFailAlloc_2107_, 2, v_pos_2058_);
lean_ctor_set(v_reuseFailAlloc_2107_, 3, v_cache_2055_);
lean_ctor_set(v_reuseFailAlloc_2107_, 4, v___x_2078_);
lean_ctor_set(v_reuseFailAlloc_2107_, 5, v_recoveredErrors_2059_);
v___x_2080_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
lean_object* v_s_2081_; lean_object* v_cache_2082_; lean_object* v_stxStack_2083_; lean_object* v_lhsPrec_2084_; lean_object* v_pos_2085_; lean_object* v_errorMsg_2086_; lean_object* v_recoveredErrors_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2106_; 
v_s_2081_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_2076_, v_p_2052_, v_c_2053_, v___x_2080_);
v_cache_2082_ = lean_ctor_get(v_s_2081_, 3);
v_stxStack_2083_ = lean_ctor_get(v_s_2081_, 0);
v_lhsPrec_2084_ = lean_ctor_get(v_s_2081_, 1);
v_pos_2085_ = lean_ctor_get(v_s_2081_, 2);
v_errorMsg_2086_ = lean_ctor_get(v_s_2081_, 4);
v_recoveredErrors_2087_ = lean_ctor_get(v_s_2081_, 5);
v_isSharedCheck_2106_ = !lean_is_exclusive(v_s_2081_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2089_ = v_s_2081_;
v_isShared_2090_ = v_isSharedCheck_2106_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_recoveredErrors_2087_);
lean_inc(v_errorMsg_2086_);
lean_inc(v_cache_2082_);
lean_inc(v_pos_2085_);
lean_inc(v_lhsPrec_2084_);
lean_inc(v_stxStack_2083_);
lean_dec(v_s_2081_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2106_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v_tokenCache_2091_; lean_object* v_parserCache_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2105_; 
v_tokenCache_2091_ = lean_ctor_get(v_cache_2082_, 0);
v_parserCache_2092_ = lean_ctor_get(v_cache_2082_, 1);
v_isSharedCheck_2105_ = !lean_is_exclusive(v_cache_2082_);
if (v_isSharedCheck_2105_ == 0)
{
v___x_2094_ = v_cache_2082_;
v_isShared_2095_ = v_isSharedCheck_2105_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_parserCache_2092_);
lean_inc(v_tokenCache_2091_);
lean_dec(v_cache_2082_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2105_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2100_; 
v___x_2096_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2083_);
lean_inc(v_errorMsg_2086_);
lean_inc(v_pos_2085_);
lean_inc(v_lhsPrec_2084_);
v___x_2097_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2096_);
lean_ctor_set(v___x_2097_, 1, v_lhsPrec_2084_);
lean_ctor_set(v___x_2097_, 2, v_pos_2085_);
lean_ctor_set(v___x_2097_, 3, v_errorMsg_2086_);
v___x_2098_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_2092_, v_key_2064_, v___x_2097_);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 1, v___x_2098_);
v___x_2100_ = v___x_2094_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2104_; 
v_reuseFailAlloc_2104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_tokenCache_2091_);
lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2098_);
v___x_2100_ = v_reuseFailAlloc_2104_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
lean_object* v___x_2102_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 3, v___x_2100_);
v___x_2102_ = v___x_2089_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_stxStack_2083_);
lean_ctor_set(v_reuseFailAlloc_2103_, 1, v_lhsPrec_2084_);
lean_ctor_set(v_reuseFailAlloc_2103_, 2, v_pos_2085_);
lean_ctor_set(v_reuseFailAlloc_2103_, 3, v___x_2100_);
lean_ctor_set(v_reuseFailAlloc_2103_, 4, v_errorMsg_2086_);
lean_ctor_set(v_reuseFailAlloc_2103_, 5, v_recoveredErrors_2087_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2112_, lean_object* v_m_2113_, lean_object* v_a_2114_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2113_, v_a_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2116_, lean_object* v_m_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2116_, v_m_2117_, v_a_2118_);
lean_dec_ref(v_a_2118_);
lean_dec_ref(v_m_2117_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2120_, lean_object* v_m_2121_, lean_object* v_a_2122_, lean_object* v_b_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2121_, v_a_2122_, v_b_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2125_, lean_object* v_a_2126_, lean_object* v_x_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2126_, v_x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2129_, lean_object* v_a_2130_, lean_object* v_x_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2129_, v_a_2130_, v_x_2131_);
lean_dec(v_x_2131_);
lean_dec_ref(v_a_2130_);
return v_res_2132_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2133_, lean_object* v_a_2134_, lean_object* v_x_2135_){
_start:
{
uint8_t v___x_2136_; 
v___x_2136_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2134_, v_x_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2137_, lean_object* v_a_2138_, lean_object* v_x_2139_){
_start:
{
uint8_t v_res_2140_; lean_object* v_r_2141_; 
v_res_2140_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2137_, v_a_2138_, v_x_2139_);
lean_dec(v_x_2139_);
lean_dec_ref(v_a_2138_);
v_r_2141_ = lean_box(v_res_2140_);
return v_r_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2142_, lean_object* v_data_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2145_, lean_object* v_a_2146_, lean_object* v_b_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2146_, v_b_2147_, v_x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2150_, lean_object* v_i_2151_, lean_object* v_source_2152_, lean_object* v_target_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2151_, v_source_2152_, v_target_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_){
_start:
{
lean_object* v___x_2158_; 
v___x_2158_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2156_, v_x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2159_, lean_object* v_p_2160_){
_start:
{
lean_object* v_info_2161_; lean_object* v_fn_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2170_; 
v_info_2161_ = lean_ctor_get(v_p_2160_, 0);
v_fn_2162_ = lean_ctor_get(v_p_2160_, 1);
v_isSharedCheck_2170_ = !lean_is_exclusive(v_p_2160_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2164_ = v_p_2160_;
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_fn_2162_);
lean_inc(v_info_2161_);
lean_dec(v_p_2160_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2170_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v___x_2168_; 
v___x_2166_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2166_, 0, v_parserName_2159_);
lean_closure_set(v___x_2166_, 1, v_fn_2162_);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 1, v___x_2166_);
v___x_2168_ = v___x_2164_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_info_2161_);
lean_ctor_set(v_reuseFailAlloc_2169_, 1, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2178_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2179_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2180_ = l_Lean_addBuiltinDocString(v___x_2178_, v___x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2190_, lean_object* v_ictx_2191_, lean_object* v_pmctx_2192_, lean_object* v_tokens_2193_, lean_object* v_s_2194_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__1));
v___x_2196_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2196_, 0, v_ictx_2191_);
lean_ctor_set(v___x_2196_, 1, v_pmctx_2192_);
lean_ctor_set(v___x_2196_, 2, v___x_2195_);
lean_ctor_set(v___x_2196_, 3, v_tokens_2193_);
v___x_2197_ = lean_apply_2(v_p_2190_, v___x_2196_, v_s_2194_);
return v___x_2197_;
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
