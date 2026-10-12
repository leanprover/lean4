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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
uint64_t l_String_instHashableRaw_hash(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedFileMap_default;
uint8_t l_Array_isEqvAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instBEqOption_beq___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___impl___boxed(lean_object*);
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
uint32_t l_Lean_Parser_getNext(lean_object* v_input_9_, lean_object* v_pos_10_){
_start:
{
lean_object* v___x_11_; uint32_t v___x_12_; 
v___x_11_ = lean_string_utf8_next(v_input_9_, v_pos_10_);
v___x_12_ = lean_string_utf8_get(v_input_9_, v___x_11_);
lean_dec(v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT void l_Lean_Parser_getNext_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_9_ = stack[0].m_obj;
lean_object* v_pos_10_ = stack[1].m_obj;
uint32_t v_res_13_;
v_res_13_ = l_Lean_Parser_getNext(v_input_9_, v_pos_10_);
stack->m_num = v_res_13_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_getNext___boxed(lean_object* v_input_14_, lean_object* v_pos_15_){
_start:
{
uint32_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l_Lean_Parser_getNext(v_input_14_, v_pos_15_);
lean_dec(v_pos_15_);
lean_dec_ref(v_input_14_);
v_r_17_ = lean_box_uint32(v_res_16_);
return v_r_17_;
}
}
static lean_object* _init_l_Lean_Parser_maxPrec(void){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(1024u);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_Parser_argPrec(void){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lean_unsigned_to_nat(1023u);
return v___x_19_;
}
}
static lean_object* _init_l_Lean_Parser_leadPrec(void){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lean_unsigned_to_nat(1022u);
return v___x_20_;
}
}
static lean_object* _init_l_Lean_Parser_minPrec(void){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lean_unsigned_to_nat(10u);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_22_, lean_object* v_x_23_, lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
lean_object* v_ks_26_; lean_object* v_vs_27_; lean_object* v___x_29_; uint8_t v_isShared_30_; uint8_t v_isSharedCheck_51_; 
v_ks_26_ = lean_ctor_get(v_x_22_, 0);
v_vs_27_ = lean_ctor_get(v_x_22_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_x_22_);
if (v_isSharedCheck_51_ == 0)
{
v___x_29_ = v_x_22_;
v_isShared_30_ = v_isSharedCheck_51_;
goto v_resetjp_28_;
}
else
{
lean_inc(v_vs_27_);
lean_inc(v_ks_26_);
lean_dec(v_x_22_);
v___x_29_ = lean_box(0);
v_isShared_30_ = v_isSharedCheck_51_;
goto v_resetjp_28_;
}
v_resetjp_28_:
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = lean_array_get_size(v_ks_26_);
v___x_32_ = lean_nat_dec_lt(v_x_23_, v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_36_; 
lean_dec(v_x_23_);
v___x_33_ = lean_array_push(v_ks_26_, v_x_24_);
v___x_34_ = lean_array_push(v_vs_27_, v_x_25_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v___x_34_);
lean_ctor_set(v___x_29_, 0, v___x_33_);
v___x_36_ = v___x_29_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v___x_33_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v___x_34_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
else
{
lean_object* v_k_x27_38_; uint8_t v___x_39_; 
v_k_x27_38_ = lean_array_fget_borrowed(v_ks_26_, v_x_23_);
v___x_39_ = lean_name_eq(v_x_24_, v_k_x27_38_);
if (v___x_39_ == 0)
{
lean_object* v___x_41_; 
if (v_isShared_30_ == 0)
{
v___x_41_ = v___x_29_;
goto v_reusejp_40_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v_ks_26_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_vs_27_);
v___x_41_ = v_reuseFailAlloc_45_;
goto v_reusejp_40_;
}
v_reusejp_40_:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(1u);
v___x_43_ = lean_nat_add(v_x_23_, v___x_42_);
lean_dec(v_x_23_);
v_x_22_ = v___x_41_;
v_x_23_ = v___x_43_;
goto _start;
}
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_46_ = lean_array_fset(v_ks_26_, v_x_23_, v_x_24_);
v___x_47_ = lean_array_fset(v_vs_27_, v_x_23_, v_x_25_);
lean_dec(v_x_23_);
if (v_isShared_30_ == 0)
{
lean_ctor_set(v___x_29_, 1, v___x_47_);
lean_ctor_set(v___x_29_, 0, v___x_46_);
v___x_49_ = v___x_29_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(lean_object* v_n_52_, lean_object* v_k_53_, lean_object* v_v_54_){
_start:
{
lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_55_ = lean_unsigned_to_nat(0u);
v___x_56_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_52_, v___x_55_, v_k_53_, v_v_54_);
return v___x_56_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_57_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(lean_object* v_x_58_, size_t v_x_59_, size_t v_x_60_, lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
if (lean_obj_tag(v_x_58_) == 0)
{
lean_object* v_es_63_; size_t v___x_64_; size_t v___x_65_; lean_object* v_j_66_; lean_object* v___x_67_; uint8_t v___x_68_; 
v_es_63_ = lean_ctor_get(v_x_58_, 0);
v___x_64_ = ((size_t)31ULL);
v___x_65_ = lean_usize_land(v_x_59_, v___x_64_);
v_j_66_ = lean_usize_to_nat(v___x_65_);
v___x_67_ = lean_array_get_size(v_es_63_);
v___x_68_ = lean_nat_dec_lt(v_j_66_, v___x_67_);
if (v___x_68_ == 0)
{
lean_dec(v_j_66_);
lean_dec(v_x_62_);
lean_dec(v_x_61_);
return v_x_58_;
}
else
{
lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_107_; 
lean_inc_ref(v_es_63_);
v_isSharedCheck_107_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_107_ == 0)
{
lean_object* v_unused_108_; 
v_unused_108_ = lean_ctor_get(v_x_58_, 0);
lean_dec(v_unused_108_);
v___x_70_ = v_x_58_;
v_isShared_71_ = v_isSharedCheck_107_;
goto v_resetjp_69_;
}
else
{
lean_dec(v_x_58_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_107_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
lean_object* v_v_72_; lean_object* v___x_73_; lean_object* v_xs_x27_74_; lean_object* v___y_76_; 
v_v_72_ = lean_array_fget(v_es_63_, v_j_66_);
v___x_73_ = lean_box(0);
v_xs_x27_74_ = lean_array_fset(v_es_63_, v_j_66_, v___x_73_);
switch(lean_obj_tag(v_v_72_))
{
case 0:
{
lean_object* v_key_81_; lean_object* v_val_82_; lean_object* v___x_84_; uint8_t v_isShared_85_; uint8_t v_isSharedCheck_92_; 
v_key_81_ = lean_ctor_get(v_v_72_, 0);
v_val_82_ = lean_ctor_get(v_v_72_, 1);
v_isSharedCheck_92_ = !lean_is_exclusive(v_v_72_);
if (v_isSharedCheck_92_ == 0)
{
v___x_84_ = v_v_72_;
v_isShared_85_ = v_isSharedCheck_92_;
goto v_resetjp_83_;
}
else
{
lean_inc(v_val_82_);
lean_inc(v_key_81_);
lean_dec(v_v_72_);
v___x_84_ = lean_box(0);
v_isShared_85_ = v_isSharedCheck_92_;
goto v_resetjp_83_;
}
v_resetjp_83_:
{
uint8_t v___x_86_; 
v___x_86_ = lean_name_eq(v_x_61_, v_key_81_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; 
lean_del_object(v___x_84_);
v___x_87_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_81_, v_val_82_, v_x_61_, v_x_62_);
v___x_88_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
v___y_76_ = v___x_88_;
goto v___jp_75_;
}
else
{
lean_object* v___x_90_; 
lean_dec(v_val_82_);
lean_dec(v_key_81_);
if (v_isShared_85_ == 0)
{
lean_ctor_set(v___x_84_, 1, v_x_62_);
lean_ctor_set(v___x_84_, 0, v_x_61_);
v___x_90_ = v___x_84_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v_x_61_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_x_62_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
v___y_76_ = v___x_90_;
goto v___jp_75_;
}
}
}
}
case 1:
{
lean_object* v_node_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_105_; 
v_node_93_ = lean_ctor_get(v_v_72_, 0);
v_isSharedCheck_105_ = !lean_is_exclusive(v_v_72_);
if (v_isSharedCheck_105_ == 0)
{
v___x_95_ = v_v_72_;
v_isShared_96_ = v_isSharedCheck_105_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_node_93_);
lean_dec(v_v_72_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_105_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
size_t v___x_97_; size_t v___x_98_; size_t v___x_99_; size_t v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_97_ = ((size_t)5ULL);
v___x_98_ = lean_usize_shift_right(v_x_59_, v___x_97_);
v___x_99_ = ((size_t)1ULL);
v___x_100_ = lean_usize_add(v_x_60_, v___x_99_);
v___x_101_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_node_93_, v___x_98_, v___x_100_, v_x_61_, v_x_62_);
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v___x_101_);
v___x_103_ = v___x_95_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v___x_101_);
v___x_103_ = v_reuseFailAlloc_104_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
v___y_76_ = v___x_103_;
goto v___jp_75_;
}
}
}
default: 
{
lean_object* v___x_106_; 
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_x_61_);
lean_ctor_set(v___x_106_, 1, v_x_62_);
v___y_76_ = v___x_106_;
goto v___jp_75_;
}
}
v___jp_75_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_array_fset(v_xs_x27_74_, v_j_66_, v___y_76_);
lean_dec(v_j_66_);
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 0, v___x_77_);
v___x_79_ = v___x_70_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
}
else
{
lean_object* v_ks_109_; lean_object* v_vs_110_; lean_object* v___x_112_; uint8_t v_isShared_113_; uint8_t v_isSharedCheck_128_; 
v_ks_109_ = lean_ctor_get(v_x_58_, 0);
v_vs_110_ = lean_ctor_get(v_x_58_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v_x_58_);
if (v_isSharedCheck_128_ == 0)
{
v___x_112_ = v_x_58_;
v_isShared_113_ = v_isSharedCheck_128_;
goto v_resetjp_111_;
}
else
{
lean_inc(v_vs_110_);
lean_inc(v_ks_109_);
lean_dec(v_x_58_);
v___x_112_ = lean_box(0);
v_isShared_113_ = v_isSharedCheck_128_;
goto v_resetjp_111_;
}
v_resetjp_111_:
{
lean_object* v___x_115_; 
if (v_isShared_113_ == 0)
{
v___x_115_ = v___x_112_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v_ks_109_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_vs_110_);
v___x_115_ = v_reuseFailAlloc_127_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v_newNode_116_; size_t v___x_117_; uint8_t v___x_118_; 
v_newNode_116_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1___redArg(v___x_115_, v_x_61_, v_x_62_);
v___x_117_ = ((size_t)7ULL);
v___x_118_ = lean_usize_dec_le(v___x_117_, v_x_60_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_119_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_116_);
v___x_120_ = lean_unsigned_to_nat(4u);
v___x_121_ = lean_nat_dec_lt(v___x_119_, v___x_120_);
lean_dec(v___x_119_);
if (v___x_121_ == 0)
{
lean_object* v_ks_122_; lean_object* v_vs_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_ks_122_ = lean_ctor_get(v_newNode_116_, 0);
lean_inc_ref(v_ks_122_);
v_vs_123_ = lean_ctor_get(v_newNode_116_, 1);
lean_inc_ref(v_vs_123_);
lean_dec_ref(v_newNode_116_);
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___closed__0);
v___x_126_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_x_60_, v_ks_122_, v_vs_123_, v___x_124_, v___x_125_);
lean_dec_ref(v_vs_123_);
lean_dec_ref(v_ks_122_);
return v___x_126_;
}
else
{
return v_newNode_116_;
}
}
else
{
return v_newNode_116_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_58_ = stack[0].m_obj;
size_t v_x_59_ = stack[1].m_num;
size_t v_x_60_ = stack[2].m_num;
lean_object* v_x_61_ = stack[3].m_obj;
lean_object* v_x_62_ = stack[4].m_obj;
lean_object* v_res_129_;
v_res_129_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_58_, v_x_59_, v_x_60_, v_x_61_, v_x_62_);
stack->m_obj
 = v_res_129_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(size_t v_depth_130_, lean_object* v_keys_131_, lean_object* v_vals_132_, lean_object* v_i_133_, lean_object* v_entries_134_){
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
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_130_ = stack[0].m_num;
lean_object* v_keys_131_ = stack[1].m_obj;
lean_object* v_vals_132_ = stack[2].m_obj;
lean_object* v_i_133_ = stack[3].m_obj;
lean_object* v_entries_134_ = stack[4].m_obj;
lean_object* v_res_153_;
v_res_153_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_130_, v_keys_131_, v_vals_132_, v_i_133_, v_entries_134_);
stack->m_obj
 = v_res_153_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_154_, lean_object* v_keys_155_, lean_object* v_vals_156_, lean_object* v_i_157_, lean_object* v_entries_158_){
_start:
{
size_t v_depth_boxed_159_; lean_object* v_res_160_; 
v_depth_boxed_159_ = lean_unbox_usize(v_depth_154_);
lean_dec(v_depth_154_);
v_res_160_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_159_, v_keys_155_, v_vals_156_, v_i_157_, v_entries_158_);
lean_dec_ref(v_vals_156_);
lean_dec_ref(v_keys_155_);
return v_res_160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg___boxed(lean_object* v_x_161_, lean_object* v_x_162_, lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_x_165_){
_start:
{
size_t v_x_389__boxed_166_; size_t v_x_390__boxed_167_; lean_object* v_res_168_; 
v_x_389__boxed_166_ = lean_unbox_usize(v_x_162_);
lean_dec(v_x_162_);
v_x_390__boxed_167_ = lean_unbox_usize(v_x_163_);
lean_dec(v_x_163_);
v_res_168_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_161_, v_x_389__boxed_166_, v_x_390__boxed_167_, v_x_164_, v_x_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(lean_object* v_x_169_, lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
uint64_t v___y_173_; 
if (lean_obj_tag(v_x_170_) == 0)
{
uint64_t v___x_177_; 
v___x_177_ = 1723ULL;
v___y_173_ = v___x_177_;
goto v___jp_172_;
}
else
{
uint64_t v_hash_178_; 
v_hash_178_ = lean_ctor_get_uint64(v_x_170_, sizeof(void*)*2);
v___y_173_ = v_hash_178_;
goto v___jp_172_;
}
v___jp_172_:
{
size_t v___x_174_; size_t v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_uint64_to_usize(v___y_173_);
v___x_175_ = ((size_t)1ULL);
v___x_176_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_169_, v___x_174_, v___x_175_, v_x_170_, v_x_171_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxNodeKindSet_insert(lean_object* v_s_179_, lean_object* v_k_180_){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_box(0);
v___x_182_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_s_179_, v_k_180_, v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0(lean_object* v_00_u03b2_183_, lean_object* v_x_184_, lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0___redArg(v_x_184_, v_x_185_, v_x_186_);
return v___x_187_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(lean_object* v_00_u03b2_188_, lean_object* v_x_189_, size_t v_x_190_, size_t v_x_191_, lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___redArg(v_x_189_, v_x_190_, v_x_191_, v_x_192_, v_x_193_);
return v___x_194_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_189_ = stack[1].m_obj;
size_t v_x_190_ = stack[2].m_num;
size_t v_x_191_ = stack[3].m_num;
lean_object* v_x_192_ = stack[4].m_obj;
lean_object* v_x_193_ = stack[5].m_obj;
lean_object* v_res_195_;
v_res_195_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(lean_box(0), v_x_189_, v_x_190_, v_x_191_, v_x_192_, v_x_193_);
stack->m_obj
 = v_res_195_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0___boxed(lean_object* v_00_u03b2_196_, lean_object* v_x_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
size_t v_x_674__boxed_202_; size_t v_x_675__boxed_203_; lean_object* v_res_204_; 
v_x_674__boxed_202_ = lean_unbox_usize(v_x_198_);
lean_dec(v_x_198_);
v_x_675__boxed_203_ = lean_unbox_usize(v_x_199_);
lean_dec(v_x_199_);
v_res_204_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0(v_00_u03b2_196_, v_x_197_, v_x_674__boxed_202_, v_x_675__boxed_203_, v_x_200_, v_x_201_);
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
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_210_, size_t v_depth_211_, lean_object* v_keys_212_, lean_object* v_vals_213_, lean_object* v_heq_214_, lean_object* v_i_215_, lean_object* v_entries_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___redArg(v_depth_211_, v_keys_212_, v_vals_213_, v_i_215_, v_entries_216_);
return v___x_217_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
size_t v_depth_211_ = stack[1].m_num;
lean_object* v_keys_212_ = stack[2].m_obj;
lean_object* v_vals_213_ = stack[3].m_obj;
lean_object* v_i_215_ = stack[5].m_obj;
lean_object* v_entries_216_ = stack[6].m_obj;
lean_object* v_res_218_;
v_res_218_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(lean_box(0), v_depth_211_, v_keys_212_, v_vals_213_, lean_box(0), v_i_215_, v_entries_216_);
stack->m_obj
 = v_res_218_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_219_, lean_object* v_depth_220_, lean_object* v_keys_221_, lean_object* v_vals_222_, lean_object* v_heq_223_, lean_object* v_i_224_, lean_object* v_entries_225_){
_start:
{
size_t v_depth_boxed_226_; lean_object* v_res_227_; 
v_depth_boxed_226_ = lean_unbox_usize(v_depth_220_);
lean_dec(v_depth_220_);
v_res_227_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__2(v_00_u03b2_219_, v_depth_boxed_226_, v_keys_221_, v_vals_222_, v_heq_223_, v_i_224_, v_entries_225_);
lean_dec_ref(v_vals_222_);
lean_dec_ref(v_keys_221_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_228_, lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v_x_232_){
_start:
{
lean_object* v___x_233_; 
v___x_233_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Parser_SyntaxNodeKindSet_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_229_, v_x_230_, v_x_231_, v_x_232_);
return v___x_233_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12(void){
_start:
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__10));
v___x_261_ = l_Lean_mkAtom(v___x_260_);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_262_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__12);
v___x_263_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_264_ = lean_array_push(v___x_263_, v___x_262_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_276_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_277_ = lean_array_push(v___x_276_, v___x_275_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_278_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__17);
v___x_279_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__15));
v___x_280_ = lean_box(2);
v___x_281_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
lean_ctor_set(v___x_281_, 2, v___x_278_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__18);
v___x_283_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__13);
v___x_284_ = lean_array_push(v___x_283_, v___x_282_);
return v___x_284_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20(void){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_286_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__19);
v___x_287_ = lean_array_push(v___x_286_, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_289_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__20);
v___x_290_ = lean_array_push(v___x_289_, v___x_288_);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22(void){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_292_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__21);
v___x_293_ = lean_array_push(v___x_292_, v___x_291_);
return v___x_293_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__16));
v___x_295_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__22);
v___x_296_ = lean_array_push(v___x_295_, v___x_294_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_297_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__23);
v___x_298_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__11));
v___x_299_ = lean_box(2);
v___x_300_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
lean_ctor_set(v___x_300_, 2, v___x_297_);
return v___x_300_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_301_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__24);
v___x_302_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_303_ = lean_array_push(v___x_302_, v___x_301_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_304_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__25);
v___x_305_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__9));
v___x_306_ = lean_box(2);
v___x_307_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_307_, 0, v___x_306_);
lean_ctor_set(v___x_307_, 1, v___x_305_);
lean_ctor_set(v___x_307_, 2, v___x_304_);
return v___x_307_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_308_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__26);
v___x_309_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_310_ = lean_array_push(v___x_309_, v___x_308_);
return v___x_310_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28(void){
_start:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_311_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__27);
v___x_312_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__7));
v___x_313_ = lean_box(2);
v___x_314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_312_);
lean_ctor_set(v___x_314_, 2, v___x_311_);
return v___x_314_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v___x_315_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__28);
v___x_316_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__5));
v___x_317_ = lean_array_push(v___x_316_, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_318_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__29);
v___x_319_ = ((lean_object*)(l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__4));
v___x_320_ = lean_box(2);
v___x_321_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
lean_ctor_set(v___x_321_, 2, v___x_318_);
return v___x_321_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_endPos__valid___autoParam(void){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext___closed__1(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = l_Lean_instInhabitedFileMap_default;
v___x_326_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_326_);
lean_ctor_set(v___x_327_, 2, v___x_325_);
lean_ctor_set(v___x_327_, 3, v___x_324_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Lean_Parser_instInhabitedInputContext___closed__1, &l_Lean_Parser_instInhabitedInputContext___closed__1_once, _init_l_Lean_Parser_instInhabitedInputContext___closed__1);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_mk___auto__1(void){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk___redArg(lean_object* v_input_330_, lean_object* v_fileName_331_, lean_object* v_endPos_332_, lean_object* v_fileMap_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_334_, 0, v_input_330_);
lean_ctor_set(v___x_334_, 1, v_fileName_331_);
lean_ctor_set(v___x_334_, 2, v_fileMap_333_);
lean_ctor_set(v___x_334_, 3, v_endPos_332_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk(lean_object* v_input_335_, lean_object* v_fileName_336_, lean_object* v_endPos_337_, lean_object* v_endPos__valid_338_, lean_object* v_fileMap_339_){
_start:
{
lean_object* v___x_340_; 
v___x_340_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_340_, 0, v_input_335_);
lean_ctor_set(v___x_340_, 1, v_fileName_336_);
lean_ctor_set(v___x_340_, 2, v_fileMap_339_);
lean_ctor_set(v___x_340_, 3, v_endPos_337_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input(lean_object* v_c_341_){
_start:
{
lean_object* v_inputString_342_; lean_object* v_endPos_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v_inputString_342_ = lean_ctor_get(v_c_341_, 0);
v_endPos_343_ = lean_ctor_get(v_c_341_, 3);
v___x_344_ = lean_unsigned_to_nat(0u);
v___x_345_ = lean_string_utf8_extract(v_inputString_342_, v___x_344_, v_endPos_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input___boxed(lean_object* v_c_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_Parser_InputContext_input(v_c_346_);
lean_dec_ref(v_c_346_);
return v_res_347_;
}
}
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object* v_c_348_, lean_object* v_p_349_){
_start:
{
lean_object* v_endPos_350_; uint8_t v___x_351_; 
v_endPos_350_ = lean_ctor_get(v_c_348_, 3);
v___x_351_ = lean_nat_dec_le(v_endPos_350_, v_p_349_);
return v___x_351_;
}
}
LEAN_EXPORT void l_Lean_Parser_InputContext_atEnd_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_348_ = stack[0].m_obj;
lean_object* v_p_349_ = stack[1].m_obj;
uint8_t v_res_352_;
v_res_352_ = l_Lean_Parser_InputContext_atEnd(v_c_348_, v_p_349_);
stack->m_num = v_res_352_;
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
uint32_t l_Lean_Parser_InputContext_get(lean_object* v_c_357_, lean_object* v_p_358_){
_start:
{
lean_object* v_inputString_359_; uint32_t v___x_360_; 
v_inputString_359_ = lean_ctor_get(v_c_357_, 0);
v___x_360_ = lean_string_utf8_get(v_inputString_359_, v_p_358_);
return v___x_360_;
}
}
LEAN_EXPORT void l_Lean_Parser_InputContext_get_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_357_ = stack[0].m_obj;
lean_object* v_p_358_ = stack[1].m_obj;
uint32_t v_res_361_;
v_res_361_ = l_Lean_Parser_InputContext_get(v_c_357_, v_p_358_);
stack->m_num = v_res_361_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get___boxed(lean_object* v_c_362_, lean_object* v_p_363_){
_start:
{
uint32_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Lean_Parser_InputContext_get(v_c_362_, v_p_363_);
lean_dec(v_p_363_);
lean_dec_ref(v_c_362_);
v_r_365_ = lean_box_uint32(v_res_364_);
return v_r_365_;
}
}
uint32_t l_Lean_Parser_InputContext_get_x27___redArg(lean_object* v_c_366_, lean_object* v_p_367_){
_start:
{
lean_object* v_inputString_368_; uint32_t v___x_369_; 
v_inputString_368_ = lean_ctor_get(v_c_366_, 0);
v___x_369_ = lean_string_utf8_get_fast(v_inputString_368_, v_p_367_);
return v___x_369_;
}
}
LEAN_EXPORT void l_Lean_Parser_InputContext_get_x27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_366_ = stack[0].m_obj;
lean_object* v_p_367_ = stack[1].m_obj;
uint32_t v_res_370_;
v_res_370_ = l_Lean_Parser_InputContext_get_x27___redArg(v_c_366_, v_p_367_);
stack->m_num = v_res_370_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___redArg___boxed(lean_object* v_c_371_, lean_object* v_p_372_){
_start:
{
uint32_t v_res_373_; lean_object* v_r_374_; 
v_res_373_ = l_Lean_Parser_InputContext_get_x27___redArg(v_c_371_, v_p_372_);
lean_dec(v_p_372_);
lean_dec_ref(v_c_371_);
v_r_374_ = lean_box_uint32(v_res_373_);
return v_r_374_;
}
}
uint32_t l_Lean_Parser_InputContext_get_x27(lean_object* v_c_375_, lean_object* v_p_376_, lean_object* v_h_377_){
_start:
{
lean_object* v_inputString_378_; uint32_t v___x_379_; 
v_inputString_378_ = lean_ctor_get(v_c_375_, 0);
v___x_379_ = lean_string_utf8_get_fast(v_inputString_378_, v_p_376_);
return v___x_379_;
}
}
LEAN_EXPORT void l_Lean_Parser_InputContext_get_x27_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_375_ = stack[0].m_obj;
lean_object* v_p_376_ = stack[1].m_obj;
uint32_t v_res_380_;
v_res_380_ = l_Lean_Parser_InputContext_get_x27(v_c_375_, v_p_376_, lean_box(0));
stack->m_num = v_res_380_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___boxed(lean_object* v_c_381_, lean_object* v_p_382_, lean_object* v_h_383_){
_start:
{
uint32_t v_res_384_; lean_object* v_r_385_; 
v_res_384_ = l_Lean_Parser_InputContext_get_x27(v_c_381_, v_p_382_, v_h_383_);
lean_dec(v_p_382_);
lean_dec_ref(v_c_381_);
v_r_385_ = lean_box_uint32(v_res_384_);
return v_r_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next(lean_object* v_c_386_, lean_object* v_p_387_){
_start:
{
lean_object* v_inputString_388_; lean_object* v___x_389_; 
v_inputString_388_ = lean_ctor_get(v_c_386_, 0);
v___x_389_ = lean_string_utf8_next(v_inputString_388_, v_p_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next___boxed(lean_object* v_c_390_, lean_object* v_p_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Parser_InputContext_next(v_c_390_, v_p_391_);
lean_dec(v_p_391_);
lean_dec_ref(v_c_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg(lean_object* v_c_393_, lean_object* v_p_394_){
_start:
{
lean_object* v_inputString_395_; lean_object* v___x_396_; 
v_inputString_395_ = lean_ctor_get(v_c_393_, 0);
v___x_396_ = lean_string_utf8_next_fast(v_inputString_395_, v_p_394_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg___boxed(lean_object* v_c_397_, lean_object* v_p_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Parser_InputContext_next_x27___redArg(v_c_397_, v_p_398_);
lean_dec(v_p_398_);
lean_dec_ref(v_c_397_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27(lean_object* v_c_400_, lean_object* v_p_401_, lean_object* v_h_402_){
_start:
{
lean_object* v_inputString_403_; lean_object* v___x_404_; 
v_inputString_403_ = lean_ctor_get(v_c_400_, 0);
v___x_404_ = lean_string_utf8_next_fast(v_inputString_403_, v_p_401_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___boxed(lean_object* v_c_405_, lean_object* v_p_406_, lean_object* v_h_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Parser_InputContext_next_x27(v_c_405_, v_p_406_, v_h_407_);
lean_dec(v_p_406_);
lean_dec_ref(v_c_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract(lean_object* v_c_409_, lean_object* v_a_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_inputString_412_; lean_object* v___x_413_; 
v_inputString_412_ = lean_ctor_get(v_c_409_, 0);
v___x_413_ = lean_string_utf8_extract(v_inputString_412_, v_a_410_, v_a_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract___boxed(lean_object* v_c_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_Parser_InputContext_extract(v_c_414_, v_a_415_, v_a_416_);
lean_dec(v_a_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_c_414_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring(lean_object* v_c_418_, lean_object* v_startPos_419_, lean_object* v_stopPos_420_){
_start:
{
lean_object* v_inputString_421_; lean_object* v_endPos_422_; uint8_t v___x_423_; 
v_inputString_421_ = lean_ctor_get(v_c_418_, 0);
v_endPos_422_ = lean_ctor_get(v_c_418_, 3);
v___x_423_ = lean_nat_dec_le(v_stopPos_420_, v_endPos_422_);
if (v___x_423_ == 0)
{
lean_object* v___x_424_; 
lean_dec(v_stopPos_420_);
lean_inc(v_endPos_422_);
lean_inc_ref(v_inputString_421_);
v___x_424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_424_, 0, v_inputString_421_);
lean_ctor_set(v___x_424_, 1, v_startPos_419_);
lean_ctor_set(v___x_424_, 2, v_endPos_422_);
return v___x_424_;
}
else
{
lean_object* v___x_425_; 
lean_inc_ref(v_inputString_421_);
v___x_425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_425_, 0, v_inputString_421_);
lean_ctor_set(v___x_425_, 1, v_startPos_419_);
lean_ctor_set(v___x_425_, 2, v_stopPos_420_);
return v___x_425_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring___boxed(lean_object* v_c_426_, lean_object* v_startPos_427_, lean_object* v_stopPos_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_Parser_InputContext_substring(v_c_426_, v_startPos_427_, v_stopPos_428_);
lean_dec_ref(v_c_426_);
return v_res_429_;
}
}
uint32_t l_Lean_Parser_InputContext_getNext(lean_object* v_input_430_, lean_object* v_pos_431_){
_start:
{
lean_object* v_inputString_432_; lean_object* v___x_433_; uint32_t v___x_434_; 
v_inputString_432_ = lean_ctor_get(v_input_430_, 0);
v___x_433_ = lean_string_utf8_next(v_inputString_432_, v_pos_431_);
v___x_434_ = lean_string_utf8_get(v_inputString_432_, v___x_433_);
lean_dec(v___x_433_);
return v___x_434_;
}
}
LEAN_EXPORT void l_Lean_Parser_InputContext_getNext_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_430_ = stack[0].m_obj;
lean_object* v_pos_431_ = stack[1].m_obj;
uint32_t v_res_435_;
v_res_435_ = l_Lean_Parser_InputContext_getNext(v_input_430_, v_pos_431_);
stack->m_num = v_res_435_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_getNext___boxed(lean_object* v_input_436_, lean_object* v_pos_437_){
_start:
{
uint32_t v_res_438_; lean_object* v_r_439_; 
v_res_438_ = l_Lean_Parser_InputContext_getNext(v_input_436_, v_pos_437_);
lean_dec(v_pos_437_);
lean_dec_ref(v_input_436_);
v_r_439_ = lean_box_uint32(v_res_438_);
return v_r_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev(lean_object* v_c_440_, lean_object* v_pos_441_){
_start:
{
lean_object* v_inputString_442_; lean_object* v___x_443_; 
v_inputString_442_ = lean_ctor_get(v_c_440_, 0);
v___x_443_ = lean_string_utf8_prev(v_inputString_442_, v_pos_441_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev___boxed(lean_object* v_c_444_, lean_object* v_pos_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Parser_InputContext_prev(v_c_444_, v_pos_445_);
lean_dec(v_pos_445_);
lean_dec_ref(v_c_444_);
return v_res_446_;
}
}
uint8_t l_Lean_Parser_instBEqCacheableParserContext_unsafe__2(lean_object* v_a_448_, lean_object* v_b_449_){
_start:
{
lean_object* v_forbiddenTks_450_; lean_object* v_forbiddenTks_451_; size_t v___x_452_; size_t v___x_453_; uint8_t v___x_454_; 
v_forbiddenTks_450_ = lean_ctor_get(v_a_448_, 3);
v_forbiddenTks_451_ = lean_ctor_get(v_b_449_, 3);
v___x_452_ = lean_ptr_addr(v_forbiddenTks_450_);
v___x_453_ = lean_ptr_addr(v_forbiddenTks_451_);
v___x_454_ = lean_usize_dec_eq(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_455_ = lean_array_get_size(v_forbiddenTks_450_);
v___x_456_ = lean_array_get_size(v_forbiddenTks_451_);
v___x_457_ = lean_nat_dec_eq(v___x_455_, v___x_456_);
if (v___x_457_ == 0)
{
return v___x_457_;
}
else
{
lean_object* v___f_458_; uint8_t v___x_459_; 
v___f_458_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0));
v___x_459_ = l_Array_isEqvAux___redArg(v_forbiddenTks_450_, v_forbiddenTks_451_, v___f_458_, v___x_455_);
return v___x_459_;
}
}
else
{
return v___x_454_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_instBEqCacheableParserContext_unsafe__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_448_ = stack[0].m_obj;
lean_object* v_b_449_ = stack[1].m_obj;
uint8_t v_res_460_;
v_res_460_ = l_Lean_Parser_instBEqCacheableParserContext_unsafe__2(v_a_448_, v_b_449_);
stack->m_num = v_res_460_;
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
uint8_t l_Lean_Parser_instBEqCacheableParserContext___lam__0(lean_object* v___f_467_, lean_object* v_a_468_, lean_object* v_b_469_){
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
v___x_482_ = l_instBEqOption_beq___redArg(v___f_481_, v_savedPos_x3f_473_, v_savedPos_x3f_478_);
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
LEAN_EXPORT void l_Lean_Parser_instBEqCacheableParserContext___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_467_ = stack[0].m_obj;
lean_object* v_a_468_ = stack[1].m_obj;
lean_object* v_b_469_ = stack[2].m_obj;
uint8_t v_res_492_;
v_res_492_ = l_Lean_Parser_instBEqCacheableParserContext___lam__0(v___f_467_, v_a_468_, v_b_469_);
stack->m_num = v_res_492_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed(lean_object* v___f_493_, lean_object* v_a_494_, lean_object* v_b_495_){
_start:
{
uint8_t v_res_496_; lean_object* v_r_497_; 
v_res_496_ = l_Lean_Parser_instBEqCacheableParserContext___lam__0(v___f_493_, v_a_494_, v_b_495_);
v_r_497_ = lean_box(v_res_496_);
return v_r_497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0(lean_object* v_x_501_){
_start:
{
lean_object* v_toInputContext_502_; 
v_toInputContext_502_ = lean_ctor_get(v_x_501_, 0);
lean_inc_ref(v_toInputContext_502_);
return v_toInputContext_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(lean_object* v_x_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_503_);
lean_dec_ref(v_x_503_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos___redArg(lean_object* v_c_507_, lean_object* v_endPos_508_){
_start:
{
lean_object* v_toInputContext_509_; lean_object* v_toParserModuleContext_510_; lean_object* v_toCacheableParserContext_511_; lean_object* v_tokens_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_530_; 
v_toInputContext_509_ = lean_ctor_get(v_c_507_, 0);
v_toParserModuleContext_510_ = lean_ctor_get(v_c_507_, 1);
v_toCacheableParserContext_511_ = lean_ctor_get(v_c_507_, 2);
v_tokens_512_ = lean_ctor_get(v_c_507_, 3);
v_isSharedCheck_530_ = !lean_is_exclusive(v_c_507_);
if (v_isSharedCheck_530_ == 0)
{
v___x_514_ = v_c_507_;
v_isShared_515_ = v_isSharedCheck_530_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_tokens_512_);
lean_inc(v_toCacheableParserContext_511_);
lean_inc(v_toParserModuleContext_510_);
lean_inc(v_toInputContext_509_);
lean_dec(v_c_507_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_530_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v_inputString_516_; lean_object* v_fileName_517_; lean_object* v_fileMap_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_528_; 
v_inputString_516_ = lean_ctor_get(v_toInputContext_509_, 0);
v_fileName_517_ = lean_ctor_get(v_toInputContext_509_, 1);
v_fileMap_518_ = lean_ctor_get(v_toInputContext_509_, 2);
v_isSharedCheck_528_ = !lean_is_exclusive(v_toInputContext_509_);
if (v_isSharedCheck_528_ == 0)
{
lean_object* v_unused_529_; 
v_unused_529_ = lean_ctor_get(v_toInputContext_509_, 3);
lean_dec(v_unused_529_);
v___x_520_ = v_toInputContext_509_;
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_fileMap_518_);
lean_inc(v_fileName_517_);
lean_inc(v_inputString_516_);
lean_dec(v_toInputContext_509_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_528_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
lean_object* v___x_523_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 3, v_endPos_508_);
v___x_523_ = v___x_520_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v_inputString_516_);
lean_ctor_set(v_reuseFailAlloc_527_, 1, v_fileName_517_);
lean_ctor_set(v_reuseFailAlloc_527_, 2, v_fileMap_518_);
lean_ctor_set(v_reuseFailAlloc_527_, 3, v_endPos_508_);
v___x_523_ = v_reuseFailAlloc_527_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
lean_object* v___x_525_; 
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_523_);
v___x_525_ = v___x_514_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
lean_ctor_set(v_reuseFailAlloc_526_, 1, v_toParserModuleContext_510_);
lean_ctor_set(v_reuseFailAlloc_526_, 2, v_toCacheableParserContext_511_);
lean_ctor_set(v_reuseFailAlloc_526_, 3, v_tokens_512_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos(lean_object* v_c_531_, lean_object* v_endPos_532_, lean_object* v_endPos__valid_533_){
_start:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_531_, v_endPos_532_);
return v___x_534_;
}
}
uint8_t l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
if (lean_obj_tag(v_x_541_) == 0)
{
if (lean_obj_tag(v_x_542_) == 0)
{
uint8_t v___x_543_; 
v___x_543_ = 1;
return v___x_543_;
}
else
{
uint8_t v___x_544_; 
v___x_544_ = 0;
return v___x_544_;
}
}
else
{
if (lean_obj_tag(v_x_542_) == 0)
{
uint8_t v___x_545_; 
v___x_545_ = 0;
return v___x_545_;
}
else
{
lean_object* v_head_546_; lean_object* v_tail_547_; lean_object* v_head_548_; lean_object* v_tail_549_; uint8_t v___x_550_; 
v_head_546_ = lean_ctor_get(v_x_541_, 0);
v_tail_547_ = lean_ctor_get(v_x_541_, 1);
v_head_548_ = lean_ctor_get(v_x_542_, 0);
v_tail_549_ = lean_ctor_get(v_x_542_, 1);
v___x_550_ = lean_string_dec_eq(v_head_546_, v_head_548_);
if (v___x_550_ == 0)
{
return v___x_550_;
}
else
{
v_x_541_ = v_tail_547_;
v_x_542_ = v_tail_549_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_541_ = stack[0].m_obj;
lean_object* v_x_542_ = stack[1].m_obj;
uint8_t v_res_552_;
v_res_552_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_541_, v_x_542_);
stack->m_num = v_res_552_;
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
uint8_t v_res_555_; lean_object* v_r_556_; 
v_res_555_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_553_, v_x_554_);
lean_dec(v_x_554_);
lean_dec(v_x_553_);
v_r_556_ = lean_box(v_res_555_);
return v_r_556_;
}
}
uint8_t l_Lean_Parser_instBEqError_beq(lean_object* v_x_557_, lean_object* v_x_558_){
_start:
{
lean_object* v_unexpectedTk_559_; lean_object* v_unexpected_560_; lean_object* v_expected_561_; lean_object* v_unexpectedTk_562_; lean_object* v_unexpected_563_; lean_object* v_expected_564_; uint8_t v___x_565_; 
v_unexpectedTk_559_ = lean_ctor_get(v_x_557_, 0);
v_unexpected_560_ = lean_ctor_get(v_x_557_, 1);
v_expected_561_ = lean_ctor_get(v_x_557_, 2);
v_unexpectedTk_562_ = lean_ctor_get(v_x_558_, 0);
v_unexpected_563_ = lean_ctor_get(v_x_558_, 1);
v_expected_564_ = lean_ctor_get(v_x_558_, 2);
v___x_565_ = l_Lean_Syntax_structEq(v_unexpectedTk_559_, v_unexpectedTk_562_);
if (v___x_565_ == 0)
{
return v___x_565_;
}
else
{
uint8_t v___x_566_; 
v___x_566_ = lean_string_dec_eq(v_unexpected_560_, v_unexpected_563_);
if (v___x_566_ == 0)
{
return v___x_566_;
}
else
{
uint8_t v___x_567_; 
v___x_567_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_561_, v_expected_564_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_instBEqError_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_557_ = stack[0].m_obj;
lean_object* v_x_558_ = stack[1].m_obj;
uint8_t v_res_568_;
v_res_568_ = l_Lean_Parser_instBEqError_beq(v_x_557_, v_x_558_);
stack->m_num = v_res_568_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object* v_x_569_, lean_object* v_x_570_){
_start:
{
uint8_t v_res_571_; lean_object* v_r_572_; 
v_res_571_ = l_Lean_Parser_instBEqError_beq(v_x_569_, v_x_570_);
lean_dec_ref(v_x_570_);
lean_dec_ref(v_x_569_);
v_r_572_ = lean_box(v_res_571_);
return v_r_572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* v_x_577_){
_start:
{
if (lean_obj_tag(v_x_577_) == 0)
{
lean_object* v___x_578_; 
v___x_578_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
return v___x_578_;
}
else
{
lean_object* v_tail_579_; 
v_tail_579_ = lean_ctor_get(v_x_577_, 1);
if (lean_obj_tag(v_tail_579_) == 0)
{
lean_object* v_head_580_; 
v_head_580_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_head_580_);
lean_dec_ref_known(v_x_577_, 2);
return v_head_580_;
}
else
{
lean_object* v_tail_581_; 
lean_inc_ref(v_tail_579_);
v_tail_581_ = lean_ctor_get(v_tail_579_, 1);
if (lean_obj_tag(v_tail_581_) == 0)
{
lean_object* v_head_582_; lean_object* v_head_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_head_582_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_head_582_);
lean_dec_ref_known(v_x_577_, 2);
v_head_583_ = lean_ctor_get(v_tail_579_, 0);
lean_inc(v_head_583_);
lean_dec_ref_known(v_tail_579_, 2);
v___x_584_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0));
v___x_585_ = lean_string_append(v_head_582_, v___x_584_);
v___x_586_ = lean_string_append(v___x_585_, v_head_583_);
lean_dec(v_head_583_);
return v___x_586_;
}
else
{
lean_object* v_head_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_head_587_ = lean_ctor_get(v_x_577_, 0);
lean_inc(v_head_587_);
lean_dec_ref_known(v_x_577_, 2);
v___x_588_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_589_ = lean_string_append(v_head_587_, v___x_588_);
v___x_590_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_tail_579_);
v___x_591_ = lean_string_append(v___x_589_, v___x_590_);
lean_dec_ref(v___x_590_);
return v___x_591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object* v_as_592_){
_start:
{
lean_object* v___f_593_; lean_object* v___x_594_; 
v___f_593_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0));
v___x_594_ = l_List_eraseRepsBy___redArg(v___f_593_, v_as_592_);
return v___x_594_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object* v_hi_595_, lean_object* v_pivot_596_, lean_object* v_as_597_, lean_object* v_i_598_, lean_object* v_k_599_){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = lean_nat_dec_lt(v_k_599_, v_hi_595_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; lean_object* v___x_602_; 
lean_dec(v_k_599_);
v___x_601_ = lean_array_fswap(v_as_597_, v_i_598_, v_hi_595_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v_i_598_);
lean_ctor_set(v___x_602_, 1, v___x_601_);
return v___x_602_;
}
else
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_array_fget_borrowed(v_as_597_, v_k_599_);
v___x_604_ = lean_string_dec_lt(v___x_603_, v_pivot_596_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = lean_nat_add(v_k_599_, v___x_605_);
lean_dec(v_k_599_);
v_k_599_ = v___x_606_;
goto _start;
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_608_ = lean_array_fswap(v_as_597_, v_i_598_, v_k_599_);
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_i_598_, v___x_609_);
lean_dec(v_i_598_);
v___x_611_ = lean_nat_add(v_k_599_, v___x_609_);
lean_dec(v_k_599_);
v_as_597_ = v___x_608_;
v_i_598_ = v___x_610_;
v_k_599_ = v___x_611_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object* v_hi_613_, lean_object* v_pivot_614_, lean_object* v_as_615_, lean_object* v_i_616_, lean_object* v_k_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_613_, v_pivot_614_, v_as_615_, v_i_616_, v_k_617_);
lean_dec_ref(v_pivot_614_);
lean_dec(v_hi_613_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_n_619_, lean_object* v_as_620_, lean_object* v_lo_621_, lean_object* v_hi_622_){
_start:
{
lean_object* v___y_624_; uint8_t v___x_634_; 
v___x_634_ = lean_nat_dec_lt(v_lo_621_, v_hi_622_);
if (v___x_634_ == 0)
{
lean_dec(v_lo_621_);
return v_as_620_;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v_mid_637_; lean_object* v___y_639_; lean_object* v___y_645_; lean_object* v___x_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v___x_635_ = lean_nat_add(v_lo_621_, v_hi_622_);
v___x_636_ = lean_unsigned_to_nat(1u);
v_mid_637_ = lean_nat_shiftr(v___x_635_, v___x_636_);
lean_dec(v___x_635_);
v___x_650_ = lean_array_fget_borrowed(v_as_620_, v_mid_637_);
v___x_651_ = lean_array_fget_borrowed(v_as_620_, v_lo_621_);
v___x_652_ = lean_string_dec_lt(v___x_650_, v___x_651_);
if (v___x_652_ == 0)
{
v___y_645_ = v_as_620_;
goto v___jp_644_;
}
else
{
lean_object* v___x_653_; 
v___x_653_ = lean_array_fswap(v_as_620_, v_lo_621_, v_mid_637_);
v___y_645_ = v___x_653_;
goto v___jp_644_;
}
v___jp_638_:
{
lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_640_ = lean_array_fget_borrowed(v___y_639_, v_mid_637_);
v___x_641_ = lean_array_fget_borrowed(v___y_639_, v_hi_622_);
v___x_642_ = lean_string_dec_lt(v___x_640_, v___x_641_);
if (v___x_642_ == 0)
{
lean_dec(v_mid_637_);
v___y_624_ = v___y_639_;
goto v___jp_623_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = lean_array_fswap(v___y_639_, v_mid_637_, v_hi_622_);
lean_dec(v_mid_637_);
v___y_624_ = v___x_643_;
goto v___jp_623_;
}
}
v___jp_644_:
{
lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_646_ = lean_array_fget_borrowed(v___y_645_, v_hi_622_);
v___x_647_ = lean_array_fget_borrowed(v___y_645_, v_lo_621_);
v___x_648_ = lean_string_dec_lt(v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
v___y_639_ = v___y_645_;
goto v___jp_638_;
}
else
{
lean_object* v___x_649_; 
v___x_649_ = lean_array_fswap(v___y_645_, v_lo_621_, v_hi_622_);
v___y_639_ = v___x_649_;
goto v___jp_638_;
}
}
}
v___jp_623_:
{
lean_object* v_pivot_625_; lean_object* v___x_626_; lean_object* v_fst_627_; lean_object* v_snd_628_; uint8_t v___x_629_; 
v_pivot_625_ = lean_array_fget(v___y_624_, v_hi_622_);
lean_inc_n(v_lo_621_, 2);
v___x_626_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_622_, v_pivot_625_, v___y_624_, v_lo_621_, v_lo_621_);
lean_dec(v_pivot_625_);
v_fst_627_ = lean_ctor_get(v___x_626_, 0);
lean_inc(v_fst_627_);
v_snd_628_ = lean_ctor_get(v___x_626_, 1);
lean_inc(v_snd_628_);
lean_dec_ref(v___x_626_);
v___x_629_ = lean_nat_dec_le(v_hi_622_, v_fst_627_);
if (v___x_629_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_619_, v_snd_628_, v_lo_621_, v_fst_627_);
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v_fst_627_, v___x_631_);
lean_dec(v_fst_627_);
v_as_620_ = v___x_630_;
v_lo_621_ = v___x_632_;
goto _start;
}
else
{
lean_dec(v_fst_627_);
lean_dec(v_lo_621_);
return v_snd_628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_n_654_, lean_object* v_as_655_, lean_object* v_lo_656_, lean_object* v_hi_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_654_, v_as_655_, v_lo_656_, v_hi_657_);
lean_dec(v_hi_657_);
lean_dec(v_n_654_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_661_){
_start:
{
lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v_unexpected_694_; lean_object* v_expected_695_; lean_object* v___y_697_; lean_object* v___x_707_; uint8_t v___x_708_; 
v_unexpected_694_ = lean_ctor_get(v_e_661_, 1);
lean_inc_ref(v_unexpected_694_);
v_expected_695_ = lean_ctor_get(v_e_661_, 2);
lean_inc(v_expected_695_);
lean_dec_ref(v_e_661_);
v___x_707_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_708_ = lean_string_dec_eq(v_unexpected_694_, v___x_707_);
if (v___x_708_ == 0)
{
lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_709_ = lean_box(0);
v___x_710_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_710_, 0, v_unexpected_694_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
v___y_697_ = v___x_710_;
goto v___jp_696_;
}
else
{
lean_object* v___x_711_; 
lean_dec_ref(v_unexpected_694_);
v___x_711_ = lean_box(0);
v___y_697_ = v___x_711_;
goto v___jp_696_;
}
v___jp_662_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_666_ = l_List_appendTR___redArg(v___y_663_, v___y_664_);
v___x_667_ = l_String_intercalate(v___x_665_, v___x_666_);
return v___x_667_;
}
v___jp_668_:
{
lean_object* v___x_672_; lean_object* v_expected_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_672_ = lean_array_to_list(v___y_671_);
v_expected_673_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_672_);
v___x_674_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_675_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_673_);
v___x_676_ = lean_string_append(v___x_674_, v___x_675_);
lean_dec_ref(v___x_675_);
v___x_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_677_, 0, v___x_676_);
lean_ctor_set(v___x_677_, 1, v___y_670_);
v___y_663_ = v___y_669_;
v___y_664_ = v___x_677_;
goto v___jp_662_;
}
v___jp_678_:
{
lean_object* v___x_685_; 
v___x_685_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_680_, v___y_682_, v___y_683_, v___y_684_);
lean_dec(v___y_684_);
lean_dec(v___y_680_);
v___y_669_ = v___y_679_;
v___y_670_ = v___y_681_;
v___y_671_ = v___x_685_;
goto v___jp_668_;
}
v___jp_686_:
{
uint8_t v___x_693_; 
v___x_693_ = lean_nat_dec_le(v___y_692_, v___y_691_);
if (v___x_693_ == 0)
{
lean_dec(v___y_691_);
lean_inc(v___y_692_);
v___y_679_ = v___y_687_;
v___y_680_ = v___y_688_;
v___y_681_ = v___y_690_;
v___y_682_ = v___y_689_;
v___y_683_ = v___y_692_;
v___y_684_ = v___y_692_;
goto v___jp_678_;
}
else
{
v___y_679_ = v___y_687_;
v___y_680_ = v___y_688_;
v___y_681_ = v___y_690_;
v___y_682_ = v___y_689_;
v___y_683_ = v___y_692_;
v___y_684_ = v___y_691_;
goto v___jp_678_;
}
}
v___jp_696_:
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_box(0);
v___x_699_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_695_, v___x_698_);
if (v___x_699_ == 0)
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_700_ = lean_array_mk(v_expected_695_);
v___x_701_ = lean_array_get_size(v___x_700_);
v___x_702_ = lean_unsigned_to_nat(0u);
v___x_703_ = lean_nat_dec_eq(v___x_701_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v___x_704_ = lean_unsigned_to_nat(1u);
v___x_705_ = lean_nat_sub(v___x_701_, v___x_704_);
v___x_706_ = lean_nat_dec_le(v___x_702_, v___x_705_);
if (v___x_706_ == 0)
{
lean_inc(v___x_705_);
v___y_687_ = v___y_697_;
v___y_688_ = v___x_701_;
v___y_689_ = v___x_700_;
v___y_690_ = v___x_698_;
v___y_691_ = v___x_705_;
v___y_692_ = v___x_705_;
goto v___jp_686_;
}
else
{
v___y_687_ = v___y_697_;
v___y_688_ = v___x_701_;
v___y_689_ = v___x_700_;
v___y_690_ = v___x_698_;
v___y_691_ = v___x_705_;
v___y_692_ = v___x_702_;
goto v___jp_686_;
}
}
else
{
v___y_669_ = v___y_697_;
v___y_670_ = v___x_698_;
v___y_671_ = v___x_700_;
goto v___jp_668_;
}
}
else
{
lean_dec(v_expected_695_);
v___y_663_ = v___y_697_;
v___y_664_ = v___x_698_;
goto v___jp_662_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_712_, lean_object* v_as_713_, lean_object* v_lo_714_, lean_object* v_hi_715_, lean_object* v_w_716_, lean_object* v_hlo_717_, lean_object* v_hhi_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_712_, v_as_713_, v_lo_714_, v_hi_715_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_720_, lean_object* v_as_721_, lean_object* v_lo_722_, lean_object* v_hi_723_, lean_object* v_w_724_, lean_object* v_hlo_725_, lean_object* v_hhi_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_720_, v_as_721_, v_lo_722_, v_hi_723_, v_w_724_, v_hlo_725_, v_hhi_726_);
lean_dec(v_hi_723_);
lean_dec(v_n_720_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object* v_n_728_, lean_object* v_lo_729_, lean_object* v_hi_730_, lean_object* v_hhi_731_, lean_object* v_pivot_732_, lean_object* v_as_733_, lean_object* v_i_734_, lean_object* v_k_735_, lean_object* v_ilo_736_, lean_object* v_ik_737_, lean_object* v_w_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_730_, v_pivot_732_, v_as_733_, v_i_734_, v_k_735_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object* v_n_740_, lean_object* v_lo_741_, lean_object* v_hi_742_, lean_object* v_hhi_743_, lean_object* v_pivot_744_, lean_object* v_as_745_, lean_object* v_i_746_, lean_object* v_k_747_, lean_object* v_ilo_748_, lean_object* v_ik_749_, lean_object* v_w_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_740_, v_lo_741_, v_hi_742_, v_hhi_743_, v_pivot_744_, v_as_745_, v_i_746_, v_k_747_, v_ilo_748_, v_ik_749_, v_w_750_);
lean_dec_ref(v_pivot_744_);
lean_dec(v_hi_742_);
lean_dec(v_lo_741_);
lean_dec(v_n_740_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_754_, lean_object* v_e_u2082_755_){
_start:
{
lean_object* v_unexpectedTk_756_; lean_object* v_unexpected_757_; lean_object* v_expected_758_; lean_object* v___y_760_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_unexpectedTk_756_ = lean_ctor_get(v_e_u2082_755_, 0);
lean_inc(v_unexpectedTk_756_);
v_unexpected_757_ = lean_ctor_get(v_e_u2082_755_, 1);
lean_inc_ref(v_unexpected_757_);
v_expected_758_ = lean_ctor_get(v_e_u2082_755_, 2);
lean_inc(v_expected_758_);
lean_dec_ref(v_e_u2082_755_);
v___x_772_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_773_ = lean_string_dec_eq(v_unexpected_757_, v___x_772_);
if (v___x_773_ == 0)
{
v___y_760_ = v_unexpected_757_;
goto v___jp_759_;
}
else
{
lean_object* v_unexpected_774_; 
lean_dec_ref(v_unexpected_757_);
v_unexpected_774_ = lean_ctor_get(v_e_u2081_754_, 1);
lean_inc_ref(v_unexpected_774_);
v___y_760_ = v_unexpected_774_;
goto v___jp_759_;
}
v___jp_759_:
{
lean_object* v_expected_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_769_; 
v_expected_761_ = lean_ctor_get(v_e_u2081_754_, 2);
v_isSharedCheck_769_ = !lean_is_exclusive(v_e_u2081_754_);
if (v_isSharedCheck_769_ == 0)
{
lean_object* v_unused_770_; lean_object* v_unused_771_; 
v_unused_770_ = lean_ctor_get(v_e_u2081_754_, 1);
lean_dec(v_unused_770_);
v_unused_771_ = lean_ctor_get(v_e_u2081_754_, 0);
lean_dec(v_unused_771_);
v___x_763_ = v_e_u2081_754_;
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_expected_761_);
lean_dec(v_e_u2081_754_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_769_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_765_; lean_object* v___x_767_; 
v___x_765_ = l_List_appendTR___redArg(v_expected_761_, v_expected_758_);
if (v_isShared_764_ == 0)
{
lean_ctor_set(v___x_763_, 2, v___x_765_);
lean_ctor_set(v___x_763_, 1, v___y_760_);
lean_ctor_set(v___x_763_, 0, v_unexpectedTk_756_);
v___x_767_ = v___x_763_;
goto v_reusejp_766_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_unexpectedTk_756_);
lean_ctor_set(v_reuseFailAlloc_768_, 1, v___y_760_);
lean_ctor_set(v_reuseFailAlloc_768_, 2, v___x_765_);
v___x_767_ = v_reuseFailAlloc_768_;
goto v_reusejp_766_;
}
v_reusejp_766_:
{
return v___x_767_;
}
}
}
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
if (lean_obj_tag(v_x_775_) == 0)
{
if (lean_obj_tag(v_x_776_) == 0)
{
uint8_t v___x_777_; 
v___x_777_ = 1;
return v___x_777_;
}
else
{
uint8_t v___x_778_; 
v___x_778_ = 0;
return v___x_778_;
}
}
else
{
if (lean_obj_tag(v_x_776_) == 0)
{
uint8_t v___x_779_; 
v___x_779_ = 0;
return v___x_779_;
}
else
{
lean_object* v_val_780_; lean_object* v_val_781_; uint8_t v_decide_782_; 
v_val_780_ = lean_ctor_get(v_x_775_, 0);
v_val_781_ = lean_ctor_get(v_x_776_, 0);
v_decide_782_ = lean_nat_dec_eq(v_val_780_, v_val_781_);
return v_decide_782_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_775_ = stack[0].m_obj;
lean_object* v_x_776_ = stack[1].m_obj;
uint8_t v_res_783_;
v_res_783_ = l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_x_775_, v_x_776_);
stack->m_num = v_res_783_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0___boxed(lean_object* v_x_784_, lean_object* v_x_785_){
_start:
{
uint8_t v_res_786_; lean_object* v_r_787_; 
v_res_786_ = l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_x_784_, v_x_785_);
lean_dec(v_x_785_);
lean_dec(v_x_784_);
v_r_787_ = lean_box(v_res_786_);
return v_r_787_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(lean_object* v_xs_788_, lean_object* v_ys_789_, lean_object* v_x_790_){
_start:
{
lean_object* v_zero_791_; uint8_t v_isZero_792_; 
v_zero_791_ = lean_unsigned_to_nat(0u);
v_isZero_792_ = lean_nat_dec_eq(v_x_790_, v_zero_791_);
if (v_isZero_792_ == 1)
{
lean_dec(v_x_790_);
return v_isZero_792_;
}
else
{
lean_object* v_one_793_; lean_object* v_n_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_one_793_ = lean_unsigned_to_nat(1u);
v_n_794_ = lean_nat_sub(v_x_790_, v_one_793_);
lean_dec(v_x_790_);
v___x_795_ = lean_array_fget_borrowed(v_xs_788_, v_n_794_);
v___x_796_ = lean_array_fget_borrowed(v_ys_789_, v_n_794_);
v___x_797_ = lean_string_dec_eq(v___x_795_, v___x_796_);
if (v___x_797_ == 0)
{
lean_dec(v_n_794_);
return v___x_797_;
}
else
{
v_x_790_ = v_n_794_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_788_ = stack[0].m_obj;
lean_object* v_ys_789_ = stack[1].m_obj;
lean_object* v_x_790_ = stack[2].m_obj;
uint8_t v_res_799_;
v_res_799_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_788_, v_ys_789_, v_x_790_);
stack->m_num = v_res_799_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg___boxed(lean_object* v_xs_800_, lean_object* v_ys_801_, lean_object* v_x_802_){
_start:
{
uint8_t v_res_803_; lean_object* v_r_804_; 
v_res_803_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_800_, v_ys_801_, v_x_802_);
lean_dec_ref(v_ys_801_);
lean_dec_ref(v_xs_800_);
v_r_804_ = lean_box(v_res_803_);
return v_r_804_;
}
}
uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_805_, lean_object* v_x_806_){
_start:
{
lean_object* v_toCacheableParserContext_807_; lean_object* v_parserName_808_; lean_object* v_pos_809_; lean_object* v_toCacheableParserContext_810_; lean_object* v_parserName_811_; lean_object* v_pos_812_; uint8_t v___y_817_; lean_object* v_prec_818_; lean_object* v_quotDepth_819_; uint8_t v_suppressInsideQuot_820_; lean_object* v_savedPos_x3f_821_; lean_object* v_forbiddenTks_822_; lean_object* v_prec_823_; lean_object* v_quotDepth_824_; uint8_t v_suppressInsideQuot_825_; lean_object* v_savedPos_x3f_826_; lean_object* v_forbiddenTks_827_; uint8_t v___x_837_; 
v_toCacheableParserContext_807_ = lean_ctor_get(v_x_805_, 0);
v_parserName_808_ = lean_ctor_get(v_x_805_, 1);
v_pos_809_ = lean_ctor_get(v_x_805_, 2);
v_toCacheableParserContext_810_ = lean_ctor_get(v_x_806_, 0);
v_parserName_811_ = lean_ctor_get(v_x_806_, 1);
v_pos_812_ = lean_ctor_get(v_x_806_, 2);
v_prec_818_ = lean_ctor_get(v_toCacheableParserContext_807_, 0);
v_quotDepth_819_ = lean_ctor_get(v_toCacheableParserContext_807_, 1);
v_suppressInsideQuot_820_ = lean_ctor_get_uint8(v_toCacheableParserContext_807_, sizeof(void*)*4);
v_savedPos_x3f_821_ = lean_ctor_get(v_toCacheableParserContext_807_, 2);
v_forbiddenTks_822_ = lean_ctor_get(v_toCacheableParserContext_807_, 3);
v_prec_823_ = lean_ctor_get(v_toCacheableParserContext_810_, 0);
v_quotDepth_824_ = lean_ctor_get(v_toCacheableParserContext_810_, 1);
v_suppressInsideQuot_825_ = lean_ctor_get_uint8(v_toCacheableParserContext_810_, sizeof(void*)*4);
v_savedPos_x3f_826_ = lean_ctor_get(v_toCacheableParserContext_810_, 2);
v_forbiddenTks_827_ = lean_ctor_get(v_toCacheableParserContext_810_, 3);
v___x_837_ = lean_nat_dec_eq(v_prec_818_, v_prec_823_);
if (v___x_837_ == 0)
{
return v___x_837_;
}
else
{
uint8_t v___x_838_; 
v___x_838_ = lean_nat_dec_eq(v_quotDepth_819_, v_quotDepth_824_);
if (v___x_838_ == 0)
{
return v___x_838_;
}
else
{
if (v_suppressInsideQuot_825_ == 0)
{
if (v_suppressInsideQuot_820_ == 0)
{
goto v___jp_828_;
}
else
{
return v_suppressInsideQuot_825_;
}
}
else
{
if (v_suppressInsideQuot_820_ == 0)
{
return v_suppressInsideQuot_820_;
}
else
{
goto v___jp_828_;
}
}
}
}
v___jp_813_:
{
uint8_t v___x_814_; 
v___x_814_ = lean_name_eq(v_parserName_808_, v_parserName_811_);
if (v___x_814_ == 0)
{
return v___x_814_;
}
else
{
uint8_t v_decide_815_; 
v_decide_815_ = lean_nat_dec_eq(v_pos_809_, v_pos_812_);
return v_decide_815_;
}
}
v___jp_816_:
{
if (v___y_817_ == 0)
{
return v___y_817_;
}
else
{
goto v___jp_813_;
}
}
v___jp_828_:
{
uint8_t v___x_829_; 
v___x_829_ = l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_savedPos_x3f_821_, v_savedPos_x3f_826_);
if (v___x_829_ == 0)
{
v___y_817_ = v___x_829_;
goto v___jp_816_;
}
else
{
size_t v___x_830_; size_t v___x_831_; uint8_t v___x_832_; 
v___x_830_ = lean_ptr_addr(v_forbiddenTks_822_);
v___x_831_ = lean_ptr_addr(v_forbiddenTks_827_);
v___x_832_ = lean_usize_dec_eq(v___x_830_, v___x_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_833_ = lean_array_get_size(v_forbiddenTks_822_);
v___x_834_ = lean_array_get_size(v_forbiddenTks_827_);
v___x_835_ = lean_nat_dec_eq(v___x_833_, v___x_834_);
if (v___x_835_ == 0)
{
return v___x_835_;
}
else
{
uint8_t v___x_836_; 
v___x_836_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_forbiddenTks_822_, v_forbiddenTks_827_, v___x_833_);
v___y_817_ = v___x_836_;
goto v___jp_816_;
}
}
else
{
goto v___jp_813_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_instBEqParserCacheKey_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_805_ = stack[0].m_obj;
lean_object* v_x_806_ = stack[1].m_obj;
uint8_t v_res_839_;
v_res_839_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_805_, v_x_806_);
stack->m_num = v_res_839_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
uint8_t v_res_842_; lean_object* v_r_843_; 
v_res_842_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_840_, v_x_841_);
lean_dec_ref(v_x_841_);
lean_dec_ref(v_x_840_);
v_r_843_ = lean_box(v_res_842_);
return v_r_843_;
}
}
uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(lean_object* v_xs_844_, lean_object* v_ys_845_, lean_object* v_hsz_846_, lean_object* v_x_847_, lean_object* v_x_848_){
_start:
{
uint8_t v___x_849_; 
v___x_849_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_844_, v_ys_845_, v_x_847_);
return v___x_849_;
}
}
LEAN_EXPORT void l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_844_ = stack[0].m_obj;
lean_object* v_ys_845_ = stack[1].m_obj;
lean_object* v_x_847_ = stack[3].m_obj;
uint8_t v_res_850_;
v_res_850_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(v_xs_844_, v_ys_845_, lean_box(0), v_x_847_, lean_box(0));
stack->m_num = v_res_850_;
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___boxed(lean_object* v_xs_851_, lean_object* v_ys_852_, lean_object* v_hsz_853_, lean_object* v_x_854_, lean_object* v_x_855_){
_start:
{
uint8_t v_res_856_; lean_object* v_r_857_; 
v_res_856_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(v_xs_851_, v_ys_852_, v_hsz_853_, v_x_854_, v_x_855_);
lean_dec_ref(v_ys_852_);
lean_dec_ref(v_xs_851_);
v_r_857_ = lean_box(v_res_856_);
return v_r_857_;
}
}
uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* v_k_860_){
_start:
{
lean_object* v_parserName_861_; lean_object* v_pos_862_; uint64_t v___x_863_; 
v_parserName_861_ = lean_ctor_get(v_k_860_, 1);
v_pos_862_ = lean_ctor_get(v_k_860_, 2);
v___x_863_ = l_String_instHashableRaw_hash(v_pos_862_);
if (lean_obj_tag(v_parserName_861_) == 0)
{
uint64_t v___x_864_; uint64_t v___x_865_; 
v___x_864_ = 1723ULL;
v___x_865_ = lean_uint64_mix_hash(v___x_863_, v___x_864_);
return v___x_865_;
}
else
{
uint64_t v_hash_866_; uint64_t v___x_867_; 
v_hash_866_ = lean_ctor_get_uint64(v_parserName_861_, sizeof(void*)*2);
v___x_867_ = lean_uint64_mix_hash(v___x_863_, v_hash_866_);
return v___x_867_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_instHashableParserCacheKey___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_860_ = stack[0].m_obj;
uint64_t v_res_868_;
v_res_868_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_860_);
stack->m_num = v_res_868_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* v_k_869_){
_start:
{
uint64_t v_res_870_; lean_object* v_r_871_; 
v_res_870_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_869_);
lean_dec_ref(v_k_869_);
v_r_871_ = lean_box_uint64(v_res_870_);
return v_r_871_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0(void){
_start:
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_874_ = lean_box(0);
v___x_875_ = lean_unsigned_to_nat(16u);
v___x_876_ = lean_mk_array(v___x_875_, v___x_874_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v___x_877_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_880_){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_881_ = lean_string_utf8_byte_size(v_input_880_);
v___x_882_ = lean_unsigned_to_nat(1u);
v___x_883_ = lean_nat_add(v___x_881_, v___x_882_);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_box(0);
v___x_886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_886_, 0, v___x_883_);
lean_ctor_set(v___x_886_, 1, v___x_884_);
lean_ctor_set(v___x_886_, 2, v___x_885_);
v___x_887_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_886_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Lean_Parser_initCacheForInput(v_input_889_);
lean_dec_ref(v_input_889_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_891_){
_start:
{
lean_object* v_raw_892_; lean_object* v_drop_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v_raw_892_ = lean_ctor_get(v_stack_891_, 0);
lean_inc_ref(v_raw_892_);
v_drop_893_ = lean_ctor_get(v_stack_891_, 1);
lean_inc(v_drop_893_);
lean_dec_ref(v_stack_891_);
v___x_894_ = lean_array_get_size(v_raw_892_);
v___x_895_ = l_Array_toSubarray___redArg(v_raw_892_, v_drop_893_, v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_902_){
_start:
{
lean_object* v_raw_903_; lean_object* v_drop_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_raw_903_ = lean_ctor_get(v_stack_902_, 0);
v_drop_904_ = lean_ctor_get(v_stack_902_, 1);
v___x_905_ = lean_array_get_size(v_raw_903_);
v___x_906_ = lean_nat_sub(v___x_905_, v_drop_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_907_){
_start:
{
lean_object* v_res_908_; 
v_res_908_ = l_Lean_Parser_SyntaxStack_size(v_stack_907_);
lean_dec_ref(v_stack_907_);
return v_res_908_;
}
}
uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_909_){
_start:
{
lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v___x_910_ = l_Lean_Parser_SyntaxStack_size(v_stack_909_);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_nat_dec_eq(v___x_910_, v___x_911_);
lean_dec(v___x_910_);
return v___x_912_;
}
}
LEAN_EXPORT void l_Lean_Parser_SyntaxStack_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_stack_909_ = stack[0].m_obj;
uint8_t v_res_913_;
v_res_913_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_909_);
stack->m_num = v_res_913_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_914_){
_start:
{
uint8_t v_res_915_; lean_object* v_r_916_; 
v_res_915_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_914_);
lean_dec_ref(v_stack_914_);
v_r_916_ = lean_box(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_917_, lean_object* v_n_918_){
_start:
{
lean_object* v_raw_919_; lean_object* v_drop_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_929_; 
v_raw_919_ = lean_ctor_get(v_stack_917_, 0);
v_drop_920_ = lean_ctor_get(v_stack_917_, 1);
v_isSharedCheck_929_ = !lean_is_exclusive(v_stack_917_);
if (v_isSharedCheck_929_ == 0)
{
v___x_922_ = v_stack_917_;
v_isShared_923_ = v_isSharedCheck_929_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_drop_920_);
lean_inc(v_raw_919_);
lean_dec(v_stack_917_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_929_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_927_; 
v___x_924_ = lean_nat_add(v_drop_920_, v_n_918_);
v___x_925_ = l_Array_shrink___redArg(v_raw_919_, v___x_924_);
lean_dec(v___x_924_);
if (v_isShared_923_ == 0)
{
lean_ctor_set(v___x_922_, 0, v___x_925_);
v___x_927_ = v___x_922_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v___x_925_);
lean_ctor_set(v_reuseFailAlloc_928_, 1, v_drop_920_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_930_, lean_object* v_n_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_930_, v_n_931_);
lean_dec(v_n_931_);
return v_res_932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_raw_935_; lean_object* v_drop_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_944_; 
v_raw_935_ = lean_ctor_get(v_stack_933_, 0);
v_drop_936_ = lean_ctor_get(v_stack_933_, 1);
v_isSharedCheck_944_ = !lean_is_exclusive(v_stack_933_);
if (v_isSharedCheck_944_ == 0)
{
v___x_938_ = v_stack_933_;
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_drop_936_);
lean_inc(v_raw_935_);
lean_dec(v_stack_933_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_944_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; lean_object* v___x_942_; 
v___x_940_ = lean_array_push(v_raw_935_, v_a_934_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 0, v___x_940_);
v___x_942_ = v___x_938_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
lean_ctor_set(v_reuseFailAlloc_943_, 1, v_drop_936_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_945_){
_start:
{
lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = l_Lean_Parser_SyntaxStack_size(v_stack_945_);
v___x_948_ = lean_nat_dec_lt(v___x_946_, v___x_947_);
lean_dec(v___x_947_);
if (v___x_948_ == 0)
{
return v_stack_945_;
}
else
{
lean_object* v_raw_949_; lean_object* v_drop_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_958_; 
v_raw_949_ = lean_ctor_get(v_stack_945_, 0);
v_drop_950_ = lean_ctor_get(v_stack_945_, 1);
v_isSharedCheck_958_ = !lean_is_exclusive(v_stack_945_);
if (v_isSharedCheck_958_ == 0)
{
v___x_952_ = v_stack_945_;
v_isShared_953_ = v_isSharedCheck_958_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_drop_950_);
lean_inc(v_raw_949_);
lean_dec(v_stack_945_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_958_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
lean_object* v___x_954_; lean_object* v___x_956_; 
v___x_954_ = lean_array_pop(v_raw_949_);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_954_);
v___x_956_ = v___x_952_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_954_);
lean_ctor_set(v_reuseFailAlloc_957_, 1, v_drop_950_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_959_){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = lean_box(0);
v___x_961_ = lean_panic_fn_borrowed(v___x_960_, v_msg_959_);
return v___x_961_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_965_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_966_ = lean_unsigned_to_nat(4u);
v___x_967_ = lean_unsigned_to_nat(315u);
v___x_968_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_969_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_970_ = l_mkPanicMessageWithDecl(v___x_969_, v___x_968_, v___x_967_, v___x_966_, v___x_965_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_971_){
_start:
{
lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = l_Lean_Parser_SyntaxStack_size(v_stack_971_);
v___x_974_ = lean_nat_dec_lt(v___x_972_, v___x_973_);
lean_dec(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_976_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_975_);
return v___x_976_;
}
else
{
lean_object* v_raw_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v_raw_977_ = lean_ctor_get(v_stack_971_, 0);
v___x_978_ = lean_box(0);
v___x_979_ = lean_array_get_size(v_raw_977_);
v___x_980_ = lean_unsigned_to_nat(1u);
v___x_981_ = lean_nat_sub(v___x_979_, v___x_980_);
v___x_982_ = lean_array_get_borrowed(v___x_978_, v_raw_977_, v___x_981_);
lean_dec(v___x_981_);
lean_inc(v___x_982_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Parser_SyntaxStack_back(v_stack_983_);
lean_dec_ref(v_stack_983_);
return v_res_984_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v___x_987_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_988_ = lean_unsigned_to_nat(4u);
v___x_989_ = lean_unsigned_to_nat(321u);
v___x_990_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_991_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_992_ = l_mkPanicMessageWithDecl(v___x_991_, v___x_990_, v___x_989_, v___x_988_, v___x_987_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_993_, lean_object* v_i_994_){
_start:
{
lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_995_ = l_Lean_Parser_SyntaxStack_size(v_stack_993_);
v___x_996_ = lean_nat_dec_lt(v_i_994_, v___x_995_);
lean_dec(v___x_995_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_997_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_998_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_997_);
return v___x_998_;
}
else
{
lean_object* v_raw_999_; lean_object* v_drop_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_raw_999_ = lean_ctor_get(v_stack_993_, 0);
v_drop_1000_ = lean_ctor_get(v_stack_993_, 1);
v___x_1001_ = lean_box(0);
v___x_1002_ = lean_nat_add(v_drop_1000_, v_i_994_);
v___x_1003_ = lean_array_get_borrowed(v___x_1001_, v_raw_999_, v___x_1002_);
lean_dec(v___x_1002_);
lean_inc(v___x_1003_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_1004_, lean_object* v_i_1005_){
_start:
{
lean_object* v_res_1006_; 
v_res_1006_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_1004_, v_i_1005_);
lean_dec(v_i_1005_);
lean_dec_ref(v_stack_1004_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_1007_, lean_object* v_start_1008_, lean_object* v_stop_1009_){
_start:
{
lean_object* v_raw_1010_; lean_object* v_drop_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; 
v_raw_1010_ = lean_ctor_get(v_stack_1007_, 0);
v_drop_1011_ = lean_ctor_get(v_stack_1007_, 1);
v___x_1012_ = lean_nat_add(v_drop_1011_, v_start_1008_);
v___x_1013_ = lean_nat_add(v_drop_1011_, v_stop_1009_);
v___x_1014_ = l_Array_extract___redArg(v_raw_1010_, v___x_1012_, v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_1015_, lean_object* v_start_1016_, lean_object* v_stop_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l_Lean_Parser_SyntaxStack_extract(v_stack_1015_, v_start_1016_, v_stop_1017_);
lean_dec(v_stop_1017_);
lean_dec(v_start_1016_);
lean_dec_ref(v_stack_1015_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_1019_, lean_object* v_stxs_1020_){
_start:
{
lean_object* v_raw_1021_; lean_object* v_drop_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1030_; 
v_raw_1021_ = lean_ctor_get(v_stack_1019_, 0);
v_drop_1022_ = lean_ctor_get(v_stack_1019_, 1);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_stack_1019_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1024_ = v_stack_1019_;
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_drop_1022_);
lean_inc(v_raw_1021_);
lean_dec(v_stack_1019_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1030_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
v___x_1026_ = l_Array_append___redArg(v_raw_1021_, v_stxs_1020_);
if (v_isShared_1025_ == 0)
{
lean_ctor_set(v___x_1024_, 0, v___x_1026_);
v___x_1028_ = v___x_1024_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
lean_ctor_set(v_reuseFailAlloc_1029_, 1, v_drop_1022_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_1031_, lean_object* v_stxs_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_1031_, v_stxs_1032_);
lean_dec_ref(v_stxs_1032_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_1034_, lean_object* v_stxs_1035_){
_start:
{
lean_object* v_raw_1036_; lean_object* v_drop_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1045_; 
v_raw_1036_ = lean_ctor_get(v_stack_1034_, 0);
v_drop_1037_ = lean_ctor_get(v_stack_1034_, 1);
v_isSharedCheck_1045_ = !lean_is_exclusive(v_stack_1034_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1039_ = v_stack_1034_;
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_drop_1037_);
lean_inc(v_raw_1036_);
lean_dec(v_stack_1034_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1045_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1041_; lean_object* v___x_1043_; 
v___x_1041_ = l_Array_append___redArg(v_raw_1036_, v_stxs_1035_);
if (v_isShared_1040_ == 0)
{
lean_ctor_set(v___x_1039_, 0, v___x_1041_);
v___x_1043_ = v___x_1039_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v___x_1041_);
lean_ctor_set(v_reuseFailAlloc_1044_, 1, v_drop_1037_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_1046_, lean_object* v_stxs_1047_){
_start:
{
lean_object* v_res_1048_; 
v_res_1048_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_1046_, v_stxs_1047_);
lean_dec_ref(v_stxs_1047_);
return v_res_1048_;
}
}
uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_1051_){
_start:
{
lean_object* v_errorMsg_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_errorMsg_1052_ = lean_ctor_get(v_s_1051_, 4);
lean_inc(v_errorMsg_1052_);
lean_dec_ref(v_s_1051_);
v___x_1053_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_1054_ = lean_box(0);
v___x_1055_ = l_instBEqOption_beq___redArg(v___x_1053_, v_errorMsg_1052_, v___x_1054_);
if (v___x_1055_ == 0)
{
uint8_t v___x_1056_; 
v___x_1056_ = 1;
return v___x_1056_;
}
else
{
uint8_t v___x_1057_; 
v___x_1057_ = 0;
return v___x_1057_;
}
}
}
LEAN_EXPORT void l_Lean_Parser_ParserState_hasError_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1051_ = stack[0].m_obj;
uint8_t v_res_1058_;
v_res_1058_ = l_Lean_Parser_ParserState_hasError(v_s_1051_);
stack->m_num = v_res_1058_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_1059_){
_start:
{
uint8_t v_res_1060_; lean_object* v_r_1061_; 
v_res_1060_ = l_Lean_Parser_ParserState_hasError(v_s_1059_);
v_r_1061_ = lean_box(v_res_1060_);
return v_r_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_1062_){
_start:
{
lean_object* v_stxStack_1063_; lean_object* v___x_1064_; 
v_stxStack_1063_ = lean_ctor_get(v_s_1062_, 0);
v___x_1064_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Lean_Parser_ParserState_stackSize(v_s_1065_);
lean_dec_ref(v_s_1065_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_1067_, lean_object* v_iniStackSz_1068_, lean_object* v_iniPos_1069_){
_start:
{
lean_object* v_stxStack_1070_; lean_object* v_lhsPrec_1071_; lean_object* v_cache_1072_; lean_object* v_recoveredErrors_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1082_; 
v_stxStack_1070_ = lean_ctor_get(v_s_1067_, 0);
v_lhsPrec_1071_ = lean_ctor_get(v_s_1067_, 1);
v_cache_1072_ = lean_ctor_get(v_s_1067_, 3);
v_recoveredErrors_1073_ = lean_ctor_get(v_s_1067_, 5);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_s_1067_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; lean_object* v_unused_1084_; 
v_unused_1083_ = lean_ctor_get(v_s_1067_, 4);
lean_dec(v_unused_1083_);
v_unused_1084_ = lean_ctor_get(v_s_1067_, 2);
lean_dec(v_unused_1084_);
v___x_1075_ = v_s_1067_;
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_recoveredErrors_1073_);
lean_inc(v_cache_1072_);
lean_inc(v_lhsPrec_1071_);
lean_inc(v_stxStack_1070_);
lean_dec(v_s_1067_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1082_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1070_, v_iniStackSz_1068_);
v___x_1078_ = lean_box(0);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 4, v___x_1078_);
lean_ctor_set(v___x_1075_, 2, v_iniPos_1069_);
lean_ctor_set(v___x_1075_, 0, v___x_1077_);
v___x_1080_ = v___x_1075_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1077_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_lhsPrec_1071_);
lean_ctor_set(v_reuseFailAlloc_1081_, 2, v_iniPos_1069_);
lean_ctor_set(v_reuseFailAlloc_1081_, 3, v_cache_1072_);
lean_ctor_set(v_reuseFailAlloc_1081_, 4, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1081_, 5, v_recoveredErrors_1073_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_1085_, lean_object* v_iniStackSz_1086_, lean_object* v_iniPos_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l_Lean_Parser_ParserState_restore(v_s_1085_, v_iniStackSz_1086_, v_iniPos_1087_);
lean_dec(v_iniStackSz_1086_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_1089_, lean_object* v_pos_1090_){
_start:
{
lean_object* v_stxStack_1091_; lean_object* v_lhsPrec_1092_; lean_object* v_cache_1093_; lean_object* v_errorMsg_1094_; lean_object* v_recoveredErrors_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
v_stxStack_1091_ = lean_ctor_get(v_s_1089_, 0);
v_lhsPrec_1092_ = lean_ctor_get(v_s_1089_, 1);
v_cache_1093_ = lean_ctor_get(v_s_1089_, 3);
v_errorMsg_1094_ = lean_ctor_get(v_s_1089_, 4);
v_recoveredErrors_1095_ = lean_ctor_get(v_s_1089_, 5);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_s_1089_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; 
v_unused_1103_ = lean_ctor_get(v_s_1089_, 2);
lean_dec(v_unused_1103_);
v___x_1097_ = v_s_1089_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_recoveredErrors_1095_);
lean_inc(v_errorMsg_1094_);
lean_inc(v_cache_1093_);
lean_inc(v_lhsPrec_1092_);
lean_inc(v_stxStack_1091_);
lean_dec(v_s_1089_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 2, v_pos_1090_);
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_stxStack_1091_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_lhsPrec_1092_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v_pos_1090_);
lean_ctor_set(v_reuseFailAlloc_1101_, 3, v_cache_1093_);
lean_ctor_set(v_reuseFailAlloc_1101_, 4, v_errorMsg_1094_);
lean_ctor_set(v_reuseFailAlloc_1101_, 5, v_recoveredErrors_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_1104_, lean_object* v_cache_1105_){
_start:
{
lean_object* v_stxStack_1106_; lean_object* v_lhsPrec_1107_; lean_object* v_pos_1108_; lean_object* v_errorMsg_1109_; lean_object* v_recoveredErrors_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
v_stxStack_1106_ = lean_ctor_get(v_s_1104_, 0);
v_lhsPrec_1107_ = lean_ctor_get(v_s_1104_, 1);
v_pos_1108_ = lean_ctor_get(v_s_1104_, 2);
v_errorMsg_1109_ = lean_ctor_get(v_s_1104_, 4);
v_recoveredErrors_1110_ = lean_ctor_get(v_s_1104_, 5);
v_isSharedCheck_1117_ = !lean_is_exclusive(v_s_1104_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v_s_1104_, 3);
lean_dec(v_unused_1118_);
v___x_1112_ = v_s_1104_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_recoveredErrors_1110_);
lean_inc(v_errorMsg_1109_);
lean_inc(v_pos_1108_);
lean_inc(v_lhsPrec_1107_);
lean_inc(v_stxStack_1106_);
lean_dec(v_s_1104_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 3, v_cache_1105_);
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_stxStack_1106_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_lhsPrec_1107_);
lean_ctor_set(v_reuseFailAlloc_1116_, 2, v_pos_1108_);
lean_ctor_set(v_reuseFailAlloc_1116_, 3, v_cache_1105_);
lean_ctor_set(v_reuseFailAlloc_1116_, 4, v_errorMsg_1109_);
lean_ctor_set(v_reuseFailAlloc_1116_, 5, v_recoveredErrors_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_1119_, lean_object* v_n_1120_){
_start:
{
lean_object* v_stxStack_1121_; lean_object* v_lhsPrec_1122_; lean_object* v_pos_1123_; lean_object* v_cache_1124_; lean_object* v_errorMsg_1125_; lean_object* v_recoveredErrors_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1134_; 
v_stxStack_1121_ = lean_ctor_get(v_s_1119_, 0);
v_lhsPrec_1122_ = lean_ctor_get(v_s_1119_, 1);
v_pos_1123_ = lean_ctor_get(v_s_1119_, 2);
v_cache_1124_ = lean_ctor_get(v_s_1119_, 3);
v_errorMsg_1125_ = lean_ctor_get(v_s_1119_, 4);
v_recoveredErrors_1126_ = lean_ctor_get(v_s_1119_, 5);
v_isSharedCheck_1134_ = !lean_is_exclusive(v_s_1119_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1128_ = v_s_1119_;
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_recoveredErrors_1126_);
lean_inc(v_errorMsg_1125_);
lean_inc(v_cache_1124_);
lean_inc(v_pos_1123_);
lean_inc(v_lhsPrec_1122_);
lean_inc(v_stxStack_1121_);
lean_dec(v_s_1119_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1134_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
v___x_1130_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1121_, v_n_1120_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v___x_1130_);
v___x_1132_ = v___x_1128_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
lean_ctor_set(v_reuseFailAlloc_1133_, 1, v_lhsPrec_1122_);
lean_ctor_set(v_reuseFailAlloc_1133_, 2, v_pos_1123_);
lean_ctor_set(v_reuseFailAlloc_1133_, 3, v_cache_1124_);
lean_ctor_set(v_reuseFailAlloc_1133_, 4, v_errorMsg_1125_);
lean_ctor_set(v_reuseFailAlloc_1133_, 5, v_recoveredErrors_1126_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1135_){
_start:
{
lean_object* v_stxStack_1136_; lean_object* v_lhsPrec_1137_; lean_object* v_pos_1138_; lean_object* v_cache_1139_; lean_object* v_errorMsg_1140_; lean_object* v_recoveredErrors_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1149_; 
v_stxStack_1136_ = lean_ctor_get(v_s_1135_, 0);
v_lhsPrec_1137_ = lean_ctor_get(v_s_1135_, 1);
v_pos_1138_ = lean_ctor_get(v_s_1135_, 2);
v_cache_1139_ = lean_ctor_get(v_s_1135_, 3);
v_errorMsg_1140_ = lean_ctor_get(v_s_1135_, 4);
v_recoveredErrors_1141_ = lean_ctor_get(v_s_1135_, 5);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_s_1135_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1143_ = v_s_1135_;
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_recoveredErrors_1141_);
lean_inc(v_errorMsg_1140_);
lean_inc(v_cache_1139_);
lean_inc(v_pos_1138_);
lean_inc(v_lhsPrec_1137_);
lean_inc(v_stxStack_1136_);
lean_dec(v_s_1135_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1149_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1136_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1145_);
v___x_1147_ = v___x_1143_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v___x_1145_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_lhsPrec_1137_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_pos_1138_);
lean_ctor_set(v_reuseFailAlloc_1148_, 3, v_cache_1139_);
lean_ctor_set(v_reuseFailAlloc_1148_, 4, v_errorMsg_1140_);
lean_ctor_set(v_reuseFailAlloc_1148_, 5, v_recoveredErrors_1141_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1150_, lean_object* v_iniStackSz_1151_){
_start:
{
lean_object* v_stxStack_1152_; lean_object* v_lhsPrec_1153_; lean_object* v_pos_1154_; lean_object* v_cache_1155_; lean_object* v_errorMsg_1156_; lean_object* v_recoveredErrors_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1165_; 
v_stxStack_1152_ = lean_ctor_get(v_s_1150_, 0);
v_lhsPrec_1153_ = lean_ctor_get(v_s_1150_, 1);
v_pos_1154_ = lean_ctor_get(v_s_1150_, 2);
v_cache_1155_ = lean_ctor_get(v_s_1150_, 3);
v_errorMsg_1156_ = lean_ctor_get(v_s_1150_, 4);
v_recoveredErrors_1157_ = lean_ctor_get(v_s_1150_, 5);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_s_1150_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1159_ = v_s_1150_;
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_recoveredErrors_1157_);
lean_inc(v_errorMsg_1156_);
lean_inc(v_cache_1155_);
lean_inc(v_pos_1154_);
lean_inc(v_lhsPrec_1153_);
lean_inc(v_stxStack_1152_);
lean_dec(v_s_1150_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1165_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v___x_1163_; 
v___x_1161_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1152_, v_iniStackSz_1151_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1163_ = v___x_1159_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_lhsPrec_1153_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_pos_1154_);
lean_ctor_set(v_reuseFailAlloc_1164_, 3, v_cache_1155_);
lean_ctor_set(v_reuseFailAlloc_1164_, 4, v_errorMsg_1156_);
lean_ctor_set(v_reuseFailAlloc_1164_, 5, v_recoveredErrors_1157_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1166_, lean_object* v_iniStackSz_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1166_, v_iniStackSz_1167_);
lean_dec(v_iniStackSz_1167_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1169_, lean_object* v_c_1170_, lean_object* v_pos_1171_){
_start:
{
lean_object* v_toInputContext_1172_; lean_object* v_stxStack_1173_; lean_object* v_lhsPrec_1174_; lean_object* v_cache_1175_; lean_object* v_errorMsg_1176_; lean_object* v_recoveredErrors_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1186_; 
v_toInputContext_1172_ = lean_ctor_get(v_c_1170_, 0);
v_stxStack_1173_ = lean_ctor_get(v_s_1169_, 0);
v_lhsPrec_1174_ = lean_ctor_get(v_s_1169_, 1);
v_cache_1175_ = lean_ctor_get(v_s_1169_, 3);
v_errorMsg_1176_ = lean_ctor_get(v_s_1169_, 4);
v_recoveredErrors_1177_ = lean_ctor_get(v_s_1169_, 5);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_s_1169_);
if (v_isSharedCheck_1186_ == 0)
{
lean_object* v_unused_1187_; 
v_unused_1187_ = lean_ctor_get(v_s_1169_, 2);
lean_dec(v_unused_1187_);
v___x_1179_ = v_s_1169_;
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_recoveredErrors_1177_);
lean_inc(v_errorMsg_1176_);
lean_inc(v_cache_1175_);
lean_inc(v_lhsPrec_1174_);
lean_inc(v_stxStack_1173_);
lean_dec(v_s_1169_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1186_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_inputString_1181_; lean_object* v___x_1182_; lean_object* v___x_1184_; 
v_inputString_1181_ = lean_ctor_get(v_toInputContext_1172_, 0);
v___x_1182_ = lean_string_utf8_next(v_inputString_1181_, v_pos_1171_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 2, v___x_1182_);
v___x_1184_ = v___x_1179_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_stxStack_1173_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v_lhsPrec_1174_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v___x_1182_);
lean_ctor_set(v_reuseFailAlloc_1185_, 3, v_cache_1175_);
lean_ctor_set(v_reuseFailAlloc_1185_, 4, v_errorMsg_1176_);
lean_ctor_set(v_reuseFailAlloc_1185_, 5, v_recoveredErrors_1177_);
v___x_1184_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
return v___x_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1188_, lean_object* v_c_1189_, lean_object* v_pos_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Parser_ParserState_next(v_s_1188_, v_c_1189_, v_pos_1190_);
lean_dec(v_pos_1190_);
lean_dec_ref(v_c_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1192_, lean_object* v_c_1193_, lean_object* v_pos_1194_){
_start:
{
lean_object* v_toInputContext_1195_; lean_object* v_stxStack_1196_; lean_object* v_lhsPrec_1197_; lean_object* v_cache_1198_; lean_object* v_errorMsg_1199_; lean_object* v_recoveredErrors_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1209_; 
v_toInputContext_1195_ = lean_ctor_get(v_c_1193_, 0);
v_stxStack_1196_ = lean_ctor_get(v_s_1192_, 0);
v_lhsPrec_1197_ = lean_ctor_get(v_s_1192_, 1);
v_cache_1198_ = lean_ctor_get(v_s_1192_, 3);
v_errorMsg_1199_ = lean_ctor_get(v_s_1192_, 4);
v_recoveredErrors_1200_ = lean_ctor_get(v_s_1192_, 5);
v_isSharedCheck_1209_ = !lean_is_exclusive(v_s_1192_);
if (v_isSharedCheck_1209_ == 0)
{
lean_object* v_unused_1210_; 
v_unused_1210_ = lean_ctor_get(v_s_1192_, 2);
lean_dec(v_unused_1210_);
v___x_1202_ = v_s_1192_;
v_isShared_1203_ = v_isSharedCheck_1209_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_recoveredErrors_1200_);
lean_inc(v_errorMsg_1199_);
lean_inc(v_cache_1198_);
lean_inc(v_lhsPrec_1197_);
lean_inc(v_stxStack_1196_);
lean_dec(v_s_1192_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1209_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v_inputString_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
v_inputString_1204_ = lean_ctor_get(v_toInputContext_1195_, 0);
v___x_1205_ = lean_string_utf8_next_fast(v_inputString_1204_, v_pos_1194_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 2, v___x_1205_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_stxStack_1196_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_lhsPrec_1197_);
lean_ctor_set(v_reuseFailAlloc_1208_, 2, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1208_, 3, v_cache_1198_);
lean_ctor_set(v_reuseFailAlloc_1208_, 4, v_errorMsg_1199_);
lean_ctor_set(v_reuseFailAlloc_1208_, 5, v_recoveredErrors_1200_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1211_, lean_object* v_c_1212_, lean_object* v_pos_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1211_, v_c_1212_, v_pos_1213_);
lean_dec(v_pos_1213_);
lean_dec_ref(v_c_1212_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1215_, lean_object* v_c_1216_, lean_object* v_pos_1217_, lean_object* v_h_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1215_, v_c_1216_, v_pos_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1220_, lean_object* v_c_1221_, lean_object* v_pos_1222_, lean_object* v_h_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_Lean_Parser_ParserState_next_x27(v_s_1220_, v_c_1221_, v_pos_1222_, v_h_1223_);
lean_dec(v_pos_1222_);
lean_dec_ref(v_c_1221_);
return v_res_1224_;
}
}
uint8_t l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1225_, lean_object* v_x_1226_){
_start:
{
if (lean_obj_tag(v_x_1225_) == 0)
{
if (lean_obj_tag(v_x_1226_) == 0)
{
uint8_t v___x_1227_; 
v___x_1227_ = 1;
return v___x_1227_;
}
else
{
uint8_t v___x_1228_; 
v___x_1228_ = 0;
return v___x_1228_;
}
}
else
{
if (lean_obj_tag(v_x_1226_) == 0)
{
uint8_t v___x_1229_; 
v___x_1229_ = 0;
return v___x_1229_;
}
else
{
lean_object* v_val_1230_; lean_object* v_val_1231_; uint8_t v___x_1232_; 
v_val_1230_ = lean_ctor_get(v_x_1225_, 0);
v_val_1231_ = lean_ctor_get(v_x_1226_, 0);
v___x_1232_ = l_Lean_Parser_instBEqError_beq(v_val_1230_, v_val_1231_);
return v___x_1232_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1225_ = stack[0].m_obj;
lean_object* v_x_1226_ = stack[1].m_obj;
uint8_t v_res_1233_;
v_res_1233_ = l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1225_, v_x_1226_);
stack->m_num = v_res_1233_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1234_, lean_object* v_x_1235_){
_start:
{
uint8_t v_res_1236_; lean_object* v_r_1237_; 
v_res_1236_ = l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1234_, v_x_1235_);
lean_dec(v_x_1235_);
lean_dec(v_x_1234_);
v_r_1237_ = lean_box(v_res_1236_);
return v_r_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1238_, lean_object* v_k_1239_, lean_object* v_iniStackSz_1240_){
_start:
{
lean_object* v_stxStack_1241_; lean_object* v_lhsPrec_1242_; lean_object* v_pos_1243_; lean_object* v_cache_1244_; lean_object* v_errorMsg_1245_; lean_object* v_recoveredErrors_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1267_; 
v_stxStack_1241_ = lean_ctor_get(v_s_1238_, 0);
v_lhsPrec_1242_ = lean_ctor_get(v_s_1238_, 1);
v_pos_1243_ = lean_ctor_get(v_s_1238_, 2);
v_cache_1244_ = lean_ctor_get(v_s_1238_, 3);
v_errorMsg_1245_ = lean_ctor_get(v_s_1238_, 4);
v_recoveredErrors_1246_ = lean_ctor_get(v_s_1238_, 5);
v_isSharedCheck_1267_ = !lean_is_exclusive(v_s_1238_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1248_ = v_s_1238_;
v_isShared_1249_ = v_isSharedCheck_1267_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_recoveredErrors_1246_);
lean_inc(v_errorMsg_1245_);
lean_inc(v_cache_1244_);
lean_inc(v_pos_1243_);
lean_inc(v_lhsPrec_1242_);
lean_inc(v_stxStack_1241_);
lean_dec(v_s_1238_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1267_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1260_; uint8_t v___x_1261_; 
v___x_1260_ = lean_box(0);
v___x_1261_ = l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1245_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1241_);
v___x_1263_ = lean_nat_dec_eq(v___x_1262_, v_iniStackSz_1240_);
lean_dec(v___x_1262_);
if (v___x_1263_ == 0)
{
goto v___jp_1250_;
}
else
{
lean_object* v___x_1264_; lean_object* v_stack_1265_; lean_object* v___x_1266_; 
lean_del_object(v___x_1248_);
lean_dec(v_k_1239_);
v___x_1264_ = lean_box(0);
v_stack_1265_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1241_, v___x_1264_);
v___x_1266_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1266_, 0, v_stack_1265_);
lean_ctor_set(v___x_1266_, 1, v_lhsPrec_1242_);
lean_ctor_set(v___x_1266_, 2, v_pos_1243_);
lean_ctor_set(v___x_1266_, 3, v_cache_1244_);
lean_ctor_set(v___x_1266_, 4, v_errorMsg_1245_);
lean_ctor_set(v___x_1266_, 5, v_recoveredErrors_1246_);
return v___x_1266_;
}
}
else
{
goto v___jp_1250_;
}
v___jp_1250_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v_newNode_1254_; lean_object* v_stack_1255_; lean_object* v_stack_1256_; lean_object* v___x_1258_; 
v___x_1251_ = lean_box(2);
v___x_1252_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1241_);
v___x_1253_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1241_, v_iniStackSz_1240_, v___x_1252_);
lean_dec(v___x_1252_);
v_newNode_1254_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1254_, 0, v___x_1251_);
lean_ctor_set(v_newNode_1254_, 1, v_k_1239_);
lean_ctor_set(v_newNode_1254_, 2, v___x_1253_);
v_stack_1255_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1241_, v_iniStackSz_1240_);
v_stack_1256_ = l_Lean_Parser_SyntaxStack_push(v_stack_1255_, v_newNode_1254_);
if (v_isShared_1249_ == 0)
{
lean_ctor_set(v___x_1248_, 0, v_stack_1256_);
v___x_1258_ = v___x_1248_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_stack_1256_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v_lhsPrec_1242_);
lean_ctor_set(v_reuseFailAlloc_1259_, 2, v_pos_1243_);
lean_ctor_set(v_reuseFailAlloc_1259_, 3, v_cache_1244_);
lean_ctor_set(v_reuseFailAlloc_1259_, 4, v_errorMsg_1245_);
lean_ctor_set(v_reuseFailAlloc_1259_, 5, v_recoveredErrors_1246_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1268_, lean_object* v_k_1269_, lean_object* v_iniStackSz_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l_Lean_Parser_ParserState_mkNode(v_s_1268_, v_k_1269_, v_iniStackSz_1270_);
lean_dec(v_iniStackSz_1270_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1272_, lean_object* v_k_1273_, lean_object* v_iniStackSz_1274_){
_start:
{
lean_object* v_stxStack_1275_; lean_object* v_lhsPrec_1276_; lean_object* v_pos_1277_; lean_object* v_cache_1278_; lean_object* v_errorMsg_1279_; lean_object* v_recoveredErrors_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1295_; 
v_stxStack_1275_ = lean_ctor_get(v_s_1272_, 0);
v_lhsPrec_1276_ = lean_ctor_get(v_s_1272_, 1);
v_pos_1277_ = lean_ctor_get(v_s_1272_, 2);
v_cache_1278_ = lean_ctor_get(v_s_1272_, 3);
v_errorMsg_1279_ = lean_ctor_get(v_s_1272_, 4);
v_recoveredErrors_1280_ = lean_ctor_get(v_s_1272_, 5);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_s_1272_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1282_ = v_s_1272_;
v_isShared_1283_ = v_isSharedCheck_1295_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_recoveredErrors_1280_);
lean_inc(v_errorMsg_1279_);
lean_inc(v_cache_1278_);
lean_inc(v_pos_1277_);
lean_inc(v_lhsPrec_1276_);
lean_inc(v_stxStack_1275_);
lean_dec(v_s_1272_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1295_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v_newNode_1289_; lean_object* v_stack_1290_; lean_object* v_stack_1291_; lean_object* v___x_1293_; 
v___x_1284_ = lean_box(2);
v___x_1285_ = lean_unsigned_to_nat(1u);
v___x_1286_ = lean_nat_sub(v_iniStackSz_1274_, v___x_1285_);
v___x_1287_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1275_);
v___x_1288_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1275_, v___x_1286_, v___x_1287_);
lean_dec(v___x_1287_);
v_newNode_1289_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1289_, 0, v___x_1284_);
lean_ctor_set(v_newNode_1289_, 1, v_k_1273_);
lean_ctor_set(v_newNode_1289_, 2, v___x_1288_);
v_stack_1290_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1275_, v___x_1286_);
lean_dec(v___x_1286_);
v_stack_1291_ = l_Lean_Parser_SyntaxStack_push(v_stack_1290_, v_newNode_1289_);
if (v_isShared_1283_ == 0)
{
lean_ctor_set(v___x_1282_, 0, v_stack_1291_);
v___x_1293_ = v___x_1282_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_stack_1291_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v_lhsPrec_1276_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_pos_1277_);
lean_ctor_set(v_reuseFailAlloc_1294_, 3, v_cache_1278_);
lean_ctor_set(v_reuseFailAlloc_1294_, 4, v_errorMsg_1279_);
lean_ctor_set(v_reuseFailAlloc_1294_, 5, v_recoveredErrors_1280_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1296_, lean_object* v_k_1297_, lean_object* v_iniStackSz_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1296_, v_k_1297_, v_iniStackSz_1298_);
lean_dec(v_iniStackSz_1298_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1302_){
_start:
{
lean_object* v_errorMsg_1303_; 
v_errorMsg_1303_ = lean_ctor_get(v_s_1302_, 4);
if (lean_obj_tag(v_errorMsg_1303_) == 0)
{
lean_object* v_recoveredErrors_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
v_recoveredErrors_1304_ = lean_ctor_get(v_s_1302_, 5);
lean_inc_ref(v_recoveredErrors_1304_);
lean_dec_ref(v_s_1302_);
v___x_1305_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1306_ = l_Array_append___redArg(v_recoveredErrors_1304_, v___x_1305_);
return v___x_1306_;
}
else
{
lean_object* v_stxStack_1307_; lean_object* v_pos_1308_; lean_object* v_recoveredErrors_1309_; lean_object* v_val_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
lean_inc_ref(v_errorMsg_1303_);
v_stxStack_1307_ = lean_ctor_get(v_s_1302_, 0);
lean_inc_ref(v_stxStack_1307_);
v_pos_1308_ = lean_ctor_get(v_s_1302_, 2);
lean_inc(v_pos_1308_);
v_recoveredErrors_1309_ = lean_ctor_get(v_s_1302_, 5);
lean_inc_ref(v_recoveredErrors_1309_);
lean_dec_ref(v_s_1302_);
v_val_1310_ = lean_ctor_get(v_errorMsg_1303_, 0);
lean_inc(v_val_1310_);
lean_dec_ref_known(v_errorMsg_1303_, 1);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v_stxStack_1307_);
lean_ctor_set(v___x_1311_, 1, v_val_1310_);
v___x_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1312_, 0, v_pos_1308_);
lean_ctor_set(v___x_1312_, 1, v___x_1311_);
v___x_1313_ = lean_unsigned_to_nat(1u);
v___x_1314_ = lean_mk_empty_array_with_capacity(v___x_1313_);
v___x_1315_ = lean_array_push(v___x_1314_, v___x_1312_);
v___x_1316_ = l_Array_append___redArg(v_recoveredErrors_1309_, v___x_1315_);
lean_dec_ref(v___x_1315_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1317_, lean_object* v_e_1318_){
_start:
{
lean_object* v_stxStack_1319_; lean_object* v_lhsPrec_1320_; lean_object* v_pos_1321_; lean_object* v_cache_1322_; lean_object* v_recoveredErrors_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1331_; 
v_stxStack_1319_ = lean_ctor_get(v_s_1317_, 0);
v_lhsPrec_1320_ = lean_ctor_get(v_s_1317_, 1);
v_pos_1321_ = lean_ctor_get(v_s_1317_, 2);
v_cache_1322_ = lean_ctor_get(v_s_1317_, 3);
v_recoveredErrors_1323_ = lean_ctor_get(v_s_1317_, 5);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_s_1317_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v_s_1317_, 4);
lean_dec(v_unused_1332_);
v___x_1325_ = v_s_1317_;
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_recoveredErrors_1323_);
lean_inc(v_cache_1322_);
lean_inc(v_pos_1321_);
lean_inc(v_lhsPrec_1320_);
lean_inc(v_stxStack_1319_);
lean_dec(v_s_1317_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1331_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1329_; 
v___x_1327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1327_, 0, v_e_1318_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 4, v___x_1327_);
v___x_1329_ = v___x_1325_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_stxStack_1319_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_lhsPrec_1320_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_pos_1321_);
lean_ctor_set(v_reuseFailAlloc_1330_, 3, v_cache_1322_);
lean_ctor_set(v_reuseFailAlloc_1330_, 4, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1330_, 5, v_recoveredErrors_1323_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1333_, lean_object* v_msg_1334_){
_start:
{
lean_object* v_stxStack_1335_; lean_object* v_lhsPrec_1336_; lean_object* v_pos_1337_; lean_object* v_cache_1338_; lean_object* v_recoveredErrors_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1353_; 
v_stxStack_1335_ = lean_ctor_get(v_s_1333_, 0);
v_lhsPrec_1336_ = lean_ctor_get(v_s_1333_, 1);
v_pos_1337_ = lean_ctor_get(v_s_1333_, 2);
v_cache_1338_ = lean_ctor_get(v_s_1333_, 3);
v_recoveredErrors_1339_ = lean_ctor_get(v_s_1333_, 5);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_s_1333_);
if (v_isSharedCheck_1353_ == 0)
{
lean_object* v_unused_1354_; 
v_unused_1354_ = lean_ctor_get(v_s_1333_, 4);
lean_dec(v_unused_1354_);
v___x_1341_ = v_s_1333_;
v_isShared_1342_ = v_isSharedCheck_1353_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_recoveredErrors_1339_);
lean_inc(v_cache_1338_);
lean_inc(v_pos_1337_);
lean_inc(v_lhsPrec_1336_);
lean_inc(v_stxStack_1335_);
lean_dec(v_s_1333_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1353_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1343_ = lean_box(0);
v___x_1344_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1346_, 0, v_msg_1334_);
lean_ctor_set(v___x_1346_, 1, v___x_1345_);
v___x_1347_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1343_);
lean_ctor_set(v___x_1347_, 1, v___x_1344_);
lean_ctor_set(v___x_1347_, 2, v___x_1346_);
v___x_1348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 4, v___x_1348_);
v___x_1350_ = v___x_1341_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_stxStack_1335_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v_lhsPrec_1336_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_pos_1337_);
lean_ctor_set(v_reuseFailAlloc_1352_, 3, v_cache_1338_);
lean_ctor_set(v_reuseFailAlloc_1352_, 4, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1352_, 5, v_recoveredErrors_1339_);
v___x_1350_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1350_, v___x_1343_);
return v___x_1351_;
}
}
}
}
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1355_, lean_object* v_msg_1356_, lean_object* v_expected_1357_, uint8_t v_pushMissing_1358_){
_start:
{
lean_object* v_stxStack_1359_; lean_object* v_lhsPrec_1360_; lean_object* v_pos_1361_; lean_object* v_cache_1362_; lean_object* v_recoveredErrors_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1374_; 
v_stxStack_1359_ = lean_ctor_get(v_s_1355_, 0);
v_lhsPrec_1360_ = lean_ctor_get(v_s_1355_, 1);
v_pos_1361_ = lean_ctor_get(v_s_1355_, 2);
v_cache_1362_ = lean_ctor_get(v_s_1355_, 3);
v_recoveredErrors_1363_ = lean_ctor_get(v_s_1355_, 5);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_s_1355_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v_s_1355_, 4);
lean_dec(v_unused_1375_);
v___x_1365_ = v_s_1355_;
v_isShared_1366_ = v_isSharedCheck_1374_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_recoveredErrors_1363_);
lean_inc(v_cache_1362_);
lean_inc(v_pos_1361_);
lean_inc(v_lhsPrec_1360_);
lean_inc(v_stxStack_1359_);
lean_dec(v_s_1355_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1374_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v_s_1371_; 
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1368_, 0, v___x_1367_);
lean_ctor_set(v___x_1368_, 1, v_msg_1356_);
lean_ctor_set(v___x_1368_, 2, v_expected_1357_);
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1368_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 4, v___x_1369_);
v_s_1371_ = v___x_1365_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_stxStack_1359_);
lean_ctor_set(v_reuseFailAlloc_1373_, 1, v_lhsPrec_1360_);
lean_ctor_set(v_reuseFailAlloc_1373_, 2, v_pos_1361_);
lean_ctor_set(v_reuseFailAlloc_1373_, 3, v_cache_1362_);
lean_ctor_set(v_reuseFailAlloc_1373_, 4, v___x_1369_);
lean_ctor_set(v_reuseFailAlloc_1373_, 5, v_recoveredErrors_1363_);
v_s_1371_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
if (v_pushMissing_1358_ == 0)
{
return v_s_1371_;
}
else
{
lean_object* v___x_1372_; 
v___x_1372_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1371_, v___x_1367_);
return v___x_1372_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Parser_ParserState_mkUnexpectedError_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1355_ = stack[0].m_obj;
lean_object* v_msg_1356_ = stack[1].m_obj;
lean_object* v_expected_1357_ = stack[2].m_obj;
uint8_t v_pushMissing_1358_ = stack[3].m_num;
lean_object* v_res_1376_;
v_res_1376_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1355_, v_msg_1356_, v_expected_1357_, v_pushMissing_1358_);
stack->m_obj
 = v_res_1376_;
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1377_, lean_object* v_msg_1378_, lean_object* v_expected_1379_, lean_object* v_pushMissing_1380_){
_start:
{
uint8_t v_pushMissing_boxed_1381_; lean_object* v_res_1382_; 
v_pushMissing_boxed_1381_ = lean_unbox(v_pushMissing_1380_);
v_res_1382_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1377_, v_msg_1378_, v_expected_1379_, v_pushMissing_boxed_1381_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1384_, lean_object* v_expected_1385_){
_start:
{
lean_object* v___x_1386_; uint8_t v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1387_ = 1;
v___x_1388_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1384_, v___x_1386_, v_expected_1385_, v___x_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1389_, lean_object* v_ex_1390_, lean_object* v_pos_1391_, lean_object* v_initStackSz_x3f_1392_){
_start:
{
lean_object* v_s_1394_; lean_object* v_s_1413_; 
v_s_1413_ = l_Lean_Parser_ParserState_setPos(v_s_1389_, v_pos_1391_);
if (lean_obj_tag(v_initStackSz_x3f_1392_) == 1)
{
lean_object* v_val_1414_; lean_object* v_s_1415_; 
v_val_1414_ = lean_ctor_get(v_initStackSz_x3f_1392_, 0);
v_s_1415_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1413_, v_val_1414_);
v_s_1394_ = v_s_1415_;
goto v___jp_1393_;
}
else
{
v_s_1394_ = v_s_1413_;
goto v___jp_1393_;
}
v___jp_1393_:
{
lean_object* v_stxStack_1395_; lean_object* v_lhsPrec_1396_; lean_object* v_pos_1397_; lean_object* v_cache_1398_; lean_object* v_recoveredErrors_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1411_; 
v_stxStack_1395_ = lean_ctor_get(v_s_1394_, 0);
v_lhsPrec_1396_ = lean_ctor_get(v_s_1394_, 1);
v_pos_1397_ = lean_ctor_get(v_s_1394_, 2);
v_cache_1398_ = lean_ctor_get(v_s_1394_, 3);
v_recoveredErrors_1399_ = lean_ctor_get(v_s_1394_, 5);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_s_1394_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v_s_1394_, 4);
lean_dec(v_unused_1412_);
v___x_1401_ = v_s_1394_;
v_isShared_1402_ = v_isSharedCheck_1411_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_recoveredErrors_1399_);
lean_inc(v_cache_1398_);
lean_inc(v_pos_1397_);
lean_inc(v_lhsPrec_1396_);
lean_inc(v_stxStack_1395_);
lean_dec(v_s_1394_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1411_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v_s_1408_; 
v___x_1403_ = lean_box(0);
v___x_1404_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1403_);
lean_ctor_set(v___x_1405_, 1, v___x_1404_);
lean_ctor_set(v___x_1405_, 2, v_ex_1390_);
v___x_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
if (v_isShared_1402_ == 0)
{
lean_ctor_set(v___x_1401_, 4, v___x_1406_);
v_s_1408_ = v___x_1401_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_stxStack_1395_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_lhsPrec_1396_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v_pos_1397_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v_cache_1398_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1410_, 5, v_recoveredErrors_1399_);
v_s_1408_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1408_, v___x_1403_);
return v___x_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1416_, lean_object* v_ex_1417_, lean_object* v_pos_1418_, lean_object* v_initStackSz_x3f_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1416_, v_ex_1417_, v_pos_1418_, v_initStackSz_x3f_1419_);
lean_dec(v_initStackSz_x3f_1419_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1421_, lean_object* v_msg_1422_, lean_object* v_pos_1423_, lean_object* v_initStackSz_x3f_1424_){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1425_ = lean_box(0);
v___x_1426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1426_, 0, v_msg_1422_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1421_, v___x_1426_, v_pos_1423_, v_initStackSz_x3f_1424_);
return v___x_1427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1428_, lean_object* v_msg_1429_, lean_object* v_pos_1430_, lean_object* v_initStackSz_x3f_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1428_, v_msg_1429_, v_pos_1430_, v_initStackSz_x3f_1431_);
lean_dec(v_initStackSz_x3f_1431_);
return v_res_1432_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1433_){
_start:
{
lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_panic_fn_borrowed(v___x_1434_, v_msg_1433_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1439_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1440_ = lean_unsigned_to_nat(14u);
v___x_1441_ = lean_unsigned_to_nat(22u);
v___x_1442_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1443_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1444_ = l_mkPanicMessageWithDecl(v___x_1443_, v___x_1442_, v___x_1441_, v___x_1440_, v___x_1439_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1445_, lean_object* v_ex_1446_, lean_object* v_iniPos_1447_){
_start:
{
lean_object* v_stxStack_1448_; lean_object* v_tk_1449_; lean_object* v___y_1451_; lean_object* v___x_1472_; uint8_t v___x_1473_; 
v_stxStack_1448_ = lean_ctor_get(v_s_1445_, 0);
v_tk_1449_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1448_);
v___x_1472_ = lean_unsigned_to_nat(1u);
v___x_1473_ = lean_nat_dec_le(v___x_1472_, v_iniPos_1447_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
lean_dec(v_iniPos_1447_);
v___x_1474_ = l_Lean_Syntax_getPos_x3f(v_tk_1449_, v___x_1473_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1476_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1475_);
v___y_1451_ = v___x_1476_;
goto v___jp_1450_;
}
else
{
lean_object* v_val_1477_; 
v_val_1477_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_val_1477_);
lean_dec_ref_known(v___x_1474_, 1);
v___y_1451_ = v_val_1477_;
goto v___jp_1450_;
}
}
else
{
v___y_1451_ = v_iniPos_1447_;
goto v___jp_1450_;
}
v___jp_1450_:
{
lean_object* v_s_1452_; lean_object* v_stxStack_1453_; lean_object* v_lhsPrec_1454_; lean_object* v_pos_1455_; lean_object* v_cache_1456_; lean_object* v_recoveredErrors_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1470_; 
v_s_1452_ = l_Lean_Parser_ParserState_setPos(v_s_1445_, v___y_1451_);
v_stxStack_1453_ = lean_ctor_get(v_s_1452_, 0);
v_lhsPrec_1454_ = lean_ctor_get(v_s_1452_, 1);
v_pos_1455_ = lean_ctor_get(v_s_1452_, 2);
v_cache_1456_ = lean_ctor_get(v_s_1452_, 3);
v_recoveredErrors_1457_ = lean_ctor_get(v_s_1452_, 5);
v_isSharedCheck_1470_ = !lean_is_exclusive(v_s_1452_);
if (v_isSharedCheck_1470_ == 0)
{
lean_object* v_unused_1471_; 
v_unused_1471_ = lean_ctor_get(v_s_1452_, 4);
lean_dec(v_unused_1471_);
v___x_1459_ = v_s_1452_;
v_isShared_1460_ = v_isSharedCheck_1470_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_recoveredErrors_1457_);
lean_inc(v_cache_1456_);
lean_inc(v_pos_1455_);
lean_inc(v_lhsPrec_1454_);
lean_inc(v_stxStack_1453_);
lean_dec(v_s_1452_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1470_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v_s_1465_; 
v___x_1461_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1462_, 0, v_tk_1449_);
lean_ctor_set(v___x_1462_, 1, v___x_1461_);
lean_ctor_set(v___x_1462_, 2, v_ex_1446_);
v___x_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1462_);
if (v_isShared_1460_ == 0)
{
lean_ctor_set(v___x_1459_, 4, v___x_1463_);
v_s_1465_ = v___x_1459_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_stxStack_1453_);
lean_ctor_set(v_reuseFailAlloc_1469_, 1, v_lhsPrec_1454_);
lean_ctor_set(v_reuseFailAlloc_1469_, 2, v_pos_1455_);
lean_ctor_set(v_reuseFailAlloc_1469_, 3, v_cache_1456_);
lean_ctor_set(v_reuseFailAlloc_1469_, 4, v___x_1463_);
lean_ctor_set(v_reuseFailAlloc_1469_, 5, v_recoveredErrors_1457_);
v_s_1465_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = l_Lean_Parser_ParserState_popSyntax(v_s_1465_);
v___x_1467_ = lean_box(0);
v___x_1468_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1466_, v___x_1467_);
return v___x_1468_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1478_, lean_object* v_msg_1479_, lean_object* v_iniPos_1480_){
_start:
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v___x_1481_ = lean_box(0);
v___x_1482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1482_, 0, v_msg_1479_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v___x_1483_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1478_, v___x_1482_, v_iniPos_1480_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1484_, lean_object* v_msg_1485_, lean_object* v_pos_1486_){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1487_ = l_Lean_Parser_ParserState_setPos(v_s_1484_, v_pos_1486_);
v___x_1488_ = lean_box(0);
v___x_1489_ = 1;
v___x_1490_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1487_, v_msg_1485_, v___x_1488_, v___x_1489_);
return v___x_1490_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1492_, lean_object* v_as_1493_, size_t v_sz_1494_, size_t v_i_1495_, lean_object* v_b_1496_){
_start:
{
uint8_t v___x_1497_; 
v___x_1497_ = lean_usize_dec_lt(v_i_1495_, v_sz_1494_);
if (v___x_1497_ == 0)
{
lean_dec_ref(v_ctx_1492_);
return v_b_1496_;
}
else
{
lean_object* v_a_1498_; lean_object* v_snd_1499_; lean_object* v_fst_1500_; lean_object* v_snd_1501_; lean_object* v_errStr_1503_; lean_object* v_errStr_1514_; uint8_t v___x_1515_; 
v_a_1498_ = lean_array_uget_borrowed(v_as_1493_, v_i_1495_);
v_snd_1499_ = lean_ctor_get(v_a_1498_, 1);
v_fst_1500_ = lean_ctor_get(v_a_1498_, 0);
v_snd_1501_ = lean_ctor_get(v_snd_1499_, 1);
v_errStr_1514_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1515_ = lean_string_dec_eq(v_b_1496_, v_errStr_1514_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1517_ = lean_string_append(v_b_1496_, v___x_1516_);
v_errStr_1503_ = v___x_1517_;
goto v___jp_1502_;
}
else
{
v_errStr_1503_ = v_b_1496_;
goto v___jp_1502_;
}
v___jp_1502_:
{
lean_object* v_fileName_1504_; lean_object* v_fileMap_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; size_t v___x_1511_; size_t v___x_1512_; 
v_fileName_1504_ = lean_ctor_get(v_ctx_1492_, 1);
v_fileMap_1505_ = lean_ctor_get(v_ctx_1492_, 2);
lean_inc_ref(v_fileMap_1505_);
v___x_1506_ = l_Lean_FileMap_toPosition(v_fileMap_1505_, v_fst_1500_);
lean_inc(v_snd_1501_);
v___x_1507_ = l_Lean_Parser_Error_toString(v_snd_1501_);
v___x_1508_ = lean_box(0);
lean_inc_ref(v_fileName_1504_);
v___x_1509_ = l_Lean_mkErrorStringWithPos(v_fileName_1504_, v___x_1506_, v___x_1507_, v___x_1508_, v___x_1508_, v___x_1508_);
lean_dec_ref(v___x_1507_);
v___x_1510_ = lean_string_append(v_errStr_1503_, v___x_1509_);
lean_dec_ref(v___x_1509_);
v___x_1511_ = ((size_t)1ULL);
v___x_1512_ = lean_usize_add(v_i_1495_, v___x_1511_);
v_i_1495_ = v___x_1512_;
v_b_1496_ = v___x_1510_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ctx_1492_ = stack[0].m_obj;
lean_object* v_as_1493_ = stack[1].m_obj;
size_t v_sz_1494_ = stack[2].m_num;
size_t v_i_1495_ = stack[3].m_num;
lean_object* v_b_1496_ = stack[4].m_obj;
lean_object* v_res_1518_;
v_res_1518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1492_, v_as_1493_, v_sz_1494_, v_i_1495_, v_b_1496_);
stack->m_obj
 = v_res_1518_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1519_, lean_object* v_as_1520_, lean_object* v_sz_1521_, lean_object* v_i_1522_, lean_object* v_b_1523_){
_start:
{
size_t v_sz_boxed_1524_; size_t v_i_boxed_1525_; lean_object* v_res_1526_; 
v_sz_boxed_1524_ = lean_unbox_usize(v_sz_1521_);
lean_dec(v_sz_1521_);
v_i_boxed_1525_ = lean_unbox_usize(v_i_1522_);
lean_dec(v_i_1522_);
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1519_, v_as_1520_, v_sz_boxed_1524_, v_i_boxed_1525_, v_b_1523_);
lean_dec_ref(v_as_1520_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1527_, lean_object* v_s_1528_){
_start:
{
lean_object* v_errStr_1529_; lean_object* v___x_1530_; size_t v_sz_1531_; size_t v___x_1532_; lean_object* v___x_1533_; 
v_errStr_1529_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1530_ = l_Lean_Parser_ParserState_allErrors(v_s_1528_);
v_sz_1531_ = lean_array_size(v___x_1530_);
v___x_1532_ = ((size_t)0ULL);
v___x_1533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1527_, v___x_1530_, v_sz_1531_, v___x_1532_, v_errStr_1529_);
lean_dec_ref(v___x_1530_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1534_, lean_object* v_s_1535_){
_start:
{
lean_inc_ref(v_s_1535_);
return v_s_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1536_, lean_object* v_s_1537_){
_start:
{
lean_object* v_res_1538_; 
v_res_1538_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1536_, v_s_1537_);
lean_dec_ref(v_s_1537_);
lean_dec_ref(v_x_1536_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___impl(lean_object* v_x_1541_){
_start:
{
lean_object* v___x_1542_; 
v___x_1542_ = lean_obj_tag_nat(v_x_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___impl___boxed(lean_object* v_x_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_Parser_FirstTokens_ctorIdx___impl(v_x_1543_);
lean_dec(v_x_1543_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1545_, lean_object* v_k_1546_){
_start:
{
switch(lean_obj_tag(v_t_1545_))
{
case 2:
{
lean_object* v_a_1547_; lean_object* v___x_1548_; 
v_a_1547_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_a_1547_);
lean_dec_ref_known(v_t_1545_, 1);
v___x_1548_ = lean_apply_1(v_k_1546_, v_a_1547_);
return v___x_1548_;
}
case 3:
{
lean_object* v_a_1549_; lean_object* v___x_1550_; 
v_a_1549_ = lean_ctor_get(v_t_1545_, 0);
lean_inc(v_a_1549_);
lean_dec_ref_known(v_t_1545_, 1);
v___x_1550_ = lean_apply_1(v_k_1546_, v_a_1549_);
return v___x_1550_;
}
default: 
{
lean_dec(v_t_1545_);
return v_k_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1551_, lean_object* v_ctorIdx_1552_, lean_object* v_t_1553_, lean_object* v_h_1554_, lean_object* v_k_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1553_, v_k_1555_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1557_, lean_object* v_ctorIdx_1558_, lean_object* v_t_1559_, lean_object* v_h_1560_, lean_object* v_k_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1557_, v_ctorIdx_1558_, v_t_1559_, v_h_1560_, v_k_1561_);
lean_dec(v_ctorIdx_1558_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1563_, lean_object* v_epsilon_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1563_, v_epsilon_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1566_, lean_object* v_t_1567_, lean_object* v_h_1568_, lean_object* v_epsilon_1569_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1567_, v_epsilon_1569_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1571_, lean_object* v_unknown_1572_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1571_, v_unknown_1572_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1574_, lean_object* v_t_1575_, lean_object* v_h_1576_, lean_object* v_unknown_1577_){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1575_, v_unknown_1577_);
return v___x_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1579_, lean_object* v_tokens_1580_){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1579_, v_tokens_1580_);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1582_, lean_object* v_t_1583_, lean_object* v_h_1584_, lean_object* v_tokens_1585_){
_start:
{
lean_object* v___x_1586_; 
v___x_1586_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1583_, v_tokens_1585_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1587_, lean_object* v_optTokens_1588_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1587_, v_optTokens_1588_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1590_, lean_object* v_t_1591_, lean_object* v_h_1592_, lean_object* v_optTokens_1593_){
_start:
{
lean_object* v___x_1594_; 
v___x_1594_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1591_, v_optTokens_1593_);
return v___x_1594_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_box(0);
return v___x_1595_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_box(0);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1597_, lean_object* v_x_1598_){
_start:
{
switch(lean_obj_tag(v_x_1597_))
{
case 0:
{
return v_x_1598_;
}
case 3:
{
switch(lean_obj_tag(v_x_1598_))
{
case 3:
{
lean_object* v_a_1599_; lean_object* v_a_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1608_; 
v_a_1599_ = lean_ctor_get(v_x_1597_, 0);
lean_inc(v_a_1599_);
lean_dec_ref_known(v_x_1597_, 1);
v_a_1600_ = lean_ctor_get(v_x_1598_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_x_1598_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1602_ = v_x_1598_;
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
else
{
lean_inc(v_a_1600_);
lean_dec(v_x_1598_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = l_List_appendTR___redArg(v_a_1599_, v_a_1600_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 0, v___x_1604_);
v___x_1606_ = v___x_1602_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v___x_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
case 2:
{
lean_object* v_a_1609_; lean_object* v_a_1610_; lean_object* v___x_1612_; uint8_t v_isShared_1613_; uint8_t v_isSharedCheck_1618_; 
v_a_1609_ = lean_ctor_get(v_x_1597_, 0);
lean_inc(v_a_1609_);
lean_dec_ref_known(v_x_1597_, 1);
v_a_1610_ = lean_ctor_get(v_x_1598_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v_x_1598_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1612_ = v_x_1598_;
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
else
{
lean_inc(v_a_1610_);
lean_dec(v_x_1598_);
v___x_1612_ = lean_box(0);
v_isShared_1613_ = v_isSharedCheck_1618_;
goto v_resetjp_1611_;
}
v_resetjp_1611_:
{
lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1614_ = l_List_appendTR___redArg(v_a_1609_, v_a_1610_);
if (v_isShared_1613_ == 0)
{
lean_ctor_set(v___x_1612_, 0, v___x_1614_);
v___x_1616_ = v___x_1612_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
case 1:
{
lean_dec_ref_known(v_x_1597_, 1);
return v_x_1598_;
}
default: 
{
lean_dec(v_x_1598_);
return v_x_1597_;
}
}
}
default: 
{
lean_dec(v_x_1598_);
return v_x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1619_){
_start:
{
if (lean_obj_tag(v_x_1619_) == 2)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1627_; 
v_a_1620_ = lean_ctor_get(v_x_1619_, 0);
v_isSharedCheck_1627_ = !lean_is_exclusive(v_x_1619_);
if (v_isSharedCheck_1627_ == 0)
{
v___x_1622_ = v_x_1619_;
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v_x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1627_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v___x_1625_; 
if (v_isShared_1623_ == 0)
{
lean_ctor_set_tag(v___x_1622_, 3);
v___x_1625_ = v___x_1622_;
goto v_reusejp_1624_;
}
else
{
lean_object* v_reuseFailAlloc_1626_; 
v_reuseFailAlloc_1626_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
v___x_1625_ = v_reuseFailAlloc_1626_;
goto v_reusejp_1624_;
}
v_reusejp_1624_:
{
return v___x_1625_;
}
}
}
else
{
return v_x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1628_, lean_object* v_x_1629_){
_start:
{
lean_object* v_s_u2081_1631_; lean_object* v_s_u2082_1632_; 
switch(lean_obj_tag(v_x_1628_))
{
case 0:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1629_);
return v___x_1635_;
}
case 2:
{
switch(lean_obj_tag(v_x_1629_))
{
case 0:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1628_);
return v___x_1636_;
}
case 2:
{
lean_object* v_a_1637_; lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1646_; 
v_a_1637_ = lean_ctor_get(v_x_1628_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v_x_1628_, 1);
v_a_1638_ = lean_ctor_get(v_x_1629_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_x_1629_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1640_ = v_x_1629_;
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v_x_1629_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1646_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = l_List_appendTR___redArg(v_a_1637_, v_a_1638_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
case 3:
{
lean_object* v_a_1647_; lean_object* v_a_1648_; 
v_a_1647_ = lean_ctor_get(v_x_1628_, 0);
lean_inc(v_a_1647_);
lean_dec_ref_known(v_x_1628_, 1);
v_a_1648_ = lean_ctor_get(v_x_1629_, 0);
lean_inc(v_a_1648_);
lean_dec_ref_known(v_x_1629_, 1);
v_s_u2081_1631_ = v_a_1647_;
v_s_u2082_1632_ = v_a_1648_;
goto v___jp_1630_;
}
default: 
{
lean_object* v___x_1649_; 
lean_dec_ref_known(v_x_1628_, 1);
lean_dec(v_x_1629_);
v___x_1649_ = lean_box(1);
return v___x_1649_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1629_))
{
case 0:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1628_);
return v___x_1650_;
}
case 3:
{
lean_object* v_a_1651_; lean_object* v_a_1652_; 
v_a_1651_ = lean_ctor_get(v_x_1628_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v_x_1628_, 1);
v_a_1652_ = lean_ctor_get(v_x_1629_, 0);
lean_inc(v_a_1652_);
lean_dec_ref_known(v_x_1629_, 1);
v_s_u2081_1631_ = v_a_1651_;
v_s_u2082_1632_ = v_a_1652_;
goto v___jp_1630_;
}
case 2:
{
lean_object* v_a_1653_; lean_object* v_a_1654_; 
v_a_1653_ = lean_ctor_get(v_x_1628_, 0);
lean_inc(v_a_1653_);
lean_dec_ref_known(v_x_1628_, 1);
v_a_1654_ = lean_ctor_get(v_x_1629_, 0);
lean_inc(v_a_1654_);
lean_dec_ref_known(v_x_1629_, 1);
v_s_u2081_1631_ = v_a_1653_;
v_s_u2082_1632_ = v_a_1654_;
goto v___jp_1630_;
}
default: 
{
lean_object* v___x_1655_; 
lean_dec_ref_known(v_x_1628_, 1);
lean_dec(v_x_1629_);
v___x_1655_ = lean_box(1);
return v___x_1655_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1629_) == 0)
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1628_);
return v___x_1656_;
}
else
{
lean_object* v___x_1657_; 
lean_dec(v_x_1629_);
lean_dec(v_x_1628_);
v___x_1657_ = lean_box(1);
return v___x_1657_;
}
}
}
v___jp_1630_:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = l_List_appendTR___redArg(v_s_u2081_1631_, v_s_u2082_1632_);
v___x_1634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1634_, 0, v___x_1633_);
return v___x_1634_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1658_, lean_object* v_x_1659_){
_start:
{
if (lean_obj_tag(v_x_1659_) == 0)
{
return v_x_1658_;
}
else
{
lean_object* v_head_1660_; lean_object* v_tail_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_head_1660_ = lean_ctor_get(v_x_1659_, 0);
v_tail_1661_ = lean_ctor_get(v_x_1659_, 1);
v___x_1662_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1663_ = lean_string_append(v_x_1658_, v___x_1662_);
v___x_1664_ = lean_string_append(v___x_1663_, v_head_1660_);
v_x_1658_ = v___x_1664_;
v_x_1659_ = v_tail_1661_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1666_, v_x_1667_);
lean_dec(v_x_1667_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1672_){
_start:
{
if (lean_obj_tag(v_x_1672_) == 0)
{
lean_object* v___x_1673_; 
v___x_1673_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1673_;
}
else
{
lean_object* v_tail_1674_; 
v_tail_1674_ = lean_ctor_get(v_x_1672_, 1);
if (lean_obj_tag(v_tail_1674_) == 0)
{
lean_object* v_head_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; 
v_head_1675_ = lean_ctor_get(v_x_1672_, 0);
v___x_1676_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1677_ = lean_string_append(v___x_1676_, v_head_1675_);
v___x_1678_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1679_ = lean_string_append(v___x_1677_, v___x_1678_);
return v___x_1679_;
}
else
{
lean_object* v_head_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint32_t v___x_1684_; lean_object* v___x_1685_; 
v_head_1680_ = lean_ctor_get(v_x_1672_, 0);
v___x_1681_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1682_ = lean_string_append(v___x_1681_, v_head_1680_);
v___x_1683_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1682_, v_tail_1674_);
v___x_1684_ = 93;
v___x_1685_ = lean_string_push(v___x_1683_, v___x_1684_);
return v___x_1685_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1686_){
_start:
{
lean_object* v_res_1687_; 
v_res_1687_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1686_);
lean_dec(v_x_1686_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1691_){
_start:
{
switch(lean_obj_tag(v_x_1691_))
{
case 0:
{
lean_object* v___x_1692_; 
v___x_1692_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1692_;
}
case 1:
{
lean_object* v___x_1693_; 
v___x_1693_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1693_;
}
case 2:
{
lean_object* v_a_1694_; lean_object* v___x_1695_; 
v_a_1694_ = lean_ctor_get(v_x_1691_, 0);
v___x_1695_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1694_);
return v___x_1695_;
}
default: 
{
lean_object* v_a_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; 
v_a_1696_ = lean_ctor_get(v_x_1691_, 0);
v___x_1697_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1698_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1696_);
v___x_1699_ = lean_string_append(v___x_1697_, v___x_1698_);
lean_dec_ref(v___x_1698_);
return v___x_1699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_Parser_FirstTokens_toStr(v_x_1700_);
lean_dec(v_x_1700_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v___y_1704_){
_start:
{
lean_inc(v___y_1704_);
return v___y_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_1705_);
lean_dec(v___y_1705_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v___y_1707_){
_start:
{
lean_inc_ref(v___y_1707_);
return v___y_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v___y_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_1708_);
lean_dec_ref(v___y_1708_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1723_, lean_object* v_p_1724_){
_start:
{
lean_object* v_info_1725_; lean_object* v_fn_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1734_; 
v_info_1725_ = lean_ctor_get(v_p_1724_, 0);
v_fn_1726_ = lean_ctor_get(v_p_1724_, 1);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_p_1724_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1728_ = v_p_1724_;
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_fn_1726_);
lean_inc(v_info_1725_);
lean_dec(v_p_1724_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1734_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1730_; lean_object* v___x_1732_; 
v___x_1730_ = lean_apply_1(v_f_1723_, v_fn_1726_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v___x_1730_);
v___x_1732_ = v___x_1728_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_info_1725_);
lean_ctor_set(v_reuseFailAlloc_1733_, 1, v___x_1730_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1735_, lean_object* v_p_1736_, lean_object* v_c_1737_, lean_object* v_s_1738_){
_start:
{
lean_object* v_toInputContext_1739_; lean_object* v_toParserModuleContext_1740_; lean_object* v_toCacheableParserContext_1741_; lean_object* v_tokens_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1751_; 
v_toInputContext_1739_ = lean_ctor_get(v_c_1737_, 0);
v_toParserModuleContext_1740_ = lean_ctor_get(v_c_1737_, 1);
v_toCacheableParserContext_1741_ = lean_ctor_get(v_c_1737_, 2);
v_tokens_1742_ = lean_ctor_get(v_c_1737_, 3);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_c_1737_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1744_ = v_c_1737_;
v_isShared_1745_ = v_isSharedCheck_1751_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_tokens_1742_);
lean_inc(v_toCacheableParserContext_1741_);
lean_inc(v_toParserModuleContext_1740_);
lean_inc(v_toInputContext_1739_);
lean_dec(v_c_1737_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1751_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1746_; lean_object* v___x_1748_; 
v___x_1746_ = lean_apply_1(v_f_1735_, v_toCacheableParserContext_1741_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 2, v___x_1746_);
v___x_1748_ = v___x_1744_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_toInputContext_1739_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_toParserModuleContext_1740_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v___x_1746_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v_tokens_1742_);
v___x_1748_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
lean_object* v___x_1749_; 
v___x_1749_ = lean_apply_2(v_p_1736_, v___x_1748_, v_s_1738_);
return v___x_1749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1752_, lean_object* v_p_1753_){
_start:
{
lean_object* v_info_1754_; lean_object* v_fn_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1763_; 
v_info_1754_ = lean_ctor_get(v_p_1753_, 0);
v_fn_1755_ = lean_ctor_get(v_p_1753_, 1);
v_isSharedCheck_1763_ = !lean_is_exclusive(v_p_1753_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1757_ = v_p_1753_;
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_fn_1755_);
lean_inc(v_info_1754_);
lean_dec(v_p_1753_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1763_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1759_; lean_object* v___x_1761_; 
v___x_1759_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1759_, 0, v_f_1752_);
lean_closure_set(v___x_1759_, 1, v_fn_1755_);
if (v_isShared_1758_ == 0)
{
lean_ctor_set(v___x_1757_, 1, v___x_1759_);
v___x_1761_ = v___x_1757_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_info_1754_);
lean_ctor_set(v_reuseFailAlloc_1762_, 1, v___x_1759_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1764_, lean_object* v_p_1765_, lean_object* v_c_1766_, lean_object* v_s_1767_){
_start:
{
lean_object* v_stxStack_1768_; lean_object* v_lhsPrec_1769_; lean_object* v_pos_1770_; lean_object* v_cache_1771_; lean_object* v_errorMsg_1772_; lean_object* v_recoveredErrors_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1812_; 
v_stxStack_1768_ = lean_ctor_get(v_s_1767_, 0);
v_lhsPrec_1769_ = lean_ctor_get(v_s_1767_, 1);
v_pos_1770_ = lean_ctor_get(v_s_1767_, 2);
v_cache_1771_ = lean_ctor_get(v_s_1767_, 3);
v_errorMsg_1772_ = lean_ctor_get(v_s_1767_, 4);
v_recoveredErrors_1773_ = lean_ctor_get(v_s_1767_, 5);
v_isSharedCheck_1812_ = !lean_is_exclusive(v_s_1767_);
if (v_isSharedCheck_1812_ == 0)
{
v___x_1775_ = v_s_1767_;
v_isShared_1776_ = v_isSharedCheck_1812_;
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
v_isShared_1776_ = v_isSharedCheck_1812_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v_raw_1777_; lean_object* v_drop_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1811_; 
v_raw_1777_ = lean_ctor_get(v_stxStack_1768_, 0);
v_drop_1778_ = lean_ctor_get(v_stxStack_1768_, 1);
v_isSharedCheck_1811_ = !lean_is_exclusive(v_stxStack_1768_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1780_ = v_stxStack_1768_;
v_isShared_1781_ = v_isSharedCheck_1811_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_drop_1778_);
lean_inc(v_raw_1777_);
lean_dec(v_stxStack_1768_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1811_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 1, v_drop_1764_);
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_raw_1777_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_drop_1764_);
v___x_1783_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
lean_object* v___x_1785_; 
if (v_isShared_1776_ == 0)
{
lean_ctor_set(v___x_1775_, 0, v___x_1783_);
v___x_1785_ = v___x_1775_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1783_);
lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_lhsPrec_1769_);
lean_ctor_set(v_reuseFailAlloc_1809_, 2, v_pos_1770_);
lean_ctor_set(v_reuseFailAlloc_1809_, 3, v_cache_1771_);
lean_ctor_set(v_reuseFailAlloc_1809_, 4, v_errorMsg_1772_);
lean_ctor_set(v_reuseFailAlloc_1809_, 5, v_recoveredErrors_1773_);
v___x_1785_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
lean_object* v_s_1786_; lean_object* v_stxStack_1787_; lean_object* v_lhsPrec_1788_; lean_object* v_pos_1789_; lean_object* v_cache_1790_; lean_object* v_errorMsg_1791_; lean_object* v_recoveredErrors_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1808_; 
v_s_1786_ = lean_apply_2(v_p_1765_, v_c_1766_, v___x_1785_);
v_stxStack_1787_ = lean_ctor_get(v_s_1786_, 0);
v_lhsPrec_1788_ = lean_ctor_get(v_s_1786_, 1);
v_pos_1789_ = lean_ctor_get(v_s_1786_, 2);
v_cache_1790_ = lean_ctor_get(v_s_1786_, 3);
v_errorMsg_1791_ = lean_ctor_get(v_s_1786_, 4);
v_recoveredErrors_1792_ = lean_ctor_get(v_s_1786_, 5);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_s_1786_);
if (v_isSharedCheck_1808_ == 0)
{
v___x_1794_ = v_s_1786_;
v_isShared_1795_ = v_isSharedCheck_1808_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_recoveredErrors_1792_);
lean_inc(v_errorMsg_1791_);
lean_inc(v_cache_1790_);
lean_inc(v_pos_1789_);
lean_inc(v_lhsPrec_1788_);
lean_inc(v_stxStack_1787_);
lean_dec(v_s_1786_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1808_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
lean_object* v_raw_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1806_; 
v_raw_1796_ = lean_ctor_get(v_stxStack_1787_, 0);
v_isSharedCheck_1806_ = !lean_is_exclusive(v_stxStack_1787_);
if (v_isSharedCheck_1806_ == 0)
{
lean_object* v_unused_1807_; 
v_unused_1807_ = lean_ctor_get(v_stxStack_1787_, 1);
lean_dec(v_unused_1807_);
v___x_1798_ = v_stxStack_1787_;
v_isShared_1799_ = v_isSharedCheck_1806_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_raw_1796_);
lean_dec(v_stxStack_1787_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1806_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 1, v_drop_1778_);
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_raw_1796_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_drop_1778_);
v___x_1801_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
lean_object* v___x_1803_; 
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 0, v___x_1801_);
v___x_1803_ = v___x_1794_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_lhsPrec_1788_);
lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_pos_1789_);
lean_ctor_set(v_reuseFailAlloc_1804_, 3, v_cache_1790_);
lean_ctor_set(v_reuseFailAlloc_1804_, 4, v_errorMsg_1791_);
lean_ctor_set(v_reuseFailAlloc_1804_, 5, v_recoveredErrors_1792_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1813_, lean_object* v_c_1814_, lean_object* v_s_1815_){
_start:
{
lean_object* v_cache_1816_; lean_object* v_stxStack_1817_; lean_object* v_lhsPrec_1818_; lean_object* v_pos_1819_; lean_object* v_errorMsg_1820_; lean_object* v_recoveredErrors_1821_; lean_object* v___x_1823_; uint8_t v_isShared_1824_; uint8_t v_isSharedCheck_1861_; 
v_cache_1816_ = lean_ctor_get(v_s_1815_, 3);
v_stxStack_1817_ = lean_ctor_get(v_s_1815_, 0);
v_lhsPrec_1818_ = lean_ctor_get(v_s_1815_, 1);
v_pos_1819_ = lean_ctor_get(v_s_1815_, 2);
v_errorMsg_1820_ = lean_ctor_get(v_s_1815_, 4);
v_recoveredErrors_1821_ = lean_ctor_get(v_s_1815_, 5);
v_isSharedCheck_1861_ = !lean_is_exclusive(v_s_1815_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1823_ = v_s_1815_;
v_isShared_1824_ = v_isSharedCheck_1861_;
goto v_resetjp_1822_;
}
else
{
lean_inc(v_recoveredErrors_1821_);
lean_inc(v_errorMsg_1820_);
lean_inc(v_cache_1816_);
lean_inc(v_pos_1819_);
lean_inc(v_lhsPrec_1818_);
lean_inc(v_stxStack_1817_);
lean_dec(v_s_1815_);
v___x_1823_ = lean_box(0);
v_isShared_1824_ = v_isSharedCheck_1861_;
goto v_resetjp_1822_;
}
v_resetjp_1822_:
{
lean_object* v_tokenCache_1825_; lean_object* v_parserCache_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1860_; 
v_tokenCache_1825_ = lean_ctor_get(v_cache_1816_, 0);
v_parserCache_1826_ = lean_ctor_get(v_cache_1816_, 1);
v_isSharedCheck_1860_ = !lean_is_exclusive(v_cache_1816_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1828_ = v_cache_1816_;
v_isShared_1829_ = v_isSharedCheck_1860_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_parserCache_1826_);
lean_inc(v_tokenCache_1825_);
lean_dec(v_cache_1816_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1860_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 1, v___x_1830_);
v___x_1832_ = v___x_1828_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_tokenCache_1825_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v___x_1830_);
v___x_1832_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1824_ == 0)
{
lean_ctor_set(v___x_1823_, 3, v___x_1832_);
v___x_1834_ = v___x_1823_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_stxStack_1817_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_lhsPrec_1818_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_pos_1819_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v___x_1832_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_errorMsg_1820_);
lean_ctor_set(v_reuseFailAlloc_1858_, 5, v_recoveredErrors_1821_);
v___x_1834_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v_s_x27_1835_; lean_object* v_cache_1836_; lean_object* v_stxStack_1837_; lean_object* v_lhsPrec_1838_; lean_object* v_pos_1839_; lean_object* v_errorMsg_1840_; lean_object* v_recoveredErrors_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1857_; 
v_s_x27_1835_ = lean_apply_2(v_p_1813_, v_c_1814_, v___x_1834_);
v_cache_1836_ = lean_ctor_get(v_s_x27_1835_, 3);
v_stxStack_1837_ = lean_ctor_get(v_s_x27_1835_, 0);
v_lhsPrec_1838_ = lean_ctor_get(v_s_x27_1835_, 1);
v_pos_1839_ = lean_ctor_get(v_s_x27_1835_, 2);
v_errorMsg_1840_ = lean_ctor_get(v_s_x27_1835_, 4);
v_recoveredErrors_1841_ = lean_ctor_get(v_s_x27_1835_, 5);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_s_x27_1835_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1843_ = v_s_x27_1835_;
v_isShared_1844_ = v_isSharedCheck_1857_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_recoveredErrors_1841_);
lean_inc(v_errorMsg_1840_);
lean_inc(v_cache_1836_);
lean_inc(v_pos_1839_);
lean_inc(v_lhsPrec_1838_);
lean_inc(v_stxStack_1837_);
lean_dec(v_s_x27_1835_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1857_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v_tokenCache_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1855_; 
v_tokenCache_1845_ = lean_ctor_get(v_cache_1836_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_cache_1836_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; 
v_unused_1856_ = lean_ctor_get(v_cache_1836_, 1);
lean_dec(v_unused_1856_);
v___x_1847_ = v_cache_1836_;
v_isShared_1848_ = v_isSharedCheck_1855_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_tokenCache_1845_);
lean_dec(v_cache_1836_);
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1855_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1850_; 
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 1, v_parserCache_1826_);
v___x_1850_ = v___x_1847_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_tokenCache_1845_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_parserCache_1826_);
v___x_1850_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1852_; 
if (v_isShared_1844_ == 0)
{
lean_ctor_set(v___x_1843_, 3, v___x_1850_);
v___x_1852_ = v___x_1843_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_stxStack_1837_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_lhsPrec_1838_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_pos_1839_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1853_, 4, v_errorMsg_1840_);
lean_ctor_set(v_reuseFailAlloc_1853_, 5, v_recoveredErrors_1841_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_){
_start:
{
lean_object* v___f_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___f_1865_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1865_, 0, v_p_1862_);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1866_, v___f_1865_, v_a_1863_, v_a_1864_);
return v___x_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1868_){
_start:
{
lean_object* v_info_1869_; lean_object* v_fn_1870_; lean_object* v___x_1872_; uint8_t v_isShared_1873_; uint8_t v_isSharedCheck_1878_; 
v_info_1869_ = lean_ctor_get(v_p_1868_, 0);
v_fn_1870_ = lean_ctor_get(v_p_1868_, 1);
v_isSharedCheck_1878_ = !lean_is_exclusive(v_p_1868_);
if (v_isSharedCheck_1878_ == 0)
{
v___x_1872_ = v_p_1868_;
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
else
{
lean_inc(v_fn_1870_);
lean_inc(v_info_1869_);
lean_dec(v_p_1868_);
v___x_1872_ = lean_box(0);
v_isShared_1873_ = v_isSharedCheck_1878_;
goto v_resetjp_1871_;
}
v_resetjp_1871_:
{
lean_object* v___x_1874_; lean_object* v___x_1876_; 
v___x_1874_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1874_, 0, v_fn_1870_);
if (v_isShared_1873_ == 0)
{
lean_ctor_set(v___x_1872_, 1, v___x_1874_);
v___x_1876_ = v___x_1872_;
goto v_reusejp_1875_;
}
else
{
lean_object* v_reuseFailAlloc_1877_; 
v_reuseFailAlloc_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1877_, 0, v_info_1869_);
lean_ctor_set(v_reuseFailAlloc_1877_, 1, v___x_1874_);
v___x_1876_ = v_reuseFailAlloc_1877_;
goto v_reusejp_1875_;
}
v_reusejp_1875_:
{
return v___x_1876_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1879_, lean_object* v_p_1880_, lean_object* v_c_1881_, lean_object* v_s_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = lean_apply_1(v_f_1879_, v_c_1881_);
v___x_1884_ = lean_apply_2(v_p_1880_, v___x_1883_, v_s_1882_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1885_, lean_object* v_p_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v___f_1889_; lean_object* v___x_1890_; 
v___f_1889_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1889_, 0, v_f_1885_);
lean_closure_set(v___f_1889_, 1, v_p_1886_);
v___x_1890_ = l_Lean_Parser_withResetCacheFn(v___f_1889_, v_a_1887_, v_a_1888_);
return v___x_1890_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1891_, lean_object* v_x_1892_){
_start:
{
if (lean_obj_tag(v_x_1892_) == 0)
{
uint8_t v___x_1893_; 
v___x_1893_ = 0;
return v___x_1893_;
}
else
{
lean_object* v_key_1894_; lean_object* v_tail_1895_; uint8_t v___x_1896_; 
v_key_1894_ = lean_ctor_get(v_x_1892_, 0);
v_tail_1895_ = lean_ctor_get(v_x_1892_, 2);
v___x_1896_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1894_, v_a_1891_);
if (v___x_1896_ == 0)
{
v_x_1892_ = v_tail_1895_;
goto _start;
}
else
{
return v___x_1896_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1891_ = stack[0].m_obj;
lean_object* v_x_1892_ = stack[1].m_obj;
uint8_t v_res_1898_;
v_res_1898_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1891_, v_x_1892_);
stack->m_num = v_res_1898_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1899_, lean_object* v_x_1900_){
_start:
{
uint8_t v_res_1901_; lean_object* v_r_1902_; 
v_res_1901_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1899_, v_x_1900_);
lean_dec(v_x_1900_);
lean_dec_ref(v_a_1899_);
v_r_1902_ = lean_box(v_res_1901_);
return v_r_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1903_, lean_object* v_x_1904_){
_start:
{
if (lean_obj_tag(v_x_1904_) == 0)
{
return v_x_1903_;
}
else
{
lean_object* v_key_1905_; lean_object* v_value_1906_; lean_object* v_tail_1907_; lean_object* v___x_1909_; uint8_t v_isShared_1910_; uint8_t v_isSharedCheck_1937_; 
v_key_1905_ = lean_ctor_get(v_x_1904_, 0);
v_value_1906_ = lean_ctor_get(v_x_1904_, 1);
v_tail_1907_ = lean_ctor_get(v_x_1904_, 2);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_x_1904_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1909_ = v_x_1904_;
v_isShared_1910_ = v_isSharedCheck_1937_;
goto v_resetjp_1908_;
}
else
{
lean_inc(v_tail_1907_);
lean_inc(v_value_1906_);
lean_inc(v_key_1905_);
lean_dec(v_x_1904_);
v___x_1909_ = lean_box(0);
v_isShared_1910_ = v_isSharedCheck_1937_;
goto v_resetjp_1908_;
}
v_resetjp_1908_:
{
lean_object* v_parserName_1911_; lean_object* v_pos_1912_; lean_object* v___x_1913_; uint64_t v___x_1914_; uint64_t v___y_1916_; 
v_parserName_1911_ = lean_ctor_get(v_key_1905_, 1);
v_pos_1912_ = lean_ctor_get(v_key_1905_, 2);
v___x_1913_ = lean_array_get_size(v_x_1903_);
v___x_1914_ = l_String_instHashableRaw_hash(v_pos_1912_);
if (lean_obj_tag(v_parserName_1911_) == 0)
{
uint64_t v___x_1935_; 
v___x_1935_ = 1723ULL;
v___y_1916_ = v___x_1935_;
goto v___jp_1915_;
}
else
{
uint64_t v_hash_1936_; 
v_hash_1936_ = lean_ctor_get_uint64(v_parserName_1911_, sizeof(void*)*2);
v___y_1916_ = v_hash_1936_;
goto v___jp_1915_;
}
v___jp_1915_:
{
uint64_t v___x_1917_; uint64_t v___x_1918_; uint64_t v___x_1919_; uint64_t v_fold_1920_; uint64_t v___x_1921_; uint64_t v___x_1922_; uint64_t v___x_1923_; size_t v___x_1924_; size_t v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1931_; 
v___x_1917_ = lean_uint64_mix_hash(v___x_1914_, v___y_1916_);
v___x_1918_ = 32ULL;
v___x_1919_ = lean_uint64_shift_right(v___x_1917_, v___x_1918_);
v_fold_1920_ = lean_uint64_xor(v___x_1917_, v___x_1919_);
v___x_1921_ = 16ULL;
v___x_1922_ = lean_uint64_shift_right(v_fold_1920_, v___x_1921_);
v___x_1923_ = lean_uint64_xor(v_fold_1920_, v___x_1922_);
v___x_1924_ = lean_uint64_to_usize(v___x_1923_);
v___x_1925_ = lean_usize_of_nat(v___x_1913_);
v___x_1926_ = ((size_t)1ULL);
v___x_1927_ = lean_usize_sub(v___x_1925_, v___x_1926_);
v___x_1928_ = lean_usize_land(v___x_1924_, v___x_1927_);
v___x_1929_ = lean_array_uget_borrowed(v_x_1903_, v___x_1928_);
lean_inc(v___x_1929_);
if (v_isShared_1910_ == 0)
{
lean_ctor_set(v___x_1909_, 2, v___x_1929_);
v___x_1931_ = v___x_1909_;
goto v_reusejp_1930_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_key_1905_);
lean_ctor_set(v_reuseFailAlloc_1934_, 1, v_value_1906_);
lean_ctor_set(v_reuseFailAlloc_1934_, 2, v___x_1929_);
v___x_1931_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1930_;
}
v_reusejp_1930_:
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_array_uset(v_x_1903_, v___x_1928_, v___x_1931_);
v_x_1903_ = v___x_1932_;
v_x_1904_ = v_tail_1907_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1938_, lean_object* v_source_1939_, lean_object* v_target_1940_){
_start:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; 
v___x_1941_ = lean_array_get_size(v_source_1939_);
v___x_1942_ = lean_nat_dec_lt(v_i_1938_, v___x_1941_);
if (v___x_1942_ == 0)
{
lean_dec_ref(v_source_1939_);
lean_dec(v_i_1938_);
return v_target_1940_;
}
else
{
lean_object* v_es_1943_; lean_object* v___x_1944_; lean_object* v_source_1945_; lean_object* v_target_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v_es_1943_ = lean_array_fget(v_source_1939_, v_i_1938_);
v___x_1944_ = lean_box(0);
v_source_1945_ = lean_array_fset(v_source_1939_, v_i_1938_, v___x_1944_);
v_target_1946_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1940_, v_es_1943_);
v___x_1947_ = lean_unsigned_to_nat(1u);
v___x_1948_ = lean_nat_add(v_i_1938_, v___x_1947_);
lean_dec(v_i_1938_);
v_i_1938_ = v___x_1948_;
v_source_1939_ = v_source_1945_;
v_target_1940_ = v_target_1946_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_nbuckets_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1951_ = lean_array_get_size(v_data_1950_);
v___x_1952_ = lean_unsigned_to_nat(2u);
v_nbuckets_1953_ = lean_nat_mul(v___x_1951_, v___x_1952_);
v___x_1954_ = lean_unsigned_to_nat(0u);
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_mk_array(v_nbuckets_1953_, v___x_1955_);
v___x_1957_ = lean_array_propagate_mark(v_data_1950_, v___x_1956_);
v___x_1958_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1954_, v_data_1950_, v___x_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1959_, lean_object* v_b_1960_, lean_object* v_x_1961_){
_start:
{
if (lean_obj_tag(v_x_1961_) == 0)
{
lean_dec(v_b_1960_);
lean_dec_ref(v_a_1959_);
return v_x_1961_;
}
else
{
lean_object* v_key_1962_; lean_object* v_value_1963_; lean_object* v_tail_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1976_; 
v_key_1962_ = lean_ctor_get(v_x_1961_, 0);
v_value_1963_ = lean_ctor_get(v_x_1961_, 1);
v_tail_1964_ = lean_ctor_get(v_x_1961_, 2);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_x_1961_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1966_ = v_x_1961_;
v_isShared_1967_ = v_isSharedCheck_1976_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_tail_1964_);
lean_inc(v_value_1963_);
lean_inc(v_key_1962_);
lean_dec(v_x_1961_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1976_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
uint8_t v___x_1968_; 
v___x_1968_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1962_, v_a_1959_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1959_, v_b_1960_, v_tail_1964_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 2, v___x_1969_);
v___x_1971_ = v___x_1966_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_key_1962_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_value_1963_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
else
{
lean_object* v___x_1974_; 
lean_dec(v_value_1963_);
lean_dec(v_key_1962_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 1, v_b_1960_);
lean_ctor_set(v___x_1966_, 0, v_a_1959_);
v___x_1974_ = v___x_1966_;
goto v_reusejp_1973_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_a_1959_);
lean_ctor_set(v_reuseFailAlloc_1975_, 1, v_b_1960_);
lean_ctor_set(v_reuseFailAlloc_1975_, 2, v_tail_1964_);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1977_, lean_object* v_a_1978_, lean_object* v_b_1979_){
_start:
{
lean_object* v_size_1980_; lean_object* v_buckets_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_2031_; 
v_size_1980_ = lean_ctor_get(v_m_1977_, 0);
v_buckets_1981_ = lean_ctor_get(v_m_1977_, 1);
v_isSharedCheck_2031_ = !lean_is_exclusive(v_m_1977_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_1983_ = v_m_1977_;
v_isShared_1984_ = v_isSharedCheck_2031_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_buckets_1981_);
lean_inc(v_size_1980_);
lean_dec(v_m_1977_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_2031_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_parserName_1985_; lean_object* v_pos_1986_; lean_object* v___x_1987_; uint64_t v___x_1988_; uint64_t v___y_1990_; 
v_parserName_1985_ = lean_ctor_get(v_a_1978_, 1);
v_pos_1986_ = lean_ctor_get(v_a_1978_, 2);
v___x_1987_ = lean_array_get_size(v_buckets_1981_);
v___x_1988_ = l_String_instHashableRaw_hash(v_pos_1986_);
if (lean_obj_tag(v_parserName_1985_) == 0)
{
uint64_t v___x_2029_; 
v___x_2029_ = 1723ULL;
v___y_1990_ = v___x_2029_;
goto v___jp_1989_;
}
else
{
uint64_t v_hash_2030_; 
v_hash_2030_ = lean_ctor_get_uint64(v_parserName_1985_, sizeof(void*)*2);
v___y_1990_ = v_hash_2030_;
goto v___jp_1989_;
}
v___jp_1989_:
{
uint64_t v___x_1991_; uint64_t v___x_1992_; uint64_t v___x_1993_; uint64_t v_fold_1994_; uint64_t v___x_1995_; uint64_t v___x_1996_; uint64_t v___x_1997_; size_t v___x_1998_; size_t v___x_1999_; size_t v___x_2000_; size_t v___x_2001_; size_t v___x_2002_; lean_object* v_bkt_2003_; uint8_t v___x_2004_; 
v___x_1991_ = lean_uint64_mix_hash(v___x_1988_, v___y_1990_);
v___x_1992_ = 32ULL;
v___x_1993_ = lean_uint64_shift_right(v___x_1991_, v___x_1992_);
v_fold_1994_ = lean_uint64_xor(v___x_1991_, v___x_1993_);
v___x_1995_ = 16ULL;
v___x_1996_ = lean_uint64_shift_right(v_fold_1994_, v___x_1995_);
v___x_1997_ = lean_uint64_xor(v_fold_1994_, v___x_1996_);
v___x_1998_ = lean_uint64_to_usize(v___x_1997_);
v___x_1999_ = lean_usize_of_nat(v___x_1987_);
v___x_2000_ = ((size_t)1ULL);
v___x_2001_ = lean_usize_sub(v___x_1999_, v___x_2000_);
v___x_2002_ = lean_usize_land(v___x_1998_, v___x_2001_);
v_bkt_2003_ = lean_array_uget_borrowed(v_buckets_1981_, v___x_2002_);
v___x_2004_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1978_, v_bkt_2003_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; lean_object* v_size_x27_2006_; lean_object* v___x_2007_; lean_object* v_buckets_x27_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2005_ = lean_unsigned_to_nat(1u);
v_size_x27_2006_ = lean_nat_add(v_size_1980_, v___x_2005_);
lean_dec(v_size_1980_);
lean_inc(v_bkt_2003_);
v___x_2007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2007_, 0, v_a_1978_);
lean_ctor_set(v___x_2007_, 1, v_b_1979_);
lean_ctor_set(v___x_2007_, 2, v_bkt_2003_);
v_buckets_x27_2008_ = lean_array_uset(v_buckets_1981_, v___x_2002_, v___x_2007_);
v___x_2009_ = lean_unsigned_to_nat(4u);
v___x_2010_ = lean_nat_mul(v_size_x27_2006_, v___x_2009_);
v___x_2011_ = lean_unsigned_to_nat(3u);
v___x_2012_ = lean_nat_div(v___x_2010_, v___x_2011_);
lean_dec(v___x_2010_);
v___x_2013_ = lean_array_get_size(v_buckets_x27_2008_);
v___x_2014_ = lean_nat_dec_le(v___x_2012_, v___x_2013_);
lean_dec(v___x_2012_);
if (v___x_2014_ == 0)
{
lean_object* v_val_2015_; lean_object* v___x_2017_; 
v_val_2015_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_2008_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 1, v_val_2015_);
lean_ctor_set(v___x_1983_, 0, v_size_x27_2006_);
v___x_2017_ = v___x_1983_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_size_x27_2006_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_val_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
else
{
lean_object* v___x_2020_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 1, v_buckets_x27_2008_);
lean_ctor_set(v___x_1983_, 0, v_size_x27_2006_);
v___x_2020_ = v___x_1983_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2021_; 
v_reuseFailAlloc_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2021_, 0, v_size_x27_2006_);
lean_ctor_set(v_reuseFailAlloc_2021_, 1, v_buckets_x27_2008_);
v___x_2020_ = v_reuseFailAlloc_2021_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
return v___x_2020_;
}
}
}
else
{
lean_object* v___x_2022_; lean_object* v_buckets_x27_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2027_; 
lean_inc(v_bkt_2003_);
v___x_2022_ = lean_box(0);
v_buckets_x27_2023_ = lean_array_uset(v_buckets_1981_, v___x_2002_, v___x_2022_);
v___x_2024_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1978_, v_b_1979_, v_bkt_2003_);
v___x_2025_ = lean_array_uset(v_buckets_x27_2023_, v___x_2002_, v___x_2024_);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 1, v___x_2025_);
v___x_2027_ = v___x_1983_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_size_1980_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v___x_2025_);
v___x_2027_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
return v___x_2027_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_2032_, lean_object* v_x_2033_){
_start:
{
if (lean_obj_tag(v_x_2033_) == 0)
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_box(0);
return v___x_2034_;
}
else
{
lean_object* v_key_2035_; lean_object* v_value_2036_; lean_object* v_tail_2037_; uint8_t v___x_2038_; 
v_key_2035_ = lean_ctor_get(v_x_2033_, 0);
v_value_2036_ = lean_ctor_get(v_x_2033_, 1);
v_tail_2037_ = lean_ctor_get(v_x_2033_, 2);
v___x_2038_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_2035_, v_a_2032_);
if (v___x_2038_ == 0)
{
v_x_2033_ = v_tail_2037_;
goto _start;
}
else
{
lean_object* v___x_2040_; 
lean_inc(v_value_2036_);
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v_value_2036_);
return v___x_2040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_2041_, lean_object* v_x_2042_){
_start:
{
lean_object* v_res_2043_; 
v_res_2043_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2041_, v_x_2042_);
lean_dec(v_x_2042_);
lean_dec_ref(v_a_2041_);
return v_res_2043_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_2044_, lean_object* v_a_2045_){
_start:
{
lean_object* v_buckets_2046_; lean_object* v_parserName_2047_; lean_object* v_pos_2048_; lean_object* v___x_2049_; uint64_t v___x_2050_; uint64_t v___y_2052_; 
v_buckets_2046_ = lean_ctor_get(v_m_2044_, 1);
v_parserName_2047_ = lean_ctor_get(v_a_2045_, 1);
v_pos_2048_ = lean_ctor_get(v_a_2045_, 2);
v___x_2049_ = lean_array_get_size(v_buckets_2046_);
v___x_2050_ = l_String_instHashableRaw_hash(v_pos_2048_);
if (lean_obj_tag(v_parserName_2047_) == 0)
{
uint64_t v___x_2067_; 
v___x_2067_ = 1723ULL;
v___y_2052_ = v___x_2067_;
goto v___jp_2051_;
}
else
{
uint64_t v_hash_2068_; 
v_hash_2068_ = lean_ctor_get_uint64(v_parserName_2047_, sizeof(void*)*2);
v___y_2052_ = v_hash_2068_;
goto v___jp_2051_;
}
v___jp_2051_:
{
uint64_t v___x_2053_; uint64_t v___x_2054_; uint64_t v___x_2055_; uint64_t v_fold_2056_; uint64_t v___x_2057_; uint64_t v___x_2058_; uint64_t v___x_2059_; size_t v___x_2060_; size_t v___x_2061_; size_t v___x_2062_; size_t v___x_2063_; size_t v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2053_ = lean_uint64_mix_hash(v___x_2050_, v___y_2052_);
v___x_2054_ = 32ULL;
v___x_2055_ = lean_uint64_shift_right(v___x_2053_, v___x_2054_);
v_fold_2056_ = lean_uint64_xor(v___x_2053_, v___x_2055_);
v___x_2057_ = 16ULL;
v___x_2058_ = lean_uint64_shift_right(v_fold_2056_, v___x_2057_);
v___x_2059_ = lean_uint64_xor(v_fold_2056_, v___x_2058_);
v___x_2060_ = lean_uint64_to_usize(v___x_2059_);
v___x_2061_ = lean_usize_of_nat(v___x_2049_);
v___x_2062_ = ((size_t)1ULL);
v___x_2063_ = lean_usize_sub(v___x_2061_, v___x_2062_);
v___x_2064_ = lean_usize_land(v___x_2060_, v___x_2063_);
v___x_2065_ = lean_array_uget_borrowed(v_buckets_2046_, v___x_2064_);
v___x_2066_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2045_, v___x_2065_);
return v___x_2066_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2069_, v_a_2070_);
lean_dec_ref(v_a_2070_);
lean_dec_ref(v_m_2069_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_2072_, lean_object* v_p_2073_, lean_object* v_c_2074_, lean_object* v_s_2075_){
_start:
{
lean_object* v_cache_2076_; lean_object* v_toCacheableParserContext_2077_; lean_object* v_stxStack_2078_; lean_object* v_pos_2079_; lean_object* v_recoveredErrors_2080_; lean_object* v___x_2082_; uint8_t v_isShared_2083_; uint8_t v_isSharedCheck_2129_; 
v_cache_2076_ = lean_ctor_get(v_s_2075_, 3);
lean_inc_ref(v_cache_2076_);
v_toCacheableParserContext_2077_ = lean_ctor_get(v_c_2074_, 2);
v_stxStack_2078_ = lean_ctor_get(v_s_2075_, 0);
v_pos_2079_ = lean_ctor_get(v_s_2075_, 2);
v_recoveredErrors_2080_ = lean_ctor_get(v_s_2075_, 5);
v_isSharedCheck_2129_ = !lean_is_exclusive(v_s_2075_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; lean_object* v_unused_2131_; lean_object* v_unused_2132_; 
v_unused_2130_ = lean_ctor_get(v_s_2075_, 4);
lean_dec(v_unused_2130_);
v_unused_2131_ = lean_ctor_get(v_s_2075_, 3);
lean_dec(v_unused_2131_);
v_unused_2132_ = lean_ctor_get(v_s_2075_, 1);
lean_dec(v_unused_2132_);
v___x_2082_ = v_s_2075_;
v_isShared_2083_ = v_isSharedCheck_2129_;
goto v_resetjp_2081_;
}
else
{
lean_inc(v_recoveredErrors_2080_);
lean_inc(v_pos_2079_);
lean_inc(v_stxStack_2078_);
lean_dec(v_s_2075_);
v___x_2082_ = lean_box(0);
v_isShared_2083_ = v_isSharedCheck_2129_;
goto v_resetjp_2081_;
}
v_resetjp_2081_:
{
lean_object* v_parserCache_2084_; lean_object* v_key_2085_; lean_object* v___x_2086_; 
v_parserCache_2084_ = lean_ctor_get(v_cache_2076_, 1);
lean_inc(v_pos_2079_);
lean_inc_ref(v_toCacheableParserContext_2077_);
v_key_2085_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_2085_, 0, v_toCacheableParserContext_2077_);
lean_ctor_set(v_key_2085_, 1, v_parserName_2072_);
lean_ctor_set(v_key_2085_, 2, v_pos_2079_);
v___x_2086_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_2084_, v_key_2085_);
if (lean_obj_tag(v___x_2086_) == 1)
{
lean_object* v_val_2087_; lean_object* v_stx_2088_; lean_object* v_lhsPrec_2089_; lean_object* v_newPos_2090_; lean_object* v_errorMsg_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
lean_dec_ref_known(v_key_2085_, 3);
lean_dec(v_pos_2079_);
lean_dec_ref(v_c_2074_);
lean_dec_ref(v_p_2073_);
v_val_2087_ = lean_ctor_get(v___x_2086_, 0);
lean_inc(v_val_2087_);
lean_dec_ref_known(v___x_2086_, 1);
v_stx_2088_ = lean_ctor_get(v_val_2087_, 0);
lean_inc(v_stx_2088_);
v_lhsPrec_2089_ = lean_ctor_get(v_val_2087_, 1);
lean_inc(v_lhsPrec_2089_);
v_newPos_2090_ = lean_ctor_get(v_val_2087_, 2);
lean_inc(v_newPos_2090_);
v_errorMsg_2091_ = lean_ctor_get(v_val_2087_, 3);
lean_inc(v_errorMsg_2091_);
lean_dec(v_val_2087_);
v___x_2092_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_2078_, v_stx_2088_);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 4, v_errorMsg_2091_);
lean_ctor_set(v___x_2082_, 2, v_newPos_2090_);
lean_ctor_set(v___x_2082_, 1, v_lhsPrec_2089_);
lean_ctor_set(v___x_2082_, 0, v___x_2092_);
v___x_2094_ = v___x_2082_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2095_; 
v_reuseFailAlloc_2095_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2095_, 0, v___x_2092_);
lean_ctor_set(v_reuseFailAlloc_2095_, 1, v_lhsPrec_2089_);
lean_ctor_set(v_reuseFailAlloc_2095_, 2, v_newPos_2090_);
lean_ctor_set(v_reuseFailAlloc_2095_, 3, v_cache_2076_);
lean_ctor_set(v_reuseFailAlloc_2095_, 4, v_errorMsg_2091_);
lean_ctor_set(v_reuseFailAlloc_2095_, 5, v_recoveredErrors_2080_);
v___x_2094_ = v_reuseFailAlloc_2095_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
return v___x_2094_;
}
}
else
{
lean_object* v_raw_2096_; lean_object* v_initStackSz_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
lean_dec(v___x_2086_);
v_raw_2096_ = lean_ctor_get(v_stxStack_2078_, 0);
v_initStackSz_2097_ = lean_array_get_size(v_raw_2096_);
v___x_2098_ = lean_unsigned_to_nat(0u);
v___x_2099_ = lean_box(0);
if (v_isShared_2083_ == 0)
{
lean_ctor_set(v___x_2082_, 4, v___x_2099_);
lean_ctor_set(v___x_2082_, 1, v___x_2098_);
v___x_2101_ = v___x_2082_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_stxStack_2078_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2128_, 2, v_pos_2079_);
lean_ctor_set(v_reuseFailAlloc_2128_, 3, v_cache_2076_);
lean_ctor_set(v_reuseFailAlloc_2128_, 4, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2128_, 5, v_recoveredErrors_2080_);
v___x_2101_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
lean_object* v_s_2102_; lean_object* v_cache_2103_; lean_object* v_stxStack_2104_; lean_object* v_lhsPrec_2105_; lean_object* v_pos_2106_; lean_object* v_errorMsg_2107_; lean_object* v_recoveredErrors_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2127_; 
v_s_2102_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_2097_, v_p_2073_, v_c_2074_, v___x_2101_);
v_cache_2103_ = lean_ctor_get(v_s_2102_, 3);
v_stxStack_2104_ = lean_ctor_get(v_s_2102_, 0);
v_lhsPrec_2105_ = lean_ctor_get(v_s_2102_, 1);
v_pos_2106_ = lean_ctor_get(v_s_2102_, 2);
v_errorMsg_2107_ = lean_ctor_get(v_s_2102_, 4);
v_recoveredErrors_2108_ = lean_ctor_get(v_s_2102_, 5);
v_isSharedCheck_2127_ = !lean_is_exclusive(v_s_2102_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2110_ = v_s_2102_;
v_isShared_2111_ = v_isSharedCheck_2127_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_recoveredErrors_2108_);
lean_inc(v_errorMsg_2107_);
lean_inc(v_cache_2103_);
lean_inc(v_pos_2106_);
lean_inc(v_lhsPrec_2105_);
lean_inc(v_stxStack_2104_);
lean_dec(v_s_2102_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2127_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v_tokenCache_2112_; lean_object* v_parserCache_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2126_; 
v_tokenCache_2112_ = lean_ctor_get(v_cache_2103_, 0);
v_parserCache_2113_ = lean_ctor_get(v_cache_2103_, 1);
v_isSharedCheck_2126_ = !lean_is_exclusive(v_cache_2103_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2115_ = v_cache_2103_;
v_isShared_2116_ = v_isSharedCheck_2126_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_parserCache_2113_);
lean_inc(v_tokenCache_2112_);
lean_dec(v_cache_2103_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2126_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2117_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2104_);
lean_inc(v_errorMsg_2107_);
lean_inc(v_pos_2106_);
lean_inc(v_lhsPrec_2105_);
v___x_2118_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v_lhsPrec_2105_);
lean_ctor_set(v___x_2118_, 2, v_pos_2106_);
lean_ctor_set(v___x_2118_, 3, v_errorMsg_2107_);
v___x_2119_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_2113_, v_key_2085_, v___x_2118_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 1, v___x_2119_);
v___x_2121_ = v___x_2115_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_tokenCache_2112_);
lean_ctor_set(v_reuseFailAlloc_2125_, 1, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2123_; 
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 3, v___x_2121_);
v___x_2123_ = v___x_2110_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_stxStack_2104_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v_lhsPrec_2105_);
lean_ctor_set(v_reuseFailAlloc_2124_, 2, v_pos_2106_);
lean_ctor_set(v_reuseFailAlloc_2124_, 3, v___x_2121_);
lean_ctor_set(v_reuseFailAlloc_2124_, 4, v_errorMsg_2107_);
lean_ctor_set(v_reuseFailAlloc_2124_, 5, v_recoveredErrors_2108_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2133_, lean_object* v_m_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v___x_2136_; 
v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2134_, v_a_2135_);
return v___x_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2137_, lean_object* v_m_2138_, lean_object* v_a_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2137_, v_m_2138_, v_a_2139_);
lean_dec_ref(v_a_2139_);
lean_dec_ref(v_m_2138_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2141_, lean_object* v_m_2142_, lean_object* v_a_2143_, lean_object* v_b_2144_){
_start:
{
lean_object* v___x_2145_; 
v___x_2145_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2142_, v_a_2143_, v_b_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2146_, lean_object* v_a_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2147_, v_x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2150_, lean_object* v_a_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v_res_2153_; 
v_res_2153_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2150_, v_a_2151_, v_x_2152_);
lean_dec(v_x_2152_);
lean_dec_ref(v_a_2151_);
return v_res_2153_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2154_, lean_object* v_a_2155_, lean_object* v_x_2156_){
_start:
{
uint8_t v___x_2157_; 
v___x_2157_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2155_, v_x_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2155_ = stack[1].m_obj;
lean_object* v_x_2156_ = stack[2].m_obj;
uint8_t v_res_2158_;
v_res_2158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_box(0), v_a_2155_, v_x_2156_);
stack->m_num = v_res_2158_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2159_, lean_object* v_a_2160_, lean_object* v_x_2161_){
_start:
{
uint8_t v_res_2162_; lean_object* v_r_2163_; 
v_res_2162_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2159_, v_a_2160_, v_x_2161_);
lean_dec(v_x_2161_);
lean_dec_ref(v_a_2160_);
v_r_2163_ = lean_box(v_res_2162_);
return v_r_2163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2164_, lean_object* v_data_2165_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2167_, lean_object* v_a_2168_, lean_object* v_b_2169_, lean_object* v_x_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2168_, v_b_2169_, v_x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2172_, lean_object* v_i_2173_, lean_object* v_source_2174_, lean_object* v_target_2175_){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2173_, v_source_2174_, v_target_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2178_, v_x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2181_, lean_object* v_p_2182_){
_start:
{
lean_object* v_info_2183_; lean_object* v_fn_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2192_; 
v_info_2183_ = lean_ctor_get(v_p_2182_, 0);
v_fn_2184_ = lean_ctor_get(v_p_2182_, 1);
v_isSharedCheck_2192_ = !lean_is_exclusive(v_p_2182_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2186_ = v_p_2182_;
v_isShared_2187_ = v_isSharedCheck_2192_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_fn_2184_);
lean_inc(v_info_2183_);
lean_dec(v_p_2182_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2192_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2188_; lean_object* v___x_2190_; 
v___x_2188_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2188_, 0, v_parserName_2181_);
lean_closure_set(v___x_2188_, 1, v_fn_2184_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v___x_2188_);
v___x_2190_ = v___x_2186_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_info_2183_);
lean_ctor_set(v_reuseFailAlloc_2191_, 1, v___x_2188_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2201_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2202_ = l_Lean_addBuiltinDocString(v___x_2200_, v___x_2201_);
return v___x_2202_;
}
}
LEAN_EXPORT void l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2203_;
v_res_2203_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
stack->m_obj
 = v_res_2203_;
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2213_, lean_object* v_ictx_2214_, lean_object* v_pmctx_2215_, lean_object* v_tokens_2216_, lean_object* v_s_2217_){
_start:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; 
v___x_2218_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__1));
v___x_2219_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2219_, 0, v_ictx_2214_);
lean_ctor_set(v___x_2219_, 1, v_pmctx_2215_);
lean_ctor_set(v___x_2219_, 2, v___x_2218_);
lean_ctor_set(v___x_2219_, 3, v_tokens_2216_);
v___x_2220_ = lean_apply_2(v_p_2213_, v___x_2219_, v_s_2217_);
return v___x_2220_;
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
