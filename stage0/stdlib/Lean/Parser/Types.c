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
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = l_Lean_instInhabitedFileMap_default;
v___x_321_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_322_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_321_);
lean_ctor_set(v___x_322_, 2, v___x_320_);
lean_ctor_set(v___x_322_, 3, v___x_319_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedInputContext(void){
_start:
{
lean_object* v___x_323_; 
v___x_323_ = lean_obj_once(&l_Lean_Parser_instInhabitedInputContext___closed__1, &l_Lean_Parser_instInhabitedInputContext___closed__1_once, _init_l_Lean_Parser_instInhabitedInputContext___closed__1);
return v___x_323_;
}
}
static lean_object* _init_l_Lean_Parser_InputContext_mk___auto__1(void){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = lean_obj_once(&l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30, &l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30_once, _init_l_Lean_Parser_InputContext_endPos__valid___autoParam___closed__30);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk___redArg(lean_object* v_input_325_, lean_object* v_fileName_326_, lean_object* v_endPos_327_, lean_object* v_fileMap_328_){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_329_, 0, v_input_325_);
lean_ctor_set(v___x_329_, 1, v_fileName_326_);
lean_ctor_set(v___x_329_, 2, v_fileMap_328_);
lean_ctor_set(v___x_329_, 3, v_endPos_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_mk(lean_object* v_input_330_, lean_object* v_fileName_331_, lean_object* v_endPos_332_, lean_object* v_endPos__valid_333_, lean_object* v_fileMap_334_){
_start:
{
lean_object* v___x_335_; 
v___x_335_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_335_, 0, v_input_330_);
lean_ctor_set(v___x_335_, 1, v_fileName_331_);
lean_ctor_set(v___x_335_, 2, v_fileMap_334_);
lean_ctor_set(v___x_335_, 3, v_endPos_332_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input(lean_object* v_c_336_){
_start:
{
lean_object* v_inputString_337_; lean_object* v_endPos_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v_inputString_337_ = lean_ctor_get(v_c_336_, 0);
v_endPos_338_ = lean_ctor_get(v_c_336_, 3);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_string_utf8_extract(v_inputString_337_, v___x_339_, v_endPos_338_);
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_input___boxed(lean_object* v_c_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_Parser_InputContext_input(v_c_341_);
lean_dec_ref(v_c_341_);
return v_res_342_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_InputContext_atEnd(lean_object* v_c_343_, lean_object* v_p_344_){
_start:
{
lean_object* v_endPos_345_; uint8_t v___x_346_; 
v_endPos_345_ = lean_ctor_get(v_c_343_, 3);
v___x_346_ = lean_nat_dec_le(v_endPos_345_, v_p_344_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_atEnd___boxed(lean_object* v_c_347_, lean_object* v_p_348_){
_start:
{
uint8_t v_res_349_; lean_object* v_r_350_; 
v_res_349_ = l_Lean_Parser_InputContext_atEnd(v_c_347_, v_p_348_);
lean_dec(v_p_348_);
lean_dec_ref(v_c_347_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get(lean_object* v_c_351_, lean_object* v_p_352_){
_start:
{
lean_object* v_inputString_353_; uint32_t v___x_354_; 
v_inputString_353_ = lean_ctor_get(v_c_351_, 0);
v___x_354_ = lean_string_utf8_get(v_inputString_353_, v_p_352_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get___boxed(lean_object* v_c_355_, lean_object* v_p_356_){
_start:
{
uint32_t v_res_357_; lean_object* v_r_358_; 
v_res_357_ = l_Lean_Parser_InputContext_get(v_c_355_, v_p_356_);
lean_dec(v_p_356_);
lean_dec_ref(v_c_355_);
v_r_358_ = lean_box_uint32(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27___redArg(lean_object* v_c_359_, lean_object* v_p_360_){
_start:
{
lean_object* v_inputString_361_; uint32_t v___x_362_; 
v_inputString_361_ = lean_ctor_get(v_c_359_, 0);
v___x_362_ = lean_string_utf8_get_fast(v_inputString_361_, v_p_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___redArg___boxed(lean_object* v_c_363_, lean_object* v_p_364_){
_start:
{
uint32_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Lean_Parser_InputContext_get_x27___redArg(v_c_363_, v_p_364_);
lean_dec(v_p_364_);
lean_dec_ref(v_c_363_);
v_r_366_ = lean_box_uint32(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27(lean_object* v_c_367_, lean_object* v_p_368_, lean_object* v_h_369_){
_start:
{
lean_object* v_inputString_370_; uint32_t v___x_371_; 
v_inputString_370_ = lean_ctor_get(v_c_367_, 0);
v___x_371_ = lean_string_utf8_get_fast(v_inputString_370_, v_p_368_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___boxed(lean_object* v_c_372_, lean_object* v_p_373_, lean_object* v_h_374_){
_start:
{
uint32_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Lean_Parser_InputContext_get_x27(v_c_372_, v_p_373_, v_h_374_);
lean_dec(v_p_373_);
lean_dec_ref(v_c_372_);
v_r_376_ = lean_box_uint32(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next(lean_object* v_c_377_, lean_object* v_p_378_){
_start:
{
lean_object* v_inputString_379_; lean_object* v___x_380_; 
v_inputString_379_ = lean_ctor_get(v_c_377_, 0);
v___x_380_ = lean_string_utf8_next(v_inputString_379_, v_p_378_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next___boxed(lean_object* v_c_381_, lean_object* v_p_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_Parser_InputContext_next(v_c_381_, v_p_382_);
lean_dec(v_p_382_);
lean_dec_ref(v_c_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg(lean_object* v_c_384_, lean_object* v_p_385_){
_start:
{
lean_object* v_inputString_386_; lean_object* v___x_387_; 
v_inputString_386_ = lean_ctor_get(v_c_384_, 0);
v___x_387_ = lean_string_utf8_next_fast(v_inputString_386_, v_p_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___redArg___boxed(lean_object* v_c_388_, lean_object* v_p_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Lean_Parser_InputContext_next_x27___redArg(v_c_388_, v_p_389_);
lean_dec(v_p_389_);
lean_dec_ref(v_c_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27(lean_object* v_c_391_, lean_object* v_p_392_, lean_object* v_h_393_){
_start:
{
lean_object* v_inputString_394_; lean_object* v___x_395_; 
v_inputString_394_ = lean_ctor_get(v_c_391_, 0);
v___x_395_ = lean_string_utf8_next_fast(v_inputString_394_, v_p_392_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_next_x27___boxed(lean_object* v_c_396_, lean_object* v_p_397_, lean_object* v_h_398_){
_start:
{
lean_object* v_res_399_; 
v_res_399_ = l_Lean_Parser_InputContext_next_x27(v_c_396_, v_p_397_, v_h_398_);
lean_dec(v_p_397_);
lean_dec_ref(v_c_396_);
return v_res_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract(lean_object* v_c_400_, lean_object* v_a_401_, lean_object* v_a_402_){
_start:
{
lean_object* v_inputString_403_; lean_object* v___x_404_; 
v_inputString_403_ = lean_ctor_get(v_c_400_, 0);
v___x_404_ = lean_string_utf8_extract(v_inputString_403_, v_a_401_, v_a_402_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_extract___boxed(lean_object* v_c_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Parser_InputContext_extract(v_c_405_, v_a_406_, v_a_407_);
lean_dec(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_c_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring(lean_object* v_c_409_, lean_object* v_startPos_410_, lean_object* v_stopPos_411_){
_start:
{
lean_object* v_inputString_412_; lean_object* v_endPos_413_; uint8_t v___x_414_; 
v_inputString_412_ = lean_ctor_get(v_c_409_, 0);
v_endPos_413_ = lean_ctor_get(v_c_409_, 3);
v___x_414_ = lean_nat_dec_le(v_stopPos_411_, v_endPos_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_dec(v_stopPos_411_);
lean_inc(v_endPos_413_);
lean_inc_ref(v_inputString_412_);
v___x_415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_415_, 0, v_inputString_412_);
lean_ctor_set(v___x_415_, 1, v_startPos_410_);
lean_ctor_set(v___x_415_, 2, v_endPos_413_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; 
lean_inc_ref(v_inputString_412_);
v___x_416_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_416_, 0, v_inputString_412_);
lean_ctor_set(v___x_416_, 1, v_startPos_410_);
lean_ctor_set(v___x_416_, 2, v_stopPos_411_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_substring___boxed(lean_object* v_c_417_, lean_object* v_startPos_418_, lean_object* v_stopPos_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Parser_InputContext_substring(v_c_417_, v_startPos_418_, v_stopPos_419_);
lean_dec_ref(v_c_417_);
return v_res_420_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_getNext(lean_object* v_input_421_, lean_object* v_pos_422_){
_start:
{
lean_object* v_inputString_423_; lean_object* v___x_424_; uint32_t v___x_425_; 
v_inputString_423_ = lean_ctor_get(v_input_421_, 0);
v___x_424_ = lean_string_utf8_next(v_inputString_423_, v_pos_422_);
v___x_425_ = lean_string_utf8_get(v_inputString_423_, v___x_424_);
lean_dec(v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_getNext___boxed(lean_object* v_input_426_, lean_object* v_pos_427_){
_start:
{
uint32_t v_res_428_; lean_object* v_r_429_; 
v_res_428_ = l_Lean_Parser_InputContext_getNext(v_input_426_, v_pos_427_);
lean_dec(v_pos_427_);
lean_dec_ref(v_input_426_);
v_r_429_ = lean_box_uint32(v_res_428_);
return v_r_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev(lean_object* v_c_430_, lean_object* v_pos_431_){
_start:
{
lean_object* v_inputString_432_; lean_object* v___x_433_; 
v_inputString_432_ = lean_ctor_get(v_c_430_, 0);
v___x_433_ = lean_string_utf8_prev(v_inputString_432_, v_pos_431_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev___boxed(lean_object* v_c_434_, lean_object* v_pos_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Parser_InputContext_prev(v_c_434_, v_pos_435_);
lean_dec(v_pos_435_);
lean_dec_ref(v_c_434_);
return v_res_436_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext_unsafe__2(lean_object* v_a_438_, lean_object* v_b_439_){
_start:
{
lean_object* v_forbiddenTks_440_; lean_object* v_forbiddenTks_441_; size_t v___x_442_; size_t v___x_443_; uint8_t v___x_444_; 
v_forbiddenTks_440_ = lean_ctor_get(v_a_438_, 3);
v_forbiddenTks_441_ = lean_ctor_get(v_b_439_, 3);
v___x_442_ = lean_ptr_addr(v_forbiddenTks_440_);
v___x_443_ = lean_ptr_addr(v_forbiddenTks_441_);
v___x_444_ = lean_usize_dec_eq(v___x_442_, v___x_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_445_ = lean_array_get_size(v_forbiddenTks_440_);
v___x_446_ = lean_array_get_size(v_forbiddenTks_441_);
v___x_447_ = lean_nat_dec_eq(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
return v___x_447_;
}
else
{
lean_object* v___f_448_; uint8_t v___x_449_; 
v___f_448_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0));
v___x_449_ = l_Array_isEqvAux___redArg(v_forbiddenTks_440_, v_forbiddenTks_441_, v___f_448_, v___x_445_);
return v___x_449_;
}
}
else
{
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___boxed(lean_object* v_a_450_, lean_object* v_b_451_){
_start:
{
uint8_t v_res_452_; lean_object* v_r_453_; 
v_res_452_ = l_Lean_Parser_instBEqCacheableParserContext_unsafe__2(v_a_450_, v_b_451_);
lean_dec_ref(v_b_451_);
lean_dec_ref(v_a_450_);
v_r_453_ = lean_box(v_res_452_);
return v_r_453_;
}
}
static lean_object* _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0(void){
_start:
{
lean_object* v___x_454_; lean_object* v___f_455_; 
v___x_454_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_455_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_455_, 0, v___x_454_);
return v___f_455_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext___lam__0(lean_object* v___f_456_, lean_object* v_a_457_, lean_object* v_b_458_){
_start:
{
lean_object* v_prec_459_; lean_object* v_quotDepth_460_; uint8_t v_suppressInsideQuot_461_; lean_object* v_savedPos_x3f_462_; lean_object* v_forbiddenTks_463_; lean_object* v_prec_464_; lean_object* v_quotDepth_465_; uint8_t v_suppressInsideQuot_466_; lean_object* v_savedPos_x3f_467_; lean_object* v_forbiddenTks_468_; uint8_t v___x_479_; 
v_prec_459_ = lean_ctor_get(v_a_457_, 0);
lean_inc(v_prec_459_);
v_quotDepth_460_ = lean_ctor_get(v_a_457_, 1);
lean_inc(v_quotDepth_460_);
v_suppressInsideQuot_461_ = lean_ctor_get_uint8(v_a_457_, sizeof(void*)*4);
v_savedPos_x3f_462_ = lean_ctor_get(v_a_457_, 2);
lean_inc(v_savedPos_x3f_462_);
v_forbiddenTks_463_ = lean_ctor_get(v_a_457_, 3);
lean_inc_ref(v_forbiddenTks_463_);
lean_dec_ref(v_a_457_);
v_prec_464_ = lean_ctor_get(v_b_458_, 0);
lean_inc(v_prec_464_);
v_quotDepth_465_ = lean_ctor_get(v_b_458_, 1);
lean_inc(v_quotDepth_465_);
v_suppressInsideQuot_466_ = lean_ctor_get_uint8(v_b_458_, sizeof(void*)*4);
v_savedPos_x3f_467_ = lean_ctor_get(v_b_458_, 2);
lean_inc(v_savedPos_x3f_467_);
v_forbiddenTks_468_ = lean_ctor_get(v_b_458_, 3);
lean_inc_ref(v_forbiddenTks_468_);
lean_dec_ref(v_b_458_);
v___x_479_ = lean_nat_dec_eq(v_prec_459_, v_prec_464_);
lean_dec(v_prec_464_);
lean_dec(v_prec_459_);
if (v___x_479_ == 0)
{
lean_dec_ref(v_forbiddenTks_468_);
lean_dec(v_savedPos_x3f_467_);
lean_dec(v_quotDepth_465_);
lean_dec_ref(v_forbiddenTks_463_);
lean_dec(v_savedPos_x3f_462_);
lean_dec(v_quotDepth_460_);
lean_dec_ref(v___f_456_);
return v___x_479_;
}
else
{
uint8_t v___x_480_; 
v___x_480_ = lean_nat_dec_eq(v_quotDepth_460_, v_quotDepth_465_);
lean_dec(v_quotDepth_465_);
lean_dec(v_quotDepth_460_);
if (v___x_480_ == 0)
{
lean_dec_ref(v_forbiddenTks_468_);
lean_dec(v_savedPos_x3f_467_);
lean_dec_ref(v_forbiddenTks_463_);
lean_dec(v_savedPos_x3f_462_);
lean_dec_ref(v___f_456_);
return v___x_480_;
}
else
{
if (v_suppressInsideQuot_466_ == 0)
{
if (v_suppressInsideQuot_461_ == 0)
{
goto v___jp_469_;
}
else
{
lean_dec_ref(v_forbiddenTks_468_);
lean_dec(v_savedPos_x3f_467_);
lean_dec_ref(v_forbiddenTks_463_);
lean_dec(v_savedPos_x3f_462_);
lean_dec_ref(v___f_456_);
return v_suppressInsideQuot_466_;
}
}
else
{
if (v_suppressInsideQuot_461_ == 0)
{
lean_dec_ref(v_forbiddenTks_468_);
lean_dec(v_savedPos_x3f_467_);
lean_dec_ref(v_forbiddenTks_463_);
lean_dec(v_savedPos_x3f_462_);
lean_dec_ref(v___f_456_);
return v_suppressInsideQuot_461_;
}
else
{
goto v___jp_469_;
}
}
}
}
v___jp_469_:
{
lean_object* v___f_470_; uint8_t v___x_471_; 
v___f_470_ = lean_obj_once(&l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0, &l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0_once, _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0);
v___x_471_ = l_instBEqOption_beq___redArg(v___f_470_, v_savedPos_x3f_462_, v_savedPos_x3f_467_);
if (v___x_471_ == 0)
{
lean_dec_ref(v_forbiddenTks_468_);
lean_dec_ref(v_forbiddenTks_463_);
lean_dec_ref(v___f_456_);
return v___x_471_;
}
else
{
size_t v___x_472_; size_t v___x_473_; uint8_t v___x_474_; 
v___x_472_ = lean_ptr_addr(v_forbiddenTks_463_);
v___x_473_ = lean_ptr_addr(v_forbiddenTks_468_);
v___x_474_ = lean_usize_dec_eq(v___x_472_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_475_ = lean_array_get_size(v_forbiddenTks_463_);
v___x_476_ = lean_array_get_size(v_forbiddenTks_468_);
v___x_477_ = lean_nat_dec_eq(v___x_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_dec_ref(v_forbiddenTks_468_);
lean_dec_ref(v_forbiddenTks_463_);
lean_dec_ref(v___f_456_);
return v___x_477_;
}
else
{
uint8_t v___x_478_; 
v___x_478_ = l_Array_isEqvAux___redArg(v_forbiddenTks_463_, v_forbiddenTks_468_, v___f_456_, v___x_475_);
lean_dec_ref(v_forbiddenTks_468_);
lean_dec_ref(v_forbiddenTks_463_);
return v___x_478_;
}
}
else
{
lean_dec_ref(v_forbiddenTks_468_);
lean_dec_ref(v_forbiddenTks_463_);
lean_dec_ref(v___f_456_);
return v___x_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed(lean_object* v___f_481_, lean_object* v_a_482_, lean_object* v_b_483_){
_start:
{
uint8_t v_res_484_; lean_object* v_r_485_; 
v_res_484_ = l_Lean_Parser_instBEqCacheableParserContext___lam__0(v___f_481_, v_a_482_, v_b_483_);
v_r_485_ = lean_box(v_res_484_);
return v_r_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0(lean_object* v_x_489_){
_start:
{
lean_object* v_toInputContext_490_; 
v_toInputContext_490_ = lean_ctor_get(v_x_489_, 0);
lean_inc_ref(v_toInputContext_490_);
return v_toInputContext_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(lean_object* v_x_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_491_);
lean_dec_ref(v_x_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos___redArg(lean_object* v_c_495_, lean_object* v_endPos_496_){
_start:
{
lean_object* v_toInputContext_497_; lean_object* v_toParserModuleContext_498_; lean_object* v_toCacheableParserContext_499_; lean_object* v_tokens_500_; lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_518_; 
v_toInputContext_497_ = lean_ctor_get(v_c_495_, 0);
v_toParserModuleContext_498_ = lean_ctor_get(v_c_495_, 1);
v_toCacheableParserContext_499_ = lean_ctor_get(v_c_495_, 2);
v_tokens_500_ = lean_ctor_get(v_c_495_, 3);
v_isSharedCheck_518_ = !lean_is_exclusive(v_c_495_);
if (v_isSharedCheck_518_ == 0)
{
v___x_502_ = v_c_495_;
v_isShared_503_ = v_isSharedCheck_518_;
goto v_resetjp_501_;
}
else
{
lean_inc(v_tokens_500_);
lean_inc(v_toCacheableParserContext_499_);
lean_inc(v_toParserModuleContext_498_);
lean_inc(v_toInputContext_497_);
lean_dec(v_c_495_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_518_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_inputString_504_; lean_object* v_fileName_505_; lean_object* v_fileMap_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_516_; 
v_inputString_504_ = lean_ctor_get(v_toInputContext_497_, 0);
v_fileName_505_ = lean_ctor_get(v_toInputContext_497_, 1);
v_fileMap_506_ = lean_ctor_get(v_toInputContext_497_, 2);
v_isSharedCheck_516_ = !lean_is_exclusive(v_toInputContext_497_);
if (v_isSharedCheck_516_ == 0)
{
lean_object* v_unused_517_; 
v_unused_517_ = lean_ctor_get(v_toInputContext_497_, 3);
lean_dec(v_unused_517_);
v___x_508_ = v_toInputContext_497_;
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_fileMap_506_);
lean_inc(v_fileName_505_);
lean_inc(v_inputString_504_);
lean_dec(v_toInputContext_497_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_516_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 3, v_endPos_496_);
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_inputString_504_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_fileName_505_);
lean_ctor_set(v_reuseFailAlloc_515_, 2, v_fileMap_506_);
lean_ctor_set(v_reuseFailAlloc_515_, 3, v_endPos_496_);
v___x_511_ = v_reuseFailAlloc_515_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
lean_object* v___x_513_; 
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_511_);
v___x_513_ = v___x_502_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_toParserModuleContext_498_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_toCacheableParserContext_499_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_tokens_500_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos(lean_object* v_c_519_, lean_object* v_endPos_520_, lean_object* v_endPos__valid_521_){
_start:
{
lean_object* v___x_522_; 
v___x_522_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_519_, v_endPos_520_);
return v___x_522_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(lean_object* v_x_529_, lean_object* v_x_530_){
_start:
{
if (lean_obj_tag(v_x_529_) == 0)
{
if (lean_obj_tag(v_x_530_) == 0)
{
uint8_t v___x_531_; 
v___x_531_ = 1;
return v___x_531_;
}
else
{
uint8_t v___x_532_; 
v___x_532_ = 0;
return v___x_532_;
}
}
else
{
if (lean_obj_tag(v_x_530_) == 0)
{
uint8_t v___x_533_; 
v___x_533_ = 0;
return v___x_533_;
}
else
{
lean_object* v_head_534_; lean_object* v_tail_535_; lean_object* v_head_536_; lean_object* v_tail_537_; uint8_t v___x_538_; 
v_head_534_ = lean_ctor_get(v_x_529_, 0);
v_tail_535_ = lean_ctor_get(v_x_529_, 1);
v_head_536_ = lean_ctor_get(v_x_530_, 0);
v_tail_537_ = lean_ctor_get(v_x_530_, 1);
v___x_538_ = lean_string_dec_eq(v_head_534_, v_head_536_);
if (v___x_538_ == 0)
{
return v___x_538_;
}
else
{
v_x_529_ = v_tail_535_;
v_x_530_ = v_tail_537_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(lean_object* v_x_540_, lean_object* v_x_541_){
_start:
{
uint8_t v_res_542_; lean_object* v_r_543_; 
v_res_542_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_540_, v_x_541_);
lean_dec(v_x_541_);
lean_dec(v_x_540_);
v_r_543_ = lean_box(v_res_542_);
return v_r_543_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqError_beq(lean_object* v_x_544_, lean_object* v_x_545_){
_start:
{
lean_object* v_unexpectedTk_546_; lean_object* v_unexpected_547_; lean_object* v_expected_548_; lean_object* v_unexpectedTk_549_; lean_object* v_unexpected_550_; lean_object* v_expected_551_; uint8_t v___x_552_; 
v_unexpectedTk_546_ = lean_ctor_get(v_x_544_, 0);
v_unexpected_547_ = lean_ctor_get(v_x_544_, 1);
v_expected_548_ = lean_ctor_get(v_x_544_, 2);
v_unexpectedTk_549_ = lean_ctor_get(v_x_545_, 0);
v_unexpected_550_ = lean_ctor_get(v_x_545_, 1);
v_expected_551_ = lean_ctor_get(v_x_545_, 2);
v___x_552_ = l_Lean_Syntax_structEq(v_unexpectedTk_546_, v_unexpectedTk_549_);
if (v___x_552_ == 0)
{
return v___x_552_;
}
else
{
uint8_t v___x_553_; 
v___x_553_ = lean_string_dec_eq(v_unexpected_547_, v_unexpected_550_);
if (v___x_553_ == 0)
{
return v___x_553_;
}
else
{
uint8_t v___x_554_; 
v___x_554_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_548_, v_expected_551_);
return v___x_554_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
uint8_t v_res_557_; lean_object* v_r_558_; 
v_res_557_ = l_Lean_Parser_instBEqError_beq(v_x_555_, v_x_556_);
lean_dec_ref(v_x_556_);
lean_dec_ref(v_x_555_);
v_r_558_ = lean_box(v_res_557_);
return v_r_558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* v_x_563_){
_start:
{
if (lean_obj_tag(v_x_563_) == 0)
{
lean_object* v___x_564_; 
v___x_564_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
return v___x_564_;
}
else
{
lean_object* v_tail_565_; 
v_tail_565_ = lean_ctor_get(v_x_563_, 1);
if (lean_obj_tag(v_tail_565_) == 0)
{
lean_object* v_head_566_; 
v_head_566_ = lean_ctor_get(v_x_563_, 0);
lean_inc(v_head_566_);
lean_dec_ref_known(v_x_563_, 2);
return v_head_566_;
}
else
{
lean_object* v_tail_567_; 
lean_inc_ref(v_tail_565_);
v_tail_567_ = lean_ctor_get(v_tail_565_, 1);
if (lean_obj_tag(v_tail_567_) == 0)
{
lean_object* v_head_568_; lean_object* v_head_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_head_568_ = lean_ctor_get(v_x_563_, 0);
lean_inc(v_head_568_);
lean_dec_ref_known(v_x_563_, 2);
v_head_569_ = lean_ctor_get(v_tail_565_, 0);
lean_inc(v_head_569_);
lean_dec_ref_known(v_tail_565_, 2);
v___x_570_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0));
v___x_571_ = lean_string_append(v_head_568_, v___x_570_);
v___x_572_ = lean_string_append(v___x_571_, v_head_569_);
lean_dec(v_head_569_);
return v___x_572_;
}
else
{
lean_object* v_head_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v_head_573_ = lean_ctor_get(v_x_563_, 0);
lean_inc(v_head_573_);
lean_dec_ref_known(v_x_563_, 2);
v___x_574_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_575_ = lean_string_append(v_head_573_, v___x_574_);
v___x_576_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_tail_565_);
v___x_577_ = lean_string_append(v___x_575_, v___x_576_);
lean_dec_ref(v___x_576_);
return v___x_577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object* v_as_578_){
_start:
{
lean_object* v___f_579_; lean_object* v___x_580_; 
v___f_579_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0));
v___x_580_ = l_List_eraseRepsBy___redArg(v___f_579_, v_as_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object* v_hi_581_, lean_object* v_pivot_582_, lean_object* v_as_583_, lean_object* v_i_584_, lean_object* v_k_585_){
_start:
{
uint8_t v___x_586_; 
v___x_586_ = lean_nat_dec_lt(v_k_585_, v_hi_581_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec(v_k_585_);
v___x_587_ = lean_array_fswap(v_as_583_, v_i_584_, v_hi_581_);
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v_i_584_);
lean_ctor_set(v___x_588_, 1, v___x_587_);
return v___x_588_;
}
else
{
lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_589_ = lean_array_fget_borrowed(v_as_583_, v_k_585_);
v___x_590_ = lean_string_dec_lt(v___x_589_, v_pivot_582_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_add(v_k_585_, v___x_591_);
lean_dec(v_k_585_);
v_k_585_ = v___x_592_;
goto _start;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_594_ = lean_array_fswap(v_as_583_, v_i_584_, v_k_585_);
v___x_595_ = lean_unsigned_to_nat(1u);
v___x_596_ = lean_nat_add(v_i_584_, v___x_595_);
lean_dec(v_i_584_);
v___x_597_ = lean_nat_add(v_k_585_, v___x_595_);
lean_dec(v_k_585_);
v_as_583_ = v___x_594_;
v_i_584_ = v___x_596_;
v_k_585_ = v___x_597_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object* v_hi_599_, lean_object* v_pivot_600_, lean_object* v_as_601_, lean_object* v_i_602_, lean_object* v_k_603_){
_start:
{
lean_object* v_res_604_; 
v_res_604_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_599_, v_pivot_600_, v_as_601_, v_i_602_, v_k_603_);
lean_dec_ref(v_pivot_600_);
lean_dec(v_hi_599_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_n_605_, lean_object* v_as_606_, lean_object* v_lo_607_, lean_object* v_hi_608_){
_start:
{
lean_object* v___y_610_; uint8_t v___x_620_; 
v___x_620_ = lean_nat_dec_lt(v_lo_607_, v_hi_608_);
if (v___x_620_ == 0)
{
lean_dec(v_lo_607_);
return v_as_606_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v_mid_623_; lean_object* v___y_625_; lean_object* v___y_631_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_621_ = lean_nat_add(v_lo_607_, v_hi_608_);
v___x_622_ = lean_unsigned_to_nat(1u);
v_mid_623_ = lean_nat_shiftr(v___x_621_, v___x_622_);
lean_dec(v___x_621_);
v___x_636_ = lean_array_fget_borrowed(v_as_606_, v_mid_623_);
v___x_637_ = lean_array_fget_borrowed(v_as_606_, v_lo_607_);
v___x_638_ = lean_string_dec_lt(v___x_636_, v___x_637_);
if (v___x_638_ == 0)
{
v___y_631_ = v_as_606_;
goto v___jp_630_;
}
else
{
lean_object* v___x_639_; 
v___x_639_ = lean_array_fswap(v_as_606_, v_lo_607_, v_mid_623_);
v___y_631_ = v___x_639_;
goto v___jp_630_;
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v___x_626_ = lean_array_fget_borrowed(v___y_625_, v_mid_623_);
v___x_627_ = lean_array_fget_borrowed(v___y_625_, v_hi_608_);
v___x_628_ = lean_string_dec_lt(v___x_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_dec(v_mid_623_);
v___y_610_ = v___y_625_;
goto v___jp_609_;
}
else
{
lean_object* v___x_629_; 
v___x_629_ = lean_array_fswap(v___y_625_, v_mid_623_, v_hi_608_);
lean_dec(v_mid_623_);
v___y_610_ = v___x_629_;
goto v___jp_609_;
}
}
v___jp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_632_ = lean_array_fget_borrowed(v___y_631_, v_hi_608_);
v___x_633_ = lean_array_fget_borrowed(v___y_631_, v_lo_607_);
v___x_634_ = lean_string_dec_lt(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
v___y_625_ = v___y_631_;
goto v___jp_624_;
}
else
{
lean_object* v___x_635_; 
v___x_635_ = lean_array_fswap(v___y_631_, v_lo_607_, v_hi_608_);
v___y_625_ = v___x_635_;
goto v___jp_624_;
}
}
}
v___jp_609_:
{
lean_object* v_pivot_611_; lean_object* v___x_612_; lean_object* v_fst_613_; lean_object* v_snd_614_; uint8_t v___x_615_; 
v_pivot_611_ = lean_array_fget(v___y_610_, v_hi_608_);
lean_inc_n(v_lo_607_, 2);
v___x_612_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_608_, v_pivot_611_, v___y_610_, v_lo_607_, v_lo_607_);
lean_dec(v_pivot_611_);
v_fst_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_fst_613_);
v_snd_614_ = lean_ctor_get(v___x_612_, 1);
lean_inc(v_snd_614_);
lean_dec_ref(v___x_612_);
v___x_615_ = lean_nat_dec_le(v_hi_608_, v_fst_613_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_616_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_605_, v_snd_614_, v_lo_607_, v_fst_613_);
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_add(v_fst_613_, v___x_617_);
lean_dec(v_fst_613_);
v_as_606_ = v___x_616_;
v_lo_607_ = v___x_618_;
goto _start;
}
else
{
lean_dec(v_fst_613_);
lean_dec(v_lo_607_);
return v_snd_614_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_n_640_, lean_object* v_as_641_, lean_object* v_lo_642_, lean_object* v_hi_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_640_, v_as_641_, v_lo_642_, v_hi_643_);
lean_dec(v_hi_643_);
lean_dec(v_n_640_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_647_){
_start:
{
lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v_unexpected_680_; lean_object* v_expected_681_; lean_object* v___y_683_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_unexpected_680_ = lean_ctor_get(v_e_647_, 1);
lean_inc_ref(v_unexpected_680_);
v_expected_681_ = lean_ctor_get(v_e_647_, 2);
lean_inc(v_expected_681_);
lean_dec_ref(v_e_647_);
v___x_693_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_694_ = lean_string_dec_eq(v_unexpected_680_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_box(0);
v___x_696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_696_, 0, v_unexpected_680_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
v___y_683_ = v___x_696_;
goto v___jp_682_;
}
else
{
lean_object* v___x_697_; 
lean_dec_ref(v_unexpected_680_);
v___x_697_ = lean_box(0);
v___y_683_ = v___x_697_;
goto v___jp_682_;
}
v___jp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_652_ = l_List_appendTR___redArg(v___y_649_, v___y_650_);
v___x_653_ = l_String_intercalate(v___x_651_, v___x_652_);
return v___x_653_;
}
v___jp_654_:
{
lean_object* v___x_658_; lean_object* v_expected_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_658_ = lean_array_to_list(v___y_657_);
v_expected_659_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_658_);
v___x_660_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_661_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_659_);
v___x_662_ = lean_string_append(v___x_660_, v___x_661_);
lean_dec_ref(v___x_661_);
v___x_663_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_663_, 0, v___x_662_);
lean_ctor_set(v___x_663_, 1, v___y_655_);
v___y_649_ = v___y_656_;
v___y_650_ = v___x_663_;
goto v___jp_648_;
}
v___jp_664_:
{
lean_object* v___x_671_; 
v___x_671_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_665_, v___y_667_, v___y_669_, v___y_670_);
lean_dec(v___y_670_);
lean_dec(v___y_665_);
v___y_655_ = v___y_666_;
v___y_656_ = v___y_668_;
v___y_657_ = v___x_671_;
goto v___jp_654_;
}
v___jp_672_:
{
uint8_t v___x_679_; 
v___x_679_ = lean_nat_dec_le(v___y_678_, v___y_673_);
if (v___x_679_ == 0)
{
lean_dec(v___y_673_);
lean_inc(v___y_678_);
v___y_665_ = v___y_674_;
v___y_666_ = v___y_675_;
v___y_667_ = v___y_676_;
v___y_668_ = v___y_677_;
v___y_669_ = v___y_678_;
v___y_670_ = v___y_678_;
goto v___jp_664_;
}
else
{
v___y_665_ = v___y_674_;
v___y_666_ = v___y_675_;
v___y_667_ = v___y_676_;
v___y_668_ = v___y_677_;
v___y_669_ = v___y_678_;
v___y_670_ = v___y_673_;
goto v___jp_664_;
}
}
v___jp_682_:
{
lean_object* v___x_684_; uint8_t v___x_685_; 
v___x_684_ = lean_box(0);
v___x_685_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_681_, v___x_684_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v___x_686_ = lean_array_mk(v_expected_681_);
v___x_687_ = lean_array_get_size(v___x_686_);
v___x_688_ = lean_unsigned_to_nat(0u);
v___x_689_ = lean_nat_dec_eq(v___x_687_, v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_unsigned_to_nat(1u);
v___x_691_ = lean_nat_sub(v___x_687_, v___x_690_);
v___x_692_ = lean_nat_dec_le(v___x_688_, v___x_691_);
if (v___x_692_ == 0)
{
lean_inc(v___x_691_);
v___y_673_ = v___x_691_;
v___y_674_ = v___x_687_;
v___y_675_ = v___x_684_;
v___y_676_ = v___x_686_;
v___y_677_ = v___y_683_;
v___y_678_ = v___x_691_;
goto v___jp_672_;
}
else
{
v___y_673_ = v___x_691_;
v___y_674_ = v___x_687_;
v___y_675_ = v___x_684_;
v___y_676_ = v___x_686_;
v___y_677_ = v___y_683_;
v___y_678_ = v___x_688_;
goto v___jp_672_;
}
}
else
{
v___y_655_ = v___x_684_;
v___y_656_ = v___y_683_;
v___y_657_ = v___x_686_;
goto v___jp_654_;
}
}
else
{
lean_dec(v_expected_681_);
v___y_649_ = v___y_683_;
v___y_650_ = v___x_684_;
goto v___jp_648_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_698_, lean_object* v_as_699_, lean_object* v_lo_700_, lean_object* v_hi_701_, lean_object* v_w_702_, lean_object* v_hlo_703_, lean_object* v_hhi_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_698_, v_as_699_, v_lo_700_, v_hi_701_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_706_, lean_object* v_as_707_, lean_object* v_lo_708_, lean_object* v_hi_709_, lean_object* v_w_710_, lean_object* v_hlo_711_, lean_object* v_hhi_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_706_, v_as_707_, v_lo_708_, v_hi_709_, v_w_710_, v_hlo_711_, v_hhi_712_);
lean_dec(v_hi_709_);
lean_dec(v_n_706_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object* v_n_714_, lean_object* v_lo_715_, lean_object* v_hi_716_, lean_object* v_hhi_717_, lean_object* v_pivot_718_, lean_object* v_as_719_, lean_object* v_i_720_, lean_object* v_k_721_, lean_object* v_ilo_722_, lean_object* v_ik_723_, lean_object* v_w_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_716_, v_pivot_718_, v_as_719_, v_i_720_, v_k_721_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object* v_n_726_, lean_object* v_lo_727_, lean_object* v_hi_728_, lean_object* v_hhi_729_, lean_object* v_pivot_730_, lean_object* v_as_731_, lean_object* v_i_732_, lean_object* v_k_733_, lean_object* v_ilo_734_, lean_object* v_ik_735_, lean_object* v_w_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_726_, v_lo_727_, v_hi_728_, v_hhi_729_, v_pivot_730_, v_as_731_, v_i_732_, v_k_733_, v_ilo_734_, v_ik_735_, v_w_736_);
lean_dec_ref(v_pivot_730_);
lean_dec(v_hi_728_);
lean_dec(v_lo_727_);
lean_dec(v_n_726_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_740_, lean_object* v_e_u2082_741_){
_start:
{
lean_object* v_unexpectedTk_742_; lean_object* v_unexpected_743_; lean_object* v_expected_744_; lean_object* v___y_746_; lean_object* v___x_758_; uint8_t v___x_759_; 
v_unexpectedTk_742_ = lean_ctor_get(v_e_u2082_741_, 0);
lean_inc(v_unexpectedTk_742_);
v_unexpected_743_ = lean_ctor_get(v_e_u2082_741_, 1);
lean_inc_ref(v_unexpected_743_);
v_expected_744_ = lean_ctor_get(v_e_u2082_741_, 2);
lean_inc(v_expected_744_);
lean_dec_ref(v_e_u2082_741_);
v___x_758_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_759_ = lean_string_dec_eq(v_unexpected_743_, v___x_758_);
if (v___x_759_ == 0)
{
v___y_746_ = v_unexpected_743_;
goto v___jp_745_;
}
else
{
lean_object* v_unexpected_760_; 
lean_dec_ref(v_unexpected_743_);
v_unexpected_760_ = lean_ctor_get(v_e_u2081_740_, 1);
lean_inc_ref(v_unexpected_760_);
v___y_746_ = v_unexpected_760_;
goto v___jp_745_;
}
v___jp_745_:
{
lean_object* v_expected_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_755_; 
v_expected_747_ = lean_ctor_get(v_e_u2081_740_, 2);
v_isSharedCheck_755_ = !lean_is_exclusive(v_e_u2081_740_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; lean_object* v_unused_757_; 
v_unused_756_ = lean_ctor_get(v_e_u2081_740_, 1);
lean_dec(v_unused_756_);
v_unused_757_ = lean_ctor_get(v_e_u2081_740_, 0);
lean_dec(v_unused_757_);
v___x_749_ = v_e_u2081_740_;
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_expected_747_);
lean_dec(v_e_u2081_740_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_755_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_751_; lean_object* v___x_753_; 
v___x_751_ = l_List_appendTR___redArg(v_expected_747_, v_expected_744_);
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 2, v___x_751_);
lean_ctor_set(v___x_749_, 1, v___y_746_);
lean_ctor_set(v___x_749_, 0, v_unexpectedTk_742_);
v___x_753_ = v___x_749_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_unexpectedTk_742_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v___y_746_);
lean_ctor_set(v_reuseFailAlloc_754_, 2, v___x_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(lean_object* v_x_761_, lean_object* v_x_762_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
if (lean_obj_tag(v_x_762_) == 0)
{
uint8_t v___x_763_; 
v___x_763_ = 1;
return v___x_763_;
}
else
{
uint8_t v___x_764_; 
v___x_764_ = 0;
return v___x_764_;
}
}
else
{
if (lean_obj_tag(v_x_762_) == 0)
{
uint8_t v___x_765_; 
v___x_765_ = 0;
return v___x_765_;
}
else
{
lean_object* v_val_766_; lean_object* v_val_767_; uint8_t v_decide_768_; 
v_val_766_ = lean_ctor_get(v_x_761_, 0);
v_val_767_ = lean_ctor_get(v_x_762_, 0);
v_decide_768_ = lean_nat_dec_eq(v_val_766_, v_val_767_);
return v_decide_768_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0___boxed(lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_x_769_, v_x_770_);
lean_dec(v_x_770_);
lean_dec(v_x_769_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(lean_object* v_xs_773_, lean_object* v_ys_774_, lean_object* v_x_775_){
_start:
{
lean_object* v_zero_776_; uint8_t v_isZero_777_; 
v_zero_776_ = lean_unsigned_to_nat(0u);
v_isZero_777_ = lean_nat_dec_eq(v_x_775_, v_zero_776_);
if (v_isZero_777_ == 1)
{
lean_dec(v_x_775_);
return v_isZero_777_;
}
else
{
lean_object* v_one_778_; lean_object* v_n_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_one_778_ = lean_unsigned_to_nat(1u);
v_n_779_ = lean_nat_sub(v_x_775_, v_one_778_);
lean_dec(v_x_775_);
v___x_780_ = lean_array_fget_borrowed(v_xs_773_, v_n_779_);
v___x_781_ = lean_array_fget_borrowed(v_ys_774_, v_n_779_);
v___x_782_ = lean_string_dec_eq(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_dec(v_n_779_);
return v___x_782_;
}
else
{
v_x_775_ = v_n_779_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg___boxed(lean_object* v_xs_784_, lean_object* v_ys_785_, lean_object* v_x_786_){
_start:
{
uint8_t v_res_787_; lean_object* v_r_788_; 
v_res_787_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_784_, v_ys_785_, v_x_786_);
lean_dec_ref(v_ys_785_);
lean_dec_ref(v_xs_784_);
v_r_788_ = lean_box(v_res_787_);
return v_r_788_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_789_, lean_object* v_x_790_){
_start:
{
lean_object* v_toCacheableParserContext_791_; lean_object* v_parserName_792_; lean_object* v_pos_793_; lean_object* v_toCacheableParserContext_794_; lean_object* v_parserName_795_; lean_object* v_pos_796_; lean_object* v_prec_800_; lean_object* v_quotDepth_801_; uint8_t v_suppressInsideQuot_802_; lean_object* v_savedPos_x3f_803_; lean_object* v_forbiddenTks_804_; lean_object* v_prec_805_; lean_object* v_quotDepth_806_; uint8_t v_suppressInsideQuot_807_; lean_object* v_savedPos_x3f_808_; lean_object* v_forbiddenTks_809_; uint8_t v___x_819_; 
v_toCacheableParserContext_791_ = lean_ctor_get(v_x_789_, 0);
v_parserName_792_ = lean_ctor_get(v_x_789_, 1);
v_pos_793_ = lean_ctor_get(v_x_789_, 2);
v_toCacheableParserContext_794_ = lean_ctor_get(v_x_790_, 0);
v_parserName_795_ = lean_ctor_get(v_x_790_, 1);
v_pos_796_ = lean_ctor_get(v_x_790_, 2);
v_prec_800_ = lean_ctor_get(v_toCacheableParserContext_791_, 0);
v_quotDepth_801_ = lean_ctor_get(v_toCacheableParserContext_791_, 1);
v_suppressInsideQuot_802_ = lean_ctor_get_uint8(v_toCacheableParserContext_791_, sizeof(void*)*4);
v_savedPos_x3f_803_ = lean_ctor_get(v_toCacheableParserContext_791_, 2);
v_forbiddenTks_804_ = lean_ctor_get(v_toCacheableParserContext_791_, 3);
v_prec_805_ = lean_ctor_get(v_toCacheableParserContext_794_, 0);
v_quotDepth_806_ = lean_ctor_get(v_toCacheableParserContext_794_, 1);
v_suppressInsideQuot_807_ = lean_ctor_get_uint8(v_toCacheableParserContext_794_, sizeof(void*)*4);
v_savedPos_x3f_808_ = lean_ctor_get(v_toCacheableParserContext_794_, 2);
v_forbiddenTks_809_ = lean_ctor_get(v_toCacheableParserContext_794_, 3);
v___x_819_ = lean_nat_dec_eq(v_prec_800_, v_prec_805_);
if (v___x_819_ == 0)
{
return v___x_819_;
}
else
{
uint8_t v___x_820_; 
v___x_820_ = lean_nat_dec_eq(v_quotDepth_801_, v_quotDepth_806_);
if (v___x_820_ == 0)
{
return v___x_820_;
}
else
{
if (v_suppressInsideQuot_807_ == 0)
{
if (v_suppressInsideQuot_802_ == 0)
{
goto v___jp_810_;
}
else
{
return v_suppressInsideQuot_807_;
}
}
else
{
if (v_suppressInsideQuot_802_ == 0)
{
return v_suppressInsideQuot_802_;
}
else
{
goto v___jp_810_;
}
}
}
}
v___jp_797_:
{
uint8_t v___x_798_; 
v___x_798_ = lean_name_eq(v_parserName_792_, v_parserName_795_);
if (v___x_798_ == 0)
{
return v___x_798_;
}
else
{
uint8_t v_decide_799_; 
v_decide_799_ = lean_nat_dec_eq(v_pos_793_, v_pos_796_);
return v_decide_799_;
}
}
v___jp_810_:
{
uint8_t v___x_811_; 
v___x_811_ = l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_savedPos_x3f_803_, v_savedPos_x3f_808_);
if (v___x_811_ == 0)
{
return v___x_811_;
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
return v___x_817_;
}
else
{
uint8_t v___x_818_; 
v___x_818_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_forbiddenTks_804_, v_forbiddenTks_809_, v___x_815_);
if (v___x_818_ == 0)
{
return v___x_818_;
}
else
{
goto v___jp_797_;
}
}
}
else
{
goto v___jp_797_;
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
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_box(0);
v___x_854_ = lean_unsigned_to_nat(16u);
v___x_855_ = lean_mk_array(v___x_854_, v___x_853_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_856_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v___x_856_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_859_){
_start:
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_860_ = lean_string_utf8_byte_size(v_input_859_);
v___x_861_ = lean_unsigned_to_nat(1u);
v___x_862_ = lean_nat_add(v___x_860_, v___x_861_);
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_box(0);
v___x_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_865_, 0, v___x_862_);
lean_ctor_set(v___x_865_, 1, v___x_863_);
lean_ctor_set(v___x_865_, 2, v___x_864_);
v___x_866_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_867_, 0, v___x_865_);
lean_ctor_set(v___x_867_, 1, v___x_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Lean_Parser_initCacheForInput(v_input_868_);
lean_dec_ref(v_input_868_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_870_){
_start:
{
lean_object* v_raw_871_; lean_object* v_drop_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_raw_871_ = lean_ctor_get(v_stack_870_, 0);
lean_inc_ref(v_raw_871_);
v_drop_872_ = lean_ctor_get(v_stack_870_, 1);
lean_inc(v_drop_872_);
lean_dec_ref(v_stack_870_);
v___x_873_ = lean_array_get_size(v_raw_871_);
v___x_874_ = l_Array_toSubarray___redArg(v_raw_871_, v_drop_872_, v___x_873_);
return v___x_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_881_){
_start:
{
lean_object* v_raw_882_; lean_object* v_drop_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_raw_882_ = lean_ctor_get(v_stack_881_, 0);
v_drop_883_ = lean_ctor_get(v_stack_881_, 1);
v___x_884_ = lean_array_get_size(v_raw_882_);
v___x_885_ = lean_nat_sub(v___x_884_, v_drop_883_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l_Lean_Parser_SyntaxStack_size(v_stack_886_);
lean_dec_ref(v_stack_886_);
return v_res_887_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_888_){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_889_ = l_Lean_Parser_SyntaxStack_size(v_stack_888_);
v___x_890_ = lean_unsigned_to_nat(0u);
v___x_891_ = lean_nat_dec_eq(v___x_889_, v___x_890_);
lean_dec(v___x_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_892_);
lean_dec_ref(v_stack_892_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_895_, lean_object* v_n_896_){
_start:
{
lean_object* v_raw_897_; lean_object* v_drop_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_907_; 
v_raw_897_ = lean_ctor_get(v_stack_895_, 0);
v_drop_898_ = lean_ctor_get(v_stack_895_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_stack_895_);
if (v_isSharedCheck_907_ == 0)
{
v___x_900_ = v_stack_895_;
v_isShared_901_ = v_isSharedCheck_907_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_drop_898_);
lean_inc(v_raw_897_);
lean_dec(v_stack_895_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_907_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_905_; 
v___x_902_ = lean_nat_add(v_drop_898_, v_n_896_);
v___x_903_ = l_Array_shrink___redArg(v_raw_897_, v___x_902_);
lean_dec(v___x_902_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 0, v___x_903_);
v___x_905_ = v___x_900_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v___x_903_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_drop_898_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_908_, lean_object* v_n_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_908_, v_n_909_);
lean_dec(v_n_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_raw_913_; lean_object* v_drop_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_922_; 
v_raw_913_ = lean_ctor_get(v_stack_911_, 0);
v_drop_914_ = lean_ctor_get(v_stack_911_, 1);
v_isSharedCheck_922_ = !lean_is_exclusive(v_stack_911_);
if (v_isSharedCheck_922_ == 0)
{
v___x_916_ = v_stack_911_;
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_drop_914_);
lean_inc(v_raw_913_);
lean_dec(v_stack_911_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_922_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_918_; lean_object* v___x_920_; 
v___x_918_ = lean_array_push(v_raw_913_, v_a_912_);
if (v_isShared_917_ == 0)
{
lean_ctor_set(v___x_916_, 0, v___x_918_);
v___x_920_ = v___x_916_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
lean_ctor_set(v_reuseFailAlloc_921_, 1, v_drop_914_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_923_){
_start:
{
lean_object* v___x_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v___x_924_ = lean_unsigned_to_nat(0u);
v___x_925_ = l_Lean_Parser_SyntaxStack_size(v_stack_923_);
v___x_926_ = lean_nat_dec_lt(v___x_924_, v___x_925_);
lean_dec(v___x_925_);
if (v___x_926_ == 0)
{
return v_stack_923_;
}
else
{
lean_object* v_raw_927_; lean_object* v_drop_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_936_; 
v_raw_927_ = lean_ctor_get(v_stack_923_, 0);
v_drop_928_ = lean_ctor_get(v_stack_923_, 1);
v_isSharedCheck_936_ = !lean_is_exclusive(v_stack_923_);
if (v_isSharedCheck_936_ == 0)
{
v___x_930_ = v_stack_923_;
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_drop_928_);
lean_inc(v_raw_927_);
lean_dec(v_stack_923_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_array_pop(v_raw_927_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_932_);
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_drop_928_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_937_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_box(0);
v___x_939_ = lean_panic_fn_borrowed(v___x_938_, v_msg_937_);
return v___x_939_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; 
v___x_943_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_944_ = lean_unsigned_to_nat(4u);
v___x_945_ = lean_unsigned_to_nat(315u);
v___x_946_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_947_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_948_ = l_mkPanicMessageWithDecl(v___x_947_, v___x_946_, v___x_945_, v___x_944_, v___x_943_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_949_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = l_Lean_Parser_SyntaxStack_size(v_stack_949_);
v___x_952_ = lean_nat_dec_lt(v___x_950_, v___x_951_);
lean_dec(v___x_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_954_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_953_);
return v___x_954_;
}
else
{
lean_object* v_raw_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v_raw_955_ = lean_ctor_get(v_stack_949_, 0);
v___x_956_ = lean_box(0);
v___x_957_ = lean_array_get_size(v_raw_955_);
v___x_958_ = lean_unsigned_to_nat(1u);
v___x_959_ = lean_nat_sub(v___x_957_, v___x_958_);
v___x_960_ = lean_array_get_borrowed(v___x_956_, v_raw_955_, v___x_959_);
lean_dec(v___x_959_);
lean_inc(v___x_960_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Parser_SyntaxStack_back(v_stack_961_);
lean_dec_ref(v_stack_961_);
return v_res_962_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v___x_965_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_966_ = lean_unsigned_to_nat(4u);
v___x_967_ = lean_unsigned_to_nat(321u);
v___x_968_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_969_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_970_ = l_mkPanicMessageWithDecl(v___x_969_, v___x_968_, v___x_967_, v___x_966_, v___x_965_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_971_, lean_object* v_i_972_){
_start:
{
lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_973_ = l_Lean_Parser_SyntaxStack_size(v_stack_971_);
v___x_974_ = lean_nat_dec_lt(v_i_972_, v___x_973_);
lean_dec(v___x_973_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_976_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_975_);
return v___x_976_;
}
else
{
lean_object* v_raw_977_; lean_object* v_drop_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_raw_977_ = lean_ctor_get(v_stack_971_, 0);
v_drop_978_ = lean_ctor_get(v_stack_971_, 1);
v___x_979_ = lean_box(0);
v___x_980_ = lean_nat_add(v_drop_978_, v_i_972_);
v___x_981_ = lean_array_get_borrowed(v___x_979_, v_raw_977_, v___x_980_);
lean_dec(v___x_980_);
lean_inc(v___x_981_);
return v___x_981_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_982_, lean_object* v_i_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_982_, v_i_983_);
lean_dec(v_i_983_);
lean_dec_ref(v_stack_982_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_985_, lean_object* v_start_986_, lean_object* v_stop_987_){
_start:
{
lean_object* v_raw_988_; lean_object* v_drop_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_raw_988_ = lean_ctor_get(v_stack_985_, 0);
v_drop_989_ = lean_ctor_get(v_stack_985_, 1);
v___x_990_ = lean_nat_add(v_drop_989_, v_start_986_);
v___x_991_ = lean_nat_add(v_drop_989_, v_stop_987_);
v___x_992_ = l_Array_extract___redArg(v_raw_988_, v___x_990_, v___x_991_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_993_, lean_object* v_start_994_, lean_object* v_stop_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Lean_Parser_SyntaxStack_extract(v_stack_993_, v_start_994_, v_stop_995_);
lean_dec(v_stop_995_);
lean_dec(v_start_994_);
lean_dec_ref(v_stack_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_997_, lean_object* v_stxs_998_){
_start:
{
lean_object* v_raw_999_; lean_object* v_drop_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1008_; 
v_raw_999_ = lean_ctor_get(v_stack_997_, 0);
v_drop_1000_ = lean_ctor_get(v_stack_997_, 1);
v_isSharedCheck_1008_ = !lean_is_exclusive(v_stack_997_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1002_ = v_stack_997_;
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_drop_1000_);
lean_inc(v_raw_999_);
lean_dec(v_stack_997_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1008_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1004_; lean_object* v___x_1006_; 
v___x_1004_ = l_Array_append___redArg(v_raw_999_, v_stxs_998_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1004_);
v___x_1006_ = v___x_1002_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v___x_1004_);
lean_ctor_set(v_reuseFailAlloc_1007_, 1, v_drop_1000_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_1009_, lean_object* v_stxs_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_1009_, v_stxs_1010_);
lean_dec_ref(v_stxs_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_1012_, lean_object* v_stxs_1013_){
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
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_1024_, lean_object* v_stxs_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_1024_, v_stxs_1025_);
lean_dec_ref(v_stxs_1025_);
return v_res_1026_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_1029_){
_start:
{
lean_object* v_errorMsg_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_errorMsg_1030_ = lean_ctor_get(v_s_1029_, 4);
lean_inc(v_errorMsg_1030_);
lean_dec_ref(v_s_1029_);
v___x_1031_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_1032_ = lean_box(0);
v___x_1033_ = l_instBEqOption_beq___redArg(v___x_1031_, v_errorMsg_1030_, v___x_1032_);
if (v___x_1033_ == 0)
{
uint8_t v___x_1034_; 
v___x_1034_ = 1;
return v___x_1034_;
}
else
{
uint8_t v___x_1035_; 
v___x_1035_ = 0;
return v___x_1035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_1036_){
_start:
{
uint8_t v_res_1037_; lean_object* v_r_1038_; 
v_res_1037_ = l_Lean_Parser_ParserState_hasError(v_s_1036_);
v_r_1038_ = lean_box(v_res_1037_);
return v_r_1038_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_1039_){
_start:
{
lean_object* v_stxStack_1040_; lean_object* v___x_1041_; 
v_stxStack_1040_ = lean_ctor_get(v_s_1039_, 0);
v___x_1041_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1040_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_Parser_ParserState_stackSize(v_s_1042_);
lean_dec_ref(v_s_1042_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_1044_, lean_object* v_iniStackSz_1045_, lean_object* v_iniPos_1046_){
_start:
{
lean_object* v_stxStack_1047_; lean_object* v_lhsPrec_1048_; lean_object* v_cache_1049_; lean_object* v_recoveredErrors_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1059_; 
v_stxStack_1047_ = lean_ctor_get(v_s_1044_, 0);
v_lhsPrec_1048_ = lean_ctor_get(v_s_1044_, 1);
v_cache_1049_ = lean_ctor_get(v_s_1044_, 3);
v_recoveredErrors_1050_ = lean_ctor_get(v_s_1044_, 5);
v_isSharedCheck_1059_ = !lean_is_exclusive(v_s_1044_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; lean_object* v_unused_1061_; 
v_unused_1060_ = lean_ctor_get(v_s_1044_, 4);
lean_dec(v_unused_1060_);
v_unused_1061_ = lean_ctor_get(v_s_1044_, 2);
lean_dec(v_unused_1061_);
v___x_1052_ = v_s_1044_;
v_isShared_1053_ = v_isSharedCheck_1059_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_recoveredErrors_1050_);
lean_inc(v_cache_1049_);
lean_inc(v_lhsPrec_1048_);
lean_inc(v_stxStack_1047_);
lean_dec(v_s_1044_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1059_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1054_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1047_, v_iniStackSz_1045_);
v___x_1055_ = lean_box(0);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 4, v___x_1055_);
lean_ctor_set(v___x_1052_, 2, v_iniPos_1046_);
lean_ctor_set(v___x_1052_, 0, v___x_1054_);
v___x_1057_ = v___x_1052_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_lhsPrec_1048_);
lean_ctor_set(v_reuseFailAlloc_1058_, 2, v_iniPos_1046_);
lean_ctor_set(v_reuseFailAlloc_1058_, 3, v_cache_1049_);
lean_ctor_set(v_reuseFailAlloc_1058_, 4, v___x_1055_);
lean_ctor_set(v_reuseFailAlloc_1058_, 5, v_recoveredErrors_1050_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_1062_, lean_object* v_iniStackSz_1063_, lean_object* v_iniPos_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_Parser_ParserState_restore(v_s_1062_, v_iniStackSz_1063_, v_iniPos_1064_);
lean_dec(v_iniStackSz_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_1066_, lean_object* v_pos_1067_){
_start:
{
lean_object* v_stxStack_1068_; lean_object* v_lhsPrec_1069_; lean_object* v_cache_1070_; lean_object* v_errorMsg_1071_; lean_object* v_recoveredErrors_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
v_stxStack_1068_ = lean_ctor_get(v_s_1066_, 0);
v_lhsPrec_1069_ = lean_ctor_get(v_s_1066_, 1);
v_cache_1070_ = lean_ctor_get(v_s_1066_, 3);
v_errorMsg_1071_ = lean_ctor_get(v_s_1066_, 4);
v_recoveredErrors_1072_ = lean_ctor_get(v_s_1066_, 5);
v_isSharedCheck_1079_ = !lean_is_exclusive(v_s_1066_);
if (v_isSharedCheck_1079_ == 0)
{
lean_object* v_unused_1080_; 
v_unused_1080_ = lean_ctor_get(v_s_1066_, 2);
lean_dec(v_unused_1080_);
v___x_1074_ = v_s_1066_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_recoveredErrors_1072_);
lean_inc(v_errorMsg_1071_);
lean_inc(v_cache_1070_);
lean_inc(v_lhsPrec_1069_);
lean_inc(v_stxStack_1068_);
lean_dec(v_s_1066_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 2, v_pos_1067_);
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_stxStack_1068_);
lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_lhsPrec_1069_);
lean_ctor_set(v_reuseFailAlloc_1078_, 2, v_pos_1067_);
lean_ctor_set(v_reuseFailAlloc_1078_, 3, v_cache_1070_);
lean_ctor_set(v_reuseFailAlloc_1078_, 4, v_errorMsg_1071_);
lean_ctor_set(v_reuseFailAlloc_1078_, 5, v_recoveredErrors_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_1081_, lean_object* v_cache_1082_){
_start:
{
lean_object* v_stxStack_1083_; lean_object* v_lhsPrec_1084_; lean_object* v_pos_1085_; lean_object* v_errorMsg_1086_; lean_object* v_recoveredErrors_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_stxStack_1083_ = lean_ctor_get(v_s_1081_, 0);
v_lhsPrec_1084_ = lean_ctor_get(v_s_1081_, 1);
v_pos_1085_ = lean_ctor_get(v_s_1081_, 2);
v_errorMsg_1086_ = lean_ctor_get(v_s_1081_, 4);
v_recoveredErrors_1087_ = lean_ctor_get(v_s_1081_, 5);
v_isSharedCheck_1094_ = !lean_is_exclusive(v_s_1081_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v_s_1081_, 3);
lean_dec(v_unused_1095_);
v___x_1089_ = v_s_1081_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_recoveredErrors_1087_);
lean_inc(v_errorMsg_1086_);
lean_inc(v_pos_1085_);
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
lean_ctor_set(v___x_1089_, 3, v_cache_1082_);
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v_stxStack_1083_);
lean_ctor_set(v_reuseFailAlloc_1093_, 1, v_lhsPrec_1084_);
lean_ctor_set(v_reuseFailAlloc_1093_, 2, v_pos_1085_);
lean_ctor_set(v_reuseFailAlloc_1093_, 3, v_cache_1082_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_1096_, lean_object* v_n_1097_){
_start:
{
lean_object* v_stxStack_1098_; lean_object* v_lhsPrec_1099_; lean_object* v_pos_1100_; lean_object* v_cache_1101_; lean_object* v_errorMsg_1102_; lean_object* v_recoveredErrors_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1111_; 
v_stxStack_1098_ = lean_ctor_get(v_s_1096_, 0);
v_lhsPrec_1099_ = lean_ctor_get(v_s_1096_, 1);
v_pos_1100_ = lean_ctor_get(v_s_1096_, 2);
v_cache_1101_ = lean_ctor_get(v_s_1096_, 3);
v_errorMsg_1102_ = lean_ctor_get(v_s_1096_, 4);
v_recoveredErrors_1103_ = lean_ctor_get(v_s_1096_, 5);
v_isSharedCheck_1111_ = !lean_is_exclusive(v_s_1096_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1105_ = v_s_1096_;
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_recoveredErrors_1103_);
lean_inc(v_errorMsg_1102_);
lean_inc(v_cache_1101_);
lean_inc(v_pos_1100_);
lean_inc(v_lhsPrec_1099_);
lean_inc(v_stxStack_1098_);
lean_dec(v_s_1096_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1111_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; lean_object* v___x_1109_; 
v___x_1107_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1098_, v_n_1097_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1107_);
v___x_1109_ = v___x_1105_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
lean_ctor_set(v_reuseFailAlloc_1110_, 1, v_lhsPrec_1099_);
lean_ctor_set(v_reuseFailAlloc_1110_, 2, v_pos_1100_);
lean_ctor_set(v_reuseFailAlloc_1110_, 3, v_cache_1101_);
lean_ctor_set(v_reuseFailAlloc_1110_, 4, v_errorMsg_1102_);
lean_ctor_set(v_reuseFailAlloc_1110_, 5, v_recoveredErrors_1103_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1112_){
_start:
{
lean_object* v_stxStack_1113_; lean_object* v_lhsPrec_1114_; lean_object* v_pos_1115_; lean_object* v_cache_1116_; lean_object* v_errorMsg_1117_; lean_object* v_recoveredErrors_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1126_; 
v_stxStack_1113_ = lean_ctor_get(v_s_1112_, 0);
v_lhsPrec_1114_ = lean_ctor_get(v_s_1112_, 1);
v_pos_1115_ = lean_ctor_get(v_s_1112_, 2);
v_cache_1116_ = lean_ctor_get(v_s_1112_, 3);
v_errorMsg_1117_ = lean_ctor_get(v_s_1112_, 4);
v_recoveredErrors_1118_ = lean_ctor_get(v_s_1112_, 5);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_s_1112_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1120_ = v_s_1112_;
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
lean_dec(v_s_1112_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1126_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1124_; 
v___x_1122_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1113_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1127_, lean_object* v_iniStackSz_1128_){
_start:
{
lean_object* v_stxStack_1129_; lean_object* v_lhsPrec_1130_; lean_object* v_pos_1131_; lean_object* v_cache_1132_; lean_object* v_errorMsg_1133_; lean_object* v_recoveredErrors_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1142_; 
v_stxStack_1129_ = lean_ctor_get(v_s_1127_, 0);
v_lhsPrec_1130_ = lean_ctor_get(v_s_1127_, 1);
v_pos_1131_ = lean_ctor_get(v_s_1127_, 2);
v_cache_1132_ = lean_ctor_get(v_s_1127_, 3);
v_errorMsg_1133_ = lean_ctor_get(v_s_1127_, 4);
v_recoveredErrors_1134_ = lean_ctor_get(v_s_1127_, 5);
v_isSharedCheck_1142_ = !lean_is_exclusive(v_s_1127_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1136_ = v_s_1127_;
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_recoveredErrors_1134_);
lean_inc(v_errorMsg_1133_);
lean_inc(v_cache_1132_);
lean_inc(v_pos_1131_);
lean_inc(v_lhsPrec_1130_);
lean_inc(v_stxStack_1129_);
lean_dec(v_s_1127_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1142_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; lean_object* v___x_1140_; 
v___x_1138_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1129_, v_iniStackSz_1128_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1138_);
v___x_1140_ = v___x_1136_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v___x_1138_);
lean_ctor_set(v_reuseFailAlloc_1141_, 1, v_lhsPrec_1130_);
lean_ctor_set(v_reuseFailAlloc_1141_, 2, v_pos_1131_);
lean_ctor_set(v_reuseFailAlloc_1141_, 3, v_cache_1132_);
lean_ctor_set(v_reuseFailAlloc_1141_, 4, v_errorMsg_1133_);
lean_ctor_set(v_reuseFailAlloc_1141_, 5, v_recoveredErrors_1134_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1143_, lean_object* v_iniStackSz_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1143_, v_iniStackSz_1144_);
lean_dec(v_iniStackSz_1144_);
return v_res_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1146_, lean_object* v_c_1147_, lean_object* v_pos_1148_){
_start:
{
lean_object* v_toInputContext_1149_; lean_object* v_stxStack_1150_; lean_object* v_lhsPrec_1151_; lean_object* v_cache_1152_; lean_object* v_errorMsg_1153_; lean_object* v_recoveredErrors_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1163_; 
v_toInputContext_1149_ = lean_ctor_get(v_c_1147_, 0);
v_stxStack_1150_ = lean_ctor_get(v_s_1146_, 0);
v_lhsPrec_1151_ = lean_ctor_get(v_s_1146_, 1);
v_cache_1152_ = lean_ctor_get(v_s_1146_, 3);
v_errorMsg_1153_ = lean_ctor_get(v_s_1146_, 4);
v_recoveredErrors_1154_ = lean_ctor_get(v_s_1146_, 5);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_s_1146_);
if (v_isSharedCheck_1163_ == 0)
{
lean_object* v_unused_1164_; 
v_unused_1164_ = lean_ctor_get(v_s_1146_, 2);
lean_dec(v_unused_1164_);
v___x_1156_ = v_s_1146_;
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_recoveredErrors_1154_);
lean_inc(v_errorMsg_1153_);
lean_inc(v_cache_1152_);
lean_inc(v_lhsPrec_1151_);
lean_inc(v_stxStack_1150_);
lean_dec(v_s_1146_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_inputString_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
v_inputString_1158_ = lean_ctor_get(v_toInputContext_1149_, 0);
v___x_1159_ = lean_string_utf8_next(v_inputString_1158_, v_pos_1148_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 2, v___x_1159_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_stxStack_1150_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_lhsPrec_1151_);
lean_ctor_set(v_reuseFailAlloc_1162_, 2, v___x_1159_);
lean_ctor_set(v_reuseFailAlloc_1162_, 3, v_cache_1152_);
lean_ctor_set(v_reuseFailAlloc_1162_, 4, v_errorMsg_1153_);
lean_ctor_set(v_reuseFailAlloc_1162_, 5, v_recoveredErrors_1154_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1165_, lean_object* v_c_1166_, lean_object* v_pos_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Lean_Parser_ParserState_next(v_s_1165_, v_c_1166_, v_pos_1167_);
lean_dec(v_pos_1167_);
lean_dec_ref(v_c_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1169_, lean_object* v_c_1170_, lean_object* v_pos_1171_){
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
v___x_1182_ = lean_string_utf8_next_fast(v_inputString_1181_, v_pos_1171_);
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
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1188_, lean_object* v_c_1189_, lean_object* v_pos_1190_){
_start:
{
lean_object* v_res_1191_; 
v_res_1191_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1188_, v_c_1189_, v_pos_1190_);
lean_dec(v_pos_1190_);
lean_dec_ref(v_c_1189_);
return v_res_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1192_, lean_object* v_c_1193_, lean_object* v_pos_1194_, lean_object* v_h_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1192_, v_c_1193_, v_pos_1194_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1197_, lean_object* v_c_1198_, lean_object* v_pos_1199_, lean_object* v_h_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_Parser_ParserState_next_x27(v_s_1197_, v_c_1198_, v_pos_1199_, v_h_1200_);
lean_dec(v_pos_1199_);
lean_dec_ref(v_c_1198_);
return v_res_1201_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1202_, lean_object* v_x_1203_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
if (lean_obj_tag(v_x_1203_) == 0)
{
uint8_t v___x_1204_; 
v___x_1204_ = 1;
return v___x_1204_;
}
else
{
uint8_t v___x_1205_; 
v___x_1205_ = 0;
return v___x_1205_;
}
}
else
{
if (lean_obj_tag(v_x_1203_) == 0)
{
uint8_t v___x_1206_; 
v___x_1206_ = 0;
return v___x_1206_;
}
else
{
lean_object* v_val_1207_; lean_object* v_val_1208_; uint8_t v___x_1209_; 
v_val_1207_ = lean_ctor_get(v_x_1202_, 0);
v_val_1208_ = lean_ctor_get(v_x_1203_, 0);
v___x_1209_ = l_Lean_Parser_instBEqError_beq(v_val_1207_, v_val_1208_);
return v___x_1209_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1210_, lean_object* v_x_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1210_, v_x_1211_);
lean_dec(v_x_1211_);
lean_dec(v_x_1210_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1214_, lean_object* v_k_1215_, lean_object* v_iniStackSz_1216_){
_start:
{
lean_object* v_stxStack_1217_; lean_object* v_lhsPrec_1218_; lean_object* v_pos_1219_; lean_object* v_cache_1220_; lean_object* v_errorMsg_1221_; lean_object* v_recoveredErrors_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1243_; 
v_stxStack_1217_ = lean_ctor_get(v_s_1214_, 0);
v_lhsPrec_1218_ = lean_ctor_get(v_s_1214_, 1);
v_pos_1219_ = lean_ctor_get(v_s_1214_, 2);
v_cache_1220_ = lean_ctor_get(v_s_1214_, 3);
v_errorMsg_1221_ = lean_ctor_get(v_s_1214_, 4);
v_recoveredErrors_1222_ = lean_ctor_get(v_s_1214_, 5);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_s_1214_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1224_ = v_s_1214_;
v_isShared_1225_ = v_isSharedCheck_1243_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_recoveredErrors_1222_);
lean_inc(v_errorMsg_1221_);
lean_inc(v_cache_1220_);
lean_inc(v_pos_1219_);
lean_inc(v_lhsPrec_1218_);
lean_inc(v_stxStack_1217_);
lean_dec(v_s_1214_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1243_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = lean_box(0);
v___x_1237_ = l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1221_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1217_);
v___x_1239_ = lean_nat_dec_eq(v___x_1238_, v_iniStackSz_1216_);
lean_dec(v___x_1238_);
if (v___x_1239_ == 0)
{
goto v___jp_1226_;
}
else
{
lean_object* v___x_1240_; lean_object* v_stack_1241_; lean_object* v___x_1242_; 
lean_del_object(v___x_1224_);
lean_dec(v_k_1215_);
v___x_1240_ = lean_box(0);
v_stack_1241_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1217_, v___x_1240_);
v___x_1242_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1242_, 0, v_stack_1241_);
lean_ctor_set(v___x_1242_, 1, v_lhsPrec_1218_);
lean_ctor_set(v___x_1242_, 2, v_pos_1219_);
lean_ctor_set(v___x_1242_, 3, v_cache_1220_);
lean_ctor_set(v___x_1242_, 4, v_errorMsg_1221_);
lean_ctor_set(v___x_1242_, 5, v_recoveredErrors_1222_);
return v___x_1242_;
}
}
else
{
goto v___jp_1226_;
}
v___jp_1226_:
{
lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v_newNode_1230_; lean_object* v_stack_1231_; lean_object* v_stack_1232_; lean_object* v___x_1234_; 
v___x_1227_ = lean_box(2);
v___x_1228_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1217_);
v___x_1229_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1217_, v_iniStackSz_1216_, v___x_1228_);
lean_dec(v___x_1228_);
v_newNode_1230_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1230_, 0, v___x_1227_);
lean_ctor_set(v_newNode_1230_, 1, v_k_1215_);
lean_ctor_set(v_newNode_1230_, 2, v___x_1229_);
v_stack_1231_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1217_, v_iniStackSz_1216_);
v_stack_1232_ = l_Lean_Parser_SyntaxStack_push(v_stack_1231_, v_newNode_1230_);
if (v_isShared_1225_ == 0)
{
lean_ctor_set(v___x_1224_, 0, v_stack_1232_);
v___x_1234_ = v___x_1224_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_stack_1232_);
lean_ctor_set(v_reuseFailAlloc_1235_, 1, v_lhsPrec_1218_);
lean_ctor_set(v_reuseFailAlloc_1235_, 2, v_pos_1219_);
lean_ctor_set(v_reuseFailAlloc_1235_, 3, v_cache_1220_);
lean_ctor_set(v_reuseFailAlloc_1235_, 4, v_errorMsg_1221_);
lean_ctor_set(v_reuseFailAlloc_1235_, 5, v_recoveredErrors_1222_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1244_, lean_object* v_k_1245_, lean_object* v_iniStackSz_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Lean_Parser_ParserState_mkNode(v_s_1244_, v_k_1245_, v_iniStackSz_1246_);
lean_dec(v_iniStackSz_1246_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1248_, lean_object* v_k_1249_, lean_object* v_iniStackSz_1250_){
_start:
{
lean_object* v_stxStack_1251_; lean_object* v_lhsPrec_1252_; lean_object* v_pos_1253_; lean_object* v_cache_1254_; lean_object* v_errorMsg_1255_; lean_object* v_recoveredErrors_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1271_; 
v_stxStack_1251_ = lean_ctor_get(v_s_1248_, 0);
v_lhsPrec_1252_ = lean_ctor_get(v_s_1248_, 1);
v_pos_1253_ = lean_ctor_get(v_s_1248_, 2);
v_cache_1254_ = lean_ctor_get(v_s_1248_, 3);
v_errorMsg_1255_ = lean_ctor_get(v_s_1248_, 4);
v_recoveredErrors_1256_ = lean_ctor_get(v_s_1248_, 5);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_s_1248_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1258_ = v_s_1248_;
v_isShared_1259_ = v_isSharedCheck_1271_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_recoveredErrors_1256_);
lean_inc(v_errorMsg_1255_);
lean_inc(v_cache_1254_);
lean_inc(v_pos_1253_);
lean_inc(v_lhsPrec_1252_);
lean_inc(v_stxStack_1251_);
lean_dec(v_s_1248_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1271_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v_newNode_1265_; lean_object* v_stack_1266_; lean_object* v_stack_1267_; lean_object* v___x_1269_; 
v___x_1260_ = lean_box(2);
v___x_1261_ = lean_unsigned_to_nat(1u);
v___x_1262_ = lean_nat_sub(v_iniStackSz_1250_, v___x_1261_);
v___x_1263_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1251_);
v___x_1264_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1251_, v___x_1262_, v___x_1263_);
lean_dec(v___x_1263_);
v_newNode_1265_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1265_, 0, v___x_1260_);
lean_ctor_set(v_newNode_1265_, 1, v_k_1249_);
lean_ctor_set(v_newNode_1265_, 2, v___x_1264_);
v_stack_1266_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1251_, v___x_1262_);
lean_dec(v___x_1262_);
v_stack_1267_ = l_Lean_Parser_SyntaxStack_push(v_stack_1266_, v_newNode_1265_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 0, v_stack_1267_);
v___x_1269_ = v___x_1258_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_stack_1267_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v_lhsPrec_1252_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_pos_1253_);
lean_ctor_set(v_reuseFailAlloc_1270_, 3, v_cache_1254_);
lean_ctor_set(v_reuseFailAlloc_1270_, 4, v_errorMsg_1255_);
lean_ctor_set(v_reuseFailAlloc_1270_, 5, v_recoveredErrors_1256_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1272_, lean_object* v_k_1273_, lean_object* v_iniStackSz_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1272_, v_k_1273_, v_iniStackSz_1274_);
lean_dec(v_iniStackSz_1274_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1278_){
_start:
{
lean_object* v_errorMsg_1279_; 
v_errorMsg_1279_ = lean_ctor_get(v_s_1278_, 4);
if (lean_obj_tag(v_errorMsg_1279_) == 0)
{
lean_object* v_recoveredErrors_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v_recoveredErrors_1280_ = lean_ctor_get(v_s_1278_, 5);
lean_inc_ref(v_recoveredErrors_1280_);
lean_dec_ref(v_s_1278_);
v___x_1281_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1282_ = l_Array_append___redArg(v_recoveredErrors_1280_, v___x_1281_);
return v___x_1282_;
}
else
{
lean_object* v_stxStack_1283_; lean_object* v_pos_1284_; lean_object* v_recoveredErrors_1285_; lean_object* v_val_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_inc_ref(v_errorMsg_1279_);
v_stxStack_1283_ = lean_ctor_get(v_s_1278_, 0);
lean_inc_ref(v_stxStack_1283_);
v_pos_1284_ = lean_ctor_get(v_s_1278_, 2);
lean_inc(v_pos_1284_);
v_recoveredErrors_1285_ = lean_ctor_get(v_s_1278_, 5);
lean_inc_ref(v_recoveredErrors_1285_);
lean_dec_ref(v_s_1278_);
v_val_1286_ = lean_ctor_get(v_errorMsg_1279_, 0);
lean_inc(v_val_1286_);
lean_dec_ref_known(v_errorMsg_1279_, 1);
v___x_1287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1287_, 0, v_stxStack_1283_);
lean_ctor_set(v___x_1287_, 1, v_val_1286_);
v___x_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1288_, 0, v_pos_1284_);
lean_ctor_set(v___x_1288_, 1, v___x_1287_);
v___x_1289_ = lean_unsigned_to_nat(1u);
v___x_1290_ = lean_mk_empty_array_with_capacity(v___x_1289_);
v___x_1291_ = lean_array_push(v___x_1290_, v___x_1288_);
v___x_1292_ = l_Array_append___redArg(v_recoveredErrors_1285_, v___x_1291_);
lean_dec_ref(v___x_1291_);
return v___x_1292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1293_, lean_object* v_e_1294_){
_start:
{
lean_object* v_stxStack_1295_; lean_object* v_lhsPrec_1296_; lean_object* v_pos_1297_; lean_object* v_cache_1298_; lean_object* v_recoveredErrors_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1307_; 
v_stxStack_1295_ = lean_ctor_get(v_s_1293_, 0);
v_lhsPrec_1296_ = lean_ctor_get(v_s_1293_, 1);
v_pos_1297_ = lean_ctor_get(v_s_1293_, 2);
v_cache_1298_ = lean_ctor_get(v_s_1293_, 3);
v_recoveredErrors_1299_ = lean_ctor_get(v_s_1293_, 5);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_s_1293_);
if (v_isSharedCheck_1307_ == 0)
{
lean_object* v_unused_1308_; 
v_unused_1308_ = lean_ctor_get(v_s_1293_, 4);
lean_dec(v_unused_1308_);
v___x_1301_ = v_s_1293_;
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_recoveredErrors_1299_);
lean_inc(v_cache_1298_);
lean_inc(v_pos_1297_);
lean_inc(v_lhsPrec_1296_);
lean_inc(v_stxStack_1295_);
lean_dec(v_s_1293_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1307_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; lean_object* v___x_1305_; 
v___x_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1303_, 0, v_e_1294_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 4, v___x_1303_);
v___x_1305_ = v___x_1301_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_stxStack_1295_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_lhsPrec_1296_);
lean_ctor_set(v_reuseFailAlloc_1306_, 2, v_pos_1297_);
lean_ctor_set(v_reuseFailAlloc_1306_, 3, v_cache_1298_);
lean_ctor_set(v_reuseFailAlloc_1306_, 4, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1306_, 5, v_recoveredErrors_1299_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1309_, lean_object* v_msg_1310_){
_start:
{
lean_object* v_stxStack_1311_; lean_object* v_lhsPrec_1312_; lean_object* v_pos_1313_; lean_object* v_cache_1314_; lean_object* v_recoveredErrors_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1329_; 
v_stxStack_1311_ = lean_ctor_get(v_s_1309_, 0);
v_lhsPrec_1312_ = lean_ctor_get(v_s_1309_, 1);
v_pos_1313_ = lean_ctor_get(v_s_1309_, 2);
v_cache_1314_ = lean_ctor_get(v_s_1309_, 3);
v_recoveredErrors_1315_ = lean_ctor_get(v_s_1309_, 5);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_s_1309_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v_s_1309_, 4);
lean_dec(v_unused_1330_);
v___x_1317_ = v_s_1309_;
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_recoveredErrors_1315_);
lean_inc(v_cache_1314_);
lean_inc(v_pos_1313_);
lean_inc(v_lhsPrec_1312_);
lean_inc(v_stxStack_1311_);
lean_dec(v_s_1309_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1319_ = lean_box(0);
v___x_1320_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1321_ = lean_box(0);
v___x_1322_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1322_, 0, v_msg_1310_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1319_);
lean_ctor_set(v___x_1323_, 1, v___x_1320_);
lean_ctor_set(v___x_1323_, 2, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 4, v___x_1324_);
v___x_1326_ = v___x_1317_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_stxStack_1311_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v_lhsPrec_1312_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_pos_1313_);
lean_ctor_set(v_reuseFailAlloc_1328_, 3, v_cache_1314_);
lean_ctor_set(v_reuseFailAlloc_1328_, 4, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1328_, 5, v_recoveredErrors_1315_);
v___x_1326_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1326_, v___x_1319_);
return v___x_1327_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1331_, lean_object* v_msg_1332_, lean_object* v_expected_1333_, uint8_t v_pushMissing_1334_){
_start:
{
lean_object* v_stxStack_1335_; lean_object* v_lhsPrec_1336_; lean_object* v_pos_1337_; lean_object* v_cache_1338_; lean_object* v_recoveredErrors_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1350_; 
v_stxStack_1335_ = lean_ctor_get(v_s_1331_, 0);
v_lhsPrec_1336_ = lean_ctor_get(v_s_1331_, 1);
v_pos_1337_ = lean_ctor_get(v_s_1331_, 2);
v_cache_1338_ = lean_ctor_get(v_s_1331_, 3);
v_recoveredErrors_1339_ = lean_ctor_get(v_s_1331_, 5);
v_isSharedCheck_1350_ = !lean_is_exclusive(v_s_1331_);
if (v_isSharedCheck_1350_ == 0)
{
lean_object* v_unused_1351_; 
v_unused_1351_ = lean_ctor_get(v_s_1331_, 4);
lean_dec(v_unused_1351_);
v___x_1341_ = v_s_1331_;
v_isShared_1342_ = v_isSharedCheck_1350_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_recoveredErrors_1339_);
lean_inc(v_cache_1338_);
lean_inc(v_pos_1337_);
lean_inc(v_lhsPrec_1336_);
lean_inc(v_stxStack_1335_);
lean_dec(v_s_1331_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1350_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v_s_1347_; 
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
lean_ctor_set(v___x_1344_, 1, v_msg_1332_);
lean_ctor_set(v___x_1344_, 2, v_expected_1333_);
v___x_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 4, v___x_1345_);
v_s_1347_ = v___x_1341_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_stxStack_1335_);
lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_lhsPrec_1336_);
lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_pos_1337_);
lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_cache_1338_);
lean_ctor_set(v_reuseFailAlloc_1349_, 4, v___x_1345_);
lean_ctor_set(v_reuseFailAlloc_1349_, 5, v_recoveredErrors_1339_);
v_s_1347_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
if (v_pushMissing_1334_ == 0)
{
return v_s_1347_;
}
else
{
lean_object* v___x_1348_; 
v___x_1348_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1347_, v___x_1343_);
return v___x_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1352_, lean_object* v_msg_1353_, lean_object* v_expected_1354_, lean_object* v_pushMissing_1355_){
_start:
{
uint8_t v_pushMissing_boxed_1356_; lean_object* v_res_1357_; 
v_pushMissing_boxed_1356_ = lean_unbox(v_pushMissing_1355_);
v_res_1357_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1352_, v_msg_1353_, v_expected_1354_, v_pushMissing_boxed_1356_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1359_, lean_object* v_expected_1360_){
_start:
{
lean_object* v___x_1361_; uint8_t v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1362_ = 1;
v___x_1363_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1359_, v___x_1361_, v_expected_1360_, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1364_, lean_object* v_ex_1365_, lean_object* v_pos_1366_, lean_object* v_initStackSz_x3f_1367_){
_start:
{
lean_object* v_s_1369_; lean_object* v_s_1388_; 
v_s_1388_ = l_Lean_Parser_ParserState_setPos(v_s_1364_, v_pos_1366_);
if (lean_obj_tag(v_initStackSz_x3f_1367_) == 1)
{
lean_object* v_val_1389_; lean_object* v_s_1390_; 
v_val_1389_ = lean_ctor_get(v_initStackSz_x3f_1367_, 0);
v_s_1390_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1388_, v_val_1389_);
v_s_1369_ = v_s_1390_;
goto v___jp_1368_;
}
else
{
v_s_1369_ = v_s_1388_;
goto v___jp_1368_;
}
v___jp_1368_:
{
lean_object* v_stxStack_1370_; lean_object* v_lhsPrec_1371_; lean_object* v_pos_1372_; lean_object* v_cache_1373_; lean_object* v_recoveredErrors_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1386_; 
v_stxStack_1370_ = lean_ctor_get(v_s_1369_, 0);
v_lhsPrec_1371_ = lean_ctor_get(v_s_1369_, 1);
v_pos_1372_ = lean_ctor_get(v_s_1369_, 2);
v_cache_1373_ = lean_ctor_get(v_s_1369_, 3);
v_recoveredErrors_1374_ = lean_ctor_get(v_s_1369_, 5);
v_isSharedCheck_1386_ = !lean_is_exclusive(v_s_1369_);
if (v_isSharedCheck_1386_ == 0)
{
lean_object* v_unused_1387_; 
v_unused_1387_ = lean_ctor_get(v_s_1369_, 4);
lean_dec(v_unused_1387_);
v___x_1376_ = v_s_1369_;
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_recoveredErrors_1374_);
lean_inc(v_cache_1373_);
lean_inc(v_pos_1372_);
lean_inc(v_lhsPrec_1371_);
lean_inc(v_stxStack_1370_);
lean_dec(v_s_1369_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1386_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v_s_1383_; 
v___x_1378_ = lean_box(0);
v___x_1379_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1378_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
lean_ctor_set(v___x_1380_, 2, v_ex_1365_);
v___x_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1380_);
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 4, v___x_1381_);
v_s_1383_ = v___x_1376_;
goto v_reusejp_1382_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_stxStack_1370_);
lean_ctor_set(v_reuseFailAlloc_1385_, 1, v_lhsPrec_1371_);
lean_ctor_set(v_reuseFailAlloc_1385_, 2, v_pos_1372_);
lean_ctor_set(v_reuseFailAlloc_1385_, 3, v_cache_1373_);
lean_ctor_set(v_reuseFailAlloc_1385_, 4, v___x_1381_);
lean_ctor_set(v_reuseFailAlloc_1385_, 5, v_recoveredErrors_1374_);
v_s_1383_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1382_;
}
v_reusejp_1382_:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1383_, v___x_1378_);
return v___x_1384_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1391_, lean_object* v_ex_1392_, lean_object* v_pos_1393_, lean_object* v_initStackSz_x3f_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1391_, v_ex_1392_, v_pos_1393_, v_initStackSz_x3f_1394_);
lean_dec(v_initStackSz_x3f_1394_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1396_, lean_object* v_msg_1397_, lean_object* v_pos_1398_, lean_object* v_initStackSz_x3f_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; 
v___x_1400_ = lean_box(0);
v___x_1401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1401_, 0, v_msg_1397_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1396_, v___x_1401_, v_pos_1398_, v_initStackSz_x3f_1399_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1403_, lean_object* v_msg_1404_, lean_object* v_pos_1405_, lean_object* v_initStackSz_x3f_1406_){
_start:
{
lean_object* v_res_1407_; 
v_res_1407_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1403_, v_msg_1404_, v_pos_1405_, v_initStackSz_x3f_1406_);
lean_dec(v_initStackSz_x3f_1406_);
return v_res_1407_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1408_){
_start:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; 
v___x_1409_ = lean_unsigned_to_nat(0u);
v___x_1410_ = lean_panic_fn_borrowed(v___x_1409_, v_msg_1408_);
return v___x_1410_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1414_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1415_ = lean_unsigned_to_nat(14u);
v___x_1416_ = lean_unsigned_to_nat(22u);
v___x_1417_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1418_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1419_ = l_mkPanicMessageWithDecl(v___x_1418_, v___x_1417_, v___x_1416_, v___x_1415_, v___x_1414_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1420_, lean_object* v_ex_1421_, lean_object* v_iniPos_1422_){
_start:
{
lean_object* v_stxStack_1423_; lean_object* v_tk_1424_; lean_object* v___y_1426_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_stxStack_1423_ = lean_ctor_get(v_s_1420_, 0);
v_tk_1424_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1423_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_nat_dec_le(v___x_1447_, v_iniPos_1422_);
if (v___x_1448_ == 0)
{
lean_object* v___x_1449_; 
lean_dec(v_iniPos_1422_);
v___x_1449_ = l_Lean_Syntax_getPos_x3f(v_tk_1424_, v___x_1448_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1451_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1450_);
v___y_1426_ = v___x_1451_;
goto v___jp_1425_;
}
else
{
lean_object* v_val_1452_; 
v_val_1452_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_val_1452_);
lean_dec_ref_known(v___x_1449_, 1);
v___y_1426_ = v_val_1452_;
goto v___jp_1425_;
}
}
else
{
v___y_1426_ = v_iniPos_1422_;
goto v___jp_1425_;
}
v___jp_1425_:
{
lean_object* v_s_1427_; lean_object* v_stxStack_1428_; lean_object* v_lhsPrec_1429_; lean_object* v_pos_1430_; lean_object* v_cache_1431_; lean_object* v_recoveredErrors_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1445_; 
v_s_1427_ = l_Lean_Parser_ParserState_setPos(v_s_1420_, v___y_1426_);
v_stxStack_1428_ = lean_ctor_get(v_s_1427_, 0);
v_lhsPrec_1429_ = lean_ctor_get(v_s_1427_, 1);
v_pos_1430_ = lean_ctor_get(v_s_1427_, 2);
v_cache_1431_ = lean_ctor_get(v_s_1427_, 3);
v_recoveredErrors_1432_ = lean_ctor_get(v_s_1427_, 5);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_s_1427_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; 
v_unused_1446_ = lean_ctor_get(v_s_1427_, 4);
lean_dec(v_unused_1446_);
v___x_1434_ = v_s_1427_;
v_isShared_1435_ = v_isSharedCheck_1445_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_recoveredErrors_1432_);
lean_inc(v_cache_1431_);
lean_inc(v_pos_1430_);
lean_inc(v_lhsPrec_1429_);
lean_inc(v_stxStack_1428_);
lean_dec(v_s_1427_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1445_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v_s_1440_; 
v___x_1436_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1437_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1437_, 0, v_tk_1424_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
lean_ctor_set(v___x_1437_, 2, v_ex_1421_);
v___x_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 4, v___x_1438_);
v_s_1440_ = v___x_1434_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_stxStack_1428_);
lean_ctor_set(v_reuseFailAlloc_1444_, 1, v_lhsPrec_1429_);
lean_ctor_set(v_reuseFailAlloc_1444_, 2, v_pos_1430_);
lean_ctor_set(v_reuseFailAlloc_1444_, 3, v_cache_1431_);
lean_ctor_set(v_reuseFailAlloc_1444_, 4, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1444_, 5, v_recoveredErrors_1432_);
v_s_1440_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = l_Lean_Parser_ParserState_popSyntax(v_s_1440_);
v___x_1442_ = lean_box(0);
v___x_1443_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1441_, v___x_1442_);
return v___x_1443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1453_, lean_object* v_msg_1454_, lean_object* v_iniPos_1455_){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_msg_1454_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1453_, v___x_1457_, v_iniPos_1455_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1459_, lean_object* v_msg_1460_, lean_object* v_pos_1461_){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; lean_object* v___x_1465_; 
v___x_1462_ = l_Lean_Parser_ParserState_setPos(v_s_1459_, v_pos_1461_);
v___x_1463_ = lean_box(0);
v___x_1464_ = 1;
v___x_1465_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1462_, v_msg_1460_, v___x_1463_, v___x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1467_, lean_object* v_as_1468_, size_t v_sz_1469_, size_t v_i_1470_, lean_object* v_b_1471_){
_start:
{
uint8_t v___x_1472_; 
v___x_1472_ = lean_usize_dec_lt(v_i_1470_, v_sz_1469_);
if (v___x_1472_ == 0)
{
lean_dec_ref(v_ctx_1467_);
return v_b_1471_;
}
else
{
lean_object* v_a_1473_; lean_object* v_snd_1474_; lean_object* v_fst_1475_; lean_object* v_snd_1476_; lean_object* v_errStr_1478_; lean_object* v_errStr_1489_; uint8_t v___x_1490_; 
v_a_1473_ = lean_array_uget_borrowed(v_as_1468_, v_i_1470_);
v_snd_1474_ = lean_ctor_get(v_a_1473_, 1);
v_fst_1475_ = lean_ctor_get(v_a_1473_, 0);
v_snd_1476_ = lean_ctor_get(v_snd_1474_, 1);
v_errStr_1489_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1490_ = lean_string_dec_eq(v_b_1471_, v_errStr_1489_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1492_ = lean_string_append(v_b_1471_, v___x_1491_);
v_errStr_1478_ = v___x_1492_;
goto v___jp_1477_;
}
else
{
v_errStr_1478_ = v_b_1471_;
goto v___jp_1477_;
}
v___jp_1477_:
{
lean_object* v_fileName_1479_; lean_object* v_fileMap_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; size_t v___x_1486_; size_t v___x_1487_; 
v_fileName_1479_ = lean_ctor_get(v_ctx_1467_, 1);
v_fileMap_1480_ = lean_ctor_get(v_ctx_1467_, 2);
lean_inc_ref(v_fileMap_1480_);
v___x_1481_ = l_Lean_FileMap_toPosition(v_fileMap_1480_, v_fst_1475_);
lean_inc(v_snd_1476_);
v___x_1482_ = l_Lean_Parser_Error_toString(v_snd_1476_);
v___x_1483_ = lean_box(0);
lean_inc_ref(v_fileName_1479_);
v___x_1484_ = l_Lean_mkErrorStringWithPos(v_fileName_1479_, v___x_1481_, v___x_1482_, v___x_1483_, v___x_1483_, v___x_1483_);
lean_dec_ref(v___x_1482_);
v___x_1485_ = lean_string_append(v_errStr_1478_, v___x_1484_);
lean_dec_ref(v___x_1484_);
v___x_1486_ = ((size_t)1ULL);
v___x_1487_ = lean_usize_add(v_i_1470_, v___x_1486_);
v_i_1470_ = v___x_1487_;
v_b_1471_ = v___x_1485_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1493_, lean_object* v_as_1494_, lean_object* v_sz_1495_, lean_object* v_i_1496_, lean_object* v_b_1497_){
_start:
{
size_t v_sz_boxed_1498_; size_t v_i_boxed_1499_; lean_object* v_res_1500_; 
v_sz_boxed_1498_ = lean_unbox_usize(v_sz_1495_);
lean_dec(v_sz_1495_);
v_i_boxed_1499_ = lean_unbox_usize(v_i_1496_);
lean_dec(v_i_1496_);
v_res_1500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1493_, v_as_1494_, v_sz_boxed_1498_, v_i_boxed_1499_, v_b_1497_);
lean_dec_ref(v_as_1494_);
return v_res_1500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1501_, lean_object* v_s_1502_){
_start:
{
lean_object* v_errStr_1503_; lean_object* v___x_1504_; size_t v_sz_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
v_errStr_1503_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1504_ = l_Lean_Parser_ParserState_allErrors(v_s_1502_);
v_sz_1505_ = lean_array_size(v___x_1504_);
v___x_1506_ = ((size_t)0ULL);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1501_, v___x_1504_, v_sz_1505_, v___x_1506_, v_errStr_1503_);
lean_dec_ref(v___x_1504_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1508_, lean_object* v_s_1509_){
_start:
{
lean_inc_ref(v_s_1509_);
return v_s_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1510_, lean_object* v_s_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1510_, v_s_1511_);
lean_dec_ref(v_s_1511_);
lean_dec_ref(v_x_1510_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___impl(lean_object* v_x_1515_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_obj_tag_nat(v_x_1515_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___impl___boxed(lean_object* v_x_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Parser_FirstTokens_ctorIdx___impl(v_x_1517_);
lean_dec(v_x_1517_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1519_, lean_object* v_k_1520_){
_start:
{
switch(lean_obj_tag(v_t_1519_))
{
case 2:
{
lean_object* v_a_1521_; lean_object* v___x_1522_; 
v_a_1521_ = lean_ctor_get(v_t_1519_, 0);
lean_inc(v_a_1521_);
lean_dec_ref_known(v_t_1519_, 1);
v___x_1522_ = lean_apply_1(v_k_1520_, v_a_1521_);
return v___x_1522_;
}
case 3:
{
lean_object* v_a_1523_; lean_object* v___x_1524_; 
v_a_1523_ = lean_ctor_get(v_t_1519_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v_t_1519_, 1);
v___x_1524_ = lean_apply_1(v_k_1520_, v_a_1523_);
return v___x_1524_;
}
default: 
{
lean_dec(v_t_1519_);
return v_k_1520_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1525_, lean_object* v_ctorIdx_1526_, lean_object* v_t_1527_, lean_object* v_h_1528_, lean_object* v_k_1529_){
_start:
{
lean_object* v___x_1530_; 
v___x_1530_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1527_, v_k_1529_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1531_, lean_object* v_ctorIdx_1532_, lean_object* v_t_1533_, lean_object* v_h_1534_, lean_object* v_k_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1531_, v_ctorIdx_1532_, v_t_1533_, v_h_1534_, v_k_1535_);
lean_dec(v_ctorIdx_1532_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1537_, lean_object* v_epsilon_1538_){
_start:
{
lean_object* v___x_1539_; 
v___x_1539_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1537_, v_epsilon_1538_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1540_, lean_object* v_t_1541_, lean_object* v_h_1542_, lean_object* v_epsilon_1543_){
_start:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1541_, v_epsilon_1543_);
return v___x_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1545_, lean_object* v_unknown_1546_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1545_, v_unknown_1546_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1548_, lean_object* v_t_1549_, lean_object* v_h_1550_, lean_object* v_unknown_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1549_, v_unknown_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1553_, lean_object* v_tokens_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1553_, v_tokens_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1556_, lean_object* v_t_1557_, lean_object* v_h_1558_, lean_object* v_tokens_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1557_, v_tokens_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1561_, lean_object* v_optTokens_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1561_, v_optTokens_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1564_, lean_object* v_t_1565_, lean_object* v_h_1566_, lean_object* v_optTokens_1567_){
_start:
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1565_, v_optTokens_1567_);
return v___x_1568_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = lean_box(0);
return v___x_1569_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = lean_box(0);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1571_, lean_object* v_x_1572_){
_start:
{
switch(lean_obj_tag(v_x_1571_))
{
case 0:
{
return v_x_1572_;
}
case 3:
{
switch(lean_obj_tag(v_x_1572_))
{
case 3:
{
lean_object* v_a_1573_; lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1582_; 
v_a_1573_ = lean_ctor_get(v_x_1571_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v_x_1571_, 1);
v_a_1574_ = lean_ctor_get(v_x_1572_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1576_ = v_x_1572_;
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v_x_1572_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1578_ = l_List_appendTR___redArg(v_a_1573_, v_a_1574_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 0, v___x_1578_);
v___x_1580_ = v___x_1576_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
case 2:
{
lean_object* v_a_1583_; lean_object* v_a_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1592_; 
v_a_1583_ = lean_ctor_get(v_x_1571_, 0);
lean_inc(v_a_1583_);
lean_dec_ref_known(v_x_1571_, 1);
v_a_1584_ = lean_ctor_get(v_x_1572_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1586_ = v_x_1572_;
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_a_1584_);
lean_dec(v_x_1572_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1592_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1588_ = l_List_appendTR___redArg(v_a_1583_, v_a_1584_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1588_);
v___x_1590_ = v___x_1586_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
case 1:
{
lean_dec_ref_known(v_x_1571_, 1);
return v_x_1572_;
}
default: 
{
lean_dec(v_x_1572_);
return v_x_1571_;
}
}
}
default: 
{
lean_dec(v_x_1572_);
return v_x_1571_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1593_){
_start:
{
if (lean_obj_tag(v_x_1593_) == 2)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1601_; 
v_a_1594_ = lean_ctor_get(v_x_1593_, 0);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_x_1593_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1596_ = v_x_1593_;
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v_x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1601_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v___x_1599_; 
if (v_isShared_1597_ == 0)
{
lean_ctor_set_tag(v___x_1596_, 3);
v___x_1599_ = v___x_1596_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_a_1594_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
else
{
return v_x_1593_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
lean_object* v_s_u2081_1605_; lean_object* v_s_u2082_1606_; 
switch(lean_obj_tag(v_x_1602_))
{
case 0:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1603_);
return v___x_1609_;
}
case 2:
{
switch(lean_obj_tag(v_x_1603_))
{
case 0:
{
lean_object* v___x_1610_; 
v___x_1610_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1602_);
return v___x_1610_;
}
case 2:
{
lean_object* v_a_1611_; lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1620_; 
v_a_1611_ = lean_ctor_get(v_x_1602_, 0);
lean_inc(v_a_1611_);
lean_dec_ref_known(v_x_1602_, 1);
v_a_1612_ = lean_ctor_get(v_x_1603_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_x_1603_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1614_ = v_x_1603_;
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v_x_1603_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1620_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1616_; lean_object* v___x_1618_; 
v___x_1616_ = l_List_appendTR___redArg(v_a_1611_, v_a_1612_);
if (v_isShared_1615_ == 0)
{
lean_ctor_set(v___x_1614_, 0, v___x_1616_);
v___x_1618_ = v___x_1614_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v___x_1616_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
case 3:
{
lean_object* v_a_1621_; lean_object* v_a_1622_; 
v_a_1621_ = lean_ctor_get(v_x_1602_, 0);
lean_inc(v_a_1621_);
lean_dec_ref_known(v_x_1602_, 1);
v_a_1622_ = lean_ctor_get(v_x_1603_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v_x_1603_, 1);
v_s_u2081_1605_ = v_a_1621_;
v_s_u2082_1606_ = v_a_1622_;
goto v___jp_1604_;
}
default: 
{
lean_object* v___x_1623_; 
lean_dec_ref_known(v_x_1602_, 1);
lean_dec(v_x_1603_);
v___x_1623_ = lean_box(1);
return v___x_1623_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1603_))
{
case 0:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1602_);
return v___x_1624_;
}
case 3:
{
lean_object* v_a_1625_; lean_object* v_a_1626_; 
v_a_1625_ = lean_ctor_get(v_x_1602_, 0);
lean_inc(v_a_1625_);
lean_dec_ref_known(v_x_1602_, 1);
v_a_1626_ = lean_ctor_get(v_x_1603_, 0);
lean_inc(v_a_1626_);
lean_dec_ref_known(v_x_1603_, 1);
v_s_u2081_1605_ = v_a_1625_;
v_s_u2082_1606_ = v_a_1626_;
goto v___jp_1604_;
}
case 2:
{
lean_object* v_a_1627_; lean_object* v_a_1628_; 
v_a_1627_ = lean_ctor_get(v_x_1602_, 0);
lean_inc(v_a_1627_);
lean_dec_ref_known(v_x_1602_, 1);
v_a_1628_ = lean_ctor_get(v_x_1603_, 0);
lean_inc(v_a_1628_);
lean_dec_ref_known(v_x_1603_, 1);
v_s_u2081_1605_ = v_a_1627_;
v_s_u2082_1606_ = v_a_1628_;
goto v___jp_1604_;
}
default: 
{
lean_object* v___x_1629_; 
lean_dec_ref_known(v_x_1602_, 1);
lean_dec(v_x_1603_);
v___x_1629_ = lean_box(1);
return v___x_1629_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1603_) == 0)
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1602_);
return v___x_1630_;
}
else
{
lean_object* v___x_1631_; 
lean_dec(v_x_1603_);
lean_dec(v_x_1602_);
v___x_1631_ = lean_box(1);
return v___x_1631_;
}
}
}
v___jp_1604_:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = l_List_appendTR___redArg(v_s_u2081_1605_, v_s_u2082_1606_);
v___x_1608_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
if (lean_obj_tag(v_x_1633_) == 0)
{
return v_x_1632_;
}
else
{
lean_object* v_head_1634_; lean_object* v_tail_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_head_1634_ = lean_ctor_get(v_x_1633_, 0);
v_tail_1635_ = lean_ctor_get(v_x_1633_, 1);
v___x_1636_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1637_ = lean_string_append(v_x_1632_, v___x_1636_);
v___x_1638_ = lean_string_append(v___x_1637_, v_head_1634_);
v_x_1632_ = v___x_1638_;
v_x_1633_ = v_tail_1635_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1640_, v_x_1641_);
lean_dec(v_x_1641_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1646_){
_start:
{
if (lean_obj_tag(v_x_1646_) == 0)
{
lean_object* v___x_1647_; 
v___x_1647_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1647_;
}
else
{
lean_object* v_tail_1648_; 
v_tail_1648_ = lean_ctor_get(v_x_1646_, 1);
if (lean_obj_tag(v_tail_1648_) == 0)
{
lean_object* v_head_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v_head_1649_ = lean_ctor_get(v_x_1646_, 0);
v___x_1650_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1651_ = lean_string_append(v___x_1650_, v_head_1649_);
v___x_1652_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1653_ = lean_string_append(v___x_1651_, v___x_1652_);
return v___x_1653_;
}
else
{
lean_object* v_head_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; uint32_t v___x_1658_; lean_object* v___x_1659_; 
v_head_1654_ = lean_ctor_get(v_x_1646_, 0);
v___x_1655_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1656_ = lean_string_append(v___x_1655_, v_head_1654_);
v___x_1657_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1656_, v_tail_1648_);
v___x_1658_ = 93;
v___x_1659_ = lean_string_push(v___x_1657_, v___x_1658_);
return v___x_1659_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1660_);
lean_dec(v_x_1660_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1665_){
_start:
{
switch(lean_obj_tag(v_x_1665_))
{
case 0:
{
lean_object* v___x_1666_; 
v___x_1666_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1666_;
}
case 1:
{
lean_object* v___x_1667_; 
v___x_1667_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1667_;
}
case 2:
{
lean_object* v_a_1668_; lean_object* v___x_1669_; 
v_a_1668_ = lean_ctor_get(v_x_1665_, 0);
v___x_1669_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1668_);
return v___x_1669_;
}
default: 
{
lean_object* v_a_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; 
v_a_1670_ = lean_ctor_get(v_x_1665_, 0);
v___x_1671_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1672_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1670_);
v___x_1673_ = lean_string_append(v___x_1671_, v___x_1672_);
lean_dec_ref(v___x_1672_);
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1674_){
_start:
{
lean_object* v_res_1675_; 
v_res_1675_ = l_Lean_Parser_FirstTokens_toStr(v_x_1674_);
lean_dec(v_x_1674_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v___y_1678_){
_start:
{
lean_inc(v___y_1678_);
return v___y_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_1679_);
lean_dec(v___y_1679_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v___y_1681_){
_start:
{
lean_inc_ref(v___y_1681_);
return v___y_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_1682_);
lean_dec_ref(v___y_1682_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1697_, lean_object* v_p_1698_){
_start:
{
lean_object* v_info_1699_; lean_object* v_fn_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1708_; 
v_info_1699_ = lean_ctor_get(v_p_1698_, 0);
v_fn_1700_ = lean_ctor_get(v_p_1698_, 1);
v_isSharedCheck_1708_ = !lean_is_exclusive(v_p_1698_);
if (v_isSharedCheck_1708_ == 0)
{
v___x_1702_ = v_p_1698_;
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_fn_1700_);
lean_inc(v_info_1699_);
lean_dec(v_p_1698_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1708_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1706_; 
v___x_1704_ = lean_apply_1(v_f_1697_, v_fn_1700_);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 1, v___x_1704_);
v___x_1706_ = v___x_1702_;
goto v_reusejp_1705_;
}
else
{
lean_object* v_reuseFailAlloc_1707_; 
v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1707_, 0, v_info_1699_);
lean_ctor_set(v_reuseFailAlloc_1707_, 1, v___x_1704_);
v___x_1706_ = v_reuseFailAlloc_1707_;
goto v_reusejp_1705_;
}
v_reusejp_1705_:
{
return v___x_1706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1709_, lean_object* v_p_1710_, lean_object* v_c_1711_, lean_object* v_s_1712_){
_start:
{
lean_object* v_toInputContext_1713_; lean_object* v_toParserModuleContext_1714_; lean_object* v_toCacheableParserContext_1715_; lean_object* v_tokens_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1725_; 
v_toInputContext_1713_ = lean_ctor_get(v_c_1711_, 0);
v_toParserModuleContext_1714_ = lean_ctor_get(v_c_1711_, 1);
v_toCacheableParserContext_1715_ = lean_ctor_get(v_c_1711_, 2);
v_tokens_1716_ = lean_ctor_get(v_c_1711_, 3);
v_isSharedCheck_1725_ = !lean_is_exclusive(v_c_1711_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1718_ = v_c_1711_;
v_isShared_1719_ = v_isSharedCheck_1725_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_tokens_1716_);
lean_inc(v_toCacheableParserContext_1715_);
lean_inc(v_toParserModuleContext_1714_);
lean_inc(v_toInputContext_1713_);
lean_dec(v_c_1711_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1725_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
v___x_1720_ = lean_apply_1(v_f_1709_, v_toCacheableParserContext_1715_);
if (v_isShared_1719_ == 0)
{
lean_ctor_set(v___x_1718_, 2, v___x_1720_);
v___x_1722_ = v___x_1718_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_toInputContext_1713_);
lean_ctor_set(v_reuseFailAlloc_1724_, 1, v_toParserModuleContext_1714_);
lean_ctor_set(v_reuseFailAlloc_1724_, 2, v___x_1720_);
lean_ctor_set(v_reuseFailAlloc_1724_, 3, v_tokens_1716_);
v___x_1722_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_apply_2(v_p_1710_, v___x_1722_, v_s_1712_);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1726_, lean_object* v_p_1727_){
_start:
{
lean_object* v_info_1728_; lean_object* v_fn_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1737_; 
v_info_1728_ = lean_ctor_get(v_p_1727_, 0);
v_fn_1729_ = lean_ctor_get(v_p_1727_, 1);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_p_1727_);
if (v_isSharedCheck_1737_ == 0)
{
v___x_1731_ = v_p_1727_;
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_fn_1729_);
lean_inc(v_info_1728_);
lean_dec(v_p_1727_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1737_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1733_; lean_object* v___x_1735_; 
v___x_1733_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1733_, 0, v_f_1726_);
lean_closure_set(v___x_1733_, 1, v_fn_1729_);
if (v_isShared_1732_ == 0)
{
lean_ctor_set(v___x_1731_, 1, v___x_1733_);
v___x_1735_ = v___x_1731_;
goto v_reusejp_1734_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_info_1728_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1733_);
v___x_1735_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1734_;
}
v_reusejp_1734_:
{
return v___x_1735_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1738_, lean_object* v_p_1739_, lean_object* v_c_1740_, lean_object* v_s_1741_){
_start:
{
lean_object* v_stxStack_1742_; lean_object* v_lhsPrec_1743_; lean_object* v_pos_1744_; lean_object* v_cache_1745_; lean_object* v_errorMsg_1746_; lean_object* v_recoveredErrors_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1786_; 
v_stxStack_1742_ = lean_ctor_get(v_s_1741_, 0);
v_lhsPrec_1743_ = lean_ctor_get(v_s_1741_, 1);
v_pos_1744_ = lean_ctor_get(v_s_1741_, 2);
v_cache_1745_ = lean_ctor_get(v_s_1741_, 3);
v_errorMsg_1746_ = lean_ctor_get(v_s_1741_, 4);
v_recoveredErrors_1747_ = lean_ctor_get(v_s_1741_, 5);
v_isSharedCheck_1786_ = !lean_is_exclusive(v_s_1741_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1749_ = v_s_1741_;
v_isShared_1750_ = v_isSharedCheck_1786_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_recoveredErrors_1747_);
lean_inc(v_errorMsg_1746_);
lean_inc(v_cache_1745_);
lean_inc(v_pos_1744_);
lean_inc(v_lhsPrec_1743_);
lean_inc(v_stxStack_1742_);
lean_dec(v_s_1741_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1786_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v_raw_1751_; lean_object* v_drop_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1785_; 
v_raw_1751_ = lean_ctor_get(v_stxStack_1742_, 0);
v_drop_1752_ = lean_ctor_get(v_stxStack_1742_, 1);
v_isSharedCheck_1785_ = !lean_is_exclusive(v_stxStack_1742_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1754_ = v_stxStack_1742_;
v_isShared_1755_ = v_isSharedCheck_1785_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_drop_1752_);
lean_inc(v_raw_1751_);
lean_dec(v_stxStack_1742_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1785_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
lean_object* v___x_1757_; 
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 1, v_drop_1738_);
v___x_1757_ = v___x_1754_;
goto v_reusejp_1756_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_raw_1751_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_drop_1738_);
v___x_1757_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1756_;
}
v_reusejp_1756_:
{
lean_object* v___x_1759_; 
if (v_isShared_1750_ == 0)
{
lean_ctor_set(v___x_1749_, 0, v___x_1757_);
v___x_1759_ = v___x_1749_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v___x_1757_);
lean_ctor_set(v_reuseFailAlloc_1783_, 1, v_lhsPrec_1743_);
lean_ctor_set(v_reuseFailAlloc_1783_, 2, v_pos_1744_);
lean_ctor_set(v_reuseFailAlloc_1783_, 3, v_cache_1745_);
lean_ctor_set(v_reuseFailAlloc_1783_, 4, v_errorMsg_1746_);
lean_ctor_set(v_reuseFailAlloc_1783_, 5, v_recoveredErrors_1747_);
v___x_1759_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1758_;
}
v_reusejp_1758_:
{
lean_object* v_s_1760_; lean_object* v_stxStack_1761_; lean_object* v_lhsPrec_1762_; lean_object* v_pos_1763_; lean_object* v_cache_1764_; lean_object* v_errorMsg_1765_; lean_object* v_recoveredErrors_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1782_; 
v_s_1760_ = lean_apply_2(v_p_1739_, v_c_1740_, v___x_1759_);
v_stxStack_1761_ = lean_ctor_get(v_s_1760_, 0);
v_lhsPrec_1762_ = lean_ctor_get(v_s_1760_, 1);
v_pos_1763_ = lean_ctor_get(v_s_1760_, 2);
v_cache_1764_ = lean_ctor_get(v_s_1760_, 3);
v_errorMsg_1765_ = lean_ctor_get(v_s_1760_, 4);
v_recoveredErrors_1766_ = lean_ctor_get(v_s_1760_, 5);
v_isSharedCheck_1782_ = !lean_is_exclusive(v_s_1760_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1768_ = v_s_1760_;
v_isShared_1769_ = v_isSharedCheck_1782_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_recoveredErrors_1766_);
lean_inc(v_errorMsg_1765_);
lean_inc(v_cache_1764_);
lean_inc(v_pos_1763_);
lean_inc(v_lhsPrec_1762_);
lean_inc(v_stxStack_1761_);
lean_dec(v_s_1760_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1782_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v_raw_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1780_; 
v_raw_1770_ = lean_ctor_get(v_stxStack_1761_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v_stxStack_1761_);
if (v_isSharedCheck_1780_ == 0)
{
lean_object* v_unused_1781_; 
v_unused_1781_ = lean_ctor_get(v_stxStack_1761_, 1);
lean_dec(v_unused_1781_);
v___x_1772_ = v_stxStack_1761_;
v_isShared_1773_ = v_isSharedCheck_1780_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_raw_1770_);
lean_dec(v_stxStack_1761_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1780_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 1, v_drop_1752_);
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_raw_1770_);
lean_ctor_set(v_reuseFailAlloc_1779_, 1, v_drop_1752_);
v___x_1775_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
lean_object* v___x_1777_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 0, v___x_1775_);
v___x_1777_ = v___x_1768_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_lhsPrec_1762_);
lean_ctor_set(v_reuseFailAlloc_1778_, 2, v_pos_1763_);
lean_ctor_set(v_reuseFailAlloc_1778_, 3, v_cache_1764_);
lean_ctor_set(v_reuseFailAlloc_1778_, 4, v_errorMsg_1765_);
lean_ctor_set(v_reuseFailAlloc_1778_, 5, v_recoveredErrors_1766_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1787_, lean_object* v_c_1788_, lean_object* v_s_1789_){
_start:
{
lean_object* v_cache_1790_; lean_object* v_stxStack_1791_; lean_object* v_lhsPrec_1792_; lean_object* v_pos_1793_; lean_object* v_errorMsg_1794_; lean_object* v_recoveredErrors_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1835_; 
v_cache_1790_ = lean_ctor_get(v_s_1789_, 3);
v_stxStack_1791_ = lean_ctor_get(v_s_1789_, 0);
v_lhsPrec_1792_ = lean_ctor_get(v_s_1789_, 1);
v_pos_1793_ = lean_ctor_get(v_s_1789_, 2);
v_errorMsg_1794_ = lean_ctor_get(v_s_1789_, 4);
v_recoveredErrors_1795_ = lean_ctor_get(v_s_1789_, 5);
v_isSharedCheck_1835_ = !lean_is_exclusive(v_s_1789_);
if (v_isSharedCheck_1835_ == 0)
{
v___x_1797_ = v_s_1789_;
v_isShared_1798_ = v_isSharedCheck_1835_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_recoveredErrors_1795_);
lean_inc(v_errorMsg_1794_);
lean_inc(v_cache_1790_);
lean_inc(v_pos_1793_);
lean_inc(v_lhsPrec_1792_);
lean_inc(v_stxStack_1791_);
lean_dec(v_s_1789_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1835_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v_tokenCache_1799_; lean_object* v_parserCache_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1834_; 
v_tokenCache_1799_ = lean_ctor_get(v_cache_1790_, 0);
v_parserCache_1800_ = lean_ctor_get(v_cache_1790_, 1);
v_isSharedCheck_1834_ = !lean_is_exclusive(v_cache_1790_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1802_ = v_cache_1790_;
v_isShared_1803_ = v_isSharedCheck_1834_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_parserCache_1800_);
lean_inc(v_tokenCache_1799_);
lean_dec(v_cache_1790_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1834_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1804_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 1, v___x_1804_);
v___x_1806_ = v___x_1802_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_tokenCache_1799_);
lean_ctor_set(v_reuseFailAlloc_1833_, 1, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
lean_object* v___x_1808_; 
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 3, v___x_1806_);
v___x_1808_ = v___x_1797_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_stxStack_1791_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v_lhsPrec_1792_);
lean_ctor_set(v_reuseFailAlloc_1832_, 2, v_pos_1793_);
lean_ctor_set(v_reuseFailAlloc_1832_, 3, v___x_1806_);
lean_ctor_set(v_reuseFailAlloc_1832_, 4, v_errorMsg_1794_);
lean_ctor_set(v_reuseFailAlloc_1832_, 5, v_recoveredErrors_1795_);
v___x_1808_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
lean_object* v_s_x27_1809_; lean_object* v_cache_1810_; lean_object* v_stxStack_1811_; lean_object* v_lhsPrec_1812_; lean_object* v_pos_1813_; lean_object* v_errorMsg_1814_; lean_object* v_recoveredErrors_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1831_; 
v_s_x27_1809_ = lean_apply_2(v_p_1787_, v_c_1788_, v___x_1808_);
v_cache_1810_ = lean_ctor_get(v_s_x27_1809_, 3);
v_stxStack_1811_ = lean_ctor_get(v_s_x27_1809_, 0);
v_lhsPrec_1812_ = lean_ctor_get(v_s_x27_1809_, 1);
v_pos_1813_ = lean_ctor_get(v_s_x27_1809_, 2);
v_errorMsg_1814_ = lean_ctor_get(v_s_x27_1809_, 4);
v_recoveredErrors_1815_ = lean_ctor_get(v_s_x27_1809_, 5);
v_isSharedCheck_1831_ = !lean_is_exclusive(v_s_x27_1809_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1817_ = v_s_x27_1809_;
v_isShared_1818_ = v_isSharedCheck_1831_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_recoveredErrors_1815_);
lean_inc(v_errorMsg_1814_);
lean_inc(v_cache_1810_);
lean_inc(v_pos_1813_);
lean_inc(v_lhsPrec_1812_);
lean_inc(v_stxStack_1811_);
lean_dec(v_s_x27_1809_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1831_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v_tokenCache_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1829_; 
v_tokenCache_1819_ = lean_ctor_get(v_cache_1810_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_cache_1810_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v_cache_1810_, 1);
lean_dec(v_unused_1830_);
v___x_1821_ = v_cache_1810_;
v_isShared_1822_ = v_isSharedCheck_1829_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_tokenCache_1819_);
lean_dec(v_cache_1810_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1829_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v_parserCache_1800_);
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_tokenCache_1819_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_parserCache_1800_);
v___x_1824_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1826_; 
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 3, v___x_1824_);
v___x_1826_ = v___x_1817_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v_stxStack_1811_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_lhsPrec_1812_);
lean_ctor_set(v_reuseFailAlloc_1827_, 2, v_pos_1813_);
lean_ctor_set(v_reuseFailAlloc_1827_, 3, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1827_, 4, v_errorMsg_1814_);
lean_ctor_set(v_reuseFailAlloc_1827_, 5, v_recoveredErrors_1815_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1836_, lean_object* v_a_1837_, lean_object* v_a_1838_){
_start:
{
lean_object* v___f_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___f_1839_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1839_, 0, v_p_1836_);
v___x_1840_ = lean_unsigned_to_nat(0u);
v___x_1841_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1840_, v___f_1839_, v_a_1837_, v_a_1838_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1842_){
_start:
{
lean_object* v_info_1843_; lean_object* v_fn_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1852_; 
v_info_1843_ = lean_ctor_get(v_p_1842_, 0);
v_fn_1844_ = lean_ctor_get(v_p_1842_, 1);
v_isSharedCheck_1852_ = !lean_is_exclusive(v_p_1842_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1846_ = v_p_1842_;
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_fn_1844_);
lean_inc(v_info_1843_);
lean_dec(v_p_1842_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1852_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1848_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1848_, 0, v_fn_1844_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1848_);
v___x_1850_ = v___x_1846_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_info_1843_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v___x_1848_);
v___x_1850_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
return v___x_1850_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1853_, lean_object* v_p_1854_, lean_object* v_c_1855_, lean_object* v_s_1856_){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1857_ = lean_apply_1(v_f_1853_, v_c_1855_);
v___x_1858_ = lean_apply_2(v_p_1854_, v___x_1857_, v_s_1856_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1859_, lean_object* v_p_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_){
_start:
{
lean_object* v___f_1863_; lean_object* v___x_1864_; 
v___f_1863_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1863_, 0, v_f_1859_);
lean_closure_set(v___f_1863_, 1, v_p_1860_);
v___x_1864_ = l_Lean_Parser_withResetCacheFn(v___f_1863_, v_a_1861_, v_a_1862_);
return v___x_1864_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1865_, lean_object* v_x_1866_){
_start:
{
if (lean_obj_tag(v_x_1866_) == 0)
{
uint8_t v___x_1867_; 
v___x_1867_ = 0;
return v___x_1867_;
}
else
{
lean_object* v_key_1868_; lean_object* v_tail_1869_; uint8_t v___x_1870_; 
v_key_1868_ = lean_ctor_get(v_x_1866_, 0);
v_tail_1869_ = lean_ctor_get(v_x_1866_, 2);
v___x_1870_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1868_, v_a_1865_);
if (v___x_1870_ == 0)
{
v_x_1866_ = v_tail_1869_;
goto _start;
}
else
{
return v___x_1870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1872_, lean_object* v_x_1873_){
_start:
{
uint8_t v_res_1874_; lean_object* v_r_1875_; 
v_res_1874_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1872_, v_x_1873_);
lean_dec(v_x_1873_);
lean_dec_ref(v_a_1872_);
v_r_1875_ = lean_box(v_res_1874_);
return v_r_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
return v_x_1876_;
}
else
{
lean_object* v_key_1878_; lean_object* v_value_1879_; lean_object* v_tail_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1910_; 
v_key_1878_ = lean_ctor_get(v_x_1877_, 0);
v_value_1879_ = lean_ctor_get(v_x_1877_, 1);
v_tail_1880_ = lean_ctor_get(v_x_1877_, 2);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_x_1877_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1882_ = v_x_1877_;
v_isShared_1883_ = v_isSharedCheck_1910_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_tail_1880_);
lean_inc(v_value_1879_);
lean_inc(v_key_1878_);
lean_dec(v_x_1877_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1910_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v_parserName_1884_; lean_object* v_pos_1885_; lean_object* v___x_1886_; uint64_t v___x_1887_; uint64_t v___y_1889_; 
v_parserName_1884_ = lean_ctor_get(v_key_1878_, 1);
v_pos_1885_ = lean_ctor_get(v_key_1878_, 2);
v___x_1886_ = lean_array_get_size(v_x_1876_);
v___x_1887_ = l_String_instHashableRaw_hash(v_pos_1885_);
if (lean_obj_tag(v_parserName_1884_) == 0)
{
uint64_t v___x_1908_; 
v___x_1908_ = 1723ULL;
v___y_1889_ = v___x_1908_;
goto v___jp_1888_;
}
else
{
uint64_t v_hash_1909_; 
v_hash_1909_ = lean_ctor_get_uint64(v_parserName_1884_, sizeof(void*)*2);
v___y_1889_ = v_hash_1909_;
goto v___jp_1888_;
}
v___jp_1888_:
{
uint64_t v___x_1890_; uint64_t v___x_1891_; uint64_t v___x_1892_; uint64_t v_fold_1893_; uint64_t v___x_1894_; uint64_t v___x_1895_; uint64_t v___x_1896_; size_t v___x_1897_; size_t v___x_1898_; size_t v___x_1899_; size_t v___x_1900_; size_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1904_; 
v___x_1890_ = lean_uint64_mix_hash(v___x_1887_, v___y_1889_);
v___x_1891_ = 32ULL;
v___x_1892_ = lean_uint64_shift_right(v___x_1890_, v___x_1891_);
v_fold_1893_ = lean_uint64_xor(v___x_1890_, v___x_1892_);
v___x_1894_ = 16ULL;
v___x_1895_ = lean_uint64_shift_right(v_fold_1893_, v___x_1894_);
v___x_1896_ = lean_uint64_xor(v_fold_1893_, v___x_1895_);
v___x_1897_ = lean_uint64_to_usize(v___x_1896_);
v___x_1898_ = lean_usize_of_nat(v___x_1886_);
v___x_1899_ = ((size_t)1ULL);
v___x_1900_ = lean_usize_sub(v___x_1898_, v___x_1899_);
v___x_1901_ = lean_usize_land(v___x_1897_, v___x_1900_);
v___x_1902_ = lean_array_uget_borrowed(v_x_1876_, v___x_1901_);
lean_inc(v___x_1902_);
if (v_isShared_1883_ == 0)
{
lean_ctor_set(v___x_1882_, 2, v___x_1902_);
v___x_1904_ = v___x_1882_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v_key_1878_);
lean_ctor_set(v_reuseFailAlloc_1907_, 1, v_value_1879_);
lean_ctor_set(v_reuseFailAlloc_1907_, 2, v___x_1902_);
v___x_1904_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_array_uset(v_x_1876_, v___x_1901_, v___x_1904_);
v_x_1876_ = v___x_1905_;
v_x_1877_ = v_tail_1880_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1911_, lean_object* v_source_1912_, lean_object* v_target_1913_){
_start:
{
lean_object* v___x_1914_; uint8_t v___x_1915_; 
v___x_1914_ = lean_array_get_size(v_source_1912_);
v___x_1915_ = lean_nat_dec_lt(v_i_1911_, v___x_1914_);
if (v___x_1915_ == 0)
{
lean_dec_ref(v_source_1912_);
lean_dec(v_i_1911_);
return v_target_1913_;
}
else
{
lean_object* v_es_1916_; lean_object* v___x_1917_; lean_object* v_source_1918_; lean_object* v_target_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v_es_1916_ = lean_array_fget(v_source_1912_, v_i_1911_);
v___x_1917_ = lean_box(0);
v_source_1918_ = lean_array_fset(v_source_1912_, v_i_1911_, v___x_1917_);
v_target_1919_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1913_, v_es_1916_);
v___x_1920_ = lean_unsigned_to_nat(1u);
v___x_1921_ = lean_nat_add(v_i_1911_, v___x_1920_);
lean_dec(v_i_1911_);
v_i_1911_ = v___x_1921_;
v_source_1912_ = v_source_1918_;
v_target_1913_ = v_target_1919_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1923_){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v_nbuckets_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1924_ = lean_array_get_size(v_data_1923_);
v___x_1925_ = lean_unsigned_to_nat(2u);
v_nbuckets_1926_ = lean_nat_mul(v___x_1924_, v___x_1925_);
v___x_1927_ = lean_unsigned_to_nat(0u);
v___x_1928_ = lean_box(0);
v___x_1929_ = lean_mk_array(v_nbuckets_1926_, v___x_1928_);
v___x_1930_ = lean_array_propagate_mark(v_data_1923_, v___x_1929_);
v___x_1931_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1927_, v_data_1923_, v___x_1930_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1932_, lean_object* v_b_1933_, lean_object* v_x_1934_){
_start:
{
if (lean_obj_tag(v_x_1934_) == 0)
{
lean_dec(v_b_1933_);
lean_dec_ref(v_a_1932_);
return v_x_1934_;
}
else
{
lean_object* v_key_1935_; lean_object* v_value_1936_; lean_object* v_tail_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1949_; 
v_key_1935_ = lean_ctor_get(v_x_1934_, 0);
v_value_1936_ = lean_ctor_get(v_x_1934_, 1);
v_tail_1937_ = lean_ctor_get(v_x_1934_, 2);
v_isSharedCheck_1949_ = !lean_is_exclusive(v_x_1934_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1939_ = v_x_1934_;
v_isShared_1940_ = v_isSharedCheck_1949_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_tail_1937_);
lean_inc(v_value_1936_);
lean_inc(v_key_1935_);
lean_dec(v_x_1934_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1949_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
uint8_t v___x_1941_; 
v___x_1941_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1935_, v_a_1932_);
if (v___x_1941_ == 0)
{
lean_object* v___x_1942_; lean_object* v___x_1944_; 
v___x_1942_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1932_, v_b_1933_, v_tail_1937_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 2, v___x_1942_);
v___x_1944_ = v___x_1939_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_key_1935_);
lean_ctor_set(v_reuseFailAlloc_1945_, 1, v_value_1936_);
lean_ctor_set(v_reuseFailAlloc_1945_, 2, v___x_1942_);
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
lean_dec(v_value_1936_);
lean_dec(v_key_1935_);
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 1, v_b_1933_);
lean_ctor_set(v___x_1939_, 0, v_a_1932_);
v___x_1947_ = v___x_1939_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1932_);
lean_ctor_set(v_reuseFailAlloc_1948_, 1, v_b_1933_);
lean_ctor_set(v_reuseFailAlloc_1948_, 2, v_tail_1937_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1950_, lean_object* v_a_1951_, lean_object* v_b_1952_){
_start:
{
lean_object* v_size_1953_; lean_object* v_buckets_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_2004_; 
v_size_1953_ = lean_ctor_get(v_m_1950_, 0);
v_buckets_1954_ = lean_ctor_get(v_m_1950_, 1);
v_isSharedCheck_2004_ = !lean_is_exclusive(v_m_1950_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1956_ = v_m_1950_;
v_isShared_1957_ = v_isSharedCheck_2004_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_buckets_1954_);
lean_inc(v_size_1953_);
lean_dec(v_m_1950_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_2004_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v_parserName_1958_; lean_object* v_pos_1959_; lean_object* v___x_1960_; uint64_t v___x_1961_; uint64_t v___y_1963_; 
v_parserName_1958_ = lean_ctor_get(v_a_1951_, 1);
v_pos_1959_ = lean_ctor_get(v_a_1951_, 2);
v___x_1960_ = lean_array_get_size(v_buckets_1954_);
v___x_1961_ = l_String_instHashableRaw_hash(v_pos_1959_);
if (lean_obj_tag(v_parserName_1958_) == 0)
{
uint64_t v___x_2002_; 
v___x_2002_ = 1723ULL;
v___y_1963_ = v___x_2002_;
goto v___jp_1962_;
}
else
{
uint64_t v_hash_2003_; 
v_hash_2003_ = lean_ctor_get_uint64(v_parserName_1958_, sizeof(void*)*2);
v___y_1963_ = v_hash_2003_;
goto v___jp_1962_;
}
v___jp_1962_:
{
uint64_t v___x_1964_; uint64_t v___x_1965_; uint64_t v___x_1966_; uint64_t v_fold_1967_; uint64_t v___x_1968_; uint64_t v___x_1969_; uint64_t v___x_1970_; size_t v___x_1971_; size_t v___x_1972_; size_t v___x_1973_; size_t v___x_1974_; size_t v___x_1975_; lean_object* v_bkt_1976_; uint8_t v___x_1977_; 
v___x_1964_ = lean_uint64_mix_hash(v___x_1961_, v___y_1963_);
v___x_1965_ = 32ULL;
v___x_1966_ = lean_uint64_shift_right(v___x_1964_, v___x_1965_);
v_fold_1967_ = lean_uint64_xor(v___x_1964_, v___x_1966_);
v___x_1968_ = 16ULL;
v___x_1969_ = lean_uint64_shift_right(v_fold_1967_, v___x_1968_);
v___x_1970_ = lean_uint64_xor(v_fold_1967_, v___x_1969_);
v___x_1971_ = lean_uint64_to_usize(v___x_1970_);
v___x_1972_ = lean_usize_of_nat(v___x_1960_);
v___x_1973_ = ((size_t)1ULL);
v___x_1974_ = lean_usize_sub(v___x_1972_, v___x_1973_);
v___x_1975_ = lean_usize_land(v___x_1971_, v___x_1974_);
v_bkt_1976_ = lean_array_uget_borrowed(v_buckets_1954_, v___x_1975_);
v___x_1977_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1951_, v_bkt_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v_size_x27_1979_; lean_object* v___x_1980_; lean_object* v_buckets_x27_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; uint8_t v___x_1987_; 
v___x_1978_ = lean_unsigned_to_nat(1u);
v_size_x27_1979_ = lean_nat_add(v_size_1953_, v___x_1978_);
lean_dec(v_size_1953_);
lean_inc(v_bkt_1976_);
v___x_1980_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1980_, 0, v_a_1951_);
lean_ctor_set(v___x_1980_, 1, v_b_1952_);
lean_ctor_set(v___x_1980_, 2, v_bkt_1976_);
v_buckets_x27_1981_ = lean_array_uset(v_buckets_1954_, v___x_1975_, v___x_1980_);
v___x_1982_ = lean_unsigned_to_nat(4u);
v___x_1983_ = lean_nat_mul(v_size_x27_1979_, v___x_1982_);
v___x_1984_ = lean_unsigned_to_nat(3u);
v___x_1985_ = lean_nat_div(v___x_1983_, v___x_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_array_get_size(v_buckets_x27_1981_);
v___x_1987_ = lean_nat_dec_le(v___x_1985_, v___x_1986_);
lean_dec(v___x_1985_);
if (v___x_1987_ == 0)
{
lean_object* v_val_1988_; lean_object* v___x_1990_; 
v_val_1988_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_1981_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v_val_1988_);
lean_ctor_set(v___x_1956_, 0, v_size_x27_1979_);
v___x_1990_ = v___x_1956_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_size_x27_1979_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_val_1988_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
else
{
lean_object* v___x_1993_; 
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v_buckets_x27_1981_);
lean_ctor_set(v___x_1956_, 0, v_size_x27_1979_);
v___x_1993_ = v___x_1956_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_size_x27_1979_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_buckets_x27_1981_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
else
{
lean_object* v___x_1995_; lean_object* v_buckets_x27_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_2000_; 
lean_inc(v_bkt_1976_);
v___x_1995_ = lean_box(0);
v_buckets_x27_1996_ = lean_array_uset(v_buckets_1954_, v___x_1975_, v___x_1995_);
v___x_1997_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1951_, v_b_1952_, v_bkt_1976_);
v___x_1998_ = lean_array_uset(v_buckets_x27_1996_, v___x_1975_, v___x_1997_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 1, v___x_1998_);
v___x_2000_ = v___x_1956_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_size_1953_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v___x_1998_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_2005_, lean_object* v_x_2006_){
_start:
{
if (lean_obj_tag(v_x_2006_) == 0)
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_box(0);
return v___x_2007_;
}
else
{
lean_object* v_key_2008_; lean_object* v_value_2009_; lean_object* v_tail_2010_; uint8_t v___x_2011_; 
v_key_2008_ = lean_ctor_get(v_x_2006_, 0);
v_value_2009_ = lean_ctor_get(v_x_2006_, 1);
v_tail_2010_ = lean_ctor_get(v_x_2006_, 2);
v___x_2011_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_2008_, v_a_2005_);
if (v___x_2011_ == 0)
{
v_x_2006_ = v_tail_2010_;
goto _start;
}
else
{
lean_object* v___x_2013_; 
lean_inc(v_value_2009_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v_value_2009_);
return v___x_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_2014_, lean_object* v_x_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2014_, v_x_2015_);
lean_dec(v_x_2015_);
lean_dec_ref(v_a_2014_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_buckets_2019_; lean_object* v_parserName_2020_; lean_object* v_pos_2021_; lean_object* v___x_2022_; uint64_t v___x_2023_; uint64_t v___y_2025_; 
v_buckets_2019_ = lean_ctor_get(v_m_2017_, 1);
v_parserName_2020_ = lean_ctor_get(v_a_2018_, 1);
v_pos_2021_ = lean_ctor_get(v_a_2018_, 2);
v___x_2022_ = lean_array_get_size(v_buckets_2019_);
v___x_2023_ = l_String_instHashableRaw_hash(v_pos_2021_);
if (lean_obj_tag(v_parserName_2020_) == 0)
{
uint64_t v___x_2040_; 
v___x_2040_ = 1723ULL;
v___y_2025_ = v___x_2040_;
goto v___jp_2024_;
}
else
{
uint64_t v_hash_2041_; 
v_hash_2041_ = lean_ctor_get_uint64(v_parserName_2020_, sizeof(void*)*2);
v___y_2025_ = v_hash_2041_;
goto v___jp_2024_;
}
v___jp_2024_:
{
uint64_t v___x_2026_; uint64_t v___x_2027_; uint64_t v___x_2028_; uint64_t v_fold_2029_; uint64_t v___x_2030_; uint64_t v___x_2031_; uint64_t v___x_2032_; size_t v___x_2033_; size_t v___x_2034_; size_t v___x_2035_; size_t v___x_2036_; size_t v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2026_ = lean_uint64_mix_hash(v___x_2023_, v___y_2025_);
v___x_2027_ = 32ULL;
v___x_2028_ = lean_uint64_shift_right(v___x_2026_, v___x_2027_);
v_fold_2029_ = lean_uint64_xor(v___x_2026_, v___x_2028_);
v___x_2030_ = 16ULL;
v___x_2031_ = lean_uint64_shift_right(v_fold_2029_, v___x_2030_);
v___x_2032_ = lean_uint64_xor(v_fold_2029_, v___x_2031_);
v___x_2033_ = lean_uint64_to_usize(v___x_2032_);
v___x_2034_ = lean_usize_of_nat(v___x_2022_);
v___x_2035_ = ((size_t)1ULL);
v___x_2036_ = lean_usize_sub(v___x_2034_, v___x_2035_);
v___x_2037_ = lean_usize_land(v___x_2033_, v___x_2036_);
v___x_2038_ = lean_array_uget_borrowed(v_buckets_2019_, v___x_2037_);
v___x_2039_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2018_, v___x_2038_);
return v___x_2039_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2042_, v_a_2043_);
lean_dec_ref(v_a_2043_);
lean_dec_ref(v_m_2042_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_2045_, lean_object* v_p_2046_, lean_object* v_c_2047_, lean_object* v_s_2048_){
_start:
{
lean_object* v_cache_2049_; lean_object* v_toCacheableParserContext_2050_; lean_object* v_stxStack_2051_; lean_object* v_pos_2052_; lean_object* v_recoveredErrors_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2102_; 
v_cache_2049_ = lean_ctor_get(v_s_2048_, 3);
lean_inc_ref(v_cache_2049_);
v_toCacheableParserContext_2050_ = lean_ctor_get(v_c_2047_, 2);
v_stxStack_2051_ = lean_ctor_get(v_s_2048_, 0);
v_pos_2052_ = lean_ctor_get(v_s_2048_, 2);
v_recoveredErrors_2053_ = lean_ctor_get(v_s_2048_, 5);
v_isSharedCheck_2102_ = !lean_is_exclusive(v_s_2048_);
if (v_isSharedCheck_2102_ == 0)
{
lean_object* v_unused_2103_; lean_object* v_unused_2104_; lean_object* v_unused_2105_; 
v_unused_2103_ = lean_ctor_get(v_s_2048_, 4);
lean_dec(v_unused_2103_);
v_unused_2104_ = lean_ctor_get(v_s_2048_, 3);
lean_dec(v_unused_2104_);
v_unused_2105_ = lean_ctor_get(v_s_2048_, 1);
lean_dec(v_unused_2105_);
v___x_2055_ = v_s_2048_;
v_isShared_2056_ = v_isSharedCheck_2102_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_recoveredErrors_2053_);
lean_inc(v_pos_2052_);
lean_inc(v_stxStack_2051_);
lean_dec(v_s_2048_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2102_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v_parserCache_2057_; lean_object* v_key_2058_; lean_object* v___x_2059_; 
v_parserCache_2057_ = lean_ctor_get(v_cache_2049_, 1);
lean_inc(v_pos_2052_);
lean_inc_ref(v_toCacheableParserContext_2050_);
v_key_2058_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_2058_, 0, v_toCacheableParserContext_2050_);
lean_ctor_set(v_key_2058_, 1, v_parserName_2045_);
lean_ctor_set(v_key_2058_, 2, v_pos_2052_);
v___x_2059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_2057_, v_key_2058_);
if (lean_obj_tag(v___x_2059_) == 1)
{
lean_object* v_val_2060_; lean_object* v_stx_2061_; lean_object* v_lhsPrec_2062_; lean_object* v_newPos_2063_; lean_object* v_errorMsg_2064_; lean_object* v___x_2065_; lean_object* v___x_2067_; 
lean_dec_ref_known(v_key_2058_, 3);
lean_dec(v_pos_2052_);
lean_dec_ref(v_c_2047_);
lean_dec_ref(v_p_2046_);
v_val_2060_ = lean_ctor_get(v___x_2059_, 0);
lean_inc(v_val_2060_);
lean_dec_ref_known(v___x_2059_, 1);
v_stx_2061_ = lean_ctor_get(v_val_2060_, 0);
lean_inc(v_stx_2061_);
v_lhsPrec_2062_ = lean_ctor_get(v_val_2060_, 1);
lean_inc(v_lhsPrec_2062_);
v_newPos_2063_ = lean_ctor_get(v_val_2060_, 2);
lean_inc(v_newPos_2063_);
v_errorMsg_2064_ = lean_ctor_get(v_val_2060_, 3);
lean_inc(v_errorMsg_2064_);
lean_dec(v_val_2060_);
v___x_2065_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_2051_, v_stx_2061_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 4, v_errorMsg_2064_);
lean_ctor_set(v___x_2055_, 2, v_newPos_2063_);
lean_ctor_set(v___x_2055_, 1, v_lhsPrec_2062_);
lean_ctor_set(v___x_2055_, 0, v___x_2065_);
v___x_2067_ = v___x_2055_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_lhsPrec_2062_);
lean_ctor_set(v_reuseFailAlloc_2068_, 2, v_newPos_2063_);
lean_ctor_set(v_reuseFailAlloc_2068_, 3, v_cache_2049_);
lean_ctor_set(v_reuseFailAlloc_2068_, 4, v_errorMsg_2064_);
lean_ctor_set(v_reuseFailAlloc_2068_, 5, v_recoveredErrors_2053_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
else
{
lean_object* v_raw_2069_; lean_object* v_initStackSz_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2074_; 
lean_dec(v___x_2059_);
v_raw_2069_ = lean_ctor_get(v_stxStack_2051_, 0);
v_initStackSz_2070_ = lean_array_get_size(v_raw_2069_);
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_box(0);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 4, v___x_2072_);
lean_ctor_set(v___x_2055_, 1, v___x_2071_);
v___x_2074_ = v___x_2055_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_stxStack_2051_);
lean_ctor_set(v_reuseFailAlloc_2101_, 1, v___x_2071_);
lean_ctor_set(v_reuseFailAlloc_2101_, 2, v_pos_2052_);
lean_ctor_set(v_reuseFailAlloc_2101_, 3, v_cache_2049_);
lean_ctor_set(v_reuseFailAlloc_2101_, 4, v___x_2072_);
lean_ctor_set(v_reuseFailAlloc_2101_, 5, v_recoveredErrors_2053_);
v___x_2074_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
lean_object* v_s_2075_; lean_object* v_cache_2076_; lean_object* v_stxStack_2077_; lean_object* v_lhsPrec_2078_; lean_object* v_pos_2079_; lean_object* v_errorMsg_2080_; lean_object* v_recoveredErrors_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2100_; 
v_s_2075_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_2070_, v_p_2046_, v_c_2047_, v___x_2074_);
v_cache_2076_ = lean_ctor_get(v_s_2075_, 3);
v_stxStack_2077_ = lean_ctor_get(v_s_2075_, 0);
v_lhsPrec_2078_ = lean_ctor_get(v_s_2075_, 1);
v_pos_2079_ = lean_ctor_get(v_s_2075_, 2);
v_errorMsg_2080_ = lean_ctor_get(v_s_2075_, 4);
v_recoveredErrors_2081_ = lean_ctor_get(v_s_2075_, 5);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_s_2075_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2083_ = v_s_2075_;
v_isShared_2084_ = v_isSharedCheck_2100_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_recoveredErrors_2081_);
lean_inc(v_errorMsg_2080_);
lean_inc(v_cache_2076_);
lean_inc(v_pos_2079_);
lean_inc(v_lhsPrec_2078_);
lean_inc(v_stxStack_2077_);
lean_dec(v_s_2075_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2100_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v_tokenCache_2085_; lean_object* v_parserCache_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2099_; 
v_tokenCache_2085_ = lean_ctor_get(v_cache_2076_, 0);
v_parserCache_2086_ = lean_ctor_get(v_cache_2076_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_cache_2076_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2088_ = v_cache_2076_;
v_isShared_2089_ = v_isSharedCheck_2099_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_parserCache_2086_);
lean_inc(v_tokenCache_2085_);
lean_dec(v_cache_2076_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2099_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2094_; 
v___x_2090_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2077_);
lean_inc(v_errorMsg_2080_);
lean_inc(v_pos_2079_);
lean_inc(v_lhsPrec_2078_);
v___x_2091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v_lhsPrec_2078_);
lean_ctor_set(v___x_2091_, 2, v_pos_2079_);
lean_ctor_set(v___x_2091_, 3, v_errorMsg_2080_);
v___x_2092_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_2086_, v_key_2058_, v___x_2091_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 1, v___x_2092_);
v___x_2094_ = v___x_2088_;
goto v_reusejp_2093_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_tokenCache_2085_);
lean_ctor_set(v_reuseFailAlloc_2098_, 1, v___x_2092_);
v___x_2094_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2093_;
}
v_reusejp_2093_:
{
lean_object* v___x_2096_; 
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 3, v___x_2094_);
v___x_2096_ = v___x_2083_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_stxStack_2077_);
lean_ctor_set(v_reuseFailAlloc_2097_, 1, v_lhsPrec_2078_);
lean_ctor_set(v_reuseFailAlloc_2097_, 2, v_pos_2079_);
lean_ctor_set(v_reuseFailAlloc_2097_, 3, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2097_, 4, v_errorMsg_2080_);
lean_ctor_set(v_reuseFailAlloc_2097_, 5, v_recoveredErrors_2081_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2106_, lean_object* v_m_2107_, lean_object* v_a_2108_){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2107_, v_a_2108_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2110_, lean_object* v_m_2111_, lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2110_, v_m_2111_, v_a_2112_);
lean_dec_ref(v_a_2112_);
lean_dec_ref(v_m_2111_);
return v_res_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2114_, lean_object* v_m_2115_, lean_object* v_a_2116_, lean_object* v_b_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2115_, v_a_2116_, v_b_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2119_, lean_object* v_a_2120_, lean_object* v_x_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2120_, v_x_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2123_, lean_object* v_a_2124_, lean_object* v_x_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2123_, v_a_2124_, v_x_2125_);
lean_dec(v_x_2125_);
lean_dec_ref(v_a_2124_);
return v_res_2126_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2127_, lean_object* v_a_2128_, lean_object* v_x_2129_){
_start:
{
uint8_t v___x_2130_; 
v___x_2130_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2128_, v_x_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2131_, lean_object* v_a_2132_, lean_object* v_x_2133_){
_start:
{
uint8_t v_res_2134_; lean_object* v_r_2135_; 
v_res_2134_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2131_, v_a_2132_, v_x_2133_);
lean_dec(v_x_2133_);
lean_dec_ref(v_a_2132_);
v_r_2135_ = lean_box(v_res_2134_);
return v_r_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2136_, lean_object* v_data_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2139_, lean_object* v_a_2140_, lean_object* v_b_2141_, lean_object* v_x_2142_){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2140_, v_b_2141_, v_x_2142_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2144_, lean_object* v_i_2145_, lean_object* v_source_2146_, lean_object* v_target_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2145_, v_source_2146_, v_target_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2150_, v_x_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2153_, lean_object* v_p_2154_){
_start:
{
lean_object* v_info_2155_; lean_object* v_fn_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2164_; 
v_info_2155_ = lean_ctor_get(v_p_2154_, 0);
v_fn_2156_ = lean_ctor_get(v_p_2154_, 1);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_p_2154_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2158_ = v_p_2154_;
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_fn_2156_);
lean_inc(v_info_2155_);
lean_dec(v_p_2154_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2164_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2160_, 0, v_parserName_2153_);
lean_closure_set(v___x_2160_, 1, v_fn_2156_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 1, v___x_2160_);
v___x_2162_ = v___x_2158_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_info_2155_);
lean_ctor_set(v_reuseFailAlloc_2163_, 1, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2173_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2174_ = l_Lean_addBuiltinDocString(v___x_2172_, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2184_, lean_object* v_ictx_2185_, lean_object* v_pmctx_2186_, lean_object* v_tokens_2187_, lean_object* v_s_2188_){
_start:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2189_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__1));
v___x_2190_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2190_, 0, v_ictx_2185_);
lean_ctor_set(v___x_2190_, 1, v_pmctx_2186_);
lean_ctor_set(v___x_2190_, 2, v___x_2189_);
lean_ctor_set(v___x_2190_, 3, v_tokens_2187_);
v___x_2191_ = lean_apply_2(v_p_2184_, v___x_2190_, v_s_2188_);
return v___x_2191_;
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
