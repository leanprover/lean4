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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter___redArg(lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_h__1_361_){
_start:
{
lean_object* v___x_362_; 
v___x_362_ = lean_apply_2(v_h__1_361_, v_x_359_, v_x_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__String_Pos_Raw_get_x3f_match__1_splitter(lean_object* v_motive_363_, lean_object* v_x_364_, lean_object* v_x_365_, lean_object* v_h__1_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = lean_apply_2(v_h__1_366_, v_x_364_, v_x_365_);
return v___x_367_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27___redArg(lean_object* v_c_368_, lean_object* v_p_369_){
_start:
{
lean_object* v_inputString_370_; uint32_t v___x_371_; 
v_inputString_370_ = lean_ctor_get(v_c_368_, 0);
v___x_371_ = lean_string_utf8_get_fast(v_inputString_370_, v_p_369_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_get_x27___redArg___boxed(lean_object* v_c_372_, lean_object* v_p_373_){
_start:
{
uint32_t v_res_374_; lean_object* v_r_375_; 
v_res_374_ = l_Lean_Parser_InputContext_get_x27___redArg(v_c_372_, v_p_373_);
lean_dec(v_p_373_);
lean_dec_ref(v_c_372_);
v_r_375_ = lean_box_uint32(v_res_374_);
return v_r_375_;
}
}
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_get_x27(lean_object* v_c_376_, lean_object* v_p_377_, lean_object* v_h_378_){
_start:
{
lean_object* v_inputString_379_; uint32_t v___x_380_; 
v_inputString_379_ = lean_ctor_get(v_c_376_, 0);
v___x_380_ = lean_string_utf8_get_fast(v_inputString_379_, v_p_377_);
return v___x_380_;
}
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
LEAN_EXPORT uint32_t l_Lean_Parser_InputContext_getNext(lean_object* v_input_430_, lean_object* v_pos_431_){
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
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_getNext___boxed(lean_object* v_input_435_, lean_object* v_pos_436_){
_start:
{
uint32_t v_res_437_; lean_object* v_r_438_; 
v_res_437_ = l_Lean_Parser_InputContext_getNext(v_input_435_, v_pos_436_);
lean_dec(v_pos_436_);
lean_dec_ref(v_input_435_);
v_r_438_ = lean_box_uint32(v_res_437_);
return v_r_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev(lean_object* v_c_439_, lean_object* v_pos_440_){
_start:
{
lean_object* v_inputString_441_; lean_object* v___x_442_; 
v_inputString_441_ = lean_ctor_get(v_c_439_, 0);
v___x_442_ = lean_string_utf8_prev(v_inputString_441_, v_pos_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_InputContext_prev___boxed(lean_object* v_c_443_, lean_object* v_pos_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Parser_InputContext_prev(v_c_443_, v_pos_444_);
lean_dec(v_pos_444_);
lean_dec_ref(v_c_443_);
return v_res_445_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext_unsafe__2(lean_object* v_a_447_, lean_object* v_b_448_){
_start:
{
lean_object* v_forbiddenTks_449_; lean_object* v_forbiddenTks_450_; size_t v___x_451_; size_t v___x_452_; uint8_t v___x_453_; 
v_forbiddenTks_449_ = lean_ctor_get(v_a_447_, 3);
v_forbiddenTks_450_ = lean_ctor_get(v_b_448_, 3);
v___x_451_ = lean_ptr_addr(v_forbiddenTks_449_);
v___x_452_ = lean_ptr_addr(v_forbiddenTks_450_);
v___x_453_ = lean_usize_dec_eq(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_454_ = lean_array_get_size(v_forbiddenTks_449_);
v___x_455_ = lean_array_get_size(v_forbiddenTks_450_);
v___x_456_ = lean_nat_dec_eq(v___x_454_, v___x_455_);
if (v___x_456_ == 0)
{
return v___x_456_;
}
else
{
lean_object* v___f_457_; uint8_t v___x_458_; 
v___f_457_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0));
v___x_458_ = l_Array_isEqvAux___redArg(v_forbiddenTks_449_, v_forbiddenTks_450_, v___f_457_, v___x_454_);
return v___x_458_;
}
}
else
{
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___boxed(lean_object* v_a_459_, lean_object* v_b_460_){
_start:
{
uint8_t v_res_461_; lean_object* v_r_462_; 
v_res_461_ = l_Lean_Parser_instBEqCacheableParserContext_unsafe__2(v_a_459_, v_b_460_);
lean_dec_ref(v_b_460_);
lean_dec_ref(v_a_459_);
v_r_462_ = lean_box(v_res_461_);
return v_r_462_;
}
}
static lean_object* _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0(void){
_start:
{
lean_object* v___x_463_; lean_object* v___f_464_; 
v___x_463_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_464_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_464_, 0, v___x_463_);
return v___f_464_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqCacheableParserContext___lam__0(lean_object* v___f_465_, lean_object* v_a_466_, lean_object* v_b_467_){
_start:
{
lean_object* v_prec_468_; lean_object* v_quotDepth_469_; uint8_t v_suppressInsideQuot_470_; lean_object* v_savedPos_x3f_471_; lean_object* v_forbiddenTks_472_; lean_object* v_prec_473_; lean_object* v_quotDepth_474_; uint8_t v_suppressInsideQuot_475_; lean_object* v_savedPos_x3f_476_; lean_object* v_forbiddenTks_477_; uint8_t v___x_488_; 
v_prec_468_ = lean_ctor_get(v_a_466_, 0);
lean_inc(v_prec_468_);
v_quotDepth_469_ = lean_ctor_get(v_a_466_, 1);
lean_inc(v_quotDepth_469_);
v_suppressInsideQuot_470_ = lean_ctor_get_uint8(v_a_466_, sizeof(void*)*4);
v_savedPos_x3f_471_ = lean_ctor_get(v_a_466_, 2);
lean_inc(v_savedPos_x3f_471_);
v_forbiddenTks_472_ = lean_ctor_get(v_a_466_, 3);
lean_inc_ref(v_forbiddenTks_472_);
lean_dec_ref(v_a_466_);
v_prec_473_ = lean_ctor_get(v_b_467_, 0);
lean_inc(v_prec_473_);
v_quotDepth_474_ = lean_ctor_get(v_b_467_, 1);
lean_inc(v_quotDepth_474_);
v_suppressInsideQuot_475_ = lean_ctor_get_uint8(v_b_467_, sizeof(void*)*4);
v_savedPos_x3f_476_ = lean_ctor_get(v_b_467_, 2);
lean_inc(v_savedPos_x3f_476_);
v_forbiddenTks_477_ = lean_ctor_get(v_b_467_, 3);
lean_inc_ref(v_forbiddenTks_477_);
lean_dec_ref(v_b_467_);
v___x_488_ = lean_nat_dec_eq(v_prec_468_, v_prec_473_);
lean_dec(v_prec_473_);
lean_dec(v_prec_468_);
if (v___x_488_ == 0)
{
lean_dec_ref(v_forbiddenTks_477_);
lean_dec(v_savedPos_x3f_476_);
lean_dec(v_quotDepth_474_);
lean_dec_ref(v_forbiddenTks_472_);
lean_dec(v_savedPos_x3f_471_);
lean_dec(v_quotDepth_469_);
lean_dec_ref(v___f_465_);
return v___x_488_;
}
else
{
uint8_t v___x_489_; 
v___x_489_ = lean_nat_dec_eq(v_quotDepth_469_, v_quotDepth_474_);
lean_dec(v_quotDepth_474_);
lean_dec(v_quotDepth_469_);
if (v___x_489_ == 0)
{
lean_dec_ref(v_forbiddenTks_477_);
lean_dec(v_savedPos_x3f_476_);
lean_dec_ref(v_forbiddenTks_472_);
lean_dec(v_savedPos_x3f_471_);
lean_dec_ref(v___f_465_);
return v___x_489_;
}
else
{
if (v_suppressInsideQuot_475_ == 0)
{
if (v_suppressInsideQuot_470_ == 0)
{
goto v___jp_478_;
}
else
{
lean_dec_ref(v_forbiddenTks_477_);
lean_dec(v_savedPos_x3f_476_);
lean_dec_ref(v_forbiddenTks_472_);
lean_dec(v_savedPos_x3f_471_);
lean_dec_ref(v___f_465_);
return v_suppressInsideQuot_475_;
}
}
else
{
if (v_suppressInsideQuot_470_ == 0)
{
lean_dec_ref(v_forbiddenTks_477_);
lean_dec(v_savedPos_x3f_476_);
lean_dec_ref(v_forbiddenTks_472_);
lean_dec(v_savedPos_x3f_471_);
lean_dec_ref(v___f_465_);
return v_suppressInsideQuot_470_;
}
else
{
goto v___jp_478_;
}
}
}
}
v___jp_478_:
{
lean_object* v___f_479_; uint8_t v___x_480_; 
v___f_479_ = lean_obj_once(&l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0, &l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0_once, _init_l_Lean_Parser_instBEqCacheableParserContext___lam__0___closed__0);
v___x_480_ = l_instBEqOption_beq___redArg(v___f_479_, v_savedPos_x3f_471_, v_savedPos_x3f_476_);
if (v___x_480_ == 0)
{
lean_dec_ref(v_forbiddenTks_477_);
lean_dec_ref(v_forbiddenTks_472_);
lean_dec_ref(v___f_465_);
return v___x_480_;
}
else
{
size_t v___x_481_; size_t v___x_482_; uint8_t v___x_483_; 
v___x_481_ = lean_ptr_addr(v_forbiddenTks_472_);
v___x_482_ = lean_ptr_addr(v_forbiddenTks_477_);
v___x_483_ = lean_usize_dec_eq(v___x_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v___x_484_ = lean_array_get_size(v_forbiddenTks_472_);
v___x_485_ = lean_array_get_size(v_forbiddenTks_477_);
v___x_486_ = lean_nat_dec_eq(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec_ref(v_forbiddenTks_477_);
lean_dec_ref(v_forbiddenTks_472_);
lean_dec_ref(v___f_465_);
return v___x_486_;
}
else
{
uint8_t v___x_487_; 
v___x_487_ = l_Array_isEqvAux___redArg(v_forbiddenTks_472_, v_forbiddenTks_477_, v___f_465_, v___x_484_);
lean_dec_ref(v_forbiddenTks_477_);
lean_dec_ref(v_forbiddenTks_472_);
return v___x_487_;
}
}
else
{
lean_dec_ref(v_forbiddenTks_477_);
lean_dec_ref(v_forbiddenTks_472_);
lean_dec_ref(v___f_465_);
return v___x_483_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqCacheableParserContext___lam__0___boxed(lean_object* v___f_490_, lean_object* v_a_491_, lean_object* v_b_492_){
_start:
{
uint8_t v_res_493_; lean_object* v_r_494_; 
v_res_493_ = l_Lean_Parser_instBEqCacheableParserContext___lam__0(v___f_490_, v_a_491_, v_b_492_);
v_r_494_ = lean_box(v_res_493_);
return v_r_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0(lean_object* v_x_498_){
_start:
{
lean_object* v_toInputContext_499_; 
v_toInputContext_499_ = lean_ctor_get(v_x_498_, 0);
lean_inc_ref(v_toInputContext_499_);
return v_toInputContext_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instCoeParserContextInputContext___lam__0___boxed(lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_Parser_instCoeParserContextInputContext___lam__0(v_x_500_);
lean_dec_ref(v_x_500_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos___redArg(lean_object* v_c_504_, lean_object* v_endPos_505_){
_start:
{
lean_object* v_toInputContext_506_; lean_object* v_toParserModuleContext_507_; lean_object* v_toCacheableParserContext_508_; lean_object* v_tokens_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_527_; 
v_toInputContext_506_ = lean_ctor_get(v_c_504_, 0);
v_toParserModuleContext_507_ = lean_ctor_get(v_c_504_, 1);
v_toCacheableParserContext_508_ = lean_ctor_get(v_c_504_, 2);
v_tokens_509_ = lean_ctor_get(v_c_504_, 3);
v_isSharedCheck_527_ = !lean_is_exclusive(v_c_504_);
if (v_isSharedCheck_527_ == 0)
{
v___x_511_ = v_c_504_;
v_isShared_512_ = v_isSharedCheck_527_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_tokens_509_);
lean_inc(v_toCacheableParserContext_508_);
lean_inc(v_toParserModuleContext_507_);
lean_inc(v_toInputContext_506_);
lean_dec(v_c_504_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_527_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v_inputString_513_; lean_object* v_fileName_514_; lean_object* v_fileMap_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_525_; 
v_inputString_513_ = lean_ctor_get(v_toInputContext_506_, 0);
v_fileName_514_ = lean_ctor_get(v_toInputContext_506_, 1);
v_fileMap_515_ = lean_ctor_get(v_toInputContext_506_, 2);
v_isSharedCheck_525_ = !lean_is_exclusive(v_toInputContext_506_);
if (v_isSharedCheck_525_ == 0)
{
lean_object* v_unused_526_; 
v_unused_526_ = lean_ctor_get(v_toInputContext_506_, 3);
lean_dec(v_unused_526_);
v___x_517_ = v_toInputContext_506_;
v_isShared_518_ = v_isSharedCheck_525_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_fileMap_515_);
lean_inc(v_fileName_514_);
lean_inc(v_inputString_513_);
lean_dec(v_toInputContext_506_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_525_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 3, v_endPos_505_);
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v_inputString_513_);
lean_ctor_set(v_reuseFailAlloc_524_, 1, v_fileName_514_);
lean_ctor_set(v_reuseFailAlloc_524_, 2, v_fileMap_515_);
lean_ctor_set(v_reuseFailAlloc_524_, 3, v_endPos_505_);
v___x_520_ = v_reuseFailAlloc_524_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
lean_object* v___x_522_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_520_);
v___x_522_ = v___x_511_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v___x_520_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_toParserModuleContext_507_);
lean_ctor_set(v_reuseFailAlloc_523_, 2, v_toCacheableParserContext_508_);
lean_ctor_set(v_reuseFailAlloc_523_, 3, v_tokens_509_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
return v___x_522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserContext_setEndPos(lean_object* v_c_528_, lean_object* v_endPos_529_, lean_object* v_endPos__valid_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Lean_Parser_ParserContext_setEndPos___redArg(v_c_528_, v_endPos_529_);
return v___x_531_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(lean_object* v_x_538_, lean_object* v_x_539_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
if (lean_obj_tag(v_x_539_) == 0)
{
uint8_t v___x_540_; 
v___x_540_ = 1;
return v___x_540_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = 0;
return v___x_541_;
}
}
else
{
if (lean_obj_tag(v_x_539_) == 0)
{
uint8_t v___x_542_; 
v___x_542_ = 0;
return v___x_542_;
}
else
{
lean_object* v_head_543_; lean_object* v_tail_544_; lean_object* v_head_545_; lean_object* v_tail_546_; uint8_t v___x_547_; 
v_head_543_ = lean_ctor_get(v_x_538_, 0);
v_tail_544_ = lean_ctor_get(v_x_538_, 1);
v_head_545_ = lean_ctor_get(v_x_539_, 0);
v_tail_546_ = lean_ctor_get(v_x_539_, 1);
v___x_547_ = lean_string_dec_eq(v_head_543_, v_head_545_);
if (v___x_547_ == 0)
{
return v___x_547_;
}
else
{
v_x_538_ = v_tail_544_;
v_x_539_ = v_tail_546_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0___boxed(lean_object* v_x_549_, lean_object* v_x_550_){
_start:
{
uint8_t v_res_551_; lean_object* v_r_552_; 
v_res_551_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_x_549_, v_x_550_);
lean_dec(v_x_550_);
lean_dec(v_x_549_);
v_r_552_ = lean_box(v_res_551_);
return v_r_552_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqError_beq(lean_object* v_x_553_, lean_object* v_x_554_){
_start:
{
lean_object* v_unexpectedTk_555_; lean_object* v_unexpected_556_; lean_object* v_expected_557_; lean_object* v_unexpectedTk_558_; lean_object* v_unexpected_559_; lean_object* v_expected_560_; uint8_t v___x_561_; 
v_unexpectedTk_555_ = lean_ctor_get(v_x_553_, 0);
v_unexpected_556_ = lean_ctor_get(v_x_553_, 1);
v_expected_557_ = lean_ctor_get(v_x_553_, 2);
v_unexpectedTk_558_ = lean_ctor_get(v_x_554_, 0);
v_unexpected_559_ = lean_ctor_get(v_x_554_, 1);
v_expected_560_ = lean_ctor_get(v_x_554_, 2);
v___x_561_ = l_Lean_Syntax_structEq(v_unexpectedTk_555_, v_unexpectedTk_558_);
if (v___x_561_ == 0)
{
return v___x_561_;
}
else
{
uint8_t v___x_562_; 
v___x_562_ = lean_string_dec_eq(v_unexpected_556_, v_unexpected_559_);
if (v___x_562_ == 0)
{
return v___x_562_;
}
else
{
uint8_t v___x_563_; 
v___x_563_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_557_, v_expected_560_);
return v___x_563_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqError_beq___boxed(lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
uint8_t v_res_566_; lean_object* v_r_567_; 
v_res_566_ = l_Lean_Parser_instBEqError_beq(v_x_564_, v_x_565_);
lean_dec_ref(v_x_565_);
lean_dec_ref(v_x_564_);
v_r_567_ = lean_box(v_res_566_);
return v_r_567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(lean_object* v_x_572_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
lean_object* v___x_573_; 
v___x_573_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
return v___x_573_;
}
else
{
lean_object* v_tail_574_; 
v_tail_574_ = lean_ctor_get(v_x_572_, 1);
if (lean_obj_tag(v_tail_574_) == 0)
{
lean_object* v_head_575_; 
v_head_575_ = lean_ctor_get(v_x_572_, 0);
lean_inc(v_head_575_);
lean_dec_ref_known(v_x_572_, 2);
return v_head_575_;
}
else
{
lean_object* v_tail_576_; 
lean_inc_ref(v_tail_574_);
v_tail_576_ = lean_ctor_get(v_tail_574_, 1);
if (lean_obj_tag(v_tail_576_) == 0)
{
lean_object* v_head_577_; lean_object* v_head_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v_head_577_ = lean_ctor_get(v_x_572_, 0);
lean_inc(v_head_577_);
lean_dec_ref_known(v_x_572_, 2);
v_head_578_ = lean_ctor_get(v_tail_574_, 0);
lean_inc(v_head_578_);
lean_dec_ref_known(v_tail_574_, 2);
v___x_579_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__0));
v___x_580_ = lean_string_append(v_head_577_, v___x_579_);
v___x_581_ = lean_string_append(v___x_580_, v_head_578_);
lean_dec(v_head_578_);
return v___x_581_;
}
else
{
lean_object* v_head_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_head_582_ = lean_ctor_get(v_x_572_, 0);
lean_inc(v_head_582_);
lean_dec_ref_known(v_x_572_, 2);
v___x_583_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_584_ = lean_string_append(v_head_582_, v___x_583_);
v___x_585_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_tail_574_);
v___x_586_ = lean_string_append(v___x_584_, v___x_585_);
lean_dec_ref(v___x_585_);
return v___x_586_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(lean_object* v_as_587_){
_start:
{
lean_object* v___f_588_; lean_object* v___x_589_; 
v___f_588_ = ((lean_object*)(l_Lean_Parser_instBEqCacheableParserContext_unsafe__2___closed__0));
v___x_589_ = l_List_eraseRepsBy___redArg(v___f_588_, v_as_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(lean_object* v_hi_590_, lean_object* v_pivot_591_, lean_object* v_as_592_, lean_object* v_i_593_, lean_object* v_k_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = lean_nat_dec_lt(v_k_594_, v_hi_590_);
if (v___x_595_ == 0)
{
lean_object* v___x_596_; lean_object* v___x_597_; 
lean_dec(v_k_594_);
v___x_596_ = lean_array_fswap(v_as_592_, v_i_593_, v_hi_590_);
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v_i_593_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
return v___x_597_;
}
else
{
lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_598_ = lean_array_fget_borrowed(v_as_592_, v_k_594_);
v___x_599_ = lean_string_dec_lt(v___x_598_, v_pivot_591_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_k_594_, v___x_600_);
lean_dec(v_k_594_);
v_k_594_ = v___x_601_;
goto _start;
}
else
{
lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_603_ = lean_array_fswap(v_as_592_, v_i_593_, v_k_594_);
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_i_593_, v___x_604_);
lean_dec(v_i_593_);
v___x_606_ = lean_nat_add(v_k_594_, v___x_604_);
lean_dec(v_k_594_);
v_as_592_ = v___x_603_;
v_i_593_ = v___x_605_;
v_k_594_ = v___x_606_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg___boxed(lean_object* v_hi_608_, lean_object* v_pivot_609_, lean_object* v_as_610_, lean_object* v_i_611_, lean_object* v_k_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_608_, v_pivot_609_, v_as_610_, v_i_611_, v_k_612_);
lean_dec_ref(v_pivot_609_);
lean_dec(v_hi_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(lean_object* v_n_614_, lean_object* v_as_615_, lean_object* v_lo_616_, lean_object* v_hi_617_){
_start:
{
lean_object* v___y_619_; uint8_t v___x_629_; 
v___x_629_ = lean_nat_dec_lt(v_lo_616_, v_hi_617_);
if (v___x_629_ == 0)
{
lean_dec(v_lo_616_);
return v_as_615_;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v_mid_632_; lean_object* v___y_634_; lean_object* v___y_640_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_630_ = lean_nat_add(v_lo_616_, v_hi_617_);
v___x_631_ = lean_unsigned_to_nat(1u);
v_mid_632_ = lean_nat_shiftr(v___x_630_, v___x_631_);
lean_dec(v___x_630_);
v___x_645_ = lean_array_fget_borrowed(v_as_615_, v_mid_632_);
v___x_646_ = lean_array_fget_borrowed(v_as_615_, v_lo_616_);
v___x_647_ = lean_string_dec_lt(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
v___y_640_ = v_as_615_;
goto v___jp_639_;
}
else
{
lean_object* v___x_648_; 
v___x_648_ = lean_array_fswap(v_as_615_, v_lo_616_, v_mid_632_);
v___y_640_ = v___x_648_;
goto v___jp_639_;
}
v___jp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_635_ = lean_array_fget_borrowed(v___y_634_, v_mid_632_);
v___x_636_ = lean_array_fget_borrowed(v___y_634_, v_hi_617_);
v___x_637_ = lean_string_dec_lt(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_dec(v_mid_632_);
v___y_619_ = v___y_634_;
goto v___jp_618_;
}
else
{
lean_object* v___x_638_; 
v___x_638_ = lean_array_fswap(v___y_634_, v_mid_632_, v_hi_617_);
lean_dec(v_mid_632_);
v___y_619_ = v___x_638_;
goto v___jp_618_;
}
}
v___jp_639_:
{
lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_641_ = lean_array_fget_borrowed(v___y_640_, v_hi_617_);
v___x_642_ = lean_array_fget_borrowed(v___y_640_, v_lo_616_);
v___x_643_ = lean_string_dec_lt(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
v___y_634_ = v___y_640_;
goto v___jp_633_;
}
else
{
lean_object* v___x_644_; 
v___x_644_ = lean_array_fswap(v___y_640_, v_lo_616_, v_hi_617_);
v___y_634_ = v___x_644_;
goto v___jp_633_;
}
}
}
v___jp_618_:
{
lean_object* v_pivot_620_; lean_object* v___x_621_; lean_object* v_fst_622_; lean_object* v_snd_623_; uint8_t v___x_624_; 
v_pivot_620_ = lean_array_fget(v___y_619_, v_hi_617_);
lean_inc_n(v_lo_616_, 2);
v___x_621_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_617_, v_pivot_620_, v___y_619_, v_lo_616_, v_lo_616_);
lean_dec(v_pivot_620_);
v_fst_622_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_fst_622_);
v_snd_623_ = lean_ctor_get(v___x_621_, 1);
lean_inc(v_snd_623_);
lean_dec_ref(v___x_621_);
v___x_624_ = lean_nat_dec_le(v_hi_617_, v_fst_622_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_625_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_614_, v_snd_623_, v_lo_616_, v_fst_622_);
v___x_626_ = lean_unsigned_to_nat(1u);
v___x_627_ = lean_nat_add(v_fst_622_, v___x_626_);
lean_dec(v_fst_622_);
v_as_615_ = v___x_625_;
v_lo_616_ = v___x_627_;
goto _start;
}
else
{
lean_dec(v_fst_622_);
lean_dec(v_lo_616_);
return v_snd_623_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg___boxed(lean_object* v_n_649_, lean_object* v_as_650_, lean_object* v_lo_651_, lean_object* v_hi_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_649_, v_as_650_, v_lo_651_, v_hi_652_);
lean_dec(v_hi_652_);
lean_dec(v_n_649_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_toString(lean_object* v_e_656_){
_start:
{
lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v_unexpected_689_; lean_object* v_expected_690_; lean_object* v___y_692_; lean_object* v___x_702_; uint8_t v___x_703_; 
v_unexpected_689_ = lean_ctor_get(v_e_656_, 1);
lean_inc_ref(v_unexpected_689_);
v_expected_690_ = lean_ctor_get(v_e_656_, 2);
lean_inc(v_expected_690_);
lean_dec_ref(v_e_656_);
v___x_702_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_703_ = lean_string_dec_eq(v_unexpected_689_, v___x_702_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_box(0);
v___x_705_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_705_, 0, v_unexpected_689_);
lean_ctor_set(v___x_705_, 1, v___x_704_);
v___y_692_ = v___x_705_;
goto v___jp_691_;
}
else
{
lean_object* v___x_706_; 
lean_dec_ref(v_unexpected_689_);
v___x_706_ = lean_box(0);
v___y_692_ = v___x_706_;
goto v___jp_691_;
}
v___jp_657_:
{
lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; 
v___x_660_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__0));
v___x_661_ = l_List_appendTR___redArg(v___y_658_, v___y_659_);
v___x_662_ = l_String_intercalate(v___x_660_, v___x_661_);
return v___x_662_;
}
v___jp_663_:
{
lean_object* v___x_667_; lean_object* v_expected_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_667_ = lean_array_to_list(v___y_666_);
v_expected_668_ = l_List_eraseReps___at___00Lean_Parser_Error_toString_spec__0(v___x_667_);
v___x_669_ = ((lean_object*)(l_Lean_Parser_Error_toString___closed__1));
v___x_670_ = l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString(v_expected_668_);
v___x_671_ = lean_string_append(v___x_669_, v___x_670_);
lean_dec_ref(v___x_670_);
v___x_672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_671_);
lean_ctor_set(v___x_672_, 1, v___y_665_);
v___y_658_ = v___y_664_;
v___y_659_ = v___x_672_;
goto v___jp_657_;
}
v___jp_673_:
{
lean_object* v___x_680_; 
v___x_680_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v___y_678_, v___y_675_, v___y_674_, v___y_679_);
lean_dec(v___y_679_);
lean_dec(v___y_678_);
v___y_664_ = v___y_676_;
v___y_665_ = v___y_677_;
v___y_666_ = v___x_680_;
goto v___jp_663_;
}
v___jp_681_:
{
uint8_t v___x_688_; 
v___x_688_ = lean_nat_dec_le(v___y_687_, v___y_683_);
if (v___x_688_ == 0)
{
lean_dec(v___y_683_);
lean_inc(v___y_687_);
v___y_674_ = v___y_687_;
v___y_675_ = v___y_682_;
v___y_676_ = v___y_684_;
v___y_677_ = v___y_686_;
v___y_678_ = v___y_685_;
v___y_679_ = v___y_687_;
goto v___jp_673_;
}
else
{
v___y_674_ = v___y_687_;
v___y_675_ = v___y_682_;
v___y_676_ = v___y_684_;
v___y_677_ = v___y_686_;
v___y_678_ = v___y_685_;
v___y_679_ = v___y_683_;
goto v___jp_673_;
}
}
v___jp_691_:
{
lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_693_ = lean_box(0);
v___x_694_ = l_List_beq___at___00Lean_Parser_instBEqError_beq_spec__0(v_expected_690_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_695_ = lean_array_mk(v_expected_690_);
v___x_696_ = lean_array_get_size(v___x_695_);
v___x_697_ = lean_unsigned_to_nat(0u);
v___x_698_ = lean_nat_dec_eq(v___x_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v___x_699_ = lean_unsigned_to_nat(1u);
v___x_700_ = lean_nat_sub(v___x_696_, v___x_699_);
v___x_701_ = lean_nat_dec_le(v___x_697_, v___x_700_);
if (v___x_701_ == 0)
{
lean_inc(v___x_700_);
v___y_682_ = v___x_695_;
v___y_683_ = v___x_700_;
v___y_684_ = v___y_692_;
v___y_685_ = v___x_696_;
v___y_686_ = v___x_693_;
v___y_687_ = v___x_700_;
goto v___jp_681_;
}
else
{
v___y_682_ = v___x_695_;
v___y_683_ = v___x_700_;
v___y_684_ = v___y_692_;
v___y_685_ = v___x_696_;
v___y_686_ = v___x_693_;
v___y_687_ = v___x_697_;
goto v___jp_681_;
}
}
else
{
v___y_664_ = v___y_692_;
v___y_665_ = v___x_693_;
v___y_666_ = v___x_695_;
goto v___jp_663_;
}
}
else
{
lean_dec(v_expected_690_);
v___y_658_ = v___y_692_;
v___y_659_ = v___x_693_;
goto v___jp_657_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(lean_object* v_n_707_, lean_object* v_as_708_, lean_object* v_lo_709_, lean_object* v_hi_710_, lean_object* v_w_711_, lean_object* v_hlo_712_, lean_object* v_hhi_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___redArg(v_n_707_, v_as_708_, v_lo_709_, v_hi_710_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1___boxed(lean_object* v_n_715_, lean_object* v_as_716_, lean_object* v_lo_717_, lean_object* v_hi_718_, lean_object* v_w_719_, lean_object* v_hlo_720_, lean_object* v_hhi_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1(v_n_715_, v_as_716_, v_lo_717_, v_hi_718_, v_w_719_, v_hlo_720_, v_hhi_721_);
lean_dec(v_hi_718_);
lean_dec(v_n_715_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(lean_object* v_n_723_, lean_object* v_lo_724_, lean_object* v_hi_725_, lean_object* v_hhi_726_, lean_object* v_pivot_727_, lean_object* v_as_728_, lean_object* v_i_729_, lean_object* v_k_730_, lean_object* v_ilo_731_, lean_object* v_ik_732_, lean_object* v_w_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___redArg(v_hi_725_, v_pivot_727_, v_as_728_, v_i_729_, v_k_730_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1___boxed(lean_object* v_n_735_, lean_object* v_lo_736_, lean_object* v_hi_737_, lean_object* v_hhi_738_, lean_object* v_pivot_739_, lean_object* v_as_740_, lean_object* v_i_741_, lean_object* v_k_742_, lean_object* v_ilo_743_, lean_object* v_ik_744_, lean_object* v_w_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_Parser_Error_toString_spec__1_spec__1(v_n_735_, v_lo_736_, v_hi_737_, v_hhi_738_, v_pivot_739_, v_as_740_, v_i_741_, v_k_742_, v_ilo_743_, v_ik_744_, v_w_745_);
lean_dec_ref(v_pivot_739_);
lean_dec(v_hi_737_);
lean_dec(v_lo_736_);
lean_dec(v_n_735_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_Error_merge(lean_object* v_e_u2081_749_, lean_object* v_e_u2082_750_){
_start:
{
lean_object* v_unexpectedTk_751_; lean_object* v_unexpected_752_; lean_object* v_expected_753_; lean_object* v___y_755_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_unexpectedTk_751_ = lean_ctor_get(v_e_u2082_750_, 0);
lean_inc(v_unexpectedTk_751_);
v_unexpected_752_ = lean_ctor_get(v_e_u2082_750_, 1);
lean_inc_ref(v_unexpected_752_);
v_expected_753_ = lean_ctor_get(v_e_u2082_750_, 2);
lean_inc(v_expected_753_);
lean_dec_ref(v_e_u2082_750_);
v___x_767_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_768_ = lean_string_dec_eq(v_unexpected_752_, v___x_767_);
if (v___x_768_ == 0)
{
v___y_755_ = v_unexpected_752_;
goto v___jp_754_;
}
else
{
lean_object* v_unexpected_769_; 
lean_dec_ref(v_unexpected_752_);
v_unexpected_769_ = lean_ctor_get(v_e_u2081_749_, 1);
lean_inc_ref(v_unexpected_769_);
v___y_755_ = v_unexpected_769_;
goto v___jp_754_;
}
v___jp_754_:
{
lean_object* v_expected_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_764_; 
v_expected_756_ = lean_ctor_get(v_e_u2081_749_, 2);
v_isSharedCheck_764_ = !lean_is_exclusive(v_e_u2081_749_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; lean_object* v_unused_766_; 
v_unused_765_ = lean_ctor_get(v_e_u2081_749_, 1);
lean_dec(v_unused_765_);
v_unused_766_ = lean_ctor_get(v_e_u2081_749_, 0);
lean_dec(v_unused_766_);
v___x_758_ = v_e_u2081_749_;
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_expected_756_);
lean_dec(v_e_u2081_749_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_764_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_762_; 
v___x_760_ = l_List_appendTR___redArg(v_expected_756_, v_expected_753_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 2, v___x_760_);
lean_ctor_set(v___x_758_, 1, v___y_755_);
lean_ctor_set(v___x_758_, 0, v_unexpectedTk_751_);
v___x_762_ = v___x_758_;
goto v_reusejp_761_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v_unexpectedTk_751_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v___y_755_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v___x_760_);
v___x_762_ = v_reuseFailAlloc_763_;
goto v_reusejp_761_;
}
v_reusejp_761_:
{
return v___x_762_;
}
}
}
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(lean_object* v_x_770_, lean_object* v_x_771_){
_start:
{
if (lean_obj_tag(v_x_770_) == 0)
{
if (lean_obj_tag(v_x_771_) == 0)
{
uint8_t v___x_772_; 
v___x_772_ = 1;
return v___x_772_;
}
else
{
uint8_t v___x_773_; 
v___x_773_ = 0;
return v___x_773_;
}
}
else
{
if (lean_obj_tag(v_x_771_) == 0)
{
uint8_t v___x_774_; 
v___x_774_ = 0;
return v___x_774_;
}
else
{
lean_object* v_val_775_; lean_object* v_val_776_; uint8_t v_decide_777_; 
v_val_775_ = lean_ctor_get(v_x_770_, 0);
v_val_776_ = lean_ctor_get(v_x_771_, 0);
v_decide_777_ = lean_nat_dec_eq(v_val_775_, v_val_776_);
return v_decide_777_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0___boxed(lean_object* v_x_778_, lean_object* v_x_779_){
_start:
{
uint8_t v_res_780_; lean_object* v_r_781_; 
v_res_780_ = l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_x_778_, v_x_779_);
lean_dec(v_x_779_);
lean_dec(v_x_778_);
v_r_781_ = lean_box(v_res_780_);
return v_r_781_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(lean_object* v_xs_782_, lean_object* v_ys_783_, lean_object* v_x_784_){
_start:
{
lean_object* v_zero_785_; uint8_t v_isZero_786_; 
v_zero_785_ = lean_unsigned_to_nat(0u);
v_isZero_786_ = lean_nat_dec_eq(v_x_784_, v_zero_785_);
if (v_isZero_786_ == 1)
{
lean_dec(v_x_784_);
return v_isZero_786_;
}
else
{
lean_object* v_one_787_; lean_object* v_n_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
v_one_787_ = lean_unsigned_to_nat(1u);
v_n_788_ = lean_nat_sub(v_x_784_, v_one_787_);
lean_dec(v_x_784_);
v___x_789_ = lean_array_fget_borrowed(v_xs_782_, v_n_788_);
v___x_790_ = lean_array_fget_borrowed(v_ys_783_, v_n_788_);
v___x_791_ = lean_string_dec_eq(v___x_789_, v___x_790_);
if (v___x_791_ == 0)
{
lean_dec(v_n_788_);
return v___x_791_;
}
else
{
v_x_784_ = v_n_788_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg___boxed(lean_object* v_xs_793_, lean_object* v_ys_794_, lean_object* v_x_795_){
_start:
{
uint8_t v_res_796_; lean_object* v_r_797_; 
v_res_796_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_793_, v_ys_794_, v_x_795_);
lean_dec_ref(v_ys_794_);
lean_dec_ref(v_xs_793_);
v_r_797_ = lean_box(v_res_796_);
return v_r_797_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_instBEqParserCacheKey_beq(lean_object* v_x_798_, lean_object* v_x_799_){
_start:
{
lean_object* v_toCacheableParserContext_800_; lean_object* v_parserName_801_; lean_object* v_pos_802_; lean_object* v_toCacheableParserContext_803_; lean_object* v_parserName_804_; lean_object* v_pos_805_; uint8_t v___y_810_; lean_object* v_prec_811_; lean_object* v_quotDepth_812_; uint8_t v_suppressInsideQuot_813_; lean_object* v_savedPos_x3f_814_; lean_object* v_forbiddenTks_815_; lean_object* v_prec_816_; lean_object* v_quotDepth_817_; uint8_t v_suppressInsideQuot_818_; lean_object* v_savedPos_x3f_819_; lean_object* v_forbiddenTks_820_; uint8_t v___x_830_; 
v_toCacheableParserContext_800_ = lean_ctor_get(v_x_798_, 0);
v_parserName_801_ = lean_ctor_get(v_x_798_, 1);
v_pos_802_ = lean_ctor_get(v_x_798_, 2);
v_toCacheableParserContext_803_ = lean_ctor_get(v_x_799_, 0);
v_parserName_804_ = lean_ctor_get(v_x_799_, 1);
v_pos_805_ = lean_ctor_get(v_x_799_, 2);
v_prec_811_ = lean_ctor_get(v_toCacheableParserContext_800_, 0);
v_quotDepth_812_ = lean_ctor_get(v_toCacheableParserContext_800_, 1);
v_suppressInsideQuot_813_ = lean_ctor_get_uint8(v_toCacheableParserContext_800_, sizeof(void*)*4);
v_savedPos_x3f_814_ = lean_ctor_get(v_toCacheableParserContext_800_, 2);
v_forbiddenTks_815_ = lean_ctor_get(v_toCacheableParserContext_800_, 3);
v_prec_816_ = lean_ctor_get(v_toCacheableParserContext_803_, 0);
v_quotDepth_817_ = lean_ctor_get(v_toCacheableParserContext_803_, 1);
v_suppressInsideQuot_818_ = lean_ctor_get_uint8(v_toCacheableParserContext_803_, sizeof(void*)*4);
v_savedPos_x3f_819_ = lean_ctor_get(v_toCacheableParserContext_803_, 2);
v_forbiddenTks_820_ = lean_ctor_get(v_toCacheableParserContext_803_, 3);
v___x_830_ = lean_nat_dec_eq(v_prec_811_, v_prec_816_);
if (v___x_830_ == 0)
{
return v___x_830_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = lean_nat_dec_eq(v_quotDepth_812_, v_quotDepth_817_);
if (v___x_831_ == 0)
{
return v___x_831_;
}
else
{
if (v_suppressInsideQuot_818_ == 0)
{
if (v_suppressInsideQuot_813_ == 0)
{
goto v___jp_821_;
}
else
{
return v_suppressInsideQuot_818_;
}
}
else
{
if (v_suppressInsideQuot_813_ == 0)
{
return v_suppressInsideQuot_813_;
}
else
{
goto v___jp_821_;
}
}
}
}
v___jp_806_:
{
uint8_t v___x_807_; 
v___x_807_ = lean_name_eq(v_parserName_801_, v_parserName_804_);
if (v___x_807_ == 0)
{
return v___x_807_;
}
else
{
uint8_t v_decide_808_; 
v_decide_808_ = lean_nat_dec_eq(v_pos_802_, v_pos_805_);
return v_decide_808_;
}
}
v___jp_809_:
{
if (v___y_810_ == 0)
{
return v___y_810_;
}
else
{
goto v___jp_806_;
}
}
v___jp_821_:
{
uint8_t v___x_822_; 
v___x_822_ = l_instBEqOption_beq___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__0(v_savedPos_x3f_814_, v_savedPos_x3f_819_);
if (v___x_822_ == 0)
{
v___y_810_ = v___x_822_;
goto v___jp_809_;
}
else
{
size_t v___x_823_; size_t v___x_824_; uint8_t v___x_825_; 
v___x_823_ = lean_ptr_addr(v_forbiddenTks_815_);
v___x_824_ = lean_ptr_addr(v_forbiddenTks_820_);
v___x_825_ = lean_usize_dec_eq(v___x_823_, v___x_824_);
if (v___x_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v___x_826_ = lean_array_get_size(v_forbiddenTks_815_);
v___x_827_ = lean_array_get_size(v_forbiddenTks_820_);
v___x_828_ = lean_nat_dec_eq(v___x_826_, v___x_827_);
if (v___x_828_ == 0)
{
return v___x_828_;
}
else
{
uint8_t v___x_829_; 
v___x_829_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_forbiddenTks_815_, v_forbiddenTks_820_, v___x_826_);
v___y_810_ = v___x_829_;
goto v___jp_809_;
}
}
else
{
goto v___jp_806_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instBEqParserCacheKey_beq___boxed(lean_object* v_x_832_, lean_object* v_x_833_){
_start:
{
uint8_t v_res_834_; lean_object* v_r_835_; 
v_res_834_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_x_832_, v_x_833_);
lean_dec_ref(v_x_833_);
lean_dec_ref(v_x_832_);
v_r_835_ = lean_box(v_res_834_);
return v_r_835_;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(lean_object* v_xs_836_, lean_object* v_ys_837_, lean_object* v_hsz_838_, lean_object* v_x_839_, lean_object* v_x_840_){
_start:
{
uint8_t v___x_841_; 
v___x_841_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___redArg(v_xs_836_, v_ys_837_, v_x_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1___boxed(lean_object* v_xs_842_, lean_object* v_ys_843_, lean_object* v_hsz_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
uint8_t v_res_847_; lean_object* v_r_848_; 
v_res_847_ = l_Array_isEqvAux___at___00Lean_Parser_instBEqParserCacheKey_beq_spec__1(v_xs_842_, v_ys_843_, v_hsz_844_, v_x_845_, v_x_846_);
lean_dec_ref(v_ys_843_);
lean_dec_ref(v_xs_842_);
v_r_848_ = lean_box(v_res_847_);
return v_r_848_;
}
}
LEAN_EXPORT uint64_t l_Lean_Parser_instHashableParserCacheKey___lam__0(lean_object* v_k_851_){
_start:
{
lean_object* v_parserName_852_; lean_object* v_pos_853_; uint64_t v___x_854_; 
v_parserName_852_ = lean_ctor_get(v_k_851_, 1);
v_pos_853_ = lean_ctor_get(v_k_851_, 2);
v___x_854_ = l_String_instHashableRaw_hash(v_pos_853_);
if (lean_obj_tag(v_parserName_852_) == 0)
{
uint64_t v___x_855_; uint64_t v___x_856_; 
v___x_855_ = 1723ULL;
v___x_856_ = lean_uint64_mix_hash(v___x_854_, v___x_855_);
return v___x_856_;
}
else
{
uint64_t v_hash_857_; uint64_t v___x_858_; 
v_hash_857_ = lean_ctor_get_uint64(v_parserName_852_, sizeof(void*)*2);
v___x_858_ = lean_uint64_mix_hash(v___x_854_, v_hash_857_);
return v___x_858_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instHashableParserCacheKey___lam__0___boxed(lean_object* v_k_859_){
_start:
{
uint64_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_Lean_Parser_instHashableParserCacheKey___lam__0(v_k_859_);
lean_dec_ref(v_k_859_);
v_r_861_ = lean_box_uint64(v_res_860_);
return v_r_861_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__0(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_box(0);
v___x_865_ = lean_unsigned_to_nat(16u);
v___x_866_ = lean_mk_array(v___x_865_, v___x_864_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_Parser_initCacheForInput___closed__1(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___x_867_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__0, &l_Lean_Parser_initCacheForInput___closed__0_once, _init_l_Lean_Parser_initCacheForInput___closed__0);
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput(lean_object* v_input_870_){
_start:
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v___x_871_ = lean_string_utf8_byte_size(v_input_870_);
v___x_872_ = lean_unsigned_to_nat(1u);
v___x_873_ = lean_nat_add(v___x_871_, v___x_872_);
v___x_874_ = lean_unsigned_to_nat(0u);
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_876_, 0, v___x_873_);
lean_ctor_set(v___x_876_, 1, v___x_874_);
lean_ctor_set(v___x_876_, 2, v___x_875_);
v___x_877_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_876_);
lean_ctor_set(v___x_878_, 1, v___x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_initCacheForInput___boxed(lean_object* v_input_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Lean_Parser_initCacheForInput(v_input_879_);
lean_dec_ref(v_input_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_toSubarray(lean_object* v_stack_881_){
_start:
{
lean_object* v_raw_882_; lean_object* v_drop_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_raw_882_ = lean_ctor_get(v_stack_881_, 0);
lean_inc_ref(v_raw_882_);
v_drop_883_ = lean_ctor_get(v_stack_881_, 1);
lean_inc(v_drop_883_);
lean_dec_ref(v_stack_881_);
v___x_884_ = lean_array_get_size(v_raw_882_);
v___x_885_ = l_Array_toSubarray___redArg(v_raw_882_, v_drop_883_, v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size(lean_object* v_stack_892_){
_start:
{
lean_object* v_raw_893_; lean_object* v_drop_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v_raw_893_ = lean_ctor_get(v_stack_892_, 0);
v_drop_894_ = lean_ctor_get(v_stack_892_, 1);
v___x_895_ = lean_array_get_size(v_raw_893_);
v___x_896_ = lean_nat_sub(v___x_895_, v_drop_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_size___boxed(lean_object* v_stack_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Lean_Parser_SyntaxStack_size(v_stack_897_);
lean_dec_ref(v_stack_897_);
return v_res_898_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_SyntaxStack_isEmpty(lean_object* v_stack_899_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_900_ = l_Lean_Parser_SyntaxStack_size(v_stack_899_);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_nat_dec_eq(v___x_900_, v___x_901_);
lean_dec(v___x_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_isEmpty___boxed(lean_object* v_stack_903_){
_start:
{
uint8_t v_res_904_; lean_object* v_r_905_; 
v_res_904_ = l_Lean_Parser_SyntaxStack_isEmpty(v_stack_903_);
lean_dec_ref(v_stack_903_);
v_r_905_ = lean_box(v_res_904_);
return v_r_905_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink(lean_object* v_stack_906_, lean_object* v_n_907_){
_start:
{
lean_object* v_raw_908_; lean_object* v_drop_909_; lean_object* v___x_911_; uint8_t v_isShared_912_; uint8_t v_isSharedCheck_918_; 
v_raw_908_ = lean_ctor_get(v_stack_906_, 0);
v_drop_909_ = lean_ctor_get(v_stack_906_, 1);
v_isSharedCheck_918_ = !lean_is_exclusive(v_stack_906_);
if (v_isSharedCheck_918_ == 0)
{
v___x_911_ = v_stack_906_;
v_isShared_912_ = v_isSharedCheck_918_;
goto v_resetjp_910_;
}
else
{
lean_inc(v_drop_909_);
lean_inc(v_raw_908_);
lean_dec(v_stack_906_);
v___x_911_ = lean_box(0);
v_isShared_912_ = v_isSharedCheck_918_;
goto v_resetjp_910_;
}
v_resetjp_910_:
{
lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_916_; 
v___x_913_ = lean_nat_add(v_drop_909_, v_n_907_);
v___x_914_ = l_Array_shrink___redArg(v_raw_908_, v___x_913_);
lean_dec(v___x_913_);
if (v_isShared_912_ == 0)
{
lean_ctor_set(v___x_911_, 0, v___x_914_);
v___x_916_ = v___x_911_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v___x_914_);
lean_ctor_set(v_reuseFailAlloc_917_, 1, v_drop_909_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_shrink___boxed(lean_object* v_stack_919_, lean_object* v_n_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Parser_SyntaxStack_shrink(v_stack_919_, v_n_920_);
lean_dec(v_n_920_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_push(lean_object* v_stack_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_raw_924_; lean_object* v_drop_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_933_; 
v_raw_924_ = lean_ctor_get(v_stack_922_, 0);
v_drop_925_ = lean_ctor_get(v_stack_922_, 1);
v_isSharedCheck_933_ = !lean_is_exclusive(v_stack_922_);
if (v_isSharedCheck_933_ == 0)
{
v___x_927_ = v_stack_922_;
v_isShared_928_ = v_isSharedCheck_933_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_drop_925_);
lean_inc(v_raw_924_);
lean_dec(v_stack_922_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_933_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_929_ = lean_array_push(v_raw_924_, v_a_923_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_929_);
v___x_931_ = v___x_927_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_drop_925_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_pop(lean_object* v_stack_934_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_935_ = lean_unsigned_to_nat(0u);
v___x_936_ = l_Lean_Parser_SyntaxStack_size(v_stack_934_);
v___x_937_ = lean_nat_dec_lt(v___x_935_, v___x_936_);
lean_dec(v___x_936_);
if (v___x_937_ == 0)
{
return v_stack_934_;
}
else
{
lean_object* v_raw_938_; lean_object* v_drop_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_947_; 
v_raw_938_ = lean_ctor_get(v_stack_934_, 0);
v_drop_939_ = lean_ctor_get(v_stack_934_, 1);
v_isSharedCheck_947_ = !lean_is_exclusive(v_stack_934_);
if (v_isSharedCheck_947_ == 0)
{
v___x_941_ = v_stack_934_;
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_drop_939_);
lean_inc(v_raw_938_);
lean_dec(v_stack_934_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_947_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_array_pop(v_raw_938_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 0, v___x_943_);
v___x_945_ = v___x_941_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v_drop_939_);
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
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(lean_object* v_msg_948_){
_start:
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = lean_box(0);
v___x_950_ = lean_panic_fn_borrowed(v___x_949_, v_msg_948_);
return v___x_950_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_back___closed__3(void){
_start:
{
lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_954_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__2));
v___x_955_ = lean_unsigned_to_nat(4u);
v___x_956_ = lean_unsigned_to_nat(315u);
v___x_957_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__1));
v___x_958_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_959_ = l_mkPanicMessageWithDecl(v___x_958_, v___x_957_, v___x_956_, v___x_955_, v___x_954_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back(lean_object* v_stack_960_){
_start:
{
lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = l_Lean_Parser_SyntaxStack_size(v_stack_960_);
v___x_963_ = lean_nat_dec_lt(v___x_961_, v___x_962_);
lean_dec(v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_964_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_back___closed__3, &l_Lean_Parser_SyntaxStack_back___closed__3_once, _init_l_Lean_Parser_SyntaxStack_back___closed__3);
v___x_965_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_964_);
return v___x_965_;
}
else
{
lean_object* v_raw_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
v_raw_966_ = lean_ctor_get(v_stack_960_, 0);
v___x_967_ = lean_box(0);
v___x_968_ = lean_array_get_size(v_raw_966_);
v___x_969_ = lean_unsigned_to_nat(1u);
v___x_970_ = lean_nat_sub(v___x_968_, v___x_969_);
v___x_971_ = lean_array_get_borrowed(v___x_967_, v_raw_966_, v___x_970_);
lean_dec(v___x_970_);
lean_inc(v___x_971_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_back___boxed(lean_object* v_stack_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Lean_Parser_SyntaxStack_back(v_stack_972_);
lean_dec_ref(v_stack_972_);
return v_res_973_;
}
}
static lean_object* _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2(void){
_start:
{
lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v___x_976_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__1));
v___x_977_ = lean_unsigned_to_nat(4u);
v___x_978_ = lean_unsigned_to_nat(321u);
v___x_979_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_get_x21___closed__0));
v___x_980_ = ((lean_object*)(l_Lean_Parser_SyntaxStack_back___closed__0));
v___x_981_ = l_mkPanicMessageWithDecl(v___x_980_, v___x_979_, v___x_978_, v___x_977_, v___x_976_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21(lean_object* v_stack_982_, lean_object* v_i_983_){
_start:
{
lean_object* v___x_984_; uint8_t v___x_985_; 
v___x_984_ = l_Lean_Parser_SyntaxStack_size(v_stack_982_);
v___x_985_ = lean_nat_dec_lt(v_i_983_, v___x_984_);
lean_dec(v___x_984_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_obj_once(&l_Lean_Parser_SyntaxStack_get_x21___closed__2, &l_Lean_Parser_SyntaxStack_get_x21___closed__2_once, _init_l_Lean_Parser_SyntaxStack_get_x21___closed__2);
v___x_987_ = l_panic___at___00Lean_Parser_SyntaxStack_back_spec__0(v___x_986_);
return v___x_987_;
}
else
{
lean_object* v_raw_988_; lean_object* v_drop_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_raw_988_ = lean_ctor_get(v_stack_982_, 0);
v_drop_989_ = lean_ctor_get(v_stack_982_, 1);
v___x_990_ = lean_box(0);
v___x_991_ = lean_nat_add(v_drop_989_, v_i_983_);
v___x_992_ = lean_array_get_borrowed(v___x_990_, v_raw_988_, v___x_991_);
lean_dec(v___x_991_);
lean_inc(v___x_992_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_get_x21___boxed(lean_object* v_stack_993_, lean_object* v_i_994_){
_start:
{
lean_object* v_res_995_; 
v_res_995_ = l_Lean_Parser_SyntaxStack_get_x21(v_stack_993_, v_i_994_);
lean_dec(v_i_994_);
lean_dec_ref(v_stack_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract(lean_object* v_stack_996_, lean_object* v_start_997_, lean_object* v_stop_998_){
_start:
{
lean_object* v_raw_999_; lean_object* v_drop_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v_raw_999_ = lean_ctor_get(v_stack_996_, 0);
v_drop_1000_ = lean_ctor_get(v_stack_996_, 1);
v___x_1001_ = lean_nat_add(v_drop_1000_, v_start_997_);
v___x_1002_ = lean_nat_add(v_drop_1000_, v_stop_998_);
v___x_1003_ = l_Array_extract___redArg(v_raw_999_, v___x_1001_, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_extract___boxed(lean_object* v_stack_1004_, lean_object* v_start_1005_, lean_object* v_stop_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Lean_Parser_SyntaxStack_extract(v_stack_1004_, v_start_1005_, v_stop_1006_);
lean_dec(v_stop_1006_);
lean_dec(v_start_1005_);
lean_dec_ref(v_stack_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(lean_object* v_stack_1008_, lean_object* v_stxs_1009_){
_start:
{
lean_object* v_raw_1010_; lean_object* v_drop_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1019_; 
v_raw_1010_ = lean_ctor_get(v_stack_1008_, 0);
v_drop_1011_ = lean_ctor_get(v_stack_1008_, 1);
v_isSharedCheck_1019_ = !lean_is_exclusive(v_stack_1008_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1013_ = v_stack_1008_;
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_drop_1011_);
lean_inc(v_raw_1010_);
lean_dec(v_stack_1008_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1015_ = l_Array_append___redArg(v_raw_1010_, v_stxs_1009_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1015_);
v___x_1017_ = v___x_1013_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1018_, 1, v_drop_1011_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1___boxed(lean_object* v_stack_1020_, lean_object* v_stxs_1021_){
_start:
{
lean_object* v_res_1022_; 
v_res_1022_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___private__1(v_stack_1020_, v_stxs_1021_);
lean_dec_ref(v_stxs_1021_);
return v_res_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(lean_object* v_stack_1023_, lean_object* v_stxs_1024_){
_start:
{
lean_object* v_raw_1025_; lean_object* v_drop_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1034_; 
v_raw_1025_ = lean_ctor_get(v_stack_1023_, 0);
v_drop_1026_ = lean_ctor_get(v_stack_1023_, 1);
v_isSharedCheck_1034_ = !lean_is_exclusive(v_stack_1023_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1028_ = v_stack_1023_;
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_drop_1026_);
lean_inc(v_raw_1025_);
lean_dec(v_stack_1023_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1034_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1030_; lean_object* v___x_1032_; 
v___x_1030_ = l_Array_append___redArg(v_raw_1025_, v_stxs_1024_);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1030_);
v___x_1032_ = v___x_1028_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v___x_1030_);
lean_ctor_set(v_reuseFailAlloc_1033_, 1, v_drop_1026_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0___boxed(lean_object* v_stack_1035_, lean_object* v_stxs_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l_Lean_Parser_SyntaxStack_instHAppendArraySyntax___lam__0(v_stack_1035_, v_stxs_1036_);
lean_dec_ref(v_stxs_1036_);
return v_res_1037_;
}
}
LEAN_EXPORT uint8_t l_Lean_Parser_ParserState_hasError(lean_object* v_s_1040_){
_start:
{
lean_object* v_errorMsg_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; uint8_t v___x_1044_; 
v_errorMsg_1041_ = lean_ctor_get(v_s_1040_, 4);
lean_inc(v_errorMsg_1041_);
lean_dec_ref(v_s_1040_);
v___x_1042_ = ((lean_object*)(l_Lean_Parser_instBEqError___closed__0));
v___x_1043_ = lean_box(0);
v___x_1044_ = l_instBEqOption_beq___redArg(v___x_1042_, v_errorMsg_1041_, v___x_1043_);
if (v___x_1044_ == 0)
{
uint8_t v___x_1045_; 
v___x_1045_ = 1;
return v___x_1045_;
}
else
{
uint8_t v___x_1046_; 
v___x_1046_ = 0;
return v___x_1046_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_hasError___boxed(lean_object* v_s_1047_){
_start:
{
uint8_t v_res_1048_; lean_object* v_r_1049_; 
v_res_1048_ = l_Lean_Parser_ParserState_hasError(v_s_1047_);
v_r_1049_ = lean_box(v_res_1048_);
return v_r_1049_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize(lean_object* v_s_1050_){
_start:
{
lean_object* v_stxStack_1051_; lean_object* v___x_1052_; 
v_stxStack_1051_ = lean_ctor_get(v_s_1050_, 0);
v___x_1052_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_stackSize___boxed(lean_object* v_s_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Parser_ParserState_stackSize(v_s_1053_);
lean_dec_ref(v_s_1053_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore(lean_object* v_s_1055_, lean_object* v_iniStackSz_1056_, lean_object* v_iniPos_1057_){
_start:
{
lean_object* v_stxStack_1058_; lean_object* v_lhsPrec_1059_; lean_object* v_cache_1060_; lean_object* v_recoveredErrors_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1070_; 
v_stxStack_1058_ = lean_ctor_get(v_s_1055_, 0);
v_lhsPrec_1059_ = lean_ctor_get(v_s_1055_, 1);
v_cache_1060_ = lean_ctor_get(v_s_1055_, 3);
v_recoveredErrors_1061_ = lean_ctor_get(v_s_1055_, 5);
v_isSharedCheck_1070_ = !lean_is_exclusive(v_s_1055_);
if (v_isSharedCheck_1070_ == 0)
{
lean_object* v_unused_1071_; lean_object* v_unused_1072_; 
v_unused_1071_ = lean_ctor_get(v_s_1055_, 4);
lean_dec(v_unused_1071_);
v_unused_1072_ = lean_ctor_get(v_s_1055_, 2);
lean_dec(v_unused_1072_);
v___x_1063_ = v_s_1055_;
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_recoveredErrors_1061_);
lean_inc(v_cache_1060_);
lean_inc(v_lhsPrec_1059_);
lean_inc(v_stxStack_1058_);
lean_dec(v_s_1055_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1070_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
v___x_1065_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1058_, v_iniStackSz_1056_);
v___x_1066_ = lean_box(0);
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 4, v___x_1066_);
lean_ctor_set(v___x_1063_, 2, v_iniPos_1057_);
lean_ctor_set(v___x_1063_, 0, v___x_1065_);
v___x_1068_ = v___x_1063_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v___x_1065_);
lean_ctor_set(v_reuseFailAlloc_1069_, 1, v_lhsPrec_1059_);
lean_ctor_set(v_reuseFailAlloc_1069_, 2, v_iniPos_1057_);
lean_ctor_set(v_reuseFailAlloc_1069_, 3, v_cache_1060_);
lean_ctor_set(v_reuseFailAlloc_1069_, 4, v___x_1066_);
lean_ctor_set(v_reuseFailAlloc_1069_, 5, v_recoveredErrors_1061_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_restore___boxed(lean_object* v_s_1073_, lean_object* v_iniStackSz_1074_, lean_object* v_iniPos_1075_){
_start:
{
lean_object* v_res_1076_; 
v_res_1076_ = l_Lean_Parser_ParserState_restore(v_s_1073_, v_iniStackSz_1074_, v_iniPos_1075_);
lean_dec(v_iniStackSz_1074_);
return v_res_1076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setPos(lean_object* v_s_1077_, lean_object* v_pos_1078_){
_start:
{
lean_object* v_stxStack_1079_; lean_object* v_lhsPrec_1080_; lean_object* v_cache_1081_; lean_object* v_errorMsg_1082_; lean_object* v_recoveredErrors_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1090_; 
v_stxStack_1079_ = lean_ctor_get(v_s_1077_, 0);
v_lhsPrec_1080_ = lean_ctor_get(v_s_1077_, 1);
v_cache_1081_ = lean_ctor_get(v_s_1077_, 3);
v_errorMsg_1082_ = lean_ctor_get(v_s_1077_, 4);
v_recoveredErrors_1083_ = lean_ctor_get(v_s_1077_, 5);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_s_1077_);
if (v_isSharedCheck_1090_ == 0)
{
lean_object* v_unused_1091_; 
v_unused_1091_ = lean_ctor_get(v_s_1077_, 2);
lean_dec(v_unused_1091_);
v___x_1085_ = v_s_1077_;
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_recoveredErrors_1083_);
lean_inc(v_errorMsg_1082_);
lean_inc(v_cache_1081_);
lean_inc(v_lhsPrec_1080_);
lean_inc(v_stxStack_1079_);
lean_dec(v_s_1077_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1090_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1088_; 
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 2, v_pos_1078_);
v___x_1088_ = v___x_1085_;
goto v_reusejp_1087_;
}
else
{
lean_object* v_reuseFailAlloc_1089_; 
v_reuseFailAlloc_1089_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_stxStack_1079_);
lean_ctor_set(v_reuseFailAlloc_1089_, 1, v_lhsPrec_1080_);
lean_ctor_set(v_reuseFailAlloc_1089_, 2, v_pos_1078_);
lean_ctor_set(v_reuseFailAlloc_1089_, 3, v_cache_1081_);
lean_ctor_set(v_reuseFailAlloc_1089_, 4, v_errorMsg_1082_);
lean_ctor_set(v_reuseFailAlloc_1089_, 5, v_recoveredErrors_1083_);
v___x_1088_ = v_reuseFailAlloc_1089_;
goto v_reusejp_1087_;
}
v_reusejp_1087_:
{
return v___x_1088_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setCache(lean_object* v_s_1092_, lean_object* v_cache_1093_){
_start:
{
lean_object* v_stxStack_1094_; lean_object* v_lhsPrec_1095_; lean_object* v_pos_1096_; lean_object* v_errorMsg_1097_; lean_object* v_recoveredErrors_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
v_stxStack_1094_ = lean_ctor_get(v_s_1092_, 0);
v_lhsPrec_1095_ = lean_ctor_get(v_s_1092_, 1);
v_pos_1096_ = lean_ctor_get(v_s_1092_, 2);
v_errorMsg_1097_ = lean_ctor_get(v_s_1092_, 4);
v_recoveredErrors_1098_ = lean_ctor_get(v_s_1092_, 5);
v_isSharedCheck_1105_ = !lean_is_exclusive(v_s_1092_);
if (v_isSharedCheck_1105_ == 0)
{
lean_object* v_unused_1106_; 
v_unused_1106_ = lean_ctor_get(v_s_1092_, 3);
lean_dec(v_unused_1106_);
v___x_1100_ = v_s_1092_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_recoveredErrors_1098_);
lean_inc(v_errorMsg_1097_);
lean_inc(v_pos_1096_);
lean_inc(v_lhsPrec_1095_);
lean_inc(v_stxStack_1094_);
lean_dec(v_s_1092_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 3, v_cache_1093_);
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_stxStack_1094_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_lhsPrec_1095_);
lean_ctor_set(v_reuseFailAlloc_1104_, 2, v_pos_1096_);
lean_ctor_set(v_reuseFailAlloc_1104_, 3, v_cache_1093_);
lean_ctor_set(v_reuseFailAlloc_1104_, 4, v_errorMsg_1097_);
lean_ctor_set(v_reuseFailAlloc_1104_, 5, v_recoveredErrors_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_pushSyntax(lean_object* v_s_1107_, lean_object* v_n_1108_){
_start:
{
lean_object* v_stxStack_1109_; lean_object* v_lhsPrec_1110_; lean_object* v_pos_1111_; lean_object* v_cache_1112_; lean_object* v_errorMsg_1113_; lean_object* v_recoveredErrors_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1122_; 
v_stxStack_1109_ = lean_ctor_get(v_s_1107_, 0);
v_lhsPrec_1110_ = lean_ctor_get(v_s_1107_, 1);
v_pos_1111_ = lean_ctor_get(v_s_1107_, 2);
v_cache_1112_ = lean_ctor_get(v_s_1107_, 3);
v_errorMsg_1113_ = lean_ctor_get(v_s_1107_, 4);
v_recoveredErrors_1114_ = lean_ctor_get(v_s_1107_, 5);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_s_1107_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1116_ = v_s_1107_;
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_recoveredErrors_1114_);
lean_inc(v_errorMsg_1113_);
lean_inc(v_cache_1112_);
lean_inc(v_pos_1111_);
lean_inc(v_lhsPrec_1110_);
lean_inc(v_stxStack_1109_);
lean_dec(v_s_1107_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1122_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
v___x_1118_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1109_, v_n_1108_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1118_);
v___x_1120_ = v___x_1116_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_lhsPrec_1110_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_pos_1111_);
lean_ctor_set(v_reuseFailAlloc_1121_, 3, v_cache_1112_);
lean_ctor_set(v_reuseFailAlloc_1121_, 4, v_errorMsg_1113_);
lean_ctor_set(v_reuseFailAlloc_1121_, 5, v_recoveredErrors_1114_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_popSyntax(lean_object* v_s_1123_){
_start:
{
lean_object* v_stxStack_1124_; lean_object* v_lhsPrec_1125_; lean_object* v_pos_1126_; lean_object* v_cache_1127_; lean_object* v_errorMsg_1128_; lean_object* v_recoveredErrors_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1137_; 
v_stxStack_1124_ = lean_ctor_get(v_s_1123_, 0);
v_lhsPrec_1125_ = lean_ctor_get(v_s_1123_, 1);
v_pos_1126_ = lean_ctor_get(v_s_1123_, 2);
v_cache_1127_ = lean_ctor_get(v_s_1123_, 3);
v_errorMsg_1128_ = lean_ctor_get(v_s_1123_, 4);
v_recoveredErrors_1129_ = lean_ctor_get(v_s_1123_, 5);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_s_1123_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1131_ = v_s_1123_;
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_recoveredErrors_1129_);
lean_inc(v_errorMsg_1128_);
lean_inc(v_cache_1127_);
lean_inc(v_pos_1126_);
lean_inc(v_lhsPrec_1125_);
lean_inc(v_stxStack_1124_);
lean_dec(v_s_1123_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1137_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
v___x_1133_ = l_Lean_Parser_SyntaxStack_pop(v_stxStack_1124_);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1133_);
v___x_1135_ = v___x_1131_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v_lhsPrec_1125_);
lean_ctor_set(v_reuseFailAlloc_1136_, 2, v_pos_1126_);
lean_ctor_set(v_reuseFailAlloc_1136_, 3, v_cache_1127_);
lean_ctor_set(v_reuseFailAlloc_1136_, 4, v_errorMsg_1128_);
lean_ctor_set(v_reuseFailAlloc_1136_, 5, v_recoveredErrors_1129_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack(lean_object* v_s_1138_, lean_object* v_iniStackSz_1139_){
_start:
{
lean_object* v_stxStack_1140_; lean_object* v_lhsPrec_1141_; lean_object* v_pos_1142_; lean_object* v_cache_1143_; lean_object* v_errorMsg_1144_; lean_object* v_recoveredErrors_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1153_; 
v_stxStack_1140_ = lean_ctor_get(v_s_1138_, 0);
v_lhsPrec_1141_ = lean_ctor_get(v_s_1138_, 1);
v_pos_1142_ = lean_ctor_get(v_s_1138_, 2);
v_cache_1143_ = lean_ctor_get(v_s_1138_, 3);
v_errorMsg_1144_ = lean_ctor_get(v_s_1138_, 4);
v_recoveredErrors_1145_ = lean_ctor_get(v_s_1138_, 5);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_s_1138_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1147_ = v_s_1138_;
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_recoveredErrors_1145_);
lean_inc(v_errorMsg_1144_);
lean_inc(v_cache_1143_);
lean_inc(v_pos_1142_);
lean_inc(v_lhsPrec_1141_);
lean_inc(v_stxStack_1140_);
lean_dec(v_s_1138_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1153_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
v___x_1149_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1140_, v_iniStackSz_1139_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1151_ = v___x_1147_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_lhsPrec_1141_);
lean_ctor_set(v_reuseFailAlloc_1152_, 2, v_pos_1142_);
lean_ctor_set(v_reuseFailAlloc_1152_, 3, v_cache_1143_);
lean_ctor_set(v_reuseFailAlloc_1152_, 4, v_errorMsg_1144_);
lean_ctor_set(v_reuseFailAlloc_1152_, 5, v_recoveredErrors_1145_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_shrinkStack___boxed(lean_object* v_s_1154_, lean_object* v_iniStackSz_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1154_, v_iniStackSz_1155_);
lean_dec(v_iniStackSz_1155_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next(lean_object* v_s_1157_, lean_object* v_c_1158_, lean_object* v_pos_1159_){
_start:
{
lean_object* v_toInputContext_1160_; lean_object* v_stxStack_1161_; lean_object* v_lhsPrec_1162_; lean_object* v_cache_1163_; lean_object* v_errorMsg_1164_; lean_object* v_recoveredErrors_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1174_; 
v_toInputContext_1160_ = lean_ctor_get(v_c_1158_, 0);
v_stxStack_1161_ = lean_ctor_get(v_s_1157_, 0);
v_lhsPrec_1162_ = lean_ctor_get(v_s_1157_, 1);
v_cache_1163_ = lean_ctor_get(v_s_1157_, 3);
v_errorMsg_1164_ = lean_ctor_get(v_s_1157_, 4);
v_recoveredErrors_1165_ = lean_ctor_get(v_s_1157_, 5);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_s_1157_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v_s_1157_, 2);
lean_dec(v_unused_1175_);
v___x_1167_ = v_s_1157_;
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_recoveredErrors_1165_);
lean_inc(v_errorMsg_1164_);
lean_inc(v_cache_1163_);
lean_inc(v_lhsPrec_1162_);
lean_inc(v_stxStack_1161_);
lean_dec(v_s_1157_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1174_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_inputString_1169_; lean_object* v___x_1170_; lean_object* v___x_1172_; 
v_inputString_1169_ = lean_ctor_get(v_toInputContext_1160_, 0);
v___x_1170_ = lean_string_utf8_next(v_inputString_1169_, v_pos_1159_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 2, v___x_1170_);
v___x_1172_ = v___x_1167_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_stxStack_1161_);
lean_ctor_set(v_reuseFailAlloc_1173_, 1, v_lhsPrec_1162_);
lean_ctor_set(v_reuseFailAlloc_1173_, 2, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1173_, 3, v_cache_1163_);
lean_ctor_set(v_reuseFailAlloc_1173_, 4, v_errorMsg_1164_);
lean_ctor_set(v_reuseFailAlloc_1173_, 5, v_recoveredErrors_1165_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next___boxed(lean_object* v_s_1176_, lean_object* v_c_1177_, lean_object* v_pos_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Parser_ParserState_next(v_s_1176_, v_c_1177_, v_pos_1178_);
lean_dec(v_pos_1178_);
lean_dec_ref(v_c_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object* v_s_1180_, lean_object* v_c_1181_, lean_object* v_pos_1182_){
_start:
{
lean_object* v_toInputContext_1183_; lean_object* v_stxStack_1184_; lean_object* v_lhsPrec_1185_; lean_object* v_cache_1186_; lean_object* v_errorMsg_1187_; lean_object* v_recoveredErrors_1188_; lean_object* v___x_1190_; uint8_t v_isShared_1191_; uint8_t v_isSharedCheck_1197_; 
v_toInputContext_1183_ = lean_ctor_get(v_c_1181_, 0);
v_stxStack_1184_ = lean_ctor_get(v_s_1180_, 0);
v_lhsPrec_1185_ = lean_ctor_get(v_s_1180_, 1);
v_cache_1186_ = lean_ctor_get(v_s_1180_, 3);
v_errorMsg_1187_ = lean_ctor_get(v_s_1180_, 4);
v_recoveredErrors_1188_ = lean_ctor_get(v_s_1180_, 5);
v_isSharedCheck_1197_ = !lean_is_exclusive(v_s_1180_);
if (v_isSharedCheck_1197_ == 0)
{
lean_object* v_unused_1198_; 
v_unused_1198_ = lean_ctor_get(v_s_1180_, 2);
lean_dec(v_unused_1198_);
v___x_1190_ = v_s_1180_;
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
else
{
lean_inc(v_recoveredErrors_1188_);
lean_inc(v_errorMsg_1187_);
lean_inc(v_cache_1186_);
lean_inc(v_lhsPrec_1185_);
lean_inc(v_stxStack_1184_);
lean_dec(v_s_1180_);
v___x_1190_ = lean_box(0);
v_isShared_1191_ = v_isSharedCheck_1197_;
goto v_resetjp_1189_;
}
v_resetjp_1189_:
{
lean_object* v_inputString_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v_inputString_1192_ = lean_ctor_get(v_toInputContext_1183_, 0);
v___x_1193_ = lean_string_utf8_next_fast(v_inputString_1192_, v_pos_1182_);
if (v_isShared_1191_ == 0)
{
lean_ctor_set(v___x_1190_, 2, v___x_1193_);
v___x_1195_ = v___x_1190_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_stxStack_1184_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_lhsPrec_1185_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1196_, 3, v_cache_1186_);
lean_ctor_set(v_reuseFailAlloc_1196_, 4, v_errorMsg_1187_);
lean_ctor_set(v_reuseFailAlloc_1196_, 5, v_recoveredErrors_1188_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___redArg___boxed(lean_object* v_s_1199_, lean_object* v_c_1200_, lean_object* v_pos_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1199_, v_c_1200_, v_pos_1201_);
lean_dec(v_pos_1201_);
lean_dec_ref(v_c_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27(lean_object* v_s_1203_, lean_object* v_c_1204_, lean_object* v_pos_1205_, lean_object* v_h_1206_){
_start:
{
lean_object* v___x_1207_; 
v___x_1207_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1203_, v_c_1204_, v_pos_1205_);
return v___x_1207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_next_x27___boxed(lean_object* v_s_1208_, lean_object* v_c_1209_, lean_object* v_pos_1210_, lean_object* v_h_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l_Lean_Parser_ParserState_next_x27(v_s_1208_, v_c_1209_, v_pos_1210_, v_h_1211_);
lean_dec(v_pos_1210_);
lean_dec_ref(v_c_1209_);
return v_res_1212_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(lean_object* v_x_1213_, lean_object* v_x_1214_){
_start:
{
if (lean_obj_tag(v_x_1213_) == 0)
{
if (lean_obj_tag(v_x_1214_) == 0)
{
uint8_t v___x_1215_; 
v___x_1215_ = 1;
return v___x_1215_;
}
else
{
uint8_t v___x_1216_; 
v___x_1216_ = 0;
return v___x_1216_;
}
}
else
{
if (lean_obj_tag(v_x_1214_) == 0)
{
uint8_t v___x_1217_; 
v___x_1217_ = 0;
return v___x_1217_;
}
else
{
lean_object* v_val_1218_; lean_object* v_val_1219_; uint8_t v___x_1220_; 
v_val_1218_ = lean_ctor_get(v_x_1213_, 0);
v_val_1219_ = lean_ctor_get(v_x_1214_, 0);
v___x_1220_ = l_Lean_Parser_instBEqError_beq(v_val_1218_, v_val_1219_);
return v___x_1220_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0___boxed(lean_object* v_x_1221_, lean_object* v_x_1222_){
_start:
{
uint8_t v_res_1223_; lean_object* v_r_1224_; 
v_res_1223_ = l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_x_1221_, v_x_1222_);
lean_dec(v_x_1222_);
lean_dec(v_x_1221_);
v_r_1224_ = lean_box(v_res_1223_);
return v_r_1224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode(lean_object* v_s_1225_, lean_object* v_k_1226_, lean_object* v_iniStackSz_1227_){
_start:
{
lean_object* v_stxStack_1228_; lean_object* v_lhsPrec_1229_; lean_object* v_pos_1230_; lean_object* v_cache_1231_; lean_object* v_errorMsg_1232_; lean_object* v_recoveredErrors_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1254_; 
v_stxStack_1228_ = lean_ctor_get(v_s_1225_, 0);
v_lhsPrec_1229_ = lean_ctor_get(v_s_1225_, 1);
v_pos_1230_ = lean_ctor_get(v_s_1225_, 2);
v_cache_1231_ = lean_ctor_get(v_s_1225_, 3);
v_errorMsg_1232_ = lean_ctor_get(v_s_1225_, 4);
v_recoveredErrors_1233_ = lean_ctor_get(v_s_1225_, 5);
v_isSharedCheck_1254_ = !lean_is_exclusive(v_s_1225_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1235_ = v_s_1225_;
v_isShared_1236_ = v_isSharedCheck_1254_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_recoveredErrors_1233_);
lean_inc(v_errorMsg_1232_);
lean_inc(v_cache_1231_);
lean_inc(v_pos_1230_);
lean_inc(v_lhsPrec_1229_);
lean_inc(v_stxStack_1228_);
lean_dec(v_s_1225_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1254_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1247_; uint8_t v___x_1248_; 
v___x_1247_ = lean_box(0);
v___x_1248_ = l_instBEqOption_beq___at___00Lean_Parser_ParserState_mkNode_spec__0(v_errorMsg_1232_, v___x_1247_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1228_);
v___x_1250_ = lean_nat_dec_eq(v___x_1249_, v_iniStackSz_1227_);
lean_dec(v___x_1249_);
if (v___x_1250_ == 0)
{
goto v___jp_1237_;
}
else
{
lean_object* v___x_1251_; lean_object* v_stack_1252_; lean_object* v___x_1253_; 
lean_del_object(v___x_1235_);
lean_dec(v_k_1226_);
v___x_1251_ = lean_box(0);
v_stack_1252_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_1228_, v___x_1251_);
v___x_1253_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1253_, 0, v_stack_1252_);
lean_ctor_set(v___x_1253_, 1, v_lhsPrec_1229_);
lean_ctor_set(v___x_1253_, 2, v_pos_1230_);
lean_ctor_set(v___x_1253_, 3, v_cache_1231_);
lean_ctor_set(v___x_1253_, 4, v_errorMsg_1232_);
lean_ctor_set(v___x_1253_, 5, v_recoveredErrors_1233_);
return v___x_1253_;
}
}
else
{
goto v___jp_1237_;
}
v___jp_1237_:
{
lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v_newNode_1241_; lean_object* v_stack_1242_; lean_object* v_stack_1243_; lean_object* v___x_1245_; 
v___x_1238_ = lean_box(2);
v___x_1239_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1228_);
v___x_1240_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1228_, v_iniStackSz_1227_, v___x_1239_);
lean_dec(v___x_1239_);
v_newNode_1241_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1241_, 0, v___x_1238_);
lean_ctor_set(v_newNode_1241_, 1, v_k_1226_);
lean_ctor_set(v_newNode_1241_, 2, v___x_1240_);
v_stack_1242_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1228_, v_iniStackSz_1227_);
v_stack_1243_ = l_Lean_Parser_SyntaxStack_push(v_stack_1242_, v_newNode_1241_);
if (v_isShared_1236_ == 0)
{
lean_ctor_set(v___x_1235_, 0, v_stack_1243_);
v___x_1245_ = v___x_1235_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_stack_1243_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v_lhsPrec_1229_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v_pos_1230_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v_cache_1231_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v_errorMsg_1232_);
lean_ctor_set(v_reuseFailAlloc_1246_, 5, v_recoveredErrors_1233_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkNode___boxed(lean_object* v_s_1255_, lean_object* v_k_1256_, lean_object* v_iniStackSz_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Lean_Parser_ParserState_mkNode(v_s_1255_, v_k_1256_, v_iniStackSz_1257_);
lean_dec(v_iniStackSz_1257_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode(lean_object* v_s_1259_, lean_object* v_k_1260_, lean_object* v_iniStackSz_1261_){
_start:
{
lean_object* v_stxStack_1262_; lean_object* v_lhsPrec_1263_; lean_object* v_pos_1264_; lean_object* v_cache_1265_; lean_object* v_errorMsg_1266_; lean_object* v_recoveredErrors_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1282_; 
v_stxStack_1262_ = lean_ctor_get(v_s_1259_, 0);
v_lhsPrec_1263_ = lean_ctor_get(v_s_1259_, 1);
v_pos_1264_ = lean_ctor_get(v_s_1259_, 2);
v_cache_1265_ = lean_ctor_get(v_s_1259_, 3);
v_errorMsg_1266_ = lean_ctor_get(v_s_1259_, 4);
v_recoveredErrors_1267_ = lean_ctor_get(v_s_1259_, 5);
v_isSharedCheck_1282_ = !lean_is_exclusive(v_s_1259_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1269_ = v_s_1259_;
v_isShared_1270_ = v_isSharedCheck_1282_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_recoveredErrors_1267_);
lean_inc(v_errorMsg_1266_);
lean_inc(v_cache_1265_);
lean_inc(v_pos_1264_);
lean_inc(v_lhsPrec_1263_);
lean_inc(v_stxStack_1262_);
lean_dec(v_s_1259_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1282_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v_newNode_1276_; lean_object* v_stack_1277_; lean_object* v_stack_1278_; lean_object* v___x_1280_; 
v___x_1271_ = lean_box(2);
v___x_1272_ = lean_unsigned_to_nat(1u);
v___x_1273_ = lean_nat_sub(v_iniStackSz_1261_, v___x_1272_);
v___x_1274_ = l_Lean_Parser_SyntaxStack_size(v_stxStack_1262_);
v___x_1275_ = l_Lean_Parser_SyntaxStack_extract(v_stxStack_1262_, v___x_1273_, v___x_1274_);
lean_dec(v___x_1274_);
v_newNode_1276_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_newNode_1276_, 0, v___x_1271_);
lean_ctor_set(v_newNode_1276_, 1, v_k_1260_);
lean_ctor_set(v_newNode_1276_, 2, v___x_1275_);
v_stack_1277_ = l_Lean_Parser_SyntaxStack_shrink(v_stxStack_1262_, v___x_1273_);
lean_dec(v___x_1273_);
v_stack_1278_ = l_Lean_Parser_SyntaxStack_push(v_stack_1277_, v_newNode_1276_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v_stack_1278_);
v___x_1280_ = v___x_1269_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_stack_1278_);
lean_ctor_set(v_reuseFailAlloc_1281_, 1, v_lhsPrec_1263_);
lean_ctor_set(v_reuseFailAlloc_1281_, 2, v_pos_1264_);
lean_ctor_set(v_reuseFailAlloc_1281_, 3, v_cache_1265_);
lean_ctor_set(v_reuseFailAlloc_1281_, 4, v_errorMsg_1266_);
lean_ctor_set(v_reuseFailAlloc_1281_, 5, v_recoveredErrors_1267_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkTrailingNode___boxed(lean_object* v_s_1283_, lean_object* v_k_1284_, lean_object* v_iniStackSz_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Parser_ParserState_mkTrailingNode(v_s_1283_, v_k_1284_, v_iniStackSz_1285_);
lean_dec(v_iniStackSz_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_allErrors(lean_object* v_s_1289_){
_start:
{
lean_object* v_errorMsg_1290_; 
v_errorMsg_1290_ = lean_ctor_get(v_s_1289_, 4);
if (lean_obj_tag(v_errorMsg_1290_) == 0)
{
lean_object* v_recoveredErrors_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v_recoveredErrors_1291_ = lean_ctor_get(v_s_1289_, 5);
lean_inc_ref(v_recoveredErrors_1291_);
lean_dec_ref(v_s_1289_);
v___x_1292_ = ((lean_object*)(l_Lean_Parser_ParserState_allErrors___closed__0));
v___x_1293_ = l_Array_append___redArg(v_recoveredErrors_1291_, v___x_1292_);
return v___x_1293_;
}
else
{
lean_object* v_stxStack_1294_; lean_object* v_pos_1295_; lean_object* v_recoveredErrors_1296_; lean_object* v_val_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_inc_ref(v_errorMsg_1290_);
v_stxStack_1294_ = lean_ctor_get(v_s_1289_, 0);
lean_inc_ref(v_stxStack_1294_);
v_pos_1295_ = lean_ctor_get(v_s_1289_, 2);
lean_inc(v_pos_1295_);
v_recoveredErrors_1296_ = lean_ctor_get(v_s_1289_, 5);
lean_inc_ref(v_recoveredErrors_1296_);
lean_dec_ref(v_s_1289_);
v_val_1297_ = lean_ctor_get(v_errorMsg_1290_, 0);
lean_inc(v_val_1297_);
lean_dec_ref_known(v_errorMsg_1290_, 1);
v___x_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_stxStack_1294_);
lean_ctor_set(v___x_1298_, 1, v_val_1297_);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v_pos_1295_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
v___x_1300_ = lean_unsigned_to_nat(1u);
v___x_1301_ = lean_mk_empty_array_with_capacity(v___x_1300_);
v___x_1302_ = lean_array_push(v___x_1301_, v___x_1299_);
v___x_1303_ = l_Array_append___redArg(v_recoveredErrors_1296_, v___x_1302_);
lean_dec_ref(v___x_1302_);
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_setError(lean_object* v_s_1304_, lean_object* v_e_1305_){
_start:
{
lean_object* v_stxStack_1306_; lean_object* v_lhsPrec_1307_; lean_object* v_pos_1308_; lean_object* v_cache_1309_; lean_object* v_recoveredErrors_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1318_; 
v_stxStack_1306_ = lean_ctor_get(v_s_1304_, 0);
v_lhsPrec_1307_ = lean_ctor_get(v_s_1304_, 1);
v_pos_1308_ = lean_ctor_get(v_s_1304_, 2);
v_cache_1309_ = lean_ctor_get(v_s_1304_, 3);
v_recoveredErrors_1310_ = lean_ctor_get(v_s_1304_, 5);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_s_1304_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v_s_1304_, 4);
lean_dec(v_unused_1319_);
v___x_1312_ = v_s_1304_;
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_recoveredErrors_1310_);
lean_inc(v_cache_1309_);
lean_inc(v_pos_1308_);
lean_inc(v_lhsPrec_1307_);
lean_inc(v_stxStack_1306_);
lean_dec(v_s_1304_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1318_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1314_, 0, v_e_1305_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 4, v___x_1314_);
v___x_1316_ = v___x_1312_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_stxStack_1306_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_lhsPrec_1307_);
lean_ctor_set(v_reuseFailAlloc_1317_, 2, v_pos_1308_);
lean_ctor_set(v_reuseFailAlloc_1317_, 3, v_cache_1309_);
lean_ctor_set(v_reuseFailAlloc_1317_, 4, v___x_1314_);
lean_ctor_set(v_reuseFailAlloc_1317_, 5, v_recoveredErrors_1310_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkError(lean_object* v_s_1320_, lean_object* v_msg_1321_){
_start:
{
lean_object* v_stxStack_1322_; lean_object* v_lhsPrec_1323_; lean_object* v_pos_1324_; lean_object* v_cache_1325_; lean_object* v_recoveredErrors_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1340_; 
v_stxStack_1322_ = lean_ctor_get(v_s_1320_, 0);
v_lhsPrec_1323_ = lean_ctor_get(v_s_1320_, 1);
v_pos_1324_ = lean_ctor_get(v_s_1320_, 2);
v_cache_1325_ = lean_ctor_get(v_s_1320_, 3);
v_recoveredErrors_1326_ = lean_ctor_get(v_s_1320_, 5);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_s_1320_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v_s_1320_, 4);
lean_dec(v_unused_1341_);
v___x_1328_ = v_s_1320_;
v_isShared_1329_ = v_isSharedCheck_1340_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_recoveredErrors_1326_);
lean_inc(v_cache_1325_);
lean_inc(v_pos_1324_);
lean_inc(v_lhsPrec_1323_);
lean_inc(v_stxStack_1322_);
lean_dec(v_s_1320_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1340_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1337_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1332_ = lean_box(0);
v___x_1333_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1333_, 0, v_msg_1321_);
lean_ctor_set(v___x_1333_, 1, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1330_);
lean_ctor_set(v___x_1334_, 1, v___x_1331_);
lean_ctor_set(v___x_1334_, 2, v___x_1333_);
v___x_1335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
if (v_isShared_1329_ == 0)
{
lean_ctor_set(v___x_1328_, 4, v___x_1335_);
v___x_1337_ = v___x_1328_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_stxStack_1322_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_lhsPrec_1323_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_pos_1324_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_cache_1325_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v___x_1335_);
lean_ctor_set(v_reuseFailAlloc_1339_, 5, v_recoveredErrors_1326_);
v___x_1337_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1337_, v___x_1330_);
return v___x_1338_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object* v_s_1342_, lean_object* v_msg_1343_, lean_object* v_expected_1344_, uint8_t v_pushMissing_1345_){
_start:
{
lean_object* v_stxStack_1346_; lean_object* v_lhsPrec_1347_; lean_object* v_pos_1348_; lean_object* v_cache_1349_; lean_object* v_recoveredErrors_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1361_; 
v_stxStack_1346_ = lean_ctor_get(v_s_1342_, 0);
v_lhsPrec_1347_ = lean_ctor_get(v_s_1342_, 1);
v_pos_1348_ = lean_ctor_get(v_s_1342_, 2);
v_cache_1349_ = lean_ctor_get(v_s_1342_, 3);
v_recoveredErrors_1350_ = lean_ctor_get(v_s_1342_, 5);
v_isSharedCheck_1361_ = !lean_is_exclusive(v_s_1342_);
if (v_isSharedCheck_1361_ == 0)
{
lean_object* v_unused_1362_; 
v_unused_1362_ = lean_ctor_get(v_s_1342_, 4);
lean_dec(v_unused_1362_);
v___x_1352_ = v_s_1342_;
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_recoveredErrors_1350_);
lean_inc(v_cache_1349_);
lean_inc(v_pos_1348_);
lean_inc(v_lhsPrec_1347_);
lean_inc(v_stxStack_1346_);
lean_dec(v_s_1342_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1361_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v_s_1358_; 
v___x_1354_ = lean_box(0);
v___x_1355_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1354_);
lean_ctor_set(v___x_1355_, 1, v_msg_1343_);
lean_ctor_set(v___x_1355_, 2, v_expected_1344_);
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 4, v___x_1356_);
v_s_1358_ = v___x_1352_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_stxStack_1346_);
lean_ctor_set(v_reuseFailAlloc_1360_, 1, v_lhsPrec_1347_);
lean_ctor_set(v_reuseFailAlloc_1360_, 2, v_pos_1348_);
lean_ctor_set(v_reuseFailAlloc_1360_, 3, v_cache_1349_);
lean_ctor_set(v_reuseFailAlloc_1360_, 4, v___x_1356_);
lean_ctor_set(v_reuseFailAlloc_1360_, 5, v_recoveredErrors_1350_);
v_s_1358_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
if (v_pushMissing_1345_ == 0)
{
return v_s_1358_;
}
else
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1358_, v___x_1354_);
return v___x_1359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedError___boxed(lean_object* v_s_1363_, lean_object* v_msg_1364_, lean_object* v_expected_1365_, lean_object* v_pushMissing_1366_){
_start:
{
uint8_t v_pushMissing_boxed_1367_; lean_object* v_res_1368_; 
v_pushMissing_boxed_1367_ = lean_unbox(v_pushMissing_1366_);
v_res_1368_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1363_, v_msg_1364_, v_expected_1365_, v_pushMissing_boxed_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object* v_s_1370_, lean_object* v_expected_1371_){
_start:
{
lean_object* v___x_1372_; uint8_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = ((lean_object*)(l_Lean_Parser_ParserState_mkEOIError___closed__0));
v___x_1373_ = 1;
v___x_1374_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1370_, v___x_1372_, v_expected_1371_, v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt(lean_object* v_s_1375_, lean_object* v_ex_1376_, lean_object* v_pos_1377_, lean_object* v_initStackSz_x3f_1378_){
_start:
{
lean_object* v_s_1380_; lean_object* v_s_1399_; 
v_s_1399_ = l_Lean_Parser_ParserState_setPos(v_s_1375_, v_pos_1377_);
if (lean_obj_tag(v_initStackSz_x3f_1378_) == 1)
{
lean_object* v_val_1400_; lean_object* v_s_1401_; 
v_val_1400_ = lean_ctor_get(v_initStackSz_x3f_1378_, 0);
v_s_1401_ = l_Lean_Parser_ParserState_shrinkStack(v_s_1399_, v_val_1400_);
v_s_1380_ = v_s_1401_;
goto v___jp_1379_;
}
else
{
v_s_1380_ = v_s_1399_;
goto v___jp_1379_;
}
v___jp_1379_:
{
lean_object* v_stxStack_1381_; lean_object* v_lhsPrec_1382_; lean_object* v_pos_1383_; lean_object* v_cache_1384_; lean_object* v_recoveredErrors_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1397_; 
v_stxStack_1381_ = lean_ctor_get(v_s_1380_, 0);
v_lhsPrec_1382_ = lean_ctor_get(v_s_1380_, 1);
v_pos_1383_ = lean_ctor_get(v_s_1380_, 2);
v_cache_1384_ = lean_ctor_get(v_s_1380_, 3);
v_recoveredErrors_1385_ = lean_ctor_get(v_s_1380_, 5);
v_isSharedCheck_1397_ = !lean_is_exclusive(v_s_1380_);
if (v_isSharedCheck_1397_ == 0)
{
lean_object* v_unused_1398_; 
v_unused_1398_ = lean_ctor_get(v_s_1380_, 4);
lean_dec(v_unused_1398_);
v___x_1387_ = v_s_1380_;
v_isShared_1388_ = v_isSharedCheck_1397_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_recoveredErrors_1385_);
lean_inc(v_cache_1384_);
lean_inc(v_pos_1383_);
lean_inc(v_lhsPrec_1382_);
lean_inc(v_stxStack_1381_);
lean_dec(v_s_1380_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1397_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v_s_1394_; 
v___x_1389_ = lean_box(0);
v___x_1390_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1391_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1389_);
lean_ctor_set(v___x_1391_, 1, v___x_1390_);
lean_ctor_set(v___x_1391_, 2, v_ex_1376_);
v___x_1392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1392_, 0, v___x_1391_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 4, v___x_1392_);
v_s_1394_ = v___x_1387_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1396_; 
v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_stxStack_1381_);
lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_lhsPrec_1382_);
lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_pos_1383_);
lean_ctor_set(v_reuseFailAlloc_1396_, 3, v_cache_1384_);
lean_ctor_set(v_reuseFailAlloc_1396_, 4, v___x_1392_);
lean_ctor_set(v_reuseFailAlloc_1396_, 5, v_recoveredErrors_1385_);
v_s_1394_ = v_reuseFailAlloc_1396_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Lean_Parser_ParserState_pushSyntax(v_s_1394_, v___x_1389_);
return v___x_1395_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorsAt___boxed(lean_object* v_s_1402_, lean_object* v_ex_1403_, lean_object* v_pos_1404_, lean_object* v_initStackSz_x3f_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1402_, v_ex_1403_, v_pos_1404_, v_initStackSz_x3f_1405_);
lean_dec(v_initStackSz_x3f_1405_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object* v_s_1407_, lean_object* v_msg_1408_, lean_object* v_pos_1409_, lean_object* v_initStackSz_x3f_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1411_ = lean_box(0);
v___x_1412_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_msg_1408_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
v___x_1413_ = l_Lean_Parser_ParserState_mkErrorsAt(v_s_1407_, v___x_1412_, v_pos_1409_, v_initStackSz_x3f_1410_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkErrorAt___boxed(lean_object* v_s_1414_, lean_object* v_msg_1415_, lean_object* v_pos_1416_, lean_object* v_initStackSz_x3f_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1414_, v_msg_1415_, v_pos_1416_, v_initStackSz_x3f_1417_);
lean_dec(v_initStackSz_x3f_1417_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(lean_object* v_msg_1419_){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = lean_panic_fn_borrowed(v___x_1420_, v_msg_1419_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1425_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__2));
v___x_1426_ = lean_unsigned_to_nat(14u);
v___x_1427_ = lean_unsigned_to_nat(22u);
v___x_1428_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__1));
v___x_1429_ = ((lean_object*)(l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__0));
v___x_1430_ = l_mkPanicMessageWithDecl(v___x_1429_, v___x_1428_, v___x_1427_, v___x_1426_, v___x_1425_);
return v___x_1430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(lean_object* v_s_1431_, lean_object* v_ex_1432_, lean_object* v_iniPos_1433_){
_start:
{
lean_object* v_stxStack_1434_; lean_object* v_tk_1435_; lean_object* v___y_1437_; lean_object* v___x_1458_; uint8_t v___x_1459_; 
v_stxStack_1434_ = lean_ctor_get(v_s_1431_, 0);
v_tk_1435_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1434_);
v___x_1458_ = lean_unsigned_to_nat(1u);
v___x_1459_ = lean_nat_dec_le(v___x_1458_, v_iniPos_1433_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1460_; 
lean_dec(v_iniPos_1433_);
v___x_1460_ = l_Lean_Syntax_getPos_x3f(v_tk_1435_, v___x_1459_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = lean_obj_once(&l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3, &l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3_once, _init_l_Lean_Parser_ParserState_mkUnexpectedTokenErrors___closed__3);
v___x_1462_ = l_panic___at___00Lean_Parser_ParserState_mkUnexpectedTokenErrors_spec__0(v___x_1461_);
v___y_1437_ = v___x_1462_;
goto v___jp_1436_;
}
else
{
lean_object* v_val_1463_; 
v_val_1463_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_val_1463_);
lean_dec_ref_known(v___x_1460_, 1);
v___y_1437_ = v_val_1463_;
goto v___jp_1436_;
}
}
else
{
v___y_1437_ = v_iniPos_1433_;
goto v___jp_1436_;
}
v___jp_1436_:
{
lean_object* v_s_1438_; lean_object* v_stxStack_1439_; lean_object* v_lhsPrec_1440_; lean_object* v_pos_1441_; lean_object* v_cache_1442_; lean_object* v_recoveredErrors_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1456_; 
v_s_1438_ = l_Lean_Parser_ParserState_setPos(v_s_1431_, v___y_1437_);
v_stxStack_1439_ = lean_ctor_get(v_s_1438_, 0);
v_lhsPrec_1440_ = lean_ctor_get(v_s_1438_, 1);
v_pos_1441_ = lean_ctor_get(v_s_1438_, 2);
v_cache_1442_ = lean_ctor_get(v_s_1438_, 3);
v_recoveredErrors_1443_ = lean_ctor_get(v_s_1438_, 5);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_s_1438_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_s_1438_, 4);
lean_dec(v_unused_1457_);
v___x_1445_ = v_s_1438_;
v_isShared_1446_ = v_isSharedCheck_1456_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_recoveredErrors_1443_);
lean_inc(v_cache_1442_);
lean_inc(v_pos_1441_);
lean_inc(v_lhsPrec_1440_);
lean_inc(v_stxStack_1439_);
lean_dec(v_s_1438_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1456_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v_s_1451_; 
v___x_1447_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1448_, 0, v_tk_1435_);
lean_ctor_set(v___x_1448_, 1, v___x_1447_);
lean_ctor_set(v___x_1448_, 2, v_ex_1432_);
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 4, v___x_1449_);
v_s_1451_ = v___x_1445_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_stxStack_1439_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v_lhsPrec_1440_);
lean_ctor_set(v_reuseFailAlloc_1455_, 2, v_pos_1441_);
lean_ctor_set(v_reuseFailAlloc_1455_, 3, v_cache_1442_);
lean_ctor_set(v_reuseFailAlloc_1455_, 4, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1455_, 5, v_recoveredErrors_1443_);
v_s_1451_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1452_ = l_Lean_Parser_ParserState_popSyntax(v_s_1451_);
v___x_1453_ = lean_box(0);
v___x_1454_ = l_Lean_Parser_ParserState_pushSyntax(v___x_1452_, v___x_1453_);
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedTokenError(lean_object* v_s_1464_, lean_object* v_msg_1465_, lean_object* v_iniPos_1466_){
_start:
{
lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; 
v___x_1467_ = lean_box(0);
v___x_1468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1468_, 0, v_msg_1465_);
lean_ctor_set(v___x_1468_, 1, v___x_1467_);
v___x_1469_ = l_Lean_Parser_ParserState_mkUnexpectedTokenErrors(v_s_1464_, v___x_1468_, v_iniPos_1466_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object* v_s_1470_, lean_object* v_msg_1471_, lean_object* v_pos_1472_){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; lean_object* v___x_1476_; 
v___x_1473_ = l_Lean_Parser_ParserState_setPos(v_s_1470_, v_pos_1472_);
v___x_1474_ = lean_box(0);
v___x_1475_ = 1;
v___x_1476_ = l_Lean_Parser_ParserState_mkUnexpectedError(v___x_1473_, v_msg_1471_, v___x_1474_, v___x_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(lean_object* v_ctx_1478_, lean_object* v_as_1479_, size_t v_sz_1480_, size_t v_i_1481_, lean_object* v_b_1482_){
_start:
{
uint8_t v___x_1483_; 
v___x_1483_ = lean_usize_dec_lt(v_i_1481_, v_sz_1480_);
if (v___x_1483_ == 0)
{
lean_dec_ref(v_ctx_1478_);
return v_b_1482_;
}
else
{
lean_object* v_a_1484_; lean_object* v_snd_1485_; lean_object* v_fst_1486_; lean_object* v_snd_1487_; lean_object* v_errStr_1489_; lean_object* v_errStr_1500_; uint8_t v___x_1501_; 
v_a_1484_ = lean_array_uget_borrowed(v_as_1479_, v_i_1481_);
v_snd_1485_ = lean_ctor_get(v_a_1484_, 1);
v_fst_1486_ = lean_ctor_get(v_a_1484_, 0);
v_snd_1487_ = lean_ctor_get(v_snd_1485_, 1);
v_errStr_1500_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1501_ = lean_string_dec_eq(v_b_1482_, v_errStr_1500_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___closed__0));
v___x_1503_ = lean_string_append(v_b_1482_, v___x_1502_);
v_errStr_1489_ = v___x_1503_;
goto v___jp_1488_;
}
else
{
v_errStr_1489_ = v_b_1482_;
goto v___jp_1488_;
}
v___jp_1488_:
{
lean_object* v_fileName_1490_; lean_object* v_fileMap_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; size_t v___x_1497_; size_t v___x_1498_; 
v_fileName_1490_ = lean_ctor_get(v_ctx_1478_, 1);
v_fileMap_1491_ = lean_ctor_get(v_ctx_1478_, 2);
lean_inc_ref(v_fileMap_1491_);
v___x_1492_ = l_Lean_FileMap_toPosition(v_fileMap_1491_, v_fst_1486_);
lean_inc(v_snd_1487_);
v___x_1493_ = l_Lean_Parser_Error_toString(v_snd_1487_);
v___x_1494_ = lean_box(0);
lean_inc_ref(v_fileName_1490_);
v___x_1495_ = l_Lean_mkErrorStringWithPos(v_fileName_1490_, v___x_1492_, v___x_1493_, v___x_1494_, v___x_1494_, v___x_1494_);
lean_dec_ref(v___x_1493_);
v___x_1496_ = lean_string_append(v_errStr_1489_, v___x_1495_);
lean_dec_ref(v___x_1495_);
v___x_1497_ = ((size_t)1ULL);
v___x_1498_ = lean_usize_add(v_i_1481_, v___x_1497_);
v_i_1481_ = v___x_1498_;
v_b_1482_ = v___x_1496_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0___boxed(lean_object* v_ctx_1504_, lean_object* v_as_1505_, lean_object* v_sz_1506_, lean_object* v_i_1507_, lean_object* v_b_1508_){
_start:
{
size_t v_sz_boxed_1509_; size_t v_i_boxed_1510_; lean_object* v_res_1511_; 
v_sz_boxed_1509_ = lean_unbox_usize(v_sz_1506_);
lean_dec(v_sz_1506_);
v_i_boxed_1510_ = lean_unbox_usize(v_i_1507_);
lean_dec(v_i_1507_);
v_res_1511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1504_, v_as_1505_, v_sz_boxed_1509_, v_i_boxed_1510_, v_b_1508_);
lean_dec_ref(v_as_1505_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserState_toErrorMsg(lean_object* v_ctx_1512_, lean_object* v_s_1513_){
_start:
{
lean_object* v_errStr_1514_; lean_object* v___x_1515_; size_t v_sz_1516_; size_t v___x_1517_; lean_object* v___x_1518_; 
v_errStr_1514_ = ((lean_object*)(l_Lean_Parser_instInhabitedInputContext___closed__0));
v___x_1515_ = l_Lean_Parser_ParserState_allErrors(v_s_1513_);
v_sz_1516_ = lean_array_size(v___x_1515_);
v___x_1517_ = ((size_t)0ULL);
v___x_1518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Parser_ParserState_toErrorMsg_spec__0(v_ctx_1512_, v___x_1515_, v_sz_1516_, v___x_1517_, v_errStr_1514_);
lean_dec_ref(v___x_1515_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0(lean_object* v_x_1519_, lean_object* v_s_1520_){
_start:
{
lean_inc_ref(v_s_1520_);
return v_s_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserFn___lam__0___boxed(lean_object* v_x_1521_, lean_object* v_s_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Lean_Parser_instInhabitedParserFn___lam__0(v_x_1521_, v_s_1522_);
lean_dec_ref(v_s_1522_);
lean_dec_ref(v_x_1521_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___impl(lean_object* v_x_1526_){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_obj_tag_nat(v_x_1526_);
return v___x_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorIdx___impl___boxed(lean_object* v_x_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l_Lean_Parser_FirstTokens_ctorIdx___impl(v_x_1528_);
lean_dec(v_x_1528_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___redArg(lean_object* v_t_1530_, lean_object* v_k_1531_){
_start:
{
switch(lean_obj_tag(v_t_1530_))
{
case 2:
{
lean_object* v_a_1532_; lean_object* v___x_1533_; 
v_a_1532_ = lean_ctor_get(v_t_1530_, 0);
lean_inc(v_a_1532_);
lean_dec_ref_known(v_t_1530_, 1);
v___x_1533_ = lean_apply_1(v_k_1531_, v_a_1532_);
return v___x_1533_;
}
case 3:
{
lean_object* v_a_1534_; lean_object* v___x_1535_; 
v_a_1534_ = lean_ctor_get(v_t_1530_, 0);
lean_inc(v_a_1534_);
lean_dec_ref_known(v_t_1530_, 1);
v___x_1535_ = lean_apply_1(v_k_1531_, v_a_1534_);
return v___x_1535_;
}
default: 
{
lean_dec(v_t_1530_);
return v_k_1531_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim(lean_object* v_motive_1536_, lean_object* v_ctorIdx_1537_, lean_object* v_t_1538_, lean_object* v_h_1539_, lean_object* v_k_1540_){
_start:
{
lean_object* v___x_1541_; 
v___x_1541_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1538_, v_k_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_ctorElim___boxed(lean_object* v_motive_1542_, lean_object* v_ctorIdx_1543_, lean_object* v_t_1544_, lean_object* v_h_1545_, lean_object* v_k_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_Parser_FirstTokens_ctorElim(v_motive_1542_, v_ctorIdx_1543_, v_t_1544_, v_h_1545_, v_k_1546_);
lean_dec(v_ctorIdx_1543_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim___redArg(lean_object* v_t_1548_, lean_object* v_epsilon_1549_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1548_, v_epsilon_1549_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_epsilon_elim(lean_object* v_motive_1551_, lean_object* v_t_1552_, lean_object* v_h_1553_, lean_object* v_epsilon_1554_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1552_, v_epsilon_1554_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim___redArg(lean_object* v_t_1556_, lean_object* v_unknown_1557_){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1556_, v_unknown_1557_);
return v___x_1558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_unknown_elim(lean_object* v_motive_1559_, lean_object* v_t_1560_, lean_object* v_h_1561_, lean_object* v_unknown_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1560_, v_unknown_1562_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim___redArg(lean_object* v_t_1564_, lean_object* v_tokens_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1564_, v_tokens_1565_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_tokens_elim(lean_object* v_motive_1567_, lean_object* v_t_1568_, lean_object* v_h_1569_, lean_object* v_tokens_1570_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1568_, v_tokens_1570_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim___redArg(lean_object* v_t_1572_, lean_object* v_optTokens_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1572_, v_optTokens_1573_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_optTokens_elim(lean_object* v_motive_1575_, lean_object* v_t_1576_, lean_object* v_h_1577_, lean_object* v_optTokens_1578_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_Parser_FirstTokens_ctorElim___redArg(v_t_1576_, v_optTokens_1578_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens_default(void){
_start:
{
lean_object* v___x_1580_; 
v___x_1580_ = lean_box(0);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_Parser_instInhabitedFirstTokens(void){
_start:
{
lean_object* v___x_1581_; 
v___x_1581_ = lean_box(0);
return v___x_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_seq(lean_object* v_x_1582_, lean_object* v_x_1583_){
_start:
{
switch(lean_obj_tag(v_x_1582_))
{
case 0:
{
return v_x_1583_;
}
case 3:
{
switch(lean_obj_tag(v_x_1583_))
{
case 3:
{
lean_object* v_a_1584_; lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1593_; 
v_a_1584_ = lean_ctor_get(v_x_1582_, 0);
lean_inc(v_a_1584_);
lean_dec_ref_known(v_x_1582_, 1);
v_a_1585_ = lean_ctor_get(v_x_1583_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_x_1583_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1587_ = v_x_1583_;
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v_x_1583_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1593_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1589_ = l_List_appendTR___redArg(v_a_1584_, v_a_1585_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1589_);
v___x_1591_ = v___x_1587_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1589_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
case 2:
{
lean_object* v_a_1594_; lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1603_; 
v_a_1594_ = lean_ctor_get(v_x_1582_, 0);
lean_inc(v_a_1594_);
lean_dec_ref_known(v_x_1582_, 1);
v_a_1595_ = lean_ctor_get(v_x_1583_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_x_1583_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1597_ = v_x_1583_;
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v_x_1583_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v___x_1599_; lean_object* v___x_1601_; 
v___x_1599_ = l_List_appendTR___redArg(v_a_1594_, v_a_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v___x_1599_);
v___x_1601_ = v___x_1597_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
case 1:
{
lean_dec_ref_known(v_x_1582_, 1);
return v_x_1583_;
}
default: 
{
lean_dec(v_x_1583_);
return v_x_1582_;
}
}
}
default: 
{
lean_dec(v_x_1583_);
return v_x_1582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toOptional(lean_object* v_x_1604_){
_start:
{
if (lean_obj_tag(v_x_1604_) == 2)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1612_; 
v_a_1605_ = lean_ctor_get(v_x_1604_, 0);
v_isSharedCheck_1612_ = !lean_is_exclusive(v_x_1604_);
if (v_isSharedCheck_1612_ == 0)
{
v___x_1607_ = v_x_1604_;
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v_x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1612_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1610_; 
if (v_isShared_1608_ == 0)
{
lean_ctor_set_tag(v___x_1607_, 3);
v___x_1610_ = v___x_1607_;
goto v_reusejp_1609_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_a_1605_);
v___x_1610_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1609_;
}
v_reusejp_1609_:
{
return v___x_1610_;
}
}
}
else
{
return v_x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_merge(lean_object* v_x_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v_s_u2081_1616_; lean_object* v_s_u2082_1617_; 
switch(lean_obj_tag(v_x_1613_))
{
case 0:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1614_);
return v___x_1620_;
}
case 2:
{
switch(lean_obj_tag(v_x_1614_))
{
case 0:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1613_);
return v___x_1621_;
}
case 2:
{
lean_object* v_a_1622_; lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1631_; 
v_a_1622_ = lean_ctor_get(v_x_1613_, 0);
lean_inc(v_a_1622_);
lean_dec_ref_known(v_x_1613_, 1);
v_a_1623_ = lean_ctor_get(v_x_1614_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v_x_1614_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1625_ = v_x_1614_;
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v_x_1614_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1631_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1627_; lean_object* v___x_1629_; 
v___x_1627_ = l_List_appendTR___redArg(v_a_1622_, v_a_1623_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v___x_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
case 3:
{
lean_object* v_a_1632_; lean_object* v_a_1633_; 
v_a_1632_ = lean_ctor_get(v_x_1613_, 0);
lean_inc(v_a_1632_);
lean_dec_ref_known(v_x_1613_, 1);
v_a_1633_ = lean_ctor_get(v_x_1614_, 0);
lean_inc(v_a_1633_);
lean_dec_ref_known(v_x_1614_, 1);
v_s_u2081_1616_ = v_a_1632_;
v_s_u2082_1617_ = v_a_1633_;
goto v___jp_1615_;
}
default: 
{
lean_object* v___x_1634_; 
lean_dec_ref_known(v_x_1613_, 1);
lean_dec(v_x_1614_);
v___x_1634_ = lean_box(1);
return v___x_1634_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_1614_))
{
case 0:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1613_);
return v___x_1635_;
}
case 3:
{
lean_object* v_a_1636_; lean_object* v_a_1637_; 
v_a_1636_ = lean_ctor_get(v_x_1613_, 0);
lean_inc(v_a_1636_);
lean_dec_ref_known(v_x_1613_, 1);
v_a_1637_ = lean_ctor_get(v_x_1614_, 0);
lean_inc(v_a_1637_);
lean_dec_ref_known(v_x_1614_, 1);
v_s_u2081_1616_ = v_a_1636_;
v_s_u2082_1617_ = v_a_1637_;
goto v___jp_1615_;
}
case 2:
{
lean_object* v_a_1638_; lean_object* v_a_1639_; 
v_a_1638_ = lean_ctor_get(v_x_1613_, 0);
lean_inc(v_a_1638_);
lean_dec_ref_known(v_x_1613_, 1);
v_a_1639_ = lean_ctor_get(v_x_1614_, 0);
lean_inc(v_a_1639_);
lean_dec_ref_known(v_x_1614_, 1);
v_s_u2081_1616_ = v_a_1638_;
v_s_u2082_1617_ = v_a_1639_;
goto v___jp_1615_;
}
default: 
{
lean_object* v___x_1640_; 
lean_dec_ref_known(v_x_1613_, 1);
lean_dec(v_x_1614_);
v___x_1640_ = lean_box(1);
return v___x_1640_;
}
}
}
default: 
{
if (lean_obj_tag(v_x_1614_) == 0)
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Parser_FirstTokens_toOptional(v_x_1613_);
return v___x_1641_;
}
else
{
lean_object* v___x_1642_; 
lean_dec(v_x_1614_);
lean_dec(v_x_1613_);
v___x_1642_ = lean_box(1);
return v___x_1642_;
}
}
}
v___jp_1615_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = l_List_appendTR___redArg(v_s_u2081_1616_, v_s_u2082_1617_);
v___x_1619_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1618_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
if (lean_obj_tag(v_x_1644_) == 0)
{
return v_x_1643_;
}
else
{
lean_object* v_head_1645_; lean_object* v_tail_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v_head_1645_ = lean_ctor_get(v_x_1644_, 0);
v_tail_1646_ = lean_ctor_get(v_x_1644_, 1);
v___x_1647_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_Error_expectedToString___closed__1));
v___x_1648_ = lean_string_append(v_x_1643_, v___x_1647_);
v___x_1649_ = lean_string_append(v___x_1648_, v_head_1645_);
v_x_1643_ = v___x_1649_;
v_x_1644_ = v_tail_1646_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0___boxed(lean_object* v_x_1651_, lean_object* v_x_1652_){
_start:
{
lean_object* v_res_1653_; 
v_res_1653_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v_x_1651_, v_x_1652_);
lean_dec(v_x_1652_);
return v_res_1653_;
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(lean_object* v_x_1657_){
_start:
{
if (lean_obj_tag(v_x_1657_) == 0)
{
lean_object* v___x_1658_; 
v___x_1658_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__0));
return v___x_1658_;
}
else
{
lean_object* v_tail_1659_; 
v_tail_1659_ = lean_ctor_get(v_x_1657_, 1);
if (lean_obj_tag(v_tail_1659_) == 0)
{
lean_object* v_head_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; 
v_head_1660_ = lean_ctor_get(v_x_1657_, 0);
v___x_1661_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1662_ = lean_string_append(v___x_1661_, v_head_1660_);
v___x_1663_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__2));
v___x_1664_ = lean_string_append(v___x_1662_, v___x_1663_);
return v___x_1664_;
}
else
{
lean_object* v_head_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint32_t v___x_1669_; lean_object* v___x_1670_; 
v_head_1665_ = lean_ctor_get(v_x_1657_, 0);
v___x_1666_ = ((lean_object*)(l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___closed__1));
v___x_1667_ = lean_string_append(v___x_1666_, v_head_1665_);
v___x_1668_ = l_List_foldl___at___00List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0_spec__0(v___x_1667_, v_tail_1659_);
v___x_1669_ = 93;
v___x_1670_ = lean_string_push(v___x_1668_, v___x_1669_);
return v___x_1670_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0___boxed(lean_object* v_x_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_x_1671_);
lean_dec(v_x_1671_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr(lean_object* v_x_1676_){
_start:
{
switch(lean_obj_tag(v_x_1676_))
{
case 0:
{
lean_object* v___x_1677_; 
v___x_1677_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__0));
return v___x_1677_;
}
case 1:
{
lean_object* v___x_1678_; 
v___x_1678_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__1));
return v___x_1678_;
}
case 2:
{
lean_object* v_a_1679_; lean_object* v___x_1680_; 
v_a_1679_ = lean_ctor_get(v_x_1676_, 0);
v___x_1680_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1679_);
return v___x_1680_;
}
default: 
{
lean_object* v_a_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v_a_1681_ = lean_ctor_get(v_x_1676_, 0);
v___x_1682_ = ((lean_object*)(l_Lean_Parser_FirstTokens_toStr___closed__2));
v___x_1683_ = l_List_toString___at___00Lean_Parser_FirstTokens_toStr_spec__0(v_a_1681_);
v___x_1684_ = lean_string_append(v___x_1682_, v___x_1683_);
lean_dec_ref(v___x_1683_);
return v___x_1684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_FirstTokens_toStr___boxed(lean_object* v_x_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean_Parser_FirstTokens_toStr(v_x_1685_);
lean_dec(v_x_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0(lean_object* v___y_1689_){
_start:
{
lean_inc(v___y_1689_);
return v___y_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__0___boxed(lean_object* v___y_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__0(v___y_1690_);
lean_dec(v___y_1690_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1(lean_object* v___y_1692_){
_start:
{
lean_inc_ref(v___y_1692_);
return v___y_1692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_instInhabitedParserInfo_default___lam__1___boxed(lean_object* v___y_1693_){
_start:
{
lean_object* v_res_1694_; 
v_res_1694_ = l_Lean_Parser_instInhabitedParserInfo_default___lam__1(v___y_1693_);
lean_dec_ref(v___y_1693_);
return v_res_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withFn(lean_object* v_f_1708_, lean_object* v_p_1709_){
_start:
{
lean_object* v_info_1710_; lean_object* v_fn_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1719_; 
v_info_1710_ = lean_ctor_get(v_p_1709_, 0);
v_fn_1711_ = lean_ctor_get(v_p_1709_, 1);
v_isSharedCheck_1719_ = !lean_is_exclusive(v_p_1709_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1713_ = v_p_1709_;
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_fn_1711_);
lean_inc(v_info_1710_);
lean_dec(v_p_1709_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1719_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v___x_1715_; lean_object* v___x_1717_; 
v___x_1715_ = lean_apply_1(v_f_1708_, v_fn_1711_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 1, v___x_1715_);
v___x_1717_ = v___x_1713_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_info_1710_);
lean_ctor_set(v_reuseFailAlloc_1718_, 1, v___x_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContextFn(lean_object* v_f_1720_, lean_object* v_p_1721_, lean_object* v_c_1722_, lean_object* v_s_1723_){
_start:
{
lean_object* v_toInputContext_1724_; lean_object* v_toParserModuleContext_1725_; lean_object* v_toCacheableParserContext_1726_; lean_object* v_tokens_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1736_; 
v_toInputContext_1724_ = lean_ctor_get(v_c_1722_, 0);
v_toParserModuleContext_1725_ = lean_ctor_get(v_c_1722_, 1);
v_toCacheableParserContext_1726_ = lean_ctor_get(v_c_1722_, 2);
v_tokens_1727_ = lean_ctor_get(v_c_1722_, 3);
v_isSharedCheck_1736_ = !lean_is_exclusive(v_c_1722_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1729_ = v_c_1722_;
v_isShared_1730_ = v_isSharedCheck_1736_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_tokens_1727_);
lean_inc(v_toCacheableParserContext_1726_);
lean_inc(v_toParserModuleContext_1725_);
lean_inc(v_toInputContext_1724_);
lean_dec(v_c_1722_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1736_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1731_; lean_object* v___x_1733_; 
v___x_1731_ = lean_apply_1(v_f_1720_, v_toCacheableParserContext_1726_);
if (v_isShared_1730_ == 0)
{
lean_ctor_set(v___x_1729_, 2, v___x_1731_);
v___x_1733_ = v___x_1729_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_toInputContext_1724_);
lean_ctor_set(v_reuseFailAlloc_1735_, 1, v_toParserModuleContext_1725_);
lean_ctor_set(v_reuseFailAlloc_1735_, 2, v___x_1731_);
lean_ctor_set(v_reuseFailAlloc_1735_, 3, v_tokens_1727_);
v___x_1733_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
lean_object* v___x_1734_; 
v___x_1734_ = lean_apply_2(v_p_1721_, v___x_1733_, v_s_1723_);
return v___x_1734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptCacheableContext(lean_object* v_f_1737_, lean_object* v_p_1738_){
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
v___x_1744_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptCacheableContextFn), 4, 2);
lean_closure_set(v___x_1744_, 0, v_f_1737_);
lean_closure_set(v___x_1744_, 1, v_fn_1740_);
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
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(lean_object* v_drop_1749_, lean_object* v_p_1750_, lean_object* v_c_1751_, lean_object* v_s_1752_){
_start:
{
lean_object* v_stxStack_1753_; lean_object* v_lhsPrec_1754_; lean_object* v_pos_1755_; lean_object* v_cache_1756_; lean_object* v_errorMsg_1757_; lean_object* v_recoveredErrors_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1797_; 
v_stxStack_1753_ = lean_ctor_get(v_s_1752_, 0);
v_lhsPrec_1754_ = lean_ctor_get(v_s_1752_, 1);
v_pos_1755_ = lean_ctor_get(v_s_1752_, 2);
v_cache_1756_ = lean_ctor_get(v_s_1752_, 3);
v_errorMsg_1757_ = lean_ctor_get(v_s_1752_, 4);
v_recoveredErrors_1758_ = lean_ctor_get(v_s_1752_, 5);
v_isSharedCheck_1797_ = !lean_is_exclusive(v_s_1752_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1760_ = v_s_1752_;
v_isShared_1761_ = v_isSharedCheck_1797_;
goto v_resetjp_1759_;
}
else
{
lean_inc(v_recoveredErrors_1758_);
lean_inc(v_errorMsg_1757_);
lean_inc(v_cache_1756_);
lean_inc(v_pos_1755_);
lean_inc(v_lhsPrec_1754_);
lean_inc(v_stxStack_1753_);
lean_dec(v_s_1752_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1797_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v_raw_1762_; lean_object* v_drop_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1796_; 
v_raw_1762_ = lean_ctor_get(v_stxStack_1753_, 0);
v_drop_1763_ = lean_ctor_get(v_stxStack_1753_, 1);
v_isSharedCheck_1796_ = !lean_is_exclusive(v_stxStack_1753_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1765_ = v_stxStack_1753_;
v_isShared_1766_ = v_isSharedCheck_1796_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_drop_1763_);
lean_inc(v_raw_1762_);
lean_dec(v_stxStack_1753_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1796_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 1, v_drop_1749_);
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_raw_1762_);
lean_ctor_set(v_reuseFailAlloc_1795_, 1, v_drop_1749_);
v___x_1768_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
lean_object* v___x_1770_; 
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1768_);
v___x_1770_ = v___x_1760_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v___x_1768_);
lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_lhsPrec_1754_);
lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_pos_1755_);
lean_ctor_set(v_reuseFailAlloc_1794_, 3, v_cache_1756_);
lean_ctor_set(v_reuseFailAlloc_1794_, 4, v_errorMsg_1757_);
lean_ctor_set(v_reuseFailAlloc_1794_, 5, v_recoveredErrors_1758_);
v___x_1770_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
lean_object* v_s_1771_; lean_object* v_stxStack_1772_; lean_object* v_lhsPrec_1773_; lean_object* v_pos_1774_; lean_object* v_cache_1775_; lean_object* v_errorMsg_1776_; lean_object* v_recoveredErrors_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1793_; 
v_s_1771_ = lean_apply_2(v_p_1750_, v_c_1751_, v___x_1770_);
v_stxStack_1772_ = lean_ctor_get(v_s_1771_, 0);
v_lhsPrec_1773_ = lean_ctor_get(v_s_1771_, 1);
v_pos_1774_ = lean_ctor_get(v_s_1771_, 2);
v_cache_1775_ = lean_ctor_get(v_s_1771_, 3);
v_errorMsg_1776_ = lean_ctor_get(v_s_1771_, 4);
v_recoveredErrors_1777_ = lean_ctor_get(v_s_1771_, 5);
v_isSharedCheck_1793_ = !lean_is_exclusive(v_s_1771_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1779_ = v_s_1771_;
v_isShared_1780_ = v_isSharedCheck_1793_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_recoveredErrors_1777_);
lean_inc(v_errorMsg_1776_);
lean_inc(v_cache_1775_);
lean_inc(v_pos_1774_);
lean_inc(v_lhsPrec_1773_);
lean_inc(v_stxStack_1772_);
lean_dec(v_s_1771_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1793_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v_raw_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1791_; 
v_raw_1781_ = lean_ctor_get(v_stxStack_1772_, 0);
v_isSharedCheck_1791_ = !lean_is_exclusive(v_stxStack_1772_);
if (v_isSharedCheck_1791_ == 0)
{
lean_object* v_unused_1792_; 
v_unused_1792_ = lean_ctor_get(v_stxStack_1772_, 1);
lean_dec(v_unused_1792_);
v___x_1783_ = v_stxStack_1772_;
v_isShared_1784_ = v_isSharedCheck_1791_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_raw_1781_);
lean_dec(v_stxStack_1772_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1791_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
lean_ctor_set(v___x_1783_, 1, v_drop_1763_);
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1790_; 
v_reuseFailAlloc_1790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_raw_1781_);
lean_ctor_set(v_reuseFailAlloc_1790_, 1, v_drop_1763_);
v___x_1786_ = v_reuseFailAlloc_1790_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
lean_object* v___x_1788_; 
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v___x_1786_);
v___x_1788_ = v___x_1779_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v___x_1786_);
lean_ctor_set(v_reuseFailAlloc_1789_, 1, v_lhsPrec_1773_);
lean_ctor_set(v_reuseFailAlloc_1789_, 2, v_pos_1774_);
lean_ctor_set(v_reuseFailAlloc_1789_, 3, v_cache_1775_);
lean_ctor_set(v_reuseFailAlloc_1789_, 4, v_errorMsg_1776_);
lean_ctor_set(v_reuseFailAlloc_1789_, 5, v_recoveredErrors_1777_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn___lam__0(lean_object* v_p_1798_, lean_object* v_c_1799_, lean_object* v_s_1800_){
_start:
{
lean_object* v_cache_1801_; lean_object* v_stxStack_1802_; lean_object* v_lhsPrec_1803_; lean_object* v_pos_1804_; lean_object* v_errorMsg_1805_; lean_object* v_recoveredErrors_1806_; lean_object* v___x_1808_; uint8_t v_isShared_1809_; uint8_t v_isSharedCheck_1846_; 
v_cache_1801_ = lean_ctor_get(v_s_1800_, 3);
v_stxStack_1802_ = lean_ctor_get(v_s_1800_, 0);
v_lhsPrec_1803_ = lean_ctor_get(v_s_1800_, 1);
v_pos_1804_ = lean_ctor_get(v_s_1800_, 2);
v_errorMsg_1805_ = lean_ctor_get(v_s_1800_, 4);
v_recoveredErrors_1806_ = lean_ctor_get(v_s_1800_, 5);
v_isSharedCheck_1846_ = !lean_is_exclusive(v_s_1800_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1808_ = v_s_1800_;
v_isShared_1809_ = v_isSharedCheck_1846_;
goto v_resetjp_1807_;
}
else
{
lean_inc(v_recoveredErrors_1806_);
lean_inc(v_errorMsg_1805_);
lean_inc(v_cache_1801_);
lean_inc(v_pos_1804_);
lean_inc(v_lhsPrec_1803_);
lean_inc(v_stxStack_1802_);
lean_dec(v_s_1800_);
v___x_1808_ = lean_box(0);
v_isShared_1809_ = v_isSharedCheck_1846_;
goto v_resetjp_1807_;
}
v_resetjp_1807_:
{
lean_object* v_tokenCache_1810_; lean_object* v_parserCache_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1845_; 
v_tokenCache_1810_ = lean_ctor_get(v_cache_1801_, 0);
v_parserCache_1811_ = lean_ctor_get(v_cache_1801_, 1);
v_isSharedCheck_1845_ = !lean_is_exclusive(v_cache_1801_);
if (v_isSharedCheck_1845_ == 0)
{
v___x_1813_ = v_cache_1801_;
v_isShared_1814_ = v_isSharedCheck_1845_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_parserCache_1811_);
lean_inc(v_tokenCache_1810_);
lean_dec(v_cache_1801_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1845_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1815_; lean_object* v___x_1817_; 
v___x_1815_ = lean_obj_once(&l_Lean_Parser_initCacheForInput___closed__1, &l_Lean_Parser_initCacheForInput___closed__1_once, _init_l_Lean_Parser_initCacheForInput___closed__1);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v___x_1815_);
v___x_1817_ = v___x_1813_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v_tokenCache_1810_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v___x_1815_);
v___x_1817_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
lean_object* v___x_1819_; 
if (v_isShared_1809_ == 0)
{
lean_ctor_set(v___x_1808_, 3, v___x_1817_);
v___x_1819_ = v___x_1808_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_stxStack_1802_);
lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_lhsPrec_1803_);
lean_ctor_set(v_reuseFailAlloc_1843_, 2, v_pos_1804_);
lean_ctor_set(v_reuseFailAlloc_1843_, 3, v___x_1817_);
lean_ctor_set(v_reuseFailAlloc_1843_, 4, v_errorMsg_1805_);
lean_ctor_set(v_reuseFailAlloc_1843_, 5, v_recoveredErrors_1806_);
v___x_1819_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v_s_x27_1820_; lean_object* v_cache_1821_; lean_object* v_stxStack_1822_; lean_object* v_lhsPrec_1823_; lean_object* v_pos_1824_; lean_object* v_errorMsg_1825_; lean_object* v_recoveredErrors_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1842_; 
v_s_x27_1820_ = lean_apply_2(v_p_1798_, v_c_1799_, v___x_1819_);
v_cache_1821_ = lean_ctor_get(v_s_x27_1820_, 3);
v_stxStack_1822_ = lean_ctor_get(v_s_x27_1820_, 0);
v_lhsPrec_1823_ = lean_ctor_get(v_s_x27_1820_, 1);
v_pos_1824_ = lean_ctor_get(v_s_x27_1820_, 2);
v_errorMsg_1825_ = lean_ctor_get(v_s_x27_1820_, 4);
v_recoveredErrors_1826_ = lean_ctor_get(v_s_x27_1820_, 5);
v_isSharedCheck_1842_ = !lean_is_exclusive(v_s_x27_1820_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1828_ = v_s_x27_1820_;
v_isShared_1829_ = v_isSharedCheck_1842_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_recoveredErrors_1826_);
lean_inc(v_errorMsg_1825_);
lean_inc(v_cache_1821_);
lean_inc(v_pos_1824_);
lean_inc(v_lhsPrec_1823_);
lean_inc(v_stxStack_1822_);
lean_dec(v_s_x27_1820_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1842_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
lean_object* v_tokenCache_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1840_; 
v_tokenCache_1830_ = lean_ctor_get(v_cache_1821_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v_cache_1821_);
if (v_isSharedCheck_1840_ == 0)
{
lean_object* v_unused_1841_; 
v_unused_1841_ = lean_ctor_get(v_cache_1821_, 1);
lean_dec(v_unused_1841_);
v___x_1832_ = v_cache_1821_;
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_tokenCache_1830_);
lean_dec(v_cache_1821_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1840_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
lean_ctor_set(v___x_1832_, 1, v_parserCache_1811_);
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_tokenCache_1830_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v_parserCache_1811_);
v___x_1835_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
lean_object* v___x_1837_; 
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 3, v___x_1835_);
v___x_1837_ = v___x_1828_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_stxStack_1822_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v_lhsPrec_1823_);
lean_ctor_set(v_reuseFailAlloc_1838_, 2, v_pos_1824_);
lean_ctor_set(v_reuseFailAlloc_1838_, 3, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1838_, 4, v_errorMsg_1825_);
lean_ctor_set(v_reuseFailAlloc_1838_, 5, v_recoveredErrors_1826_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
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
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCacheFn(lean_object* v_p_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v___f_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___f_1850_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn___lam__0), 3, 1);
lean_closure_set(v___f_1850_, 0, v_p_1847_);
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v___x_1851_, v___f_1850_, v_a_1848_, v_a_1849_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withResetCache(lean_object* v_p_1853_){
_start:
{
lean_object* v_info_1854_; lean_object* v_fn_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1863_; 
v_info_1854_ = lean_ctor_get(v_p_1853_, 0);
v_fn_1855_ = lean_ctor_get(v_p_1853_, 1);
v_isSharedCheck_1863_ = !lean_is_exclusive(v_p_1853_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1857_ = v_p_1853_;
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_fn_1855_);
lean_inc(v_info_1854_);
lean_dec(v_p_1853_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1863_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = lean_alloc_closure((void*)(l_Lean_Parser_withResetCacheFn), 3, 1);
lean_closure_set(v___x_1859_, 0, v_fn_1855_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v___x_1859_);
v___x_1861_ = v___x_1857_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_info_1854_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn___lam__0(lean_object* v_f_1864_, lean_object* v_p_1865_, lean_object* v_c_1866_, lean_object* v_s_1867_){
_start:
{
lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1868_ = lean_apply_1(v_f_1864_, v_c_1866_);
v___x_1869_ = lean_apply_2(v_p_1865_, v___x_1868_, v_s_1867_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object* v_f_1870_, lean_object* v_p_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_){
_start:
{
lean_object* v___f_1874_; lean_object* v___x_1875_; 
v___f_1874_ = lean_alloc_closure((void*)(l_Lean_Parser_adaptUncacheableContextFn___lam__0), 4, 2);
lean_closure_set(v___f_1874_, 0, v_f_1870_);
lean_closure_set(v___f_1874_, 1, v_p_1871_);
v___x_1875_ = l_Lean_Parser_withResetCacheFn(v___f_1874_, v_a_1872_, v_a_1873_);
return v___x_1875_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(lean_object* v_a_1876_, lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
uint8_t v___x_1878_; 
v___x_1878_ = 0;
return v___x_1878_;
}
else
{
lean_object* v_key_1879_; lean_object* v_tail_1880_; uint8_t v___x_1881_; 
v_key_1879_ = lean_ctor_get(v_x_1877_, 0);
v_tail_1880_ = lean_ctor_get(v_x_1877_, 2);
v___x_1881_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1879_, v_a_1876_);
if (v___x_1881_ == 0)
{
v_x_1877_ = v_tail_1880_;
goto _start;
}
else
{
return v___x_1881_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg___boxed(lean_object* v_a_1883_, lean_object* v_x_1884_){
_start:
{
uint8_t v_res_1885_; lean_object* v_r_1886_; 
v_res_1885_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1883_, v_x_1884_);
lean_dec(v_x_1884_);
lean_dec_ref(v_a_1883_);
v_r_1886_ = lean_box(v_res_1885_);
return v_r_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
if (lean_obj_tag(v_x_1888_) == 0)
{
return v_x_1887_;
}
else
{
lean_object* v_key_1889_; lean_object* v_value_1890_; lean_object* v_tail_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1921_; 
v_key_1889_ = lean_ctor_get(v_x_1888_, 0);
v_value_1890_ = lean_ctor_get(v_x_1888_, 1);
v_tail_1891_ = lean_ctor_get(v_x_1888_, 2);
v_isSharedCheck_1921_ = !lean_is_exclusive(v_x_1888_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1893_ = v_x_1888_;
v_isShared_1894_ = v_isSharedCheck_1921_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_tail_1891_);
lean_inc(v_value_1890_);
lean_inc(v_key_1889_);
lean_dec(v_x_1888_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1921_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v_parserName_1895_; lean_object* v_pos_1896_; lean_object* v___x_1897_; uint64_t v___x_1898_; uint64_t v___y_1900_; 
v_parserName_1895_ = lean_ctor_get(v_key_1889_, 1);
v_pos_1896_ = lean_ctor_get(v_key_1889_, 2);
v___x_1897_ = lean_array_get_size(v_x_1887_);
v___x_1898_ = l_String_instHashableRaw_hash(v_pos_1896_);
if (lean_obj_tag(v_parserName_1895_) == 0)
{
uint64_t v___x_1919_; 
v___x_1919_ = 1723ULL;
v___y_1900_ = v___x_1919_;
goto v___jp_1899_;
}
else
{
uint64_t v_hash_1920_; 
v_hash_1920_ = lean_ctor_get_uint64(v_parserName_1895_, sizeof(void*)*2);
v___y_1900_ = v_hash_1920_;
goto v___jp_1899_;
}
v___jp_1899_:
{
uint64_t v___x_1901_; uint64_t v___x_1902_; uint64_t v___x_1903_; uint64_t v_fold_1904_; uint64_t v___x_1905_; uint64_t v___x_1906_; uint64_t v___x_1907_; size_t v___x_1908_; size_t v___x_1909_; size_t v___x_1910_; size_t v___x_1911_; size_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1915_; 
v___x_1901_ = lean_uint64_mix_hash(v___x_1898_, v___y_1900_);
v___x_1902_ = 32ULL;
v___x_1903_ = lean_uint64_shift_right(v___x_1901_, v___x_1902_);
v_fold_1904_ = lean_uint64_xor(v___x_1901_, v___x_1903_);
v___x_1905_ = 16ULL;
v___x_1906_ = lean_uint64_shift_right(v_fold_1904_, v___x_1905_);
v___x_1907_ = lean_uint64_xor(v_fold_1904_, v___x_1906_);
v___x_1908_ = lean_uint64_to_usize(v___x_1907_);
v___x_1909_ = lean_usize_of_nat(v___x_1897_);
v___x_1910_ = ((size_t)1ULL);
v___x_1911_ = lean_usize_sub(v___x_1909_, v___x_1910_);
v___x_1912_ = lean_usize_land(v___x_1908_, v___x_1911_);
v___x_1913_ = lean_array_uget_borrowed(v_x_1887_, v___x_1912_);
lean_inc(v___x_1913_);
if (v_isShared_1894_ == 0)
{
lean_ctor_set(v___x_1893_, 2, v___x_1913_);
v___x_1915_ = v___x_1893_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_key_1889_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_value_1890_);
lean_ctor_set(v_reuseFailAlloc_1918_, 2, v___x_1913_);
v___x_1915_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_array_uset(v_x_1887_, v___x_1912_, v___x_1915_);
v_x_1887_ = v___x_1916_;
v_x_1888_ = v_tail_1891_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(lean_object* v_i_1922_, lean_object* v_source_1923_, lean_object* v_target_1924_){
_start:
{
lean_object* v___x_1925_; uint8_t v___x_1926_; 
v___x_1925_ = lean_array_get_size(v_source_1923_);
v___x_1926_ = lean_nat_dec_lt(v_i_1922_, v___x_1925_);
if (v___x_1926_ == 0)
{
lean_dec_ref(v_source_1923_);
lean_dec(v_i_1922_);
return v_target_1924_;
}
else
{
lean_object* v_es_1927_; lean_object* v___x_1928_; lean_object* v_source_1929_; lean_object* v_target_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_es_1927_ = lean_array_fget(v_source_1923_, v_i_1922_);
v___x_1928_ = lean_box(0);
v_source_1929_ = lean_array_fset(v_source_1923_, v_i_1922_, v___x_1928_);
v_target_1930_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_target_1924_, v_es_1927_);
v___x_1931_ = lean_unsigned_to_nat(1u);
v___x_1932_ = lean_nat_add(v_i_1922_, v___x_1931_);
lean_dec(v_i_1922_);
v_i_1922_ = v___x_1932_;
v_source_1923_ = v_source_1929_;
v_target_1924_ = v_target_1930_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(lean_object* v_data_1934_){
_start:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v_nbuckets_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1935_ = lean_array_get_size(v_data_1934_);
v___x_1936_ = lean_unsigned_to_nat(2u);
v_nbuckets_1937_ = lean_nat_mul(v___x_1935_, v___x_1936_);
v___x_1938_ = lean_unsigned_to_nat(0u);
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_mk_array(v_nbuckets_1937_, v___x_1939_);
v___x_1941_ = lean_array_propagate_mark(v_data_1934_, v___x_1940_);
v___x_1942_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v___x_1938_, v_data_1934_, v___x_1941_);
return v___x_1942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(lean_object* v_a_1943_, lean_object* v_b_1944_, lean_object* v_x_1945_){
_start:
{
if (lean_obj_tag(v_x_1945_) == 0)
{
lean_dec(v_b_1944_);
lean_dec_ref(v_a_1943_);
return v_x_1945_;
}
else
{
lean_object* v_key_1946_; lean_object* v_value_1947_; lean_object* v_tail_1948_; lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1960_; 
v_key_1946_ = lean_ctor_get(v_x_1945_, 0);
v_value_1947_ = lean_ctor_get(v_x_1945_, 1);
v_tail_1948_ = lean_ctor_get(v_x_1945_, 2);
v_isSharedCheck_1960_ = !lean_is_exclusive(v_x_1945_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1950_ = v_x_1945_;
v_isShared_1951_ = v_isSharedCheck_1960_;
goto v_resetjp_1949_;
}
else
{
lean_inc(v_tail_1948_);
lean_inc(v_value_1947_);
lean_inc(v_key_1946_);
lean_dec(v_x_1945_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1960_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
uint8_t v___x_1952_; 
v___x_1952_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_1946_, v_a_1943_);
if (v___x_1952_ == 0)
{
lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1953_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1943_, v_b_1944_, v_tail_1948_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 2, v___x_1953_);
v___x_1955_ = v___x_1950_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_key_1946_);
lean_ctor_set(v_reuseFailAlloc_1956_, 1, v_value_1947_);
lean_ctor_set(v_reuseFailAlloc_1956_, 2, v___x_1953_);
v___x_1955_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
return v___x_1955_;
}
}
else
{
lean_object* v___x_1958_; 
lean_dec(v_value_1947_);
lean_dec(v_key_1946_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 1, v_b_1944_);
lean_ctor_set(v___x_1950_, 0, v_a_1943_);
v___x_1958_ = v___x_1950_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1943_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_b_1944_);
lean_ctor_set(v_reuseFailAlloc_1959_, 2, v_tail_1948_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(lean_object* v_m_1961_, lean_object* v_a_1962_, lean_object* v_b_1963_){
_start:
{
lean_object* v_size_1964_; lean_object* v_buckets_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_2015_; 
v_size_1964_ = lean_ctor_get(v_m_1961_, 0);
v_buckets_1965_ = lean_ctor_get(v_m_1961_, 1);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_m_1961_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_1967_ = v_m_1961_;
v_isShared_1968_ = v_isSharedCheck_2015_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_buckets_1965_);
lean_inc(v_size_1964_);
lean_dec(v_m_1961_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_2015_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v_parserName_1969_; lean_object* v_pos_1970_; lean_object* v___x_1971_; uint64_t v___x_1972_; uint64_t v___y_1974_; 
v_parserName_1969_ = lean_ctor_get(v_a_1962_, 1);
v_pos_1970_ = lean_ctor_get(v_a_1962_, 2);
v___x_1971_ = lean_array_get_size(v_buckets_1965_);
v___x_1972_ = l_String_instHashableRaw_hash(v_pos_1970_);
if (lean_obj_tag(v_parserName_1969_) == 0)
{
uint64_t v___x_2013_; 
v___x_2013_ = 1723ULL;
v___y_1974_ = v___x_2013_;
goto v___jp_1973_;
}
else
{
uint64_t v_hash_2014_; 
v_hash_2014_ = lean_ctor_get_uint64(v_parserName_1969_, sizeof(void*)*2);
v___y_1974_ = v_hash_2014_;
goto v___jp_1973_;
}
v___jp_1973_:
{
uint64_t v___x_1975_; uint64_t v___x_1976_; uint64_t v___x_1977_; uint64_t v_fold_1978_; uint64_t v___x_1979_; uint64_t v___x_1980_; uint64_t v___x_1981_; size_t v___x_1982_; size_t v___x_1983_; size_t v___x_1984_; size_t v___x_1985_; size_t v___x_1986_; lean_object* v_bkt_1987_; uint8_t v___x_1988_; 
v___x_1975_ = lean_uint64_mix_hash(v___x_1972_, v___y_1974_);
v___x_1976_ = 32ULL;
v___x_1977_ = lean_uint64_shift_right(v___x_1975_, v___x_1976_);
v_fold_1978_ = lean_uint64_xor(v___x_1975_, v___x_1977_);
v___x_1979_ = 16ULL;
v___x_1980_ = lean_uint64_shift_right(v_fold_1978_, v___x_1979_);
v___x_1981_ = lean_uint64_xor(v_fold_1978_, v___x_1980_);
v___x_1982_ = lean_uint64_to_usize(v___x_1981_);
v___x_1983_ = lean_usize_of_nat(v___x_1971_);
v___x_1984_ = ((size_t)1ULL);
v___x_1985_ = lean_usize_sub(v___x_1983_, v___x_1984_);
v___x_1986_ = lean_usize_land(v___x_1982_, v___x_1985_);
v_bkt_1987_ = lean_array_uget_borrowed(v_buckets_1965_, v___x_1986_);
v___x_1988_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_1962_, v_bkt_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; lean_object* v_size_x27_1990_; lean_object* v___x_1991_; lean_object* v_buckets_x27_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; uint8_t v___x_1998_; 
v___x_1989_ = lean_unsigned_to_nat(1u);
v_size_x27_1990_ = lean_nat_add(v_size_1964_, v___x_1989_);
lean_dec(v_size_1964_);
lean_inc(v_bkt_1987_);
v___x_1991_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1991_, 0, v_a_1962_);
lean_ctor_set(v___x_1991_, 1, v_b_1963_);
lean_ctor_set(v___x_1991_, 2, v_bkt_1987_);
v_buckets_x27_1992_ = lean_array_uset(v_buckets_1965_, v___x_1986_, v___x_1991_);
v___x_1993_ = lean_unsigned_to_nat(4u);
v___x_1994_ = lean_nat_mul(v_size_x27_1990_, v___x_1993_);
v___x_1995_ = lean_unsigned_to_nat(3u);
v___x_1996_ = lean_nat_div(v___x_1994_, v___x_1995_);
lean_dec(v___x_1994_);
v___x_1997_ = lean_array_get_size(v_buckets_x27_1992_);
v___x_1998_ = lean_nat_dec_le(v___x_1996_, v___x_1997_);
lean_dec(v___x_1996_);
if (v___x_1998_ == 0)
{
lean_object* v_val_1999_; lean_object* v___x_2001_; 
v_val_1999_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_buckets_x27_1992_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v_val_1999_);
lean_ctor_set(v___x_1967_, 0, v_size_x27_1990_);
v___x_2001_ = v___x_1967_;
goto v_reusejp_2000_;
}
else
{
lean_object* v_reuseFailAlloc_2002_; 
v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_size_x27_1990_);
lean_ctor_set(v_reuseFailAlloc_2002_, 1, v_val_1999_);
v___x_2001_ = v_reuseFailAlloc_2002_;
goto v_reusejp_2000_;
}
v_reusejp_2000_:
{
return v___x_2001_;
}
}
else
{
lean_object* v___x_2004_; 
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v_buckets_x27_1992_);
lean_ctor_set(v___x_1967_, 0, v_size_x27_1990_);
v___x_2004_ = v___x_1967_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_size_x27_1990_);
lean_ctor_set(v_reuseFailAlloc_2005_, 1, v_buckets_x27_1992_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
else
{
lean_object* v___x_2006_; lean_object* v_buckets_x27_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2011_; 
lean_inc(v_bkt_1987_);
v___x_2006_ = lean_box(0);
v_buckets_x27_2007_ = lean_array_uset(v_buckets_1965_, v___x_1986_, v___x_2006_);
v___x_2008_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_1962_, v_b_1963_, v_bkt_1987_);
v___x_2009_ = lean_array_uset(v_buckets_x27_2007_, v___x_1986_, v___x_2008_);
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 1, v___x_2009_);
v___x_2011_ = v___x_1967_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_size_1964_);
lean_ctor_set(v_reuseFailAlloc_2012_, 1, v___x_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(lean_object* v_a_2016_, lean_object* v_x_2017_){
_start:
{
if (lean_obj_tag(v_x_2017_) == 0)
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_box(0);
return v___x_2018_;
}
else
{
lean_object* v_key_2019_; lean_object* v_value_2020_; lean_object* v_tail_2021_; uint8_t v___x_2022_; 
v_key_2019_ = lean_ctor_get(v_x_2017_, 0);
v_value_2020_ = lean_ctor_get(v_x_2017_, 1);
v_tail_2021_ = lean_ctor_get(v_x_2017_, 2);
v___x_2022_ = l_Lean_Parser_instBEqParserCacheKey_beq(v_key_2019_, v_a_2016_);
if (v___x_2022_ == 0)
{
v_x_2017_ = v_tail_2021_;
goto _start;
}
else
{
lean_object* v___x_2024_; 
lean_inc(v_value_2020_);
v___x_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2024_, 0, v_value_2020_);
return v___x_2024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg___boxed(lean_object* v_a_2025_, lean_object* v_x_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2025_, v_x_2026_);
lean_dec(v_x_2026_);
lean_dec_ref(v_a_2025_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(lean_object* v_m_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_buckets_2030_; lean_object* v_parserName_2031_; lean_object* v_pos_2032_; lean_object* v___x_2033_; uint64_t v___x_2034_; uint64_t v___y_2036_; 
v_buckets_2030_ = lean_ctor_get(v_m_2028_, 1);
v_parserName_2031_ = lean_ctor_get(v_a_2029_, 1);
v_pos_2032_ = lean_ctor_get(v_a_2029_, 2);
v___x_2033_ = lean_array_get_size(v_buckets_2030_);
v___x_2034_ = l_String_instHashableRaw_hash(v_pos_2032_);
if (lean_obj_tag(v_parserName_2031_) == 0)
{
uint64_t v___x_2051_; 
v___x_2051_ = 1723ULL;
v___y_2036_ = v___x_2051_;
goto v___jp_2035_;
}
else
{
uint64_t v_hash_2052_; 
v_hash_2052_ = lean_ctor_get_uint64(v_parserName_2031_, sizeof(void*)*2);
v___y_2036_ = v_hash_2052_;
goto v___jp_2035_;
}
v___jp_2035_:
{
uint64_t v___x_2037_; uint64_t v___x_2038_; uint64_t v___x_2039_; uint64_t v_fold_2040_; uint64_t v___x_2041_; uint64_t v___x_2042_; uint64_t v___x_2043_; size_t v___x_2044_; size_t v___x_2045_; size_t v___x_2046_; size_t v___x_2047_; size_t v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2037_ = lean_uint64_mix_hash(v___x_2034_, v___y_2036_);
v___x_2038_ = 32ULL;
v___x_2039_ = lean_uint64_shift_right(v___x_2037_, v___x_2038_);
v_fold_2040_ = lean_uint64_xor(v___x_2037_, v___x_2039_);
v___x_2041_ = 16ULL;
v___x_2042_ = lean_uint64_shift_right(v_fold_2040_, v___x_2041_);
v___x_2043_ = lean_uint64_xor(v_fold_2040_, v___x_2042_);
v___x_2044_ = lean_uint64_to_usize(v___x_2043_);
v___x_2045_ = lean_usize_of_nat(v___x_2033_);
v___x_2046_ = ((size_t)1ULL);
v___x_2047_ = lean_usize_sub(v___x_2045_, v___x_2046_);
v___x_2048_ = lean_usize_land(v___x_2044_, v___x_2047_);
v___x_2049_ = lean_array_uget_borrowed(v_buckets_2030_, v___x_2048_);
v___x_2050_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2029_, v___x_2049_);
return v___x_2050_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg___boxed(lean_object* v_m_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2053_, v_a_2054_);
lean_dec_ref(v_a_2054_);
lean_dec_ref(v_m_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCacheFn(lean_object* v_parserName_2056_, lean_object* v_p_2057_, lean_object* v_c_2058_, lean_object* v_s_2059_){
_start:
{
lean_object* v_cache_2060_; lean_object* v_toCacheableParserContext_2061_; lean_object* v_stxStack_2062_; lean_object* v_pos_2063_; lean_object* v_recoveredErrors_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2113_; 
v_cache_2060_ = lean_ctor_get(v_s_2059_, 3);
lean_inc_ref(v_cache_2060_);
v_toCacheableParserContext_2061_ = lean_ctor_get(v_c_2058_, 2);
v_stxStack_2062_ = lean_ctor_get(v_s_2059_, 0);
v_pos_2063_ = lean_ctor_get(v_s_2059_, 2);
v_recoveredErrors_2064_ = lean_ctor_get(v_s_2059_, 5);
v_isSharedCheck_2113_ = !lean_is_exclusive(v_s_2059_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; lean_object* v_unused_2115_; lean_object* v_unused_2116_; 
v_unused_2114_ = lean_ctor_get(v_s_2059_, 4);
lean_dec(v_unused_2114_);
v_unused_2115_ = lean_ctor_get(v_s_2059_, 3);
lean_dec(v_unused_2115_);
v_unused_2116_ = lean_ctor_get(v_s_2059_, 1);
lean_dec(v_unused_2116_);
v___x_2066_ = v_s_2059_;
v_isShared_2067_ = v_isSharedCheck_2113_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_recoveredErrors_2064_);
lean_inc(v_pos_2063_);
lean_inc(v_stxStack_2062_);
lean_dec(v_s_2059_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2113_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v_parserCache_2068_; lean_object* v_key_2069_; lean_object* v___x_2070_; 
v_parserCache_2068_ = lean_ctor_get(v_cache_2060_, 1);
lean_inc(v_pos_2063_);
lean_inc_ref(v_toCacheableParserContext_2061_);
v_key_2069_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_key_2069_, 0, v_toCacheableParserContext_2061_);
lean_ctor_set(v_key_2069_, 1, v_parserName_2056_);
lean_ctor_set(v_key_2069_, 2, v_pos_2063_);
v___x_2070_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_parserCache_2068_, v_key_2069_);
if (lean_obj_tag(v___x_2070_) == 1)
{
lean_object* v_val_2071_; lean_object* v_stx_2072_; lean_object* v_lhsPrec_2073_; lean_object* v_newPos_2074_; lean_object* v_errorMsg_2075_; lean_object* v___x_2076_; lean_object* v___x_2078_; 
lean_dec_ref_known(v_key_2069_, 3);
lean_dec(v_pos_2063_);
lean_dec_ref(v_c_2058_);
lean_dec_ref(v_p_2057_);
v_val_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_val_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v_stx_2072_ = lean_ctor_get(v_val_2071_, 0);
lean_inc(v_stx_2072_);
v_lhsPrec_2073_ = lean_ctor_get(v_val_2071_, 1);
lean_inc(v_lhsPrec_2073_);
v_newPos_2074_ = lean_ctor_get(v_val_2071_, 2);
lean_inc(v_newPos_2074_);
v_errorMsg_2075_ = lean_ctor_get(v_val_2071_, 3);
lean_inc(v_errorMsg_2075_);
lean_dec(v_val_2071_);
v___x_2076_ = l_Lean_Parser_SyntaxStack_push(v_stxStack_2062_, v_stx_2072_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 4, v_errorMsg_2075_);
lean_ctor_set(v___x_2066_, 2, v_newPos_2074_);
lean_ctor_set(v___x_2066_, 1, v_lhsPrec_2073_);
lean_ctor_set(v___x_2066_, 0, v___x_2076_);
v___x_2078_ = v___x_2066_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_lhsPrec_2073_);
lean_ctor_set(v_reuseFailAlloc_2079_, 2, v_newPos_2074_);
lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_cache_2060_);
lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_errorMsg_2075_);
lean_ctor_set(v_reuseFailAlloc_2079_, 5, v_recoveredErrors_2064_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
else
{
lean_object* v_raw_2080_; lean_object* v_initStackSz_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2085_; 
lean_dec(v___x_2070_);
v_raw_2080_ = lean_ctor_get(v_stxStack_2062_, 0);
v_initStackSz_2081_ = lean_array_get_size(v_raw_2080_);
v___x_2082_ = lean_unsigned_to_nat(0u);
v___x_2083_ = lean_box(0);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 4, v___x_2083_);
lean_ctor_set(v___x_2066_, 1, v___x_2082_);
v___x_2085_ = v___x_2066_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_stxStack_2062_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2082_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_pos_2063_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_cache_2060_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v___x_2083_);
lean_ctor_set(v_reuseFailAlloc_2112_, 5, v_recoveredErrors_2064_);
v___x_2085_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
lean_object* v_s_2086_; lean_object* v_cache_2087_; lean_object* v_stxStack_2088_; lean_object* v_lhsPrec_2089_; lean_object* v_pos_2090_; lean_object* v_errorMsg_2091_; lean_object* v_recoveredErrors_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2111_; 
v_s_2086_ = l___private_Lean_Parser_Types_0__Lean_Parser_withStackDrop(v_initStackSz_2081_, v_p_2057_, v_c_2058_, v___x_2085_);
v_cache_2087_ = lean_ctor_get(v_s_2086_, 3);
v_stxStack_2088_ = lean_ctor_get(v_s_2086_, 0);
v_lhsPrec_2089_ = lean_ctor_get(v_s_2086_, 1);
v_pos_2090_ = lean_ctor_get(v_s_2086_, 2);
v_errorMsg_2091_ = lean_ctor_get(v_s_2086_, 4);
v_recoveredErrors_2092_ = lean_ctor_get(v_s_2086_, 5);
v_isSharedCheck_2111_ = !lean_is_exclusive(v_s_2086_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2094_ = v_s_2086_;
v_isShared_2095_ = v_isSharedCheck_2111_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_recoveredErrors_2092_);
lean_inc(v_errorMsg_2091_);
lean_inc(v_cache_2087_);
lean_inc(v_pos_2090_);
lean_inc(v_lhsPrec_2089_);
lean_inc(v_stxStack_2088_);
lean_dec(v_s_2086_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2111_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_tokenCache_2096_; lean_object* v_parserCache_2097_; lean_object* v___x_2099_; uint8_t v_isShared_2100_; uint8_t v_isSharedCheck_2110_; 
v_tokenCache_2096_ = lean_ctor_get(v_cache_2087_, 0);
v_parserCache_2097_ = lean_ctor_get(v_cache_2087_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_cache_2087_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2099_ = v_cache_2087_;
v_isShared_2100_ = v_isSharedCheck_2110_;
goto v_resetjp_2098_;
}
else
{
lean_inc(v_parserCache_2097_);
lean_inc(v_tokenCache_2096_);
lean_dec(v_cache_2087_);
v___x_2099_ = lean_box(0);
v_isShared_2100_ = v_isSharedCheck_2110_;
goto v_resetjp_2098_;
}
v_resetjp_2098_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2105_; 
v___x_2101_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2088_);
lean_inc(v_errorMsg_2091_);
lean_inc(v_pos_2090_);
lean_inc(v_lhsPrec_2089_);
v___x_2102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2102_, 0, v___x_2101_);
lean_ctor_set(v___x_2102_, 1, v_lhsPrec_2089_);
lean_ctor_set(v___x_2102_, 2, v_pos_2090_);
lean_ctor_set(v___x_2102_, 3, v_errorMsg_2091_);
v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_parserCache_2097_, v_key_2069_, v___x_2102_);
if (v_isShared_2100_ == 0)
{
lean_ctor_set(v___x_2099_, 1, v___x_2103_);
v___x_2105_ = v___x_2099_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_tokenCache_2096_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___x_2103_);
v___x_2105_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
lean_object* v___x_2107_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 3, v___x_2105_);
v___x_2107_ = v___x_2094_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_stxStack_2088_);
lean_ctor_set(v_reuseFailAlloc_2108_, 1, v_lhsPrec_2089_);
lean_ctor_set(v_reuseFailAlloc_2108_, 2, v_pos_2090_);
lean_ctor_set(v_reuseFailAlloc_2108_, 3, v___x_2105_);
lean_ctor_set(v_reuseFailAlloc_2108_, 4, v_errorMsg_2091_);
lean_ctor_set(v_reuseFailAlloc_2108_, 5, v_recoveredErrors_2092_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(lean_object* v_00_u03b2_2117_, lean_object* v_m_2118_, lean_object* v_a_2119_){
_start:
{
lean_object* v___x_2120_; 
v___x_2120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___redArg(v_m_2118_, v_a_2119_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0___boxed(lean_object* v_00_u03b2_2121_, lean_object* v_m_2122_, lean_object* v_a_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0(v_00_u03b2_2121_, v_m_2122_, v_a_2123_);
lean_dec_ref(v_a_2123_);
lean_dec_ref(v_m_2122_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1(lean_object* v_00_u03b2_2125_, lean_object* v_m_2126_, lean_object* v_a_2127_, lean_object* v_b_2128_){
_start:
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1___redArg(v_m_2126_, v_a_2127_, v_b_2128_);
return v___x_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(lean_object* v_00_u03b2_2130_, lean_object* v_a_2131_, lean_object* v_x_2132_){
_start:
{
lean_object* v___x_2133_; 
v___x_2133_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___redArg(v_a_2131_, v_x_2132_);
return v___x_2133_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0___boxed(lean_object* v_00_u03b2_2134_, lean_object* v_a_2135_, lean_object* v_x_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Parser_withCacheFn_spec__0_spec__0(v_00_u03b2_2134_, v_a_2135_, v_x_2136_);
lean_dec(v_x_2136_);
lean_dec_ref(v_a_2135_);
return v_res_2137_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(lean_object* v_00_u03b2_2138_, lean_object* v_a_2139_, lean_object* v_x_2140_){
_start:
{
uint8_t v___x_2141_; 
v___x_2141_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___redArg(v_a_2139_, v_x_2140_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2142_, lean_object* v_a_2143_, lean_object* v_x_2144_){
_start:
{
uint8_t v_res_2145_; lean_object* v_r_2146_; 
v_res_2145_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__2(v_00_u03b2_2142_, v_a_2143_, v_x_2144_);
lean_dec(v_x_2144_);
lean_dec_ref(v_a_2143_);
v_r_2146_ = lean_box(v_res_2145_);
return v_r_2146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3(lean_object* v_00_u03b2_2147_, lean_object* v_data_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3___redArg(v_data_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4(lean_object* v_00_u03b2_2150_, lean_object* v_a_2151_, lean_object* v_b_2152_, lean_object* v_x_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__4___redArg(v_a_2151_, v_b_2152_, v_x_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4(lean_object* v_00_u03b2_2155_, lean_object* v_i_2156_, lean_object* v_source_2157_, lean_object* v_target_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4___redArg(v_i_2156_, v_source_2157_, v_target_2158_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5(lean_object* v_00_u03b2_2160_, lean_object* v_x_2161_, lean_object* v_x_2162_){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Parser_withCacheFn_spec__1_spec__3_spec__4_spec__5___redArg(v_x_2161_, v_x_2162_);
return v___x_2163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_withCache(lean_object* v_parserName_2164_, lean_object* v_p_2165_){
_start:
{
lean_object* v_info_2166_; lean_object* v_fn_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2175_; 
v_info_2166_ = lean_ctor_get(v_p_2165_, 0);
v_fn_2167_ = lean_ctor_get(v_p_2165_, 1);
v_isSharedCheck_2175_ = !lean_is_exclusive(v_p_2165_);
if (v_isSharedCheck_2175_ == 0)
{
v___x_2169_ = v_p_2165_;
v_isShared_2170_ = v_isSharedCheck_2175_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_fn_2167_);
lean_inc(v_info_2166_);
lean_dec(v_p_2165_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2175_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2171_ = lean_alloc_closure((void*)(l_Lean_Parser_withCacheFn), 4, 2);
lean_closure_set(v___x_2171_, 0, v_parserName_2164_);
lean_closure_set(v___x_2171_, 1, v_fn_2167_);
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 1, v___x_2171_);
v___x_2173_ = v___x_2169_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v_info_2166_);
lean_ctor_set(v_reuseFailAlloc_2174_, 1, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1(){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__1));
v___x_2184_ = ((lean_object*)(l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___closed__2));
v___x_2185_ = l_Lean_addBuiltinDocString(v___x_2183_, v___x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1___boxed(lean_object* v_a_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Lean_Parser_Types_0__Lean_Parser_withCache___regBuiltin_Lean_Parser_withCache_docString__1();
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Parser_ParserFn_run(lean_object* v_p_2195_, lean_object* v_ictx_2196_, lean_object* v_pmctx_2197_, lean_object* v_tokens_2198_, lean_object* v_s_2199_){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = ((lean_object*)(l_Lean_Parser_ParserFn_run___closed__1));
v___x_2201_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2201_, 0, v_ictx_2196_);
lean_ctor_set(v___x_2201_, 1, v_pmctx_2197_);
lean_ctor_set(v___x_2201_, 2, v___x_2200_);
lean_ctor_set(v___x_2201_, 3, v_tokens_2198_);
v___x_2202_ = lean_apply_2(v_p_2195_, v___x_2201_, v_s_2199_);
return v___x_2202_;
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
