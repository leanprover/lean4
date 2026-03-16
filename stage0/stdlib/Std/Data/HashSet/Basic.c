// Lean compiler output
// Module: Std.Data.HashSet.Basic
// Imports: public import Std.Data.HashMap.Basic
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
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_HashSet_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instEmptyCollection___closed__1;
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__0 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HashSet"};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__1 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__2 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__2_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__3_value_aux_0),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 195, 212, 176, 236, 184, 63, 58)}};
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__3_value_aux_1),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(31, 188, 56, 164, 219, 178, 234, 183)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__3 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__3_value;
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__4 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__4_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__5 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__5_value;
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__6 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__6_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__6_value)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__7 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__7_value;
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__8 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__8_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__9 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__9_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__10 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__5_value),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__7_value),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__10_value)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__11 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__12 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__12_value;
LEAN_EXPORT const lean_object* l_Std_HashSet_term___x7em__ = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__12_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_0),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_1),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_2),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value;
static lean_once_cell_t l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_0),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 195, 212, 176, 236, 184, 63, 58)}};
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_1),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(222, 215, 188, 50, 207, 199, 108, 184)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9_value),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11_value)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14_value;
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__1_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__2 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__2_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__3 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__3_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__4 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__4_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__5 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__5_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__6 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__6_value;
static const lean_ctor_object l_Std_HashSet_toList___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__0_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__1_value)}};
static const lean_object* l_Std_HashSet_toList___redArg___closed__7 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__7_value;
static const lean_ctor_object l_Std_HashSet_toList___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__7_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__2_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__3_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__4_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__5_value)}};
static const lean_object* l_Std_HashSet_toList___redArg___closed__8 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__8_value;
static const lean_ctor_object l_Std_HashSet_toList___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__8_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__6_value)}};
static const lean_object* l_Std_HashSet_toList___redArg___closed__9 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__9_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__10 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__10_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_toList___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__9_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__10_value)} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__11 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__9_value)} };
static const lean_object* l_Std_HashSet_ofList___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashSet_ofList___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toArray___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_toArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_toArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__9_value),((lean_object*)&l_Std_HashSet_toArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashSet_toArray___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_HashSet_all___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet_all___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_all___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_HashSet_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__9_value)} };
static const lean_object* l_Std_HashSet_union___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInter(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_beq___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_beq___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_HashSet_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_partition___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_partition___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__9_value)} };
static const lean_object* l_Std_HashSet_ofArray___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_ofArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_ofArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_ofArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashSet_ofArray___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_ofArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashSet_instRepr___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashSet.ofList "};
static const lean_object* l_Std_HashSet_instRepr___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_HashSet_instRepr___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Std_HashSet_instRepr___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_HashSet_instRepr___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Std_HashSet_instRepr___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_HashSet_instRepr___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_2_ = lean_unsigned_to_nat(0u);
v___x_3_ = lean_unsigned_to_nat(4u);
v___x_4_ = lean_nat_mul(v_capacity_1_, v___x_3_);
v___x_5_ = lean_unsigned_to_nat(3u);
v___x_6_ = lean_nat_div(v___x_4_, v___x_5_);
lean_dec(v___x_4_);
v___x_7_ = l_Nat_nextPowerOfTwo(v___x_6_);
lean_dec(v___x_6_);
v___x_8_ = lean_box(0);
v___x_9_ = lean_mk_array(v___x_7_, v___x_8_);
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_2_);
lean_ctor_set(v___x_10_, 1, v___x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_HashSet_emptyWithCapacity___redArg(v_capacity_11_);
lean_dec(v_capacity_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity(lean_object* v_00_u03b1_13_, lean_object* v_inst_14_, lean_object* v_inst_15_, lean_object* v_capacity_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_unsigned_to_nat(4u);
v___x_19_ = lean_nat_mul(v_capacity_16_, v___x_18_);
v___x_20_ = lean_unsigned_to_nat(3u);
v___x_21_ = lean_nat_div(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
v___x_22_ = l_Nat_nextPowerOfTwo(v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = lean_box(0);
v___x_24_ = lean_mk_array(v___x_22_, v___x_23_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_17_);
lean_ctor_set(v___x_25_, 1, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___boxed(lean_object* v_00_u03b1_26_, lean_object* v_inst_27_, lean_object* v_inst_28_, lean_object* v_capacity_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_HashSet_emptyWithCapacity(v_00_u03b1_26_, v_inst_27_, v_inst_28_, v_capacity_29_);
lean_dec(v_capacity_29_);
lean_dec_ref(v_inst_28_);
lean_dec_ref(v_inst_27_);
return v_res_30_;
}
}
static lean_object* _init_l_Std_HashSet_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = lean_unsigned_to_nat(16u);
v___x_33_ = lean_mk_array(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_HashSet_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__0, &l_Std_HashSet_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_instEmptyCollection___closed__0);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_inst_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_inst_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_HashSet_instEmptyCollection(v_00_u03b1_41_, v_inst_42_, v_inst_43_);
lean_dec_ref(v_inst_43_);
lean_dec_ref(v_inst_42_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited(lean_object* v_00_u03b1_45_, lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___boxed(lean_object* v_00_u03b1_49_, lean_object* v_inst_50_, lean_object* v_inst_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Std_HashSet_instInhabited(v_00_u03b1_49_, v_inst_50_, v_inst_51_);
lean_dec_ref(v_inst_51_);
lean_dec_ref(v_inst_50_);
return v_res_52_;
}
}
static lean_object* _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5));
v___x_92_ = l_String_toRawSubstring_x27(v___x_91_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(lean_object* v_x_113_, lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__3));
lean_inc(v_x_113_);
v___x_117_ = l_Lean_Syntax_isOfKind(v_x_113_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec_ref(v_a_114_);
lean_dec(v_x_113_);
v___x_118_ = lean_box(1);
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_115_);
return v___x_119_;
}
else
{
lean_object* v_quotContext_120_; lean_object* v_currMacroScope_121_; lean_object* v_ref_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; uint8_t v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_quotContext_120_ = lean_ctor_get(v_a_114_, 1);
lean_inc(v_quotContext_120_);
v_currMacroScope_121_ = lean_ctor_get(v_a_114_, 2);
lean_inc(v_currMacroScope_121_);
v_ref_122_ = lean_ctor_get(v_a_114_, 5);
lean_inc(v_ref_122_);
lean_dec_ref(v_a_114_);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = l_Lean_Syntax_getArg(v_x_113_, v___x_123_);
v___x_125_ = lean_unsigned_to_nat(2u);
v___x_126_ = l_Lean_Syntax_getArg(v_x_113_, v___x_125_);
lean_dec(v_x_113_);
v___x_127_ = 0;
v___x_128_ = l_Lean_SourceInfo_fromRef(v_ref_122_, v___x_127_);
lean_dec(v_ref_122_);
v___x_129_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4));
v___x_130_ = lean_obj_once(&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6, &l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6_once, _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6);
v___x_131_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7));
v___x_132_ = l_Lean_addMacroScope(v_quotContext_120_, v___x_131_, v_currMacroScope_121_);
v___x_133_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12));
lean_inc(v___x_128_);
v___x_134_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_134_, 0, v___x_128_);
lean_ctor_set(v___x_134_, 1, v___x_130_);
lean_ctor_set(v___x_134_, 2, v___x_132_);
lean_ctor_set(v___x_134_, 3, v___x_133_);
v___x_135_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14));
lean_inc(v___x_128_);
v___x_136_ = l_Lean_Syntax_node2(v___x_128_, v___x_135_, v___x_124_, v___x_126_);
v___x_137_ = l_Lean_Syntax_node2(v___x_128_, v___x_129_, v___x_134_, v___x_136_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v_a_115_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(lean_object* v_x_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_145_; uint8_t v___x_146_; 
v___x_145_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4));
lean_inc(v_x_142_);
v___x_146_ = l_Lean_Syntax_isOfKind(v_x_142_, v___x_145_);
if (v___x_146_ == 0)
{
lean_object* v___x_147_; lean_object* v___x_148_; 
lean_dec(v_x_142_);
v___x_147_ = lean_box(0);
v___x_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_a_144_);
return v___x_148_;
}
else
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_149_ = lean_unsigned_to_nat(0u);
v___x_150_ = l_Lean_Syntax_getArg(v_x_142_, v___x_149_);
v___x_151_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1));
lean_inc(v___x_150_);
v___x_152_ = l_Lean_Syntax_isOfKind(v___x_150_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v___x_150_);
lean_dec(v_x_142_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_a_144_);
return v___x_154_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_155_ = lean_unsigned_to_nat(1u);
v___x_156_ = l_Lean_Syntax_getArg(v_x_142_, v___x_155_);
lean_dec(v_x_142_);
v___x_157_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_156_);
v___x_158_ = l_Lean_Syntax_matchesNull(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v___x_156_);
lean_dec(v___x_150_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v_a_144_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v_ref_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_161_ = l_Lean_Syntax_getArg(v___x_156_, v___x_149_);
v___x_162_ = l_Lean_Syntax_getArg(v___x_156_, v___x_155_);
lean_dec(v___x_156_);
v_ref_163_ = l_Lean_replaceRef(v___x_150_, v_a_143_);
lean_dec(v___x_150_);
v___x_164_ = 0;
v___x_165_ = l_Lean_SourceInfo_fromRef(v_ref_163_, v___x_164_);
lean_dec(v_ref_163_);
v___x_166_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__3));
v___x_167_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__6));
lean_inc(v___x_165_);
v___x_168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_165_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = l_Lean_Syntax_node3(v___x_165_, v___x_166_, v___x_161_, v___x_168_, v___x_162_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_a_144_);
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___boxed(lean_object* v_x_171_, lean_object* v_a_172_, lean_object* v_a_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(v_x_171_, v_a_172_, v_a_173_);
lean_dec(v_a_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert___redArg(lean_object* v_x_175_, lean_object* v_x_176_, lean_object* v_m_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = lean_box(0);
v___x_180_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_175_, v_x_176_, v_m_177_, v_a_178_, v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert(lean_object* v_00_u03b1_181_, lean_object* v_x_182_, lean_object* v_x_183_, lean_object* v_m_184_, lean_object* v_a_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_box(0);
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_182_, v_x_183_, v_m_184_, v_a_185_, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg___lam__0(lean_object* v_x_188_, lean_object* v_x_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_192_ = lean_box(0);
v___x_193_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_188_, v_x_189_, v___x_191_, v_a_190_, v___x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg(lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
lean_object* v___f_196_; 
v___f_196_ = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(v___f_196_, 0, v_x_194_);
lean_closure_set(v___f_196_, 1, v_x_195_);
return v___f_196_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton(lean_object* v_00_u03b1_197_, lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(v___f_200_, 0, v_x_198_);
lean_closure_set(v___f_200_, 1, v_x_199_);
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg___lam__0(lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_a_203_, lean_object* v_s_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_box(0);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_201_, v_x_202_, v_s_204_, v_a_203_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg(lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
lean_object* v___f_209_; 
v___f_209_ = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(v___f_209_, 0, v_x_207_);
lean_closure_set(v___f_209_, 1, v_x_208_);
return v___f_209_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert(lean_object* v_00_u03b1_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(v___f_213_, 0, v_x_211_);
lean_closure_set(v___f_213_, 1, v_x_212_);
return v___f_213_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert___redArg(lean_object* v_x_214_, lean_object* v_x_215_, lean_object* v_m_216_, lean_object* v_a_217_){
_start:
{
lean_object* v_size_218_; lean_object* v_buckets_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint64_t v___x_222_; uint64_t v___x_223_; uint64_t v___x_224_; uint64_t v___x_225_; uint64_t v_fold_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; size_t v___x_230_; size_t v___x_231_; size_t v___x_232_; size_t v___x_233_; size_t v___x_234_; lean_object* v_bkt_235_; uint8_t v___x_236_; 
v_size_218_ = lean_ctor_get(v_m_216_, 0);
v_buckets_219_ = lean_ctor_get(v_m_216_, 1);
v___x_220_ = lean_array_get_size(v_buckets_219_);
lean_inc_ref(v_x_215_);
lean_inc(v_a_217_);
v___x_221_ = lean_apply_1(v_x_215_, v_a_217_);
v___x_222_ = 32ULL;
v___x_223_ = lean_unbox_uint64(v___x_221_);
v___x_224_ = lean_uint64_shift_right(v___x_223_, v___x_222_);
v___x_225_ = lean_unbox_uint64(v___x_221_);
lean_dec_ref(v___x_221_);
v_fold_226_ = lean_uint64_xor(v___x_225_, v___x_224_);
v___x_227_ = 16ULL;
v___x_228_ = lean_uint64_shift_right(v_fold_226_, v___x_227_);
v___x_229_ = lean_uint64_xor(v_fold_226_, v___x_228_);
v___x_230_ = lean_uint64_to_usize(v___x_229_);
v___x_231_ = lean_usize_of_nat(v___x_220_);
v___x_232_ = ((size_t)1ULL);
v___x_233_ = lean_usize_sub(v___x_231_, v___x_232_);
v___x_234_ = lean_usize_land(v___x_230_, v___x_233_);
v_bkt_235_ = lean_array_uget_borrowed(v_buckets_219_, v___x_234_);
lean_inc(v_bkt_235_);
lean_inc(v_a_217_);
v___x_236_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_214_, v_a_217_, v_bkt_235_);
if (v___x_236_ == 0)
{
lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_262_; 
lean_inc_ref(v_buckets_219_);
lean_inc(v_size_218_);
v_isSharedCheck_262_ = !lean_is_exclusive(v_m_216_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; lean_object* v_unused_264_; 
v_unused_263_ = lean_ctor_get(v_m_216_, 1);
lean_dec(v_unused_263_);
v_unused_264_ = lean_ctor_get(v_m_216_, 0);
lean_dec(v_unused_264_);
v___x_238_ = v_m_216_;
v_isShared_239_ = v_isSharedCheck_262_;
goto v_resetjp_237_;
}
else
{
lean_dec(v_m_216_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_262_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v_size_x27_242_; lean_object* v___x_243_; lean_object* v_buckets_x27_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_240_ = lean_box(0);
v___x_241_ = lean_unsigned_to_nat(1u);
v_size_x27_242_ = lean_nat_add(v_size_218_, v___x_241_);
lean_dec(v_size_218_);
lean_inc(v_bkt_235_);
v___x_243_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_243_, 0, v_a_217_);
lean_ctor_set(v___x_243_, 1, v___x_240_);
lean_ctor_set(v___x_243_, 2, v_bkt_235_);
v_buckets_x27_244_ = lean_array_uset(v_buckets_219_, v___x_234_, v___x_243_);
v___x_245_ = lean_unsigned_to_nat(4u);
v___x_246_ = lean_nat_mul(v_size_x27_242_, v___x_245_);
v___x_247_ = lean_unsigned_to_nat(3u);
v___x_248_ = lean_nat_div(v___x_246_, v___x_247_);
lean_dec(v___x_246_);
v___x_249_ = lean_array_get_size(v_buckets_x27_244_);
v___x_250_ = lean_nat_dec_le(v___x_248_, v___x_249_);
lean_dec(v___x_248_);
if (v___x_250_ == 0)
{
lean_object* v_val_251_; lean_object* v___x_253_; 
v_val_251_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_215_, v_buckets_x27_244_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v_val_251_);
lean_ctor_set(v___x_238_, 0, v_size_x27_242_);
v___x_253_ = v___x_238_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_size_x27_242_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_val_251_);
v___x_253_ = v_reuseFailAlloc_256_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_box(v___x_236_);
v___x_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
return v___x_255_;
}
}
else
{
lean_object* v___x_258_; 
lean_dec_ref(v_x_215_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 1, v_buckets_x27_244_);
lean_ctor_set(v___x_238_, 0, v_size_x27_242_);
v___x_258_ = v___x_238_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_size_x27_242_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v_buckets_x27_244_);
v___x_258_ = v_reuseFailAlloc_261_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(v___x_236_);
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_258_);
return v___x_260_;
}
}
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_a_217_);
lean_dec_ref(v_x_215_);
v___x_265_ = lean_box(v___x_236_);
v___x_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
lean_ctor_set(v___x_266_, 1, v_m_216_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert(lean_object* v_00_u03b1_267_, lean_object* v_x_268_, lean_object* v_x_269_, lean_object* v_m_270_, lean_object* v_a_271_){
_start:
{
lean_object* v_size_272_; lean_object* v_buckets_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint64_t v___x_276_; uint64_t v___x_277_; uint64_t v___x_278_; uint64_t v___x_279_; uint64_t v_fold_280_; uint64_t v___x_281_; uint64_t v___x_282_; uint64_t v___x_283_; size_t v___x_284_; size_t v___x_285_; size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; lean_object* v_bkt_289_; uint8_t v___x_290_; 
v_size_272_ = lean_ctor_get(v_m_270_, 0);
v_buckets_273_ = lean_ctor_get(v_m_270_, 1);
v___x_274_ = lean_array_get_size(v_buckets_273_);
lean_inc_ref(v_x_269_);
lean_inc(v_a_271_);
v___x_275_ = lean_apply_1(v_x_269_, v_a_271_);
v___x_276_ = 32ULL;
v___x_277_ = lean_unbox_uint64(v___x_275_);
v___x_278_ = lean_uint64_shift_right(v___x_277_, v___x_276_);
v___x_279_ = lean_unbox_uint64(v___x_275_);
lean_dec_ref(v___x_275_);
v_fold_280_ = lean_uint64_xor(v___x_279_, v___x_278_);
v___x_281_ = 16ULL;
v___x_282_ = lean_uint64_shift_right(v_fold_280_, v___x_281_);
v___x_283_ = lean_uint64_xor(v_fold_280_, v___x_282_);
v___x_284_ = lean_uint64_to_usize(v___x_283_);
v___x_285_ = lean_usize_of_nat(v___x_274_);
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_sub(v___x_285_, v___x_286_);
v___x_288_ = lean_usize_land(v___x_284_, v___x_287_);
v_bkt_289_ = lean_array_uget_borrowed(v_buckets_273_, v___x_288_);
lean_inc(v_bkt_289_);
lean_inc(v_a_271_);
v___x_290_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_268_, v_a_271_, v_bkt_289_);
if (v___x_290_ == 0)
{
lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_316_; 
lean_inc_ref(v_buckets_273_);
lean_inc(v_size_272_);
v_isSharedCheck_316_ = !lean_is_exclusive(v_m_270_);
if (v_isSharedCheck_316_ == 0)
{
lean_object* v_unused_317_; lean_object* v_unused_318_; 
v_unused_317_ = lean_ctor_get(v_m_270_, 1);
lean_dec(v_unused_317_);
v_unused_318_ = lean_ctor_get(v_m_270_, 0);
lean_dec(v_unused_318_);
v___x_292_ = v_m_270_;
v_isShared_293_ = v_isSharedCheck_316_;
goto v_resetjp_291_;
}
else
{
lean_dec(v_m_270_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_316_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_size_x27_296_; lean_object* v___x_297_; lean_object* v_buckets_x27_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_294_ = lean_box(0);
v___x_295_ = lean_unsigned_to_nat(1u);
v_size_x27_296_ = lean_nat_add(v_size_272_, v___x_295_);
lean_dec(v_size_272_);
lean_inc(v_bkt_289_);
v___x_297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_297_, 0, v_a_271_);
lean_ctor_set(v___x_297_, 1, v___x_294_);
lean_ctor_set(v___x_297_, 2, v_bkt_289_);
v_buckets_x27_298_ = lean_array_uset(v_buckets_273_, v___x_288_, v___x_297_);
v___x_299_ = lean_unsigned_to_nat(4u);
v___x_300_ = lean_nat_mul(v_size_x27_296_, v___x_299_);
v___x_301_ = lean_unsigned_to_nat(3u);
v___x_302_ = lean_nat_div(v___x_300_, v___x_301_);
lean_dec(v___x_300_);
v___x_303_ = lean_array_get_size(v_buckets_x27_298_);
v___x_304_ = lean_nat_dec_le(v___x_302_, v___x_303_);
lean_dec(v___x_302_);
if (v___x_304_ == 0)
{
lean_object* v_val_305_; lean_object* v___x_307_; 
v_val_305_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_269_, v_buckets_x27_298_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v_val_305_);
lean_ctor_set(v___x_292_, 0, v_size_x27_296_);
v___x_307_ = v___x_292_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_size_x27_296_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v_val_305_);
v___x_307_ = v_reuseFailAlloc_310_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_box(v___x_290_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
return v___x_309_;
}
}
else
{
lean_object* v___x_312_; 
lean_dec_ref(v_x_269_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v_buckets_x27_298_);
lean_ctor_set(v___x_292_, 0, v_size_x27_296_);
v___x_312_ = v___x_292_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_size_x27_296_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v_buckets_x27_298_);
v___x_312_ = v_reuseFailAlloc_315_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_box(v___x_290_);
v___x_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v___x_312_);
return v___x_314_;
}
}
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_a_271_);
lean_dec_ref(v_x_269_);
v___x_319_ = lean_box(v___x_290_);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_m_270_);
return v___x_320_;
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_contains___redArg(lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_m_323_, lean_object* v_a_324_){
_start:
{
uint8_t v___x_325_; 
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_321_, v_x_322_, v_m_323_, v_a_324_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___redArg___boxed(lean_object* v_x_326_, lean_object* v_x_327_, lean_object* v_m_328_, lean_object* v_a_329_){
_start:
{
uint8_t v_res_330_; lean_object* v_r_331_; 
v_res_330_ = l_Std_HashSet_contains___redArg(v_x_326_, v_x_327_, v_m_328_, v_a_329_);
lean_dec_ref(v_m_328_);
v_r_331_ = lean_box(v_res_330_);
return v_r_331_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_contains(lean_object* v_00_u03b1_332_, lean_object* v_x_333_, lean_object* v_x_334_, lean_object* v_m_335_, lean_object* v_a_336_){
_start:
{
uint8_t v___x_337_; 
v___x_337_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_333_, v_x_334_, v_m_335_, v_a_336_);
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___boxed(lean_object* v_00_u03b1_338_, lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_m_341_, lean_object* v_a_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Std_HashSet_contains(v_00_u03b1_338_, v_x_339_, v_x_340_, v_m_341_, v_a_342_);
lean_dec_ref(v_m_341_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership(lean_object* v_00_u03b1_345_, lean_object* v_inst_346_, lean_object* v_inst_347_){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_box(0);
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___boxed(lean_object* v_00_u03b1_349_, lean_object* v_inst_350_, lean_object* v_inst_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Std_HashSet_instMembership(v_00_u03b1_349_, v_inst_350_, v_inst_351_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
return v_res_352_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem___redArg(lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_m_355_, lean_object* v_a_356_){
_start:
{
uint8_t v___x_357_; 
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_353_, v_inst_354_, v_m_355_, v_a_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___redArg___boxed(lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_m_360_, lean_object* v_a_361_){
_start:
{
uint8_t v_res_362_; lean_object* v_r_363_; 
v_res_362_ = l_Std_HashSet_instDecidableMem___redArg(v_inst_358_, v_inst_359_, v_m_360_, v_a_361_);
lean_dec_ref(v_m_360_);
v_r_363_ = lean_box(v_res_362_);
return v_r_363_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem(lean_object* v_00_u03b1_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_m_367_, lean_object* v_a_368_){
_start:
{
uint8_t v___x_369_; 
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_365_, v_inst_366_, v_m_367_, v_a_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___boxed(lean_object* v_00_u03b1_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_m_373_, lean_object* v_a_374_){
_start:
{
uint8_t v_res_375_; lean_object* v_r_376_; 
v_res_375_ = l_Std_HashSet_instDecidableMem(v_00_u03b1_370_, v_inst_371_, v_inst_372_, v_m_373_, v_a_374_);
lean_dec_ref(v_m_373_);
v_r_376_ = lean_box(v_res_375_);
return v_r_376_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase___redArg(lean_object* v_x_377_, lean_object* v_x_378_, lean_object* v_m_379_, lean_object* v_a_380_){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_377_, v_x_378_, v_m_379_, v_a_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase(lean_object* v_00_u03b1_382_, lean_object* v_x_383_, lean_object* v_x_384_, lean_object* v_m_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_383_, v_x_384_, v_m_385_, v_a_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg(lean_object* v_m_388_){
_start:
{
lean_object* v_size_389_; 
v_size_389_ = lean_ctor_get(v_m_388_, 0);
lean_inc(v_size_389_);
return v_size_389_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg___boxed(lean_object* v_m_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_HashSet_size___redArg(v_m_390_);
lean_dec_ref(v_m_390_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size(lean_object* v_00_u03b1_392_, lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_m_395_){
_start:
{
lean_object* v_size_396_; 
v_size_396_ = lean_ctor_get(v_m_395_, 0);
lean_inc(v_size_396_);
return v_size_396_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___boxed(lean_object* v_00_u03b1_397_, lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_m_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_HashSet_size(v_00_u03b1_397_, v_x_398_, v_x_399_, v_m_400_);
lean_dec_ref(v_m_400_);
lean_dec_ref(v_x_399_);
lean_dec_ref(v_x_398_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg(lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_m_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_402_, v_x_403_, v_m_404_, v_a_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg___boxed(lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_m_409_, lean_object* v_a_410_){
_start:
{
lean_object* v_res_411_; 
v_res_411_ = l_Std_HashSet_get_x3f___redArg(v_x_407_, v_x_408_, v_m_409_, v_a_410_);
lean_dec_ref(v_m_409_);
return v_res_411_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f(lean_object* v_00_u03b1_412_, lean_object* v_x_413_, lean_object* v_x_414_, lean_object* v_m_415_, lean_object* v_a_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_413_, v_x_414_, v_m_415_, v_a_416_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___boxed(lean_object* v_00_u03b1_418_, lean_object* v_x_419_, lean_object* v_x_420_, lean_object* v_m_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Std_HashSet_get_x3f(v_00_u03b1_418_, v_x_419_, v_x_420_, v_m_421_, v_a_422_);
lean_dec_ref(v_m_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg(lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_m_426_, lean_object* v_a_427_){
_start:
{
lean_object* v___x_428_; 
v___x_428_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_424_, v_inst_425_, v_m_426_, v_a_427_);
return v___x_428_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg___boxed(lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_m_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_HashSet_get___redArg(v_inst_429_, v_inst_430_, v_m_431_, v_a_432_);
lean_dec_ref(v_m_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get(lean_object* v_00_u03b1_434_, lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_m_437_, lean_object* v_a_438_, lean_object* v_h_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_435_, v_inst_436_, v_m_437_, v_a_438_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___boxed(lean_object* v_00_u03b1_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_m_444_, lean_object* v_a_445_, lean_object* v_h_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Std_HashSet_get(v_00_u03b1_441_, v_inst_442_, v_inst_443_, v_m_444_, v_a_445_, v_h_446_);
lean_dec_ref(v_m_444_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg(lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_m_450_, lean_object* v_a_451_, lean_object* v_fallback_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_448_, v_inst_449_, v_m_450_, v_a_451_, v_fallback_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg___boxed(lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_m_456_, lean_object* v_a_457_, lean_object* v_fallback_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_HashSet_getD___redArg(v_inst_454_, v_inst_455_, v_m_456_, v_a_457_, v_fallback_458_);
lean_dec(v_fallback_458_);
lean_dec_ref(v_m_456_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD(lean_object* v_00_u03b1_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_m_463_, lean_object* v_a_464_, lean_object* v_fallback_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_461_, v_inst_462_, v_m_463_, v_a_464_, v_fallback_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___boxed(lean_object* v_00_u03b1_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_m_470_, lean_object* v_a_471_, lean_object* v_fallback_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Std_HashSet_getD(v_00_u03b1_467_, v_inst_468_, v_inst_469_, v_m_470_, v_a_471_, v_fallback_472_);
lean_dec(v_fallback_472_);
lean_dec_ref(v_m_470_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg(lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_m_477_, lean_object* v_a_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_474_, v_inst_475_, v_inst_476_, v_m_477_, v_a_478_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg___boxed(lean_object* v_inst_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_m_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_HashSet_get_x21___redArg(v_inst_480_, v_inst_481_, v_inst_482_, v_m_483_, v_a_484_);
lean_dec_ref(v_m_483_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21(lean_object* v_00_u03b1_486_, lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_m_490_, lean_object* v_a_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_487_, v_inst_488_, v_inst_489_, v_m_490_, v_a_491_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___boxed(lean_object* v_00_u03b1_493_, lean_object* v_inst_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_m_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l_Std_HashSet_get_x21(v_00_u03b1_493_, v_inst_494_, v_inst_495_, v_inst_496_, v_m_497_, v_a_498_);
lean_dec_ref(v_m_497_);
return v_res_499_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty___redArg(lean_object* v_m_500_){
_start:
{
lean_object* v_size_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_size_501_ = lean_ctor_get(v_m_500_, 0);
v___x_502_ = lean_unsigned_to_nat(0u);
v___x_503_ = lean_nat_dec_eq(v_size_501_, v___x_502_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___redArg___boxed(lean_object* v_m_504_){
_start:
{
uint8_t v_res_505_; lean_object* v_r_506_; 
v_res_505_ = l_Std_HashSet_isEmpty___redArg(v_m_504_);
lean_dec_ref(v_m_504_);
v_r_506_ = lean_box(v_res_505_);
return v_r_506_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty(lean_object* v_00_u03b1_507_, lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_m_510_){
_start:
{
lean_object* v_size_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_size_511_ = lean_ctor_get(v_m_510_, 0);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_nat_dec_eq(v_size_511_, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___boxed(lean_object* v_00_u03b1_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_m_517_){
_start:
{
uint8_t v_res_518_; lean_object* v_r_519_; 
v_res_518_ = l_Std_HashSet_isEmpty(v_00_u03b1_514_, v_x_515_, v_x_516_, v_m_517_);
lean_dec_ref(v_m_517_);
lean_dec_ref(v_x_516_);
lean_dec_ref(v_x_515_);
v_r_519_ = lean_box(v_res_518_);
return v_r_519_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0(lean_object* v_a_520_, lean_object* v_b_521_, lean_object* v_d_522_){
_start:
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_523_, 0, v_a_520_);
lean_ctor_set(v___x_523_, 1, v_d_522_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__1(lean_object* v___x_524_, lean_object* v___f_525_, lean_object* v_l_526_, lean_object* v_acc_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_524_, v___f_525_, v_acc_527_, v_l_526_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg(lean_object* v_m_552_){
_start:
{
lean_object* v___x_553_; lean_object* v_buckets_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_553_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_554_ = lean_ctor_get(v_m_552_, 1);
lean_inc_ref(v_buckets_554_);
lean_dec_ref(v_m_552_);
v___x_555_ = lean_box(0);
v___x_556_ = lean_array_get_size(v_buckets_554_);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_nat_dec_lt(v___x_557_, v___x_556_);
if (v___x_558_ == 0)
{
lean_dec_ref(v_buckets_554_);
return v___x_555_;
}
else
{
lean_object* v___f_559_; size_t v___x_560_; size_t v___x_561_; lean_object* v___x_562_; 
v___f_559_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__11));
v___x_560_ = lean_usize_of_nat(v___x_556_);
v___x_561_ = ((size_t)0ULL);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_553_, v___f_559_, v_buckets_554_, v___x_560_, v___x_561_, v___x_555_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList(lean_object* v_00_u03b1_563_, lean_object* v_x_564_, lean_object* v_x_565_, lean_object* v_m_566_){
_start:
{
lean_object* v___x_567_; lean_object* v_buckets_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v___x_567_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_568_ = lean_ctor_get(v_m_566_, 1);
lean_inc_ref(v_buckets_568_);
lean_dec_ref(v_m_566_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_array_get_size(v_buckets_568_);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_nat_dec_lt(v___x_571_, v___x_570_);
if (v___x_572_ == 0)
{
lean_dec_ref(v_buckets_568_);
return v___x_569_;
}
else
{
lean_object* v___f_573_; size_t v___x_574_; size_t v___x_575_; lean_object* v___x_576_; 
v___f_573_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__11));
v___x_574_ = lean_usize_of_nat(v___x_570_);
v___x_575_ = ((size_t)0ULL);
v___x_576_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_567_, v___f_573_, v_buckets_568_, v___x_574_, v___x_575_, v___x_569_);
return v___x_576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___boxed(lean_object* v_00_u03b1_577_, lean_object* v_x_578_, lean_object* v_x_579_, lean_object* v_m_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_HashSet_toList(v_00_u03b1_577_, v_x_578_, v_x_579_, v_m_580_);
lean_dec_ref(v_x_579_);
lean_dec_ref(v_x_578_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg(lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_l_588_){
_start:
{
lean_object* v___f_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___f_589_ = ((lean_object*)(l_Std_HashSet_ofList___redArg___closed__1));
v___x_590_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_589_, v_inst_586_, v_inst_587_, v___x_590_, v_l_588_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList(lean_object* v_00_u03b1_592_, lean_object* v_inst_593_, lean_object* v_inst_594_, lean_object* v_l_595_){
_start:
{
lean_object* v___f_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
v___f_596_ = ((lean_object*)(l_Std_HashSet_ofList___redArg___closed__1));
v___x_597_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_598_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_596_, v_inst_593_, v_inst_594_, v___x_597_, v_l_595_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0(lean_object* v_f_599_, lean_object* v_b_600_, lean_object* v_a_601_, lean_object* v_x_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = lean_apply_2(v_f_599_, v_b_600_, v_a_601_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__1(lean_object* v_inst_604_, lean_object* v___f_605_, lean_object* v_acc_606_, lean_object* v_l_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_604_, v___f_605_, v_acc_606_, v_l_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg(lean_object* v_inst_609_, lean_object* v_f_610_, lean_object* v_init_611_, lean_object* v_b_612_){
_start:
{
lean_object* v_buckets_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_buckets_613_ = lean_ctor_get(v_b_612_, 1);
lean_inc_ref(v_buckets_613_);
lean_dec_ref(v_b_612_);
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = lean_array_get_size(v_buckets_613_);
v___x_616_ = lean_nat_dec_lt(v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v_toApplicative_617_; lean_object* v_toPure_618_; lean_object* v___x_619_; 
lean_dec_ref(v_buckets_613_);
lean_dec(v_f_610_);
v_toApplicative_617_ = lean_ctor_get(v_inst_609_, 0);
lean_inc_ref(v_toApplicative_617_);
lean_dec_ref(v_inst_609_);
v_toPure_618_ = lean_ctor_get(v_toApplicative_617_, 1);
lean_inc(v_toPure_618_);
lean_dec_ref(v_toApplicative_617_);
v___x_619_ = lean_apply_2(v_toPure_618_, lean_box(0), v_init_611_);
return v___x_619_;
}
else
{
lean_object* v___f_620_; lean_object* v___f_621_; uint8_t v___x_622_; 
v___f_620_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_620_, 0, v_f_610_);
lean_inc_ref(v_inst_609_);
v___f_621_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_621_, 0, v_inst_609_);
lean_closure_set(v___f_621_, 1, v___f_620_);
v___x_622_ = lean_nat_dec_le(v___x_615_, v___x_615_);
if (v___x_622_ == 0)
{
if (v___x_616_ == 0)
{
lean_object* v_toApplicative_623_; lean_object* v_toPure_624_; lean_object* v___x_625_; 
lean_dec_ref(v___f_621_);
lean_dec_ref(v_buckets_613_);
v_toApplicative_623_ = lean_ctor_get(v_inst_609_, 0);
lean_inc_ref(v_toApplicative_623_);
lean_dec_ref(v_inst_609_);
v_toPure_624_ = lean_ctor_get(v_toApplicative_623_, 1);
lean_inc(v_toPure_624_);
lean_dec_ref(v_toApplicative_623_);
v___x_625_ = lean_apply_2(v_toPure_624_, lean_box(0), v_init_611_);
return v___x_625_;
}
else
{
size_t v___x_626_; size_t v___x_627_; lean_object* v___x_628_; 
v___x_626_ = ((size_t)0ULL);
v___x_627_ = lean_usize_of_nat(v___x_615_);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_609_, v___f_621_, v_buckets_613_, v___x_626_, v___x_627_, v_init_611_);
return v___x_628_;
}
}
else
{
size_t v___x_629_; size_t v___x_630_; lean_object* v___x_631_; 
v___x_629_ = ((size_t)0ULL);
v___x_630_ = lean_usize_of_nat(v___x_615_);
v___x_631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_609_, v___f_621_, v_buckets_613_, v___x_629_, v___x_630_, v_init_611_);
return v___x_631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM(lean_object* v_00_u03b1_632_, lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_m_635_, lean_object* v_inst_636_, lean_object* v_00_u03b2_637_, lean_object* v_f_638_, lean_object* v_init_639_, lean_object* v_b_640_){
_start:
{
lean_object* v_buckets_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_buckets_641_ = lean_ctor_get(v_b_640_, 1);
lean_inc_ref(v_buckets_641_);
lean_dec_ref(v_b_640_);
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_array_get_size(v_buckets_641_);
v___x_644_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v_toApplicative_645_; lean_object* v_toPure_646_; lean_object* v___x_647_; 
lean_dec_ref(v_buckets_641_);
lean_dec(v_f_638_);
v_toApplicative_645_ = lean_ctor_get(v_inst_636_, 0);
lean_inc_ref(v_toApplicative_645_);
lean_dec_ref(v_inst_636_);
v_toPure_646_ = lean_ctor_get(v_toApplicative_645_, 1);
lean_inc(v_toPure_646_);
lean_dec_ref(v_toApplicative_645_);
v___x_647_ = lean_apply_2(v_toPure_646_, lean_box(0), v_init_639_);
return v___x_647_;
}
else
{
lean_object* v___f_648_; lean_object* v___f_649_; uint8_t v___x_650_; 
v___f_648_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_648_, 0, v_f_638_);
lean_inc_ref(v_inst_636_);
v___f_649_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_649_, 0, v_inst_636_);
lean_closure_set(v___f_649_, 1, v___f_648_);
v___x_650_ = lean_nat_dec_le(v___x_643_, v___x_643_);
if (v___x_650_ == 0)
{
if (v___x_644_ == 0)
{
lean_object* v_toApplicative_651_; lean_object* v_toPure_652_; lean_object* v___x_653_; 
lean_dec_ref(v___f_649_);
lean_dec_ref(v_buckets_641_);
v_toApplicative_651_ = lean_ctor_get(v_inst_636_, 0);
lean_inc_ref(v_toApplicative_651_);
lean_dec_ref(v_inst_636_);
v_toPure_652_ = lean_ctor_get(v_toApplicative_651_, 1);
lean_inc(v_toPure_652_);
lean_dec_ref(v_toApplicative_651_);
v___x_653_ = lean_apply_2(v_toPure_652_, lean_box(0), v_init_639_);
return v___x_653_;
}
else
{
size_t v___x_654_; size_t v___x_655_; lean_object* v___x_656_; 
v___x_654_ = ((size_t)0ULL);
v___x_655_ = lean_usize_of_nat(v___x_643_);
v___x_656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_636_, v___f_649_, v_buckets_641_, v___x_654_, v___x_655_, v_init_639_);
return v___x_656_;
}
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = ((size_t)0ULL);
v___x_658_ = lean_usize_of_nat(v___x_643_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_636_, v___f_649_, v_buckets_641_, v___x_657_, v___x_658_, v_init_639_);
return v___x_659_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___boxed(lean_object* v_00_u03b1_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_m_663_, lean_object* v_inst_664_, lean_object* v_00_u03b2_665_, lean_object* v_f_666_, lean_object* v_init_667_, lean_object* v_b_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_Std_HashSet_foldM(v_00_u03b1_660_, v_x_661_, v_x_662_, v_m_663_, v_inst_664_, v_00_u03b2_665_, v_f_666_, v_init_667_, v_b_668_);
lean_dec_ref(v_x_662_);
lean_dec_ref(v_x_661_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__0(lean_object* v_f_670_, lean_object* v_x1_671_, lean_object* v_x2_672_, lean_object* v_x3_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_apply_2(v_f_670_, v_x1_671_, v_x2_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__1(lean_object* v___x_675_, lean_object* v___f_676_, lean_object* v_acc_677_, lean_object* v_l_678_){
_start:
{
lean_object* v___x_679_; 
v___x_679_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_675_, v___f_676_, v_acc_677_, v_l_678_);
return v___x_679_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg(lean_object* v_f_680_, lean_object* v_init_681_, lean_object* v_m_682_){
_start:
{
lean_object* v___x_683_; lean_object* v_buckets_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v___x_683_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_684_ = lean_ctor_get(v_m_682_, 1);
lean_inc_ref(v_buckets_684_);
lean_dec_ref(v_m_682_);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_array_get_size(v_buckets_684_);
v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec_ref(v_buckets_684_);
lean_dec(v_f_680_);
return v_init_681_;
}
else
{
lean_object* v___f_688_; lean_object* v___f_689_; uint8_t v___x_690_; 
v___f_688_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_688_, 0, v_f_680_);
v___f_689_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_689_, 0, v___x_683_);
lean_closure_set(v___f_689_, 1, v___f_688_);
v___x_690_ = lean_nat_dec_le(v___x_686_, v___x_686_);
if (v___x_690_ == 0)
{
if (v___x_687_ == 0)
{
lean_dec_ref(v___f_689_);
lean_dec_ref(v_buckets_684_);
return v_init_681_;
}
else
{
size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___x_691_ = ((size_t)0ULL);
v___x_692_ = lean_usize_of_nat(v___x_686_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_683_, v___f_689_, v_buckets_684_, v___x_691_, v___x_692_, v_init_681_);
return v___x_693_;
}
}
else
{
size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((size_t)0ULL);
v___x_695_ = lean_usize_of_nat(v___x_686_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_683_, v___f_689_, v_buckets_684_, v___x_694_, v___x_695_, v_init_681_);
return v___x_696_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold(lean_object* v_00_u03b1_697_, lean_object* v_x_698_, lean_object* v_x_699_, lean_object* v_00_u03b2_700_, lean_object* v_f_701_, lean_object* v_init_702_, lean_object* v_m_703_){
_start:
{
lean_object* v___x_704_; lean_object* v_buckets_705_; lean_object* v___x_706_; lean_object* v___x_707_; uint8_t v___x_708_; 
v___x_704_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_705_ = lean_ctor_get(v_m_703_, 1);
lean_inc_ref(v_buckets_705_);
lean_dec_ref(v_m_703_);
v___x_706_ = lean_unsigned_to_nat(0u);
v___x_707_ = lean_array_get_size(v_buckets_705_);
v___x_708_ = lean_nat_dec_lt(v___x_706_, v___x_707_);
if (v___x_708_ == 0)
{
lean_dec_ref(v_buckets_705_);
lean_dec(v_f_701_);
return v_init_702_;
}
else
{
lean_object* v___f_709_; lean_object* v___f_710_; uint8_t v___x_711_; 
v___f_709_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_709_, 0, v_f_701_);
v___f_710_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_710_, 0, v___x_704_);
lean_closure_set(v___f_710_, 1, v___f_709_);
v___x_711_ = lean_nat_dec_le(v___x_707_, v___x_707_);
if (v___x_711_ == 0)
{
if (v___x_708_ == 0)
{
lean_dec_ref(v___f_710_);
lean_dec_ref(v_buckets_705_);
return v_init_702_;
}
else
{
size_t v___x_712_; size_t v___x_713_; lean_object* v___x_714_; 
v___x_712_ = ((size_t)0ULL);
v___x_713_ = lean_usize_of_nat(v___x_707_);
v___x_714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_704_, v___f_710_, v_buckets_705_, v___x_712_, v___x_713_, v_init_702_);
return v___x_714_;
}
}
else
{
size_t v___x_715_; size_t v___x_716_; lean_object* v___x_717_; 
v___x_715_ = ((size_t)0ULL);
v___x_716_ = lean_usize_of_nat(v___x_707_);
v___x_717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_704_, v___f_710_, v_buckets_705_, v___x_715_, v___x_716_, v_init_702_);
return v___x_717_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___boxed(lean_object* v_00_u03b1_718_, lean_object* v_x_719_, lean_object* v_x_720_, lean_object* v_00_u03b2_721_, lean_object* v_f_722_, lean_object* v_init_723_, lean_object* v_m_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Std_HashSet_fold(v_00_u03b1_718_, v_x_719_, v_x_720_, v_00_u03b2_721_, v_f_722_, v_init_723_, v_m_724_);
lean_dec_ref(v_x_720_);
lean_dec_ref(v_x_719_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0(lean_object* v_f_726_, lean_object* v_x_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = lean_apply_1(v_f_726_, v___y_728_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__1(lean_object* v_inst_731_, lean_object* v___f_732_, lean_object* v_x_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_735_ = lean_box(0);
v___x_736_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_731_, v___f_732_, v___x_735_, v___y_734_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg(lean_object* v_inst_737_, lean_object* v_f_738_, lean_object* v_b_739_){
_start:
{
lean_object* v_buckets_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_buckets_740_ = lean_ctor_get(v_b_739_, 1);
lean_inc_ref(v_buckets_740_);
lean_dec_ref(v_b_739_);
v___x_741_ = lean_unsigned_to_nat(0u);
v___x_742_ = lean_array_get_size(v_buckets_740_);
v___x_743_ = lean_box(0);
v___x_744_ = lean_nat_dec_lt(v___x_741_, v___x_742_);
if (v___x_744_ == 0)
{
lean_object* v_toApplicative_745_; lean_object* v_toPure_746_; lean_object* v___x_747_; 
lean_dec_ref(v_buckets_740_);
lean_dec(v_f_738_);
v_toApplicative_745_ = lean_ctor_get(v_inst_737_, 0);
lean_inc_ref(v_toApplicative_745_);
lean_dec_ref(v_inst_737_);
v_toPure_746_ = lean_ctor_get(v_toApplicative_745_, 1);
lean_inc(v_toPure_746_);
lean_dec_ref(v_toApplicative_745_);
v___x_747_ = lean_apply_2(v_toPure_746_, lean_box(0), v___x_743_);
return v___x_747_;
}
else
{
lean_object* v___f_748_; lean_object* v___f_749_; uint8_t v___x_750_; 
v___f_748_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_748_, 0, v_f_738_);
lean_inc_ref(v_inst_737_);
v___f_749_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_749_, 0, v_inst_737_);
lean_closure_set(v___f_749_, 1, v___f_748_);
v___x_750_ = lean_nat_dec_le(v___x_742_, v___x_742_);
if (v___x_750_ == 0)
{
if (v___x_744_ == 0)
{
lean_object* v_toApplicative_751_; lean_object* v_toPure_752_; lean_object* v___x_753_; 
lean_dec_ref(v___f_749_);
lean_dec_ref(v_buckets_740_);
v_toApplicative_751_ = lean_ctor_get(v_inst_737_, 0);
lean_inc_ref(v_toApplicative_751_);
lean_dec_ref(v_inst_737_);
v_toPure_752_ = lean_ctor_get(v_toApplicative_751_, 1);
lean_inc(v_toPure_752_);
lean_dec_ref(v_toApplicative_751_);
v___x_753_ = lean_apply_2(v_toPure_752_, lean_box(0), v___x_743_);
return v___x_753_;
}
else
{
size_t v___x_754_; size_t v___x_755_; lean_object* v___x_756_; 
v___x_754_ = ((size_t)0ULL);
v___x_755_ = lean_usize_of_nat(v___x_742_);
v___x_756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_737_, v___f_749_, v_buckets_740_, v___x_754_, v___x_755_, v___x_743_);
return v___x_756_;
}
}
else
{
size_t v___x_757_; size_t v___x_758_; lean_object* v___x_759_; 
v___x_757_ = ((size_t)0ULL);
v___x_758_ = lean_usize_of_nat(v___x_742_);
v___x_759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_737_, v___f_749_, v_buckets_740_, v___x_757_, v___x_758_, v___x_743_);
return v___x_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM(lean_object* v_00_u03b1_760_, lean_object* v_x_761_, lean_object* v_x_762_, lean_object* v_m_763_, lean_object* v_inst_764_, lean_object* v_f_765_, lean_object* v_b_766_){
_start:
{
lean_object* v_buckets_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_buckets_767_ = lean_ctor_get(v_b_766_, 1);
lean_inc_ref(v_buckets_767_);
lean_dec_ref(v_b_766_);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_array_get_size(v_buckets_767_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_nat_dec_lt(v___x_768_, v___x_769_);
if (v___x_771_ == 0)
{
lean_object* v_toApplicative_772_; lean_object* v_toPure_773_; lean_object* v___x_774_; 
lean_dec_ref(v_buckets_767_);
lean_dec(v_f_765_);
v_toApplicative_772_ = lean_ctor_get(v_inst_764_, 0);
lean_inc_ref(v_toApplicative_772_);
lean_dec_ref(v_inst_764_);
v_toPure_773_ = lean_ctor_get(v_toApplicative_772_, 1);
lean_inc(v_toPure_773_);
lean_dec_ref(v_toApplicative_772_);
v___x_774_ = lean_apply_2(v_toPure_773_, lean_box(0), v___x_770_);
return v___x_774_;
}
else
{
lean_object* v___f_775_; lean_object* v___f_776_; uint8_t v___x_777_; 
v___f_775_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_775_, 0, v_f_765_);
lean_inc_ref(v_inst_764_);
v___f_776_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_776_, 0, v_inst_764_);
lean_closure_set(v___f_776_, 1, v___f_775_);
v___x_777_ = lean_nat_dec_le(v___x_769_, v___x_769_);
if (v___x_777_ == 0)
{
if (v___x_771_ == 0)
{
lean_object* v_toApplicative_778_; lean_object* v_toPure_779_; lean_object* v___x_780_; 
lean_dec_ref(v___f_776_);
lean_dec_ref(v_buckets_767_);
v_toApplicative_778_ = lean_ctor_get(v_inst_764_, 0);
lean_inc_ref(v_toApplicative_778_);
lean_dec_ref(v_inst_764_);
v_toPure_779_ = lean_ctor_get(v_toApplicative_778_, 1);
lean_inc(v_toPure_779_);
lean_dec_ref(v_toApplicative_778_);
v___x_780_ = lean_apply_2(v_toPure_779_, lean_box(0), v___x_770_);
return v___x_780_;
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_of_nat(v___x_769_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_764_, v___f_776_, v_buckets_767_, v___x_781_, v___x_782_, v___x_770_);
return v___x_783_;
}
}
else
{
size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
v___x_784_ = ((size_t)0ULL);
v___x_785_ = lean_usize_of_nat(v___x_769_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_764_, v___f_776_, v_buckets_767_, v___x_784_, v___x_785_, v___x_770_);
return v___x_786_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___boxed(lean_object* v_00_u03b1_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_m_790_, lean_object* v_inst_791_, lean_object* v_f_792_, lean_object* v_b_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_HashSet_forM(v_00_u03b1_787_, v_x_788_, v_x_789_, v_m_790_, v_inst_791_, v_f_792_, v_b_793_);
lean_dec_ref(v_x_789_);
lean_dec_ref(v_x_788_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0(lean_object* v_f_795_, lean_object* v_a_796_, lean_object* v_x_797_, lean_object* v_acc_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = lean_apply_2(v_f_795_, v_a_796_, v_acc_798_);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__1(lean_object* v_inst_800_, lean_object* v___f_801_, lean_object* v_a_802_, lean_object* v_x_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_805_; 
v___x_805_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_800_, v___f_801_, v_a_802_, v___y_804_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg(lean_object* v_inst_806_, lean_object* v_f_807_, lean_object* v_init_808_, lean_object* v_b_809_){
_start:
{
lean_object* v_buckets_810_; lean_object* v___f_811_; lean_object* v___f_812_; size_t v_sz_813_; size_t v___x_814_; lean_object* v___x_815_; 
v_buckets_810_ = lean_ctor_get(v_b_809_, 1);
lean_inc_ref(v_buckets_810_);
lean_dec_ref(v_b_809_);
v___f_811_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_811_, 0, v_f_807_);
lean_inc_ref(v_inst_806_);
v___f_812_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_812_, 0, v_inst_806_);
lean_closure_set(v___f_812_, 1, v___f_811_);
v_sz_813_ = lean_array_size(v_buckets_810_);
v___x_814_ = ((size_t)0ULL);
v___x_815_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_806_, v_buckets_810_, v___f_812_, v_sz_813_, v___x_814_, v_init_808_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn(lean_object* v_00_u03b1_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_m_819_, lean_object* v_inst_820_, lean_object* v_00_u03b2_821_, lean_object* v_f_822_, lean_object* v_init_823_, lean_object* v_b_824_){
_start:
{
lean_object* v_buckets_825_; lean_object* v___f_826_; lean_object* v___f_827_; size_t v_sz_828_; size_t v___x_829_; lean_object* v___x_830_; 
v_buckets_825_ = lean_ctor_get(v_b_824_, 1);
lean_inc_ref(v_buckets_825_);
lean_dec_ref(v_b_824_);
v___f_826_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_826_, 0, v_f_822_);
lean_inc_ref(v_inst_820_);
v___f_827_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_827_, 0, v_inst_820_);
lean_closure_set(v___f_827_, 1, v___f_826_);
v_sz_828_ = lean_array_size(v_buckets_825_);
v___x_829_ = ((size_t)0ULL);
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_820_, v_buckets_825_, v___f_827_, v_sz_828_, v___x_829_, v_init_823_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___boxed(lean_object* v_00_u03b1_831_, lean_object* v_x_832_, lean_object* v_x_833_, lean_object* v_m_834_, lean_object* v_inst_835_, lean_object* v_00_u03b2_836_, lean_object* v_f_837_, lean_object* v_init_838_, lean_object* v_b_839_){
_start:
{
lean_object* v_res_840_; 
v_res_840_ = l_Std_HashSet_forIn(v_00_u03b1_831_, v_x_832_, v_x_833_, v_m_834_, v_inst_835_, v_00_u03b2_836_, v_f_837_, v_init_838_, v_b_839_);
lean_dec_ref(v_x_833_);
lean_dec_ref(v_x_832_);
return v_res_840_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg___lam__2(lean_object* v_inst_841_, lean_object* v_m_842_, lean_object* v_f_843_){
_start:
{
lean_object* v_buckets_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; uint8_t v___x_848_; 
v_buckets_844_ = lean_ctor_get(v_m_842_, 1);
lean_inc_ref(v_buckets_844_);
lean_dec_ref(v_m_842_);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_array_get_size(v_buckets_844_);
v___x_847_ = lean_box(0);
v___x_848_ = lean_nat_dec_lt(v___x_845_, v___x_846_);
if (v___x_848_ == 0)
{
lean_object* v_toApplicative_849_; lean_object* v_toPure_850_; lean_object* v___x_851_; 
lean_dec_ref(v_buckets_844_);
lean_dec(v_f_843_);
v_toApplicative_849_ = lean_ctor_get(v_inst_841_, 0);
lean_inc_ref(v_toApplicative_849_);
lean_dec_ref(v_inst_841_);
v_toPure_850_ = lean_ctor_get(v_toApplicative_849_, 1);
lean_inc(v_toPure_850_);
lean_dec_ref(v_toApplicative_849_);
v___x_851_ = lean_apply_2(v_toPure_850_, lean_box(0), v___x_847_);
return v___x_851_;
}
else
{
lean_object* v___f_852_; lean_object* v___f_853_; uint8_t v___x_854_; 
v___f_852_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_852_, 0, v_f_843_);
lean_inc_ref(v_inst_841_);
v___f_853_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_853_, 0, v_inst_841_);
lean_closure_set(v___f_853_, 1, v___f_852_);
v___x_854_ = lean_nat_dec_le(v___x_846_, v___x_846_);
if (v___x_854_ == 0)
{
if (v___x_848_ == 0)
{
lean_object* v_toApplicative_855_; lean_object* v_toPure_856_; lean_object* v___x_857_; 
lean_dec_ref(v___f_853_);
lean_dec_ref(v_buckets_844_);
v_toApplicative_855_ = lean_ctor_get(v_inst_841_, 0);
lean_inc_ref(v_toApplicative_855_);
lean_dec_ref(v_inst_841_);
v_toPure_856_ = lean_ctor_get(v_toApplicative_855_, 1);
lean_inc(v_toPure_856_);
lean_dec_ref(v_toApplicative_855_);
v___x_857_ = lean_apply_2(v_toPure_856_, lean_box(0), v___x_847_);
return v___x_857_;
}
else
{
size_t v___x_858_; size_t v___x_859_; lean_object* v___x_860_; 
v___x_858_ = ((size_t)0ULL);
v___x_859_ = lean_usize_of_nat(v___x_846_);
v___x_860_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_841_, v___f_853_, v_buckets_844_, v___x_858_, v___x_859_, v___x_847_);
return v___x_860_;
}
}
else
{
size_t v___x_861_; size_t v___x_862_; lean_object* v___x_863_; 
v___x_861_ = ((size_t)0ULL);
v___x_862_ = lean_usize_of_nat(v___x_846_);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_841_, v___f_853_, v_buckets_844_, v___x_861_, v___x_862_, v___x_847_);
return v___x_863_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg(lean_object* v_inst_864_){
_start:
{
lean_object* v___f_865_; 
v___f_865_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_865_, 0, v_inst_864_);
return v___f_865_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad(lean_object* v_00_u03b1_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_m_869_, lean_object* v_inst_870_){
_start:
{
lean_object* v___f_871_; 
v___f_871_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_871_, 0, v_inst_870_);
return v___f_871_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_m_875_, lean_object* v_inst_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_HashSet_instForMOfMonad(v_00_u03b1_872_, v_inst_873_, v_inst_874_, v_m_875_, v_inst_876_);
lean_dec_ref(v_inst_874_);
lean_dec_ref(v_inst_873_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg___lam__2(lean_object* v_inst_878_, lean_object* v_00_u03b2_879_, lean_object* v_m_880_, lean_object* v_init_881_, lean_object* v_f_882_){
_start:
{
lean_object* v_buckets_883_; lean_object* v___f_884_; lean_object* v___f_885_; size_t v_sz_886_; size_t v___x_887_; lean_object* v___x_888_; 
v_buckets_883_ = lean_ctor_get(v_m_880_, 1);
lean_inc_ref(v_buckets_883_);
lean_dec_ref(v_m_880_);
v___f_884_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_884_, 0, v_f_882_);
lean_inc_ref(v_inst_878_);
v___f_885_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_885_, 0, v_inst_878_);
lean_closure_set(v___f_885_, 1, v___f_884_);
v_sz_886_ = lean_array_size(v_buckets_883_);
v___x_887_ = ((size_t)0ULL);
v___x_888_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_878_, v_buckets_883_, v___f_885_, v_sz_886_, v___x_887_, v_init_881_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg(lean_object* v_inst_889_){
_start:
{
lean_object* v___f_890_; 
v___f_890_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_890_, 0, v_inst_889_);
return v___f_890_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad(lean_object* v_00_u03b1_891_, lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_m_894_, lean_object* v_inst_895_){
_start:
{
lean_object* v___f_896_; 
v___f_896_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_896_, 0, v_inst_895_);
return v___f_896_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_m_900_, lean_object* v_inst_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l_Std_HashSet_instForInOfMonad(v_00_u03b1_897_, v_inst_898_, v_inst_899_, v_m_900_, v_inst_901_);
lean_dec_ref(v_inst_899_);
lean_dec_ref(v_inst_898_);
return v_res_902_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_filter___redArg___lam__0(lean_object* v_f_903_, lean_object* v_a_904_, lean_object* v_x_905_){
_start:
{
lean_object* v___x_906_; uint8_t v___x_907_; 
v___x_906_ = lean_apply_1(v_f_903_, v_a_904_);
v___x_907_ = lean_unbox(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__0___boxed(lean_object* v_f_908_, lean_object* v_a_909_, lean_object* v_x_910_){
_start:
{
uint8_t v_res_911_; lean_object* v_r_912_; 
v_res_911_ = l_Std_HashSet_filter___redArg___lam__0(v_f_908_, v_a_909_, v_x_910_);
v_r_912_ = lean_box(v_res_911_);
return v_r_912_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg(lean_object* v_f_913_, lean_object* v_m_914_){
_start:
{
lean_object* v___f_915_; lean_object* v___x_916_; 
v___f_915_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_915_, 0, v_f_913_);
v___x_916_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_915_, v_m_914_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter(lean_object* v_00_u03b1_917_, lean_object* v_x_918_, lean_object* v_x_919_, lean_object* v_f_920_, lean_object* v_m_921_){
_start:
{
lean_object* v___f_922_; lean_object* v___x_923_; 
v___f_922_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_922_, 0, v_f_920_);
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_922_, v_m_921_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___boxed(lean_object* v_00_u03b1_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_f_927_, lean_object* v_m_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_HashSet_filter(v_00_u03b1_924_, v_x_925_, v_x_926_, v_f_927_, v_m_928_);
lean_dec_ref(v_x_926_);
lean_dec_ref(v_x_925_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg(lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_inst_932_, lean_object* v_m_933_, lean_object* v_l_934_){
_start:
{
lean_object* v___x_935_; 
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_932_, v_x_930_, v_x_931_, v_m_933_, v_l_934_);
return v___x_935_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany(lean_object* v_00_u03b1_936_, lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_00_u03c1_939_, lean_object* v_inst_940_, lean_object* v_m_941_, lean_object* v_l_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_940_, v_x_937_, v_x_938_, v_m_941_, v_l_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0(lean_object* v_x1_944_, lean_object* v_x2_945_, lean_object* v_x3_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = lean_array_push(v_x1_944_, v_x2_945_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__1(lean_object* v___x_948_, lean_object* v___f_949_, lean_object* v_acc_950_, lean_object* v_l_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_948_, v___f_949_, v_acc_950_, v_l_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg(lean_object* v_m_957_){
_start:
{
lean_object* v_size_958_; lean_object* v_buckets_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_size_958_ = lean_ctor_get(v_m_957_, 0);
lean_inc(v_size_958_);
v_buckets_959_ = lean_ctor_get(v_m_957_, 1);
lean_inc_ref(v_buckets_959_);
lean_dec_ref(v_m_957_);
v___x_960_ = lean_mk_empty_array_with_capacity(v_size_958_);
lean_dec(v_size_958_);
v___x_961_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___x_962_ = lean_unsigned_to_nat(0u);
v___x_963_ = lean_array_get_size(v_buckets_959_);
v___x_964_ = lean_nat_dec_lt(v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
lean_dec_ref(v_buckets_959_);
return v___x_960_;
}
else
{
lean_object* v___f_965_; uint8_t v___x_966_; 
v___f_965_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__1));
v___x_966_ = lean_nat_dec_le(v___x_963_, v___x_963_);
if (v___x_966_ == 0)
{
if (v___x_964_ == 0)
{
lean_dec_ref(v_buckets_959_);
return v___x_960_;
}
else
{
size_t v___x_967_; size_t v___x_968_; lean_object* v___x_969_; 
v___x_967_ = ((size_t)0ULL);
v___x_968_ = lean_usize_of_nat(v___x_963_);
v___x_969_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_961_, v___f_965_, v_buckets_959_, v___x_967_, v___x_968_, v___x_960_);
return v___x_969_;
}
}
else
{
size_t v___x_970_; size_t v___x_971_; lean_object* v___x_972_; 
v___x_970_ = ((size_t)0ULL);
v___x_971_ = lean_usize_of_nat(v___x_963_);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_961_, v___f_965_, v_buckets_959_, v___x_970_, v___x_971_, v___x_960_);
return v___x_972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray(lean_object* v_00_u03b1_973_, lean_object* v_x_974_, lean_object* v_x_975_, lean_object* v_m_976_){
_start:
{
lean_object* v_size_977_; lean_object* v_buckets_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; uint8_t v___x_983_; 
v_size_977_ = lean_ctor_get(v_m_976_, 0);
lean_inc(v_size_977_);
v_buckets_978_ = lean_ctor_get(v_m_976_, 1);
lean_inc_ref(v_buckets_978_);
lean_dec_ref(v_m_976_);
v___x_979_ = lean_mk_empty_array_with_capacity(v_size_977_);
lean_dec(v_size_977_);
v___x_980_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_array_get_size(v_buckets_978_);
v___x_983_ = lean_nat_dec_lt(v___x_981_, v___x_982_);
if (v___x_983_ == 0)
{
lean_dec_ref(v_buckets_978_);
return v___x_979_;
}
else
{
lean_object* v___f_984_; uint8_t v___x_985_; 
v___f_984_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__1));
v___x_985_ = lean_nat_dec_le(v___x_982_, v___x_982_);
if (v___x_985_ == 0)
{
if (v___x_983_ == 0)
{
lean_dec_ref(v_buckets_978_);
return v___x_979_;
}
else
{
size_t v___x_986_; size_t v___x_987_; lean_object* v___x_988_; 
v___x_986_ = ((size_t)0ULL);
v___x_987_ = lean_usize_of_nat(v___x_982_);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_980_, v___f_984_, v_buckets_978_, v___x_986_, v___x_987_, v___x_979_);
return v___x_988_;
}
}
else
{
size_t v___x_989_; size_t v___x_990_; lean_object* v___x_991_; 
v___x_989_ = ((size_t)0ULL);
v___x_990_ = lean_usize_of_nat(v___x_982_);
v___x_991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_980_, v___f_984_, v_buckets_978_, v___x_989_, v___x_990_, v___x_979_);
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___boxed(lean_object* v_00_u03b1_992_, lean_object* v_x_993_, lean_object* v_x_994_, lean_object* v_m_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l_Std_HashSet_toArray(v_00_u03b1_992_, v_x_993_, v_x_994_, v_m_995_);
lean_dec_ref(v_x_994_);
lean_dec_ref(v_x_993_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0(lean_object* v_p_997_, lean_object* v___x_998_, lean_object* v___x_999_, lean_object* v_a_1000_, lean_object* v_b_1001_, lean_object* v_acc_1002_){
_start:
{
lean_object* v___x_1003_; uint8_t v___x_1004_; 
v___x_1003_ = lean_apply_1(v_p_997_, v_a_1000_);
v___x_1004_ = lean_unbox(v___x_1003_);
if (v___x_1004_ == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec_ref(v___x_999_);
v___x_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1003_);
v___x_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v___x_998_);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1008_, 0, v___x_999_);
return v___x_1008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0___boxed(lean_object* v_p_1009_, lean_object* v___x_1010_, lean_object* v___x_1011_, lean_object* v_a_1012_, lean_object* v_b_1013_, lean_object* v_acc_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_Std_HashSet_all___redArg___lam__0(v_p_1009_, v___x_1010_, v___x_1011_, v_a_1012_, v_b_1013_, v_acc_1014_);
lean_dec_ref(v_acc_1014_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__1(lean_object* v___x_1016_, lean_object* v___f_1017_, lean_object* v_a_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_){
_start:
{
lean_object* v___x_1021_; 
v___x_1021_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1016_, v___f_1017_, v_a_1018_, v___y_1020_);
return v___x_1021_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all___redArg(lean_object* v_m_1025_, lean_object* v_p_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v_buckets_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___f_1031_; lean_object* v___f_1032_; size_t v_sz_1033_; size_t v___x_1034_; lean_object* v___x_1035_; lean_object* v_fst_1036_; 
v___x_1027_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1028_ = lean_ctor_get(v_m_1025_, 1);
lean_inc_ref(v_buckets_1028_);
lean_dec_ref(v_m_1025_);
v___x_1029_ = lean_box(0);
v___x_1030_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1031_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1031_, 0, v_p_1026_);
lean_closure_set(v___f_1031_, 1, v___x_1029_);
lean_closure_set(v___f_1031_, 2, v___x_1030_);
v___f_1032_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1032_, 0, v___x_1027_);
lean_closure_set(v___f_1032_, 1, v___f_1031_);
v_sz_1033_ = lean_array_size(v_buckets_1028_);
v___x_1034_ = ((size_t)0ULL);
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1027_, v_buckets_1028_, v___f_1032_, v_sz_1033_, v___x_1034_, v___x_1030_);
v_fst_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_fst_1036_);
lean_dec(v___x_1035_);
if (lean_obj_tag(v_fst_1036_) == 0)
{
uint8_t v___x_1037_; 
v___x_1037_ = 1;
return v___x_1037_;
}
else
{
lean_object* v_val_1038_; uint8_t v___x_1039_; 
v_val_1038_ = lean_ctor_get(v_fst_1036_, 0);
lean_inc(v_val_1038_);
lean_dec_ref(v_fst_1036_);
v___x_1039_ = lean_unbox(v_val_1038_);
lean_dec(v_val_1038_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___boxed(lean_object* v_m_1040_, lean_object* v_p_1041_){
_start:
{
uint8_t v_res_1042_; lean_object* v_r_1043_; 
v_res_1042_ = l_Std_HashSet_all___redArg(v_m_1040_, v_p_1041_);
v_r_1043_ = lean_box(v_res_1042_);
return v_r_1043_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all(lean_object* v_00_u03b1_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_, lean_object* v_m_1047_, lean_object* v_p_1048_){
_start:
{
lean_object* v___x_1049_; lean_object* v_buckets_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___f_1053_; lean_object* v___f_1054_; size_t v_sz_1055_; size_t v___x_1056_; lean_object* v___x_1057_; lean_object* v_fst_1058_; 
v___x_1049_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1050_ = lean_ctor_get(v_m_1047_, 1);
lean_inc_ref(v_buckets_1050_);
lean_dec_ref(v_m_1047_);
v___x_1051_ = lean_box(0);
v___x_1052_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1053_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1053_, 0, v_p_1048_);
lean_closure_set(v___f_1053_, 1, v___x_1051_);
lean_closure_set(v___f_1053_, 2, v___x_1052_);
v___f_1054_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1054_, 0, v___x_1049_);
lean_closure_set(v___f_1054_, 1, v___f_1053_);
v_sz_1055_ = lean_array_size(v_buckets_1050_);
v___x_1056_ = ((size_t)0ULL);
v___x_1057_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1049_, v_buckets_1050_, v___f_1054_, v_sz_1055_, v___x_1056_, v___x_1052_);
v_fst_1058_ = lean_ctor_get(v___x_1057_, 0);
lean_inc(v_fst_1058_);
lean_dec(v___x_1057_);
if (lean_obj_tag(v_fst_1058_) == 0)
{
uint8_t v___x_1059_; 
v___x_1059_ = 1;
return v___x_1059_;
}
else
{
lean_object* v_val_1060_; uint8_t v___x_1061_; 
v_val_1060_ = lean_ctor_get(v_fst_1058_, 0);
lean_inc(v_val_1060_);
lean_dec_ref(v_fst_1058_);
v___x_1061_ = lean_unbox(v_val_1060_);
lean_dec(v_val_1060_);
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___boxed(lean_object* v_00_u03b1_1062_, lean_object* v_x_1063_, lean_object* v_x_1064_, lean_object* v_m_1065_, lean_object* v_p_1066_){
_start:
{
uint8_t v_res_1067_; lean_object* v_r_1068_; 
v_res_1067_ = l_Std_HashSet_all(v_00_u03b1_1062_, v_x_1063_, v_x_1064_, v_m_1065_, v_p_1066_);
lean_dec_ref(v_x_1064_);
lean_dec_ref(v_x_1063_);
v_r_1068_ = lean_box(v_res_1067_);
return v_r_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0(lean_object* v_p_1069_, lean_object* v___x_1070_, lean_object* v___x_1071_, lean_object* v_a_1072_, lean_object* v_b_1073_, lean_object* v_acc_1074_){
_start:
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = lean_apply_1(v_p_1069_, v_a_1072_);
v___x_1076_ = lean_unbox(v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1070_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
lean_dec_ref(v___x_1070_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1075_);
v___x_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1071_);
v___x_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1080_, 0, v___x_1079_);
return v___x_1080_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0___boxed(lean_object* v_p_1081_, lean_object* v___x_1082_, lean_object* v___x_1083_, lean_object* v_a_1084_, lean_object* v_b_1085_, lean_object* v_acc_1086_){
_start:
{
lean_object* v_res_1087_; 
v_res_1087_ = l_Std_HashSet_any___redArg___lam__0(v_p_1081_, v___x_1082_, v___x_1083_, v_a_1084_, v_b_1085_, v_acc_1086_);
lean_dec_ref(v_acc_1086_);
return v_res_1087_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any___redArg(lean_object* v_m_1088_, lean_object* v_p_1089_){
_start:
{
lean_object* v___x_1090_; lean_object* v_buckets_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___f_1094_; lean_object* v___f_1095_; size_t v_sz_1096_; size_t v___x_1097_; lean_object* v___x_1098_; lean_object* v_fst_1099_; 
v___x_1090_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1091_ = lean_ctor_get(v_m_1088_, 1);
lean_inc_ref(v_buckets_1091_);
lean_dec_ref(v_m_1088_);
v___x_1092_ = lean_box(0);
v___x_1093_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1094_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1094_, 0, v_p_1089_);
lean_closure_set(v___f_1094_, 1, v___x_1093_);
lean_closure_set(v___f_1094_, 2, v___x_1092_);
v___f_1095_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1095_, 0, v___x_1090_);
lean_closure_set(v___f_1095_, 1, v___f_1094_);
v_sz_1096_ = lean_array_size(v_buckets_1091_);
v___x_1097_ = ((size_t)0ULL);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1090_, v_buckets_1091_, v___f_1095_, v_sz_1096_, v___x_1097_, v___x_1093_);
v_fst_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_fst_1099_);
lean_dec(v___x_1098_);
if (lean_obj_tag(v_fst_1099_) == 0)
{
uint8_t v___x_1100_; 
v___x_1100_ = 0;
return v___x_1100_;
}
else
{
lean_object* v_val_1101_; uint8_t v___x_1102_; 
v_val_1101_ = lean_ctor_get(v_fst_1099_, 0);
lean_inc(v_val_1101_);
lean_dec_ref(v_fst_1099_);
v___x_1102_ = lean_unbox(v_val_1101_);
lean_dec(v_val_1101_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___boxed(lean_object* v_m_1103_, lean_object* v_p_1104_){
_start:
{
uint8_t v_res_1105_; lean_object* v_r_1106_; 
v_res_1105_ = l_Std_HashSet_any___redArg(v_m_1103_, v_p_1104_);
v_r_1106_ = lean_box(v_res_1105_);
return v_r_1106_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any(lean_object* v_00_u03b1_1107_, lean_object* v_x_1108_, lean_object* v_x_1109_, lean_object* v_m_1110_, lean_object* v_p_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v_buckets_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___f_1116_; lean_object* v___f_1117_; size_t v_sz_1118_; size_t v___x_1119_; lean_object* v___x_1120_; lean_object* v_fst_1121_; 
v___x_1112_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1113_ = lean_ctor_get(v_m_1110_, 1);
lean_inc_ref(v_buckets_1113_);
lean_dec_ref(v_m_1110_);
v___x_1114_ = lean_box(0);
v___x_1115_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1116_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1116_, 0, v_p_1111_);
lean_closure_set(v___f_1116_, 1, v___x_1115_);
lean_closure_set(v___f_1116_, 2, v___x_1114_);
v___f_1117_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1117_, 0, v___x_1112_);
lean_closure_set(v___f_1117_, 1, v___f_1116_);
v_sz_1118_ = lean_array_size(v_buckets_1113_);
v___x_1119_ = ((size_t)0ULL);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1112_, v_buckets_1113_, v___f_1117_, v_sz_1118_, v___x_1119_, v___x_1115_);
v_fst_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_fst_1121_);
lean_dec(v___x_1120_);
if (lean_obj_tag(v_fst_1121_) == 0)
{
uint8_t v___x_1122_; 
v___x_1122_ = 0;
return v___x_1122_;
}
else
{
lean_object* v_val_1123_; uint8_t v___x_1124_; 
v_val_1123_ = lean_ctor_get(v_fst_1121_, 0);
lean_inc(v_val_1123_);
lean_dec_ref(v_fst_1121_);
v___x_1124_ = lean_unbox(v_val_1123_);
lean_dec(v_val_1123_);
return v___x_1124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_x_1126_, lean_object* v_x_1127_, lean_object* v_m_1128_, lean_object* v_p_1129_){
_start:
{
uint8_t v_res_1130_; lean_object* v_r_1131_; 
v_res_1130_ = l_Std_HashSet_any(v_00_u03b1_1125_, v_x_1126_, v_x_1127_, v_m_1128_, v_p_1129_);
lean_dec_ref(v_x_1127_);
lean_dec_ref(v_x_1126_);
v_r_1131_ = lean_box(v_res_1130_);
return v_r_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0(lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_a_1134_, lean_object* v_b_1135_, lean_object* v_acc_1136_){
_start:
{
lean_object* v_r_1137_; lean_object* v___x_1138_; 
v_r_1137_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1132_, v_inst_1133_, v_acc_1136_, v_a_1134_, v_b_1135_);
v___x_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1138_, 0, v_r_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__1(lean_object* v___x_1139_, lean_object* v___f_1140_, lean_object* v_a_1141_, lean_object* v_x_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1139_, v___f_1140_, v_a_1141_, v___y_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg(lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_m_u2081_1149_, lean_object* v_m_u2082_1150_){
_start:
{
lean_object* v_size_1151_; lean_object* v_buckets_1152_; lean_object* v_size_1153_; uint8_t v___x_1154_; 
v_size_1151_ = lean_ctor_get(v_m_u2081_1149_, 0);
v_buckets_1152_ = lean_ctor_get(v_m_u2081_1149_, 1);
v_size_1153_ = lean_ctor_get(v_m_u2082_1150_, 0);
v___x_1154_ = lean_nat_dec_le(v_size_1151_, v_size_1153_);
if (v___x_1154_ == 0)
{
lean_object* v___f_1155_; lean_object* v___x_1156_; 
v___f_1155_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1156_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1155_, v_inst_1147_, v_inst_1148_, v_m_u2081_1149_, v_m_u2082_1150_);
return v___x_1156_;
}
else
{
lean_object* v___f_1157_; lean_object* v___x_1158_; lean_object* v___f_1159_; size_t v_sz_1160_; size_t v___x_1161_; lean_object* v___x_1162_; 
lean_inc_ref(v_buckets_1152_);
lean_dec_ref(v_m_u2081_1149_);
v___f_1157_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1157_, 0, v_inst_1147_);
lean_closure_set(v___f_1157_, 1, v_inst_1148_);
v___x_1158_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___f_1159_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1159_, 0, v___x_1158_);
lean_closure_set(v___f_1159_, 1, v___f_1157_);
v_sz_1160_ = lean_array_size(v_buckets_1152_);
v___x_1161_ = ((size_t)0ULL);
v___x_1162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1158_, v_buckets_1152_, v___f_1159_, v_sz_1160_, v___x_1161_, v_m_u2082_1150_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union(lean_object* v_00_u03b1_1163_, lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_m_u2081_1166_, lean_object* v_m_u2082_1167_){
_start:
{
lean_object* v_size_1168_; lean_object* v_buckets_1169_; lean_object* v_size_1170_; uint8_t v___x_1171_; 
v_size_1168_ = lean_ctor_get(v_m_u2081_1166_, 0);
v_buckets_1169_ = lean_ctor_get(v_m_u2081_1166_, 1);
v_size_1170_ = lean_ctor_get(v_m_u2082_1167_, 0);
v___x_1171_ = lean_nat_dec_le(v_size_1168_, v_size_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___f_1172_; lean_object* v___x_1173_; 
v___f_1172_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1173_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1172_, v_inst_1164_, v_inst_1165_, v_m_u2081_1166_, v_m_u2082_1167_);
return v___x_1173_;
}
else
{
lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___f_1176_; size_t v_sz_1177_; size_t v___x_1178_; lean_object* v___x_1179_; 
lean_inc_ref(v_buckets_1169_);
lean_dec_ref(v_m_u2081_1166_);
v___f_1174_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1174_, 0, v_inst_1164_);
lean_closure_set(v___f_1174_, 1, v_inst_1165_);
v___x_1175_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___f_1176_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1176_, 0, v___x_1175_);
lean_closure_set(v___f_1176_, 1, v___f_1174_);
v_sz_1177_ = lean_array_size(v_buckets_1169_);
v___x_1178_ = ((size_t)0ULL);
v___x_1179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1175_, v_buckets_1169_, v___f_1176_, v_sz_1177_, v___x_1178_, v_m_u2082_1167_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion___redArg(lean_object* v_inst_1180_, lean_object* v_inst_1181_){
_start:
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1182_, 0, lean_box(0));
lean_closure_set(v___x_1182_, 1, v_inst_1180_);
lean_closure_set(v___x_1182_, 2, v_inst_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion(lean_object* v_00_u03b1_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1186_, 0, lean_box(0));
lean_closure_set(v___x_1186_, 1, v_inst_1184_);
lean_closure_set(v___x_1186_, 2, v_inst_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter___redArg(lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_m_u2081_1189_, lean_object* v_m_u2082_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1187_, v_inst_1188_, v_m_u2081_1189_, v_m_u2082_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter(lean_object* v_00_u03b1_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_m_u2081_1195_, lean_object* v_m_u2082_1196_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1193_, v_inst_1194_, v_m_u2081_1195_, v_m_u2082_1196_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter___redArg(lean_object* v_inst_1198_, lean_object* v_inst_1199_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1200_, 0, lean_box(0));
lean_closure_set(v___x_1200_, 1, v_inst_1198_);
lean_closure_set(v___x_1200_, 2, v_inst_1199_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter(lean_object* v_00_u03b1_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1204_, 0, lean_box(0));
lean_closure_set(v___x_1204_, 1, v_inst_1202_);
lean_closure_set(v___x_1204_, 2, v_inst_1203_);
return v___x_1204_;
}
}
static lean_object* _init_l_Std_HashSet_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___f_1206_; 
v___x_1205_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1206_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1206_, 0, v___x_1205_);
return v___f_1206_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq___redArg(lean_object* v_x_1207_, lean_object* v_inst_1208_, lean_object* v_m_u2081_1209_, lean_object* v_m_u2082_1210_){
_start:
{
lean_object* v___f_1211_; uint8_t v___x_1212_; 
v___f_1211_ = lean_obj_once(&l_Std_HashSet_beq___redArg___closed__0, &l_Std_HashSet_beq___redArg___closed__0_once, _init_l_Std_HashSet_beq___redArg___closed__0);
v___x_1212_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1208_, v_x_1207_, v___f_1211_, v_m_u2081_1209_, v_m_u2082_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___redArg___boxed(lean_object* v_x_1213_, lean_object* v_inst_1214_, lean_object* v_m_u2081_1215_, lean_object* v_m_u2082_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = l_Std_HashSet_beq___redArg(v_x_1213_, v_inst_1214_, v_m_u2081_1215_, v_m_u2082_1216_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq(lean_object* v_00_u03b1_1219_, lean_object* v_x_1220_, lean_object* v_inst_1221_, lean_object* v_m_u2081_1222_, lean_object* v_m_u2082_1223_){
_start:
{
uint8_t v___x_1224_; 
v___x_1224_ = l_Std_HashSet_beq___redArg(v_x_1220_, v_inst_1221_, v_m_u2081_1222_, v_m_u2082_1223_);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___boxed(lean_object* v_00_u03b1_1225_, lean_object* v_x_1226_, lean_object* v_inst_1227_, lean_object* v_m_u2081_1228_, lean_object* v_m_u2082_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l_Std_HashSet_beq(v_00_u03b1_1225_, v_x_1226_, v_inst_1227_, v_m_u2081_1228_, v_m_u2082_1229_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq___redArg(lean_object* v_x_1232_, lean_object* v_inst_1233_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1234_, 0, lean_box(0));
lean_closure_set(v___x_1234_, 1, v_x_1232_);
lean_closure_set(v___x_1234_, 2, v_inst_1233_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq(lean_object* v_00_u03b1_1235_, lean_object* v_x_1236_, lean_object* v_inst_1237_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1238_, 0, lean_box(0));
lean_closure_set(v___x_1238_, 1, v_x_1236_);
lean_closure_set(v___x_1238_, 2, v_inst_1237_);
return v___x_1238_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_diff___redArg___lam__0(lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_m_u2082_1241_, uint8_t v___x_1242_, lean_object* v_k_1243_, lean_object* v_x_1244_){
_start:
{
uint8_t v___x_1245_; 
v___x_1245_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1239_, v_inst_1240_, v_m_u2082_1241_, v_k_1243_);
if (v___x_1245_ == 0)
{
return v___x_1242_;
}
else
{
uint8_t v___x_1246_; 
v___x_1246_ = 0;
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg___lam__0___boxed(lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_m_u2082_1249_, lean_object* v___x_1250_, lean_object* v_k_1251_, lean_object* v_x_1252_){
_start:
{
uint8_t v___x_83__boxed_1253_; uint8_t v_res_1254_; lean_object* v_r_1255_; 
v___x_83__boxed_1253_ = lean_unbox(v___x_1250_);
v_res_1254_ = l_Std_HashSet_diff___redArg___lam__0(v_inst_1247_, v_inst_1248_, v_m_u2082_1249_, v___x_83__boxed_1253_, v_k_1251_, v_x_1252_);
lean_dec_ref(v_m_u2082_1249_);
v_r_1255_ = lean_box(v_res_1254_);
return v_r_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg(lean_object* v_inst_1256_, lean_object* v_inst_1257_, lean_object* v_m_u2081_1258_, lean_object* v_m_u2082_1259_){
_start:
{
lean_object* v_size_1260_; lean_object* v_size_1261_; uint8_t v___x_1262_; 
v_size_1260_ = lean_ctor_get(v_m_u2081_1258_, 0);
v_size_1261_ = lean_ctor_get(v_m_u2082_1259_, 0);
v___x_1262_ = lean_nat_dec_le(v_size_1260_, v_size_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___f_1263_; lean_object* v___x_1264_; 
v___f_1263_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1264_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1263_, v_inst_1256_, v_inst_1257_, v_m_u2081_1258_, v_m_u2082_1259_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___f_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_box(v___x_1262_);
v___f_1266_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1266_, 0, v_inst_1256_);
lean_closure_set(v___f_1266_, 1, v_inst_1257_);
lean_closure_set(v___f_1266_, 2, v_m_u2082_1259_);
lean_closure_set(v___f_1266_, 3, v___x_1265_);
v___x_1267_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1266_, v_m_u2081_1258_);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff(lean_object* v_00_u03b1_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_m_u2081_1271_, lean_object* v_m_u2082_1272_){
_start:
{
lean_object* v_size_1273_; lean_object* v_size_1274_; uint8_t v___x_1275_; 
v_size_1273_ = lean_ctor_get(v_m_u2081_1271_, 0);
v_size_1274_ = lean_ctor_get(v_m_u2082_1272_, 0);
v___x_1275_ = lean_nat_dec_le(v_size_1273_, v_size_1274_);
if (v___x_1275_ == 0)
{
lean_object* v___f_1276_; lean_object* v___x_1277_; 
v___f_1276_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1277_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1276_, v_inst_1269_, v_inst_1270_, v_m_u2081_1271_, v_m_u2082_1272_);
return v___x_1277_;
}
else
{
lean_object* v___x_1278_; lean_object* v___f_1279_; lean_object* v___x_1280_; 
v___x_1278_ = lean_box(v___x_1275_);
v___f_1279_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1279_, 0, v_inst_1269_);
lean_closure_set(v___f_1279_, 1, v_inst_1270_);
lean_closure_set(v___f_1279_, 2, v_m_u2082_1272_);
lean_closure_set(v___f_1279_, 3, v___x_1278_);
v___x_1280_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1279_, v_m_u2081_1271_);
return v___x_1280_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff___redArg(lean_object* v_inst_1281_, lean_object* v_inst_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1283_, 0, lean_box(0));
lean_closure_set(v___x_1283_, 1, v_inst_1281_);
lean_closure_set(v___x_1283_, 2, v_inst_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff(lean_object* v_00_u03b1_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_){
_start:
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1287_, 0, lean_box(0));
lean_closure_set(v___x_1287_, 1, v_inst_1285_);
lean_closure_set(v___x_1287_, 2, v_inst_1286_);
return v___x_1287_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__0(lean_object* v_f_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_, lean_object* v_x1_1291_, lean_object* v_x2_1292_, lean_object* v_x3_1293_){
_start:
{
lean_object* v_fst_1294_; lean_object* v_snd_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1309_; 
v_fst_1294_ = lean_ctor_get(v_x1_1291_, 0);
v_snd_1295_ = lean_ctor_get(v_x1_1291_, 1);
v_isSharedCheck_1309_ = !lean_is_exclusive(v_x1_1291_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1297_ = v_x1_1291_;
v_isShared_1298_ = v_isSharedCheck_1309_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_snd_1295_);
lean_inc(v_fst_1294_);
lean_dec(v_x1_1291_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1309_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
lean_inc(v_x2_1292_);
v___x_1299_ = lean_apply_1(v_f_1288_, v_x2_1292_);
v___x_1300_ = lean_unbox(v___x_1299_);
if (v___x_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1289_, v_x_1290_, v_snd_1295_, v_x2_1292_, v_x3_1293_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 1, v___x_1301_);
v___x_1303_ = v___x_1297_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_fst_1294_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1289_, v_x_1290_, v_fst_1294_, v_x2_1292_, v_x3_1293_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 0, v___x_1305_);
v___x_1307_ = v___x_1297_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1305_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v_snd_1295_);
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
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__1(lean_object* v___x_1310_, lean_object* v___f_1311_, lean_object* v_acc_1312_, lean_object* v_l_1313_){
_start:
{
lean_object* v___x_1314_; 
v___x_1314_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1310_, v___f_1311_, v_acc_1312_, v_l_1313_);
return v___x_1314_;
}
}
static lean_object* _init_l_Std_HashSet_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1315_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v___x_1315_);
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg(lean_object* v_x_1317_, lean_object* v_x_1318_, lean_object* v_f_1319_, lean_object* v_m_1320_){
_start:
{
lean_object* v___y_1322_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v_buckets_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1332_ = lean_unsigned_to_nat(0u);
v___x_1333_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1334_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1335_ = lean_ctor_get(v_m_1320_, 1);
lean_inc_ref(v_buckets_1335_);
lean_dec_ref(v_m_1320_);
v___x_1336_ = lean_array_get_size(v_buckets_1335_);
v___x_1337_ = lean_nat_dec_lt(v___x_1332_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_dec_ref(v_buckets_1335_);
lean_dec_ref(v_f_1319_);
lean_dec_ref(v_x_1318_);
lean_dec_ref(v_x_1317_);
return v___x_1333_;
}
else
{
lean_object* v___f_1338_; lean_object* v___f_1339_; uint8_t v___x_1340_; 
v___f_1338_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1338_, 0, v_f_1319_);
lean_closure_set(v___f_1338_, 1, v_x_1317_);
lean_closure_set(v___f_1338_, 2, v_x_1318_);
v___f_1339_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1339_, 0, v___x_1334_);
lean_closure_set(v___f_1339_, 1, v___f_1338_);
v___x_1340_ = lean_nat_dec_le(v___x_1336_, v___x_1336_);
if (v___x_1340_ == 0)
{
if (v___x_1337_ == 0)
{
lean_dec_ref(v___f_1339_);
lean_dec_ref(v_buckets_1335_);
return v___x_1333_;
}
else
{
size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = ((size_t)0ULL);
v___x_1342_ = lean_usize_of_nat(v___x_1336_);
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1334_, v___f_1339_, v_buckets_1335_, v___x_1341_, v___x_1342_, v___x_1333_);
v___y_1322_ = v___x_1343_;
goto v___jp_1321_;
}
}
else
{
size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((size_t)0ULL);
v___x_1345_ = lean_usize_of_nat(v___x_1336_);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1334_, v___f_1339_, v_buckets_1335_, v___x_1344_, v___x_1345_, v___x_1333_);
v___y_1322_ = v___x_1346_;
goto v___jp_1321_;
}
}
v___jp_1321_:
{
lean_object* v_fst_1323_; lean_object* v_snd_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
v_fst_1323_ = lean_ctor_get(v___y_1322_, 0);
v_snd_1324_ = lean_ctor_get(v___y_1322_, 1);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___y_1322_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___y_1322_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_snd_1324_);
lean_inc(v_fst_1323_);
lean_dec(v___y_1322_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_fst_1323_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v_snd_1324_);
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
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition(lean_object* v_00_u03b1_1347_, lean_object* v_x_1348_, lean_object* v_x_1349_, lean_object* v_f_1350_, lean_object* v_m_1351_){
_start:
{
lean_object* v___y_1353_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v_buckets_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v___x_1363_ = lean_unsigned_to_nat(0u);
v___x_1364_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1365_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1366_ = lean_ctor_get(v_m_1351_, 1);
lean_inc_ref(v_buckets_1366_);
lean_dec_ref(v_m_1351_);
v___x_1367_ = lean_array_get_size(v_buckets_1366_);
v___x_1368_ = lean_nat_dec_lt(v___x_1363_, v___x_1367_);
if (v___x_1368_ == 0)
{
lean_dec_ref(v_buckets_1366_);
lean_dec_ref(v_f_1350_);
lean_dec_ref(v_x_1349_);
lean_dec_ref(v_x_1348_);
return v___x_1364_;
}
else
{
lean_object* v___f_1369_; lean_object* v___f_1370_; uint8_t v___x_1371_; 
v___f_1369_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1369_, 0, v_f_1350_);
lean_closure_set(v___f_1369_, 1, v_x_1348_);
lean_closure_set(v___f_1369_, 2, v_x_1349_);
v___f_1370_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1370_, 0, v___x_1365_);
lean_closure_set(v___f_1370_, 1, v___f_1369_);
v___x_1371_ = lean_nat_dec_le(v___x_1367_, v___x_1367_);
if (v___x_1371_ == 0)
{
if (v___x_1368_ == 0)
{
lean_dec_ref(v___f_1370_);
lean_dec_ref(v_buckets_1366_);
return v___x_1364_;
}
else
{
size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = lean_usize_of_nat(v___x_1367_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1365_, v___f_1370_, v_buckets_1366_, v___x_1372_, v___x_1373_, v___x_1364_);
v___y_1353_ = v___x_1374_;
goto v___jp_1352_;
}
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = lean_usize_of_nat(v___x_1367_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1365_, v___f_1370_, v_buckets_1366_, v___x_1375_, v___x_1376_, v___x_1364_);
v___y_1353_ = v___x_1377_;
goto v___jp_1352_;
}
}
v___jp_1352_:
{
lean_object* v_fst_1354_; lean_object* v_snd_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
v_fst_1354_ = lean_ctor_get(v___y_1353_, 0);
v_snd_1355_ = lean_ctor_get(v___y_1353_, 1);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___y_1353_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___y_1353_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_snd_1355_);
lean_inc(v_fst_1354_);
lean_dec(v___y_1353_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_fst_1354_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_snd_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray___redArg(lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v_l_1384_){
_start:
{
lean_object* v___f_1385_; lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___f_1385_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1386_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_1387_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1385_, v_inst_1382_, v_inst_1383_, v___x_1386_, v_l_1384_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray(lean_object* v_00_u03b1_1388_, lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_l_1391_){
_start:
{
lean_object* v___f_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___f_1392_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1393_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_1394_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1392_, v_inst_1389_, v_inst_1390_, v___x_1393_, v_l_1391_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg(lean_object* v_m_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg___boxed(lean_object* v_m_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Std_HashSet_Internal_numBuckets___redArg(v_m_1397_);
lean_dec_ref(v_m_1397_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets(lean_object* v_00_u03b1_1399_, lean_object* v_x_1400_, lean_object* v_x_1401_, lean_object* v_m_1402_){
_start:
{
lean_object* v___x_1403_; 
v___x_1403_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1402_);
return v___x_1403_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_, lean_object* v_m_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_HashSet_Internal_numBuckets(v_00_u03b1_1404_, v_x_1405_, v_x_1406_, v_m_1407_);
lean_dec_ref(v_m_1407_);
lean_dec_ref(v_x_1406_);
lean_dec_ref(v_x_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2(lean_object* v_inst_1412_, lean_object* v___f_1413_, lean_object* v_m_1414_, lean_object* v_prec_1415_){
_start:
{
lean_object* v___x_1416_; lean_object* v_buckets_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1437_; 
v___x_1416_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1417_ = lean_ctor_get(v_m_1414_, 1);
v_isSharedCheck_1437_ = !lean_is_exclusive(v_m_1414_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v_m_1414_, 0);
lean_dec(v_unused_1438_);
v___x_1419_ = v_m_1414_;
v_isShared_1420_ = v_isSharedCheck_1437_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_buckets_1417_);
lean_dec(v_m_1414_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1437_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1421_; lean_object* v___y_1423_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; uint8_t v___x_1432_; 
v___x_1421_ = ((lean_object*)(l_Std_HashSet_instRepr___redArg___lam__2___closed__1));
v___x_1429_ = lean_box(0);
v___x_1430_ = lean_array_get_size(v_buckets_1417_);
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_nat_dec_lt(v___x_1431_, v___x_1430_);
if (v___x_1432_ == 0)
{
lean_dec_ref(v_buckets_1417_);
lean_dec_ref(v___f_1413_);
v___y_1423_ = v___x_1429_;
goto v___jp_1422_;
}
else
{
lean_object* v___f_1433_; size_t v___x_1434_; size_t v___x_1435_; lean_object* v___x_1436_; 
v___f_1433_ = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1433_, 0, v___x_1416_);
lean_closure_set(v___f_1433_, 1, v___f_1413_);
v___x_1434_ = lean_usize_of_nat(v___x_1430_);
v___x_1435_ = ((size_t)0ULL);
v___x_1436_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1416_, v___f_1433_, v_buckets_1417_, v___x_1434_, v___x_1435_, v___x_1429_);
v___y_1423_ = v___x_1436_;
goto v___jp_1422_;
}
v___jp_1422_:
{
lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1424_ = l_List_repr___redArg(v_inst_1412_, v___y_1423_);
if (v_isShared_1420_ == 0)
{
lean_ctor_set_tag(v___x_1419_, 5);
lean_ctor_set(v___x_1419_, 1, v___x_1424_);
lean_ctor_set(v___x_1419_, 0, v___x_1421_);
v___x_1426_ = v___x_1419_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1421_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Repr_addAppParen(v___x_1426_, v_prec_1415_);
return v___x_1427_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1439_, lean_object* v___f_1440_, lean_object* v_m_1441_, lean_object* v_prec_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l_Std_HashSet_instRepr___redArg___lam__2(v_inst_1439_, v___f_1440_, v_m_1441_, v_prec_1442_);
lean_dec(v_prec_1442_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg(lean_object* v_inst_1444_){
_start:
{
lean_object* v___f_1445_; lean_object* v___f_1446_; 
v___f_1445_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___f_1446_ = lean_alloc_closure((void*)(l_Std_HashSet_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1446_, 0, v_inst_1444_);
lean_closure_set(v___f_1446_, 1, v___f_1445_);
return v___f_1446_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr(lean_object* v_00_u03b1_1447_, lean_object* v_inst_1448_, lean_object* v_inst_1449_, lean_object* v_inst_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Std_HashSet_instRepr___redArg(v_inst_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___boxed(lean_object* v_00_u03b1_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_){
_start:
{
lean_object* v_res_1456_; 
v_res_1456_ = l_Std_HashSet_instRepr(v_00_u03b1_1452_, v_inst_1453_, v_inst_1454_, v_inst_1455_);
lean_dec_ref(v_inst_1454_);
lean_dec_ref(v_inst_1453_);
return v_res_1456_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashSet_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
