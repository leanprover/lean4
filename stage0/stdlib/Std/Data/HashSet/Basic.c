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
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
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
v_currMacroScope_121_ = lean_ctor_get(v_a_114_, 2);
v_ref_122_ = lean_ctor_get(v_a_114_, 5);
v___x_123_ = lean_unsigned_to_nat(0u);
v___x_124_ = l_Lean_Syntax_getArg(v_x_113_, v___x_123_);
v___x_125_ = lean_unsigned_to_nat(2u);
v___x_126_ = l_Lean_Syntax_getArg(v_x_113_, v___x_125_);
lean_dec(v_x_113_);
v___x_127_ = 0;
v___x_128_ = l_Lean_SourceInfo_fromRef(v_ref_122_, v___x_127_);
v___x_129_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4));
v___x_130_ = lean_obj_once(&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6, &l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6_once, _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6);
v___x_131_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_121_);
lean_inc(v_quotContext_120_);
v___x_132_ = l_Lean_addMacroScope(v_quotContext_120_, v___x_131_, v_currMacroScope_121_);
v___x_133_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12));
lean_inc_n(v___x_128_, 2);
v___x_134_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_134_, 0, v___x_128_);
lean_ctor_set(v___x_134_, 1, v___x_130_);
lean_ctor_set(v___x_134_, 2, v___x_132_);
lean_ctor_set(v___x_134_, 3, v___x_133_);
v___x_135_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14));
v___x_136_ = l_Lean_Syntax_node2(v___x_128_, v___x_135_, v___x_124_, v___x_126_);
v___x_137_ = l_Lean_Syntax_node2(v___x_128_, v___x_129_, v___x_134_, v___x_136_);
v___x_138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v_a_115_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___boxed(lean_object* v_x_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(v_x_139_, v_a_140_, v_a_141_);
lean_dec_ref(v_a_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(lean_object* v_x_146_, lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
lean_object* v___x_149_; uint8_t v___x_150_; 
v___x_149_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4));
lean_inc(v_x_146_);
v___x_150_ = l_Lean_Syntax_isOfKind(v_x_146_, v___x_149_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_x_146_);
v___x_151_ = lean_box(0);
v___x_152_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v_a_148_);
return v___x_152_;
}
else
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Lean_Syntax_getArg(v_x_146_, v___x_153_);
v___x_155_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1));
lean_inc(v___x_154_);
v___x_156_ = l_Lean_Syntax_isOfKind(v___x_154_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v___x_154_);
lean_dec(v_x_146_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v_a_148_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_159_ = lean_unsigned_to_nat(1u);
v___x_160_ = l_Lean_Syntax_getArg(v_x_146_, v___x_159_);
lean_dec(v_x_146_);
v___x_161_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_160_);
v___x_162_ = l_Lean_Syntax_matchesNull(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v___x_160_);
lean_dec(v___x_154_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_a_148_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v_ref_167_; uint8_t v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_165_ = l_Lean_Syntax_getArg(v___x_160_, v___x_153_);
v___x_166_ = l_Lean_Syntax_getArg(v___x_160_, v___x_159_);
lean_dec(v___x_160_);
v_ref_167_ = l_Lean_replaceRef(v___x_154_, v_a_147_);
lean_dec(v___x_154_);
v___x_168_ = 0;
v___x_169_ = l_Lean_SourceInfo_fromRef(v_ref_167_, v___x_168_);
lean_dec(v_ref_167_);
v___x_170_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__3));
v___x_171_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__6));
lean_inc(v___x_169_);
v___x_172_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_169_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = l_Lean_Syntax_node3(v___x_169_, v___x_170_, v___x_165_, v___x_172_, v___x_166_);
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_a_148_);
return v___x_174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___boxed(lean_object* v_x_175_, lean_object* v_a_176_, lean_object* v_a_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(v_x_175_, v_a_176_, v_a_177_);
lean_dec(v_a_176_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert___redArg(lean_object* v_x_179_, lean_object* v_x_180_, lean_object* v_m_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_box(0);
v___x_184_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_179_, v_x_180_, v_m_181_, v_a_182_, v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert(lean_object* v_00_u03b1_185_, lean_object* v_x_186_, lean_object* v_x_187_, lean_object* v_m_188_, lean_object* v_a_189_){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_190_ = lean_box(0);
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_186_, v_x_187_, v_m_188_, v_a_189_, v___x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg___lam__0(lean_object* v_x_192_, lean_object* v_x_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_196_ = lean_box(0);
v___x_197_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_192_, v_x_193_, v___x_195_, v_a_194_, v___x_196_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg(lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
lean_object* v___f_200_; 
v___f_200_ = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(v___f_200_, 0, v_x_198_);
lean_closure_set(v___f_200_, 1, v_x_199_);
return v___f_200_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton(lean_object* v_00_u03b1_201_, lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
lean_object* v___f_204_; 
v___f_204_ = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(v___f_204_, 0, v_x_202_);
lean_closure_set(v___f_204_, 1, v_x_203_);
return v___f_204_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg___lam__0(lean_object* v_x_205_, lean_object* v_x_206_, lean_object* v_a_207_, lean_object* v_s_208_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_box(0);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_205_, v_x_206_, v_s_208_, v_a_207_, v___x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg(lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(v___f_213_, 0, v_x_211_);
lean_closure_set(v___f_213_, 1, v_x_212_);
return v___f_213_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert(lean_object* v_00_u03b1_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v___f_217_; 
v___f_217_ = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(v___f_217_, 0, v_x_215_);
lean_closure_set(v___f_217_, 1, v_x_216_);
return v___f_217_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert___redArg(lean_object* v_x_218_, lean_object* v_x_219_, lean_object* v_m_220_, lean_object* v_a_221_){
_start:
{
lean_object* v_size_222_; lean_object* v_buckets_223_; lean_object* v___x_224_; lean_object* v___x_225_; uint64_t v___x_226_; uint64_t v___x_227_; uint64_t v___x_228_; uint64_t v___x_229_; uint64_t v_fold_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; size_t v___x_234_; size_t v___x_235_; size_t v___x_236_; size_t v___x_237_; size_t v___x_238_; lean_object* v_bkt_239_; uint8_t v___x_240_; 
v_size_222_ = lean_ctor_get(v_m_220_, 0);
v_buckets_223_ = lean_ctor_get(v_m_220_, 1);
v___x_224_ = lean_array_get_size(v_buckets_223_);
lean_inc_ref(v_x_219_);
lean_inc_n(v_a_221_, 2);
v___x_225_ = lean_apply_1(v_x_219_, v_a_221_);
v___x_226_ = 32ULL;
v___x_227_ = lean_unbox_uint64(v___x_225_);
v___x_228_ = lean_uint64_shift_right(v___x_227_, v___x_226_);
v___x_229_ = lean_unbox_uint64(v___x_225_);
lean_dec_ref(v___x_225_);
v_fold_230_ = lean_uint64_xor(v___x_229_, v___x_228_);
v___x_231_ = 16ULL;
v___x_232_ = lean_uint64_shift_right(v_fold_230_, v___x_231_);
v___x_233_ = lean_uint64_xor(v_fold_230_, v___x_232_);
v___x_234_ = lean_uint64_to_usize(v___x_233_);
v___x_235_ = lean_usize_of_nat(v___x_224_);
v___x_236_ = ((size_t)1ULL);
v___x_237_ = lean_usize_sub(v___x_235_, v___x_236_);
v___x_238_ = lean_usize_land(v___x_234_, v___x_237_);
v_bkt_239_ = lean_array_uget_borrowed(v_buckets_223_, v___x_238_);
lean_inc(v_bkt_239_);
v___x_240_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_218_, v_a_221_, v_bkt_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_266_; 
lean_inc_ref(v_buckets_223_);
lean_inc(v_size_222_);
v_isSharedCheck_266_ = !lean_is_exclusive(v_m_220_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; lean_object* v_unused_268_; 
v_unused_267_ = lean_ctor_get(v_m_220_, 1);
lean_dec(v_unused_267_);
v_unused_268_ = lean_ctor_get(v_m_220_, 0);
lean_dec(v_unused_268_);
v___x_242_ = v_m_220_;
v_isShared_243_ = v_isSharedCheck_266_;
goto v_resetjp_241_;
}
else
{
lean_dec(v_m_220_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_266_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v_size_x27_246_; lean_object* v___x_247_; lean_object* v_buckets_x27_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_244_ = lean_box(0);
v___x_245_ = lean_unsigned_to_nat(1u);
v_size_x27_246_ = lean_nat_add(v_size_222_, v___x_245_);
lean_dec(v_size_222_);
lean_inc(v_bkt_239_);
v___x_247_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_247_, 0, v_a_221_);
lean_ctor_set(v___x_247_, 1, v___x_244_);
lean_ctor_set(v___x_247_, 2, v_bkt_239_);
v_buckets_x27_248_ = lean_array_uset(v_buckets_223_, v___x_238_, v___x_247_);
v___x_249_ = lean_unsigned_to_nat(4u);
v___x_250_ = lean_nat_mul(v_size_x27_246_, v___x_249_);
v___x_251_ = lean_unsigned_to_nat(3u);
v___x_252_ = lean_nat_div(v___x_250_, v___x_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_array_get_size(v_buckets_x27_248_);
v___x_254_ = lean_nat_dec_le(v___x_252_, v___x_253_);
lean_dec(v___x_252_);
if (v___x_254_ == 0)
{
lean_object* v_val_255_; lean_object* v___x_257_; 
v_val_255_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_219_, v_buckets_x27_248_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_val_255_);
lean_ctor_set(v___x_242_, 0, v_size_x27_246_);
v___x_257_ = v___x_242_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_size_x27_246_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v_val_255_);
v___x_257_ = v_reuseFailAlloc_260_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_box(v___x_240_);
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
return v___x_259_;
}
}
else
{
lean_object* v___x_262_; 
lean_dec_ref(v_x_219_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v_buckets_x27_248_);
lean_ctor_set(v___x_242_, 0, v_size_x27_246_);
v___x_262_ = v___x_242_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_size_x27_246_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_buckets_x27_248_);
v___x_262_ = v_reuseFailAlloc_265_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_box(v___x_240_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
return v___x_264_;
}
}
}
}
else
{
lean_object* v___x_269_; lean_object* v___x_270_; 
lean_dec(v_a_221_);
lean_dec_ref(v_x_219_);
v___x_269_ = lean_box(v___x_240_);
v___x_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_269_);
lean_ctor_set(v___x_270_, 1, v_m_220_);
return v___x_270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert(lean_object* v_00_u03b1_271_, lean_object* v_x_272_, lean_object* v_x_273_, lean_object* v_m_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_size_276_; lean_object* v_buckets_277_; lean_object* v___x_278_; lean_object* v___x_279_; uint64_t v___x_280_; uint64_t v___x_281_; uint64_t v___x_282_; uint64_t v___x_283_; uint64_t v_fold_284_; uint64_t v___x_285_; uint64_t v___x_286_; uint64_t v___x_287_; size_t v___x_288_; size_t v___x_289_; size_t v___x_290_; size_t v___x_291_; size_t v___x_292_; lean_object* v_bkt_293_; uint8_t v___x_294_; 
v_size_276_ = lean_ctor_get(v_m_274_, 0);
v_buckets_277_ = lean_ctor_get(v_m_274_, 1);
v___x_278_ = lean_array_get_size(v_buckets_277_);
lean_inc_ref(v_x_273_);
lean_inc_n(v_a_275_, 2);
v___x_279_ = lean_apply_1(v_x_273_, v_a_275_);
v___x_280_ = 32ULL;
v___x_281_ = lean_unbox_uint64(v___x_279_);
v___x_282_ = lean_uint64_shift_right(v___x_281_, v___x_280_);
v___x_283_ = lean_unbox_uint64(v___x_279_);
lean_dec_ref(v___x_279_);
v_fold_284_ = lean_uint64_xor(v___x_283_, v___x_282_);
v___x_285_ = 16ULL;
v___x_286_ = lean_uint64_shift_right(v_fold_284_, v___x_285_);
v___x_287_ = lean_uint64_xor(v_fold_284_, v___x_286_);
v___x_288_ = lean_uint64_to_usize(v___x_287_);
v___x_289_ = lean_usize_of_nat(v___x_278_);
v___x_290_ = ((size_t)1ULL);
v___x_291_ = lean_usize_sub(v___x_289_, v___x_290_);
v___x_292_ = lean_usize_land(v___x_288_, v___x_291_);
v_bkt_293_ = lean_array_uget_borrowed(v_buckets_277_, v___x_292_);
lean_inc(v_bkt_293_);
v___x_294_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_272_, v_a_275_, v_bkt_293_);
if (v___x_294_ == 0)
{
lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_320_; 
lean_inc_ref(v_buckets_277_);
lean_inc(v_size_276_);
v_isSharedCheck_320_ = !lean_is_exclusive(v_m_274_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; lean_object* v_unused_322_; 
v_unused_321_ = lean_ctor_get(v_m_274_, 1);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_m_274_, 0);
lean_dec(v_unused_322_);
v___x_296_ = v_m_274_;
v_isShared_297_ = v_isSharedCheck_320_;
goto v_resetjp_295_;
}
else
{
lean_dec(v_m_274_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_320_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v_size_x27_300_; lean_object* v___x_301_; lean_object* v_buckets_x27_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_298_ = lean_box(0);
v___x_299_ = lean_unsigned_to_nat(1u);
v_size_x27_300_ = lean_nat_add(v_size_276_, v___x_299_);
lean_dec(v_size_276_);
lean_inc(v_bkt_293_);
v___x_301_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_301_, 0, v_a_275_);
lean_ctor_set(v___x_301_, 1, v___x_298_);
lean_ctor_set(v___x_301_, 2, v_bkt_293_);
v_buckets_x27_302_ = lean_array_uset(v_buckets_277_, v___x_292_, v___x_301_);
v___x_303_ = lean_unsigned_to_nat(4u);
v___x_304_ = lean_nat_mul(v_size_x27_300_, v___x_303_);
v___x_305_ = lean_unsigned_to_nat(3u);
v___x_306_ = lean_nat_div(v___x_304_, v___x_305_);
lean_dec(v___x_304_);
v___x_307_ = lean_array_get_size(v_buckets_x27_302_);
v___x_308_ = lean_nat_dec_le(v___x_306_, v___x_307_);
lean_dec(v___x_306_);
if (v___x_308_ == 0)
{
lean_object* v_val_309_; lean_object* v___x_311_; 
v_val_309_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_273_, v_buckets_x27_302_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v_val_309_);
lean_ctor_set(v___x_296_, 0, v_size_x27_300_);
v___x_311_ = v___x_296_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_size_x27_300_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v_val_309_);
v___x_311_ = v_reuseFailAlloc_314_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_box(v___x_294_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
return v___x_313_;
}
}
else
{
lean_object* v___x_316_; 
lean_dec_ref(v_x_273_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v_buckets_x27_302_);
lean_ctor_set(v___x_296_, 0, v_size_x27_300_);
v___x_316_ = v___x_296_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v_size_x27_300_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v_buckets_x27_302_);
v___x_316_ = v_reuseFailAlloc_319_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = lean_box(v___x_294_);
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___x_317_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
return v___x_318_;
}
}
}
}
else
{
lean_object* v___x_323_; lean_object* v___x_324_; 
lean_dec(v_a_275_);
lean_dec_ref(v_x_273_);
v___x_323_ = lean_box(v___x_294_);
v___x_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
lean_ctor_set(v___x_324_, 1, v_m_274_);
return v___x_324_;
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_contains___redArg(lean_object* v_x_325_, lean_object* v_x_326_, lean_object* v_m_327_, lean_object* v_a_328_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_325_, v_x_326_, v_m_327_, v_a_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___redArg___boxed(lean_object* v_x_330_, lean_object* v_x_331_, lean_object* v_m_332_, lean_object* v_a_333_){
_start:
{
uint8_t v_res_334_; lean_object* v_r_335_; 
v_res_334_ = l_Std_HashSet_contains___redArg(v_x_330_, v_x_331_, v_m_332_, v_a_333_);
lean_dec_ref(v_m_332_);
v_r_335_ = lean_box(v_res_334_);
return v_r_335_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_contains(lean_object* v_00_u03b1_336_, lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_m_339_, lean_object* v_a_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_337_, v_x_338_, v_m_339_, v_a_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___boxed(lean_object* v_00_u03b1_342_, lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_m_345_, lean_object* v_a_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Std_HashSet_contains(v_00_u03b1_342_, v_x_343_, v_x_344_, v_m_345_, v_a_346_);
lean_dec_ref(v_m_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership(lean_object* v_00_u03b1_349_, lean_object* v_inst_350_, lean_object* v_inst_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = lean_box(0);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___boxed(lean_object* v_00_u03b1_353_, lean_object* v_inst_354_, lean_object* v_inst_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_HashSet_instMembership(v_00_u03b1_353_, v_inst_354_, v_inst_355_);
lean_dec_ref(v_inst_355_);
lean_dec_ref(v_inst_354_);
return v_res_356_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem___redArg(lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_m_359_, lean_object* v_a_360_){
_start:
{
uint8_t v___x_361_; 
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_357_, v_inst_358_, v_m_359_, v_a_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___redArg___boxed(lean_object* v_inst_362_, lean_object* v_inst_363_, lean_object* v_m_364_, lean_object* v_a_365_){
_start:
{
uint8_t v_res_366_; lean_object* v_r_367_; 
v_res_366_ = l_Std_HashSet_instDecidableMem___redArg(v_inst_362_, v_inst_363_, v_m_364_, v_a_365_);
lean_dec_ref(v_m_364_);
v_r_367_ = lean_box(v_res_366_);
return v_r_367_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem(lean_object* v_00_u03b1_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_m_371_, lean_object* v_a_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_369_, v_inst_370_, v_m_371_, v_a_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___boxed(lean_object* v_00_u03b1_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_m_377_, lean_object* v_a_378_){
_start:
{
uint8_t v_res_379_; lean_object* v_r_380_; 
v_res_379_ = l_Std_HashSet_instDecidableMem(v_00_u03b1_374_, v_inst_375_, v_inst_376_, v_m_377_, v_a_378_);
lean_dec_ref(v_m_377_);
v_r_380_ = lean_box(v_res_379_);
return v_r_380_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase___redArg(lean_object* v_x_381_, lean_object* v_x_382_, lean_object* v_m_383_, lean_object* v_a_384_){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_381_, v_x_382_, v_m_383_, v_a_384_);
return v___x_385_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase(lean_object* v_00_u03b1_386_, lean_object* v_x_387_, lean_object* v_x_388_, lean_object* v_m_389_, lean_object* v_a_390_){
_start:
{
lean_object* v___x_391_; 
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_387_, v_x_388_, v_m_389_, v_a_390_);
return v___x_391_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg(lean_object* v_m_392_){
_start:
{
lean_object* v_size_393_; 
v_size_393_ = lean_ctor_get(v_m_392_, 0);
lean_inc(v_size_393_);
return v_size_393_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg___boxed(lean_object* v_m_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_HashSet_size___redArg(v_m_394_);
lean_dec_ref(v_m_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size(lean_object* v_00_u03b1_396_, lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v_m_399_){
_start:
{
lean_object* v_size_400_; 
v_size_400_ = lean_ctor_get(v_m_399_, 0);
lean_inc(v_size_400_);
return v_size_400_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___boxed(lean_object* v_00_u03b1_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_m_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l_Std_HashSet_size(v_00_u03b1_401_, v_x_402_, v_x_403_, v_m_404_);
lean_dec_ref(v_m_404_);
lean_dec_ref(v_x_403_);
lean_dec_ref(v_x_402_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg(lean_object* v_x_406_, lean_object* v_x_407_, lean_object* v_m_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_406_, v_x_407_, v_m_408_, v_a_409_);
return v___x_410_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg___boxed(lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v_m_413_, lean_object* v_a_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Std_HashSet_get_x3f___redArg(v_x_411_, v_x_412_, v_m_413_, v_a_414_);
lean_dec_ref(v_m_413_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f(lean_object* v_00_u03b1_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_m_419_, lean_object* v_a_420_){
_start:
{
lean_object* v___x_421_; 
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_417_, v_x_418_, v_m_419_, v_a_420_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___boxed(lean_object* v_00_u03b1_422_, lean_object* v_x_423_, lean_object* v_x_424_, lean_object* v_m_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Std_HashSet_get_x3f(v_00_u03b1_422_, v_x_423_, v_x_424_, v_m_425_, v_a_426_);
lean_dec_ref(v_m_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg(lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_m_430_, lean_object* v_a_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_428_, v_inst_429_, v_m_430_, v_a_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg___boxed(lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_m_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_Std_HashSet_get___redArg(v_inst_433_, v_inst_434_, v_m_435_, v_a_436_);
lean_dec_ref(v_m_435_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get(lean_object* v_00_u03b1_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_m_441_, lean_object* v_a_442_, lean_object* v_h_443_){
_start:
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_439_, v_inst_440_, v_m_441_, v_a_442_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___boxed(lean_object* v_00_u03b1_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_m_448_, lean_object* v_a_449_, lean_object* v_h_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_HashSet_get(v_00_u03b1_445_, v_inst_446_, v_inst_447_, v_m_448_, v_a_449_, v_h_450_);
lean_dec_ref(v_m_448_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg(lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_m_454_, lean_object* v_a_455_, lean_object* v_fallback_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_452_, v_inst_453_, v_m_454_, v_a_455_, v_fallback_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg___boxed(lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_m_460_, lean_object* v_a_461_, lean_object* v_fallback_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Std_HashSet_getD___redArg(v_inst_458_, v_inst_459_, v_m_460_, v_a_461_, v_fallback_462_);
lean_dec(v_fallback_462_);
lean_dec_ref(v_m_460_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD(lean_object* v_00_u03b1_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_m_467_, lean_object* v_a_468_, lean_object* v_fallback_469_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_465_, v_inst_466_, v_m_467_, v_a_468_, v_fallback_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___boxed(lean_object* v_00_u03b1_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_m_474_, lean_object* v_a_475_, lean_object* v_fallback_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_HashSet_getD(v_00_u03b1_471_, v_inst_472_, v_inst_473_, v_m_474_, v_a_475_, v_fallback_476_);
lean_dec(v_fallback_476_);
lean_dec_ref(v_m_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg(lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_m_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_478_, v_inst_479_, v_inst_480_, v_m_481_, v_a_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg___boxed(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_m_487_, lean_object* v_a_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l_Std_HashSet_get_x21___redArg(v_inst_484_, v_inst_485_, v_inst_486_, v_m_487_, v_a_488_);
lean_dec_ref(v_m_487_);
lean_dec(v_inst_486_);
return v_res_489_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21(lean_object* v_00_u03b1_490_, lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_m_494_, lean_object* v_a_495_){
_start:
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_491_, v_inst_492_, v_inst_493_, v_m_494_, v_a_495_);
return v___x_496_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___boxed(lean_object* v_00_u03b1_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_m_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_HashSet_get_x21(v_00_u03b1_497_, v_inst_498_, v_inst_499_, v_inst_500_, v_m_501_, v_a_502_);
lean_dec_ref(v_m_501_);
lean_dec(v_inst_500_);
return v_res_503_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty___redArg(lean_object* v_m_504_){
_start:
{
lean_object* v_size_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_size_505_ = lean_ctor_get(v_m_504_, 0);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_nat_dec_eq(v_size_505_, v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___redArg___boxed(lean_object* v_m_508_){
_start:
{
uint8_t v_res_509_; lean_object* v_r_510_; 
v_res_509_ = l_Std_HashSet_isEmpty___redArg(v_m_508_);
lean_dec_ref(v_m_508_);
v_r_510_ = lean_box(v_res_509_);
return v_r_510_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty(lean_object* v_00_u03b1_511_, lean_object* v_x_512_, lean_object* v_x_513_, lean_object* v_m_514_){
_start:
{
lean_object* v_size_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_size_515_ = lean_ctor_get(v_m_514_, 0);
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = lean_nat_dec_eq(v_size_515_, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___boxed(lean_object* v_00_u03b1_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_m_521_){
_start:
{
uint8_t v_res_522_; lean_object* v_r_523_; 
v_res_522_ = l_Std_HashSet_isEmpty(v_00_u03b1_518_, v_x_519_, v_x_520_, v_m_521_);
lean_dec_ref(v_m_521_);
lean_dec_ref(v_x_520_);
lean_dec_ref(v_x_519_);
v_r_523_ = lean_box(v_res_522_);
return v_r_523_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0(lean_object* v_a_524_, lean_object* v_b_525_, lean_object* v_d_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_527_, 0, v_a_524_);
lean_ctor_set(v___x_527_, 1, v_d_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__1(lean_object* v___x_528_, lean_object* v___f_529_, lean_object* v_l_530_, lean_object* v_acc_531_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_528_, v___f_529_, v_acc_531_, v_l_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg(lean_object* v_m_556_){
_start:
{
lean_object* v___x_557_; lean_object* v_buckets_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_557_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_558_ = lean_ctor_get(v_m_556_, 1);
lean_inc_ref(v_buckets_558_);
lean_dec_ref(v_m_556_);
v___x_559_ = lean_box(0);
v___x_560_ = lean_array_get_size(v_buckets_558_);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_nat_dec_lt(v___x_561_, v___x_560_);
if (v___x_562_ == 0)
{
lean_dec_ref(v_buckets_558_);
return v___x_559_;
}
else
{
lean_object* v___f_563_; size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___f_563_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__11));
v___x_564_ = lean_usize_of_nat(v___x_560_);
v___x_565_ = ((size_t)0ULL);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_557_, v___f_563_, v_buckets_558_, v___x_564_, v___x_565_, v___x_559_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList(lean_object* v_00_u03b1_567_, lean_object* v_x_568_, lean_object* v_x_569_, lean_object* v_m_570_){
_start:
{
lean_object* v___x_571_; lean_object* v_buckets_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; uint8_t v___x_576_; 
v___x_571_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_572_ = lean_ctor_get(v_m_570_, 1);
lean_inc_ref(v_buckets_572_);
lean_dec_ref(v_m_570_);
v___x_573_ = lean_box(0);
v___x_574_ = lean_array_get_size(v_buckets_572_);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_nat_dec_lt(v___x_575_, v___x_574_);
if (v___x_576_ == 0)
{
lean_dec_ref(v_buckets_572_);
return v___x_573_;
}
else
{
lean_object* v___f_577_; size_t v___x_578_; size_t v___x_579_; lean_object* v___x_580_; 
v___f_577_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__11));
v___x_578_ = lean_usize_of_nat(v___x_574_);
v___x_579_ = ((size_t)0ULL);
v___x_580_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_571_, v___f_577_, v_buckets_572_, v___x_578_, v___x_579_, v___x_573_);
return v___x_580_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___boxed(lean_object* v_00_u03b1_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_m_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_HashSet_toList(v_00_u03b1_581_, v_x_582_, v_x_583_, v_m_584_);
lean_dec_ref(v_x_583_);
lean_dec_ref(v_x_582_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg(lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_l_592_){
_start:
{
lean_object* v___f_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___f_593_ = ((lean_object*)(l_Std_HashSet_ofList___redArg___closed__1));
v___x_594_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_593_, v_inst_590_, v_inst_591_, v___x_594_, v_l_592_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList(lean_object* v_00_u03b1_596_, lean_object* v_inst_597_, lean_object* v_inst_598_, lean_object* v_l_599_){
_start:
{
lean_object* v___f_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v___f_600_ = ((lean_object*)(l_Std_HashSet_ofList___redArg___closed__1));
v___x_601_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_600_, v_inst_597_, v_inst_598_, v___x_601_, v_l_599_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0(lean_object* v_f_603_, lean_object* v_b_604_, lean_object* v_a_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = lean_apply_2(v_f_603_, v_b_604_, v_a_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__1(lean_object* v_inst_608_, lean_object* v___f_609_, lean_object* v_acc_610_, lean_object* v_l_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_608_, v___f_609_, v_acc_610_, v_l_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg(lean_object* v_inst_613_, lean_object* v_f_614_, lean_object* v_init_615_, lean_object* v_b_616_){
_start:
{
lean_object* v_buckets_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_buckets_617_ = lean_ctor_get(v_b_616_, 1);
lean_inc_ref(v_buckets_617_);
lean_dec_ref(v_b_616_);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_array_get_size(v_buckets_617_);
v___x_620_ = lean_nat_dec_lt(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v_toApplicative_621_; lean_object* v_toPure_622_; lean_object* v___x_623_; 
lean_dec_ref(v_buckets_617_);
lean_dec(v_f_614_);
v_toApplicative_621_ = lean_ctor_get(v_inst_613_, 0);
lean_inc_ref(v_toApplicative_621_);
lean_dec_ref(v_inst_613_);
v_toPure_622_ = lean_ctor_get(v_toApplicative_621_, 1);
lean_inc(v_toPure_622_);
lean_dec_ref(v_toApplicative_621_);
v___x_623_ = lean_apply_2(v_toPure_622_, lean_box(0), v_init_615_);
return v___x_623_;
}
else
{
lean_object* v___f_624_; lean_object* v___f_625_; uint8_t v___x_626_; 
v___f_624_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_624_, 0, v_f_614_);
lean_inc_ref(v_inst_613_);
v___f_625_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_625_, 0, v_inst_613_);
lean_closure_set(v___f_625_, 1, v___f_624_);
v___x_626_ = lean_nat_dec_le(v___x_619_, v___x_619_);
if (v___x_626_ == 0)
{
if (v___x_620_ == 0)
{
lean_object* v_toApplicative_627_; lean_object* v_toPure_628_; lean_object* v___x_629_; 
lean_dec_ref(v___f_625_);
lean_dec_ref(v_buckets_617_);
v_toApplicative_627_ = lean_ctor_get(v_inst_613_, 0);
lean_inc_ref(v_toApplicative_627_);
lean_dec_ref(v_inst_613_);
v_toPure_628_ = lean_ctor_get(v_toApplicative_627_, 1);
lean_inc(v_toPure_628_);
lean_dec_ref(v_toApplicative_627_);
v___x_629_ = lean_apply_2(v_toPure_628_, lean_box(0), v_init_615_);
return v___x_629_;
}
else
{
size_t v___x_630_; size_t v___x_631_; lean_object* v___x_632_; 
v___x_630_ = ((size_t)0ULL);
v___x_631_ = lean_usize_of_nat(v___x_619_);
v___x_632_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_613_, v___f_625_, v_buckets_617_, v___x_630_, v___x_631_, v_init_615_);
return v___x_632_;
}
}
else
{
size_t v___x_633_; size_t v___x_634_; lean_object* v___x_635_; 
v___x_633_ = ((size_t)0ULL);
v___x_634_ = lean_usize_of_nat(v___x_619_);
v___x_635_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_613_, v___f_625_, v_buckets_617_, v___x_633_, v___x_634_, v_init_615_);
return v___x_635_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM(lean_object* v_00_u03b1_636_, lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_m_639_, lean_object* v_inst_640_, lean_object* v_00_u03b2_641_, lean_object* v_f_642_, lean_object* v_init_643_, lean_object* v_b_644_){
_start:
{
lean_object* v_buckets_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_buckets_645_ = lean_ctor_get(v_b_644_, 1);
lean_inc_ref(v_buckets_645_);
lean_dec_ref(v_b_644_);
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = lean_array_get_size(v_buckets_645_);
v___x_648_ = lean_nat_dec_lt(v___x_646_, v___x_647_);
if (v___x_648_ == 0)
{
lean_object* v_toApplicative_649_; lean_object* v_toPure_650_; lean_object* v___x_651_; 
lean_dec_ref(v_buckets_645_);
lean_dec(v_f_642_);
v_toApplicative_649_ = lean_ctor_get(v_inst_640_, 0);
lean_inc_ref(v_toApplicative_649_);
lean_dec_ref(v_inst_640_);
v_toPure_650_ = lean_ctor_get(v_toApplicative_649_, 1);
lean_inc(v_toPure_650_);
lean_dec_ref(v_toApplicative_649_);
v___x_651_ = lean_apply_2(v_toPure_650_, lean_box(0), v_init_643_);
return v___x_651_;
}
else
{
lean_object* v___f_652_; lean_object* v___f_653_; uint8_t v___x_654_; 
v___f_652_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_652_, 0, v_f_642_);
lean_inc_ref(v_inst_640_);
v___f_653_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_653_, 0, v_inst_640_);
lean_closure_set(v___f_653_, 1, v___f_652_);
v___x_654_ = lean_nat_dec_le(v___x_647_, v___x_647_);
if (v___x_654_ == 0)
{
if (v___x_648_ == 0)
{
lean_object* v_toApplicative_655_; lean_object* v_toPure_656_; lean_object* v___x_657_; 
lean_dec_ref(v___f_653_);
lean_dec_ref(v_buckets_645_);
v_toApplicative_655_ = lean_ctor_get(v_inst_640_, 0);
lean_inc_ref(v_toApplicative_655_);
lean_dec_ref(v_inst_640_);
v_toPure_656_ = lean_ctor_get(v_toApplicative_655_, 1);
lean_inc(v_toPure_656_);
lean_dec_ref(v_toApplicative_655_);
v___x_657_ = lean_apply_2(v_toPure_656_, lean_box(0), v_init_643_);
return v___x_657_;
}
else
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_647_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_640_, v___f_653_, v_buckets_645_, v___x_658_, v___x_659_, v_init_643_);
return v___x_660_;
}
}
else
{
size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; 
v___x_661_ = ((size_t)0ULL);
v___x_662_ = lean_usize_of_nat(v___x_647_);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_640_, v___f_653_, v_buckets_645_, v___x_661_, v___x_662_, v_init_643_);
return v___x_663_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___boxed(lean_object* v_00_u03b1_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_m_667_, lean_object* v_inst_668_, lean_object* v_00_u03b2_669_, lean_object* v_f_670_, lean_object* v_init_671_, lean_object* v_b_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_HashSet_foldM(v_00_u03b1_664_, v_x_665_, v_x_666_, v_m_667_, v_inst_668_, v_00_u03b2_669_, v_f_670_, v_init_671_, v_b_672_);
lean_dec_ref(v_x_666_);
lean_dec_ref(v_x_665_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__0(lean_object* v_f_674_, lean_object* v_x1_675_, lean_object* v_x2_676_, lean_object* v_x3_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_apply_2(v_f_674_, v_x1_675_, v_x2_676_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__1(lean_object* v___x_679_, lean_object* v___f_680_, lean_object* v_acc_681_, lean_object* v_l_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_679_, v___f_680_, v_acc_681_, v_l_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg(lean_object* v_f_684_, lean_object* v_init_685_, lean_object* v_m_686_){
_start:
{
lean_object* v___x_687_; lean_object* v_buckets_688_; lean_object* v___x_689_; lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_687_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_688_ = lean_ctor_get(v_m_686_, 1);
lean_inc_ref(v_buckets_688_);
lean_dec_ref(v_m_686_);
v___x_689_ = lean_unsigned_to_nat(0u);
v___x_690_ = lean_array_get_size(v_buckets_688_);
v___x_691_ = lean_nat_dec_lt(v___x_689_, v___x_690_);
if (v___x_691_ == 0)
{
lean_dec_ref(v_buckets_688_);
lean_dec(v_f_684_);
return v_init_685_;
}
else
{
lean_object* v___f_692_; lean_object* v___f_693_; uint8_t v___x_694_; 
v___f_692_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_692_, 0, v_f_684_);
v___f_693_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_693_, 0, v___x_687_);
lean_closure_set(v___f_693_, 1, v___f_692_);
v___x_694_ = lean_nat_dec_le(v___x_690_, v___x_690_);
if (v___x_694_ == 0)
{
if (v___x_691_ == 0)
{
lean_dec_ref(v___f_693_);
lean_dec_ref(v_buckets_688_);
return v_init_685_;
}
else
{
size_t v___x_695_; size_t v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((size_t)0ULL);
v___x_696_ = lean_usize_of_nat(v___x_690_);
v___x_697_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_687_, v___f_693_, v_buckets_688_, v___x_695_, v___x_696_, v_init_685_);
return v___x_697_;
}
}
else
{
size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v___x_698_ = ((size_t)0ULL);
v___x_699_ = lean_usize_of_nat(v___x_690_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_687_, v___f_693_, v_buckets_688_, v___x_698_, v___x_699_, v_init_685_);
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold(lean_object* v_00_u03b1_701_, lean_object* v_x_702_, lean_object* v_x_703_, lean_object* v_00_u03b2_704_, lean_object* v_f_705_, lean_object* v_init_706_, lean_object* v_m_707_){
_start:
{
lean_object* v___x_708_; lean_object* v_buckets_709_; lean_object* v___x_710_; lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_708_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_709_ = lean_ctor_get(v_m_707_, 1);
lean_inc_ref(v_buckets_709_);
lean_dec_ref(v_m_707_);
v___x_710_ = lean_unsigned_to_nat(0u);
v___x_711_ = lean_array_get_size(v_buckets_709_);
v___x_712_ = lean_nat_dec_lt(v___x_710_, v___x_711_);
if (v___x_712_ == 0)
{
lean_dec_ref(v_buckets_709_);
lean_dec(v_f_705_);
return v_init_706_;
}
else
{
lean_object* v___f_713_; lean_object* v___f_714_; uint8_t v___x_715_; 
v___f_713_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_713_, 0, v_f_705_);
v___f_714_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_714_, 0, v___x_708_);
lean_closure_set(v___f_714_, 1, v___f_713_);
v___x_715_ = lean_nat_dec_le(v___x_711_, v___x_711_);
if (v___x_715_ == 0)
{
if (v___x_712_ == 0)
{
lean_dec_ref(v___f_714_);
lean_dec_ref(v_buckets_709_);
return v_init_706_;
}
else
{
size_t v___x_716_; size_t v___x_717_; lean_object* v___x_718_; 
v___x_716_ = ((size_t)0ULL);
v___x_717_ = lean_usize_of_nat(v___x_711_);
v___x_718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_708_, v___f_714_, v_buckets_709_, v___x_716_, v___x_717_, v_init_706_);
return v___x_718_;
}
}
else
{
size_t v___x_719_; size_t v___x_720_; lean_object* v___x_721_; 
v___x_719_ = ((size_t)0ULL);
v___x_720_ = lean_usize_of_nat(v___x_711_);
v___x_721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_708_, v___f_714_, v_buckets_709_, v___x_719_, v___x_720_, v_init_706_);
return v___x_721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___boxed(lean_object* v_00_u03b1_722_, lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_00_u03b2_725_, lean_object* v_f_726_, lean_object* v_init_727_, lean_object* v_m_728_){
_start:
{
lean_object* v_res_729_; 
v_res_729_ = l_Std_HashSet_fold(v_00_u03b1_722_, v_x_723_, v_x_724_, v_00_u03b2_725_, v_f_726_, v_init_727_, v_m_728_);
lean_dec_ref(v_x_724_);
lean_dec_ref(v_x_723_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0(lean_object* v_f_730_, lean_object* v_x_731_, lean_object* v___y_732_, lean_object* v___y_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = lean_apply_1(v_f_730_, v___y_732_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__1(lean_object* v_inst_735_, lean_object* v___f_736_, lean_object* v_x_737_, lean_object* v___y_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_box(0);
v___x_740_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_735_, v___f_736_, v___x_739_, v___y_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg(lean_object* v_inst_741_, lean_object* v_f_742_, lean_object* v_b_743_){
_start:
{
lean_object* v_buckets_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_buckets_744_ = lean_ctor_get(v_b_743_, 1);
lean_inc_ref(v_buckets_744_);
lean_dec_ref(v_b_743_);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_array_get_size(v_buckets_744_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_nat_dec_lt(v___x_745_, v___x_746_);
if (v___x_748_ == 0)
{
lean_object* v_toApplicative_749_; lean_object* v_toPure_750_; lean_object* v___x_751_; 
lean_dec_ref(v_buckets_744_);
lean_dec(v_f_742_);
v_toApplicative_749_ = lean_ctor_get(v_inst_741_, 0);
lean_inc_ref(v_toApplicative_749_);
lean_dec_ref(v_inst_741_);
v_toPure_750_ = lean_ctor_get(v_toApplicative_749_, 1);
lean_inc(v_toPure_750_);
lean_dec_ref(v_toApplicative_749_);
v___x_751_ = lean_apply_2(v_toPure_750_, lean_box(0), v___x_747_);
return v___x_751_;
}
else
{
lean_object* v___f_752_; lean_object* v___f_753_; uint8_t v___x_754_; 
v___f_752_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_752_, 0, v_f_742_);
lean_inc_ref(v_inst_741_);
v___f_753_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_753_, 0, v_inst_741_);
lean_closure_set(v___f_753_, 1, v___f_752_);
v___x_754_ = lean_nat_dec_le(v___x_746_, v___x_746_);
if (v___x_754_ == 0)
{
if (v___x_748_ == 0)
{
lean_object* v_toApplicative_755_; lean_object* v_toPure_756_; lean_object* v___x_757_; 
lean_dec_ref(v___f_753_);
lean_dec_ref(v_buckets_744_);
v_toApplicative_755_ = lean_ctor_get(v_inst_741_, 0);
lean_inc_ref(v_toApplicative_755_);
lean_dec_ref(v_inst_741_);
v_toPure_756_ = lean_ctor_get(v_toApplicative_755_, 1);
lean_inc(v_toPure_756_);
lean_dec_ref(v_toApplicative_755_);
v___x_757_ = lean_apply_2(v_toPure_756_, lean_box(0), v___x_747_);
return v___x_757_;
}
else
{
size_t v___x_758_; size_t v___x_759_; lean_object* v___x_760_; 
v___x_758_ = ((size_t)0ULL);
v___x_759_ = lean_usize_of_nat(v___x_746_);
v___x_760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_741_, v___f_753_, v_buckets_744_, v___x_758_, v___x_759_, v___x_747_);
return v___x_760_;
}
}
else
{
size_t v___x_761_; size_t v___x_762_; lean_object* v___x_763_; 
v___x_761_ = ((size_t)0ULL);
v___x_762_ = lean_usize_of_nat(v___x_746_);
v___x_763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_741_, v___f_753_, v_buckets_744_, v___x_761_, v___x_762_, v___x_747_);
return v___x_763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM(lean_object* v_00_u03b1_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_m_767_, lean_object* v_inst_768_, lean_object* v_f_769_, lean_object* v_b_770_){
_start:
{
lean_object* v_buckets_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; uint8_t v___x_775_; 
v_buckets_771_ = lean_ctor_get(v_b_770_, 1);
lean_inc_ref(v_buckets_771_);
lean_dec_ref(v_b_770_);
v___x_772_ = lean_unsigned_to_nat(0u);
v___x_773_ = lean_array_get_size(v_buckets_771_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_nat_dec_lt(v___x_772_, v___x_773_);
if (v___x_775_ == 0)
{
lean_object* v_toApplicative_776_; lean_object* v_toPure_777_; lean_object* v___x_778_; 
lean_dec_ref(v_buckets_771_);
lean_dec(v_f_769_);
v_toApplicative_776_ = lean_ctor_get(v_inst_768_, 0);
lean_inc_ref(v_toApplicative_776_);
lean_dec_ref(v_inst_768_);
v_toPure_777_ = lean_ctor_get(v_toApplicative_776_, 1);
lean_inc(v_toPure_777_);
lean_dec_ref(v_toApplicative_776_);
v___x_778_ = lean_apply_2(v_toPure_777_, lean_box(0), v___x_774_);
return v___x_778_;
}
else
{
lean_object* v___f_779_; lean_object* v___f_780_; uint8_t v___x_781_; 
v___f_779_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_779_, 0, v_f_769_);
lean_inc_ref(v_inst_768_);
v___f_780_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_780_, 0, v_inst_768_);
lean_closure_set(v___f_780_, 1, v___f_779_);
v___x_781_ = lean_nat_dec_le(v___x_773_, v___x_773_);
if (v___x_781_ == 0)
{
if (v___x_775_ == 0)
{
lean_object* v_toApplicative_782_; lean_object* v_toPure_783_; lean_object* v___x_784_; 
lean_dec_ref(v___f_780_);
lean_dec_ref(v_buckets_771_);
v_toApplicative_782_ = lean_ctor_get(v_inst_768_, 0);
lean_inc_ref(v_toApplicative_782_);
lean_dec_ref(v_inst_768_);
v_toPure_783_ = lean_ctor_get(v_toApplicative_782_, 1);
lean_inc(v_toPure_783_);
lean_dec_ref(v_toApplicative_782_);
v___x_784_ = lean_apply_2(v_toPure_783_, lean_box(0), v___x_774_);
return v___x_784_;
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_of_nat(v___x_773_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_768_, v___f_780_, v_buckets_771_, v___x_785_, v___x_786_, v___x_774_);
return v___x_787_;
}
}
else
{
size_t v___x_788_; size_t v___x_789_; lean_object* v___x_790_; 
v___x_788_ = ((size_t)0ULL);
v___x_789_ = lean_usize_of_nat(v___x_773_);
v___x_790_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_768_, v___f_780_, v_buckets_771_, v___x_788_, v___x_789_, v___x_774_);
return v___x_790_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___boxed(lean_object* v_00_u03b1_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_m_794_, lean_object* v_inst_795_, lean_object* v_f_796_, lean_object* v_b_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Std_HashSet_forM(v_00_u03b1_791_, v_x_792_, v_x_793_, v_m_794_, v_inst_795_, v_f_796_, v_b_797_);
lean_dec_ref(v_x_793_);
lean_dec_ref(v_x_792_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0(lean_object* v_f_799_, lean_object* v_a_800_, lean_object* v_x_801_, lean_object* v_acc_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = lean_apply_2(v_f_799_, v_a_800_, v_acc_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__1(lean_object* v_inst_804_, lean_object* v___f_805_, lean_object* v_a_806_, lean_object* v_x_807_, lean_object* v___y_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_804_, v___f_805_, v_a_806_, v___y_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg(lean_object* v_inst_810_, lean_object* v_f_811_, lean_object* v_init_812_, lean_object* v_b_813_){
_start:
{
lean_object* v_buckets_814_; lean_object* v___f_815_; lean_object* v___f_816_; size_t v_sz_817_; size_t v___x_818_; lean_object* v___x_819_; 
v_buckets_814_ = lean_ctor_get(v_b_813_, 1);
lean_inc_ref(v_buckets_814_);
lean_dec_ref(v_b_813_);
v___f_815_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_815_, 0, v_f_811_);
lean_inc_ref(v_inst_810_);
v___f_816_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_816_, 0, v_inst_810_);
lean_closure_set(v___f_816_, 1, v___f_815_);
v_sz_817_ = lean_array_size(v_buckets_814_);
v___x_818_ = ((size_t)0ULL);
v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_810_, v_buckets_814_, v___f_816_, v_sz_817_, v___x_818_, v_init_812_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn(lean_object* v_00_u03b1_820_, lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_m_823_, lean_object* v_inst_824_, lean_object* v_00_u03b2_825_, lean_object* v_f_826_, lean_object* v_init_827_, lean_object* v_b_828_){
_start:
{
lean_object* v_buckets_829_; lean_object* v___f_830_; lean_object* v___f_831_; size_t v_sz_832_; size_t v___x_833_; lean_object* v___x_834_; 
v_buckets_829_ = lean_ctor_get(v_b_828_, 1);
lean_inc_ref(v_buckets_829_);
lean_dec_ref(v_b_828_);
v___f_830_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_830_, 0, v_f_826_);
lean_inc_ref(v_inst_824_);
v___f_831_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_831_, 0, v_inst_824_);
lean_closure_set(v___f_831_, 1, v___f_830_);
v_sz_832_ = lean_array_size(v_buckets_829_);
v___x_833_ = ((size_t)0ULL);
v___x_834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_824_, v_buckets_829_, v___f_831_, v_sz_832_, v___x_833_, v_init_827_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___boxed(lean_object* v_00_u03b1_835_, lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_m_838_, lean_object* v_inst_839_, lean_object* v_00_u03b2_840_, lean_object* v_f_841_, lean_object* v_init_842_, lean_object* v_b_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Std_HashSet_forIn(v_00_u03b1_835_, v_x_836_, v_x_837_, v_m_838_, v_inst_839_, v_00_u03b2_840_, v_f_841_, v_init_842_, v_b_843_);
lean_dec_ref(v_x_837_);
lean_dec_ref(v_x_836_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg___lam__2(lean_object* v_inst_845_, lean_object* v_m_846_, lean_object* v_f_847_){
_start:
{
lean_object* v_buckets_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_buckets_848_ = lean_ctor_get(v_m_846_, 1);
lean_inc_ref(v_buckets_848_);
lean_dec_ref(v_m_846_);
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_array_get_size(v_buckets_848_);
v___x_851_ = lean_box(0);
v___x_852_ = lean_nat_dec_lt(v___x_849_, v___x_850_);
if (v___x_852_ == 0)
{
lean_object* v_toApplicative_853_; lean_object* v_toPure_854_; lean_object* v___x_855_; 
lean_dec_ref(v_buckets_848_);
lean_dec(v_f_847_);
v_toApplicative_853_ = lean_ctor_get(v_inst_845_, 0);
lean_inc_ref(v_toApplicative_853_);
lean_dec_ref(v_inst_845_);
v_toPure_854_ = lean_ctor_get(v_toApplicative_853_, 1);
lean_inc(v_toPure_854_);
lean_dec_ref(v_toApplicative_853_);
v___x_855_ = lean_apply_2(v_toPure_854_, lean_box(0), v___x_851_);
return v___x_855_;
}
else
{
lean_object* v___f_856_; lean_object* v___f_857_; uint8_t v___x_858_; 
v___f_856_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_856_, 0, v_f_847_);
lean_inc_ref(v_inst_845_);
v___f_857_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_857_, 0, v_inst_845_);
lean_closure_set(v___f_857_, 1, v___f_856_);
v___x_858_ = lean_nat_dec_le(v___x_850_, v___x_850_);
if (v___x_858_ == 0)
{
if (v___x_852_ == 0)
{
lean_object* v_toApplicative_859_; lean_object* v_toPure_860_; lean_object* v___x_861_; 
lean_dec_ref(v___f_857_);
lean_dec_ref(v_buckets_848_);
v_toApplicative_859_ = lean_ctor_get(v_inst_845_, 0);
lean_inc_ref(v_toApplicative_859_);
lean_dec_ref(v_inst_845_);
v_toPure_860_ = lean_ctor_get(v_toApplicative_859_, 1);
lean_inc(v_toPure_860_);
lean_dec_ref(v_toApplicative_859_);
v___x_861_ = lean_apply_2(v_toPure_860_, lean_box(0), v___x_851_);
return v___x_861_;
}
else
{
size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
v___x_862_ = ((size_t)0ULL);
v___x_863_ = lean_usize_of_nat(v___x_850_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_845_, v___f_857_, v_buckets_848_, v___x_862_, v___x_863_, v___x_851_);
return v___x_864_;
}
}
else
{
size_t v___x_865_; size_t v___x_866_; lean_object* v___x_867_; 
v___x_865_ = ((size_t)0ULL);
v___x_866_ = lean_usize_of_nat(v___x_850_);
v___x_867_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_845_, v___f_857_, v_buckets_848_, v___x_865_, v___x_866_, v___x_851_);
return v___x_867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg(lean_object* v_inst_868_){
_start:
{
lean_object* v___f_869_; 
v___f_869_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_869_, 0, v_inst_868_);
return v___f_869_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad(lean_object* v_00_u03b1_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_m_873_, lean_object* v_inst_874_){
_start:
{
lean_object* v___f_875_; 
v___f_875_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_875_, 0, v_inst_874_);
return v___f_875_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_876_, lean_object* v_inst_877_, lean_object* v_inst_878_, lean_object* v_m_879_, lean_object* v_inst_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_Std_HashSet_instForMOfMonad(v_00_u03b1_876_, v_inst_877_, v_inst_878_, v_m_879_, v_inst_880_);
lean_dec_ref(v_inst_878_);
lean_dec_ref(v_inst_877_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg___lam__2(lean_object* v_inst_882_, lean_object* v_00_u03b2_883_, lean_object* v_m_884_, lean_object* v_init_885_, lean_object* v_f_886_){
_start:
{
lean_object* v_buckets_887_; lean_object* v___f_888_; lean_object* v___f_889_; size_t v_sz_890_; size_t v___x_891_; lean_object* v___x_892_; 
v_buckets_887_ = lean_ctor_get(v_m_884_, 1);
lean_inc_ref(v_buckets_887_);
lean_dec_ref(v_m_884_);
v___f_888_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_888_, 0, v_f_886_);
lean_inc_ref(v_inst_882_);
v___f_889_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_889_, 0, v_inst_882_);
lean_closure_set(v___f_889_, 1, v___f_888_);
v_sz_890_ = lean_array_size(v_buckets_887_);
v___x_891_ = ((size_t)0ULL);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_882_, v_buckets_887_, v___f_889_, v_sz_890_, v___x_891_, v_init_885_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg(lean_object* v_inst_893_){
_start:
{
lean_object* v___f_894_; 
v___f_894_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_894_, 0, v_inst_893_);
return v___f_894_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad(lean_object* v_00_u03b1_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_m_898_, lean_object* v_inst_899_){
_start:
{
lean_object* v___f_900_; 
v___f_900_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_900_, 0, v_inst_899_);
return v___f_900_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_m_904_, lean_object* v_inst_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_HashSet_instForInOfMonad(v_00_u03b1_901_, v_inst_902_, v_inst_903_, v_m_904_, v_inst_905_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
return v_res_906_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_filter___redArg___lam__0(lean_object* v_f_907_, lean_object* v_a_908_, lean_object* v_x_909_){
_start:
{
lean_object* v___x_910_; uint8_t v___x_911_; 
v___x_910_ = lean_apply_1(v_f_907_, v_a_908_);
v___x_911_ = lean_unbox(v___x_910_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__0___boxed(lean_object* v_f_912_, lean_object* v_a_913_, lean_object* v_x_914_){
_start:
{
uint8_t v_res_915_; lean_object* v_r_916_; 
v_res_915_ = l_Std_HashSet_filter___redArg___lam__0(v_f_912_, v_a_913_, v_x_914_);
v_r_916_ = lean_box(v_res_915_);
return v_r_916_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg(lean_object* v_f_917_, lean_object* v_m_918_){
_start:
{
lean_object* v___f_919_; lean_object* v___x_920_; 
v___f_919_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_919_, 0, v_f_917_);
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_919_, v_m_918_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter(lean_object* v_00_u03b1_921_, lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_f_924_, lean_object* v_m_925_){
_start:
{
lean_object* v___f_926_; lean_object* v___x_927_; 
v___f_926_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_926_, 0, v_f_924_);
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_926_, v_m_925_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___boxed(lean_object* v_00_u03b1_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_f_931_, lean_object* v_m_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_HashSet_filter(v_00_u03b1_928_, v_x_929_, v_x_930_, v_f_931_, v_m_932_);
lean_dec_ref(v_x_930_);
lean_dec_ref(v_x_929_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg(lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_inst_936_, lean_object* v_m_937_, lean_object* v_l_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_936_, v_x_934_, v_x_935_, v_m_937_, v_l_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany(lean_object* v_00_u03b1_940_, lean_object* v_x_941_, lean_object* v_x_942_, lean_object* v_00_u03c1_943_, lean_object* v_inst_944_, lean_object* v_m_945_, lean_object* v_l_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_944_, v_x_941_, v_x_942_, v_m_945_, v_l_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0(lean_object* v_x1_948_, lean_object* v_x2_949_, lean_object* v_x3_950_){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lean_array_push(v_x1_948_, v_x2_949_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__1(lean_object* v___x_952_, lean_object* v___f_953_, lean_object* v_acc_954_, lean_object* v_l_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_952_, v___f_953_, v_acc_954_, v_l_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg(lean_object* v_m_961_){
_start:
{
lean_object* v_size_962_; lean_object* v_buckets_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_size_962_ = lean_ctor_get(v_m_961_, 0);
lean_inc(v_size_962_);
v_buckets_963_ = lean_ctor_get(v_m_961_, 1);
lean_inc_ref(v_buckets_963_);
lean_dec_ref(v_m_961_);
v___x_964_ = lean_mk_empty_array_with_capacity(v_size_962_);
lean_dec(v_size_962_);
v___x_965_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_array_get_size(v_buckets_963_);
v___x_968_ = lean_nat_dec_lt(v___x_966_, v___x_967_);
if (v___x_968_ == 0)
{
lean_dec_ref(v_buckets_963_);
return v___x_964_;
}
else
{
lean_object* v___f_969_; uint8_t v___x_970_; 
v___f_969_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__1));
v___x_970_ = lean_nat_dec_le(v___x_967_, v___x_967_);
if (v___x_970_ == 0)
{
if (v___x_968_ == 0)
{
lean_dec_ref(v_buckets_963_);
return v___x_964_;
}
else
{
size_t v___x_971_; size_t v___x_972_; lean_object* v___x_973_; 
v___x_971_ = ((size_t)0ULL);
v___x_972_ = lean_usize_of_nat(v___x_967_);
v___x_973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_965_, v___f_969_, v_buckets_963_, v___x_971_, v___x_972_, v___x_964_);
return v___x_973_;
}
}
else
{
size_t v___x_974_; size_t v___x_975_; lean_object* v___x_976_; 
v___x_974_ = ((size_t)0ULL);
v___x_975_ = lean_usize_of_nat(v___x_967_);
v___x_976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_965_, v___f_969_, v_buckets_963_, v___x_974_, v___x_975_, v___x_964_);
return v___x_976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray(lean_object* v_00_u03b1_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_m_980_){
_start:
{
lean_object* v_size_981_; lean_object* v_buckets_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; uint8_t v___x_987_; 
v_size_981_ = lean_ctor_get(v_m_980_, 0);
lean_inc(v_size_981_);
v_buckets_982_ = lean_ctor_get(v_m_980_, 1);
lean_inc_ref(v_buckets_982_);
lean_dec_ref(v_m_980_);
v___x_983_ = lean_mk_empty_array_with_capacity(v_size_981_);
lean_dec(v_size_981_);
v___x_984_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_array_get_size(v_buckets_982_);
v___x_987_ = lean_nat_dec_lt(v___x_985_, v___x_986_);
if (v___x_987_ == 0)
{
lean_dec_ref(v_buckets_982_);
return v___x_983_;
}
else
{
lean_object* v___f_988_; uint8_t v___x_989_; 
v___f_988_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__1));
v___x_989_ = lean_nat_dec_le(v___x_986_, v___x_986_);
if (v___x_989_ == 0)
{
if (v___x_987_ == 0)
{
lean_dec_ref(v_buckets_982_);
return v___x_983_;
}
else
{
size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
v___x_990_ = ((size_t)0ULL);
v___x_991_ = lean_usize_of_nat(v___x_986_);
v___x_992_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_984_, v___f_988_, v_buckets_982_, v___x_990_, v___x_991_, v___x_983_);
return v___x_992_;
}
}
else
{
size_t v___x_993_; size_t v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((size_t)0ULL);
v___x_994_ = lean_usize_of_nat(v___x_986_);
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_984_, v___f_988_, v_buckets_982_, v___x_993_, v___x_994_, v___x_983_);
return v___x_995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___boxed(lean_object* v_00_u03b1_996_, lean_object* v_x_997_, lean_object* v_x_998_, lean_object* v_m_999_){
_start:
{
lean_object* v_res_1000_; 
v_res_1000_ = l_Std_HashSet_toArray(v_00_u03b1_996_, v_x_997_, v_x_998_, v_m_999_);
lean_dec_ref(v_x_998_);
lean_dec_ref(v_x_997_);
return v_res_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0(lean_object* v_p_1001_, lean_object* v___x_1002_, lean_object* v___x_1003_, lean_object* v_a_1004_, lean_object* v_b_1005_, lean_object* v_acc_1006_){
_start:
{
lean_object* v___x_1007_; uint8_t v___x_1008_; 
v___x_1007_ = lean_apply_1(v_p_1001_, v_a_1004_);
v___x_1008_ = lean_unbox(v___x_1007_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec_ref(v___x_1003_);
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1007_);
v___x_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
lean_ctor_set(v___x_1010_, 1, v___x_1002_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1003_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0___boxed(lean_object* v_p_1013_, lean_object* v___x_1014_, lean_object* v___x_1015_, lean_object* v_a_1016_, lean_object* v_b_1017_, lean_object* v_acc_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_Std_HashSet_all___redArg___lam__0(v_p_1013_, v___x_1014_, v___x_1015_, v_a_1016_, v_b_1017_, v_acc_1018_);
lean_dec_ref(v_acc_1018_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__1(lean_object* v___x_1020_, lean_object* v___f_1021_, lean_object* v_a_1022_, lean_object* v_x_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1020_, v___f_1021_, v_a_1022_, v___y_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all___redArg(lean_object* v_m_1029_, lean_object* v_p_1030_){
_start:
{
lean_object* v___x_1031_; lean_object* v_buckets_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___f_1035_; lean_object* v___f_1036_; size_t v_sz_1037_; size_t v___x_1038_; lean_object* v___x_1039_; lean_object* v_fst_1040_; 
v___x_1031_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1032_ = lean_ctor_get(v_m_1029_, 1);
lean_inc_ref(v_buckets_1032_);
lean_dec_ref(v_m_1029_);
v___x_1033_ = lean_box(0);
v___x_1034_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1035_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1035_, 0, v_p_1030_);
lean_closure_set(v___f_1035_, 1, v___x_1033_);
lean_closure_set(v___f_1035_, 2, v___x_1034_);
v___f_1036_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1036_, 0, v___x_1031_);
lean_closure_set(v___f_1036_, 1, v___f_1035_);
v_sz_1037_ = lean_array_size(v_buckets_1032_);
v___x_1038_ = ((size_t)0ULL);
v___x_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1031_, v_buckets_1032_, v___f_1036_, v_sz_1037_, v___x_1038_, v___x_1034_);
v_fst_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_fst_1040_);
lean_dec(v___x_1039_);
if (lean_obj_tag(v_fst_1040_) == 0)
{
uint8_t v___x_1041_; 
v___x_1041_ = 1;
return v___x_1041_;
}
else
{
lean_object* v_val_1042_; uint8_t v___x_1043_; 
v_val_1042_ = lean_ctor_get(v_fst_1040_, 0);
lean_inc(v_val_1042_);
lean_dec_ref(v_fst_1040_);
v___x_1043_ = lean_unbox(v_val_1042_);
lean_dec(v_val_1042_);
return v___x_1043_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___boxed(lean_object* v_m_1044_, lean_object* v_p_1045_){
_start:
{
uint8_t v_res_1046_; lean_object* v_r_1047_; 
v_res_1046_ = l_Std_HashSet_all___redArg(v_m_1044_, v_p_1045_);
v_r_1047_ = lean_box(v_res_1046_);
return v_r_1047_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all(lean_object* v_00_u03b1_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_m_1051_, lean_object* v_p_1052_){
_start:
{
lean_object* v___x_1053_; lean_object* v_buckets_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___f_1057_; lean_object* v___f_1058_; size_t v_sz_1059_; size_t v___x_1060_; lean_object* v___x_1061_; lean_object* v_fst_1062_; 
v___x_1053_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1054_ = lean_ctor_get(v_m_1051_, 1);
lean_inc_ref(v_buckets_1054_);
lean_dec_ref(v_m_1051_);
v___x_1055_ = lean_box(0);
v___x_1056_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1057_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1057_, 0, v_p_1052_);
lean_closure_set(v___f_1057_, 1, v___x_1055_);
lean_closure_set(v___f_1057_, 2, v___x_1056_);
v___f_1058_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1058_, 0, v___x_1053_);
lean_closure_set(v___f_1058_, 1, v___f_1057_);
v_sz_1059_ = lean_array_size(v_buckets_1054_);
v___x_1060_ = ((size_t)0ULL);
v___x_1061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1053_, v_buckets_1054_, v___f_1058_, v_sz_1059_, v___x_1060_, v___x_1056_);
v_fst_1062_ = lean_ctor_get(v___x_1061_, 0);
lean_inc(v_fst_1062_);
lean_dec(v___x_1061_);
if (lean_obj_tag(v_fst_1062_) == 0)
{
uint8_t v___x_1063_; 
v___x_1063_ = 1;
return v___x_1063_;
}
else
{
lean_object* v_val_1064_; uint8_t v___x_1065_; 
v_val_1064_ = lean_ctor_get(v_fst_1062_, 0);
lean_inc(v_val_1064_);
lean_dec_ref(v_fst_1062_);
v___x_1065_ = lean_unbox(v_val_1064_);
lean_dec(v_val_1064_);
return v___x_1065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___boxed(lean_object* v_00_u03b1_1066_, lean_object* v_x_1067_, lean_object* v_x_1068_, lean_object* v_m_1069_, lean_object* v_p_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Std_HashSet_all(v_00_u03b1_1066_, v_x_1067_, v_x_1068_, v_m_1069_, v_p_1070_);
lean_dec_ref(v_x_1068_);
lean_dec_ref(v_x_1067_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0(lean_object* v_p_1073_, lean_object* v___x_1074_, lean_object* v___x_1075_, lean_object* v_a_1076_, lean_object* v_b_1077_, lean_object* v_acc_1078_){
_start:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_apply_1(v_p_1073_, v_a_1076_);
v___x_1080_ = lean_unbox(v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1074_);
return v___x_1081_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
lean_dec_ref(v___x_1074_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1079_);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v___x_1075_);
v___x_1084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1083_);
return v___x_1084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0___boxed(lean_object* v_p_1085_, lean_object* v___x_1086_, lean_object* v___x_1087_, lean_object* v_a_1088_, lean_object* v_b_1089_, lean_object* v_acc_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_HashSet_any___redArg___lam__0(v_p_1085_, v___x_1086_, v___x_1087_, v_a_1088_, v_b_1089_, v_acc_1090_);
lean_dec_ref(v_acc_1090_);
return v_res_1091_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any___redArg(lean_object* v_m_1092_, lean_object* v_p_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v_buckets_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___f_1098_; lean_object* v___f_1099_; size_t v_sz_1100_; size_t v___x_1101_; lean_object* v___x_1102_; lean_object* v_fst_1103_; 
v___x_1094_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1095_ = lean_ctor_get(v_m_1092_, 1);
lean_inc_ref(v_buckets_1095_);
lean_dec_ref(v_m_1092_);
v___x_1096_ = lean_box(0);
v___x_1097_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1098_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1098_, 0, v_p_1093_);
lean_closure_set(v___f_1098_, 1, v___x_1097_);
lean_closure_set(v___f_1098_, 2, v___x_1096_);
v___f_1099_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1099_, 0, v___x_1094_);
lean_closure_set(v___f_1099_, 1, v___f_1098_);
v_sz_1100_ = lean_array_size(v_buckets_1095_);
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1094_, v_buckets_1095_, v___f_1099_, v_sz_1100_, v___x_1101_, v___x_1097_);
v_fst_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_fst_1103_);
lean_dec(v___x_1102_);
if (lean_obj_tag(v_fst_1103_) == 0)
{
uint8_t v___x_1104_; 
v___x_1104_ = 0;
return v___x_1104_;
}
else
{
lean_object* v_val_1105_; uint8_t v___x_1106_; 
v_val_1105_ = lean_ctor_get(v_fst_1103_, 0);
lean_inc(v_val_1105_);
lean_dec_ref(v_fst_1103_);
v___x_1106_ = lean_unbox(v_val_1105_);
lean_dec(v_val_1105_);
return v___x_1106_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___boxed(lean_object* v_m_1107_, lean_object* v_p_1108_){
_start:
{
uint8_t v_res_1109_; lean_object* v_r_1110_; 
v_res_1109_ = l_Std_HashSet_any___redArg(v_m_1107_, v_p_1108_);
v_r_1110_ = lean_box(v_res_1109_);
return v_r_1110_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any(lean_object* v_00_u03b1_1111_, lean_object* v_x_1112_, lean_object* v_x_1113_, lean_object* v_m_1114_, lean_object* v_p_1115_){
_start:
{
lean_object* v___x_1116_; lean_object* v_buckets_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___f_1120_; lean_object* v___f_1121_; size_t v_sz_1122_; size_t v___x_1123_; lean_object* v___x_1124_; lean_object* v_fst_1125_; 
v___x_1116_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1117_ = lean_ctor_get(v_m_1114_, 1);
lean_inc_ref(v_buckets_1117_);
lean_dec_ref(v_m_1114_);
v___x_1118_ = lean_box(0);
v___x_1119_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1120_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1120_, 0, v_p_1115_);
lean_closure_set(v___f_1120_, 1, v___x_1119_);
lean_closure_set(v___f_1120_, 2, v___x_1118_);
v___f_1121_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1121_, 0, v___x_1116_);
lean_closure_set(v___f_1121_, 1, v___f_1120_);
v_sz_1122_ = lean_array_size(v_buckets_1117_);
v___x_1123_ = ((size_t)0ULL);
v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1116_, v_buckets_1117_, v___f_1121_, v_sz_1122_, v___x_1123_, v___x_1119_);
v_fst_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_fst_1125_);
lean_dec(v___x_1124_);
if (lean_obj_tag(v_fst_1125_) == 0)
{
uint8_t v___x_1126_; 
v___x_1126_ = 0;
return v___x_1126_;
}
else
{
lean_object* v_val_1127_; uint8_t v___x_1128_; 
v_val_1127_ = lean_ctor_get(v_fst_1125_, 0);
lean_inc(v_val_1127_);
lean_dec_ref(v_fst_1125_);
v___x_1128_ = lean_unbox(v_val_1127_);
lean_dec(v_val_1127_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_m_1132_, lean_object* v_p_1133_){
_start:
{
uint8_t v_res_1134_; lean_object* v_r_1135_; 
v_res_1134_ = l_Std_HashSet_any(v_00_u03b1_1129_, v_x_1130_, v_x_1131_, v_m_1132_, v_p_1133_);
lean_dec_ref(v_x_1131_);
lean_dec_ref(v_x_1130_);
v_r_1135_ = lean_box(v_res_1134_);
return v_r_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0(lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_a_1138_, lean_object* v_b_1139_, lean_object* v_acc_1140_){
_start:
{
lean_object* v_r_1141_; lean_object* v___x_1142_; 
v_r_1141_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1136_, v_inst_1137_, v_acc_1140_, v_a_1138_, v_b_1139_);
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v_r_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__1(lean_object* v___x_1143_, lean_object* v___f_1144_, lean_object* v_a_1145_, lean_object* v_x_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v___x_1148_; 
v___x_1148_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1143_, v___f_1144_, v_a_1145_, v___y_1147_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg(lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_m_u2081_1153_, lean_object* v_m_u2082_1154_){
_start:
{
lean_object* v_size_1155_; lean_object* v_buckets_1156_; lean_object* v_size_1157_; uint8_t v___x_1158_; 
v_size_1155_ = lean_ctor_get(v_m_u2081_1153_, 0);
v_buckets_1156_ = lean_ctor_get(v_m_u2081_1153_, 1);
v_size_1157_ = lean_ctor_get(v_m_u2082_1154_, 0);
v___x_1158_ = lean_nat_dec_le(v_size_1155_, v_size_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___f_1159_; lean_object* v___x_1160_; 
v___f_1159_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1160_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1159_, v_inst_1151_, v_inst_1152_, v_m_u2081_1153_, v_m_u2082_1154_);
return v___x_1160_;
}
else
{
lean_object* v___f_1161_; lean_object* v___x_1162_; lean_object* v___f_1163_; size_t v_sz_1164_; size_t v___x_1165_; lean_object* v___x_1166_; 
lean_inc_ref(v_buckets_1156_);
lean_dec_ref(v_m_u2081_1153_);
v___f_1161_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1161_, 0, v_inst_1151_);
lean_closure_set(v___f_1161_, 1, v_inst_1152_);
v___x_1162_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___f_1163_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1163_, 0, v___x_1162_);
lean_closure_set(v___f_1163_, 1, v___f_1161_);
v_sz_1164_ = lean_array_size(v_buckets_1156_);
v___x_1165_ = ((size_t)0ULL);
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1162_, v_buckets_1156_, v___f_1163_, v_sz_1164_, v___x_1165_, v_m_u2082_1154_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union(lean_object* v_00_u03b1_1167_, lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_m_u2081_1170_, lean_object* v_m_u2082_1171_){
_start:
{
lean_object* v_size_1172_; lean_object* v_buckets_1173_; lean_object* v_size_1174_; uint8_t v___x_1175_; 
v_size_1172_ = lean_ctor_get(v_m_u2081_1170_, 0);
v_buckets_1173_ = lean_ctor_get(v_m_u2081_1170_, 1);
v_size_1174_ = lean_ctor_get(v_m_u2082_1171_, 0);
v___x_1175_ = lean_nat_dec_le(v_size_1172_, v_size_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___f_1176_; lean_object* v___x_1177_; 
v___f_1176_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1177_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1176_, v_inst_1168_, v_inst_1169_, v_m_u2081_1170_, v_m_u2082_1171_);
return v___x_1177_;
}
else
{
lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___f_1180_; size_t v_sz_1181_; size_t v___x_1182_; lean_object* v___x_1183_; 
lean_inc_ref(v_buckets_1173_);
lean_dec_ref(v_m_u2081_1170_);
v___f_1178_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1178_, 0, v_inst_1168_);
lean_closure_set(v___f_1178_, 1, v_inst_1169_);
v___x_1179_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___f_1180_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1180_, 0, v___x_1179_);
lean_closure_set(v___f_1180_, 1, v___f_1178_);
v_sz_1181_ = lean_array_size(v_buckets_1173_);
v___x_1182_ = ((size_t)0ULL);
v___x_1183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1179_, v_buckets_1173_, v___f_1180_, v_sz_1181_, v___x_1182_, v_m_u2082_1171_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion___redArg(lean_object* v_inst_1184_, lean_object* v_inst_1185_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion(lean_object* v_00_u03b1_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1190_, 0, lean_box(0));
lean_closure_set(v___x_1190_, 1, v_inst_1188_);
lean_closure_set(v___x_1190_, 2, v_inst_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter___redArg(lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_m_u2081_1193_, lean_object* v_m_u2082_1194_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1191_, v_inst_1192_, v_m_u2081_1193_, v_m_u2082_1194_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter(lean_object* v_00_u03b1_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_m_u2081_1199_, lean_object* v_m_u2082_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1197_, v_inst_1198_, v_m_u2081_1199_, v_m_u2082_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter___redArg(lean_object* v_inst_1202_, lean_object* v_inst_1203_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_instInter(lean_object* v_00_u03b1_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1208_, 0, lean_box(0));
lean_closure_set(v___x_1208_, 1, v_inst_1206_);
lean_closure_set(v___x_1208_, 2, v_inst_1207_);
return v___x_1208_;
}
}
static lean_object* _init_l_Std_HashSet_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1209_; lean_object* v___f_1210_; 
v___x_1209_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1210_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1210_, 0, v___x_1209_);
return v___f_1210_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq___redArg(lean_object* v_x_1211_, lean_object* v_inst_1212_, lean_object* v_m_u2081_1213_, lean_object* v_m_u2082_1214_){
_start:
{
lean_object* v___f_1215_; uint8_t v___x_1216_; 
v___f_1215_ = lean_obj_once(&l_Std_HashSet_beq___redArg___closed__0, &l_Std_HashSet_beq___redArg___closed__0_once, _init_l_Std_HashSet_beq___redArg___closed__0);
v___x_1216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1212_, v_x_1211_, v___f_1215_, v_m_u2081_1213_, v_m_u2082_1214_);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___redArg___boxed(lean_object* v_x_1217_, lean_object* v_inst_1218_, lean_object* v_m_u2081_1219_, lean_object* v_m_u2082_1220_){
_start:
{
uint8_t v_res_1221_; lean_object* v_r_1222_; 
v_res_1221_ = l_Std_HashSet_beq___redArg(v_x_1217_, v_inst_1218_, v_m_u2081_1219_, v_m_u2082_1220_);
v_r_1222_ = lean_box(v_res_1221_);
return v_r_1222_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq(lean_object* v_00_u03b1_1223_, lean_object* v_x_1224_, lean_object* v_inst_1225_, lean_object* v_m_u2081_1226_, lean_object* v_m_u2082_1227_){
_start:
{
uint8_t v___x_1228_; 
v___x_1228_ = l_Std_HashSet_beq___redArg(v_x_1224_, v_inst_1225_, v_m_u2081_1226_, v_m_u2082_1227_);
return v___x_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___boxed(lean_object* v_00_u03b1_1229_, lean_object* v_x_1230_, lean_object* v_inst_1231_, lean_object* v_m_u2081_1232_, lean_object* v_m_u2082_1233_){
_start:
{
uint8_t v_res_1234_; lean_object* v_r_1235_; 
v_res_1234_ = l_Std_HashSet_beq(v_00_u03b1_1229_, v_x_1230_, v_inst_1231_, v_m_u2081_1232_, v_m_u2082_1233_);
v_r_1235_ = lean_box(v_res_1234_);
return v_r_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq___redArg(lean_object* v_x_1236_, lean_object* v_inst_1237_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq(lean_object* v_00_u03b1_1239_, lean_object* v_x_1240_, lean_object* v_inst_1241_){
_start:
{
lean_object* v___x_1242_; 
v___x_1242_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1242_, 0, lean_box(0));
lean_closure_set(v___x_1242_, 1, v_x_1240_);
lean_closure_set(v___x_1242_, 2, v_inst_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_diff___redArg___lam__0(lean_object* v_inst_1243_, lean_object* v_inst_1244_, lean_object* v_m_u2082_1245_, uint8_t v___x_1246_, lean_object* v_k_1247_, lean_object* v_x_1248_){
_start:
{
uint8_t v___x_1249_; 
v___x_1249_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1243_, v_inst_1244_, v_m_u2082_1245_, v_k_1247_);
if (v___x_1249_ == 0)
{
return v___x_1246_;
}
else
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg___lam__0___boxed(lean_object* v_inst_1251_, lean_object* v_inst_1252_, lean_object* v_m_u2082_1253_, lean_object* v___x_1254_, lean_object* v_k_1255_, lean_object* v_x_1256_){
_start:
{
uint8_t v___x_83__boxed_1257_; uint8_t v_res_1258_; lean_object* v_r_1259_; 
v___x_83__boxed_1257_ = lean_unbox(v___x_1254_);
v_res_1258_ = l_Std_HashSet_diff___redArg___lam__0(v_inst_1251_, v_inst_1252_, v_m_u2082_1253_, v___x_83__boxed_1257_, v_k_1255_, v_x_1256_);
lean_dec_ref(v_m_u2082_1253_);
v_r_1259_ = lean_box(v_res_1258_);
return v_r_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg(lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_m_u2081_1262_, lean_object* v_m_u2082_1263_){
_start:
{
lean_object* v_size_1264_; lean_object* v_size_1265_; uint8_t v___x_1266_; 
v_size_1264_ = lean_ctor_get(v_m_u2081_1262_, 0);
v_size_1265_ = lean_ctor_get(v_m_u2082_1263_, 0);
v___x_1266_ = lean_nat_dec_le(v_size_1264_, v_size_1265_);
if (v___x_1266_ == 0)
{
lean_object* v___f_1267_; lean_object* v___x_1268_; 
v___f_1267_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1268_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1267_, v_inst_1260_, v_inst_1261_, v_m_u2081_1262_, v_m_u2082_1263_);
return v___x_1268_;
}
else
{
lean_object* v___x_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; 
v___x_1269_ = lean_box(v___x_1266_);
v___f_1270_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1270_, 0, v_inst_1260_);
lean_closure_set(v___f_1270_, 1, v_inst_1261_);
lean_closure_set(v___f_1270_, 2, v_m_u2082_1263_);
lean_closure_set(v___f_1270_, 3, v___x_1269_);
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1270_, v_m_u2081_1262_);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff(lean_object* v_00_u03b1_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_m_u2081_1275_, lean_object* v_m_u2082_1276_){
_start:
{
lean_object* v_size_1277_; lean_object* v_size_1278_; uint8_t v___x_1279_; 
v_size_1277_ = lean_ctor_get(v_m_u2081_1275_, 0);
v_size_1278_ = lean_ctor_get(v_m_u2082_1276_, 0);
v___x_1279_ = lean_nat_dec_le(v_size_1277_, v_size_1278_);
if (v___x_1279_ == 0)
{
lean_object* v___f_1280_; lean_object* v___x_1281_; 
v___f_1280_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1281_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1280_, v_inst_1273_, v_inst_1274_, v_m_u2081_1275_, v_m_u2082_1276_);
return v___x_1281_;
}
else
{
lean_object* v___x_1282_; lean_object* v___f_1283_; lean_object* v___x_1284_; 
v___x_1282_ = lean_box(v___x_1279_);
v___f_1283_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1283_, 0, v_inst_1273_);
lean_closure_set(v___f_1283_, 1, v_inst_1274_);
lean_closure_set(v___f_1283_, 2, v_m_u2082_1276_);
lean_closure_set(v___f_1283_, 3, v___x_1282_);
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1283_, v_m_u2081_1275_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff___redArg(lean_object* v_inst_1285_, lean_object* v_inst_1286_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff(lean_object* v_00_u03b1_1288_, lean_object* v_inst_1289_, lean_object* v_inst_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1291_, 0, lean_box(0));
lean_closure_set(v___x_1291_, 1, v_inst_1289_);
lean_closure_set(v___x_1291_, 2, v_inst_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__0(lean_object* v_f_1292_, lean_object* v_x_1293_, lean_object* v_x_1294_, lean_object* v_x1_1295_, lean_object* v_x2_1296_, lean_object* v_x3_1297_){
_start:
{
lean_object* v_fst_1298_; lean_object* v_snd_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1313_; 
v_fst_1298_ = lean_ctor_get(v_x1_1295_, 0);
v_snd_1299_ = lean_ctor_get(v_x1_1295_, 1);
v_isSharedCheck_1313_ = !lean_is_exclusive(v_x1_1295_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1301_ = v_x1_1295_;
v_isShared_1302_ = v_isSharedCheck_1313_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_snd_1299_);
lean_inc(v_fst_1298_);
lean_dec(v_x1_1295_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1313_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
lean_inc(v_x2_1296_);
v___x_1303_ = lean_apply_1(v_f_1292_, v_x2_1296_);
v___x_1304_ = lean_unbox(v___x_1303_);
if (v___x_1304_ == 0)
{
lean_object* v___x_1305_; lean_object* v___x_1307_; 
v___x_1305_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1293_, v_x_1294_, v_snd_1299_, v_x2_1296_, v_x3_1297_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 1, v___x_1305_);
v___x_1307_ = v___x_1301_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_fst_1298_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___x_1305_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1311_; 
v___x_1309_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1293_, v_x_1294_, v_fst_1298_, v_x2_1296_, v_x3_1297_);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1309_);
v___x_1311_ = v___x_1301_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1309_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v_snd_1299_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__1(lean_object* v___x_1314_, lean_object* v___f_1315_, lean_object* v_acc_1316_, lean_object* v_l_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1314_, v___f_1315_, v_acc_1316_, v_l_1317_);
return v___x_1318_;
}
}
static lean_object* _init_l_Std_HashSet_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1319_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v___x_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg(lean_object* v_x_1321_, lean_object* v_x_1322_, lean_object* v_f_1323_, lean_object* v_m_1324_){
_start:
{
lean_object* v___y_1326_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v_buckets_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1336_ = lean_unsigned_to_nat(0u);
v___x_1337_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1338_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1339_ = lean_ctor_get(v_m_1324_, 1);
lean_inc_ref(v_buckets_1339_);
lean_dec_ref(v_m_1324_);
v___x_1340_ = lean_array_get_size(v_buckets_1339_);
v___x_1341_ = lean_nat_dec_lt(v___x_1336_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_dec_ref(v_buckets_1339_);
lean_dec_ref(v_f_1323_);
lean_dec_ref(v_x_1322_);
lean_dec_ref(v_x_1321_);
return v___x_1337_;
}
else
{
lean_object* v___f_1342_; lean_object* v___f_1343_; uint8_t v___x_1344_; 
v___f_1342_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1342_, 0, v_f_1323_);
lean_closure_set(v___f_1342_, 1, v_x_1321_);
lean_closure_set(v___f_1342_, 2, v_x_1322_);
v___f_1343_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1343_, 0, v___x_1338_);
lean_closure_set(v___f_1343_, 1, v___f_1342_);
v___x_1344_ = lean_nat_dec_le(v___x_1340_, v___x_1340_);
if (v___x_1344_ == 0)
{
if (v___x_1341_ == 0)
{
lean_dec_ref(v___f_1343_);
lean_dec_ref(v_buckets_1339_);
return v___x_1337_;
}
else
{
size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = lean_usize_of_nat(v___x_1340_);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1338_, v___f_1343_, v_buckets_1339_, v___x_1345_, v___x_1346_, v___x_1337_);
v___y_1326_ = v___x_1347_;
goto v___jp_1325_;
}
}
else
{
size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = lean_usize_of_nat(v___x_1340_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1338_, v___f_1343_, v_buckets_1339_, v___x_1348_, v___x_1349_, v___x_1337_);
v___y_1326_ = v___x_1350_;
goto v___jp_1325_;
}
}
v___jp_1325_:
{
lean_object* v_fst_1327_; lean_object* v_snd_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_fst_1327_ = lean_ctor_get(v___y_1326_, 0);
v_snd_1328_ = lean_ctor_get(v___y_1326_, 1);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___y_1326_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___y_1326_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_snd_1328_);
lean_inc(v_fst_1327_);
lean_dec(v___y_1326_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_fst_1327_);
lean_ctor_set(v_reuseFailAlloc_1334_, 1, v_snd_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition(lean_object* v_00_u03b1_1351_, lean_object* v_x_1352_, lean_object* v_x_1353_, lean_object* v_f_1354_, lean_object* v_m_1355_){
_start:
{
lean_object* v___y_1357_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v_buckets_1370_; lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1369_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1370_ = lean_ctor_get(v_m_1355_, 1);
lean_inc_ref(v_buckets_1370_);
lean_dec_ref(v_m_1355_);
v___x_1371_ = lean_array_get_size(v_buckets_1370_);
v___x_1372_ = lean_nat_dec_lt(v___x_1367_, v___x_1371_);
if (v___x_1372_ == 0)
{
lean_dec_ref(v_buckets_1370_);
lean_dec_ref(v_f_1354_);
lean_dec_ref(v_x_1353_);
lean_dec_ref(v_x_1352_);
return v___x_1368_;
}
else
{
lean_object* v___f_1373_; lean_object* v___f_1374_; uint8_t v___x_1375_; 
v___f_1373_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1373_, 0, v_f_1354_);
lean_closure_set(v___f_1373_, 1, v_x_1352_);
lean_closure_set(v___f_1373_, 2, v_x_1353_);
v___f_1374_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1374_, 0, v___x_1369_);
lean_closure_set(v___f_1374_, 1, v___f_1373_);
v___x_1375_ = lean_nat_dec_le(v___x_1371_, v___x_1371_);
if (v___x_1375_ == 0)
{
if (v___x_1372_ == 0)
{
lean_dec_ref(v___f_1374_);
lean_dec_ref(v_buckets_1370_);
return v___x_1368_;
}
else
{
size_t v___x_1376_; size_t v___x_1377_; lean_object* v___x_1378_; 
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = lean_usize_of_nat(v___x_1371_);
v___x_1378_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1369_, v___f_1374_, v_buckets_1370_, v___x_1376_, v___x_1377_, v___x_1368_);
v___y_1357_ = v___x_1378_;
goto v___jp_1356_;
}
}
else
{
size_t v___x_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v___x_1379_ = ((size_t)0ULL);
v___x_1380_ = lean_usize_of_nat(v___x_1371_);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1369_, v___f_1374_, v_buckets_1370_, v___x_1379_, v___x_1380_, v___x_1368_);
v___y_1357_ = v___x_1381_;
goto v___jp_1356_;
}
}
v___jp_1356_:
{
lean_object* v_fst_1358_; lean_object* v_snd_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
v_fst_1358_ = lean_ctor_get(v___y_1357_, 0);
v_snd_1359_ = lean_ctor_get(v___y_1357_, 1);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___y_1357_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___y_1357_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_snd_1359_);
lean_inc(v_fst_1358_);
lean_dec(v___y_1357_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_fst_1358_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v_snd_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray___redArg(lean_object* v_inst_1386_, lean_object* v_inst_1387_, lean_object* v_l_1388_){
_start:
{
lean_object* v___f_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___f_1389_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1390_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_1391_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1389_, v_inst_1386_, v_inst_1387_, v___x_1390_, v_l_1388_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray(lean_object* v_00_u03b1_1392_, lean_object* v_inst_1393_, lean_object* v_inst_1394_, lean_object* v_l_1395_){
_start:
{
lean_object* v___f_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___f_1396_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1397_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_1398_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1396_, v_inst_1393_, v_inst_1394_, v___x_1397_, v_l_1395_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg(lean_object* v_m_1399_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1399_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg___boxed(lean_object* v_m_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Std_HashSet_Internal_numBuckets___redArg(v_m_1401_);
lean_dec_ref(v_m_1401_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets(lean_object* v_00_u03b1_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_, lean_object* v_m_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1408_, lean_object* v_x_1409_, lean_object* v_x_1410_, lean_object* v_m_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Std_HashSet_Internal_numBuckets(v_00_u03b1_1408_, v_x_1409_, v_x_1410_, v_m_1411_);
lean_dec_ref(v_m_1411_);
lean_dec_ref(v_x_1410_);
lean_dec_ref(v_x_1409_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2(lean_object* v_inst_1416_, lean_object* v___f_1417_, lean_object* v_m_1418_, lean_object* v_prec_1419_){
_start:
{
lean_object* v___x_1420_; lean_object* v_buckets_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1441_; 
v___x_1420_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1421_ = lean_ctor_get(v_m_1418_, 1);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_m_1418_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; 
v_unused_1442_ = lean_ctor_get(v_m_1418_, 0);
lean_dec(v_unused_1442_);
v___x_1423_ = v_m_1418_;
v_isShared_1424_ = v_isSharedCheck_1441_;
goto v_resetjp_1422_;
}
else
{
lean_inc(v_buckets_1421_);
lean_dec(v_m_1418_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1441_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___y_1427_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1425_ = ((lean_object*)(l_Std_HashSet_instRepr___redArg___lam__2___closed__1));
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_array_get_size(v_buckets_1421_);
v___x_1435_ = lean_unsigned_to_nat(0u);
v___x_1436_ = lean_nat_dec_lt(v___x_1435_, v___x_1434_);
if (v___x_1436_ == 0)
{
lean_dec_ref(v_buckets_1421_);
lean_dec_ref(v___f_1417_);
v___y_1427_ = v___x_1433_;
goto v___jp_1426_;
}
else
{
lean_object* v___f_1437_; size_t v___x_1438_; size_t v___x_1439_; lean_object* v___x_1440_; 
v___f_1437_ = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1437_, 0, v___x_1420_);
lean_closure_set(v___f_1437_, 1, v___f_1417_);
v___x_1438_ = lean_usize_of_nat(v___x_1434_);
v___x_1439_ = ((size_t)0ULL);
v___x_1440_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1420_, v___f_1437_, v_buckets_1421_, v___x_1438_, v___x_1439_, v___x_1433_);
v___y_1427_ = v___x_1440_;
goto v___jp_1426_;
}
v___jp_1426_:
{
lean_object* v___x_1428_; lean_object* v___x_1430_; 
v___x_1428_ = l_List_repr___redArg(v_inst_1416_, v___y_1427_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set_tag(v___x_1423_, 5);
lean_ctor_set(v___x_1423_, 1, v___x_1428_);
lean_ctor_set(v___x_1423_, 0, v___x_1425_);
v___x_1430_ = v___x_1423_;
goto v_reusejp_1429_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1432_, 1, v___x_1428_);
v___x_1430_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1429_;
}
v_reusejp_1429_:
{
lean_object* v___x_1431_; 
v___x_1431_ = l_Repr_addAppParen(v___x_1430_, v_prec_1419_);
return v___x_1431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1443_, lean_object* v___f_1444_, lean_object* v_m_1445_, lean_object* v_prec_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Std_HashSet_instRepr___redArg___lam__2(v_inst_1443_, v___f_1444_, v_m_1445_, v_prec_1446_);
lean_dec(v_prec_1446_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg(lean_object* v_inst_1448_){
_start:
{
lean_object* v___f_1449_; lean_object* v___f_1450_; 
v___f_1449_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___f_1450_ = lean_alloc_closure((void*)(l_Std_HashSet_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1450_, 0, v_inst_1448_);
lean_closure_set(v___f_1450_, 1, v___f_1449_);
return v___f_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr(lean_object* v_00_u03b1_1451_, lean_object* v_inst_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Std_HashSet_instRepr___redArg(v_inst_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___boxed(lean_object* v_00_u03b1_1456_, lean_object* v_inst_1457_, lean_object* v_inst_1458_, lean_object* v_inst_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Std_HashSet_instRepr(v_00_u03b1_1456_, v_inst_1457_, v_inst_1458_, v_inst_1459_);
lean_dec_ref(v_inst_1458_);
lean_dec_ref(v_inst_1457_);
return v_res_1460_;
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
