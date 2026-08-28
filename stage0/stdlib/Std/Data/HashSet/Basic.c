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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_HashSet_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__9_value)} };
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
lean_object* v_toApplicative_617_; lean_object* v_buckets_618_; lean_object* v_toPure_619_; lean_object* v___x_620_; lean_object* v___x_621_; uint8_t v___x_622_; 
v_toApplicative_617_ = lean_ctor_get(v_inst_613_, 0);
v_buckets_618_ = lean_ctor_get(v_b_616_, 1);
lean_inc_ref(v_buckets_618_);
lean_dec_ref(v_b_616_);
v_toPure_619_ = lean_ctor_get(v_toApplicative_617_, 1);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_array_get_size(v_buckets_618_);
v___x_622_ = lean_nat_dec_lt(v___x_620_, v___x_621_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; 
lean_inc(v_toPure_619_);
lean_dec_ref(v_buckets_618_);
lean_dec(v_f_614_);
lean_dec_ref(v_inst_613_);
v___x_623_ = lean_apply_2(v_toPure_619_, lean_box(0), v_init_615_);
return v___x_623_;
}
else
{
lean_object* v___f_624_; lean_object* v___f_625_; size_t v___x_626_; size_t v___x_627_; lean_object* v___x_628_; 
v___f_624_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_624_, 0, v_f_614_);
lean_inc_ref(v_inst_613_);
v___f_625_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_625_, 0, v_inst_613_);
lean_closure_set(v___f_625_, 1, v___f_624_);
v___x_626_ = ((size_t)0ULL);
v___x_627_ = lean_usize_of_nat(v___x_621_);
v___x_628_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_613_, v___f_625_, v_buckets_618_, v___x_626_, v___x_627_, v_init_615_);
return v___x_628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM(lean_object* v_00_u03b1_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v_m_632_, lean_object* v_inst_633_, lean_object* v_00_u03b2_634_, lean_object* v_f_635_, lean_object* v_init_636_, lean_object* v_b_637_){
_start:
{
lean_object* v_toApplicative_638_; lean_object* v_buckets_639_; lean_object* v_toPure_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v_toApplicative_638_ = lean_ctor_get(v_inst_633_, 0);
v_buckets_639_ = lean_ctor_get(v_b_637_, 1);
lean_inc_ref(v_buckets_639_);
lean_dec_ref(v_b_637_);
v_toPure_640_ = lean_ctor_get(v_toApplicative_638_, 1);
v___x_641_ = lean_unsigned_to_nat(0u);
v___x_642_ = lean_array_get_size(v_buckets_639_);
v___x_643_ = lean_nat_dec_lt(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; 
lean_inc(v_toPure_640_);
lean_dec_ref(v_buckets_639_);
lean_dec(v_f_635_);
lean_dec_ref(v_inst_633_);
v___x_644_ = lean_apply_2(v_toPure_640_, lean_box(0), v_init_636_);
return v___x_644_;
}
else
{
lean_object* v___f_645_; lean_object* v___f_646_; size_t v___x_647_; size_t v___x_648_; lean_object* v___x_649_; 
v___f_645_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_645_, 0, v_f_635_);
lean_inc_ref(v_inst_633_);
v___f_646_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_646_, 0, v_inst_633_);
lean_closure_set(v___f_646_, 1, v___f_645_);
v___x_647_ = ((size_t)0ULL);
v___x_648_ = lean_usize_of_nat(v___x_642_);
v___x_649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_633_, v___f_646_, v_buckets_639_, v___x_647_, v___x_648_, v_init_636_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___boxed(lean_object* v_00_u03b1_650_, lean_object* v_x_651_, lean_object* v_x_652_, lean_object* v_m_653_, lean_object* v_inst_654_, lean_object* v_00_u03b2_655_, lean_object* v_f_656_, lean_object* v_init_657_, lean_object* v_b_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_HashSet_foldM(v_00_u03b1_650_, v_x_651_, v_x_652_, v_m_653_, v_inst_654_, v_00_u03b2_655_, v_f_656_, v_init_657_, v_b_658_);
lean_dec_ref(v_x_652_);
lean_dec_ref(v_x_651_);
return v_res_659_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__0(lean_object* v_f_660_, lean_object* v_x1_661_, lean_object* v_x2_662_, lean_object* v_x3_663_){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = lean_apply_2(v_f_660_, v_x1_661_, v_x2_662_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__1(lean_object* v___x_665_, lean_object* v___f_666_, lean_object* v_acc_667_, lean_object* v_l_668_){
_start:
{
lean_object* v___x_669_; 
v___x_669_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_665_, v___f_666_, v_acc_667_, v_l_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg(lean_object* v_f_670_, lean_object* v_init_671_, lean_object* v_m_672_){
_start:
{
lean_object* v___x_673_; lean_object* v_buckets_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v___x_673_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_674_ = lean_ctor_get(v_m_672_, 1);
lean_inc_ref(v_buckets_674_);
lean_dec_ref(v_m_672_);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_array_get_size(v_buckets_674_);
v___x_677_ = lean_nat_dec_lt(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
lean_dec_ref(v_buckets_674_);
lean_dec(v_f_670_);
return v_init_671_;
}
else
{
lean_object* v___f_678_; lean_object* v___f_679_; size_t v___x_680_; size_t v___x_681_; lean_object* v___x_682_; 
v___f_678_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_678_, 0, v_f_670_);
v___f_679_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_679_, 0, v___x_673_);
lean_closure_set(v___f_679_, 1, v___f_678_);
v___x_680_ = ((size_t)0ULL);
v___x_681_ = lean_usize_of_nat(v___x_676_);
v___x_682_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_673_, v___f_679_, v_buckets_674_, v___x_680_, v___x_681_, v_init_671_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold(lean_object* v_00_u03b1_683_, lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_00_u03b2_686_, lean_object* v_f_687_, lean_object* v_init_688_, lean_object* v_m_689_){
_start:
{
lean_object* v___x_690_; lean_object* v_buckets_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v___x_690_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_691_ = lean_ctor_get(v_m_689_, 1);
lean_inc_ref(v_buckets_691_);
lean_dec_ref(v_m_689_);
v___x_692_ = lean_unsigned_to_nat(0u);
v___x_693_ = lean_array_get_size(v_buckets_691_);
v___x_694_ = lean_nat_dec_lt(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_dec_ref(v_buckets_691_);
lean_dec(v_f_687_);
return v_init_688_;
}
else
{
lean_object* v___f_695_; lean_object* v___f_696_; size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___f_695_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_695_, 0, v_f_687_);
v___f_696_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_696_, 0, v___x_690_);
lean_closure_set(v___f_696_, 1, v___f_695_);
v___x_697_ = ((size_t)0ULL);
v___x_698_ = lean_usize_of_nat(v___x_693_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_690_, v___f_696_, v_buckets_691_, v___x_697_, v___x_698_, v_init_688_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___boxed(lean_object* v_00_u03b1_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_00_u03b2_703_, lean_object* v_f_704_, lean_object* v_init_705_, lean_object* v_m_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_Std_HashSet_fold(v_00_u03b1_700_, v_x_701_, v_x_702_, v_00_u03b2_703_, v_f_704_, v_init_705_, v_m_706_);
lean_dec_ref(v_x_702_);
lean_dec_ref(v_x_701_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0(lean_object* v_f_708_, lean_object* v_x_709_, lean_object* v___y_710_, lean_object* v___y_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = lean_apply_1(v_f_708_, v___y_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__1(lean_object* v_inst_713_, lean_object* v___f_714_, lean_object* v_x_715_, lean_object* v___y_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_box(0);
v___x_718_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_713_, v___f_714_, v___x_717_, v___y_716_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg(lean_object* v_inst_719_, lean_object* v_f_720_, lean_object* v_b_721_){
_start:
{
lean_object* v_toApplicative_722_; lean_object* v_buckets_723_; lean_object* v_toPure_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; uint8_t v___x_728_; 
v_toApplicative_722_ = lean_ctor_get(v_inst_719_, 0);
v_buckets_723_ = lean_ctor_get(v_b_721_, 1);
lean_inc_ref(v_buckets_723_);
lean_dec_ref(v_b_721_);
v_toPure_724_ = lean_ctor_get(v_toApplicative_722_, 1);
v___x_725_ = lean_unsigned_to_nat(0u);
v___x_726_ = lean_array_get_size(v_buckets_723_);
v___x_727_ = lean_box(0);
v___x_728_ = lean_nat_dec_lt(v___x_725_, v___x_726_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_inc(v_toPure_724_);
lean_dec_ref(v_buckets_723_);
lean_dec(v_f_720_);
lean_dec_ref(v_inst_719_);
v___x_729_ = lean_apply_2(v_toPure_724_, lean_box(0), v___x_727_);
return v___x_729_;
}
else
{
lean_object* v___f_730_; lean_object* v___f_731_; size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; 
v___f_730_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_730_, 0, v_f_720_);
lean_inc_ref(v_inst_719_);
v___f_731_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_731_, 0, v_inst_719_);
lean_closure_set(v___f_731_, 1, v___f_730_);
v___x_732_ = ((size_t)0ULL);
v___x_733_ = lean_usize_of_nat(v___x_726_);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_719_, v___f_731_, v_buckets_723_, v___x_732_, v___x_733_, v___x_727_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM(lean_object* v_00_u03b1_735_, lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_m_738_, lean_object* v_inst_739_, lean_object* v_f_740_, lean_object* v_b_741_){
_start:
{
lean_object* v_toApplicative_742_; lean_object* v_buckets_743_; lean_object* v_toPure_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_toApplicative_742_ = lean_ctor_get(v_inst_739_, 0);
v_buckets_743_ = lean_ctor_get(v_b_741_, 1);
lean_inc_ref(v_buckets_743_);
lean_dec_ref(v_b_741_);
v_toPure_744_ = lean_ctor_get(v_toApplicative_742_, 1);
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = lean_array_get_size(v_buckets_743_);
v___x_747_ = lean_box(0);
v___x_748_ = lean_nat_dec_lt(v___x_745_, v___x_746_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; 
lean_inc(v_toPure_744_);
lean_dec_ref(v_buckets_743_);
lean_dec(v_f_740_);
lean_dec_ref(v_inst_739_);
v___x_749_ = lean_apply_2(v_toPure_744_, lean_box(0), v___x_747_);
return v___x_749_;
}
else
{
lean_object* v___f_750_; lean_object* v___f_751_; size_t v___x_752_; size_t v___x_753_; lean_object* v___x_754_; 
v___f_750_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_750_, 0, v_f_740_);
lean_inc_ref(v_inst_739_);
v___f_751_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_751_, 0, v_inst_739_);
lean_closure_set(v___f_751_, 1, v___f_750_);
v___x_752_ = ((size_t)0ULL);
v___x_753_ = lean_usize_of_nat(v___x_746_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_739_, v___f_751_, v_buckets_743_, v___x_752_, v___x_753_, v___x_747_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___boxed(lean_object* v_00_u03b1_755_, lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_m_758_, lean_object* v_inst_759_, lean_object* v_f_760_, lean_object* v_b_761_){
_start:
{
lean_object* v_res_762_; 
v_res_762_ = l_Std_HashSet_forM(v_00_u03b1_755_, v_x_756_, v_x_757_, v_m_758_, v_inst_759_, v_f_760_, v_b_761_);
lean_dec_ref(v_x_757_);
lean_dec_ref(v_x_756_);
return v_res_762_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0(lean_object* v_f_763_, lean_object* v_a_764_, lean_object* v_x_765_, lean_object* v_acc_766_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = lean_apply_2(v_f_763_, v_a_764_, v_acc_766_);
return v___x_767_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__1(lean_object* v_inst_768_, lean_object* v___f_769_, lean_object* v_a_770_, lean_object* v_x_771_, lean_object* v___y_772_){
_start:
{
lean_object* v___x_773_; 
v___x_773_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_768_, v___f_769_, v_a_770_, v___y_772_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg(lean_object* v_inst_774_, lean_object* v_f_775_, lean_object* v_init_776_, lean_object* v_b_777_){
_start:
{
lean_object* v_buckets_778_; lean_object* v___f_779_; lean_object* v___f_780_; size_t v_sz_781_; size_t v___x_782_; lean_object* v___x_783_; 
v_buckets_778_ = lean_ctor_get(v_b_777_, 1);
lean_inc_ref(v_buckets_778_);
lean_dec_ref(v_b_777_);
v___f_779_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_779_, 0, v_f_775_);
lean_inc_ref(v_inst_774_);
v___f_780_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_780_, 0, v_inst_774_);
lean_closure_set(v___f_780_, 1, v___f_779_);
v_sz_781_ = lean_array_size(v_buckets_778_);
v___x_782_ = ((size_t)0ULL);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_774_, v_buckets_778_, v___f_780_, v_sz_781_, v___x_782_, v_init_776_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn(lean_object* v_00_u03b1_784_, lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_m_787_, lean_object* v_inst_788_, lean_object* v_00_u03b2_789_, lean_object* v_f_790_, lean_object* v_init_791_, lean_object* v_b_792_){
_start:
{
lean_object* v_buckets_793_; lean_object* v___f_794_; lean_object* v___f_795_; size_t v_sz_796_; size_t v___x_797_; lean_object* v___x_798_; 
v_buckets_793_ = lean_ctor_get(v_b_792_, 1);
lean_inc_ref(v_buckets_793_);
lean_dec_ref(v_b_792_);
v___f_794_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_794_, 0, v_f_790_);
lean_inc_ref(v_inst_788_);
v___f_795_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_795_, 0, v_inst_788_);
lean_closure_set(v___f_795_, 1, v___f_794_);
v_sz_796_ = lean_array_size(v_buckets_793_);
v___x_797_ = ((size_t)0ULL);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_788_, v_buckets_793_, v___f_795_, v_sz_796_, v___x_797_, v_init_791_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___boxed(lean_object* v_00_u03b1_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_m_802_, lean_object* v_inst_803_, lean_object* v_00_u03b2_804_, lean_object* v_f_805_, lean_object* v_init_806_, lean_object* v_b_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_HashSet_forIn(v_00_u03b1_799_, v_x_800_, v_x_801_, v_m_802_, v_inst_803_, v_00_u03b2_804_, v_f_805_, v_init_806_, v_b_807_);
lean_dec_ref(v_x_801_);
lean_dec_ref(v_x_800_);
return v_res_808_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg___lam__2(lean_object* v_inst_809_, lean_object* v_m_810_, lean_object* v_f_811_){
_start:
{
lean_object* v_toApplicative_812_; lean_object* v_buckets_813_; lean_object* v_toPure_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_toApplicative_812_ = lean_ctor_get(v_inst_809_, 0);
v_buckets_813_ = lean_ctor_get(v_m_810_, 1);
lean_inc_ref(v_buckets_813_);
lean_dec_ref(v_m_810_);
v_toPure_814_ = lean_ctor_get(v_toApplicative_812_, 1);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_array_get_size(v_buckets_813_);
v___x_817_ = lean_box(0);
v___x_818_ = lean_nat_dec_lt(v___x_815_, v___x_816_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_inc(v_toPure_814_);
lean_dec_ref(v_buckets_813_);
lean_dec(v_f_811_);
lean_dec_ref(v_inst_809_);
v___x_819_ = lean_apply_2(v_toPure_814_, lean_box(0), v___x_817_);
return v___x_819_;
}
else
{
lean_object* v___f_820_; lean_object* v___f_821_; size_t v___x_822_; size_t v___x_823_; lean_object* v___x_824_; 
v___f_820_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_820_, 0, v_f_811_);
lean_inc_ref(v_inst_809_);
v___f_821_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_821_, 0, v_inst_809_);
lean_closure_set(v___f_821_, 1, v___f_820_);
v___x_822_ = ((size_t)0ULL);
v___x_823_ = lean_usize_of_nat(v___x_816_);
v___x_824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_809_, v___f_821_, v_buckets_813_, v___x_822_, v___x_823_, v___x_817_);
return v___x_824_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg(lean_object* v_inst_825_){
_start:
{
lean_object* v___f_826_; 
v___f_826_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_826_, 0, v_inst_825_);
return v___f_826_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad(lean_object* v_00_u03b1_827_, lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_m_830_, lean_object* v_inst_831_){
_start:
{
lean_object* v___f_832_; 
v___f_832_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_832_, 0, v_inst_831_);
return v___f_832_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_833_, lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_m_836_, lean_object* v_inst_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_HashSet_instForMOfMonad(v_00_u03b1_833_, v_inst_834_, v_inst_835_, v_m_836_, v_inst_837_);
lean_dec_ref(v_inst_835_);
lean_dec_ref(v_inst_834_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg___lam__2(lean_object* v_inst_839_, lean_object* v_00_u03b2_840_, lean_object* v_m_841_, lean_object* v_init_842_, lean_object* v_f_843_){
_start:
{
lean_object* v_buckets_844_; lean_object* v___f_845_; lean_object* v___f_846_; size_t v_sz_847_; size_t v___x_848_; lean_object* v___x_849_; 
v_buckets_844_ = lean_ctor_get(v_m_841_, 1);
lean_inc_ref(v_buckets_844_);
lean_dec_ref(v_m_841_);
v___f_845_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_845_, 0, v_f_843_);
lean_inc_ref(v_inst_839_);
v___f_846_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_846_, 0, v_inst_839_);
lean_closure_set(v___f_846_, 1, v___f_845_);
v_sz_847_ = lean_array_size(v_buckets_844_);
v___x_848_ = ((size_t)0ULL);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_839_, v_buckets_844_, v___f_846_, v_sz_847_, v___x_848_, v_init_842_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg(lean_object* v_inst_850_){
_start:
{
lean_object* v___f_851_; 
v___f_851_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_851_, 0, v_inst_850_);
return v___f_851_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad(lean_object* v_00_u03b1_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_m_855_, lean_object* v_inst_856_){
_start:
{
lean_object* v___f_857_; 
v___f_857_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_857_, 0, v_inst_856_);
return v___f_857_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_m_861_, lean_object* v_inst_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_HashSet_instForInOfMonad(v_00_u03b1_858_, v_inst_859_, v_inst_860_, v_m_861_, v_inst_862_);
lean_dec_ref(v_inst_860_);
lean_dec_ref(v_inst_859_);
return v_res_863_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_filter___redArg___lam__0(lean_object* v_f_864_, lean_object* v_a_865_, lean_object* v_x_866_){
_start:
{
lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_867_ = lean_apply_1(v_f_864_, v_a_865_);
v___x_868_ = lean_unbox(v___x_867_);
return v___x_868_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__0___boxed(lean_object* v_f_869_, lean_object* v_a_870_, lean_object* v_x_871_){
_start:
{
uint8_t v_res_872_; lean_object* v_r_873_; 
v_res_872_ = l_Std_HashSet_filter___redArg___lam__0(v_f_869_, v_a_870_, v_x_871_);
v_r_873_ = lean_box(v_res_872_);
return v_r_873_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg(lean_object* v_f_874_, lean_object* v_m_875_){
_start:
{
lean_object* v___f_876_; lean_object* v___x_877_; 
v___f_876_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_876_, 0, v_f_874_);
v___x_877_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_876_, v_m_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter(lean_object* v_00_u03b1_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_f_881_, lean_object* v_m_882_){
_start:
{
lean_object* v___f_883_; lean_object* v___x_884_; 
v___f_883_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_883_, 0, v_f_881_);
v___x_884_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_883_, v_m_882_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___boxed(lean_object* v_00_u03b1_885_, lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_f_888_, lean_object* v_m_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l_Std_HashSet_filter(v_00_u03b1_885_, v_x_886_, v_x_887_, v_f_888_, v_m_889_);
lean_dec_ref(v_x_887_);
lean_dec_ref(v_x_886_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg(lean_object* v_x_891_, lean_object* v_x_892_, lean_object* v_inst_893_, lean_object* v_m_894_, lean_object* v_l_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_893_, v_x_891_, v_x_892_, v_m_894_, v_l_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany(lean_object* v_00_u03b1_897_, lean_object* v_x_898_, lean_object* v_x_899_, lean_object* v_00_u03c1_900_, lean_object* v_inst_901_, lean_object* v_m_902_, lean_object* v_l_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_901_, v_x_898_, v_x_899_, v_m_902_, v_l_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0(lean_object* v_x1_905_, lean_object* v_x2_906_, lean_object* v_x3_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = lean_array_push(v_x1_905_, v_x2_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__1(lean_object* v___x_909_, lean_object* v___f_910_, lean_object* v_acc_911_, lean_object* v_l_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_909_, v___f_910_, v_acc_911_, v_l_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg(lean_object* v_m_918_){
_start:
{
lean_object* v_size_919_; lean_object* v_buckets_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_size_919_ = lean_ctor_get(v_m_918_, 0);
lean_inc(v_size_919_);
v_buckets_920_ = lean_ctor_get(v_m_918_, 1);
lean_inc_ref(v_buckets_920_);
lean_dec_ref(v_m_918_);
v___x_921_ = lean_mk_empty_array_with_capacity(v_size_919_);
lean_dec(v_size_919_);
v___x_922_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___x_923_ = lean_unsigned_to_nat(0u);
v___x_924_ = lean_array_get_size(v_buckets_920_);
v___x_925_ = lean_nat_dec_lt(v___x_923_, v___x_924_);
if (v___x_925_ == 0)
{
lean_dec_ref(v_buckets_920_);
return v___x_921_;
}
else
{
lean_object* v___f_926_; size_t v___x_927_; size_t v___x_928_; lean_object* v___x_929_; 
v___f_926_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__1));
v___x_927_ = ((size_t)0ULL);
v___x_928_ = lean_usize_of_nat(v___x_924_);
v___x_929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_922_, v___f_926_, v_buckets_920_, v___x_927_, v___x_928_, v___x_921_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray(lean_object* v_00_u03b1_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_m_933_){
_start:
{
lean_object* v_size_934_; lean_object* v_buckets_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_size_934_ = lean_ctor_get(v_m_933_, 0);
lean_inc(v_size_934_);
v_buckets_935_ = lean_ctor_get(v_m_933_, 1);
lean_inc_ref(v_buckets_935_);
lean_dec_ref(v_m_933_);
v___x_936_ = lean_mk_empty_array_with_capacity(v_size_934_);
lean_dec(v_size_934_);
v___x_937_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___x_938_ = lean_unsigned_to_nat(0u);
v___x_939_ = lean_array_get_size(v_buckets_935_);
v___x_940_ = lean_nat_dec_lt(v___x_938_, v___x_939_);
if (v___x_940_ == 0)
{
lean_dec_ref(v_buckets_935_);
return v___x_936_;
}
else
{
lean_object* v___f_941_; size_t v___x_942_; size_t v___x_943_; lean_object* v___x_944_; 
v___f_941_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__1));
v___x_942_ = ((size_t)0ULL);
v___x_943_ = lean_usize_of_nat(v___x_939_);
v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_937_, v___f_941_, v_buckets_935_, v___x_942_, v___x_943_, v___x_936_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___boxed(lean_object* v_00_u03b1_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_m_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_HashSet_toArray(v_00_u03b1_945_, v_x_946_, v_x_947_, v_m_948_);
lean_dec_ref(v_x_947_);
lean_dec_ref(v_x_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0(lean_object* v_p_950_, lean_object* v___x_951_, lean_object* v___x_952_, lean_object* v_a_953_, lean_object* v_b_954_, lean_object* v_acc_955_){
_start:
{
lean_object* v___x_956_; uint8_t v___x_957_; 
v___x_956_ = lean_apply_1(v_p_950_, v_a_953_);
v___x_957_ = lean_unbox(v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec_ref(v___x_952_);
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_956_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_951_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
else
{
lean_object* v___x_961_; 
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v___x_952_);
return v___x_961_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0___boxed(lean_object* v_p_962_, lean_object* v___x_963_, lean_object* v___x_964_, lean_object* v_a_965_, lean_object* v_b_966_, lean_object* v_acc_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Std_HashSet_all___redArg___lam__0(v_p_962_, v___x_963_, v___x_964_, v_a_965_, v_b_966_, v_acc_967_);
lean_dec_ref(v_acc_967_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__1(lean_object* v___x_969_, lean_object* v___f_970_, lean_object* v_a_971_, lean_object* v_x_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_969_, v___f_970_, v_a_971_, v___y_973_);
return v___x_974_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all___redArg(lean_object* v_m_978_, lean_object* v_p_979_){
_start:
{
lean_object* v___x_980_; lean_object* v_buckets_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___f_984_; lean_object* v___f_985_; size_t v_sz_986_; size_t v___x_987_; lean_object* v___x_988_; lean_object* v_fst_989_; 
v___x_980_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_981_ = lean_ctor_get(v_m_978_, 1);
lean_inc_ref(v_buckets_981_);
lean_dec_ref(v_m_978_);
v___x_982_ = lean_box(0);
v___x_983_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_984_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_984_, 0, v_p_979_);
lean_closure_set(v___f_984_, 1, v___x_982_);
lean_closure_set(v___f_984_, 2, v___x_983_);
v___f_985_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_985_, 0, v___x_980_);
lean_closure_set(v___f_985_, 1, v___f_984_);
v_sz_986_ = lean_array_size(v_buckets_981_);
v___x_987_ = ((size_t)0ULL);
v___x_988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_980_, v_buckets_981_, v___f_985_, v_sz_986_, v___x_987_, v___x_983_);
v_fst_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_fst_989_);
lean_dec(v___x_988_);
if (lean_obj_tag(v_fst_989_) == 0)
{
uint8_t v___x_990_; 
v___x_990_ = 1;
return v___x_990_;
}
else
{
lean_object* v_val_991_; uint8_t v___x_992_; 
v_val_991_ = lean_ctor_get(v_fst_989_, 0);
lean_inc(v_val_991_);
lean_dec_ref_known(v_fst_989_, 1);
v___x_992_ = lean_unbox(v_val_991_);
lean_dec(v_val_991_);
return v___x_992_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___boxed(lean_object* v_m_993_, lean_object* v_p_994_){
_start:
{
uint8_t v_res_995_; lean_object* v_r_996_; 
v_res_995_ = l_Std_HashSet_all___redArg(v_m_993_, v_p_994_);
v_r_996_ = lean_box(v_res_995_);
return v_r_996_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all(lean_object* v_00_u03b1_997_, lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_m_1000_, lean_object* v_p_1001_){
_start:
{
lean_object* v___x_1002_; lean_object* v_buckets_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___f_1006_; lean_object* v___f_1007_; size_t v_sz_1008_; size_t v___x_1009_; lean_object* v___x_1010_; lean_object* v_fst_1011_; 
v___x_1002_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1003_ = lean_ctor_get(v_m_1000_, 1);
lean_inc_ref(v_buckets_1003_);
lean_dec_ref(v_m_1000_);
v___x_1004_ = lean_box(0);
v___x_1005_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1006_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1006_, 0, v_p_1001_);
lean_closure_set(v___f_1006_, 1, v___x_1004_);
lean_closure_set(v___f_1006_, 2, v___x_1005_);
v___f_1007_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1007_, 0, v___x_1002_);
lean_closure_set(v___f_1007_, 1, v___f_1006_);
v_sz_1008_ = lean_array_size(v_buckets_1003_);
v___x_1009_ = ((size_t)0ULL);
v___x_1010_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1002_, v_buckets_1003_, v___f_1007_, v_sz_1008_, v___x_1009_, v___x_1005_);
v_fst_1011_ = lean_ctor_get(v___x_1010_, 0);
lean_inc(v_fst_1011_);
lean_dec(v___x_1010_);
if (lean_obj_tag(v_fst_1011_) == 0)
{
uint8_t v___x_1012_; 
v___x_1012_ = 1;
return v___x_1012_;
}
else
{
lean_object* v_val_1013_; uint8_t v___x_1014_; 
v_val_1013_ = lean_ctor_get(v_fst_1011_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v_fst_1011_, 1);
v___x_1014_ = lean_unbox(v_val_1013_);
lean_dec(v_val_1013_);
return v___x_1014_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___boxed(lean_object* v_00_u03b1_1015_, lean_object* v_x_1016_, lean_object* v_x_1017_, lean_object* v_m_1018_, lean_object* v_p_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = l_Std_HashSet_all(v_00_u03b1_1015_, v_x_1016_, v_x_1017_, v_m_1018_, v_p_1019_);
lean_dec_ref(v_x_1017_);
lean_dec_ref(v_x_1016_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0(lean_object* v_p_1022_, lean_object* v___x_1023_, lean_object* v___x_1024_, lean_object* v_a_1025_, lean_object* v_b_1026_, lean_object* v_acc_1027_){
_start:
{
lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1028_ = lean_apply_1(v_p_1022_, v_a_1025_);
v___x_1029_ = lean_unbox(v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1023_);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v___x_1023_);
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1028_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_1024_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0___boxed(lean_object* v_p_1034_, lean_object* v___x_1035_, lean_object* v___x_1036_, lean_object* v_a_1037_, lean_object* v_b_1038_, lean_object* v_acc_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Std_HashSet_any___redArg___lam__0(v_p_1034_, v___x_1035_, v___x_1036_, v_a_1037_, v_b_1038_, v_acc_1039_);
lean_dec_ref(v_acc_1039_);
return v_res_1040_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any___redArg(lean_object* v_m_1041_, lean_object* v_p_1042_){
_start:
{
lean_object* v___x_1043_; lean_object* v_buckets_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___f_1047_; lean_object* v___f_1048_; size_t v_sz_1049_; size_t v___x_1050_; lean_object* v___x_1051_; lean_object* v_fst_1052_; 
v___x_1043_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1044_ = lean_ctor_get(v_m_1041_, 1);
lean_inc_ref(v_buckets_1044_);
lean_dec_ref(v_m_1041_);
v___x_1045_ = lean_box(0);
v___x_1046_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1047_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1047_, 0, v_p_1042_);
lean_closure_set(v___f_1047_, 1, v___x_1046_);
lean_closure_set(v___f_1047_, 2, v___x_1045_);
v___f_1048_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1048_, 0, v___x_1043_);
lean_closure_set(v___f_1048_, 1, v___f_1047_);
v_sz_1049_ = lean_array_size(v_buckets_1044_);
v___x_1050_ = ((size_t)0ULL);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1043_, v_buckets_1044_, v___f_1048_, v_sz_1049_, v___x_1050_, v___x_1046_);
v_fst_1052_ = lean_ctor_get(v___x_1051_, 0);
lean_inc(v_fst_1052_);
lean_dec(v___x_1051_);
if (lean_obj_tag(v_fst_1052_) == 0)
{
uint8_t v___x_1053_; 
v___x_1053_ = 0;
return v___x_1053_;
}
else
{
lean_object* v_val_1054_; uint8_t v___x_1055_; 
v_val_1054_ = lean_ctor_get(v_fst_1052_, 0);
lean_inc(v_val_1054_);
lean_dec_ref_known(v_fst_1052_, 1);
v___x_1055_ = lean_unbox(v_val_1054_);
lean_dec(v_val_1054_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___boxed(lean_object* v_m_1056_, lean_object* v_p_1057_){
_start:
{
uint8_t v_res_1058_; lean_object* v_r_1059_; 
v_res_1058_ = l_Std_HashSet_any___redArg(v_m_1056_, v_p_1057_);
v_r_1059_ = lean_box(v_res_1058_);
return v_r_1059_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any(lean_object* v_00_u03b1_1060_, lean_object* v_x_1061_, lean_object* v_x_1062_, lean_object* v_m_1063_, lean_object* v_p_1064_){
_start:
{
lean_object* v___x_1065_; lean_object* v_buckets_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___f_1069_; lean_object* v___f_1070_; size_t v_sz_1071_; size_t v___x_1072_; lean_object* v___x_1073_; lean_object* v_fst_1074_; 
v___x_1065_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1066_ = lean_ctor_get(v_m_1063_, 1);
lean_inc_ref(v_buckets_1066_);
lean_dec_ref(v_m_1063_);
v___x_1067_ = lean_box(0);
v___x_1068_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1069_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1069_, 0, v_p_1064_);
lean_closure_set(v___f_1069_, 1, v___x_1068_);
lean_closure_set(v___f_1069_, 2, v___x_1067_);
v___f_1070_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1070_, 0, v___x_1065_);
lean_closure_set(v___f_1070_, 1, v___f_1069_);
v_sz_1071_ = lean_array_size(v_buckets_1066_);
v___x_1072_ = ((size_t)0ULL);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1065_, v_buckets_1066_, v___f_1070_, v_sz_1071_, v___x_1072_, v___x_1068_);
v_fst_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_fst_1074_);
lean_dec(v___x_1073_);
if (lean_obj_tag(v_fst_1074_) == 0)
{
uint8_t v___x_1075_; 
v___x_1075_ = 0;
return v___x_1075_;
}
else
{
lean_object* v_val_1076_; uint8_t v___x_1077_; 
v_val_1076_ = lean_ctor_get(v_fst_1074_, 0);
lean_inc(v_val_1076_);
lean_dec_ref_known(v_fst_1074_, 1);
v___x_1077_ = lean_unbox(v_val_1076_);
lean_dec(v_val_1076_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___boxed(lean_object* v_00_u03b1_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_m_1081_, lean_object* v_p_1082_){
_start:
{
uint8_t v_res_1083_; lean_object* v_r_1084_; 
v_res_1083_ = l_Std_HashSet_any(v_00_u03b1_1078_, v_x_1079_, v_x_1080_, v_m_1081_, v_p_1082_);
lean_dec_ref(v_x_1080_);
lean_dec_ref(v_x_1079_);
v_r_1084_ = lean_box(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0(lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_a_1087_, lean_object* v_b_1088_, lean_object* v_acc_1089_){
_start:
{
lean_object* v_r_1090_; lean_object* v___x_1091_; 
v_r_1090_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1085_, v_inst_1086_, v_acc_1089_, v_a_1087_, v_b_1088_);
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_r_1090_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__1(lean_object* v___x_1092_, lean_object* v___f_1093_, lean_object* v_a_1094_, lean_object* v_x_1095_, lean_object* v___y_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1092_, v___f_1093_, v_a_1094_, v___y_1096_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg(lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_m_u2081_1102_, lean_object* v_m_u2082_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v_size_1105_; lean_object* v_buckets_1106_; lean_object* v_size_1107_; uint8_t v___x_1108_; 
v___x_1104_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_size_1105_ = lean_ctor_get(v_m_u2081_1102_, 0);
v_buckets_1106_ = lean_ctor_get(v_m_u2081_1102_, 1);
v_size_1107_ = lean_ctor_get(v_m_u2082_1103_, 0);
v___x_1108_ = lean_nat_dec_le(v_size_1105_, v_size_1107_);
if (v___x_1108_ == 0)
{
lean_object* v___f_1109_; lean_object* v___x_1110_; 
v___f_1109_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1110_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1109_, v_inst_1100_, v_inst_1101_, v_m_u2081_1102_, v_m_u2082_1103_);
return v___x_1110_;
}
else
{
lean_object* v___f_1111_; lean_object* v___f_1112_; size_t v_sz_1113_; size_t v___x_1114_; lean_object* v___x_1115_; 
lean_inc_ref(v_buckets_1106_);
lean_dec_ref(v_m_u2081_1102_);
v___f_1111_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1111_, 0, v_inst_1100_);
lean_closure_set(v___f_1111_, 1, v_inst_1101_);
v___f_1112_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1112_, 0, v___x_1104_);
lean_closure_set(v___f_1112_, 1, v___f_1111_);
v_sz_1113_ = lean_array_size(v_buckets_1106_);
v___x_1114_ = ((size_t)0ULL);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1104_, v_buckets_1106_, v___f_1112_, v_sz_1113_, v___x_1114_, v_m_u2082_1103_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union(lean_object* v_00_u03b1_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_m_u2081_1119_, lean_object* v_m_u2082_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v_size_1122_; lean_object* v_buckets_1123_; lean_object* v_size_1124_; uint8_t v___x_1125_; 
v___x_1121_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_size_1122_ = lean_ctor_get(v_m_u2081_1119_, 0);
v_buckets_1123_ = lean_ctor_get(v_m_u2081_1119_, 1);
v_size_1124_ = lean_ctor_get(v_m_u2082_1120_, 0);
v___x_1125_ = lean_nat_dec_le(v_size_1122_, v_size_1124_);
if (v___x_1125_ == 0)
{
lean_object* v___f_1126_; lean_object* v___x_1127_; 
v___f_1126_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1127_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1126_, v_inst_1117_, v_inst_1118_, v_m_u2081_1119_, v_m_u2082_1120_);
return v___x_1127_;
}
else
{
lean_object* v___f_1128_; lean_object* v___f_1129_; size_t v_sz_1130_; size_t v___x_1131_; lean_object* v___x_1132_; 
lean_inc_ref(v_buckets_1123_);
lean_dec_ref(v_m_u2081_1119_);
v___f_1128_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1128_, 0, v_inst_1117_);
lean_closure_set(v___f_1128_, 1, v_inst_1118_);
v___f_1129_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1129_, 0, v___x_1121_);
lean_closure_set(v___f_1129_, 1, v___f_1128_);
v_sz_1130_ = lean_array_size(v_buckets_1123_);
v___x_1131_ = ((size_t)0ULL);
v___x_1132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1121_, v_buckets_1123_, v___f_1129_, v_sz_1130_, v___x_1131_, v_m_u2082_1120_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion___redArg(lean_object* v_inst_1133_, lean_object* v_inst_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1135_, 0, lean_box(0));
lean_closure_set(v___x_1135_, 1, v_inst_1133_);
lean_closure_set(v___x_1135_, 2, v_inst_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion(lean_object* v_00_u03b1_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1139_, 0, lean_box(0));
lean_closure_set(v___x_1139_, 1, v_inst_1137_);
lean_closure_set(v___x_1139_, 2, v_inst_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter___redArg(lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_m_u2081_1142_, lean_object* v_m_u2082_1143_){
_start:
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1140_, v_inst_1141_, v_m_u2081_1142_, v_m_u2082_1143_);
return v___x_1144_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter(lean_object* v_00_u03b1_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_m_u2081_1148_, lean_object* v_m_u2082_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1146_, v_inst_1147_, v_m_u2081_1148_, v_m_u2082_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter___redArg(lean_object* v_inst_1151_, lean_object* v_inst_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1153_, 0, lean_box(0));
lean_closure_set(v___x_1153_, 1, v_inst_1151_);
lean_closure_set(v___x_1153_, 2, v_inst_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter(lean_object* v_00_u03b1_1154_, lean_object* v_inst_1155_, lean_object* v_inst_1156_){
_start:
{
lean_object* v___x_1157_; 
v___x_1157_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1157_, 0, lean_box(0));
lean_closure_set(v___x_1157_, 1, v_inst_1155_);
lean_closure_set(v___x_1157_, 2, v_inst_1156_);
return v___x_1157_;
}
}
static lean_object* _init_l_Std_HashSet_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1158_; lean_object* v___f_1159_; 
v___x_1158_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1159_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1159_, 0, v___x_1158_);
return v___f_1159_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq___redArg(lean_object* v_x_1160_, lean_object* v_inst_1161_, lean_object* v_m_u2081_1162_, lean_object* v_m_u2082_1163_){
_start:
{
lean_object* v___f_1164_; uint8_t v___x_1165_; 
v___f_1164_ = lean_obj_once(&l_Std_HashSet_beq___redArg___closed__0, &l_Std_HashSet_beq___redArg___closed__0_once, _init_l_Std_HashSet_beq___redArg___closed__0);
v___x_1165_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1161_, v_x_1160_, v___f_1164_, v_m_u2081_1162_, v_m_u2082_1163_);
return v___x_1165_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___redArg___boxed(lean_object* v_x_1166_, lean_object* v_inst_1167_, lean_object* v_m_u2081_1168_, lean_object* v_m_u2082_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Std_HashSet_beq___redArg(v_x_1166_, v_inst_1167_, v_m_u2081_1168_, v_m_u2082_1169_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq(lean_object* v_00_u03b1_1172_, lean_object* v_x_1173_, lean_object* v_inst_1174_, lean_object* v_m_u2081_1175_, lean_object* v_m_u2082_1176_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = l_Std_HashSet_beq___redArg(v_x_1173_, v_inst_1174_, v_m_u2081_1175_, v_m_u2082_1176_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___boxed(lean_object* v_00_u03b1_1178_, lean_object* v_x_1179_, lean_object* v_inst_1180_, lean_object* v_m_u2081_1181_, lean_object* v_m_u2082_1182_){
_start:
{
uint8_t v_res_1183_; lean_object* v_r_1184_; 
v_res_1183_ = l_Std_HashSet_beq(v_00_u03b1_1178_, v_x_1179_, v_inst_1180_, v_m_u2081_1181_, v_m_u2082_1182_);
v_r_1184_ = lean_box(v_res_1183_);
return v_r_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq___redArg(lean_object* v_x_1185_, lean_object* v_inst_1186_){
_start:
{
lean_object* v___x_1187_; 
v___x_1187_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1187_, 0, lean_box(0));
lean_closure_set(v___x_1187_, 1, v_x_1185_);
lean_closure_set(v___x_1187_, 2, v_inst_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq(lean_object* v_00_u03b1_1188_, lean_object* v_x_1189_, lean_object* v_inst_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1191_, 0, lean_box(0));
lean_closure_set(v___x_1191_, 1, v_x_1189_);
lean_closure_set(v___x_1191_, 2, v_inst_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_diff___redArg___lam__0(lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_m_u2082_1194_, uint8_t v___x_1195_, lean_object* v_k_1196_, lean_object* v_x_1197_){
_start:
{
uint8_t v___x_1198_; 
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1192_, v_inst_1193_, v_m_u2082_1194_, v_k_1196_);
if (v___x_1198_ == 0)
{
return v___x_1195_;
}
else
{
uint8_t v___x_1199_; 
v___x_1199_ = 0;
return v___x_1199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg___lam__0___boxed(lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_m_u2082_1202_, lean_object* v___x_1203_, lean_object* v_k_1204_, lean_object* v_x_1205_){
_start:
{
uint8_t v___x_81__boxed_1206_; uint8_t v_res_1207_; lean_object* v_r_1208_; 
v___x_81__boxed_1206_ = lean_unbox(v___x_1203_);
v_res_1207_ = l_Std_HashSet_diff___redArg___lam__0(v_inst_1200_, v_inst_1201_, v_m_u2082_1202_, v___x_81__boxed_1206_, v_k_1204_, v_x_1205_);
lean_dec_ref(v_m_u2082_1202_);
v_r_1208_ = lean_box(v_res_1207_);
return v_r_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg(lean_object* v_inst_1209_, lean_object* v_inst_1210_, lean_object* v_m_u2081_1211_, lean_object* v_m_u2082_1212_){
_start:
{
lean_object* v_size_1213_; lean_object* v_size_1214_; uint8_t v___x_1215_; 
v_size_1213_ = lean_ctor_get(v_m_u2081_1211_, 0);
v_size_1214_ = lean_ctor_get(v_m_u2082_1212_, 0);
v___x_1215_ = lean_nat_dec_le(v_size_1213_, v_size_1214_);
if (v___x_1215_ == 0)
{
lean_object* v___f_1216_; lean_object* v___x_1217_; 
v___f_1216_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1217_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1216_, v_inst_1209_, v_inst_1210_, v_m_u2081_1211_, v_m_u2082_1212_);
return v___x_1217_;
}
else
{
lean_object* v___x_1218_; lean_object* v___f_1219_; lean_object* v___x_1220_; 
v___x_1218_ = lean_box(v___x_1215_);
v___f_1219_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1219_, 0, v_inst_1209_);
lean_closure_set(v___f_1219_, 1, v_inst_1210_);
lean_closure_set(v___f_1219_, 2, v_m_u2082_1212_);
lean_closure_set(v___f_1219_, 3, v___x_1218_);
v___x_1220_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1219_, v_m_u2081_1211_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff(lean_object* v_00_u03b1_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_m_u2081_1224_, lean_object* v_m_u2082_1225_){
_start:
{
lean_object* v_size_1226_; lean_object* v_size_1227_; uint8_t v___x_1228_; 
v_size_1226_ = lean_ctor_get(v_m_u2081_1224_, 0);
v_size_1227_ = lean_ctor_get(v_m_u2082_1225_, 0);
v___x_1228_ = lean_nat_dec_le(v_size_1226_, v_size_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___f_1229_; lean_object* v___x_1230_; 
v___f_1229_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1230_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1229_, v_inst_1222_, v_inst_1223_, v_m_u2081_1224_, v_m_u2082_1225_);
return v___x_1230_;
}
else
{
lean_object* v___x_1231_; lean_object* v___f_1232_; lean_object* v___x_1233_; 
v___x_1231_ = lean_box(v___x_1228_);
v___f_1232_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1232_, 0, v_inst_1222_);
lean_closure_set(v___f_1232_, 1, v_inst_1223_);
lean_closure_set(v___f_1232_, 2, v_m_u2082_1225_);
lean_closure_set(v___f_1232_, 3, v___x_1231_);
v___x_1233_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1232_, v_m_u2081_1224_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff___redArg(lean_object* v_inst_1234_, lean_object* v_inst_1235_){
_start:
{
lean_object* v___x_1236_; 
v___x_1236_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1236_, 0, lean_box(0));
lean_closure_set(v___x_1236_, 1, v_inst_1234_);
lean_closure_set(v___x_1236_, 2, v_inst_1235_);
return v___x_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff(lean_object* v_00_u03b1_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1240_, 0, lean_box(0));
lean_closure_set(v___x_1240_, 1, v_inst_1238_);
lean_closure_set(v___x_1240_, 2, v_inst_1239_);
return v___x_1240_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__0(lean_object* v_f_1241_, lean_object* v_x_1242_, lean_object* v_x_1243_, lean_object* v_x1_1244_, lean_object* v_x2_1245_, lean_object* v_x3_1246_){
_start:
{
lean_object* v_fst_1247_; lean_object* v_snd_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1262_; 
v_fst_1247_ = lean_ctor_get(v_x1_1244_, 0);
v_snd_1248_ = lean_ctor_get(v_x1_1244_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_x1_1244_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1250_ = v_x1_1244_;
v_isShared_1251_ = v_isSharedCheck_1262_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_snd_1248_);
lean_inc(v_fst_1247_);
lean_dec(v_x1_1244_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1262_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1252_; uint8_t v___x_1253_; 
lean_inc(v_x2_1245_);
v___x_1252_ = lean_apply_1(v_f_1241_, v_x2_1245_);
v___x_1253_ = lean_unbox(v___x_1252_);
if (v___x_1253_ == 0)
{
lean_object* v___x_1254_; lean_object* v___x_1256_; 
v___x_1254_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1242_, v_x_1243_, v_snd_1248_, v_x2_1245_, v_x3_1246_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 1, v___x_1254_);
v___x_1256_ = v___x_1250_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_fst_1247_);
lean_ctor_set(v_reuseFailAlloc_1257_, 1, v___x_1254_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
else
{
lean_object* v___x_1258_; lean_object* v___x_1260_; 
v___x_1258_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1242_, v_x_1243_, v_fst_1247_, v_x2_1245_, v_x3_1246_);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1258_);
v___x_1260_ = v___x_1250_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1258_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_snd_1248_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__1(lean_object* v___x_1263_, lean_object* v___f_1264_, lean_object* v_acc_1265_, lean_object* v_l_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1263_, v___f_1264_, v_acc_1265_, v_l_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l_Std_HashSet_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_f_1272_, lean_object* v_m_1273_){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v_buckets_1277_; lean_object* v___x_1278_; uint8_t v___x_1279_; 
v___x_1274_ = lean_unsigned_to_nat(0u);
v___x_1275_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1276_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1277_ = lean_ctor_get(v_m_1273_, 1);
lean_inc_ref(v_buckets_1277_);
lean_dec_ref(v_m_1273_);
v___x_1278_ = lean_array_get_size(v_buckets_1277_);
v___x_1279_ = lean_nat_dec_lt(v___x_1274_, v___x_1278_);
if (v___x_1279_ == 0)
{
lean_dec_ref(v_buckets_1277_);
lean_dec_ref(v_f_1272_);
lean_dec_ref(v_x_1271_);
lean_dec_ref(v_x_1270_);
return v___x_1275_;
}
else
{
lean_object* v___f_1280_; lean_object* v___f_1281_; size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; lean_object* v_fst_1285_; lean_object* v_snd_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v___f_1280_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1280_, 0, v_f_1272_);
lean_closure_set(v___f_1280_, 1, v_x_1270_);
lean_closure_set(v___f_1280_, 2, v_x_1271_);
v___f_1281_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1281_, 0, v___x_1276_);
lean_closure_set(v___f_1281_, 1, v___f_1280_);
v___x_1282_ = ((size_t)0ULL);
v___x_1283_ = lean_usize_of_nat(v___x_1278_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1276_, v___f_1281_, v_buckets_1277_, v___x_1282_, v___x_1283_, v___x_1275_);
v_fst_1285_ = lean_ctor_get(v___x_1284_, 0);
v_snd_1286_ = lean_ctor_get(v___x_1284_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1284_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_snd_1286_);
lean_inc(v_fst_1285_);
lean_dec(v___x_1284_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_fst_1285_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_snd_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition(lean_object* v_00_u03b1_1294_, lean_object* v_x_1295_, lean_object* v_x_1296_, lean_object* v_f_1297_, lean_object* v_m_1298_){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v_buckets_1302_; lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1299_ = lean_unsigned_to_nat(0u);
v___x_1300_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1301_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1302_ = lean_ctor_get(v_m_1298_, 1);
lean_inc_ref(v_buckets_1302_);
lean_dec_ref(v_m_1298_);
v___x_1303_ = lean_array_get_size(v_buckets_1302_);
v___x_1304_ = lean_nat_dec_lt(v___x_1299_, v___x_1303_);
if (v___x_1304_ == 0)
{
lean_dec_ref(v_buckets_1302_);
lean_dec_ref(v_f_1297_);
lean_dec_ref(v_x_1296_);
lean_dec_ref(v_x_1295_);
return v___x_1300_;
}
else
{
lean_object* v___f_1305_; lean_object* v___f_1306_; size_t v___x_1307_; size_t v___x_1308_; lean_object* v___x_1309_; lean_object* v_fst_1310_; lean_object* v_snd_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v___f_1305_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1305_, 0, v_f_1297_);
lean_closure_set(v___f_1305_, 1, v_x_1295_);
lean_closure_set(v___f_1305_, 2, v_x_1296_);
v___f_1306_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1306_, 0, v___x_1301_);
lean_closure_set(v___f_1306_, 1, v___f_1305_);
v___x_1307_ = ((size_t)0ULL);
v___x_1308_ = lean_usize_of_nat(v___x_1303_);
v___x_1309_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1301_, v___f_1306_, v_buckets_1302_, v___x_1307_, v___x_1308_, v___x_1300_);
v_fst_1310_ = lean_ctor_get(v___x_1309_, 0);
v_snd_1311_ = lean_ctor_get(v___x_1309_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1309_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_snd_1311_);
lean_inc(v_fst_1310_);
lean_dec(v___x_1309_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_fst_1310_);
lean_ctor_set(v_reuseFailAlloc_1317_, 1, v_snd_1311_);
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
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray___redArg(lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_l_1325_){
_start:
{
lean_object* v___f_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; 
v___f_1326_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1327_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_1328_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1326_, v_inst_1323_, v_inst_1324_, v___x_1327_, v_l_1325_);
return v___x_1328_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray(lean_object* v_00_u03b1_1329_, lean_object* v_inst_1330_, lean_object* v_inst_1331_, lean_object* v_l_1332_){
_start:
{
lean_object* v___f_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___f_1333_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1334_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_1335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1333_, v_inst_1330_, v_inst_1331_, v___x_1334_, v_l_1332_);
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg(lean_object* v_m_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg___boxed(lean_object* v_m_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Std_HashSet_Internal_numBuckets___redArg(v_m_1338_);
lean_dec_ref(v_m_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets(lean_object* v_00_u03b1_1340_, lean_object* v_x_1341_, lean_object* v_x_1342_, lean_object* v_m_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_x_1346_, lean_object* v_x_1347_, lean_object* v_m_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Std_HashSet_Internal_numBuckets(v_00_u03b1_1345_, v_x_1346_, v_x_1347_, v_m_1348_);
lean_dec_ref(v_m_1348_);
lean_dec_ref(v_x_1347_);
lean_dec_ref(v_x_1346_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2(lean_object* v_inst_1353_, lean_object* v___f_1354_, lean_object* v_m_1355_, lean_object* v_prec_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v_buckets_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1378_; 
v___x_1357_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1358_ = lean_ctor_get(v_m_1355_, 1);
v_isSharedCheck_1378_ = !lean_is_exclusive(v_m_1355_);
if (v_isSharedCheck_1378_ == 0)
{
lean_object* v_unused_1379_; 
v_unused_1379_ = lean_ctor_get(v_m_1355_, 0);
lean_dec(v_unused_1379_);
v___x_1360_ = v_m_1355_;
v_isShared_1361_ = v_isSharedCheck_1378_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_buckets_1358_);
lean_dec(v_m_1355_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1378_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1362_; lean_object* v___y_1364_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1362_ = ((lean_object*)(l_Std_HashSet_instRepr___redArg___lam__2___closed__1));
v___x_1370_ = lean_box(0);
v___x_1371_ = lean_array_get_size(v_buckets_1358_);
v___x_1372_ = lean_unsigned_to_nat(0u);
v___x_1373_ = lean_nat_dec_lt(v___x_1372_, v___x_1371_);
if (v___x_1373_ == 0)
{
lean_dec_ref(v_buckets_1358_);
lean_dec_ref(v___f_1354_);
v___y_1364_ = v___x_1370_;
goto v___jp_1363_;
}
else
{
lean_object* v___f_1374_; size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___f_1374_ = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1374_, 0, v___x_1357_);
lean_closure_set(v___f_1374_, 1, v___f_1354_);
v___x_1375_ = lean_usize_of_nat(v___x_1371_);
v___x_1376_ = ((size_t)0ULL);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1357_, v___f_1374_, v_buckets_1358_, v___x_1375_, v___x_1376_, v___x_1370_);
v___y_1364_ = v___x_1377_;
goto v___jp_1363_;
}
v___jp_1363_:
{
lean_object* v___x_1365_; lean_object* v___x_1367_; 
v___x_1365_ = l_List_repr___redArg(v_inst_1353_, v___y_1364_);
if (v_isShared_1361_ == 0)
{
lean_ctor_set_tag(v___x_1360_, 5);
lean_ctor_set(v___x_1360_, 1, v___x_1365_);
lean_ctor_set(v___x_1360_, 0, v___x_1362_);
v___x_1367_ = v___x_1360_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1362_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Repr_addAppParen(v___x_1367_, v_prec_1356_);
return v___x_1368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1380_, lean_object* v___f_1381_, lean_object* v_m_1382_, lean_object* v_prec_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Std_HashSet_instRepr___redArg___lam__2(v_inst_1380_, v___f_1381_, v_m_1382_, v_prec_1383_);
lean_dec(v_prec_1383_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg(lean_object* v_inst_1385_){
_start:
{
lean_object* v___f_1386_; lean_object* v___f_1387_; 
v___f_1386_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___f_1387_ = lean_alloc_closure((void*)(l_Std_HashSet_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1387_, 0, v_inst_1385_);
lean_closure_set(v___f_1387_, 1, v___f_1386_);
return v___f_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr(lean_object* v_00_u03b1_1388_, lean_object* v_inst_1389_, lean_object* v_inst_1390_, lean_object* v_inst_1391_){
_start:
{
lean_object* v___x_1392_; 
v___x_1392_ = l_Std_HashSet_instRepr___redArg(v_inst_1391_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___boxed(lean_object* v_00_u03b1_1393_, lean_object* v_inst_1394_, lean_object* v_inst_1395_, lean_object* v_inst_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Std_HashSet_instRepr(v_00_u03b1_1393_, v_inst_1394_, v_inst_1395_, v_inst_1396_);
lean_dec_ref(v_inst_1395_);
lean_dec_ref(v_inst_1394_);
return v_res_1397_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
