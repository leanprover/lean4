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
static lean_once_cell_t l_Std_HashSet_instEmptyCollection___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instEmptyCollection___redArg___closed__0;
static lean_once_cell_t l_Std_HashSet_instEmptyCollection___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instEmptyCollection___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_HashSet_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_HashSet_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instInhabited___closed__0;
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
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Std_HashSet_instEmptyCollection___redArg___closed__0(void){
_start:
{
lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_31_ = lean_box(0);
v___x_32_ = lean_unsigned_to_nat(16u);
v___x_33_ = lean_mk_array(v___x_32_, v___x_31_);
return v___x_33_;
}
}
static lean_object* _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__0, &l_Std_HashSet_instEmptyCollection___redArg___closed__0_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__0);
v___x_35_ = lean_unsigned_to_nat(0u);
v___x_36_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
lean_ctor_set(v___x_36_, 1, v___x_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Std_HashSet_instEmptyCollection___redArg();
return v_res_40_;
}
}
static lean_object* _init_l_Std_HashSet_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Std_HashSet_instEmptyCollection___redArg();
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection(lean_object* v_00_u03b1_42_, lean_object* v_inst_43_, lean_object* v_inst_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__0, &l_Std_HashSet_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_instEmptyCollection___closed__0);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_46_, lean_object* v_inst_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_HashSet_instEmptyCollection(v_00_u03b1_46_, v_inst_47_, v_inst_48_);
lean_dec_ref(v_inst_48_);
lean_dec_ref(v_inst_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___redArg___boxed(lean_object* v___dummy_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_HashSet_instInhabited___redArg();
return v_res_53_;
}
}
static lean_object* _init_l_Std_HashSet_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = l_Std_HashSet_instInhabited___redArg();
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lean_obj_once(&l_Std_HashSet_instInhabited___closed__0, &l_Std_HashSet_instInhabited___closed__0_once, _init_l_Std_HashSet_instInhabited___closed__0);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___boxed(lean_object* v_00_u03b1_59_, lean_object* v_inst_60_, lean_object* v_inst_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Std_HashSet_instInhabited(v_00_u03b1_59_, v_inst_60_, v_inst_61_);
lean_dec_ref(v_inst_61_);
lean_dec_ref(v_inst_60_);
return v_res_62_;
}
}
static lean_object* _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_101_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5));
v___x_102_ = l_String_toRawSubstring_x27(v___x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(lean_object* v_x_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__3));
lean_inc(v_x_123_);
v___x_127_ = l_Lean_Syntax_isOfKind(v_x_123_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_x_123_);
v___x_128_ = lean_box(1);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v_a_125_);
return v___x_129_;
}
else
{
lean_object* v_quotContext_130_; lean_object* v_currMacroScope_131_; lean_object* v_ref_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v_quotContext_130_ = lean_ctor_get(v_a_124_, 1);
v_currMacroScope_131_ = lean_ctor_get(v_a_124_, 2);
v_ref_132_ = lean_ctor_get(v_a_124_, 5);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = l_Lean_Syntax_getArg(v_x_123_, v___x_133_);
v___x_135_ = lean_unsigned_to_nat(2u);
v___x_136_ = l_Lean_Syntax_getArg(v_x_123_, v___x_135_);
lean_dec(v_x_123_);
v___x_137_ = 0;
v___x_138_ = l_Lean_SourceInfo_fromRef(v_ref_132_, v___x_137_);
v___x_139_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4));
v___x_140_ = lean_obj_once(&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6, &l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6_once, _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6);
v___x_141_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_131_);
lean_inc(v_quotContext_130_);
v___x_142_ = l_Lean_addMacroScope(v_quotContext_130_, v___x_141_, v_currMacroScope_131_);
v___x_143_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12));
lean_inc_n(v___x_138_, 2);
v___x_144_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_144_, 0, v___x_138_);
lean_ctor_set(v___x_144_, 1, v___x_140_);
lean_ctor_set(v___x_144_, 2, v___x_142_);
lean_ctor_set(v___x_144_, 3, v___x_143_);
v___x_145_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14));
v___x_146_ = l_Lean_Syntax_node2(v___x_138_, v___x_145_, v___x_134_, v___x_136_);
v___x_147_ = l_Lean_Syntax_node2(v___x_138_, v___x_139_, v___x_144_, v___x_146_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_a_125_);
return v___x_148_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___boxed(lean_object* v_x_149_, lean_object* v_a_150_, lean_object* v_a_151_){
_start:
{
lean_object* v_res_152_; 
v_res_152_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(v_x_149_, v_a_150_, v_a_151_);
lean_dec_ref(v_a_150_);
return v_res_152_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(lean_object* v_x_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4));
lean_inc(v_x_156_);
v___x_160_ = l_Lean_Syntax_isOfKind(v_x_156_, v___x_159_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v___x_162_; 
lean_dec(v_x_156_);
v___x_161_ = lean_box(0);
v___x_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v_a_158_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v___x_163_ = lean_unsigned_to_nat(0u);
v___x_164_ = l_Lean_Syntax_getArg(v_x_156_, v___x_163_);
v___x_165_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1));
lean_inc(v___x_164_);
v___x_166_ = l_Lean_Syntax_isOfKind(v___x_164_, v___x_165_);
if (v___x_166_ == 0)
{
lean_object* v___x_167_; lean_object* v___x_168_; 
lean_dec(v___x_164_);
lean_dec(v_x_156_);
v___x_167_ = lean_box(0);
v___x_168_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v_a_158_);
return v___x_168_;
}
else
{
lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_169_ = lean_unsigned_to_nat(1u);
v___x_170_ = l_Lean_Syntax_getArg(v_x_156_, v___x_169_);
lean_dec(v_x_156_);
v___x_171_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_170_);
v___x_172_ = l_Lean_Syntax_matchesNull(v___x_170_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
lean_dec(v___x_170_);
lean_dec(v___x_164_);
v___x_173_ = lean_box(0);
v___x_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
lean_ctor_set(v___x_174_, 1, v_a_158_);
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_ref_177_; uint8_t v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_175_ = l_Lean_Syntax_getArg(v___x_170_, v___x_163_);
v___x_176_ = l_Lean_Syntax_getArg(v___x_170_, v___x_169_);
lean_dec(v___x_170_);
v_ref_177_ = l_Lean_replaceRef(v___x_164_, v_a_157_);
lean_dec(v___x_164_);
v___x_178_ = 0;
v___x_179_ = l_Lean_SourceInfo_fromRef(v_ref_177_, v___x_178_);
lean_dec(v_ref_177_);
v___x_180_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__3));
v___x_181_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__6));
lean_inc(v___x_179_);
v___x_182_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_179_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = l_Lean_Syntax_node3(v___x_179_, v___x_180_, v___x_175_, v___x_182_, v___x_176_);
v___x_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v_a_158_);
return v___x_184_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___boxed(lean_object* v_x_185_, lean_object* v_a_186_, lean_object* v_a_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(v_x_185_, v_a_186_, v_a_187_);
lean_dec(v_a_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert___redArg(lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_m_191_, lean_object* v_a_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_box(0);
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_189_, v_x_190_, v_m_191_, v_a_192_, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert(lean_object* v_00_u03b1_195_, lean_object* v_x_196_, lean_object* v_x_197_, lean_object* v_m_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_box(0);
v___x_201_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_196_, v_x_197_, v_m_198_, v_a_199_, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg___lam__0(lean_object* v_x_202_, lean_object* v_x_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
v___x_205_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_206_ = lean_box(0);
v___x_207_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_202_, v_x_203_, v___x_205_, v_a_204_, v___x_206_);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg(lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
lean_object* v___f_210_; 
v___f_210_ = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(v___f_210_, 0, v_x_208_);
lean_closure_set(v___f_210_, 1, v_x_209_);
return v___f_210_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton(lean_object* v_00_u03b1_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
lean_object* v___f_214_; 
v___f_214_ = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(v___f_214_, 0, v_x_212_);
lean_closure_set(v___f_214_, 1, v_x_213_);
return v___f_214_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg___lam__0(lean_object* v_x_215_, lean_object* v_x_216_, lean_object* v_a_217_, lean_object* v_s_218_){
_start:
{
lean_object* v___x_219_; lean_object* v___x_220_; 
v___x_219_ = lean_box(0);
v___x_220_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_215_, v_x_216_, v_s_218_, v_a_217_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg(lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
lean_object* v___f_223_; 
v___f_223_ = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(v___f_223_, 0, v_x_221_);
lean_closure_set(v___f_223_, 1, v_x_222_);
return v___f_223_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert(lean_object* v_00_u03b1_224_, lean_object* v_x_225_, lean_object* v_x_226_){
_start:
{
lean_object* v___f_227_; 
v___f_227_ = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(v___f_227_, 0, v_x_225_);
lean_closure_set(v___f_227_, 1, v_x_226_);
return v___f_227_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert___redArg(lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_m_230_, lean_object* v_a_231_){
_start:
{
lean_object* v_size_232_; lean_object* v_buckets_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v_fold_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v_bkt_249_; uint8_t v___x_250_; 
v_size_232_ = lean_ctor_get(v_m_230_, 0);
v_buckets_233_ = lean_ctor_get(v_m_230_, 1);
v___x_234_ = lean_array_get_size(v_buckets_233_);
lean_inc_ref(v_x_229_);
lean_inc_n(v_a_231_, 2);
v___x_235_ = lean_apply_1(v_x_229_, v_a_231_);
v___x_236_ = 32ULL;
v___x_237_ = lean_unbox_uint64(v___x_235_);
v___x_238_ = lean_uint64_shift_right(v___x_237_, v___x_236_);
v___x_239_ = lean_unbox_uint64(v___x_235_);
lean_dec_ref(v___x_235_);
v_fold_240_ = lean_uint64_xor(v___x_239_, v___x_238_);
v___x_241_ = 16ULL;
v___x_242_ = lean_uint64_shift_right(v_fold_240_, v___x_241_);
v___x_243_ = lean_uint64_xor(v_fold_240_, v___x_242_);
v___x_244_ = lean_uint64_to_usize(v___x_243_);
v___x_245_ = lean_usize_of_nat(v___x_234_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_sub(v___x_245_, v___x_246_);
v___x_248_ = lean_usize_land(v___x_244_, v___x_247_);
v_bkt_249_ = lean_array_uget_borrowed(v_buckets_233_, v___x_248_);
lean_inc(v_bkt_249_);
v___x_250_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_228_, v_a_231_, v_bkt_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_276_; 
lean_inc_ref(v_buckets_233_);
lean_inc(v_size_232_);
v_isSharedCheck_276_ = !lean_is_exclusive(v_m_230_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; lean_object* v_unused_278_; 
v_unused_277_ = lean_ctor_get(v_m_230_, 1);
lean_dec(v_unused_277_);
v_unused_278_ = lean_ctor_get(v_m_230_, 0);
lean_dec(v_unused_278_);
v___x_252_ = v_m_230_;
v_isShared_253_ = v_isSharedCheck_276_;
goto v_resetjp_251_;
}
else
{
lean_dec(v_m_230_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_276_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v_size_x27_256_; lean_object* v___x_257_; lean_object* v_buckets_x27_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_254_ = lean_box(0);
v___x_255_ = lean_unsigned_to_nat(1u);
v_size_x27_256_ = lean_nat_add(v_size_232_, v___x_255_);
lean_dec(v_size_232_);
lean_inc(v_bkt_249_);
v___x_257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_257_, 0, v_a_231_);
lean_ctor_set(v___x_257_, 1, v___x_254_);
lean_ctor_set(v___x_257_, 2, v_bkt_249_);
v_buckets_x27_258_ = lean_array_uset(v_buckets_233_, v___x_248_, v___x_257_);
v___x_259_ = lean_unsigned_to_nat(4u);
v___x_260_ = lean_nat_mul(v_size_x27_256_, v___x_259_);
v___x_261_ = lean_unsigned_to_nat(3u);
v___x_262_ = lean_nat_div(v___x_260_, v___x_261_);
lean_dec(v___x_260_);
v___x_263_ = lean_array_get_size(v_buckets_x27_258_);
v___x_264_ = lean_nat_dec_le(v___x_262_, v___x_263_);
lean_dec(v___x_262_);
if (v___x_264_ == 0)
{
lean_object* v_val_265_; lean_object* v___x_267_; 
v_val_265_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_229_, v_buckets_x27_258_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_val_265_);
lean_ctor_set(v___x_252_, 0, v_size_x27_256_);
v___x_267_ = v___x_252_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_size_x27_256_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_val_265_);
v___x_267_ = v_reuseFailAlloc_270_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_box(v___x_250_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
return v___x_269_;
}
}
else
{
lean_object* v___x_272_; 
lean_dec_ref(v_x_229_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 1, v_buckets_x27_258_);
lean_ctor_set(v___x_252_, 0, v_size_x27_256_);
v___x_272_ = v___x_252_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_size_x27_256_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v_buckets_x27_258_);
v___x_272_ = v_reuseFailAlloc_275_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_box(v___x_250_);
v___x_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___x_272_);
return v___x_274_;
}
}
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec(v_a_231_);
lean_dec_ref(v_x_229_);
v___x_279_ = lean_box(v___x_250_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v_m_230_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert(lean_object* v_00_u03b1_281_, lean_object* v_x_282_, lean_object* v_x_283_, lean_object* v_m_284_, lean_object* v_a_285_){
_start:
{
lean_object* v_size_286_; lean_object* v_buckets_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v_fold_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; lean_object* v_bkt_303_; uint8_t v___x_304_; 
v_size_286_ = lean_ctor_get(v_m_284_, 0);
v_buckets_287_ = lean_ctor_get(v_m_284_, 1);
v___x_288_ = lean_array_get_size(v_buckets_287_);
lean_inc_ref(v_x_283_);
lean_inc_n(v_a_285_, 2);
v___x_289_ = lean_apply_1(v_x_283_, v_a_285_);
v___x_290_ = 32ULL;
v___x_291_ = lean_unbox_uint64(v___x_289_);
v___x_292_ = lean_uint64_shift_right(v___x_291_, v___x_290_);
v___x_293_ = lean_unbox_uint64(v___x_289_);
lean_dec_ref(v___x_289_);
v_fold_294_ = lean_uint64_xor(v___x_293_, v___x_292_);
v___x_295_ = 16ULL;
v___x_296_ = lean_uint64_shift_right(v_fold_294_, v___x_295_);
v___x_297_ = lean_uint64_xor(v_fold_294_, v___x_296_);
v___x_298_ = lean_uint64_to_usize(v___x_297_);
v___x_299_ = lean_usize_of_nat(v___x_288_);
v___x_300_ = ((size_t)1ULL);
v___x_301_ = lean_usize_sub(v___x_299_, v___x_300_);
v___x_302_ = lean_usize_land(v___x_298_, v___x_301_);
v_bkt_303_ = lean_array_uget_borrowed(v_buckets_287_, v___x_302_);
lean_inc(v_bkt_303_);
v___x_304_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_282_, v_a_285_, v_bkt_303_);
if (v___x_304_ == 0)
{
lean_object* v___x_306_; uint8_t v_isShared_307_; uint8_t v_isSharedCheck_330_; 
lean_inc_ref(v_buckets_287_);
lean_inc(v_size_286_);
v_isSharedCheck_330_ = !lean_is_exclusive(v_m_284_);
if (v_isSharedCheck_330_ == 0)
{
lean_object* v_unused_331_; lean_object* v_unused_332_; 
v_unused_331_ = lean_ctor_get(v_m_284_, 1);
lean_dec(v_unused_331_);
v_unused_332_ = lean_ctor_get(v_m_284_, 0);
lean_dec(v_unused_332_);
v___x_306_ = v_m_284_;
v_isShared_307_ = v_isSharedCheck_330_;
goto v_resetjp_305_;
}
else
{
lean_dec(v_m_284_);
v___x_306_ = lean_box(0);
v_isShared_307_ = v_isSharedCheck_330_;
goto v_resetjp_305_;
}
v_resetjp_305_:
{
lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v_size_x27_310_; lean_object* v___x_311_; lean_object* v_buckets_x27_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_308_ = lean_box(0);
v___x_309_ = lean_unsigned_to_nat(1u);
v_size_x27_310_ = lean_nat_add(v_size_286_, v___x_309_);
lean_dec(v_size_286_);
lean_inc(v_bkt_303_);
v___x_311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_311_, 0, v_a_285_);
lean_ctor_set(v___x_311_, 1, v___x_308_);
lean_ctor_set(v___x_311_, 2, v_bkt_303_);
v_buckets_x27_312_ = lean_array_uset(v_buckets_287_, v___x_302_, v___x_311_);
v___x_313_ = lean_unsigned_to_nat(4u);
v___x_314_ = lean_nat_mul(v_size_x27_310_, v___x_313_);
v___x_315_ = lean_unsigned_to_nat(3u);
v___x_316_ = lean_nat_div(v___x_314_, v___x_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_array_get_size(v_buckets_x27_312_);
v___x_318_ = lean_nat_dec_le(v___x_316_, v___x_317_);
lean_dec(v___x_316_);
if (v___x_318_ == 0)
{
lean_object* v_val_319_; lean_object* v___x_321_; 
v_val_319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_283_, v_buckets_x27_312_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_val_319_);
lean_ctor_set(v___x_306_, 0, v_size_x27_310_);
v___x_321_ = v___x_306_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_size_x27_310_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_val_319_);
v___x_321_ = v_reuseFailAlloc_324_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_box(v___x_304_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
return v___x_323_;
}
}
else
{
lean_object* v___x_326_; 
lean_dec_ref(v_x_283_);
if (v_isShared_307_ == 0)
{
lean_ctor_set(v___x_306_, 1, v_buckets_x27_312_);
lean_ctor_set(v___x_306_, 0, v_size_x27_310_);
v___x_326_ = v___x_306_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_size_x27_310_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_buckets_x27_312_);
v___x_326_ = v_reuseFailAlloc_329_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_box(v___x_304_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
return v___x_328_;
}
}
}
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_a_285_);
lean_dec_ref(v_x_283_);
v___x_333_ = lean_box(v___x_304_);
v___x_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v_m_284_);
return v___x_334_;
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_contains___redArg(lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_m_337_, lean_object* v_a_338_){
_start:
{
uint8_t v___x_339_; 
v___x_339_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_335_, v_x_336_, v_m_337_, v_a_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___redArg___boxed(lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_m_342_, lean_object* v_a_343_){
_start:
{
uint8_t v_res_344_; lean_object* v_r_345_; 
v_res_344_ = l_Std_HashSet_contains___redArg(v_x_340_, v_x_341_, v_m_342_, v_a_343_);
lean_dec_ref(v_m_342_);
v_r_345_ = lean_box(v_res_344_);
return v_r_345_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_contains(lean_object* v_00_u03b1_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_m_349_, lean_object* v_a_350_){
_start:
{
uint8_t v___x_351_; 
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_347_, v_x_348_, v_m_349_, v_a_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___boxed(lean_object* v_00_u03b1_352_, lean_object* v_x_353_, lean_object* v_x_354_, lean_object* v_m_355_, lean_object* v_a_356_){
_start:
{
uint8_t v_res_357_; lean_object* v_r_358_; 
v_res_357_ = l_Std_HashSet_contains(v_00_u03b1_352_, v_x_353_, v_x_354_, v_m_355_, v_a_356_);
lean_dec_ref(v_m_355_);
v_r_358_ = lean_box(v_res_357_);
return v_r_358_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___redArg(){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = lean_box(0);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___redArg___boxed(lean_object* v___dummy_361_){
_start:
{
lean_object* v_res_362_; 
v_res_362_ = l_Std_HashSet_instMembership___redArg();
return v_res_362_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership(lean_object* v_00_u03b1_363_, lean_object* v_inst_364_, lean_object* v_inst_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = lean_box(0);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___boxed(lean_object* v_00_u03b1_367_, lean_object* v_inst_368_, lean_object* v_inst_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_HashSet_instMembership(v_00_u03b1_367_, v_inst_368_, v_inst_369_);
lean_dec_ref(v_inst_369_);
lean_dec_ref(v_inst_368_);
return v_res_370_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem___redArg(lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_m_373_, lean_object* v_a_374_){
_start:
{
uint8_t v___x_375_; 
v___x_375_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_371_, v_inst_372_, v_m_373_, v_a_374_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___redArg___boxed(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_m_378_, lean_object* v_a_379_){
_start:
{
uint8_t v_res_380_; lean_object* v_r_381_; 
v_res_380_ = l_Std_HashSet_instDecidableMem___redArg(v_inst_376_, v_inst_377_, v_m_378_, v_a_379_);
lean_dec_ref(v_m_378_);
v_r_381_ = lean_box(v_res_380_);
return v_r_381_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem(lean_object* v_00_u03b1_382_, lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_m_385_, lean_object* v_a_386_){
_start:
{
uint8_t v___x_387_; 
v___x_387_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_383_, v_inst_384_, v_m_385_, v_a_386_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___boxed(lean_object* v_00_u03b1_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_m_391_, lean_object* v_a_392_){
_start:
{
uint8_t v_res_393_; lean_object* v_r_394_; 
v_res_393_ = l_Std_HashSet_instDecidableMem(v_00_u03b1_388_, v_inst_389_, v_inst_390_, v_m_391_, v_a_392_);
lean_dec_ref(v_m_391_);
v_r_394_ = lean_box(v_res_393_);
return v_r_394_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase___redArg(lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_m_397_, lean_object* v_a_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_395_, v_x_396_, v_m_397_, v_a_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase(lean_object* v_00_u03b1_400_, lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_m_403_, lean_object* v_a_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_401_, v_x_402_, v_m_403_, v_a_404_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg(lean_object* v_m_406_){
_start:
{
lean_object* v_size_407_; 
v_size_407_ = lean_ctor_get(v_m_406_, 0);
lean_inc(v_size_407_);
return v_size_407_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg___boxed(lean_object* v_m_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_HashSet_size___redArg(v_m_408_);
lean_dec_ref(v_m_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size(lean_object* v_00_u03b1_410_, lean_object* v_x_411_, lean_object* v_x_412_, lean_object* v_m_413_){
_start:
{
lean_object* v_size_414_; 
v_size_414_ = lean_ctor_get(v_m_413_, 0);
lean_inc(v_size_414_);
return v_size_414_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___boxed(lean_object* v_00_u03b1_415_, lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_m_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_HashSet_size(v_00_u03b1_415_, v_x_416_, v_x_417_, v_m_418_);
lean_dec_ref(v_m_418_);
lean_dec_ref(v_x_417_);
lean_dec_ref(v_x_416_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg(lean_object* v_x_420_, lean_object* v_x_421_, lean_object* v_m_422_, lean_object* v_a_423_){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_420_, v_x_421_, v_m_422_, v_a_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg___boxed(lean_object* v_x_425_, lean_object* v_x_426_, lean_object* v_m_427_, lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Std_HashSet_get_x3f___redArg(v_x_425_, v_x_426_, v_m_427_, v_a_428_);
lean_dec_ref(v_m_427_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f(lean_object* v_00_u03b1_430_, lean_object* v_x_431_, lean_object* v_x_432_, lean_object* v_m_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_435_; 
v___x_435_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_431_, v_x_432_, v_m_433_, v_a_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___boxed(lean_object* v_00_u03b1_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_m_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_HashSet_get_x3f(v_00_u03b1_436_, v_x_437_, v_x_438_, v_m_439_, v_a_440_);
lean_dec_ref(v_m_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg(lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_m_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___x_446_; 
v___x_446_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_442_, v_inst_443_, v_m_444_, v_a_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg___boxed(lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_m_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_HashSet_get___redArg(v_inst_447_, v_inst_448_, v_m_449_, v_a_450_);
lean_dec_ref(v_m_449_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get(lean_object* v_00_u03b1_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_m_455_, lean_object* v_a_456_, lean_object* v_h_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_453_, v_inst_454_, v_m_455_, v_a_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___boxed(lean_object* v_00_u03b1_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_m_462_, lean_object* v_a_463_, lean_object* v_h_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_HashSet_get(v_00_u03b1_459_, v_inst_460_, v_inst_461_, v_m_462_, v_a_463_, v_h_464_);
lean_dec_ref(v_m_462_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg(lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_m_468_, lean_object* v_a_469_, lean_object* v_fallback_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_466_, v_inst_467_, v_m_468_, v_a_469_, v_fallback_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg___boxed(lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_m_474_, lean_object* v_a_475_, lean_object* v_fallback_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_HashSet_getD___redArg(v_inst_472_, v_inst_473_, v_m_474_, v_a_475_, v_fallback_476_);
lean_dec(v_fallback_476_);
lean_dec_ref(v_m_474_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD(lean_object* v_00_u03b1_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_m_481_, lean_object* v_a_482_, lean_object* v_fallback_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_479_, v_inst_480_, v_m_481_, v_a_482_, v_fallback_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___boxed(lean_object* v_00_u03b1_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_m_488_, lean_object* v_a_489_, lean_object* v_fallback_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_HashSet_getD(v_00_u03b1_485_, v_inst_486_, v_inst_487_, v_m_488_, v_a_489_, v_fallback_490_);
lean_dec(v_fallback_490_);
lean_dec_ref(v_m_488_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg(lean_object* v_inst_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_m_495_, lean_object* v_a_496_){
_start:
{
lean_object* v___x_497_; 
v___x_497_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_492_, v_inst_493_, v_inst_494_, v_m_495_, v_a_496_);
return v___x_497_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg___boxed(lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_m_501_, lean_object* v_a_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Std_HashSet_get_x21___redArg(v_inst_498_, v_inst_499_, v_inst_500_, v_m_501_, v_a_502_);
lean_dec_ref(v_m_501_);
lean_dec(v_inst_500_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21(lean_object* v_00_u03b1_504_, lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_m_508_, lean_object* v_a_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_505_, v_inst_506_, v_inst_507_, v_m_508_, v_a_509_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___boxed(lean_object* v_00_u03b1_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_m_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_HashSet_get_x21(v_00_u03b1_511_, v_inst_512_, v_inst_513_, v_inst_514_, v_m_515_, v_a_516_);
lean_dec_ref(v_m_515_);
lean_dec(v_inst_514_);
return v_res_517_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty___redArg(lean_object* v_m_518_){
_start:
{
lean_object* v_size_519_; lean_object* v___x_520_; uint8_t v___x_521_; 
v_size_519_ = lean_ctor_get(v_m_518_, 0);
v___x_520_ = lean_unsigned_to_nat(0u);
v___x_521_ = lean_nat_dec_eq(v_size_519_, v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___redArg___boxed(lean_object* v_m_522_){
_start:
{
uint8_t v_res_523_; lean_object* v_r_524_; 
v_res_523_ = l_Std_HashSet_isEmpty___redArg(v_m_522_);
lean_dec_ref(v_m_522_);
v_r_524_ = lean_box(v_res_523_);
return v_r_524_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty(lean_object* v_00_u03b1_525_, lean_object* v_x_526_, lean_object* v_x_527_, lean_object* v_m_528_){
_start:
{
lean_object* v_size_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_size_529_ = lean_ctor_get(v_m_528_, 0);
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_nat_dec_eq(v_size_529_, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___boxed(lean_object* v_00_u03b1_532_, lean_object* v_x_533_, lean_object* v_x_534_, lean_object* v_m_535_){
_start:
{
uint8_t v_res_536_; lean_object* v_r_537_; 
v_res_536_ = l_Std_HashSet_isEmpty(v_00_u03b1_532_, v_x_533_, v_x_534_, v_m_535_);
lean_dec_ref(v_m_535_);
lean_dec_ref(v_x_534_);
lean_dec_ref(v_x_533_);
v_r_537_ = lean_box(v_res_536_);
return v_r_537_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0(lean_object* v_a_538_, lean_object* v_b_539_, lean_object* v_d_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_541_, 0, v_a_538_);
lean_ctor_set(v___x_541_, 1, v_d_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__1(lean_object* v___x_542_, lean_object* v___f_543_, lean_object* v_l_544_, lean_object* v_acc_545_){
_start:
{
lean_object* v___x_546_; 
v___x_546_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_542_, v___f_543_, v_acc_545_, v_l_544_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg(lean_object* v_m_570_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_toList(lean_object* v_00_u03b1_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_m_584_){
_start:
{
lean_object* v___x_585_; lean_object* v_buckets_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_585_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_586_ = lean_ctor_get(v_m_584_, 1);
lean_inc_ref(v_buckets_586_);
lean_dec_ref(v_m_584_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_array_get_size(v_buckets_586_);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_nat_dec_lt(v___x_589_, v___x_588_);
if (v___x_590_ == 0)
{
lean_dec_ref(v_buckets_586_);
return v___x_587_;
}
else
{
lean_object* v___f_591_; size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v___f_591_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__11));
v___x_592_ = lean_usize_of_nat(v___x_588_);
v___x_593_ = ((size_t)0ULL);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_585_, v___f_591_, v_buckets_586_, v___x_592_, v___x_593_, v___x_587_);
return v___x_594_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___boxed(lean_object* v_00_u03b1_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_m_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Std_HashSet_toList(v_00_u03b1_595_, v_x_596_, v_x_597_, v_m_598_);
lean_dec_ref(v_x_597_);
lean_dec_ref(v_x_596_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg(lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_l_606_){
_start:
{
lean_object* v___f_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
v___f_607_ = ((lean_object*)(l_Std_HashSet_ofList___redArg___closed__1));
v___x_608_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_607_, v_inst_604_, v_inst_605_, v___x_608_, v_l_606_);
return v___x_609_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList(lean_object* v_00_u03b1_610_, lean_object* v_inst_611_, lean_object* v_inst_612_, lean_object* v_l_613_){
_start:
{
lean_object* v___f_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___f_614_ = ((lean_object*)(l_Std_HashSet_ofList___redArg___closed__1));
v___x_615_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_616_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_614_, v_inst_611_, v_inst_612_, v___x_615_, v_l_613_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0(lean_object* v_f_617_, lean_object* v_b_618_, lean_object* v_a_619_, lean_object* v_x_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_apply_2(v_f_617_, v_b_618_, v_a_619_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__1(lean_object* v_inst_622_, lean_object* v___f_623_, lean_object* v_acc_624_, lean_object* v_l_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_622_, v___f_623_, v_acc_624_, v_l_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg(lean_object* v_inst_627_, lean_object* v_f_628_, lean_object* v_init_629_, lean_object* v_b_630_){
_start:
{
lean_object* v_toApplicative_631_; lean_object* v_buckets_632_; lean_object* v_toPure_633_; lean_object* v___x_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_toApplicative_631_ = lean_ctor_get(v_inst_627_, 0);
v_buckets_632_ = lean_ctor_get(v_b_630_, 1);
lean_inc_ref(v_buckets_632_);
lean_dec_ref(v_b_630_);
v_toPure_633_ = lean_ctor_get(v_toApplicative_631_, 1);
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = lean_array_get_size(v_buckets_632_);
v___x_636_ = lean_nat_dec_lt(v___x_634_, v___x_635_);
if (v___x_636_ == 0)
{
lean_object* v___x_637_; 
lean_inc(v_toPure_633_);
lean_dec_ref(v_buckets_632_);
lean_dec(v_f_628_);
lean_dec_ref(v_inst_627_);
v___x_637_ = lean_apply_2(v_toPure_633_, lean_box(0), v_init_629_);
return v___x_637_;
}
else
{
lean_object* v___f_638_; lean_object* v___f_639_; size_t v___x_640_; size_t v___x_641_; lean_object* v___x_642_; 
v___f_638_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_638_, 0, v_f_628_);
lean_inc_ref(v_inst_627_);
v___f_639_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_639_, 0, v_inst_627_);
lean_closure_set(v___f_639_, 1, v___f_638_);
v___x_640_ = ((size_t)0ULL);
v___x_641_ = lean_usize_of_nat(v___x_635_);
v___x_642_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_627_, v___f_639_, v_buckets_632_, v___x_640_, v___x_641_, v_init_629_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM(lean_object* v_00_u03b1_643_, lean_object* v_x_644_, lean_object* v_x_645_, lean_object* v_m_646_, lean_object* v_inst_647_, lean_object* v_00_u03b2_648_, lean_object* v_f_649_, lean_object* v_init_650_, lean_object* v_b_651_){
_start:
{
lean_object* v_toApplicative_652_; lean_object* v_buckets_653_; lean_object* v_toPure_654_; lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_toApplicative_652_ = lean_ctor_get(v_inst_647_, 0);
v_buckets_653_ = lean_ctor_get(v_b_651_, 1);
lean_inc_ref(v_buckets_653_);
lean_dec_ref(v_b_651_);
v_toPure_654_ = lean_ctor_get(v_toApplicative_652_, 1);
v___x_655_ = lean_unsigned_to_nat(0u);
v___x_656_ = lean_array_get_size(v_buckets_653_);
v___x_657_ = lean_nat_dec_lt(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_inc(v_toPure_654_);
lean_dec_ref(v_buckets_653_);
lean_dec(v_f_649_);
lean_dec_ref(v_inst_647_);
v___x_658_ = lean_apply_2(v_toPure_654_, lean_box(0), v_init_650_);
return v___x_658_;
}
else
{
lean_object* v___f_659_; lean_object* v___f_660_; size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; 
v___f_659_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_659_, 0, v_f_649_);
lean_inc_ref(v_inst_647_);
v___f_660_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_660_, 0, v_inst_647_);
lean_closure_set(v___f_660_, 1, v___f_659_);
v___x_661_ = ((size_t)0ULL);
v___x_662_ = lean_usize_of_nat(v___x_656_);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_647_, v___f_660_, v_buckets_653_, v___x_661_, v___x_662_, v_init_650_);
return v___x_663_;
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
lean_object* v___f_692_; lean_object* v___f_693_; size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
v___f_692_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_692_, 0, v_f_684_);
v___f_693_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_693_, 0, v___x_687_);
lean_closure_set(v___f_693_, 1, v___f_692_);
v___x_694_ = ((size_t)0ULL);
v___x_695_ = lean_usize_of_nat(v___x_690_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_687_, v___f_693_, v_buckets_688_, v___x_694_, v___x_695_, v_init_685_);
return v___x_696_;
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
lean_object* v___f_709_; lean_object* v___f_710_; size_t v___x_711_; size_t v___x_712_; lean_object* v___x_713_; 
v___f_709_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_709_, 0, v_f_701_);
v___f_710_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_710_, 0, v___x_704_);
lean_closure_set(v___f_710_, 1, v___f_709_);
v___x_711_ = ((size_t)0ULL);
v___x_712_ = lean_usize_of_nat(v___x_707_);
v___x_713_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_704_, v___f_710_, v_buckets_705_, v___x_711_, v___x_712_, v_init_702_);
return v___x_713_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___boxed(lean_object* v_00_u03b1_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_00_u03b2_717_, lean_object* v_f_718_, lean_object* v_init_719_, lean_object* v_m_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Std_HashSet_fold(v_00_u03b1_714_, v_x_715_, v_x_716_, v_00_u03b2_717_, v_f_718_, v_init_719_, v_m_720_);
lean_dec_ref(v_x_716_);
lean_dec_ref(v_x_715_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0(lean_object* v_f_722_, lean_object* v_x_723_, lean_object* v___y_724_, lean_object* v___y_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = lean_apply_1(v_f_722_, v___y_724_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__1(lean_object* v_inst_727_, lean_object* v___f_728_, lean_object* v_x_729_, lean_object* v___y_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_731_ = lean_box(0);
v___x_732_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_727_, v___f_728_, v___x_731_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg(lean_object* v_inst_733_, lean_object* v_f_734_, lean_object* v_b_735_){
_start:
{
lean_object* v_toApplicative_736_; lean_object* v_buckets_737_; lean_object* v_toPure_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; uint8_t v___x_742_; 
v_toApplicative_736_ = lean_ctor_get(v_inst_733_, 0);
v_buckets_737_ = lean_ctor_get(v_b_735_, 1);
lean_inc_ref(v_buckets_737_);
lean_dec_ref(v_b_735_);
v_toPure_738_ = lean_ctor_get(v_toApplicative_736_, 1);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_array_get_size(v_buckets_737_);
v___x_741_ = lean_box(0);
v___x_742_ = lean_nat_dec_lt(v___x_739_, v___x_740_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; 
lean_inc(v_toPure_738_);
lean_dec_ref(v_buckets_737_);
lean_dec(v_f_734_);
lean_dec_ref(v_inst_733_);
v___x_743_ = lean_apply_2(v_toPure_738_, lean_box(0), v___x_741_);
return v___x_743_;
}
else
{
lean_object* v___f_744_; lean_object* v___f_745_; size_t v___x_746_; size_t v___x_747_; lean_object* v___x_748_; 
v___f_744_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_744_, 0, v_f_734_);
lean_inc_ref(v_inst_733_);
v___f_745_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_745_, 0, v_inst_733_);
lean_closure_set(v___f_745_, 1, v___f_744_);
v___x_746_ = ((size_t)0ULL);
v___x_747_ = lean_usize_of_nat(v___x_740_);
v___x_748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_733_, v___f_745_, v_buckets_737_, v___x_746_, v___x_747_, v___x_741_);
return v___x_748_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM(lean_object* v_00_u03b1_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_m_752_, lean_object* v_inst_753_, lean_object* v_f_754_, lean_object* v_b_755_){
_start:
{
lean_object* v_toApplicative_756_; lean_object* v_buckets_757_; lean_object* v_toPure_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_toApplicative_756_ = lean_ctor_get(v_inst_753_, 0);
v_buckets_757_ = lean_ctor_get(v_b_755_, 1);
lean_inc_ref(v_buckets_757_);
lean_dec_ref(v_b_755_);
v_toPure_758_ = lean_ctor_get(v_toApplicative_756_, 1);
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_array_get_size(v_buckets_757_);
v___x_761_ = lean_box(0);
v___x_762_ = lean_nat_dec_lt(v___x_759_, v___x_760_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
lean_inc(v_toPure_758_);
lean_dec_ref(v_buckets_757_);
lean_dec(v_f_754_);
lean_dec_ref(v_inst_753_);
v___x_763_ = lean_apply_2(v_toPure_758_, lean_box(0), v___x_761_);
return v___x_763_;
}
else
{
lean_object* v___f_764_; lean_object* v___f_765_; size_t v___x_766_; size_t v___x_767_; lean_object* v___x_768_; 
v___f_764_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_764_, 0, v_f_754_);
lean_inc_ref(v_inst_753_);
v___f_765_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_765_, 0, v_inst_753_);
lean_closure_set(v___f_765_, 1, v___f_764_);
v___x_766_ = ((size_t)0ULL);
v___x_767_ = lean_usize_of_nat(v___x_760_);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_753_, v___f_765_, v_buckets_757_, v___x_766_, v___x_767_, v___x_761_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___boxed(lean_object* v_00_u03b1_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_m_772_, lean_object* v_inst_773_, lean_object* v_f_774_, lean_object* v_b_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Std_HashSet_forM(v_00_u03b1_769_, v_x_770_, v_x_771_, v_m_772_, v_inst_773_, v_f_774_, v_b_775_);
lean_dec_ref(v_x_771_);
lean_dec_ref(v_x_770_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0(lean_object* v_f_777_, lean_object* v_a_778_, lean_object* v_x_779_, lean_object* v_acc_780_){
_start:
{
lean_object* v___x_781_; 
v___x_781_ = lean_apply_2(v_f_777_, v_a_778_, v_acc_780_);
return v___x_781_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__1(lean_object* v_inst_782_, lean_object* v___f_783_, lean_object* v_a_784_, lean_object* v_x_785_, lean_object* v___y_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_782_, v___f_783_, v_a_784_, v___y_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg(lean_object* v_inst_788_, lean_object* v_f_789_, lean_object* v_init_790_, lean_object* v_b_791_){
_start:
{
lean_object* v_buckets_792_; lean_object* v___f_793_; lean_object* v___f_794_; size_t v_sz_795_; size_t v___x_796_; lean_object* v___x_797_; 
v_buckets_792_ = lean_ctor_get(v_b_791_, 1);
lean_inc_ref(v_buckets_792_);
lean_dec_ref(v_b_791_);
v___f_793_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_793_, 0, v_f_789_);
lean_inc_ref(v_inst_788_);
v___f_794_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_794_, 0, v_inst_788_);
lean_closure_set(v___f_794_, 1, v___f_793_);
v_sz_795_ = lean_array_size(v_buckets_792_);
v___x_796_ = ((size_t)0ULL);
v___x_797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_788_, v_buckets_792_, v___f_794_, v_sz_795_, v___x_796_, v_init_790_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn(lean_object* v_00_u03b1_798_, lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_m_801_, lean_object* v_inst_802_, lean_object* v_00_u03b2_803_, lean_object* v_f_804_, lean_object* v_init_805_, lean_object* v_b_806_){
_start:
{
lean_object* v_buckets_807_; lean_object* v___f_808_; lean_object* v___f_809_; size_t v_sz_810_; size_t v___x_811_; lean_object* v___x_812_; 
v_buckets_807_ = lean_ctor_get(v_b_806_, 1);
lean_inc_ref(v_buckets_807_);
lean_dec_ref(v_b_806_);
v___f_808_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_808_, 0, v_f_804_);
lean_inc_ref(v_inst_802_);
v___f_809_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_809_, 0, v_inst_802_);
lean_closure_set(v___f_809_, 1, v___f_808_);
v_sz_810_ = lean_array_size(v_buckets_807_);
v___x_811_ = ((size_t)0ULL);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_802_, v_buckets_807_, v___f_809_, v_sz_810_, v___x_811_, v_init_805_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___boxed(lean_object* v_00_u03b1_813_, lean_object* v_x_814_, lean_object* v_x_815_, lean_object* v_m_816_, lean_object* v_inst_817_, lean_object* v_00_u03b2_818_, lean_object* v_f_819_, lean_object* v_init_820_, lean_object* v_b_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Std_HashSet_forIn(v_00_u03b1_813_, v_x_814_, v_x_815_, v_m_816_, v_inst_817_, v_00_u03b2_818_, v_f_819_, v_init_820_, v_b_821_);
lean_dec_ref(v_x_815_);
lean_dec_ref(v_x_814_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg___lam__2(lean_object* v_inst_823_, lean_object* v_m_824_, lean_object* v_f_825_){
_start:
{
lean_object* v_toApplicative_826_; lean_object* v_buckets_827_; lean_object* v_toPure_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_toApplicative_826_ = lean_ctor_get(v_inst_823_, 0);
v_buckets_827_ = lean_ctor_get(v_m_824_, 1);
lean_inc_ref(v_buckets_827_);
lean_dec_ref(v_m_824_);
v_toPure_828_ = lean_ctor_get(v_toApplicative_826_, 1);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_array_get_size(v_buckets_827_);
v___x_831_ = lean_box(0);
v___x_832_ = lean_nat_dec_lt(v___x_829_, v___x_830_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; 
lean_inc(v_toPure_828_);
lean_dec_ref(v_buckets_827_);
lean_dec(v_f_825_);
lean_dec_ref(v_inst_823_);
v___x_833_ = lean_apply_2(v_toPure_828_, lean_box(0), v___x_831_);
return v___x_833_;
}
else
{
lean_object* v___f_834_; lean_object* v___f_835_; size_t v___x_836_; size_t v___x_837_; lean_object* v___x_838_; 
v___f_834_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_834_, 0, v_f_825_);
lean_inc_ref(v_inst_823_);
v___f_835_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_835_, 0, v_inst_823_);
lean_closure_set(v___f_835_, 1, v___f_834_);
v___x_836_ = ((size_t)0ULL);
v___x_837_ = lean_usize_of_nat(v___x_830_);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_823_, v___f_835_, v_buckets_827_, v___x_836_, v___x_837_, v___x_831_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg(lean_object* v_inst_839_){
_start:
{
lean_object* v___f_840_; 
v___f_840_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_840_, 0, v_inst_839_);
return v___f_840_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad(lean_object* v_00_u03b1_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_m_844_, lean_object* v_inst_845_){
_start:
{
lean_object* v___f_846_; 
v___f_846_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_846_, 0, v_inst_845_);
return v___f_846_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_847_, lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_m_850_, lean_object* v_inst_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l_Std_HashSet_instForMOfMonad(v_00_u03b1_847_, v_inst_848_, v_inst_849_, v_m_850_, v_inst_851_);
lean_dec_ref(v_inst_849_);
lean_dec_ref(v_inst_848_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg___lam__2(lean_object* v_inst_853_, lean_object* v_00_u03b2_854_, lean_object* v_m_855_, lean_object* v_init_856_, lean_object* v_f_857_){
_start:
{
lean_object* v_buckets_858_; lean_object* v___f_859_; lean_object* v___f_860_; size_t v_sz_861_; size_t v___x_862_; lean_object* v___x_863_; 
v_buckets_858_ = lean_ctor_get(v_m_855_, 1);
lean_inc_ref(v_buckets_858_);
lean_dec_ref(v_m_855_);
v___f_859_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_859_, 0, v_f_857_);
lean_inc_ref(v_inst_853_);
v___f_860_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_860_, 0, v_inst_853_);
lean_closure_set(v___f_860_, 1, v___f_859_);
v_sz_861_ = lean_array_size(v_buckets_858_);
v___x_862_ = ((size_t)0ULL);
v___x_863_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_853_, v_buckets_858_, v___f_860_, v_sz_861_, v___x_862_, v_init_856_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg(lean_object* v_inst_864_){
_start:
{
lean_object* v___f_865_; 
v___f_865_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_865_, 0, v_inst_864_);
return v___f_865_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad(lean_object* v_00_u03b1_866_, lean_object* v_inst_867_, lean_object* v_inst_868_, lean_object* v_m_869_, lean_object* v_inst_870_){
_start:
{
lean_object* v___f_871_; 
v___f_871_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_871_, 0, v_inst_870_);
return v___f_871_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_m_875_, lean_object* v_inst_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_HashSet_instForInOfMonad(v_00_u03b1_872_, v_inst_873_, v_inst_874_, v_m_875_, v_inst_876_);
lean_dec_ref(v_inst_874_);
lean_dec_ref(v_inst_873_);
return v_res_877_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_filter___redArg___lam__0(lean_object* v_f_878_, lean_object* v_a_879_, lean_object* v_x_880_){
_start:
{
lean_object* v___x_881_; uint8_t v___x_882_; 
v___x_881_ = lean_apply_1(v_f_878_, v_a_879_);
v___x_882_ = lean_unbox(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__0___boxed(lean_object* v_f_883_, lean_object* v_a_884_, lean_object* v_x_885_){
_start:
{
uint8_t v_res_886_; lean_object* v_r_887_; 
v_res_886_ = l_Std_HashSet_filter___redArg___lam__0(v_f_883_, v_a_884_, v_x_885_);
v_r_887_ = lean_box(v_res_886_);
return v_r_887_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg(lean_object* v_f_888_, lean_object* v_m_889_){
_start:
{
lean_object* v___f_890_; lean_object* v___x_891_; 
v___f_890_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_890_, 0, v_f_888_);
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_890_, v_m_889_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter(lean_object* v_00_u03b1_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_f_895_, lean_object* v_m_896_){
_start:
{
lean_object* v___f_897_; lean_object* v___x_898_; 
v___f_897_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_897_, 0, v_f_895_);
v___x_898_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_897_, v_m_896_);
return v___x_898_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___boxed(lean_object* v_00_u03b1_899_, lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_f_902_, lean_object* v_m_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Std_HashSet_filter(v_00_u03b1_899_, v_x_900_, v_x_901_, v_f_902_, v_m_903_);
lean_dec_ref(v_x_901_);
lean_dec_ref(v_x_900_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg(lean_object* v_x_905_, lean_object* v_x_906_, lean_object* v_inst_907_, lean_object* v_m_908_, lean_object* v_l_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_907_, v_x_905_, v_x_906_, v_m_908_, v_l_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany(lean_object* v_00_u03b1_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_00_u03c1_914_, lean_object* v_inst_915_, lean_object* v_m_916_, lean_object* v_l_917_){
_start:
{
lean_object* v___x_918_; 
v___x_918_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_915_, v_x_912_, v_x_913_, v_m_916_, v_l_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0(lean_object* v_x1_919_, lean_object* v_x2_920_, lean_object* v_x3_921_){
_start:
{
lean_object* v___x_922_; 
v___x_922_ = lean_array_push(v_x1_919_, v_x2_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__1(lean_object* v___x_923_, lean_object* v___f_924_, lean_object* v_acc_925_, lean_object* v_l_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_923_, v___f_924_, v_acc_925_, v_l_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg(lean_object* v_m_932_){
_start:
{
lean_object* v_size_933_; lean_object* v_buckets_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_size_933_ = lean_ctor_get(v_m_932_, 0);
lean_inc(v_size_933_);
v_buckets_934_ = lean_ctor_get(v_m_932_, 1);
lean_inc_ref(v_buckets_934_);
lean_dec_ref(v_m_932_);
v___x_935_ = lean_mk_empty_array_with_capacity(v_size_933_);
lean_dec(v_size_933_);
v___x_936_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_array_get_size(v_buckets_934_);
v___x_939_ = lean_nat_dec_lt(v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_dec_ref(v_buckets_934_);
return v___x_935_;
}
else
{
lean_object* v___f_940_; size_t v___x_941_; size_t v___x_942_; lean_object* v___x_943_; 
v___f_940_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__1));
v___x_941_ = ((size_t)0ULL);
v___x_942_ = lean_usize_of_nat(v___x_938_);
v___x_943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_936_, v___f_940_, v_buckets_934_, v___x_941_, v___x_942_, v___x_935_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray(lean_object* v_00_u03b1_944_, lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_m_947_){
_start:
{
lean_object* v_size_948_; lean_object* v_buckets_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v_size_948_ = lean_ctor_get(v_m_947_, 0);
lean_inc(v_size_948_);
v_buckets_949_ = lean_ctor_get(v_m_947_, 1);
lean_inc_ref(v_buckets_949_);
lean_dec_ref(v_m_947_);
v___x_950_ = lean_mk_empty_array_with_capacity(v_size_948_);
lean_dec(v_size_948_);
v___x_951_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = lean_array_get_size(v_buckets_949_);
v___x_954_ = lean_nat_dec_lt(v___x_952_, v___x_953_);
if (v___x_954_ == 0)
{
lean_dec_ref(v_buckets_949_);
return v___x_950_;
}
else
{
lean_object* v___f_955_; size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v___f_955_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__1));
v___x_956_ = ((size_t)0ULL);
v___x_957_ = lean_usize_of_nat(v___x_953_);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_951_, v___f_955_, v_buckets_949_, v___x_956_, v___x_957_, v___x_950_);
return v___x_958_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___boxed(lean_object* v_00_u03b1_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_m_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_HashSet_toArray(v_00_u03b1_959_, v_x_960_, v_x_961_, v_m_962_);
lean_dec_ref(v_x_961_);
lean_dec_ref(v_x_960_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0(lean_object* v_p_964_, lean_object* v___x_965_, lean_object* v___x_966_, lean_object* v_a_967_, lean_object* v_b_968_, lean_object* v_acc_969_){
_start:
{
lean_object* v___x_970_; uint8_t v___x_971_; 
v___x_970_ = lean_apply_1(v_p_964_, v_a_967_);
v___x_971_ = lean_unbox(v___x_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec_ref(v___x_966_);
v___x_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_972_, 0, v___x_970_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
lean_ctor_set(v___x_973_, 1, v___x_965_);
v___x_974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_973_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_966_);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0___boxed(lean_object* v_p_976_, lean_object* v___x_977_, lean_object* v___x_978_, lean_object* v_a_979_, lean_object* v_b_980_, lean_object* v_acc_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Std_HashSet_all___redArg___lam__0(v_p_976_, v___x_977_, v___x_978_, v_a_979_, v_b_980_, v_acc_981_);
lean_dec_ref(v_acc_981_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__1(lean_object* v___x_983_, lean_object* v___f_984_, lean_object* v_a_985_, lean_object* v_x_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_983_, v___f_984_, v_a_985_, v___y_987_);
return v___x_988_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all___redArg(lean_object* v_m_992_, lean_object* v_p_993_){
_start:
{
lean_object* v___x_994_; lean_object* v_buckets_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___f_998_; lean_object* v___f_999_; size_t v_sz_1000_; size_t v___x_1001_; lean_object* v___x_1002_; lean_object* v_fst_1003_; 
v___x_994_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_995_ = lean_ctor_get(v_m_992_, 1);
lean_inc_ref(v_buckets_995_);
lean_dec_ref(v_m_992_);
v___x_996_ = lean_box(0);
v___x_997_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_998_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_998_, 0, v_p_993_);
lean_closure_set(v___f_998_, 1, v___x_996_);
lean_closure_set(v___f_998_, 2, v___x_997_);
v___f_999_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_999_, 0, v___x_994_);
lean_closure_set(v___f_999_, 1, v___f_998_);
v_sz_1000_ = lean_array_size(v_buckets_995_);
v___x_1001_ = ((size_t)0ULL);
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_994_, v_buckets_995_, v___f_999_, v_sz_1000_, v___x_1001_, v___x_997_);
v_fst_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_fst_1003_);
lean_dec(v___x_1002_);
if (lean_obj_tag(v_fst_1003_) == 0)
{
uint8_t v___x_1004_; 
v___x_1004_ = 1;
return v___x_1004_;
}
else
{
lean_object* v_val_1005_; uint8_t v___x_1006_; 
v_val_1005_ = lean_ctor_get(v_fst_1003_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v_fst_1003_, 1);
v___x_1006_ = lean_unbox(v_val_1005_);
lean_dec(v_val_1005_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___boxed(lean_object* v_m_1007_, lean_object* v_p_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Std_HashSet_all___redArg(v_m_1007_, v_p_1008_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all(lean_object* v_00_u03b1_1011_, lean_object* v_x_1012_, lean_object* v_x_1013_, lean_object* v_m_1014_, lean_object* v_p_1015_){
_start:
{
lean_object* v___x_1016_; lean_object* v_buckets_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___f_1020_; lean_object* v___f_1021_; size_t v_sz_1022_; size_t v___x_1023_; lean_object* v___x_1024_; lean_object* v_fst_1025_; 
v___x_1016_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1017_ = lean_ctor_get(v_m_1014_, 1);
lean_inc_ref(v_buckets_1017_);
lean_dec_ref(v_m_1014_);
v___x_1018_ = lean_box(0);
v___x_1019_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1020_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1020_, 0, v_p_1015_);
lean_closure_set(v___f_1020_, 1, v___x_1018_);
lean_closure_set(v___f_1020_, 2, v___x_1019_);
v___f_1021_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1021_, 0, v___x_1016_);
lean_closure_set(v___f_1021_, 1, v___f_1020_);
v_sz_1022_ = lean_array_size(v_buckets_1017_);
v___x_1023_ = ((size_t)0ULL);
v___x_1024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1016_, v_buckets_1017_, v___f_1021_, v_sz_1022_, v___x_1023_, v___x_1019_);
v_fst_1025_ = lean_ctor_get(v___x_1024_, 0);
lean_inc(v_fst_1025_);
lean_dec(v___x_1024_);
if (lean_obj_tag(v_fst_1025_) == 0)
{
uint8_t v___x_1026_; 
v___x_1026_ = 1;
return v___x_1026_;
}
else
{
lean_object* v_val_1027_; uint8_t v___x_1028_; 
v_val_1027_ = lean_ctor_get(v_fst_1025_, 0);
lean_inc(v_val_1027_);
lean_dec_ref_known(v_fst_1025_, 1);
v___x_1028_ = lean_unbox(v_val_1027_);
lean_dec(v_val_1027_);
return v___x_1028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___boxed(lean_object* v_00_u03b1_1029_, lean_object* v_x_1030_, lean_object* v_x_1031_, lean_object* v_m_1032_, lean_object* v_p_1033_){
_start:
{
uint8_t v_res_1034_; lean_object* v_r_1035_; 
v_res_1034_ = l_Std_HashSet_all(v_00_u03b1_1029_, v_x_1030_, v_x_1031_, v_m_1032_, v_p_1033_);
lean_dec_ref(v_x_1031_);
lean_dec_ref(v_x_1030_);
v_r_1035_ = lean_box(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0(lean_object* v_p_1036_, lean_object* v___x_1037_, lean_object* v___x_1038_, lean_object* v_a_1039_, lean_object* v_b_1040_, lean_object* v_acc_1041_){
_start:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_apply_1(v_p_1036_, v_a_1039_);
v___x_1043_ = lean_unbox(v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; 
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1037_);
return v___x_1044_;
}
else
{
lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref(v___x_1037_);
v___x_1045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1042_);
v___x_1046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
lean_ctor_set(v___x_1046_, 1, v___x_1038_);
v___x_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0___boxed(lean_object* v_p_1048_, lean_object* v___x_1049_, lean_object* v___x_1050_, lean_object* v_a_1051_, lean_object* v_b_1052_, lean_object* v_acc_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Std_HashSet_any___redArg___lam__0(v_p_1048_, v___x_1049_, v___x_1050_, v_a_1051_, v_b_1052_, v_acc_1053_);
lean_dec_ref(v_acc_1053_);
return v_res_1054_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any___redArg(lean_object* v_m_1055_, lean_object* v_p_1056_){
_start:
{
lean_object* v___x_1057_; lean_object* v_buckets_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___f_1061_; lean_object* v___f_1062_; size_t v_sz_1063_; size_t v___x_1064_; lean_object* v___x_1065_; lean_object* v_fst_1066_; 
v___x_1057_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1058_ = lean_ctor_get(v_m_1055_, 1);
lean_inc_ref(v_buckets_1058_);
lean_dec_ref(v_m_1055_);
v___x_1059_ = lean_box(0);
v___x_1060_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1061_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1061_, 0, v_p_1056_);
lean_closure_set(v___f_1061_, 1, v___x_1060_);
lean_closure_set(v___f_1061_, 2, v___x_1059_);
v___f_1062_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1062_, 0, v___x_1057_);
lean_closure_set(v___f_1062_, 1, v___f_1061_);
v_sz_1063_ = lean_array_size(v_buckets_1058_);
v___x_1064_ = ((size_t)0ULL);
v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1057_, v_buckets_1058_, v___f_1062_, v_sz_1063_, v___x_1064_, v___x_1060_);
v_fst_1066_ = lean_ctor_get(v___x_1065_, 0);
lean_inc(v_fst_1066_);
lean_dec(v___x_1065_);
if (lean_obj_tag(v_fst_1066_) == 0)
{
uint8_t v___x_1067_; 
v___x_1067_ = 0;
return v___x_1067_;
}
else
{
lean_object* v_val_1068_; uint8_t v___x_1069_; 
v_val_1068_ = lean_ctor_get(v_fst_1066_, 0);
lean_inc(v_val_1068_);
lean_dec_ref_known(v_fst_1066_, 1);
v___x_1069_ = lean_unbox(v_val_1068_);
lean_dec(v_val_1068_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___boxed(lean_object* v_m_1070_, lean_object* v_p_1071_){
_start:
{
uint8_t v_res_1072_; lean_object* v_r_1073_; 
v_res_1072_ = l_Std_HashSet_any___redArg(v_m_1070_, v_p_1071_);
v_r_1073_ = lean_box(v_res_1072_);
return v_r_1073_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any(lean_object* v_00_u03b1_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_m_1077_, lean_object* v_p_1078_){
_start:
{
lean_object* v___x_1079_; lean_object* v_buckets_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___f_1083_; lean_object* v___f_1084_; size_t v_sz_1085_; size_t v___x_1086_; lean_object* v___x_1087_; lean_object* v_fst_1088_; 
v___x_1079_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1080_ = lean_ctor_get(v_m_1077_, 1);
lean_inc_ref(v_buckets_1080_);
lean_dec_ref(v_m_1077_);
v___x_1081_ = lean_box(0);
v___x_1082_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1083_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1083_, 0, v_p_1078_);
lean_closure_set(v___f_1083_, 1, v___x_1082_);
lean_closure_set(v___f_1083_, 2, v___x_1081_);
v___f_1084_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1084_, 0, v___x_1079_);
lean_closure_set(v___f_1084_, 1, v___f_1083_);
v_sz_1085_ = lean_array_size(v_buckets_1080_);
v___x_1086_ = ((size_t)0ULL);
v___x_1087_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1079_, v_buckets_1080_, v___f_1084_, v_sz_1085_, v___x_1086_, v___x_1082_);
v_fst_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_fst_1088_);
lean_dec(v___x_1087_);
if (lean_obj_tag(v_fst_1088_) == 0)
{
uint8_t v___x_1089_; 
v___x_1089_ = 0;
return v___x_1089_;
}
else
{
lean_object* v_val_1090_; uint8_t v___x_1091_; 
v_val_1090_ = lean_ctor_get(v_fst_1088_, 0);
lean_inc(v_val_1090_);
lean_dec_ref_known(v_fst_1088_, 1);
v___x_1091_ = lean_unbox(v_val_1090_);
lean_dec(v_val_1090_);
return v___x_1091_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_x_1093_, lean_object* v_x_1094_, lean_object* v_m_1095_, lean_object* v_p_1096_){
_start:
{
uint8_t v_res_1097_; lean_object* v_r_1098_; 
v_res_1097_ = l_Std_HashSet_any(v_00_u03b1_1092_, v_x_1093_, v_x_1094_, v_m_1095_, v_p_1096_);
lean_dec_ref(v_x_1094_);
lean_dec_ref(v_x_1093_);
v_r_1098_ = lean_box(v_res_1097_);
return v_r_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0(lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_a_1101_, lean_object* v_b_1102_, lean_object* v_acc_1103_){
_start:
{
lean_object* v_r_1104_; lean_object* v___x_1105_; 
v_r_1104_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1099_, v_inst_1100_, v_acc_1103_, v_a_1101_, v_b_1102_);
v___x_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1105_, 0, v_r_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__1(lean_object* v___x_1106_, lean_object* v___f_1107_, lean_object* v_a_1108_, lean_object* v_x_1109_, lean_object* v___y_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1106_, v___f_1107_, v_a_1108_, v___y_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg(lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_m_u2081_1116_, lean_object* v_m_u2082_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v_size_1119_; lean_object* v_buckets_1120_; lean_object* v_size_1121_; uint8_t v___x_1122_; 
v___x_1118_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_size_1119_ = lean_ctor_get(v_m_u2081_1116_, 0);
v_buckets_1120_ = lean_ctor_get(v_m_u2081_1116_, 1);
v_size_1121_ = lean_ctor_get(v_m_u2082_1117_, 0);
v___x_1122_ = lean_nat_dec_le(v_size_1119_, v_size_1121_);
if (v___x_1122_ == 0)
{
lean_object* v___f_1123_; lean_object* v___x_1124_; 
v___f_1123_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1124_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1123_, v_inst_1114_, v_inst_1115_, v_m_u2081_1116_, v_m_u2082_1117_);
return v___x_1124_;
}
else
{
lean_object* v___f_1125_; lean_object* v___f_1126_; size_t v_sz_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
lean_inc_ref(v_buckets_1120_);
lean_dec_ref(v_m_u2081_1116_);
v___f_1125_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1125_, 0, v_inst_1114_);
lean_closure_set(v___f_1125_, 1, v_inst_1115_);
v___f_1126_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1126_, 0, v___x_1118_);
lean_closure_set(v___f_1126_, 1, v___f_1125_);
v_sz_1127_ = lean_array_size(v_buckets_1120_);
v___x_1128_ = ((size_t)0ULL);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1118_, v_buckets_1120_, v___f_1126_, v_sz_1127_, v___x_1128_, v_m_u2082_1117_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union(lean_object* v_00_u03b1_1130_, lean_object* v_inst_1131_, lean_object* v_inst_1132_, lean_object* v_m_u2081_1133_, lean_object* v_m_u2082_1134_){
_start:
{
lean_object* v___x_1135_; lean_object* v_size_1136_; lean_object* v_buckets_1137_; lean_object* v_size_1138_; uint8_t v___x_1139_; 
v___x_1135_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_size_1136_ = lean_ctor_get(v_m_u2081_1133_, 0);
v_buckets_1137_ = lean_ctor_get(v_m_u2081_1133_, 1);
v_size_1138_ = lean_ctor_get(v_m_u2082_1134_, 0);
v___x_1139_ = lean_nat_dec_le(v_size_1136_, v_size_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___f_1140_; lean_object* v___x_1141_; 
v___f_1140_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1141_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1140_, v_inst_1131_, v_inst_1132_, v_m_u2081_1133_, v_m_u2082_1134_);
return v___x_1141_;
}
else
{
lean_object* v___f_1142_; lean_object* v___f_1143_; size_t v_sz_1144_; size_t v___x_1145_; lean_object* v___x_1146_; 
lean_inc_ref(v_buckets_1137_);
lean_dec_ref(v_m_u2081_1133_);
v___f_1142_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1142_, 0, v_inst_1131_);
lean_closure_set(v___f_1142_, 1, v_inst_1132_);
v___f_1143_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1143_, 0, v___x_1135_);
lean_closure_set(v___f_1143_, 1, v___f_1142_);
v_sz_1144_ = lean_array_size(v_buckets_1137_);
v___x_1145_ = ((size_t)0ULL);
v___x_1146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1135_, v_buckets_1137_, v___f_1143_, v_sz_1144_, v___x_1145_, v_m_u2082_1134_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion___redArg(lean_object* v_inst_1147_, lean_object* v_inst_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1149_, 0, lean_box(0));
lean_closure_set(v___x_1149_, 1, v_inst_1147_);
lean_closure_set(v___x_1149_, 2, v_inst_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion(lean_object* v_00_u03b1_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1153_, 0, lean_box(0));
lean_closure_set(v___x_1153_, 1, v_inst_1151_);
lean_closure_set(v___x_1153_, 2, v_inst_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter___redArg(lean_object* v_inst_1154_, lean_object* v_inst_1155_, lean_object* v_m_u2081_1156_, lean_object* v_m_u2082_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1154_, v_inst_1155_, v_m_u2081_1156_, v_m_u2082_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter(lean_object* v_00_u03b1_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_m_u2081_1162_, lean_object* v_m_u2082_1163_){
_start:
{
lean_object* v___x_1164_; 
v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1160_, v_inst_1161_, v_m_u2081_1162_, v_m_u2082_1163_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter___redArg(lean_object* v_inst_1165_, lean_object* v_inst_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1167_, 0, lean_box(0));
lean_closure_set(v___x_1167_, 1, v_inst_1165_);
lean_closure_set(v___x_1167_, 2, v_inst_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter(lean_object* v_00_u03b1_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1171_, 0, lean_box(0));
lean_closure_set(v___x_1171_, 1, v_inst_1169_);
lean_closure_set(v___x_1171_, 2, v_inst_1170_);
return v___x_1171_;
}
}
static lean_object* _init_l_Std_HashSet_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___f_1173_; 
v___x_1172_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1173_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1173_, 0, v___x_1172_);
return v___f_1173_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq___redArg(lean_object* v_x_1174_, lean_object* v_inst_1175_, lean_object* v_m_u2081_1176_, lean_object* v_m_u2082_1177_){
_start:
{
lean_object* v___f_1178_; uint8_t v___x_1179_; 
v___f_1178_ = lean_obj_once(&l_Std_HashSet_beq___redArg___closed__0, &l_Std_HashSet_beq___redArg___closed__0_once, _init_l_Std_HashSet_beq___redArg___closed__0);
v___x_1179_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1175_, v_x_1174_, v___f_1178_, v_m_u2081_1176_, v_m_u2082_1177_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___redArg___boxed(lean_object* v_x_1180_, lean_object* v_inst_1181_, lean_object* v_m_u2081_1182_, lean_object* v_m_u2082_1183_){
_start:
{
uint8_t v_res_1184_; lean_object* v_r_1185_; 
v_res_1184_ = l_Std_HashSet_beq___redArg(v_x_1180_, v_inst_1181_, v_m_u2081_1182_, v_m_u2082_1183_);
v_r_1185_ = lean_box(v_res_1184_);
return v_r_1185_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq(lean_object* v_00_u03b1_1186_, lean_object* v_x_1187_, lean_object* v_inst_1188_, lean_object* v_m_u2081_1189_, lean_object* v_m_u2082_1190_){
_start:
{
uint8_t v___x_1191_; 
v___x_1191_ = l_Std_HashSet_beq___redArg(v_x_1187_, v_inst_1188_, v_m_u2081_1189_, v_m_u2082_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_x_1193_, lean_object* v_inst_1194_, lean_object* v_m_u2081_1195_, lean_object* v_m_u2082_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l_Std_HashSet_beq(v_00_u03b1_1192_, v_x_1193_, v_inst_1194_, v_m_u2081_1195_, v_m_u2082_1196_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq___redArg(lean_object* v_x_1199_, lean_object* v_inst_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1201_, 0, lean_box(0));
lean_closure_set(v___x_1201_, 1, v_x_1199_);
lean_closure_set(v___x_1201_, 2, v_inst_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq(lean_object* v_00_u03b1_1202_, lean_object* v_x_1203_, lean_object* v_inst_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1205_, 0, lean_box(0));
lean_closure_set(v___x_1205_, 1, v_x_1203_);
lean_closure_set(v___x_1205_, 2, v_inst_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_diff___redArg___lam__0(lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_m_u2082_1208_, uint8_t v___x_1209_, lean_object* v_k_1210_, lean_object* v_x_1211_){
_start:
{
uint8_t v___x_1212_; 
v___x_1212_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1206_, v_inst_1207_, v_m_u2082_1208_, v_k_1210_);
if (v___x_1212_ == 0)
{
return v___x_1209_;
}
else
{
uint8_t v___x_1213_; 
v___x_1213_ = 0;
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg___lam__0___boxed(lean_object* v_inst_1214_, lean_object* v_inst_1215_, lean_object* v_m_u2082_1216_, lean_object* v___x_1217_, lean_object* v_k_1218_, lean_object* v_x_1219_){
_start:
{
uint8_t v___x_84__boxed_1220_; uint8_t v_res_1221_; lean_object* v_r_1222_; 
v___x_84__boxed_1220_ = lean_unbox(v___x_1217_);
v_res_1221_ = l_Std_HashSet_diff___redArg___lam__0(v_inst_1214_, v_inst_1215_, v_m_u2082_1216_, v___x_84__boxed_1220_, v_k_1218_, v_x_1219_);
lean_dec_ref(v_m_u2082_1216_);
v_r_1222_ = lean_box(v_res_1221_);
return v_r_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg(lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_m_u2081_1225_, lean_object* v_m_u2082_1226_){
_start:
{
lean_object* v_size_1227_; lean_object* v_size_1228_; uint8_t v___x_1229_; 
v_size_1227_ = lean_ctor_get(v_m_u2081_1225_, 0);
v_size_1228_ = lean_ctor_get(v_m_u2082_1226_, 0);
v___x_1229_ = lean_nat_dec_le(v_size_1227_, v_size_1228_);
if (v___x_1229_ == 0)
{
lean_object* v___f_1230_; lean_object* v___x_1231_; 
v___f_1230_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1231_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1230_, v_inst_1223_, v_inst_1224_, v_m_u2081_1225_, v_m_u2082_1226_);
return v___x_1231_;
}
else
{
lean_object* v___x_1232_; lean_object* v___f_1233_; lean_object* v___x_1234_; 
v___x_1232_ = lean_box(v___x_1229_);
v___f_1233_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1233_, 0, v_inst_1223_);
lean_closure_set(v___f_1233_, 1, v_inst_1224_);
lean_closure_set(v___f_1233_, 2, v_m_u2082_1226_);
lean_closure_set(v___f_1233_, 3, v___x_1232_);
v___x_1234_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1233_, v_m_u2081_1225_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff(lean_object* v_00_u03b1_1235_, lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_m_u2081_1238_, lean_object* v_m_u2082_1239_){
_start:
{
lean_object* v_size_1240_; lean_object* v_size_1241_; uint8_t v___x_1242_; 
v_size_1240_ = lean_ctor_get(v_m_u2081_1238_, 0);
v_size_1241_ = lean_ctor_get(v_m_u2082_1239_, 0);
v___x_1242_ = lean_nat_dec_le(v_size_1240_, v_size_1241_);
if (v___x_1242_ == 0)
{
lean_object* v___f_1243_; lean_object* v___x_1244_; 
v___f_1243_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1244_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1243_, v_inst_1236_, v_inst_1237_, v_m_u2081_1238_, v_m_u2082_1239_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; lean_object* v___f_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_box(v___x_1242_);
v___f_1246_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1246_, 0, v_inst_1236_);
lean_closure_set(v___f_1246_, 1, v_inst_1237_);
lean_closure_set(v___f_1246_, 2, v_m_u2082_1239_);
lean_closure_set(v___f_1246_, 3, v___x_1245_);
v___x_1247_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1246_, v_m_u2081_1238_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff___redArg(lean_object* v_inst_1248_, lean_object* v_inst_1249_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1250_, 0, lean_box(0));
lean_closure_set(v___x_1250_, 1, v_inst_1248_);
lean_closure_set(v___x_1250_, 2, v_inst_1249_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff(lean_object* v_00_u03b1_1251_, lean_object* v_inst_1252_, lean_object* v_inst_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1254_, 0, lean_box(0));
lean_closure_set(v___x_1254_, 1, v_inst_1252_);
lean_closure_set(v___x_1254_, 2, v_inst_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__0(lean_object* v_f_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x1_1258_, lean_object* v_x2_1259_, lean_object* v_x3_1260_){
_start:
{
lean_object* v_fst_1261_; lean_object* v_snd_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1276_; 
v_fst_1261_ = lean_ctor_get(v_x1_1258_, 0);
v_snd_1262_ = lean_ctor_get(v_x1_1258_, 1);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_x1_1258_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1264_ = v_x1_1258_;
v_isShared_1265_ = v_isSharedCheck_1276_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_snd_1262_);
lean_inc(v_fst_1261_);
lean_dec(v_x1_1258_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1276_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1266_; uint8_t v___x_1267_; 
lean_inc(v_x2_1259_);
v___x_1266_ = lean_apply_1(v_f_1255_, v_x2_1259_);
v___x_1267_ = lean_unbox(v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
v___x_1268_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1256_, v_x_1257_, v_snd_1262_, v_x2_1259_, v_x3_1260_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 1, v___x_1268_);
v___x_1270_ = v___x_1264_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_fst_1261_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1268_);
v___x_1270_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
return v___x_1270_;
}
}
else
{
lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1272_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1256_, v_x_1257_, v_fst_1261_, v_x2_1259_, v_x3_1260_);
if (v_isShared_1265_ == 0)
{
lean_ctor_set(v___x_1264_, 0, v___x_1272_);
v___x_1274_ = v___x_1264_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v_snd_1262_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__1(lean_object* v___x_1277_, lean_object* v___f_1278_, lean_object* v_acc_1279_, lean_object* v_l_1280_){
_start:
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1277_, v___f_1278_, v_acc_1279_, v_l_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l_Std_HashSet_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_1283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1283_, 0, v___x_1282_);
lean_ctor_set(v___x_1283_, 1, v___x_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg(lean_object* v_x_1284_, lean_object* v_x_1285_, lean_object* v_f_1286_, lean_object* v_m_1287_){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v_buckets_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1288_ = lean_unsigned_to_nat(0u);
v___x_1289_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1290_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1291_ = lean_ctor_get(v_m_1287_, 1);
lean_inc_ref(v_buckets_1291_);
lean_dec_ref(v_m_1287_);
v___x_1292_ = lean_array_get_size(v_buckets_1291_);
v___x_1293_ = lean_nat_dec_lt(v___x_1288_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_dec_ref(v_buckets_1291_);
lean_dec_ref(v_f_1286_);
lean_dec_ref(v_x_1285_);
lean_dec_ref(v_x_1284_);
return v___x_1289_;
}
else
{
lean_object* v___f_1294_; lean_object* v___f_1295_; size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; lean_object* v_fst_1299_; lean_object* v_snd_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
v___f_1294_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1294_, 0, v_f_1286_);
lean_closure_set(v___f_1294_, 1, v_x_1284_);
lean_closure_set(v___f_1294_, 2, v_x_1285_);
v___f_1295_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1295_, 0, v___x_1290_);
lean_closure_set(v___f_1295_, 1, v___f_1294_);
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = lean_usize_of_nat(v___x_1292_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1290_, v___f_1295_, v_buckets_1291_, v___x_1296_, v___x_1297_, v___x_1289_);
v_fst_1299_ = lean_ctor_get(v___x_1298_, 0);
v_snd_1300_ = lean_ctor_get(v___x_1298_, 1);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1298_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_snd_1300_);
lean_inc(v_fst_1299_);
lean_dec(v___x_1298_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_fst_1299_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v_snd_1300_);
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
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition(lean_object* v_00_u03b1_1308_, lean_object* v_x_1309_, lean_object* v_x_1310_, lean_object* v_f_1311_, lean_object* v_m_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v_buckets_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1315_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1316_ = lean_ctor_get(v_m_1312_, 1);
lean_inc_ref(v_buckets_1316_);
lean_dec_ref(v_m_1312_);
v___x_1317_ = lean_array_get_size(v_buckets_1316_);
v___x_1318_ = lean_nat_dec_lt(v___x_1313_, v___x_1317_);
if (v___x_1318_ == 0)
{
lean_dec_ref(v_buckets_1316_);
lean_dec_ref(v_f_1311_);
lean_dec_ref(v_x_1310_);
lean_dec_ref(v_x_1309_);
return v___x_1314_;
}
else
{
lean_object* v___f_1319_; lean_object* v___f_1320_; size_t v___x_1321_; size_t v___x_1322_; lean_object* v___x_1323_; lean_object* v_fst_1324_; lean_object* v_snd_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v___f_1319_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1319_, 0, v_f_1311_);
lean_closure_set(v___f_1319_, 1, v_x_1309_);
lean_closure_set(v___f_1319_, 2, v_x_1310_);
v___f_1320_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1320_, 0, v___x_1315_);
lean_closure_set(v___f_1320_, 1, v___f_1319_);
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = lean_usize_of_nat(v___x_1317_);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1315_, v___f_1320_, v_buckets_1316_, v___x_1321_, v___x_1322_, v___x_1314_);
v_fst_1324_ = lean_ctor_get(v___x_1323_, 0);
v_snd_1325_ = lean_ctor_get(v___x_1323_, 1);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1323_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_snd_1325_);
lean_inc(v_fst_1324_);
lean_dec(v___x_1323_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_fst_1324_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v_snd_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray___redArg(lean_object* v_inst_1337_, lean_object* v_inst_1338_, lean_object* v_l_1339_){
_start:
{
lean_object* v___f_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___f_1340_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1341_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_1342_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1340_, v_inst_1337_, v_inst_1338_, v___x_1341_, v_l_1339_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray(lean_object* v_00_u03b1_1343_, lean_object* v_inst_1344_, lean_object* v_inst_1345_, lean_object* v_l_1346_){
_start:
{
lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; 
v___f_1347_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1348_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_1349_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1347_, v_inst_1344_, v_inst_1345_, v___x_1348_, v_l_1346_);
return v___x_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg(lean_object* v_m_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg___boxed(lean_object* v_m_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Std_HashSet_Internal_numBuckets___redArg(v_m_1352_);
lean_dec_ref(v_m_1352_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets(lean_object* v_00_u03b1_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_, lean_object* v_m_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1359_, lean_object* v_x_1360_, lean_object* v_x_1361_, lean_object* v_m_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_Std_HashSet_Internal_numBuckets(v_00_u03b1_1359_, v_x_1360_, v_x_1361_, v_m_1362_);
lean_dec_ref(v_m_1362_);
lean_dec_ref(v_x_1361_);
lean_dec_ref(v_x_1360_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2(lean_object* v_inst_1367_, lean_object* v___f_1368_, lean_object* v_m_1369_, lean_object* v_prec_1370_){
_start:
{
lean_object* v___x_1371_; lean_object* v_buckets_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1392_; 
v___x_1371_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1372_ = lean_ctor_get(v_m_1369_, 1);
v_isSharedCheck_1392_ = !lean_is_exclusive(v_m_1369_);
if (v_isSharedCheck_1392_ == 0)
{
lean_object* v_unused_1393_; 
v_unused_1393_ = lean_ctor_get(v_m_1369_, 0);
lean_dec(v_unused_1393_);
v___x_1374_ = v_m_1369_;
v_isShared_1375_ = v_isSharedCheck_1392_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_buckets_1372_);
lean_dec(v_m_1369_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1392_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1376_; lean_object* v___y_1378_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v___x_1386_; uint8_t v___x_1387_; 
v___x_1376_ = ((lean_object*)(l_Std_HashSet_instRepr___redArg___lam__2___closed__1));
v___x_1384_ = lean_box(0);
v___x_1385_ = lean_array_get_size(v_buckets_1372_);
v___x_1386_ = lean_unsigned_to_nat(0u);
v___x_1387_ = lean_nat_dec_lt(v___x_1386_, v___x_1385_);
if (v___x_1387_ == 0)
{
lean_dec_ref(v_buckets_1372_);
lean_dec_ref(v___f_1368_);
v___y_1378_ = v___x_1384_;
goto v___jp_1377_;
}
else
{
lean_object* v___f_1388_; size_t v___x_1389_; size_t v___x_1390_; lean_object* v___x_1391_; 
v___f_1388_ = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1388_, 0, v___x_1371_);
lean_closure_set(v___f_1388_, 1, v___f_1368_);
v___x_1389_ = lean_usize_of_nat(v___x_1385_);
v___x_1390_ = ((size_t)0ULL);
v___x_1391_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1371_, v___f_1388_, v_buckets_1372_, v___x_1389_, v___x_1390_, v___x_1384_);
v___y_1378_ = v___x_1391_;
goto v___jp_1377_;
}
v___jp_1377_:
{
lean_object* v___x_1379_; lean_object* v___x_1381_; 
v___x_1379_ = l_List_repr___redArg(v_inst_1367_, v___y_1378_);
if (v_isShared_1375_ == 0)
{
lean_ctor_set_tag(v___x_1374_, 5);
lean_ctor_set(v___x_1374_, 1, v___x_1379_);
lean_ctor_set(v___x_1374_, 0, v___x_1376_);
v___x_1381_ = v___x_1374_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v___x_1376_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Repr_addAppParen(v___x_1381_, v_prec_1370_);
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1394_, lean_object* v___f_1395_, lean_object* v_m_1396_, lean_object* v_prec_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Std_HashSet_instRepr___redArg___lam__2(v_inst_1394_, v___f_1395_, v_m_1396_, v_prec_1397_);
lean_dec(v_prec_1397_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg(lean_object* v_inst_1399_){
_start:
{
lean_object* v___f_1400_; lean_object* v___f_1401_; 
v___f_1400_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___f_1401_ = lean_alloc_closure((void*)(l_Std_HashSet_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1401_, 0, v_inst_1399_);
lean_closure_set(v___f_1401_, 1, v___f_1400_);
return v___f_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr(lean_object* v_00_u03b1_1402_, lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_inst_1405_){
_start:
{
lean_object* v___x_1406_; 
v___x_1406_ = l_Std_HashSet_instRepr___redArg(v_inst_1405_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___boxed(lean_object* v_00_u03b1_1407_, lean_object* v_inst_1408_, lean_object* v_inst_1409_, lean_object* v_inst_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Std_HashSet_instRepr(v_00_u03b1_1407_, v_inst_1408_, v_inst_1409_, v_inst_1410_);
lean_dec_ref(v_inst_1409_);
lean_dec_ref(v_inst_1408_);
return v_res_1411_;
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
