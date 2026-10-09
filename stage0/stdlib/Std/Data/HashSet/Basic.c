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
lean_object* l_Std_HashSet_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
return v___x_38_;
}
}
LEAN_EXPORT void l_Std_HashSet_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_39_;
v_res_39_ = l_Std_HashSet_instEmptyCollection___redArg();
stack->m_obj
 = v_res_39_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___redArg___boxed(lean_object* v___dummy_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Std_HashSet_instEmptyCollection___redArg();
return v_res_41_;
}
}
static lean_object* _init_l_Std_HashSet_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Std_HashSet_instEmptyCollection___redArg();
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__0, &l_Std_HashSet_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_instEmptyCollection___closed__0);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_HashSet_instEmptyCollection(v_00_u03b1_47_, v_inst_48_, v_inst_49_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_inst_48_);
return v_res_50_;
}
}
lean_object* l_Std_HashSet_instInhabited___redArg(){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
return v___x_52_;
}
}
LEAN_EXPORT void l_Std_HashSet_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_53_;
v_res_53_ = l_Std_HashSet_instInhabited___redArg();
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___redArg___boxed(lean_object* v___dummy_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_HashSet_instInhabited___redArg();
return v_res_55_;
}
}
static lean_object* _init_l_Std_HashSet_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Std_HashSet_instInhabited___redArg();
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited(lean_object* v_00_u03b1_57_, lean_object* v_inst_58_, lean_object* v_inst_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lean_obj_once(&l_Std_HashSet_instInhabited___closed__0, &l_Std_HashSet_instInhabited___closed__0_once, _init_l_Std_HashSet_instInhabited___closed__0);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___boxed(lean_object* v_00_u03b1_61_, lean_object* v_inst_62_, lean_object* v_inst_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_HashSet_instInhabited(v_00_u03b1_61_, v_inst_62_, v_inst_63_);
lean_dec_ref(v_inst_63_);
lean_dec_ref(v_inst_62_);
return v_res_64_;
}
}
static lean_object* _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5));
v___x_104_ = l_String_toRawSubstring_x27(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(lean_object* v_x_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__3));
lean_inc(v_x_125_);
v___x_129_ = l_Lean_Syntax_isOfKind(v_x_125_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_x_125_);
v___x_130_ = lean_box(1);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_127_);
return v___x_131_;
}
else
{
lean_object* v_quotContext_132_; lean_object* v_currMacroScope_133_; lean_object* v_ref_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_quotContext_132_ = lean_ctor_get(v_a_126_, 1);
v_currMacroScope_133_ = lean_ctor_get(v_a_126_, 2);
v_ref_134_ = lean_ctor_get(v_a_126_, 5);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = l_Lean_Syntax_getArg(v_x_125_, v___x_135_);
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = l_Lean_Syntax_getArg(v_x_125_, v___x_137_);
lean_dec(v_x_125_);
v___x_139_ = 0;
v___x_140_ = l_Lean_SourceInfo_fromRef(v_ref_134_, v___x_139_);
v___x_141_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4));
v___x_142_ = lean_obj_once(&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6, &l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6_once, _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6);
v___x_143_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_133_);
lean_inc(v_quotContext_132_);
v___x_144_ = l_Lean_addMacroScope(v_quotContext_132_, v___x_143_, v_currMacroScope_133_);
v___x_145_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12));
lean_inc_n(v___x_140_, 2);
v___x_146_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_146_, 0, v___x_140_);
lean_ctor_set(v___x_146_, 1, v___x_142_);
lean_ctor_set(v___x_146_, 2, v___x_144_);
lean_ctor_set(v___x_146_, 3, v___x_145_);
v___x_147_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14));
v___x_148_ = l_Lean_Syntax_node2(v___x_140_, v___x_147_, v___x_136_, v___x_138_);
v___x_149_ = l_Lean_Syntax_node2(v___x_140_, v___x_141_, v___x_146_, v___x_148_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_a_127_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___boxed(lean_object* v_x_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(v_x_151_, v_a_152_, v_a_153_);
lean_dec_ref(v_a_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(lean_object* v_x_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4));
lean_inc(v_x_158_);
v___x_162_ = l_Lean_Syntax_isOfKind(v_x_158_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_x_158_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_a_160_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = l_Lean_Syntax_getArg(v_x_158_, v___x_165_);
v___x_167_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1));
lean_inc(v___x_166_);
v___x_168_ = l_Lean_Syntax_isOfKind(v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v___x_166_);
lean_dec(v_x_158_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_a_160_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = l_Lean_Syntax_getArg(v_x_158_, v___x_171_);
lean_dec(v_x_158_);
v___x_173_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_172_);
v___x_174_ = l_Lean_Syntax_matchesNull(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v___x_172_);
lean_dec(v___x_166_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_a_160_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_ref_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_177_ = l_Lean_Syntax_getArg(v___x_172_, v___x_165_);
v___x_178_ = l_Lean_Syntax_getArg(v___x_172_, v___x_171_);
lean_dec(v___x_172_);
v_ref_179_ = l_Lean_replaceRef(v___x_166_, v_a_159_);
lean_dec(v___x_166_);
v___x_180_ = 0;
v___x_181_ = l_Lean_SourceInfo_fromRef(v_ref_179_, v___x_180_);
lean_dec(v_ref_179_);
v___x_182_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__3));
v___x_183_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__6));
lean_inc(v___x_181_);
v___x_184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_181_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = l_Lean_Syntax_node3(v___x_181_, v___x_182_, v___x_177_, v___x_184_, v___x_178_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_a_160_);
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___boxed(lean_object* v_x_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(v_x_187_, v_a_188_, v_a_189_);
lean_dec(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert___redArg(lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_m_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_box(0);
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_191_, v_x_192_, v_m_193_, v_a_194_, v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert(lean_object* v_00_u03b1_197_, lean_object* v_x_198_, lean_object* v_x_199_, lean_object* v_m_200_, lean_object* v_a_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_box(0);
v___x_203_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_198_, v_x_199_, v_m_200_, v_a_201_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg___lam__0(lean_object* v_x_204_, lean_object* v_x_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_207_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_208_ = lean_box(0);
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_204_, v_x_205_, v___x_207_, v_a_206_, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg(lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
lean_object* v___f_212_; 
v___f_212_ = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(v___f_212_, 0, v_x_210_);
lean_closure_set(v___f_212_, 1, v_x_211_);
return v___f_212_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton(lean_object* v_00_u03b1_213_, lean_object* v_x_214_, lean_object* v_x_215_){
_start:
{
lean_object* v___f_216_; 
v___f_216_ = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(v___f_216_, 0, v_x_214_);
lean_closure_set(v___f_216_, 1, v_x_215_);
return v___f_216_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg___lam__0(lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_a_219_, lean_object* v_s_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_box(0);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_217_, v_x_218_, v_s_220_, v_a_219_, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg(lean_object* v_x_223_, lean_object* v_x_224_){
_start:
{
lean_object* v___f_225_; 
v___f_225_ = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(v___f_225_, 0, v_x_223_);
lean_closure_set(v___f_225_, 1, v_x_224_);
return v___f_225_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert(lean_object* v_00_u03b1_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
lean_object* v___f_229_; 
v___f_229_ = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(v___f_229_, 0, v_x_227_);
lean_closure_set(v___f_229_, 1, v_x_228_);
return v___f_229_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert___redArg(lean_object* v_x_230_, lean_object* v_x_231_, lean_object* v_m_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_size_234_; lean_object* v_buckets_235_; lean_object* v___x_236_; lean_object* v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v_fold_242_; uint64_t v___x_243_; uint64_t v___x_244_; uint64_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; size_t v___x_249_; size_t v___x_250_; lean_object* v_bkt_251_; uint8_t v___x_252_; 
v_size_234_ = lean_ctor_get(v_m_232_, 0);
v_buckets_235_ = lean_ctor_get(v_m_232_, 1);
v___x_236_ = lean_array_get_size(v_buckets_235_);
lean_inc_ref(v_x_231_);
lean_inc_n(v_a_233_, 2);
v___x_237_ = lean_apply_1(v_x_231_, v_a_233_);
v___x_238_ = 32ULL;
v___x_239_ = lean_unbox_uint64(v___x_237_);
v___x_240_ = lean_uint64_shift_right(v___x_239_, v___x_238_);
v___x_241_ = lean_unbox_uint64(v___x_237_);
lean_dec_ref(v___x_237_);
v_fold_242_ = lean_uint64_xor(v___x_241_, v___x_240_);
v___x_243_ = 16ULL;
v___x_244_ = lean_uint64_shift_right(v_fold_242_, v___x_243_);
v___x_245_ = lean_uint64_xor(v_fold_242_, v___x_244_);
v___x_246_ = lean_uint64_to_usize(v___x_245_);
v___x_247_ = lean_usize_of_nat(v___x_236_);
v___x_248_ = ((size_t)1ULL);
v___x_249_ = lean_usize_sub(v___x_247_, v___x_248_);
v___x_250_ = lean_usize_land(v___x_246_, v___x_249_);
v_bkt_251_ = lean_array_uget_borrowed(v_buckets_235_, v___x_250_);
lean_inc(v_bkt_251_);
v___x_252_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_230_, v_a_233_, v_bkt_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_278_; 
lean_inc_ref(v_buckets_235_);
lean_inc(v_size_234_);
v_isSharedCheck_278_ = !lean_is_exclusive(v_m_232_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; lean_object* v_unused_280_; 
v_unused_279_ = lean_ctor_get(v_m_232_, 1);
lean_dec(v_unused_279_);
v_unused_280_ = lean_ctor_get(v_m_232_, 0);
lean_dec(v_unused_280_);
v___x_254_ = v_m_232_;
v_isShared_255_ = v_isSharedCheck_278_;
goto v_resetjp_253_;
}
else
{
lean_dec(v_m_232_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_278_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v_size_x27_258_; lean_object* v___x_259_; lean_object* v_buckets_x27_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_256_ = lean_box(0);
v___x_257_ = lean_unsigned_to_nat(1u);
v_size_x27_258_ = lean_nat_add(v_size_234_, v___x_257_);
lean_dec(v_size_234_);
lean_inc(v_bkt_251_);
v___x_259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_259_, 0, v_a_233_);
lean_ctor_set(v___x_259_, 1, v___x_256_);
lean_ctor_set(v___x_259_, 2, v_bkt_251_);
v_buckets_x27_260_ = lean_array_uset(v_buckets_235_, v___x_250_, v___x_259_);
v___x_261_ = lean_unsigned_to_nat(4u);
v___x_262_ = lean_nat_mul(v_size_x27_258_, v___x_261_);
v___x_263_ = lean_unsigned_to_nat(3u);
v___x_264_ = lean_nat_div(v___x_262_, v___x_263_);
lean_dec(v___x_262_);
v___x_265_ = lean_array_get_size(v_buckets_x27_260_);
v___x_266_ = lean_nat_dec_le(v___x_264_, v___x_265_);
lean_dec(v___x_264_);
if (v___x_266_ == 0)
{
lean_object* v_val_267_; lean_object* v___x_269_; 
v_val_267_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_231_, v_buckets_x27_260_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_val_267_);
lean_ctor_set(v___x_254_, 0, v_size_x27_258_);
v___x_269_ = v___x_254_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_size_x27_258_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_val_267_);
v___x_269_ = v_reuseFailAlloc_272_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = lean_box(v___x_252_);
v___x_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_270_);
lean_ctor_set(v___x_271_, 1, v___x_269_);
return v___x_271_;
}
}
else
{
lean_object* v___x_274_; 
lean_dec_ref(v_x_231_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_buckets_x27_260_);
lean_ctor_set(v___x_254_, 0, v_size_x27_258_);
v___x_274_ = v___x_254_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v_size_x27_258_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v_buckets_x27_260_);
v___x_274_ = v_reuseFailAlloc_277_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_box(v___x_252_);
v___x_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set(v___x_276_, 1, v___x_274_);
return v___x_276_;
}
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; 
lean_dec(v_a_233_);
lean_dec_ref(v_x_231_);
v___x_281_ = lean_box(v___x_252_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v_m_232_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert(lean_object* v_00_u03b1_283_, lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_m_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_size_288_; lean_object* v_buckets_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v_fold_296_; uint64_t v___x_297_; uint64_t v___x_298_; uint64_t v___x_299_; size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; lean_object* v_bkt_305_; uint8_t v___x_306_; 
v_size_288_ = lean_ctor_get(v_m_286_, 0);
v_buckets_289_ = lean_ctor_get(v_m_286_, 1);
v___x_290_ = lean_array_get_size(v_buckets_289_);
lean_inc_ref(v_x_285_);
lean_inc_n(v_a_287_, 2);
v___x_291_ = lean_apply_1(v_x_285_, v_a_287_);
v___x_292_ = 32ULL;
v___x_293_ = lean_unbox_uint64(v___x_291_);
v___x_294_ = lean_uint64_shift_right(v___x_293_, v___x_292_);
v___x_295_ = lean_unbox_uint64(v___x_291_);
lean_dec_ref(v___x_291_);
v_fold_296_ = lean_uint64_xor(v___x_295_, v___x_294_);
v___x_297_ = 16ULL;
v___x_298_ = lean_uint64_shift_right(v_fold_296_, v___x_297_);
v___x_299_ = lean_uint64_xor(v_fold_296_, v___x_298_);
v___x_300_ = lean_uint64_to_usize(v___x_299_);
v___x_301_ = lean_usize_of_nat(v___x_290_);
v___x_302_ = ((size_t)1ULL);
v___x_303_ = lean_usize_sub(v___x_301_, v___x_302_);
v___x_304_ = lean_usize_land(v___x_300_, v___x_303_);
v_bkt_305_ = lean_array_uget_borrowed(v_buckets_289_, v___x_304_);
lean_inc(v_bkt_305_);
v___x_306_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_284_, v_a_287_, v_bkt_305_);
if (v___x_306_ == 0)
{
lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_332_; 
lean_inc_ref(v_buckets_289_);
lean_inc(v_size_288_);
v_isSharedCheck_332_ = !lean_is_exclusive(v_m_286_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; lean_object* v_unused_334_; 
v_unused_333_ = lean_ctor_get(v_m_286_, 1);
lean_dec(v_unused_333_);
v_unused_334_ = lean_ctor_get(v_m_286_, 0);
lean_dec(v_unused_334_);
v___x_308_ = v_m_286_;
v_isShared_309_ = v_isSharedCheck_332_;
goto v_resetjp_307_;
}
else
{
lean_dec(v_m_286_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_332_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v_size_x27_312_; lean_object* v___x_313_; lean_object* v_buckets_x27_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_310_ = lean_box(0);
v___x_311_ = lean_unsigned_to_nat(1u);
v_size_x27_312_ = lean_nat_add(v_size_288_, v___x_311_);
lean_dec(v_size_288_);
lean_inc(v_bkt_305_);
v___x_313_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_313_, 0, v_a_287_);
lean_ctor_set(v___x_313_, 1, v___x_310_);
lean_ctor_set(v___x_313_, 2, v_bkt_305_);
v_buckets_x27_314_ = lean_array_uset(v_buckets_289_, v___x_304_, v___x_313_);
v___x_315_ = lean_unsigned_to_nat(4u);
v___x_316_ = lean_nat_mul(v_size_x27_312_, v___x_315_);
v___x_317_ = lean_unsigned_to_nat(3u);
v___x_318_ = lean_nat_div(v___x_316_, v___x_317_);
lean_dec(v___x_316_);
v___x_319_ = lean_array_get_size(v_buckets_x27_314_);
v___x_320_ = lean_nat_dec_le(v___x_318_, v___x_319_);
lean_dec(v___x_318_);
if (v___x_320_ == 0)
{
lean_object* v_val_321_; lean_object* v___x_323_; 
v_val_321_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_285_, v_buckets_x27_314_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v_val_321_);
lean_ctor_set(v___x_308_, 0, v_size_x27_312_);
v___x_323_ = v___x_308_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_size_x27_312_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_val_321_);
v___x_323_ = v_reuseFailAlloc_326_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_box(v___x_306_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v___x_323_);
return v___x_325_;
}
}
else
{
lean_object* v___x_328_; 
lean_dec_ref(v_x_285_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 1, v_buckets_x27_314_);
lean_ctor_set(v___x_308_, 0, v_size_x27_312_);
v___x_328_ = v___x_308_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_size_x27_312_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v_buckets_x27_314_);
v___x_328_ = v_reuseFailAlloc_331_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_box(v___x_306_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
return v___x_330_;
}
}
}
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_a_287_);
lean_dec_ref(v_x_285_);
v___x_335_ = lean_box(v___x_306_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_m_286_);
return v___x_336_;
}
}
}
uint8_t l_Std_HashSet_contains___redArg(lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_m_339_, lean_object* v_a_340_){
_start:
{
uint8_t v___x_341_; 
v___x_341_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_337_, v_x_338_, v_m_339_, v_a_340_);
return v___x_341_;
}
}
LEAN_EXPORT void l_Std_HashSet_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_337_ = stack[0].m_obj;
lean_object* v_x_338_ = stack[1].m_obj;
lean_object* v_m_339_ = stack[2].m_obj;
lean_object* v_a_340_ = stack[3].m_obj;
uint8_t v_res_342_;
v_res_342_ = l_Std_HashSet_contains___redArg(v_x_337_, v_x_338_, v_m_339_, v_a_340_);
stack->m_num = v_res_342_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___redArg___boxed(lean_object* v_x_343_, lean_object* v_x_344_, lean_object* v_m_345_, lean_object* v_a_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Std_HashSet_contains___redArg(v_x_343_, v_x_344_, v_m_345_, v_a_346_);
lean_dec_ref(v_m_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
uint8_t l_Std_HashSet_contains(lean_object* v_00_u03b1_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_m_352_, lean_object* v_a_353_){
_start:
{
uint8_t v___x_354_; 
v___x_354_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_350_, v_x_351_, v_m_352_, v_a_353_);
return v___x_354_;
}
}
LEAN_EXPORT void l_Std_HashSet_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_350_ = stack[1].m_obj;
lean_object* v_x_351_ = stack[2].m_obj;
lean_object* v_m_352_ = stack[3].m_obj;
lean_object* v_a_353_ = stack[4].m_obj;
uint8_t v_res_355_;
v_res_355_ = l_Std_HashSet_contains(lean_box(0), v_x_350_, v_x_351_, v_m_352_, v_a_353_);
stack->m_num = v_res_355_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___boxed(lean_object* v_00_u03b1_356_, lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v_m_359_, lean_object* v_a_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Std_HashSet_contains(v_00_u03b1_356_, v_x_357_, v_x_358_, v_m_359_, v_a_360_);
lean_dec_ref(v_m_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
lean_object* l_Std_HashSet_instMembership___redArg(){
_start:
{
lean_object* v___x_364_; 
v___x_364_ = lean_box(0);
return v___x_364_;
}
}
LEAN_EXPORT void l_Std_HashSet_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_365_;
v_res_365_ = l_Std_HashSet_instMembership___redArg();
stack->m_obj
 = v_res_365_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___redArg___boxed(lean_object* v___dummy_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_Std_HashSet_instMembership___redArg();
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership(lean_object* v_00_u03b1_368_, lean_object* v_inst_369_, lean_object* v_inst_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___boxed(lean_object* v_00_u03b1_372_, lean_object* v_inst_373_, lean_object* v_inst_374_){
_start:
{
lean_object* v_res_375_; 
v_res_375_ = l_Std_HashSet_instMembership(v_00_u03b1_372_, v_inst_373_, v_inst_374_);
lean_dec_ref(v_inst_374_);
lean_dec_ref(v_inst_373_);
return v_res_375_;
}
}
uint8_t l_Std_HashSet_instDecidableMem___redArg(lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_m_378_, lean_object* v_a_379_){
_start:
{
uint8_t v___x_380_; 
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_376_, v_inst_377_, v_m_378_, v_a_379_);
return v___x_380_;
}
}
LEAN_EXPORT void l_Std_HashSet_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_376_ = stack[0].m_obj;
lean_object* v_inst_377_ = stack[1].m_obj;
lean_object* v_m_378_ = stack[2].m_obj;
lean_object* v_a_379_ = stack[3].m_obj;
uint8_t v_res_381_;
v_res_381_ = l_Std_HashSet_instDecidableMem___redArg(v_inst_376_, v_inst_377_, v_m_378_, v_a_379_);
stack->m_num = v_res_381_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___redArg___boxed(lean_object* v_inst_382_, lean_object* v_inst_383_, lean_object* v_m_384_, lean_object* v_a_385_){
_start:
{
uint8_t v_res_386_; lean_object* v_r_387_; 
v_res_386_ = l_Std_HashSet_instDecidableMem___redArg(v_inst_382_, v_inst_383_, v_m_384_, v_a_385_);
lean_dec_ref(v_m_384_);
v_r_387_ = lean_box(v_res_386_);
return v_r_387_;
}
}
uint8_t l_Std_HashSet_instDecidableMem(lean_object* v_00_u03b1_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_m_391_, lean_object* v_a_392_){
_start:
{
uint8_t v___x_393_; 
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_389_, v_inst_390_, v_m_391_, v_a_392_);
return v___x_393_;
}
}
LEAN_EXPORT void l_Std_HashSet_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_389_ = stack[1].m_obj;
lean_object* v_inst_390_ = stack[2].m_obj;
lean_object* v_m_391_ = stack[3].m_obj;
lean_object* v_a_392_ = stack[4].m_obj;
uint8_t v_res_394_;
v_res_394_ = l_Std_HashSet_instDecidableMem(lean_box(0), v_inst_389_, v_inst_390_, v_m_391_, v_a_392_);
stack->m_num = v_res_394_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___boxed(lean_object* v_00_u03b1_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_m_398_, lean_object* v_a_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Std_HashSet_instDecidableMem(v_00_u03b1_395_, v_inst_396_, v_inst_397_, v_m_398_, v_a_399_);
lean_dec_ref(v_m_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase___redArg(lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_m_404_, lean_object* v_a_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_402_, v_x_403_, v_m_404_, v_a_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase(lean_object* v_00_u03b1_407_, lean_object* v_x_408_, lean_object* v_x_409_, lean_object* v_m_410_, lean_object* v_a_411_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_408_, v_x_409_, v_m_410_, v_a_411_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg(lean_object* v_m_413_){
_start:
{
lean_object* v_size_414_; 
v_size_414_ = lean_ctor_get(v_m_413_, 0);
lean_inc(v_size_414_);
return v_size_414_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg___boxed(lean_object* v_m_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_HashSet_size___redArg(v_m_415_);
lean_dec_ref(v_m_415_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size(lean_object* v_00_u03b1_417_, lean_object* v_x_418_, lean_object* v_x_419_, lean_object* v_m_420_){
_start:
{
lean_object* v_size_421_; 
v_size_421_ = lean_ctor_get(v_m_420_, 0);
lean_inc(v_size_421_);
return v_size_421_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___boxed(lean_object* v_00_u03b1_422_, lean_object* v_x_423_, lean_object* v_x_424_, lean_object* v_m_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_HashSet_size(v_00_u03b1_422_, v_x_423_, v_x_424_, v_m_425_);
lean_dec_ref(v_m_425_);
lean_dec_ref(v_x_424_);
lean_dec_ref(v_x_423_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg(lean_object* v_x_427_, lean_object* v_x_428_, lean_object* v_m_429_, lean_object* v_a_430_){
_start:
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_427_, v_x_428_, v_m_429_, v_a_430_);
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg___boxed(lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_m_434_, lean_object* v_a_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_HashSet_get_x3f___redArg(v_x_432_, v_x_433_, v_m_434_, v_a_435_);
lean_dec_ref(v_m_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f(lean_object* v_00_u03b1_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_m_440_, lean_object* v_a_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_438_, v_x_439_, v_m_440_, v_a_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___boxed(lean_object* v_00_u03b1_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_m_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Std_HashSet_get_x3f(v_00_u03b1_443_, v_x_444_, v_x_445_, v_m_446_, v_a_447_);
lean_dec_ref(v_m_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg(lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_m_451_, lean_object* v_a_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_449_, v_inst_450_, v_m_451_, v_a_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg___boxed(lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_m_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_HashSet_get___redArg(v_inst_454_, v_inst_455_, v_m_456_, v_a_457_);
lean_dec_ref(v_m_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get(lean_object* v_00_u03b1_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_m_462_, lean_object* v_a_463_, lean_object* v_h_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_460_, v_inst_461_, v_m_462_, v_a_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___boxed(lean_object* v_00_u03b1_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_m_469_, lean_object* v_a_470_, lean_object* v_h_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_HashSet_get(v_00_u03b1_466_, v_inst_467_, v_inst_468_, v_m_469_, v_a_470_, v_h_471_);
lean_dec_ref(v_m_469_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg(lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_m_475_, lean_object* v_a_476_, lean_object* v_fallback_477_){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_473_, v_inst_474_, v_m_475_, v_a_476_, v_fallback_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg___boxed(lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_m_481_, lean_object* v_a_482_, lean_object* v_fallback_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_HashSet_getD___redArg(v_inst_479_, v_inst_480_, v_m_481_, v_a_482_, v_fallback_483_);
lean_dec(v_fallback_483_);
lean_dec_ref(v_m_481_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD(lean_object* v_00_u03b1_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_m_488_, lean_object* v_a_489_, lean_object* v_fallback_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_486_, v_inst_487_, v_m_488_, v_a_489_, v_fallback_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___boxed(lean_object* v_00_u03b1_492_, lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_m_495_, lean_object* v_a_496_, lean_object* v_fallback_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_HashSet_getD(v_00_u03b1_492_, v_inst_493_, v_inst_494_, v_m_495_, v_a_496_, v_fallback_497_);
lean_dec(v_fallback_497_);
lean_dec_ref(v_m_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg(lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_m_502_, lean_object* v_a_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_499_, v_inst_500_, v_inst_501_, v_m_502_, v_a_503_);
return v___x_504_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg___boxed(lean_object* v_inst_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_m_508_, lean_object* v_a_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Std_HashSet_get_x21___redArg(v_inst_505_, v_inst_506_, v_inst_507_, v_m_508_, v_a_509_);
lean_dec_ref(v_m_508_);
lean_dec(v_inst_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21(lean_object* v_00_u03b1_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_inst_514_, lean_object* v_m_515_, lean_object* v_a_516_){
_start:
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_512_, v_inst_513_, v_inst_514_, v_m_515_, v_a_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___boxed(lean_object* v_00_u03b1_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_m_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_HashSet_get_x21(v_00_u03b1_518_, v_inst_519_, v_inst_520_, v_inst_521_, v_m_522_, v_a_523_);
lean_dec_ref(v_m_522_);
lean_dec(v_inst_521_);
return v_res_524_;
}
}
uint8_t l_Std_HashSet_isEmpty___redArg(lean_object* v_m_525_){
_start:
{
lean_object* v_size_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_size_526_ = lean_ctor_get(v_m_525_, 0);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_nat_dec_eq(v_size_526_, v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT void l_Std_HashSet_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_525_ = stack[0].m_obj;
uint8_t v_res_529_;
v_res_529_ = l_Std_HashSet_isEmpty___redArg(v_m_525_);
stack->m_num = v_res_529_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___redArg___boxed(lean_object* v_m_530_){
_start:
{
uint8_t v_res_531_; lean_object* v_r_532_; 
v_res_531_ = l_Std_HashSet_isEmpty___redArg(v_m_530_);
lean_dec_ref(v_m_530_);
v_r_532_ = lean_box(v_res_531_);
return v_r_532_;
}
}
uint8_t l_Std_HashSet_isEmpty(lean_object* v_00_u03b1_533_, lean_object* v_x_534_, lean_object* v_x_535_, lean_object* v_m_536_){
_start:
{
lean_object* v_size_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_size_537_ = lean_ctor_get(v_m_536_, 0);
v___x_538_ = lean_unsigned_to_nat(0u);
v___x_539_ = lean_nat_dec_eq(v_size_537_, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT void l_Std_HashSet_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_534_ = stack[1].m_obj;
lean_object* v_x_535_ = stack[2].m_obj;
lean_object* v_m_536_ = stack[3].m_obj;
uint8_t v_res_540_;
v_res_540_ = l_Std_HashSet_isEmpty(lean_box(0), v_x_534_, v_x_535_, v_m_536_);
stack->m_num = v_res_540_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___boxed(lean_object* v_00_u03b1_541_, lean_object* v_x_542_, lean_object* v_x_543_, lean_object* v_m_544_){
_start:
{
uint8_t v_res_545_; lean_object* v_r_546_; 
v_res_545_ = l_Std_HashSet_isEmpty(v_00_u03b1_541_, v_x_542_, v_x_543_, v_m_544_);
lean_dec_ref(v_m_544_);
lean_dec_ref(v_x_543_);
lean_dec_ref(v_x_542_);
v_r_546_ = lean_box(v_res_545_);
return v_r_546_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0(lean_object* v_a_547_, lean_object* v_b_548_, lean_object* v_d_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_550_, 0, v_a_547_);
lean_ctor_set(v___x_550_, 1, v_d_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__1(lean_object* v___x_551_, lean_object* v___f_552_, lean_object* v_l_553_, lean_object* v_acc_554_){
_start:
{
lean_object* v___x_555_; 
v___x_555_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_551_, v___f_552_, v_acc_554_, v_l_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg(lean_object* v_m_579_){
_start:
{
lean_object* v___x_580_; lean_object* v_buckets_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; uint8_t v___x_585_; 
v___x_580_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_581_ = lean_ctor_get(v_m_579_, 1);
lean_inc_ref(v_buckets_581_);
lean_dec_ref(v_m_579_);
v___x_582_ = lean_box(0);
v___x_583_ = lean_array_get_size(v_buckets_581_);
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = lean_nat_dec_lt(v___x_584_, v___x_583_);
if (v___x_585_ == 0)
{
lean_dec_ref(v_buckets_581_);
return v___x_582_;
}
else
{
lean_object* v___f_586_; size_t v___x_587_; size_t v___x_588_; lean_object* v___x_589_; 
v___f_586_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__11));
v___x_587_ = lean_usize_of_nat(v___x_583_);
v___x_588_ = ((size_t)0ULL);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_580_, v___f_586_, v_buckets_581_, v___x_587_, v___x_588_, v___x_582_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList(lean_object* v_00_u03b1_590_, lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_m_593_){
_start:
{
lean_object* v___x_594_; lean_object* v_buckets_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_594_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_595_ = lean_ctor_get(v_m_593_, 1);
lean_inc_ref(v_buckets_595_);
lean_dec_ref(v_m_593_);
v___x_596_ = lean_box(0);
v___x_597_ = lean_array_get_size(v_buckets_595_);
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = lean_nat_dec_lt(v___x_598_, v___x_597_);
if (v___x_599_ == 0)
{
lean_dec_ref(v_buckets_595_);
return v___x_596_;
}
else
{
lean_object* v___f_600_; size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; 
v___f_600_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__11));
v___x_601_ = lean_usize_of_nat(v___x_597_);
v___x_602_ = ((size_t)0ULL);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_594_, v___f_600_, v_buckets_595_, v___x_601_, v___x_602_, v___x_596_);
return v___x_603_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___boxed(lean_object* v_00_u03b1_604_, lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v_m_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Std_HashSet_toList(v_00_u03b1_604_, v_x_605_, v_x_606_, v_m_607_);
lean_dec_ref(v_x_606_);
lean_dec_ref(v_x_605_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg(lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_l_615_){
_start:
{
lean_object* v___f_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___f_616_ = ((lean_object*)(l_Std_HashSet_ofList___redArg___closed__1));
v___x_617_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_618_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_616_, v_inst_613_, v_inst_614_, v___x_617_, v_l_615_);
return v___x_618_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList(lean_object* v_00_u03b1_619_, lean_object* v_inst_620_, lean_object* v_inst_621_, lean_object* v_l_622_){
_start:
{
lean_object* v___f_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___f_623_ = ((lean_object*)(l_Std_HashSet_ofList___redArg___closed__1));
v___x_624_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_625_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_623_, v_inst_620_, v_inst_621_, v___x_624_, v_l_622_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0(lean_object* v_f_626_, lean_object* v_b_627_, lean_object* v_a_628_, lean_object* v_x_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_apply_2(v_f_626_, v_b_627_, v_a_628_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__1(lean_object* v_inst_631_, lean_object* v___f_632_, lean_object* v_acc_633_, lean_object* v_l_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_631_, v___f_632_, v_acc_633_, v_l_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg(lean_object* v_inst_636_, lean_object* v_f_637_, lean_object* v_init_638_, lean_object* v_b_639_){
_start:
{
lean_object* v_toApplicative_640_; lean_object* v_buckets_641_; lean_object* v_toPure_642_; lean_object* v___x_643_; lean_object* v___x_644_; uint8_t v___x_645_; 
v_toApplicative_640_ = lean_ctor_get(v_inst_636_, 0);
v_buckets_641_ = lean_ctor_get(v_b_639_, 1);
lean_inc_ref(v_buckets_641_);
lean_dec_ref(v_b_639_);
v_toPure_642_ = lean_ctor_get(v_toApplicative_640_, 1);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_array_get_size(v_buckets_641_);
v___x_645_ = lean_nat_dec_lt(v___x_643_, v___x_644_);
if (v___x_645_ == 0)
{
lean_object* v___x_646_; 
lean_inc(v_toPure_642_);
lean_dec_ref(v_buckets_641_);
lean_dec(v_f_637_);
lean_dec_ref(v_inst_636_);
v___x_646_ = lean_apply_2(v_toPure_642_, lean_box(0), v_init_638_);
return v___x_646_;
}
else
{
lean_object* v___f_647_; lean_object* v___f_648_; size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
v___f_647_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_647_, 0, v_f_637_);
lean_inc_ref(v_inst_636_);
v___f_648_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_648_, 0, v_inst_636_);
lean_closure_set(v___f_648_, 1, v___f_647_);
v___x_649_ = ((size_t)0ULL);
v___x_650_ = lean_usize_of_nat(v___x_644_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_636_, v___f_648_, v_buckets_641_, v___x_649_, v___x_650_, v_init_638_);
return v___x_651_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM(lean_object* v_00_u03b1_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_m_655_, lean_object* v_inst_656_, lean_object* v_00_u03b2_657_, lean_object* v_f_658_, lean_object* v_init_659_, lean_object* v_b_660_){
_start:
{
lean_object* v_toApplicative_661_; lean_object* v_buckets_662_; lean_object* v_toPure_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_toApplicative_661_ = lean_ctor_get(v_inst_656_, 0);
v_buckets_662_ = lean_ctor_get(v_b_660_, 1);
lean_inc_ref(v_buckets_662_);
lean_dec_ref(v_b_660_);
v_toPure_663_ = lean_ctor_get(v_toApplicative_661_, 1);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_array_get_size(v_buckets_662_);
v___x_666_ = lean_nat_dec_lt(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_inc(v_toPure_663_);
lean_dec_ref(v_buckets_662_);
lean_dec(v_f_658_);
lean_dec_ref(v_inst_656_);
v___x_667_ = lean_apply_2(v_toPure_663_, lean_box(0), v_init_659_);
return v___x_667_;
}
else
{
lean_object* v___f_668_; lean_object* v___f_669_; size_t v___x_670_; size_t v___x_671_; lean_object* v___x_672_; 
v___f_668_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_668_, 0, v_f_658_);
lean_inc_ref(v_inst_656_);
v___f_669_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_669_, 0, v_inst_656_);
lean_closure_set(v___f_669_, 1, v___f_668_);
v___x_670_ = ((size_t)0ULL);
v___x_671_ = lean_usize_of_nat(v___x_665_);
v___x_672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_656_, v___f_669_, v_buckets_662_, v___x_670_, v___x_671_, v_init_659_);
return v___x_672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___boxed(lean_object* v_00_u03b1_673_, lean_object* v_x_674_, lean_object* v_x_675_, lean_object* v_m_676_, lean_object* v_inst_677_, lean_object* v_00_u03b2_678_, lean_object* v_f_679_, lean_object* v_init_680_, lean_object* v_b_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_HashSet_foldM(v_00_u03b1_673_, v_x_674_, v_x_675_, v_m_676_, v_inst_677_, v_00_u03b2_678_, v_f_679_, v_init_680_, v_b_681_);
lean_dec_ref(v_x_675_);
lean_dec_ref(v_x_674_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__0(lean_object* v_f_683_, lean_object* v_x1_684_, lean_object* v_x2_685_, lean_object* v_x3_686_){
_start:
{
lean_object* v___x_687_; 
v___x_687_ = lean_apply_2(v_f_683_, v_x1_684_, v_x2_685_);
return v___x_687_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__1(lean_object* v___x_688_, lean_object* v___f_689_, lean_object* v_acc_690_, lean_object* v_l_691_){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_688_, v___f_689_, v_acc_690_, v_l_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg(lean_object* v_f_693_, lean_object* v_init_694_, lean_object* v_m_695_){
_start:
{
lean_object* v___x_696_; lean_object* v_buckets_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_696_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_697_ = lean_ctor_get(v_m_695_, 1);
lean_inc_ref(v_buckets_697_);
lean_dec_ref(v_m_695_);
v___x_698_ = lean_unsigned_to_nat(0u);
v___x_699_ = lean_array_get_size(v_buckets_697_);
v___x_700_ = lean_nat_dec_lt(v___x_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_dec_ref(v_buckets_697_);
lean_dec(v_f_693_);
return v_init_694_;
}
else
{
lean_object* v___f_701_; lean_object* v___f_702_; size_t v___x_703_; size_t v___x_704_; lean_object* v___x_705_; 
v___f_701_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_701_, 0, v_f_693_);
v___f_702_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_702_, 0, v___x_696_);
lean_closure_set(v___f_702_, 1, v___f_701_);
v___x_703_ = ((size_t)0ULL);
v___x_704_ = lean_usize_of_nat(v___x_699_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_696_, v___f_702_, v_buckets_697_, v___x_703_, v___x_704_, v_init_694_);
return v___x_705_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold(lean_object* v_00_u03b1_706_, lean_object* v_x_707_, lean_object* v_x_708_, lean_object* v_00_u03b2_709_, lean_object* v_f_710_, lean_object* v_init_711_, lean_object* v_m_712_){
_start:
{
lean_object* v___x_713_; lean_object* v_buckets_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_713_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_714_ = lean_ctor_get(v_m_712_, 1);
lean_inc_ref(v_buckets_714_);
lean_dec_ref(v_m_712_);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = lean_array_get_size(v_buckets_714_);
v___x_717_ = lean_nat_dec_lt(v___x_715_, v___x_716_);
if (v___x_717_ == 0)
{
lean_dec_ref(v_buckets_714_);
lean_dec(v_f_710_);
return v_init_711_;
}
else
{
lean_object* v___f_718_; lean_object* v___f_719_; size_t v___x_720_; size_t v___x_721_; lean_object* v___x_722_; 
v___f_718_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_718_, 0, v_f_710_);
v___f_719_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_719_, 0, v___x_713_);
lean_closure_set(v___f_719_, 1, v___f_718_);
v___x_720_ = ((size_t)0ULL);
v___x_721_ = lean_usize_of_nat(v___x_716_);
v___x_722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_713_, v___f_719_, v_buckets_714_, v___x_720_, v___x_721_, v_init_711_);
return v___x_722_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___boxed(lean_object* v_00_u03b1_723_, lean_object* v_x_724_, lean_object* v_x_725_, lean_object* v_00_u03b2_726_, lean_object* v_f_727_, lean_object* v_init_728_, lean_object* v_m_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_HashSet_fold(v_00_u03b1_723_, v_x_724_, v_x_725_, v_00_u03b2_726_, v_f_727_, v_init_728_, v_m_729_);
lean_dec_ref(v_x_725_);
lean_dec_ref(v_x_724_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0(lean_object* v_f_731_, lean_object* v_x_732_, lean_object* v___y_733_, lean_object* v___y_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = lean_apply_1(v_f_731_, v___y_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__1(lean_object* v_inst_736_, lean_object* v___f_737_, lean_object* v_x_738_, lean_object* v___y_739_){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = lean_box(0);
v___x_741_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_736_, v___f_737_, v___x_740_, v___y_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg(lean_object* v_inst_742_, lean_object* v_f_743_, lean_object* v_b_744_){
_start:
{
lean_object* v_toApplicative_745_; lean_object* v_buckets_746_; lean_object* v_toPure_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_toApplicative_745_ = lean_ctor_get(v_inst_742_, 0);
v_buckets_746_ = lean_ctor_get(v_b_744_, 1);
lean_inc_ref(v_buckets_746_);
lean_dec_ref(v_b_744_);
v_toPure_747_ = lean_ctor_get(v_toApplicative_745_, 1);
v___x_748_ = lean_unsigned_to_nat(0u);
v___x_749_ = lean_array_get_size(v_buckets_746_);
v___x_750_ = lean_box(0);
v___x_751_ = lean_nat_dec_lt(v___x_748_, v___x_749_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_inc(v_toPure_747_);
lean_dec_ref(v_buckets_746_);
lean_dec(v_f_743_);
lean_dec_ref(v_inst_742_);
v___x_752_ = lean_apply_2(v_toPure_747_, lean_box(0), v___x_750_);
return v___x_752_;
}
else
{
lean_object* v___f_753_; lean_object* v___f_754_; size_t v___x_755_; size_t v___x_756_; lean_object* v___x_757_; 
v___f_753_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_753_, 0, v_f_743_);
lean_inc_ref(v_inst_742_);
v___f_754_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_754_, 0, v_inst_742_);
lean_closure_set(v___f_754_, 1, v___f_753_);
v___x_755_ = ((size_t)0ULL);
v___x_756_ = lean_usize_of_nat(v___x_749_);
v___x_757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_742_, v___f_754_, v_buckets_746_, v___x_755_, v___x_756_, v___x_750_);
return v___x_757_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM(lean_object* v_00_u03b1_758_, lean_object* v_x_759_, lean_object* v_x_760_, lean_object* v_m_761_, lean_object* v_inst_762_, lean_object* v_f_763_, lean_object* v_b_764_){
_start:
{
lean_object* v_toApplicative_765_; lean_object* v_buckets_766_; lean_object* v_toPure_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_toApplicative_765_ = lean_ctor_get(v_inst_762_, 0);
v_buckets_766_ = lean_ctor_get(v_b_764_, 1);
lean_inc_ref(v_buckets_766_);
lean_dec_ref(v_b_764_);
v_toPure_767_ = lean_ctor_get(v_toApplicative_765_, 1);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_array_get_size(v_buckets_766_);
v___x_770_ = lean_box(0);
v___x_771_ = lean_nat_dec_lt(v___x_768_, v___x_769_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; 
lean_inc(v_toPure_767_);
lean_dec_ref(v_buckets_766_);
lean_dec(v_f_763_);
lean_dec_ref(v_inst_762_);
v___x_772_ = lean_apply_2(v_toPure_767_, lean_box(0), v___x_770_);
return v___x_772_;
}
else
{
lean_object* v___f_773_; lean_object* v___f_774_; size_t v___x_775_; size_t v___x_776_; lean_object* v___x_777_; 
v___f_773_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_773_, 0, v_f_763_);
lean_inc_ref(v_inst_762_);
v___f_774_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_774_, 0, v_inst_762_);
lean_closure_set(v___f_774_, 1, v___f_773_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = lean_usize_of_nat(v___x_769_);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_762_, v___f_774_, v_buckets_766_, v___x_775_, v___x_776_, v___x_770_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___boxed(lean_object* v_00_u03b1_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_m_781_, lean_object* v_inst_782_, lean_object* v_f_783_, lean_object* v_b_784_){
_start:
{
lean_object* v_res_785_; 
v_res_785_ = l_Std_HashSet_forM(v_00_u03b1_778_, v_x_779_, v_x_780_, v_m_781_, v_inst_782_, v_f_783_, v_b_784_);
lean_dec_ref(v_x_780_);
lean_dec_ref(v_x_779_);
return v_res_785_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0(lean_object* v_f_786_, lean_object* v_a_787_, lean_object* v_x_788_, lean_object* v_acc_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_apply_2(v_f_786_, v_a_787_, v_acc_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__1(lean_object* v_inst_791_, lean_object* v___f_792_, lean_object* v_a_793_, lean_object* v_x_794_, lean_object* v___y_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_791_, v___f_792_, v_a_793_, v___y_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg(lean_object* v_inst_797_, lean_object* v_f_798_, lean_object* v_init_799_, lean_object* v_b_800_){
_start:
{
lean_object* v_buckets_801_; lean_object* v___f_802_; lean_object* v___f_803_; size_t v_sz_804_; size_t v___x_805_; lean_object* v___x_806_; 
v_buckets_801_ = lean_ctor_get(v_b_800_, 1);
lean_inc_ref(v_buckets_801_);
lean_dec_ref(v_b_800_);
v___f_802_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_802_, 0, v_f_798_);
lean_inc_ref(v_inst_797_);
v___f_803_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_803_, 0, v_inst_797_);
lean_closure_set(v___f_803_, 1, v___f_802_);
v_sz_804_ = lean_array_size(v_buckets_801_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_797_, v_buckets_801_, v___f_803_, v_sz_804_, v___x_805_, v_init_799_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn(lean_object* v_00_u03b1_807_, lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_m_810_, lean_object* v_inst_811_, lean_object* v_00_u03b2_812_, lean_object* v_f_813_, lean_object* v_init_814_, lean_object* v_b_815_){
_start:
{
lean_object* v_buckets_816_; lean_object* v___f_817_; lean_object* v___f_818_; size_t v_sz_819_; size_t v___x_820_; lean_object* v___x_821_; 
v_buckets_816_ = lean_ctor_get(v_b_815_, 1);
lean_inc_ref(v_buckets_816_);
lean_dec_ref(v_b_815_);
v___f_817_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_817_, 0, v_f_813_);
lean_inc_ref(v_inst_811_);
v___f_818_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_818_, 0, v_inst_811_);
lean_closure_set(v___f_818_, 1, v___f_817_);
v_sz_819_ = lean_array_size(v_buckets_816_);
v___x_820_ = ((size_t)0ULL);
v___x_821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_811_, v_buckets_816_, v___f_818_, v_sz_819_, v___x_820_, v_init_814_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___boxed(lean_object* v_00_u03b1_822_, lean_object* v_x_823_, lean_object* v_x_824_, lean_object* v_m_825_, lean_object* v_inst_826_, lean_object* v_00_u03b2_827_, lean_object* v_f_828_, lean_object* v_init_829_, lean_object* v_b_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Std_HashSet_forIn(v_00_u03b1_822_, v_x_823_, v_x_824_, v_m_825_, v_inst_826_, v_00_u03b2_827_, v_f_828_, v_init_829_, v_b_830_);
lean_dec_ref(v_x_824_);
lean_dec_ref(v_x_823_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg___lam__2(lean_object* v_inst_832_, lean_object* v_m_833_, lean_object* v_f_834_){
_start:
{
lean_object* v_toApplicative_835_; lean_object* v_buckets_836_; lean_object* v_toPure_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_toApplicative_835_ = lean_ctor_get(v_inst_832_, 0);
v_buckets_836_ = lean_ctor_get(v_m_833_, 1);
lean_inc_ref(v_buckets_836_);
lean_dec_ref(v_m_833_);
v_toPure_837_ = lean_ctor_get(v_toApplicative_835_, 1);
v___x_838_ = lean_unsigned_to_nat(0u);
v___x_839_ = lean_array_get_size(v_buckets_836_);
v___x_840_ = lean_box(0);
v___x_841_ = lean_nat_dec_lt(v___x_838_, v___x_839_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
lean_inc(v_toPure_837_);
lean_dec_ref(v_buckets_836_);
lean_dec(v_f_834_);
lean_dec_ref(v_inst_832_);
v___x_842_ = lean_apply_2(v_toPure_837_, lean_box(0), v___x_840_);
return v___x_842_;
}
else
{
lean_object* v___f_843_; lean_object* v___f_844_; size_t v___x_845_; size_t v___x_846_; lean_object* v___x_847_; 
v___f_843_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_843_, 0, v_f_834_);
lean_inc_ref(v_inst_832_);
v___f_844_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_844_, 0, v_inst_832_);
lean_closure_set(v___f_844_, 1, v___f_843_);
v___x_845_ = ((size_t)0ULL);
v___x_846_ = lean_usize_of_nat(v___x_839_);
v___x_847_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_832_, v___f_844_, v_buckets_836_, v___x_845_, v___x_846_, v___x_840_);
return v___x_847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg(lean_object* v_inst_848_){
_start:
{
lean_object* v___f_849_; 
v___f_849_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_849_, 0, v_inst_848_);
return v___f_849_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad(lean_object* v_00_u03b1_850_, lean_object* v_inst_851_, lean_object* v_inst_852_, lean_object* v_m_853_, lean_object* v_inst_854_){
_start:
{
lean_object* v___f_855_; 
v___f_855_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_855_, 0, v_inst_854_);
return v___f_855_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_m_859_, lean_object* v_inst_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_HashSet_instForMOfMonad(v_00_u03b1_856_, v_inst_857_, v_inst_858_, v_m_859_, v_inst_860_);
lean_dec_ref(v_inst_858_);
lean_dec_ref(v_inst_857_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg___lam__2(lean_object* v_inst_862_, lean_object* v_00_u03b2_863_, lean_object* v_m_864_, lean_object* v_init_865_, lean_object* v_f_866_){
_start:
{
lean_object* v_buckets_867_; lean_object* v___f_868_; lean_object* v___f_869_; size_t v_sz_870_; size_t v___x_871_; lean_object* v___x_872_; 
v_buckets_867_ = lean_ctor_get(v_m_864_, 1);
lean_inc_ref(v_buckets_867_);
lean_dec_ref(v_m_864_);
v___f_868_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_868_, 0, v_f_866_);
lean_inc_ref(v_inst_862_);
v___f_869_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_869_, 0, v_inst_862_);
lean_closure_set(v___f_869_, 1, v___f_868_);
v_sz_870_ = lean_array_size(v_buckets_867_);
v___x_871_ = ((size_t)0ULL);
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_862_, v_buckets_867_, v___f_869_, v_sz_870_, v___x_871_, v_init_865_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg(lean_object* v_inst_873_){
_start:
{
lean_object* v___f_874_; 
v___f_874_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_874_, 0, v_inst_873_);
return v___f_874_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad(lean_object* v_00_u03b1_875_, lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_m_878_, lean_object* v_inst_879_){
_start:
{
lean_object* v___f_880_; 
v___f_880_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_880_, 0, v_inst_879_);
return v___f_880_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_881_, lean_object* v_inst_882_, lean_object* v_inst_883_, lean_object* v_m_884_, lean_object* v_inst_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_HashSet_instForInOfMonad(v_00_u03b1_881_, v_inst_882_, v_inst_883_, v_m_884_, v_inst_885_);
lean_dec_ref(v_inst_883_);
lean_dec_ref(v_inst_882_);
return v_res_886_;
}
}
uint8_t l_Std_HashSet_filter___redArg___lam__0(lean_object* v_f_887_, lean_object* v_a_888_, lean_object* v_x_889_){
_start:
{
lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_890_ = lean_apply_1(v_f_887_, v_a_888_);
v___x_891_ = lean_unbox(v___x_890_);
return v___x_891_;
}
}
LEAN_EXPORT void l_Std_HashSet_filter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_887_ = stack[0].m_obj;
lean_object* v_a_888_ = stack[1].m_obj;
lean_object* v_x_889_ = stack[2].m_obj;
uint8_t v_res_892_;
v_res_892_ = l_Std_HashSet_filter___redArg___lam__0(v_f_887_, v_a_888_, v_x_889_);
stack->m_num = v_res_892_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__0___boxed(lean_object* v_f_893_, lean_object* v_a_894_, lean_object* v_x_895_){
_start:
{
uint8_t v_res_896_; lean_object* v_r_897_; 
v_res_896_ = l_Std_HashSet_filter___redArg___lam__0(v_f_893_, v_a_894_, v_x_895_);
v_r_897_ = lean_box(v_res_896_);
return v_r_897_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg(lean_object* v_f_898_, lean_object* v_m_899_){
_start:
{
lean_object* v___f_900_; lean_object* v___x_901_; 
v___f_900_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_900_, 0, v_f_898_);
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_900_, v_m_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter(lean_object* v_00_u03b1_902_, lean_object* v_x_903_, lean_object* v_x_904_, lean_object* v_f_905_, lean_object* v_m_906_){
_start:
{
lean_object* v___f_907_; lean_object* v___x_908_; 
v___f_907_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_907_, 0, v_f_905_);
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_907_, v_m_906_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___boxed(lean_object* v_00_u03b1_909_, lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v_f_912_, lean_object* v_m_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_HashSet_filter(v_00_u03b1_909_, v_x_910_, v_x_911_, v_f_912_, v_m_913_);
lean_dec_ref(v_x_911_);
lean_dec_ref(v_x_910_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg(lean_object* v_x_915_, lean_object* v_x_916_, lean_object* v_inst_917_, lean_object* v_m_918_, lean_object* v_l_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_917_, v_x_915_, v_x_916_, v_m_918_, v_l_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany(lean_object* v_00_u03b1_921_, lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_00_u03c1_924_, lean_object* v_inst_925_, lean_object* v_m_926_, lean_object* v_l_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_925_, v_x_922_, v_x_923_, v_m_926_, v_l_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0(lean_object* v_x1_929_, lean_object* v_x2_930_, lean_object* v_x3_931_){
_start:
{
lean_object* v___x_932_; 
v___x_932_ = lean_array_push(v_x1_929_, v_x2_930_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__1(lean_object* v___x_933_, lean_object* v___f_934_, lean_object* v_acc_935_, lean_object* v_l_936_){
_start:
{
lean_object* v___x_937_; 
v___x_937_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_933_, v___f_934_, v_acc_935_, v_l_936_);
return v___x_937_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg(lean_object* v_m_942_){
_start:
{
lean_object* v_size_943_; lean_object* v_buckets_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_size_943_ = lean_ctor_get(v_m_942_, 0);
lean_inc(v_size_943_);
v_buckets_944_ = lean_ctor_get(v_m_942_, 1);
lean_inc_ref(v_buckets_944_);
lean_dec_ref(v_m_942_);
v___x_945_ = lean_mk_empty_array_with_capacity(v_size_943_);
lean_dec(v_size_943_);
v___x_946_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v___x_947_ = lean_unsigned_to_nat(0u);
v___x_948_ = lean_array_get_size(v_buckets_944_);
v___x_949_ = lean_nat_dec_lt(v___x_947_, v___x_948_);
if (v___x_949_ == 0)
{
lean_dec_ref(v_buckets_944_);
return v___x_945_;
}
else
{
lean_object* v___f_950_; size_t v___x_951_; size_t v___x_952_; lean_object* v___x_953_; 
v___f_950_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__1));
v___x_951_ = ((size_t)0ULL);
v___x_952_ = lean_usize_of_nat(v___x_948_);
v___x_953_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_946_, v___f_950_, v_buckets_944_, v___x_951_, v___x_952_, v___x_945_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray(lean_object* v_00_u03b1_954_, lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v_m_957_){
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
lean_object* v___f_965_; size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; 
v___f_965_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__1));
v___x_966_ = ((size_t)0ULL);
v___x_967_ = lean_usize_of_nat(v___x_963_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_961_, v___f_965_, v_buckets_959_, v___x_966_, v___x_967_, v___x_960_);
return v___x_968_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___boxed(lean_object* v_00_u03b1_969_, lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v_m_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_HashSet_toArray(v_00_u03b1_969_, v_x_970_, v_x_971_, v_m_972_);
lean_dec_ref(v_x_971_);
lean_dec_ref(v_x_970_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0(lean_object* v_p_974_, lean_object* v___x_975_, lean_object* v___x_976_, lean_object* v_a_977_, lean_object* v_b_978_, lean_object* v_acc_979_){
_start:
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_apply_1(v_p_974_, v_a_977_);
v___x_981_ = lean_unbox(v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
lean_dec_ref(v___x_976_);
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_980_);
v___x_983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
lean_ctor_set(v___x_983_, 1, v___x_975_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
return v___x_984_;
}
else
{
lean_object* v___x_985_; 
v___x_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_976_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0___boxed(lean_object* v_p_986_, lean_object* v___x_987_, lean_object* v___x_988_, lean_object* v_a_989_, lean_object* v_b_990_, lean_object* v_acc_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_HashSet_all___redArg___lam__0(v_p_986_, v___x_987_, v___x_988_, v_a_989_, v_b_990_, v_acc_991_);
lean_dec_ref(v_acc_991_);
return v_res_992_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__1(lean_object* v___x_993_, lean_object* v___f_994_, lean_object* v_a_995_, lean_object* v_x_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_993_, v___f_994_, v_a_995_, v___y_997_);
return v___x_998_;
}
}
uint8_t l_Std_HashSet_all___redArg(lean_object* v_m_1002_, lean_object* v_p_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v_buckets_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___f_1008_; lean_object* v___f_1009_; size_t v_sz_1010_; size_t v___x_1011_; lean_object* v___x_1012_; lean_object* v_fst_1013_; 
v___x_1004_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1005_ = lean_ctor_get(v_m_1002_, 1);
lean_inc_ref(v_buckets_1005_);
lean_dec_ref(v_m_1002_);
v___x_1006_ = lean_box(0);
v___x_1007_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1008_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1008_, 0, v_p_1003_);
lean_closure_set(v___f_1008_, 1, v___x_1006_);
lean_closure_set(v___f_1008_, 2, v___x_1007_);
v___f_1009_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1009_, 0, v___x_1004_);
lean_closure_set(v___f_1009_, 1, v___f_1008_);
v_sz_1010_ = lean_array_size(v_buckets_1005_);
v___x_1011_ = ((size_t)0ULL);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1004_, v_buckets_1005_, v___f_1009_, v_sz_1010_, v___x_1011_, v___x_1007_);
v_fst_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_fst_1013_);
lean_dec(v___x_1012_);
if (lean_obj_tag(v_fst_1013_) == 0)
{
uint8_t v___x_1014_; 
v___x_1014_ = 1;
return v___x_1014_;
}
else
{
lean_object* v_val_1015_; uint8_t v___x_1016_; 
v_val_1015_ = lean_ctor_get(v_fst_1013_, 0);
lean_inc(v_val_1015_);
lean_dec_ref_known(v_fst_1013_, 1);
v___x_1016_ = lean_unbox(v_val_1015_);
lean_dec(v_val_1015_);
return v___x_1016_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1002_ = stack[0].m_obj;
lean_object* v_p_1003_ = stack[1].m_obj;
uint8_t v_res_1017_;
v_res_1017_ = l_Std_HashSet_all___redArg(v_m_1002_, v_p_1003_);
stack->m_num = v_res_1017_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___boxed(lean_object* v_m_1018_, lean_object* v_p_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = l_Std_HashSet_all___redArg(v_m_1018_, v_p_1019_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
uint8_t l_Std_HashSet_all(lean_object* v_00_u03b1_1022_, lean_object* v_x_1023_, lean_object* v_x_1024_, lean_object* v_m_1025_, lean_object* v_p_1026_){
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
lean_dec_ref_known(v_fst_1036_, 1);
v___x_1039_ = lean_unbox(v_val_1038_);
lean_dec(v_val_1038_);
return v___x_1039_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1023_ = stack[1].m_obj;
lean_object* v_x_1024_ = stack[2].m_obj;
lean_object* v_m_1025_ = stack[3].m_obj;
lean_object* v_p_1026_ = stack[4].m_obj;
uint8_t v_res_1040_;
v_res_1040_ = l_Std_HashSet_all(lean_box(0), v_x_1023_, v_x_1024_, v_m_1025_, v_p_1026_);
stack->m_num = v_res_1040_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_x_1042_, lean_object* v_x_1043_, lean_object* v_m_1044_, lean_object* v_p_1045_){
_start:
{
uint8_t v_res_1046_; lean_object* v_r_1047_; 
v_res_1046_ = l_Std_HashSet_all(v_00_u03b1_1041_, v_x_1042_, v_x_1043_, v_m_1044_, v_p_1045_);
lean_dec_ref(v_x_1043_);
lean_dec_ref(v_x_1042_);
v_r_1047_ = lean_box(v_res_1046_);
return v_r_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0(lean_object* v_p_1048_, lean_object* v___x_1049_, lean_object* v___x_1050_, lean_object* v_a_1051_, lean_object* v_b_1052_, lean_object* v_acc_1053_){
_start:
{
lean_object* v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = lean_apply_1(v_p_1048_, v_a_1051_);
v___x_1055_ = lean_unbox(v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1056_, 0, v___x_1049_);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec_ref(v___x_1049_);
v___x_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1054_);
v___x_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1058_, 0, v___x_1057_);
lean_ctor_set(v___x_1058_, 1, v___x_1050_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0___boxed(lean_object* v_p_1060_, lean_object* v___x_1061_, lean_object* v___x_1062_, lean_object* v_a_1063_, lean_object* v_b_1064_, lean_object* v_acc_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l_Std_HashSet_any___redArg___lam__0(v_p_1060_, v___x_1061_, v___x_1062_, v_a_1063_, v_b_1064_, v_acc_1065_);
lean_dec_ref(v_acc_1065_);
return v_res_1066_;
}
}
uint8_t l_Std_HashSet_any___redArg(lean_object* v_m_1067_, lean_object* v_p_1068_){
_start:
{
lean_object* v___x_1069_; lean_object* v_buckets_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___f_1073_; lean_object* v___f_1074_; size_t v_sz_1075_; size_t v___x_1076_; lean_object* v___x_1077_; lean_object* v_fst_1078_; 
v___x_1069_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1070_ = lean_ctor_get(v_m_1067_, 1);
lean_inc_ref(v_buckets_1070_);
lean_dec_ref(v_m_1067_);
v___x_1071_ = lean_box(0);
v___x_1072_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1073_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1073_, 0, v_p_1068_);
lean_closure_set(v___f_1073_, 1, v___x_1072_);
lean_closure_set(v___f_1073_, 2, v___x_1071_);
v___f_1074_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1074_, 0, v___x_1069_);
lean_closure_set(v___f_1074_, 1, v___f_1073_);
v_sz_1075_ = lean_array_size(v_buckets_1070_);
v___x_1076_ = ((size_t)0ULL);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1069_, v_buckets_1070_, v___f_1074_, v_sz_1075_, v___x_1076_, v___x_1072_);
v_fst_1078_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_fst_1078_);
lean_dec(v___x_1077_);
if (lean_obj_tag(v_fst_1078_) == 0)
{
uint8_t v___x_1079_; 
v___x_1079_ = 0;
return v___x_1079_;
}
else
{
lean_object* v_val_1080_; uint8_t v___x_1081_; 
v_val_1080_ = lean_ctor_get(v_fst_1078_, 0);
lean_inc(v_val_1080_);
lean_dec_ref_known(v_fst_1078_, 1);
v___x_1081_ = lean_unbox(v_val_1080_);
lean_dec(v_val_1080_);
return v___x_1081_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1067_ = stack[0].m_obj;
lean_object* v_p_1068_ = stack[1].m_obj;
uint8_t v_res_1082_;
v_res_1082_ = l_Std_HashSet_any___redArg(v_m_1067_, v_p_1068_);
stack->m_num = v_res_1082_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___boxed(lean_object* v_m_1083_, lean_object* v_p_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l_Std_HashSet_any___redArg(v_m_1083_, v_p_1084_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
uint8_t l_Std_HashSet_any(lean_object* v_00_u03b1_1087_, lean_object* v_x_1088_, lean_object* v_x_1089_, lean_object* v_m_1090_, lean_object* v_p_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v_buckets_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___f_1096_; lean_object* v___f_1097_; size_t v_sz_1098_; size_t v___x_1099_; lean_object* v___x_1100_; lean_object* v_fst_1101_; 
v___x_1092_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1093_ = lean_ctor_get(v_m_1090_, 1);
lean_inc_ref(v_buckets_1093_);
lean_dec_ref(v_m_1090_);
v___x_1094_ = lean_box(0);
v___x_1095_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1096_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1096_, 0, v_p_1091_);
lean_closure_set(v___f_1096_, 1, v___x_1095_);
lean_closure_set(v___f_1096_, 2, v___x_1094_);
v___f_1097_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1097_, 0, v___x_1092_);
lean_closure_set(v___f_1097_, 1, v___f_1096_);
v_sz_1098_ = lean_array_size(v_buckets_1093_);
v___x_1099_ = ((size_t)0ULL);
v___x_1100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1092_, v_buckets_1093_, v___f_1097_, v_sz_1098_, v___x_1099_, v___x_1095_);
v_fst_1101_ = lean_ctor_get(v___x_1100_, 0);
lean_inc(v_fst_1101_);
lean_dec(v___x_1100_);
if (lean_obj_tag(v_fst_1101_) == 0)
{
uint8_t v___x_1102_; 
v___x_1102_ = 0;
return v___x_1102_;
}
else
{
lean_object* v_val_1103_; uint8_t v___x_1104_; 
v_val_1103_ = lean_ctor_get(v_fst_1101_, 0);
lean_inc(v_val_1103_);
lean_dec_ref_known(v_fst_1101_, 1);
v___x_1104_ = lean_unbox(v_val_1103_);
lean_dec(v_val_1103_);
return v___x_1104_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1088_ = stack[1].m_obj;
lean_object* v_x_1089_ = stack[2].m_obj;
lean_object* v_m_1090_ = stack[3].m_obj;
lean_object* v_p_1091_ = stack[4].m_obj;
uint8_t v_res_1105_;
v_res_1105_ = l_Std_HashSet_any(lean_box(0), v_x_1088_, v_x_1089_, v_m_1090_, v_p_1091_);
stack->m_num = v_res_1105_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___boxed(lean_object* v_00_u03b1_1106_, lean_object* v_x_1107_, lean_object* v_x_1108_, lean_object* v_m_1109_, lean_object* v_p_1110_){
_start:
{
uint8_t v_res_1111_; lean_object* v_r_1112_; 
v_res_1111_ = l_Std_HashSet_any(v_00_u03b1_1106_, v_x_1107_, v_x_1108_, v_m_1109_, v_p_1110_);
lean_dec_ref(v_x_1108_);
lean_dec_ref(v_x_1107_);
v_r_1112_ = lean_box(v_res_1111_);
return v_r_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0(lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_a_1115_, lean_object* v_b_1116_, lean_object* v_acc_1117_){
_start:
{
lean_object* v_r_1118_; lean_object* v___x_1119_; 
v_r_1118_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1113_, v_inst_1114_, v_acc_1117_, v_a_1115_, v_b_1116_);
v___x_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_r_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__1(lean_object* v___x_1120_, lean_object* v___f_1121_, lean_object* v_a_1122_, lean_object* v_x_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1120_, v___f_1121_, v_a_1122_, v___y_1124_);
return v___x_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg(lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_m_u2081_1130_, lean_object* v_m_u2082_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v_size_1133_; lean_object* v_buckets_1134_; lean_object* v_size_1135_; uint8_t v___x_1136_; 
v___x_1132_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_size_1133_ = lean_ctor_get(v_m_u2081_1130_, 0);
v_buckets_1134_ = lean_ctor_get(v_m_u2081_1130_, 1);
v_size_1135_ = lean_ctor_get(v_m_u2082_1131_, 0);
v___x_1136_ = lean_nat_dec_le(v_size_1133_, v_size_1135_);
if (v___x_1136_ == 0)
{
lean_object* v___f_1137_; lean_object* v___x_1138_; 
v___f_1137_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1137_, v_inst_1128_, v_inst_1129_, v_m_u2081_1130_, v_m_u2082_1131_);
return v___x_1138_;
}
else
{
lean_object* v___f_1139_; lean_object* v___f_1140_; size_t v_sz_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
lean_inc_ref(v_buckets_1134_);
lean_dec_ref(v_m_u2081_1130_);
v___f_1139_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1139_, 0, v_inst_1128_);
lean_closure_set(v___f_1139_, 1, v_inst_1129_);
v___f_1140_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1140_, 0, v___x_1132_);
lean_closure_set(v___f_1140_, 1, v___f_1139_);
v_sz_1141_ = lean_array_size(v_buckets_1134_);
v___x_1142_ = ((size_t)0ULL);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1132_, v_buckets_1134_, v___f_1140_, v_sz_1141_, v___x_1142_, v_m_u2082_1131_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union(lean_object* v_00_u03b1_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_m_u2081_1147_, lean_object* v_m_u2082_1148_){
_start:
{
lean_object* v___x_1149_; lean_object* v_size_1150_; lean_object* v_buckets_1151_; lean_object* v_size_1152_; uint8_t v___x_1153_; 
v___x_1149_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_size_1150_ = lean_ctor_get(v_m_u2081_1147_, 0);
v_buckets_1151_ = lean_ctor_get(v_m_u2081_1147_, 1);
v_size_1152_ = lean_ctor_get(v_m_u2082_1148_, 0);
v___x_1153_ = lean_nat_dec_le(v_size_1150_, v_size_1152_);
if (v___x_1153_ == 0)
{
lean_object* v___f_1154_; lean_object* v___x_1155_; 
v___f_1154_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1155_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1154_, v_inst_1145_, v_inst_1146_, v_m_u2081_1147_, v_m_u2082_1148_);
return v___x_1155_;
}
else
{
lean_object* v___f_1156_; lean_object* v___f_1157_; size_t v_sz_1158_; size_t v___x_1159_; lean_object* v___x_1160_; 
lean_inc_ref(v_buckets_1151_);
lean_dec_ref(v_m_u2081_1147_);
v___f_1156_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1156_, 0, v_inst_1145_);
lean_closure_set(v___f_1156_, 1, v_inst_1146_);
v___f_1157_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1157_, 0, v___x_1149_);
lean_closure_set(v___f_1157_, 1, v___f_1156_);
v_sz_1158_ = lean_array_size(v_buckets_1151_);
v___x_1159_ = ((size_t)0ULL);
v___x_1160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1149_, v_buckets_1151_, v___f_1157_, v_sz_1158_, v___x_1159_, v_m_u2082_1148_);
return v___x_1160_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion___redArg(lean_object* v_inst_1161_, lean_object* v_inst_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1163_, 0, lean_box(0));
lean_closure_set(v___x_1163_, 1, v_inst_1161_);
lean_closure_set(v___x_1163_, 2, v_inst_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion(lean_object* v_00_u03b1_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1167_, 0, lean_box(0));
lean_closure_set(v___x_1167_, 1, v_inst_1165_);
lean_closure_set(v___x_1167_, 2, v_inst_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter___redArg(lean_object* v_inst_1168_, lean_object* v_inst_1169_, lean_object* v_m_u2081_1170_, lean_object* v_m_u2082_1171_){
_start:
{
lean_object* v___x_1172_; 
v___x_1172_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1168_, v_inst_1169_, v_m_u2081_1170_, v_m_u2082_1171_);
return v___x_1172_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter(lean_object* v_00_u03b1_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_, lean_object* v_m_u2081_1176_, lean_object* v_m_u2082_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1174_, v_inst_1175_, v_m_u2081_1176_, v_m_u2082_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter___redArg(lean_object* v_inst_1179_, lean_object* v_inst_1180_){
_start:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1181_, 0, lean_box(0));
lean_closure_set(v___x_1181_, 1, v_inst_1179_);
lean_closure_set(v___x_1181_, 2, v_inst_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter(lean_object* v_00_u03b1_1182_, lean_object* v_inst_1183_, lean_object* v_inst_1184_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1185_, 0, lean_box(0));
lean_closure_set(v___x_1185_, 1, v_inst_1183_);
lean_closure_set(v___x_1185_, 2, v_inst_1184_);
return v___x_1185_;
}
}
static lean_object* _init_l_Std_HashSet_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___f_1187_; 
v___x_1186_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1187_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1187_, 0, v___x_1186_);
return v___f_1187_;
}
}
uint8_t l_Std_HashSet_beq___redArg(lean_object* v_x_1188_, lean_object* v_inst_1189_, lean_object* v_m_u2081_1190_, lean_object* v_m_u2082_1191_){
_start:
{
lean_object* v___f_1192_; uint8_t v___x_1193_; 
v___f_1192_ = lean_obj_once(&l_Std_HashSet_beq___redArg___closed__0, &l_Std_HashSet_beq___redArg___closed__0_once, _init_l_Std_HashSet_beq___redArg___closed__0);
v___x_1193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1189_, v_x_1188_, v___f_1192_, v_m_u2081_1190_, v_m_u2082_1191_);
return v___x_1193_;
}
}
LEAN_EXPORT void l_Std_HashSet_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1188_ = stack[0].m_obj;
lean_object* v_inst_1189_ = stack[1].m_obj;
lean_object* v_m_u2081_1190_ = stack[2].m_obj;
lean_object* v_m_u2082_1191_ = stack[3].m_obj;
uint8_t v_res_1194_;
v_res_1194_ = l_Std_HashSet_beq___redArg(v_x_1188_, v_inst_1189_, v_m_u2081_1190_, v_m_u2082_1191_);
stack->m_num = v_res_1194_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___redArg___boxed(lean_object* v_x_1195_, lean_object* v_inst_1196_, lean_object* v_m_u2081_1197_, lean_object* v_m_u2082_1198_){
_start:
{
uint8_t v_res_1199_; lean_object* v_r_1200_; 
v_res_1199_ = l_Std_HashSet_beq___redArg(v_x_1195_, v_inst_1196_, v_m_u2081_1197_, v_m_u2082_1198_);
v_r_1200_ = lean_box(v_res_1199_);
return v_r_1200_;
}
}
uint8_t l_Std_HashSet_beq(lean_object* v_00_u03b1_1201_, lean_object* v_x_1202_, lean_object* v_inst_1203_, lean_object* v_m_u2081_1204_, lean_object* v_m_u2082_1205_){
_start:
{
uint8_t v___x_1206_; 
v___x_1206_ = l_Std_HashSet_beq___redArg(v_x_1202_, v_inst_1203_, v_m_u2081_1204_, v_m_u2082_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT void l_Std_HashSet_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1202_ = stack[1].m_obj;
lean_object* v_inst_1203_ = stack[2].m_obj;
lean_object* v_m_u2081_1204_ = stack[3].m_obj;
lean_object* v_m_u2082_1205_ = stack[4].m_obj;
uint8_t v_res_1207_;
v_res_1207_ = l_Std_HashSet_beq(lean_box(0), v_x_1202_, v_inst_1203_, v_m_u2081_1204_, v_m_u2082_1205_);
stack->m_num = v_res_1207_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___boxed(lean_object* v_00_u03b1_1208_, lean_object* v_x_1209_, lean_object* v_inst_1210_, lean_object* v_m_u2081_1211_, lean_object* v_m_u2082_1212_){
_start:
{
uint8_t v_res_1213_; lean_object* v_r_1214_; 
v_res_1213_ = l_Std_HashSet_beq(v_00_u03b1_1208_, v_x_1209_, v_inst_1210_, v_m_u2081_1211_, v_m_u2082_1212_);
v_r_1214_ = lean_box(v_res_1213_);
return v_r_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq___redArg(lean_object* v_x_1215_, lean_object* v_inst_1216_){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1217_, 0, lean_box(0));
lean_closure_set(v___x_1217_, 1, v_x_1215_);
lean_closure_set(v___x_1217_, 2, v_inst_1216_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq(lean_object* v_00_u03b1_1218_, lean_object* v_x_1219_, lean_object* v_inst_1220_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1221_, 0, lean_box(0));
lean_closure_set(v___x_1221_, 1, v_x_1219_);
lean_closure_set(v___x_1221_, 2, v_inst_1220_);
return v___x_1221_;
}
}
uint8_t l_Std_HashSet_diff___redArg___lam__0(lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_m_u2082_1224_, uint8_t v___x_1225_, lean_object* v_k_1226_, lean_object* v_x_1227_){
_start:
{
uint8_t v___x_1228_; 
v___x_1228_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1222_, v_inst_1223_, v_m_u2082_1224_, v_k_1226_);
if (v___x_1228_ == 0)
{
return v___x_1225_;
}
else
{
uint8_t v___x_1229_; 
v___x_1229_ = 0;
return v___x_1229_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_diff___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1222_ = stack[0].m_obj;
lean_object* v_inst_1223_ = stack[1].m_obj;
lean_object* v_m_u2082_1224_ = stack[2].m_obj;
uint8_t v___x_1225_ = stack[3].m_num;
lean_object* v_k_1226_ = stack[4].m_obj;
lean_object* v_x_1227_ = stack[5].m_obj;
uint8_t v_res_1230_;
v_res_1230_ = l_Std_HashSet_diff___redArg___lam__0(v_inst_1222_, v_inst_1223_, v_m_u2082_1224_, v___x_1225_, v_k_1226_, v_x_1227_);
stack->m_num = v_res_1230_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg___lam__0___boxed(lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_m_u2082_1233_, lean_object* v___x_1234_, lean_object* v_k_1235_, lean_object* v_x_1236_){
_start:
{
uint8_t v___x_84__boxed_1237_; uint8_t v_res_1238_; lean_object* v_r_1239_; 
v___x_84__boxed_1237_ = lean_unbox(v___x_1234_);
v_res_1238_ = l_Std_HashSet_diff___redArg___lam__0(v_inst_1231_, v_inst_1232_, v_m_u2082_1233_, v___x_84__boxed_1237_, v_k_1235_, v_x_1236_);
lean_dec_ref(v_m_u2082_1233_);
v_r_1239_ = lean_box(v_res_1238_);
return v_r_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg(lean_object* v_inst_1240_, lean_object* v_inst_1241_, lean_object* v_m_u2081_1242_, lean_object* v_m_u2082_1243_){
_start:
{
lean_object* v_size_1244_; lean_object* v_size_1245_; uint8_t v___x_1246_; 
v_size_1244_ = lean_ctor_get(v_m_u2081_1242_, 0);
v_size_1245_ = lean_ctor_get(v_m_u2082_1243_, 0);
v___x_1246_ = lean_nat_dec_le(v_size_1244_, v_size_1245_);
if (v___x_1246_ == 0)
{
lean_object* v___f_1247_; lean_object* v___x_1248_; 
v___f_1247_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1248_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1247_, v_inst_1240_, v_inst_1241_, v_m_u2081_1242_, v_m_u2082_1243_);
return v___x_1248_;
}
else
{
lean_object* v___x_1249_; lean_object* v___f_1250_; lean_object* v___x_1251_; 
v___x_1249_ = lean_box(v___x_1246_);
v___f_1250_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1250_, 0, v_inst_1240_);
lean_closure_set(v___f_1250_, 1, v_inst_1241_);
lean_closure_set(v___f_1250_, 2, v_m_u2082_1243_);
lean_closure_set(v___f_1250_, 3, v___x_1249_);
v___x_1251_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1250_, v_m_u2081_1242_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff(lean_object* v_00_u03b1_1252_, lean_object* v_inst_1253_, lean_object* v_inst_1254_, lean_object* v_m_u2081_1255_, lean_object* v_m_u2082_1256_){
_start:
{
lean_object* v_size_1257_; lean_object* v_size_1258_; uint8_t v___x_1259_; 
v_size_1257_ = lean_ctor_get(v_m_u2081_1255_, 0);
v_size_1258_ = lean_ctor_get(v_m_u2082_1256_, 0);
v___x_1259_ = lean_nat_dec_le(v_size_1257_, v_size_1258_);
if (v___x_1259_ == 0)
{
lean_object* v___f_1260_; lean_object* v___x_1261_; 
v___f_1260_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1261_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1260_, v_inst_1253_, v_inst_1254_, v_m_u2081_1255_, v_m_u2082_1256_);
return v___x_1261_;
}
else
{
lean_object* v___x_1262_; lean_object* v___f_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_box(v___x_1259_);
v___f_1263_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1263_, 0, v_inst_1253_);
lean_closure_set(v___f_1263_, 1, v_inst_1254_);
lean_closure_set(v___f_1263_, 2, v_m_u2082_1256_);
lean_closure_set(v___f_1263_, 3, v___x_1262_);
v___x_1264_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1263_, v_m_u2081_1255_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff___redArg(lean_object* v_inst_1265_, lean_object* v_inst_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1267_, 0, lean_box(0));
lean_closure_set(v___x_1267_, 1, v_inst_1265_);
lean_closure_set(v___x_1267_, 2, v_inst_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff(lean_object* v_00_u03b1_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1271_, 0, lean_box(0));
lean_closure_set(v___x_1271_, 1, v_inst_1269_);
lean_closure_set(v___x_1271_, 2, v_inst_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__0(lean_object* v_f_1272_, lean_object* v_x_1273_, lean_object* v_x_1274_, lean_object* v_x1_1275_, lean_object* v_x2_1276_, lean_object* v_x3_1277_){
_start:
{
lean_object* v_fst_1278_; lean_object* v_snd_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1293_; 
v_fst_1278_ = lean_ctor_get(v_x1_1275_, 0);
v_snd_1279_ = lean_ctor_get(v_x1_1275_, 1);
v_isSharedCheck_1293_ = !lean_is_exclusive(v_x1_1275_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1281_ = v_x1_1275_;
v_isShared_1282_ = v_isSharedCheck_1293_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_snd_1279_);
lean_inc(v_fst_1278_);
lean_dec(v_x1_1275_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1293_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
lean_inc(v_x2_1276_);
v___x_1283_ = lean_apply_1(v_f_1272_, v_x2_1276_);
v___x_1284_ = lean_unbox(v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
v___x_1285_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1273_, v_x_1274_, v_snd_1279_, v_x2_1276_, v_x3_1277_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1285_);
v___x_1287_ = v___x_1281_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_fst_1278_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1273_, v_x_1274_, v_fst_1278_, v_x2_1276_, v_x3_1277_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 0, v___x_1289_);
v___x_1291_ = v___x_1281_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
lean_ctor_set(v_reuseFailAlloc_1292_, 1, v_snd_1279_);
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
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__1(lean_object* v___x_1294_, lean_object* v___f_1295_, lean_object* v_acc_1296_, lean_object* v_l_1297_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1294_, v___f_1295_, v_acc_1296_, v_l_1297_);
return v___x_1298_;
}
}
static lean_object* _init_l_Std_HashSet_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1299_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg(lean_object* v_x_1301_, lean_object* v_x_1302_, lean_object* v_f_1303_, lean_object* v_m_1304_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v_buckets_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1307_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1308_ = lean_ctor_get(v_m_1304_, 1);
lean_inc_ref(v_buckets_1308_);
lean_dec_ref(v_m_1304_);
v___x_1309_ = lean_array_get_size(v_buckets_1308_);
v___x_1310_ = lean_nat_dec_lt(v___x_1305_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_dec_ref(v_buckets_1308_);
lean_dec_ref(v_f_1303_);
lean_dec_ref(v_x_1302_);
lean_dec_ref(v_x_1301_);
return v___x_1306_;
}
else
{
lean_object* v___f_1311_; lean_object* v___f_1312_; size_t v___x_1313_; size_t v___x_1314_; lean_object* v___x_1315_; lean_object* v_fst_1316_; lean_object* v_snd_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
v___f_1311_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1311_, 0, v_f_1303_);
lean_closure_set(v___f_1311_, 1, v_x_1301_);
lean_closure_set(v___f_1311_, 2, v_x_1302_);
v___f_1312_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1312_, 0, v___x_1307_);
lean_closure_set(v___f_1312_, 1, v___f_1311_);
v___x_1313_ = ((size_t)0ULL);
v___x_1314_ = lean_usize_of_nat(v___x_1309_);
v___x_1315_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1307_, v___f_1312_, v_buckets_1308_, v___x_1313_, v___x_1314_, v___x_1306_);
v_fst_1316_ = lean_ctor_get(v___x_1315_, 0);
v_snd_1317_ = lean_ctor_get(v___x_1315_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1315_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_snd_1317_);
lean_inc(v_fst_1316_);
lean_dec(v___x_1315_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_fst_1316_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_snd_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition(lean_object* v_00_u03b1_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_, lean_object* v_f_1328_, lean_object* v_m_1329_){
_start:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_buckets_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1332_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1333_ = lean_ctor_get(v_m_1329_, 1);
lean_inc_ref(v_buckets_1333_);
lean_dec_ref(v_m_1329_);
v___x_1334_ = lean_array_get_size(v_buckets_1333_);
v___x_1335_ = lean_nat_dec_lt(v___x_1330_, v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec_ref(v_buckets_1333_);
lean_dec_ref(v_f_1328_);
lean_dec_ref(v_x_1327_);
lean_dec_ref(v_x_1326_);
return v___x_1331_;
}
else
{
lean_object* v___f_1336_; lean_object* v___f_1337_; size_t v___x_1338_; size_t v___x_1339_; lean_object* v___x_1340_; lean_object* v_fst_1341_; lean_object* v_snd_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1349_; 
v___f_1336_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1336_, 0, v_f_1328_);
lean_closure_set(v___f_1336_, 1, v_x_1326_);
lean_closure_set(v___f_1336_, 2, v_x_1327_);
v___f_1337_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1337_, 0, v___x_1332_);
lean_closure_set(v___f_1337_, 1, v___f_1336_);
v___x_1338_ = ((size_t)0ULL);
v___x_1339_ = lean_usize_of_nat(v___x_1334_);
v___x_1340_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1332_, v___f_1337_, v_buckets_1333_, v___x_1338_, v___x_1339_, v___x_1331_);
v_fst_1341_ = lean_ctor_get(v___x_1340_, 0);
v_snd_1342_ = lean_ctor_get(v___x_1340_, 1);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1344_ = v___x_1340_;
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snd_1342_);
lean_inc(v_fst_1341_);
lean_dec(v___x_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1349_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1347_; 
if (v_isShared_1345_ == 0)
{
v___x_1347_ = v___x_1344_;
goto v_reusejp_1346_;
}
else
{
lean_object* v_reuseFailAlloc_1348_; 
v_reuseFailAlloc_1348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_fst_1341_);
lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_snd_1342_);
v___x_1347_ = v_reuseFailAlloc_1348_;
goto v_reusejp_1346_;
}
v_reusejp_1346_:
{
return v___x_1347_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray___redArg(lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_l_1356_){
_start:
{
lean_object* v___f_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___f_1357_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1358_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_1359_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1357_, v_inst_1354_, v_inst_1355_, v___x_1358_, v_l_1356_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray(lean_object* v_00_u03b1_1360_, lean_object* v_inst_1361_, lean_object* v_inst_1362_, lean_object* v_l_1363_){
_start:
{
lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; 
v___f_1364_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1365_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___redArg___closed__1);
v___x_1366_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1364_, v_inst_1361_, v_inst_1362_, v___x_1365_, v_l_1363_);
return v___x_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg(lean_object* v_m_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg___boxed(lean_object* v_m_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Std_HashSet_Internal_numBuckets___redArg(v_m_1369_);
lean_dec_ref(v_m_1369_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets(lean_object* v_00_u03b1_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_m_1374_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1374_);
return v___x_1375_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1376_, lean_object* v_x_1377_, lean_object* v_x_1378_, lean_object* v_m_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_HashSet_Internal_numBuckets(v_00_u03b1_1376_, v_x_1377_, v_x_1378_, v_m_1379_);
lean_dec_ref(v_m_1379_);
lean_dec_ref(v_x_1378_);
lean_dec_ref(v_x_1377_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2(lean_object* v_inst_1384_, lean_object* v___f_1385_, lean_object* v_m_1386_, lean_object* v_prec_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v_buckets_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1409_; 
v___x_1388_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__9));
v_buckets_1389_ = lean_ctor_get(v_m_1386_, 1);
v_isSharedCheck_1409_ = !lean_is_exclusive(v_m_1386_);
if (v_isSharedCheck_1409_ == 0)
{
lean_object* v_unused_1410_; 
v_unused_1410_ = lean_ctor_get(v_m_1386_, 0);
lean_dec(v_unused_1410_);
v___x_1391_ = v_m_1386_;
v_isShared_1392_ = v_isSharedCheck_1409_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_buckets_1389_);
lean_dec(v_m_1386_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1409_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1393_; lean_object* v___y_1395_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; uint8_t v___x_1404_; 
v___x_1393_ = ((lean_object*)(l_Std_HashSet_instRepr___redArg___lam__2___closed__1));
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_array_get_size(v_buckets_1389_);
v___x_1403_ = lean_unsigned_to_nat(0u);
v___x_1404_ = lean_nat_dec_lt(v___x_1403_, v___x_1402_);
if (v___x_1404_ == 0)
{
lean_dec_ref(v_buckets_1389_);
lean_dec_ref(v___f_1385_);
v___y_1395_ = v___x_1401_;
goto v___jp_1394_;
}
else
{
lean_object* v___f_1405_; size_t v___x_1406_; size_t v___x_1407_; lean_object* v___x_1408_; 
v___f_1405_ = lean_alloc_closure((void*)(l_Std_HashSet_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1405_, 0, v___x_1388_);
lean_closure_set(v___f_1405_, 1, v___f_1385_);
v___x_1406_ = lean_usize_of_nat(v___x_1402_);
v___x_1407_ = ((size_t)0ULL);
v___x_1408_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1388_, v___f_1405_, v_buckets_1389_, v___x_1406_, v___x_1407_, v___x_1401_);
v___y_1395_ = v___x_1408_;
goto v___jp_1394_;
}
v___jp_1394_:
{
lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1396_ = l_List_repr___redArg(v_inst_1384_, v___y_1395_);
if (v_isShared_1392_ == 0)
{
lean_ctor_set_tag(v___x_1391_, 5);
lean_ctor_set(v___x_1391_, 1, v___x_1396_);
lean_ctor_set(v___x_1391_, 0, v___x_1393_);
v___x_1398_ = v___x_1391_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1400_; 
v_reuseFailAlloc_1400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1400_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1400_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1400_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Repr_addAppParen(v___x_1398_, v_prec_1387_);
return v___x_1399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1411_, lean_object* v___f_1412_, lean_object* v_m_1413_, lean_object* v_prec_1414_){
_start:
{
lean_object* v_res_1415_; 
v_res_1415_ = l_Std_HashSet_instRepr___redArg___lam__2(v_inst_1411_, v___f_1412_, v_m_1413_, v_prec_1414_);
lean_dec(v_prec_1414_);
return v_res_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg(lean_object* v_inst_1416_){
_start:
{
lean_object* v___f_1417_; lean_object* v___f_1418_; 
v___f_1417_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___f_1418_ = lean_alloc_closure((void*)(l_Std_HashSet_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1418_, 0, v_inst_1416_);
lean_closure_set(v___f_1418_, 1, v___f_1417_);
return v___f_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr(lean_object* v_00_u03b1_1419_, lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Std_HashSet_instRepr___redArg(v_inst_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___boxed(lean_object* v_00_u03b1_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_inst_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Std_HashSet_instRepr(v_00_u03b1_1424_, v_inst_1425_, v_inst_1426_, v_inst_1427_);
lean_dec_ref(v_inst_1426_);
lean_dec_ref(v_inst_1425_);
return v_res_1428_;
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
