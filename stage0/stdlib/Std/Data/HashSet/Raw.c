// Lean compiler output
// Module: Std.Data.HashSet.Raw
// Imports: public import Std.Data.HashMap.Raw
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
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_Raw_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_HashSet_Raw_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instEmptyCollection___closed__1;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited(lean_object*);
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__0 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HashSet"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__1 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__2 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__2_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__3 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__3_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_0),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 195, 212, 176, 236, 184, 63, 58)}};
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_1),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(186, 185, 85, 79, 168, 190, 254, 250)}};
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_2),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(84, 53, 251, 222, 148, 252, 181, 241)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__4 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__4_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__5 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__5_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__6 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__6_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__7 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__7_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__7_value)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__8 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__8_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__9 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__10 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__10_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__11 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__6_value),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__8_value),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__12 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__12_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__4_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__12_value)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__13 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Std_HashSet_Raw_term___x7em__ = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__13_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_0),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_1),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_2),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value;
static lean_once_cell_t l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_0),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 195, 212, 176, 236, 184, 63, 58)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_1),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(186, 185, 85, 79, 168, 190, 254, 250)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_2),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(149, 151, 195, 206, 178, 68, 5, 119)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__1_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__2 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__2_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__3 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__3_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__4 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__4_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__5 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__5_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__6 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__6_value;
static const lean_ctor_object l_Std_HashSet_Raw_toList___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__0_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__1_value)}};
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__7 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__7_value;
static const lean_ctor_object l_Std_HashSet_Raw_toList___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__7_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__2_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__3_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__4_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__5_value)}};
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__8 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__8_value;
static const lean_ctor_object l_Std_HashSet_Raw_toList___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__8_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__6_value)}};
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__9 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__9_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_Raw_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__10 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__10_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_Raw_toList___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__9_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__10_value)} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__11 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList(lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_Raw_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__9_value)} };
static const lean_object* l_Std_HashSet_Raw_ofList___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_Raw_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashSet_Raw_ofList___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_Raw_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_Raw_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_Raw_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toArray___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_toArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_Raw_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_Raw_toArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__9_value),((lean_object*)&l_Std_HashSet_Raw_toArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashSet_Raw_toArray___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_Raw_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_Raw_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__9_value)} };
static const lean_object* l_Std_HashSet_Raw_union___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_Raw_beq___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_beq___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_HashSet_Raw_all___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet_Raw_all___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_all___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_Raw_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__9_value)} };
static const lean_object* l_Std_HashSet_Raw_ofArray___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_ofArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_Raw_ofArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_ofArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashSet_Raw_ofArray___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_Raw_ofArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.HashSet.Raw.ofList "};
static const lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_HashSet_Raw_emptyWithCapacity___redArg(v_capacity_11_);
lean_dec(v_capacity_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity(lean_object* v_00_u03b1_13_, lean_object* v_capacity_14_){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_15_ = lean_unsigned_to_nat(0u);
v___x_16_ = lean_unsigned_to_nat(4u);
v___x_17_ = lean_nat_mul(v_capacity_14_, v___x_16_);
v___x_18_ = lean_unsigned_to_nat(3u);
v___x_19_ = lean_nat_div(v___x_17_, v___x_18_);
lean_dec(v___x_17_);
v___x_20_ = l_Nat_nextPowerOfTwo(v___x_19_);
lean_dec(v___x_19_);
v___x_21_ = lean_box(0);
v___x_22_ = lean_mk_array(v___x_20_, v___x_21_);
v___x_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_23_, 0, v___x_15_);
lean_ctor_set(v___x_23_, 1, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___boxed(lean_object* v_00_u03b1_24_, lean_object* v_capacity_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Std_HashSet_Raw_emptyWithCapacity(v_00_u03b1_24_, v_capacity_25_);
lean_dec(v_capacity_25_);
return v_res_26_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_box(0);
v___x_28_ = lean_unsigned_to_nat(16u);
v___x_29_ = lean_mk_array(v___x_28_, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__0, &l_Std_HashSet_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___x_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection(lean_object* v_00_u03b1_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited(lean_object* v_00_u03b1_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
return v___x_36_;
}
}
static lean_object* _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5));
v___x_78_ = l_String_toRawSubstring_x27(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(lean_object* v_x_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v___x_103_; uint8_t v___x_104_; 
v___x_103_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__4));
lean_inc(v_x_100_);
v___x_104_ = l_Lean_Syntax_isOfKind(v_x_100_, v___x_103_);
if (v___x_104_ == 0)
{
lean_object* v___x_105_; lean_object* v___x_106_; 
lean_dec(v_x_100_);
v___x_105_ = lean_box(1);
v___x_106_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
lean_ctor_set(v___x_106_, 1, v_a_102_);
return v___x_106_;
}
else
{
lean_object* v_quotContext_107_; lean_object* v_currMacroScope_108_; lean_object* v_ref_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_quotContext_107_ = lean_ctor_get(v_a_101_, 1);
v_currMacroScope_108_ = lean_ctor_get(v_a_101_, 2);
v_ref_109_ = lean_ctor_get(v_a_101_, 5);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = l_Lean_Syntax_getArg(v_x_100_, v___x_110_);
v___x_112_ = lean_unsigned_to_nat(2u);
v___x_113_ = l_Lean_Syntax_getArg(v_x_100_, v___x_112_);
lean_dec(v_x_100_);
v___x_114_ = 0;
v___x_115_ = l_Lean_SourceInfo_fromRef(v_ref_109_, v___x_114_);
v___x_116_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4));
v___x_117_ = lean_obj_once(&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6, &l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6);
v___x_118_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_108_);
lean_inc(v_quotContext_107_);
v___x_119_ = l_Lean_addMacroScope(v_quotContext_107_, v___x_118_, v_currMacroScope_108_);
v___x_120_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12));
lean_inc_n(v___x_115_, 2);
v___x_121_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_121_, 0, v___x_115_);
lean_ctor_set(v___x_121_, 1, v___x_117_);
lean_ctor_set(v___x_121_, 2, v___x_119_);
lean_ctor_set(v___x_121_, 3, v___x_120_);
v___x_122_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14));
v___x_123_ = l_Lean_Syntax_node2(v___x_115_, v___x_122_, v___x_111_, v___x_113_);
v___x_124_ = l_Lean_Syntax_node2(v___x_115_, v___x_116_, v___x_121_, v___x_123_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_a_102_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___boxed(lean_object* v_x_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(v_x_126_, v_a_127_, v_a_128_);
lean_dec_ref(v_a_127_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(lean_object* v_x_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4));
lean_inc(v_x_133_);
v___x_137_ = l_Lean_Syntax_isOfKind(v_x_133_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v_x_133_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_a_135_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = l_Lean_Syntax_getArg(v_x_133_, v___x_140_);
v___x_142_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1));
lean_inc(v___x_141_);
v___x_143_ = l_Lean_Syntax_isOfKind(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v___x_141_);
lean_dec(v_x_133_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_a_135_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_146_ = lean_unsigned_to_nat(1u);
v___x_147_ = l_Lean_Syntax_getArg(v_x_133_, v___x_146_);
lean_dec(v_x_133_);
v___x_148_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_147_);
v___x_149_ = l_Lean_Syntax_matchesNull(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v___x_147_);
lean_dec(v___x_141_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_a_135_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_ref_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_152_ = l_Lean_Syntax_getArg(v___x_147_, v___x_140_);
v___x_153_ = l_Lean_Syntax_getArg(v___x_147_, v___x_146_);
lean_dec(v___x_147_);
v_ref_154_ = l_Lean_replaceRef(v___x_141_, v_a_134_);
lean_dec(v___x_141_);
v___x_155_ = 0;
v___x_156_ = l_Lean_SourceInfo_fromRef(v_ref_154_, v___x_155_);
lean_dec(v_ref_154_);
v___x_157_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__4));
v___x_158_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__7));
lean_inc(v___x_156_);
v___x_159_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_156_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = l_Lean_Syntax_node3(v___x_156_, v___x_157_, v___x_152_, v___x_159_, v___x_153_);
v___x_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v_a_135_);
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___boxed(lean_object* v_x_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(v_x_162_, v_a_163_, v_a_164_);
lean_dec(v_a_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert___redArg(lean_object* v_inst_166_, lean_object* v_inst_167_, lean_object* v_m_168_, lean_object* v_a_169_){
_start:
{
lean_object* v_buckets_170_; lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; 
v_buckets_170_ = lean_ctor_get(v_m_168_, 1);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_array_get_size(v_buckets_170_);
v___x_173_ = lean_nat_dec_lt(v___x_171_, v___x_172_);
if (v___x_173_ == 0)
{
lean_dec(v_a_169_);
lean_dec_ref(v_inst_167_);
lean_dec_ref(v_inst_166_);
return v_m_168_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_box(0);
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_166_, v_inst_167_, v_m_168_, v_a_169_, v___x_174_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert(lean_object* v_00_u03b1_176_, lean_object* v_inst_177_, lean_object* v_inst_178_, lean_object* v_m_179_, lean_object* v_a_180_){
_start:
{
lean_object* v_buckets_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_buckets_181_ = lean_ctor_get(v_m_179_, 1);
v___x_182_ = lean_unsigned_to_nat(0u);
v___x_183_ = lean_array_get_size(v_buckets_181_);
v___x_184_ = lean_nat_dec_lt(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_dec(v_a_180_);
lean_dec_ref(v_inst_178_);
lean_dec_ref(v_inst_177_);
return v_m_179_;
}
else
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_box(0);
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_177_, v_inst_178_, v_m_179_, v_a_180_, v___x_185_);
return v___x_186_;
}
}
}
static lean_object* _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__0, &l_Std_HashSet_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0);
v___x_188_ = lean_array_get_size(v___x_187_);
return v___x_188_;
}
}
static uint8_t _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_189_ = lean_obj_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_190_ = lean_unsigned_to_nat(0u);
v___x_191_ = lean_nat_dec_lt(v___x_190_, v___x_189_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_196_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_196_ == 0)
{
lean_dec(v_a_194_);
lean_dec_ref(v_inst_193_);
lean_dec_ref(v_inst_192_);
return v___x_195_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_box(0);
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_192_, v_inst_193_, v___x_195_, v_a_194_, v___x_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg(lean_object* v_inst_199_, lean_object* v_inst_200_){
_start:
{
lean_object* v___f_201_; 
v___f_201_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_201_, 0, v_inst_199_);
lean_closure_set(v___f_201_, 1, v_inst_200_);
return v___f_201_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable(lean_object* v_00_u03b1_202_, lean_object* v_inst_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v___f_205_; 
v___f_205_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_205_, 0, v_inst_203_);
lean_closure_set(v___f_205_, 1, v_inst_204_);
return v___f_205_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_a_208_, lean_object* v_s_209_){
_start:
{
lean_object* v_buckets_210_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
v_buckets_210_ = lean_ctor_get(v_s_209_, 1);
v___x_211_ = lean_unsigned_to_nat(0u);
v___x_212_ = lean_array_get_size(v_buckets_210_);
v___x_213_ = lean_nat_dec_lt(v___x_211_, v___x_212_);
if (v___x_213_ == 0)
{
lean_dec(v_a_208_);
lean_dec_ref(v_inst_207_);
lean_dec_ref(v_inst_206_);
return v_s_209_;
}
else
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_box(0);
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_206_, v_inst_207_, v_s_209_, v_a_208_, v___x_214_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg(lean_object* v_inst_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___f_218_; 
v___f_218_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_218_, 0, v_inst_216_);
lean_closure_set(v___f_218_, 1, v_inst_217_);
return v___f_218_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable(lean_object* v_00_u03b1_219_, lean_object* v_inst_220_, lean_object* v_inst_221_){
_start:
{
lean_object* v___f_222_; 
v___f_222_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_222_, 0, v_inst_220_);
lean_closure_set(v___f_222_, 1, v_inst_221_);
return v___f_222_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert___redArg(lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_m_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_size_227_; lean_object* v_buckets_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_size_227_ = lean_ctor_get(v_m_225_, 0);
v_buckets_228_ = lean_ctor_get(v_m_225_, 1);
v___x_229_ = lean_unsigned_to_nat(0u);
v___x_230_ = lean_array_get_size(v_buckets_228_);
v___x_231_ = lean_nat_dec_lt(v___x_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_a_226_);
lean_dec_ref(v_inst_224_);
lean_dec_ref(v_inst_223_);
v___x_232_ = lean_box(v___x_231_);
v___x_233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_232_);
lean_ctor_set(v___x_233_, 1, v_m_225_);
return v___x_233_;
}
else
{
lean_object* v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v_fold_239_; uint64_t v___x_240_; uint64_t v___x_241_; uint64_t v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; lean_object* v_bkt_248_; uint8_t v___x_249_; 
lean_inc_ref(v_inst_224_);
lean_inc_n(v_a_226_, 2);
v___x_234_ = lean_apply_1(v_inst_224_, v_a_226_);
v___x_235_ = 32ULL;
v___x_236_ = lean_unbox_uint64(v___x_234_);
v___x_237_ = lean_uint64_shift_right(v___x_236_, v___x_235_);
v___x_238_ = lean_unbox_uint64(v___x_234_);
lean_dec_ref(v___x_234_);
v_fold_239_ = lean_uint64_xor(v___x_238_, v___x_237_);
v___x_240_ = 16ULL;
v___x_241_ = lean_uint64_shift_right(v_fold_239_, v___x_240_);
v___x_242_ = lean_uint64_xor(v_fold_239_, v___x_241_);
v___x_243_ = lean_uint64_to_usize(v___x_242_);
v___x_244_ = lean_usize_of_nat(v___x_230_);
v___x_245_ = ((size_t)1ULL);
v___x_246_ = lean_usize_sub(v___x_244_, v___x_245_);
v___x_247_ = lean_usize_land(v___x_243_, v___x_246_);
v_bkt_248_ = lean_array_uget_borrowed(v_buckets_228_, v___x_247_);
lean_inc(v_bkt_248_);
v___x_249_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_223_, v_a_226_, v_bkt_248_);
if (v___x_249_ == 0)
{
lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_275_; 
lean_inc_ref(v_buckets_228_);
lean_inc(v_size_227_);
v_isSharedCheck_275_ = !lean_is_exclusive(v_m_225_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; lean_object* v_unused_277_; 
v_unused_276_ = lean_ctor_get(v_m_225_, 1);
lean_dec(v_unused_276_);
v_unused_277_ = lean_ctor_get(v_m_225_, 0);
lean_dec(v_unused_277_);
v___x_251_ = v_m_225_;
v_isShared_252_ = v_isSharedCheck_275_;
goto v_resetjp_250_;
}
else
{
lean_dec(v_m_225_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_275_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v_size_x27_255_; lean_object* v___x_256_; lean_object* v_buckets_x27_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_253_ = lean_box(0);
v___x_254_ = lean_unsigned_to_nat(1u);
v_size_x27_255_ = lean_nat_add(v_size_227_, v___x_254_);
lean_dec(v_size_227_);
lean_inc(v_bkt_248_);
v___x_256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_256_, 0, v_a_226_);
lean_ctor_set(v___x_256_, 1, v___x_253_);
lean_ctor_set(v___x_256_, 2, v_bkt_248_);
v_buckets_x27_257_ = lean_array_uset(v_buckets_228_, v___x_247_, v___x_256_);
v___x_258_ = lean_unsigned_to_nat(4u);
v___x_259_ = lean_nat_mul(v_size_x27_255_, v___x_258_);
v___x_260_ = lean_unsigned_to_nat(3u);
v___x_261_ = lean_nat_div(v___x_259_, v___x_260_);
lean_dec(v___x_259_);
v___x_262_ = lean_array_get_size(v_buckets_x27_257_);
v___x_263_ = lean_nat_dec_le(v___x_261_, v___x_262_);
lean_dec(v___x_261_);
if (v___x_263_ == 0)
{
lean_object* v_val_264_; lean_object* v___x_266_; 
v_val_264_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_224_, v_buckets_x27_257_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_val_264_);
lean_ctor_set(v___x_251_, 0, v_size_x27_255_);
v___x_266_ = v___x_251_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_size_x27_255_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v_val_264_);
v___x_266_ = v_reuseFailAlloc_269_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_box(v___x_249_);
v___x_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
return v___x_268_;
}
}
else
{
lean_object* v___x_271_; 
lean_dec_ref(v_inst_224_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_buckets_x27_257_);
lean_ctor_set(v___x_251_, 0, v_size_x27_255_);
v___x_271_ = v___x_251_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_size_x27_255_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_buckets_x27_257_);
v___x_271_ = v_reuseFailAlloc_274_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_272_ = lean_box(v___x_249_);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
return v___x_273_;
}
}
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; 
lean_dec(v_a_226_);
lean_dec_ref(v_inst_224_);
v___x_278_ = lean_box(v___x_249_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v_m_225_);
return v___x_279_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert(lean_object* v_00_u03b1_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_m_283_, lean_object* v_a_284_){
_start:
{
lean_object* v_size_285_; lean_object* v_buckets_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; 
v_size_285_ = lean_ctor_get(v_m_283_, 0);
v_buckets_286_ = lean_ctor_get(v_m_283_, 1);
v___x_287_ = lean_unsigned_to_nat(0u);
v___x_288_ = lean_array_get_size(v_buckets_286_);
v___x_289_ = lean_nat_dec_lt(v___x_287_, v___x_288_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec(v_a_284_);
lean_dec_ref(v_inst_282_);
lean_dec_ref(v_inst_281_);
v___x_290_ = lean_box(v___x_289_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_m_283_);
return v___x_291_;
}
else
{
lean_object* v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v_fold_297_; uint64_t v___x_298_; uint64_t v___x_299_; uint64_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; lean_object* v_bkt_306_; uint8_t v___x_307_; 
lean_inc_ref(v_inst_282_);
lean_inc_n(v_a_284_, 2);
v___x_292_ = lean_apply_1(v_inst_282_, v_a_284_);
v___x_293_ = 32ULL;
v___x_294_ = lean_unbox_uint64(v___x_292_);
v___x_295_ = lean_uint64_shift_right(v___x_294_, v___x_293_);
v___x_296_ = lean_unbox_uint64(v___x_292_);
lean_dec_ref(v___x_292_);
v_fold_297_ = lean_uint64_xor(v___x_296_, v___x_295_);
v___x_298_ = 16ULL;
v___x_299_ = lean_uint64_shift_right(v_fold_297_, v___x_298_);
v___x_300_ = lean_uint64_xor(v_fold_297_, v___x_299_);
v___x_301_ = lean_uint64_to_usize(v___x_300_);
v___x_302_ = lean_usize_of_nat(v___x_288_);
v___x_303_ = ((size_t)1ULL);
v___x_304_ = lean_usize_sub(v___x_302_, v___x_303_);
v___x_305_ = lean_usize_land(v___x_301_, v___x_304_);
v_bkt_306_ = lean_array_uget_borrowed(v_buckets_286_, v___x_305_);
lean_inc(v_bkt_306_);
v___x_307_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_281_, v_a_284_, v_bkt_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_333_; 
lean_inc_ref(v_buckets_286_);
lean_inc(v_size_285_);
v_isSharedCheck_333_ = !lean_is_exclusive(v_m_283_);
if (v_isSharedCheck_333_ == 0)
{
lean_object* v_unused_334_; lean_object* v_unused_335_; 
v_unused_334_ = lean_ctor_get(v_m_283_, 1);
lean_dec(v_unused_334_);
v_unused_335_ = lean_ctor_get(v_m_283_, 0);
lean_dec(v_unused_335_);
v___x_309_ = v_m_283_;
v_isShared_310_ = v_isSharedCheck_333_;
goto v_resetjp_308_;
}
else
{
lean_dec(v_m_283_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_333_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v_size_x27_313_; lean_object* v___x_314_; lean_object* v_buckets_x27_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_311_ = lean_box(0);
v___x_312_ = lean_unsigned_to_nat(1u);
v_size_x27_313_ = lean_nat_add(v_size_285_, v___x_312_);
lean_dec(v_size_285_);
lean_inc(v_bkt_306_);
v___x_314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_314_, 0, v_a_284_);
lean_ctor_set(v___x_314_, 1, v___x_311_);
lean_ctor_set(v___x_314_, 2, v_bkt_306_);
v_buckets_x27_315_ = lean_array_uset(v_buckets_286_, v___x_305_, v___x_314_);
v___x_316_ = lean_unsigned_to_nat(4u);
v___x_317_ = lean_nat_mul(v_size_x27_313_, v___x_316_);
v___x_318_ = lean_unsigned_to_nat(3u);
v___x_319_ = lean_nat_div(v___x_317_, v___x_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_array_get_size(v_buckets_x27_315_);
v___x_321_ = lean_nat_dec_le(v___x_319_, v___x_320_);
lean_dec(v___x_319_);
if (v___x_321_ == 0)
{
lean_object* v_val_322_; lean_object* v___x_324_; 
v_val_322_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_282_, v_buckets_x27_315_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v_val_322_);
lean_ctor_set(v___x_309_, 0, v_size_x27_313_);
v___x_324_ = v___x_309_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_size_x27_313_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_val_322_);
v___x_324_ = v_reuseFailAlloc_327_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_box(v___x_307_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
return v___x_326_;
}
}
else
{
lean_object* v___x_329_; 
lean_dec_ref(v_inst_282_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v_buckets_x27_315_);
lean_ctor_set(v___x_309_, 0, v_size_x27_313_);
v___x_329_ = v___x_309_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_size_x27_313_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_buckets_x27_315_);
v___x_329_ = v_reuseFailAlloc_332_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_box(v___x_307_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
return v___x_331_;
}
}
}
}
else
{
lean_object* v___x_336_; lean_object* v___x_337_; 
lean_dec(v_a_284_);
lean_dec_ref(v_inst_282_);
v___x_336_ = lean_box(v___x_307_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v_m_283_);
return v___x_337_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains___redArg(lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_m_340_, lean_object* v_a_341_){
_start:
{
lean_object* v_buckets_342_; lean_object* v___x_343_; lean_object* v___x_344_; uint8_t v___x_345_; 
v_buckets_342_ = lean_ctor_get(v_m_340_, 1);
v___x_343_ = lean_unsigned_to_nat(0u);
v___x_344_ = lean_array_get_size(v_buckets_342_);
v___x_345_ = lean_nat_dec_lt(v___x_343_, v___x_344_);
if (v___x_345_ == 0)
{
lean_dec(v_a_341_);
lean_dec_ref(v_inst_339_);
lean_dec_ref(v_inst_338_);
return v___x_345_;
}
else
{
uint8_t v___x_346_; 
v___x_346_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_338_, v_inst_339_, v_m_340_, v_a_341_);
return v___x_346_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___redArg___boxed(lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_m_349_, lean_object* v_a_350_){
_start:
{
uint8_t v_res_351_; lean_object* v_r_352_; 
v_res_351_ = l_Std_HashSet_Raw_contains___redArg(v_inst_347_, v_inst_348_, v_m_349_, v_a_350_);
lean_dec_ref(v_m_349_);
v_r_352_ = lean_box(v_res_351_);
return v_r_352_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains(lean_object* v_00_u03b1_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_m_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_buckets_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_buckets_358_ = lean_ctor_get(v_m_356_, 1);
v___x_359_ = lean_unsigned_to_nat(0u);
v___x_360_ = lean_array_get_size(v_buckets_358_);
v___x_361_ = lean_nat_dec_lt(v___x_359_, v___x_360_);
if (v___x_361_ == 0)
{
lean_dec(v_a_357_);
lean_dec_ref(v_inst_355_);
lean_dec_ref(v_inst_354_);
return v___x_361_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_354_, v_inst_355_, v_m_356_, v_a_357_);
return v___x_362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___boxed(lean_object* v_00_u03b1_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_m_366_, lean_object* v_a_367_){
_start:
{
uint8_t v_res_368_; lean_object* v_r_369_; 
v_res_368_ = l_Std_HashSet_Raw_contains(v_00_u03b1_363_, v_inst_364_, v_inst_365_, v_m_366_, v_a_367_);
lean_dec_ref(v_m_366_);
v_r_369_ = lean_box(v_res_368_);
return v_r_369_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_370_, lean_object* v_inst_371_, lean_object* v_inst_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = lean_box(0);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_374_, lean_object* v_inst_375_, lean_object* v_inst_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_374_, v_inst_375_, v_inst_376_);
lean_dec_ref(v_inst_376_);
lean_dec_ref(v_inst_375_);
return v_res_377_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem___redArg(lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_m_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_buckets_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v_buckets_382_ = lean_ctor_get(v_m_380_, 1);
v___x_383_ = lean_unsigned_to_nat(0u);
v___x_384_ = lean_array_get_size(v_buckets_382_);
v___x_385_ = lean_nat_dec_lt(v___x_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_dec(v_a_381_);
lean_dec_ref(v_inst_379_);
lean_dec_ref(v_inst_378_);
return v___x_385_;
}
else
{
uint8_t v___x_386_; 
v___x_386_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_378_, v_inst_379_, v_m_380_, v_a_381_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_m_389_, lean_object* v_a_390_){
_start:
{
uint8_t v_res_391_; lean_object* v_r_392_; 
v_res_391_ = l_Std_HashSet_Raw_instDecidableMem___redArg(v_inst_387_, v_inst_388_, v_m_389_, v_a_390_);
lean_dec_ref(v_m_389_);
v_r_392_ = lean_box(v_res_391_);
return v_r_392_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem(lean_object* v_00_u03b1_393_, lean_object* v_inst_394_, lean_object* v_inst_395_, lean_object* v_m_396_, lean_object* v_a_397_){
_start:
{
uint8_t v___x_398_; 
v___x_398_ = l_Std_HashSet_Raw_instDecidableMem___redArg(v_inst_394_, v_inst_395_, v_m_396_, v_a_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_m_402_, lean_object* v_a_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Std_HashSet_Raw_instDecidableMem(v_00_u03b1_399_, v_inst_400_, v_inst_401_, v_m_402_, v_a_403_);
lean_dec_ref(v_m_402_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase___redArg(lean_object* v_inst_406_, lean_object* v_inst_407_, lean_object* v_m_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_buckets_410_; lean_object* v___x_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_buckets_410_ = lean_ctor_get(v_m_408_, 1);
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_array_get_size(v_buckets_410_);
v___x_413_ = lean_nat_dec_lt(v___x_411_, v___x_412_);
if (v___x_413_ == 0)
{
lean_dec(v_a_409_);
lean_dec_ref(v_inst_407_);
lean_dec_ref(v_inst_406_);
return v_m_408_;
}
else
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_406_, v_inst_407_, v_m_408_, v_a_409_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase(lean_object* v_00_u03b1_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_m_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_buckets_420_; lean_object* v___x_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_buckets_420_ = lean_ctor_get(v_m_418_, 1);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = lean_array_get_size(v_buckets_420_);
v___x_423_ = lean_nat_dec_lt(v___x_421_, v___x_422_);
if (v___x_423_ == 0)
{
lean_dec(v_a_419_);
lean_dec_ref(v_inst_417_);
lean_dec_ref(v_inst_416_);
return v_m_418_;
}
else
{
lean_object* v___x_424_; 
v___x_424_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_416_, v_inst_417_, v_m_418_, v_a_419_);
return v___x_424_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg(lean_object* v_m_425_){
_start:
{
lean_object* v_size_426_; 
v_size_426_ = lean_ctor_get(v_m_425_, 0);
lean_inc(v_size_426_);
return v_size_426_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg___boxed(lean_object* v_m_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_HashSet_Raw_size___redArg(v_m_427_);
lean_dec_ref(v_m_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size(lean_object* v_00_u03b1_429_, lean_object* v_m_430_){
_start:
{
lean_object* v_size_431_; 
v_size_431_ = lean_ctor_get(v_m_430_, 0);
lean_inc(v_size_431_);
return v_size_431_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___boxed(lean_object* v_00_u03b1_432_, lean_object* v_m_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Std_HashSet_Raw_size(v_00_u03b1_432_, v_m_433_);
lean_dec_ref(v_m_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg(lean_object* v_inst_435_, lean_object* v_inst_436_, lean_object* v_m_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_buckets_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_buckets_439_ = lean_ctor_get(v_m_437_, 1);
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_441_ = lean_array_get_size(v_buckets_439_);
v___x_442_ = lean_nat_dec_lt(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
lean_dec(v_a_438_);
lean_dec_ref(v_inst_436_);
lean_dec_ref(v_inst_435_);
v___x_443_ = lean_box(0);
return v___x_443_;
}
else
{
lean_object* v___x_444_; 
v___x_444_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_435_, v_inst_436_, v_m_437_, v_a_438_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg___boxed(lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_m_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_HashSet_Raw_get_x3f___redArg(v_inst_445_, v_inst_446_, v_m_447_, v_a_448_);
lean_dec_ref(v_m_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f(lean_object* v_00_u03b1_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_m_453_, lean_object* v_a_454_){
_start:
{
lean_object* v_buckets_455_; lean_object* v___x_456_; lean_object* v___x_457_; uint8_t v___x_458_; 
v_buckets_455_ = lean_ctor_get(v_m_453_, 1);
v___x_456_ = lean_unsigned_to_nat(0u);
v___x_457_ = lean_array_get_size(v_buckets_455_);
v___x_458_ = lean_nat_dec_lt(v___x_456_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; 
lean_dec(v_a_454_);
lean_dec_ref(v_inst_452_);
lean_dec_ref(v_inst_451_);
v___x_459_ = lean_box(0);
return v___x_459_;
}
else
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_451_, v_inst_452_, v_m_453_, v_a_454_);
return v___x_460_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___boxed(lean_object* v_00_u03b1_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_m_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_HashSet_Raw_get_x3f(v_00_u03b1_461_, v_inst_462_, v_inst_463_, v_m_464_, v_a_465_);
lean_dec_ref(v_m_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg(lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_m_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_467_, v_inst_468_, v_m_469_, v_a_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg___boxed(lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_m_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_HashSet_Raw_get___redArg(v_inst_472_, v_inst_473_, v_m_474_, v_a_475_);
lean_dec_ref(v_m_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get(lean_object* v_00_u03b1_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_m_480_, lean_object* v_a_481_, lean_object* v_h_482_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_478_, v_inst_479_, v_m_480_, v_a_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___boxed(lean_object* v_00_u03b1_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_m_487_, lean_object* v_a_488_, lean_object* v_h_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_HashSet_Raw_get(v_00_u03b1_484_, v_inst_485_, v_inst_486_, v_m_487_, v_a_488_, v_h_489_);
lean_dec_ref(v_m_487_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg(lean_object* v_inst_491_, lean_object* v_inst_492_, lean_object* v_m_493_, lean_object* v_a_494_, lean_object* v_fallback_495_){
_start:
{
lean_object* v_buckets_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_buckets_496_ = lean_ctor_get(v_m_493_, 1);
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = lean_array_get_size(v_buckets_496_);
v___x_499_ = lean_nat_dec_lt(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_dec(v_a_494_);
lean_dec_ref(v_inst_492_);
lean_dec_ref(v_inst_491_);
lean_inc(v_fallback_495_);
return v_fallback_495_;
}
else
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_491_, v_inst_492_, v_m_493_, v_a_494_, v_fallback_495_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg___boxed(lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_m_503_, lean_object* v_a_504_, lean_object* v_fallback_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_HashSet_Raw_getD___redArg(v_inst_501_, v_inst_502_, v_m_503_, v_a_504_, v_fallback_505_);
lean_dec(v_fallback_505_);
lean_dec_ref(v_m_503_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD(lean_object* v_00_u03b1_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_m_510_, lean_object* v_a_511_, lean_object* v_fallback_512_){
_start:
{
lean_object* v_buckets_513_; lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v_buckets_513_ = lean_ctor_get(v_m_510_, 1);
v___x_514_ = lean_unsigned_to_nat(0u);
v___x_515_ = lean_array_get_size(v_buckets_513_);
v___x_516_ = lean_nat_dec_lt(v___x_514_, v___x_515_);
if (v___x_516_ == 0)
{
lean_dec(v_a_511_);
lean_dec_ref(v_inst_509_);
lean_dec_ref(v_inst_508_);
lean_inc(v_fallback_512_);
return v_fallback_512_;
}
else
{
lean_object* v___x_517_; 
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_508_, v_inst_509_, v_m_510_, v_a_511_, v_fallback_512_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___boxed(lean_object* v_00_u03b1_518_, lean_object* v_inst_519_, lean_object* v_inst_520_, lean_object* v_m_521_, lean_object* v_a_522_, lean_object* v_fallback_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_HashSet_Raw_getD(v_00_u03b1_518_, v_inst_519_, v_inst_520_, v_m_521_, v_a_522_, v_fallback_523_);
lean_dec(v_fallback_523_);
lean_dec_ref(v_m_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg(lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_m_528_, lean_object* v_a_529_){
_start:
{
lean_object* v_buckets_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_buckets_530_ = lean_ctor_get(v_m_528_, 1);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_array_get_size(v_buckets_530_);
v___x_533_ = lean_nat_dec_lt(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec(v_a_529_);
lean_dec_ref(v_inst_526_);
lean_dec_ref(v_inst_525_);
lean_inc(v_inst_527_);
return v_inst_527_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_525_, v_inst_526_, v_inst_527_, v_m_528_, v_a_529_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg___boxed(lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_m_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_HashSet_Raw_get_x21___redArg(v_inst_535_, v_inst_536_, v_inst_537_, v_m_538_, v_a_539_);
lean_dec_ref(v_m_538_);
lean_dec(v_inst_537_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21(lean_object* v_00_u03b1_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_m_545_, lean_object* v_a_546_){
_start:
{
lean_object* v_buckets_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_buckets_547_ = lean_ctor_get(v_m_545_, 1);
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_array_get_size(v_buckets_547_);
v___x_550_ = lean_nat_dec_lt(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_dec(v_a_546_);
lean_dec_ref(v_inst_543_);
lean_dec_ref(v_inst_542_);
lean_inc(v_inst_544_);
return v_inst_544_;
}
else
{
lean_object* v___x_551_; 
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_542_, v_inst_543_, v_inst_544_, v_m_545_, v_a_546_);
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___boxed(lean_object* v_00_u03b1_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_inst_555_, lean_object* v_m_556_, lean_object* v_a_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_HashSet_Raw_get_x21(v_00_u03b1_552_, v_inst_553_, v_inst_554_, v_inst_555_, v_m_556_, v_a_557_);
lean_dec_ref(v_m_556_);
lean_dec(v_inst_555_);
return v_res_558_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty___redArg(lean_object* v_m_559_){
_start:
{
lean_object* v_size_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_size_560_ = lean_ctor_get(v_m_559_, 0);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_nat_dec_eq(v_size_560_, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___redArg___boxed(lean_object* v_m_563_){
_start:
{
uint8_t v_res_564_; lean_object* v_r_565_; 
v_res_564_ = l_Std_HashSet_Raw_isEmpty___redArg(v_m_563_);
lean_dec_ref(v_m_563_);
v_r_565_ = lean_box(v_res_564_);
return v_r_565_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty(lean_object* v_00_u03b1_566_, lean_object* v_m_567_){
_start:
{
lean_object* v_size_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_size_568_ = lean_ctor_get(v_m_567_, 0);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_nat_dec_eq(v_size_568_, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_571_, lean_object* v_m_572_){
_start:
{
uint8_t v_res_573_; lean_object* v_r_574_; 
v_res_573_ = l_Std_HashSet_Raw_isEmpty(v_00_u03b1_571_, v_m_572_);
lean_dec_ref(v_m_572_);
v_r_574_ = lean_box(v_res_573_);
return v_r_574_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__0(lean_object* v_a_575_, lean_object* v_b_576_, lean_object* v_d_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_578_, 0, v_a_575_);
lean_ctor_set(v___x_578_, 1, v_d_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__1(lean_object* v___x_579_, lean_object* v___f_580_, lean_object* v_l_581_, lean_object* v_acc_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_579_, v___f_580_, v_acc_582_, v_l_581_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg(lean_object* v_m_607_){
_start:
{
lean_object* v___x_608_; lean_object* v_buckets_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_608_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_609_ = lean_ctor_get(v_m_607_, 1);
lean_inc_ref(v_buckets_609_);
lean_dec_ref(v_m_607_);
v___x_610_ = lean_box(0);
v___x_611_ = lean_array_get_size(v_buckets_609_);
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = lean_nat_dec_lt(v___x_612_, v___x_611_);
if (v___x_613_ == 0)
{
lean_dec_ref(v_buckets_609_);
return v___x_610_;
}
else
{
lean_object* v___f_614_; size_t v___x_615_; size_t v___x_616_; lean_object* v___x_617_; 
v___f_614_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__11));
v___x_615_ = lean_usize_of_nat(v___x_611_);
v___x_616_ = ((size_t)0ULL);
v___x_617_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_608_, v___f_614_, v_buckets_609_, v___x_615_, v___x_616_, v___x_610_);
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList(lean_object* v_00_u03b1_618_, lean_object* v_m_619_){
_start:
{
lean_object* v___x_620_; lean_object* v_buckets_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v___x_620_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_621_ = lean_ctor_get(v_m_619_, 1);
lean_inc_ref(v_buckets_621_);
lean_dec_ref(v_m_619_);
v___x_622_ = lean_box(0);
v___x_623_ = lean_array_get_size(v_buckets_621_);
v___x_624_ = lean_unsigned_to_nat(0u);
v___x_625_ = lean_nat_dec_lt(v___x_624_, v___x_623_);
if (v___x_625_ == 0)
{
lean_dec_ref(v_buckets_621_);
return v___x_622_;
}
else
{
lean_object* v___f_626_; size_t v___x_627_; size_t v___x_628_; lean_object* v___x_629_; 
v___f_626_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__11));
v___x_627_ = lean_usize_of_nat(v___x_623_);
v___x_628_ = ((size_t)0ULL);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_620_, v___f_626_, v_buckets_621_, v___x_627_, v___x_628_, v___x_622_);
return v___x_629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList___redArg(lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_l_636_){
_start:
{
lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_637_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_638_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_638_ == 0)
{
lean_dec(v_l_636_);
lean_dec_ref(v_inst_635_);
lean_dec_ref(v_inst_634_);
return v___x_637_;
}
else
{
lean_object* v___f_639_; lean_object* v___x_640_; 
v___f_639_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_639_, v_inst_634_, v_inst_635_, v___x_637_, v_l_636_);
return v___x_640_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList(lean_object* v_00_u03b1_641_, lean_object* v_inst_642_, lean_object* v_inst_643_, lean_object* v_l_644_){
_start:
{
lean_object* v___x_645_; uint8_t v___x_646_; 
v___x_645_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_646_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_646_ == 0)
{
lean_dec(v_l_644_);
lean_dec_ref(v_inst_643_);
lean_dec_ref(v_inst_642_);
return v___x_645_;
}
else
{
lean_object* v___f_647_; lean_object* v___x_648_; 
v___f_647_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_647_, v_inst_642_, v_inst_643_, v___x_645_, v_l_644_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__0(lean_object* v_f_649_, lean_object* v_b_650_, lean_object* v_a_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = lean_apply_2(v_f_649_, v_b_650_, v_a_651_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__1(lean_object* v_inst_654_, lean_object* v___f_655_, lean_object* v_acc_656_, lean_object* v_l_657_){
_start:
{
lean_object* v___x_658_; 
v___x_658_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_654_, v___f_655_, v_acc_656_, v_l_657_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg(lean_object* v_inst_659_, lean_object* v_f_660_, lean_object* v_init_661_, lean_object* v_b_662_){
_start:
{
lean_object* v_buckets_663_; lean_object* v___x_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_buckets_663_ = lean_ctor_get(v_b_662_, 1);
lean_inc_ref(v_buckets_663_);
lean_dec_ref(v_b_662_);
v___x_664_ = lean_unsigned_to_nat(0u);
v___x_665_ = lean_array_get_size(v_buckets_663_);
v___x_666_ = lean_nat_dec_lt(v___x_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_object* v_toApplicative_667_; lean_object* v_toPure_668_; lean_object* v___x_669_; 
lean_dec_ref(v_buckets_663_);
lean_dec(v_f_660_);
v_toApplicative_667_ = lean_ctor_get(v_inst_659_, 0);
lean_inc_ref(v_toApplicative_667_);
lean_dec_ref(v_inst_659_);
v_toPure_668_ = lean_ctor_get(v_toApplicative_667_, 1);
lean_inc(v_toPure_668_);
lean_dec_ref(v_toApplicative_667_);
v___x_669_ = lean_apply_2(v_toPure_668_, lean_box(0), v_init_661_);
return v___x_669_;
}
else
{
lean_object* v___f_670_; lean_object* v___f_671_; uint8_t v___x_672_; 
v___f_670_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_670_, 0, v_f_660_);
lean_inc_ref(v_inst_659_);
v___f_671_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_671_, 0, v_inst_659_);
lean_closure_set(v___f_671_, 1, v___f_670_);
v___x_672_ = lean_nat_dec_le(v___x_665_, v___x_665_);
if (v___x_672_ == 0)
{
if (v___x_666_ == 0)
{
lean_object* v_toApplicative_673_; lean_object* v_toPure_674_; lean_object* v___x_675_; 
lean_dec_ref(v___f_671_);
lean_dec_ref(v_buckets_663_);
v_toApplicative_673_ = lean_ctor_get(v_inst_659_, 0);
lean_inc_ref(v_toApplicative_673_);
lean_dec_ref(v_inst_659_);
v_toPure_674_ = lean_ctor_get(v_toApplicative_673_, 1);
lean_inc(v_toPure_674_);
lean_dec_ref(v_toApplicative_673_);
v___x_675_ = lean_apply_2(v_toPure_674_, lean_box(0), v_init_661_);
return v___x_675_;
}
else
{
size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v___x_676_ = ((size_t)0ULL);
v___x_677_ = lean_usize_of_nat(v___x_665_);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_659_, v___f_671_, v_buckets_663_, v___x_676_, v___x_677_, v_init_661_);
return v___x_678_;
}
}
else
{
size_t v___x_679_; size_t v___x_680_; lean_object* v___x_681_; 
v___x_679_ = ((size_t)0ULL);
v___x_680_ = lean_usize_of_nat(v___x_665_);
v___x_681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_659_, v___f_671_, v_buckets_663_, v___x_679_, v___x_680_, v_init_661_);
return v___x_681_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM(lean_object* v_00_u03b1_682_, lean_object* v_m_683_, lean_object* v_inst_684_, lean_object* v_00_u03b2_685_, lean_object* v_f_686_, lean_object* v_init_687_, lean_object* v_b_688_){
_start:
{
lean_object* v_buckets_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_buckets_689_ = lean_ctor_get(v_b_688_, 1);
lean_inc_ref(v_buckets_689_);
lean_dec_ref(v_b_688_);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get_size(v_buckets_689_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v_toApplicative_693_; lean_object* v_toPure_694_; lean_object* v___x_695_; 
lean_dec_ref(v_buckets_689_);
lean_dec(v_f_686_);
v_toApplicative_693_ = lean_ctor_get(v_inst_684_, 0);
lean_inc_ref(v_toApplicative_693_);
lean_dec_ref(v_inst_684_);
v_toPure_694_ = lean_ctor_get(v_toApplicative_693_, 1);
lean_inc(v_toPure_694_);
lean_dec_ref(v_toApplicative_693_);
v___x_695_ = lean_apply_2(v_toPure_694_, lean_box(0), v_init_687_);
return v___x_695_;
}
else
{
lean_object* v___f_696_; lean_object* v___f_697_; uint8_t v___x_698_; 
v___f_696_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_696_, 0, v_f_686_);
lean_inc_ref(v_inst_684_);
v___f_697_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_697_, 0, v_inst_684_);
lean_closure_set(v___f_697_, 1, v___f_696_);
v___x_698_ = lean_nat_dec_le(v___x_691_, v___x_691_);
if (v___x_698_ == 0)
{
if (v___x_692_ == 0)
{
lean_object* v_toApplicative_699_; lean_object* v_toPure_700_; lean_object* v___x_701_; 
lean_dec_ref(v___f_697_);
lean_dec_ref(v_buckets_689_);
v_toApplicative_699_ = lean_ctor_get(v_inst_684_, 0);
lean_inc_ref(v_toApplicative_699_);
lean_dec_ref(v_inst_684_);
v_toPure_700_ = lean_ctor_get(v_toApplicative_699_, 1);
lean_inc(v_toPure_700_);
lean_dec_ref(v_toApplicative_699_);
v___x_701_ = lean_apply_2(v_toPure_700_, lean_box(0), v_init_687_);
return v___x_701_;
}
else
{
size_t v___x_702_; size_t v___x_703_; lean_object* v___x_704_; 
v___x_702_ = ((size_t)0ULL);
v___x_703_ = lean_usize_of_nat(v___x_691_);
v___x_704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_684_, v___f_697_, v_buckets_689_, v___x_702_, v___x_703_, v_init_687_);
return v___x_704_;
}
}
else
{
size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
v___x_705_ = ((size_t)0ULL);
v___x_706_ = lean_usize_of_nat(v___x_691_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_684_, v___f_697_, v_buckets_689_, v___x_705_, v___x_706_, v_init_687_);
return v___x_707_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__0(lean_object* v_f_708_, lean_object* v_x1_709_, lean_object* v_x2_710_, lean_object* v_x3_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = lean_apply_2(v_f_708_, v_x1_709_, v_x2_710_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__1(lean_object* v___x_713_, lean_object* v___f_714_, lean_object* v_acc_715_, lean_object* v_l_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_713_, v___f_714_, v_acc_715_, v_l_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg(lean_object* v_f_718_, lean_object* v_init_719_, lean_object* v_m_720_){
_start:
{
lean_object* v___x_721_; lean_object* v_buckets_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_721_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_722_ = lean_ctor_get(v_m_720_, 1);
lean_inc_ref(v_buckets_722_);
lean_dec_ref(v_m_720_);
v___x_723_ = lean_unsigned_to_nat(0u);
v___x_724_ = lean_array_get_size(v_buckets_722_);
v___x_725_ = lean_nat_dec_lt(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_dec_ref(v_buckets_722_);
lean_dec(v_f_718_);
return v_init_719_;
}
else
{
lean_object* v___f_726_; lean_object* v___f_727_; uint8_t v___x_728_; 
v___f_726_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_726_, 0, v_f_718_);
v___f_727_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_727_, 0, v___x_721_);
lean_closure_set(v___f_727_, 1, v___f_726_);
v___x_728_ = lean_nat_dec_le(v___x_724_, v___x_724_);
if (v___x_728_ == 0)
{
if (v___x_725_ == 0)
{
lean_dec_ref(v___f_727_);
lean_dec_ref(v_buckets_722_);
return v_init_719_;
}
else
{
size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
v___x_729_ = ((size_t)0ULL);
v___x_730_ = lean_usize_of_nat(v___x_724_);
v___x_731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_721_, v___f_727_, v_buckets_722_, v___x_729_, v___x_730_, v_init_719_);
return v___x_731_;
}
}
else
{
size_t v___x_732_; size_t v___x_733_; lean_object* v___x_734_; 
v___x_732_ = ((size_t)0ULL);
v___x_733_ = lean_usize_of_nat(v___x_724_);
v___x_734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_721_, v___f_727_, v_buckets_722_, v___x_732_, v___x_733_, v_init_719_);
return v___x_734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_f_737_, lean_object* v_init_738_, lean_object* v_m_739_){
_start:
{
lean_object* v___x_740_; lean_object* v_buckets_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_740_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_741_ = lean_ctor_get(v_m_739_, 1);
lean_inc_ref(v_buckets_741_);
lean_dec_ref(v_m_739_);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_array_get_size(v_buckets_741_);
v___x_744_ = lean_nat_dec_lt(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_dec_ref(v_buckets_741_);
lean_dec(v_f_737_);
return v_init_738_;
}
else
{
lean_object* v___f_745_; lean_object* v___f_746_; uint8_t v___x_747_; 
v___f_745_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_745_, 0, v_f_737_);
v___f_746_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_746_, 0, v___x_740_);
lean_closure_set(v___f_746_, 1, v___f_745_);
v___x_747_ = lean_nat_dec_le(v___x_743_, v___x_743_);
if (v___x_747_ == 0)
{
if (v___x_744_ == 0)
{
lean_dec_ref(v___f_746_);
lean_dec_ref(v_buckets_741_);
return v_init_738_;
}
else
{
size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_743_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_740_, v___f_746_, v_buckets_741_, v___x_748_, v___x_749_, v_init_738_);
return v___x_750_;
}
}
else
{
size_t v___x_751_; size_t v___x_752_; lean_object* v___x_753_; 
v___x_751_ = ((size_t)0ULL);
v___x_752_ = lean_usize_of_nat(v___x_743_);
v___x_753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_740_, v___f_746_, v_buckets_741_, v___x_751_, v___x_752_, v_init_738_);
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__0(lean_object* v_f_754_, lean_object* v_x_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = lean_apply_1(v_f_754_, v___y_756_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__1(lean_object* v_inst_759_, lean_object* v___f_760_, lean_object* v_x_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = lean_box(0);
v___x_764_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_759_, v___f_760_, v___x_763_, v___y_762_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg(lean_object* v_inst_765_, lean_object* v_f_766_, lean_object* v_b_767_){
_start:
{
lean_object* v_buckets_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v_buckets_768_ = lean_ctor_get(v_b_767_, 1);
lean_inc_ref(v_buckets_768_);
lean_dec_ref(v_b_767_);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_array_get_size(v_buckets_768_);
v___x_771_ = lean_box(0);
v___x_772_ = lean_nat_dec_lt(v___x_769_, v___x_770_);
if (v___x_772_ == 0)
{
lean_object* v_toApplicative_773_; lean_object* v_toPure_774_; lean_object* v___x_775_; 
lean_dec_ref(v_buckets_768_);
lean_dec(v_f_766_);
v_toApplicative_773_ = lean_ctor_get(v_inst_765_, 0);
lean_inc_ref(v_toApplicative_773_);
lean_dec_ref(v_inst_765_);
v_toPure_774_ = lean_ctor_get(v_toApplicative_773_, 1);
lean_inc(v_toPure_774_);
lean_dec_ref(v_toApplicative_773_);
v___x_775_ = lean_apply_2(v_toPure_774_, lean_box(0), v___x_771_);
return v___x_775_;
}
else
{
lean_object* v___f_776_; lean_object* v___f_777_; uint8_t v___x_778_; 
v___f_776_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_776_, 0, v_f_766_);
lean_inc_ref(v_inst_765_);
v___f_777_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_777_, 0, v_inst_765_);
lean_closure_set(v___f_777_, 1, v___f_776_);
v___x_778_ = lean_nat_dec_le(v___x_770_, v___x_770_);
if (v___x_778_ == 0)
{
if (v___x_772_ == 0)
{
lean_object* v_toApplicative_779_; lean_object* v_toPure_780_; lean_object* v___x_781_; 
lean_dec_ref(v___f_777_);
lean_dec_ref(v_buckets_768_);
v_toApplicative_779_ = lean_ctor_get(v_inst_765_, 0);
lean_inc_ref(v_toApplicative_779_);
lean_dec_ref(v_inst_765_);
v_toPure_780_ = lean_ctor_get(v_toApplicative_779_, 1);
lean_inc(v_toPure_780_);
lean_dec_ref(v_toApplicative_779_);
v___x_781_ = lean_apply_2(v_toPure_780_, lean_box(0), v___x_771_);
return v___x_781_;
}
else
{
size_t v___x_782_; size_t v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((size_t)0ULL);
v___x_783_ = lean_usize_of_nat(v___x_770_);
v___x_784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_765_, v___f_777_, v_buckets_768_, v___x_782_, v___x_783_, v___x_771_);
return v___x_784_;
}
}
else
{
size_t v___x_785_; size_t v___x_786_; lean_object* v___x_787_; 
v___x_785_ = ((size_t)0ULL);
v___x_786_ = lean_usize_of_nat(v___x_770_);
v___x_787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_765_, v___f_777_, v_buckets_768_, v___x_785_, v___x_786_, v___x_771_);
return v___x_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM(lean_object* v_00_u03b1_788_, lean_object* v_m_789_, lean_object* v_inst_790_, lean_object* v_f_791_, lean_object* v_b_792_){
_start:
{
lean_object* v_buckets_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_buckets_793_ = lean_ctor_get(v_b_792_, 1);
lean_inc_ref(v_buckets_793_);
lean_dec_ref(v_b_792_);
v___x_794_ = lean_unsigned_to_nat(0u);
v___x_795_ = lean_array_get_size(v_buckets_793_);
v___x_796_ = lean_box(0);
v___x_797_ = lean_nat_dec_lt(v___x_794_, v___x_795_);
if (v___x_797_ == 0)
{
lean_object* v_toApplicative_798_; lean_object* v_toPure_799_; lean_object* v___x_800_; 
lean_dec_ref(v_buckets_793_);
lean_dec(v_f_791_);
v_toApplicative_798_ = lean_ctor_get(v_inst_790_, 0);
lean_inc_ref(v_toApplicative_798_);
lean_dec_ref(v_inst_790_);
v_toPure_799_ = lean_ctor_get(v_toApplicative_798_, 1);
lean_inc(v_toPure_799_);
lean_dec_ref(v_toApplicative_798_);
v___x_800_ = lean_apply_2(v_toPure_799_, lean_box(0), v___x_796_);
return v___x_800_;
}
else
{
lean_object* v___f_801_; lean_object* v___f_802_; uint8_t v___x_803_; 
v___f_801_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_801_, 0, v_f_791_);
lean_inc_ref(v_inst_790_);
v___f_802_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_802_, 0, v_inst_790_);
lean_closure_set(v___f_802_, 1, v___f_801_);
v___x_803_ = lean_nat_dec_le(v___x_795_, v___x_795_);
if (v___x_803_ == 0)
{
if (v___x_797_ == 0)
{
lean_object* v_toApplicative_804_; lean_object* v_toPure_805_; lean_object* v___x_806_; 
lean_dec_ref(v___f_802_);
lean_dec_ref(v_buckets_793_);
v_toApplicative_804_ = lean_ctor_get(v_inst_790_, 0);
lean_inc_ref(v_toApplicative_804_);
lean_dec_ref(v_inst_790_);
v_toPure_805_ = lean_ctor_get(v_toApplicative_804_, 1);
lean_inc(v_toPure_805_);
lean_dec_ref(v_toApplicative_804_);
v___x_806_ = lean_apply_2(v_toPure_805_, lean_box(0), v___x_796_);
return v___x_806_;
}
else
{
size_t v___x_807_; size_t v___x_808_; lean_object* v___x_809_; 
v___x_807_ = ((size_t)0ULL);
v___x_808_ = lean_usize_of_nat(v___x_795_);
v___x_809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_790_, v___f_802_, v_buckets_793_, v___x_807_, v___x_808_, v___x_796_);
return v___x_809_;
}
}
else
{
size_t v___x_810_; size_t v___x_811_; lean_object* v___x_812_; 
v___x_810_ = ((size_t)0ULL);
v___x_811_ = lean_usize_of_nat(v___x_795_);
v___x_812_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_790_, v___f_802_, v_buckets_793_, v___x_810_, v___x_811_, v___x_796_);
return v___x_812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__0(lean_object* v_f_813_, lean_object* v_a_814_, lean_object* v_x_815_, lean_object* v_acc_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = lean_apply_2(v_f_813_, v_a_814_, v_acc_816_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__1(lean_object* v_inst_818_, lean_object* v___f_819_, lean_object* v_a_820_, lean_object* v_x_821_, lean_object* v___y_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_818_, v___f_819_, v_a_820_, v___y_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg(lean_object* v_inst_824_, lean_object* v_f_825_, lean_object* v_init_826_, lean_object* v_b_827_){
_start:
{
lean_object* v_buckets_828_; lean_object* v___f_829_; lean_object* v___f_830_; size_t v_sz_831_; size_t v___x_832_; lean_object* v___x_833_; 
v_buckets_828_ = lean_ctor_get(v_b_827_, 1);
lean_inc_ref(v_buckets_828_);
lean_dec_ref(v_b_827_);
v___f_829_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_829_, 0, v_f_825_);
lean_inc_ref(v_inst_824_);
v___f_830_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_830_, 0, v_inst_824_);
lean_closure_set(v___f_830_, 1, v___f_829_);
v_sz_831_ = lean_array_size(v_buckets_828_);
v___x_832_ = ((size_t)0ULL);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_824_, v_buckets_828_, v___f_830_, v_sz_831_, v___x_832_, v_init_826_);
return v___x_833_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn(lean_object* v_00_u03b1_834_, lean_object* v_m_835_, lean_object* v_inst_836_, lean_object* v_00_u03b2_837_, lean_object* v_f_838_, lean_object* v_init_839_, lean_object* v_b_840_){
_start:
{
lean_object* v_buckets_841_; lean_object* v___f_842_; lean_object* v___f_843_; size_t v_sz_844_; size_t v___x_845_; lean_object* v___x_846_; 
v_buckets_841_ = lean_ctor_get(v_b_840_, 1);
lean_inc_ref(v_buckets_841_);
lean_dec_ref(v_b_840_);
v___f_842_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_842_, 0, v_f_838_);
lean_inc_ref(v_inst_836_);
v___f_843_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_843_, 0, v_inst_836_);
lean_closure_set(v___f_843_, 1, v___f_842_);
v_sz_844_ = lean_array_size(v_buckets_841_);
v___x_845_ = ((size_t)0ULL);
v___x_846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_836_, v_buckets_841_, v___f_843_, v_sz_844_, v___x_845_, v_init_839_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2(lean_object* v_inst_847_, lean_object* v_m_848_, lean_object* v_f_849_){
_start:
{
lean_object* v_buckets_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; uint8_t v___x_854_; 
v_buckets_850_ = lean_ctor_get(v_m_848_, 1);
lean_inc_ref(v_buckets_850_);
lean_dec_ref(v_m_848_);
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_array_get_size(v_buckets_850_);
v___x_853_ = lean_box(0);
v___x_854_ = lean_nat_dec_lt(v___x_851_, v___x_852_);
if (v___x_854_ == 0)
{
lean_object* v_toApplicative_855_; lean_object* v_toPure_856_; lean_object* v___x_857_; 
lean_dec_ref(v_buckets_850_);
lean_dec(v_f_849_);
v_toApplicative_855_ = lean_ctor_get(v_inst_847_, 0);
lean_inc_ref(v_toApplicative_855_);
lean_dec_ref(v_inst_847_);
v_toPure_856_ = lean_ctor_get(v_toApplicative_855_, 1);
lean_inc(v_toPure_856_);
lean_dec_ref(v_toApplicative_855_);
v___x_857_ = lean_apply_2(v_toPure_856_, lean_box(0), v___x_853_);
return v___x_857_;
}
else
{
lean_object* v___f_858_; lean_object* v___f_859_; uint8_t v___x_860_; 
v___f_858_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_858_, 0, v_f_849_);
lean_inc_ref(v_inst_847_);
v___f_859_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_859_, 0, v_inst_847_);
lean_closure_set(v___f_859_, 1, v___f_858_);
v___x_860_ = lean_nat_dec_le(v___x_852_, v___x_852_);
if (v___x_860_ == 0)
{
if (v___x_854_ == 0)
{
lean_object* v_toApplicative_861_; lean_object* v_toPure_862_; lean_object* v___x_863_; 
lean_dec_ref(v___f_859_);
lean_dec_ref(v_buckets_850_);
v_toApplicative_861_ = lean_ctor_get(v_inst_847_, 0);
lean_inc_ref(v_toApplicative_861_);
lean_dec_ref(v_inst_847_);
v_toPure_862_ = lean_ctor_get(v_toApplicative_861_, 1);
lean_inc(v_toPure_862_);
lean_dec_ref(v_toApplicative_861_);
v___x_863_ = lean_apply_2(v_toPure_862_, lean_box(0), v___x_853_);
return v___x_863_;
}
else
{
size_t v___x_864_; size_t v___x_865_; lean_object* v___x_866_; 
v___x_864_ = ((size_t)0ULL);
v___x_865_ = lean_usize_of_nat(v___x_852_);
v___x_866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_847_, v___f_859_, v_buckets_850_, v___x_864_, v___x_865_, v___x_853_);
return v___x_866_;
}
}
else
{
size_t v___x_867_; size_t v___x_868_; lean_object* v___x_869_; 
v___x_867_ = ((size_t)0ULL);
v___x_868_ = lean_usize_of_nat(v___x_852_);
v___x_869_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_847_, v___f_859_, v_buckets_850_, v___x_867_, v___x_868_, v___x_853_);
return v___x_869_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_870_){
_start:
{
lean_object* v___f_871_; 
v___f_871_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_871_, 0, v_inst_870_);
return v___f_871_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_872_, lean_object* v_m_873_, lean_object* v_inst_874_){
_start:
{
lean_object* v___f_875_; 
v___f_875_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_875_, 0, v_inst_874_);
return v___f_875_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_876_, lean_object* v_00_u03b2_877_, lean_object* v_m_878_, lean_object* v_init_879_, lean_object* v_f_880_){
_start:
{
lean_object* v_buckets_881_; lean_object* v___f_882_; lean_object* v___f_883_; size_t v_sz_884_; size_t v___x_885_; lean_object* v___x_886_; 
v_buckets_881_ = lean_ctor_get(v_m_878_, 1);
lean_inc_ref(v_buckets_881_);
lean_dec_ref(v_m_878_);
v___f_882_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_882_, 0, v_f_880_);
lean_inc_ref(v_inst_876_);
v___f_883_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_883_, 0, v_inst_876_);
lean_closure_set(v___f_883_, 1, v___f_882_);
v_sz_884_ = lean_array_size(v_buckets_881_);
v___x_885_ = ((size_t)0ULL);
v___x_886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_876_, v_buckets_881_, v___f_883_, v_sz_884_, v___x_885_, v_init_879_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_887_){
_start:
{
lean_object* v___f_888_; 
v___f_888_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_888_, 0, v_inst_887_);
return v___f_888_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_889_, lean_object* v_m_890_, lean_object* v_inst_891_){
_start:
{
lean_object* v___f_892_; 
v___f_892_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_892_, 0, v_inst_891_);
return v___f_892_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_filter___redArg___lam__0(lean_object* v_f_893_, lean_object* v_a_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_896_ = lean_apply_1(v_f_893_, v_a_894_);
v___x_897_ = lean_unbox(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_898_, lean_object* v_a_899_, lean_object* v_x_900_){
_start:
{
uint8_t v_res_901_; lean_object* v_r_902_; 
v_res_901_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_898_, v_a_899_, v_x_900_);
v_r_902_ = lean_box(v_res_901_);
return v_r_902_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg(lean_object* v_f_903_, lean_object* v_m_904_){
_start:
{
lean_object* v_buckets_905_; lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v_buckets_905_ = lean_ctor_get(v_m_904_, 1);
v___x_906_ = lean_unsigned_to_nat(0u);
v___x_907_ = lean_array_get_size(v_buckets_905_);
v___x_908_ = lean_nat_dec_lt(v___x_906_, v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
lean_dec_ref(v_m_904_);
lean_dec_ref(v_f_903_);
v___x_909_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
return v___x_909_;
}
else
{
lean_object* v___f_910_; lean_object* v___x_911_; 
v___f_910_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_910_, 0, v_f_903_);
v___x_911_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_910_, v_m_904_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter(lean_object* v_00_u03b1_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_f_915_, lean_object* v_m_916_){
_start:
{
lean_object* v_buckets_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_buckets_917_ = lean_ctor_get(v_m_916_, 1);
v___x_918_ = lean_unsigned_to_nat(0u);
v___x_919_ = lean_array_get_size(v_buckets_917_);
v___x_920_ = lean_nat_dec_lt(v___x_918_, v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
lean_dec_ref(v_m_916_);
lean_dec_ref(v_f_915_);
v___x_921_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
return v___x_921_;
}
else
{
lean_object* v___f_922_; lean_object* v___x_923_; 
v___f_922_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_922_, 0, v_f_915_);
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_922_, v_m_916_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___boxed(lean_object* v_00_u03b1_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_f_927_, lean_object* v_m_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_HashSet_Raw_filter(v_00_u03b1_924_, v_inst_925_, v_inst_926_, v_f_927_, v_m_928_);
lean_dec_ref(v_inst_926_);
lean_dec_ref(v_inst_925_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__0(lean_object* v_x1_930_, lean_object* v_x2_931_, lean_object* v_x3_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = lean_array_push(v_x1_930_, v_x2_931_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__1(lean_object* v___x_934_, lean_object* v___f_935_, lean_object* v_acc_936_, lean_object* v_l_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_934_, v___f_935_, v_acc_936_, v_l_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg(lean_object* v_m_943_){
_start:
{
lean_object* v_size_944_; lean_object* v_buckets_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
v_size_944_ = lean_ctor_get(v_m_943_, 0);
lean_inc(v_size_944_);
v_buckets_945_ = lean_ctor_get(v_m_943_, 1);
lean_inc_ref(v_buckets_945_);
lean_dec_ref(v_m_943_);
v___x_946_ = lean_mk_empty_array_with_capacity(v_size_944_);
lean_dec(v_size_944_);
v___x_947_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = lean_array_get_size(v_buckets_945_);
v___x_950_ = lean_nat_dec_lt(v___x_948_, v___x_949_);
if (v___x_950_ == 0)
{
lean_dec_ref(v_buckets_945_);
return v___x_946_;
}
else
{
lean_object* v___f_951_; uint8_t v___x_952_; 
v___f_951_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_952_ = lean_nat_dec_le(v___x_949_, v___x_949_);
if (v___x_952_ == 0)
{
if (v___x_950_ == 0)
{
lean_dec_ref(v_buckets_945_);
return v___x_946_;
}
else
{
size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
v___x_953_ = ((size_t)0ULL);
v___x_954_ = lean_usize_of_nat(v___x_949_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_947_, v___f_951_, v_buckets_945_, v___x_953_, v___x_954_, v___x_946_);
return v___x_955_;
}
}
else
{
size_t v___x_956_; size_t v___x_957_; lean_object* v___x_958_; 
v___x_956_ = ((size_t)0ULL);
v___x_957_ = lean_usize_of_nat(v___x_949_);
v___x_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_947_, v___f_951_, v_buckets_945_, v___x_956_, v___x_957_, v___x_946_);
return v___x_958_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray(lean_object* v_00_u03b1_959_, lean_object* v_m_960_){
_start:
{
lean_object* v_size_961_; lean_object* v_buckets_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_size_961_ = lean_ctor_get(v_m_960_, 0);
lean_inc(v_size_961_);
v_buckets_962_ = lean_ctor_get(v_m_960_, 1);
lean_inc_ref(v_buckets_962_);
lean_dec_ref(v_m_960_);
v___x_963_ = lean_mk_empty_array_with_capacity(v_size_961_);
lean_dec(v_size_961_);
v___x_964_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = lean_array_get_size(v_buckets_962_);
v___x_967_ = lean_nat_dec_lt(v___x_965_, v___x_966_);
if (v___x_967_ == 0)
{
lean_dec_ref(v_buckets_962_);
return v___x_963_;
}
else
{
lean_object* v___f_968_; uint8_t v___x_969_; 
v___f_968_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_969_ = lean_nat_dec_le(v___x_966_, v___x_966_);
if (v___x_969_ == 0)
{
if (v___x_967_ == 0)
{
lean_dec_ref(v_buckets_962_);
return v___x_963_;
}
else
{
size_t v___x_970_; size_t v___x_971_; lean_object* v___x_972_; 
v___x_970_ = ((size_t)0ULL);
v___x_971_ = lean_usize_of_nat(v___x_966_);
v___x_972_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_964_, v___f_968_, v_buckets_962_, v___x_970_, v___x_971_, v___x_963_);
return v___x_972_;
}
}
else
{
size_t v___x_973_; size_t v___x_974_; lean_object* v___x_975_; 
v___x_973_ = ((size_t)0ULL);
v___x_974_ = lean_usize_of_nat(v___x_966_);
v___x_975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_964_, v___f_968_, v_buckets_962_, v___x_973_, v___x_974_, v___x_963_);
return v___x_975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__0(lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_a_978_, lean_object* v_b_979_, lean_object* v_acc_980_){
_start:
{
lean_object* v_r_981_; lean_object* v___x_982_; 
v_r_981_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_976_, v_inst_977_, v_acc_980_, v_a_978_, v_b_979_);
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v_r_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__1(lean_object* v___x_983_, lean_object* v___f_984_, lean_object* v_a_985_, lean_object* v_x_986_, lean_object* v___y_987_){
_start:
{
lean_object* v___x_988_; 
v___x_988_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_983_, v___f_984_, v_a_985_, v___y_987_);
return v___x_988_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg(lean_object* v_inst_991_, lean_object* v_inst_992_, lean_object* v_m_u2081_993_, lean_object* v_m_u2082_994_){
_start:
{
lean_object* v_size_995_; lean_object* v_buckets_996_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_size_995_ = lean_ctor_get(v_m_u2081_993_, 0);
v_buckets_996_ = lean_ctor_get(v_m_u2081_993_, 1);
v___x_997_ = lean_unsigned_to_nat(0u);
v___x_998_ = lean_array_get_size(v_buckets_996_);
v___x_999_ = lean_nat_dec_lt(v___x_997_, v___x_998_);
if (v___x_999_ == 0)
{
lean_dec_ref(v_m_u2081_993_);
lean_dec_ref(v_inst_992_);
lean_dec_ref(v_inst_991_);
return v_m_u2082_994_;
}
else
{
lean_object* v_size_1000_; lean_object* v_buckets_1001_; lean_object* v___x_1002_; uint8_t v___x_1003_; 
v_size_1000_ = lean_ctor_get(v_m_u2082_994_, 0);
v_buckets_1001_ = lean_ctor_get(v_m_u2082_994_, 1);
v___x_1002_ = lean_array_get_size(v_buckets_1001_);
v___x_1003_ = lean_nat_dec_lt(v___x_997_, v___x_1002_);
if (v___x_1003_ == 0)
{
lean_dec_ref(v_m_u2082_994_);
lean_dec_ref(v_inst_992_);
lean_dec_ref(v_inst_991_);
return v_m_u2081_993_;
}
else
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_nat_dec_le(v_size_995_, v_size_1000_);
if (v___x_1004_ == 0)
{
lean_object* v___f_1005_; lean_object* v___x_1006_; 
v___f_1005_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1006_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1005_, v_inst_991_, v_inst_992_, v_m_u2081_993_, v_m_u2082_994_);
return v___x_1006_;
}
else
{
lean_object* v___f_1007_; lean_object* v___x_1008_; lean_object* v___f_1009_; size_t v_sz_1010_; size_t v___x_1011_; lean_object* v___x_1012_; 
lean_inc_ref(v_buckets_996_);
lean_dec_ref(v_m_u2081_993_);
v___f_1007_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1007_, 0, v_inst_991_);
lean_closure_set(v___f_1007_, 1, v_inst_992_);
v___x_1008_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___f_1009_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1009_, 0, v___x_1008_);
lean_closure_set(v___f_1009_, 1, v___f_1007_);
v_sz_1010_ = lean_array_size(v_buckets_996_);
v___x_1011_ = ((size_t)0ULL);
v___x_1012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1008_, v_buckets_996_, v___f_1009_, v_sz_1010_, v___x_1011_, v_m_u2082_994_);
return v___x_1012_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union(lean_object* v_00_u03b1_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_m_u2081_1016_, lean_object* v_m_u2082_1017_){
_start:
{
lean_object* v_size_1018_; lean_object* v_buckets_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_size_1018_ = lean_ctor_get(v_m_u2081_1016_, 0);
v_buckets_1019_ = lean_ctor_get(v_m_u2081_1016_, 1);
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_array_get_size(v_buckets_1019_);
v___x_1022_ = lean_nat_dec_lt(v___x_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec_ref(v_m_u2081_1016_);
lean_dec_ref(v_inst_1015_);
lean_dec_ref(v_inst_1014_);
return v_m_u2082_1017_;
}
else
{
lean_object* v_size_1023_; lean_object* v_buckets_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_size_1023_ = lean_ctor_get(v_m_u2082_1017_, 0);
v_buckets_1024_ = lean_ctor_get(v_m_u2082_1017_, 1);
v___x_1025_ = lean_array_get_size(v_buckets_1024_);
v___x_1026_ = lean_nat_dec_lt(v___x_1020_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_dec_ref(v_m_u2082_1017_);
lean_dec_ref(v_inst_1015_);
lean_dec_ref(v_inst_1014_);
return v_m_u2081_1016_;
}
else
{
uint8_t v___x_1027_; 
v___x_1027_ = lean_nat_dec_le(v_size_1018_, v_size_1023_);
if (v___x_1027_ == 0)
{
lean_object* v___f_1028_; lean_object* v___x_1029_; 
v___f_1028_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1029_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1028_, v_inst_1014_, v_inst_1015_, v_m_u2081_1016_, v_m_u2082_1017_);
return v___x_1029_;
}
else
{
lean_object* v___f_1030_; lean_object* v___x_1031_; lean_object* v___f_1032_; size_t v_sz_1033_; size_t v___x_1034_; lean_object* v___x_1035_; 
lean_inc_ref(v_buckets_1019_);
lean_dec_ref(v_m_u2081_1016_);
v___f_1030_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1030_, 0, v_inst_1014_);
lean_closure_set(v___f_1030_, 1, v_inst_1015_);
v___x_1031_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___f_1032_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1032_, 0, v___x_1031_);
lean_closure_set(v___f_1032_, 1, v___f_1030_);
v_sz_1033_ = lean_array_size(v_buckets_1019_);
v___x_1034_ = ((size_t)0ULL);
v___x_1035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1031_, v_buckets_1019_, v___f_1032_, v_sz_1033_, v___x_1034_, v_m_u2082_1017_);
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1036_, lean_object* v_inst_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_1038_, 0, lean_box(0));
lean_closure_set(v___x_1038_, 1, v_inst_1036_);
lean_closure_set(v___x_1038_, 2, v_inst_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_1042_, 0, lean_box(0));
lean_closure_set(v___x_1042_, 1, v_inst_1040_);
lean_closure_set(v___x_1042_, 2, v_inst_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter___redArg(lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_m_u2081_1045_, lean_object* v_m_u2082_1046_){
_start:
{
lean_object* v_buckets_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; uint8_t v___x_1050_; 
v_buckets_1047_ = lean_ctor_get(v_m_u2081_1045_, 1);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = lean_array_get_size(v_buckets_1047_);
v___x_1050_ = lean_nat_dec_lt(v___x_1048_, v___x_1049_);
if (v___x_1050_ == 0)
{
lean_dec_ref(v_m_u2081_1045_);
lean_dec_ref(v_inst_1044_);
lean_dec_ref(v_inst_1043_);
return v_m_u2082_1046_;
}
else
{
lean_object* v_buckets_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v_buckets_1051_ = lean_ctor_get(v_m_u2082_1046_, 1);
v___x_1052_ = lean_array_get_size(v_buckets_1051_);
v___x_1053_ = lean_nat_dec_lt(v___x_1048_, v___x_1052_);
if (v___x_1053_ == 0)
{
lean_dec_ref(v_m_u2082_1046_);
lean_dec_ref(v_inst_1044_);
lean_dec_ref(v_inst_1043_);
return v_m_u2081_1045_;
}
else
{
lean_object* v___x_1054_; 
v___x_1054_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1043_, v_inst_1044_, v_m_u2081_1045_, v_m_u2082_1046_);
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter(lean_object* v_00_u03b1_1055_, lean_object* v_inst_1056_, lean_object* v_inst_1057_, lean_object* v_m_u2081_1058_, lean_object* v_m_u2082_1059_){
_start:
{
lean_object* v_buckets_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; uint8_t v___x_1063_; 
v_buckets_1060_ = lean_ctor_get(v_m_u2081_1058_, 1);
v___x_1061_ = lean_unsigned_to_nat(0u);
v___x_1062_ = lean_array_get_size(v_buckets_1060_);
v___x_1063_ = lean_nat_dec_lt(v___x_1061_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_dec_ref(v_m_u2081_1058_);
lean_dec_ref(v_inst_1057_);
lean_dec_ref(v_inst_1056_);
return v_m_u2082_1059_;
}
else
{
lean_object* v_buckets_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_buckets_1064_ = lean_ctor_get(v_m_u2082_1059_, 1);
v___x_1065_ = lean_array_get_size(v_buckets_1064_);
v___x_1066_ = lean_nat_dec_lt(v___x_1061_, v___x_1065_);
if (v___x_1066_ == 0)
{
lean_dec_ref(v_m_u2082_1059_);
lean_dec_ref(v_inst_1057_);
lean_dec_ref(v_inst_1056_);
return v_m_u2081_1058_;
}
else
{
lean_object* v___x_1067_; 
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1056_, v_inst_1057_, v_m_u2081_1058_, v_m_u2082_1059_);
return v___x_1067_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1068_, lean_object* v_inst_1069_){
_start:
{
lean_object* v___x_1070_; 
v___x_1070_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1070_, 0, lean_box(0));
lean_closure_set(v___x_1070_, 1, v_inst_1068_);
lean_closure_set(v___x_1070_, 2, v_inst_1069_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1071_, lean_object* v_inst_1072_, lean_object* v_inst_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1074_, 0, lean_box(0));
lean_closure_set(v___x_1074_, 1, v_inst_1072_);
lean_closure_set(v___x_1074_, 2, v_inst_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1075_; lean_object* v___f_1076_; 
v___x_1075_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1076_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1076_, 0, v___x_1075_);
return v___f_1076_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq___redArg(lean_object* v_inst_1077_, lean_object* v_inst_1078_, lean_object* v_m_u2081_1079_, lean_object* v_m_u2082_1080_){
_start:
{
lean_object* v___f_1081_; uint8_t v___x_1082_; 
v___f_1081_ = lean_obj_once(&l_Std_HashSet_Raw_beq___redArg___closed__0, &l_Std_HashSet_Raw_beq___redArg___closed__0_once, _init_l_Std_HashSet_Raw_beq___redArg___closed__0);
v___x_1082_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1077_, v_inst_1078_, v___f_1081_, v_m_u2081_1079_, v_m_u2082_1080_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___redArg___boxed(lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_m_u2081_1085_, lean_object* v_m_u2082_1086_){
_start:
{
uint8_t v_res_1087_; lean_object* v_r_1088_; 
v_res_1087_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1083_, v_inst_1084_, v_m_u2081_1085_, v_m_u2082_1086_);
v_r_1088_ = lean_box(v_res_1087_);
return v_r_1088_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq(lean_object* v_00_u03b1_1089_, lean_object* v_inst_1090_, lean_object* v_inst_1091_, lean_object* v_m_u2081_1092_, lean_object* v_m_u2082_1093_){
_start:
{
uint8_t v___x_1094_; 
v___x_1094_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1090_, v_inst_1091_, v_m_u2081_1092_, v_m_u2082_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___boxed(lean_object* v_00_u03b1_1095_, lean_object* v_inst_1096_, lean_object* v_inst_1097_, lean_object* v_m_u2081_1098_, lean_object* v_m_u2082_1099_){
_start:
{
uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_res_1100_ = l_Std_HashSet_Raw_beq(v_00_u03b1_1095_, v_inst_1096_, v_inst_1097_, v_m_u2081_1098_, v_m_u2082_1099_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1102_, lean_object* v_inst_1103_){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1104_, 0, lean_box(0));
lean_closure_set(v___x_1104_, 1, v_inst_1102_);
lean_closure_set(v___x_1104_, 2, v_inst_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1108_, 0, lean_box(0));
lean_closure_set(v___x_1108_, 1, v_inst_1106_);
lean_closure_set(v___x_1108_, 2, v_inst_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_diff___redArg___lam__0(lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_m_u2082_1111_, uint8_t v___x_1112_, lean_object* v_k_1113_, lean_object* v_x_1114_){
_start:
{
uint8_t v___x_1115_; 
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1109_, v_inst_1110_, v_m_u2082_1111_, v_k_1113_);
if (v___x_1115_ == 0)
{
return v___x_1112_;
}
else
{
uint8_t v___x_1116_; 
v___x_1116_ = 0;
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_m_u2082_1119_, lean_object* v___x_1120_, lean_object* v_k_1121_, lean_object* v_x_1122_){
_start:
{
uint8_t v___x_97__boxed_1123_; uint8_t v_res_1124_; lean_object* v_r_1125_; 
v___x_97__boxed_1123_ = lean_unbox(v___x_1120_);
v_res_1124_ = l_Std_HashSet_Raw_diff___redArg___lam__0(v_inst_1117_, v_inst_1118_, v_m_u2082_1119_, v___x_97__boxed_1123_, v_k_1121_, v_x_1122_);
lean_dec_ref(v_m_u2082_1119_);
v_r_1125_ = lean_box(v_res_1124_);
return v_r_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg(lean_object* v_inst_1126_, lean_object* v_inst_1127_, lean_object* v_m_u2081_1128_, lean_object* v_m_u2082_1129_){
_start:
{
lean_object* v_size_1130_; lean_object* v_buckets_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_size_1130_ = lean_ctor_get(v_m_u2081_1128_, 0);
v_buckets_1131_ = lean_ctor_get(v_m_u2081_1128_, 1);
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_array_get_size(v_buckets_1131_);
v___x_1134_ = lean_nat_dec_lt(v___x_1132_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_dec_ref(v_m_u2081_1128_);
lean_dec_ref(v_inst_1127_);
lean_dec_ref(v_inst_1126_);
return v_m_u2082_1129_;
}
else
{
lean_object* v_size_1135_; lean_object* v_buckets_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v_size_1135_ = lean_ctor_get(v_m_u2082_1129_, 0);
v_buckets_1136_ = lean_ctor_get(v_m_u2082_1129_, 1);
v___x_1137_ = lean_array_get_size(v_buckets_1136_);
v___x_1138_ = lean_nat_dec_lt(v___x_1132_, v___x_1137_);
if (v___x_1138_ == 0)
{
lean_dec_ref(v_m_u2082_1129_);
lean_dec_ref(v_inst_1127_);
lean_dec_ref(v_inst_1126_);
return v_m_u2081_1128_;
}
else
{
uint8_t v___x_1139_; 
v___x_1139_ = lean_nat_dec_le(v_size_1130_, v_size_1135_);
if (v___x_1139_ == 0)
{
lean_object* v___f_1140_; lean_object* v___x_1141_; 
v___f_1140_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1141_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1140_, v_inst_1126_, v_inst_1127_, v_m_u2081_1128_, v_m_u2082_1129_);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; lean_object* v___f_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_box(v___x_1139_);
v___f_1143_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1143_, 0, v_inst_1126_);
lean_closure_set(v___f_1143_, 1, v_inst_1127_);
lean_closure_set(v___f_1143_, 2, v_m_u2082_1129_);
lean_closure_set(v___f_1143_, 3, v___x_1142_);
v___x_1144_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1143_, v_m_u2081_1128_);
return v___x_1144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff(lean_object* v_00_u03b1_1145_, lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_m_u2081_1148_, lean_object* v_m_u2082_1149_){
_start:
{
lean_object* v_size_1150_; lean_object* v_buckets_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_size_1150_ = lean_ctor_get(v_m_u2081_1148_, 0);
v_buckets_1151_ = lean_ctor_get(v_m_u2081_1148_, 1);
v___x_1152_ = lean_unsigned_to_nat(0u);
v___x_1153_ = lean_array_get_size(v_buckets_1151_);
v___x_1154_ = lean_nat_dec_lt(v___x_1152_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_dec_ref(v_m_u2081_1148_);
lean_dec_ref(v_inst_1147_);
lean_dec_ref(v_inst_1146_);
return v_m_u2082_1149_;
}
else
{
lean_object* v_size_1155_; lean_object* v_buckets_1156_; lean_object* v___x_1157_; uint8_t v___x_1158_; 
v_size_1155_ = lean_ctor_get(v_m_u2082_1149_, 0);
v_buckets_1156_ = lean_ctor_get(v_m_u2082_1149_, 1);
v___x_1157_ = lean_array_get_size(v_buckets_1156_);
v___x_1158_ = lean_nat_dec_lt(v___x_1152_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_dec_ref(v_m_u2082_1149_);
lean_dec_ref(v_inst_1147_);
lean_dec_ref(v_inst_1146_);
return v_m_u2081_1148_;
}
else
{
uint8_t v___x_1159_; 
v___x_1159_ = lean_nat_dec_le(v_size_1150_, v_size_1155_);
if (v___x_1159_ == 0)
{
lean_object* v___f_1160_; lean_object* v___x_1161_; 
v___f_1160_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1161_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1160_, v_inst_1146_, v_inst_1147_, v_m_u2081_1148_, v_m_u2082_1149_);
return v___x_1161_;
}
else
{
lean_object* v___x_1162_; lean_object* v___f_1163_; lean_object* v___x_1164_; 
v___x_1162_ = lean_box(v___x_1159_);
v___f_1163_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1163_, 0, v_inst_1146_);
lean_closure_set(v___f_1163_, 1, v_inst_1147_);
lean_closure_set(v___f_1163_, 2, v_m_u2082_1149_);
lean_closure_set(v___f_1163_, 3, v___x_1162_);
v___x_1164_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1163_, v_m_u2081_1148_);
return v___x_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1165_, lean_object* v_inst_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1167_, 0, lean_box(0));
lean_closure_set(v___x_1167_, 1, v_inst_1165_);
lean_closure_set(v___x_1167_, 2, v_inst_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1168_, lean_object* v_inst_1169_, lean_object* v_inst_1170_){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1171_, 0, lean_box(0));
lean_closure_set(v___x_1171_, 1, v_inst_1169_);
lean_closure_set(v___x_1171_, 2, v_inst_1170_);
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0(lean_object* v_p_1172_, lean_object* v___x_1173_, lean_object* v___x_1174_, lean_object* v_a_1175_, lean_object* v_b_1176_, lean_object* v_acc_1177_){
_start:
{
lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1178_ = lean_apply_1(v_p_1172_, v_a_1175_);
v___x_1179_ = lean_unbox(v___x_1178_);
if (v___x_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
lean_dec_ref(v___x_1174_);
v___x_1180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1180_);
lean_ctor_set(v___x_1181_, 1, v___x_1173_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1183_, 0, v___x_1174_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1184_, lean_object* v___x_1185_, lean_object* v___x_1186_, lean_object* v_a_1187_, lean_object* v_b_1188_, lean_object* v_acc_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Std_HashSet_Raw_all___redArg___lam__0(v_p_1184_, v___x_1185_, v___x_1186_, v_a_1187_, v_b_1188_, v_acc_1189_);
lean_dec_ref(v_acc_1189_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__1(lean_object* v___x_1191_, lean_object* v___f_1192_, lean_object* v_a_1193_, lean_object* v_x_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1191_, v___f_1192_, v_a_1193_, v___y_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all___redArg(lean_object* v_m_1200_, lean_object* v_p_1201_){
_start:
{
lean_object* v___x_1202_; lean_object* v_buckets_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; size_t v_sz_1208_; size_t v___x_1209_; lean_object* v___x_1210_; lean_object* v_fst_1211_; 
v___x_1202_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1203_ = lean_ctor_get(v_m_1200_, 1);
lean_inc_ref(v_buckets_1203_);
lean_dec_ref(v_m_1200_);
v___x_1204_ = lean_box(0);
v___x_1205_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1206_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1206_, 0, v_p_1201_);
lean_closure_set(v___f_1206_, 1, v___x_1204_);
lean_closure_set(v___f_1206_, 2, v___x_1205_);
v___f_1207_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1207_, 0, v___x_1202_);
lean_closure_set(v___f_1207_, 1, v___f_1206_);
v_sz_1208_ = lean_array_size(v_buckets_1203_);
v___x_1209_ = ((size_t)0ULL);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1202_, v_buckets_1203_, v___f_1207_, v_sz_1208_, v___x_1209_, v___x_1205_);
v_fst_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_fst_1211_);
lean_dec(v___x_1210_);
if (lean_obj_tag(v_fst_1211_) == 0)
{
uint8_t v___x_1212_; 
v___x_1212_ = 1;
return v___x_1212_;
}
else
{
lean_object* v_val_1213_; uint8_t v___x_1214_; 
v_val_1213_ = lean_ctor_get(v_fst_1211_, 0);
lean_inc(v_val_1213_);
lean_dec_ref(v_fst_1211_);
v___x_1214_ = lean_unbox(v_val_1213_);
lean_dec(v_val_1213_);
return v___x_1214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___boxed(lean_object* v_m_1215_, lean_object* v_p_1216_){
_start:
{
uint8_t v_res_1217_; lean_object* v_r_1218_; 
v_res_1217_ = l_Std_HashSet_Raw_all___redArg(v_m_1215_, v_p_1216_);
v_r_1218_ = lean_box(v_res_1217_);
return v_r_1218_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all(lean_object* v_00_u03b1_1219_, lean_object* v_m_1220_, lean_object* v_p_1221_){
_start:
{
lean_object* v___x_1222_; lean_object* v_buckets_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; size_t v_sz_1228_; size_t v___x_1229_; lean_object* v___x_1230_; lean_object* v_fst_1231_; 
v___x_1222_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1223_ = lean_ctor_get(v_m_1220_, 1);
lean_inc_ref(v_buckets_1223_);
lean_dec_ref(v_m_1220_);
v___x_1224_ = lean_box(0);
v___x_1225_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1226_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1226_, 0, v_p_1221_);
lean_closure_set(v___f_1226_, 1, v___x_1224_);
lean_closure_set(v___f_1226_, 2, v___x_1225_);
v___f_1227_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1227_, 0, v___x_1222_);
lean_closure_set(v___f_1227_, 1, v___f_1226_);
v_sz_1228_ = lean_array_size(v_buckets_1223_);
v___x_1229_ = ((size_t)0ULL);
v___x_1230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1222_, v_buckets_1223_, v___f_1227_, v_sz_1228_, v___x_1229_, v___x_1225_);
v_fst_1231_ = lean_ctor_get(v___x_1230_, 0);
lean_inc(v_fst_1231_);
lean_dec(v___x_1230_);
if (lean_obj_tag(v_fst_1231_) == 0)
{
uint8_t v___x_1232_; 
v___x_1232_ = 1;
return v___x_1232_;
}
else
{
lean_object* v_val_1233_; uint8_t v___x_1234_; 
v_val_1233_ = lean_ctor_get(v_fst_1231_, 0);
lean_inc(v_val_1233_);
lean_dec_ref(v_fst_1231_);
v___x_1234_ = lean_unbox(v_val_1233_);
lean_dec(v_val_1233_);
return v___x_1234_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___boxed(lean_object* v_00_u03b1_1235_, lean_object* v_m_1236_, lean_object* v_p_1237_){
_start:
{
uint8_t v_res_1238_; lean_object* v_r_1239_; 
v_res_1238_ = l_Std_HashSet_Raw_all(v_00_u03b1_1235_, v_m_1236_, v_p_1237_);
v_r_1239_ = lean_box(v_res_1238_);
return v_r_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0(lean_object* v_p_1240_, lean_object* v___x_1241_, lean_object* v___x_1242_, lean_object* v_a_1243_, lean_object* v_b_1244_, lean_object* v_acc_1245_){
_start:
{
lean_object* v___x_1246_; uint8_t v___x_1247_; 
v___x_1246_ = lean_apply_1(v_p_1240_, v_a_1243_);
v___x_1247_ = lean_unbox(v___x_1246_);
if (v___x_1247_ == 0)
{
lean_object* v___x_1248_; 
v___x_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1241_);
return v___x_1248_;
}
else
{
lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
lean_dec_ref(v___x_1241_);
v___x_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1246_);
v___x_1250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1249_);
lean_ctor_set(v___x_1250_, 1, v___x_1242_);
v___x_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1250_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1252_, lean_object* v___x_1253_, lean_object* v___x_1254_, lean_object* v_a_1255_, lean_object* v_b_1256_, lean_object* v_acc_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_Std_HashSet_Raw_any___redArg___lam__0(v_p_1252_, v___x_1253_, v___x_1254_, v_a_1255_, v_b_1256_, v_acc_1257_);
lean_dec_ref(v_acc_1257_);
return v_res_1258_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any___redArg(lean_object* v_m_1259_, lean_object* v_p_1260_){
_start:
{
lean_object* v___x_1261_; lean_object* v_buckets_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___f_1265_; lean_object* v___f_1266_; size_t v_sz_1267_; size_t v___x_1268_; lean_object* v___x_1269_; lean_object* v_fst_1270_; 
v___x_1261_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1262_ = lean_ctor_get(v_m_1259_, 1);
lean_inc_ref(v_buckets_1262_);
lean_dec_ref(v_m_1259_);
v___x_1263_ = lean_box(0);
v___x_1264_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1265_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1265_, 0, v_p_1260_);
lean_closure_set(v___f_1265_, 1, v___x_1264_);
lean_closure_set(v___f_1265_, 2, v___x_1263_);
v___f_1266_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1266_, 0, v___x_1261_);
lean_closure_set(v___f_1266_, 1, v___f_1265_);
v_sz_1267_ = lean_array_size(v_buckets_1262_);
v___x_1268_ = ((size_t)0ULL);
v___x_1269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1261_, v_buckets_1262_, v___f_1266_, v_sz_1267_, v___x_1268_, v___x_1264_);
v_fst_1270_ = lean_ctor_get(v___x_1269_, 0);
lean_inc(v_fst_1270_);
lean_dec(v___x_1269_);
if (lean_obj_tag(v_fst_1270_) == 0)
{
uint8_t v___x_1271_; 
v___x_1271_ = 0;
return v___x_1271_;
}
else
{
lean_object* v_val_1272_; uint8_t v___x_1273_; 
v_val_1272_ = lean_ctor_get(v_fst_1270_, 0);
lean_inc(v_val_1272_);
lean_dec_ref(v_fst_1270_);
v___x_1273_ = lean_unbox(v_val_1272_);
lean_dec(v_val_1272_);
return v___x_1273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___boxed(lean_object* v_m_1274_, lean_object* v_p_1275_){
_start:
{
uint8_t v_res_1276_; lean_object* v_r_1277_; 
v_res_1276_ = l_Std_HashSet_Raw_any___redArg(v_m_1274_, v_p_1275_);
v_r_1277_ = lean_box(v_res_1276_);
return v_r_1277_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any(lean_object* v_00_u03b1_1278_, lean_object* v_m_1279_, lean_object* v_p_1280_){
_start:
{
lean_object* v___x_1281_; lean_object* v_buckets_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___f_1285_; lean_object* v___f_1286_; size_t v_sz_1287_; size_t v___x_1288_; lean_object* v___x_1289_; lean_object* v_fst_1290_; 
v___x_1281_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1282_ = lean_ctor_get(v_m_1279_, 1);
lean_inc_ref(v_buckets_1282_);
lean_dec_ref(v_m_1279_);
v___x_1283_ = lean_box(0);
v___x_1284_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1285_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1285_, 0, v_p_1280_);
lean_closure_set(v___f_1285_, 1, v___x_1284_);
lean_closure_set(v___f_1285_, 2, v___x_1283_);
v___f_1286_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1286_, 0, v___x_1281_);
lean_closure_set(v___f_1286_, 1, v___f_1285_);
v_sz_1287_ = lean_array_size(v_buckets_1282_);
v___x_1288_ = ((size_t)0ULL);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1281_, v_buckets_1282_, v___f_1286_, v_sz_1287_, v___x_1288_, v___x_1284_);
v_fst_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_fst_1290_);
lean_dec(v___x_1289_);
if (lean_obj_tag(v_fst_1290_) == 0)
{
uint8_t v___x_1291_; 
v___x_1291_ = 0;
return v___x_1291_;
}
else
{
lean_object* v_val_1292_; uint8_t v___x_1293_; 
v_val_1292_ = lean_ctor_get(v_fst_1290_, 0);
lean_inc(v_val_1292_);
lean_dec_ref(v_fst_1290_);
v___x_1293_ = lean_unbox(v_val_1292_);
lean_dec(v_val_1292_);
return v___x_1293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___boxed(lean_object* v_00_u03b1_1294_, lean_object* v_m_1295_, lean_object* v_p_1296_){
_start:
{
uint8_t v_res_1297_; lean_object* v_r_1298_; 
v_res_1297_ = l_Std_HashSet_Raw_any(v_00_u03b1_1294_, v_m_1295_, v_p_1296_);
v_r_1298_ = lean_box(v_res_1297_);
return v_r_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany___redArg(lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_inst_1301_, lean_object* v_m_1302_, lean_object* v_l_1303_){
_start:
{
lean_object* v_buckets_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v_buckets_1304_ = lean_ctor_get(v_m_1302_, 1);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_array_get_size(v_buckets_1304_);
v___x_1307_ = lean_nat_dec_lt(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec(v_l_1303_);
lean_dec(v_inst_1301_);
lean_dec_ref(v_inst_1300_);
lean_dec_ref(v_inst_1299_);
return v_m_1302_;
}
else
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1301_, v_inst_1299_, v_inst_1300_, v_m_1302_, v_l_1303_);
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany(lean_object* v_00_u03b1_1309_, lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_00_u03c1_1312_, lean_object* v_inst_1313_, lean_object* v_m_1314_, lean_object* v_l_1315_){
_start:
{
lean_object* v_buckets_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_buckets_1316_ = lean_ctor_get(v_m_1314_, 1);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_array_get_size(v_buckets_1316_);
v___x_1319_ = lean_nat_dec_lt(v___x_1317_, v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec(v_l_1315_);
lean_dec(v_inst_1313_);
lean_dec_ref(v_inst_1311_);
lean_dec_ref(v_inst_1310_);
return v_m_1314_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1313_, v_inst_1310_, v_inst_1311_, v_m_1314_, v_l_1315_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray___redArg(lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_l_1327_){
_start:
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_1329_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1329_ == 0)
{
lean_dec_ref(v_l_1327_);
lean_dec_ref(v_inst_1326_);
lean_dec_ref(v_inst_1325_);
return v___x_1328_;
}
else
{
lean_object* v___f_1330_; lean_object* v___x_1331_; 
v___f_1330_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1330_, v_inst_1325_, v_inst_1326_, v___x_1328_, v_l_1327_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray(lean_object* v_00_u03b1_1332_, lean_object* v_inst_1333_, lean_object* v_inst_1334_, lean_object* v_l_1335_){
_start:
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_1337_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1337_ == 0)
{
lean_dec_ref(v_l_1335_);
lean_dec_ref(v_inst_1334_);
lean_dec_ref(v_inst_1333_);
return v___x_1336_;
}
else
{
lean_object* v___f_1338_; lean_object* v___x_1339_; 
v___f_1338_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1339_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1338_, v_inst_1333_, v_inst_1334_, v___x_1336_, v_l_1335_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg(lean_object* v_m_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1340_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_HashSet_Raw_Internal_numBuckets___redArg(v_m_1342_);
lean_dec_ref(v_m_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets(lean_object* v_00_u03b1_1344_, lean_object* v_m_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1347_, lean_object* v_m_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Std_HashSet_Raw_Internal_numBuckets(v_00_u03b1_1347_, v_m_1348_);
lean_dec_ref(v_m_1348_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2(lean_object* v_inst_1353_, lean_object* v___f_1354_, lean_object* v_m_1355_, lean_object* v_prec_1356_){
_start:
{
lean_object* v___x_1357_; lean_object* v_buckets_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1378_; 
v___x_1357_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
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
v___x_1362_ = ((lean_object*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1));
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
v___f_1374_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_toList___redArg___lam__1), 4, 2);
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1380_, lean_object* v___f_1381_, lean_object* v_m_1382_, lean_object* v_prec_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2(v_inst_1380_, v___f_1381_, v_m_1382_, v_prec_1383_);
lean_dec(v_prec_1383_);
return v_res_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg(lean_object* v_inst_1385_){
_start:
{
lean_object* v___f_1386_; lean_object* v___f_1387_; 
v___f_1386_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___f_1387_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1387_, 0, v_inst_1385_);
lean_closure_set(v___f_1387_, 1, v___f_1386_);
return v___f_1387_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr(lean_object* v_00_u03b1_1388_, lean_object* v_inst_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = l_Std_HashSet_Raw_instRepr___redArg(v_inst_1389_);
return v___x_1390_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashSet_Raw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashSet_Raw(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashSet_Raw(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashSet_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashSet_Raw(builtin);
}
#ifdef __cplusplus
}
#endif
