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
uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_382_; 
v___x_382_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_378_, v_inst_379_, v_m_380_, v_a_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_383_, lean_object* v_inst_384_, lean_object* v_m_385_, lean_object* v_a_386_){
_start:
{
uint8_t v_res_387_; lean_object* v_r_388_; 
v_res_387_ = l_Std_HashSet_Raw_instDecidableMem___redArg(v_inst_383_, v_inst_384_, v_m_385_, v_a_386_);
lean_dec_ref(v_m_385_);
v_r_388_ = lean_box(v_res_387_);
return v_r_388_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem(lean_object* v_00_u03b1_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_m_392_, lean_object* v_a_393_){
_start:
{
uint8_t v___x_394_; 
v___x_394_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_390_, v_inst_391_, v_m_392_, v_a_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_395_, lean_object* v_inst_396_, lean_object* v_inst_397_, lean_object* v_m_398_, lean_object* v_a_399_){
_start:
{
uint8_t v_res_400_; lean_object* v_r_401_; 
v_res_400_ = l_Std_HashSet_Raw_instDecidableMem(v_00_u03b1_395_, v_inst_396_, v_inst_397_, v_m_398_, v_a_399_);
lean_dec_ref(v_m_398_);
v_r_401_ = lean_box(v_res_400_);
return v_r_401_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase___redArg(lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_m_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_buckets_406_; lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v_buckets_406_ = lean_ctor_get(v_m_404_, 1);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_array_get_size(v_buckets_406_);
v___x_409_ = lean_nat_dec_lt(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
lean_dec(v_a_405_);
lean_dec_ref(v_inst_403_);
lean_dec_ref(v_inst_402_);
return v_m_404_;
}
else
{
lean_object* v___x_410_; 
v___x_410_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_402_, v_inst_403_, v_m_404_, v_a_405_);
return v___x_410_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase(lean_object* v_00_u03b1_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_m_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_buckets_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
v_buckets_416_ = lean_ctor_get(v_m_414_, 1);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_418_ = lean_array_get_size(v_buckets_416_);
v___x_419_ = lean_nat_dec_lt(v___x_417_, v___x_418_);
if (v___x_419_ == 0)
{
lean_dec(v_a_415_);
lean_dec_ref(v_inst_413_);
lean_dec_ref(v_inst_412_);
return v_m_414_;
}
else
{
lean_object* v___x_420_; 
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_412_, v_inst_413_, v_m_414_, v_a_415_);
return v___x_420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg(lean_object* v_m_421_){
_start:
{
lean_object* v_size_422_; 
v_size_422_ = lean_ctor_get(v_m_421_, 0);
lean_inc(v_size_422_);
return v_size_422_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg___boxed(lean_object* v_m_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Std_HashSet_Raw_size___redArg(v_m_423_);
lean_dec_ref(v_m_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size(lean_object* v_00_u03b1_425_, lean_object* v_m_426_){
_start:
{
lean_object* v_size_427_; 
v_size_427_ = lean_ctor_get(v_m_426_, 0);
lean_inc(v_size_427_);
return v_size_427_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___boxed(lean_object* v_00_u03b1_428_, lean_object* v_m_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Std_HashSet_Raw_size(v_00_u03b1_428_, v_m_429_);
lean_dec_ref(v_m_429_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg(lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_m_433_, lean_object* v_a_434_){
_start:
{
lean_object* v_buckets_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_buckets_435_ = lean_ctor_get(v_m_433_, 1);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_array_get_size(v_buckets_435_);
v___x_438_ = lean_nat_dec_lt(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_439_; 
lean_dec(v_a_434_);
lean_dec_ref(v_inst_432_);
lean_dec_ref(v_inst_431_);
v___x_439_ = lean_box(0);
return v___x_439_;
}
else
{
lean_object* v___x_440_; 
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_431_, v_inst_432_, v_m_433_, v_a_434_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg___boxed(lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_m_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_HashSet_Raw_get_x3f___redArg(v_inst_441_, v_inst_442_, v_m_443_, v_a_444_);
lean_dec_ref(v_m_443_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f(lean_object* v_00_u03b1_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_m_449_, lean_object* v_a_450_){
_start:
{
lean_object* v_buckets_451_; lean_object* v___x_452_; lean_object* v___x_453_; uint8_t v___x_454_; 
v_buckets_451_ = lean_ctor_get(v_m_449_, 1);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = lean_array_get_size(v_buckets_451_);
v___x_454_ = lean_nat_dec_lt(v___x_452_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_dec(v_a_450_);
lean_dec_ref(v_inst_448_);
lean_dec_ref(v_inst_447_);
v___x_455_ = lean_box(0);
return v___x_455_;
}
else
{
lean_object* v___x_456_; 
v___x_456_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_447_, v_inst_448_, v_m_449_, v_a_450_);
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___boxed(lean_object* v_00_u03b1_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_m_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_HashSet_Raw_get_x3f(v_00_u03b1_457_, v_inst_458_, v_inst_459_, v_m_460_, v_a_461_);
lean_dec_ref(v_m_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg(lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_m_465_, lean_object* v_a_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_463_, v_inst_464_, v_m_465_, v_a_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg___boxed(lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_m_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Std_HashSet_Raw_get___redArg(v_inst_468_, v_inst_469_, v_m_470_, v_a_471_);
lean_dec_ref(v_m_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get(lean_object* v_00_u03b1_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_m_476_, lean_object* v_a_477_, lean_object* v_h_478_){
_start:
{
lean_object* v___x_479_; 
v___x_479_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_474_, v_inst_475_, v_m_476_, v_a_477_);
return v___x_479_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___boxed(lean_object* v_00_u03b1_480_, lean_object* v_inst_481_, lean_object* v_inst_482_, lean_object* v_m_483_, lean_object* v_a_484_, lean_object* v_h_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_HashSet_Raw_get(v_00_u03b1_480_, v_inst_481_, v_inst_482_, v_m_483_, v_a_484_, v_h_485_);
lean_dec_ref(v_m_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg(lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_m_489_, lean_object* v_a_490_, lean_object* v_fallback_491_){
_start:
{
lean_object* v_buckets_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_buckets_492_ = lean_ctor_get(v_m_489_, 1);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = lean_array_get_size(v_buckets_492_);
v___x_495_ = lean_nat_dec_lt(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_dec(v_a_490_);
lean_dec_ref(v_inst_488_);
lean_dec_ref(v_inst_487_);
lean_inc(v_fallback_491_);
return v_fallback_491_;
}
else
{
lean_object* v___x_496_; 
v___x_496_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_487_, v_inst_488_, v_m_489_, v_a_490_, v_fallback_491_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg___boxed(lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_m_499_, lean_object* v_a_500_, lean_object* v_fallback_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_HashSet_Raw_getD___redArg(v_inst_497_, v_inst_498_, v_m_499_, v_a_500_, v_fallback_501_);
lean_dec(v_fallback_501_);
lean_dec_ref(v_m_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD(lean_object* v_00_u03b1_503_, lean_object* v_inst_504_, lean_object* v_inst_505_, lean_object* v_m_506_, lean_object* v_a_507_, lean_object* v_fallback_508_){
_start:
{
lean_object* v_buckets_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v_buckets_509_ = lean_ctor_get(v_m_506_, 1);
v___x_510_ = lean_unsigned_to_nat(0u);
v___x_511_ = lean_array_get_size(v_buckets_509_);
v___x_512_ = lean_nat_dec_lt(v___x_510_, v___x_511_);
if (v___x_512_ == 0)
{
lean_dec(v_a_507_);
lean_dec_ref(v_inst_505_);
lean_dec_ref(v_inst_504_);
lean_inc(v_fallback_508_);
return v_fallback_508_;
}
else
{
lean_object* v___x_513_; 
v___x_513_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_504_, v_inst_505_, v_m_506_, v_a_507_, v_fallback_508_);
return v___x_513_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___boxed(lean_object* v_00_u03b1_514_, lean_object* v_inst_515_, lean_object* v_inst_516_, lean_object* v_m_517_, lean_object* v_a_518_, lean_object* v_fallback_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Std_HashSet_Raw_getD(v_00_u03b1_514_, v_inst_515_, v_inst_516_, v_m_517_, v_a_518_, v_fallback_519_);
lean_dec(v_fallback_519_);
lean_dec_ref(v_m_517_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg(lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_m_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_buckets_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v_buckets_526_ = lean_ctor_get(v_m_524_, 1);
v___x_527_ = lean_unsigned_to_nat(0u);
v___x_528_ = lean_array_get_size(v_buckets_526_);
v___x_529_ = lean_nat_dec_lt(v___x_527_, v___x_528_);
if (v___x_529_ == 0)
{
lean_dec(v_a_525_);
lean_dec_ref(v_inst_522_);
lean_dec_ref(v_inst_521_);
lean_inc(v_inst_523_);
return v_inst_523_;
}
else
{
lean_object* v___x_530_; 
v___x_530_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_521_, v_inst_522_, v_inst_523_, v_m_524_, v_a_525_);
return v___x_530_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg___boxed(lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_m_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Std_HashSet_Raw_get_x21___redArg(v_inst_531_, v_inst_532_, v_inst_533_, v_m_534_, v_a_535_);
lean_dec_ref(v_m_534_);
lean_dec(v_inst_533_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21(lean_object* v_00_u03b1_537_, lean_object* v_inst_538_, lean_object* v_inst_539_, lean_object* v_inst_540_, lean_object* v_m_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_buckets_543_; lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v_buckets_543_ = lean_ctor_get(v_m_541_, 1);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_array_get_size(v_buckets_543_);
v___x_546_ = lean_nat_dec_lt(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_dec(v_a_542_);
lean_dec_ref(v_inst_539_);
lean_dec_ref(v_inst_538_);
lean_inc(v_inst_540_);
return v_inst_540_;
}
else
{
lean_object* v___x_547_; 
v___x_547_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_538_, v_inst_539_, v_inst_540_, v_m_541_, v_a_542_);
return v___x_547_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___boxed(lean_object* v_00_u03b1_548_, lean_object* v_inst_549_, lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_m_552_, lean_object* v_a_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_HashSet_Raw_get_x21(v_00_u03b1_548_, v_inst_549_, v_inst_550_, v_inst_551_, v_m_552_, v_a_553_);
lean_dec_ref(v_m_552_);
lean_dec(v_inst_551_);
return v_res_554_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty___redArg(lean_object* v_m_555_){
_start:
{
lean_object* v_size_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_size_556_ = lean_ctor_get(v_m_555_, 0);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_558_ = lean_nat_dec_eq(v_size_556_, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___redArg___boxed(lean_object* v_m_559_){
_start:
{
uint8_t v_res_560_; lean_object* v_r_561_; 
v_res_560_ = l_Std_HashSet_Raw_isEmpty___redArg(v_m_559_);
lean_dec_ref(v_m_559_);
v_r_561_ = lean_box(v_res_560_);
return v_r_561_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty(lean_object* v_00_u03b1_562_, lean_object* v_m_563_){
_start:
{
lean_object* v_size_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_size_564_ = lean_ctor_get(v_m_563_, 0);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_nat_dec_eq(v_size_564_, v___x_565_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_567_, lean_object* v_m_568_){
_start:
{
uint8_t v_res_569_; lean_object* v_r_570_; 
v_res_569_ = l_Std_HashSet_Raw_isEmpty(v_00_u03b1_567_, v_m_568_);
lean_dec_ref(v_m_568_);
v_r_570_ = lean_box(v_res_569_);
return v_r_570_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__0(lean_object* v_a_571_, lean_object* v_b_572_, lean_object* v_d_573_){
_start:
{
lean_object* v___x_574_; 
v___x_574_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_574_, 0, v_a_571_);
lean_ctor_set(v___x_574_, 1, v_d_573_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__1(lean_object* v___x_575_, lean_object* v___f_576_, lean_object* v_l_577_, lean_object* v_acc_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_575_, v___f_576_, v_acc_578_, v_l_577_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg(lean_object* v_m_603_){
_start:
{
lean_object* v___x_604_; lean_object* v_buckets_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v___x_604_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_605_ = lean_ctor_get(v_m_603_, 1);
lean_inc_ref(v_buckets_605_);
lean_dec_ref(v_m_603_);
v___x_606_ = lean_box(0);
v___x_607_ = lean_array_get_size(v_buckets_605_);
v___x_608_ = lean_unsigned_to_nat(0u);
v___x_609_ = lean_nat_dec_lt(v___x_608_, v___x_607_);
if (v___x_609_ == 0)
{
lean_dec_ref(v_buckets_605_);
return v___x_606_;
}
else
{
lean_object* v___f_610_; size_t v___x_611_; size_t v___x_612_; lean_object* v___x_613_; 
v___f_610_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__11));
v___x_611_ = lean_usize_of_nat(v___x_607_);
v___x_612_ = ((size_t)0ULL);
v___x_613_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_604_, v___f_610_, v_buckets_605_, v___x_611_, v___x_612_, v___x_606_);
return v___x_613_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList(lean_object* v_00_u03b1_614_, lean_object* v_m_615_){
_start:
{
lean_object* v___x_616_; lean_object* v_buckets_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; uint8_t v___x_621_; 
v___x_616_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_617_ = lean_ctor_get(v_m_615_, 1);
lean_inc_ref(v_buckets_617_);
lean_dec_ref(v_m_615_);
v___x_618_ = lean_box(0);
v___x_619_ = lean_array_get_size(v_buckets_617_);
v___x_620_ = lean_unsigned_to_nat(0u);
v___x_621_ = lean_nat_dec_lt(v___x_620_, v___x_619_);
if (v___x_621_ == 0)
{
lean_dec_ref(v_buckets_617_);
return v___x_618_;
}
else
{
lean_object* v___f_622_; size_t v___x_623_; size_t v___x_624_; lean_object* v___x_625_; 
v___f_622_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__11));
v___x_623_ = lean_usize_of_nat(v___x_619_);
v___x_624_ = ((size_t)0ULL);
v___x_625_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_616_, v___f_622_, v_buckets_617_, v___x_623_, v___x_624_, v___x_618_);
return v___x_625_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList___redArg(lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_l_632_){
_start:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_634_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_634_ == 0)
{
lean_dec(v_l_632_);
lean_dec_ref(v_inst_631_);
lean_dec_ref(v_inst_630_);
return v___x_633_;
}
else
{
lean_object* v___f_635_; lean_object* v___x_636_; 
v___f_635_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_635_, v_inst_630_, v_inst_631_, v___x_633_, v_l_632_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList(lean_object* v_00_u03b1_637_, lean_object* v_inst_638_, lean_object* v_inst_639_, lean_object* v_l_640_){
_start:
{
lean_object* v___x_641_; uint8_t v___x_642_; 
v___x_641_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_642_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_642_ == 0)
{
lean_dec(v_l_640_);
lean_dec_ref(v_inst_639_);
lean_dec_ref(v_inst_638_);
return v___x_641_;
}
else
{
lean_object* v___f_643_; lean_object* v___x_644_; 
v___f_643_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_643_, v_inst_638_, v_inst_639_, v___x_641_, v_l_640_);
return v___x_644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__0(lean_object* v_f_645_, lean_object* v_b_646_, lean_object* v_a_647_, lean_object* v_x_648_){
_start:
{
lean_object* v___x_649_; 
v___x_649_ = lean_apply_2(v_f_645_, v_b_646_, v_a_647_);
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__1(lean_object* v_inst_650_, lean_object* v___f_651_, lean_object* v_acc_652_, lean_object* v_l_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_650_, v___f_651_, v_acc_652_, v_l_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg(lean_object* v_inst_655_, lean_object* v_f_656_, lean_object* v_init_657_, lean_object* v_b_658_){
_start:
{
lean_object* v_buckets_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v_buckets_659_ = lean_ctor_get(v_b_658_, 1);
lean_inc_ref(v_buckets_659_);
lean_dec_ref(v_b_658_);
v___x_660_ = lean_unsigned_to_nat(0u);
v___x_661_ = lean_array_get_size(v_buckets_659_);
v___x_662_ = lean_nat_dec_lt(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v_toApplicative_663_; lean_object* v_toPure_664_; lean_object* v___x_665_; 
lean_dec_ref(v_buckets_659_);
lean_dec(v_f_656_);
v_toApplicative_663_ = lean_ctor_get(v_inst_655_, 0);
lean_inc_ref(v_toApplicative_663_);
lean_dec_ref(v_inst_655_);
v_toPure_664_ = lean_ctor_get(v_toApplicative_663_, 1);
lean_inc(v_toPure_664_);
lean_dec_ref(v_toApplicative_663_);
v___x_665_ = lean_apply_2(v_toPure_664_, lean_box(0), v_init_657_);
return v___x_665_;
}
else
{
lean_object* v___f_666_; lean_object* v___f_667_; uint8_t v___x_668_; 
v___f_666_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_666_, 0, v_f_656_);
lean_inc_ref(v_inst_655_);
v___f_667_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_667_, 0, v_inst_655_);
lean_closure_set(v___f_667_, 1, v___f_666_);
v___x_668_ = lean_nat_dec_le(v___x_661_, v___x_661_);
if (v___x_668_ == 0)
{
if (v___x_662_ == 0)
{
lean_object* v_toApplicative_669_; lean_object* v_toPure_670_; lean_object* v___x_671_; 
lean_dec_ref(v___f_667_);
lean_dec_ref(v_buckets_659_);
v_toApplicative_669_ = lean_ctor_get(v_inst_655_, 0);
lean_inc_ref(v_toApplicative_669_);
lean_dec_ref(v_inst_655_);
v_toPure_670_ = lean_ctor_get(v_toApplicative_669_, 1);
lean_inc(v_toPure_670_);
lean_dec_ref(v_toApplicative_669_);
v___x_671_ = lean_apply_2(v_toPure_670_, lean_box(0), v_init_657_);
return v___x_671_;
}
else
{
size_t v___x_672_; size_t v___x_673_; lean_object* v___x_674_; 
v___x_672_ = ((size_t)0ULL);
v___x_673_ = lean_usize_of_nat(v___x_661_);
v___x_674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_667_, v_buckets_659_, v___x_672_, v___x_673_, v_init_657_);
return v___x_674_;
}
}
else
{
size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
v___x_675_ = ((size_t)0ULL);
v___x_676_ = lean_usize_of_nat(v___x_661_);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_667_, v_buckets_659_, v___x_675_, v___x_676_, v_init_657_);
return v___x_677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM(lean_object* v_00_u03b1_678_, lean_object* v_m_679_, lean_object* v_inst_680_, lean_object* v_00_u03b2_681_, lean_object* v_f_682_, lean_object* v_init_683_, lean_object* v_b_684_){
_start:
{
lean_object* v_buckets_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_buckets_685_ = lean_ctor_get(v_b_684_, 1);
lean_inc_ref(v_buckets_685_);
lean_dec_ref(v_b_684_);
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_array_get_size(v_buckets_685_);
v___x_688_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v_toApplicative_689_; lean_object* v_toPure_690_; lean_object* v___x_691_; 
lean_dec_ref(v_buckets_685_);
lean_dec(v_f_682_);
v_toApplicative_689_ = lean_ctor_get(v_inst_680_, 0);
lean_inc_ref(v_toApplicative_689_);
lean_dec_ref(v_inst_680_);
v_toPure_690_ = lean_ctor_get(v_toApplicative_689_, 1);
lean_inc(v_toPure_690_);
lean_dec_ref(v_toApplicative_689_);
v___x_691_ = lean_apply_2(v_toPure_690_, lean_box(0), v_init_683_);
return v___x_691_;
}
else
{
lean_object* v___f_692_; lean_object* v___f_693_; uint8_t v___x_694_; 
v___f_692_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_692_, 0, v_f_682_);
lean_inc_ref(v_inst_680_);
v___f_693_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_693_, 0, v_inst_680_);
lean_closure_set(v___f_693_, 1, v___f_692_);
v___x_694_ = lean_nat_dec_le(v___x_687_, v___x_687_);
if (v___x_694_ == 0)
{
if (v___x_688_ == 0)
{
lean_object* v_toApplicative_695_; lean_object* v_toPure_696_; lean_object* v___x_697_; 
lean_dec_ref(v___f_693_);
lean_dec_ref(v_buckets_685_);
v_toApplicative_695_ = lean_ctor_get(v_inst_680_, 0);
lean_inc_ref(v_toApplicative_695_);
lean_dec_ref(v_inst_680_);
v_toPure_696_ = lean_ctor_get(v_toApplicative_695_, 1);
lean_inc(v_toPure_696_);
lean_dec_ref(v_toApplicative_695_);
v___x_697_ = lean_apply_2(v_toPure_696_, lean_box(0), v_init_683_);
return v___x_697_;
}
else
{
size_t v___x_698_; size_t v___x_699_; lean_object* v___x_700_; 
v___x_698_ = ((size_t)0ULL);
v___x_699_ = lean_usize_of_nat(v___x_687_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_680_, v___f_693_, v_buckets_685_, v___x_698_, v___x_699_, v_init_683_);
return v___x_700_;
}
}
else
{
size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; 
v___x_701_ = ((size_t)0ULL);
v___x_702_ = lean_usize_of_nat(v___x_687_);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_680_, v___f_693_, v_buckets_685_, v___x_701_, v___x_702_, v_init_683_);
return v___x_703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__0(lean_object* v_f_704_, lean_object* v_x1_705_, lean_object* v_x2_706_, lean_object* v_x3_707_){
_start:
{
lean_object* v___x_708_; 
v___x_708_ = lean_apply_2(v_f_704_, v_x1_705_, v_x2_706_);
return v___x_708_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__1(lean_object* v___x_709_, lean_object* v___f_710_, lean_object* v_acc_711_, lean_object* v_l_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_709_, v___f_710_, v_acc_711_, v_l_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg(lean_object* v_f_714_, lean_object* v_init_715_, lean_object* v_m_716_){
_start:
{
lean_object* v___x_717_; lean_object* v_buckets_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v___x_717_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_718_ = lean_ctor_get(v_m_716_, 1);
lean_inc_ref(v_buckets_718_);
lean_dec_ref(v_m_716_);
v___x_719_ = lean_unsigned_to_nat(0u);
v___x_720_ = lean_array_get_size(v_buckets_718_);
v___x_721_ = lean_nat_dec_lt(v___x_719_, v___x_720_);
if (v___x_721_ == 0)
{
lean_dec_ref(v_buckets_718_);
lean_dec(v_f_714_);
return v_init_715_;
}
else
{
lean_object* v___f_722_; lean_object* v___f_723_; uint8_t v___x_724_; 
v___f_722_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_722_, 0, v_f_714_);
v___f_723_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_723_, 0, v___x_717_);
lean_closure_set(v___f_723_, 1, v___f_722_);
v___x_724_ = lean_nat_dec_le(v___x_720_, v___x_720_);
if (v___x_724_ == 0)
{
if (v___x_721_ == 0)
{
lean_dec_ref(v___f_723_);
lean_dec_ref(v_buckets_718_);
return v_init_715_;
}
else
{
size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___x_725_ = ((size_t)0ULL);
v___x_726_ = lean_usize_of_nat(v___x_720_);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_717_, v___f_723_, v_buckets_718_, v___x_725_, v___x_726_, v_init_715_);
return v___x_727_;
}
}
else
{
size_t v___x_728_; size_t v___x_729_; lean_object* v___x_730_; 
v___x_728_ = ((size_t)0ULL);
v___x_729_ = lean_usize_of_nat(v___x_720_);
v___x_730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_717_, v___f_723_, v_buckets_718_, v___x_728_, v___x_729_, v_init_715_);
return v___x_730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_f_733_, lean_object* v_init_734_, lean_object* v_m_735_){
_start:
{
lean_object* v___x_736_; lean_object* v_buckets_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v___x_736_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_737_ = lean_ctor_get(v_m_735_, 1);
lean_inc_ref(v_buckets_737_);
lean_dec_ref(v_m_735_);
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = lean_array_get_size(v_buckets_737_);
v___x_740_ = lean_nat_dec_lt(v___x_738_, v___x_739_);
if (v___x_740_ == 0)
{
lean_dec_ref(v_buckets_737_);
lean_dec(v_f_733_);
return v_init_734_;
}
else
{
lean_object* v___f_741_; lean_object* v___f_742_; uint8_t v___x_743_; 
v___f_741_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_741_, 0, v_f_733_);
v___f_742_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_742_, 0, v___x_736_);
lean_closure_set(v___f_742_, 1, v___f_741_);
v___x_743_ = lean_nat_dec_le(v___x_739_, v___x_739_);
if (v___x_743_ == 0)
{
if (v___x_740_ == 0)
{
lean_dec_ref(v___f_742_);
lean_dec_ref(v_buckets_737_);
return v_init_734_;
}
else
{
size_t v___x_744_; size_t v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((size_t)0ULL);
v___x_745_ = lean_usize_of_nat(v___x_739_);
v___x_746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_736_, v___f_742_, v_buckets_737_, v___x_744_, v___x_745_, v_init_734_);
return v___x_746_;
}
}
else
{
size_t v___x_747_; size_t v___x_748_; lean_object* v___x_749_; 
v___x_747_ = ((size_t)0ULL);
v___x_748_ = lean_usize_of_nat(v___x_739_);
v___x_749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_736_, v___f_742_, v_buckets_737_, v___x_747_, v___x_748_, v_init_734_);
return v___x_749_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__0(lean_object* v_f_750_, lean_object* v_x_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = lean_apply_1(v_f_750_, v___y_752_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__1(lean_object* v_inst_755_, lean_object* v___f_756_, lean_object* v_x_757_, lean_object* v___y_758_){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = lean_box(0);
v___x_760_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_755_, v___f_756_, v___x_759_, v___y_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg(lean_object* v_inst_761_, lean_object* v_f_762_, lean_object* v_b_763_){
_start:
{
lean_object* v_buckets_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_buckets_764_ = lean_ctor_get(v_b_763_, 1);
lean_inc_ref(v_buckets_764_);
lean_dec_ref(v_b_763_);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_array_get_size(v_buckets_764_);
v___x_767_ = lean_box(0);
v___x_768_ = lean_nat_dec_lt(v___x_765_, v___x_766_);
if (v___x_768_ == 0)
{
lean_object* v_toApplicative_769_; lean_object* v_toPure_770_; lean_object* v___x_771_; 
lean_dec_ref(v_buckets_764_);
lean_dec(v_f_762_);
v_toApplicative_769_ = lean_ctor_get(v_inst_761_, 0);
lean_inc_ref(v_toApplicative_769_);
lean_dec_ref(v_inst_761_);
v_toPure_770_ = lean_ctor_get(v_toApplicative_769_, 1);
lean_inc(v_toPure_770_);
lean_dec_ref(v_toApplicative_769_);
v___x_771_ = lean_apply_2(v_toPure_770_, lean_box(0), v___x_767_);
return v___x_771_;
}
else
{
lean_object* v___f_772_; lean_object* v___f_773_; uint8_t v___x_774_; 
v___f_772_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_772_, 0, v_f_762_);
lean_inc_ref(v_inst_761_);
v___f_773_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_773_, 0, v_inst_761_);
lean_closure_set(v___f_773_, 1, v___f_772_);
v___x_774_ = lean_nat_dec_le(v___x_766_, v___x_766_);
if (v___x_774_ == 0)
{
if (v___x_768_ == 0)
{
lean_object* v_toApplicative_775_; lean_object* v_toPure_776_; lean_object* v___x_777_; 
lean_dec_ref(v___f_773_);
lean_dec_ref(v_buckets_764_);
v_toApplicative_775_ = lean_ctor_get(v_inst_761_, 0);
lean_inc_ref(v_toApplicative_775_);
lean_dec_ref(v_inst_761_);
v_toPure_776_ = lean_ctor_get(v_toApplicative_775_, 1);
lean_inc(v_toPure_776_);
lean_dec_ref(v_toApplicative_775_);
v___x_777_ = lean_apply_2(v_toPure_776_, lean_box(0), v___x_767_);
return v___x_777_;
}
else
{
size_t v___x_778_; size_t v___x_779_; lean_object* v___x_780_; 
v___x_778_ = ((size_t)0ULL);
v___x_779_ = lean_usize_of_nat(v___x_766_);
v___x_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_761_, v___f_773_, v_buckets_764_, v___x_778_, v___x_779_, v___x_767_);
return v___x_780_;
}
}
else
{
size_t v___x_781_; size_t v___x_782_; lean_object* v___x_783_; 
v___x_781_ = ((size_t)0ULL);
v___x_782_ = lean_usize_of_nat(v___x_766_);
v___x_783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_761_, v___f_773_, v_buckets_764_, v___x_781_, v___x_782_, v___x_767_);
return v___x_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM(lean_object* v_00_u03b1_784_, lean_object* v_m_785_, lean_object* v_inst_786_, lean_object* v_f_787_, lean_object* v_b_788_){
_start:
{
lean_object* v_buckets_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; uint8_t v___x_793_; 
v_buckets_789_ = lean_ctor_get(v_b_788_, 1);
lean_inc_ref(v_buckets_789_);
lean_dec_ref(v_b_788_);
v___x_790_ = lean_unsigned_to_nat(0u);
v___x_791_ = lean_array_get_size(v_buckets_789_);
v___x_792_ = lean_box(0);
v___x_793_ = lean_nat_dec_lt(v___x_790_, v___x_791_);
if (v___x_793_ == 0)
{
lean_object* v_toApplicative_794_; lean_object* v_toPure_795_; lean_object* v___x_796_; 
lean_dec_ref(v_buckets_789_);
lean_dec(v_f_787_);
v_toApplicative_794_ = lean_ctor_get(v_inst_786_, 0);
lean_inc_ref(v_toApplicative_794_);
lean_dec_ref(v_inst_786_);
v_toPure_795_ = lean_ctor_get(v_toApplicative_794_, 1);
lean_inc(v_toPure_795_);
lean_dec_ref(v_toApplicative_794_);
v___x_796_ = lean_apply_2(v_toPure_795_, lean_box(0), v___x_792_);
return v___x_796_;
}
else
{
lean_object* v___f_797_; lean_object* v___f_798_; uint8_t v___x_799_; 
v___f_797_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_797_, 0, v_f_787_);
lean_inc_ref(v_inst_786_);
v___f_798_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_798_, 0, v_inst_786_);
lean_closure_set(v___f_798_, 1, v___f_797_);
v___x_799_ = lean_nat_dec_le(v___x_791_, v___x_791_);
if (v___x_799_ == 0)
{
if (v___x_793_ == 0)
{
lean_object* v_toApplicative_800_; lean_object* v_toPure_801_; lean_object* v___x_802_; 
lean_dec_ref(v___f_798_);
lean_dec_ref(v_buckets_789_);
v_toApplicative_800_ = lean_ctor_get(v_inst_786_, 0);
lean_inc_ref(v_toApplicative_800_);
lean_dec_ref(v_inst_786_);
v_toPure_801_ = lean_ctor_get(v_toApplicative_800_, 1);
lean_inc(v_toPure_801_);
lean_dec_ref(v_toApplicative_800_);
v___x_802_ = lean_apply_2(v_toPure_801_, lean_box(0), v___x_792_);
return v___x_802_;
}
else
{
size_t v___x_803_; size_t v___x_804_; lean_object* v___x_805_; 
v___x_803_ = ((size_t)0ULL);
v___x_804_ = lean_usize_of_nat(v___x_791_);
v___x_805_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_786_, v___f_798_, v_buckets_789_, v___x_803_, v___x_804_, v___x_792_);
return v___x_805_;
}
}
else
{
size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_806_ = ((size_t)0ULL);
v___x_807_ = lean_usize_of_nat(v___x_791_);
v___x_808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_786_, v___f_798_, v_buckets_789_, v___x_806_, v___x_807_, v___x_792_);
return v___x_808_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__0(lean_object* v_f_809_, lean_object* v_a_810_, lean_object* v_x_811_, lean_object* v_acc_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = lean_apply_2(v_f_809_, v_a_810_, v_acc_812_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__1(lean_object* v_inst_814_, lean_object* v___f_815_, lean_object* v_a_816_, lean_object* v_x_817_, lean_object* v___y_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_814_, v___f_815_, v_a_816_, v___y_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg(lean_object* v_inst_820_, lean_object* v_f_821_, lean_object* v_init_822_, lean_object* v_b_823_){
_start:
{
lean_object* v_buckets_824_; lean_object* v___f_825_; lean_object* v___f_826_; size_t v_sz_827_; size_t v___x_828_; lean_object* v___x_829_; 
v_buckets_824_ = lean_ctor_get(v_b_823_, 1);
lean_inc_ref(v_buckets_824_);
lean_dec_ref(v_b_823_);
v___f_825_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_825_, 0, v_f_821_);
lean_inc_ref(v_inst_820_);
v___f_826_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_826_, 0, v_inst_820_);
lean_closure_set(v___f_826_, 1, v___f_825_);
v_sz_827_ = lean_array_size(v_buckets_824_);
v___x_828_ = ((size_t)0ULL);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_820_, v_buckets_824_, v___f_826_, v_sz_827_, v___x_828_, v_init_822_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn(lean_object* v_00_u03b1_830_, lean_object* v_m_831_, lean_object* v_inst_832_, lean_object* v_00_u03b2_833_, lean_object* v_f_834_, lean_object* v_init_835_, lean_object* v_b_836_){
_start:
{
lean_object* v_buckets_837_; lean_object* v___f_838_; lean_object* v___f_839_; size_t v_sz_840_; size_t v___x_841_; lean_object* v___x_842_; 
v_buckets_837_ = lean_ctor_get(v_b_836_, 1);
lean_inc_ref(v_buckets_837_);
lean_dec_ref(v_b_836_);
v___f_838_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_838_, 0, v_f_834_);
lean_inc_ref(v_inst_832_);
v___f_839_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_839_, 0, v_inst_832_);
lean_closure_set(v___f_839_, 1, v___f_838_);
v_sz_840_ = lean_array_size(v_buckets_837_);
v___x_841_ = ((size_t)0ULL);
v___x_842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_832_, v_buckets_837_, v___f_839_, v_sz_840_, v___x_841_, v_init_835_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2(lean_object* v_inst_843_, lean_object* v_m_844_, lean_object* v_f_845_){
_start:
{
lean_object* v_buckets_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v_buckets_846_ = lean_ctor_get(v_m_844_, 1);
lean_inc_ref(v_buckets_846_);
lean_dec_ref(v_m_844_);
v___x_847_ = lean_unsigned_to_nat(0u);
v___x_848_ = lean_array_get_size(v_buckets_846_);
v___x_849_ = lean_box(0);
v___x_850_ = lean_nat_dec_lt(v___x_847_, v___x_848_);
if (v___x_850_ == 0)
{
lean_object* v_toApplicative_851_; lean_object* v_toPure_852_; lean_object* v___x_853_; 
lean_dec_ref(v_buckets_846_);
lean_dec(v_f_845_);
v_toApplicative_851_ = lean_ctor_get(v_inst_843_, 0);
lean_inc_ref(v_toApplicative_851_);
lean_dec_ref(v_inst_843_);
v_toPure_852_ = lean_ctor_get(v_toApplicative_851_, 1);
lean_inc(v_toPure_852_);
lean_dec_ref(v_toApplicative_851_);
v___x_853_ = lean_apply_2(v_toPure_852_, lean_box(0), v___x_849_);
return v___x_853_;
}
else
{
lean_object* v___f_854_; lean_object* v___f_855_; uint8_t v___x_856_; 
v___f_854_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_854_, 0, v_f_845_);
lean_inc_ref(v_inst_843_);
v___f_855_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_855_, 0, v_inst_843_);
lean_closure_set(v___f_855_, 1, v___f_854_);
v___x_856_ = lean_nat_dec_le(v___x_848_, v___x_848_);
if (v___x_856_ == 0)
{
if (v___x_850_ == 0)
{
lean_object* v_toApplicative_857_; lean_object* v_toPure_858_; lean_object* v___x_859_; 
lean_dec_ref(v___f_855_);
lean_dec_ref(v_buckets_846_);
v_toApplicative_857_ = lean_ctor_get(v_inst_843_, 0);
lean_inc_ref(v_toApplicative_857_);
lean_dec_ref(v_inst_843_);
v_toPure_858_ = lean_ctor_get(v_toApplicative_857_, 1);
lean_inc(v_toPure_858_);
lean_dec_ref(v_toApplicative_857_);
v___x_859_ = lean_apply_2(v_toPure_858_, lean_box(0), v___x_849_);
return v___x_859_;
}
else
{
size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; 
v___x_860_ = ((size_t)0ULL);
v___x_861_ = lean_usize_of_nat(v___x_848_);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_843_, v___f_855_, v_buckets_846_, v___x_860_, v___x_861_, v___x_849_);
return v___x_862_;
}
}
else
{
size_t v___x_863_; size_t v___x_864_; lean_object* v___x_865_; 
v___x_863_ = ((size_t)0ULL);
v___x_864_ = lean_usize_of_nat(v___x_848_);
v___x_865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_843_, v___f_855_, v_buckets_846_, v___x_863_, v___x_864_, v___x_849_);
return v___x_865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_866_){
_start:
{
lean_object* v___f_867_; 
v___f_867_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_867_, 0, v_inst_866_);
return v___f_867_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_868_, lean_object* v_m_869_, lean_object* v_inst_870_){
_start:
{
lean_object* v___f_871_; 
v___f_871_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_871_, 0, v_inst_870_);
return v___f_871_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_872_, lean_object* v_00_u03b2_873_, lean_object* v_m_874_, lean_object* v_init_875_, lean_object* v_f_876_){
_start:
{
lean_object* v_buckets_877_; lean_object* v___f_878_; lean_object* v___f_879_; size_t v_sz_880_; size_t v___x_881_; lean_object* v___x_882_; 
v_buckets_877_ = lean_ctor_get(v_m_874_, 1);
lean_inc_ref(v_buckets_877_);
lean_dec_ref(v_m_874_);
v___f_878_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_878_, 0, v_f_876_);
lean_inc_ref(v_inst_872_);
v___f_879_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_879_, 0, v_inst_872_);
lean_closure_set(v___f_879_, 1, v___f_878_);
v_sz_880_ = lean_array_size(v_buckets_877_);
v___x_881_ = ((size_t)0ULL);
v___x_882_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_872_, v_buckets_877_, v___f_879_, v_sz_880_, v___x_881_, v_init_875_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_883_){
_start:
{
lean_object* v___f_884_; 
v___f_884_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_884_, 0, v_inst_883_);
return v___f_884_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_885_, lean_object* v_m_886_, lean_object* v_inst_887_){
_start:
{
lean_object* v___f_888_; 
v___f_888_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_888_, 0, v_inst_887_);
return v___f_888_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_filter___redArg___lam__0(lean_object* v_f_889_, lean_object* v_a_890_, lean_object* v_x_891_){
_start:
{
lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_892_ = lean_apply_1(v_f_889_, v_a_890_);
v___x_893_ = lean_unbox(v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_894_, lean_object* v_a_895_, lean_object* v_x_896_){
_start:
{
uint8_t v_res_897_; lean_object* v_r_898_; 
v_res_897_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_894_, v_a_895_, v_x_896_);
v_r_898_ = lean_box(v_res_897_);
return v_r_898_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg(lean_object* v_f_899_, lean_object* v_m_900_){
_start:
{
lean_object* v_buckets_901_; lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v_buckets_901_ = lean_ctor_get(v_m_900_, 1);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_array_get_size(v_buckets_901_);
v___x_904_ = lean_nat_dec_lt(v___x_902_, v___x_903_);
if (v___x_904_ == 0)
{
lean_object* v___x_905_; 
lean_dec_ref(v_m_900_);
lean_dec_ref(v_f_899_);
v___x_905_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
return v___x_905_;
}
else
{
lean_object* v___f_906_; lean_object* v___x_907_; 
v___f_906_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_906_, 0, v_f_899_);
v___x_907_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_906_, v_m_900_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter(lean_object* v_00_u03b1_908_, lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_f_911_, lean_object* v_m_912_){
_start:
{
lean_object* v_buckets_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_buckets_913_ = lean_ctor_get(v_m_912_, 1);
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_array_get_size(v_buckets_913_);
v___x_916_ = lean_nat_dec_lt(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; 
lean_dec_ref(v_m_912_);
lean_dec_ref(v_f_911_);
v___x_917_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
return v___x_917_;
}
else
{
lean_object* v___f_918_; lean_object* v___x_919_; 
v___f_918_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_918_, 0, v_f_911_);
v___x_919_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_918_, v_m_912_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___boxed(lean_object* v_00_u03b1_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_f_923_, lean_object* v_m_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_HashSet_Raw_filter(v_00_u03b1_920_, v_inst_921_, v_inst_922_, v_f_923_, v_m_924_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_inst_921_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__0(lean_object* v_x1_926_, lean_object* v_x2_927_, lean_object* v_x3_928_){
_start:
{
lean_object* v___x_929_; 
v___x_929_ = lean_array_push(v_x1_926_, v_x2_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__1(lean_object* v___x_930_, lean_object* v___f_931_, lean_object* v_acc_932_, lean_object* v_l_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_930_, v___f_931_, v_acc_932_, v_l_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg(lean_object* v_m_939_){
_start:
{
lean_object* v_size_940_; lean_object* v_buckets_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_size_940_ = lean_ctor_get(v_m_939_, 0);
lean_inc(v_size_940_);
v_buckets_941_ = lean_ctor_get(v_m_939_, 1);
lean_inc_ref(v_buckets_941_);
lean_dec_ref(v_m_939_);
v___x_942_ = lean_mk_empty_array_with_capacity(v_size_940_);
lean_dec(v_size_940_);
v___x_943_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_944_ = lean_unsigned_to_nat(0u);
v___x_945_ = lean_array_get_size(v_buckets_941_);
v___x_946_ = lean_nat_dec_lt(v___x_944_, v___x_945_);
if (v___x_946_ == 0)
{
lean_dec_ref(v_buckets_941_);
return v___x_942_;
}
else
{
lean_object* v___f_947_; uint8_t v___x_948_; 
v___f_947_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_948_ = lean_nat_dec_le(v___x_945_, v___x_945_);
if (v___x_948_ == 0)
{
if (v___x_946_ == 0)
{
lean_dec_ref(v_buckets_941_);
return v___x_942_;
}
else
{
size_t v___x_949_; size_t v___x_950_; lean_object* v___x_951_; 
v___x_949_ = ((size_t)0ULL);
v___x_950_ = lean_usize_of_nat(v___x_945_);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_943_, v___f_947_, v_buckets_941_, v___x_949_, v___x_950_, v___x_942_);
return v___x_951_;
}
}
else
{
size_t v___x_952_; size_t v___x_953_; lean_object* v___x_954_; 
v___x_952_ = ((size_t)0ULL);
v___x_953_ = lean_usize_of_nat(v___x_945_);
v___x_954_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_943_, v___f_947_, v_buckets_941_, v___x_952_, v___x_953_, v___x_942_);
return v___x_954_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray(lean_object* v_00_u03b1_955_, lean_object* v_m_956_){
_start:
{
lean_object* v_size_957_; lean_object* v_buckets_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_size_957_ = lean_ctor_get(v_m_956_, 0);
lean_inc(v_size_957_);
v_buckets_958_ = lean_ctor_get(v_m_956_, 1);
lean_inc_ref(v_buckets_958_);
lean_dec_ref(v_m_956_);
v___x_959_ = lean_mk_empty_array_with_capacity(v_size_957_);
lean_dec(v_size_957_);
v___x_960_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_961_ = lean_unsigned_to_nat(0u);
v___x_962_ = lean_array_get_size(v_buckets_958_);
v___x_963_ = lean_nat_dec_lt(v___x_961_, v___x_962_);
if (v___x_963_ == 0)
{
lean_dec_ref(v_buckets_958_);
return v___x_959_;
}
else
{
lean_object* v___f_964_; uint8_t v___x_965_; 
v___f_964_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_965_ = lean_nat_dec_le(v___x_962_, v___x_962_);
if (v___x_965_ == 0)
{
if (v___x_963_ == 0)
{
lean_dec_ref(v_buckets_958_);
return v___x_959_;
}
else
{
size_t v___x_966_; size_t v___x_967_; lean_object* v___x_968_; 
v___x_966_ = ((size_t)0ULL);
v___x_967_ = lean_usize_of_nat(v___x_962_);
v___x_968_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_960_, v___f_964_, v_buckets_958_, v___x_966_, v___x_967_, v___x_959_);
return v___x_968_;
}
}
else
{
size_t v___x_969_; size_t v___x_970_; lean_object* v___x_971_; 
v___x_969_ = ((size_t)0ULL);
v___x_970_ = lean_usize_of_nat(v___x_962_);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_960_, v___f_964_, v_buckets_958_, v___x_969_, v___x_970_, v___x_959_);
return v___x_971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__0(lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_a_974_, lean_object* v_b_975_, lean_object* v_acc_976_){
_start:
{
lean_object* v_r_977_; lean_object* v___x_978_; 
v_r_977_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_972_, v_inst_973_, v_acc_976_, v_a_974_, v_b_975_);
v___x_978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_978_, 0, v_r_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__1(lean_object* v___x_979_, lean_object* v___f_980_, lean_object* v_a_981_, lean_object* v_x_982_, lean_object* v___y_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_979_, v___f_980_, v_a_981_, v___y_983_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg(lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_m_u2081_989_, lean_object* v_m_u2082_990_){
_start:
{
lean_object* v_size_991_; lean_object* v_buckets_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_size_991_ = lean_ctor_get(v_m_u2081_989_, 0);
v_buckets_992_ = lean_ctor_get(v_m_u2081_989_, 1);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get_size(v_buckets_992_);
v___x_995_ = lean_nat_dec_lt(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
lean_dec_ref(v_m_u2081_989_);
lean_dec_ref(v_inst_988_);
lean_dec_ref(v_inst_987_);
return v_m_u2082_990_;
}
else
{
lean_object* v_size_996_; lean_object* v_buckets_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v_size_996_ = lean_ctor_get(v_m_u2082_990_, 0);
v_buckets_997_ = lean_ctor_get(v_m_u2082_990_, 1);
v___x_998_ = lean_array_get_size(v_buckets_997_);
v___x_999_ = lean_nat_dec_lt(v___x_993_, v___x_998_);
if (v___x_999_ == 0)
{
lean_dec_ref(v_m_u2082_990_);
lean_dec_ref(v_inst_988_);
lean_dec_ref(v_inst_987_);
return v_m_u2081_989_;
}
else
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_nat_dec_le(v_size_991_, v_size_996_);
if (v___x_1000_ == 0)
{
lean_object* v___f_1001_; lean_object* v___x_1002_; 
v___f_1001_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1002_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1001_, v_inst_987_, v_inst_988_, v_m_u2081_989_, v_m_u2082_990_);
return v___x_1002_;
}
else
{
lean_object* v___f_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; size_t v_sz_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
lean_inc_ref(v_buckets_992_);
lean_dec_ref(v_m_u2081_989_);
v___f_1003_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1003_, 0, v_inst_987_);
lean_closure_set(v___f_1003_, 1, v_inst_988_);
v___x_1004_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___f_1005_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1005_, 0, v___x_1004_);
lean_closure_set(v___f_1005_, 1, v___f_1003_);
v_sz_1006_ = lean_array_size(v_buckets_992_);
v___x_1007_ = ((size_t)0ULL);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1004_, v_buckets_992_, v___f_1005_, v_sz_1006_, v___x_1007_, v_m_u2082_990_);
return v___x_1008_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union(lean_object* v_00_u03b1_1009_, lean_object* v_inst_1010_, lean_object* v_inst_1011_, lean_object* v_m_u2081_1012_, lean_object* v_m_u2082_1013_){
_start:
{
lean_object* v_size_1014_; lean_object* v_buckets_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_size_1014_ = lean_ctor_get(v_m_u2081_1012_, 0);
v_buckets_1015_ = lean_ctor_get(v_m_u2081_1012_, 1);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_array_get_size(v_buckets_1015_);
v___x_1018_ = lean_nat_dec_lt(v___x_1016_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_dec_ref(v_m_u2081_1012_);
lean_dec_ref(v_inst_1011_);
lean_dec_ref(v_inst_1010_);
return v_m_u2082_1013_;
}
else
{
lean_object* v_size_1019_; lean_object* v_buckets_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_size_1019_ = lean_ctor_get(v_m_u2082_1013_, 0);
v_buckets_1020_ = lean_ctor_get(v_m_u2082_1013_, 1);
v___x_1021_ = lean_array_get_size(v_buckets_1020_);
v___x_1022_ = lean_nat_dec_lt(v___x_1016_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec_ref(v_m_u2082_1013_);
lean_dec_ref(v_inst_1011_);
lean_dec_ref(v_inst_1010_);
return v_m_u2081_1012_;
}
else
{
uint8_t v___x_1023_; 
v___x_1023_ = lean_nat_dec_le(v_size_1014_, v_size_1019_);
if (v___x_1023_ == 0)
{
lean_object* v___f_1024_; lean_object* v___x_1025_; 
v___f_1024_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1025_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1024_, v_inst_1010_, v_inst_1011_, v_m_u2081_1012_, v_m_u2082_1013_);
return v___x_1025_;
}
else
{
lean_object* v___f_1026_; lean_object* v___x_1027_; lean_object* v___f_1028_; size_t v_sz_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
lean_inc_ref(v_buckets_1015_);
lean_dec_ref(v_m_u2081_1012_);
v___f_1026_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1026_, 0, v_inst_1010_);
lean_closure_set(v___f_1026_, 1, v_inst_1011_);
v___x_1027_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___f_1028_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1028_, 0, v___x_1027_);
lean_closure_set(v___f_1028_, 1, v___f_1026_);
v_sz_1029_ = lean_array_size(v_buckets_1015_);
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1027_, v_buckets_1015_, v___f_1028_, v_sz_1029_, v___x_1030_, v_m_u2082_1013_);
return v___x_1031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1032_, lean_object* v_inst_1033_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_1034_, 0, lean_box(0));
lean_closure_set(v___x_1034_, 1, v_inst_1032_);
lean_closure_set(v___x_1034_, 2, v_inst_1033_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1035_, lean_object* v_inst_1036_, lean_object* v_inst_1037_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter___redArg(lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_m_u2081_1041_, lean_object* v_m_u2082_1042_){
_start:
{
lean_object* v_buckets_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_buckets_1043_ = lean_ctor_get(v_m_u2081_1041_, 1);
v___x_1044_ = lean_unsigned_to_nat(0u);
v___x_1045_ = lean_array_get_size(v_buckets_1043_);
v___x_1046_ = lean_nat_dec_lt(v___x_1044_, v___x_1045_);
if (v___x_1046_ == 0)
{
lean_dec_ref(v_m_u2081_1041_);
lean_dec_ref(v_inst_1040_);
lean_dec_ref(v_inst_1039_);
return v_m_u2082_1042_;
}
else
{
lean_object* v_buckets_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v_buckets_1047_ = lean_ctor_get(v_m_u2082_1042_, 1);
v___x_1048_ = lean_array_get_size(v_buckets_1047_);
v___x_1049_ = lean_nat_dec_lt(v___x_1044_, v___x_1048_);
if (v___x_1049_ == 0)
{
lean_dec_ref(v_m_u2082_1042_);
lean_dec_ref(v_inst_1040_);
lean_dec_ref(v_inst_1039_);
return v_m_u2081_1041_;
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1039_, v_inst_1040_, v_m_u2081_1041_, v_m_u2082_1042_);
return v___x_1050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter(lean_object* v_00_u03b1_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_m_u2081_1054_, lean_object* v_m_u2082_1055_){
_start:
{
lean_object* v_buckets_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; uint8_t v___x_1059_; 
v_buckets_1056_ = lean_ctor_get(v_m_u2081_1054_, 1);
v___x_1057_ = lean_unsigned_to_nat(0u);
v___x_1058_ = lean_array_get_size(v_buckets_1056_);
v___x_1059_ = lean_nat_dec_lt(v___x_1057_, v___x_1058_);
if (v___x_1059_ == 0)
{
lean_dec_ref(v_m_u2081_1054_);
lean_dec_ref(v_inst_1053_);
lean_dec_ref(v_inst_1052_);
return v_m_u2082_1055_;
}
else
{
lean_object* v_buckets_1060_; lean_object* v___x_1061_; uint8_t v___x_1062_; 
v_buckets_1060_ = lean_ctor_get(v_m_u2082_1055_, 1);
v___x_1061_ = lean_array_get_size(v_buckets_1060_);
v___x_1062_ = lean_nat_dec_lt(v___x_1057_, v___x_1061_);
if (v___x_1062_ == 0)
{
lean_dec_ref(v_m_u2082_1055_);
lean_dec_ref(v_inst_1053_);
lean_dec_ref(v_inst_1052_);
return v_m_u2081_1054_;
}
else
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1052_, v_inst_1053_, v_m_u2081_1054_, v_m_u2082_1055_);
return v___x_1063_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1064_, lean_object* v_inst_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1066_, 0, lean_box(0));
lean_closure_set(v___x_1066_, 1, v_inst_1064_);
lean_closure_set(v___x_1066_, 2, v_inst_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1067_, lean_object* v_inst_1068_, lean_object* v_inst_1069_){
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
static lean_object* _init_l_Std_HashSet_Raw_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___f_1072_; 
v___x_1071_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1072_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1072_, 0, v___x_1071_);
return v___f_1072_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq___redArg(lean_object* v_inst_1073_, lean_object* v_inst_1074_, lean_object* v_m_u2081_1075_, lean_object* v_m_u2082_1076_){
_start:
{
lean_object* v___f_1077_; uint8_t v___x_1078_; 
v___f_1077_ = lean_obj_once(&l_Std_HashSet_Raw_beq___redArg___closed__0, &l_Std_HashSet_Raw_beq___redArg___closed__0_once, _init_l_Std_HashSet_Raw_beq___redArg___closed__0);
v___x_1078_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1073_, v_inst_1074_, v___f_1077_, v_m_u2081_1075_, v_m_u2082_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___redArg___boxed(lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_m_u2081_1081_, lean_object* v_m_u2082_1082_){
_start:
{
uint8_t v_res_1083_; lean_object* v_r_1084_; 
v_res_1083_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1079_, v_inst_1080_, v_m_u2081_1081_, v_m_u2082_1082_);
v_r_1084_ = lean_box(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq(lean_object* v_00_u03b1_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_, lean_object* v_m_u2081_1088_, lean_object* v_m_u2082_1089_){
_start:
{
uint8_t v___x_1090_; 
v___x_1090_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1086_, v_inst_1087_, v_m_u2081_1088_, v_m_u2082_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___boxed(lean_object* v_00_u03b1_1091_, lean_object* v_inst_1092_, lean_object* v_inst_1093_, lean_object* v_m_u2081_1094_, lean_object* v_m_u2082_1095_){
_start:
{
uint8_t v_res_1096_; lean_object* v_r_1097_; 
v_res_1096_ = l_Std_HashSet_Raw_beq(v_00_u03b1_1091_, v_inst_1092_, v_inst_1093_, v_m_u2081_1094_, v_m_u2082_1095_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1098_, lean_object* v_inst_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1100_, 0, lean_box(0));
lean_closure_set(v___x_1100_, 1, v_inst_1098_);
lean_closure_set(v___x_1100_, 2, v_inst_1099_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_){
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
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_diff___redArg___lam__0(lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_m_u2082_1107_, uint8_t v___x_1108_, lean_object* v_k_1109_, lean_object* v_x_1110_){
_start:
{
uint8_t v___x_1111_; 
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1105_, v_inst_1106_, v_m_u2082_1107_, v_k_1109_);
if (v___x_1111_ == 0)
{
return v___x_1108_;
}
else
{
uint8_t v___x_1112_; 
v___x_1112_ = 0;
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_m_u2082_1115_, lean_object* v___x_1116_, lean_object* v_k_1117_, lean_object* v_x_1118_){
_start:
{
uint8_t v___x_97__boxed_1119_; uint8_t v_res_1120_; lean_object* v_r_1121_; 
v___x_97__boxed_1119_ = lean_unbox(v___x_1116_);
v_res_1120_ = l_Std_HashSet_Raw_diff___redArg___lam__0(v_inst_1113_, v_inst_1114_, v_m_u2082_1115_, v___x_97__boxed_1119_, v_k_1117_, v_x_1118_);
lean_dec_ref(v_m_u2082_1115_);
v_r_1121_ = lean_box(v_res_1120_);
return v_r_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg(lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_m_u2081_1124_, lean_object* v_m_u2082_1125_){
_start:
{
lean_object* v_size_1126_; lean_object* v_buckets_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_size_1126_ = lean_ctor_get(v_m_u2081_1124_, 0);
v_buckets_1127_ = lean_ctor_get(v_m_u2081_1124_, 1);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_array_get_size(v_buckets_1127_);
v___x_1130_ = lean_nat_dec_lt(v___x_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_dec_ref(v_m_u2081_1124_);
lean_dec_ref(v_inst_1123_);
lean_dec_ref(v_inst_1122_);
return v_m_u2082_1125_;
}
else
{
lean_object* v_size_1131_; lean_object* v_buckets_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_size_1131_ = lean_ctor_get(v_m_u2082_1125_, 0);
v_buckets_1132_ = lean_ctor_get(v_m_u2082_1125_, 1);
v___x_1133_ = lean_array_get_size(v_buckets_1132_);
v___x_1134_ = lean_nat_dec_lt(v___x_1128_, v___x_1133_);
if (v___x_1134_ == 0)
{
lean_dec_ref(v_m_u2082_1125_);
lean_dec_ref(v_inst_1123_);
lean_dec_ref(v_inst_1122_);
return v_m_u2081_1124_;
}
else
{
uint8_t v___x_1135_; 
v___x_1135_ = lean_nat_dec_le(v_size_1126_, v_size_1131_);
if (v___x_1135_ == 0)
{
lean_object* v___f_1136_; lean_object* v___x_1137_; 
v___f_1136_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1137_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1136_, v_inst_1122_, v_inst_1123_, v_m_u2081_1124_, v_m_u2082_1125_);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_box(v___x_1135_);
v___f_1139_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1139_, 0, v_inst_1122_);
lean_closure_set(v___f_1139_, 1, v_inst_1123_);
lean_closure_set(v___f_1139_, 2, v_m_u2082_1125_);
lean_closure_set(v___f_1139_, 3, v___x_1138_);
v___x_1140_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1139_, v_m_u2081_1124_);
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff(lean_object* v_00_u03b1_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_m_u2081_1144_, lean_object* v_m_u2082_1145_){
_start:
{
lean_object* v_size_1146_; lean_object* v_buckets_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_size_1146_ = lean_ctor_get(v_m_u2081_1144_, 0);
v_buckets_1147_ = lean_ctor_get(v_m_u2081_1144_, 1);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = lean_array_get_size(v_buckets_1147_);
v___x_1150_ = lean_nat_dec_lt(v___x_1148_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_dec_ref(v_m_u2081_1144_);
lean_dec_ref(v_inst_1143_);
lean_dec_ref(v_inst_1142_);
return v_m_u2082_1145_;
}
else
{
lean_object* v_size_1151_; lean_object* v_buckets_1152_; lean_object* v___x_1153_; uint8_t v___x_1154_; 
v_size_1151_ = lean_ctor_get(v_m_u2082_1145_, 0);
v_buckets_1152_ = lean_ctor_get(v_m_u2082_1145_, 1);
v___x_1153_ = lean_array_get_size(v_buckets_1152_);
v___x_1154_ = lean_nat_dec_lt(v___x_1148_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_dec_ref(v_m_u2082_1145_);
lean_dec_ref(v_inst_1143_);
lean_dec_ref(v_inst_1142_);
return v_m_u2081_1144_;
}
else
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_nat_dec_le(v_size_1146_, v_size_1151_);
if (v___x_1155_ == 0)
{
lean_object* v___f_1156_; lean_object* v___x_1157_; 
v___f_1156_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1157_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1156_, v_inst_1142_, v_inst_1143_, v_m_u2081_1144_, v_m_u2082_1145_);
return v___x_1157_;
}
else
{
lean_object* v___x_1158_; lean_object* v___f_1159_; lean_object* v___x_1160_; 
v___x_1158_ = lean_box(v___x_1155_);
v___f_1159_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1159_, 0, v_inst_1142_);
lean_closure_set(v___f_1159_, 1, v_inst_1143_);
lean_closure_set(v___f_1159_, 2, v_m_u2082_1145_);
lean_closure_set(v___f_1159_, 3, v___x_1158_);
v___x_1160_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1159_, v_m_u2081_1144_);
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1161_, lean_object* v_inst_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1163_, 0, lean_box(0));
lean_closure_set(v___x_1163_, 1, v_inst_1161_);
lean_closure_set(v___x_1163_, 2, v_inst_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0(lean_object* v_p_1168_, lean_object* v___x_1169_, lean_object* v___x_1170_, lean_object* v_a_1171_, lean_object* v_b_1172_, lean_object* v_acc_1173_){
_start:
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_apply_1(v_p_1168_, v_a_1171_);
v___x_1175_ = lean_unbox(v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v___x_1170_);
v___x_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1174_);
v___x_1177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1177_, 0, v___x_1176_);
lean_ctor_set(v___x_1177_, 1, v___x_1169_);
v___x_1178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
return v___x_1178_;
}
else
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1170_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1180_, lean_object* v___x_1181_, lean_object* v___x_1182_, lean_object* v_a_1183_, lean_object* v_b_1184_, lean_object* v_acc_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Std_HashSet_Raw_all___redArg___lam__0(v_p_1180_, v___x_1181_, v___x_1182_, v_a_1183_, v_b_1184_, v_acc_1185_);
lean_dec_ref(v_acc_1185_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__1(lean_object* v___x_1187_, lean_object* v___f_1188_, lean_object* v_a_1189_, lean_object* v_x_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1187_, v___f_1188_, v_a_1189_, v___y_1191_);
return v___x_1192_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all___redArg(lean_object* v_m_1196_, lean_object* v_p_1197_){
_start:
{
lean_object* v___x_1198_; lean_object* v_buckets_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; size_t v_sz_1204_; size_t v___x_1205_; lean_object* v___x_1206_; lean_object* v_fst_1207_; 
v___x_1198_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1199_ = lean_ctor_get(v_m_1196_, 1);
lean_inc_ref(v_buckets_1199_);
lean_dec_ref(v_m_1196_);
v___x_1200_ = lean_box(0);
v___x_1201_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1202_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1202_, 0, v_p_1197_);
lean_closure_set(v___f_1202_, 1, v___x_1200_);
lean_closure_set(v___f_1202_, 2, v___x_1201_);
v___f_1203_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1203_, 0, v___x_1198_);
lean_closure_set(v___f_1203_, 1, v___f_1202_);
v_sz_1204_ = lean_array_size(v_buckets_1199_);
v___x_1205_ = ((size_t)0ULL);
v___x_1206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1198_, v_buckets_1199_, v___f_1203_, v_sz_1204_, v___x_1205_, v___x_1201_);
v_fst_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_fst_1207_);
lean_dec(v___x_1206_);
if (lean_obj_tag(v_fst_1207_) == 0)
{
uint8_t v___x_1208_; 
v___x_1208_ = 1;
return v___x_1208_;
}
else
{
lean_object* v_val_1209_; uint8_t v___x_1210_; 
v_val_1209_ = lean_ctor_get(v_fst_1207_, 0);
lean_inc(v_val_1209_);
lean_dec_ref(v_fst_1207_);
v___x_1210_ = lean_unbox(v_val_1209_);
lean_dec(v_val_1209_);
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___boxed(lean_object* v_m_1211_, lean_object* v_p_1212_){
_start:
{
uint8_t v_res_1213_; lean_object* v_r_1214_; 
v_res_1213_ = l_Std_HashSet_Raw_all___redArg(v_m_1211_, v_p_1212_);
v_r_1214_ = lean_box(v_res_1213_);
return v_r_1214_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all(lean_object* v_00_u03b1_1215_, lean_object* v_m_1216_, lean_object* v_p_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v_buckets_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; size_t v_sz_1224_; size_t v___x_1225_; lean_object* v___x_1226_; lean_object* v_fst_1227_; 
v___x_1218_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1219_ = lean_ctor_get(v_m_1216_, 1);
lean_inc_ref(v_buckets_1219_);
lean_dec_ref(v_m_1216_);
v___x_1220_ = lean_box(0);
v___x_1221_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1222_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1222_, 0, v_p_1217_);
lean_closure_set(v___f_1222_, 1, v___x_1220_);
lean_closure_set(v___f_1222_, 2, v___x_1221_);
v___f_1223_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1223_, 0, v___x_1218_);
lean_closure_set(v___f_1223_, 1, v___f_1222_);
v_sz_1224_ = lean_array_size(v_buckets_1219_);
v___x_1225_ = ((size_t)0ULL);
v___x_1226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1218_, v_buckets_1219_, v___f_1223_, v_sz_1224_, v___x_1225_, v___x_1221_);
v_fst_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_fst_1227_);
lean_dec(v___x_1226_);
if (lean_obj_tag(v_fst_1227_) == 0)
{
uint8_t v___x_1228_; 
v___x_1228_ = 1;
return v___x_1228_;
}
else
{
lean_object* v_val_1229_; uint8_t v___x_1230_; 
v_val_1229_ = lean_ctor_get(v_fst_1227_, 0);
lean_inc(v_val_1229_);
lean_dec_ref(v_fst_1227_);
v___x_1230_ = lean_unbox(v_val_1229_);
lean_dec(v_val_1229_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___boxed(lean_object* v_00_u03b1_1231_, lean_object* v_m_1232_, lean_object* v_p_1233_){
_start:
{
uint8_t v_res_1234_; lean_object* v_r_1235_; 
v_res_1234_ = l_Std_HashSet_Raw_all(v_00_u03b1_1231_, v_m_1232_, v_p_1233_);
v_r_1235_ = lean_box(v_res_1234_);
return v_r_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0(lean_object* v_p_1236_, lean_object* v___x_1237_, lean_object* v___x_1238_, lean_object* v_a_1239_, lean_object* v_b_1240_, lean_object* v_acc_1241_){
_start:
{
lean_object* v___x_1242_; uint8_t v___x_1243_; 
v___x_1242_ = lean_apply_1(v_p_1236_, v_a_1239_);
v___x_1243_ = lean_unbox(v___x_1242_);
if (v___x_1243_ == 0)
{
lean_object* v___x_1244_; 
v___x_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1237_);
return v___x_1244_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec_ref(v___x_1237_);
v___x_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1242_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1245_);
lean_ctor_set(v___x_1246_, 1, v___x_1238_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1248_, lean_object* v___x_1249_, lean_object* v___x_1250_, lean_object* v_a_1251_, lean_object* v_b_1252_, lean_object* v_acc_1253_){
_start:
{
lean_object* v_res_1254_; 
v_res_1254_ = l_Std_HashSet_Raw_any___redArg___lam__0(v_p_1248_, v___x_1249_, v___x_1250_, v_a_1251_, v_b_1252_, v_acc_1253_);
lean_dec_ref(v_acc_1253_);
return v_res_1254_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any___redArg(lean_object* v_m_1255_, lean_object* v_p_1256_){
_start:
{
lean_object* v___x_1257_; lean_object* v_buckets_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___f_1261_; lean_object* v___f_1262_; size_t v_sz_1263_; size_t v___x_1264_; lean_object* v___x_1265_; lean_object* v_fst_1266_; 
v___x_1257_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1258_ = lean_ctor_get(v_m_1255_, 1);
lean_inc_ref(v_buckets_1258_);
lean_dec_ref(v_m_1255_);
v___x_1259_ = lean_box(0);
v___x_1260_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1261_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1261_, 0, v_p_1256_);
lean_closure_set(v___f_1261_, 1, v___x_1260_);
lean_closure_set(v___f_1261_, 2, v___x_1259_);
v___f_1262_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1262_, 0, v___x_1257_);
lean_closure_set(v___f_1262_, 1, v___f_1261_);
v_sz_1263_ = lean_array_size(v_buckets_1258_);
v___x_1264_ = ((size_t)0ULL);
v___x_1265_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1257_, v_buckets_1258_, v___f_1262_, v_sz_1263_, v___x_1264_, v___x_1260_);
v_fst_1266_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_fst_1266_);
lean_dec(v___x_1265_);
if (lean_obj_tag(v_fst_1266_) == 0)
{
uint8_t v___x_1267_; 
v___x_1267_ = 0;
return v___x_1267_;
}
else
{
lean_object* v_val_1268_; uint8_t v___x_1269_; 
v_val_1268_ = lean_ctor_get(v_fst_1266_, 0);
lean_inc(v_val_1268_);
lean_dec_ref(v_fst_1266_);
v___x_1269_ = lean_unbox(v_val_1268_);
lean_dec(v_val_1268_);
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___boxed(lean_object* v_m_1270_, lean_object* v_p_1271_){
_start:
{
uint8_t v_res_1272_; lean_object* v_r_1273_; 
v_res_1272_ = l_Std_HashSet_Raw_any___redArg(v_m_1270_, v_p_1271_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any(lean_object* v_00_u03b1_1274_, lean_object* v_m_1275_, lean_object* v_p_1276_){
_start:
{
lean_object* v___x_1277_; lean_object* v_buckets_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___f_1281_; lean_object* v___f_1282_; size_t v_sz_1283_; size_t v___x_1284_; lean_object* v___x_1285_; lean_object* v_fst_1286_; 
v___x_1277_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1278_ = lean_ctor_get(v_m_1275_, 1);
lean_inc_ref(v_buckets_1278_);
lean_dec_ref(v_m_1275_);
v___x_1279_ = lean_box(0);
v___x_1280_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1281_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1281_, 0, v_p_1276_);
lean_closure_set(v___f_1281_, 1, v___x_1280_);
lean_closure_set(v___f_1281_, 2, v___x_1279_);
v___f_1282_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1282_, 0, v___x_1277_);
lean_closure_set(v___f_1282_, 1, v___f_1281_);
v_sz_1283_ = lean_array_size(v_buckets_1278_);
v___x_1284_ = ((size_t)0ULL);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1277_, v_buckets_1278_, v___f_1282_, v_sz_1283_, v___x_1284_, v___x_1280_);
v_fst_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_fst_1286_);
lean_dec(v___x_1285_);
if (lean_obj_tag(v_fst_1286_) == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = 0;
return v___x_1287_;
}
else
{
lean_object* v_val_1288_; uint8_t v___x_1289_; 
v_val_1288_ = lean_ctor_get(v_fst_1286_, 0);
lean_inc(v_val_1288_);
lean_dec_ref(v_fst_1286_);
v___x_1289_ = lean_unbox(v_val_1288_);
lean_dec(v_val_1288_);
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___boxed(lean_object* v_00_u03b1_1290_, lean_object* v_m_1291_, lean_object* v_p_1292_){
_start:
{
uint8_t v_res_1293_; lean_object* v_r_1294_; 
v_res_1293_ = l_Std_HashSet_Raw_any(v_00_u03b1_1290_, v_m_1291_, v_p_1292_);
v_r_1294_ = lean_box(v_res_1293_);
return v_r_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany___redArg(lean_object* v_inst_1295_, lean_object* v_inst_1296_, lean_object* v_inst_1297_, lean_object* v_m_1298_, lean_object* v_l_1299_){
_start:
{
lean_object* v_buckets_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; uint8_t v___x_1303_; 
v_buckets_1300_ = lean_ctor_get(v_m_1298_, 1);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = lean_array_get_size(v_buckets_1300_);
v___x_1303_ = lean_nat_dec_lt(v___x_1301_, v___x_1302_);
if (v___x_1303_ == 0)
{
lean_dec(v_l_1299_);
lean_dec(v_inst_1297_);
lean_dec_ref(v_inst_1296_);
lean_dec_ref(v_inst_1295_);
return v_m_1298_;
}
else
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1297_, v_inst_1295_, v_inst_1296_, v_m_1298_, v_l_1299_);
return v___x_1304_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany(lean_object* v_00_u03b1_1305_, lean_object* v_inst_1306_, lean_object* v_inst_1307_, lean_object* v_00_u03c1_1308_, lean_object* v_inst_1309_, lean_object* v_m_1310_, lean_object* v_l_1311_){
_start:
{
lean_object* v_buckets_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v_buckets_1312_ = lean_ctor_get(v_m_1310_, 1);
v___x_1313_ = lean_unsigned_to_nat(0u);
v___x_1314_ = lean_array_get_size(v_buckets_1312_);
v___x_1315_ = lean_nat_dec_lt(v___x_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_dec(v_l_1311_);
lean_dec(v_inst_1309_);
lean_dec_ref(v_inst_1307_);
lean_dec_ref(v_inst_1306_);
return v_m_1310_;
}
else
{
lean_object* v___x_1316_; 
v___x_1316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1309_, v_inst_1306_, v_inst_1307_, v_m_1310_, v_l_1311_);
return v___x_1316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray___redArg(lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_l_1323_){
_start:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_1325_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1325_ == 0)
{
lean_dec_ref(v_l_1323_);
lean_dec_ref(v_inst_1322_);
lean_dec_ref(v_inst_1321_);
return v___x_1324_;
}
else
{
lean_object* v___f_1326_; lean_object* v___x_1327_; 
v___f_1326_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1326_, v_inst_1321_, v_inst_1322_, v___x_1324_, v_l_1323_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray(lean_object* v_00_u03b1_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_l_1331_){
_start:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_1333_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1333_ == 0)
{
lean_dec_ref(v_l_1331_);
lean_dec_ref(v_inst_1330_);
lean_dec_ref(v_inst_1329_);
return v___x_1332_;
}
else
{
lean_object* v___f_1334_; lean_object* v___x_1335_; 
v___f_1334_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1335_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1334_, v_inst_1329_, v_inst_1330_, v___x_1332_, v_l_1331_);
return v___x_1335_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg(lean_object* v_m_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Std_HashSet_Raw_Internal_numBuckets___redArg(v_m_1338_);
lean_dec_ref(v_m_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets(lean_object* v_00_u03b1_1340_, lean_object* v_m_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1343_, lean_object* v_m_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Std_HashSet_Raw_Internal_numBuckets(v_00_u03b1_1343_, v_m_1344_);
lean_dec_ref(v_m_1344_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2(lean_object* v_inst_1349_, lean_object* v___f_1350_, lean_object* v_m_1351_, lean_object* v_prec_1352_){
_start:
{
lean_object* v___x_1353_; lean_object* v_buckets_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1374_; 
v___x_1353_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1354_ = lean_ctor_get(v_m_1351_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_m_1351_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v_m_1351_, 0);
lean_dec(v_unused_1375_);
v___x_1356_ = v_m_1351_;
v_isShared_1357_ = v_isSharedCheck_1374_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_buckets_1354_);
lean_dec(v_m_1351_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1374_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1358_; lean_object* v___y_1360_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1358_ = ((lean_object*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1));
v___x_1366_ = lean_box(0);
v___x_1367_ = lean_array_get_size(v_buckets_1354_);
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = lean_nat_dec_lt(v___x_1368_, v___x_1367_);
if (v___x_1369_ == 0)
{
lean_dec_ref(v_buckets_1354_);
lean_dec_ref(v___f_1350_);
v___y_1360_ = v___x_1366_;
goto v___jp_1359_;
}
else
{
lean_object* v___f_1370_; size_t v___x_1371_; size_t v___x_1372_; lean_object* v___x_1373_; 
v___f_1370_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1370_, 0, v___x_1353_);
lean_closure_set(v___f_1370_, 1, v___f_1350_);
v___x_1371_ = lean_usize_of_nat(v___x_1367_);
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1353_, v___f_1370_, v_buckets_1354_, v___x_1371_, v___x_1372_, v___x_1366_);
v___y_1360_ = v___x_1373_;
goto v___jp_1359_;
}
v___jp_1359_:
{
lean_object* v___x_1361_; lean_object* v___x_1363_; 
v___x_1361_ = l_List_repr___redArg(v_inst_1349_, v___y_1360_);
if (v_isShared_1357_ == 0)
{
lean_ctor_set_tag(v___x_1356_, 5);
lean_ctor_set(v___x_1356_, 1, v___x_1361_);
lean_ctor_set(v___x_1356_, 0, v___x_1358_);
v___x_1363_ = v___x_1356_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1361_);
v___x_1363_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Repr_addAppParen(v___x_1363_, v_prec_1352_);
return v___x_1364_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1376_, lean_object* v___f_1377_, lean_object* v_m_1378_, lean_object* v_prec_1379_){
_start:
{
lean_object* v_res_1380_; 
v_res_1380_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2(v_inst_1376_, v___f_1377_, v_m_1378_, v_prec_1379_);
lean_dec(v_prec_1379_);
return v_res_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg(lean_object* v_inst_1381_){
_start:
{
lean_object* v___f_1382_; lean_object* v___f_1383_; 
v___f_1382_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___f_1383_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1383_, 0, v_inst_1381_);
lean_closure_set(v___f_1383_, 1, v___f_1382_);
return v___f_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr(lean_object* v_00_u03b1_1384_, lean_object* v_inst_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Std_HashSet_Raw_instRepr___redArg(v_inst_1385_);
return v___x_1386_;
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
