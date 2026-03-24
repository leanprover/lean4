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
lean_dec_ref(v_a_101_);
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
lean_inc(v_quotContext_107_);
v_currMacroScope_108_ = lean_ctor_get(v_a_101_, 2);
lean_inc(v_currMacroScope_108_);
v_ref_109_ = lean_ctor_get(v_a_101_, 5);
lean_inc(v_ref_109_);
lean_dec_ref(v_a_101_);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = l_Lean_Syntax_getArg(v_x_100_, v___x_110_);
v___x_112_ = lean_unsigned_to_nat(2u);
v___x_113_ = l_Lean_Syntax_getArg(v_x_100_, v___x_112_);
lean_dec(v_x_100_);
v___x_114_ = 0;
v___x_115_ = l_Lean_SourceInfo_fromRef(v_ref_109_, v___x_114_);
lean_dec(v_ref_109_);
v___x_116_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4));
v___x_117_ = lean_obj_once(&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6, &l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6);
v___x_118_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7));
v___x_119_ = l_Lean_addMacroScope(v_quotContext_107_, v___x_118_, v_currMacroScope_108_);
v___x_120_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12));
lean_inc(v___x_115_);
v___x_121_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_121_, 0, v___x_115_);
lean_ctor_set(v___x_121_, 1, v___x_117_);
lean_ctor_set(v___x_121_, 2, v___x_119_);
lean_ctor_set(v___x_121_, 3, v___x_120_);
v___x_122_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14));
lean_inc(v___x_115_);
v___x_123_ = l_Lean_Syntax_node2(v___x_115_, v___x_122_, v___x_111_, v___x_113_);
v___x_124_ = l_Lean_Syntax_node2(v___x_115_, v___x_116_, v___x_121_, v___x_123_);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_a_102_);
return v___x_125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(lean_object* v_x_129_, lean_object* v_a_130_, lean_object* v_a_131_){
_start:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4));
lean_inc(v_x_129_);
v___x_133_ = l_Lean_Syntax_isOfKind(v_x_129_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v_x_129_);
v___x_134_ = lean_box(0);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_a_131_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = l_Lean_Syntax_getArg(v_x_129_, v___x_136_);
v___x_138_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1));
lean_inc(v___x_137_);
v___x_139_ = l_Lean_Syntax_isOfKind(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v___x_137_);
lean_dec(v_x_129_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_a_131_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; uint8_t v___x_145_; 
v___x_142_ = lean_unsigned_to_nat(1u);
v___x_143_ = l_Lean_Syntax_getArg(v_x_129_, v___x_142_);
lean_dec(v_x_129_);
v___x_144_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_143_);
v___x_145_ = l_Lean_Syntax_matchesNull(v___x_143_, v___x_144_);
if (v___x_145_ == 0)
{
lean_object* v___x_146_; lean_object* v___x_147_; 
lean_dec(v___x_143_);
lean_dec(v___x_137_);
v___x_146_ = lean_box(0);
v___x_147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v_a_131_);
return v___x_147_;
}
else
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v_ref_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_148_ = l_Lean_Syntax_getArg(v___x_143_, v___x_136_);
v___x_149_ = l_Lean_Syntax_getArg(v___x_143_, v___x_142_);
lean_dec(v___x_143_);
v_ref_150_ = l_Lean_replaceRef(v___x_137_, v_a_130_);
lean_dec(v___x_137_);
v___x_151_ = 0;
v___x_152_ = l_Lean_SourceInfo_fromRef(v_ref_150_, v___x_151_);
lean_dec(v_ref_150_);
v___x_153_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__4));
v___x_154_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__7));
lean_inc(v___x_152_);
v___x_155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_152_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = l_Lean_Syntax_node3(v___x_152_, v___x_153_, v___x_148_, v___x_155_, v___x_149_);
v___x_157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_131_);
return v___x_157_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___boxed(lean_object* v_x_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(v_x_158_, v_a_159_, v_a_160_);
lean_dec(v_a_159_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert___redArg(lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_m_164_, lean_object* v_a_165_){
_start:
{
lean_object* v_buckets_166_; lean_object* v___x_167_; lean_object* v___x_168_; uint8_t v___x_169_; 
v_buckets_166_ = lean_ctor_get(v_m_164_, 1);
v___x_167_ = lean_unsigned_to_nat(0u);
v___x_168_ = lean_array_get_size(v_buckets_166_);
v___x_169_ = lean_nat_dec_lt(v___x_167_, v___x_168_);
if (v___x_169_ == 0)
{
lean_dec(v_a_165_);
lean_dec_ref(v_inst_163_);
lean_dec_ref(v_inst_162_);
return v_m_164_;
}
else
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_box(0);
v___x_171_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_162_, v_inst_163_, v_m_164_, v_a_165_, v___x_170_);
return v___x_171_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert(lean_object* v_00_u03b1_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_m_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_buckets_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_buckets_177_ = lean_ctor_get(v_m_175_, 1);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_array_get_size(v_buckets_177_);
v___x_180_ = lean_nat_dec_lt(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_dec(v_a_176_);
lean_dec_ref(v_inst_174_);
lean_dec_ref(v_inst_173_);
return v_m_175_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_box(0);
v___x_182_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_173_, v_inst_174_, v_m_175_, v_a_176_, v___x_181_);
return v___x_182_;
}
}
}
static lean_object* _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__0, &l_Std_HashSet_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0);
v___x_184_ = lean_array_get_size(v___x_183_);
return v___x_184_;
}
}
static uint8_t _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; uint8_t v___x_187_; 
v___x_185_ = lean_obj_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_186_ = lean_unsigned_to_nat(0u);
v___x_187_ = lean_nat_dec_lt(v___x_186_, v___x_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_a_190_){
_start:
{
lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_191_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_192_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_192_ == 0)
{
lean_dec(v_a_190_);
lean_dec_ref(v_inst_189_);
lean_dec_ref(v_inst_188_);
return v___x_191_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = lean_box(0);
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_188_, v_inst_189_, v___x_191_, v_a_190_, v___x_193_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg(lean_object* v_inst_195_, lean_object* v_inst_196_){
_start:
{
lean_object* v___f_197_; 
v___f_197_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_197_, 0, v_inst_195_);
lean_closure_set(v___f_197_, 1, v_inst_196_);
return v___f_197_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_, lean_object* v_inst_200_){
_start:
{
lean_object* v___f_201_; 
v___f_201_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_201_, 0, v_inst_199_);
lean_closure_set(v___f_201_, 1, v_inst_200_);
return v___f_201_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_a_204_, lean_object* v_s_205_){
_start:
{
lean_object* v_buckets_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; 
v_buckets_206_ = lean_ctor_get(v_s_205_, 1);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_208_ = lean_array_get_size(v_buckets_206_);
v___x_209_ = lean_nat_dec_lt(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_dec(v_a_204_);
lean_dec_ref(v_inst_203_);
lean_dec_ref(v_inst_202_);
return v_s_205_;
}
else
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_box(0);
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_202_, v_inst_203_, v_s_205_, v_a_204_, v___x_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg(lean_object* v_inst_212_, lean_object* v_inst_213_){
_start:
{
lean_object* v___f_214_; 
v___f_214_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_214_, 0, v_inst_212_);
lean_closure_set(v___f_214_, 1, v_inst_213_);
return v___f_214_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable(lean_object* v_00_u03b1_215_, lean_object* v_inst_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___f_218_; 
v___f_218_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_218_, 0, v_inst_216_);
lean_closure_set(v___f_218_, 1, v_inst_217_);
return v___f_218_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert___redArg(lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_m_221_, lean_object* v_a_222_){
_start:
{
lean_object* v_size_223_; lean_object* v_buckets_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_size_223_ = lean_ctor_get(v_m_221_, 0);
v_buckets_224_ = lean_ctor_get(v_m_221_, 1);
v___x_225_ = lean_unsigned_to_nat(0u);
v___x_226_ = lean_array_get_size(v_buckets_224_);
v___x_227_ = lean_nat_dec_lt(v___x_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; lean_object* v___x_229_; 
lean_dec(v_a_222_);
lean_dec_ref(v_inst_220_);
lean_dec_ref(v_inst_219_);
v___x_228_ = lean_box(v___x_227_);
v___x_229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v_m_221_);
return v___x_229_;
}
else
{
lean_object* v___x_230_; uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v_fold_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; lean_object* v_bkt_244_; uint8_t v___x_245_; 
lean_inc_ref(v_inst_220_);
lean_inc(v_a_222_);
v___x_230_ = lean_apply_1(v_inst_220_, v_a_222_);
v___x_231_ = 32ULL;
v___x_232_ = lean_unbox_uint64(v___x_230_);
v___x_233_ = lean_uint64_shift_right(v___x_232_, v___x_231_);
v___x_234_ = lean_unbox_uint64(v___x_230_);
lean_dec_ref(v___x_230_);
v_fold_235_ = lean_uint64_xor(v___x_234_, v___x_233_);
v___x_236_ = 16ULL;
v___x_237_ = lean_uint64_shift_right(v_fold_235_, v___x_236_);
v___x_238_ = lean_uint64_xor(v_fold_235_, v___x_237_);
v___x_239_ = lean_uint64_to_usize(v___x_238_);
v___x_240_ = lean_usize_of_nat(v___x_226_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_sub(v___x_240_, v___x_241_);
v___x_243_ = lean_usize_land(v___x_239_, v___x_242_);
v_bkt_244_ = lean_array_uget_borrowed(v_buckets_224_, v___x_243_);
lean_inc(v_bkt_244_);
lean_inc(v_a_222_);
v___x_245_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_219_, v_a_222_, v_bkt_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_271_; 
lean_inc_ref(v_buckets_224_);
lean_inc(v_size_223_);
v_isSharedCheck_271_ = !lean_is_exclusive(v_m_221_);
if (v_isSharedCheck_271_ == 0)
{
lean_object* v_unused_272_; lean_object* v_unused_273_; 
v_unused_272_ = lean_ctor_get(v_m_221_, 1);
lean_dec(v_unused_272_);
v_unused_273_ = lean_ctor_get(v_m_221_, 0);
lean_dec(v_unused_273_);
v___x_247_ = v_m_221_;
v_isShared_248_ = v_isSharedCheck_271_;
goto v_resetjp_246_;
}
else
{
lean_dec(v_m_221_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_271_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v_size_x27_251_; lean_object* v___x_252_; lean_object* v_buckets_x27_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_249_ = lean_box(0);
v___x_250_ = lean_unsigned_to_nat(1u);
v_size_x27_251_ = lean_nat_add(v_size_223_, v___x_250_);
lean_dec(v_size_223_);
lean_inc(v_bkt_244_);
v___x_252_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_252_, 0, v_a_222_);
lean_ctor_set(v___x_252_, 1, v___x_249_);
lean_ctor_set(v___x_252_, 2, v_bkt_244_);
v_buckets_x27_253_ = lean_array_uset(v_buckets_224_, v___x_243_, v___x_252_);
v___x_254_ = lean_unsigned_to_nat(4u);
v___x_255_ = lean_nat_mul(v_size_x27_251_, v___x_254_);
v___x_256_ = lean_unsigned_to_nat(3u);
v___x_257_ = lean_nat_div(v___x_255_, v___x_256_);
lean_dec(v___x_255_);
v___x_258_ = lean_array_get_size(v_buckets_x27_253_);
v___x_259_ = lean_nat_dec_le(v___x_257_, v___x_258_);
lean_dec(v___x_257_);
if (v___x_259_ == 0)
{
lean_object* v_val_260_; lean_object* v___x_262_; 
v_val_260_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_220_, v_buckets_x27_253_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_val_260_);
lean_ctor_set(v___x_247_, 0, v_size_x27_251_);
v___x_262_ = v___x_247_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v_size_x27_251_);
lean_ctor_set(v_reuseFailAlloc_265_, 1, v_val_260_);
v___x_262_ = v_reuseFailAlloc_265_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_box(v___x_245_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
return v___x_264_;
}
}
else
{
lean_object* v___x_267_; 
lean_dec_ref(v_inst_220_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_buckets_x27_253_);
lean_ctor_set(v___x_247_, 0, v_size_x27_251_);
v___x_267_ = v___x_247_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_size_x27_251_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_buckets_x27_253_);
v___x_267_ = v_reuseFailAlloc_270_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_box(v___x_245_);
v___x_269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
return v___x_269_;
}
}
}
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec(v_a_222_);
lean_dec_ref(v_inst_220_);
v___x_274_ = lean_box(v___x_245_);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v_m_221_);
return v___x_275_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert(lean_object* v_00_u03b1_276_, lean_object* v_inst_277_, lean_object* v_inst_278_, lean_object* v_m_279_, lean_object* v_a_280_){
_start:
{
lean_object* v_size_281_; lean_object* v_buckets_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_size_281_ = lean_ctor_get(v_m_279_, 0);
v_buckets_282_ = lean_ctor_get(v_m_279_, 1);
v___x_283_ = lean_unsigned_to_nat(0u);
v___x_284_ = lean_array_get_size(v_buckets_282_);
v___x_285_ = lean_nat_dec_lt(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_a_280_);
lean_dec_ref(v_inst_278_);
lean_dec_ref(v_inst_277_);
v___x_286_ = lean_box(v___x_285_);
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_m_279_);
return v___x_287_;
}
else
{
lean_object* v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v___x_291_; uint64_t v___x_292_; uint64_t v_fold_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; size_t v___x_301_; lean_object* v_bkt_302_; uint8_t v___x_303_; 
lean_inc_ref(v_inst_278_);
lean_inc(v_a_280_);
v___x_288_ = lean_apply_1(v_inst_278_, v_a_280_);
v___x_289_ = 32ULL;
v___x_290_ = lean_unbox_uint64(v___x_288_);
v___x_291_ = lean_uint64_shift_right(v___x_290_, v___x_289_);
v___x_292_ = lean_unbox_uint64(v___x_288_);
lean_dec_ref(v___x_288_);
v_fold_293_ = lean_uint64_xor(v___x_292_, v___x_291_);
v___x_294_ = 16ULL;
v___x_295_ = lean_uint64_shift_right(v_fold_293_, v___x_294_);
v___x_296_ = lean_uint64_xor(v_fold_293_, v___x_295_);
v___x_297_ = lean_uint64_to_usize(v___x_296_);
v___x_298_ = lean_usize_of_nat(v___x_284_);
v___x_299_ = ((size_t)1ULL);
v___x_300_ = lean_usize_sub(v___x_298_, v___x_299_);
v___x_301_ = lean_usize_land(v___x_297_, v___x_300_);
v_bkt_302_ = lean_array_uget_borrowed(v_buckets_282_, v___x_301_);
lean_inc(v_bkt_302_);
lean_inc(v_a_280_);
v___x_303_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_277_, v_a_280_, v_bkt_302_);
if (v___x_303_ == 0)
{
lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_329_; 
lean_inc_ref(v_buckets_282_);
lean_inc(v_size_281_);
v_isSharedCheck_329_ = !lean_is_exclusive(v_m_279_);
if (v_isSharedCheck_329_ == 0)
{
lean_object* v_unused_330_; lean_object* v_unused_331_; 
v_unused_330_ = lean_ctor_get(v_m_279_, 1);
lean_dec(v_unused_330_);
v_unused_331_ = lean_ctor_get(v_m_279_, 0);
lean_dec(v_unused_331_);
v___x_305_ = v_m_279_;
v_isShared_306_ = v_isSharedCheck_329_;
goto v_resetjp_304_;
}
else
{
lean_dec(v_m_279_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_329_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v_size_x27_309_; lean_object* v___x_310_; lean_object* v_buckets_x27_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_307_ = lean_box(0);
v___x_308_ = lean_unsigned_to_nat(1u);
v_size_x27_309_ = lean_nat_add(v_size_281_, v___x_308_);
lean_dec(v_size_281_);
lean_inc(v_bkt_302_);
v___x_310_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_310_, 0, v_a_280_);
lean_ctor_set(v___x_310_, 1, v___x_307_);
lean_ctor_set(v___x_310_, 2, v_bkt_302_);
v_buckets_x27_311_ = lean_array_uset(v_buckets_282_, v___x_301_, v___x_310_);
v___x_312_ = lean_unsigned_to_nat(4u);
v___x_313_ = lean_nat_mul(v_size_x27_309_, v___x_312_);
v___x_314_ = lean_unsigned_to_nat(3u);
v___x_315_ = lean_nat_div(v___x_313_, v___x_314_);
lean_dec(v___x_313_);
v___x_316_ = lean_array_get_size(v_buckets_x27_311_);
v___x_317_ = lean_nat_dec_le(v___x_315_, v___x_316_);
lean_dec(v___x_315_);
if (v___x_317_ == 0)
{
lean_object* v_val_318_; lean_object* v___x_320_; 
v_val_318_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_278_, v_buckets_x27_311_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_val_318_);
lean_ctor_set(v___x_305_, 0, v_size_x27_309_);
v___x_320_ = v___x_305_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_323_; 
v_reuseFailAlloc_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_323_, 0, v_size_x27_309_);
lean_ctor_set(v_reuseFailAlloc_323_, 1, v_val_318_);
v___x_320_ = v_reuseFailAlloc_323_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_321_ = lean_box(v___x_303_);
v___x_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_320_);
return v___x_322_;
}
}
else
{
lean_object* v___x_325_; 
lean_dec_ref(v_inst_278_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 1, v_buckets_x27_311_);
lean_ctor_set(v___x_305_, 0, v_size_x27_309_);
v___x_325_ = v___x_305_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v_size_x27_309_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v_buckets_x27_311_);
v___x_325_ = v_reuseFailAlloc_328_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_box(v___x_303_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
return v___x_327_;
}
}
}
}
else
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_dec(v_a_280_);
lean_dec_ref(v_inst_278_);
v___x_332_ = lean_box(v___x_303_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_m_279_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains___redArg(lean_object* v_inst_334_, lean_object* v_inst_335_, lean_object* v_m_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_buckets_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v_buckets_338_ = lean_ctor_get(v_m_336_, 1);
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = lean_array_get_size(v_buckets_338_);
v___x_341_ = lean_nat_dec_lt(v___x_339_, v___x_340_);
if (v___x_341_ == 0)
{
lean_dec(v_a_337_);
lean_dec_ref(v_inst_335_);
lean_dec_ref(v_inst_334_);
return v___x_341_;
}
else
{
uint8_t v___x_342_; 
v___x_342_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_334_, v_inst_335_, v_m_336_, v_a_337_);
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___redArg___boxed(lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_m_345_, lean_object* v_a_346_){
_start:
{
uint8_t v_res_347_; lean_object* v_r_348_; 
v_res_347_ = l_Std_HashSet_Raw_contains___redArg(v_inst_343_, v_inst_344_, v_m_345_, v_a_346_);
lean_dec_ref(v_m_345_);
v_r_348_ = lean_box(v_res_347_);
return v_r_348_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains(lean_object* v_00_u03b1_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_m_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_buckets_354_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_357_; 
v_buckets_354_ = lean_ctor_get(v_m_352_, 1);
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = lean_array_get_size(v_buckets_354_);
v___x_357_ = lean_nat_dec_lt(v___x_355_, v___x_356_);
if (v___x_357_ == 0)
{
lean_dec(v_a_353_);
lean_dec_ref(v_inst_351_);
lean_dec_ref(v_inst_350_);
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_350_, v_inst_351_, v_m_352_, v_a_353_);
return v___x_358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___boxed(lean_object* v_00_u03b1_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_m_362_, lean_object* v_a_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Std_HashSet_Raw_contains(v_00_u03b1_359_, v_inst_360_, v_inst_361_, v_m_362_, v_a_363_);
lean_dec_ref(v_m_362_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_366_, lean_object* v_inst_367_, lean_object* v_inst_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = lean_box(0);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_370_, lean_object* v_inst_371_, lean_object* v_inst_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_370_, v_inst_371_, v_inst_372_);
lean_dec_ref(v_inst_372_);
lean_dec_ref(v_inst_371_);
return v_res_373_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem___redArg(lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_m_376_, lean_object* v_a_377_){
_start:
{
uint8_t v___x_378_; 
v___x_378_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_374_, v_inst_375_, v_m_376_, v_a_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_m_381_, lean_object* v_a_382_){
_start:
{
uint8_t v_res_383_; lean_object* v_r_384_; 
v_res_383_ = l_Std_HashSet_Raw_instDecidableMem___redArg(v_inst_379_, v_inst_380_, v_m_381_, v_a_382_);
lean_dec_ref(v_m_381_);
v_r_384_ = lean_box(v_res_383_);
return v_r_384_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem(lean_object* v_00_u03b1_385_, lean_object* v_inst_386_, lean_object* v_inst_387_, lean_object* v_m_388_, lean_object* v_a_389_){
_start:
{
uint8_t v___x_390_; 
v___x_390_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_386_, v_inst_387_, v_m_388_, v_a_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_m_394_, lean_object* v_a_395_){
_start:
{
uint8_t v_res_396_; lean_object* v_r_397_; 
v_res_396_ = l_Std_HashSet_Raw_instDecidableMem(v_00_u03b1_391_, v_inst_392_, v_inst_393_, v_m_394_, v_a_395_);
lean_dec_ref(v_m_394_);
v_r_397_ = lean_box(v_res_396_);
return v_r_397_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase___redArg(lean_object* v_inst_398_, lean_object* v_inst_399_, lean_object* v_m_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_buckets_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v_buckets_402_ = lean_ctor_get(v_m_400_, 1);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_array_get_size(v_buckets_402_);
v___x_405_ = lean_nat_dec_lt(v___x_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_dec(v_a_401_);
lean_dec_ref(v_inst_399_);
lean_dec_ref(v_inst_398_);
return v_m_400_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_398_, v_inst_399_, v_m_400_, v_a_401_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase(lean_object* v_00_u03b1_407_, lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_m_410_, lean_object* v_a_411_){
_start:
{
lean_object* v_buckets_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_buckets_412_ = lean_ctor_get(v_m_410_, 1);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_array_get_size(v_buckets_412_);
v___x_415_ = lean_nat_dec_lt(v___x_413_, v___x_414_);
if (v___x_415_ == 0)
{
lean_dec(v_a_411_);
lean_dec_ref(v_inst_409_);
lean_dec_ref(v_inst_408_);
return v_m_410_;
}
else
{
lean_object* v___x_416_; 
v___x_416_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_408_, v_inst_409_, v_m_410_, v_a_411_);
return v___x_416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg(lean_object* v_m_417_){
_start:
{
lean_object* v_size_418_; 
v_size_418_ = lean_ctor_get(v_m_417_, 0);
lean_inc(v_size_418_);
return v_size_418_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg___boxed(lean_object* v_m_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Std_HashSet_Raw_size___redArg(v_m_419_);
lean_dec_ref(v_m_419_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size(lean_object* v_00_u03b1_421_, lean_object* v_m_422_){
_start:
{
lean_object* v_size_423_; 
v_size_423_ = lean_ctor_get(v_m_422_, 0);
lean_inc(v_size_423_);
return v_size_423_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___boxed(lean_object* v_00_u03b1_424_, lean_object* v_m_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_Std_HashSet_Raw_size(v_00_u03b1_424_, v_m_425_);
lean_dec_ref(v_m_425_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg(lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_m_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_buckets_431_; lean_object* v___x_432_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_buckets_431_ = lean_ctor_get(v_m_429_, 1);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_array_get_size(v_buckets_431_);
v___x_434_ = lean_nat_dec_lt(v___x_432_, v___x_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; 
lean_dec(v_a_430_);
lean_dec_ref(v_inst_428_);
lean_dec_ref(v_inst_427_);
v___x_435_ = lean_box(0);
return v___x_435_;
}
else
{
lean_object* v___x_436_; 
v___x_436_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_427_, v_inst_428_, v_m_429_, v_a_430_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg___boxed(lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_m_439_, lean_object* v_a_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_HashSet_Raw_get_x3f___redArg(v_inst_437_, v_inst_438_, v_m_439_, v_a_440_);
lean_dec_ref(v_m_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f(lean_object* v_00_u03b1_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_m_445_, lean_object* v_a_446_){
_start:
{
lean_object* v_buckets_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_buckets_447_ = lean_ctor_get(v_m_445_, 1);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_get_size(v_buckets_447_);
v___x_450_ = lean_nat_dec_lt(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
lean_dec(v_a_446_);
lean_dec_ref(v_inst_444_);
lean_dec_ref(v_inst_443_);
v___x_451_ = lean_box(0);
return v___x_451_;
}
else
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_443_, v_inst_444_, v_m_445_, v_a_446_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___boxed(lean_object* v_00_u03b1_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_m_456_, lean_object* v_a_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_HashSet_Raw_get_x3f(v_00_u03b1_453_, v_inst_454_, v_inst_455_, v_m_456_, v_a_457_);
lean_dec_ref(v_m_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg(lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_m_461_, lean_object* v_a_462_){
_start:
{
lean_object* v___x_463_; 
v___x_463_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_459_, v_inst_460_, v_m_461_, v_a_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg___boxed(lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_m_466_, lean_object* v_a_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_Std_HashSet_Raw_get___redArg(v_inst_464_, v_inst_465_, v_m_466_, v_a_467_);
lean_dec_ref(v_m_466_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get(lean_object* v_00_u03b1_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_m_472_, lean_object* v_a_473_, lean_object* v_h_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_470_, v_inst_471_, v_m_472_, v_a_473_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___boxed(lean_object* v_00_u03b1_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_m_479_, lean_object* v_a_480_, lean_object* v_h_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_HashSet_Raw_get(v_00_u03b1_476_, v_inst_477_, v_inst_478_, v_m_479_, v_a_480_, v_h_481_);
lean_dec_ref(v_m_479_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg(lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_m_485_, lean_object* v_a_486_, lean_object* v_fallback_487_){
_start:
{
lean_object* v_buckets_488_; lean_object* v___x_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_buckets_488_ = lean_ctor_get(v_m_485_, 1);
v___x_489_ = lean_unsigned_to_nat(0u);
v___x_490_ = lean_array_get_size(v_buckets_488_);
v___x_491_ = lean_nat_dec_lt(v___x_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_dec(v_a_486_);
lean_dec_ref(v_inst_484_);
lean_dec_ref(v_inst_483_);
lean_inc(v_fallback_487_);
return v_fallback_487_;
}
else
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_483_, v_inst_484_, v_m_485_, v_a_486_, v_fallback_487_);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg___boxed(lean_object* v_inst_493_, lean_object* v_inst_494_, lean_object* v_m_495_, lean_object* v_a_496_, lean_object* v_fallback_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_HashSet_Raw_getD___redArg(v_inst_493_, v_inst_494_, v_m_495_, v_a_496_, v_fallback_497_);
lean_dec(v_fallback_497_);
lean_dec_ref(v_m_495_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD(lean_object* v_00_u03b1_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_m_502_, lean_object* v_a_503_, lean_object* v_fallback_504_){
_start:
{
lean_object* v_buckets_505_; lean_object* v___x_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_buckets_505_ = lean_ctor_get(v_m_502_, 1);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = lean_array_get_size(v_buckets_505_);
v___x_508_ = lean_nat_dec_lt(v___x_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_dec(v_a_503_);
lean_dec_ref(v_inst_501_);
lean_dec_ref(v_inst_500_);
lean_inc(v_fallback_504_);
return v_fallback_504_;
}
else
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_500_, v_inst_501_, v_m_502_, v_a_503_, v_fallback_504_);
return v___x_509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___boxed(lean_object* v_00_u03b1_510_, lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_m_513_, lean_object* v_a_514_, lean_object* v_fallback_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_HashSet_Raw_getD(v_00_u03b1_510_, v_inst_511_, v_inst_512_, v_m_513_, v_a_514_, v_fallback_515_);
lean_dec(v_fallback_515_);
lean_dec_ref(v_m_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg(lean_object* v_inst_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_m_520_, lean_object* v_a_521_){
_start:
{
lean_object* v_buckets_522_; lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v_buckets_522_ = lean_ctor_get(v_m_520_, 1);
v___x_523_ = lean_unsigned_to_nat(0u);
v___x_524_ = lean_array_get_size(v_buckets_522_);
v___x_525_ = lean_nat_dec_lt(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v_a_521_);
lean_dec_ref(v_inst_518_);
lean_dec_ref(v_inst_517_);
return v_inst_519_;
}
else
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_517_, v_inst_518_, v_inst_519_, v_m_520_, v_a_521_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg___boxed(lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_m_530_, lean_object* v_a_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_HashSet_Raw_get_x21___redArg(v_inst_527_, v_inst_528_, v_inst_529_, v_m_530_, v_a_531_);
lean_dec_ref(v_m_530_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21(lean_object* v_00_u03b1_533_, lean_object* v_inst_534_, lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_m_537_, lean_object* v_a_538_){
_start:
{
lean_object* v_buckets_539_; lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_buckets_539_ = lean_ctor_get(v_m_537_, 1);
v___x_540_ = lean_unsigned_to_nat(0u);
v___x_541_ = lean_array_get_size(v_buckets_539_);
v___x_542_ = lean_nat_dec_lt(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_dec(v_a_538_);
lean_dec_ref(v_inst_535_);
lean_dec_ref(v_inst_534_);
return v_inst_536_;
}
else
{
lean_object* v___x_543_; 
v___x_543_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_534_, v_inst_535_, v_inst_536_, v_m_537_, v_a_538_);
return v___x_543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___boxed(lean_object* v_00_u03b1_544_, lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_m_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_HashSet_Raw_get_x21(v_00_u03b1_544_, v_inst_545_, v_inst_546_, v_inst_547_, v_m_548_, v_a_549_);
lean_dec_ref(v_m_548_);
return v_res_550_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty___redArg(lean_object* v_m_551_){
_start:
{
lean_object* v_size_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_size_552_ = lean_ctor_get(v_m_551_, 0);
v___x_553_ = lean_unsigned_to_nat(0u);
v___x_554_ = lean_nat_dec_eq(v_size_552_, v___x_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___redArg___boxed(lean_object* v_m_555_){
_start:
{
uint8_t v_res_556_; lean_object* v_r_557_; 
v_res_556_ = l_Std_HashSet_Raw_isEmpty___redArg(v_m_555_);
lean_dec_ref(v_m_555_);
v_r_557_ = lean_box(v_res_556_);
return v_r_557_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty(lean_object* v_00_u03b1_558_, lean_object* v_m_559_){
_start:
{
lean_object* v_size_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_size_560_ = lean_ctor_get(v_m_559_, 0);
v___x_561_ = lean_unsigned_to_nat(0u);
v___x_562_ = lean_nat_dec_eq(v_size_560_, v___x_561_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_563_, lean_object* v_m_564_){
_start:
{
uint8_t v_res_565_; lean_object* v_r_566_; 
v_res_565_ = l_Std_HashSet_Raw_isEmpty(v_00_u03b1_563_, v_m_564_);
lean_dec_ref(v_m_564_);
v_r_566_ = lean_box(v_res_565_);
return v_r_566_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__0(lean_object* v_a_567_, lean_object* v_b_568_, lean_object* v_d_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_570_, 0, v_a_567_);
lean_ctor_set(v___x_570_, 1, v_d_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__1(lean_object* v___x_571_, lean_object* v___f_572_, lean_object* v_l_573_, lean_object* v_acc_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_571_, v___f_572_, v_acc_574_, v_l_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg(lean_object* v_m_599_){
_start:
{
lean_object* v___x_600_; lean_object* v_buckets_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_600_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_601_ = lean_ctor_get(v_m_599_, 1);
lean_inc_ref(v_buckets_601_);
lean_dec_ref(v_m_599_);
v___x_602_ = lean_box(0);
v___x_603_ = lean_array_get_size(v_buckets_601_);
v___x_604_ = lean_unsigned_to_nat(0u);
v___x_605_ = lean_nat_dec_lt(v___x_604_, v___x_603_);
if (v___x_605_ == 0)
{
lean_dec_ref(v_buckets_601_);
return v___x_602_;
}
else
{
lean_object* v___f_606_; size_t v___x_607_; size_t v___x_608_; lean_object* v___x_609_; 
v___f_606_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__11));
v___x_607_ = lean_usize_of_nat(v___x_603_);
v___x_608_ = ((size_t)0ULL);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_600_, v___f_606_, v_buckets_601_, v___x_607_, v___x_608_, v___x_602_);
return v___x_609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList(lean_object* v_00_u03b1_610_, lean_object* v_m_611_){
_start:
{
lean_object* v___x_612_; lean_object* v_buckets_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_612_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_613_ = lean_ctor_get(v_m_611_, 1);
lean_inc_ref(v_buckets_613_);
lean_dec_ref(v_m_611_);
v___x_614_ = lean_box(0);
v___x_615_ = lean_array_get_size(v_buckets_613_);
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = lean_nat_dec_lt(v___x_616_, v___x_615_);
if (v___x_617_ == 0)
{
lean_dec_ref(v_buckets_613_);
return v___x_614_;
}
else
{
lean_object* v___f_618_; size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; 
v___f_618_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__11));
v___x_619_ = lean_usize_of_nat(v___x_615_);
v___x_620_ = ((size_t)0ULL);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_612_, v___f_618_, v_buckets_613_, v___x_619_, v___x_620_, v___x_614_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList___redArg(lean_object* v_inst_626_, lean_object* v_inst_627_, lean_object* v_l_628_){
_start:
{
lean_object* v___x_629_; uint8_t v___x_630_; 
v___x_629_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_630_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_630_ == 0)
{
lean_dec(v_l_628_);
lean_dec_ref(v_inst_627_);
lean_dec_ref(v_inst_626_);
return v___x_629_;
}
else
{
lean_object* v___f_631_; lean_object* v___x_632_; 
v___f_631_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_631_, v_inst_626_, v_inst_627_, v___x_629_, v_l_628_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList(lean_object* v_00_u03b1_633_, lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_l_636_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__0(lean_object* v_f_641_, lean_object* v_b_642_, lean_object* v_a_643_, lean_object* v_x_644_){
_start:
{
lean_object* v___x_645_; 
v___x_645_ = lean_apply_2(v_f_641_, v_b_642_, v_a_643_);
return v___x_645_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__1(lean_object* v_inst_646_, lean_object* v___f_647_, lean_object* v_acc_648_, lean_object* v_l_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_646_, v___f_647_, v_acc_648_, v_l_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg(lean_object* v_inst_651_, lean_object* v_f_652_, lean_object* v_init_653_, lean_object* v_b_654_){
_start:
{
lean_object* v_buckets_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_buckets_655_ = lean_ctor_get(v_b_654_, 1);
lean_inc_ref(v_buckets_655_);
lean_dec_ref(v_b_654_);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_array_get_size(v_buckets_655_);
v___x_658_ = lean_nat_dec_lt(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v_toApplicative_659_; lean_object* v_toPure_660_; lean_object* v___x_661_; 
lean_dec_ref(v_buckets_655_);
lean_dec(v_f_652_);
v_toApplicative_659_ = lean_ctor_get(v_inst_651_, 0);
lean_inc_ref(v_toApplicative_659_);
lean_dec_ref(v_inst_651_);
v_toPure_660_ = lean_ctor_get(v_toApplicative_659_, 1);
lean_inc(v_toPure_660_);
lean_dec_ref(v_toApplicative_659_);
v___x_661_ = lean_apply_2(v_toPure_660_, lean_box(0), v_init_653_);
return v___x_661_;
}
else
{
lean_object* v___f_662_; lean_object* v___f_663_; uint8_t v___x_664_; 
v___f_662_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_662_, 0, v_f_652_);
lean_inc_ref(v_inst_651_);
v___f_663_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_663_, 0, v_inst_651_);
lean_closure_set(v___f_663_, 1, v___f_662_);
v___x_664_ = lean_nat_dec_le(v___x_657_, v___x_657_);
if (v___x_664_ == 0)
{
if (v___x_658_ == 0)
{
lean_object* v_toApplicative_665_; lean_object* v_toPure_666_; lean_object* v___x_667_; 
lean_dec_ref(v___f_663_);
lean_dec_ref(v_buckets_655_);
v_toApplicative_665_ = lean_ctor_get(v_inst_651_, 0);
lean_inc_ref(v_toApplicative_665_);
lean_dec_ref(v_inst_651_);
v_toPure_666_ = lean_ctor_get(v_toApplicative_665_, 1);
lean_inc(v_toPure_666_);
lean_dec_ref(v_toApplicative_665_);
v___x_667_ = lean_apply_2(v_toPure_666_, lean_box(0), v_init_653_);
return v___x_667_;
}
else
{
size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
v___x_668_ = ((size_t)0ULL);
v___x_669_ = lean_usize_of_nat(v___x_657_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_651_, v___f_663_, v_buckets_655_, v___x_668_, v___x_669_, v_init_653_);
return v___x_670_;
}
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_657_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_651_, v___f_663_, v_buckets_655_, v___x_671_, v___x_672_, v_init_653_);
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM(lean_object* v_00_u03b1_674_, lean_object* v_m_675_, lean_object* v_inst_676_, lean_object* v_00_u03b2_677_, lean_object* v_f_678_, lean_object* v_init_679_, lean_object* v_b_680_){
_start:
{
lean_object* v_buckets_681_; lean_object* v___x_682_; lean_object* v___x_683_; uint8_t v___x_684_; 
v_buckets_681_ = lean_ctor_get(v_b_680_, 1);
lean_inc_ref(v_buckets_681_);
lean_dec_ref(v_b_680_);
v___x_682_ = lean_unsigned_to_nat(0u);
v___x_683_ = lean_array_get_size(v_buckets_681_);
v___x_684_ = lean_nat_dec_lt(v___x_682_, v___x_683_);
if (v___x_684_ == 0)
{
lean_object* v_toApplicative_685_; lean_object* v_toPure_686_; lean_object* v___x_687_; 
lean_dec_ref(v_buckets_681_);
lean_dec(v_f_678_);
v_toApplicative_685_ = lean_ctor_get(v_inst_676_, 0);
lean_inc_ref(v_toApplicative_685_);
lean_dec_ref(v_inst_676_);
v_toPure_686_ = lean_ctor_get(v_toApplicative_685_, 1);
lean_inc(v_toPure_686_);
lean_dec_ref(v_toApplicative_685_);
v___x_687_ = lean_apply_2(v_toPure_686_, lean_box(0), v_init_679_);
return v___x_687_;
}
else
{
lean_object* v___f_688_; lean_object* v___f_689_; uint8_t v___x_690_; 
v___f_688_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_688_, 0, v_f_678_);
lean_inc_ref(v_inst_676_);
v___f_689_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_689_, 0, v_inst_676_);
lean_closure_set(v___f_689_, 1, v___f_688_);
v___x_690_ = lean_nat_dec_le(v___x_683_, v___x_683_);
if (v___x_690_ == 0)
{
if (v___x_684_ == 0)
{
lean_object* v_toApplicative_691_; lean_object* v_toPure_692_; lean_object* v___x_693_; 
lean_dec_ref(v___f_689_);
lean_dec_ref(v_buckets_681_);
v_toApplicative_691_ = lean_ctor_get(v_inst_676_, 0);
lean_inc_ref(v_toApplicative_691_);
lean_dec_ref(v_inst_676_);
v_toPure_692_ = lean_ctor_get(v_toApplicative_691_, 1);
lean_inc(v_toPure_692_);
lean_dec_ref(v_toApplicative_691_);
v___x_693_ = lean_apply_2(v_toPure_692_, lean_box(0), v_init_679_);
return v___x_693_;
}
else
{
size_t v___x_694_; size_t v___x_695_; lean_object* v___x_696_; 
v___x_694_ = ((size_t)0ULL);
v___x_695_ = lean_usize_of_nat(v___x_683_);
v___x_696_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_676_, v___f_689_, v_buckets_681_, v___x_694_, v___x_695_, v_init_679_);
return v___x_696_;
}
}
else
{
size_t v___x_697_; size_t v___x_698_; lean_object* v___x_699_; 
v___x_697_ = ((size_t)0ULL);
v___x_698_ = lean_usize_of_nat(v___x_683_);
v___x_699_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_676_, v___f_689_, v_buckets_681_, v___x_697_, v___x_698_, v_init_679_);
return v___x_699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__0(lean_object* v_f_700_, lean_object* v_x1_701_, lean_object* v_x2_702_, lean_object* v_x3_703_){
_start:
{
lean_object* v___x_704_; 
v___x_704_ = lean_apply_2(v_f_700_, v_x1_701_, v_x2_702_);
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__1(lean_object* v___x_705_, lean_object* v___f_706_, lean_object* v_acc_707_, lean_object* v_l_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_705_, v___f_706_, v_acc_707_, v_l_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg(lean_object* v_f_710_, lean_object* v_init_711_, lean_object* v_m_712_){
_start:
{
lean_object* v___x_713_; lean_object* v_buckets_714_; lean_object* v___x_715_; lean_object* v___x_716_; uint8_t v___x_717_; 
v___x_713_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
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
lean_object* v___f_718_; lean_object* v___f_719_; uint8_t v___x_720_; 
v___f_718_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_718_, 0, v_f_710_);
v___f_719_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_719_, 0, v___x_713_);
lean_closure_set(v___f_719_, 1, v___f_718_);
v___x_720_ = lean_nat_dec_le(v___x_716_, v___x_716_);
if (v___x_720_ == 0)
{
if (v___x_717_ == 0)
{
lean_dec_ref(v___f_719_);
lean_dec_ref(v_buckets_714_);
return v_init_711_;
}
else
{
size_t v___x_721_; size_t v___x_722_; lean_object* v___x_723_; 
v___x_721_ = ((size_t)0ULL);
v___x_722_ = lean_usize_of_nat(v___x_716_);
v___x_723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_713_, v___f_719_, v_buckets_714_, v___x_721_, v___x_722_, v_init_711_);
return v___x_723_;
}
}
else
{
size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; 
v___x_724_ = ((size_t)0ULL);
v___x_725_ = lean_usize_of_nat(v___x_716_);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_713_, v___f_719_, v_buckets_714_, v___x_724_, v___x_725_, v_init_711_);
return v___x_726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold(lean_object* v_00_u03b1_727_, lean_object* v_00_u03b2_728_, lean_object* v_f_729_, lean_object* v_init_730_, lean_object* v_m_731_){
_start:
{
lean_object* v___x_732_; lean_object* v_buckets_733_; lean_object* v___x_734_; lean_object* v___x_735_; uint8_t v___x_736_; 
v___x_732_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_733_ = lean_ctor_get(v_m_731_, 1);
lean_inc_ref(v_buckets_733_);
lean_dec_ref(v_m_731_);
v___x_734_ = lean_unsigned_to_nat(0u);
v___x_735_ = lean_array_get_size(v_buckets_733_);
v___x_736_ = lean_nat_dec_lt(v___x_734_, v___x_735_);
if (v___x_736_ == 0)
{
lean_dec_ref(v_buckets_733_);
lean_dec(v_f_729_);
return v_init_730_;
}
else
{
lean_object* v___f_737_; lean_object* v___f_738_; uint8_t v___x_739_; 
v___f_737_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_737_, 0, v_f_729_);
v___f_738_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_738_, 0, v___x_732_);
lean_closure_set(v___f_738_, 1, v___f_737_);
v___x_739_ = lean_nat_dec_le(v___x_735_, v___x_735_);
if (v___x_739_ == 0)
{
if (v___x_736_ == 0)
{
lean_dec_ref(v___f_738_);
lean_dec_ref(v_buckets_733_);
return v_init_730_;
}
else
{
size_t v___x_740_; size_t v___x_741_; lean_object* v___x_742_; 
v___x_740_ = ((size_t)0ULL);
v___x_741_ = lean_usize_of_nat(v___x_735_);
v___x_742_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_732_, v___f_738_, v_buckets_733_, v___x_740_, v___x_741_, v_init_730_);
return v___x_742_;
}
}
else
{
size_t v___x_743_; size_t v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((size_t)0ULL);
v___x_744_ = lean_usize_of_nat(v___x_735_);
v___x_745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_732_, v___f_738_, v_buckets_733_, v___x_743_, v___x_744_, v_init_730_);
return v___x_745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__0(lean_object* v_f_746_, lean_object* v_x_747_, lean_object* v___y_748_, lean_object* v___y_749_){
_start:
{
lean_object* v___x_750_; 
v___x_750_ = lean_apply_1(v_f_746_, v___y_748_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__1(lean_object* v_inst_751_, lean_object* v___f_752_, lean_object* v_x_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_755_; lean_object* v___x_756_; 
v___x_755_ = lean_box(0);
v___x_756_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_751_, v___f_752_, v___x_755_, v___y_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg(lean_object* v_inst_757_, lean_object* v_f_758_, lean_object* v_b_759_){
_start:
{
lean_object* v_buckets_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_buckets_760_ = lean_ctor_get(v_b_759_, 1);
lean_inc_ref(v_buckets_760_);
lean_dec_ref(v_b_759_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_array_get_size(v_buckets_760_);
v___x_763_ = lean_box(0);
v___x_764_ = lean_nat_dec_lt(v___x_761_, v___x_762_);
if (v___x_764_ == 0)
{
lean_object* v_toApplicative_765_; lean_object* v_toPure_766_; lean_object* v___x_767_; 
lean_dec_ref(v_buckets_760_);
lean_dec(v_f_758_);
v_toApplicative_765_ = lean_ctor_get(v_inst_757_, 0);
lean_inc_ref(v_toApplicative_765_);
lean_dec_ref(v_inst_757_);
v_toPure_766_ = lean_ctor_get(v_toApplicative_765_, 1);
lean_inc(v_toPure_766_);
lean_dec_ref(v_toApplicative_765_);
v___x_767_ = lean_apply_2(v_toPure_766_, lean_box(0), v___x_763_);
return v___x_767_;
}
else
{
lean_object* v___f_768_; lean_object* v___f_769_; uint8_t v___x_770_; 
v___f_768_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_768_, 0, v_f_758_);
lean_inc_ref(v_inst_757_);
v___f_769_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_769_, 0, v_inst_757_);
lean_closure_set(v___f_769_, 1, v___f_768_);
v___x_770_ = lean_nat_dec_le(v___x_762_, v___x_762_);
if (v___x_770_ == 0)
{
if (v___x_764_ == 0)
{
lean_object* v_toApplicative_771_; lean_object* v_toPure_772_; lean_object* v___x_773_; 
lean_dec_ref(v___f_769_);
lean_dec_ref(v_buckets_760_);
v_toApplicative_771_ = lean_ctor_get(v_inst_757_, 0);
lean_inc_ref(v_toApplicative_771_);
lean_dec_ref(v_inst_757_);
v_toPure_772_ = lean_ctor_get(v_toApplicative_771_, 1);
lean_inc(v_toPure_772_);
lean_dec_ref(v_toApplicative_771_);
v___x_773_ = lean_apply_2(v_toPure_772_, lean_box(0), v___x_763_);
return v___x_773_;
}
else
{
size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = ((size_t)0ULL);
v___x_775_ = lean_usize_of_nat(v___x_762_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_757_, v___f_769_, v_buckets_760_, v___x_774_, v___x_775_, v___x_763_);
return v___x_776_;
}
}
else
{
size_t v___x_777_; size_t v___x_778_; lean_object* v___x_779_; 
v___x_777_ = ((size_t)0ULL);
v___x_778_ = lean_usize_of_nat(v___x_762_);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_757_, v___f_769_, v_buckets_760_, v___x_777_, v___x_778_, v___x_763_);
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM(lean_object* v_00_u03b1_780_, lean_object* v_m_781_, lean_object* v_inst_782_, lean_object* v_f_783_, lean_object* v_b_784_){
_start:
{
lean_object* v_buckets_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_buckets_785_ = lean_ctor_get(v_b_784_, 1);
lean_inc_ref(v_buckets_785_);
lean_dec_ref(v_b_784_);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_array_get_size(v_buckets_785_);
v___x_788_ = lean_box(0);
v___x_789_ = lean_nat_dec_lt(v___x_786_, v___x_787_);
if (v___x_789_ == 0)
{
lean_object* v_toApplicative_790_; lean_object* v_toPure_791_; lean_object* v___x_792_; 
lean_dec_ref(v_buckets_785_);
lean_dec(v_f_783_);
v_toApplicative_790_ = lean_ctor_get(v_inst_782_, 0);
lean_inc_ref(v_toApplicative_790_);
lean_dec_ref(v_inst_782_);
v_toPure_791_ = lean_ctor_get(v_toApplicative_790_, 1);
lean_inc(v_toPure_791_);
lean_dec_ref(v_toApplicative_790_);
v___x_792_ = lean_apply_2(v_toPure_791_, lean_box(0), v___x_788_);
return v___x_792_;
}
else
{
lean_object* v___f_793_; lean_object* v___f_794_; uint8_t v___x_795_; 
v___f_793_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_793_, 0, v_f_783_);
lean_inc_ref(v_inst_782_);
v___f_794_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_794_, 0, v_inst_782_);
lean_closure_set(v___f_794_, 1, v___f_793_);
v___x_795_ = lean_nat_dec_le(v___x_787_, v___x_787_);
if (v___x_795_ == 0)
{
if (v___x_789_ == 0)
{
lean_object* v_toApplicative_796_; lean_object* v_toPure_797_; lean_object* v___x_798_; 
lean_dec_ref(v___f_794_);
lean_dec_ref(v_buckets_785_);
v_toApplicative_796_ = lean_ctor_get(v_inst_782_, 0);
lean_inc_ref(v_toApplicative_796_);
lean_dec_ref(v_inst_782_);
v_toPure_797_ = lean_ctor_get(v_toApplicative_796_, 1);
lean_inc(v_toPure_797_);
lean_dec_ref(v_toApplicative_796_);
v___x_798_ = lean_apply_2(v_toPure_797_, lean_box(0), v___x_788_);
return v___x_798_;
}
else
{
size_t v___x_799_; size_t v___x_800_; lean_object* v___x_801_; 
v___x_799_ = ((size_t)0ULL);
v___x_800_ = lean_usize_of_nat(v___x_787_);
v___x_801_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_782_, v___f_794_, v_buckets_785_, v___x_799_, v___x_800_, v___x_788_);
return v___x_801_;
}
}
else
{
size_t v___x_802_; size_t v___x_803_; lean_object* v___x_804_; 
v___x_802_ = ((size_t)0ULL);
v___x_803_ = lean_usize_of_nat(v___x_787_);
v___x_804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_782_, v___f_794_, v_buckets_785_, v___x_802_, v___x_803_, v___x_788_);
return v___x_804_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__0(lean_object* v_f_805_, lean_object* v_a_806_, lean_object* v_x_807_, lean_object* v_acc_808_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = lean_apply_2(v_f_805_, v_a_806_, v_acc_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__1(lean_object* v_inst_810_, lean_object* v___f_811_, lean_object* v_a_812_, lean_object* v_x_813_, lean_object* v___y_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_810_, v___f_811_, v_a_812_, v___y_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg(lean_object* v_inst_816_, lean_object* v_f_817_, lean_object* v_init_818_, lean_object* v_b_819_){
_start:
{
lean_object* v_buckets_820_; lean_object* v___f_821_; lean_object* v___f_822_; size_t v_sz_823_; size_t v___x_824_; lean_object* v___x_825_; 
v_buckets_820_ = lean_ctor_get(v_b_819_, 1);
lean_inc_ref(v_buckets_820_);
lean_dec_ref(v_b_819_);
v___f_821_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_821_, 0, v_f_817_);
lean_inc_ref(v_inst_816_);
v___f_822_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_822_, 0, v_inst_816_);
lean_closure_set(v___f_822_, 1, v___f_821_);
v_sz_823_ = lean_array_size(v_buckets_820_);
v___x_824_ = ((size_t)0ULL);
v___x_825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_816_, v_buckets_820_, v___f_822_, v_sz_823_, v___x_824_, v_init_818_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn(lean_object* v_00_u03b1_826_, lean_object* v_m_827_, lean_object* v_inst_828_, lean_object* v_00_u03b2_829_, lean_object* v_f_830_, lean_object* v_init_831_, lean_object* v_b_832_){
_start:
{
lean_object* v_buckets_833_; lean_object* v___f_834_; lean_object* v___f_835_; size_t v_sz_836_; size_t v___x_837_; lean_object* v___x_838_; 
v_buckets_833_ = lean_ctor_get(v_b_832_, 1);
lean_inc_ref(v_buckets_833_);
lean_dec_ref(v_b_832_);
v___f_834_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_834_, 0, v_f_830_);
lean_inc_ref(v_inst_828_);
v___f_835_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_835_, 0, v_inst_828_);
lean_closure_set(v___f_835_, 1, v___f_834_);
v_sz_836_ = lean_array_size(v_buckets_833_);
v___x_837_ = ((size_t)0ULL);
v___x_838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_828_, v_buckets_833_, v___f_835_, v_sz_836_, v___x_837_, v_init_831_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2(lean_object* v_inst_839_, lean_object* v_m_840_, lean_object* v_f_841_){
_start:
{
lean_object* v_buckets_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v_buckets_842_ = lean_ctor_get(v_m_840_, 1);
lean_inc_ref(v_buckets_842_);
lean_dec_ref(v_m_840_);
v___x_843_ = lean_unsigned_to_nat(0u);
v___x_844_ = lean_array_get_size(v_buckets_842_);
v___x_845_ = lean_box(0);
v___x_846_ = lean_nat_dec_lt(v___x_843_, v___x_844_);
if (v___x_846_ == 0)
{
lean_object* v_toApplicative_847_; lean_object* v_toPure_848_; lean_object* v___x_849_; 
lean_dec_ref(v_buckets_842_);
lean_dec(v_f_841_);
v_toApplicative_847_ = lean_ctor_get(v_inst_839_, 0);
lean_inc_ref(v_toApplicative_847_);
lean_dec_ref(v_inst_839_);
v_toPure_848_ = lean_ctor_get(v_toApplicative_847_, 1);
lean_inc(v_toPure_848_);
lean_dec_ref(v_toApplicative_847_);
v___x_849_ = lean_apply_2(v_toPure_848_, lean_box(0), v___x_845_);
return v___x_849_;
}
else
{
lean_object* v___f_850_; lean_object* v___f_851_; uint8_t v___x_852_; 
v___f_850_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_850_, 0, v_f_841_);
lean_inc_ref(v_inst_839_);
v___f_851_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_851_, 0, v_inst_839_);
lean_closure_set(v___f_851_, 1, v___f_850_);
v___x_852_ = lean_nat_dec_le(v___x_844_, v___x_844_);
if (v___x_852_ == 0)
{
if (v___x_846_ == 0)
{
lean_object* v_toApplicative_853_; lean_object* v_toPure_854_; lean_object* v___x_855_; 
lean_dec_ref(v___f_851_);
lean_dec_ref(v_buckets_842_);
v_toApplicative_853_ = lean_ctor_get(v_inst_839_, 0);
lean_inc_ref(v_toApplicative_853_);
lean_dec_ref(v_inst_839_);
v_toPure_854_ = lean_ctor_get(v_toApplicative_853_, 1);
lean_inc(v_toPure_854_);
lean_dec_ref(v_toApplicative_853_);
v___x_855_ = lean_apply_2(v_toPure_854_, lean_box(0), v___x_845_);
return v___x_855_;
}
else
{
size_t v___x_856_; size_t v___x_857_; lean_object* v___x_858_; 
v___x_856_ = ((size_t)0ULL);
v___x_857_ = lean_usize_of_nat(v___x_844_);
v___x_858_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_839_, v___f_851_, v_buckets_842_, v___x_856_, v___x_857_, v___x_845_);
return v___x_858_;
}
}
else
{
size_t v___x_859_; size_t v___x_860_; lean_object* v___x_861_; 
v___x_859_ = ((size_t)0ULL);
v___x_860_ = lean_usize_of_nat(v___x_844_);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_839_, v___f_851_, v_buckets_842_, v___x_859_, v___x_860_, v___x_845_);
return v___x_861_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_862_){
_start:
{
lean_object* v___f_863_; 
v___f_863_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_863_, 0, v_inst_862_);
return v___f_863_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_864_, lean_object* v_m_865_, lean_object* v_inst_866_){
_start:
{
lean_object* v___f_867_; 
v___f_867_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_867_, 0, v_inst_866_);
return v___f_867_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_868_, lean_object* v_00_u03b2_869_, lean_object* v_m_870_, lean_object* v_init_871_, lean_object* v_f_872_){
_start:
{
lean_object* v_buckets_873_; lean_object* v___f_874_; lean_object* v___f_875_; size_t v_sz_876_; size_t v___x_877_; lean_object* v___x_878_; 
v_buckets_873_ = lean_ctor_get(v_m_870_, 1);
lean_inc_ref(v_buckets_873_);
lean_dec_ref(v_m_870_);
v___f_874_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_874_, 0, v_f_872_);
lean_inc_ref(v_inst_868_);
v___f_875_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_875_, 0, v_inst_868_);
lean_closure_set(v___f_875_, 1, v___f_874_);
v_sz_876_ = lean_array_size(v_buckets_873_);
v___x_877_ = ((size_t)0ULL);
v___x_878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_868_, v_buckets_873_, v___f_875_, v_sz_876_, v___x_877_, v_init_871_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_879_){
_start:
{
lean_object* v___f_880_; 
v___f_880_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_880_, 0, v_inst_879_);
return v___f_880_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_881_, lean_object* v_m_882_, lean_object* v_inst_883_){
_start:
{
lean_object* v___f_884_; 
v___f_884_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_884_, 0, v_inst_883_);
return v___f_884_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_filter___redArg___lam__0(lean_object* v_f_885_, lean_object* v_a_886_, lean_object* v_x_887_){
_start:
{
lean_object* v___x_888_; uint8_t v___x_889_; 
v___x_888_ = lean_apply_1(v_f_885_, v_a_886_);
v___x_889_ = lean_unbox(v___x_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_890_, lean_object* v_a_891_, lean_object* v_x_892_){
_start:
{
uint8_t v_res_893_; lean_object* v_r_894_; 
v_res_893_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_890_, v_a_891_, v_x_892_);
v_r_894_ = lean_box(v_res_893_);
return v_r_894_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg(lean_object* v_f_895_, lean_object* v_m_896_){
_start:
{
lean_object* v_buckets_897_; lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v_buckets_897_ = lean_ctor_get(v_m_896_, 1);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_array_get_size(v_buckets_897_);
v___x_900_ = lean_nat_dec_lt(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
lean_dec_ref(v_m_896_);
lean_dec_ref(v_f_895_);
v___x_901_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
return v___x_901_;
}
else
{
lean_object* v___f_902_; lean_object* v___x_903_; 
v___f_902_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_902_, 0, v_f_895_);
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_902_, v_m_896_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter(lean_object* v_00_u03b1_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_f_907_, lean_object* v_m_908_){
_start:
{
lean_object* v_buckets_909_; lean_object* v___x_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_buckets_909_ = lean_ctor_get(v_m_908_, 1);
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = lean_array_get_size(v_buckets_909_);
v___x_912_ = lean_nat_dec_lt(v___x_910_, v___x_911_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; 
lean_dec_ref(v_m_908_);
lean_dec_ref(v_f_907_);
v___x_913_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
return v___x_913_;
}
else
{
lean_object* v___f_914_; lean_object* v___x_915_; 
v___f_914_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_914_, 0, v_f_907_);
v___x_915_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_914_, v_m_908_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___boxed(lean_object* v_00_u03b1_916_, lean_object* v_inst_917_, lean_object* v_inst_918_, lean_object* v_f_919_, lean_object* v_m_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_HashSet_Raw_filter(v_00_u03b1_916_, v_inst_917_, v_inst_918_, v_f_919_, v_m_920_);
lean_dec_ref(v_inst_918_);
lean_dec_ref(v_inst_917_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__0(lean_object* v_x1_922_, lean_object* v_x2_923_, lean_object* v_x3_924_){
_start:
{
lean_object* v___x_925_; 
v___x_925_ = lean_array_push(v_x1_922_, v_x2_923_);
return v___x_925_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__1(lean_object* v___x_926_, lean_object* v___f_927_, lean_object* v_acc_928_, lean_object* v_l_929_){
_start:
{
lean_object* v___x_930_; 
v___x_930_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_926_, v___f_927_, v_acc_928_, v_l_929_);
return v___x_930_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg(lean_object* v_m_935_){
_start:
{
lean_object* v_size_936_; lean_object* v_buckets_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; uint8_t v___x_942_; 
v_size_936_ = lean_ctor_get(v_m_935_, 0);
lean_inc(v_size_936_);
v_buckets_937_ = lean_ctor_get(v_m_935_, 1);
lean_inc_ref(v_buckets_937_);
lean_dec_ref(v_m_935_);
v___x_938_ = lean_mk_empty_array_with_capacity(v_size_936_);
lean_dec(v_size_936_);
v___x_939_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_940_ = lean_unsigned_to_nat(0u);
v___x_941_ = lean_array_get_size(v_buckets_937_);
v___x_942_ = lean_nat_dec_lt(v___x_940_, v___x_941_);
if (v___x_942_ == 0)
{
lean_dec_ref(v_buckets_937_);
return v___x_938_;
}
else
{
lean_object* v___f_943_; uint8_t v___x_944_; 
v___f_943_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_944_ = lean_nat_dec_le(v___x_941_, v___x_941_);
if (v___x_944_ == 0)
{
if (v___x_942_ == 0)
{
lean_dec_ref(v_buckets_937_);
return v___x_938_;
}
else
{
size_t v___x_945_; size_t v___x_946_; lean_object* v___x_947_; 
v___x_945_ = ((size_t)0ULL);
v___x_946_ = lean_usize_of_nat(v___x_941_);
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_939_, v___f_943_, v_buckets_937_, v___x_945_, v___x_946_, v___x_938_);
return v___x_947_;
}
}
else
{
size_t v___x_948_; size_t v___x_949_; lean_object* v___x_950_; 
v___x_948_ = ((size_t)0ULL);
v___x_949_ = lean_usize_of_nat(v___x_941_);
v___x_950_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_939_, v___f_943_, v_buckets_937_, v___x_948_, v___x_949_, v___x_938_);
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray(lean_object* v_00_u03b1_951_, lean_object* v_m_952_){
_start:
{
lean_object* v_size_953_; lean_object* v_buckets_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; uint8_t v___x_959_; 
v_size_953_ = lean_ctor_get(v_m_952_, 0);
lean_inc(v_size_953_);
v_buckets_954_ = lean_ctor_get(v_m_952_, 1);
lean_inc_ref(v_buckets_954_);
lean_dec_ref(v_m_952_);
v___x_955_ = lean_mk_empty_array_with_capacity(v_size_953_);
lean_dec(v_size_953_);
v___x_956_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_957_ = lean_unsigned_to_nat(0u);
v___x_958_ = lean_array_get_size(v_buckets_954_);
v___x_959_ = lean_nat_dec_lt(v___x_957_, v___x_958_);
if (v___x_959_ == 0)
{
lean_dec_ref(v_buckets_954_);
return v___x_955_;
}
else
{
lean_object* v___f_960_; uint8_t v___x_961_; 
v___f_960_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_961_ = lean_nat_dec_le(v___x_958_, v___x_958_);
if (v___x_961_ == 0)
{
if (v___x_959_ == 0)
{
lean_dec_ref(v_buckets_954_);
return v___x_955_;
}
else
{
size_t v___x_962_; size_t v___x_963_; lean_object* v___x_964_; 
v___x_962_ = ((size_t)0ULL);
v___x_963_ = lean_usize_of_nat(v___x_958_);
v___x_964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_956_, v___f_960_, v_buckets_954_, v___x_962_, v___x_963_, v___x_955_);
return v___x_964_;
}
}
else
{
size_t v___x_965_; size_t v___x_966_; lean_object* v___x_967_; 
v___x_965_ = ((size_t)0ULL);
v___x_966_ = lean_usize_of_nat(v___x_958_);
v___x_967_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_956_, v___f_960_, v_buckets_954_, v___x_965_, v___x_966_, v___x_955_);
return v___x_967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__0(lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_a_970_, lean_object* v_b_971_, lean_object* v_acc_972_){
_start:
{
lean_object* v_r_973_; lean_object* v___x_974_; 
v_r_973_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_968_, v_inst_969_, v_acc_972_, v_a_970_, v_b_971_);
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v_r_973_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__1(lean_object* v___x_975_, lean_object* v___f_976_, lean_object* v_a_977_, lean_object* v_x_978_, lean_object* v___y_979_){
_start:
{
lean_object* v___x_980_; 
v___x_980_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_975_, v___f_976_, v_a_977_, v___y_979_);
return v___x_980_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg(lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_m_u2081_985_, lean_object* v_m_u2082_986_){
_start:
{
lean_object* v_size_987_; lean_object* v_buckets_988_; lean_object* v___x_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_size_987_ = lean_ctor_get(v_m_u2081_985_, 0);
v_buckets_988_ = lean_ctor_get(v_m_u2081_985_, 1);
v___x_989_ = lean_unsigned_to_nat(0u);
v___x_990_ = lean_array_get_size(v_buckets_988_);
v___x_991_ = lean_nat_dec_lt(v___x_989_, v___x_990_);
if (v___x_991_ == 0)
{
lean_dec_ref(v_m_u2081_985_);
lean_dec_ref(v_inst_984_);
lean_dec_ref(v_inst_983_);
return v_m_u2082_986_;
}
else
{
lean_object* v_size_992_; lean_object* v_buckets_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_size_992_ = lean_ctor_get(v_m_u2082_986_, 0);
v_buckets_993_ = lean_ctor_get(v_m_u2082_986_, 1);
v___x_994_ = lean_array_get_size(v_buckets_993_);
v___x_995_ = lean_nat_dec_lt(v___x_989_, v___x_994_);
if (v___x_995_ == 0)
{
lean_dec_ref(v_m_u2082_986_);
lean_dec_ref(v_inst_984_);
lean_dec_ref(v_inst_983_);
return v_m_u2081_985_;
}
else
{
uint8_t v___x_996_; 
v___x_996_ = lean_nat_dec_le(v_size_987_, v_size_992_);
if (v___x_996_ == 0)
{
lean_object* v___f_997_; lean_object* v___x_998_; 
v___f_997_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_998_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_997_, v_inst_983_, v_inst_984_, v_m_u2081_985_, v_m_u2082_986_);
return v___x_998_;
}
else
{
lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v___f_1001_; size_t v_sz_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
lean_inc_ref(v_buckets_988_);
lean_dec_ref(v_m_u2081_985_);
v___f_999_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_999_, 0, v_inst_983_);
lean_closure_set(v___f_999_, 1, v_inst_984_);
v___x_1000_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___f_1001_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1001_, 0, v___x_1000_);
lean_closure_set(v___f_1001_, 1, v___f_999_);
v_sz_1002_ = lean_array_size(v_buckets_988_);
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1000_, v_buckets_988_, v___f_1001_, v_sz_1002_, v___x_1003_, v_m_u2082_986_);
return v___x_1004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union(lean_object* v_00_u03b1_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_m_u2081_1008_, lean_object* v_m_u2082_1009_){
_start:
{
lean_object* v_size_1010_; lean_object* v_buckets_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v_size_1010_ = lean_ctor_get(v_m_u2081_1008_, 0);
v_buckets_1011_ = lean_ctor_get(v_m_u2081_1008_, 1);
v___x_1012_ = lean_unsigned_to_nat(0u);
v___x_1013_ = lean_array_get_size(v_buckets_1011_);
v___x_1014_ = lean_nat_dec_lt(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_dec_ref(v_m_u2081_1008_);
lean_dec_ref(v_inst_1007_);
lean_dec_ref(v_inst_1006_);
return v_m_u2082_1009_;
}
else
{
lean_object* v_size_1015_; lean_object* v_buckets_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_size_1015_ = lean_ctor_get(v_m_u2082_1009_, 0);
v_buckets_1016_ = lean_ctor_get(v_m_u2082_1009_, 1);
v___x_1017_ = lean_array_get_size(v_buckets_1016_);
v___x_1018_ = lean_nat_dec_lt(v___x_1012_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_dec_ref(v_m_u2082_1009_);
lean_dec_ref(v_inst_1007_);
lean_dec_ref(v_inst_1006_);
return v_m_u2081_1008_;
}
else
{
uint8_t v___x_1019_; 
v___x_1019_ = lean_nat_dec_le(v_size_1010_, v_size_1015_);
if (v___x_1019_ == 0)
{
lean_object* v___f_1020_; lean_object* v___x_1021_; 
v___f_1020_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1021_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1020_, v_inst_1006_, v_inst_1007_, v_m_u2081_1008_, v_m_u2082_1009_);
return v___x_1021_;
}
else
{
lean_object* v___f_1022_; lean_object* v___x_1023_; lean_object* v___f_1024_; size_t v_sz_1025_; size_t v___x_1026_; lean_object* v___x_1027_; 
lean_inc_ref(v_buckets_1011_);
lean_dec_ref(v_m_u2081_1008_);
v___f_1022_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1022_, 0, v_inst_1006_);
lean_closure_set(v___f_1022_, 1, v_inst_1007_);
v___x_1023_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___f_1024_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1024_, 0, v___x_1023_);
lean_closure_set(v___f_1024_, 1, v___f_1022_);
v_sz_1025_ = lean_array_size(v_buckets_1011_);
v___x_1026_ = ((size_t)0ULL);
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1023_, v_buckets_1011_, v___f_1024_, v_sz_1025_, v___x_1026_, v_m_u2082_1009_);
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1028_, lean_object* v_inst_1029_){
_start:
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_1030_, 0, lean_box(0));
lean_closure_set(v___x_1030_, 1, v_inst_1028_);
lean_closure_set(v___x_1030_, 2, v_inst_1029_);
return v___x_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1031_, lean_object* v_inst_1032_, lean_object* v_inst_1033_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter___redArg(lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_m_u2081_1037_, lean_object* v_m_u2082_1038_){
_start:
{
lean_object* v_buckets_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_buckets_1039_ = lean_ctor_get(v_m_u2081_1037_, 1);
v___x_1040_ = lean_unsigned_to_nat(0u);
v___x_1041_ = lean_array_get_size(v_buckets_1039_);
v___x_1042_ = lean_nat_dec_lt(v___x_1040_, v___x_1041_);
if (v___x_1042_ == 0)
{
lean_dec_ref(v_m_u2081_1037_);
lean_dec_ref(v_inst_1036_);
lean_dec_ref(v_inst_1035_);
return v_m_u2082_1038_;
}
else
{
lean_object* v_buckets_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_buckets_1043_ = lean_ctor_get(v_m_u2082_1038_, 1);
v___x_1044_ = lean_array_get_size(v_buckets_1043_);
v___x_1045_ = lean_nat_dec_lt(v___x_1040_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_dec_ref(v_m_u2082_1038_);
lean_dec_ref(v_inst_1036_);
lean_dec_ref(v_inst_1035_);
return v_m_u2081_1037_;
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1035_, v_inst_1036_, v_m_u2081_1037_, v_m_u2082_1038_);
return v___x_1046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter(lean_object* v_00_u03b1_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_m_u2081_1050_, lean_object* v_m_u2082_1051_){
_start:
{
lean_object* v_buckets_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; 
v_buckets_1052_ = lean_ctor_get(v_m_u2081_1050_, 1);
v___x_1053_ = lean_unsigned_to_nat(0u);
v___x_1054_ = lean_array_get_size(v_buckets_1052_);
v___x_1055_ = lean_nat_dec_lt(v___x_1053_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_dec_ref(v_m_u2081_1050_);
lean_dec_ref(v_inst_1049_);
lean_dec_ref(v_inst_1048_);
return v_m_u2082_1051_;
}
else
{
lean_object* v_buckets_1056_; lean_object* v___x_1057_; uint8_t v___x_1058_; 
v_buckets_1056_ = lean_ctor_get(v_m_u2082_1051_, 1);
v___x_1057_ = lean_array_get_size(v_buckets_1056_);
v___x_1058_ = lean_nat_dec_lt(v___x_1053_, v___x_1057_);
if (v___x_1058_ == 0)
{
lean_dec_ref(v_m_u2082_1051_);
lean_dec_ref(v_inst_1049_);
lean_dec_ref(v_inst_1048_);
return v_m_u2081_1050_;
}
else
{
lean_object* v___x_1059_; 
v___x_1059_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1048_, v_inst_1049_, v_m_u2081_1050_, v_m_u2082_1051_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1060_, lean_object* v_inst_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1062_, 0, lean_box(0));
lean_closure_set(v___x_1062_, 1, v_inst_1060_);
lean_closure_set(v___x_1062_, 2, v_inst_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_){
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
static lean_object* _init_l_Std_HashSet_Raw_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1067_; lean_object* v___f_1068_; 
v___x_1067_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1068_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1068_, 0, v___x_1067_);
return v___f_1068_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq___redArg(lean_object* v_inst_1069_, lean_object* v_inst_1070_, lean_object* v_m_u2081_1071_, lean_object* v_m_u2082_1072_){
_start:
{
lean_object* v___f_1073_; uint8_t v___x_1074_; 
v___f_1073_ = lean_obj_once(&l_Std_HashSet_Raw_beq___redArg___closed__0, &l_Std_HashSet_Raw_beq___redArg___closed__0_once, _init_l_Std_HashSet_Raw_beq___redArg___closed__0);
v___x_1074_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1069_, v_inst_1070_, v___f_1073_, v_m_u2081_1071_, v_m_u2082_1072_);
return v___x_1074_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___redArg___boxed(lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_m_u2081_1077_, lean_object* v_m_u2082_1078_){
_start:
{
uint8_t v_res_1079_; lean_object* v_r_1080_; 
v_res_1079_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1075_, v_inst_1076_, v_m_u2081_1077_, v_m_u2082_1078_);
v_r_1080_ = lean_box(v_res_1079_);
return v_r_1080_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq(lean_object* v_00_u03b1_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_, lean_object* v_m_u2081_1084_, lean_object* v_m_u2082_1085_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1082_, v_inst_1083_, v_m_u2081_1084_, v_m_u2082_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___boxed(lean_object* v_00_u03b1_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_m_u2081_1090_, lean_object* v_m_u2082_1091_){
_start:
{
uint8_t v_res_1092_; lean_object* v_r_1093_; 
v_res_1092_ = l_Std_HashSet_Raw_beq(v_00_u03b1_1087_, v_inst_1088_, v_inst_1089_, v_m_u2081_1090_, v_m_u2082_1091_);
v_r_1093_ = lean_box(v_res_1092_);
return v_r_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1094_, lean_object* v_inst_1095_){
_start:
{
lean_object* v___x_1096_; 
v___x_1096_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1096_, 0, lean_box(0));
lean_closure_set(v___x_1096_, 1, v_inst_1094_);
lean_closure_set(v___x_1096_, 2, v_inst_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_){
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
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_diff___redArg___lam__0(lean_object* v_inst_1101_, lean_object* v_inst_1102_, lean_object* v_m_u2082_1103_, uint8_t v___x_1104_, lean_object* v_k_1105_, lean_object* v_x_1106_){
_start:
{
uint8_t v___x_1107_; 
v___x_1107_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1101_, v_inst_1102_, v_m_u2082_1103_, v_k_1105_);
if (v___x_1107_ == 0)
{
return v___x_1104_;
}
else
{
uint8_t v___x_1108_; 
v___x_1108_ = 0;
return v___x_1108_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1109_, lean_object* v_inst_1110_, lean_object* v_m_u2082_1111_, lean_object* v___x_1112_, lean_object* v_k_1113_, lean_object* v_x_1114_){
_start:
{
uint8_t v___x_97__boxed_1115_; uint8_t v_res_1116_; lean_object* v_r_1117_; 
v___x_97__boxed_1115_ = lean_unbox(v___x_1112_);
v_res_1116_ = l_Std_HashSet_Raw_diff___redArg___lam__0(v_inst_1109_, v_inst_1110_, v_m_u2082_1111_, v___x_97__boxed_1115_, v_k_1113_, v_x_1114_);
lean_dec_ref(v_m_u2082_1111_);
v_r_1117_ = lean_box(v_res_1116_);
return v_r_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg(lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_m_u2081_1120_, lean_object* v_m_u2082_1121_){
_start:
{
lean_object* v_size_1122_; lean_object* v_buckets_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_size_1122_ = lean_ctor_get(v_m_u2081_1120_, 0);
v_buckets_1123_ = lean_ctor_get(v_m_u2081_1120_, 1);
v___x_1124_ = lean_unsigned_to_nat(0u);
v___x_1125_ = lean_array_get_size(v_buckets_1123_);
v___x_1126_ = lean_nat_dec_lt(v___x_1124_, v___x_1125_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v_m_u2081_1120_);
lean_dec_ref(v_inst_1119_);
lean_dec_ref(v_inst_1118_);
return v_m_u2082_1121_;
}
else
{
lean_object* v_size_1127_; lean_object* v_buckets_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_size_1127_ = lean_ctor_get(v_m_u2082_1121_, 0);
v_buckets_1128_ = lean_ctor_get(v_m_u2082_1121_, 1);
v___x_1129_ = lean_array_get_size(v_buckets_1128_);
v___x_1130_ = lean_nat_dec_lt(v___x_1124_, v___x_1129_);
if (v___x_1130_ == 0)
{
lean_dec_ref(v_m_u2082_1121_);
lean_dec_ref(v_inst_1119_);
lean_dec_ref(v_inst_1118_);
return v_m_u2081_1120_;
}
else
{
uint8_t v___x_1131_; 
v___x_1131_ = lean_nat_dec_le(v_size_1122_, v_size_1127_);
if (v___x_1131_ == 0)
{
lean_object* v___f_1132_; lean_object* v___x_1133_; 
v___f_1132_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1133_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1132_, v_inst_1118_, v_inst_1119_, v_m_u2081_1120_, v_m_u2082_1121_);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; lean_object* v___f_1135_; lean_object* v___x_1136_; 
v___x_1134_ = lean_box(v___x_1131_);
v___f_1135_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1135_, 0, v_inst_1118_);
lean_closure_set(v___f_1135_, 1, v_inst_1119_);
lean_closure_set(v___f_1135_, 2, v_m_u2082_1121_);
lean_closure_set(v___f_1135_, 3, v___x_1134_);
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1135_, v_m_u2081_1120_);
return v___x_1136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff(lean_object* v_00_u03b1_1137_, lean_object* v_inst_1138_, lean_object* v_inst_1139_, lean_object* v_m_u2081_1140_, lean_object* v_m_u2082_1141_){
_start:
{
lean_object* v_size_1142_; lean_object* v_buckets_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; uint8_t v___x_1146_; 
v_size_1142_ = lean_ctor_get(v_m_u2081_1140_, 0);
v_buckets_1143_ = lean_ctor_get(v_m_u2081_1140_, 1);
v___x_1144_ = lean_unsigned_to_nat(0u);
v___x_1145_ = lean_array_get_size(v_buckets_1143_);
v___x_1146_ = lean_nat_dec_lt(v___x_1144_, v___x_1145_);
if (v___x_1146_ == 0)
{
lean_dec_ref(v_m_u2081_1140_);
lean_dec_ref(v_inst_1139_);
lean_dec_ref(v_inst_1138_);
return v_m_u2082_1141_;
}
else
{
lean_object* v_size_1147_; lean_object* v_buckets_1148_; lean_object* v___x_1149_; uint8_t v___x_1150_; 
v_size_1147_ = lean_ctor_get(v_m_u2082_1141_, 0);
v_buckets_1148_ = lean_ctor_get(v_m_u2082_1141_, 1);
v___x_1149_ = lean_array_get_size(v_buckets_1148_);
v___x_1150_ = lean_nat_dec_lt(v___x_1144_, v___x_1149_);
if (v___x_1150_ == 0)
{
lean_dec_ref(v_m_u2082_1141_);
lean_dec_ref(v_inst_1139_);
lean_dec_ref(v_inst_1138_);
return v_m_u2081_1140_;
}
else
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_nat_dec_le(v_size_1142_, v_size_1147_);
if (v___x_1151_ == 0)
{
lean_object* v___f_1152_; lean_object* v___x_1153_; 
v___f_1152_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1153_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1152_, v_inst_1138_, v_inst_1139_, v_m_u2081_1140_, v_m_u2082_1141_);
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; lean_object* v___f_1155_; lean_object* v___x_1156_; 
v___x_1154_ = lean_box(v___x_1151_);
v___f_1155_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1155_, 0, v_inst_1138_);
lean_closure_set(v___f_1155_, 1, v_inst_1139_);
lean_closure_set(v___f_1155_, 2, v_m_u2082_1141_);
lean_closure_set(v___f_1155_, 3, v___x_1154_);
v___x_1156_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1155_, v_m_u2081_1140_);
return v___x_1156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1157_, lean_object* v_inst_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1159_, 0, lean_box(0));
lean_closure_set(v___x_1159_, 1, v_inst_1157_);
lean_closure_set(v___x_1159_, 2, v_inst_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0(lean_object* v_p_1164_, lean_object* v___x_1165_, lean_object* v___x_1166_, lean_object* v_a_1167_, lean_object* v_b_1168_, lean_object* v_acc_1169_){
_start:
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = lean_apply_1(v_p_1164_, v_a_1167_);
v___x_1171_ = lean_unbox(v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_dec_ref(v___x_1166_);
v___x_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1170_);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v___x_1165_);
v___x_1174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1175_, 0, v___x_1166_);
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1176_, lean_object* v___x_1177_, lean_object* v___x_1178_, lean_object* v_a_1179_, lean_object* v_b_1180_, lean_object* v_acc_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Std_HashSet_Raw_all___redArg___lam__0(v_p_1176_, v___x_1177_, v___x_1178_, v_a_1179_, v_b_1180_, v_acc_1181_);
lean_dec_ref(v_acc_1181_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__1(lean_object* v___x_1183_, lean_object* v___f_1184_, lean_object* v_a_1185_, lean_object* v_x_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v___x_1188_; 
v___x_1188_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1183_, v___f_1184_, v_a_1185_, v___y_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all___redArg(lean_object* v_m_1192_, lean_object* v_p_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v_buckets_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; size_t v_sz_1200_; size_t v___x_1201_; lean_object* v___x_1202_; lean_object* v_fst_1203_; 
v___x_1194_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1195_ = lean_ctor_get(v_m_1192_, 1);
lean_inc_ref(v_buckets_1195_);
lean_dec_ref(v_m_1192_);
v___x_1196_ = lean_box(0);
v___x_1197_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1198_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1198_, 0, v_p_1193_);
lean_closure_set(v___f_1198_, 1, v___x_1196_);
lean_closure_set(v___f_1198_, 2, v___x_1197_);
v___f_1199_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1199_, 0, v___x_1194_);
lean_closure_set(v___f_1199_, 1, v___f_1198_);
v_sz_1200_ = lean_array_size(v_buckets_1195_);
v___x_1201_ = ((size_t)0ULL);
v___x_1202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1194_, v_buckets_1195_, v___f_1199_, v_sz_1200_, v___x_1201_, v___x_1197_);
v_fst_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_fst_1203_);
lean_dec(v___x_1202_);
if (lean_obj_tag(v_fst_1203_) == 0)
{
uint8_t v___x_1204_; 
v___x_1204_ = 1;
return v___x_1204_;
}
else
{
lean_object* v_val_1205_; uint8_t v___x_1206_; 
v_val_1205_ = lean_ctor_get(v_fst_1203_, 0);
lean_inc(v_val_1205_);
lean_dec_ref(v_fst_1203_);
v___x_1206_ = lean_unbox(v_val_1205_);
lean_dec(v_val_1205_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___boxed(lean_object* v_m_1207_, lean_object* v_p_1208_){
_start:
{
uint8_t v_res_1209_; lean_object* v_r_1210_; 
v_res_1209_ = l_Std_HashSet_Raw_all___redArg(v_m_1207_, v_p_1208_);
v_r_1210_ = lean_box(v_res_1209_);
return v_r_1210_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all(lean_object* v_00_u03b1_1211_, lean_object* v_m_1212_, lean_object* v_p_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v_buckets_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___f_1218_; lean_object* v___f_1219_; size_t v_sz_1220_; size_t v___x_1221_; lean_object* v___x_1222_; lean_object* v_fst_1223_; 
v___x_1214_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1215_ = lean_ctor_get(v_m_1212_, 1);
lean_inc_ref(v_buckets_1215_);
lean_dec_ref(v_m_1212_);
v___x_1216_ = lean_box(0);
v___x_1217_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1218_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1218_, 0, v_p_1213_);
lean_closure_set(v___f_1218_, 1, v___x_1216_);
lean_closure_set(v___f_1218_, 2, v___x_1217_);
v___f_1219_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1219_, 0, v___x_1214_);
lean_closure_set(v___f_1219_, 1, v___f_1218_);
v_sz_1220_ = lean_array_size(v_buckets_1215_);
v___x_1221_ = ((size_t)0ULL);
v___x_1222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1214_, v_buckets_1215_, v___f_1219_, v_sz_1220_, v___x_1221_, v___x_1217_);
v_fst_1223_ = lean_ctor_get(v___x_1222_, 0);
lean_inc(v_fst_1223_);
lean_dec(v___x_1222_);
if (lean_obj_tag(v_fst_1223_) == 0)
{
uint8_t v___x_1224_; 
v___x_1224_ = 1;
return v___x_1224_;
}
else
{
lean_object* v_val_1225_; uint8_t v___x_1226_; 
v_val_1225_ = lean_ctor_get(v_fst_1223_, 0);
lean_inc(v_val_1225_);
lean_dec_ref(v_fst_1223_);
v___x_1226_ = lean_unbox(v_val_1225_);
lean_dec(v_val_1225_);
return v___x_1226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___boxed(lean_object* v_00_u03b1_1227_, lean_object* v_m_1228_, lean_object* v_p_1229_){
_start:
{
uint8_t v_res_1230_; lean_object* v_r_1231_; 
v_res_1230_ = l_Std_HashSet_Raw_all(v_00_u03b1_1227_, v_m_1228_, v_p_1229_);
v_r_1231_ = lean_box(v_res_1230_);
return v_r_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0(lean_object* v_p_1232_, lean_object* v___x_1233_, lean_object* v___x_1234_, lean_object* v_a_1235_, lean_object* v_b_1236_, lean_object* v_acc_1237_){
_start:
{
lean_object* v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = lean_apply_1(v_p_1232_, v_a_1235_);
v___x_1239_ = lean_unbox(v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1233_);
return v___x_1240_;
}
else
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_dec_ref(v___x_1233_);
v___x_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1238_);
v___x_1242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1241_);
lean_ctor_set(v___x_1242_, 1, v___x_1234_);
v___x_1243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1242_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1244_, lean_object* v___x_1245_, lean_object* v___x_1246_, lean_object* v_a_1247_, lean_object* v_b_1248_, lean_object* v_acc_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Std_HashSet_Raw_any___redArg___lam__0(v_p_1244_, v___x_1245_, v___x_1246_, v_a_1247_, v_b_1248_, v_acc_1249_);
lean_dec_ref(v_acc_1249_);
return v_res_1250_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any___redArg(lean_object* v_m_1251_, lean_object* v_p_1252_){
_start:
{
lean_object* v___x_1253_; lean_object* v_buckets_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___f_1257_; lean_object* v___f_1258_; size_t v_sz_1259_; size_t v___x_1260_; lean_object* v___x_1261_; lean_object* v_fst_1262_; 
v___x_1253_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1254_ = lean_ctor_get(v_m_1251_, 1);
lean_inc_ref(v_buckets_1254_);
lean_dec_ref(v_m_1251_);
v___x_1255_ = lean_box(0);
v___x_1256_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1257_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1257_, 0, v_p_1252_);
lean_closure_set(v___f_1257_, 1, v___x_1256_);
lean_closure_set(v___f_1257_, 2, v___x_1255_);
v___f_1258_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1258_, 0, v___x_1253_);
lean_closure_set(v___f_1258_, 1, v___f_1257_);
v_sz_1259_ = lean_array_size(v_buckets_1254_);
v___x_1260_ = ((size_t)0ULL);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1253_, v_buckets_1254_, v___f_1258_, v_sz_1259_, v___x_1260_, v___x_1256_);
v_fst_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_fst_1262_);
lean_dec(v___x_1261_);
if (lean_obj_tag(v_fst_1262_) == 0)
{
uint8_t v___x_1263_; 
v___x_1263_ = 0;
return v___x_1263_;
}
else
{
lean_object* v_val_1264_; uint8_t v___x_1265_; 
v_val_1264_ = lean_ctor_get(v_fst_1262_, 0);
lean_inc(v_val_1264_);
lean_dec_ref(v_fst_1262_);
v___x_1265_ = lean_unbox(v_val_1264_);
lean_dec(v_val_1264_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___boxed(lean_object* v_m_1266_, lean_object* v_p_1267_){
_start:
{
uint8_t v_res_1268_; lean_object* v_r_1269_; 
v_res_1268_ = l_Std_HashSet_Raw_any___redArg(v_m_1266_, v_p_1267_);
v_r_1269_ = lean_box(v_res_1268_);
return v_r_1269_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any(lean_object* v_00_u03b1_1270_, lean_object* v_m_1271_, lean_object* v_p_1272_){
_start:
{
lean_object* v___x_1273_; lean_object* v_buckets_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___f_1277_; lean_object* v___f_1278_; size_t v_sz_1279_; size_t v___x_1280_; lean_object* v___x_1281_; lean_object* v_fst_1282_; 
v___x_1273_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1274_ = lean_ctor_get(v_m_1271_, 1);
lean_inc_ref(v_buckets_1274_);
lean_dec_ref(v_m_1271_);
v___x_1275_ = lean_box(0);
v___x_1276_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1277_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1277_, 0, v_p_1272_);
lean_closure_set(v___f_1277_, 1, v___x_1276_);
lean_closure_set(v___f_1277_, 2, v___x_1275_);
v___f_1278_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1278_, 0, v___x_1273_);
lean_closure_set(v___f_1278_, 1, v___f_1277_);
v_sz_1279_ = lean_array_size(v_buckets_1274_);
v___x_1280_ = ((size_t)0ULL);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1273_, v_buckets_1274_, v___f_1278_, v_sz_1279_, v___x_1280_, v___x_1276_);
v_fst_1282_ = lean_ctor_get(v___x_1281_, 0);
lean_inc(v_fst_1282_);
lean_dec(v___x_1281_);
if (lean_obj_tag(v_fst_1282_) == 0)
{
uint8_t v___x_1283_; 
v___x_1283_ = 0;
return v___x_1283_;
}
else
{
lean_object* v_val_1284_; uint8_t v___x_1285_; 
v_val_1284_ = lean_ctor_get(v_fst_1282_, 0);
lean_inc(v_val_1284_);
lean_dec_ref(v_fst_1282_);
v___x_1285_ = lean_unbox(v_val_1284_);
lean_dec(v_val_1284_);
return v___x_1285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___boxed(lean_object* v_00_u03b1_1286_, lean_object* v_m_1287_, lean_object* v_p_1288_){
_start:
{
uint8_t v_res_1289_; lean_object* v_r_1290_; 
v_res_1289_ = l_Std_HashSet_Raw_any(v_00_u03b1_1286_, v_m_1287_, v_p_1288_);
v_r_1290_ = lean_box(v_res_1289_);
return v_r_1290_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany___redArg(lean_object* v_inst_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_m_1294_, lean_object* v_l_1295_){
_start:
{
lean_object* v_buckets_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; uint8_t v___x_1299_; 
v_buckets_1296_ = lean_ctor_get(v_m_1294_, 1);
v___x_1297_ = lean_unsigned_to_nat(0u);
v___x_1298_ = lean_array_get_size(v_buckets_1296_);
v___x_1299_ = lean_nat_dec_lt(v___x_1297_, v___x_1298_);
if (v___x_1299_ == 0)
{
lean_dec(v_l_1295_);
lean_dec(v_inst_1293_);
lean_dec_ref(v_inst_1292_);
lean_dec_ref(v_inst_1291_);
return v_m_1294_;
}
else
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1293_, v_inst_1291_, v_inst_1292_, v_m_1294_, v_l_1295_);
return v___x_1300_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany(lean_object* v_00_u03b1_1301_, lean_object* v_inst_1302_, lean_object* v_inst_1303_, lean_object* v_00_u03c1_1304_, lean_object* v_inst_1305_, lean_object* v_m_1306_, lean_object* v_l_1307_){
_start:
{
lean_object* v_buckets_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v_buckets_1308_ = lean_ctor_get(v_m_1306_, 1);
v___x_1309_ = lean_unsigned_to_nat(0u);
v___x_1310_ = lean_array_get_size(v_buckets_1308_);
v___x_1311_ = lean_nat_dec_lt(v___x_1309_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_dec(v_l_1307_);
lean_dec(v_inst_1305_);
lean_dec_ref(v_inst_1303_);
lean_dec_ref(v_inst_1302_);
return v_m_1306_;
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1305_, v_inst_1302_, v_inst_1303_, v_m_1306_, v_l_1307_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray___redArg(lean_object* v_inst_1317_, lean_object* v_inst_1318_, lean_object* v_l_1319_){
_start:
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_1321_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1321_ == 0)
{
lean_dec_ref(v_l_1319_);
lean_dec_ref(v_inst_1318_);
lean_dec_ref(v_inst_1317_);
return v___x_1320_;
}
else
{
lean_object* v___f_1322_; lean_object* v___x_1323_; 
v___f_1322_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1323_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1322_, v_inst_1317_, v_inst_1318_, v___x_1320_, v_l_1319_);
return v___x_1323_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray(lean_object* v_00_u03b1_1324_, lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_l_1327_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg(lean_object* v_m_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_Std_HashSet_Raw_Internal_numBuckets___redArg(v_m_1334_);
lean_dec_ref(v_m_1334_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets(lean_object* v_00_u03b1_1336_, lean_object* v_m_1337_){
_start:
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1337_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1339_, lean_object* v_m_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_HashSet_Raw_Internal_numBuckets(v_00_u03b1_1339_, v_m_1340_);
lean_dec_ref(v_m_1340_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2(lean_object* v_inst_1345_, lean_object* v___f_1346_, lean_object* v_m_1347_, lean_object* v_prec_1348_){
_start:
{
lean_object* v___x_1349_; lean_object* v_buckets_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1370_; 
v___x_1349_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1350_ = lean_ctor_get(v_m_1347_, 1);
v_isSharedCheck_1370_ = !lean_is_exclusive(v_m_1347_);
if (v_isSharedCheck_1370_ == 0)
{
lean_object* v_unused_1371_; 
v_unused_1371_ = lean_ctor_get(v_m_1347_, 0);
lean_dec(v_unused_1371_);
v___x_1352_ = v_m_1347_;
v_isShared_1353_ = v_isSharedCheck_1370_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_buckets_1350_);
lean_dec(v_m_1347_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1370_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; lean_object* v___y_1356_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v___x_1354_ = ((lean_object*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1));
v___x_1362_ = lean_box(0);
v___x_1363_ = lean_array_get_size(v_buckets_1350_);
v___x_1364_ = lean_unsigned_to_nat(0u);
v___x_1365_ = lean_nat_dec_lt(v___x_1364_, v___x_1363_);
if (v___x_1365_ == 0)
{
lean_dec_ref(v_buckets_1350_);
lean_dec_ref(v___f_1346_);
v___y_1356_ = v___x_1362_;
goto v___jp_1355_;
}
else
{
lean_object* v___f_1366_; size_t v___x_1367_; size_t v___x_1368_; lean_object* v___x_1369_; 
v___f_1366_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1366_, 0, v___x_1349_);
lean_closure_set(v___f_1366_, 1, v___f_1346_);
v___x_1367_ = lean_usize_of_nat(v___x_1363_);
v___x_1368_ = ((size_t)0ULL);
v___x_1369_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1349_, v___f_1366_, v_buckets_1350_, v___x_1367_, v___x_1368_, v___x_1362_);
v___y_1356_ = v___x_1369_;
goto v___jp_1355_;
}
v___jp_1355_:
{
lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1357_ = l_List_repr___redArg(v_inst_1345_, v___y_1356_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 5);
lean_ctor_set(v___x_1352_, 1, v___x_1357_);
lean_ctor_set(v___x_1352_, 0, v___x_1354_);
v___x_1359_ = v___x_1352_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1361_, 1, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Repr_addAppParen(v___x_1359_, v_prec_1348_);
return v___x_1360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1372_, lean_object* v___f_1373_, lean_object* v_m_1374_, lean_object* v_prec_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2(v_inst_1372_, v___f_1373_, v_m_1374_, v_prec_1375_);
lean_dec(v_prec_1375_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg(lean_object* v_inst_1377_){
_start:
{
lean_object* v___f_1378_; lean_object* v___f_1379_; 
v___f_1378_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___f_1379_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1379_, 0, v_inst_1377_);
lean_closure_set(v___f_1379_, 1, v___f_1378_);
return v___f_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr(lean_object* v_00_u03b1_1380_, lean_object* v_inst_1381_){
_start:
{
lean_object* v___x_1382_; 
v___x_1382_ = l_Std_HashSet_Raw_instRepr___redArg(v_inst_1381_);
return v___x_1382_;
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
