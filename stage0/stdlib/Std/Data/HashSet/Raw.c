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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_HashSet_Raw_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__9_value)} };
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
lean_object* v_toApplicative_659_; lean_object* v_buckets_660_; lean_object* v_toPure_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_toApplicative_659_ = lean_ctor_get(v_inst_655_, 0);
v_buckets_660_ = lean_ctor_get(v_b_658_, 1);
lean_inc_ref(v_buckets_660_);
lean_dec_ref(v_b_658_);
v_toPure_661_ = lean_ctor_get(v_toApplicative_659_, 1);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_array_get_size(v_buckets_660_);
v___x_664_ = lean_nat_dec_lt(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; 
lean_inc(v_toPure_661_);
lean_dec_ref(v_buckets_660_);
lean_dec(v_f_656_);
lean_dec_ref(v_inst_655_);
v___x_665_ = lean_apply_2(v_toPure_661_, lean_box(0), v_init_657_);
return v___x_665_;
}
else
{
lean_object* v___f_666_; lean_object* v___f_667_; size_t v___x_668_; size_t v___x_669_; lean_object* v___x_670_; 
v___f_666_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_666_, 0, v_f_656_);
lean_inc_ref(v_inst_655_);
v___f_667_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_667_, 0, v_inst_655_);
lean_closure_set(v___f_667_, 1, v___f_666_);
v___x_668_ = ((size_t)0ULL);
v___x_669_ = lean_usize_of_nat(v___x_663_);
v___x_670_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_655_, v___f_667_, v_buckets_660_, v___x_668_, v___x_669_, v_init_657_);
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM(lean_object* v_00_u03b1_671_, lean_object* v_m_672_, lean_object* v_inst_673_, lean_object* v_00_u03b2_674_, lean_object* v_f_675_, lean_object* v_init_676_, lean_object* v_b_677_){
_start:
{
lean_object* v_toApplicative_678_; lean_object* v_buckets_679_; lean_object* v_toPure_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_toApplicative_678_ = lean_ctor_get(v_inst_673_, 0);
v_buckets_679_ = lean_ctor_get(v_b_677_, 1);
lean_inc_ref(v_buckets_679_);
lean_dec_ref(v_b_677_);
v_toPure_680_ = lean_ctor_get(v_toApplicative_678_, 1);
v___x_681_ = lean_unsigned_to_nat(0u);
v___x_682_ = lean_array_get_size(v_buckets_679_);
v___x_683_ = lean_nat_dec_lt(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_inc(v_toPure_680_);
lean_dec_ref(v_buckets_679_);
lean_dec(v_f_675_);
lean_dec_ref(v_inst_673_);
v___x_684_ = lean_apply_2(v_toPure_680_, lean_box(0), v_init_676_);
return v___x_684_;
}
else
{
lean_object* v___f_685_; lean_object* v___f_686_; size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v___f_685_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_685_, 0, v_f_675_);
lean_inc_ref(v_inst_673_);
v___f_686_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_686_, 0, v_inst_673_);
lean_closure_set(v___f_686_, 1, v___f_685_);
v___x_687_ = ((size_t)0ULL);
v___x_688_ = lean_usize_of_nat(v___x_682_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_673_, v___f_686_, v_buckets_679_, v___x_687_, v___x_688_, v_init_676_);
return v___x_689_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__0(lean_object* v_f_690_, lean_object* v_x1_691_, lean_object* v_x2_692_, lean_object* v_x3_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = lean_apply_2(v_f_690_, v_x1_691_, v_x2_692_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__1(lean_object* v___x_695_, lean_object* v___f_696_, lean_object* v_acc_697_, lean_object* v_l_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_695_, v___f_696_, v_acc_697_, v_l_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg(lean_object* v_f_700_, lean_object* v_init_701_, lean_object* v_m_702_){
_start:
{
lean_object* v___x_703_; lean_object* v_buckets_704_; lean_object* v___x_705_; lean_object* v___x_706_; uint8_t v___x_707_; 
v___x_703_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_704_ = lean_ctor_get(v_m_702_, 1);
lean_inc_ref(v_buckets_704_);
lean_dec_ref(v_m_702_);
v___x_705_ = lean_unsigned_to_nat(0u);
v___x_706_ = lean_array_get_size(v_buckets_704_);
v___x_707_ = lean_nat_dec_lt(v___x_705_, v___x_706_);
if (v___x_707_ == 0)
{
lean_dec_ref(v_buckets_704_);
lean_dec(v_f_700_);
return v_init_701_;
}
else
{
lean_object* v___f_708_; lean_object* v___f_709_; size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; 
v___f_708_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_708_, 0, v_f_700_);
v___f_709_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_709_, 0, v___x_703_);
lean_closure_set(v___f_709_, 1, v___f_708_);
v___x_710_ = ((size_t)0ULL);
v___x_711_ = lean_usize_of_nat(v___x_706_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_703_, v___f_709_, v_buckets_704_, v___x_710_, v___x_711_, v_init_701_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold(lean_object* v_00_u03b1_713_, lean_object* v_00_u03b2_714_, lean_object* v_f_715_, lean_object* v_init_716_, lean_object* v_m_717_){
_start:
{
lean_object* v___x_718_; lean_object* v_buckets_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v___x_718_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_719_ = lean_ctor_get(v_m_717_, 1);
lean_inc_ref(v_buckets_719_);
lean_dec_ref(v_m_717_);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_array_get_size(v_buckets_719_);
v___x_722_ = lean_nat_dec_lt(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_dec_ref(v_buckets_719_);
lean_dec(v_f_715_);
return v_init_716_;
}
else
{
lean_object* v___f_723_; lean_object* v___f_724_; size_t v___x_725_; size_t v___x_726_; lean_object* v___x_727_; 
v___f_723_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_723_, 0, v_f_715_);
v___f_724_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_724_, 0, v___x_718_);
lean_closure_set(v___f_724_, 1, v___f_723_);
v___x_725_ = ((size_t)0ULL);
v___x_726_ = lean_usize_of_nat(v___x_721_);
v___x_727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_718_, v___f_724_, v_buckets_719_, v___x_725_, v___x_726_, v_init_716_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__0(lean_object* v_f_728_, lean_object* v_x_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = lean_apply_1(v_f_728_, v___y_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__1(lean_object* v_inst_733_, lean_object* v___f_734_, lean_object* v_x_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = lean_box(0);
v___x_738_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_733_, v___f_734_, v___x_737_, v___y_736_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg(lean_object* v_inst_739_, lean_object* v_f_740_, lean_object* v_b_741_){
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
v___f_750_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_750_, 0, v_f_740_);
lean_inc_ref(v_inst_739_);
v___f_751_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_751_, 0, v_inst_739_);
lean_closure_set(v___f_751_, 1, v___f_750_);
v___x_752_ = ((size_t)0ULL);
v___x_753_ = lean_usize_of_nat(v___x_746_);
v___x_754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_739_, v___f_751_, v_buckets_743_, v___x_752_, v___x_753_, v___x_747_);
return v___x_754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM(lean_object* v_00_u03b1_755_, lean_object* v_m_756_, lean_object* v_inst_757_, lean_object* v_f_758_, lean_object* v_b_759_){
_start:
{
lean_object* v_toApplicative_760_; lean_object* v_buckets_761_; lean_object* v_toPure_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_toApplicative_760_ = lean_ctor_get(v_inst_757_, 0);
v_buckets_761_ = lean_ctor_get(v_b_759_, 1);
lean_inc_ref(v_buckets_761_);
lean_dec_ref(v_b_759_);
v_toPure_762_ = lean_ctor_get(v_toApplicative_760_, 1);
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_array_get_size(v_buckets_761_);
v___x_765_ = lean_box(0);
v___x_766_ = lean_nat_dec_lt(v___x_763_, v___x_764_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; 
lean_inc(v_toPure_762_);
lean_dec_ref(v_buckets_761_);
lean_dec(v_f_758_);
lean_dec_ref(v_inst_757_);
v___x_767_ = lean_apply_2(v_toPure_762_, lean_box(0), v___x_765_);
return v___x_767_;
}
else
{
lean_object* v___f_768_; lean_object* v___f_769_; size_t v___x_770_; size_t v___x_771_; lean_object* v___x_772_; 
v___f_768_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_768_, 0, v_f_758_);
lean_inc_ref(v_inst_757_);
v___f_769_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_769_, 0, v_inst_757_);
lean_closure_set(v___f_769_, 1, v___f_768_);
v___x_770_ = ((size_t)0ULL);
v___x_771_ = lean_usize_of_nat(v___x_764_);
v___x_772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_757_, v___f_769_, v_buckets_761_, v___x_770_, v___x_771_, v___x_765_);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__0(lean_object* v_f_773_, lean_object* v_a_774_, lean_object* v_x_775_, lean_object* v_acc_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = lean_apply_2(v_f_773_, v_a_774_, v_acc_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__1(lean_object* v_inst_778_, lean_object* v___f_779_, lean_object* v_a_780_, lean_object* v_x_781_, lean_object* v___y_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_778_, v___f_779_, v_a_780_, v___y_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg(lean_object* v_inst_784_, lean_object* v_f_785_, lean_object* v_init_786_, lean_object* v_b_787_){
_start:
{
lean_object* v_buckets_788_; lean_object* v___f_789_; lean_object* v___f_790_; size_t v_sz_791_; size_t v___x_792_; lean_object* v___x_793_; 
v_buckets_788_ = lean_ctor_get(v_b_787_, 1);
lean_inc_ref(v_buckets_788_);
lean_dec_ref(v_b_787_);
v___f_789_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_789_, 0, v_f_785_);
lean_inc_ref(v_inst_784_);
v___f_790_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_790_, 0, v_inst_784_);
lean_closure_set(v___f_790_, 1, v___f_789_);
v_sz_791_ = lean_array_size(v_buckets_788_);
v___x_792_ = ((size_t)0ULL);
v___x_793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_784_, v_buckets_788_, v___f_790_, v_sz_791_, v___x_792_, v_init_786_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn(lean_object* v_00_u03b1_794_, lean_object* v_m_795_, lean_object* v_inst_796_, lean_object* v_00_u03b2_797_, lean_object* v_f_798_, lean_object* v_init_799_, lean_object* v_b_800_){
_start:
{
lean_object* v_buckets_801_; lean_object* v___f_802_; lean_object* v___f_803_; size_t v_sz_804_; size_t v___x_805_; lean_object* v___x_806_; 
v_buckets_801_ = lean_ctor_get(v_b_800_, 1);
lean_inc_ref(v_buckets_801_);
lean_dec_ref(v_b_800_);
v___f_802_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_802_, 0, v_f_798_);
lean_inc_ref(v_inst_796_);
v___f_803_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_803_, 0, v_inst_796_);
lean_closure_set(v___f_803_, 1, v___f_802_);
v_sz_804_ = lean_array_size(v_buckets_801_);
v___x_805_ = ((size_t)0ULL);
v___x_806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_796_, v_buckets_801_, v___f_803_, v_sz_804_, v___x_805_, v_init_799_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2(lean_object* v_inst_807_, lean_object* v_m_808_, lean_object* v_f_809_){
_start:
{
lean_object* v_toApplicative_810_; lean_object* v_buckets_811_; lean_object* v_toPure_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_toApplicative_810_ = lean_ctor_get(v_inst_807_, 0);
v_buckets_811_ = lean_ctor_get(v_m_808_, 1);
lean_inc_ref(v_buckets_811_);
lean_dec_ref(v_m_808_);
v_toPure_812_ = lean_ctor_get(v_toApplicative_810_, 1);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_array_get_size(v_buckets_811_);
v___x_815_ = lean_box(0);
v___x_816_ = lean_nat_dec_lt(v___x_813_, v___x_814_);
if (v___x_816_ == 0)
{
lean_object* v___x_817_; 
lean_inc(v_toPure_812_);
lean_dec_ref(v_buckets_811_);
lean_dec(v_f_809_);
lean_dec_ref(v_inst_807_);
v___x_817_ = lean_apply_2(v_toPure_812_, lean_box(0), v___x_815_);
return v___x_817_;
}
else
{
lean_object* v___f_818_; lean_object* v___f_819_; size_t v___x_820_; size_t v___x_821_; lean_object* v___x_822_; 
v___f_818_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_818_, 0, v_f_809_);
lean_inc_ref(v_inst_807_);
v___f_819_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_819_, 0, v_inst_807_);
lean_closure_set(v___f_819_, 1, v___f_818_);
v___x_820_ = ((size_t)0ULL);
v___x_821_ = lean_usize_of_nat(v___x_814_);
v___x_822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_807_, v___f_819_, v_buckets_811_, v___x_820_, v___x_821_, v___x_815_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_823_){
_start:
{
lean_object* v___f_824_; 
v___f_824_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_824_, 0, v_inst_823_);
return v___f_824_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_825_, lean_object* v_m_826_, lean_object* v_inst_827_){
_start:
{
lean_object* v___f_828_; 
v___f_828_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_828_, 0, v_inst_827_);
return v___f_828_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_829_, lean_object* v_00_u03b2_830_, lean_object* v_m_831_, lean_object* v_init_832_, lean_object* v_f_833_){
_start:
{
lean_object* v_buckets_834_; lean_object* v___f_835_; lean_object* v___f_836_; size_t v_sz_837_; size_t v___x_838_; lean_object* v___x_839_; 
v_buckets_834_ = lean_ctor_get(v_m_831_, 1);
lean_inc_ref(v_buckets_834_);
lean_dec_ref(v_m_831_);
v___f_835_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_835_, 0, v_f_833_);
lean_inc_ref(v_inst_829_);
v___f_836_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_836_, 0, v_inst_829_);
lean_closure_set(v___f_836_, 1, v___f_835_);
v_sz_837_ = lean_array_size(v_buckets_834_);
v___x_838_ = ((size_t)0ULL);
v___x_839_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_829_, v_buckets_834_, v___f_836_, v_sz_837_, v___x_838_, v_init_832_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_840_){
_start:
{
lean_object* v___f_841_; 
v___f_841_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_841_, 0, v_inst_840_);
return v___f_841_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_842_, lean_object* v_m_843_, lean_object* v_inst_844_){
_start:
{
lean_object* v___f_845_; 
v___f_845_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_845_, 0, v_inst_844_);
return v___f_845_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_filter___redArg___lam__0(lean_object* v_f_846_, lean_object* v_a_847_, lean_object* v_x_848_){
_start:
{
lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_849_ = lean_apply_1(v_f_846_, v_a_847_);
v___x_850_ = lean_unbox(v___x_849_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_851_, lean_object* v_a_852_, lean_object* v_x_853_){
_start:
{
uint8_t v_res_854_; lean_object* v_r_855_; 
v_res_854_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_851_, v_a_852_, v_x_853_);
v_r_855_ = lean_box(v_res_854_);
return v_r_855_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg(lean_object* v_f_856_, lean_object* v_m_857_){
_start:
{
lean_object* v_buckets_858_; lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_buckets_858_ = lean_ctor_get(v_m_857_, 1);
v___x_859_ = lean_unsigned_to_nat(0u);
v___x_860_ = lean_array_get_size(v_buckets_858_);
v___x_861_ = lean_nat_dec_lt(v___x_859_, v___x_860_);
if (v___x_861_ == 0)
{
lean_object* v___x_862_; 
lean_dec_ref(v_m_857_);
lean_dec_ref(v_f_856_);
v___x_862_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
return v___x_862_;
}
else
{
lean_object* v___f_863_; lean_object* v___x_864_; 
v___f_863_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_863_, 0, v_f_856_);
v___x_864_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_863_, v_m_857_);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter(lean_object* v_00_u03b1_865_, lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_f_868_, lean_object* v_m_869_){
_start:
{
lean_object* v_buckets_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_buckets_870_ = lean_ctor_get(v_m_869_, 1);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_array_get_size(v_buckets_870_);
v___x_873_ = lean_nat_dec_lt(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec_ref(v_m_869_);
lean_dec_ref(v_f_868_);
v___x_874_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
return v___x_874_;
}
else
{
lean_object* v___f_875_; lean_object* v___x_876_; 
v___f_875_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_875_, 0, v_f_868_);
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_875_, v_m_869_);
return v___x_876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___boxed(lean_object* v_00_u03b1_877_, lean_object* v_inst_878_, lean_object* v_inst_879_, lean_object* v_f_880_, lean_object* v_m_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_HashSet_Raw_filter(v_00_u03b1_877_, v_inst_878_, v_inst_879_, v_f_880_, v_m_881_);
lean_dec_ref(v_inst_879_);
lean_dec_ref(v_inst_878_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__0(lean_object* v_x1_883_, lean_object* v_x2_884_, lean_object* v_x3_885_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = lean_array_push(v_x1_883_, v_x2_884_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__1(lean_object* v___x_887_, lean_object* v___f_888_, lean_object* v_acc_889_, lean_object* v_l_890_){
_start:
{
lean_object* v___x_891_; 
v___x_891_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_887_, v___f_888_, v_acc_889_, v_l_890_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg(lean_object* v_m_896_){
_start:
{
lean_object* v_size_897_; lean_object* v_buckets_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v_size_897_ = lean_ctor_get(v_m_896_, 0);
lean_inc(v_size_897_);
v_buckets_898_ = lean_ctor_get(v_m_896_, 1);
lean_inc_ref(v_buckets_898_);
lean_dec_ref(v_m_896_);
v___x_899_ = lean_mk_empty_array_with_capacity(v_size_897_);
lean_dec(v_size_897_);
v___x_900_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_array_get_size(v_buckets_898_);
v___x_903_ = lean_nat_dec_lt(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
lean_dec_ref(v_buckets_898_);
return v___x_899_;
}
else
{
lean_object* v___f_904_; size_t v___x_905_; size_t v___x_906_; lean_object* v___x_907_; 
v___f_904_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_905_ = ((size_t)0ULL);
v___x_906_ = lean_usize_of_nat(v___x_902_);
v___x_907_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_900_, v___f_904_, v_buckets_898_, v___x_905_, v___x_906_, v___x_899_);
return v___x_907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray(lean_object* v_00_u03b1_908_, lean_object* v_m_909_){
_start:
{
lean_object* v_size_910_; lean_object* v_buckets_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; uint8_t v___x_916_; 
v_size_910_ = lean_ctor_get(v_m_909_, 0);
lean_inc(v_size_910_);
v_buckets_911_ = lean_ctor_get(v_m_909_, 1);
lean_inc_ref(v_buckets_911_);
lean_dec_ref(v_m_909_);
v___x_912_ = lean_mk_empty_array_with_capacity(v_size_910_);
lean_dec(v_size_910_);
v___x_913_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_914_ = lean_unsigned_to_nat(0u);
v___x_915_ = lean_array_get_size(v_buckets_911_);
v___x_916_ = lean_nat_dec_lt(v___x_914_, v___x_915_);
if (v___x_916_ == 0)
{
lean_dec_ref(v_buckets_911_);
return v___x_912_;
}
else
{
lean_object* v___f_917_; size_t v___x_918_; size_t v___x_919_; lean_object* v___x_920_; 
v___f_917_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_918_ = ((size_t)0ULL);
v___x_919_ = lean_usize_of_nat(v___x_915_);
v___x_920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_913_, v___f_917_, v_buckets_911_, v___x_918_, v___x_919_, v___x_912_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__0(lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_a_923_, lean_object* v_b_924_, lean_object* v_acc_925_){
_start:
{
lean_object* v_r_926_; lean_object* v___x_927_; 
v_r_926_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_921_, v_inst_922_, v_acc_925_, v_a_923_, v_b_924_);
v___x_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_927_, 0, v_r_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__1(lean_object* v___x_928_, lean_object* v___f_929_, lean_object* v_a_930_, lean_object* v_x_931_, lean_object* v___y_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_928_, v___f_929_, v_a_930_, v___y_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg(lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_m_u2081_938_, lean_object* v_m_u2082_939_){
_start:
{
lean_object* v_size_940_; lean_object* v_buckets_941_; lean_object* v___x_942_; lean_object* v___x_943_; uint8_t v___x_944_; 
v_size_940_ = lean_ctor_get(v_m_u2081_938_, 0);
v_buckets_941_ = lean_ctor_get(v_m_u2081_938_, 1);
v___x_942_ = lean_unsigned_to_nat(0u);
v___x_943_ = lean_array_get_size(v_buckets_941_);
v___x_944_ = lean_nat_dec_lt(v___x_942_, v___x_943_);
if (v___x_944_ == 0)
{
lean_dec_ref(v_m_u2081_938_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
return v_m_u2082_939_;
}
else
{
lean_object* v_size_945_; lean_object* v_buckets_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_size_945_ = lean_ctor_get(v_m_u2082_939_, 0);
v_buckets_946_ = lean_ctor_get(v_m_u2082_939_, 1);
v___x_947_ = lean_array_get_size(v_buckets_946_);
v___x_948_ = lean_nat_dec_lt(v___x_942_, v___x_947_);
if (v___x_948_ == 0)
{
lean_dec_ref(v_m_u2082_939_);
lean_dec_ref(v_inst_937_);
lean_dec_ref(v_inst_936_);
return v_m_u2081_938_;
}
else
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_950_ = lean_nat_dec_le(v_size_940_, v_size_945_);
if (v___x_950_ == 0)
{
lean_object* v___f_951_; lean_object* v___x_952_; 
v___f_951_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_952_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_951_, v_inst_936_, v_inst_937_, v_m_u2081_938_, v_m_u2082_939_);
return v___x_952_;
}
else
{
lean_object* v___f_953_; lean_object* v___f_954_; size_t v_sz_955_; size_t v___x_956_; lean_object* v___x_957_; 
lean_inc_ref(v_buckets_941_);
lean_dec_ref(v_m_u2081_938_);
v___f_953_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_953_, 0, v_inst_936_);
lean_closure_set(v___f_953_, 1, v_inst_937_);
v___f_954_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_954_, 0, v___x_949_);
lean_closure_set(v___f_954_, 1, v___f_953_);
v_sz_955_ = lean_array_size(v_buckets_941_);
v___x_956_ = ((size_t)0ULL);
v___x_957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_949_, v_buckets_941_, v___f_954_, v_sz_955_, v___x_956_, v_m_u2082_939_);
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union(lean_object* v_00_u03b1_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_m_u2081_961_, lean_object* v_m_u2082_962_){
_start:
{
lean_object* v_size_963_; lean_object* v_buckets_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_size_963_ = lean_ctor_get(v_m_u2081_961_, 0);
v_buckets_964_ = lean_ctor_get(v_m_u2081_961_, 1);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = lean_array_get_size(v_buckets_964_);
v___x_967_ = lean_nat_dec_lt(v___x_965_, v___x_966_);
if (v___x_967_ == 0)
{
lean_dec_ref(v_m_u2081_961_);
lean_dec_ref(v_inst_960_);
lean_dec_ref(v_inst_959_);
return v_m_u2082_962_;
}
else
{
lean_object* v_size_968_; lean_object* v_buckets_969_; lean_object* v___x_970_; uint8_t v___x_971_; 
v_size_968_ = lean_ctor_get(v_m_u2082_962_, 0);
v_buckets_969_ = lean_ctor_get(v_m_u2082_962_, 1);
v___x_970_ = lean_array_get_size(v_buckets_969_);
v___x_971_ = lean_nat_dec_lt(v___x_965_, v___x_970_);
if (v___x_971_ == 0)
{
lean_dec_ref(v_m_u2082_962_);
lean_dec_ref(v_inst_960_);
lean_dec_ref(v_inst_959_);
return v_m_u2081_961_;
}
else
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_973_ = lean_nat_dec_le(v_size_963_, v_size_968_);
if (v___x_973_ == 0)
{
lean_object* v___f_974_; lean_object* v___x_975_; 
v___f_974_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_974_, v_inst_959_, v_inst_960_, v_m_u2081_961_, v_m_u2082_962_);
return v___x_975_;
}
else
{
lean_object* v___f_976_; lean_object* v___f_977_; size_t v_sz_978_; size_t v___x_979_; lean_object* v___x_980_; 
lean_inc_ref(v_buckets_964_);
lean_dec_ref(v_m_u2081_961_);
v___f_976_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_976_, 0, v_inst_959_);
lean_closure_set(v___f_976_, 1, v_inst_960_);
v___f_977_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_977_, 0, v___x_972_);
lean_closure_set(v___f_977_, 1, v___f_976_);
v_sz_978_ = lean_array_size(v_buckets_964_);
v___x_979_ = ((size_t)0ULL);
v___x_980_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_972_, v_buckets_964_, v___f_977_, v_sz_978_, v___x_979_, v_m_u2082_962_);
return v___x_980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_981_, lean_object* v_inst_982_){
_start:
{
lean_object* v___x_983_; 
v___x_983_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_983_, 0, lean_box(0));
lean_closure_set(v___x_983_, 1, v_inst_981_);
lean_closure_set(v___x_983_, 2, v_inst_982_);
return v___x_983_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_984_, lean_object* v_inst_985_, lean_object* v_inst_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_987_, 0, lean_box(0));
lean_closure_set(v___x_987_, 1, v_inst_985_);
lean_closure_set(v___x_987_, 2, v_inst_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter___redArg(lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_m_u2081_990_, lean_object* v_m_u2082_991_){
_start:
{
lean_object* v_buckets_992_; lean_object* v___x_993_; lean_object* v___x_994_; uint8_t v___x_995_; 
v_buckets_992_ = lean_ctor_get(v_m_u2081_990_, 1);
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = lean_array_get_size(v_buckets_992_);
v___x_995_ = lean_nat_dec_lt(v___x_993_, v___x_994_);
if (v___x_995_ == 0)
{
lean_dec_ref(v_m_u2081_990_);
lean_dec_ref(v_inst_989_);
lean_dec_ref(v_inst_988_);
return v_m_u2082_991_;
}
else
{
lean_object* v_buckets_996_; lean_object* v___x_997_; uint8_t v___x_998_; 
v_buckets_996_ = lean_ctor_get(v_m_u2082_991_, 1);
v___x_997_ = lean_array_get_size(v_buckets_996_);
v___x_998_ = lean_nat_dec_lt(v___x_993_, v___x_997_);
if (v___x_998_ == 0)
{
lean_dec_ref(v_m_u2082_991_);
lean_dec_ref(v_inst_989_);
lean_dec_ref(v_inst_988_);
return v_m_u2081_990_;
}
else
{
lean_object* v___x_999_; 
v___x_999_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_988_, v_inst_989_, v_m_u2081_990_, v_m_u2082_991_);
return v___x_999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter(lean_object* v_00_u03b1_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_m_u2081_1003_, lean_object* v_m_u2082_1004_){
_start:
{
lean_object* v_buckets_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; uint8_t v___x_1008_; 
v_buckets_1005_ = lean_ctor_get(v_m_u2081_1003_, 1);
v___x_1006_ = lean_unsigned_to_nat(0u);
v___x_1007_ = lean_array_get_size(v_buckets_1005_);
v___x_1008_ = lean_nat_dec_lt(v___x_1006_, v___x_1007_);
if (v___x_1008_ == 0)
{
lean_dec_ref(v_m_u2081_1003_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v_inst_1001_);
return v_m_u2082_1004_;
}
else
{
lean_object* v_buckets_1009_; lean_object* v___x_1010_; uint8_t v___x_1011_; 
v_buckets_1009_ = lean_ctor_get(v_m_u2082_1004_, 1);
v___x_1010_ = lean_array_get_size(v_buckets_1009_);
v___x_1011_ = lean_nat_dec_lt(v___x_1006_, v___x_1010_);
if (v___x_1011_ == 0)
{
lean_dec_ref(v_m_u2082_1004_);
lean_dec_ref(v_inst_1002_);
lean_dec_ref(v_inst_1001_);
return v_m_u2081_1003_;
}
else
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1001_, v_inst_1002_, v_m_u2081_1003_, v_m_u2082_1004_);
return v___x_1012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1013_, lean_object* v_inst_1014_){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1015_, 0, lean_box(0));
lean_closure_set(v___x_1015_, 1, v_inst_1013_);
lean_closure_set(v___x_1015_, 2, v_inst_1014_);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1016_, lean_object* v_inst_1017_, lean_object* v_inst_1018_){
_start:
{
lean_object* v___x_1019_; 
v___x_1019_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1019_, 0, lean_box(0));
lean_closure_set(v___x_1019_, 1, v_inst_1017_);
lean_closure_set(v___x_1019_, 2, v_inst_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___f_1021_; 
v___x_1020_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1021_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1021_, 0, v___x_1020_);
return v___f_1021_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq___redArg(lean_object* v_inst_1022_, lean_object* v_inst_1023_, lean_object* v_m_u2081_1024_, lean_object* v_m_u2082_1025_){
_start:
{
lean_object* v___f_1026_; uint8_t v___x_1027_; 
v___f_1026_ = lean_obj_once(&l_Std_HashSet_Raw_beq___redArg___closed__0, &l_Std_HashSet_Raw_beq___redArg___closed__0_once, _init_l_Std_HashSet_Raw_beq___redArg___closed__0);
v___x_1027_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1022_, v_inst_1023_, v___f_1026_, v_m_u2081_1024_, v_m_u2082_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___redArg___boxed(lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_m_u2081_1030_, lean_object* v_m_u2082_1031_){
_start:
{
uint8_t v_res_1032_; lean_object* v_r_1033_; 
v_res_1032_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1028_, v_inst_1029_, v_m_u2081_1030_, v_m_u2082_1031_);
v_r_1033_ = lean_box(v_res_1032_);
return v_r_1033_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq(lean_object* v_00_u03b1_1034_, lean_object* v_inst_1035_, lean_object* v_inst_1036_, lean_object* v_m_u2081_1037_, lean_object* v_m_u2082_1038_){
_start:
{
uint8_t v___x_1039_; 
v___x_1039_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1035_, v_inst_1036_, v_m_u2081_1037_, v_m_u2082_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___boxed(lean_object* v_00_u03b1_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_, lean_object* v_m_u2081_1043_, lean_object* v_m_u2082_1044_){
_start:
{
uint8_t v_res_1045_; lean_object* v_r_1046_; 
v_res_1045_ = l_Std_HashSet_Raw_beq(v_00_u03b1_1040_, v_inst_1041_, v_inst_1042_, v_m_u2081_1043_, v_m_u2082_1044_);
v_r_1046_ = lean_box(v_res_1045_);
return v_r_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1047_, lean_object* v_inst_1048_){
_start:
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1049_, 0, lean_box(0));
lean_closure_set(v___x_1049_, 1, v_inst_1047_);
lean_closure_set(v___x_1049_, 2, v_inst_1048_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_){
_start:
{
lean_object* v___x_1053_; 
v___x_1053_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1053_, 0, lean_box(0));
lean_closure_set(v___x_1053_, 1, v_inst_1051_);
lean_closure_set(v___x_1053_, 2, v_inst_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_diff___redArg___lam__0(lean_object* v_inst_1054_, lean_object* v_inst_1055_, lean_object* v_m_u2082_1056_, uint8_t v___x_1057_, lean_object* v_k_1058_, lean_object* v_x_1059_){
_start:
{
uint8_t v___x_1060_; 
v___x_1060_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1054_, v_inst_1055_, v_m_u2082_1056_, v_k_1058_);
if (v___x_1060_ == 0)
{
return v___x_1057_;
}
else
{
uint8_t v___x_1061_; 
v___x_1061_ = 0;
return v___x_1061_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1062_, lean_object* v_inst_1063_, lean_object* v_m_u2082_1064_, lean_object* v___x_1065_, lean_object* v_k_1066_, lean_object* v_x_1067_){
_start:
{
uint8_t v___x_97__boxed_1068_; uint8_t v_res_1069_; lean_object* v_r_1070_; 
v___x_97__boxed_1068_ = lean_unbox(v___x_1065_);
v_res_1069_ = l_Std_HashSet_Raw_diff___redArg___lam__0(v_inst_1062_, v_inst_1063_, v_m_u2082_1064_, v___x_97__boxed_1068_, v_k_1066_, v_x_1067_);
lean_dec_ref(v_m_u2082_1064_);
v_r_1070_ = lean_box(v_res_1069_);
return v_r_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg(lean_object* v_inst_1071_, lean_object* v_inst_1072_, lean_object* v_m_u2081_1073_, lean_object* v_m_u2082_1074_){
_start:
{
lean_object* v_size_1075_; lean_object* v_buckets_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v_size_1075_ = lean_ctor_get(v_m_u2081_1073_, 0);
v_buckets_1076_ = lean_ctor_get(v_m_u2081_1073_, 1);
v___x_1077_ = lean_unsigned_to_nat(0u);
v___x_1078_ = lean_array_get_size(v_buckets_1076_);
v___x_1079_ = lean_nat_dec_lt(v___x_1077_, v___x_1078_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v_m_u2081_1073_);
lean_dec_ref(v_inst_1072_);
lean_dec_ref(v_inst_1071_);
return v_m_u2082_1074_;
}
else
{
lean_object* v_size_1080_; lean_object* v_buckets_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v_size_1080_ = lean_ctor_get(v_m_u2082_1074_, 0);
v_buckets_1081_ = lean_ctor_get(v_m_u2082_1074_, 1);
v___x_1082_ = lean_array_get_size(v_buckets_1081_);
v___x_1083_ = lean_nat_dec_lt(v___x_1077_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_dec_ref(v_m_u2082_1074_);
lean_dec_ref(v_inst_1072_);
lean_dec_ref(v_inst_1071_);
return v_m_u2081_1073_;
}
else
{
uint8_t v___x_1084_; 
v___x_1084_ = lean_nat_dec_le(v_size_1075_, v_size_1080_);
if (v___x_1084_ == 0)
{
lean_object* v___f_1085_; lean_object* v___x_1086_; 
v___f_1085_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1086_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1085_, v_inst_1071_, v_inst_1072_, v_m_u2081_1073_, v_m_u2082_1074_);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; lean_object* v___f_1088_; lean_object* v___x_1089_; 
v___x_1087_ = lean_box(v___x_1084_);
v___f_1088_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1088_, 0, v_inst_1071_);
lean_closure_set(v___f_1088_, 1, v_inst_1072_);
lean_closure_set(v___f_1088_, 2, v_m_u2082_1074_);
lean_closure_set(v___f_1088_, 3, v___x_1087_);
v___x_1089_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1088_, v_m_u2081_1073_);
return v___x_1089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff(lean_object* v_00_u03b1_1090_, lean_object* v_inst_1091_, lean_object* v_inst_1092_, lean_object* v_m_u2081_1093_, lean_object* v_m_u2082_1094_){
_start:
{
lean_object* v_size_1095_; lean_object* v_buckets_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v_size_1095_ = lean_ctor_get(v_m_u2081_1093_, 0);
v_buckets_1096_ = lean_ctor_get(v_m_u2081_1093_, 1);
v___x_1097_ = lean_unsigned_to_nat(0u);
v___x_1098_ = lean_array_get_size(v_buckets_1096_);
v___x_1099_ = lean_nat_dec_lt(v___x_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v_m_u2081_1093_);
lean_dec_ref(v_inst_1092_);
lean_dec_ref(v_inst_1091_);
return v_m_u2082_1094_;
}
else
{
lean_object* v_size_1100_; lean_object* v_buckets_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v_size_1100_ = lean_ctor_get(v_m_u2082_1094_, 0);
v_buckets_1101_ = lean_ctor_get(v_m_u2082_1094_, 1);
v___x_1102_ = lean_array_get_size(v_buckets_1101_);
v___x_1103_ = lean_nat_dec_lt(v___x_1097_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_dec_ref(v_m_u2082_1094_);
lean_dec_ref(v_inst_1092_);
lean_dec_ref(v_inst_1091_);
return v_m_u2081_1093_;
}
else
{
uint8_t v___x_1104_; 
v___x_1104_ = lean_nat_dec_le(v_size_1095_, v_size_1100_);
if (v___x_1104_ == 0)
{
lean_object* v___f_1105_; lean_object* v___x_1106_; 
v___f_1105_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1106_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1105_, v_inst_1091_, v_inst_1092_, v_m_u2081_1093_, v_m_u2082_1094_);
return v___x_1106_;
}
else
{
lean_object* v___x_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_box(v___x_1104_);
v___f_1108_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1108_, 0, v_inst_1091_);
lean_closure_set(v___f_1108_, 1, v_inst_1092_);
lean_closure_set(v___f_1108_, 2, v_m_u2082_1094_);
lean_closure_set(v___f_1108_, 3, v___x_1107_);
v___x_1109_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1108_, v_m_u2081_1093_);
return v___x_1109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1110_, lean_object* v_inst_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1112_, 0, lean_box(0));
lean_closure_set(v___x_1112_, 1, v_inst_1110_);
lean_closure_set(v___x_1112_, 2, v_inst_1111_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_){
_start:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1116_, 0, lean_box(0));
lean_closure_set(v___x_1116_, 1, v_inst_1114_);
lean_closure_set(v___x_1116_, 2, v_inst_1115_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0(lean_object* v_p_1117_, lean_object* v___x_1118_, lean_object* v___x_1119_, lean_object* v_a_1120_, lean_object* v_b_1121_, lean_object* v_acc_1122_){
_start:
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = lean_apply_1(v_p_1117_, v_a_1120_);
v___x_1124_ = lean_unbox(v___x_1123_);
if (v___x_1124_ == 0)
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec_ref(v___x_1119_);
v___x_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1125_, 0, v___x_1123_);
v___x_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
lean_ctor_set(v___x_1126_, 1, v___x_1118_);
v___x_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1126_);
return v___x_1127_;
}
else
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1119_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1129_, lean_object* v___x_1130_, lean_object* v___x_1131_, lean_object* v_a_1132_, lean_object* v_b_1133_, lean_object* v_acc_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l_Std_HashSet_Raw_all___redArg___lam__0(v_p_1129_, v___x_1130_, v___x_1131_, v_a_1132_, v_b_1133_, v_acc_1134_);
lean_dec_ref(v_acc_1134_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__1(lean_object* v___x_1136_, lean_object* v___f_1137_, lean_object* v_a_1138_, lean_object* v_x_1139_, lean_object* v___y_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1136_, v___f_1137_, v_a_1138_, v___y_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all___redArg(lean_object* v_m_1145_, lean_object* v_p_1146_){
_start:
{
lean_object* v___x_1147_; lean_object* v_buckets_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___f_1151_; lean_object* v___f_1152_; size_t v_sz_1153_; size_t v___x_1154_; lean_object* v___x_1155_; lean_object* v_fst_1156_; 
v___x_1147_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1148_ = lean_ctor_get(v_m_1145_, 1);
lean_inc_ref(v_buckets_1148_);
lean_dec_ref(v_m_1145_);
v___x_1149_ = lean_box(0);
v___x_1150_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1151_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1151_, 0, v_p_1146_);
lean_closure_set(v___f_1151_, 1, v___x_1149_);
lean_closure_set(v___f_1151_, 2, v___x_1150_);
v___f_1152_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1152_, 0, v___x_1147_);
lean_closure_set(v___f_1152_, 1, v___f_1151_);
v_sz_1153_ = lean_array_size(v_buckets_1148_);
v___x_1154_ = ((size_t)0ULL);
v___x_1155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1147_, v_buckets_1148_, v___f_1152_, v_sz_1153_, v___x_1154_, v___x_1150_);
v_fst_1156_ = lean_ctor_get(v___x_1155_, 0);
lean_inc(v_fst_1156_);
lean_dec(v___x_1155_);
if (lean_obj_tag(v_fst_1156_) == 0)
{
uint8_t v___x_1157_; 
v___x_1157_ = 1;
return v___x_1157_;
}
else
{
lean_object* v_val_1158_; uint8_t v___x_1159_; 
v_val_1158_ = lean_ctor_get(v_fst_1156_, 0);
lean_inc(v_val_1158_);
lean_dec_ref_known(v_fst_1156_, 1);
v___x_1159_ = lean_unbox(v_val_1158_);
lean_dec(v_val_1158_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___boxed(lean_object* v_m_1160_, lean_object* v_p_1161_){
_start:
{
uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_res_1162_ = l_Std_HashSet_Raw_all___redArg(v_m_1160_, v_p_1161_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all(lean_object* v_00_u03b1_1164_, lean_object* v_m_1165_, lean_object* v_p_1166_){
_start:
{
lean_object* v___x_1167_; lean_object* v_buckets_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___f_1171_; lean_object* v___f_1172_; size_t v_sz_1173_; size_t v___x_1174_; lean_object* v___x_1175_; lean_object* v_fst_1176_; 
v___x_1167_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1168_ = lean_ctor_get(v_m_1165_, 1);
lean_inc_ref(v_buckets_1168_);
lean_dec_ref(v_m_1165_);
v___x_1169_ = lean_box(0);
v___x_1170_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1171_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1171_, 0, v_p_1166_);
lean_closure_set(v___f_1171_, 1, v___x_1169_);
lean_closure_set(v___f_1171_, 2, v___x_1170_);
v___f_1172_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1172_, 0, v___x_1167_);
lean_closure_set(v___f_1172_, 1, v___f_1171_);
v_sz_1173_ = lean_array_size(v_buckets_1168_);
v___x_1174_ = ((size_t)0ULL);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1167_, v_buckets_1168_, v___f_1172_, v_sz_1173_, v___x_1174_, v___x_1170_);
v_fst_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_fst_1176_);
lean_dec(v___x_1175_);
if (lean_obj_tag(v_fst_1176_) == 0)
{
uint8_t v___x_1177_; 
v___x_1177_ = 1;
return v___x_1177_;
}
else
{
lean_object* v_val_1178_; uint8_t v___x_1179_; 
v_val_1178_ = lean_ctor_get(v_fst_1176_, 0);
lean_inc(v_val_1178_);
lean_dec_ref_known(v_fst_1176_, 1);
v___x_1179_ = lean_unbox(v_val_1178_);
lean_dec(v_val_1178_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___boxed(lean_object* v_00_u03b1_1180_, lean_object* v_m_1181_, lean_object* v_p_1182_){
_start:
{
uint8_t v_res_1183_; lean_object* v_r_1184_; 
v_res_1183_ = l_Std_HashSet_Raw_all(v_00_u03b1_1180_, v_m_1181_, v_p_1182_);
v_r_1184_ = lean_box(v_res_1183_);
return v_r_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0(lean_object* v_p_1185_, lean_object* v___x_1186_, lean_object* v___x_1187_, lean_object* v_a_1188_, lean_object* v_b_1189_, lean_object* v_acc_1190_){
_start:
{
lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1191_ = lean_apply_1(v_p_1185_, v_a_1188_);
v___x_1192_ = lean_unbox(v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
v___x_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1186_);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v___x_1186_);
v___x_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1191_);
v___x_1195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v___x_1187_);
v___x_1196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1196_, 0, v___x_1195_);
return v___x_1196_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1197_, lean_object* v___x_1198_, lean_object* v___x_1199_, lean_object* v_a_1200_, lean_object* v_b_1201_, lean_object* v_acc_1202_){
_start:
{
lean_object* v_res_1203_; 
v_res_1203_ = l_Std_HashSet_Raw_any___redArg___lam__0(v_p_1197_, v___x_1198_, v___x_1199_, v_a_1200_, v_b_1201_, v_acc_1202_);
lean_dec_ref(v_acc_1202_);
return v_res_1203_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any___redArg(lean_object* v_m_1204_, lean_object* v_p_1205_){
_start:
{
lean_object* v___x_1206_; lean_object* v_buckets_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___f_1210_; lean_object* v___f_1211_; size_t v_sz_1212_; size_t v___x_1213_; lean_object* v___x_1214_; lean_object* v_fst_1215_; 
v___x_1206_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1207_ = lean_ctor_get(v_m_1204_, 1);
lean_inc_ref(v_buckets_1207_);
lean_dec_ref(v_m_1204_);
v___x_1208_ = lean_box(0);
v___x_1209_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1210_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1210_, 0, v_p_1205_);
lean_closure_set(v___f_1210_, 1, v___x_1209_);
lean_closure_set(v___f_1210_, 2, v___x_1208_);
v___f_1211_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1211_, 0, v___x_1206_);
lean_closure_set(v___f_1211_, 1, v___f_1210_);
v_sz_1212_ = lean_array_size(v_buckets_1207_);
v___x_1213_ = ((size_t)0ULL);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1206_, v_buckets_1207_, v___f_1211_, v_sz_1212_, v___x_1213_, v___x_1209_);
v_fst_1215_ = lean_ctor_get(v___x_1214_, 0);
lean_inc(v_fst_1215_);
lean_dec(v___x_1214_);
if (lean_obj_tag(v_fst_1215_) == 0)
{
uint8_t v___x_1216_; 
v___x_1216_ = 0;
return v___x_1216_;
}
else
{
lean_object* v_val_1217_; uint8_t v___x_1218_; 
v_val_1217_ = lean_ctor_get(v_fst_1215_, 0);
lean_inc(v_val_1217_);
lean_dec_ref_known(v_fst_1215_, 1);
v___x_1218_ = lean_unbox(v_val_1217_);
lean_dec(v_val_1217_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___boxed(lean_object* v_m_1219_, lean_object* v_p_1220_){
_start:
{
uint8_t v_res_1221_; lean_object* v_r_1222_; 
v_res_1221_ = l_Std_HashSet_Raw_any___redArg(v_m_1219_, v_p_1220_);
v_r_1222_ = lean_box(v_res_1221_);
return v_r_1222_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any(lean_object* v_00_u03b1_1223_, lean_object* v_m_1224_, lean_object* v_p_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v_buckets_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___f_1230_; lean_object* v___f_1231_; size_t v_sz_1232_; size_t v___x_1233_; lean_object* v___x_1234_; lean_object* v_fst_1235_; 
v___x_1226_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1227_ = lean_ctor_get(v_m_1224_, 1);
lean_inc_ref(v_buckets_1227_);
lean_dec_ref(v_m_1224_);
v___x_1228_ = lean_box(0);
v___x_1229_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1230_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1230_, 0, v_p_1225_);
lean_closure_set(v___f_1230_, 1, v___x_1229_);
lean_closure_set(v___f_1230_, 2, v___x_1228_);
v___f_1231_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1231_, 0, v___x_1226_);
lean_closure_set(v___f_1231_, 1, v___f_1230_);
v_sz_1232_ = lean_array_size(v_buckets_1227_);
v___x_1233_ = ((size_t)0ULL);
v___x_1234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1226_, v_buckets_1227_, v___f_1231_, v_sz_1232_, v___x_1233_, v___x_1229_);
v_fst_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_fst_1235_);
lean_dec(v___x_1234_);
if (lean_obj_tag(v_fst_1235_) == 0)
{
uint8_t v___x_1236_; 
v___x_1236_ = 0;
return v___x_1236_;
}
else
{
lean_object* v_val_1237_; uint8_t v___x_1238_; 
v_val_1237_ = lean_ctor_get(v_fst_1235_, 0);
lean_inc(v_val_1237_);
lean_dec_ref_known(v_fst_1235_, 1);
v___x_1238_ = lean_unbox(v_val_1237_);
lean_dec(v_val_1237_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___boxed(lean_object* v_00_u03b1_1239_, lean_object* v_m_1240_, lean_object* v_p_1241_){
_start:
{
uint8_t v_res_1242_; lean_object* v_r_1243_; 
v_res_1242_ = l_Std_HashSet_Raw_any(v_00_u03b1_1239_, v_m_1240_, v_p_1241_);
v_r_1243_ = lean_box(v_res_1242_);
return v_r_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany___redArg(lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_inst_1246_, lean_object* v_m_1247_, lean_object* v_l_1248_){
_start:
{
lean_object* v_buckets_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; uint8_t v___x_1252_; 
v_buckets_1249_ = lean_ctor_get(v_m_1247_, 1);
v___x_1250_ = lean_unsigned_to_nat(0u);
v___x_1251_ = lean_array_get_size(v_buckets_1249_);
v___x_1252_ = lean_nat_dec_lt(v___x_1250_, v___x_1251_);
if (v___x_1252_ == 0)
{
lean_dec(v_l_1248_);
lean_dec(v_inst_1246_);
lean_dec_ref(v_inst_1245_);
lean_dec_ref(v_inst_1244_);
return v_m_1247_;
}
else
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1246_, v_inst_1244_, v_inst_1245_, v_m_1247_, v_l_1248_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany(lean_object* v_00_u03b1_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_00_u03c1_1257_, lean_object* v_inst_1258_, lean_object* v_m_1259_, lean_object* v_l_1260_){
_start:
{
lean_object* v_buckets_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; uint8_t v___x_1264_; 
v_buckets_1261_ = lean_ctor_get(v_m_1259_, 1);
v___x_1262_ = lean_unsigned_to_nat(0u);
v___x_1263_ = lean_array_get_size(v_buckets_1261_);
v___x_1264_ = lean_nat_dec_lt(v___x_1262_, v___x_1263_);
if (v___x_1264_ == 0)
{
lean_dec(v_l_1260_);
lean_dec(v_inst_1258_);
lean_dec_ref(v_inst_1256_);
lean_dec_ref(v_inst_1255_);
return v_m_1259_;
}
else
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1258_, v_inst_1255_, v_inst_1256_, v_m_1259_, v_l_1260_);
return v___x_1265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray___redArg(lean_object* v_inst_1270_, lean_object* v_inst_1271_, lean_object* v_l_1272_){
_start:
{
lean_object* v___x_1273_; uint8_t v___x_1274_; 
v___x_1273_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_1274_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1274_ == 0)
{
lean_dec_ref(v_l_1272_);
lean_dec_ref(v_inst_1271_);
lean_dec_ref(v_inst_1270_);
return v___x_1273_;
}
else
{
lean_object* v___f_1275_; lean_object* v___x_1276_; 
v___f_1275_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1275_, v_inst_1270_, v_inst_1271_, v___x_1273_, v_l_1272_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray(lean_object* v_00_u03b1_1277_, lean_object* v_inst_1278_, lean_object* v_inst_1279_, lean_object* v_l_1280_){
_start:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_1282_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1282_ == 0)
{
lean_dec_ref(v_l_1280_);
lean_dec_ref(v_inst_1279_);
lean_dec_ref(v_inst_1278_);
return v___x_1281_;
}
else
{
lean_object* v___f_1283_; lean_object* v___x_1284_; 
v___f_1283_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1283_, v_inst_1278_, v_inst_1279_, v___x_1281_, v_l_1280_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg(lean_object* v_m_1285_){
_start:
{
lean_object* v___x_1286_; 
v___x_1286_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_1287_){
_start:
{
lean_object* v_res_1288_; 
v_res_1288_ = l_Std_HashSet_Raw_Internal_numBuckets___redArg(v_m_1287_);
lean_dec_ref(v_m_1287_);
return v_res_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets(lean_object* v_00_u03b1_1289_, lean_object* v_m_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1290_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_m_1293_){
_start:
{
lean_object* v_res_1294_; 
v_res_1294_ = l_Std_HashSet_Raw_Internal_numBuckets(v_00_u03b1_1292_, v_m_1293_);
lean_dec_ref(v_m_1293_);
return v_res_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2(lean_object* v_inst_1298_, lean_object* v___f_1299_, lean_object* v_m_1300_, lean_object* v_prec_1301_){
_start:
{
lean_object* v___x_1302_; lean_object* v_buckets_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1323_; 
v___x_1302_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1303_ = lean_ctor_get(v_m_1300_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_m_1300_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v_m_1300_, 0);
lean_dec(v_unused_1324_);
v___x_1305_ = v_m_1300_;
v_isShared_1306_ = v_isSharedCheck_1323_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_buckets_1303_);
lean_dec(v_m_1300_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1323_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1307_; lean_object* v___y_1309_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1307_ = ((lean_object*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1));
v___x_1315_ = lean_box(0);
v___x_1316_ = lean_array_get_size(v_buckets_1303_);
v___x_1317_ = lean_unsigned_to_nat(0u);
v___x_1318_ = lean_nat_dec_lt(v___x_1317_, v___x_1316_);
if (v___x_1318_ == 0)
{
lean_dec_ref(v_buckets_1303_);
lean_dec_ref(v___f_1299_);
v___y_1309_ = v___x_1315_;
goto v___jp_1308_;
}
else
{
lean_object* v___f_1319_; size_t v___x_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v___f_1319_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1319_, 0, v___x_1302_);
lean_closure_set(v___f_1319_, 1, v___f_1299_);
v___x_1320_ = lean_usize_of_nat(v___x_1316_);
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1302_, v___f_1319_, v_buckets_1303_, v___x_1320_, v___x_1321_, v___x_1315_);
v___y_1309_ = v___x_1322_;
goto v___jp_1308_;
}
v___jp_1308_:
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
v___x_1310_ = l_List_repr___redArg(v_inst_1298_, v___y_1309_);
if (v_isShared_1306_ == 0)
{
lean_ctor_set_tag(v___x_1305_, 5);
lean_ctor_set(v___x_1305_, 1, v___x_1310_);
lean_ctor_set(v___x_1305_, 0, v___x_1307_);
v___x_1312_ = v___x_1305_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1307_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Repr_addAppParen(v___x_1312_, v_prec_1301_);
return v___x_1313_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1325_, lean_object* v___f_1326_, lean_object* v_m_1327_, lean_object* v_prec_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2(v_inst_1325_, v___f_1326_, v_m_1327_, v_prec_1328_);
lean_dec(v_prec_1328_);
return v_res_1329_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg(lean_object* v_inst_1330_){
_start:
{
lean_object* v___f_1331_; lean_object* v___f_1332_; 
v___f_1331_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___f_1332_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1332_, 0, v_inst_1330_);
lean_closure_set(v___f_1332_, 1, v___f_1331_);
return v___f_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr(lean_object* v_00_u03b1_1333_, lean_object* v_inst_1334_){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Std_HashSet_Raw_instRepr___redArg(v_inst_1334_);
return v___x_1335_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashSet_Raw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
