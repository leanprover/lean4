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
static lean_once_cell_t l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0;
static lean_once_cell_t l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_HashSet_Raw_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_HashSet_Raw_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instInhabited___closed__0;
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___redArg();
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_27_ = lean_box(0);
v___x_28_ = lean_unsigned_to_nat(16u);
v___x_29_ = lean_mk_array(v___x_28_, v___x_27_);
return v___x_29_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_30_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0);
v___x_31_ = lean_unsigned_to_nat(0u);
v___x_32_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v___x_30_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_HashSet_Raw_instEmptyCollection___redArg();
return v_res_36_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Std_HashSet_Raw_instEmptyCollection___redArg();
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection(lean_object* v_00_u03b1_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__0, &l_Std_HashSet_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_HashSet_Raw_instInhabited___redArg();
return v_res_43_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_HashSet_Raw_instInhabited___redArg();
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited(lean_object* v_00_u03b1_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Std_HashSet_Raw_instInhabited___closed__0, &l_Std_HashSet_Raw_instInhabited___closed__0_once, _init_l_Std_HashSet_Raw_instInhabited___closed__0);
return v___x_46_;
}
}
static lean_object* _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5));
v___x_88_ = l_String_toRawSubstring_x27(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(lean_object* v_x_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__4));
lean_inc(v_x_110_);
v___x_114_ = l_Lean_Syntax_isOfKind(v_x_110_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
lean_dec(v_x_110_);
v___x_115_ = lean_box(1);
v___x_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_a_112_);
return v___x_116_;
}
else
{
lean_object* v_quotContext_117_; lean_object* v_currMacroScope_118_; lean_object* v_ref_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_quotContext_117_ = lean_ctor_get(v_a_111_, 1);
v_currMacroScope_118_ = lean_ctor_get(v_a_111_, 2);
v_ref_119_ = lean_ctor_get(v_a_111_, 5);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = l_Lean_Syntax_getArg(v_x_110_, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(2u);
v___x_123_ = l_Lean_Syntax_getArg(v_x_110_, v___x_122_);
lean_dec(v_x_110_);
v___x_124_ = 0;
v___x_125_ = l_Lean_SourceInfo_fromRef(v_ref_119_, v___x_124_);
v___x_126_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4));
v___x_127_ = lean_obj_once(&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6, &l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6);
v___x_128_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_118_);
lean_inc(v_quotContext_117_);
v___x_129_ = l_Lean_addMacroScope(v_quotContext_117_, v___x_128_, v_currMacroScope_118_);
v___x_130_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12));
lean_inc_n(v___x_125_, 2);
v___x_131_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_131_, 0, v___x_125_);
lean_ctor_set(v___x_131_, 1, v___x_127_);
lean_ctor_set(v___x_131_, 2, v___x_129_);
lean_ctor_set(v___x_131_, 3, v___x_130_);
v___x_132_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14));
v___x_133_ = l_Lean_Syntax_node2(v___x_125_, v___x_132_, v___x_121_, v___x_123_);
v___x_134_ = l_Lean_Syntax_node2(v___x_125_, v___x_126_, v___x_131_, v___x_133_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_a_112_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___boxed(lean_object* v_x_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(v_x_136_, v_a_137_, v_a_138_);
lean_dec_ref(v_a_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4));
lean_inc(v_x_143_);
v___x_147_ = l_Lean_Syntax_isOfKind(v_x_143_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_x_143_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_a_145_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = l_Lean_Syntax_getArg(v_x_143_, v___x_150_);
v___x_152_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1));
lean_inc(v___x_151_);
v___x_153_ = l_Lean_Syntax_isOfKind(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v___x_151_);
lean_dec(v_x_143_);
v___x_154_ = lean_box(0);
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_145_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = l_Lean_Syntax_getArg(v_x_143_, v___x_156_);
lean_dec(v_x_143_);
v___x_158_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_157_);
v___x_159_ = l_Lean_Syntax_matchesNull(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v___x_157_);
lean_dec(v___x_151_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v_a_145_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_ref_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_162_ = l_Lean_Syntax_getArg(v___x_157_, v___x_150_);
v___x_163_ = l_Lean_Syntax_getArg(v___x_157_, v___x_156_);
lean_dec(v___x_157_);
v_ref_164_ = l_Lean_replaceRef(v___x_151_, v_a_144_);
lean_dec(v___x_151_);
v___x_165_ = 0;
v___x_166_ = l_Lean_SourceInfo_fromRef(v_ref_164_, v___x_165_);
lean_dec(v_ref_164_);
v___x_167_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__4));
v___x_168_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__7));
lean_inc(v___x_166_);
v___x_169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_166_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = l_Lean_Syntax_node3(v___x_166_, v___x_167_, v___x_162_, v___x_169_, v___x_163_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_a_145_);
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___boxed(lean_object* v_x_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(v_x_172_, v_a_173_, v_a_174_);
lean_dec(v_a_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert___redArg(lean_object* v_inst_176_, lean_object* v_inst_177_, lean_object* v_m_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_buckets_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_buckets_180_ = lean_ctor_get(v_m_178_, 1);
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = lean_array_get_size(v_buckets_180_);
v___x_183_ = lean_nat_dec_lt(v___x_181_, v___x_182_);
if (v___x_183_ == 0)
{
lean_dec(v_a_179_);
lean_dec_ref(v_inst_177_);
lean_dec_ref(v_inst_176_);
return v_m_178_;
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_184_ = lean_box(0);
v___x_185_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_176_, v_inst_177_, v_m_178_, v_a_179_, v___x_184_);
return v___x_185_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert(lean_object* v_00_u03b1_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_m_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_buckets_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v_buckets_191_ = lean_ctor_get(v_m_189_, 1);
v___x_192_ = lean_unsigned_to_nat(0u);
v___x_193_ = lean_array_get_size(v_buckets_191_);
v___x_194_ = lean_nat_dec_lt(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_dec(v_a_190_);
lean_dec_ref(v_inst_188_);
lean_dec_ref(v_inst_187_);
return v_m_189_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_box(0);
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_187_, v_inst_188_, v_m_189_, v_a_190_, v___x_195_);
return v___x_196_;
}
}
}
static lean_object* _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0);
v___x_198_ = lean_array_get_size(v___x_197_);
return v___x_198_;
}
}
static uint8_t _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_199_ = lean_obj_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_nat_dec_lt(v___x_200_, v___x_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_a_204_){
_start:
{
lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_205_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
v___x_206_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_206_ == 0)
{
lean_dec(v_a_204_);
lean_dec_ref(v_inst_203_);
lean_dec_ref(v_inst_202_);
return v___x_205_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_box(0);
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_202_, v_inst_203_, v___x_205_, v_a_204_, v___x_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg(lean_object* v_inst_209_, lean_object* v_inst_210_){
_start:
{
lean_object* v___f_211_; 
v___f_211_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_211_, 0, v_inst_209_);
lean_closure_set(v___f_211_, 1, v_inst_210_);
return v___f_211_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable(lean_object* v_00_u03b1_212_, lean_object* v_inst_213_, lean_object* v_inst_214_){
_start:
{
lean_object* v___f_215_; 
v___f_215_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_215_, 0, v_inst_213_);
lean_closure_set(v___f_215_, 1, v_inst_214_);
return v___f_215_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_a_218_, lean_object* v_s_219_){
_start:
{
lean_object* v_buckets_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_buckets_220_ = lean_ctor_get(v_s_219_, 1);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_array_get_size(v_buckets_220_);
v___x_223_ = lean_nat_dec_lt(v___x_221_, v___x_222_);
if (v___x_223_ == 0)
{
lean_dec(v_a_218_);
lean_dec_ref(v_inst_217_);
lean_dec_ref(v_inst_216_);
return v_s_219_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_box(0);
v___x_225_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_216_, v_inst_217_, v_s_219_, v_a_218_, v___x_224_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg(lean_object* v_inst_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v___f_228_; 
v___f_228_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_228_, 0, v_inst_226_);
lean_closure_set(v___f_228_, 1, v_inst_227_);
return v___f_228_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable(lean_object* v_00_u03b1_229_, lean_object* v_inst_230_, lean_object* v_inst_231_){
_start:
{
lean_object* v___f_232_; 
v___f_232_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_232_, 0, v_inst_230_);
lean_closure_set(v___f_232_, 1, v_inst_231_);
return v___f_232_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert___redArg(lean_object* v_inst_233_, lean_object* v_inst_234_, lean_object* v_m_235_, lean_object* v_a_236_){
_start:
{
lean_object* v_size_237_; lean_object* v_buckets_238_; lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_size_237_ = lean_ctor_get(v_m_235_, 0);
v_buckets_238_ = lean_ctor_get(v_m_235_, 1);
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_array_get_size(v_buckets_238_);
v___x_241_ = lean_nat_dec_lt(v___x_239_, v___x_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_a_236_);
lean_dec_ref(v_inst_234_);
lean_dec_ref(v_inst_233_);
v___x_242_ = lean_box(v___x_241_);
v___x_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v_m_235_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; uint64_t v___x_245_; uint64_t v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; uint64_t v_fold_249_; uint64_t v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; size_t v___x_253_; size_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; lean_object* v_bkt_258_; uint8_t v___x_259_; 
lean_inc_ref(v_inst_234_);
lean_inc_n(v_a_236_, 2);
v___x_244_ = lean_apply_1(v_inst_234_, v_a_236_);
v___x_245_ = 32ULL;
v___x_246_ = lean_unbox_uint64(v___x_244_);
v___x_247_ = lean_uint64_shift_right(v___x_246_, v___x_245_);
v___x_248_ = lean_unbox_uint64(v___x_244_);
lean_dec_ref(v___x_244_);
v_fold_249_ = lean_uint64_xor(v___x_248_, v___x_247_);
v___x_250_ = 16ULL;
v___x_251_ = lean_uint64_shift_right(v_fold_249_, v___x_250_);
v___x_252_ = lean_uint64_xor(v_fold_249_, v___x_251_);
v___x_253_ = lean_uint64_to_usize(v___x_252_);
v___x_254_ = lean_usize_of_nat(v___x_240_);
v___x_255_ = ((size_t)1ULL);
v___x_256_ = lean_usize_sub(v___x_254_, v___x_255_);
v___x_257_ = lean_usize_land(v___x_253_, v___x_256_);
v_bkt_258_ = lean_array_uget_borrowed(v_buckets_238_, v___x_257_);
lean_inc(v_bkt_258_);
v___x_259_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_233_, v_a_236_, v_bkt_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_285_; 
lean_inc_ref(v_buckets_238_);
lean_inc(v_size_237_);
v_isSharedCheck_285_ = !lean_is_exclusive(v_m_235_);
if (v_isSharedCheck_285_ == 0)
{
lean_object* v_unused_286_; lean_object* v_unused_287_; 
v_unused_286_ = lean_ctor_get(v_m_235_, 1);
lean_dec(v_unused_286_);
v_unused_287_ = lean_ctor_get(v_m_235_, 0);
lean_dec(v_unused_287_);
v___x_261_ = v_m_235_;
v_isShared_262_ = v_isSharedCheck_285_;
goto v_resetjp_260_;
}
else
{
lean_dec(v_m_235_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_285_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v_size_x27_265_; lean_object* v___x_266_; lean_object* v_buckets_x27_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v___x_263_ = lean_box(0);
v___x_264_ = lean_unsigned_to_nat(1u);
v_size_x27_265_ = lean_nat_add(v_size_237_, v___x_264_);
lean_dec(v_size_237_);
lean_inc(v_bkt_258_);
v___x_266_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_266_, 0, v_a_236_);
lean_ctor_set(v___x_266_, 1, v___x_263_);
lean_ctor_set(v___x_266_, 2, v_bkt_258_);
v_buckets_x27_267_ = lean_array_uset(v_buckets_238_, v___x_257_, v___x_266_);
v___x_268_ = lean_unsigned_to_nat(4u);
v___x_269_ = lean_nat_mul(v_size_x27_265_, v___x_268_);
v___x_270_ = lean_unsigned_to_nat(3u);
v___x_271_ = lean_nat_div(v___x_269_, v___x_270_);
lean_dec(v___x_269_);
v___x_272_ = lean_array_get_size(v_buckets_x27_267_);
v___x_273_ = lean_nat_dec_le(v___x_271_, v___x_272_);
lean_dec(v___x_271_);
if (v___x_273_ == 0)
{
lean_object* v_val_274_; lean_object* v___x_276_; 
v_val_274_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_234_, v_buckets_x27_267_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v_val_274_);
lean_ctor_set(v___x_261_, 0, v_size_x27_265_);
v___x_276_ = v___x_261_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v_size_x27_265_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_val_274_);
v___x_276_ = v_reuseFailAlloc_279_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_box(v___x_259_);
v___x_278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
lean_ctor_set(v___x_278_, 1, v___x_276_);
return v___x_278_;
}
}
else
{
lean_object* v___x_281_; 
lean_dec_ref(v_inst_234_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v_buckets_x27_267_);
lean_ctor_set(v___x_261_, 0, v_size_x27_265_);
v___x_281_ = v___x_261_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v_size_x27_265_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v_buckets_x27_267_);
v___x_281_ = v_reuseFailAlloc_284_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_box(v___x_259_);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v___x_281_);
return v___x_283_;
}
}
}
}
else
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec(v_a_236_);
lean_dec_ref(v_inst_234_);
v___x_288_ = lean_box(v___x_259_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v_m_235_);
return v___x_289_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert(lean_object* v_00_u03b1_290_, lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_m_293_, lean_object* v_a_294_){
_start:
{
lean_object* v_size_295_; lean_object* v_buckets_296_; lean_object* v___x_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_size_295_ = lean_ctor_get(v_m_293_, 0);
v_buckets_296_ = lean_ctor_get(v_m_293_, 1);
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_array_get_size(v_buckets_296_);
v___x_299_ = lean_nat_dec_lt(v___x_297_, v___x_298_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_a_294_);
lean_dec_ref(v_inst_292_);
lean_dec_ref(v_inst_291_);
v___x_300_ = lean_box(v___x_299_);
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v_m_293_);
return v___x_301_;
}
else
{
lean_object* v___x_302_; uint64_t v___x_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v_fold_307_; uint64_t v___x_308_; uint64_t v___x_309_; uint64_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; lean_object* v_bkt_316_; uint8_t v___x_317_; 
lean_inc_ref(v_inst_292_);
lean_inc_n(v_a_294_, 2);
v___x_302_ = lean_apply_1(v_inst_292_, v_a_294_);
v___x_303_ = 32ULL;
v___x_304_ = lean_unbox_uint64(v___x_302_);
v___x_305_ = lean_uint64_shift_right(v___x_304_, v___x_303_);
v___x_306_ = lean_unbox_uint64(v___x_302_);
lean_dec_ref(v___x_302_);
v_fold_307_ = lean_uint64_xor(v___x_306_, v___x_305_);
v___x_308_ = 16ULL;
v___x_309_ = lean_uint64_shift_right(v_fold_307_, v___x_308_);
v___x_310_ = lean_uint64_xor(v_fold_307_, v___x_309_);
v___x_311_ = lean_uint64_to_usize(v___x_310_);
v___x_312_ = lean_usize_of_nat(v___x_298_);
v___x_313_ = ((size_t)1ULL);
v___x_314_ = lean_usize_sub(v___x_312_, v___x_313_);
v___x_315_ = lean_usize_land(v___x_311_, v___x_314_);
v_bkt_316_ = lean_array_uget_borrowed(v_buckets_296_, v___x_315_);
lean_inc(v_bkt_316_);
v___x_317_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_291_, v_a_294_, v_bkt_316_);
if (v___x_317_ == 0)
{
lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_343_; 
lean_inc_ref(v_buckets_296_);
lean_inc(v_size_295_);
v_isSharedCheck_343_ = !lean_is_exclusive(v_m_293_);
if (v_isSharedCheck_343_ == 0)
{
lean_object* v_unused_344_; lean_object* v_unused_345_; 
v_unused_344_ = lean_ctor_get(v_m_293_, 1);
lean_dec(v_unused_344_);
v_unused_345_ = lean_ctor_get(v_m_293_, 0);
lean_dec(v_unused_345_);
v___x_319_ = v_m_293_;
v_isShared_320_ = v_isSharedCheck_343_;
goto v_resetjp_318_;
}
else
{
lean_dec(v_m_293_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_343_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v_size_x27_323_; lean_object* v___x_324_; lean_object* v_buckets_x27_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_321_ = lean_box(0);
v___x_322_ = lean_unsigned_to_nat(1u);
v_size_x27_323_ = lean_nat_add(v_size_295_, v___x_322_);
lean_dec(v_size_295_);
lean_inc(v_bkt_316_);
v___x_324_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_324_, 0, v_a_294_);
lean_ctor_set(v___x_324_, 1, v___x_321_);
lean_ctor_set(v___x_324_, 2, v_bkt_316_);
v_buckets_x27_325_ = lean_array_uset(v_buckets_296_, v___x_315_, v___x_324_);
v___x_326_ = lean_unsigned_to_nat(4u);
v___x_327_ = lean_nat_mul(v_size_x27_323_, v___x_326_);
v___x_328_ = lean_unsigned_to_nat(3u);
v___x_329_ = lean_nat_div(v___x_327_, v___x_328_);
lean_dec(v___x_327_);
v___x_330_ = lean_array_get_size(v_buckets_x27_325_);
v___x_331_ = lean_nat_dec_le(v___x_329_, v___x_330_);
lean_dec(v___x_329_);
if (v___x_331_ == 0)
{
lean_object* v_val_332_; lean_object* v___x_334_; 
v_val_332_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_292_, v_buckets_x27_325_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v_val_332_);
lean_ctor_set(v___x_319_, 0, v_size_x27_323_);
v___x_334_ = v___x_319_;
goto v_reusejp_333_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v_size_x27_323_);
lean_ctor_set(v_reuseFailAlloc_337_, 1, v_val_332_);
v___x_334_ = v_reuseFailAlloc_337_;
goto v_reusejp_333_;
}
v_reusejp_333_:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_box(v___x_317_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v___x_334_);
return v___x_336_;
}
}
else
{
lean_object* v___x_339_; 
lean_dec_ref(v_inst_292_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v_buckets_x27_325_);
lean_ctor_set(v___x_319_, 0, v_size_x27_323_);
v___x_339_ = v___x_319_;
goto v_reusejp_338_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_size_x27_323_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_buckets_x27_325_);
v___x_339_ = v_reuseFailAlloc_342_;
goto v_reusejp_338_;
}
v_reusejp_338_:
{
lean_object* v___x_340_; lean_object* v___x_341_; 
v___x_340_ = lean_box(v___x_317_);
v___x_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_340_);
lean_ctor_set(v___x_341_, 1, v___x_339_);
return v___x_341_;
}
}
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
lean_dec(v_a_294_);
lean_dec_ref(v_inst_292_);
v___x_346_ = lean_box(v___x_317_);
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_346_);
lean_ctor_set(v___x_347_, 1, v_m_293_);
return v___x_347_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains___redArg(lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_m_350_, lean_object* v_a_351_){
_start:
{
lean_object* v_buckets_352_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_buckets_352_ = lean_ctor_get(v_m_350_, 1);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_array_get_size(v_buckets_352_);
v___x_355_ = lean_nat_dec_lt(v___x_353_, v___x_354_);
if (v___x_355_ == 0)
{
lean_dec(v_a_351_);
lean_dec_ref(v_inst_349_);
lean_dec_ref(v_inst_348_);
return v___x_355_;
}
else
{
uint8_t v___x_356_; 
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_348_, v_inst_349_, v_m_350_, v_a_351_);
return v___x_356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___redArg___boxed(lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_m_359_, lean_object* v_a_360_){
_start:
{
uint8_t v_res_361_; lean_object* v_r_362_; 
v_res_361_ = l_Std_HashSet_Raw_contains___redArg(v_inst_357_, v_inst_358_, v_m_359_, v_a_360_);
lean_dec_ref(v_m_359_);
v_r_362_ = lean_box(v_res_361_);
return v_r_362_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains(lean_object* v_00_u03b1_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_m_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_buckets_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_buckets_368_ = lean_ctor_get(v_m_366_, 1);
v___x_369_ = lean_unsigned_to_nat(0u);
v___x_370_ = lean_array_get_size(v_buckets_368_);
v___x_371_ = lean_nat_dec_lt(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_dec(v_a_367_);
lean_dec_ref(v_inst_365_);
lean_dec_ref(v_inst_364_);
return v___x_371_;
}
else
{
uint8_t v___x_372_; 
v___x_372_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_364_, v_inst_365_, v_m_366_, v_a_367_);
return v___x_372_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___boxed(lean_object* v_00_u03b1_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_m_376_, lean_object* v_a_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_Std_HashSet_Raw_contains(v_00_u03b1_373_, v_inst_374_, v_inst_375_, v_m_376_, v_a_377_);
lean_dec_ref(v_m_376_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___redArg(){
_start:
{
lean_object* v___x_381_; 
v___x_381_ = lean_box(0);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___redArg___boxed(lean_object* v___dummy_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___redArg();
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_384_, lean_object* v_inst_385_, lean_object* v_inst_386_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = lean_box(0);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_388_, lean_object* v_inst_389_, lean_object* v_inst_390_){
_start:
{
lean_object* v_res_391_; 
v_res_391_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_388_, v_inst_389_, v_inst_390_);
lean_dec_ref(v_inst_390_);
lean_dec_ref(v_inst_389_);
return v_res_391_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem___redArg(lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_m_394_, lean_object* v_a_395_){
_start:
{
uint8_t v___x_396_; 
v___x_396_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_392_, v_inst_393_, v_m_394_, v_a_395_);
return v___x_396_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Std_HashSet_Raw_instDecidableMem___redArg(v_inst_397_, v_inst_398_, v_m_399_, v_a_400_);
lean_dec_ref(v_m_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem(lean_object* v_00_u03b1_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_m_406_, lean_object* v_a_407_){
_start:
{
uint8_t v___x_408_; 
v___x_408_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_404_, v_inst_405_, v_m_406_, v_a_407_);
return v___x_408_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_m_412_, lean_object* v_a_413_){
_start:
{
uint8_t v_res_414_; lean_object* v_r_415_; 
v_res_414_ = l_Std_HashSet_Raw_instDecidableMem(v_00_u03b1_409_, v_inst_410_, v_inst_411_, v_m_412_, v_a_413_);
lean_dec_ref(v_m_412_);
v_r_415_ = lean_box(v_res_414_);
return v_r_415_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase___redArg(lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_m_418_, lean_object* v_a_419_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase(lean_object* v_00_u03b1_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_m_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_buckets_430_; lean_object* v___x_431_; lean_object* v___x_432_; uint8_t v___x_433_; 
v_buckets_430_ = lean_ctor_get(v_m_428_, 1);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_array_get_size(v_buckets_430_);
v___x_433_ = lean_nat_dec_lt(v___x_431_, v___x_432_);
if (v___x_433_ == 0)
{
lean_dec(v_a_429_);
lean_dec_ref(v_inst_427_);
lean_dec_ref(v_inst_426_);
return v_m_428_;
}
else
{
lean_object* v___x_434_; 
v___x_434_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_426_, v_inst_427_, v_m_428_, v_a_429_);
return v___x_434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg(lean_object* v_m_435_){
_start:
{
lean_object* v_size_436_; 
v_size_436_ = lean_ctor_get(v_m_435_, 0);
lean_inc(v_size_436_);
return v_size_436_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg___boxed(lean_object* v_m_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_HashSet_Raw_size___redArg(v_m_437_);
lean_dec_ref(v_m_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size(lean_object* v_00_u03b1_439_, lean_object* v_m_440_){
_start:
{
lean_object* v_size_441_; 
v_size_441_ = lean_ctor_get(v_m_440_, 0);
lean_inc(v_size_441_);
return v_size_441_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___boxed(lean_object* v_00_u03b1_442_, lean_object* v_m_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Std_HashSet_Raw_size(v_00_u03b1_442_, v_m_443_);
lean_dec_ref(v_m_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg(lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_m_447_, lean_object* v_a_448_){
_start:
{
lean_object* v_buckets_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_buckets_449_ = lean_ctor_get(v_m_447_, 1);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_array_get_size(v_buckets_449_);
v___x_452_ = lean_nat_dec_lt(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_dec(v_a_448_);
lean_dec_ref(v_inst_446_);
lean_dec_ref(v_inst_445_);
v___x_453_ = lean_box(0);
return v___x_453_;
}
else
{
lean_object* v___x_454_; 
v___x_454_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_445_, v_inst_446_, v_m_447_, v_a_448_);
return v___x_454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg___boxed(lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_m_457_, lean_object* v_a_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_HashSet_Raw_get_x3f___redArg(v_inst_455_, v_inst_456_, v_m_457_, v_a_458_);
lean_dec_ref(v_m_457_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f(lean_object* v_00_u03b1_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_m_463_, lean_object* v_a_464_){
_start:
{
lean_object* v_buckets_465_; lean_object* v___x_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_buckets_465_ = lean_ctor_get(v_m_463_, 1);
v___x_466_ = lean_unsigned_to_nat(0u);
v___x_467_ = lean_array_get_size(v_buckets_465_);
v___x_468_ = lean_nat_dec_lt(v___x_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_object* v___x_469_; 
lean_dec(v_a_464_);
lean_dec_ref(v_inst_462_);
lean_dec_ref(v_inst_461_);
v___x_469_ = lean_box(0);
return v___x_469_;
}
else
{
lean_object* v___x_470_; 
v___x_470_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_461_, v_inst_462_, v_m_463_, v_a_464_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___boxed(lean_object* v_00_u03b1_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_m_474_, lean_object* v_a_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Std_HashSet_Raw_get_x3f(v_00_u03b1_471_, v_inst_472_, v_inst_473_, v_m_474_, v_a_475_);
lean_dec_ref(v_m_474_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg(lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_m_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_477_, v_inst_478_, v_m_479_, v_a_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg___boxed(lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_m_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_HashSet_Raw_get___redArg(v_inst_482_, v_inst_483_, v_m_484_, v_a_485_);
lean_dec_ref(v_m_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get(lean_object* v_00_u03b1_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_m_490_, lean_object* v_a_491_, lean_object* v_h_492_){
_start:
{
lean_object* v___x_493_; 
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_488_, v_inst_489_, v_m_490_, v_a_491_);
return v___x_493_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___boxed(lean_object* v_00_u03b1_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_m_497_, lean_object* v_a_498_, lean_object* v_h_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_HashSet_Raw_get(v_00_u03b1_494_, v_inst_495_, v_inst_496_, v_m_497_, v_a_498_, v_h_499_);
lean_dec_ref(v_m_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg(lean_object* v_inst_501_, lean_object* v_inst_502_, lean_object* v_m_503_, lean_object* v_a_504_, lean_object* v_fallback_505_){
_start:
{
lean_object* v_buckets_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_buckets_506_ = lean_ctor_get(v_m_503_, 1);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_array_get_size(v_buckets_506_);
v___x_509_ = lean_nat_dec_lt(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_dec(v_a_504_);
lean_dec_ref(v_inst_502_);
lean_dec_ref(v_inst_501_);
lean_inc(v_fallback_505_);
return v_fallback_505_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_501_, v_inst_502_, v_m_503_, v_a_504_, v_fallback_505_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg___boxed(lean_object* v_inst_511_, lean_object* v_inst_512_, lean_object* v_m_513_, lean_object* v_a_514_, lean_object* v_fallback_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l_Std_HashSet_Raw_getD___redArg(v_inst_511_, v_inst_512_, v_m_513_, v_a_514_, v_fallback_515_);
lean_dec(v_fallback_515_);
lean_dec_ref(v_m_513_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD(lean_object* v_00_u03b1_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_m_520_, lean_object* v_a_521_, lean_object* v_fallback_522_){
_start:
{
lean_object* v_buckets_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_buckets_523_ = lean_ctor_get(v_m_520_, 1);
v___x_524_ = lean_unsigned_to_nat(0u);
v___x_525_ = lean_array_get_size(v_buckets_523_);
v___x_526_ = lean_nat_dec_lt(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec(v_a_521_);
lean_dec_ref(v_inst_519_);
lean_dec_ref(v_inst_518_);
lean_inc(v_fallback_522_);
return v_fallback_522_;
}
else
{
lean_object* v___x_527_; 
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_518_, v_inst_519_, v_m_520_, v_a_521_, v_fallback_522_);
return v___x_527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___boxed(lean_object* v_00_u03b1_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_m_531_, lean_object* v_a_532_, lean_object* v_fallback_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_HashSet_Raw_getD(v_00_u03b1_528_, v_inst_529_, v_inst_530_, v_m_531_, v_a_532_, v_fallback_533_);
lean_dec(v_fallback_533_);
lean_dec_ref(v_m_531_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg(lean_object* v_inst_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_m_538_, lean_object* v_a_539_){
_start:
{
lean_object* v_buckets_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v_buckets_540_ = lean_ctor_get(v_m_538_, 1);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_array_get_size(v_buckets_540_);
v___x_543_ = lean_nat_dec_lt(v___x_541_, v___x_542_);
if (v___x_543_ == 0)
{
lean_dec(v_a_539_);
lean_dec_ref(v_inst_536_);
lean_dec_ref(v_inst_535_);
lean_inc(v_inst_537_);
return v_inst_537_;
}
else
{
lean_object* v___x_544_; 
v___x_544_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_535_, v_inst_536_, v_inst_537_, v_m_538_, v_a_539_);
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg___boxed(lean_object* v_inst_545_, lean_object* v_inst_546_, lean_object* v_inst_547_, lean_object* v_m_548_, lean_object* v_a_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Std_HashSet_Raw_get_x21___redArg(v_inst_545_, v_inst_546_, v_inst_547_, v_m_548_, v_a_549_);
lean_dec_ref(v_m_548_);
lean_dec(v_inst_547_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21(lean_object* v_00_u03b1_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_m_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_buckets_557_; lean_object* v___x_558_; lean_object* v___x_559_; uint8_t v___x_560_; 
v_buckets_557_ = lean_ctor_get(v_m_555_, 1);
v___x_558_ = lean_unsigned_to_nat(0u);
v___x_559_ = lean_array_get_size(v_buckets_557_);
v___x_560_ = lean_nat_dec_lt(v___x_558_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec(v_a_556_);
lean_dec_ref(v_inst_553_);
lean_dec_ref(v_inst_552_);
lean_inc(v_inst_554_);
return v_inst_554_;
}
else
{
lean_object* v___x_561_; 
v___x_561_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_552_, v_inst_553_, v_inst_554_, v_m_555_, v_a_556_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___boxed(lean_object* v_00_u03b1_562_, lean_object* v_inst_563_, lean_object* v_inst_564_, lean_object* v_inst_565_, lean_object* v_m_566_, lean_object* v_a_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Std_HashSet_Raw_get_x21(v_00_u03b1_562_, v_inst_563_, v_inst_564_, v_inst_565_, v_m_566_, v_a_567_);
lean_dec_ref(v_m_566_);
lean_dec(v_inst_565_);
return v_res_568_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty___redArg(lean_object* v_m_569_){
_start:
{
lean_object* v_size_570_; lean_object* v___x_571_; uint8_t v___x_572_; 
v_size_570_ = lean_ctor_get(v_m_569_, 0);
v___x_571_ = lean_unsigned_to_nat(0u);
v___x_572_ = lean_nat_dec_eq(v_size_570_, v___x_571_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___redArg___boxed(lean_object* v_m_573_){
_start:
{
uint8_t v_res_574_; lean_object* v_r_575_; 
v_res_574_ = l_Std_HashSet_Raw_isEmpty___redArg(v_m_573_);
lean_dec_ref(v_m_573_);
v_r_575_ = lean_box(v_res_574_);
return v_r_575_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty(lean_object* v_00_u03b1_576_, lean_object* v_m_577_){
_start:
{
lean_object* v_size_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v_size_578_ = lean_ctor_get(v_m_577_, 0);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_nat_dec_eq(v_size_578_, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_581_, lean_object* v_m_582_){
_start:
{
uint8_t v_res_583_; lean_object* v_r_584_; 
v_res_583_ = l_Std_HashSet_Raw_isEmpty(v_00_u03b1_581_, v_m_582_);
lean_dec_ref(v_m_582_);
v_r_584_ = lean_box(v_res_583_);
return v_r_584_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__0(lean_object* v_a_585_, lean_object* v_b_586_, lean_object* v_d_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_588_, 0, v_a_585_);
lean_ctor_set(v___x_588_, 1, v_d_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__1(lean_object* v___x_589_, lean_object* v___f_590_, lean_object* v_l_591_, lean_object* v_acc_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_589_, v___f_590_, v_acc_592_, v_l_591_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg(lean_object* v_m_617_){
_start:
{
lean_object* v___x_618_; lean_object* v_buckets_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_618_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_619_ = lean_ctor_get(v_m_617_, 1);
lean_inc_ref(v_buckets_619_);
lean_dec_ref(v_m_617_);
v___x_620_ = lean_box(0);
v___x_621_ = lean_array_get_size(v_buckets_619_);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_nat_dec_lt(v___x_622_, v___x_621_);
if (v___x_623_ == 0)
{
lean_dec_ref(v_buckets_619_);
return v___x_620_;
}
else
{
lean_object* v___f_624_; size_t v___x_625_; size_t v___x_626_; lean_object* v___x_627_; 
v___f_624_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__11));
v___x_625_ = lean_usize_of_nat(v___x_621_);
v___x_626_ = ((size_t)0ULL);
v___x_627_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_618_, v___f_624_, v_buckets_619_, v___x_625_, v___x_626_, v___x_620_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList(lean_object* v_00_u03b1_628_, lean_object* v_m_629_){
_start:
{
lean_object* v___x_630_; lean_object* v_buckets_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_630_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_631_ = lean_ctor_get(v_m_629_, 1);
lean_inc_ref(v_buckets_631_);
lean_dec_ref(v_m_629_);
v___x_632_ = lean_box(0);
v___x_633_ = lean_array_get_size(v_buckets_631_);
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = lean_nat_dec_lt(v___x_634_, v___x_633_);
if (v___x_635_ == 0)
{
lean_dec_ref(v_buckets_631_);
return v___x_632_;
}
else
{
lean_object* v___f_636_; size_t v___x_637_; size_t v___x_638_; lean_object* v___x_639_; 
v___f_636_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__11));
v___x_637_ = lean_usize_of_nat(v___x_633_);
v___x_638_ = ((size_t)0ULL);
v___x_639_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_630_, v___f_636_, v_buckets_631_, v___x_637_, v___x_638_, v___x_632_);
return v___x_639_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList___redArg(lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_l_646_){
_start:
{
lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_647_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
v___x_648_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_648_ == 0)
{
lean_dec(v_l_646_);
lean_dec_ref(v_inst_645_);
lean_dec_ref(v_inst_644_);
return v___x_647_;
}
else
{
lean_object* v___f_649_; lean_object* v___x_650_; 
v___f_649_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_650_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_649_, v_inst_644_, v_inst_645_, v___x_647_, v_l_646_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList(lean_object* v_00_u03b1_651_, lean_object* v_inst_652_, lean_object* v_inst_653_, lean_object* v_l_654_){
_start:
{
lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_655_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
v___x_656_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_656_ == 0)
{
lean_dec(v_l_654_);
lean_dec_ref(v_inst_653_);
lean_dec_ref(v_inst_652_);
return v___x_655_;
}
else
{
lean_object* v___f_657_; lean_object* v___x_658_; 
v___f_657_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_657_, v_inst_652_, v_inst_653_, v___x_655_, v_l_654_);
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__0(lean_object* v_f_659_, lean_object* v_b_660_, lean_object* v_a_661_, lean_object* v_x_662_){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = lean_apply_2(v_f_659_, v_b_660_, v_a_661_);
return v___x_663_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__1(lean_object* v_inst_664_, lean_object* v___f_665_, lean_object* v_acc_666_, lean_object* v_l_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_664_, v___f_665_, v_acc_666_, v_l_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg(lean_object* v_inst_669_, lean_object* v_f_670_, lean_object* v_init_671_, lean_object* v_b_672_){
_start:
{
lean_object* v_toApplicative_673_; lean_object* v_buckets_674_; lean_object* v_toPure_675_; lean_object* v___x_676_; lean_object* v___x_677_; uint8_t v___x_678_; 
v_toApplicative_673_ = lean_ctor_get(v_inst_669_, 0);
v_buckets_674_ = lean_ctor_get(v_b_672_, 1);
lean_inc_ref(v_buckets_674_);
lean_dec_ref(v_b_672_);
v_toPure_675_ = lean_ctor_get(v_toApplicative_673_, 1);
v___x_676_ = lean_unsigned_to_nat(0u);
v___x_677_ = lean_array_get_size(v_buckets_674_);
v___x_678_ = lean_nat_dec_lt(v___x_676_, v___x_677_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_inc(v_toPure_675_);
lean_dec_ref(v_buckets_674_);
lean_dec(v_f_670_);
lean_dec_ref(v_inst_669_);
v___x_679_ = lean_apply_2(v_toPure_675_, lean_box(0), v_init_671_);
return v___x_679_;
}
else
{
lean_object* v___f_680_; lean_object* v___f_681_; size_t v___x_682_; size_t v___x_683_; lean_object* v___x_684_; 
v___f_680_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_680_, 0, v_f_670_);
lean_inc_ref(v_inst_669_);
v___f_681_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_681_, 0, v_inst_669_);
lean_closure_set(v___f_681_, 1, v___f_680_);
v___x_682_ = ((size_t)0ULL);
v___x_683_ = lean_usize_of_nat(v___x_677_);
v___x_684_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_669_, v___f_681_, v_buckets_674_, v___x_682_, v___x_683_, v_init_671_);
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM(lean_object* v_00_u03b1_685_, lean_object* v_m_686_, lean_object* v_inst_687_, lean_object* v_00_u03b2_688_, lean_object* v_f_689_, lean_object* v_init_690_, lean_object* v_b_691_){
_start:
{
lean_object* v_toApplicative_692_; lean_object* v_buckets_693_; lean_object* v_toPure_694_; lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_toApplicative_692_ = lean_ctor_get(v_inst_687_, 0);
v_buckets_693_ = lean_ctor_get(v_b_691_, 1);
lean_inc_ref(v_buckets_693_);
lean_dec_ref(v_b_691_);
v_toPure_694_ = lean_ctor_get(v_toApplicative_692_, 1);
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_array_get_size(v_buckets_693_);
v___x_697_ = lean_nat_dec_lt(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; 
lean_inc(v_toPure_694_);
lean_dec_ref(v_buckets_693_);
lean_dec(v_f_689_);
lean_dec_ref(v_inst_687_);
v___x_698_ = lean_apply_2(v_toPure_694_, lean_box(0), v_init_690_);
return v___x_698_;
}
else
{
lean_object* v___f_699_; lean_object* v___f_700_; size_t v___x_701_; size_t v___x_702_; lean_object* v___x_703_; 
v___f_699_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_699_, 0, v_f_689_);
lean_inc_ref(v_inst_687_);
v___f_700_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_700_, 0, v_inst_687_);
lean_closure_set(v___f_700_, 1, v___f_699_);
v___x_701_ = ((size_t)0ULL);
v___x_702_ = lean_usize_of_nat(v___x_696_);
v___x_703_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_687_, v___f_700_, v_buckets_693_, v___x_701_, v___x_702_, v_init_690_);
return v___x_703_;
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
lean_object* v___f_722_; lean_object* v___f_723_; size_t v___x_724_; size_t v___x_725_; lean_object* v___x_726_; 
v___f_722_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_722_, 0, v_f_714_);
v___f_723_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_723_, 0, v___x_717_);
lean_closure_set(v___f_723_, 1, v___f_722_);
v___x_724_ = ((size_t)0ULL);
v___x_725_ = lean_usize_of_nat(v___x_720_);
v___x_726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_717_, v___f_723_, v_buckets_718_, v___x_724_, v___x_725_, v_init_715_);
return v___x_726_;
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
lean_object* v___f_737_; lean_object* v___f_738_; size_t v___x_739_; size_t v___x_740_; lean_object* v___x_741_; 
v___f_737_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_737_, 0, v_f_729_);
v___f_738_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_738_, 0, v___x_732_);
lean_closure_set(v___f_738_, 1, v___f_737_);
v___x_739_ = ((size_t)0ULL);
v___x_740_ = lean_usize_of_nat(v___x_735_);
v___x_741_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_732_, v___f_738_, v_buckets_733_, v___x_739_, v___x_740_, v_init_730_);
return v___x_741_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__0(lean_object* v_f_742_, lean_object* v_x_743_, lean_object* v___y_744_, lean_object* v___y_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_apply_1(v_f_742_, v___y_744_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__1(lean_object* v_inst_747_, lean_object* v___f_748_, lean_object* v_x_749_, lean_object* v___y_750_){
_start:
{
lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_751_ = lean_box(0);
v___x_752_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_747_, v___f_748_, v___x_751_, v___y_750_);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg(lean_object* v_inst_753_, lean_object* v_f_754_, lean_object* v_b_755_){
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
v___f_764_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_764_, 0, v_f_754_);
lean_inc_ref(v_inst_753_);
v___f_765_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_765_, 0, v_inst_753_);
lean_closure_set(v___f_765_, 1, v___f_764_);
v___x_766_ = ((size_t)0ULL);
v___x_767_ = lean_usize_of_nat(v___x_760_);
v___x_768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_753_, v___f_765_, v_buckets_757_, v___x_766_, v___x_767_, v___x_761_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM(lean_object* v_00_u03b1_769_, lean_object* v_m_770_, lean_object* v_inst_771_, lean_object* v_f_772_, lean_object* v_b_773_){
_start:
{
lean_object* v_toApplicative_774_; lean_object* v_buckets_775_; lean_object* v_toPure_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_toApplicative_774_ = lean_ctor_get(v_inst_771_, 0);
v_buckets_775_ = lean_ctor_get(v_b_773_, 1);
lean_inc_ref(v_buckets_775_);
lean_dec_ref(v_b_773_);
v_toPure_776_ = lean_ctor_get(v_toApplicative_774_, 1);
v___x_777_ = lean_unsigned_to_nat(0u);
v___x_778_ = lean_array_get_size(v_buckets_775_);
v___x_779_ = lean_box(0);
v___x_780_ = lean_nat_dec_lt(v___x_777_, v___x_778_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_inc(v_toPure_776_);
lean_dec_ref(v_buckets_775_);
lean_dec(v_f_772_);
lean_dec_ref(v_inst_771_);
v___x_781_ = lean_apply_2(v_toPure_776_, lean_box(0), v___x_779_);
return v___x_781_;
}
else
{
lean_object* v___f_782_; lean_object* v___f_783_; size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
v___f_782_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_782_, 0, v_f_772_);
lean_inc_ref(v_inst_771_);
v___f_783_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_783_, 0, v_inst_771_);
lean_closure_set(v___f_783_, 1, v___f_782_);
v___x_784_ = ((size_t)0ULL);
v___x_785_ = lean_usize_of_nat(v___x_778_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_771_, v___f_783_, v_buckets_775_, v___x_784_, v___x_785_, v___x_779_);
return v___x_786_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__0(lean_object* v_f_787_, lean_object* v_a_788_, lean_object* v_x_789_, lean_object* v_acc_790_){
_start:
{
lean_object* v___x_791_; 
v___x_791_ = lean_apply_2(v_f_787_, v_a_788_, v_acc_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__1(lean_object* v_inst_792_, lean_object* v___f_793_, lean_object* v_a_794_, lean_object* v_x_795_, lean_object* v___y_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_792_, v___f_793_, v_a_794_, v___y_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg(lean_object* v_inst_798_, lean_object* v_f_799_, lean_object* v_init_800_, lean_object* v_b_801_){
_start:
{
lean_object* v_buckets_802_; lean_object* v___f_803_; lean_object* v___f_804_; size_t v_sz_805_; size_t v___x_806_; lean_object* v___x_807_; 
v_buckets_802_ = lean_ctor_get(v_b_801_, 1);
lean_inc_ref(v_buckets_802_);
lean_dec_ref(v_b_801_);
v___f_803_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_803_, 0, v_f_799_);
lean_inc_ref(v_inst_798_);
v___f_804_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_804_, 0, v_inst_798_);
lean_closure_set(v___f_804_, 1, v___f_803_);
v_sz_805_ = lean_array_size(v_buckets_802_);
v___x_806_ = ((size_t)0ULL);
v___x_807_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_798_, v_buckets_802_, v___f_804_, v_sz_805_, v___x_806_, v_init_800_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn(lean_object* v_00_u03b1_808_, lean_object* v_m_809_, lean_object* v_inst_810_, lean_object* v_00_u03b2_811_, lean_object* v_f_812_, lean_object* v_init_813_, lean_object* v_b_814_){
_start:
{
lean_object* v_buckets_815_; lean_object* v___f_816_; lean_object* v___f_817_; size_t v_sz_818_; size_t v___x_819_; lean_object* v___x_820_; 
v_buckets_815_ = lean_ctor_get(v_b_814_, 1);
lean_inc_ref(v_buckets_815_);
lean_dec_ref(v_b_814_);
v___f_816_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_816_, 0, v_f_812_);
lean_inc_ref(v_inst_810_);
v___f_817_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_817_, 0, v_inst_810_);
lean_closure_set(v___f_817_, 1, v___f_816_);
v_sz_818_ = lean_array_size(v_buckets_815_);
v___x_819_ = ((size_t)0ULL);
v___x_820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_810_, v_buckets_815_, v___f_817_, v_sz_818_, v___x_819_, v_init_813_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2(lean_object* v_inst_821_, lean_object* v_m_822_, lean_object* v_f_823_){
_start:
{
lean_object* v_toApplicative_824_; lean_object* v_buckets_825_; lean_object* v_toPure_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v_toApplicative_824_ = lean_ctor_get(v_inst_821_, 0);
v_buckets_825_ = lean_ctor_get(v_m_822_, 1);
lean_inc_ref(v_buckets_825_);
lean_dec_ref(v_m_822_);
v_toPure_826_ = lean_ctor_get(v_toApplicative_824_, 1);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_array_get_size(v_buckets_825_);
v___x_829_ = lean_box(0);
v___x_830_ = lean_nat_dec_lt(v___x_827_, v___x_828_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; 
lean_inc(v_toPure_826_);
lean_dec_ref(v_buckets_825_);
lean_dec(v_f_823_);
lean_dec_ref(v_inst_821_);
v___x_831_ = lean_apply_2(v_toPure_826_, lean_box(0), v___x_829_);
return v___x_831_;
}
else
{
lean_object* v___f_832_; lean_object* v___f_833_; size_t v___x_834_; size_t v___x_835_; lean_object* v___x_836_; 
v___f_832_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_832_, 0, v_f_823_);
lean_inc_ref(v_inst_821_);
v___f_833_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_833_, 0, v_inst_821_);
lean_closure_set(v___f_833_, 1, v___f_832_);
v___x_834_ = ((size_t)0ULL);
v___x_835_ = lean_usize_of_nat(v___x_828_);
v___x_836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_821_, v___f_833_, v_buckets_825_, v___x_834_, v___x_835_, v___x_829_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_837_){
_start:
{
lean_object* v___f_838_; 
v___f_838_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_838_, 0, v_inst_837_);
return v___f_838_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_839_, lean_object* v_m_840_, lean_object* v_inst_841_){
_start:
{
lean_object* v___f_842_; 
v___f_842_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_842_, 0, v_inst_841_);
return v___f_842_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_843_, lean_object* v_00_u03b2_844_, lean_object* v_m_845_, lean_object* v_init_846_, lean_object* v_f_847_){
_start:
{
lean_object* v_buckets_848_; lean_object* v___f_849_; lean_object* v___f_850_; size_t v_sz_851_; size_t v___x_852_; lean_object* v___x_853_; 
v_buckets_848_ = lean_ctor_get(v_m_845_, 1);
lean_inc_ref(v_buckets_848_);
lean_dec_ref(v_m_845_);
v___f_849_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_849_, 0, v_f_847_);
lean_inc_ref(v_inst_843_);
v___f_850_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_850_, 0, v_inst_843_);
lean_closure_set(v___f_850_, 1, v___f_849_);
v_sz_851_ = lean_array_size(v_buckets_848_);
v___x_852_ = ((size_t)0ULL);
v___x_853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_843_, v_buckets_848_, v___f_850_, v_sz_851_, v___x_852_, v_init_846_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_854_){
_start:
{
lean_object* v___f_855_; 
v___f_855_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_855_, 0, v_inst_854_);
return v___f_855_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_856_, lean_object* v_m_857_, lean_object* v_inst_858_){
_start:
{
lean_object* v___f_859_; 
v___f_859_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_859_, 0, v_inst_858_);
return v___f_859_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_filter___redArg___lam__0(lean_object* v_f_860_, lean_object* v_a_861_, lean_object* v_x_862_){
_start:
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_apply_1(v_f_860_, v_a_861_);
v___x_864_ = lean_unbox(v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_865_, lean_object* v_a_866_, lean_object* v_x_867_){
_start:
{
uint8_t v_res_868_; lean_object* v_r_869_; 
v_res_868_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_865_, v_a_866_, v_x_867_);
v_r_869_ = lean_box(v_res_868_);
return v_r_869_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg(lean_object* v_f_870_, lean_object* v_m_871_){
_start:
{
lean_object* v_buckets_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_buckets_872_ = lean_ctor_get(v_m_871_, 1);
v___x_873_ = lean_unsigned_to_nat(0u);
v___x_874_ = lean_array_get_size(v_buckets_872_);
v___x_875_ = lean_nat_dec_lt(v___x_873_, v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_dec_ref(v_m_871_);
lean_dec_ref(v_f_870_);
v___x_876_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
return v___x_876_;
}
else
{
lean_object* v___f_877_; lean_object* v___x_878_; 
v___f_877_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_877_, 0, v_f_870_);
v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_877_, v_m_871_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter(lean_object* v_00_u03b1_879_, lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_f_882_, lean_object* v_m_883_){
_start:
{
lean_object* v_buckets_884_; lean_object* v___x_885_; lean_object* v___x_886_; uint8_t v___x_887_; 
v_buckets_884_ = lean_ctor_get(v_m_883_, 1);
v___x_885_ = lean_unsigned_to_nat(0u);
v___x_886_ = lean_array_get_size(v_buckets_884_);
v___x_887_ = lean_nat_dec_lt(v___x_885_, v___x_886_);
if (v___x_887_ == 0)
{
lean_object* v___x_888_; 
lean_dec_ref(v_m_883_);
lean_dec_ref(v_f_882_);
v___x_888_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
return v___x_888_;
}
else
{
lean_object* v___f_889_; lean_object* v___x_890_; 
v___f_889_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_889_, 0, v_f_882_);
v___x_890_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_889_, v_m_883_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___boxed(lean_object* v_00_u03b1_891_, lean_object* v_inst_892_, lean_object* v_inst_893_, lean_object* v_f_894_, lean_object* v_m_895_){
_start:
{
lean_object* v_res_896_; 
v_res_896_ = l_Std_HashSet_Raw_filter(v_00_u03b1_891_, v_inst_892_, v_inst_893_, v_f_894_, v_m_895_);
lean_dec_ref(v_inst_893_);
lean_dec_ref(v_inst_892_);
return v_res_896_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__0(lean_object* v_x1_897_, lean_object* v_x2_898_, lean_object* v_x3_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = lean_array_push(v_x1_897_, v_x2_898_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__1(lean_object* v___x_901_, lean_object* v___f_902_, lean_object* v_acc_903_, lean_object* v_l_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_901_, v___f_902_, v_acc_903_, v_l_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg(lean_object* v_m_910_){
_start:
{
lean_object* v_size_911_; lean_object* v_buckets_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_size_911_ = lean_ctor_get(v_m_910_, 0);
lean_inc(v_size_911_);
v_buckets_912_ = lean_ctor_get(v_m_910_, 1);
lean_inc_ref(v_buckets_912_);
lean_dec_ref(v_m_910_);
v___x_913_ = lean_mk_empty_array_with_capacity(v_size_911_);
lean_dec(v_size_911_);
v___x_914_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_915_ = lean_unsigned_to_nat(0u);
v___x_916_ = lean_array_get_size(v_buckets_912_);
v___x_917_ = lean_nat_dec_lt(v___x_915_, v___x_916_);
if (v___x_917_ == 0)
{
lean_dec_ref(v_buckets_912_);
return v___x_913_;
}
else
{
lean_object* v___f_918_; size_t v___x_919_; size_t v___x_920_; lean_object* v___x_921_; 
v___f_918_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_919_ = ((size_t)0ULL);
v___x_920_ = lean_usize_of_nat(v___x_916_);
v___x_921_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_914_, v___f_918_, v_buckets_912_, v___x_919_, v___x_920_, v___x_913_);
return v___x_921_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray(lean_object* v_00_u03b1_922_, lean_object* v_m_923_){
_start:
{
lean_object* v_size_924_; lean_object* v_buckets_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_size_924_ = lean_ctor_get(v_m_923_, 0);
lean_inc(v_size_924_);
v_buckets_925_ = lean_ctor_get(v_m_923_, 1);
lean_inc_ref(v_buckets_925_);
lean_dec_ref(v_m_923_);
v___x_926_ = lean_mk_empty_array_with_capacity(v_size_924_);
lean_dec(v_size_924_);
v___x_927_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_array_get_size(v_buckets_925_);
v___x_930_ = lean_nat_dec_lt(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_dec_ref(v_buckets_925_);
return v___x_926_;
}
else
{
lean_object* v___f_931_; size_t v___x_932_; size_t v___x_933_; lean_object* v___x_934_; 
v___f_931_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_932_ = ((size_t)0ULL);
v___x_933_ = lean_usize_of_nat(v___x_929_);
v___x_934_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_927_, v___f_931_, v_buckets_925_, v___x_932_, v___x_933_, v___x_926_);
return v___x_934_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__0(lean_object* v_inst_935_, lean_object* v_inst_936_, lean_object* v_a_937_, lean_object* v_b_938_, lean_object* v_acc_939_){
_start:
{
lean_object* v_r_940_; lean_object* v___x_941_; 
v_r_940_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_935_, v_inst_936_, v_acc_939_, v_a_937_, v_b_938_);
v___x_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_941_, 0, v_r_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__1(lean_object* v___x_942_, lean_object* v___f_943_, lean_object* v_a_944_, lean_object* v_x_945_, lean_object* v___y_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_942_, v___f_943_, v_a_944_, v___y_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg(lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_m_u2081_952_, lean_object* v_m_u2082_953_){
_start:
{
lean_object* v_size_954_; lean_object* v_buckets_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_size_954_ = lean_ctor_get(v_m_u2081_952_, 0);
v_buckets_955_ = lean_ctor_get(v_m_u2081_952_, 1);
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_array_get_size(v_buckets_955_);
v___x_958_ = lean_nat_dec_lt(v___x_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec_ref(v_m_u2081_952_);
lean_dec_ref(v_inst_951_);
lean_dec_ref(v_inst_950_);
return v_m_u2082_953_;
}
else
{
lean_object* v_size_959_; lean_object* v_buckets_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_size_959_ = lean_ctor_get(v_m_u2082_953_, 0);
v_buckets_960_ = lean_ctor_get(v_m_u2082_953_, 1);
v___x_961_ = lean_array_get_size(v_buckets_960_);
v___x_962_ = lean_nat_dec_lt(v___x_956_, v___x_961_);
if (v___x_962_ == 0)
{
lean_dec_ref(v_m_u2082_953_);
lean_dec_ref(v_inst_951_);
lean_dec_ref(v_inst_950_);
return v_m_u2081_952_;
}
else
{
lean_object* v___x_963_; uint8_t v___x_964_; 
v___x_963_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_964_ = lean_nat_dec_le(v_size_954_, v_size_959_);
if (v___x_964_ == 0)
{
lean_object* v___f_965_; lean_object* v___x_966_; 
v___f_965_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_966_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_965_, v_inst_950_, v_inst_951_, v_m_u2081_952_, v_m_u2082_953_);
return v___x_966_;
}
else
{
lean_object* v___f_967_; lean_object* v___f_968_; size_t v_sz_969_; size_t v___x_970_; lean_object* v___x_971_; 
lean_inc_ref(v_buckets_955_);
lean_dec_ref(v_m_u2081_952_);
v___f_967_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_967_, 0, v_inst_950_);
lean_closure_set(v___f_967_, 1, v_inst_951_);
v___f_968_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_968_, 0, v___x_963_);
lean_closure_set(v___f_968_, 1, v___f_967_);
v_sz_969_ = lean_array_size(v_buckets_955_);
v___x_970_ = ((size_t)0ULL);
v___x_971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_963_, v_buckets_955_, v___f_968_, v_sz_969_, v___x_970_, v_m_u2082_953_);
return v___x_971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union(lean_object* v_00_u03b1_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_m_u2081_975_, lean_object* v_m_u2082_976_){
_start:
{
lean_object* v_size_977_; lean_object* v_buckets_978_; lean_object* v___x_979_; lean_object* v___x_980_; uint8_t v___x_981_; 
v_size_977_ = lean_ctor_get(v_m_u2081_975_, 0);
v_buckets_978_ = lean_ctor_get(v_m_u2081_975_, 1);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = lean_array_get_size(v_buckets_978_);
v___x_981_ = lean_nat_dec_lt(v___x_979_, v___x_980_);
if (v___x_981_ == 0)
{
lean_dec_ref(v_m_u2081_975_);
lean_dec_ref(v_inst_974_);
lean_dec_ref(v_inst_973_);
return v_m_u2082_976_;
}
else
{
lean_object* v_size_982_; lean_object* v_buckets_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v_size_982_ = lean_ctor_get(v_m_u2082_976_, 0);
v_buckets_983_ = lean_ctor_get(v_m_u2082_976_, 1);
v___x_984_ = lean_array_get_size(v_buckets_983_);
v___x_985_ = lean_nat_dec_lt(v___x_979_, v___x_984_);
if (v___x_985_ == 0)
{
lean_dec_ref(v_m_u2082_976_);
lean_dec_ref(v_inst_974_);
lean_dec_ref(v_inst_973_);
return v_m_u2081_975_;
}
else
{
lean_object* v___x_986_; uint8_t v___x_987_; 
v___x_986_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_987_ = lean_nat_dec_le(v_size_977_, v_size_982_);
if (v___x_987_ == 0)
{
lean_object* v___f_988_; lean_object* v___x_989_; 
v___f_988_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_988_, v_inst_973_, v_inst_974_, v_m_u2081_975_, v_m_u2082_976_);
return v___x_989_;
}
else
{
lean_object* v___f_990_; lean_object* v___f_991_; size_t v_sz_992_; size_t v___x_993_; lean_object* v___x_994_; 
lean_inc_ref(v_buckets_978_);
lean_dec_ref(v_m_u2081_975_);
v___f_990_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_990_, 0, v_inst_973_);
lean_closure_set(v___f_990_, 1, v_inst_974_);
v___f_991_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_991_, 0, v___x_986_);
lean_closure_set(v___f_991_, 1, v___f_990_);
v_sz_992_ = lean_array_size(v_buckets_978_);
v___x_993_ = ((size_t)0ULL);
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_986_, v_buckets_978_, v___f_991_, v_sz_992_, v___x_993_, v_m_u2082_976_);
return v___x_994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_995_, lean_object* v_inst_996_){
_start:
{
lean_object* v___x_997_; 
v___x_997_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_997_, 0, lean_box(0));
lean_closure_set(v___x_997_, 1, v_inst_995_);
lean_closure_set(v___x_997_, 2, v_inst_996_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_998_, lean_object* v_inst_999_, lean_object* v_inst_1000_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_1001_, 0, lean_box(0));
lean_closure_set(v___x_1001_, 1, v_inst_999_);
lean_closure_set(v___x_1001_, 2, v_inst_1000_);
return v___x_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter___redArg(lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_m_u2081_1004_, lean_object* v_m_u2082_1005_){
_start:
{
lean_object* v_buckets_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_buckets_1006_ = lean_ctor_get(v_m_u2081_1004_, 1);
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_array_get_size(v_buckets_1006_);
v___x_1009_ = lean_nat_dec_lt(v___x_1007_, v___x_1008_);
if (v___x_1009_ == 0)
{
lean_dec_ref(v_m_u2081_1004_);
lean_dec_ref(v_inst_1003_);
lean_dec_ref(v_inst_1002_);
return v_m_u2082_1005_;
}
else
{
lean_object* v_buckets_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_buckets_1010_ = lean_ctor_get(v_m_u2082_1005_, 1);
v___x_1011_ = lean_array_get_size(v_buckets_1010_);
v___x_1012_ = lean_nat_dec_lt(v___x_1007_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_dec_ref(v_m_u2082_1005_);
lean_dec_ref(v_inst_1003_);
lean_dec_ref(v_inst_1002_);
return v_m_u2081_1004_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1002_, v_inst_1003_, v_m_u2081_1004_, v_m_u2082_1005_);
return v___x_1013_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter(lean_object* v_00_u03b1_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_m_u2081_1017_, lean_object* v_m_u2082_1018_){
_start:
{
lean_object* v_buckets_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_buckets_1019_ = lean_ctor_get(v_m_u2081_1017_, 1);
v___x_1020_ = lean_unsigned_to_nat(0u);
v___x_1021_ = lean_array_get_size(v_buckets_1019_);
v___x_1022_ = lean_nat_dec_lt(v___x_1020_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec_ref(v_m_u2081_1017_);
lean_dec_ref(v_inst_1016_);
lean_dec_ref(v_inst_1015_);
return v_m_u2082_1018_;
}
else
{
lean_object* v_buckets_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_buckets_1023_ = lean_ctor_get(v_m_u2082_1018_, 1);
v___x_1024_ = lean_array_get_size(v_buckets_1023_);
v___x_1025_ = lean_nat_dec_lt(v___x_1020_, v___x_1024_);
if (v___x_1025_ == 0)
{
lean_dec_ref(v_m_u2082_1018_);
lean_dec_ref(v_inst_1016_);
lean_dec_ref(v_inst_1015_);
return v_m_u2081_1017_;
}
else
{
lean_object* v___x_1026_; 
v___x_1026_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1015_, v_inst_1016_, v_m_u2081_1017_, v_m_u2082_1018_);
return v___x_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1027_, lean_object* v_inst_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1029_, 0, lean_box(0));
lean_closure_set(v___x_1029_, 1, v_inst_1027_);
lean_closure_set(v___x_1029_, 2, v_inst_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1033_, 0, lean_box(0));
lean_closure_set(v___x_1033_, 1, v_inst_1031_);
lean_closure_set(v___x_1033_, 2, v_inst_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___f_1035_; 
v___x_1034_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1035_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1035_, 0, v___x_1034_);
return v___f_1035_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq___redArg(lean_object* v_inst_1036_, lean_object* v_inst_1037_, lean_object* v_m_u2081_1038_, lean_object* v_m_u2082_1039_){
_start:
{
lean_object* v___f_1040_; uint8_t v___x_1041_; 
v___f_1040_ = lean_obj_once(&l_Std_HashSet_Raw_beq___redArg___closed__0, &l_Std_HashSet_Raw_beq___redArg___closed__0_once, _init_l_Std_HashSet_Raw_beq___redArg___closed__0);
v___x_1041_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1036_, v_inst_1037_, v___f_1040_, v_m_u2081_1038_, v_m_u2082_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___redArg___boxed(lean_object* v_inst_1042_, lean_object* v_inst_1043_, lean_object* v_m_u2081_1044_, lean_object* v_m_u2082_1045_){
_start:
{
uint8_t v_res_1046_; lean_object* v_r_1047_; 
v_res_1046_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1042_, v_inst_1043_, v_m_u2081_1044_, v_m_u2082_1045_);
v_r_1047_ = lean_box(v_res_1046_);
return v_r_1047_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq(lean_object* v_00_u03b1_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_, lean_object* v_m_u2081_1051_, lean_object* v_m_u2082_1052_){
_start:
{
uint8_t v___x_1053_; 
v___x_1053_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1049_, v_inst_1050_, v_m_u2081_1051_, v_m_u2082_1052_);
return v___x_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___boxed(lean_object* v_00_u03b1_1054_, lean_object* v_inst_1055_, lean_object* v_inst_1056_, lean_object* v_m_u2081_1057_, lean_object* v_m_u2082_1058_){
_start:
{
uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_res_1059_ = l_Std_HashSet_Raw_beq(v_00_u03b1_1054_, v_inst_1055_, v_inst_1056_, v_m_u2081_1057_, v_m_u2082_1058_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1061_, lean_object* v_inst_1062_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1063_, 0, lean_box(0));
lean_closure_set(v___x_1063_, 1, v_inst_1061_);
lean_closure_set(v___x_1063_, 2, v_inst_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1067_, 0, lean_box(0));
lean_closure_set(v___x_1067_, 1, v_inst_1065_);
lean_closure_set(v___x_1067_, 2, v_inst_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_diff___redArg___lam__0(lean_object* v_inst_1068_, lean_object* v_inst_1069_, lean_object* v_m_u2082_1070_, uint8_t v___x_1071_, lean_object* v_k_1072_, lean_object* v_x_1073_){
_start:
{
uint8_t v___x_1074_; 
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1068_, v_inst_1069_, v_m_u2082_1070_, v_k_1072_);
if (v___x_1074_ == 0)
{
return v___x_1071_;
}
else
{
uint8_t v___x_1075_; 
v___x_1075_ = 0;
return v___x_1075_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1076_, lean_object* v_inst_1077_, lean_object* v_m_u2082_1078_, lean_object* v___x_1079_, lean_object* v_k_1080_, lean_object* v_x_1081_){
_start:
{
uint8_t v___x_100__boxed_1082_; uint8_t v_res_1083_; lean_object* v_r_1084_; 
v___x_100__boxed_1082_ = lean_unbox(v___x_1079_);
v_res_1083_ = l_Std_HashSet_Raw_diff___redArg___lam__0(v_inst_1076_, v_inst_1077_, v_m_u2082_1078_, v___x_100__boxed_1082_, v_k_1080_, v_x_1081_);
lean_dec_ref(v_m_u2082_1078_);
v_r_1084_ = lean_box(v_res_1083_);
return v_r_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg(lean_object* v_inst_1085_, lean_object* v_inst_1086_, lean_object* v_m_u2081_1087_, lean_object* v_m_u2082_1088_){
_start:
{
lean_object* v_size_1089_; lean_object* v_buckets_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_size_1089_ = lean_ctor_get(v_m_u2081_1087_, 0);
v_buckets_1090_ = lean_ctor_get(v_m_u2081_1087_, 1);
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = lean_array_get_size(v_buckets_1090_);
v___x_1093_ = lean_nat_dec_lt(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_dec_ref(v_m_u2081_1087_);
lean_dec_ref(v_inst_1086_);
lean_dec_ref(v_inst_1085_);
return v_m_u2082_1088_;
}
else
{
lean_object* v_size_1094_; lean_object* v_buckets_1095_; lean_object* v___x_1096_; uint8_t v___x_1097_; 
v_size_1094_ = lean_ctor_get(v_m_u2082_1088_, 0);
v_buckets_1095_ = lean_ctor_get(v_m_u2082_1088_, 1);
v___x_1096_ = lean_array_get_size(v_buckets_1095_);
v___x_1097_ = lean_nat_dec_lt(v___x_1091_, v___x_1096_);
if (v___x_1097_ == 0)
{
lean_dec_ref(v_m_u2082_1088_);
lean_dec_ref(v_inst_1086_);
lean_dec_ref(v_inst_1085_);
return v_m_u2081_1087_;
}
else
{
uint8_t v___x_1098_; 
v___x_1098_ = lean_nat_dec_le(v_size_1089_, v_size_1094_);
if (v___x_1098_ == 0)
{
lean_object* v___f_1099_; lean_object* v___x_1100_; 
v___f_1099_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1100_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1099_, v_inst_1085_, v_inst_1086_, v_m_u2081_1087_, v_m_u2082_1088_);
return v___x_1100_;
}
else
{
lean_object* v___x_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_box(v___x_1098_);
v___f_1102_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1102_, 0, v_inst_1085_);
lean_closure_set(v___f_1102_, 1, v_inst_1086_);
lean_closure_set(v___f_1102_, 2, v_m_u2082_1088_);
lean_closure_set(v___f_1102_, 3, v___x_1101_);
v___x_1103_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1102_, v_m_u2081_1087_);
return v___x_1103_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff(lean_object* v_00_u03b1_1104_, lean_object* v_inst_1105_, lean_object* v_inst_1106_, lean_object* v_m_u2081_1107_, lean_object* v_m_u2082_1108_){
_start:
{
lean_object* v_size_1109_; lean_object* v_buckets_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_size_1109_ = lean_ctor_get(v_m_u2081_1107_, 0);
v_buckets_1110_ = lean_ctor_get(v_m_u2081_1107_, 1);
v___x_1111_ = lean_unsigned_to_nat(0u);
v___x_1112_ = lean_array_get_size(v_buckets_1110_);
v___x_1113_ = lean_nat_dec_lt(v___x_1111_, v___x_1112_);
if (v___x_1113_ == 0)
{
lean_dec_ref(v_m_u2081_1107_);
lean_dec_ref(v_inst_1106_);
lean_dec_ref(v_inst_1105_);
return v_m_u2082_1108_;
}
else
{
lean_object* v_size_1114_; lean_object* v_buckets_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_size_1114_ = lean_ctor_get(v_m_u2082_1108_, 0);
v_buckets_1115_ = lean_ctor_get(v_m_u2082_1108_, 1);
v___x_1116_ = lean_array_get_size(v_buckets_1115_);
v___x_1117_ = lean_nat_dec_lt(v___x_1111_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_dec_ref(v_m_u2082_1108_);
lean_dec_ref(v_inst_1106_);
lean_dec_ref(v_inst_1105_);
return v_m_u2081_1107_;
}
else
{
uint8_t v___x_1118_; 
v___x_1118_ = lean_nat_dec_le(v_size_1109_, v_size_1114_);
if (v___x_1118_ == 0)
{
lean_object* v___f_1119_; lean_object* v___x_1120_; 
v___f_1119_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1120_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1119_, v_inst_1105_, v_inst_1106_, v_m_u2081_1107_, v_m_u2082_1108_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; lean_object* v___f_1122_; lean_object* v___x_1123_; 
v___x_1121_ = lean_box(v___x_1118_);
v___f_1122_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1122_, 0, v_inst_1105_);
lean_closure_set(v___f_1122_, 1, v_inst_1106_);
lean_closure_set(v___f_1122_, 2, v_m_u2082_1108_);
lean_closure_set(v___f_1122_, 3, v___x_1121_);
v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1122_, v_m_u2081_1107_);
return v___x_1123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1124_, lean_object* v_inst_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1126_, 0, lean_box(0));
lean_closure_set(v___x_1126_, 1, v_inst_1124_);
lean_closure_set(v___x_1126_, 2, v_inst_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1127_, lean_object* v_inst_1128_, lean_object* v_inst_1129_){
_start:
{
lean_object* v___x_1130_; 
v___x_1130_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1130_, 0, lean_box(0));
lean_closure_set(v___x_1130_, 1, v_inst_1128_);
lean_closure_set(v___x_1130_, 2, v_inst_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0(lean_object* v_p_1131_, lean_object* v___x_1132_, lean_object* v___x_1133_, lean_object* v_a_1134_, lean_object* v_b_1135_, lean_object* v_acc_1136_){
_start:
{
lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1137_ = lean_apply_1(v_p_1131_, v_a_1134_);
v___x_1138_ = lean_unbox(v___x_1137_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec_ref(v___x_1133_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v___x_1132_);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1133_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1143_, lean_object* v___x_1144_, lean_object* v___x_1145_, lean_object* v_a_1146_, lean_object* v_b_1147_, lean_object* v_acc_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Std_HashSet_Raw_all___redArg___lam__0(v_p_1143_, v___x_1144_, v___x_1145_, v_a_1146_, v_b_1147_, v_acc_1148_);
lean_dec_ref(v_acc_1148_);
return v_res_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__1(lean_object* v___x_1150_, lean_object* v___f_1151_, lean_object* v_a_1152_, lean_object* v_x_1153_, lean_object* v___y_1154_){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1150_, v___f_1151_, v_a_1152_, v___y_1154_);
return v___x_1155_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all___redArg(lean_object* v_m_1159_, lean_object* v_p_1160_){
_start:
{
lean_object* v___x_1161_; lean_object* v_buckets_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___f_1165_; lean_object* v___f_1166_; size_t v_sz_1167_; size_t v___x_1168_; lean_object* v___x_1169_; lean_object* v_fst_1170_; 
v___x_1161_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1162_ = lean_ctor_get(v_m_1159_, 1);
lean_inc_ref(v_buckets_1162_);
lean_dec_ref(v_m_1159_);
v___x_1163_ = lean_box(0);
v___x_1164_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1165_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1165_, 0, v_p_1160_);
lean_closure_set(v___f_1165_, 1, v___x_1163_);
lean_closure_set(v___f_1165_, 2, v___x_1164_);
v___f_1166_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1166_, 0, v___x_1161_);
lean_closure_set(v___f_1166_, 1, v___f_1165_);
v_sz_1167_ = lean_array_size(v_buckets_1162_);
v___x_1168_ = ((size_t)0ULL);
v___x_1169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1161_, v_buckets_1162_, v___f_1166_, v_sz_1167_, v___x_1168_, v___x_1164_);
v_fst_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_fst_1170_);
lean_dec(v___x_1169_);
if (lean_obj_tag(v_fst_1170_) == 0)
{
uint8_t v___x_1171_; 
v___x_1171_ = 1;
return v___x_1171_;
}
else
{
lean_object* v_val_1172_; uint8_t v___x_1173_; 
v_val_1172_ = lean_ctor_get(v_fst_1170_, 0);
lean_inc(v_val_1172_);
lean_dec_ref_known(v_fst_1170_, 1);
v___x_1173_ = lean_unbox(v_val_1172_);
lean_dec(v_val_1172_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___boxed(lean_object* v_m_1174_, lean_object* v_p_1175_){
_start:
{
uint8_t v_res_1176_; lean_object* v_r_1177_; 
v_res_1176_ = l_Std_HashSet_Raw_all___redArg(v_m_1174_, v_p_1175_);
v_r_1177_ = lean_box(v_res_1176_);
return v_r_1177_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all(lean_object* v_00_u03b1_1178_, lean_object* v_m_1179_, lean_object* v_p_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v_buckets_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___f_1185_; lean_object* v___f_1186_; size_t v_sz_1187_; size_t v___x_1188_; lean_object* v___x_1189_; lean_object* v_fst_1190_; 
v___x_1181_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1182_ = lean_ctor_get(v_m_1179_, 1);
lean_inc_ref(v_buckets_1182_);
lean_dec_ref(v_m_1179_);
v___x_1183_ = lean_box(0);
v___x_1184_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1185_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1185_, 0, v_p_1180_);
lean_closure_set(v___f_1185_, 1, v___x_1183_);
lean_closure_set(v___f_1185_, 2, v___x_1184_);
v___f_1186_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1186_, 0, v___x_1181_);
lean_closure_set(v___f_1186_, 1, v___f_1185_);
v_sz_1187_ = lean_array_size(v_buckets_1182_);
v___x_1188_ = ((size_t)0ULL);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1181_, v_buckets_1182_, v___f_1186_, v_sz_1187_, v___x_1188_, v___x_1184_);
v_fst_1190_ = lean_ctor_get(v___x_1189_, 0);
lean_inc(v_fst_1190_);
lean_dec(v___x_1189_);
if (lean_obj_tag(v_fst_1190_) == 0)
{
uint8_t v___x_1191_; 
v___x_1191_ = 1;
return v___x_1191_;
}
else
{
lean_object* v_val_1192_; uint8_t v___x_1193_; 
v_val_1192_ = lean_ctor_get(v_fst_1190_, 0);
lean_inc(v_val_1192_);
lean_dec_ref_known(v_fst_1190_, 1);
v___x_1193_ = lean_unbox(v_val_1192_);
lean_dec(v_val_1192_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___boxed(lean_object* v_00_u03b1_1194_, lean_object* v_m_1195_, lean_object* v_p_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l_Std_HashSet_Raw_all(v_00_u03b1_1194_, v_m_1195_, v_p_1196_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0(lean_object* v_p_1199_, lean_object* v___x_1200_, lean_object* v___x_1201_, lean_object* v_a_1202_, lean_object* v_b_1203_, lean_object* v_acc_1204_){
_start:
{
lean_object* v___x_1205_; uint8_t v___x_1206_; 
v___x_1205_ = lean_apply_1(v_p_1199_, v_a_1202_);
v___x_1206_ = lean_unbox(v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1207_, 0, v___x_1200_);
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref(v___x_1200_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1205_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___x_1201_);
v___x_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1209_);
return v___x_1210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1211_, lean_object* v___x_1212_, lean_object* v___x_1213_, lean_object* v_a_1214_, lean_object* v_b_1215_, lean_object* v_acc_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_HashSet_Raw_any___redArg___lam__0(v_p_1211_, v___x_1212_, v___x_1213_, v_a_1214_, v_b_1215_, v_acc_1216_);
lean_dec_ref(v_acc_1216_);
return v_res_1217_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any___redArg(lean_object* v_m_1218_, lean_object* v_p_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v_buckets_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___f_1225_; size_t v_sz_1226_; size_t v___x_1227_; lean_object* v___x_1228_; lean_object* v_fst_1229_; 
v___x_1220_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1221_ = lean_ctor_get(v_m_1218_, 1);
lean_inc_ref(v_buckets_1221_);
lean_dec_ref(v_m_1218_);
v___x_1222_ = lean_box(0);
v___x_1223_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1224_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1224_, 0, v_p_1219_);
lean_closure_set(v___f_1224_, 1, v___x_1223_);
lean_closure_set(v___f_1224_, 2, v___x_1222_);
v___f_1225_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1225_, 0, v___x_1220_);
lean_closure_set(v___f_1225_, 1, v___f_1224_);
v_sz_1226_ = lean_array_size(v_buckets_1221_);
v___x_1227_ = ((size_t)0ULL);
v___x_1228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1220_, v_buckets_1221_, v___f_1225_, v_sz_1226_, v___x_1227_, v___x_1223_);
v_fst_1229_ = lean_ctor_get(v___x_1228_, 0);
lean_inc(v_fst_1229_);
lean_dec(v___x_1228_);
if (lean_obj_tag(v_fst_1229_) == 0)
{
uint8_t v___x_1230_; 
v___x_1230_ = 0;
return v___x_1230_;
}
else
{
lean_object* v_val_1231_; uint8_t v___x_1232_; 
v_val_1231_ = lean_ctor_get(v_fst_1229_, 0);
lean_inc(v_val_1231_);
lean_dec_ref_known(v_fst_1229_, 1);
v___x_1232_ = lean_unbox(v_val_1231_);
lean_dec(v_val_1231_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___boxed(lean_object* v_m_1233_, lean_object* v_p_1234_){
_start:
{
uint8_t v_res_1235_; lean_object* v_r_1236_; 
v_res_1235_ = l_Std_HashSet_Raw_any___redArg(v_m_1233_, v_p_1234_);
v_r_1236_ = lean_box(v_res_1235_);
return v_r_1236_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any(lean_object* v_00_u03b1_1237_, lean_object* v_m_1238_, lean_object* v_p_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v_buckets_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___f_1244_; lean_object* v___f_1245_; size_t v_sz_1246_; size_t v___x_1247_; lean_object* v___x_1248_; lean_object* v_fst_1249_; 
v___x_1240_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1241_ = lean_ctor_get(v_m_1238_, 1);
lean_inc_ref(v_buckets_1241_);
lean_dec_ref(v_m_1238_);
v___x_1242_ = lean_box(0);
v___x_1243_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1244_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1244_, 0, v_p_1239_);
lean_closure_set(v___f_1244_, 1, v___x_1243_);
lean_closure_set(v___f_1244_, 2, v___x_1242_);
v___f_1245_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1245_, 0, v___x_1240_);
lean_closure_set(v___f_1245_, 1, v___f_1244_);
v_sz_1246_ = lean_array_size(v_buckets_1241_);
v___x_1247_ = ((size_t)0ULL);
v___x_1248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1240_, v_buckets_1241_, v___f_1245_, v_sz_1246_, v___x_1247_, v___x_1243_);
v_fst_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_fst_1249_);
lean_dec(v___x_1248_);
if (lean_obj_tag(v_fst_1249_) == 0)
{
uint8_t v___x_1250_; 
v___x_1250_ = 0;
return v___x_1250_;
}
else
{
lean_object* v_val_1251_; uint8_t v___x_1252_; 
v_val_1251_ = lean_ctor_get(v_fst_1249_, 0);
lean_inc(v_val_1251_);
lean_dec_ref_known(v_fst_1249_, 1);
v___x_1252_ = lean_unbox(v_val_1251_);
lean_dec(v_val_1251_);
return v___x_1252_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___boxed(lean_object* v_00_u03b1_1253_, lean_object* v_m_1254_, lean_object* v_p_1255_){
_start:
{
uint8_t v_res_1256_; lean_object* v_r_1257_; 
v_res_1256_ = l_Std_HashSet_Raw_any(v_00_u03b1_1253_, v_m_1254_, v_p_1255_);
v_r_1257_ = lean_box(v_res_1256_);
return v_r_1257_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany___redArg(lean_object* v_inst_1258_, lean_object* v_inst_1259_, lean_object* v_inst_1260_, lean_object* v_m_1261_, lean_object* v_l_1262_){
_start:
{
lean_object* v_buckets_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; uint8_t v___x_1266_; 
v_buckets_1263_ = lean_ctor_get(v_m_1261_, 1);
v___x_1264_ = lean_unsigned_to_nat(0u);
v___x_1265_ = lean_array_get_size(v_buckets_1263_);
v___x_1266_ = lean_nat_dec_lt(v___x_1264_, v___x_1265_);
if (v___x_1266_ == 0)
{
lean_dec(v_l_1262_);
lean_dec(v_inst_1260_);
lean_dec_ref(v_inst_1259_);
lean_dec_ref(v_inst_1258_);
return v_m_1261_;
}
else
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1260_, v_inst_1258_, v_inst_1259_, v_m_1261_, v_l_1262_);
return v___x_1267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany(lean_object* v_00_u03b1_1268_, lean_object* v_inst_1269_, lean_object* v_inst_1270_, lean_object* v_00_u03c1_1271_, lean_object* v_inst_1272_, lean_object* v_m_1273_, lean_object* v_l_1274_){
_start:
{
lean_object* v_buckets_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v_buckets_1275_ = lean_ctor_get(v_m_1273_, 1);
v___x_1276_ = lean_unsigned_to_nat(0u);
v___x_1277_ = lean_array_get_size(v_buckets_1275_);
v___x_1278_ = lean_nat_dec_lt(v___x_1276_, v___x_1277_);
if (v___x_1278_ == 0)
{
lean_dec(v_l_1274_);
lean_dec(v_inst_1272_);
lean_dec_ref(v_inst_1270_);
lean_dec_ref(v_inst_1269_);
return v_m_1273_;
}
else
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1272_, v_inst_1269_, v_inst_1270_, v_m_1273_, v_l_1274_);
return v___x_1279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray___redArg(lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_l_1286_){
_start:
{
lean_object* v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
v___x_1288_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1288_ == 0)
{
lean_dec_ref(v_l_1286_);
lean_dec_ref(v_inst_1285_);
lean_dec_ref(v_inst_1284_);
return v___x_1287_;
}
else
{
lean_object* v___f_1289_; lean_object* v___x_1290_; 
v___f_1289_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1290_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1289_, v_inst_1284_, v_inst_1285_, v___x_1287_, v_l_1286_);
return v___x_1290_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray(lean_object* v_00_u03b1_1291_, lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_l_1294_){
_start:
{
lean_object* v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
v___x_1296_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1296_ == 0)
{
lean_dec_ref(v_l_1294_);
lean_dec_ref(v_inst_1293_);
lean_dec_ref(v_inst_1292_);
return v___x_1295_;
}
else
{
lean_object* v___f_1297_; lean_object* v___x_1298_; 
v___f_1297_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1298_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1297_, v_inst_1292_, v_inst_1293_, v___x_1295_, v_l_1294_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg(lean_object* v_m_1299_){
_start:
{
lean_object* v___x_1300_; 
v___x_1300_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1299_);
return v___x_1300_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_HashSet_Raw_Internal_numBuckets___redArg(v_m_1301_);
lean_dec_ref(v_m_1301_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets(lean_object* v_00_u03b1_1303_, lean_object* v_m_1304_){
_start:
{
lean_object* v___x_1305_; 
v___x_1305_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1306_, lean_object* v_m_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_Std_HashSet_Raw_Internal_numBuckets(v_00_u03b1_1306_, v_m_1307_);
lean_dec_ref(v_m_1307_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2(lean_object* v_inst_1312_, lean_object* v___f_1313_, lean_object* v_m_1314_, lean_object* v_prec_1315_){
_start:
{
lean_object* v___x_1316_; lean_object* v_buckets_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1337_; 
v___x_1316_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1317_ = lean_ctor_get(v_m_1314_, 1);
v_isSharedCheck_1337_ = !lean_is_exclusive(v_m_1314_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v_m_1314_, 0);
lean_dec(v_unused_1338_);
v___x_1319_ = v_m_1314_;
v_isShared_1320_ = v_isSharedCheck_1337_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_buckets_1317_);
lean_dec(v_m_1314_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1337_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1321_; lean_object* v___y_1323_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v___x_1321_ = ((lean_object*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1));
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_array_get_size(v_buckets_1317_);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = lean_nat_dec_lt(v___x_1331_, v___x_1330_);
if (v___x_1332_ == 0)
{
lean_dec_ref(v_buckets_1317_);
lean_dec_ref(v___f_1313_);
v___y_1323_ = v___x_1329_;
goto v___jp_1322_;
}
else
{
lean_object* v___f_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___f_1333_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1333_, 0, v___x_1316_);
lean_closure_set(v___f_1333_, 1, v___f_1313_);
v___x_1334_ = lean_usize_of_nat(v___x_1330_);
v___x_1335_ = ((size_t)0ULL);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1316_, v___f_1333_, v_buckets_1317_, v___x_1334_, v___x_1335_, v___x_1329_);
v___y_1323_ = v___x_1336_;
goto v___jp_1322_;
}
v___jp_1322_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = l_List_repr___redArg(v_inst_1312_, v___y_1323_);
if (v_isShared_1320_ == 0)
{
lean_ctor_set_tag(v___x_1319_, 5);
lean_ctor_set(v___x_1319_, 1, v___x_1324_);
lean_ctor_set(v___x_1319_, 0, v___x_1321_);
v___x_1326_ = v___x_1319_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1321_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Repr_addAppParen(v___x_1326_, v_prec_1315_);
return v___x_1327_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1339_, lean_object* v___f_1340_, lean_object* v_m_1341_, lean_object* v_prec_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2(v_inst_1339_, v___f_1340_, v_m_1341_, v_prec_1342_);
lean_dec(v_prec_1342_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg(lean_object* v_inst_1344_){
_start:
{
lean_object* v___f_1345_; lean_object* v___f_1346_; 
v___f_1345_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___f_1346_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1346_, 0, v_inst_1344_);
lean_closure_set(v___f_1346_, 1, v___f_1345_);
return v___f_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr(lean_object* v_00_u03b1_1347_, lean_object* v_inst_1348_){
_start:
{
lean_object* v___x_1349_; 
v___x_1349_ = l_Std_HashSet_Raw_instRepr___redArg(v_inst_1348_);
return v___x_1349_;
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
