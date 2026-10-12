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
lean_object* l_Std_HashSet_Raw_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
return v___x_34_;
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_35_;
v_res_35_ = l_Std_HashSet_Raw_instEmptyCollection___redArg();
stack->m_obj
 = v_res_35_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection___redArg___boxed(lean_object* v___dummy_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Std_HashSet_Raw_instEmptyCollection___redArg();
return v_res_37_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Std_HashSet_Raw_instEmptyCollection___redArg();
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection(lean_object* v_00_u03b1_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__0, &l_Std_HashSet_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0);
return v___x_40_;
}
}
lean_object* l_Std_HashSet_Raw_instInhabited___redArg(){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
return v___x_42_;
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_43_;
v_res_43_ = l_Std_HashSet_Raw_instInhabited___redArg();
stack->m_obj
 = v_res_43_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited___redArg___boxed(lean_object* v___dummy_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Std_HashSet_Raw_instInhabited___redArg();
return v_res_45_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_HashSet_Raw_instInhabited___redArg();
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited(lean_object* v_00_u03b1_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l_Std_HashSet_Raw_instInhabited___closed__0, &l_Std_HashSet_Raw_instInhabited___closed__0_once, _init_l_Std_HashSet_Raw_instInhabited___closed__0);
return v___x_48_;
}
}
static lean_object* _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5));
v___x_90_ = l_String_toRawSubstring_x27(v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(lean_object* v_x_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__4));
lean_inc(v_x_112_);
v___x_116_ = l_Lean_Syntax_isOfKind(v_x_112_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_x_112_);
v___x_117_ = lean_box(1);
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_a_114_);
return v___x_118_;
}
else
{
lean_object* v_quotContext_119_; lean_object* v_currMacroScope_120_; lean_object* v_ref_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_quotContext_119_ = lean_ctor_get(v_a_113_, 1);
v_currMacroScope_120_ = lean_ctor_get(v_a_113_, 2);
v_ref_121_ = lean_ctor_get(v_a_113_, 5);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = l_Lean_Syntax_getArg(v_x_112_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(2u);
v___x_125_ = l_Lean_Syntax_getArg(v_x_112_, v___x_124_);
lean_dec(v_x_112_);
v___x_126_ = 0;
v___x_127_ = l_Lean_SourceInfo_fromRef(v_ref_121_, v___x_126_);
v___x_128_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4));
v___x_129_ = lean_obj_once(&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6, &l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6);
v___x_130_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_120_);
lean_inc(v_quotContext_119_);
v___x_131_ = l_Lean_addMacroScope(v_quotContext_119_, v___x_130_, v_currMacroScope_120_);
v___x_132_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12));
lean_inc_n(v___x_127_, 2);
v___x_133_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_133_, 0, v___x_127_);
lean_ctor_set(v___x_133_, 1, v___x_129_);
lean_ctor_set(v___x_133_, 2, v___x_131_);
lean_ctor_set(v___x_133_, 3, v___x_132_);
v___x_134_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14));
v___x_135_ = l_Lean_Syntax_node2(v___x_127_, v___x_134_, v___x_123_, v___x_125_);
v___x_136_ = l_Lean_Syntax_node2(v___x_127_, v___x_128_, v___x_133_, v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v_a_114_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___boxed(lean_object* v_x_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(v_x_138_, v_a_139_, v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(lean_object* v_x_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4));
lean_inc(v_x_145_);
v___x_149_ = l_Lean_Syntax_isOfKind(v_x_145_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v_x_145_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_a_147_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = l_Lean_Syntax_getArg(v_x_145_, v___x_152_);
v___x_154_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1));
lean_inc(v___x_153_);
v___x_155_ = l_Lean_Syntax_isOfKind(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v___x_153_);
lean_dec(v_x_145_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_147_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = l_Lean_Syntax_getArg(v_x_145_, v___x_158_);
lean_dec(v_x_145_);
v___x_160_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_159_);
v___x_161_ = l_Lean_Syntax_matchesNull(v___x_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v___x_159_);
lean_dec(v___x_153_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_a_147_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_ref_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_164_ = l_Lean_Syntax_getArg(v___x_159_, v___x_152_);
v___x_165_ = l_Lean_Syntax_getArg(v___x_159_, v___x_158_);
lean_dec(v___x_159_);
v_ref_166_ = l_Lean_replaceRef(v___x_153_, v_a_146_);
lean_dec(v___x_153_);
v___x_167_ = 0;
v___x_168_ = l_Lean_SourceInfo_fromRef(v_ref_166_, v___x_167_);
lean_dec(v_ref_166_);
v___x_169_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__4));
v___x_170_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__7));
lean_inc(v___x_168_);
v___x_171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_168_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = l_Lean_Syntax_node3(v___x_168_, v___x_169_, v___x_164_, v___x_171_, v___x_165_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_a_147_);
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___boxed(lean_object* v_x_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(v_x_174_, v_a_175_, v_a_176_);
lean_dec(v_a_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert___redArg(lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_m_180_, lean_object* v_a_181_){
_start:
{
lean_object* v_buckets_182_; lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v_buckets_182_ = lean_ctor_get(v_m_180_, 1);
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = lean_array_get_size(v_buckets_182_);
v___x_185_ = lean_nat_dec_lt(v___x_183_, v___x_184_);
if (v___x_185_ == 0)
{
lean_dec(v_a_181_);
lean_dec_ref(v_inst_179_);
lean_dec_ref(v_inst_178_);
return v_m_180_;
}
else
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = lean_box(0);
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_178_, v_inst_179_, v_m_180_, v_a_181_, v___x_186_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert(lean_object* v_00_u03b1_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_m_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_buckets_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v_buckets_193_ = lean_ctor_get(v_m_191_, 1);
v___x_194_ = lean_unsigned_to_nat(0u);
v___x_195_ = lean_array_get_size(v_buckets_193_);
v___x_196_ = lean_nat_dec_lt(v___x_194_, v___x_195_);
if (v___x_196_ == 0)
{
lean_dec(v_a_192_);
lean_dec_ref(v_inst_190_);
lean_dec_ref(v_inst_189_);
return v_m_191_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_box(0);
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_189_, v_inst_190_, v_m_191_, v_a_192_, v___x_197_);
return v___x_198_;
}
}
}
static lean_object* _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__0);
v___x_200_ = lean_array_get_size(v___x_199_);
return v___x_200_;
}
}
static uint8_t _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v___x_201_ = lean_obj_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_202_ = lean_unsigned_to_nat(0u);
v___x_203_ = lean_nat_dec_lt(v___x_202_, v___x_201_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_207_; uint8_t v___x_208_; 
v___x_207_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
v___x_208_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_208_ == 0)
{
lean_dec(v_a_206_);
lean_dec_ref(v_inst_205_);
lean_dec_ref(v_inst_204_);
return v___x_207_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_box(0);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_204_, v_inst_205_, v___x_207_, v_a_206_, v___x_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg(lean_object* v_inst_211_, lean_object* v_inst_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_213_, 0, v_inst_211_);
lean_closure_set(v___f_213_, 1, v_inst_212_);
return v___f_213_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable(lean_object* v_00_u03b1_214_, lean_object* v_inst_215_, lean_object* v_inst_216_){
_start:
{
lean_object* v___f_217_; 
v___f_217_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_217_, 0, v_inst_215_);
lean_closure_set(v___f_217_, 1, v_inst_216_);
return v___f_217_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_a_220_, lean_object* v_s_221_){
_start:
{
lean_object* v_buckets_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_buckets_222_ = lean_ctor_get(v_s_221_, 1);
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = lean_array_get_size(v_buckets_222_);
v___x_225_ = lean_nat_dec_lt(v___x_223_, v___x_224_);
if (v___x_225_ == 0)
{
lean_dec(v_a_220_);
lean_dec_ref(v_inst_219_);
lean_dec_ref(v_inst_218_);
return v_s_221_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_box(0);
v___x_227_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_218_, v_inst_219_, v_s_221_, v_a_220_, v___x_226_);
return v___x_227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg(lean_object* v_inst_228_, lean_object* v_inst_229_){
_start:
{
lean_object* v___f_230_; 
v___f_230_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_230_, 0, v_inst_228_);
lean_closure_set(v___f_230_, 1, v_inst_229_);
return v___f_230_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable(lean_object* v_00_u03b1_231_, lean_object* v_inst_232_, lean_object* v_inst_233_){
_start:
{
lean_object* v___f_234_; 
v___f_234_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_234_, 0, v_inst_232_);
lean_closure_set(v___f_234_, 1, v_inst_233_);
return v___f_234_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert___redArg(lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_m_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_size_239_; lean_object* v_buckets_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_size_239_ = lean_ctor_get(v_m_237_, 0);
v_buckets_240_ = lean_ctor_get(v_m_237_, 1);
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_array_get_size(v_buckets_240_);
v___x_243_ = lean_nat_dec_lt(v___x_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_a_238_);
lean_dec_ref(v_inst_236_);
lean_dec_ref(v_inst_235_);
v___x_244_ = lean_box(v___x_243_);
v___x_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v_m_237_);
return v___x_245_;
}
else
{
lean_object* v___x_246_; uint64_t v___x_247_; uint64_t v___x_248_; uint64_t v___x_249_; uint64_t v___x_250_; uint64_t v_fold_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; size_t v___x_255_; size_t v___x_256_; size_t v___x_257_; size_t v___x_258_; size_t v___x_259_; lean_object* v_bkt_260_; uint8_t v___x_261_; 
lean_inc_ref(v_inst_236_);
lean_inc_n(v_a_238_, 2);
v___x_246_ = lean_apply_1(v_inst_236_, v_a_238_);
v___x_247_ = 32ULL;
v___x_248_ = lean_unbox_uint64(v___x_246_);
v___x_249_ = lean_uint64_shift_right(v___x_248_, v___x_247_);
v___x_250_ = lean_unbox_uint64(v___x_246_);
lean_dec_ref(v___x_246_);
v_fold_251_ = lean_uint64_xor(v___x_250_, v___x_249_);
v___x_252_ = 16ULL;
v___x_253_ = lean_uint64_shift_right(v_fold_251_, v___x_252_);
v___x_254_ = lean_uint64_xor(v_fold_251_, v___x_253_);
v___x_255_ = lean_uint64_to_usize(v___x_254_);
v___x_256_ = lean_usize_of_nat(v___x_242_);
v___x_257_ = ((size_t)1ULL);
v___x_258_ = lean_usize_sub(v___x_256_, v___x_257_);
v___x_259_ = lean_usize_land(v___x_255_, v___x_258_);
v_bkt_260_ = lean_array_uget_borrowed(v_buckets_240_, v___x_259_);
lean_inc(v_bkt_260_);
v___x_261_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_235_, v_a_238_, v_bkt_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_287_; 
lean_inc_ref(v_buckets_240_);
lean_inc(v_size_239_);
v_isSharedCheck_287_ = !lean_is_exclusive(v_m_237_);
if (v_isSharedCheck_287_ == 0)
{
lean_object* v_unused_288_; lean_object* v_unused_289_; 
v_unused_288_ = lean_ctor_get(v_m_237_, 1);
lean_dec(v_unused_288_);
v_unused_289_ = lean_ctor_get(v_m_237_, 0);
lean_dec(v_unused_289_);
v___x_263_ = v_m_237_;
v_isShared_264_ = v_isSharedCheck_287_;
goto v_resetjp_262_;
}
else
{
lean_dec(v_m_237_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_287_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v_size_x27_267_; lean_object* v___x_268_; lean_object* v_buckets_x27_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_265_ = lean_box(0);
v___x_266_ = lean_unsigned_to_nat(1u);
v_size_x27_267_ = lean_nat_add(v_size_239_, v___x_266_);
lean_dec(v_size_239_);
lean_inc(v_bkt_260_);
v___x_268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_268_, 0, v_a_238_);
lean_ctor_set(v___x_268_, 1, v___x_265_);
lean_ctor_set(v___x_268_, 2, v_bkt_260_);
v_buckets_x27_269_ = lean_array_uset(v_buckets_240_, v___x_259_, v___x_268_);
v___x_270_ = lean_unsigned_to_nat(4u);
v___x_271_ = lean_nat_mul(v_size_x27_267_, v___x_270_);
v___x_272_ = lean_unsigned_to_nat(3u);
v___x_273_ = lean_nat_div(v___x_271_, v___x_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_array_get_size(v_buckets_x27_269_);
v___x_275_ = lean_nat_dec_le(v___x_273_, v___x_274_);
lean_dec(v___x_273_);
if (v___x_275_ == 0)
{
lean_object* v_val_276_; lean_object* v___x_278_; 
v_val_276_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_236_, v_buckets_x27_269_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v_val_276_);
lean_ctor_set(v___x_263_, 0, v_size_x27_267_);
v___x_278_ = v___x_263_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_size_x27_267_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_val_276_);
v___x_278_ = v_reuseFailAlloc_281_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_box(v___x_261_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
return v___x_280_;
}
}
else
{
lean_object* v___x_283_; 
lean_dec_ref(v_inst_236_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v_buckets_x27_269_);
lean_ctor_set(v___x_263_, 0, v_size_x27_267_);
v___x_283_ = v___x_263_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v_size_x27_267_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v_buckets_x27_269_);
v___x_283_ = v_reuseFailAlloc_286_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_box(v___x_261_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
return v___x_285_;
}
}
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_dec(v_a_238_);
lean_dec_ref(v_inst_236_);
v___x_290_ = lean_box(v___x_261_);
v___x_291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
lean_ctor_set(v___x_291_, 1, v_m_237_);
return v___x_291_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert(lean_object* v_00_u03b1_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_m_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_size_297_; lean_object* v_buckets_298_; lean_object* v___x_299_; lean_object* v___x_300_; uint8_t v___x_301_; 
v_size_297_ = lean_ctor_get(v_m_295_, 0);
v_buckets_298_ = lean_ctor_get(v_m_295_, 1);
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = lean_array_get_size(v_buckets_298_);
v___x_301_ = lean_nat_dec_lt(v___x_299_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_a_296_);
lean_dec_ref(v_inst_294_);
lean_dec_ref(v_inst_293_);
v___x_302_ = lean_box(v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_m_295_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; uint64_t v___x_307_; uint64_t v___x_308_; uint64_t v_fold_309_; uint64_t v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; size_t v___x_313_; size_t v___x_314_; size_t v___x_315_; size_t v___x_316_; size_t v___x_317_; lean_object* v_bkt_318_; uint8_t v___x_319_; 
lean_inc_ref(v_inst_294_);
lean_inc_n(v_a_296_, 2);
v___x_304_ = lean_apply_1(v_inst_294_, v_a_296_);
v___x_305_ = 32ULL;
v___x_306_ = lean_unbox_uint64(v___x_304_);
v___x_307_ = lean_uint64_shift_right(v___x_306_, v___x_305_);
v___x_308_ = lean_unbox_uint64(v___x_304_);
lean_dec_ref(v___x_304_);
v_fold_309_ = lean_uint64_xor(v___x_308_, v___x_307_);
v___x_310_ = 16ULL;
v___x_311_ = lean_uint64_shift_right(v_fold_309_, v___x_310_);
v___x_312_ = lean_uint64_xor(v_fold_309_, v___x_311_);
v___x_313_ = lean_uint64_to_usize(v___x_312_);
v___x_314_ = lean_usize_of_nat(v___x_300_);
v___x_315_ = ((size_t)1ULL);
v___x_316_ = lean_usize_sub(v___x_314_, v___x_315_);
v___x_317_ = lean_usize_land(v___x_313_, v___x_316_);
v_bkt_318_ = lean_array_uget_borrowed(v_buckets_298_, v___x_317_);
lean_inc(v_bkt_318_);
v___x_319_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_293_, v_a_296_, v_bkt_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_345_; 
lean_inc_ref(v_buckets_298_);
lean_inc(v_size_297_);
v_isSharedCheck_345_ = !lean_is_exclusive(v_m_295_);
if (v_isSharedCheck_345_ == 0)
{
lean_object* v_unused_346_; lean_object* v_unused_347_; 
v_unused_346_ = lean_ctor_get(v_m_295_, 1);
lean_dec(v_unused_346_);
v_unused_347_ = lean_ctor_get(v_m_295_, 0);
lean_dec(v_unused_347_);
v___x_321_ = v_m_295_;
v_isShared_322_ = v_isSharedCheck_345_;
goto v_resetjp_320_;
}
else
{
lean_dec(v_m_295_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_345_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_size_x27_325_; lean_object* v___x_326_; lean_object* v_buckets_x27_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_323_ = lean_box(0);
v___x_324_ = lean_unsigned_to_nat(1u);
v_size_x27_325_ = lean_nat_add(v_size_297_, v___x_324_);
lean_dec(v_size_297_);
lean_inc(v_bkt_318_);
v___x_326_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_326_, 0, v_a_296_);
lean_ctor_set(v___x_326_, 1, v___x_323_);
lean_ctor_set(v___x_326_, 2, v_bkt_318_);
v_buckets_x27_327_ = lean_array_uset(v_buckets_298_, v___x_317_, v___x_326_);
v___x_328_ = lean_unsigned_to_nat(4u);
v___x_329_ = lean_nat_mul(v_size_x27_325_, v___x_328_);
v___x_330_ = lean_unsigned_to_nat(3u);
v___x_331_ = lean_nat_div(v___x_329_, v___x_330_);
lean_dec(v___x_329_);
v___x_332_ = lean_array_get_size(v_buckets_x27_327_);
v___x_333_ = lean_nat_dec_le(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
if (v___x_333_ == 0)
{
lean_object* v_val_334_; lean_object* v___x_336_; 
v_val_334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_294_, v_buckets_x27_327_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v_val_334_);
lean_ctor_set(v___x_321_, 0, v_size_x27_325_);
v___x_336_ = v___x_321_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_size_x27_325_);
lean_ctor_set(v_reuseFailAlloc_339_, 1, v_val_334_);
v___x_336_ = v_reuseFailAlloc_339_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_box(v___x_319_);
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v___x_336_);
return v___x_338_;
}
}
else
{
lean_object* v___x_341_; 
lean_dec_ref(v_inst_294_);
if (v_isShared_322_ == 0)
{
lean_ctor_set(v___x_321_, 1, v_buckets_x27_327_);
lean_ctor_set(v___x_321_, 0, v_size_x27_325_);
v___x_341_ = v___x_321_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_size_x27_325_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_buckets_x27_327_);
v___x_341_ = v_reuseFailAlloc_344_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
lean_object* v___x_342_; lean_object* v___x_343_; 
v___x_342_ = lean_box(v___x_319_);
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___x_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
}
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_a_296_);
lean_dec_ref(v_inst_294_);
v___x_348_ = lean_box(v___x_319_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v_m_295_);
return v___x_349_;
}
}
}
}
uint8_t l_Std_HashSet_Raw_contains___redArg(lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_m_352_, lean_object* v_a_353_){
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
LEAN_EXPORT void l_Std_HashSet_Raw_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_350_ = stack[0].m_obj;
lean_object* v_inst_351_ = stack[1].m_obj;
lean_object* v_m_352_ = stack[2].m_obj;
lean_object* v_a_353_ = stack[3].m_obj;
uint8_t v_res_359_;
v_res_359_ = l_Std_HashSet_Raw_contains___redArg(v_inst_350_, v_inst_351_, v_m_352_, v_a_353_);
stack->m_num = v_res_359_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___redArg___boxed(lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v_m_362_, lean_object* v_a_363_){
_start:
{
uint8_t v_res_364_; lean_object* v_r_365_; 
v_res_364_ = l_Std_HashSet_Raw_contains___redArg(v_inst_360_, v_inst_361_, v_m_362_, v_a_363_);
lean_dec_ref(v_m_362_);
v_r_365_ = lean_box(v_res_364_);
return v_r_365_;
}
}
uint8_t l_Std_HashSet_Raw_contains(lean_object* v_00_u03b1_366_, lean_object* v_inst_367_, lean_object* v_inst_368_, lean_object* v_m_369_, lean_object* v_a_370_){
_start:
{
lean_object* v_buckets_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_buckets_371_ = lean_ctor_get(v_m_369_, 1);
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_array_get_size(v_buckets_371_);
v___x_374_ = lean_nat_dec_lt(v___x_372_, v___x_373_);
if (v___x_374_ == 0)
{
lean_dec(v_a_370_);
lean_dec_ref(v_inst_368_);
lean_dec_ref(v_inst_367_);
return v___x_374_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_367_, v_inst_368_, v_m_369_, v_a_370_);
return v___x_375_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_367_ = stack[1].m_obj;
lean_object* v_inst_368_ = stack[2].m_obj;
lean_object* v_m_369_ = stack[3].m_obj;
lean_object* v_a_370_ = stack[4].m_obj;
uint8_t v_res_376_;
v_res_376_ = l_Std_HashSet_Raw_contains(lean_box(0), v_inst_367_, v_inst_368_, v_m_369_, v_a_370_);
stack->m_num = v_res_376_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___boxed(lean_object* v_00_u03b1_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_m_380_, lean_object* v_a_381_){
_start:
{
uint8_t v_res_382_; lean_object* v_r_383_; 
v_res_382_ = l_Std_HashSet_Raw_contains(v_00_u03b1_377_, v_inst_378_, v_inst_379_, v_m_380_, v_a_381_);
lean_dec_ref(v_m_380_);
v_r_383_ = lean_box(v_res_382_);
return v_r_383_;
}
}
lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___redArg(){
_start:
{
lean_object* v___x_385_; 
v___x_385_ = lean_box(0);
return v___x_385_;
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_386_;
v_res_386_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___redArg();
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___redArg___boxed(lean_object* v___dummy_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___redArg();
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_389_, lean_object* v_inst_390_, lean_object* v_inst_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = lean_box(0);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_393_, lean_object* v_inst_394_, lean_object* v_inst_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_393_, v_inst_394_, v_inst_395_);
lean_dec_ref(v_inst_395_);
lean_dec_ref(v_inst_394_);
return v_res_396_;
}
}
uint8_t l_Std_HashSet_Raw_instDecidableMem___redArg(lean_object* v_inst_397_, lean_object* v_inst_398_, lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
uint8_t v___x_401_; 
v___x_401_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_397_, v_inst_398_, v_m_399_, v_a_400_);
return v___x_401_;
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_397_ = stack[0].m_obj;
lean_object* v_inst_398_ = stack[1].m_obj;
lean_object* v_m_399_ = stack[2].m_obj;
lean_object* v_a_400_ = stack[3].m_obj;
uint8_t v_res_402_;
v_res_402_ = l_Std_HashSet_Raw_instDecidableMem___redArg(v_inst_397_, v_inst_398_, v_m_399_, v_a_400_);
stack->m_num = v_res_402_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_m_405_, lean_object* v_a_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_Std_HashSet_Raw_instDecidableMem___redArg(v_inst_403_, v_inst_404_, v_m_405_, v_a_406_);
lean_dec_ref(v_m_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
uint8_t l_Std_HashSet_Raw_instDecidableMem(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_m_412_, lean_object* v_a_413_){
_start:
{
uint8_t v___x_414_; 
v___x_414_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_410_, v_inst_411_, v_m_412_, v_a_413_);
return v___x_414_;
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_410_ = stack[1].m_obj;
lean_object* v_inst_411_ = stack[2].m_obj;
lean_object* v_m_412_ = stack[3].m_obj;
lean_object* v_a_413_ = stack[4].m_obj;
uint8_t v_res_415_;
v_res_415_ = l_Std_HashSet_Raw_instDecidableMem(lean_box(0), v_inst_410_, v_inst_411_, v_m_412_, v_a_413_);
stack->m_num = v_res_415_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_m_419_, lean_object* v_a_420_){
_start:
{
uint8_t v_res_421_; lean_object* v_r_422_; 
v_res_421_ = l_Std_HashSet_Raw_instDecidableMem(v_00_u03b1_416_, v_inst_417_, v_inst_418_, v_m_419_, v_a_420_);
lean_dec_ref(v_m_419_);
v_r_422_ = lean_box(v_res_421_);
return v_r_422_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase___redArg(lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_m_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_buckets_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_buckets_427_ = lean_ctor_get(v_m_425_, 1);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_array_get_size(v_buckets_427_);
v___x_430_ = lean_nat_dec_lt(v___x_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_dec(v_a_426_);
lean_dec_ref(v_inst_424_);
lean_dec_ref(v_inst_423_);
return v_m_425_;
}
else
{
lean_object* v___x_431_; 
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_423_, v_inst_424_, v_m_425_, v_a_426_);
return v___x_431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase(lean_object* v_00_u03b1_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_m_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_buckets_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_buckets_437_ = lean_ctor_get(v_m_435_, 1);
v___x_438_ = lean_unsigned_to_nat(0u);
v___x_439_ = lean_array_get_size(v_buckets_437_);
v___x_440_ = lean_nat_dec_lt(v___x_438_, v___x_439_);
if (v___x_440_ == 0)
{
lean_dec(v_a_436_);
lean_dec_ref(v_inst_434_);
lean_dec_ref(v_inst_433_);
return v_m_435_;
}
else
{
lean_object* v___x_441_; 
v___x_441_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_433_, v_inst_434_, v_m_435_, v_a_436_);
return v___x_441_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg(lean_object* v_m_442_){
_start:
{
lean_object* v_size_443_; 
v_size_443_ = lean_ctor_get(v_m_442_, 0);
lean_inc(v_size_443_);
return v_size_443_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg___boxed(lean_object* v_m_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_HashSet_Raw_size___redArg(v_m_444_);
lean_dec_ref(v_m_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size(lean_object* v_00_u03b1_446_, lean_object* v_m_447_){
_start:
{
lean_object* v_size_448_; 
v_size_448_ = lean_ctor_get(v_m_447_, 0);
lean_inc(v_size_448_);
return v_size_448_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___boxed(lean_object* v_00_u03b1_449_, lean_object* v_m_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l_Std_HashSet_Raw_size(v_00_u03b1_449_, v_m_450_);
lean_dec_ref(v_m_450_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg(lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_m_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_buckets_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_buckets_456_ = lean_ctor_get(v_m_454_, 1);
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_458_ = lean_array_get_size(v_buckets_456_);
v___x_459_ = lean_nat_dec_lt(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; 
lean_dec(v_a_455_);
lean_dec_ref(v_inst_453_);
lean_dec_ref(v_inst_452_);
v___x_460_ = lean_box(0);
return v___x_460_;
}
else
{
lean_object* v___x_461_; 
v___x_461_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_452_, v_inst_453_, v_m_454_, v_a_455_);
return v___x_461_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg___boxed(lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_m_464_, lean_object* v_a_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_HashSet_Raw_get_x3f___redArg(v_inst_462_, v_inst_463_, v_m_464_, v_a_465_);
lean_dec_ref(v_m_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f(lean_object* v_00_u03b1_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_m_470_, lean_object* v_a_471_){
_start:
{
lean_object* v_buckets_472_; lean_object* v___x_473_; lean_object* v___x_474_; uint8_t v___x_475_; 
v_buckets_472_ = lean_ctor_get(v_m_470_, 1);
v___x_473_ = lean_unsigned_to_nat(0u);
v___x_474_ = lean_array_get_size(v_buckets_472_);
v___x_475_ = lean_nat_dec_lt(v___x_473_, v___x_474_);
if (v___x_475_ == 0)
{
lean_object* v___x_476_; 
lean_dec(v_a_471_);
lean_dec_ref(v_inst_469_);
lean_dec_ref(v_inst_468_);
v___x_476_ = lean_box(0);
return v___x_476_;
}
else
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_468_, v_inst_469_, v_m_470_, v_a_471_);
return v___x_477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___boxed(lean_object* v_00_u03b1_478_, lean_object* v_inst_479_, lean_object* v_inst_480_, lean_object* v_m_481_, lean_object* v_a_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_HashSet_Raw_get_x3f(v_00_u03b1_478_, v_inst_479_, v_inst_480_, v_m_481_, v_a_482_);
lean_dec_ref(v_m_481_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg(lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_m_486_, lean_object* v_a_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_484_, v_inst_485_, v_m_486_, v_a_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg___boxed(lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_m_491_, lean_object* v_a_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_HashSet_Raw_get___redArg(v_inst_489_, v_inst_490_, v_m_491_, v_a_492_);
lean_dec_ref(v_m_491_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get(lean_object* v_00_u03b1_494_, lean_object* v_inst_495_, lean_object* v_inst_496_, lean_object* v_m_497_, lean_object* v_a_498_, lean_object* v_h_499_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_495_, v_inst_496_, v_m_497_, v_a_498_);
return v___x_500_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___boxed(lean_object* v_00_u03b1_501_, lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_m_504_, lean_object* v_a_505_, lean_object* v_h_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_HashSet_Raw_get(v_00_u03b1_501_, v_inst_502_, v_inst_503_, v_m_504_, v_a_505_, v_h_506_);
lean_dec_ref(v_m_504_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg(lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_m_510_, lean_object* v_a_511_, lean_object* v_fallback_512_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg___boxed(lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_m_520_, lean_object* v_a_521_, lean_object* v_fallback_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Std_HashSet_Raw_getD___redArg(v_inst_518_, v_inst_519_, v_m_520_, v_a_521_, v_fallback_522_);
lean_dec(v_fallback_522_);
lean_dec_ref(v_m_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD(lean_object* v_00_u03b1_524_, lean_object* v_inst_525_, lean_object* v_inst_526_, lean_object* v_m_527_, lean_object* v_a_528_, lean_object* v_fallback_529_){
_start:
{
lean_object* v_buckets_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_buckets_530_ = lean_ctor_get(v_m_527_, 1);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_array_get_size(v_buckets_530_);
v___x_533_ = lean_nat_dec_lt(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec(v_a_528_);
lean_dec_ref(v_inst_526_);
lean_dec_ref(v_inst_525_);
lean_inc(v_fallback_529_);
return v_fallback_529_;
}
else
{
lean_object* v___x_534_; 
v___x_534_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_525_, v_inst_526_, v_m_527_, v_a_528_, v_fallback_529_);
return v___x_534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___boxed(lean_object* v_00_u03b1_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_m_538_, lean_object* v_a_539_, lean_object* v_fallback_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_HashSet_Raw_getD(v_00_u03b1_535_, v_inst_536_, v_inst_537_, v_m_538_, v_a_539_, v_fallback_540_);
lean_dec(v_fallback_540_);
lean_dec_ref(v_m_538_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg(lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_inst_544_, lean_object* v_m_545_, lean_object* v_a_546_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg___boxed(lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_inst_554_, lean_object* v_m_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_HashSet_Raw_get_x21___redArg(v_inst_552_, v_inst_553_, v_inst_554_, v_m_555_, v_a_556_);
lean_dec_ref(v_m_555_);
lean_dec(v_inst_554_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21(lean_object* v_00_u03b1_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_inst_561_, lean_object* v_m_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_buckets_564_; lean_object* v___x_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_buckets_564_ = lean_ctor_get(v_m_562_, 1);
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_array_get_size(v_buckets_564_);
v___x_567_ = lean_nat_dec_lt(v___x_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_dec(v_a_563_);
lean_dec_ref(v_inst_560_);
lean_dec_ref(v_inst_559_);
lean_inc(v_inst_561_);
return v_inst_561_;
}
else
{
lean_object* v___x_568_; 
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_559_, v_inst_560_, v_inst_561_, v_m_562_, v_a_563_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___boxed(lean_object* v_00_u03b1_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_m_573_, lean_object* v_a_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Std_HashSet_Raw_get_x21(v_00_u03b1_569_, v_inst_570_, v_inst_571_, v_inst_572_, v_m_573_, v_a_574_);
lean_dec_ref(v_m_573_);
lean_dec(v_inst_572_);
return v_res_575_;
}
}
uint8_t l_Std_HashSet_Raw_isEmpty___redArg(lean_object* v_m_576_){
_start:
{
lean_object* v_size_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v_size_577_ = lean_ctor_get(v_m_576_, 0);
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_nat_dec_eq(v_size_577_, v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_576_ = stack[0].m_obj;
uint8_t v_res_580_;
v_res_580_ = l_Std_HashSet_Raw_isEmpty___redArg(v_m_576_);
stack->m_num = v_res_580_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___redArg___boxed(lean_object* v_m_581_){
_start:
{
uint8_t v_res_582_; lean_object* v_r_583_; 
v_res_582_ = l_Std_HashSet_Raw_isEmpty___redArg(v_m_581_);
lean_dec_ref(v_m_581_);
v_r_583_ = lean_box(v_res_582_);
return v_r_583_;
}
}
uint8_t l_Std_HashSet_Raw_isEmpty(lean_object* v_00_u03b1_584_, lean_object* v_m_585_){
_start:
{
lean_object* v_size_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v_size_586_ = lean_ctor_get(v_m_585_, 0);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_nat_dec_eq(v_size_586_, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_585_ = stack[1].m_obj;
uint8_t v_res_589_;
v_res_589_ = l_Std_HashSet_Raw_isEmpty(lean_box(0), v_m_585_);
stack->m_num = v_res_589_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_590_, lean_object* v_m_591_){
_start:
{
uint8_t v_res_592_; lean_object* v_r_593_; 
v_res_592_ = l_Std_HashSet_Raw_isEmpty(v_00_u03b1_590_, v_m_591_);
lean_dec_ref(v_m_591_);
v_r_593_ = lean_box(v_res_592_);
return v_r_593_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__0(lean_object* v_a_594_, lean_object* v_b_595_, lean_object* v_d_596_){
_start:
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_597_, 0, v_a_594_);
lean_ctor_set(v___x_597_, 1, v_d_596_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__1(lean_object* v___x_598_, lean_object* v___f_599_, lean_object* v_l_600_, lean_object* v_acc_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_598_, v___f_599_, v_acc_601_, v_l_600_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg(lean_object* v_m_626_){
_start:
{
lean_object* v___x_627_; lean_object* v_buckets_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v___x_627_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_628_ = lean_ctor_get(v_m_626_, 1);
lean_inc_ref(v_buckets_628_);
lean_dec_ref(v_m_626_);
v___x_629_ = lean_box(0);
v___x_630_ = lean_array_get_size(v_buckets_628_);
v___x_631_ = lean_unsigned_to_nat(0u);
v___x_632_ = lean_nat_dec_lt(v___x_631_, v___x_630_);
if (v___x_632_ == 0)
{
lean_dec_ref(v_buckets_628_);
return v___x_629_;
}
else
{
lean_object* v___f_633_; size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; 
v___f_633_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__11));
v___x_634_ = lean_usize_of_nat(v___x_630_);
v___x_635_ = ((size_t)0ULL);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_627_, v___f_633_, v_buckets_628_, v___x_634_, v___x_635_, v___x_629_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList(lean_object* v_00_u03b1_637_, lean_object* v_m_638_){
_start:
{
lean_object* v___x_639_; lean_object* v_buckets_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_639_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_640_ = lean_ctor_get(v_m_638_, 1);
lean_inc_ref(v_buckets_640_);
lean_dec_ref(v_m_638_);
v___x_641_ = lean_box(0);
v___x_642_ = lean_array_get_size(v_buckets_640_);
v___x_643_ = lean_unsigned_to_nat(0u);
v___x_644_ = lean_nat_dec_lt(v___x_643_, v___x_642_);
if (v___x_644_ == 0)
{
lean_dec_ref(v_buckets_640_);
return v___x_641_;
}
else
{
lean_object* v___f_645_; size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
v___f_645_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__11));
v___x_646_ = lean_usize_of_nat(v___x_642_);
v___x_647_ = ((size_t)0ULL);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_639_, v___f_645_, v_buckets_640_, v___x_646_, v___x_647_, v___x_641_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList___redArg(lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_l_655_){
_start:
{
lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_656_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
v___x_657_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_657_ == 0)
{
lean_dec(v_l_655_);
lean_dec_ref(v_inst_654_);
lean_dec_ref(v_inst_653_);
return v___x_656_;
}
else
{
lean_object* v___f_658_; lean_object* v___x_659_; 
v___f_658_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_659_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_658_, v_inst_653_, v_inst_654_, v___x_656_, v_l_655_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList(lean_object* v_00_u03b1_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_l_663_){
_start:
{
lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_664_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
v___x_665_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_665_ == 0)
{
lean_dec(v_l_663_);
lean_dec_ref(v_inst_662_);
lean_dec_ref(v_inst_661_);
return v___x_664_;
}
else
{
lean_object* v___f_666_; lean_object* v___x_667_; 
v___f_666_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_666_, v_inst_661_, v_inst_662_, v___x_664_, v_l_663_);
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__0(lean_object* v_f_668_, lean_object* v_b_669_, lean_object* v_a_670_, lean_object* v_x_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = lean_apply_2(v_f_668_, v_b_669_, v_a_670_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__1(lean_object* v_inst_673_, lean_object* v___f_674_, lean_object* v_acc_675_, lean_object* v_l_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_673_, v___f_674_, v_acc_675_, v_l_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg(lean_object* v_inst_678_, lean_object* v_f_679_, lean_object* v_init_680_, lean_object* v_b_681_){
_start:
{
lean_object* v_toApplicative_682_; lean_object* v_buckets_683_; lean_object* v_toPure_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_toApplicative_682_ = lean_ctor_get(v_inst_678_, 0);
v_buckets_683_ = lean_ctor_get(v_b_681_, 1);
lean_inc_ref(v_buckets_683_);
lean_dec_ref(v_b_681_);
v_toPure_684_ = lean_ctor_get(v_toApplicative_682_, 1);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_array_get_size(v_buckets_683_);
v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; 
lean_inc(v_toPure_684_);
lean_dec_ref(v_buckets_683_);
lean_dec(v_f_679_);
lean_dec_ref(v_inst_678_);
v___x_688_ = lean_apply_2(v_toPure_684_, lean_box(0), v_init_680_);
return v___x_688_;
}
else
{
lean_object* v___f_689_; lean_object* v___f_690_; size_t v___x_691_; size_t v___x_692_; lean_object* v___x_693_; 
v___f_689_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_689_, 0, v_f_679_);
lean_inc_ref(v_inst_678_);
v___f_690_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_690_, 0, v_inst_678_);
lean_closure_set(v___f_690_, 1, v___f_689_);
v___x_691_ = ((size_t)0ULL);
v___x_692_ = lean_usize_of_nat(v___x_686_);
v___x_693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_678_, v___f_690_, v_buckets_683_, v___x_691_, v___x_692_, v_init_680_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM(lean_object* v_00_u03b1_694_, lean_object* v_m_695_, lean_object* v_inst_696_, lean_object* v_00_u03b2_697_, lean_object* v_f_698_, lean_object* v_init_699_, lean_object* v_b_700_){
_start:
{
lean_object* v_toApplicative_701_; lean_object* v_buckets_702_; lean_object* v_toPure_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_toApplicative_701_ = lean_ctor_get(v_inst_696_, 0);
v_buckets_702_ = lean_ctor_get(v_b_700_, 1);
lean_inc_ref(v_buckets_702_);
lean_dec_ref(v_b_700_);
v_toPure_703_ = lean_ctor_get(v_toApplicative_701_, 1);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_array_get_size(v_buckets_702_);
v___x_706_ = lean_nat_dec_lt(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
lean_inc(v_toPure_703_);
lean_dec_ref(v_buckets_702_);
lean_dec(v_f_698_);
lean_dec_ref(v_inst_696_);
v___x_707_ = lean_apply_2(v_toPure_703_, lean_box(0), v_init_699_);
return v___x_707_;
}
else
{
lean_object* v___f_708_; lean_object* v___f_709_; size_t v___x_710_; size_t v___x_711_; lean_object* v___x_712_; 
v___f_708_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_708_, 0, v_f_698_);
lean_inc_ref(v_inst_696_);
v___f_709_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_709_, 0, v_inst_696_);
lean_closure_set(v___f_709_, 1, v___f_708_);
v___x_710_ = ((size_t)0ULL);
v___x_711_ = lean_usize_of_nat(v___x_705_);
v___x_712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_696_, v___f_709_, v_buckets_702_, v___x_710_, v___x_711_, v_init_699_);
return v___x_712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__0(lean_object* v_f_713_, lean_object* v_x1_714_, lean_object* v_x2_715_, lean_object* v_x3_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = lean_apply_2(v_f_713_, v_x1_714_, v_x2_715_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__1(lean_object* v___x_718_, lean_object* v___f_719_, lean_object* v_acc_720_, lean_object* v_l_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_718_, v___f_719_, v_acc_720_, v_l_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg(lean_object* v_f_723_, lean_object* v_init_724_, lean_object* v_m_725_){
_start:
{
lean_object* v___x_726_; lean_object* v_buckets_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_726_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_727_ = lean_ctor_get(v_m_725_, 1);
lean_inc_ref(v_buckets_727_);
lean_dec_ref(v_m_725_);
v___x_728_ = lean_unsigned_to_nat(0u);
v___x_729_ = lean_array_get_size(v_buckets_727_);
v___x_730_ = lean_nat_dec_lt(v___x_728_, v___x_729_);
if (v___x_730_ == 0)
{
lean_dec_ref(v_buckets_727_);
lean_dec(v_f_723_);
return v_init_724_;
}
else
{
lean_object* v___f_731_; lean_object* v___f_732_; size_t v___x_733_; size_t v___x_734_; lean_object* v___x_735_; 
v___f_731_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_731_, 0, v_f_723_);
v___f_732_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_732_, 0, v___x_726_);
lean_closure_set(v___f_732_, 1, v___f_731_);
v___x_733_ = ((size_t)0ULL);
v___x_734_ = lean_usize_of_nat(v___x_729_);
v___x_735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_726_, v___f_732_, v_buckets_727_, v___x_733_, v___x_734_, v_init_724_);
return v___x_735_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold(lean_object* v_00_u03b1_736_, lean_object* v_00_u03b2_737_, lean_object* v_f_738_, lean_object* v_init_739_, lean_object* v_m_740_){
_start:
{
lean_object* v___x_741_; lean_object* v_buckets_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_741_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_742_ = lean_ctor_get(v_m_740_, 1);
lean_inc_ref(v_buckets_742_);
lean_dec_ref(v_m_740_);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_array_get_size(v_buckets_742_);
v___x_745_ = lean_nat_dec_lt(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_dec_ref(v_buckets_742_);
lean_dec(v_f_738_);
return v_init_739_;
}
else
{
lean_object* v___f_746_; lean_object* v___f_747_; size_t v___x_748_; size_t v___x_749_; lean_object* v___x_750_; 
v___f_746_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_746_, 0, v_f_738_);
v___f_747_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_747_, 0, v___x_741_);
lean_closure_set(v___f_747_, 1, v___f_746_);
v___x_748_ = ((size_t)0ULL);
v___x_749_ = lean_usize_of_nat(v___x_744_);
v___x_750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_741_, v___f_747_, v_buckets_742_, v___x_748_, v___x_749_, v_init_739_);
return v___x_750_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__0(lean_object* v_f_751_, lean_object* v_x_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = lean_apply_1(v_f_751_, v___y_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__1(lean_object* v_inst_756_, lean_object* v___f_757_, lean_object* v_x_758_, lean_object* v___y_759_){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = lean_box(0);
v___x_761_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_756_, v___f_757_, v___x_760_, v___y_759_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg(lean_object* v_inst_762_, lean_object* v_f_763_, lean_object* v_b_764_){
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
v___f_773_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_773_, 0, v_f_763_);
lean_inc_ref(v_inst_762_);
v___f_774_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_774_, 0, v_inst_762_);
lean_closure_set(v___f_774_, 1, v___f_773_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = lean_usize_of_nat(v___x_769_);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_762_, v___f_774_, v_buckets_766_, v___x_775_, v___x_776_, v___x_770_);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM(lean_object* v_00_u03b1_778_, lean_object* v_m_779_, lean_object* v_inst_780_, lean_object* v_f_781_, lean_object* v_b_782_){
_start:
{
lean_object* v_toApplicative_783_; lean_object* v_buckets_784_; lean_object* v_toPure_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; uint8_t v___x_789_; 
v_toApplicative_783_ = lean_ctor_get(v_inst_780_, 0);
v_buckets_784_ = lean_ctor_get(v_b_782_, 1);
lean_inc_ref(v_buckets_784_);
lean_dec_ref(v_b_782_);
v_toPure_785_ = lean_ctor_get(v_toApplicative_783_, 1);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_array_get_size(v_buckets_784_);
v___x_788_ = lean_box(0);
v___x_789_ = lean_nat_dec_lt(v___x_786_, v___x_787_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_inc(v_toPure_785_);
lean_dec_ref(v_buckets_784_);
lean_dec(v_f_781_);
lean_dec_ref(v_inst_780_);
v___x_790_ = lean_apply_2(v_toPure_785_, lean_box(0), v___x_788_);
return v___x_790_;
}
else
{
lean_object* v___f_791_; lean_object* v___f_792_; size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
v___f_791_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_791_, 0, v_f_781_);
lean_inc_ref(v_inst_780_);
v___f_792_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_792_, 0, v_inst_780_);
lean_closure_set(v___f_792_, 1, v___f_791_);
v___x_793_ = ((size_t)0ULL);
v___x_794_ = lean_usize_of_nat(v___x_787_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_780_, v___f_792_, v_buckets_784_, v___x_793_, v___x_794_, v___x_788_);
return v___x_795_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__0(lean_object* v_f_796_, lean_object* v_a_797_, lean_object* v_x_798_, lean_object* v_acc_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = lean_apply_2(v_f_796_, v_a_797_, v_acc_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__1(lean_object* v_inst_801_, lean_object* v___f_802_, lean_object* v_a_803_, lean_object* v_x_804_, lean_object* v___y_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_801_, v___f_802_, v_a_803_, v___y_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg(lean_object* v_inst_807_, lean_object* v_f_808_, lean_object* v_init_809_, lean_object* v_b_810_){
_start:
{
lean_object* v_buckets_811_; lean_object* v___f_812_; lean_object* v___f_813_; size_t v_sz_814_; size_t v___x_815_; lean_object* v___x_816_; 
v_buckets_811_ = lean_ctor_get(v_b_810_, 1);
lean_inc_ref(v_buckets_811_);
lean_dec_ref(v_b_810_);
v___f_812_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_812_, 0, v_f_808_);
lean_inc_ref(v_inst_807_);
v___f_813_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_813_, 0, v_inst_807_);
lean_closure_set(v___f_813_, 1, v___f_812_);
v_sz_814_ = lean_array_size(v_buckets_811_);
v___x_815_ = ((size_t)0ULL);
v___x_816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_807_, v_buckets_811_, v___f_813_, v_sz_814_, v___x_815_, v_init_809_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn(lean_object* v_00_u03b1_817_, lean_object* v_m_818_, lean_object* v_inst_819_, lean_object* v_00_u03b2_820_, lean_object* v_f_821_, lean_object* v_init_822_, lean_object* v_b_823_){
_start:
{
lean_object* v_buckets_824_; lean_object* v___f_825_; lean_object* v___f_826_; size_t v_sz_827_; size_t v___x_828_; lean_object* v___x_829_; 
v_buckets_824_ = lean_ctor_get(v_b_823_, 1);
lean_inc_ref(v_buckets_824_);
lean_dec_ref(v_b_823_);
v___f_825_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_825_, 0, v_f_821_);
lean_inc_ref(v_inst_819_);
v___f_826_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_826_, 0, v_inst_819_);
lean_closure_set(v___f_826_, 1, v___f_825_);
v_sz_827_ = lean_array_size(v_buckets_824_);
v___x_828_ = ((size_t)0ULL);
v___x_829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_819_, v_buckets_824_, v___f_826_, v_sz_827_, v___x_828_, v_init_822_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2(lean_object* v_inst_830_, lean_object* v_m_831_, lean_object* v_f_832_){
_start:
{
lean_object* v_toApplicative_833_; lean_object* v_buckets_834_; lean_object* v_toPure_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_toApplicative_833_ = lean_ctor_get(v_inst_830_, 0);
v_buckets_834_ = lean_ctor_get(v_m_831_, 1);
lean_inc_ref(v_buckets_834_);
lean_dec_ref(v_m_831_);
v_toPure_835_ = lean_ctor_get(v_toApplicative_833_, 1);
v___x_836_ = lean_unsigned_to_nat(0u);
v___x_837_ = lean_array_get_size(v_buckets_834_);
v___x_838_ = lean_box(0);
v___x_839_ = lean_nat_dec_lt(v___x_836_, v___x_837_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
lean_inc(v_toPure_835_);
lean_dec_ref(v_buckets_834_);
lean_dec(v_f_832_);
lean_dec_ref(v_inst_830_);
v___x_840_ = lean_apply_2(v_toPure_835_, lean_box(0), v___x_838_);
return v___x_840_;
}
else
{
lean_object* v___f_841_; lean_object* v___f_842_; size_t v___x_843_; size_t v___x_844_; lean_object* v___x_845_; 
v___f_841_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_841_, 0, v_f_832_);
lean_inc_ref(v_inst_830_);
v___f_842_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_842_, 0, v_inst_830_);
lean_closure_set(v___f_842_, 1, v___f_841_);
v___x_843_ = ((size_t)0ULL);
v___x_844_ = lean_usize_of_nat(v___x_837_);
v___x_845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_830_, v___f_842_, v_buckets_834_, v___x_843_, v___x_844_, v___x_838_);
return v___x_845_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_846_){
_start:
{
lean_object* v___f_847_; 
v___f_847_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_847_, 0, v_inst_846_);
return v___f_847_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_848_, lean_object* v_m_849_, lean_object* v_inst_850_){
_start:
{
lean_object* v___f_851_; 
v___f_851_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_851_, 0, v_inst_850_);
return v___f_851_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2(lean_object* v_inst_852_, lean_object* v_00_u03b2_853_, lean_object* v_m_854_, lean_object* v_init_855_, lean_object* v_f_856_){
_start:
{
lean_object* v_buckets_857_; lean_object* v___f_858_; lean_object* v___f_859_; size_t v_sz_860_; size_t v___x_861_; lean_object* v___x_862_; 
v_buckets_857_ = lean_ctor_get(v_m_854_, 1);
lean_inc_ref(v_buckets_857_);
lean_dec_ref(v_m_854_);
v___f_858_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_858_, 0, v_f_856_);
lean_inc_ref(v_inst_852_);
v___f_859_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__1), 5, 2);
lean_closure_set(v___f_859_, 0, v_inst_852_);
lean_closure_set(v___f_859_, 1, v___f_858_);
v_sz_860_ = lean_array_size(v_buckets_857_);
v___x_861_ = ((size_t)0ULL);
v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_852_, v_buckets_857_, v___f_859_, v_sz_860_, v___x_861_, v_init_855_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_863_){
_start:
{
lean_object* v___f_864_; 
v___f_864_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_864_, 0, v_inst_863_);
return v___f_864_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_865_, lean_object* v_m_866_, lean_object* v_inst_867_){
_start:
{
lean_object* v___f_868_; 
v___f_868_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_868_, 0, v_inst_867_);
return v___f_868_;
}
}
uint8_t l_Std_HashSet_Raw_filter___redArg___lam__0(lean_object* v_f_869_, lean_object* v_a_870_, lean_object* v_x_871_){
_start:
{
lean_object* v___x_872_; uint8_t v___x_873_; 
v___x_872_ = lean_apply_1(v_f_869_, v_a_870_);
v___x_873_ = lean_unbox(v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_filter___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_869_ = stack[0].m_obj;
lean_object* v_a_870_ = stack[1].m_obj;
lean_object* v_x_871_ = stack[2].m_obj;
uint8_t v_res_874_;
v_res_874_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_869_, v_a_870_, v_x_871_);
stack->m_num = v_res_874_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_875_, lean_object* v_a_876_, lean_object* v_x_877_){
_start:
{
uint8_t v_res_878_; lean_object* v_r_879_; 
v_res_878_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_875_, v_a_876_, v_x_877_);
v_r_879_ = lean_box(v_res_878_);
return v_r_879_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg(lean_object* v_f_880_, lean_object* v_m_881_){
_start:
{
lean_object* v_buckets_882_; lean_object* v___x_883_; lean_object* v___x_884_; uint8_t v___x_885_; 
v_buckets_882_ = lean_ctor_get(v_m_881_, 1);
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_array_get_size(v_buckets_882_);
v___x_885_ = lean_nat_dec_lt(v___x_883_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
lean_dec_ref(v_m_881_);
lean_dec_ref(v_f_880_);
v___x_886_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
return v___x_886_;
}
else
{
lean_object* v___f_887_; lean_object* v___x_888_; 
v___f_887_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_887_, 0, v_f_880_);
v___x_888_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_887_, v_m_881_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter(lean_object* v_00_u03b1_889_, lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_f_892_, lean_object* v_m_893_){
_start:
{
lean_object* v_buckets_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_buckets_894_ = lean_ctor_get(v_m_893_, 1);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_array_get_size(v_buckets_894_);
v___x_897_ = lean_nat_dec_lt(v___x_895_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_dec_ref(v_m_893_);
lean_dec_ref(v_f_892_);
v___x_898_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
return v___x_898_;
}
else
{
lean_object* v___f_899_; lean_object* v___x_900_; 
v___f_899_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_899_, 0, v_f_892_);
v___x_900_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_899_, v_m_893_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___boxed(lean_object* v_00_u03b1_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_f_904_, lean_object* v_m_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Std_HashSet_Raw_filter(v_00_u03b1_901_, v_inst_902_, v_inst_903_, v_f_904_, v_m_905_);
lean_dec_ref(v_inst_903_);
lean_dec_ref(v_inst_902_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__0(lean_object* v_x1_907_, lean_object* v_x2_908_, lean_object* v_x3_909_){
_start:
{
lean_object* v___x_910_; 
v___x_910_ = lean_array_push(v_x1_907_, v_x2_908_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__1(lean_object* v___x_911_, lean_object* v___f_912_, lean_object* v_acc_913_, lean_object* v_l_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_911_, v___f_912_, v_acc_913_, v_l_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg(lean_object* v_m_920_){
_start:
{
lean_object* v_size_921_; lean_object* v_buckets_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_size_921_ = lean_ctor_get(v_m_920_, 0);
lean_inc(v_size_921_);
v_buckets_922_ = lean_ctor_get(v_m_920_, 1);
lean_inc_ref(v_buckets_922_);
lean_dec_ref(v_m_920_);
v___x_923_ = lean_mk_empty_array_with_capacity(v_size_921_);
lean_dec(v_size_921_);
v___x_924_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_925_ = lean_unsigned_to_nat(0u);
v___x_926_ = lean_array_get_size(v_buckets_922_);
v___x_927_ = lean_nat_dec_lt(v___x_925_, v___x_926_);
if (v___x_927_ == 0)
{
lean_dec_ref(v_buckets_922_);
return v___x_923_;
}
else
{
lean_object* v___f_928_; size_t v___x_929_; size_t v___x_930_; lean_object* v___x_931_; 
v___f_928_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_929_ = ((size_t)0ULL);
v___x_930_ = lean_usize_of_nat(v___x_926_);
v___x_931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_924_, v___f_928_, v_buckets_922_, v___x_929_, v___x_930_, v___x_923_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray(lean_object* v_00_u03b1_932_, lean_object* v_m_933_){
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
v___x_937_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
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
v___f_941_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__1));
v___x_942_ = ((size_t)0ULL);
v___x_943_ = lean_usize_of_nat(v___x_939_);
v___x_944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_937_, v___f_941_, v_buckets_935_, v___x_942_, v___x_943_, v___x_936_);
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__0(lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_a_947_, lean_object* v_b_948_, lean_object* v_acc_949_){
_start:
{
lean_object* v_r_950_; lean_object* v___x_951_; 
v_r_950_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_945_, v_inst_946_, v_acc_949_, v_a_947_, v_b_948_);
v___x_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_951_, 0, v_r_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__1(lean_object* v___x_952_, lean_object* v___f_953_, lean_object* v_a_954_, lean_object* v_x_955_, lean_object* v___y_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_952_, v___f_953_, v_a_954_, v___y_956_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg(lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_m_u2081_962_, lean_object* v_m_u2082_963_){
_start:
{
lean_object* v_size_964_; lean_object* v_buckets_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_size_964_ = lean_ctor_get(v_m_u2081_962_, 0);
v_buckets_965_ = lean_ctor_get(v_m_u2081_962_, 1);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_array_get_size(v_buckets_965_);
v___x_968_ = lean_nat_dec_lt(v___x_966_, v___x_967_);
if (v___x_968_ == 0)
{
lean_dec_ref(v_m_u2081_962_);
lean_dec_ref(v_inst_961_);
lean_dec_ref(v_inst_960_);
return v_m_u2082_963_;
}
else
{
lean_object* v_size_969_; lean_object* v_buckets_970_; lean_object* v___x_971_; uint8_t v___x_972_; 
v_size_969_ = lean_ctor_get(v_m_u2082_963_, 0);
v_buckets_970_ = lean_ctor_get(v_m_u2082_963_, 1);
v___x_971_ = lean_array_get_size(v_buckets_970_);
v___x_972_ = lean_nat_dec_lt(v___x_966_, v___x_971_);
if (v___x_972_ == 0)
{
lean_dec_ref(v_m_u2082_963_);
lean_dec_ref(v_inst_961_);
lean_dec_ref(v_inst_960_);
return v_m_u2081_962_;
}
else
{
lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_973_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_974_ = lean_nat_dec_le(v_size_964_, v_size_969_);
if (v___x_974_ == 0)
{
lean_object* v___f_975_; lean_object* v___x_976_; 
v___f_975_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_976_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_975_, v_inst_960_, v_inst_961_, v_m_u2081_962_, v_m_u2082_963_);
return v___x_976_;
}
else
{
lean_object* v___f_977_; lean_object* v___f_978_; size_t v_sz_979_; size_t v___x_980_; lean_object* v___x_981_; 
lean_inc_ref(v_buckets_965_);
lean_dec_ref(v_m_u2081_962_);
v___f_977_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_977_, 0, v_inst_960_);
lean_closure_set(v___f_977_, 1, v_inst_961_);
v___f_978_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_978_, 0, v___x_973_);
lean_closure_set(v___f_978_, 1, v___f_977_);
v_sz_979_ = lean_array_size(v_buckets_965_);
v___x_980_ = ((size_t)0ULL);
v___x_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_973_, v_buckets_965_, v___f_978_, v_sz_979_, v___x_980_, v_m_u2082_963_);
return v___x_981_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union(lean_object* v_00_u03b1_982_, lean_object* v_inst_983_, lean_object* v_inst_984_, lean_object* v_m_u2081_985_, lean_object* v_m_u2082_986_){
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
lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_996_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v___x_997_ = lean_nat_dec_le(v_size_987_, v_size_992_);
if (v___x_997_ == 0)
{
lean_object* v___f_998_; lean_object* v___x_999_; 
v___f_998_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_999_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_998_, v_inst_983_, v_inst_984_, v_m_u2081_985_, v_m_u2082_986_);
return v___x_999_;
}
else
{
lean_object* v___f_1000_; lean_object* v___f_1001_; size_t v_sz_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
lean_inc_ref(v_buckets_988_);
lean_dec_ref(v_m_u2081_985_);
v___f_1000_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1000_, 0, v_inst_983_);
lean_closure_set(v___f_1000_, 1, v_inst_984_);
v___f_1001_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1001_, 0, v___x_996_);
lean_closure_set(v___f_1001_, 1, v___f_1000_);
v_sz_1002_ = lean_array_size(v_buckets_988_);
v___x_1003_ = ((size_t)0ULL);
v___x_1004_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_996_, v_buckets_988_, v___f_1001_, v_sz_1002_, v___x_1003_, v_m_u2082_986_);
return v___x_1004_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1005_, lean_object* v_inst_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_1007_, 0, lean_box(0));
lean_closure_set(v___x_1007_, 1, v_inst_1005_);
lean_closure_set(v___x_1007_, 2, v_inst_1006_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_1011_, 0, lean_box(0));
lean_closure_set(v___x_1011_, 1, v_inst_1009_);
lean_closure_set(v___x_1011_, 2, v_inst_1010_);
return v___x_1011_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter___redArg(lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_m_u2081_1014_, lean_object* v_m_u2082_1015_){
_start:
{
lean_object* v_buckets_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v_buckets_1016_ = lean_ctor_get(v_m_u2081_1014_, 1);
v___x_1017_ = lean_unsigned_to_nat(0u);
v___x_1018_ = lean_array_get_size(v_buckets_1016_);
v___x_1019_ = lean_nat_dec_lt(v___x_1017_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_dec_ref(v_m_u2081_1014_);
lean_dec_ref(v_inst_1013_);
lean_dec_ref(v_inst_1012_);
return v_m_u2082_1015_;
}
else
{
lean_object* v_buckets_1020_; lean_object* v___x_1021_; uint8_t v___x_1022_; 
v_buckets_1020_ = lean_ctor_get(v_m_u2082_1015_, 1);
v___x_1021_ = lean_array_get_size(v_buckets_1020_);
v___x_1022_ = lean_nat_dec_lt(v___x_1017_, v___x_1021_);
if (v___x_1022_ == 0)
{
lean_dec_ref(v_m_u2082_1015_);
lean_dec_ref(v_inst_1013_);
lean_dec_ref(v_inst_1012_);
return v_m_u2081_1014_;
}
else
{
lean_object* v___x_1023_; 
v___x_1023_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1012_, v_inst_1013_, v_m_u2081_1014_, v_m_u2082_1015_);
return v___x_1023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter(lean_object* v_00_u03b1_1024_, lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_m_u2081_1027_, lean_object* v_m_u2082_1028_){
_start:
{
lean_object* v_buckets_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; uint8_t v___x_1032_; 
v_buckets_1029_ = lean_ctor_get(v_m_u2081_1027_, 1);
v___x_1030_ = lean_unsigned_to_nat(0u);
v___x_1031_ = lean_array_get_size(v_buckets_1029_);
v___x_1032_ = lean_nat_dec_lt(v___x_1030_, v___x_1031_);
if (v___x_1032_ == 0)
{
lean_dec_ref(v_m_u2081_1027_);
lean_dec_ref(v_inst_1026_);
lean_dec_ref(v_inst_1025_);
return v_m_u2082_1028_;
}
else
{
lean_object* v_buckets_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_buckets_1033_ = lean_ctor_get(v_m_u2082_1028_, 1);
v___x_1034_ = lean_array_get_size(v_buckets_1033_);
v___x_1035_ = lean_nat_dec_lt(v___x_1030_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_dec_ref(v_m_u2082_1028_);
lean_dec_ref(v_inst_1026_);
lean_dec_ref(v_inst_1025_);
return v_m_u2081_1027_;
}
else
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1025_, v_inst_1026_, v_m_u2081_1027_, v_m_u2082_1028_);
return v___x_1036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1037_, lean_object* v_inst_1038_){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1039_, 0, lean_box(0));
lean_closure_set(v___x_1039_, 1, v_inst_1037_);
lean_closure_set(v___x_1039_, 2, v_inst_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1040_, lean_object* v_inst_1041_, lean_object* v_inst_1042_){
_start:
{
lean_object* v___x_1043_; 
v___x_1043_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1043_, 0, lean_box(0));
lean_closure_set(v___x_1043_, 1, v_inst_1041_);
lean_closure_set(v___x_1043_, 2, v_inst_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___f_1045_; 
v___x_1044_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1045_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1045_, 0, v___x_1044_);
return v___f_1045_;
}
}
uint8_t l_Std_HashSet_Raw_beq___redArg(lean_object* v_inst_1046_, lean_object* v_inst_1047_, lean_object* v_m_u2081_1048_, lean_object* v_m_u2082_1049_){
_start:
{
lean_object* v___f_1050_; uint8_t v___x_1051_; 
v___f_1050_ = lean_obj_once(&l_Std_HashSet_Raw_beq___redArg___closed__0, &l_Std_HashSet_Raw_beq___redArg___closed__0_once, _init_l_Std_HashSet_Raw_beq___redArg___closed__0);
v___x_1051_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1046_, v_inst_1047_, v___f_1050_, v_m_u2081_1048_, v_m_u2082_1049_);
return v___x_1051_;
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1046_ = stack[0].m_obj;
lean_object* v_inst_1047_ = stack[1].m_obj;
lean_object* v_m_u2081_1048_ = stack[2].m_obj;
lean_object* v_m_u2082_1049_ = stack[3].m_obj;
uint8_t v_res_1052_;
v_res_1052_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1046_, v_inst_1047_, v_m_u2081_1048_, v_m_u2082_1049_);
stack->m_num = v_res_1052_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___redArg___boxed(lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_m_u2081_1055_, lean_object* v_m_u2082_1056_){
_start:
{
uint8_t v_res_1057_; lean_object* v_r_1058_; 
v_res_1057_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1053_, v_inst_1054_, v_m_u2081_1055_, v_m_u2082_1056_);
v_r_1058_ = lean_box(v_res_1057_);
return v_r_1058_;
}
}
uint8_t l_Std_HashSet_Raw_beq(lean_object* v_00_u03b1_1059_, lean_object* v_inst_1060_, lean_object* v_inst_1061_, lean_object* v_m_u2081_1062_, lean_object* v_m_u2082_1063_){
_start:
{
uint8_t v___x_1064_; 
v___x_1064_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1060_, v_inst_1061_, v_m_u2081_1062_, v_m_u2082_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1060_ = stack[1].m_obj;
lean_object* v_inst_1061_ = stack[2].m_obj;
lean_object* v_m_u2081_1062_ = stack[3].m_obj;
lean_object* v_m_u2082_1063_ = stack[4].m_obj;
uint8_t v_res_1065_;
v_res_1065_ = l_Std_HashSet_Raw_beq(lean_box(0), v_inst_1060_, v_inst_1061_, v_m_u2081_1062_, v_m_u2082_1063_);
stack->m_num = v_res_1065_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___boxed(lean_object* v_00_u03b1_1066_, lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_m_u2081_1069_, lean_object* v_m_u2082_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Std_HashSet_Raw_beq(v_00_u03b1_1066_, v_inst_1067_, v_inst_1068_, v_m_u2081_1069_, v_m_u2082_1070_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1073_, lean_object* v_inst_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1075_, 0, lean_box(0));
lean_closure_set(v___x_1075_, 1, v_inst_1073_);
lean_closure_set(v___x_1075_, 2, v_inst_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1076_, lean_object* v_inst_1077_, lean_object* v_inst_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1079_, 0, lean_box(0));
lean_closure_set(v___x_1079_, 1, v_inst_1077_);
lean_closure_set(v___x_1079_, 2, v_inst_1078_);
return v___x_1079_;
}
}
uint8_t l_Std_HashSet_Raw_diff___redArg___lam__0(lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_m_u2082_1082_, uint8_t v___x_1083_, lean_object* v_k_1084_, lean_object* v_x_1085_){
_start:
{
uint8_t v___x_1086_; 
v___x_1086_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1080_, v_inst_1081_, v_m_u2082_1082_, v_k_1084_);
if (v___x_1086_ == 0)
{
return v___x_1083_;
}
else
{
uint8_t v___x_1087_; 
v___x_1087_ = 0;
return v___x_1087_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_diff___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1080_ = stack[0].m_obj;
lean_object* v_inst_1081_ = stack[1].m_obj;
lean_object* v_m_u2082_1082_ = stack[2].m_obj;
uint8_t v___x_1083_ = stack[3].m_num;
lean_object* v_k_1084_ = stack[4].m_obj;
lean_object* v_x_1085_ = stack[5].m_obj;
uint8_t v_res_1088_;
v_res_1088_ = l_Std_HashSet_Raw_diff___redArg___lam__0(v_inst_1080_, v_inst_1081_, v_m_u2082_1082_, v___x_1083_, v_k_1084_, v_x_1085_);
stack->m_num = v_res_1088_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_m_u2082_1091_, lean_object* v___x_1092_, lean_object* v_k_1093_, lean_object* v_x_1094_){
_start:
{
uint8_t v___x_100__boxed_1095_; uint8_t v_res_1096_; lean_object* v_r_1097_; 
v___x_100__boxed_1095_ = lean_unbox(v___x_1092_);
v_res_1096_ = l_Std_HashSet_Raw_diff___redArg___lam__0(v_inst_1089_, v_inst_1090_, v_m_u2082_1091_, v___x_100__boxed_1095_, v_k_1093_, v_x_1094_);
lean_dec_ref(v_m_u2082_1091_);
v_r_1097_ = lean_box(v_res_1096_);
return v_r_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg(lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_m_u2081_1100_, lean_object* v_m_u2082_1101_){
_start:
{
lean_object* v_size_1102_; lean_object* v_buckets_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; uint8_t v___x_1106_; 
v_size_1102_ = lean_ctor_get(v_m_u2081_1100_, 0);
v_buckets_1103_ = lean_ctor_get(v_m_u2081_1100_, 1);
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = lean_array_get_size(v_buckets_1103_);
v___x_1106_ = lean_nat_dec_lt(v___x_1104_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_dec_ref(v_m_u2081_1100_);
lean_dec_ref(v_inst_1099_);
lean_dec_ref(v_inst_1098_);
return v_m_u2082_1101_;
}
else
{
lean_object* v_size_1107_; lean_object* v_buckets_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_size_1107_ = lean_ctor_get(v_m_u2082_1101_, 0);
v_buckets_1108_ = lean_ctor_get(v_m_u2082_1101_, 1);
v___x_1109_ = lean_array_get_size(v_buckets_1108_);
v___x_1110_ = lean_nat_dec_lt(v___x_1104_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_dec_ref(v_m_u2082_1101_);
lean_dec_ref(v_inst_1099_);
lean_dec_ref(v_inst_1098_);
return v_m_u2081_1100_;
}
else
{
uint8_t v___x_1111_; 
v___x_1111_ = lean_nat_dec_le(v_size_1102_, v_size_1107_);
if (v___x_1111_ == 0)
{
lean_object* v___f_1112_; lean_object* v___x_1113_; 
v___f_1112_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1113_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1112_, v_inst_1098_, v_inst_1099_, v_m_u2081_1100_, v_m_u2082_1101_);
return v___x_1113_;
}
else
{
lean_object* v___x_1114_; lean_object* v___f_1115_; lean_object* v___x_1116_; 
v___x_1114_ = lean_box(v___x_1111_);
v___f_1115_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1115_, 0, v_inst_1098_);
lean_closure_set(v___f_1115_, 1, v_inst_1099_);
lean_closure_set(v___f_1115_, 2, v_m_u2082_1101_);
lean_closure_set(v___f_1115_, 3, v___x_1114_);
v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1115_, v_m_u2081_1100_);
return v___x_1116_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff(lean_object* v_00_u03b1_1117_, lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_m_u2081_1120_, lean_object* v_m_u2082_1121_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1137_, lean_object* v_inst_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1139_, 0, lean_box(0));
lean_closure_set(v___x_1139_, 1, v_inst_1137_);
lean_closure_set(v___x_1139_, 2, v_inst_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_){
_start:
{
lean_object* v___x_1143_; 
v___x_1143_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1143_, 0, lean_box(0));
lean_closure_set(v___x_1143_, 1, v_inst_1141_);
lean_closure_set(v___x_1143_, 2, v_inst_1142_);
return v___x_1143_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0(lean_object* v_p_1144_, lean_object* v___x_1145_, lean_object* v___x_1146_, lean_object* v_a_1147_, lean_object* v_b_1148_, lean_object* v_acc_1149_){
_start:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = lean_apply_1(v_p_1144_, v_a_1147_);
v___x_1151_ = lean_unbox(v___x_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref(v___x_1146_);
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1150_);
v___x_1153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1152_);
lean_ctor_set(v___x_1153_, 1, v___x_1145_);
v___x_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
return v___x_1154_;
}
else
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1146_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1156_, lean_object* v___x_1157_, lean_object* v___x_1158_, lean_object* v_a_1159_, lean_object* v_b_1160_, lean_object* v_acc_1161_){
_start:
{
lean_object* v_res_1162_; 
v_res_1162_ = l_Std_HashSet_Raw_all___redArg___lam__0(v_p_1156_, v___x_1157_, v___x_1158_, v_a_1159_, v_b_1160_, v_acc_1161_);
lean_dec_ref(v_acc_1161_);
return v_res_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__1(lean_object* v___x_1163_, lean_object* v___f_1164_, lean_object* v_a_1165_, lean_object* v_x_1166_, lean_object* v___y_1167_){
_start:
{
lean_object* v___x_1168_; 
v___x_1168_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1163_, v___f_1164_, v_a_1165_, v___y_1167_);
return v___x_1168_;
}
}
uint8_t l_Std_HashSet_Raw_all___redArg(lean_object* v_m_1172_, lean_object* v_p_1173_){
_start:
{
lean_object* v___x_1174_; lean_object* v_buckets_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; size_t v_sz_1180_; size_t v___x_1181_; lean_object* v___x_1182_; lean_object* v_fst_1183_; 
v___x_1174_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1175_ = lean_ctor_get(v_m_1172_, 1);
lean_inc_ref(v_buckets_1175_);
lean_dec_ref(v_m_1172_);
v___x_1176_ = lean_box(0);
v___x_1177_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1178_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1178_, 0, v_p_1173_);
lean_closure_set(v___f_1178_, 1, v___x_1176_);
lean_closure_set(v___f_1178_, 2, v___x_1177_);
v___f_1179_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1179_, 0, v___x_1174_);
lean_closure_set(v___f_1179_, 1, v___f_1178_);
v_sz_1180_ = lean_array_size(v_buckets_1175_);
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1174_, v_buckets_1175_, v___f_1179_, v_sz_1180_, v___x_1181_, v___x_1177_);
v_fst_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_fst_1183_);
lean_dec(v___x_1182_);
if (lean_obj_tag(v_fst_1183_) == 0)
{
uint8_t v___x_1184_; 
v___x_1184_ = 1;
return v___x_1184_;
}
else
{
lean_object* v_val_1185_; uint8_t v___x_1186_; 
v_val_1185_ = lean_ctor_get(v_fst_1183_, 0);
lean_inc(v_val_1185_);
lean_dec_ref_known(v_fst_1183_, 1);
v___x_1186_ = lean_unbox(v_val_1185_);
lean_dec(v_val_1185_);
return v___x_1186_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1172_ = stack[0].m_obj;
lean_object* v_p_1173_ = stack[1].m_obj;
uint8_t v_res_1187_;
v_res_1187_ = l_Std_HashSet_Raw_all___redArg(v_m_1172_, v_p_1173_);
stack->m_num = v_res_1187_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___boxed(lean_object* v_m_1188_, lean_object* v_p_1189_){
_start:
{
uint8_t v_res_1190_; lean_object* v_r_1191_; 
v_res_1190_ = l_Std_HashSet_Raw_all___redArg(v_m_1188_, v_p_1189_);
v_r_1191_ = lean_box(v_res_1190_);
return v_r_1191_;
}
}
uint8_t l_Std_HashSet_Raw_all(lean_object* v_00_u03b1_1192_, lean_object* v_m_1193_, lean_object* v_p_1194_){
_start:
{
lean_object* v___x_1195_; lean_object* v_buckets_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; size_t v_sz_1201_; size_t v___x_1202_; lean_object* v___x_1203_; lean_object* v_fst_1204_; 
v___x_1195_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1196_ = lean_ctor_get(v_m_1193_, 1);
lean_inc_ref(v_buckets_1196_);
lean_dec_ref(v_m_1193_);
v___x_1197_ = lean_box(0);
v___x_1198_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1199_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1199_, 0, v_p_1194_);
lean_closure_set(v___f_1199_, 1, v___x_1197_);
lean_closure_set(v___f_1199_, 2, v___x_1198_);
v___f_1200_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1200_, 0, v___x_1195_);
lean_closure_set(v___f_1200_, 1, v___f_1199_);
v_sz_1201_ = lean_array_size(v_buckets_1196_);
v___x_1202_ = ((size_t)0ULL);
v___x_1203_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1195_, v_buckets_1196_, v___f_1200_, v_sz_1201_, v___x_1202_, v___x_1198_);
v_fst_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_fst_1204_);
lean_dec(v___x_1203_);
if (lean_obj_tag(v_fst_1204_) == 0)
{
uint8_t v___x_1205_; 
v___x_1205_ = 1;
return v___x_1205_;
}
else
{
lean_object* v_val_1206_; uint8_t v___x_1207_; 
v_val_1206_ = lean_ctor_get(v_fst_1204_, 0);
lean_inc(v_val_1206_);
lean_dec_ref_known(v_fst_1204_, 1);
v___x_1207_ = lean_unbox(v_val_1206_);
lean_dec(v_val_1206_);
return v___x_1207_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1193_ = stack[1].m_obj;
lean_object* v_p_1194_ = stack[2].m_obj;
uint8_t v_res_1208_;
v_res_1208_ = l_Std_HashSet_Raw_all(lean_box(0), v_m_1193_, v_p_1194_);
stack->m_num = v_res_1208_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___boxed(lean_object* v_00_u03b1_1209_, lean_object* v_m_1210_, lean_object* v_p_1211_){
_start:
{
uint8_t v_res_1212_; lean_object* v_r_1213_; 
v_res_1212_ = l_Std_HashSet_Raw_all(v_00_u03b1_1209_, v_m_1210_, v_p_1211_);
v_r_1213_ = lean_box(v_res_1212_);
return v_r_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0(lean_object* v_p_1214_, lean_object* v___x_1215_, lean_object* v___x_1216_, lean_object* v_a_1217_, lean_object* v_b_1218_, lean_object* v_acc_1219_){
_start:
{
lean_object* v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = lean_apply_1(v_p_1214_, v_a_1217_);
v___x_1221_ = lean_unbox(v___x_1220_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1215_);
return v___x_1222_;
}
else
{
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec_ref(v___x_1215_);
v___x_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1220_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___x_1223_);
lean_ctor_set(v___x_1224_, 1, v___x_1216_);
v___x_1225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1226_, lean_object* v___x_1227_, lean_object* v___x_1228_, lean_object* v_a_1229_, lean_object* v_b_1230_, lean_object* v_acc_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l_Std_HashSet_Raw_any___redArg___lam__0(v_p_1226_, v___x_1227_, v___x_1228_, v_a_1229_, v_b_1230_, v_acc_1231_);
lean_dec_ref(v_acc_1231_);
return v_res_1232_;
}
}
uint8_t l_Std_HashSet_Raw_any___redArg(lean_object* v_m_1233_, lean_object* v_p_1234_){
_start:
{
lean_object* v___x_1235_; lean_object* v_buckets_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___f_1239_; lean_object* v___f_1240_; size_t v_sz_1241_; size_t v___x_1242_; lean_object* v___x_1243_; lean_object* v_fst_1244_; 
v___x_1235_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1236_ = lean_ctor_get(v_m_1233_, 1);
lean_inc_ref(v_buckets_1236_);
lean_dec_ref(v_m_1233_);
v___x_1237_ = lean_box(0);
v___x_1238_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1239_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1239_, 0, v_p_1234_);
lean_closure_set(v___f_1239_, 1, v___x_1238_);
lean_closure_set(v___f_1239_, 2, v___x_1237_);
v___f_1240_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1240_, 0, v___x_1235_);
lean_closure_set(v___f_1240_, 1, v___f_1239_);
v_sz_1241_ = lean_array_size(v_buckets_1236_);
v___x_1242_ = ((size_t)0ULL);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1235_, v_buckets_1236_, v___f_1240_, v_sz_1241_, v___x_1242_, v___x_1238_);
v_fst_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_fst_1244_);
lean_dec(v___x_1243_);
if (lean_obj_tag(v_fst_1244_) == 0)
{
uint8_t v___x_1245_; 
v___x_1245_ = 0;
return v___x_1245_;
}
else
{
lean_object* v_val_1246_; uint8_t v___x_1247_; 
v_val_1246_ = lean_ctor_get(v_fst_1244_, 0);
lean_inc(v_val_1246_);
lean_dec_ref_known(v_fst_1244_, 1);
v___x_1247_ = lean_unbox(v_val_1246_);
lean_dec(v_val_1246_);
return v___x_1247_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1233_ = stack[0].m_obj;
lean_object* v_p_1234_ = stack[1].m_obj;
uint8_t v_res_1248_;
v_res_1248_ = l_Std_HashSet_Raw_any___redArg(v_m_1233_, v_p_1234_);
stack->m_num = v_res_1248_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___boxed(lean_object* v_m_1249_, lean_object* v_p_1250_){
_start:
{
uint8_t v_res_1251_; lean_object* v_r_1252_; 
v_res_1251_ = l_Std_HashSet_Raw_any___redArg(v_m_1249_, v_p_1250_);
v_r_1252_ = lean_box(v_res_1251_);
return v_r_1252_;
}
}
uint8_t l_Std_HashSet_Raw_any(lean_object* v_00_u03b1_1253_, lean_object* v_m_1254_, lean_object* v_p_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v_buckets_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___f_1260_; lean_object* v___f_1261_; size_t v_sz_1262_; size_t v___x_1263_; lean_object* v___x_1264_; lean_object* v_fst_1265_; 
v___x_1256_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1257_ = lean_ctor_get(v_m_1254_, 1);
lean_inc_ref(v_buckets_1257_);
lean_dec_ref(v_m_1254_);
v___x_1258_ = lean_box(0);
v___x_1259_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1260_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1260_, 0, v_p_1255_);
lean_closure_set(v___f_1260_, 1, v___x_1259_);
lean_closure_set(v___f_1260_, 2, v___x_1258_);
v___f_1261_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1261_, 0, v___x_1256_);
lean_closure_set(v___f_1261_, 1, v___f_1260_);
v_sz_1262_ = lean_array_size(v_buckets_1257_);
v___x_1263_ = ((size_t)0ULL);
v___x_1264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1256_, v_buckets_1257_, v___f_1261_, v_sz_1262_, v___x_1263_, v___x_1259_);
v_fst_1265_ = lean_ctor_get(v___x_1264_, 0);
lean_inc(v_fst_1265_);
lean_dec(v___x_1264_);
if (lean_obj_tag(v_fst_1265_) == 0)
{
uint8_t v___x_1266_; 
v___x_1266_ = 0;
return v___x_1266_;
}
else
{
lean_object* v_val_1267_; uint8_t v___x_1268_; 
v_val_1267_ = lean_ctor_get(v_fst_1265_, 0);
lean_inc(v_val_1267_);
lean_dec_ref_known(v_fst_1265_, 1);
v___x_1268_ = lean_unbox(v_val_1267_);
lean_dec(v_val_1267_);
return v___x_1268_;
}
}
}
LEAN_EXPORT void l_Std_HashSet_Raw_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1254_ = stack[1].m_obj;
lean_object* v_p_1255_ = stack[2].m_obj;
uint8_t v_res_1269_;
v_res_1269_ = l_Std_HashSet_Raw_any(lean_box(0), v_m_1254_, v_p_1255_);
stack->m_num = v_res_1269_;
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___boxed(lean_object* v_00_u03b1_1270_, lean_object* v_m_1271_, lean_object* v_p_1272_){
_start:
{
uint8_t v_res_1273_; lean_object* v_r_1274_; 
v_res_1273_ = l_Std_HashSet_Raw_any(v_00_u03b1_1270_, v_m_1271_, v_p_1272_);
v_r_1274_ = lean_box(v_res_1273_);
return v_r_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany___redArg(lean_object* v_inst_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_m_1278_, lean_object* v_l_1279_){
_start:
{
lean_object* v_buckets_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
v_buckets_1280_ = lean_ctor_get(v_m_1278_, 1);
v___x_1281_ = lean_unsigned_to_nat(0u);
v___x_1282_ = lean_array_get_size(v_buckets_1280_);
v___x_1283_ = lean_nat_dec_lt(v___x_1281_, v___x_1282_);
if (v___x_1283_ == 0)
{
lean_dec(v_l_1279_);
lean_dec(v_inst_1277_);
lean_dec_ref(v_inst_1276_);
lean_dec_ref(v_inst_1275_);
return v_m_1278_;
}
else
{
lean_object* v___x_1284_; 
v___x_1284_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1277_, v_inst_1275_, v_inst_1276_, v_m_1278_, v_l_1279_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany(lean_object* v_00_u03b1_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_00_u03c1_1288_, lean_object* v_inst_1289_, lean_object* v_m_1290_, lean_object* v_l_1291_){
_start:
{
lean_object* v_buckets_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; 
v_buckets_1292_ = lean_ctor_get(v_m_1290_, 1);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_array_get_size(v_buckets_1292_);
v___x_1295_ = lean_nat_dec_lt(v___x_1293_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_dec(v_l_1291_);
lean_dec(v_inst_1289_);
lean_dec_ref(v_inst_1287_);
lean_dec_ref(v_inst_1286_);
return v_m_1290_;
}
else
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1289_, v_inst_1286_, v_inst_1287_, v_m_1290_, v_l_1291_);
return v___x_1296_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray___redArg(lean_object* v_inst_1301_, lean_object* v_inst_1302_, lean_object* v_l_1303_){
_start:
{
lean_object* v___x_1304_; uint8_t v___x_1305_; 
v___x_1304_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
v___x_1305_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1305_ == 0)
{
lean_dec_ref(v_l_1303_);
lean_dec_ref(v_inst_1302_);
lean_dec_ref(v_inst_1301_);
return v___x_1304_;
}
else
{
lean_object* v___f_1306_; lean_object* v___x_1307_; 
v___f_1306_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1307_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1306_, v_inst_1301_, v_inst_1302_, v___x_1304_, v_l_1303_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray(lean_object* v_00_u03b1_1308_, lean_object* v_inst_1309_, lean_object* v_inst_1310_, lean_object* v_l_1311_){
_start:
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___redArg___closed__1);
v___x_1313_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1313_ == 0)
{
lean_dec_ref(v_l_1311_);
lean_dec_ref(v_inst_1310_);
lean_dec_ref(v_inst_1309_);
return v___x_1312_;
}
else
{
lean_object* v___f_1314_; lean_object* v___x_1315_; 
v___f_1314_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1315_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1314_, v_inst_1309_, v_inst_1310_, v___x_1312_, v_l_1311_);
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg(lean_object* v_m_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_1318_){
_start:
{
lean_object* v_res_1319_; 
v_res_1319_ = l_Std_HashSet_Raw_Internal_numBuckets___redArg(v_m_1318_);
lean_dec_ref(v_m_1318_);
return v_res_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets(lean_object* v_00_u03b1_1320_, lean_object* v_m_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1323_, lean_object* v_m_1324_){
_start:
{
lean_object* v_res_1325_; 
v_res_1325_ = l_Std_HashSet_Raw_Internal_numBuckets(v_00_u03b1_1323_, v_m_1324_);
lean_dec_ref(v_m_1324_);
return v_res_1325_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2(lean_object* v_inst_1329_, lean_object* v___f_1330_, lean_object* v_m_1331_, lean_object* v_prec_1332_){
_start:
{
lean_object* v___x_1333_; lean_object* v_buckets_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1354_; 
v___x_1333_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__9));
v_buckets_1334_ = lean_ctor_get(v_m_1331_, 1);
v_isSharedCheck_1354_ = !lean_is_exclusive(v_m_1331_);
if (v_isSharedCheck_1354_ == 0)
{
lean_object* v_unused_1355_; 
v_unused_1355_ = lean_ctor_get(v_m_1331_, 0);
lean_dec(v_unused_1355_);
v___x_1336_ = v_m_1331_;
v_isShared_1337_ = v_isSharedCheck_1354_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_buckets_1334_);
lean_dec(v_m_1331_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1354_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1338_; lean_object* v___y_1340_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1338_ = ((lean_object*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___closed__1));
v___x_1346_ = lean_box(0);
v___x_1347_ = lean_array_get_size(v_buckets_1334_);
v___x_1348_ = lean_unsigned_to_nat(0u);
v___x_1349_ = lean_nat_dec_lt(v___x_1348_, v___x_1347_);
if (v___x_1349_ == 0)
{
lean_dec_ref(v_buckets_1334_);
lean_dec_ref(v___f_1330_);
v___y_1340_ = v___x_1346_;
goto v___jp_1339_;
}
else
{
lean_object* v___f_1350_; size_t v___x_1351_; size_t v___x_1352_; lean_object* v___x_1353_; 
v___f_1350_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1350_, 0, v___x_1333_);
lean_closure_set(v___f_1350_, 1, v___f_1330_);
v___x_1351_ = lean_usize_of_nat(v___x_1347_);
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1333_, v___f_1350_, v_buckets_1334_, v___x_1351_, v___x_1352_, v___x_1346_);
v___y_1340_ = v___x_1353_;
goto v___jp_1339_;
}
v___jp_1339_:
{
lean_object* v___x_1341_; lean_object* v___x_1343_; 
v___x_1341_ = l_List_repr___redArg(v_inst_1329_, v___y_1340_);
if (v_isShared_1337_ == 0)
{
lean_ctor_set_tag(v___x_1336_, 5);
lean_ctor_set(v___x_1336_, 1, v___x_1341_);
lean_ctor_set(v___x_1336_, 0, v___x_1338_);
v___x_1343_ = v___x_1336_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1345_, 1, v___x_1341_);
v___x_1343_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Repr_addAppParen(v___x_1343_, v_prec_1332_);
return v___x_1344_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed(lean_object* v_inst_1356_, lean_object* v___f_1357_, lean_object* v_m_1358_, lean_object* v_prec_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Std_HashSet_Raw_instRepr___redArg___lam__2(v_inst_1356_, v___f_1357_, v_m_1358_, v_prec_1359_);
lean_dec(v_prec_1359_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg(lean_object* v_inst_1361_){
_start:
{
lean_object* v___f_1362_; lean_object* v___f_1363_; 
v___f_1362_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___f_1363_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_1363_, 0, v_inst_1361_);
lean_closure_set(v___f_1363_, 1, v___f_1362_);
return v___f_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr(lean_object* v_00_u03b1_1364_, lean_object* v_inst_1365_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l_Std_HashSet_Raw_instRepr___redArg(v_inst_1365_);
return v___x_1366_;
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
