// Lean compiler output
// Module: Std.Data.HashMap.Raw
// Imports: public import Std.Data.DHashMap.Raw
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
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
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashMap_Raw_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_HashMap_Raw_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_instEmptyCollection___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited(lean_object*, lean_object*);
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__0 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HashMap"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__1 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__2 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__2_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__3 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__3_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_0),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 156, 61, 172, 252, 129, 143, 98)}};
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_1),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 114, 108, 172, 163, 107, 109, 115)}};
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__4_value_aux_2),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(59, 178, 34, 125, 85, 115, 99, 157)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__4 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__4_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__5 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__5_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__6 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__6_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__7 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__7_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__7_value)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__8 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__8_value;
static const lean_string_object l_Std_HashMap_Raw_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__9 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__10 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__10_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__11 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__6_value),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__8_value),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__12 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__12_value;
static const lean_ctor_object l_Std_HashMap_Raw_term___x7em___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__4_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__12_value)}};
static const lean_object* l_Std_HashMap_Raw_term___x7em___00__closed__13 = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Std_HashMap_Raw_term___x7em__ = (const lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__13_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_0),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_1),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value_aux_2),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value;
static lean_once_cell_t l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_0),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 156, 61, 172, 252, 129, 143, 98)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_1),((lean_object*)&l_Std_HashMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(49, 114, 108, 172, 163, 107, 109, 115)}};
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value_aux_2),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(82, 235, 84, 249, 222, 26, 229, 203)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__8_value)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__9_value),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__11_value)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12_value;
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1 = (const lean_object*)&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__1_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__2 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__2_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__3 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__3_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__4 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__4_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__5 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__5_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__6 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__6_value;
static const lean_ctor_object l_Std_HashMap_Raw_keys___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__0_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__1_value)}};
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__7 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__7_value;
static const lean_ctor_object l_Std_HashMap_Raw_keys___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__7_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__2_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__3_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__4_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__5_value)}};
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__8 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__8_value;
static const lean_ctor_object l_Std_HashMap_Raw_keys___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__8_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__6_value)}};
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__9 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__10 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__10_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keys___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__10_value)} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__11 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value)} };
static const lean_object* l_Std_HashMap_Raw_ofList___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_ofList___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value)} };
static const lean_object* l_Std_HashMap_Raw_ofArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_ofArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_ofArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_ofArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_ofArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_ofArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_toList___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_toList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_toList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_toList___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_toList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_toList___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_toList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_HashMap_Raw_all___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap_Raw_all___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_all___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value)} };
static const lean_object* l_Std_HashMap_Raw_union___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_toArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_toArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_toArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_toArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_toArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_keysArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_keysArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keysArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_keysArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_keysArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_keysArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_values___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_values___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_values___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keys___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_values___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_values___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_values___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_valuesArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keysArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_valuesArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_valuesArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.HashMap.Raw.ofList "};
static const lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_HashMap_Raw_emptyWithCapacity___redArg(v_capacity_11_);
lean_dec(v_capacity_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_capacity_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_16_ = lean_unsigned_to_nat(0u);
v___x_17_ = lean_unsigned_to_nat(4u);
v___x_18_ = lean_nat_mul(v_capacity_15_, v___x_17_);
v___x_19_ = lean_unsigned_to_nat(3u);
v___x_20_ = lean_nat_div(v___x_18_, v___x_19_);
lean_dec(v___x_18_);
v___x_21_ = l_Nat_nextPowerOfTwo(v___x_20_);
lean_dec(v___x_20_);
v___x_22_ = lean_box(0);
v___x_23_ = lean_mk_array(v___x_21_, v___x_22_);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v___x_16_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___boxed(lean_object* v_00_u03b1_25_, lean_object* v_00_u03b2_26_, lean_object* v_capacity_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Std_HashMap_Raw_emptyWithCapacity(v_00_u03b1_25_, v_00_u03b2_26_, v_capacity_27_);
lean_dec(v_capacity_27_);
return v_res_28_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_box(0);
v___x_30_ = lean_unsigned_to_nat(16u);
v___x_31_ = lean_mk_array(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_32_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0);
v___x_33_ = lean_unsigned_to_nat(0u);
v___x_34_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
lean_ctor_set(v___x_34_, 1, v___x_32_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited(lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_40_;
}
}
static lean_object* _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5));
v___x_82_ = l_String_toRawSubstring_x27(v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(lean_object* v_x_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_104_);
v___x_108_ = l_Lean_Syntax_isOfKind(v_x_104_, v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
lean_dec(v_x_104_);
v___x_109_ = lean_box(1);
v___x_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v_a_106_);
return v___x_110_;
}
else
{
lean_object* v_quotContext_111_; lean_object* v_currMacroScope_112_; lean_object* v_ref_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v_quotContext_111_ = lean_ctor_get(v_a_105_, 1);
v_currMacroScope_112_ = lean_ctor_get(v_a_105_, 2);
v_ref_113_ = lean_ctor_get(v_a_105_, 5);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = l_Lean_Syntax_getArg(v_x_104_, v___x_114_);
v___x_116_ = lean_unsigned_to_nat(2u);
v___x_117_ = l_Lean_Syntax_getArg(v_x_104_, v___x_116_);
lean_dec(v_x_104_);
v___x_118_ = 0;
v___x_119_ = l_Lean_SourceInfo_fromRef(v_ref_113_, v___x_118_);
v___x_120_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
v___x_121_ = lean_obj_once(&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6, &l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6);
v___x_122_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_112_);
lean_inc(v_quotContext_111_);
v___x_123_ = l_Lean_addMacroScope(v_quotContext_111_, v___x_122_, v_currMacroScope_112_);
v___x_124_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12));
lean_inc_n(v___x_119_, 2);
v___x_125_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_125_, 0, v___x_119_);
lean_ctor_set(v___x_125_, 1, v___x_121_);
lean_ctor_set(v___x_125_, 2, v___x_123_);
lean_ctor_set(v___x_125_, 3, v___x_124_);
v___x_126_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14));
v___x_127_ = l_Lean_Syntax_node2(v___x_119_, v___x_126_, v___x_115_, v___x_117_);
v___x_128_ = l_Lean_Syntax_node2(v___x_119_, v___x_120_, v___x_125_, v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v_a_106_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___boxed(lean_object* v_x_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(v_x_130_, v_a_131_, v_a_132_);
lean_dec_ref(v_a_131_);
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(lean_object* v_x_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
lean_inc(v_x_137_);
v___x_141_ = l_Lean_Syntax_isOfKind(v_x_137_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v___x_143_; 
lean_dec(v_x_137_);
v___x_142_ = lean_box(0);
v___x_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v_a_139_);
return v___x_143_;
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_144_ = lean_unsigned_to_nat(0u);
v___x_145_ = l_Lean_Syntax_getArg(v_x_137_, v___x_144_);
v___x_146_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_145_);
v___x_147_ = l_Lean_Syntax_isOfKind(v___x_145_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v___x_145_);
lean_dec(v_x_137_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_a_139_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_150_ = lean_unsigned_to_nat(1u);
v___x_151_ = l_Lean_Syntax_getArg(v_x_137_, v___x_150_);
lean_dec(v_x_137_);
v___x_152_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_151_);
v___x_153_ = l_Lean_Syntax_matchesNull(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v___x_151_);
lean_dec(v___x_145_);
v___x_154_ = lean_box(0);
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_139_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_ref_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_156_ = l_Lean_Syntax_getArg(v___x_151_, v___x_144_);
v___x_157_ = l_Lean_Syntax_getArg(v___x_151_, v___x_150_);
lean_dec(v___x_151_);
v_ref_158_ = l_Lean_replaceRef(v___x_145_, v_a_138_);
lean_dec(v___x_145_);
v___x_159_ = 0;
v___x_160_ = l_Lean_SourceInfo_fromRef(v_ref_158_, v___x_159_);
lean_dec(v_ref_158_);
v___x_161_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
v___x_162_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_160_);
v___x_163_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_160_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = l_Lean_Syntax_node3(v___x_160_, v___x_161_, v___x_156_, v___x_163_, v___x_157_);
v___x_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_a_139_);
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___boxed(lean_object* v_x_166_, lean_object* v_a_167_, lean_object* v_a_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(v_x_166_, v_a_167_, v_a_168_);
lean_dec(v_a_167_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert___redArg(lean_object* v_beq_170_, lean_object* v_inst_171_, lean_object* v_m_172_, lean_object* v_a_173_, lean_object* v_b_174_){
_start:
{
lean_object* v_buckets_175_; lean_object* v___x_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v_buckets_175_ = lean_ctor_get(v_m_172_, 1);
v___x_176_ = lean_unsigned_to_nat(0u);
v___x_177_ = lean_array_get_size(v_buckets_175_);
v___x_178_ = lean_nat_dec_lt(v___x_176_, v___x_177_);
if (v___x_178_ == 0)
{
lean_dec(v_b_174_);
lean_dec(v_a_173_);
lean_dec_ref(v_inst_171_);
lean_dec_ref(v_beq_170_);
return v_m_172_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_beq_170_, v_inst_171_, v_m_172_, v_a_173_, v_b_174_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert(lean_object* v_00_u03b1_180_, lean_object* v_00_u03b2_181_, lean_object* v_beq_182_, lean_object* v_inst_183_, lean_object* v_m_184_, lean_object* v_a_185_, lean_object* v_b_186_){
_start:
{
lean_object* v_buckets_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v_buckets_187_ = lean_ctor_get(v_m_184_, 1);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_array_get_size(v_buckets_187_);
v___x_190_ = lean_nat_dec_lt(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_dec(v_b_186_);
lean_dec(v_a_185_);
lean_dec_ref(v_inst_183_);
lean_dec_ref(v_beq_182_);
return v_m_184_;
}
else
{
lean_object* v___x_191_; 
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_beq_182_, v_inst_183_, v_m_184_, v_a_185_, v_b_186_);
return v___x_191_;
}
}
}
static lean_object* _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0);
v___x_193_ = lean_array_get_size(v___x_192_);
return v___x_193_;
}
}
static uint8_t _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_194_ = lean_obj_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = lean_nat_dec_lt(v___x_195_, v___x_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_x_199_){
_start:
{
lean_object* v_fst_200_; lean_object* v_snd_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_fst_200_ = lean_ctor_get(v_x_199_, 0);
lean_inc(v_fst_200_);
v_snd_201_ = lean_ctor_get(v_x_199_, 1);
lean_inc(v_snd_201_);
lean_dec_ref(v_x_199_);
v___x_202_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_203_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_203_ == 0)
{
lean_dec(v_snd_201_);
lean_dec(v_fst_200_);
lean_dec_ref(v_inst_198_);
lean_dec_ref(v_inst_197_);
return v___x_202_;
}
else
{
lean_object* v___x_204_; 
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_197_, v_inst_198_, v___x_202_, v_fst_200_, v_snd_201_);
return v___x_204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg(lean_object* v_inst_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v___f_207_; 
v___f_207_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_207_, 0, v_inst_205_);
lean_closure_set(v___f_207_, 1, v_inst_206_);
return v___f_207_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_inst_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v___f_212_; 
v___f_212_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_212_, 0, v_inst_210_);
lean_closure_set(v___f_212_, 1, v_inst_211_);
return v___f_212_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_x_215_, lean_object* v_s_216_){
_start:
{
lean_object* v_fst_217_; lean_object* v_snd_218_; lean_object* v_buckets_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_fst_217_ = lean_ctor_get(v_x_215_, 0);
lean_inc(v_fst_217_);
v_snd_218_ = lean_ctor_get(v_x_215_, 1);
lean_inc(v_snd_218_);
lean_dec_ref(v_x_215_);
v_buckets_219_ = lean_ctor_get(v_s_216_, 1);
v___x_220_ = lean_unsigned_to_nat(0u);
v___x_221_ = lean_array_get_size(v_buckets_219_);
v___x_222_ = lean_nat_dec_lt(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_dec(v_snd_218_);
lean_dec(v_fst_217_);
lean_dec_ref(v_inst_214_);
lean_dec_ref(v_inst_213_);
return v_s_216_;
}
else
{
lean_object* v___x_223_; 
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_213_, v_inst_214_, v_s_216_, v_fst_217_, v_snd_218_);
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg(lean_object* v_inst_224_, lean_object* v_inst_225_){
_start:
{
lean_object* v___f_226_; 
v___f_226_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_226_, 0, v_inst_224_);
lean_closure_set(v___f_226_, 1, v_inst_225_);
return v___f_226_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable(lean_object* v_00_u03b1_227_, lean_object* v_00_u03b2_228_, lean_object* v_inst_229_, lean_object* v_inst_230_){
_start:
{
lean_object* v___f_231_; 
v___f_231_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_231_, 0, v_inst_229_);
lean_closure_set(v___f_231_, 1, v_inst_230_);
return v___f_231_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew___redArg(lean_object* v_inst_232_, lean_object* v_inst_233_, lean_object* v_m_234_, lean_object* v_a_235_, lean_object* v_b_236_){
_start:
{
lean_object* v_buckets_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v_buckets_237_ = lean_ctor_get(v_m_234_, 1);
v___x_238_ = lean_unsigned_to_nat(0u);
v___x_239_ = lean_array_get_size(v_buckets_237_);
v___x_240_ = lean_nat_dec_lt(v___x_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_dec(v_b_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_inst_233_);
lean_dec_ref(v_inst_232_);
return v_m_234_;
}
else
{
lean_object* v___x_241_; 
v___x_241_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_232_, v_inst_233_, v_m_234_, v_a_235_, v_b_236_);
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_m_246_, lean_object* v_a_247_, lean_object* v_b_248_){
_start:
{
lean_object* v_buckets_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_buckets_249_ = lean_ctor_get(v_m_246_, 1);
v___x_250_ = lean_unsigned_to_nat(0u);
v___x_251_ = lean_array_get_size(v_buckets_249_);
v___x_252_ = lean_nat_dec_lt(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_dec(v_b_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_inst_245_);
lean_dec_ref(v_inst_244_);
return v_m_246_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_244_, v_inst_245_, v_m_246_, v_a_247_, v_b_248_);
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_254_, lean_object* v_inst_255_, lean_object* v_m_256_, lean_object* v_a_257_, lean_object* v_b_258_){
_start:
{
lean_object* v_size_259_; lean_object* v_buckets_260_; lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_size_259_ = lean_ctor_get(v_m_256_, 0);
v_buckets_260_ = lean_ctor_get(v_m_256_, 1);
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_array_get_size(v_buckets_260_);
v___x_263_ = lean_nat_dec_lt(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec(v_b_258_);
lean_dec(v_a_257_);
lean_dec_ref(v_inst_255_);
lean_dec_ref(v_inst_254_);
v___x_264_ = lean_box(v___x_263_);
v___x_265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_264_);
lean_ctor_set(v___x_265_, 1, v_m_256_);
return v___x_265_;
}
else
{
lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_315_; 
lean_inc_ref(v_buckets_260_);
lean_inc(v_size_259_);
v_isSharedCheck_315_ = !lean_is_exclusive(v_m_256_);
if (v_isSharedCheck_315_ == 0)
{
lean_object* v_unused_316_; lean_object* v_unused_317_; 
v_unused_316_ = lean_ctor_get(v_m_256_, 1);
lean_dec(v_unused_316_);
v_unused_317_ = lean_ctor_get(v_m_256_, 0);
lean_dec(v_unused_317_);
v___x_267_ = v_m_256_;
v_isShared_268_ = v_isSharedCheck_315_;
goto v_resetjp_266_;
}
else
{
lean_dec(v_m_256_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_315_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___x_269_; uint64_t v___x_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; uint64_t v_fold_274_; uint64_t v___x_275_; uint64_t v___x_276_; uint64_t v___x_277_; size_t v___x_278_; size_t v___x_279_; size_t v___x_280_; size_t v___x_281_; size_t v___x_282_; lean_object* v_bkt_283_; uint8_t v___x_284_; 
lean_inc_ref(v_inst_255_);
lean_inc_n(v_a_257_, 2);
v___x_269_ = lean_apply_1(v_inst_255_, v_a_257_);
v___x_270_ = 32ULL;
v___x_271_ = lean_unbox_uint64(v___x_269_);
v___x_272_ = lean_uint64_shift_right(v___x_271_, v___x_270_);
v___x_273_ = lean_unbox_uint64(v___x_269_);
lean_dec_ref(v___x_269_);
v_fold_274_ = lean_uint64_xor(v___x_273_, v___x_272_);
v___x_275_ = 16ULL;
v___x_276_ = lean_uint64_shift_right(v_fold_274_, v___x_275_);
v___x_277_ = lean_uint64_xor(v_fold_274_, v___x_276_);
v___x_278_ = lean_uint64_to_usize(v___x_277_);
v___x_279_ = lean_usize_of_nat(v___x_262_);
v___x_280_ = ((size_t)1ULL);
v___x_281_ = lean_usize_sub(v___x_279_, v___x_280_);
v___x_282_ = lean_usize_land(v___x_278_, v___x_281_);
v_bkt_283_ = lean_array_uget_borrowed(v_buckets_260_, v___x_282_);
lean_inc(v_bkt_283_);
lean_inc_ref(v_inst_254_);
v___x_284_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_254_, v_a_257_, v_bkt_283_);
if (v___x_284_ == 0)
{
lean_object* v___x_285_; lean_object* v_size_x27_286_; lean_object* v___x_287_; lean_object* v_buckets_x27_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; 
lean_dec_ref(v_inst_254_);
v___x_285_ = lean_unsigned_to_nat(1u);
v_size_x27_286_ = lean_nat_add(v_size_259_, v___x_285_);
lean_dec(v_size_259_);
lean_inc(v_bkt_283_);
v___x_287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_287_, 0, v_a_257_);
lean_ctor_set(v___x_287_, 1, v_b_258_);
lean_ctor_set(v___x_287_, 2, v_bkt_283_);
v_buckets_x27_288_ = lean_array_uset(v_buckets_260_, v___x_282_, v___x_287_);
v___x_289_ = lean_unsigned_to_nat(4u);
v___x_290_ = lean_nat_mul(v_size_x27_286_, v___x_289_);
v___x_291_ = lean_unsigned_to_nat(3u);
v___x_292_ = lean_nat_div(v___x_290_, v___x_291_);
lean_dec(v___x_290_);
v___x_293_ = lean_array_get_size(v_buckets_x27_288_);
v___x_294_ = lean_nat_dec_le(v___x_292_, v___x_293_);
lean_dec(v___x_292_);
if (v___x_294_ == 0)
{
lean_object* v_val_295_; lean_object* v___x_297_; 
v_val_295_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_255_, v_buckets_x27_288_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v_val_295_);
lean_ctor_set(v___x_267_, 0, v_size_x27_286_);
v___x_297_ = v___x_267_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v_size_x27_286_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v_val_295_);
v___x_297_ = v_reuseFailAlloc_300_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_box(v___x_284_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
lean_ctor_set(v___x_299_, 1, v___x_297_);
return v___x_299_;
}
}
else
{
lean_object* v___x_302_; 
lean_dec_ref(v_inst_255_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v_buckets_x27_288_);
lean_ctor_set(v___x_267_, 0, v_size_x27_286_);
v___x_302_ = v___x_267_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v_size_x27_286_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_buckets_x27_288_);
v___x_302_ = v_reuseFailAlloc_305_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_box(v___x_284_);
v___x_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_304_, 0, v___x_303_);
lean_ctor_set(v___x_304_, 1, v___x_302_);
return v___x_304_;
}
}
}
else
{
lean_object* v___x_306_; lean_object* v_buckets_x27_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_311_; 
lean_inc(v_bkt_283_);
lean_dec_ref(v_inst_255_);
v___x_306_ = lean_box(0);
v_buckets_x27_307_ = lean_array_uset(v_buckets_260_, v___x_282_, v___x_306_);
v___x_308_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_254_, v_a_257_, v_b_258_, v_bkt_283_);
v___x_309_ = lean_array_uset(v_buckets_x27_307_, v___x_282_, v___x_308_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_309_);
v___x_311_ = v___x_267_;
goto v_reusejp_310_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v_size_259_);
lean_ctor_set(v_reuseFailAlloc_314_, 1, v___x_309_);
v___x_311_ = v_reuseFailAlloc_314_;
goto v_reusejp_310_;
}
v_reusejp_310_:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_box(v___x_284_);
v___x_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
lean_ctor_set(v___x_313_, 1, v___x_311_);
return v___x_313_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_318_, lean_object* v_00_u03b2_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_m_322_, lean_object* v_a_323_, lean_object* v_b_324_){
_start:
{
lean_object* v_size_325_; lean_object* v_buckets_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v_size_325_ = lean_ctor_get(v_m_322_, 0);
v_buckets_326_ = lean_ctor_get(v_m_322_, 1);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_array_get_size(v_buckets_326_);
v___x_329_ = lean_nat_dec_lt(v___x_327_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_b_324_);
lean_dec(v_a_323_);
lean_dec_ref(v_inst_321_);
lean_dec_ref(v_inst_320_);
v___x_330_ = lean_box(v___x_329_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_m_322_);
return v___x_331_;
}
else
{
lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_381_; 
lean_inc_ref(v_buckets_326_);
lean_inc(v_size_325_);
v_isSharedCheck_381_ = !lean_is_exclusive(v_m_322_);
if (v_isSharedCheck_381_ == 0)
{
lean_object* v_unused_382_; lean_object* v_unused_383_; 
v_unused_382_ = lean_ctor_get(v_m_322_, 1);
lean_dec(v_unused_382_);
v_unused_383_ = lean_ctor_get(v_m_322_, 0);
lean_dec(v_unused_383_);
v___x_333_ = v_m_322_;
v_isShared_334_ = v_isSharedCheck_381_;
goto v_resetjp_332_;
}
else
{
lean_dec(v_m_322_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_381_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; uint64_t v___x_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; uint64_t v_fold_340_; uint64_t v___x_341_; uint64_t v___x_342_; uint64_t v___x_343_; size_t v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v___x_348_; lean_object* v_bkt_349_; uint8_t v___x_350_; 
lean_inc_ref(v_inst_321_);
lean_inc_n(v_a_323_, 2);
v___x_335_ = lean_apply_1(v_inst_321_, v_a_323_);
v___x_336_ = 32ULL;
v___x_337_ = lean_unbox_uint64(v___x_335_);
v___x_338_ = lean_uint64_shift_right(v___x_337_, v___x_336_);
v___x_339_ = lean_unbox_uint64(v___x_335_);
lean_dec_ref(v___x_335_);
v_fold_340_ = lean_uint64_xor(v___x_339_, v___x_338_);
v___x_341_ = 16ULL;
v___x_342_ = lean_uint64_shift_right(v_fold_340_, v___x_341_);
v___x_343_ = lean_uint64_xor(v_fold_340_, v___x_342_);
v___x_344_ = lean_uint64_to_usize(v___x_343_);
v___x_345_ = lean_usize_of_nat(v___x_328_);
v___x_346_ = ((size_t)1ULL);
v___x_347_ = lean_usize_sub(v___x_345_, v___x_346_);
v___x_348_ = lean_usize_land(v___x_344_, v___x_347_);
v_bkt_349_ = lean_array_uget_borrowed(v_buckets_326_, v___x_348_);
lean_inc(v_bkt_349_);
lean_inc_ref(v_inst_320_);
v___x_350_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_320_, v_a_323_, v_bkt_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v_size_x27_352_; lean_object* v___x_353_; lean_object* v_buckets_x27_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
lean_dec_ref(v_inst_320_);
v___x_351_ = lean_unsigned_to_nat(1u);
v_size_x27_352_ = lean_nat_add(v_size_325_, v___x_351_);
lean_dec(v_size_325_);
lean_inc(v_bkt_349_);
v___x_353_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_353_, 0, v_a_323_);
lean_ctor_set(v___x_353_, 1, v_b_324_);
lean_ctor_set(v___x_353_, 2, v_bkt_349_);
v_buckets_x27_354_ = lean_array_uset(v_buckets_326_, v___x_348_, v___x_353_);
v___x_355_ = lean_unsigned_to_nat(4u);
v___x_356_ = lean_nat_mul(v_size_x27_352_, v___x_355_);
v___x_357_ = lean_unsigned_to_nat(3u);
v___x_358_ = lean_nat_div(v___x_356_, v___x_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_array_get_size(v_buckets_x27_354_);
v___x_360_ = lean_nat_dec_le(v___x_358_, v___x_359_);
lean_dec(v___x_358_);
if (v___x_360_ == 0)
{
lean_object* v_val_361_; lean_object* v___x_363_; 
v_val_361_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_321_, v_buckets_x27_354_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_val_361_);
lean_ctor_set(v___x_333_, 0, v_size_x27_352_);
v___x_363_ = v___x_333_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_size_x27_352_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_val_361_);
v___x_363_ = v_reuseFailAlloc_366_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = lean_box(v___x_350_);
v___x_365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
lean_ctor_set(v___x_365_, 1, v___x_363_);
return v___x_365_;
}
}
else
{
lean_object* v___x_368_; 
lean_dec_ref(v_inst_321_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v_buckets_x27_354_);
lean_ctor_set(v___x_333_, 0, v_size_x27_352_);
v___x_368_ = v___x_333_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_size_x27_352_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_buckets_x27_354_);
v___x_368_ = v_reuseFailAlloc_371_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_369_ = lean_box(v___x_350_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_368_);
return v___x_370_;
}
}
}
else
{
lean_object* v___x_372_; lean_object* v_buckets_x27_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
lean_inc(v_bkt_349_);
lean_dec_ref(v_inst_321_);
v___x_372_ = lean_box(0);
v_buckets_x27_373_ = lean_array_uset(v_buckets_326_, v___x_348_, v___x_372_);
v___x_374_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_320_, v_a_323_, v_b_324_, v_bkt_349_);
v___x_375_ = lean_array_uset(v_buckets_x27_373_, v___x_348_, v___x_374_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_375_);
v___x_377_ = v___x_333_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_size_325_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v___x_375_);
v___x_377_ = v_reuseFailAlloc_380_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = lean_box(v___x_350_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_377_);
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_m_386_, lean_object* v_a_387_, lean_object* v_b_388_){
_start:
{
lean_object* v_size_389_; lean_object* v_buckets_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_size_389_ = lean_ctor_get(v_m_386_, 0);
v_buckets_390_ = lean_ctor_get(v_m_386_, 1);
v___x_391_ = lean_unsigned_to_nat(0u);
v___x_392_ = lean_array_get_size(v_buckets_390_);
v___x_393_ = lean_nat_dec_lt(v___x_391_, v___x_392_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; lean_object* v___x_395_; 
lean_dec(v_b_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_inst_385_);
lean_dec_ref(v_inst_384_);
v___x_394_ = lean_box(v___x_393_);
v___x_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_394_);
lean_ctor_set(v___x_395_, 1, v_m_386_);
return v___x_395_;
}
else
{
lean_object* v___x_396_; uint64_t v___x_397_; uint64_t v___x_398_; uint64_t v___x_399_; uint64_t v___x_400_; uint64_t v_fold_401_; uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; size_t v___x_405_; size_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; lean_object* v_bkt_410_; uint8_t v___x_411_; 
lean_inc_ref(v_inst_385_);
lean_inc_n(v_a_387_, 2);
v___x_396_ = lean_apply_1(v_inst_385_, v_a_387_);
v___x_397_ = 32ULL;
v___x_398_ = lean_unbox_uint64(v___x_396_);
v___x_399_ = lean_uint64_shift_right(v___x_398_, v___x_397_);
v___x_400_ = lean_unbox_uint64(v___x_396_);
lean_dec_ref(v___x_396_);
v_fold_401_ = lean_uint64_xor(v___x_400_, v___x_399_);
v___x_402_ = 16ULL;
v___x_403_ = lean_uint64_shift_right(v_fold_401_, v___x_402_);
v___x_404_ = lean_uint64_xor(v_fold_401_, v___x_403_);
v___x_405_ = lean_uint64_to_usize(v___x_404_);
v___x_406_ = lean_usize_of_nat(v___x_392_);
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_sub(v___x_406_, v___x_407_);
v___x_409_ = lean_usize_land(v___x_405_, v___x_408_);
v_bkt_410_ = lean_array_uget_borrowed(v_buckets_390_, v___x_409_);
lean_inc(v_bkt_410_);
v___x_411_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_384_, v_a_387_, v_bkt_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_436_; 
lean_inc_ref(v_buckets_390_);
lean_inc(v_size_389_);
v_isSharedCheck_436_ = !lean_is_exclusive(v_m_386_);
if (v_isSharedCheck_436_ == 0)
{
lean_object* v_unused_437_; lean_object* v_unused_438_; 
v_unused_437_ = lean_ctor_get(v_m_386_, 1);
lean_dec(v_unused_437_);
v_unused_438_ = lean_ctor_get(v_m_386_, 0);
lean_dec(v_unused_438_);
v___x_413_ = v_m_386_;
v_isShared_414_ = v_isSharedCheck_436_;
goto v_resetjp_412_;
}
else
{
lean_dec(v_m_386_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_436_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v_size_x27_416_; lean_object* v___x_417_; lean_object* v_buckets_x27_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_415_ = lean_unsigned_to_nat(1u);
v_size_x27_416_ = lean_nat_add(v_size_389_, v___x_415_);
lean_dec(v_size_389_);
lean_inc(v_bkt_410_);
v___x_417_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_417_, 0, v_a_387_);
lean_ctor_set(v___x_417_, 1, v_b_388_);
lean_ctor_set(v___x_417_, 2, v_bkt_410_);
v_buckets_x27_418_ = lean_array_uset(v_buckets_390_, v___x_409_, v___x_417_);
v___x_419_ = lean_unsigned_to_nat(4u);
v___x_420_ = lean_nat_mul(v_size_x27_416_, v___x_419_);
v___x_421_ = lean_unsigned_to_nat(3u);
v___x_422_ = lean_nat_div(v___x_420_, v___x_421_);
lean_dec(v___x_420_);
v___x_423_ = lean_array_get_size(v_buckets_x27_418_);
v___x_424_ = lean_nat_dec_le(v___x_422_, v___x_423_);
lean_dec(v___x_422_);
if (v___x_424_ == 0)
{
lean_object* v_val_425_; lean_object* v___x_427_; 
v_val_425_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_385_, v_buckets_x27_418_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v_val_425_);
lean_ctor_set(v___x_413_, 0, v_size_x27_416_);
v___x_427_ = v___x_413_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v_size_x27_416_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v_val_425_);
v___x_427_ = v_reuseFailAlloc_430_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_428_ = lean_box(v___x_411_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
return v___x_429_;
}
}
else
{
lean_object* v___x_432_; 
lean_dec_ref(v_inst_385_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v_buckets_x27_418_);
lean_ctor_set(v___x_413_, 0, v_size_x27_416_);
v___x_432_ = v___x_413_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_size_x27_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_buckets_x27_418_);
v___x_432_ = v_reuseFailAlloc_435_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_box(v___x_411_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
return v___x_434_;
}
}
}
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec(v_b_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_inst_385_);
v___x_439_ = lean_box(v___x_411_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v_m_386_);
return v___x_440_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_441_, lean_object* v_00_u03b2_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_m_445_, lean_object* v_a_446_, lean_object* v_b_447_){
_start:
{
lean_object* v_size_448_; lean_object* v_buckets_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_size_448_ = lean_ctor_get(v_m_445_, 0);
v_buckets_449_ = lean_ctor_get(v_m_445_, 1);
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_array_get_size(v_buckets_449_);
v___x_452_ = lean_nat_dec_lt(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; lean_object* v___x_454_; 
lean_dec(v_b_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_inst_444_);
lean_dec_ref(v_inst_443_);
v___x_453_ = lean_box(v___x_452_);
v___x_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_454_, 0, v___x_453_);
lean_ctor_set(v___x_454_, 1, v_m_445_);
return v___x_454_;
}
else
{
lean_object* v___x_455_; uint64_t v___x_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v_fold_460_; uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; size_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; lean_object* v_bkt_469_; uint8_t v___x_470_; 
lean_inc_ref(v_inst_444_);
lean_inc_n(v_a_446_, 2);
v___x_455_ = lean_apply_1(v_inst_444_, v_a_446_);
v___x_456_ = 32ULL;
v___x_457_ = lean_unbox_uint64(v___x_455_);
v___x_458_ = lean_uint64_shift_right(v___x_457_, v___x_456_);
v___x_459_ = lean_unbox_uint64(v___x_455_);
lean_dec_ref(v___x_455_);
v_fold_460_ = lean_uint64_xor(v___x_459_, v___x_458_);
v___x_461_ = 16ULL;
v___x_462_ = lean_uint64_shift_right(v_fold_460_, v___x_461_);
v___x_463_ = lean_uint64_xor(v_fold_460_, v___x_462_);
v___x_464_ = lean_uint64_to_usize(v___x_463_);
v___x_465_ = lean_usize_of_nat(v___x_451_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_sub(v___x_465_, v___x_466_);
v___x_468_ = lean_usize_land(v___x_464_, v___x_467_);
v_bkt_469_ = lean_array_uget_borrowed(v_buckets_449_, v___x_468_);
lean_inc(v_bkt_469_);
v___x_470_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_443_, v_a_446_, v_bkt_469_);
if (v___x_470_ == 0)
{
lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_495_; 
lean_inc_ref(v_buckets_449_);
lean_inc(v_size_448_);
v_isSharedCheck_495_ = !lean_is_exclusive(v_m_445_);
if (v_isSharedCheck_495_ == 0)
{
lean_object* v_unused_496_; lean_object* v_unused_497_; 
v_unused_496_ = lean_ctor_get(v_m_445_, 1);
lean_dec(v_unused_496_);
v_unused_497_ = lean_ctor_get(v_m_445_, 0);
lean_dec(v_unused_497_);
v___x_472_ = v_m_445_;
v_isShared_473_ = v_isSharedCheck_495_;
goto v_resetjp_471_;
}
else
{
lean_dec(v_m_445_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_495_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v___x_474_; lean_object* v_size_x27_475_; lean_object* v___x_476_; lean_object* v_buckets_x27_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v___x_474_ = lean_unsigned_to_nat(1u);
v_size_x27_475_ = lean_nat_add(v_size_448_, v___x_474_);
lean_dec(v_size_448_);
lean_inc(v_bkt_469_);
v___x_476_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_476_, 0, v_a_446_);
lean_ctor_set(v___x_476_, 1, v_b_447_);
lean_ctor_set(v___x_476_, 2, v_bkt_469_);
v_buckets_x27_477_ = lean_array_uset(v_buckets_449_, v___x_468_, v___x_476_);
v___x_478_ = lean_unsigned_to_nat(4u);
v___x_479_ = lean_nat_mul(v_size_x27_475_, v___x_478_);
v___x_480_ = lean_unsigned_to_nat(3u);
v___x_481_ = lean_nat_div(v___x_479_, v___x_480_);
lean_dec(v___x_479_);
v___x_482_ = lean_array_get_size(v_buckets_x27_477_);
v___x_483_ = lean_nat_dec_le(v___x_481_, v___x_482_);
lean_dec(v___x_481_);
if (v___x_483_ == 0)
{
lean_object* v_val_484_; lean_object* v___x_486_; 
v_val_484_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_444_, v_buckets_x27_477_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_val_484_);
lean_ctor_set(v___x_472_, 0, v_size_x27_475_);
v___x_486_ = v___x_472_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_size_x27_475_);
lean_ctor_set(v_reuseFailAlloc_489_, 1, v_val_484_);
v___x_486_ = v_reuseFailAlloc_489_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_box(v___x_470_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
return v___x_488_;
}
}
else
{
lean_object* v___x_491_; 
lean_dec_ref(v_inst_444_);
if (v_isShared_473_ == 0)
{
lean_ctor_set(v___x_472_, 1, v_buckets_x27_477_);
lean_ctor_set(v___x_472_, 0, v_size_x27_475_);
v___x_491_ = v___x_472_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_size_x27_475_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v_buckets_x27_477_);
v___x_491_ = v_reuseFailAlloc_494_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_box(v___x_470_);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v___x_491_);
return v___x_493_;
}
}
}
}
else
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v_b_447_);
lean_dec(v_a_446_);
lean_dec_ref(v_inst_444_);
v___x_498_ = lean_box(v___x_470_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_m_445_);
return v___x_499_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_m_502_, lean_object* v_a_503_, lean_object* v_b_504_){
_start:
{
lean_object* v_size_505_; lean_object* v_buckets_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_size_505_ = lean_ctor_get(v_m_502_, 0);
v_buckets_506_ = lean_ctor_get(v_m_502_, 1);
v___x_507_ = lean_unsigned_to_nat(0u);
v___x_508_ = lean_array_get_size(v_buckets_506_);
v___x_509_ = lean_nat_dec_lt(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_b_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_inst_501_);
lean_dec_ref(v_inst_500_);
v___x_510_ = lean_box(0);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v_m_502_);
return v___x_511_;
}
else
{
lean_object* v___x_512_; uint64_t v___x_513_; uint64_t v___x_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v_fold_517_; uint64_t v___x_518_; uint64_t v___x_519_; uint64_t v___x_520_; size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; lean_object* v_bkt_526_; lean_object* v___x_527_; 
lean_inc_ref(v_inst_501_);
lean_inc_n(v_a_503_, 2);
v___x_512_ = lean_apply_1(v_inst_501_, v_a_503_);
v___x_513_ = 32ULL;
v___x_514_ = lean_unbox_uint64(v___x_512_);
v___x_515_ = lean_uint64_shift_right(v___x_514_, v___x_513_);
v___x_516_ = lean_unbox_uint64(v___x_512_);
lean_dec_ref(v___x_512_);
v_fold_517_ = lean_uint64_xor(v___x_516_, v___x_515_);
v___x_518_ = 16ULL;
v___x_519_ = lean_uint64_shift_right(v_fold_517_, v___x_518_);
v___x_520_ = lean_uint64_xor(v_fold_517_, v___x_519_);
v___x_521_ = lean_uint64_to_usize(v___x_520_);
v___x_522_ = lean_usize_of_nat(v___x_508_);
v___x_523_ = ((size_t)1ULL);
v___x_524_ = lean_usize_sub(v___x_522_, v___x_523_);
v___x_525_ = lean_usize_land(v___x_521_, v___x_524_);
v_bkt_526_ = lean_array_uget_borrowed(v_buckets_506_, v___x_525_);
lean_inc(v_bkt_526_);
v___x_527_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_500_, v_a_503_, v_bkt_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_550_; 
lean_inc_ref(v_buckets_506_);
lean_inc(v_size_505_);
v_isSharedCheck_550_ = !lean_is_exclusive(v_m_502_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; lean_object* v_unused_552_; 
v_unused_551_ = lean_ctor_get(v_m_502_, 1);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_m_502_, 0);
lean_dec(v_unused_552_);
v___x_529_ = v_m_502_;
v_isShared_530_ = v_isSharedCheck_550_;
goto v_resetjp_528_;
}
else
{
lean_dec(v_m_502_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_550_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_531_; lean_object* v_size_x27_532_; lean_object* v___x_533_; lean_object* v_buckets_x27_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_531_ = lean_unsigned_to_nat(1u);
v_size_x27_532_ = lean_nat_add(v_size_505_, v___x_531_);
lean_dec(v_size_505_);
lean_inc(v_bkt_526_);
v___x_533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_533_, 0, v_a_503_);
lean_ctor_set(v___x_533_, 1, v_b_504_);
lean_ctor_set(v___x_533_, 2, v_bkt_526_);
v_buckets_x27_534_ = lean_array_uset(v_buckets_506_, v___x_525_, v___x_533_);
v___x_535_ = lean_unsigned_to_nat(4u);
v___x_536_ = lean_nat_mul(v_size_x27_532_, v___x_535_);
v___x_537_ = lean_unsigned_to_nat(3u);
v___x_538_ = lean_nat_div(v___x_536_, v___x_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_array_get_size(v_buckets_x27_534_);
v___x_540_ = lean_nat_dec_le(v___x_538_, v___x_539_);
lean_dec(v___x_538_);
if (v___x_540_ == 0)
{
lean_object* v_val_541_; lean_object* v___x_543_; 
v_val_541_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_501_, v_buckets_x27_534_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v_val_541_);
lean_ctor_set(v___x_529_, 0, v_size_x27_532_);
v___x_543_ = v___x_529_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_size_x27_532_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_val_541_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_527_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
return v___x_544_;
}
}
else
{
lean_object* v___x_547_; 
lean_dec_ref(v_inst_501_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v_buckets_x27_534_);
lean_ctor_set(v___x_529_, 0, v_size_x27_532_);
v___x_547_ = v___x_529_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_size_x27_532_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_buckets_x27_534_);
v___x_547_ = v_reuseFailAlloc_549_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_527_);
lean_ctor_set(v___x_548_, 1, v___x_547_);
return v___x_548_;
}
}
}
}
else
{
lean_object* v___x_553_; 
lean_dec(v_b_504_);
lean_dec(v_a_503_);
lean_dec_ref(v_inst_501_);
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_527_);
lean_ctor_set(v___x_553_, 1, v_m_502_);
return v___x_553_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_554_, lean_object* v_00_u03b2_555_, lean_object* v_inst_556_, lean_object* v_inst_557_, lean_object* v_m_558_, lean_object* v_a_559_, lean_object* v_b_560_){
_start:
{
lean_object* v_size_561_; lean_object* v_buckets_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_size_561_ = lean_ctor_get(v_m_558_, 0);
v_buckets_562_ = lean_ctor_get(v_m_558_, 1);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_array_get_size(v_buckets_562_);
v___x_565_ = lean_nat_dec_lt(v___x_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec(v_b_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_inst_557_);
lean_dec_ref(v_inst_556_);
v___x_566_ = lean_box(0);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
lean_ctor_set(v___x_567_, 1, v_m_558_);
return v___x_567_;
}
else
{
lean_object* v___x_568_; uint64_t v___x_569_; uint64_t v___x_570_; uint64_t v___x_571_; uint64_t v___x_572_; uint64_t v_fold_573_; uint64_t v___x_574_; uint64_t v___x_575_; uint64_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; size_t v___x_581_; lean_object* v_bkt_582_; lean_object* v___x_583_; 
lean_inc_ref(v_inst_557_);
lean_inc_n(v_a_559_, 2);
v___x_568_ = lean_apply_1(v_inst_557_, v_a_559_);
v___x_569_ = 32ULL;
v___x_570_ = lean_unbox_uint64(v___x_568_);
v___x_571_ = lean_uint64_shift_right(v___x_570_, v___x_569_);
v___x_572_ = lean_unbox_uint64(v___x_568_);
lean_dec_ref(v___x_568_);
v_fold_573_ = lean_uint64_xor(v___x_572_, v___x_571_);
v___x_574_ = 16ULL;
v___x_575_ = lean_uint64_shift_right(v_fold_573_, v___x_574_);
v___x_576_ = lean_uint64_xor(v_fold_573_, v___x_575_);
v___x_577_ = lean_uint64_to_usize(v___x_576_);
v___x_578_ = lean_usize_of_nat(v___x_564_);
v___x_579_ = ((size_t)1ULL);
v___x_580_ = lean_usize_sub(v___x_578_, v___x_579_);
v___x_581_ = lean_usize_land(v___x_577_, v___x_580_);
v_bkt_582_ = lean_array_uget_borrowed(v_buckets_562_, v___x_581_);
lean_inc(v_bkt_582_);
v___x_583_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_556_, v_a_559_, v_bkt_582_);
if (lean_obj_tag(v___x_583_) == 0)
{
lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_606_; 
lean_inc_ref(v_buckets_562_);
lean_inc(v_size_561_);
v_isSharedCheck_606_ = !lean_is_exclusive(v_m_558_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; lean_object* v_unused_608_; 
v_unused_607_ = lean_ctor_get(v_m_558_, 1);
lean_dec(v_unused_607_);
v_unused_608_ = lean_ctor_get(v_m_558_, 0);
lean_dec(v_unused_608_);
v___x_585_ = v_m_558_;
v_isShared_586_ = v_isSharedCheck_606_;
goto v_resetjp_584_;
}
else
{
lean_dec(v_m_558_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_606_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v___x_587_; lean_object* v_size_x27_588_; lean_object* v___x_589_; lean_object* v_buckets_x27_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_587_ = lean_unsigned_to_nat(1u);
v_size_x27_588_ = lean_nat_add(v_size_561_, v___x_587_);
lean_dec(v_size_561_);
lean_inc(v_bkt_582_);
v___x_589_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_589_, 0, v_a_559_);
lean_ctor_set(v___x_589_, 1, v_b_560_);
lean_ctor_set(v___x_589_, 2, v_bkt_582_);
v_buckets_x27_590_ = lean_array_uset(v_buckets_562_, v___x_581_, v___x_589_);
v___x_591_ = lean_unsigned_to_nat(4u);
v___x_592_ = lean_nat_mul(v_size_x27_588_, v___x_591_);
v___x_593_ = lean_unsigned_to_nat(3u);
v___x_594_ = lean_nat_div(v___x_592_, v___x_593_);
lean_dec(v___x_592_);
v___x_595_ = lean_array_get_size(v_buckets_x27_590_);
v___x_596_ = lean_nat_dec_le(v___x_594_, v___x_595_);
lean_dec(v___x_594_);
if (v___x_596_ == 0)
{
lean_object* v_val_597_; lean_object* v___x_599_; 
v_val_597_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_557_, v_buckets_x27_590_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 1, v_val_597_);
lean_ctor_set(v___x_585_, 0, v_size_x27_588_);
v___x_599_ = v___x_585_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_size_x27_588_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_val_597_);
v___x_599_ = v_reuseFailAlloc_601_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_583_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
return v___x_600_;
}
}
else
{
lean_object* v___x_603_; 
lean_dec_ref(v_inst_557_);
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 1, v_buckets_x27_590_);
lean_ctor_set(v___x_585_, 0, v_size_x27_588_);
v___x_603_ = v___x_585_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_size_x27_588_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_buckets_x27_590_);
v___x_603_ = v_reuseFailAlloc_605_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
lean_object* v___x_604_; 
v___x_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_604_, 0, v___x_583_);
lean_ctor_set(v___x_604_, 1, v___x_603_);
return v___x_604_;
}
}
}
}
else
{
lean_object* v___x_609_; 
lean_dec(v_b_560_);
lean_dec(v_a_559_);
lean_dec_ref(v_inst_557_);
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_583_);
lean_ctor_set(v___x_609_, 1, v_m_558_);
return v___x_609_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg(lean_object* v_beq_610_, lean_object* v_inst_611_, lean_object* v_m_612_, lean_object* v_a_613_){
_start:
{
lean_object* v_buckets_614_; lean_object* v___x_615_; lean_object* v___x_616_; uint8_t v___x_617_; 
v_buckets_614_ = lean_ctor_get(v_m_612_, 1);
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_array_get_size(v_buckets_614_);
v___x_617_ = lean_nat_dec_lt(v___x_615_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; 
lean_dec(v_a_613_);
lean_dec_ref(v_inst_611_);
lean_dec_ref(v_beq_610_);
v___x_618_ = lean_box(0);
return v___x_618_;
}
else
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_610_, v_inst_611_, v_m_612_, v_a_613_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg___boxed(lean_object* v_beq_620_, lean_object* v_inst_621_, lean_object* v_m_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_HashMap_Raw_get_x3f___redArg(v_beq_620_, v_inst_621_, v_m_622_, v_a_623_);
lean_dec_ref(v_m_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f(lean_object* v_00_u03b1_625_, lean_object* v_00_u03b2_626_, lean_object* v_beq_627_, lean_object* v_inst_628_, lean_object* v_m_629_, lean_object* v_a_630_){
_start:
{
lean_object* v_buckets_631_; lean_object* v___x_632_; lean_object* v___x_633_; uint8_t v___x_634_; 
v_buckets_631_ = lean_ctor_get(v_m_629_, 1);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_array_get_size(v_buckets_631_);
v___x_634_ = lean_nat_dec_lt(v___x_632_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v___x_635_; 
lean_dec(v_a_630_);
lean_dec_ref(v_inst_628_);
lean_dec_ref(v_beq_627_);
v___x_635_ = lean_box(0);
return v___x_635_;
}
else
{
lean_object* v___x_636_; 
v___x_636_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_627_, v_inst_628_, v_m_629_, v_a_630_);
return v___x_636_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_637_, lean_object* v_00_u03b2_638_, lean_object* v_beq_639_, lean_object* v_inst_640_, lean_object* v_m_641_, lean_object* v_a_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_HashMap_Raw_get_x3f(v_00_u03b1_637_, v_00_u03b2_638_, v_beq_639_, v_inst_640_, v_m_641_, v_a_642_);
lean_dec_ref(v_m_641_);
return v_res_643_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains___redArg(lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_m_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_buckets_648_; lean_object* v___x_649_; lean_object* v___x_650_; uint8_t v___x_651_; 
v_buckets_648_ = lean_ctor_get(v_m_646_, 1);
v___x_649_ = lean_unsigned_to_nat(0u);
v___x_650_ = lean_array_get_size(v_buckets_648_);
v___x_651_ = lean_nat_dec_lt(v___x_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_dec(v_a_647_);
lean_dec_ref(v_inst_645_);
lean_dec_ref(v_inst_644_);
return v___x_651_;
}
else
{
uint8_t v___x_652_; 
v___x_652_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_644_, v_inst_645_, v_m_646_, v_a_647_);
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___redArg___boxed(lean_object* v_inst_653_, lean_object* v_inst_654_, lean_object* v_m_655_, lean_object* v_a_656_){
_start:
{
uint8_t v_res_657_; lean_object* v_r_658_; 
v_res_657_ = l_Std_HashMap_Raw_contains___redArg(v_inst_653_, v_inst_654_, v_m_655_, v_a_656_);
lean_dec_ref(v_m_655_);
v_r_658_ = lean_box(v_res_657_);
return v_r_658_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_m_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_buckets_665_; lean_object* v___x_666_; lean_object* v___x_667_; uint8_t v___x_668_; 
v_buckets_665_ = lean_ctor_get(v_m_663_, 1);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_array_get_size(v_buckets_665_);
v___x_668_ = lean_nat_dec_lt(v___x_666_, v___x_667_);
if (v___x_668_ == 0)
{
lean_dec(v_a_664_);
lean_dec_ref(v_inst_662_);
lean_dec_ref(v_inst_661_);
return v___x_668_;
}
else
{
uint8_t v___x_669_; 
v___x_669_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_661_, v_inst_662_, v_m_663_, v_a_664_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___boxed(lean_object* v_00_u03b1_670_, lean_object* v_00_u03b2_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_m_674_, lean_object* v_a_675_){
_start:
{
uint8_t v_res_676_; lean_object* v_r_677_; 
v_res_676_ = l_Std_HashMap_Raw_contains(v_00_u03b1_670_, v_00_u03b2_671_, v_inst_672_, v_inst_673_, v_m_674_, v_a_675_);
lean_dec_ref(v_m_674_);
v_r_677_ = lean_box(v_res_676_);
return v_r_677_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_678_, lean_object* v_00_u03b2_679_, lean_object* v_inst_680_, lean_object* v_inst_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = lean_box(0);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_inst_685_, lean_object* v_inst_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_683_, v_00_u03b2_684_, v_inst_685_, v_inst_686_);
lean_dec_ref(v_inst_686_);
lean_dec_ref(v_inst_685_);
return v_res_687_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_m_690_, lean_object* v_a_691_){
_start:
{
lean_object* v_buckets_692_; lean_object* v___x_693_; lean_object* v___x_694_; uint8_t v___x_695_; 
v_buckets_692_ = lean_ctor_get(v_m_690_, 1);
v___x_693_ = lean_unsigned_to_nat(0u);
v___x_694_ = lean_array_get_size(v_buckets_692_);
v___x_695_ = lean_nat_dec_lt(v___x_693_, v___x_694_);
if (v___x_695_ == 0)
{
lean_dec(v_a_691_);
lean_dec_ref(v_inst_689_);
lean_dec_ref(v_inst_688_);
return v___x_695_;
}
else
{
uint8_t v___x_696_; 
v___x_696_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_688_, v_inst_689_, v_m_690_, v_a_691_);
return v___x_696_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_m_699_, lean_object* v_a_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l_Std_HashMap_Raw_instDecidableMem___redArg(v_inst_697_, v_inst_698_, v_m_699_, v_a_700_);
lean_dec_ref(v_m_699_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_inst_705_, lean_object* v_inst_706_, lean_object* v_m_707_, lean_object* v_a_708_){
_start:
{
uint8_t v___x_709_; 
v___x_709_ = l_Std_HashMap_Raw_instDecidableMem___redArg(v_inst_705_, v_inst_706_, v_m_707_, v_a_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_710_, lean_object* v_00_u03b2_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_m_714_, lean_object* v_a_715_){
_start:
{
uint8_t v_res_716_; lean_object* v_r_717_; 
v_res_716_ = l_Std_HashMap_Raw_instDecidableMem(v_00_u03b1_710_, v_00_u03b2_711_, v_inst_712_, v_inst_713_, v_m_714_, v_a_715_);
lean_dec_ref(v_m_714_);
v_r_717_ = lean_box(v_res_716_);
return v_r_717_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg(lean_object* v_inst_718_, lean_object* v_inst_719_, lean_object* v_m_720_, lean_object* v_a_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_718_, v_inst_719_, v_m_720_, v_a_721_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg___boxed(lean_object* v_inst_723_, lean_object* v_inst_724_, lean_object* v_m_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Std_HashMap_Raw_get___redArg(v_inst_723_, v_inst_724_, v_m_725_, v_a_726_);
lean_dec_ref(v_m_725_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get(lean_object* v_00_u03b1_728_, lean_object* v_00_u03b2_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_m_732_, lean_object* v_a_733_, lean_object* v_h_734_){
_start:
{
lean_object* v___x_735_; 
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_730_, v_inst_731_, v_m_732_, v_a_733_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___boxed(lean_object* v_00_u03b1_736_, lean_object* v_00_u03b2_737_, lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_m_740_, lean_object* v_a_741_, lean_object* v_h_742_){
_start:
{
lean_object* v_res_743_; 
v_res_743_ = l_Std_HashMap_Raw_get(v_00_u03b1_736_, v_00_u03b2_737_, v_inst_738_, v_inst_739_, v_m_740_, v_a_741_, v_h_742_);
lean_dec_ref(v_m_740_);
return v_res_743_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg(lean_object* v_inst_744_, lean_object* v_inst_745_, lean_object* v_m_746_, lean_object* v_a_747_, lean_object* v_fallback_748_){
_start:
{
lean_object* v_buckets_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_buckets_749_ = lean_ctor_get(v_m_746_, 1);
v___x_750_ = lean_unsigned_to_nat(0u);
v___x_751_ = lean_array_get_size(v_buckets_749_);
v___x_752_ = lean_nat_dec_lt(v___x_750_, v___x_751_);
if (v___x_752_ == 0)
{
lean_dec(v_a_747_);
lean_dec_ref(v_inst_745_);
lean_dec_ref(v_inst_744_);
lean_inc(v_fallback_748_);
return v_fallback_748_;
}
else
{
lean_object* v___x_753_; 
v___x_753_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_744_, v_inst_745_, v_m_746_, v_a_747_, v_fallback_748_);
return v___x_753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg___boxed(lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_m_756_, lean_object* v_a_757_, lean_object* v_fallback_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_Std_HashMap_Raw_getD___redArg(v_inst_754_, v_inst_755_, v_m_756_, v_a_757_, v_fallback_758_);
lean_dec(v_fallback_758_);
lean_dec_ref(v_m_756_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD(lean_object* v_00_u03b1_760_, lean_object* v_00_u03b2_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_m_764_, lean_object* v_a_765_, lean_object* v_fallback_766_){
_start:
{
lean_object* v_buckets_767_; lean_object* v___x_768_; lean_object* v___x_769_; uint8_t v___x_770_; 
v_buckets_767_ = lean_ctor_get(v_m_764_, 1);
v___x_768_ = lean_unsigned_to_nat(0u);
v___x_769_ = lean_array_get_size(v_buckets_767_);
v___x_770_ = lean_nat_dec_lt(v___x_768_, v___x_769_);
if (v___x_770_ == 0)
{
lean_dec(v_a_765_);
lean_dec_ref(v_inst_763_);
lean_dec_ref(v_inst_762_);
lean_inc(v_fallback_766_);
return v_fallback_766_;
}
else
{
lean_object* v___x_771_; 
v___x_771_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_762_, v_inst_763_, v_m_764_, v_a_765_, v_fallback_766_);
return v___x_771_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___boxed(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_m_776_, lean_object* v_a_777_, lean_object* v_fallback_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_HashMap_Raw_getD(v_00_u03b1_772_, v_00_u03b2_773_, v_inst_774_, v_inst_775_, v_m_776_, v_a_777_, v_fallback_778_);
lean_dec(v_fallback_778_);
lean_dec_ref(v_m_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg(lean_object* v_inst_780_, lean_object* v_inst_781_, lean_object* v_inst_782_, lean_object* v_m_783_, lean_object* v_a_784_){
_start:
{
lean_object* v_buckets_785_; lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v_buckets_785_ = lean_ctor_get(v_m_783_, 1);
v___x_786_ = lean_unsigned_to_nat(0u);
v___x_787_ = lean_array_get_size(v_buckets_785_);
v___x_788_ = lean_nat_dec_lt(v___x_786_, v___x_787_);
if (v___x_788_ == 0)
{
lean_dec(v_a_784_);
lean_dec_ref(v_inst_781_);
lean_dec_ref(v_inst_780_);
lean_inc(v_inst_782_);
return v_inst_782_;
}
else
{
lean_object* v___x_789_; 
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_780_, v_inst_781_, v_inst_782_, v_m_783_, v_a_784_);
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_m_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_Std_HashMap_Raw_get_x21___redArg(v_inst_790_, v_inst_791_, v_inst_792_, v_m_793_, v_a_794_);
lean_dec_ref(v_m_793_);
lean_dec(v_inst_792_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21(lean_object* v_00_u03b1_796_, lean_object* v_00_u03b2_797_, lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_m_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_buckets_803_; lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v_buckets_803_ = lean_ctor_get(v_m_801_, 1);
v___x_804_ = lean_unsigned_to_nat(0u);
v___x_805_ = lean_array_get_size(v_buckets_803_);
v___x_806_ = lean_nat_dec_lt(v___x_804_, v___x_805_);
if (v___x_806_ == 0)
{
lean_dec(v_a_802_);
lean_dec_ref(v_inst_799_);
lean_dec_ref(v_inst_798_);
lean_inc(v_inst_800_);
return v_inst_800_;
}
else
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_798_, v_inst_799_, v_inst_800_, v_m_801_, v_a_802_);
return v___x_807_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_808_, lean_object* v_00_u03b2_809_, lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_m_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_HashMap_Raw_get_x21(v_00_u03b1_808_, v_00_u03b2_809_, v_inst_810_, v_inst_811_, v_inst_812_, v_m_813_, v_a_814_);
lean_dec_ref(v_m_813_);
lean_dec(v_inst_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_816_, lean_object* v_inst_817_, lean_object* v_m_818_, lean_object* v_a_819_, lean_object* v_h_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_816_, v_inst_817_, v_m_818_, v_a_819_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_822_, lean_object* v_inst_823_, lean_object* v_m_824_, lean_object* v_a_825_, lean_object* v_h_826_){
_start:
{
lean_object* v_res_827_; 
v_res_827_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(v_inst_822_, v_inst_823_, v_m_824_, v_a_825_, v_h_826_);
lean_dec_ref(v_m_824_);
return v_res_827_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_828_, lean_object* v_inst_829_, lean_object* v_m_830_, lean_object* v_a_831_){
_start:
{
lean_object* v_buckets_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_buckets_832_ = lean_ctor_get(v_m_830_, 1);
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = lean_array_get_size(v_buckets_832_);
v___x_835_ = lean_nat_dec_lt(v___x_833_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; 
lean_dec(v_a_831_);
lean_dec_ref(v_inst_829_);
lean_dec_ref(v_inst_828_);
v___x_836_ = lean_box(0);
return v___x_836_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_828_, v_inst_829_, v_m_830_, v_a_831_);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_m_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(v_inst_838_, v_inst_839_, v_m_840_, v_a_841_);
lean_dec_ref(v_m_840_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_m_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_buckets_848_; lean_object* v___x_849_; lean_object* v___x_850_; uint8_t v___x_851_; 
v_buckets_848_ = lean_ctor_get(v_m_846_, 1);
v___x_849_ = lean_unsigned_to_nat(0u);
v___x_850_ = lean_array_get_size(v_buckets_848_);
v___x_851_ = lean_nat_dec_lt(v___x_849_, v___x_850_);
if (v___x_851_ == 0)
{
lean_dec(v_a_847_);
lean_dec_ref(v_inst_844_);
lean_dec_ref(v_inst_843_);
lean_inc(v_inst_845_);
return v_inst_845_;
}
else
{
lean_object* v___x_852_; 
v___x_852_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_843_, v_inst_844_, v_inst_845_, v_m_846_, v_a_847_);
return v___x_852_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_m_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(v_inst_853_, v_inst_854_, v_inst_855_, v_m_856_, v_a_857_);
lean_dec_ref(v_m_856_);
lean_dec(v_inst_855_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(lean_object* v_inst_859_, lean_object* v_inst_860_){
_start:
{
lean_object* v___f_861_; lean_object* v___f_862_; lean_object* v___f_863_; lean_object* v___x_864_; 
lean_inc_ref_n(v_inst_860_, 2);
lean_inc_ref_n(v_inst_859_, 2);
v___f_861_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_861_, 0, v_inst_859_);
lean_closure_set(v___f_861_, 1, v_inst_860_);
v___f_862_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_862_, 0, v_inst_859_);
lean_closure_set(v___f_862_, 1, v_inst_860_);
v___f_863_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_863_, 0, v_inst_859_);
lean_closure_set(v___f_863_, 1, v_inst_860_);
v___x_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_864_, 0, v___f_861_);
lean_ctor_set(v___x_864_, 1, v___f_862_);
lean_ctor_set(v___x_864_, 2, v___f_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem(lean_object* v_00_u03b1_865_, lean_object* v_00_u03b2_866_, lean_object* v_inst_867_, lean_object* v_inst_868_){
_start:
{
lean_object* v___x_869_; 
v___x_869_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(v_inst_867_, v_inst_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_870_, lean_object* v_inst_871_, lean_object* v_m_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_buckets_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_buckets_874_ = lean_ctor_get(v_m_872_, 1);
v___x_875_ = lean_unsigned_to_nat(0u);
v___x_876_ = lean_array_get_size(v_buckets_874_);
v___x_877_ = lean_nat_dec_lt(v___x_875_, v___x_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; 
lean_dec(v_a_873_);
lean_dec_ref(v_inst_871_);
lean_dec_ref(v_inst_870_);
v___x_878_ = lean_box(0);
return v___x_878_;
}
else
{
lean_object* v___x_879_; 
v___x_879_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_870_, v_inst_871_, v_m_872_, v_a_873_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_880_, lean_object* v_inst_881_, lean_object* v_m_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l_Std_HashMap_Raw_getKey_x3f___redArg(v_inst_880_, v_inst_881_, v_m_882_, v_a_883_);
lean_dec_ref(v_m_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_885_, lean_object* v_00_u03b2_886_, lean_object* v_inst_887_, lean_object* v_inst_888_, lean_object* v_m_889_, lean_object* v_a_890_){
_start:
{
lean_object* v_buckets_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_buckets_891_ = lean_ctor_get(v_m_889_, 1);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = lean_array_get_size(v_buckets_891_);
v___x_894_ = lean_nat_dec_lt(v___x_892_, v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; 
lean_dec(v_a_890_);
lean_dec_ref(v_inst_888_);
lean_dec_ref(v_inst_887_);
v___x_895_ = lean_box(0);
return v___x_895_;
}
else
{
lean_object* v___x_896_; 
v___x_896_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_887_, v_inst_888_, v_m_889_, v_a_890_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_897_, lean_object* v_00_u03b2_898_, lean_object* v_inst_899_, lean_object* v_inst_900_, lean_object* v_m_901_, lean_object* v_a_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l_Std_HashMap_Raw_getKey_x3f(v_00_u03b1_897_, v_00_u03b2_898_, v_inst_899_, v_inst_900_, v_m_901_, v_a_902_);
lean_dec_ref(v_m_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg(lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_m_906_, lean_object* v_a_907_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_904_, v_inst_905_, v_m_906_, v_a_907_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_909_, lean_object* v_inst_910_, lean_object* v_m_911_, lean_object* v_a_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Std_HashMap_Raw_getKey___redArg(v_inst_909_, v_inst_910_, v_m_911_, v_a_912_);
lean_dec_ref(v_m_911_);
return v_res_913_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey(lean_object* v_00_u03b1_914_, lean_object* v_00_u03b2_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_m_918_, lean_object* v_a_919_, lean_object* v_h_920_){
_start:
{
lean_object* v___x_921_; 
v___x_921_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_916_, v_inst_917_, v_m_918_, v_a_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_922_, lean_object* v_00_u03b2_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_m_926_, lean_object* v_a_927_, lean_object* v_h_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l_Std_HashMap_Raw_getKey(v_00_u03b1_922_, v_00_u03b2_923_, v_inst_924_, v_inst_925_, v_m_926_, v_a_927_, v_h_928_);
lean_dec_ref(v_m_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg(lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_m_932_, lean_object* v_a_933_, lean_object* v_fallback_934_){
_start:
{
lean_object* v_buckets_935_; lean_object* v___x_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_buckets_935_ = lean_ctor_get(v_m_932_, 1);
v___x_936_ = lean_unsigned_to_nat(0u);
v___x_937_ = lean_array_get_size(v_buckets_935_);
v___x_938_ = lean_nat_dec_lt(v___x_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_dec(v_a_933_);
lean_dec_ref(v_inst_931_);
lean_dec_ref(v_inst_930_);
lean_inc(v_fallback_934_);
return v_fallback_934_;
}
else
{
lean_object* v___x_939_; 
v___x_939_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_930_, v_inst_931_, v_m_932_, v_a_933_, v_fallback_934_);
return v___x_939_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_m_942_, lean_object* v_a_943_, lean_object* v_fallback_944_){
_start:
{
lean_object* v_res_945_; 
v_res_945_ = l_Std_HashMap_Raw_getKeyD___redArg(v_inst_940_, v_inst_941_, v_m_942_, v_a_943_, v_fallback_944_);
lean_dec(v_fallback_944_);
lean_dec_ref(v_m_942_);
return v_res_945_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD(lean_object* v_00_u03b1_946_, lean_object* v_00_u03b2_947_, lean_object* v_inst_948_, lean_object* v_inst_949_, lean_object* v_m_950_, lean_object* v_a_951_, lean_object* v_fallback_952_){
_start:
{
lean_object* v_buckets_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_buckets_953_ = lean_ctor_get(v_m_950_, 1);
v___x_954_ = lean_unsigned_to_nat(0u);
v___x_955_ = lean_array_get_size(v_buckets_953_);
v___x_956_ = lean_nat_dec_lt(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_dec(v_a_951_);
lean_dec_ref(v_inst_949_);
lean_dec_ref(v_inst_948_);
lean_inc(v_fallback_952_);
return v_fallback_952_;
}
else
{
lean_object* v___x_957_; 
v___x_957_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_948_, v_inst_949_, v_m_950_, v_a_951_, v_fallback_952_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_958_, lean_object* v_00_u03b2_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_m_962_, lean_object* v_a_963_, lean_object* v_fallback_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_HashMap_Raw_getKeyD(v_00_u03b1_958_, v_00_u03b2_959_, v_inst_960_, v_inst_961_, v_m_962_, v_a_963_, v_fallback_964_);
lean_dec(v_fallback_964_);
lean_dec_ref(v_m_962_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg(lean_object* v_inst_966_, lean_object* v_inst_967_, lean_object* v_inst_968_, lean_object* v_m_969_, lean_object* v_a_970_){
_start:
{
lean_object* v_buckets_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_buckets_971_ = lean_ctor_get(v_m_969_, 1);
v___x_972_ = lean_unsigned_to_nat(0u);
v___x_973_ = lean_array_get_size(v_buckets_971_);
v___x_974_ = lean_nat_dec_lt(v___x_972_, v___x_973_);
if (v___x_974_ == 0)
{
lean_dec(v_a_970_);
lean_dec_ref(v_inst_967_);
lean_dec_ref(v_inst_966_);
lean_inc(v_inst_968_);
return v_inst_968_;
}
else
{
lean_object* v___x_975_; 
v___x_975_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_966_, v_inst_967_, v_inst_968_, v_m_969_, v_a_970_);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v_m_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_HashMap_Raw_getKey_x21___redArg(v_inst_976_, v_inst_977_, v_inst_978_, v_m_979_, v_a_980_);
lean_dec_ref(v_m_979_);
lean_dec(v_inst_978_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21(lean_object* v_00_u03b1_982_, lean_object* v_00_u03b2_983_, lean_object* v_inst_984_, lean_object* v_inst_985_, lean_object* v_inst_986_, lean_object* v_m_987_, lean_object* v_a_988_){
_start:
{
lean_object* v_buckets_989_; lean_object* v___x_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_buckets_989_ = lean_ctor_get(v_m_987_, 1);
v___x_990_ = lean_unsigned_to_nat(0u);
v___x_991_ = lean_array_get_size(v_buckets_989_);
v___x_992_ = lean_nat_dec_lt(v___x_990_, v___x_991_);
if (v___x_992_ == 0)
{
lean_dec(v_a_988_);
lean_dec_ref(v_inst_985_);
lean_dec_ref(v_inst_984_);
lean_inc(v_inst_986_);
return v_inst_986_;
}
else
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_984_, v_inst_985_, v_inst_986_, v_m_987_, v_a_988_);
return v___x_993_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_994_, lean_object* v_00_u03b2_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_m_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_HashMap_Raw_getKey_x21(v_00_u03b1_994_, v_00_u03b2_995_, v_inst_996_, v_inst_997_, v_inst_998_, v_m_999_, v_a_1000_);
lean_dec_ref(v_m_999_);
lean_dec(v_inst_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase___redArg(lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_m_1004_, lean_object* v_a_1005_){
_start:
{
lean_object* v_buckets_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; uint8_t v___x_1009_; 
v_buckets_1006_ = lean_ctor_get(v_m_1004_, 1);
v___x_1007_ = lean_unsigned_to_nat(0u);
v___x_1008_ = lean_array_get_size(v_buckets_1006_);
v___x_1009_ = lean_nat_dec_lt(v___x_1007_, v___x_1008_);
if (v___x_1009_ == 0)
{
lean_dec(v_a_1005_);
lean_dec_ref(v_inst_1003_);
lean_dec_ref(v_inst_1002_);
return v_m_1004_;
}
else
{
lean_object* v___x_1010_; 
v___x_1010_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1002_, v_inst_1003_, v_m_1004_, v_a_1005_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase(lean_object* v_00_u03b1_1011_, lean_object* v_00_u03b2_1012_, lean_object* v_inst_1013_, lean_object* v_inst_1014_, lean_object* v_m_1015_, lean_object* v_a_1016_){
_start:
{
lean_object* v_buckets_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_buckets_1017_ = lean_ctor_get(v_m_1015_, 1);
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = lean_array_get_size(v_buckets_1017_);
v___x_1020_ = lean_nat_dec_lt(v___x_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_dec(v_a_1016_);
lean_dec_ref(v_inst_1014_);
lean_dec_ref(v_inst_1013_);
return v_m_1015_;
}
else
{
lean_object* v___x_1021_; 
v___x_1021_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1013_, v_inst_1014_, v_m_1015_, v_a_1016_);
return v___x_1021_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg(lean_object* v_m_1022_){
_start:
{
lean_object* v_size_1023_; 
v_size_1023_ = lean_ctor_get(v_m_1022_, 0);
lean_inc(v_size_1023_);
return v_size_1023_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg___boxed(lean_object* v_m_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_HashMap_Raw_size___redArg(v_m_1024_);
lean_dec_ref(v_m_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size(lean_object* v_00_u03b1_1026_, lean_object* v_00_u03b2_1027_, lean_object* v_m_1028_){
_start:
{
lean_object* v_size_1029_; 
v_size_1029_ = lean_ctor_get(v_m_1028_, 0);
lean_inc(v_size_1029_);
return v_size_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___boxed(lean_object* v_00_u03b1_1030_, lean_object* v_00_u03b2_1031_, lean_object* v_m_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Std_HashMap_Raw_size(v_00_u03b1_1030_, v_00_u03b2_1031_, v_m_1032_);
lean_dec_ref(v_m_1032_);
return v_res_1033_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty___redArg(lean_object* v_m_1034_){
_start:
{
lean_object* v_size_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v_size_1035_ = lean_ctor_get(v_m_1034_, 0);
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_nat_dec_eq(v_size_1035_, v___x_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1038_){
_start:
{
uint8_t v_res_1039_; lean_object* v_r_1040_; 
v_res_1039_ = l_Std_HashMap_Raw_isEmpty___redArg(v_m_1038_);
lean_dec_ref(v_m_1038_);
v_r_1040_ = lean_box(v_res_1039_);
return v_r_1040_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty(lean_object* v_00_u03b1_1041_, lean_object* v_00_u03b2_1042_, lean_object* v_m_1043_){
_start:
{
lean_object* v_size_1044_; lean_object* v___x_1045_; uint8_t v___x_1046_; 
v_size_1044_ = lean_ctor_get(v_m_1043_, 0);
v___x_1045_ = lean_unsigned_to_nat(0u);
v___x_1046_ = lean_nat_dec_eq(v_size_1044_, v___x_1045_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1047_, lean_object* v_00_u03b2_1048_, lean_object* v_m_1049_){
_start:
{
uint8_t v_res_1050_; lean_object* v_r_1051_; 
v_res_1050_ = l_Std_HashMap_Raw_isEmpty(v_00_u03b1_1047_, v_00_u03b2_1048_, v_m_1049_);
lean_dec_ref(v_m_1049_);
v_r_1051_ = lean_box(v_res_1050_);
return v_r_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0(lean_object* v_a_1052_, lean_object* v_b_1053_, lean_object* v_d_1054_){
_start:
{
lean_object* v___x_1055_; 
v___x_1055_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1055_, 0, v_a_1052_);
lean_ctor_set(v___x_1055_, 1, v_d_1054_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_a_1056_, lean_object* v_b_1057_, lean_object* v_d_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Std_HashMap_Raw_keys___redArg___lam__0(v_a_1056_, v_b_1057_, v_d_1058_);
lean_dec(v_b_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__1(lean_object* v___x_1060_, lean_object* v___f_1061_, lean_object* v_l_1062_, lean_object* v_acc_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1060_, v___f_1061_, v_acc_1063_, v_l_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg(lean_object* v_m_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v_buckets_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; uint8_t v___x_1094_; 
v___x_1089_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1090_ = lean_ctor_get(v_m_1088_, 1);
lean_inc_ref(v_buckets_1090_);
lean_dec_ref(v_m_1088_);
v___x_1091_ = lean_box(0);
v___x_1092_ = lean_array_get_size(v_buckets_1090_);
v___x_1093_ = lean_unsigned_to_nat(0u);
v___x_1094_ = lean_nat_dec_lt(v___x_1093_, v___x_1092_);
if (v___x_1094_ == 0)
{
lean_dec_ref(v_buckets_1090_);
return v___x_1091_;
}
else
{
lean_object* v___f_1095_; size_t v___x_1096_; size_t v___x_1097_; lean_object* v___x_1098_; 
v___f_1095_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1096_ = lean_usize_of_nat(v___x_1092_);
v___x_1097_ = ((size_t)0ULL);
v___x_1098_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1089_, v___f_1095_, v_buckets_1090_, v___x_1096_, v___x_1097_, v___x_1091_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys(lean_object* v_00_u03b1_1099_, lean_object* v_00_u03b2_1100_, lean_object* v_m_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v_buckets_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1102_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1103_ = lean_ctor_get(v_m_1101_, 1);
lean_inc_ref(v_buckets_1103_);
lean_dec_ref(v_m_1101_);
v___x_1104_ = lean_box(0);
v___x_1105_ = lean_array_get_size(v_buckets_1103_);
v___x_1106_ = lean_unsigned_to_nat(0u);
v___x_1107_ = lean_nat_dec_lt(v___x_1106_, v___x_1105_);
if (v___x_1107_ == 0)
{
lean_dec_ref(v_buckets_1103_);
return v___x_1104_;
}
else
{
lean_object* v___f_1108_; size_t v___x_1109_; size_t v___x_1110_; lean_object* v___x_1111_; 
v___f_1108_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1109_ = lean_usize_of_nat(v___x_1105_);
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1102_, v___f_1108_, v_buckets_1103_, v___x_1109_, v___x_1110_, v___x_1104_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList___redArg(lean_object* v_inst_1116_, lean_object* v_inst_1117_, lean_object* v_l_1118_){
_start:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1119_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1120_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1120_ == 0)
{
lean_dec(v_l_1118_);
lean_dec_ref(v_inst_1117_);
lean_dec_ref(v_inst_1116_);
return v___x_1119_;
}
else
{
lean_object* v___f_1121_; lean_object* v___x_1122_; 
v___f_1121_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1122_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1121_, v_inst_1116_, v_inst_1117_, v___x_1119_, v_l_1118_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList(lean_object* v_00_u03b1_1123_, lean_object* v_00_u03b2_1124_, lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_l_1127_){
_start:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1129_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1129_ == 0)
{
lean_dec(v_l_1127_);
lean_dec_ref(v_inst_1126_);
lean_dec_ref(v_inst_1125_);
return v___x_1128_;
}
else
{
lean_object* v___f_1130_; lean_object* v___x_1131_; 
v___f_1130_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1131_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1130_, v_inst_1125_, v_inst_1126_, v___x_1128_, v_l_1127_);
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList___redArg(lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_l_1134_){
_start:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; 
v___x_1135_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1136_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1136_ == 0)
{
lean_dec(v_l_1134_);
lean_dec_ref(v_inst_1133_);
lean_dec_ref(v_inst_1132_);
return v___x_1135_;
}
else
{
lean_object* v___f_1137_; lean_object* v___x_1138_; 
v___f_1137_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1137_, v_inst_1132_, v_inst_1133_, v___x_1135_, v_l_1134_);
return v___x_1138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList(lean_object* v_00_u03b1_1139_, lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_l_1142_){
_start:
{
lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1143_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1144_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1144_ == 0)
{
lean_dec(v_l_1142_);
lean_dec_ref(v_inst_1141_);
lean_dec_ref(v_inst_1140_);
return v___x_1143_;
}
else
{
lean_object* v___f_1145_; lean_object* v___x_1146_; 
v___f_1145_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1146_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1145_, v_inst_1140_, v_inst_1141_, v___x_1143_, v_l_1142_);
return v___x_1146_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray___redArg(lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_a_1153_){
_start:
{
lean_object* v___x_1154_; uint8_t v___x_1155_; 
v___x_1154_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1155_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1155_ == 0)
{
lean_dec_ref(v_a_1153_);
lean_dec_ref(v_inst_1152_);
lean_dec_ref(v_inst_1151_);
return v___x_1154_;
}
else
{
lean_object* v___f_1156_; lean_object* v___x_1157_; 
v___f_1156_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1157_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1156_, v_inst_1151_, v_inst_1152_, v___x_1154_, v_a_1153_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray(lean_object* v_00_u03b1_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1164_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1164_ == 0)
{
lean_dec_ref(v_a_1162_);
lean_dec_ref(v_inst_1161_);
lean_dec_ref(v_inst_1160_);
return v___x_1163_;
}
else
{
lean_object* v___f_1165_; lean_object* v___x_1166_; 
v___f_1165_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1166_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1165_, v_inst_1160_, v_inst_1161_, v___x_1163_, v_a_1162_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter___redArg(lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_m_1169_, lean_object* v_a_1170_, lean_object* v_f_1171_){
_start:
{
lean_object* v_buckets_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; uint8_t v___x_1175_; 
v_buckets_1172_ = lean_ctor_get(v_m_1169_, 1);
v___x_1173_ = lean_unsigned_to_nat(0u);
v___x_1174_ = lean_array_get_size(v_buckets_1172_);
v___x_1175_ = lean_nat_dec_lt(v___x_1173_, v___x_1174_);
if (v___x_1175_ == 0)
{
lean_object* v___x_1176_; 
lean_dec_ref(v_f_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_m_1169_);
lean_dec_ref(v_inst_1168_);
lean_dec_ref(v_inst_1167_);
v___x_1176_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1176_;
}
else
{
lean_object* v___x_1177_; 
v___x_1177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1167_, v_inst_1168_, v_m_1169_, v_a_1170_, v_f_1171_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter(lean_object* v_00_u03b1_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_m_1183_, lean_object* v_a_1184_, lean_object* v_f_1185_){
_start:
{
lean_object* v_buckets_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; uint8_t v___x_1189_; 
v_buckets_1186_ = lean_ctor_get(v_m_1183_, 1);
v___x_1187_ = lean_unsigned_to_nat(0u);
v___x_1188_ = lean_array_get_size(v_buckets_1186_);
v___x_1189_ = lean_nat_dec_lt(v___x_1187_, v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
lean_dec_ref(v_f_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_m_1183_);
lean_dec_ref(v_inst_1182_);
lean_dec_ref(v_inst_1180_);
v___x_1190_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1190_;
}
else
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1180_, v_inst_1182_, v_m_1183_, v_a_1184_, v_f_1185_);
return v___x_1191_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify___redArg(lean_object* v_inst_1192_, lean_object* v_inst_1193_, lean_object* v_m_1194_, lean_object* v_a_1195_, lean_object* v_f_1196_){
_start:
{
lean_object* v_buckets_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; uint8_t v___x_1200_; 
v_buckets_1197_ = lean_ctor_get(v_m_1194_, 1);
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_array_get_size(v_buckets_1197_);
v___x_1200_ = lean_nat_dec_lt(v___x_1198_, v___x_1199_);
if (v___x_1200_ == 0)
{
lean_object* v___x_1201_; 
lean_dec(v_f_1196_);
lean_dec(v_a_1195_);
lean_dec_ref(v_m_1194_);
lean_dec_ref(v_inst_1193_);
lean_dec_ref(v_inst_1192_);
v___x_1201_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1201_;
}
else
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1192_, v_inst_1193_, v_m_1194_, v_a_1195_, v_f_1196_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify(lean_object* v_00_u03b1_1203_, lean_object* v_00_u03b2_1204_, lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_m_1208_, lean_object* v_a_1209_, lean_object* v_f_1210_){
_start:
{
lean_object* v_buckets_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_buckets_1211_ = lean_ctor_get(v_m_1208_, 1);
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = lean_array_get_size(v_buckets_1211_);
v___x_1214_ = lean_nat_dec_lt(v___x_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; 
lean_dec(v_f_1210_);
lean_dec(v_a_1209_);
lean_dec_ref(v_m_1208_);
lean_dec_ref(v_inst_1207_);
lean_dec_ref(v_inst_1205_);
v___x_1215_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; 
v___x_1216_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1205_, v_inst_1207_, v_m_1208_, v_a_1209_, v_f_1210_);
return v___x_1216_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__0(lean_object* v_a_1217_, lean_object* v_b_1218_, lean_object* v_d_1219_){
_start:
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v_a_1217_);
lean_ctor_set(v___x_1220_, 1, v_b_1218_);
v___x_1221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v_d_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__1(lean_object* v___x_1222_, lean_object* v___f_1223_, lean_object* v_l_1224_, lean_object* v_acc_1225_){
_start:
{
lean_object* v___x_1226_; 
v___x_1226_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1222_, v___f_1223_, v_acc_1225_, v_l_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg(lean_object* v_m_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v_buckets_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v___x_1232_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1233_ = lean_ctor_get(v_m_1231_, 1);
lean_inc_ref(v_buckets_1233_);
lean_dec_ref(v_m_1231_);
v___x_1234_ = lean_box(0);
v___x_1235_ = lean_array_get_size(v_buckets_1233_);
v___x_1236_ = lean_unsigned_to_nat(0u);
v___x_1237_ = lean_nat_dec_lt(v___x_1236_, v___x_1235_);
if (v___x_1237_ == 0)
{
lean_dec_ref(v_buckets_1233_);
return v___x_1234_;
}
else
{
lean_object* v___f_1238_; size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v___f_1238_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1239_ = lean_usize_of_nat(v___x_1235_);
v___x_1240_ = ((size_t)0ULL);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1232_, v___f_1238_, v_buckets_1233_, v___x_1239_, v___x_1240_, v___x_1234_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList(lean_object* v_00_u03b1_1242_, lean_object* v_00_u03b2_1243_, lean_object* v_m_1244_){
_start:
{
lean_object* v___x_1245_; lean_object* v_buckets_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1245_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1246_ = lean_ctor_get(v_m_1244_, 1);
lean_inc_ref(v_buckets_1246_);
lean_dec_ref(v_m_1244_);
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_array_get_size(v_buckets_1246_);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_nat_dec_lt(v___x_1249_, v___x_1248_);
if (v___x_1250_ == 0)
{
lean_dec_ref(v_buckets_1246_);
return v___x_1247_;
}
else
{
lean_object* v___f_1251_; size_t v___x_1252_; size_t v___x_1253_; lean_object* v___x_1254_; 
v___f_1251_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1252_ = lean_usize_of_nat(v___x_1248_);
v___x_1253_ = ((size_t)0ULL);
v___x_1254_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1245_, v___f_1251_, v_buckets_1246_, v___x_1252_, v___x_1253_, v___x_1247_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg___lam__0(lean_object* v_inst_1255_, lean_object* v_f_1256_, lean_object* v_acc_1257_, lean_object* v_l_1258_){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1255_, v_f_1256_, v_acc_1257_, v_l_1258_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg(lean_object* v_inst_1260_, lean_object* v_f_1261_, lean_object* v_init_1262_, lean_object* v_b_1263_){
_start:
{
lean_object* v_buckets_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; uint8_t v___x_1267_; 
v_buckets_1264_ = lean_ctor_get(v_b_1263_, 1);
lean_inc_ref(v_buckets_1264_);
lean_dec_ref(v_b_1263_);
v___x_1265_ = lean_unsigned_to_nat(0u);
v___x_1266_ = lean_array_get_size(v_buckets_1264_);
v___x_1267_ = lean_nat_dec_lt(v___x_1265_, v___x_1266_);
if (v___x_1267_ == 0)
{
lean_object* v_toApplicative_1268_; lean_object* v_toPure_1269_; lean_object* v___x_1270_; 
lean_dec_ref(v_buckets_1264_);
lean_dec(v_f_1261_);
v_toApplicative_1268_ = lean_ctor_get(v_inst_1260_, 0);
lean_inc_ref(v_toApplicative_1268_);
lean_dec_ref(v_inst_1260_);
v_toPure_1269_ = lean_ctor_get(v_toApplicative_1268_, 1);
lean_inc(v_toPure_1269_);
lean_dec_ref(v_toApplicative_1268_);
v___x_1270_ = lean_apply_2(v_toPure_1269_, lean_box(0), v_init_1262_);
return v___x_1270_;
}
else
{
lean_object* v___f_1271_; uint8_t v___x_1272_; 
lean_inc_ref(v_inst_1260_);
v___f_1271_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1271_, 0, v_inst_1260_);
lean_closure_set(v___f_1271_, 1, v_f_1261_);
v___x_1272_ = lean_nat_dec_le(v___x_1266_, v___x_1266_);
if (v___x_1272_ == 0)
{
if (v___x_1267_ == 0)
{
lean_object* v_toApplicative_1273_; lean_object* v_toPure_1274_; lean_object* v___x_1275_; 
lean_dec_ref(v___f_1271_);
lean_dec_ref(v_buckets_1264_);
v_toApplicative_1273_ = lean_ctor_get(v_inst_1260_, 0);
lean_inc_ref(v_toApplicative_1273_);
lean_dec_ref(v_inst_1260_);
v_toPure_1274_ = lean_ctor_get(v_toApplicative_1273_, 1);
lean_inc(v_toPure_1274_);
lean_dec_ref(v_toApplicative_1273_);
v___x_1275_ = lean_apply_2(v_toPure_1274_, lean_box(0), v_init_1262_);
return v___x_1275_;
}
else
{
size_t v___x_1276_; size_t v___x_1277_; lean_object* v___x_1278_; 
v___x_1276_ = ((size_t)0ULL);
v___x_1277_ = lean_usize_of_nat(v___x_1266_);
v___x_1278_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1260_, v___f_1271_, v_buckets_1264_, v___x_1276_, v___x_1277_, v_init_1262_);
return v___x_1278_;
}
}
else
{
size_t v___x_1279_; size_t v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = lean_usize_of_nat(v___x_1266_);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1260_, v___f_1271_, v_buckets_1264_, v___x_1279_, v___x_1280_, v_init_1262_);
return v___x_1281_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object* v_00_u03b1_1282_, lean_object* v_00_u03b2_1283_, lean_object* v_m_1284_, lean_object* v_inst_1285_, lean_object* v_00_u03b3_1286_, lean_object* v_f_1287_, lean_object* v_init_1288_, lean_object* v_b_1289_){
_start:
{
lean_object* v_buckets_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_buckets_1290_ = lean_ctor_get(v_b_1289_, 1);
lean_inc_ref(v_buckets_1290_);
lean_dec_ref(v_b_1289_);
v___x_1291_ = lean_unsigned_to_nat(0u);
v___x_1292_ = lean_array_get_size(v_buckets_1290_);
v___x_1293_ = lean_nat_dec_lt(v___x_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_object* v_toApplicative_1294_; lean_object* v_toPure_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v_buckets_1290_);
lean_dec(v_f_1287_);
v_toApplicative_1294_ = lean_ctor_get(v_inst_1285_, 0);
lean_inc_ref(v_toApplicative_1294_);
lean_dec_ref(v_inst_1285_);
v_toPure_1295_ = lean_ctor_get(v_toApplicative_1294_, 1);
lean_inc(v_toPure_1295_);
lean_dec_ref(v_toApplicative_1294_);
v___x_1296_ = lean_apply_2(v_toPure_1295_, lean_box(0), v_init_1288_);
return v___x_1296_;
}
else
{
lean_object* v___f_1297_; uint8_t v___x_1298_; 
lean_inc_ref(v_inst_1285_);
v___f_1297_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1297_, 0, v_inst_1285_);
lean_closure_set(v___f_1297_, 1, v_f_1287_);
v___x_1298_ = lean_nat_dec_le(v___x_1292_, v___x_1292_);
if (v___x_1298_ == 0)
{
if (v___x_1293_ == 0)
{
lean_object* v_toApplicative_1299_; lean_object* v_toPure_1300_; lean_object* v___x_1301_; 
lean_dec_ref(v___f_1297_);
lean_dec_ref(v_buckets_1290_);
v_toApplicative_1299_ = lean_ctor_get(v_inst_1285_, 0);
lean_inc_ref(v_toApplicative_1299_);
lean_dec_ref(v_inst_1285_);
v_toPure_1300_ = lean_ctor_get(v_toApplicative_1299_, 1);
lean_inc(v_toPure_1300_);
lean_dec_ref(v_toApplicative_1299_);
v___x_1301_ = lean_apply_2(v_toPure_1300_, lean_box(0), v_init_1288_);
return v___x_1301_;
}
else
{
size_t v___x_1302_; size_t v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = ((size_t)0ULL);
v___x_1303_ = lean_usize_of_nat(v___x_1292_);
v___x_1304_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1285_, v___f_1297_, v_buckets_1290_, v___x_1302_, v___x_1303_, v_init_1288_);
return v___x_1304_;
}
}
else
{
size_t v___x_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = ((size_t)0ULL);
v___x_1306_ = lean_usize_of_nat(v___x_1292_);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1285_, v___f_1297_, v_buckets_1290_, v___x_1305_, v___x_1306_, v_init_1288_);
return v___x_1307_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object* v_f_1308_, lean_object* v_x1_1309_, lean_object* v_x2_1310_, lean_object* v_x3_1311_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = lean_apply_3(v_f_1308_, v_x1_1309_, v_x2_1310_, v_x3_1311_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__1(lean_object* v___x_1313_, lean_object* v___f_1314_, lean_object* v_acc_1315_, lean_object* v_l_1316_){
_start:
{
lean_object* v___x_1317_; 
v___x_1317_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1313_, v___f_1314_, v_acc_1315_, v_l_1316_);
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object* v_f_1318_, lean_object* v_init_1319_, lean_object* v_b_1320_){
_start:
{
lean_object* v___x_1321_; lean_object* v_buckets_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1321_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1322_ = lean_ctor_get(v_b_1320_, 1);
lean_inc_ref(v_buckets_1322_);
lean_dec_ref(v_b_1320_);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_array_get_size(v_buckets_1322_);
v___x_1325_ = lean_nat_dec_lt(v___x_1323_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec_ref(v_buckets_1322_);
lean_dec(v_f_1318_);
return v_init_1319_;
}
else
{
lean_object* v___f_1326_; lean_object* v___f_1327_; uint8_t v___x_1328_; 
v___f_1326_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1326_, 0, v_f_1318_);
v___f_1327_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1327_, 0, v___x_1321_);
lean_closure_set(v___f_1327_, 1, v___f_1326_);
v___x_1328_ = lean_nat_dec_le(v___x_1324_, v___x_1324_);
if (v___x_1328_ == 0)
{
if (v___x_1325_ == 0)
{
lean_dec_ref(v___f_1327_);
lean_dec_ref(v_buckets_1322_);
return v_init_1319_;
}
else
{
size_t v___x_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((size_t)0ULL);
v___x_1330_ = lean_usize_of_nat(v___x_1324_);
v___x_1331_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1321_, v___f_1327_, v_buckets_1322_, v___x_1329_, v___x_1330_, v_init_1319_);
return v___x_1331_;
}
}
else
{
size_t v___x_1332_; size_t v___x_1333_; lean_object* v___x_1334_; 
v___x_1332_ = ((size_t)0ULL);
v___x_1333_ = lean_usize_of_nat(v___x_1324_);
v___x_1334_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1321_, v___f_1327_, v_buckets_1322_, v___x_1332_, v___x_1333_, v_init_1319_);
return v___x_1334_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object* v_00_u03b1_1335_, lean_object* v_00_u03b2_1336_, lean_object* v_00_u03b3_1337_, lean_object* v_f_1338_, lean_object* v_init_1339_, lean_object* v_b_1340_){
_start:
{
lean_object* v___x_1341_; lean_object* v_buckets_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; uint8_t v___x_1345_; 
v___x_1341_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1342_ = lean_ctor_get(v_b_1340_, 1);
lean_inc_ref(v_buckets_1342_);
lean_dec_ref(v_b_1340_);
v___x_1343_ = lean_unsigned_to_nat(0u);
v___x_1344_ = lean_array_get_size(v_buckets_1342_);
v___x_1345_ = lean_nat_dec_lt(v___x_1343_, v___x_1344_);
if (v___x_1345_ == 0)
{
lean_dec_ref(v_buckets_1342_);
lean_dec(v_f_1338_);
return v_init_1339_;
}
else
{
lean_object* v___f_1346_; lean_object* v___f_1347_; uint8_t v___x_1348_; 
v___f_1346_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1346_, 0, v_f_1338_);
v___f_1347_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1347_, 0, v___x_1341_);
lean_closure_set(v___f_1347_, 1, v___f_1346_);
v___x_1348_ = lean_nat_dec_le(v___x_1344_, v___x_1344_);
if (v___x_1348_ == 0)
{
if (v___x_1345_ == 0)
{
lean_dec_ref(v___f_1347_);
lean_dec_ref(v_buckets_1342_);
return v_init_1339_;
}
else
{
size_t v___x_1349_; size_t v___x_1350_; lean_object* v___x_1351_; 
v___x_1349_ = ((size_t)0ULL);
v___x_1350_ = lean_usize_of_nat(v___x_1344_);
v___x_1351_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1341_, v___f_1347_, v_buckets_1342_, v___x_1349_, v___x_1350_, v_init_1339_);
return v___x_1351_;
}
}
else
{
size_t v___x_1352_; size_t v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = ((size_t)0ULL);
v___x_1353_ = lean_usize_of_nat(v___x_1344_);
v___x_1354_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1341_, v___f_1347_, v_buckets_1342_, v___x_1352_, v___x_1353_, v_init_1339_);
return v___x_1354_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object* v_f_1355_, lean_object* v_x_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = lean_apply_2(v_f_1355_, v___y_1357_, v___y_1358_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__1(lean_object* v_inst_1360_, lean_object* v___f_1361_, lean_object* v_x_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_box(0);
v___x_1365_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1360_, v___f_1361_, v___x_1364_, v___y_1363_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object* v_inst_1366_, lean_object* v_f_1367_, lean_object* v_b_1368_){
_start:
{
lean_object* v_buckets_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_buckets_1369_ = lean_ctor_get(v_b_1368_, 1);
lean_inc_ref(v_buckets_1369_);
lean_dec_ref(v_b_1368_);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = lean_array_get_size(v_buckets_1369_);
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_nat_dec_lt(v___x_1370_, v___x_1371_);
if (v___x_1373_ == 0)
{
lean_object* v_toApplicative_1374_; lean_object* v_toPure_1375_; lean_object* v___x_1376_; 
lean_dec_ref(v_buckets_1369_);
lean_dec(v_f_1367_);
v_toApplicative_1374_ = lean_ctor_get(v_inst_1366_, 0);
lean_inc_ref(v_toApplicative_1374_);
lean_dec_ref(v_inst_1366_);
v_toPure_1375_ = lean_ctor_get(v_toApplicative_1374_, 1);
lean_inc(v_toPure_1375_);
lean_dec_ref(v_toApplicative_1374_);
v___x_1376_ = lean_apply_2(v_toPure_1375_, lean_box(0), v___x_1372_);
return v___x_1376_;
}
else
{
lean_object* v___f_1377_; lean_object* v___f_1378_; uint8_t v___x_1379_; 
v___f_1377_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1377_, 0, v_f_1367_);
lean_inc_ref(v_inst_1366_);
v___f_1378_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1378_, 0, v_inst_1366_);
lean_closure_set(v___f_1378_, 1, v___f_1377_);
v___x_1379_ = lean_nat_dec_le(v___x_1371_, v___x_1371_);
if (v___x_1379_ == 0)
{
if (v___x_1373_ == 0)
{
lean_object* v_toApplicative_1380_; lean_object* v_toPure_1381_; lean_object* v___x_1382_; 
lean_dec_ref(v___f_1378_);
lean_dec_ref(v_buckets_1369_);
v_toApplicative_1380_ = lean_ctor_get(v_inst_1366_, 0);
lean_inc_ref(v_toApplicative_1380_);
lean_dec_ref(v_inst_1366_);
v_toPure_1381_ = lean_ctor_get(v_toApplicative_1380_, 1);
lean_inc(v_toPure_1381_);
lean_dec_ref(v_toApplicative_1380_);
v___x_1382_ = lean_apply_2(v_toPure_1381_, lean_box(0), v___x_1372_);
return v___x_1382_;
}
else
{
size_t v___x_1383_; size_t v___x_1384_; lean_object* v___x_1385_; 
v___x_1383_ = ((size_t)0ULL);
v___x_1384_ = lean_usize_of_nat(v___x_1371_);
v___x_1385_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1366_, v___f_1378_, v_buckets_1369_, v___x_1383_, v___x_1384_, v___x_1372_);
return v___x_1385_;
}
}
else
{
size_t v___x_1386_; size_t v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = ((size_t)0ULL);
v___x_1387_ = lean_usize_of_nat(v___x_1371_);
v___x_1388_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1366_, v___f_1378_, v_buckets_1369_, v___x_1386_, v___x_1387_, v___x_1372_);
return v___x_1388_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object* v_00_u03b1_1389_, lean_object* v_00_u03b2_1390_, lean_object* v_m_1391_, lean_object* v_inst_1392_, lean_object* v_f_1393_, lean_object* v_b_1394_){
_start:
{
lean_object* v_buckets_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_buckets_1395_ = lean_ctor_get(v_b_1394_, 1);
lean_inc_ref(v_buckets_1395_);
lean_dec_ref(v_b_1394_);
v___x_1396_ = lean_unsigned_to_nat(0u);
v___x_1397_ = lean_array_get_size(v_buckets_1395_);
v___x_1398_ = lean_box(0);
v___x_1399_ = lean_nat_dec_lt(v___x_1396_, v___x_1397_);
if (v___x_1399_ == 0)
{
lean_object* v_toApplicative_1400_; lean_object* v_toPure_1401_; lean_object* v___x_1402_; 
lean_dec_ref(v_buckets_1395_);
lean_dec(v_f_1393_);
v_toApplicative_1400_ = lean_ctor_get(v_inst_1392_, 0);
lean_inc_ref(v_toApplicative_1400_);
lean_dec_ref(v_inst_1392_);
v_toPure_1401_ = lean_ctor_get(v_toApplicative_1400_, 1);
lean_inc(v_toPure_1401_);
lean_dec_ref(v_toApplicative_1400_);
v___x_1402_ = lean_apply_2(v_toPure_1401_, lean_box(0), v___x_1398_);
return v___x_1402_;
}
else
{
lean_object* v___f_1403_; lean_object* v___f_1404_; uint8_t v___x_1405_; 
v___f_1403_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1403_, 0, v_f_1393_);
lean_inc_ref(v_inst_1392_);
v___f_1404_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1404_, 0, v_inst_1392_);
lean_closure_set(v___f_1404_, 1, v___f_1403_);
v___x_1405_ = lean_nat_dec_le(v___x_1397_, v___x_1397_);
if (v___x_1405_ == 0)
{
if (v___x_1399_ == 0)
{
lean_object* v_toApplicative_1406_; lean_object* v_toPure_1407_; lean_object* v___x_1408_; 
lean_dec_ref(v___f_1404_);
lean_dec_ref(v_buckets_1395_);
v_toApplicative_1406_ = lean_ctor_get(v_inst_1392_, 0);
lean_inc_ref(v_toApplicative_1406_);
lean_dec_ref(v_inst_1392_);
v_toPure_1407_ = lean_ctor_get(v_toApplicative_1406_, 1);
lean_inc(v_toPure_1407_);
lean_dec_ref(v_toApplicative_1406_);
v___x_1408_ = lean_apply_2(v_toPure_1407_, lean_box(0), v___x_1398_);
return v___x_1408_;
}
else
{
size_t v___x_1409_; size_t v___x_1410_; lean_object* v___x_1411_; 
v___x_1409_ = ((size_t)0ULL);
v___x_1410_ = lean_usize_of_nat(v___x_1397_);
v___x_1411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1392_, v___f_1404_, v_buckets_1395_, v___x_1409_, v___x_1410_, v___x_1398_);
return v___x_1411_;
}
}
else
{
size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; 
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = lean_usize_of_nat(v___x_1397_);
v___x_1414_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1392_, v___f_1404_, v_buckets_1395_, v___x_1412_, v___x_1413_, v___x_1398_);
return v___x_1414_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg___lam__0(lean_object* v_inst_1415_, lean_object* v_f_1416_, lean_object* v_a_1417_, lean_object* v_x_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1415_, v_f_1416_, v_a_1417_, v___y_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object* v_inst_1421_, lean_object* v_f_1422_, lean_object* v_init_1423_, lean_object* v_b_1424_){
_start:
{
lean_object* v_buckets_1425_; lean_object* v___f_1426_; size_t v_sz_1427_; size_t v___x_1428_; lean_object* v___x_1429_; 
v_buckets_1425_ = lean_ctor_get(v_b_1424_, 1);
lean_inc_ref(v_buckets_1425_);
lean_dec_ref(v_b_1424_);
lean_inc_ref(v_inst_1421_);
v___f_1426_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1426_, 0, v_inst_1421_);
lean_closure_set(v___f_1426_, 1, v_f_1422_);
v_sz_1427_ = lean_array_size(v_buckets_1425_);
v___x_1428_ = ((size_t)0ULL);
v___x_1429_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1421_, v_buckets_1425_, v___f_1426_, v_sz_1427_, v___x_1428_, v_init_1423_);
return v___x_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object* v_00_u03b1_1430_, lean_object* v_00_u03b2_1431_, lean_object* v_m_1432_, lean_object* v_inst_1433_, lean_object* v_00_u03b3_1434_, lean_object* v_f_1435_, lean_object* v_init_1436_, lean_object* v_b_1437_){
_start:
{
lean_object* v_buckets_1438_; lean_object* v___f_1439_; size_t v_sz_1440_; size_t v___x_1441_; lean_object* v___x_1442_; 
v_buckets_1438_ = lean_ctor_get(v_b_1437_, 1);
lean_inc_ref(v_buckets_1438_);
lean_dec_ref(v_b_1437_);
lean_inc_ref(v_inst_1433_);
v___f_1439_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1439_, 0, v_inst_1433_);
lean_closure_set(v___f_1439_, 1, v_f_1435_);
v_sz_1440_ = lean_array_size(v_buckets_1438_);
v___x_1441_ = ((size_t)0ULL);
v___x_1442_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1433_, v_buckets_1438_, v___f_1439_, v_sz_1440_, v___x_1441_, v_init_1436_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1443_, lean_object* v_x_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___y_1445_);
lean_ctor_set(v___x_1447_, 1, v___y_1446_);
v___x_1448_ = lean_apply_1(v_f_1443_, v___x_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1449_, lean_object* v_m_1450_, lean_object* v_f_1451_){
_start:
{
lean_object* v_buckets_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; 
v_buckets_1452_ = lean_ctor_get(v_m_1450_, 1);
lean_inc_ref(v_buckets_1452_);
lean_dec_ref(v_m_1450_);
v___x_1453_ = lean_unsigned_to_nat(0u);
v___x_1454_ = lean_array_get_size(v_buckets_1452_);
v___x_1455_ = lean_box(0);
v___x_1456_ = lean_nat_dec_lt(v___x_1453_, v___x_1454_);
if (v___x_1456_ == 0)
{
lean_object* v_toApplicative_1457_; lean_object* v_toPure_1458_; lean_object* v___x_1459_; 
lean_dec_ref(v_buckets_1452_);
lean_dec(v_f_1451_);
v_toApplicative_1457_ = lean_ctor_get(v_inst_1449_, 0);
lean_inc_ref(v_toApplicative_1457_);
lean_dec_ref(v_inst_1449_);
v_toPure_1458_ = lean_ctor_get(v_toApplicative_1457_, 1);
lean_inc(v_toPure_1458_);
lean_dec_ref(v_toApplicative_1457_);
v___x_1459_ = lean_apply_2(v_toPure_1458_, lean_box(0), v___x_1455_);
return v___x_1459_;
}
else
{
lean_object* v___f_1460_; lean_object* v___f_1461_; uint8_t v___x_1462_; 
v___f_1460_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1460_, 0, v_f_1451_);
lean_inc_ref(v_inst_1449_);
v___f_1461_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1461_, 0, v_inst_1449_);
lean_closure_set(v___f_1461_, 1, v___f_1460_);
v___x_1462_ = lean_nat_dec_le(v___x_1454_, v___x_1454_);
if (v___x_1462_ == 0)
{
if (v___x_1456_ == 0)
{
lean_object* v_toApplicative_1463_; lean_object* v_toPure_1464_; lean_object* v___x_1465_; 
lean_dec_ref(v___f_1461_);
lean_dec_ref(v_buckets_1452_);
v_toApplicative_1463_ = lean_ctor_get(v_inst_1449_, 0);
lean_inc_ref(v_toApplicative_1463_);
lean_dec_ref(v_inst_1449_);
v_toPure_1464_ = lean_ctor_get(v_toApplicative_1463_, 1);
lean_inc(v_toPure_1464_);
lean_dec_ref(v_toApplicative_1463_);
v___x_1465_ = lean_apply_2(v_toPure_1464_, lean_box(0), v___x_1455_);
return v___x_1465_;
}
else
{
size_t v___x_1466_; size_t v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = ((size_t)0ULL);
v___x_1467_ = lean_usize_of_nat(v___x_1454_);
v___x_1468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1449_, v___f_1461_, v_buckets_1452_, v___x_1466_, v___x_1467_, v___x_1455_);
return v___x_1468_;
}
}
else
{
size_t v___x_1469_; size_t v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = ((size_t)0ULL);
v___x_1470_ = lean_usize_of_nat(v___x_1454_);
v___x_1471_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1449_, v___f_1461_, v_buckets_1452_, v___x_1469_, v___x_1470_, v___x_1455_);
return v___x_1471_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1472_){
_start:
{
lean_object* v___f_1473_; 
v___f_1473_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1473_, 0, v_inst_1472_);
return v___f_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1474_, lean_object* v_00_u03b2_1475_, lean_object* v_m_1476_, lean_object* v_inst_1477_){
_start:
{
lean_object* v___f_1478_; 
v___f_1478_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1478_, 0, v_inst_1477_);
return v___f_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1479_, lean_object* v_a_1480_, lean_object* v_b_1481_, lean_object* v_acc_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1483_, 0, v_a_1480_);
lean_ctor_set(v___x_1483_, 1, v_b_1481_);
v___x_1484_ = lean_apply_2(v_f_1479_, v___x_1483_, v_acc_1482_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1485_, lean_object* v___f_1486_, lean_object* v_a_1487_, lean_object* v_x_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1485_, v___f_1486_, v_a_1487_, v___y_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1491_, lean_object* v_00_u03b2_1492_, lean_object* v_m_1493_, lean_object* v_init_1494_, lean_object* v_f_1495_){
_start:
{
lean_object* v_buckets_1496_; lean_object* v___f_1497_; lean_object* v___f_1498_; size_t v_sz_1499_; size_t v___x_1500_; lean_object* v___x_1501_; 
v_buckets_1496_ = lean_ctor_get(v_m_1493_, 1);
lean_inc_ref(v_buckets_1496_);
lean_dec_ref(v_m_1493_);
v___f_1497_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1497_, 0, v_f_1495_);
lean_inc_ref(v_inst_1491_);
v___f_1498_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1498_, 0, v_inst_1491_);
lean_closure_set(v___f_1498_, 1, v___f_1497_);
v_sz_1499_ = lean_array_size(v_buckets_1496_);
v___x_1500_ = ((size_t)0ULL);
v___x_1501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1491_, v_buckets_1496_, v___f_1498_, v_sz_1499_, v___x_1500_, v_init_1494_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1502_){
_start:
{
lean_object* v___f_1503_; 
v___f_1503_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1503_, 0, v_inst_1502_);
return v___f_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1504_, lean_object* v_00_u03b2_1505_, lean_object* v_m_1506_, lean_object* v_inst_1507_){
_start:
{
lean_object* v___f_1508_; 
v___f_1508_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1508_, 0, v_inst_1507_);
return v___f_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object* v_p_1509_, lean_object* v___x_1510_, lean_object* v___x_1511_, lean_object* v_a_1512_, lean_object* v_b_1513_, lean_object* v_acc_1514_){
_start:
{
lean_object* v___x_1515_; uint8_t v___x_1516_; 
v___x_1515_ = lean_apply_2(v_p_1509_, v_a_1512_, v_b_1513_);
v___x_1516_ = lean_unbox(v___x_1515_);
if (v___x_1516_ == 0)
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
lean_dec_ref(v___x_1511_);
v___x_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
v___x_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___x_1510_);
v___x_1519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1511_);
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1521_, lean_object* v___x_1522_, lean_object* v___x_1523_, lean_object* v_a_1524_, lean_object* v_b_1525_, lean_object* v_acc_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Std_HashMap_Raw_all___redArg___lam__0(v_p_1521_, v___x_1522_, v___x_1523_, v_a_1524_, v_b_1525_, v_acc_1526_);
lean_dec_ref(v_acc_1526_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__1(lean_object* v___x_1528_, lean_object* v___f_1529_, lean_object* v_a_1530_, lean_object* v_x_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1533_; 
v___x_1533_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1528_, v___f_1529_, v_a_1530_, v___y_1532_);
return v___x_1533_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all___redArg(lean_object* v_m_1537_, lean_object* v_p_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v_buckets_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___f_1543_; lean_object* v___f_1544_; size_t v_sz_1545_; size_t v___x_1546_; lean_object* v___x_1547_; lean_object* v_fst_1548_; 
v___x_1539_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1540_ = lean_ctor_get(v_m_1537_, 1);
lean_inc_ref(v_buckets_1540_);
lean_dec_ref(v_m_1537_);
v___x_1541_ = lean_box(0);
v___x_1542_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1543_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1543_, 0, v_p_1538_);
lean_closure_set(v___f_1543_, 1, v___x_1541_);
lean_closure_set(v___f_1543_, 2, v___x_1542_);
v___f_1544_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1544_, 0, v___x_1539_);
lean_closure_set(v___f_1544_, 1, v___f_1543_);
v_sz_1545_ = lean_array_size(v_buckets_1540_);
v___x_1546_ = ((size_t)0ULL);
v___x_1547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1539_, v_buckets_1540_, v___f_1544_, v_sz_1545_, v___x_1546_, v___x_1542_);
v_fst_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_fst_1548_);
lean_dec(v___x_1547_);
if (lean_obj_tag(v_fst_1548_) == 0)
{
uint8_t v___x_1549_; 
v___x_1549_ = 1;
return v___x_1549_;
}
else
{
lean_object* v_val_1550_; uint8_t v___x_1551_; 
v_val_1550_ = lean_ctor_get(v_fst_1548_, 0);
lean_inc(v_val_1550_);
lean_dec_ref(v_fst_1548_);
v___x_1551_ = lean_unbox(v_val_1550_);
lean_dec(v_val_1550_);
return v___x_1551_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___boxed(lean_object* v_m_1552_, lean_object* v_p_1553_){
_start:
{
uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_res_1554_ = l_Std_HashMap_Raw_all___redArg(v_m_1552_, v_p_1553_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all(lean_object* v_00_u03b1_1556_, lean_object* v_00_u03b2_1557_, lean_object* v_m_1558_, lean_object* v_p_1559_){
_start:
{
lean_object* v___x_1560_; lean_object* v_buckets_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___f_1564_; lean_object* v___f_1565_; size_t v_sz_1566_; size_t v___x_1567_; lean_object* v___x_1568_; lean_object* v_fst_1569_; 
v___x_1560_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1561_ = lean_ctor_get(v_m_1558_, 1);
lean_inc_ref(v_buckets_1561_);
lean_dec_ref(v_m_1558_);
v___x_1562_ = lean_box(0);
v___x_1563_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1564_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1564_, 0, v_p_1559_);
lean_closure_set(v___f_1564_, 1, v___x_1562_);
lean_closure_set(v___f_1564_, 2, v___x_1563_);
v___f_1565_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1565_, 0, v___x_1560_);
lean_closure_set(v___f_1565_, 1, v___f_1564_);
v_sz_1566_ = lean_array_size(v_buckets_1561_);
v___x_1567_ = ((size_t)0ULL);
v___x_1568_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1560_, v_buckets_1561_, v___f_1565_, v_sz_1566_, v___x_1567_, v___x_1563_);
v_fst_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc(v_fst_1569_);
lean_dec(v___x_1568_);
if (lean_obj_tag(v_fst_1569_) == 0)
{
uint8_t v___x_1570_; 
v___x_1570_ = 1;
return v___x_1570_;
}
else
{
lean_object* v_val_1571_; uint8_t v___x_1572_; 
v_val_1571_ = lean_ctor_get(v_fst_1569_, 0);
lean_inc(v_val_1571_);
lean_dec_ref(v_fst_1569_);
v___x_1572_ = lean_unbox(v_val_1571_);
lean_dec(v_val_1571_);
return v___x_1572_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_00_u03b2_1574_, lean_object* v_m_1575_, lean_object* v_p_1576_){
_start:
{
uint8_t v_res_1577_; lean_object* v_r_1578_; 
v_res_1577_ = l_Std_HashMap_Raw_all(v_00_u03b1_1573_, v_00_u03b2_1574_, v_m_1575_, v_p_1576_);
v_r_1578_ = lean_box(v_res_1577_);
return v_r_1578_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0(lean_object* v_p_1579_, lean_object* v___x_1580_, lean_object* v___x_1581_, lean_object* v_a_1582_, lean_object* v_b_1583_, lean_object* v_acc_1584_){
_start:
{
lean_object* v___x_1585_; uint8_t v___x_1586_; 
v___x_1585_ = lean_apply_2(v_p_1579_, v_a_1582_, v_b_1583_);
v___x_1586_ = lean_unbox(v___x_1585_);
if (v___x_1586_ == 0)
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1580_);
return v___x_1587_;
}
else
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec_ref(v___x_1580_);
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1585_);
v___x_1589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1581_);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1591_, lean_object* v___x_1592_, lean_object* v___x_1593_, lean_object* v_a_1594_, lean_object* v_b_1595_, lean_object* v_acc_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Std_HashMap_Raw_any___redArg___lam__0(v_p_1591_, v___x_1592_, v___x_1593_, v_a_1594_, v_b_1595_, v_acc_1596_);
lean_dec_ref(v_acc_1596_);
return v_res_1597_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any___redArg(lean_object* v_m_1598_, lean_object* v_p_1599_){
_start:
{
lean_object* v___x_1600_; lean_object* v_buckets_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___f_1604_; lean_object* v___f_1605_; size_t v_sz_1606_; size_t v___x_1607_; lean_object* v___x_1608_; lean_object* v_fst_1609_; 
v___x_1600_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1601_ = lean_ctor_get(v_m_1598_, 1);
lean_inc_ref(v_buckets_1601_);
lean_dec_ref(v_m_1598_);
v___x_1602_ = lean_box(0);
v___x_1603_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1604_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1604_, 0, v_p_1599_);
lean_closure_set(v___f_1604_, 1, v___x_1603_);
lean_closure_set(v___f_1604_, 2, v___x_1602_);
v___f_1605_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1605_, 0, v___x_1600_);
lean_closure_set(v___f_1605_, 1, v___f_1604_);
v_sz_1606_ = lean_array_size(v_buckets_1601_);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1600_, v_buckets_1601_, v___f_1605_, v_sz_1606_, v___x_1607_, v___x_1603_);
v_fst_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_fst_1609_);
lean_dec(v___x_1608_);
if (lean_obj_tag(v_fst_1609_) == 0)
{
uint8_t v___x_1610_; 
v___x_1610_ = 0;
return v___x_1610_;
}
else
{
lean_object* v_val_1611_; uint8_t v___x_1612_; 
v_val_1611_ = lean_ctor_get(v_fst_1609_, 0);
lean_inc(v_val_1611_);
lean_dec_ref(v_fst_1609_);
v___x_1612_ = lean_unbox(v_val_1611_);
lean_dec(v_val_1611_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___boxed(lean_object* v_m_1613_, lean_object* v_p_1614_){
_start:
{
uint8_t v_res_1615_; lean_object* v_r_1616_; 
v_res_1615_ = l_Std_HashMap_Raw_any___redArg(v_m_1613_, v_p_1614_);
v_r_1616_ = lean_box(v_res_1615_);
return v_r_1616_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any(lean_object* v_00_u03b1_1617_, lean_object* v_00_u03b2_1618_, lean_object* v_m_1619_, lean_object* v_p_1620_){
_start:
{
lean_object* v___x_1621_; lean_object* v_buckets_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___f_1625_; lean_object* v___f_1626_; size_t v_sz_1627_; size_t v___x_1628_; lean_object* v___x_1629_; lean_object* v_fst_1630_; 
v___x_1621_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1622_ = lean_ctor_get(v_m_1619_, 1);
lean_inc_ref(v_buckets_1622_);
lean_dec_ref(v_m_1619_);
v___x_1623_ = lean_box(0);
v___x_1624_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1625_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1625_, 0, v_p_1620_);
lean_closure_set(v___f_1625_, 1, v___x_1624_);
lean_closure_set(v___f_1625_, 2, v___x_1623_);
v___f_1626_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1626_, 0, v___x_1621_);
lean_closure_set(v___f_1626_, 1, v___f_1625_);
v_sz_1627_ = lean_array_size(v_buckets_1622_);
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1621_, v_buckets_1622_, v___f_1626_, v_sz_1627_, v___x_1628_, v___x_1624_);
v_fst_1630_ = lean_ctor_get(v___x_1629_, 0);
lean_inc(v_fst_1630_);
lean_dec(v___x_1629_);
if (lean_obj_tag(v_fst_1630_) == 0)
{
uint8_t v___x_1631_; 
v___x_1631_ = 0;
return v___x_1631_;
}
else
{
lean_object* v_val_1632_; uint8_t v___x_1633_; 
v_val_1632_ = lean_ctor_get(v_fst_1630_, 0);
lean_inc(v_val_1632_);
lean_dec_ref(v_fst_1630_);
v___x_1633_ = lean_unbox(v_val_1632_);
lean_dec(v_val_1632_);
return v___x_1633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___boxed(lean_object* v_00_u03b1_1634_, lean_object* v_00_u03b2_1635_, lean_object* v_m_1636_, lean_object* v_p_1637_){
_start:
{
uint8_t v_res_1638_; lean_object* v_r_1639_; 
v_res_1638_ = l_Std_HashMap_Raw_any(v_00_u03b1_1634_, v_00_u03b2_1635_, v_m_1636_, v_p_1637_);
v_r_1639_ = lean_box(v_res_1638_);
return v_r_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_a_1642_, lean_object* v_b_1643_, lean_object* v_acc_1644_){
_start:
{
lean_object* v_r_1645_; lean_object* v___x_1646_; 
v_r_1645_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1640_, v_inst_1641_, v_acc_1644_, v_a_1642_, v_b_1643_);
v___x_1646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1646_, 0, v_r_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__1(lean_object* v___x_1647_, lean_object* v___f_1648_, lean_object* v_a_1649_, lean_object* v_x_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v___x_1652_; 
v___x_1652_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1647_, v___f_1648_, v_a_1649_, v___y_1651_);
return v___x_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg(lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_m_u2081_1657_, lean_object* v_m_u2082_1658_){
_start:
{
lean_object* v_size_1659_; lean_object* v_buckets_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_size_1659_ = lean_ctor_get(v_m_u2081_1657_, 0);
v_buckets_1660_ = lean_ctor_get(v_m_u2081_1657_, 1);
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = lean_array_get_size(v_buckets_1660_);
v___x_1663_ = lean_nat_dec_lt(v___x_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_dec_ref(v_m_u2081_1657_);
lean_dec_ref(v_inst_1656_);
lean_dec_ref(v_inst_1655_);
return v_m_u2082_1658_;
}
else
{
lean_object* v_size_1664_; lean_object* v_buckets_1665_; lean_object* v___x_1666_; uint8_t v___x_1667_; 
v_size_1664_ = lean_ctor_get(v_m_u2082_1658_, 0);
v_buckets_1665_ = lean_ctor_get(v_m_u2082_1658_, 1);
v___x_1666_ = lean_array_get_size(v_buckets_1665_);
v___x_1667_ = lean_nat_dec_lt(v___x_1661_, v___x_1666_);
if (v___x_1667_ == 0)
{
lean_dec_ref(v_m_u2082_1658_);
lean_dec_ref(v_inst_1656_);
lean_dec_ref(v_inst_1655_);
return v_m_u2081_1657_;
}
else
{
uint8_t v___x_1668_; 
v___x_1668_ = lean_nat_dec_le(v_size_1659_, v_size_1664_);
if (v___x_1668_ == 0)
{
lean_object* v___f_1669_; lean_object* v___x_1670_; 
v___f_1669_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1670_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1669_, v_inst_1655_, v_inst_1656_, v_m_u2081_1657_, v_m_u2082_1658_);
return v___x_1670_;
}
else
{
lean_object* v___f_1671_; lean_object* v___x_1672_; lean_object* v___f_1673_; size_t v_sz_1674_; size_t v___x_1675_; lean_object* v___x_1676_; 
lean_inc_ref(v_buckets_1660_);
lean_dec_ref(v_m_u2081_1657_);
v___f_1671_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1671_, 0, v_inst_1655_);
lean_closure_set(v___f_1671_, 1, v_inst_1656_);
v___x_1672_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___f_1673_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1673_, 0, v___x_1672_);
lean_closure_set(v___f_1673_, 1, v___f_1671_);
v_sz_1674_ = lean_array_size(v_buckets_1660_);
v___x_1675_ = ((size_t)0ULL);
v___x_1676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1672_, v_buckets_1660_, v___f_1673_, v_sz_1674_, v___x_1675_, v_m_u2082_1658_);
return v___x_1676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union(lean_object* v_00_u03b1_1677_, lean_object* v_00_u03b2_1678_, lean_object* v_inst_1679_, lean_object* v_inst_1680_, lean_object* v_m_u2081_1681_, lean_object* v_m_u2082_1682_){
_start:
{
lean_object* v_size_1683_; lean_object* v_buckets_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; 
v_size_1683_ = lean_ctor_get(v_m_u2081_1681_, 0);
v_buckets_1684_ = lean_ctor_get(v_m_u2081_1681_, 1);
v___x_1685_ = lean_unsigned_to_nat(0u);
v___x_1686_ = lean_array_get_size(v_buckets_1684_);
v___x_1687_ = lean_nat_dec_lt(v___x_1685_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_dec_ref(v_m_u2081_1681_);
lean_dec_ref(v_inst_1680_);
lean_dec_ref(v_inst_1679_);
return v_m_u2082_1682_;
}
else
{
lean_object* v_size_1688_; lean_object* v_buckets_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v_size_1688_ = lean_ctor_get(v_m_u2082_1682_, 0);
v_buckets_1689_ = lean_ctor_get(v_m_u2082_1682_, 1);
v___x_1690_ = lean_array_get_size(v_buckets_1689_);
v___x_1691_ = lean_nat_dec_lt(v___x_1685_, v___x_1690_);
if (v___x_1691_ == 0)
{
lean_dec_ref(v_m_u2082_1682_);
lean_dec_ref(v_inst_1680_);
lean_dec_ref(v_inst_1679_);
return v_m_u2081_1681_;
}
else
{
uint8_t v___x_1692_; 
v___x_1692_ = lean_nat_dec_le(v_size_1683_, v_size_1688_);
if (v___x_1692_ == 0)
{
lean_object* v___f_1693_; lean_object* v___x_1694_; 
v___f_1693_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1694_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1693_, v_inst_1679_, v_inst_1680_, v_m_u2081_1681_, v_m_u2082_1682_);
return v___x_1694_;
}
else
{
lean_object* v___f_1695_; lean_object* v___x_1696_; lean_object* v___f_1697_; size_t v_sz_1698_; size_t v___x_1699_; lean_object* v___x_1700_; 
lean_inc_ref(v_buckets_1684_);
lean_dec_ref(v_m_u2081_1681_);
v___f_1695_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1695_, 0, v_inst_1679_);
lean_closure_set(v___f_1695_, 1, v_inst_1680_);
v___x_1696_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___f_1697_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1697_, 0, v___x_1696_);
lean_closure_set(v___f_1697_, 1, v___f_1695_);
v_sz_1698_ = lean_array_size(v_buckets_1684_);
v___x_1699_ = ((size_t)0ULL);
v___x_1700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1696_, v_buckets_1684_, v___f_1697_, v_sz_1698_, v___x_1699_, v_m_u2082_1682_);
return v___x_1700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter___redArg(lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_m_u2081_1703_, lean_object* v_m_u2082_1704_){
_start:
{
lean_object* v_buckets_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v_buckets_1705_ = lean_ctor_get(v_m_u2081_1703_, 1);
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = lean_array_get_size(v_buckets_1705_);
v___x_1708_ = lean_nat_dec_lt(v___x_1706_, v___x_1707_);
if (v___x_1708_ == 0)
{
lean_dec_ref(v_m_u2081_1703_);
lean_dec_ref(v_inst_1702_);
lean_dec_ref(v_inst_1701_);
return v_m_u2082_1704_;
}
else
{
lean_object* v_buckets_1709_; lean_object* v___x_1710_; uint8_t v___x_1711_; 
v_buckets_1709_ = lean_ctor_get(v_m_u2082_1704_, 1);
v___x_1710_ = lean_array_get_size(v_buckets_1709_);
v___x_1711_ = lean_nat_dec_lt(v___x_1706_, v___x_1710_);
if (v___x_1711_ == 0)
{
lean_dec_ref(v_m_u2082_1704_);
lean_dec_ref(v_inst_1702_);
lean_dec_ref(v_inst_1701_);
return v_m_u2081_1703_;
}
else
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1701_, v_inst_1702_, v_m_u2081_1703_, v_m_u2082_1704_);
return v___x_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_inst_1715_, lean_object* v_inst_1716_, lean_object* v_m_u2081_1717_, lean_object* v_m_u2082_1718_){
_start:
{
lean_object* v_buckets_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; uint8_t v___x_1722_; 
v_buckets_1719_ = lean_ctor_get(v_m_u2081_1717_, 1);
v___x_1720_ = lean_unsigned_to_nat(0u);
v___x_1721_ = lean_array_get_size(v_buckets_1719_);
v___x_1722_ = lean_nat_dec_lt(v___x_1720_, v___x_1721_);
if (v___x_1722_ == 0)
{
lean_dec_ref(v_m_u2081_1717_);
lean_dec_ref(v_inst_1716_);
lean_dec_ref(v_inst_1715_);
return v_m_u2082_1718_;
}
else
{
lean_object* v_buckets_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v_buckets_1723_ = lean_ctor_get(v_m_u2082_1718_, 1);
v___x_1724_ = lean_array_get_size(v_buckets_1723_);
v___x_1725_ = lean_nat_dec_lt(v___x_1720_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_dec_ref(v_m_u2082_1718_);
lean_dec_ref(v_inst_1716_);
lean_dec_ref(v_inst_1715_);
return v_m_u2081_1717_;
}
else
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1715_, v_inst_1716_, v_m_u2081_1717_, v_m_u2082_1718_);
return v___x_1726_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_m_u2082_1729_, uint8_t v___x_1730_, lean_object* v_k_1731_, lean_object* v_x_1732_){
_start:
{
uint8_t v___x_1733_; 
v___x_1733_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1727_, v_inst_1728_, v_m_u2082_1729_, v_k_1731_);
if (v___x_1733_ == 0)
{
return v___x_1730_;
}
else
{
uint8_t v___x_1734_; 
v___x_1734_ = 0;
return v___x_1734_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1735_, lean_object* v_inst_1736_, lean_object* v_m_u2082_1737_, lean_object* v___x_1738_, lean_object* v_k_1739_, lean_object* v_x_1740_){
_start:
{
uint8_t v___x_91__boxed_1741_; uint8_t v_res_1742_; lean_object* v_r_1743_; 
v___x_91__boxed_1741_ = lean_unbox(v___x_1738_);
v_res_1742_ = l_Std_HashMap_Raw_diff___redArg___lam__0(v_inst_1735_, v_inst_1736_, v_m_u2082_1737_, v___x_91__boxed_1741_, v_k_1739_, v_x_1740_);
lean_dec(v_x_1740_);
lean_dec_ref(v_m_u2082_1737_);
v_r_1743_ = lean_box(v_res_1742_);
return v_r_1743_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg(lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_m_u2081_1746_, lean_object* v_m_u2082_1747_){
_start:
{
lean_object* v_size_1748_; lean_object* v_buckets_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v_size_1748_ = lean_ctor_get(v_m_u2081_1746_, 0);
v_buckets_1749_ = lean_ctor_get(v_m_u2081_1746_, 1);
v___x_1750_ = lean_unsigned_to_nat(0u);
v___x_1751_ = lean_array_get_size(v_buckets_1749_);
v___x_1752_ = lean_nat_dec_lt(v___x_1750_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec_ref(v_m_u2081_1746_);
lean_dec_ref(v_inst_1745_);
lean_dec_ref(v_inst_1744_);
return v_m_u2082_1747_;
}
else
{
lean_object* v_size_1753_; lean_object* v_buckets_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_size_1753_ = lean_ctor_get(v_m_u2082_1747_, 0);
v_buckets_1754_ = lean_ctor_get(v_m_u2082_1747_, 1);
v___x_1755_ = lean_array_get_size(v_buckets_1754_);
v___x_1756_ = lean_nat_dec_lt(v___x_1750_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_dec_ref(v_m_u2082_1747_);
lean_dec_ref(v_inst_1745_);
lean_dec_ref(v_inst_1744_);
return v_m_u2081_1746_;
}
else
{
uint8_t v___x_1757_; 
v___x_1757_ = lean_nat_dec_le(v_size_1748_, v_size_1753_);
if (v___x_1757_ == 0)
{
lean_object* v___f_1758_; lean_object* v___x_1759_; 
v___f_1758_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1758_, v_inst_1744_, v_inst_1745_, v_m_u2081_1746_, v_m_u2082_1747_);
return v___x_1759_;
}
else
{
lean_object* v___x_1760_; lean_object* v___f_1761_; lean_object* v___x_1762_; 
v___x_1760_ = lean_box(v___x_1757_);
v___f_1761_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1761_, 0, v_inst_1744_);
lean_closure_set(v___f_1761_, 1, v_inst_1745_);
lean_closure_set(v___f_1761_, 2, v_m_u2082_1747_);
lean_closure_set(v___f_1761_, 3, v___x_1760_);
v___x_1762_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1761_, v_m_u2081_1746_);
return v___x_1762_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff(lean_object* v_00_u03b1_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_m_u2081_1767_, lean_object* v_m_u2082_1768_){
_start:
{
lean_object* v_size_1769_; lean_object* v_buckets_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_size_1769_ = lean_ctor_get(v_m_u2081_1767_, 0);
v_buckets_1770_ = lean_ctor_get(v_m_u2081_1767_, 1);
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_array_get_size(v_buckets_1770_);
v___x_1773_ = lean_nat_dec_lt(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_dec_ref(v_m_u2081_1767_);
lean_dec_ref(v_inst_1766_);
lean_dec_ref(v_inst_1765_);
return v_m_u2082_1768_;
}
else
{
lean_object* v_size_1774_; lean_object* v_buckets_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v_size_1774_ = lean_ctor_get(v_m_u2082_1768_, 0);
v_buckets_1775_ = lean_ctor_get(v_m_u2082_1768_, 1);
v___x_1776_ = lean_array_get_size(v_buckets_1775_);
v___x_1777_ = lean_nat_dec_lt(v___x_1771_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec_ref(v_m_u2082_1768_);
lean_dec_ref(v_inst_1766_);
lean_dec_ref(v_inst_1765_);
return v_m_u2081_1767_;
}
else
{
uint8_t v___x_1778_; 
v___x_1778_ = lean_nat_dec_le(v_size_1769_, v_size_1774_);
if (v___x_1778_ == 0)
{
lean_object* v___f_1779_; lean_object* v___x_1780_; 
v___f_1779_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1780_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1779_, v_inst_1765_, v_inst_1766_, v_m_u2081_1767_, v_m_u2082_1768_);
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; lean_object* v___f_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_box(v___x_1778_);
v___f_1782_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1782_, 0, v_inst_1765_);
lean_closure_set(v___f_1782_, 1, v_inst_1766_);
lean_closure_set(v___f_1782_, 2, v_m_u2082_1768_);
lean_closure_set(v___f_1782_, 3, v___x_1781_);
v___x_1783_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1782_, v_m_u2081_1767_);
return v___x_1783_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1784_, lean_object* v_inst_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1786_, 0, lean_box(0));
lean_closure_set(v___x_1786_, 1, lean_box(0));
lean_closure_set(v___x_1786_, 2, v_inst_1784_);
lean_closure_set(v___x_1786_, 3, v_inst_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1791_, 0, lean_box(0));
lean_closure_set(v___x_1791_, 1, lean_box(0));
lean_closure_set(v___x_1791_, 2, v_inst_1789_);
lean_closure_set(v___x_1791_, 3, v_inst_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1792_, lean_object* v_inst_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1794_, 0, lean_box(0));
lean_closure_set(v___x_1794_, 1, lean_box(0));
lean_closure_set(v___x_1794_, 2, v_inst_1792_);
lean_closure_set(v___x_1794_, 3, v_inst_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1795_, lean_object* v_00_u03b2_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1799_, 0, lean_box(0));
lean_closure_set(v___x_1799_, 1, lean_box(0));
lean_closure_set(v___x_1799_, 2, v_inst_1797_);
lean_closure_set(v___x_1799_, 3, v_inst_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1800_, lean_object* v_inst_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1802_, 0, lean_box(0));
lean_closure_set(v___x_1802_, 1, lean_box(0));
lean_closure_set(v___x_1802_, 2, v_inst_1800_);
lean_closure_set(v___x_1802_, 3, v_inst_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1807_, 0, lean_box(0));
lean_closure_set(v___x_1807_, 1, lean_box(0));
lean_closure_set(v___x_1807_, 2, v_inst_1805_);
lean_closure_set(v___x_1807_, 3, v_inst_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq___redArg(lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_m_u2081_1811_, lean_object* v_m_u2082_1812_){
_start:
{
uint8_t v___x_1813_; 
v___x_1813_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1808_, v_inst_1809_, v_inst_1810_, v_m_u2081_1811_, v_m_u2082_1812_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___redArg___boxed(lean_object* v_inst_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_m_u2081_1817_, lean_object* v_m_u2082_1818_){
_start:
{
uint8_t v_res_1819_; lean_object* v_r_1820_; 
v_res_1819_ = l_Std_HashMap_Raw_beq___redArg(v_inst_1814_, v_inst_1815_, v_inst_1816_, v_m_u2081_1817_, v_m_u2082_1818_);
v_r_1820_ = lean_box(v_res_1819_);
return v_r_1820_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq(lean_object* v_00_u03b1_1821_, lean_object* v_00_u03b2_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_m_u2081_1826_, lean_object* v_m_u2082_1827_){
_start:
{
uint8_t v___x_1828_; 
v___x_1828_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1823_, v_inst_1824_, v_inst_1825_, v_m_u2081_1826_, v_m_u2082_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___boxed(lean_object* v_00_u03b1_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_, lean_object* v_m_u2081_1834_, lean_object* v_m_u2082_1835_){
_start:
{
uint8_t v_res_1836_; lean_object* v_r_1837_; 
v_res_1836_ = l_Std_HashMap_Raw_beq(v_00_u03b1_1829_, v_00_u03b2_1830_, v_inst_1831_, v_inst_1832_, v_inst_1833_, v_m_u2081_1834_, v_m_u2082_1835_);
v_r_1837_ = lean_box(v_res_1836_);
return v_r_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_){
_start:
{
lean_object* v___x_1841_; 
v___x_1841_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1841_, 0, lean_box(0));
lean_closure_set(v___x_1841_, 1, lean_box(0));
lean_closure_set(v___x_1841_, 2, v_inst_1838_);
lean_closure_set(v___x_1841_, 3, v_inst_1839_);
lean_closure_set(v___x_1841_, 4, v_inst_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1842_, lean_object* v_00_u03b2_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_){
_start:
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1847_, 0, lean_box(0));
lean_closure_set(v___x_1847_, 1, lean_box(0));
lean_closure_set(v___x_1847_, 2, v_inst_1844_);
lean_closure_set(v___x_1847_, 3, v_inst_1845_);
lean_closure_set(v___x_1847_, 4, v_inst_1846_);
return v___x_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg(lean_object* v_f_1848_, lean_object* v_m_1849_){
_start:
{
lean_object* v_buckets_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v_buckets_1850_ = lean_ctor_get(v_m_1849_, 1);
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_array_get_size(v_buckets_1850_);
v___x_1853_ = lean_nat_dec_lt(v___x_1851_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; 
lean_dec_ref(v_m_1849_);
lean_dec_ref(v_f_1848_);
v___x_1854_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1854_;
}
else
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1848_, v_m_1849_);
return v___x_1855_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object* v_00_u03b1_1856_, lean_object* v_00_u03b2_1857_, lean_object* v_00_u03b3_1858_, lean_object* v_f_1859_, lean_object* v_m_1860_){
_start:
{
lean_object* v_buckets_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1864_; 
v_buckets_1861_ = lean_ctor_get(v_m_1860_, 1);
v___x_1862_ = lean_unsigned_to_nat(0u);
v___x_1863_ = lean_array_get_size(v_buckets_1861_);
v___x_1864_ = lean_nat_dec_lt(v___x_1862_, v___x_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1865_; 
lean_dec_ref(v_m_1860_);
lean_dec_ref(v_f_1859_);
v___x_1865_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1859_, v_m_1860_);
return v___x_1866_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object* v_f_1867_, lean_object* v_m_1868_){
_start:
{
lean_object* v_buckets_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v_buckets_1869_ = lean_ctor_get(v_m_1868_, 1);
v___x_1870_ = lean_unsigned_to_nat(0u);
v___x_1871_ = lean_array_get_size(v_buckets_1869_);
v___x_1872_ = lean_nat_dec_lt(v___x_1870_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_object* v___x_1873_; 
lean_dec_ref(v_m_1868_);
lean_dec(v_f_1867_);
v___x_1873_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1873_;
}
else
{
lean_object* v___x_1874_; 
v___x_1874_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1867_, v_m_1868_);
return v___x_1874_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object* v_00_u03b1_1875_, lean_object* v_00_u03b2_1876_, lean_object* v_00_u03b3_1877_, lean_object* v_f_1878_, lean_object* v_m_1879_){
_start:
{
lean_object* v_buckets_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v_buckets_1880_ = lean_ctor_get(v_m_1879_, 1);
v___x_1881_ = lean_unsigned_to_nat(0u);
v___x_1882_ = lean_array_get_size(v_buckets_1880_);
v___x_1883_ = lean_nat_dec_lt(v___x_1881_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
lean_dec_ref(v_m_1879_);
lean_dec(v_f_1878_);
v___x_1884_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1878_, v_m_1879_);
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object* v_f_1886_, lean_object* v_m_1887_){
_start:
{
lean_object* v_buckets_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; uint8_t v___x_1891_; 
v_buckets_1888_ = lean_ctor_get(v_m_1887_, 1);
v___x_1889_ = lean_unsigned_to_nat(0u);
v___x_1890_ = lean_array_get_size(v_buckets_1888_);
v___x_1891_ = lean_nat_dec_lt(v___x_1889_, v___x_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___x_1892_; 
lean_dec_ref(v_m_1887_);
lean_dec_ref(v_f_1886_);
v___x_1892_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1892_;
}
else
{
lean_object* v___x_1893_; 
v___x_1893_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1886_, v_m_1887_);
return v___x_1893_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object* v_00_u03b1_1894_, lean_object* v_00_u03b2_1895_, lean_object* v_f_1896_, lean_object* v_m_1897_){
_start:
{
lean_object* v_buckets_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; uint8_t v___x_1901_; 
v_buckets_1898_ = lean_ctor_get(v_m_1897_, 1);
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = lean_array_get_size(v_buckets_1898_);
v___x_1901_ = lean_nat_dec_lt(v___x_1899_, v___x_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___x_1902_; 
lean_dec_ref(v_m_1897_);
lean_dec_ref(v_f_1896_);
v___x_1902_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1902_;
}
else
{
lean_object* v___x_1903_; 
v___x_1903_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1896_, v_m_1897_);
return v___x_1903_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1904_, lean_object* v_x2_1905_, lean_object* v_x3_1906_){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v_x2_1905_);
lean_ctor_set(v___x_1907_, 1, v_x3_1906_);
v___x_1908_ = lean_array_push(v_x1_1904_, v___x_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1909_, lean_object* v___f_1910_, lean_object* v_acc_1911_, lean_object* v_l_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1909_, v___f_1910_, v_acc_1911_, v_l_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object* v_m_1918_){
_start:
{
lean_object* v_size_1919_; lean_object* v_buckets_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_size_1919_ = lean_ctor_get(v_m_1918_, 0);
lean_inc(v_size_1919_);
v_buckets_1920_ = lean_ctor_get(v_m_1918_, 1);
lean_inc_ref(v_buckets_1920_);
lean_dec_ref(v_m_1918_);
v___x_1921_ = lean_mk_empty_array_with_capacity(v_size_1919_);
lean_dec(v_size_1919_);
v___x_1922_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1923_ = lean_unsigned_to_nat(0u);
v___x_1924_ = lean_array_get_size(v_buckets_1920_);
v___x_1925_ = lean_nat_dec_lt(v___x_1923_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_dec_ref(v_buckets_1920_);
return v___x_1921_;
}
else
{
lean_object* v___f_1926_; uint8_t v___x_1927_; 
v___f_1926_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1927_ = lean_nat_dec_le(v___x_1924_, v___x_1924_);
if (v___x_1927_ == 0)
{
if (v___x_1925_ == 0)
{
lean_dec_ref(v_buckets_1920_);
return v___x_1921_;
}
else
{
size_t v___x_1928_; size_t v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((size_t)0ULL);
v___x_1929_ = lean_usize_of_nat(v___x_1924_);
v___x_1930_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1922_, v___f_1926_, v_buckets_1920_, v___x_1928_, v___x_1929_, v___x_1921_);
return v___x_1930_;
}
}
else
{
size_t v___x_1931_; size_t v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = ((size_t)0ULL);
v___x_1932_ = lean_usize_of_nat(v___x_1924_);
v___x_1933_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1922_, v___f_1926_, v_buckets_1920_, v___x_1931_, v___x_1932_, v___x_1921_);
return v___x_1933_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object* v_00_u03b1_1934_, lean_object* v_00_u03b2_1935_, lean_object* v_m_1936_){
_start:
{
lean_object* v_size_1937_; lean_object* v_buckets_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v_size_1937_ = lean_ctor_get(v_m_1936_, 0);
lean_inc(v_size_1937_);
v_buckets_1938_ = lean_ctor_get(v_m_1936_, 1);
lean_inc_ref(v_buckets_1938_);
lean_dec_ref(v_m_1936_);
v___x_1939_ = lean_mk_empty_array_with_capacity(v_size_1937_);
lean_dec(v_size_1937_);
v___x_1940_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_array_get_size(v_buckets_1938_);
v___x_1943_ = lean_nat_dec_lt(v___x_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_dec_ref(v_buckets_1938_);
return v___x_1939_;
}
else
{
lean_object* v___f_1944_; uint8_t v___x_1945_; 
v___f_1944_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1945_ = lean_nat_dec_le(v___x_1942_, v___x_1942_);
if (v___x_1945_ == 0)
{
if (v___x_1943_ == 0)
{
lean_dec_ref(v_buckets_1938_);
return v___x_1939_;
}
else
{
size_t v___x_1946_; size_t v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = ((size_t)0ULL);
v___x_1947_ = lean_usize_of_nat(v___x_1942_);
v___x_1948_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1940_, v___f_1944_, v_buckets_1938_, v___x_1946_, v___x_1947_, v___x_1939_);
return v___x_1948_;
}
}
else
{
size_t v___x_1949_; size_t v___x_1950_; lean_object* v___x_1951_; 
v___x_1949_ = ((size_t)0ULL);
v___x_1950_ = lean_usize_of_nat(v___x_1942_);
v___x_1951_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1940_, v___f_1944_, v_buckets_1938_, v___x_1949_, v___x_1950_, v___x_1939_);
return v___x_1951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1952_, lean_object* v_x2_1953_, lean_object* v_x3_1954_){
_start:
{
lean_object* v___x_1955_; 
v___x_1955_ = lean_array_push(v_x1_1952_, v_x2_1953_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1956_, lean_object* v_x2_1957_, lean_object* v_x3_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Std_HashMap_Raw_keysArray___redArg___lam__0(v_x1_1956_, v_x2_1957_, v_x3_1958_);
lean_dec(v_x3_1958_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1960_, lean_object* v___f_1961_, lean_object* v_acc_1962_, lean_object* v_l_1963_){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1960_, v___f_1961_, v_acc_1962_, v_l_1963_);
return v___x_1964_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object* v_m_1969_){
_start:
{
lean_object* v_size_1970_; lean_object* v_buckets_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; uint8_t v___x_1976_; 
v_size_1970_ = lean_ctor_get(v_m_1969_, 0);
lean_inc(v_size_1970_);
v_buckets_1971_ = lean_ctor_get(v_m_1969_, 1);
lean_inc_ref(v_buckets_1971_);
lean_dec_ref(v_m_1969_);
v___x_1972_ = lean_mk_empty_array_with_capacity(v_size_1970_);
lean_dec(v_size_1970_);
v___x_1973_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1974_ = lean_unsigned_to_nat(0u);
v___x_1975_ = lean_array_get_size(v_buckets_1971_);
v___x_1976_ = lean_nat_dec_lt(v___x_1974_, v___x_1975_);
if (v___x_1976_ == 0)
{
lean_dec_ref(v_buckets_1971_);
return v___x_1972_;
}
else
{
lean_object* v___f_1977_; uint8_t v___x_1978_; 
v___f_1977_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1978_ = lean_nat_dec_le(v___x_1975_, v___x_1975_);
if (v___x_1978_ == 0)
{
if (v___x_1976_ == 0)
{
lean_dec_ref(v_buckets_1971_);
return v___x_1972_;
}
else
{
size_t v___x_1979_; size_t v___x_1980_; lean_object* v___x_1981_; 
v___x_1979_ = ((size_t)0ULL);
v___x_1980_ = lean_usize_of_nat(v___x_1975_);
v___x_1981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1973_, v___f_1977_, v_buckets_1971_, v___x_1979_, v___x_1980_, v___x_1972_);
return v___x_1981_;
}
}
else
{
size_t v___x_1982_; size_t v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = ((size_t)0ULL);
v___x_1983_ = lean_usize_of_nat(v___x_1975_);
v___x_1984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1973_, v___f_1977_, v_buckets_1971_, v___x_1982_, v___x_1983_, v___x_1972_);
return v___x_1984_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object* v_00_u03b1_1985_, lean_object* v_00_u03b2_1986_, lean_object* v_m_1987_){
_start:
{
lean_object* v_size_1988_; lean_object* v_buckets_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v_size_1988_ = lean_ctor_get(v_m_1987_, 0);
lean_inc(v_size_1988_);
v_buckets_1989_ = lean_ctor_get(v_m_1987_, 1);
lean_inc_ref(v_buckets_1989_);
lean_dec_ref(v_m_1987_);
v___x_1990_ = lean_mk_empty_array_with_capacity(v_size_1988_);
lean_dec(v_size_1988_);
v___x_1991_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1992_ = lean_unsigned_to_nat(0u);
v___x_1993_ = lean_array_get_size(v_buckets_1989_);
v___x_1994_ = lean_nat_dec_lt(v___x_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
lean_dec_ref(v_buckets_1989_);
return v___x_1990_;
}
else
{
lean_object* v___f_1995_; uint8_t v___x_1996_; 
v___f_1995_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1996_ = lean_nat_dec_le(v___x_1993_, v___x_1993_);
if (v___x_1996_ == 0)
{
if (v___x_1994_ == 0)
{
lean_dec_ref(v_buckets_1989_);
return v___x_1990_;
}
else
{
size_t v___x_1997_; size_t v___x_1998_; lean_object* v___x_1999_; 
v___x_1997_ = ((size_t)0ULL);
v___x_1998_ = lean_usize_of_nat(v___x_1993_);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1991_, v___f_1995_, v_buckets_1989_, v___x_1997_, v___x_1998_, v___x_1990_);
return v___x_1999_;
}
}
else
{
size_t v___x_2000_; size_t v___x_2001_; lean_object* v___x_2002_; 
v___x_2000_ = ((size_t)0ULL);
v___x_2001_ = lean_usize_of_nat(v___x_1993_);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1991_, v___f_1995_, v_buckets_1989_, v___x_2000_, v___x_2001_, v___x_1990_);
return v___x_2002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object* v_a_2003_, lean_object* v_b_2004_, lean_object* v_d_2005_){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2006_, 0, v_b_2004_);
lean_ctor_set(v___x_2006_, 1, v_d_2005_);
return v___x_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_2007_, lean_object* v_b_2008_, lean_object* v_d_2009_){
_start:
{
lean_object* v_res_2010_; 
v_res_2010_ = l_Std_HashMap_Raw_values___redArg___lam__0(v_a_2007_, v_b_2008_, v_d_2009_);
lean_dec(v_a_2007_);
return v_res_2010_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object* v_m_2015_){
_start:
{
lean_object* v___x_2016_; lean_object* v_buckets_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; uint8_t v___x_2021_; 
v___x_2016_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2017_ = lean_ctor_get(v_m_2015_, 1);
lean_inc_ref(v_buckets_2017_);
lean_dec_ref(v_m_2015_);
v___x_2018_ = lean_box(0);
v___x_2019_ = lean_array_get_size(v_buckets_2017_);
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = lean_nat_dec_lt(v___x_2020_, v___x_2019_);
if (v___x_2021_ == 0)
{
lean_dec_ref(v_buckets_2017_);
return v___x_2018_;
}
else
{
lean_object* v___f_2022_; size_t v___x_2023_; size_t v___x_2024_; lean_object* v___x_2025_; 
v___f_2022_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_2023_ = lean_usize_of_nat(v___x_2019_);
v___x_2024_ = ((size_t)0ULL);
v___x_2025_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2016_, v___f_2022_, v_buckets_2017_, v___x_2023_, v___x_2024_, v___x_2018_);
return v___x_2025_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object* v_00_u03b1_2026_, lean_object* v_00_u03b2_2027_, lean_object* v_m_2028_){
_start:
{
lean_object* v___x_2029_; lean_object* v_buckets_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2029_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2030_ = lean_ctor_get(v_m_2028_, 1);
lean_inc_ref(v_buckets_2030_);
lean_dec_ref(v_m_2028_);
v___x_2031_ = lean_box(0);
v___x_2032_ = lean_array_get_size(v_buckets_2030_);
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = lean_nat_dec_lt(v___x_2033_, v___x_2032_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v_buckets_2030_);
return v___x_2031_;
}
else
{
lean_object* v___f_2035_; size_t v___x_2036_; size_t v___x_2037_; lean_object* v___x_2038_; 
v___f_2035_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_2036_ = lean_usize_of_nat(v___x_2032_);
v___x_2037_ = ((size_t)0ULL);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2029_, v___f_2035_, v_buckets_2030_, v___x_2036_, v___x_2037_, v___x_2031_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2039_, lean_object* v_x2_2040_, lean_object* v_x3_2041_){
_start:
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_array_push(v_x1_2039_, v_x3_2041_);
return v___x_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2043_, lean_object* v_x2_2044_, lean_object* v_x3_2045_){
_start:
{
lean_object* v_res_2046_; 
v_res_2046_ = l_Std_HashMap_Raw_valuesArray___redArg___lam__0(v_x1_2043_, v_x2_2044_, v_x3_2045_);
lean_dec(v_x2_2044_);
return v_res_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg(lean_object* v_m_2051_){
_start:
{
lean_object* v_size_2052_; lean_object* v_buckets_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; uint8_t v___x_2058_; 
v_size_2052_ = lean_ctor_get(v_m_2051_, 0);
lean_inc(v_size_2052_);
v_buckets_2053_ = lean_ctor_get(v_m_2051_, 1);
lean_inc_ref(v_buckets_2053_);
lean_dec_ref(v_m_2051_);
v___x_2054_ = lean_mk_empty_array_with_capacity(v_size_2052_);
lean_dec(v_size_2052_);
v___x_2055_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2057_ = lean_array_get_size(v_buckets_2053_);
v___x_2058_ = lean_nat_dec_lt(v___x_2056_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_dec_ref(v_buckets_2053_);
return v___x_2054_;
}
else
{
lean_object* v___f_2059_; uint8_t v___x_2060_; 
v___f_2059_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2060_ = lean_nat_dec_le(v___x_2057_, v___x_2057_);
if (v___x_2060_ == 0)
{
if (v___x_2058_ == 0)
{
lean_dec_ref(v_buckets_2053_);
return v___x_2054_;
}
else
{
size_t v___x_2061_; size_t v___x_2062_; lean_object* v___x_2063_; 
v___x_2061_ = ((size_t)0ULL);
v___x_2062_ = lean_usize_of_nat(v___x_2057_);
v___x_2063_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2055_, v___f_2059_, v_buckets_2053_, v___x_2061_, v___x_2062_, v___x_2054_);
return v___x_2063_;
}
}
else
{
size_t v___x_2064_; size_t v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = ((size_t)0ULL);
v___x_2065_ = lean_usize_of_nat(v___x_2057_);
v___x_2066_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2055_, v___f_2059_, v_buckets_2053_, v___x_2064_, v___x_2065_, v___x_2054_);
return v___x_2066_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray(lean_object* v_00_u03b1_2067_, lean_object* v_00_u03b2_2068_, lean_object* v_m_2069_){
_start:
{
lean_object* v_size_2070_; lean_object* v_buckets_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; uint8_t v___x_2076_; 
v_size_2070_ = lean_ctor_get(v_m_2069_, 0);
lean_inc(v_size_2070_);
v_buckets_2071_ = lean_ctor_get(v_m_2069_, 1);
lean_inc_ref(v_buckets_2071_);
lean_dec_ref(v_m_2069_);
v___x_2072_ = lean_mk_empty_array_with_capacity(v_size_2070_);
lean_dec(v_size_2070_);
v___x_2073_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = lean_array_get_size(v_buckets_2071_);
v___x_2076_ = lean_nat_dec_lt(v___x_2074_, v___x_2075_);
if (v___x_2076_ == 0)
{
lean_dec_ref(v_buckets_2071_);
return v___x_2072_;
}
else
{
lean_object* v___f_2077_; uint8_t v___x_2078_; 
v___f_2077_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2078_ = lean_nat_dec_le(v___x_2075_, v___x_2075_);
if (v___x_2078_ == 0)
{
if (v___x_2076_ == 0)
{
lean_dec_ref(v_buckets_2071_);
return v___x_2072_;
}
else
{
size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = ((size_t)0ULL);
v___x_2080_ = lean_usize_of_nat(v___x_2075_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2073_, v___f_2077_, v_buckets_2071_, v___x_2079_, v___x_2080_, v___x_2072_);
return v___x_2081_;
}
}
else
{
size_t v___x_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = lean_usize_of_nat(v___x_2075_);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2073_, v___f_2077_, v_buckets_2071_, v___x_2082_, v___x_2083_, v___x_2072_);
return v___x_2084_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany___redArg(lean_object* v_inst_2085_, lean_object* v_inst_2086_, lean_object* v_inst_2087_, lean_object* v_m_2088_, lean_object* v_l_2089_){
_start:
{
lean_object* v_buckets_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_buckets_2090_ = lean_ctor_get(v_m_2088_, 1);
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_array_get_size(v_buckets_2090_);
v___x_2093_ = lean_nat_dec_lt(v___x_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_dec(v_l_2089_);
lean_dec(v_inst_2087_);
lean_dec_ref(v_inst_2086_);
lean_dec_ref(v_inst_2085_);
return v_m_2088_;
}
else
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2087_, v_inst_2085_, v_inst_2086_, v_m_2088_, v_l_2089_);
return v___x_2094_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany(lean_object* v_00_u03b1_2095_, lean_object* v_00_u03b2_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_00_u03c1_2099_, lean_object* v_inst_2100_, lean_object* v_m_2101_, lean_object* v_l_2102_){
_start:
{
lean_object* v_buckets_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; uint8_t v___x_2106_; 
v_buckets_2103_ = lean_ctor_get(v_m_2101_, 1);
v___x_2104_ = lean_unsigned_to_nat(0u);
v___x_2105_ = lean_array_get_size(v_buckets_2103_);
v___x_2106_ = lean_nat_dec_lt(v___x_2104_, v___x_2105_);
if (v___x_2106_ == 0)
{
lean_dec(v_l_2102_);
lean_dec(v_inst_2100_);
lean_dec_ref(v_inst_2098_);
lean_dec_ref(v_inst_2097_);
return v_m_2101_;
}
else
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2100_, v_inst_2097_, v_inst_2098_, v_m_2101_, v_l_2102_);
return v___x_2107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_inst_2110_, lean_object* v_m_2111_, lean_object* v_l_2112_){
_start:
{
lean_object* v_buckets_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; uint8_t v___x_2116_; 
v_buckets_2113_ = lean_ctor_get(v_m_2111_, 1);
v___x_2114_ = lean_unsigned_to_nat(0u);
v___x_2115_ = lean_array_get_size(v_buckets_2113_);
v___x_2116_ = lean_nat_dec_lt(v___x_2114_, v___x_2115_);
if (v___x_2116_ == 0)
{
lean_dec(v_l_2112_);
lean_dec(v_inst_2110_);
lean_dec_ref(v_inst_2109_);
lean_dec_ref(v_inst_2108_);
return v_m_2111_;
}
else
{
lean_object* v___x_2117_; 
v___x_2117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2110_, v_inst_2108_, v_inst_2109_, v_m_2111_, v_l_2112_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2118_, lean_object* v_inst_2119_, lean_object* v_inst_2120_, lean_object* v_00_u03c1_2121_, lean_object* v_inst_2122_, lean_object* v_m_2123_, lean_object* v_l_2124_){
_start:
{
lean_object* v_buckets_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v_buckets_2125_ = lean_ctor_get(v_m_2123_, 1);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = lean_array_get_size(v_buckets_2125_);
v___x_2128_ = lean_nat_dec_lt(v___x_2126_, v___x_2127_);
if (v___x_2128_ == 0)
{
lean_dec(v_l_2124_);
lean_dec(v_inst_2122_);
lean_dec_ref(v_inst_2120_);
lean_dec_ref(v_inst_2119_);
return v_m_2123_;
}
else
{
lean_object* v___x_2129_; 
v___x_2129_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2122_, v_inst_2119_, v_inst_2120_, v_m_2123_, v_l_2124_);
return v___x_2129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray___redArg(lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_l_2132_){
_start:
{
lean_object* v___x_2133_; uint8_t v___x_2134_; 
v___x_2133_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_2134_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2134_ == 0)
{
lean_dec_ref(v_l_2132_);
lean_dec_ref(v_inst_2131_);
lean_dec_ref(v_inst_2130_);
return v___x_2133_;
}
else
{
lean_object* v___f_2135_; lean_object* v___x_2136_; 
v___f_2135_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2136_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2135_, v_inst_2130_, v_inst_2131_, v___x_2133_, v_l_2132_);
return v___x_2136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray(lean_object* v_00_u03b1_2137_, lean_object* v_inst_2138_, lean_object* v_inst_2139_, lean_object* v_l_2140_){
_start:
{
lean_object* v___x_2141_; uint8_t v___x_2142_; 
v___x_2141_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_2142_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2142_ == 0)
{
lean_dec_ref(v_l_2140_);
lean_dec_ref(v_inst_2139_);
lean_dec_ref(v_inst_2138_);
return v___x_2141_;
}
else
{
lean_object* v___f_2143_; lean_object* v___x_2144_; 
v___f_2143_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2144_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2143_, v_inst_2138_, v_inst_2139_, v___x_2141_, v_l_2140_);
return v___x_2144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2145_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2145_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Std_HashMap_Raw_Internal_numBuckets___redArg(v_m_2147_);
lean_dec_ref(v_m_2147_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2149_, lean_object* v_00_u03b2_2150_, lean_object* v_m_2151_){
_start:
{
lean_object* v___x_2152_; 
v___x_2152_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2151_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2153_, lean_object* v_00_u03b2_2154_, lean_object* v_m_2155_){
_start:
{
lean_object* v_res_2156_; 
v_res_2156_ = l_Std_HashMap_Raw_Internal_numBuckets(v_00_u03b1_2153_, v_00_u03b2_2154_, v_m_2155_);
lean_dec_ref(v_m_2155_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2160_, lean_object* v___f_2161_, lean_object* v_m_2162_, lean_object* v_prec_2163_){
_start:
{
lean_object* v___x_2164_; lean_object* v_buckets_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2185_; 
v___x_2164_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2165_ = lean_ctor_get(v_m_2162_, 1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_m_2162_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; 
v_unused_2186_ = lean_ctor_get(v_m_2162_, 0);
lean_dec(v_unused_2186_);
v___x_2167_ = v_m_2162_;
v_isShared_2168_ = v_isSharedCheck_2185_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_buckets_2165_);
lean_dec(v_m_2162_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2185_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___y_2171_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; uint8_t v___x_2180_; 
v___x_2169_ = ((lean_object*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2177_ = lean_box(0);
v___x_2178_ = lean_array_get_size(v_buckets_2165_);
v___x_2179_ = lean_unsigned_to_nat(0u);
v___x_2180_ = lean_nat_dec_lt(v___x_2179_, v___x_2178_);
if (v___x_2180_ == 0)
{
lean_dec_ref(v_buckets_2165_);
lean_dec_ref(v___f_2161_);
v___y_2171_ = v___x_2177_;
goto v___jp_2170_;
}
else
{
lean_object* v___f_2181_; size_t v___x_2182_; size_t v___x_2183_; lean_object* v___x_2184_; 
v___f_2181_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2181_, 0, v___x_2164_);
lean_closure_set(v___f_2181_, 1, v___f_2161_);
v___x_2182_ = lean_usize_of_nat(v___x_2178_);
v___x_2183_ = ((size_t)0ULL);
v___x_2184_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2164_, v___f_2181_, v_buckets_2165_, v___x_2182_, v___x_2183_, v___x_2177_);
v___y_2171_ = v___x_2184_;
goto v___jp_2170_;
}
v___jp_2170_:
{
lean_object* v___x_2172_; lean_object* v___x_2174_; 
v___x_2172_ = l_List_repr___redArg(v___x_2160_, v___y_2171_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set_tag(v___x_2167_, 5);
lean_ctor_set(v___x_2167_, 1, v___x_2172_);
lean_ctor_set(v___x_2167_, 0, v___x_2169_);
v___x_2174_ = v___x_2167_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2176_, 1, v___x_2172_);
v___x_2174_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
lean_object* v___x_2175_; 
v___x_2175_ = l_Repr_addAppParen(v___x_2174_, v_prec_2163_);
return v___x_2175_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2187_, lean_object* v___f_2188_, lean_object* v_m_2189_, lean_object* v_prec_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2(v___x_2187_, v___f_2188_, v_m_2189_, v_prec_2190_);
lean_dec(v_prec_2190_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object* v_inst_2192_, lean_object* v_inst_2193_){
_start:
{
lean_object* v___f_2194_; lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v___f_2197_; 
v___f_2194_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__0));
v___f_2195_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2195_, 0, v_inst_2193_);
v___x_2196_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2196_, 0, lean_box(0));
lean_closure_set(v___x_2196_, 1, lean_box(0));
lean_closure_set(v___x_2196_, 2, v_inst_2192_);
lean_closure_set(v___x_2196_, 3, v___f_2195_);
v___f_2197_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2197_, 0, v___x_2196_);
lean_closure_set(v___f_2197_, 1, v___f_2194_);
return v___f_2197_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object* v_00_u03b1_2198_, lean_object* v_00_u03b2_2199_, lean_object* v_inst_2200_, lean_object* v_inst_2201_){
_start:
{
lean_object* v___x_2202_; 
v___x_2202_ = l_Std_HashMap_Raw_instRepr___redArg(v_inst_2200_, v_inst_2201_);
return v___x_2202_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Raw(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Raw(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashMap_Raw(builtin);
}
#ifdef __cplusplus
}
#endif
