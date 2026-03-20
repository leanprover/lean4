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
uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_105_);
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
lean_inc(v_quotContext_111_);
v_currMacroScope_112_ = lean_ctor_get(v_a_105_, 2);
lean_inc(v_currMacroScope_112_);
v_ref_113_ = lean_ctor_get(v_a_105_, 5);
lean_inc(v_ref_113_);
lean_dec_ref(v_a_105_);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = l_Lean_Syntax_getArg(v_x_104_, v___x_114_);
v___x_116_ = lean_unsigned_to_nat(2u);
v___x_117_ = l_Lean_Syntax_getArg(v_x_104_, v___x_116_);
lean_dec(v_x_104_);
v___x_118_ = 0;
v___x_119_ = l_Lean_SourceInfo_fromRef(v_ref_113_, v___x_118_);
lean_dec(v_ref_113_);
v___x_120_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
v___x_121_ = lean_obj_once(&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6, &l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6);
v___x_122_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7));
v___x_123_ = l_Lean_addMacroScope(v_quotContext_111_, v___x_122_, v_currMacroScope_112_);
v___x_124_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12));
lean_inc(v___x_119_);
v___x_125_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_125_, 0, v___x_119_);
lean_ctor_set(v___x_125_, 1, v___x_121_);
lean_ctor_set(v___x_125_, 2, v___x_123_);
lean_ctor_set(v___x_125_, 3, v___x_124_);
v___x_126_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14));
lean_inc(v___x_119_);
v___x_127_ = l_Lean_Syntax_node2(v___x_119_, v___x_126_, v___x_115_, v___x_117_);
v___x_128_ = l_Lean_Syntax_node2(v___x_119_, v___x_120_, v___x_125_, v___x_127_);
v___x_129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v_a_106_);
return v___x_129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(lean_object* v_x_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
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
v___x_142_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1));
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
v___x_157_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
v___x_158_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__7));
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___boxed(lean_object* v_x_162_, lean_object* v_a_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(v_x_162_, v_a_163_, v_a_164_);
lean_dec(v_a_163_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert___redArg(lean_object* v_beq_166_, lean_object* v_inst_167_, lean_object* v_m_168_, lean_object* v_a_169_, lean_object* v_b_170_){
_start:
{
lean_object* v_buckets_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v_buckets_171_ = lean_ctor_get(v_m_168_, 1);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_array_get_size(v_buckets_171_);
v___x_174_ = lean_nat_dec_lt(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_dec(v_b_170_);
lean_dec(v_a_169_);
lean_dec_ref(v_inst_167_);
lean_dec_ref(v_beq_166_);
return v_m_168_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_beq_166_, v_inst_167_, v_m_168_, v_a_169_, v_b_170_);
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert(lean_object* v_00_u03b1_176_, lean_object* v_00_u03b2_177_, lean_object* v_beq_178_, lean_object* v_inst_179_, lean_object* v_m_180_, lean_object* v_a_181_, lean_object* v_b_182_){
_start:
{
lean_object* v_buckets_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v_buckets_183_ = lean_ctor_get(v_m_180_, 1);
v___x_184_ = lean_unsigned_to_nat(0u);
v___x_185_ = lean_array_get_size(v_buckets_183_);
v___x_186_ = lean_nat_dec_lt(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_dec(v_b_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_inst_179_);
lean_dec_ref(v_beq_178_);
return v_m_180_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_beq_178_, v_inst_179_, v_m_180_, v_a_181_, v_b_182_);
return v___x_187_;
}
}
}
static lean_object* _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_188_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0);
v___x_189_ = lean_array_get_size(v___x_188_);
return v___x_189_;
}
}
static uint8_t _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_190_ = lean_obj_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = lean_nat_dec_lt(v___x_191_, v___x_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_x_195_){
_start:
{
lean_object* v_fst_196_; lean_object* v_snd_197_; lean_object* v___x_198_; uint8_t v___x_199_; 
v_fst_196_ = lean_ctor_get(v_x_195_, 0);
lean_inc(v_fst_196_);
v_snd_197_ = lean_ctor_get(v_x_195_, 1);
lean_inc(v_snd_197_);
lean_dec_ref(v_x_195_);
v___x_198_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_199_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_199_ == 0)
{
lean_dec(v_snd_197_);
lean_dec(v_fst_196_);
lean_dec_ref(v_inst_194_);
lean_dec_ref(v_inst_193_);
return v___x_198_;
}
else
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_193_, v_inst_194_, v___x_198_, v_fst_196_, v_snd_197_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg(lean_object* v_inst_201_, lean_object* v_inst_202_){
_start:
{
lean_object* v___f_203_; 
v___f_203_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_203_, 0, v_inst_201_);
lean_closure_set(v___f_203_, 1, v_inst_202_);
return v___f_203_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable(lean_object* v_00_u03b1_204_, lean_object* v_00_u03b2_205_, lean_object* v_inst_206_, lean_object* v_inst_207_){
_start:
{
lean_object* v___f_208_; 
v___f_208_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_208_, 0, v_inst_206_);
lean_closure_set(v___f_208_, 1, v_inst_207_);
return v___f_208_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_x_211_, lean_object* v_s_212_){
_start:
{
lean_object* v_fst_213_; lean_object* v_snd_214_; lean_object* v_buckets_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_fst_213_ = lean_ctor_get(v_x_211_, 0);
lean_inc(v_fst_213_);
v_snd_214_ = lean_ctor_get(v_x_211_, 1);
lean_inc(v_snd_214_);
lean_dec_ref(v_x_211_);
v_buckets_215_ = lean_ctor_get(v_s_212_, 1);
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_array_get_size(v_buckets_215_);
v___x_218_ = lean_nat_dec_lt(v___x_216_, v___x_217_);
if (v___x_218_ == 0)
{
lean_dec(v_snd_214_);
lean_dec(v_fst_213_);
lean_dec_ref(v_inst_210_);
lean_dec_ref(v_inst_209_);
return v_s_212_;
}
else
{
lean_object* v___x_219_; 
v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_209_, v_inst_210_, v_s_212_, v_fst_213_, v_snd_214_);
return v___x_219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg(lean_object* v_inst_220_, lean_object* v_inst_221_){
_start:
{
lean_object* v___f_222_; 
v___f_222_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_222_, 0, v_inst_220_);
lean_closure_set(v___f_222_, 1, v_inst_221_);
return v___f_222_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable(lean_object* v_00_u03b1_223_, lean_object* v_00_u03b2_224_, lean_object* v_inst_225_, lean_object* v_inst_226_){
_start:
{
lean_object* v___f_227_; 
v___f_227_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_227_, 0, v_inst_225_);
lean_closure_set(v___f_227_, 1, v_inst_226_);
return v___f_227_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew___redArg(lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_m_230_, lean_object* v_a_231_, lean_object* v_b_232_){
_start:
{
lean_object* v_buckets_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v_buckets_233_ = lean_ctor_get(v_m_230_, 1);
v___x_234_ = lean_unsigned_to_nat(0u);
v___x_235_ = lean_array_get_size(v_buckets_233_);
v___x_236_ = lean_nat_dec_lt(v___x_234_, v___x_235_);
if (v___x_236_ == 0)
{
lean_dec(v_b_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_inst_229_);
lean_dec_ref(v_inst_228_);
return v_m_230_;
}
else
{
lean_object* v___x_237_; 
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_228_, v_inst_229_, v_m_230_, v_a_231_, v_b_232_);
return v___x_237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew(lean_object* v_00_u03b1_238_, lean_object* v_00_u03b2_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_m_242_, lean_object* v_a_243_, lean_object* v_b_244_){
_start:
{
lean_object* v_buckets_245_; lean_object* v___x_246_; lean_object* v___x_247_; uint8_t v___x_248_; 
v_buckets_245_ = lean_ctor_get(v_m_242_, 1);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_array_get_size(v_buckets_245_);
v___x_248_ = lean_nat_dec_lt(v___x_246_, v___x_247_);
if (v___x_248_ == 0)
{
lean_dec(v_b_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_inst_241_);
lean_dec_ref(v_inst_240_);
return v_m_242_;
}
else
{
lean_object* v___x_249_; 
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_240_, v_inst_241_, v_m_242_, v_a_243_, v_b_244_);
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_250_, lean_object* v_inst_251_, lean_object* v_m_252_, lean_object* v_a_253_, lean_object* v_b_254_){
_start:
{
lean_object* v_size_255_; lean_object* v_buckets_256_; lean_object* v___x_257_; lean_object* v___x_258_; uint8_t v___x_259_; 
v_size_255_ = lean_ctor_get(v_m_252_, 0);
v_buckets_256_ = lean_ctor_get(v_m_252_, 1);
v___x_257_ = lean_unsigned_to_nat(0u);
v___x_258_ = lean_array_get_size(v_buckets_256_);
v___x_259_ = lean_nat_dec_lt(v___x_257_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; 
lean_dec(v_b_254_);
lean_dec(v_a_253_);
lean_dec_ref(v_inst_251_);
lean_dec_ref(v_inst_250_);
v___x_260_ = lean_box(v___x_259_);
v___x_261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_261_, 0, v___x_260_);
lean_ctor_set(v___x_261_, 1, v_m_252_);
return v___x_261_;
}
else
{
lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_311_; 
lean_inc_ref(v_buckets_256_);
lean_inc(v_size_255_);
v_isSharedCheck_311_ = !lean_is_exclusive(v_m_252_);
if (v_isSharedCheck_311_ == 0)
{
lean_object* v_unused_312_; lean_object* v_unused_313_; 
v_unused_312_ = lean_ctor_get(v_m_252_, 1);
lean_dec(v_unused_312_);
v_unused_313_ = lean_ctor_get(v_m_252_, 0);
lean_dec(v_unused_313_);
v___x_263_ = v_m_252_;
v_isShared_264_ = v_isSharedCheck_311_;
goto v_resetjp_262_;
}
else
{
lean_dec(v_m_252_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_311_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; uint64_t v___x_266_; uint64_t v___x_267_; uint64_t v___x_268_; uint64_t v___x_269_; uint64_t v_fold_270_; uint64_t v___x_271_; uint64_t v___x_272_; uint64_t v___x_273_; size_t v___x_274_; size_t v___x_275_; size_t v___x_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v_bkt_279_; uint8_t v___x_280_; 
lean_inc_ref(v_inst_251_);
lean_inc(v_a_253_);
v___x_265_ = lean_apply_1(v_inst_251_, v_a_253_);
v___x_266_ = 32ULL;
v___x_267_ = lean_unbox_uint64(v___x_265_);
v___x_268_ = lean_uint64_shift_right(v___x_267_, v___x_266_);
v___x_269_ = lean_unbox_uint64(v___x_265_);
lean_dec_ref(v___x_265_);
v_fold_270_ = lean_uint64_xor(v___x_269_, v___x_268_);
v___x_271_ = 16ULL;
v___x_272_ = lean_uint64_shift_right(v_fold_270_, v___x_271_);
v___x_273_ = lean_uint64_xor(v_fold_270_, v___x_272_);
v___x_274_ = lean_uint64_to_usize(v___x_273_);
v___x_275_ = lean_usize_of_nat(v___x_258_);
v___x_276_ = ((size_t)1ULL);
v___x_277_ = lean_usize_sub(v___x_275_, v___x_276_);
v___x_278_ = lean_usize_land(v___x_274_, v___x_277_);
v_bkt_279_ = lean_array_uget_borrowed(v_buckets_256_, v___x_278_);
lean_inc(v_bkt_279_);
lean_inc(v_a_253_);
lean_inc_ref(v_inst_250_);
v___x_280_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_250_, v_a_253_, v_bkt_279_);
if (v___x_280_ == 0)
{
lean_object* v___x_281_; lean_object* v_size_x27_282_; lean_object* v___x_283_; lean_object* v_buckets_x27_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___x_290_; 
lean_dec_ref(v_inst_250_);
v___x_281_ = lean_unsigned_to_nat(1u);
v_size_x27_282_ = lean_nat_add(v_size_255_, v___x_281_);
lean_dec(v_size_255_);
lean_inc(v_bkt_279_);
v___x_283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_283_, 0, v_a_253_);
lean_ctor_set(v___x_283_, 1, v_b_254_);
lean_ctor_set(v___x_283_, 2, v_bkt_279_);
v_buckets_x27_284_ = lean_array_uset(v_buckets_256_, v___x_278_, v___x_283_);
v___x_285_ = lean_unsigned_to_nat(4u);
v___x_286_ = lean_nat_mul(v_size_x27_282_, v___x_285_);
v___x_287_ = lean_unsigned_to_nat(3u);
v___x_288_ = lean_nat_div(v___x_286_, v___x_287_);
lean_dec(v___x_286_);
v___x_289_ = lean_array_get_size(v_buckets_x27_284_);
v___x_290_ = lean_nat_dec_le(v___x_288_, v___x_289_);
lean_dec(v___x_288_);
if (v___x_290_ == 0)
{
lean_object* v_val_291_; lean_object* v___x_293_; 
v_val_291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_251_, v_buckets_x27_284_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v_val_291_);
lean_ctor_set(v___x_263_, 0, v_size_x27_282_);
v___x_293_ = v___x_263_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_size_x27_282_);
lean_ctor_set(v_reuseFailAlloc_296_, 1, v_val_291_);
v___x_293_ = v_reuseFailAlloc_296_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
lean_object* v___x_294_; lean_object* v___x_295_; 
v___x_294_ = lean_box(v___x_280_);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
lean_ctor_set(v___x_295_, 1, v___x_293_);
return v___x_295_;
}
}
else
{
lean_object* v___x_298_; 
lean_dec_ref(v_inst_251_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v_buckets_x27_284_);
lean_ctor_set(v___x_263_, 0, v_size_x27_282_);
v___x_298_ = v___x_263_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_301_; 
v_reuseFailAlloc_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_301_, 0, v_size_x27_282_);
lean_ctor_set(v_reuseFailAlloc_301_, 1, v_buckets_x27_284_);
v___x_298_ = v_reuseFailAlloc_301_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_box(v___x_280_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v___x_298_);
return v___x_300_;
}
}
}
else
{
lean_object* v___x_302_; lean_object* v_buckets_x27_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_307_; 
lean_inc(v_bkt_279_);
lean_dec_ref(v_inst_251_);
v___x_302_ = lean_box(0);
v_buckets_x27_303_ = lean_array_uset(v_buckets_256_, v___x_278_, v___x_302_);
v___x_304_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_250_, v_a_253_, v_b_254_, v_bkt_279_);
v___x_305_ = lean_array_uset(v_buckets_x27_303_, v___x_278_, v___x_304_);
if (v_isShared_264_ == 0)
{
lean_ctor_set(v___x_263_, 1, v___x_305_);
v___x_307_ = v___x_263_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_310_; 
v_reuseFailAlloc_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_310_, 0, v_size_255_);
lean_ctor_set(v_reuseFailAlloc_310_, 1, v___x_305_);
v___x_307_ = v_reuseFailAlloc_310_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = lean_box(v___x_280_);
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v___x_307_);
return v___x_309_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_314_, lean_object* v_00_u03b2_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_m_318_, lean_object* v_a_319_, lean_object* v_b_320_){
_start:
{
lean_object* v_size_321_; lean_object* v_buckets_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_size_321_ = lean_ctor_get(v_m_318_, 0);
v_buckets_322_ = lean_ctor_get(v_m_318_, 1);
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_array_get_size(v_buckets_322_);
v___x_325_ = lean_nat_dec_lt(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v___x_327_; 
lean_dec(v_b_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_inst_317_);
lean_dec_ref(v_inst_316_);
v___x_326_ = lean_box(v___x_325_);
v___x_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v_m_318_);
return v___x_327_;
}
else
{
lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_377_; 
lean_inc_ref(v_buckets_322_);
lean_inc(v_size_321_);
v_isSharedCheck_377_ = !lean_is_exclusive(v_m_318_);
if (v_isSharedCheck_377_ == 0)
{
lean_object* v_unused_378_; lean_object* v_unused_379_; 
v_unused_378_ = lean_ctor_get(v_m_318_, 1);
lean_dec(v_unused_378_);
v_unused_379_ = lean_ctor_get(v_m_318_, 0);
lean_dec(v_unused_379_);
v___x_329_ = v_m_318_;
v_isShared_330_ = v_isSharedCheck_377_;
goto v_resetjp_328_;
}
else
{
lean_dec(v_m_318_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_377_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; uint64_t v___x_332_; uint64_t v___x_333_; uint64_t v___x_334_; uint64_t v___x_335_; uint64_t v_fold_336_; uint64_t v___x_337_; uint64_t v___x_338_; uint64_t v___x_339_; size_t v___x_340_; size_t v___x_341_; size_t v___x_342_; size_t v___x_343_; size_t v___x_344_; lean_object* v_bkt_345_; uint8_t v___x_346_; 
lean_inc_ref(v_inst_317_);
lean_inc(v_a_319_);
v___x_331_ = lean_apply_1(v_inst_317_, v_a_319_);
v___x_332_ = 32ULL;
v___x_333_ = lean_unbox_uint64(v___x_331_);
v___x_334_ = lean_uint64_shift_right(v___x_333_, v___x_332_);
v___x_335_ = lean_unbox_uint64(v___x_331_);
lean_dec_ref(v___x_331_);
v_fold_336_ = lean_uint64_xor(v___x_335_, v___x_334_);
v___x_337_ = 16ULL;
v___x_338_ = lean_uint64_shift_right(v_fold_336_, v___x_337_);
v___x_339_ = lean_uint64_xor(v_fold_336_, v___x_338_);
v___x_340_ = lean_uint64_to_usize(v___x_339_);
v___x_341_ = lean_usize_of_nat(v___x_324_);
v___x_342_ = ((size_t)1ULL);
v___x_343_ = lean_usize_sub(v___x_341_, v___x_342_);
v___x_344_ = lean_usize_land(v___x_340_, v___x_343_);
v_bkt_345_ = lean_array_uget_borrowed(v_buckets_322_, v___x_344_);
lean_inc(v_bkt_345_);
lean_inc(v_a_319_);
lean_inc_ref(v_inst_316_);
v___x_346_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_316_, v_a_319_, v_bkt_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; lean_object* v_size_x27_348_; lean_object* v___x_349_; lean_object* v_buckets_x27_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
lean_dec_ref(v_inst_316_);
v___x_347_ = lean_unsigned_to_nat(1u);
v_size_x27_348_ = lean_nat_add(v_size_321_, v___x_347_);
lean_dec(v_size_321_);
lean_inc(v_bkt_345_);
v___x_349_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_349_, 0, v_a_319_);
lean_ctor_set(v___x_349_, 1, v_b_320_);
lean_ctor_set(v___x_349_, 2, v_bkt_345_);
v_buckets_x27_350_ = lean_array_uset(v_buckets_322_, v___x_344_, v___x_349_);
v___x_351_ = lean_unsigned_to_nat(4u);
v___x_352_ = lean_nat_mul(v_size_x27_348_, v___x_351_);
v___x_353_ = lean_unsigned_to_nat(3u);
v___x_354_ = lean_nat_div(v___x_352_, v___x_353_);
lean_dec(v___x_352_);
v___x_355_ = lean_array_get_size(v_buckets_x27_350_);
v___x_356_ = lean_nat_dec_le(v___x_354_, v___x_355_);
lean_dec(v___x_354_);
if (v___x_356_ == 0)
{
lean_object* v_val_357_; lean_object* v___x_359_; 
v_val_357_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_317_, v_buckets_x27_350_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_val_357_);
lean_ctor_set(v___x_329_, 0, v_size_x27_348_);
v___x_359_ = v___x_329_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_size_x27_348_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_val_357_);
v___x_359_ = v_reuseFailAlloc_362_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_box(v___x_346_);
v___x_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v___x_359_);
return v___x_361_;
}
}
else
{
lean_object* v___x_364_; 
lean_dec_ref(v_inst_317_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_buckets_x27_350_);
lean_ctor_set(v___x_329_, 0, v_size_x27_348_);
v___x_364_ = v___x_329_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_size_x27_348_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v_buckets_x27_350_);
v___x_364_ = v_reuseFailAlloc_367_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
lean_object* v___x_365_; lean_object* v___x_366_; 
v___x_365_ = lean_box(v___x_346_);
v___x_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_364_);
return v___x_366_;
}
}
}
else
{
lean_object* v___x_368_; lean_object* v_buckets_x27_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_373_; 
lean_inc(v_bkt_345_);
lean_dec_ref(v_inst_317_);
v___x_368_ = lean_box(0);
v_buckets_x27_369_ = lean_array_uset(v_buckets_322_, v___x_344_, v___x_368_);
v___x_370_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_316_, v_a_319_, v_b_320_, v_bkt_345_);
v___x_371_ = lean_array_uset(v_buckets_x27_369_, v___x_344_, v___x_370_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v___x_371_);
v___x_373_ = v___x_329_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_size_321_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_371_);
v___x_373_ = v_reuseFailAlloc_376_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = lean_box(v___x_346_);
v___x_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_374_);
lean_ctor_set(v___x_375_, 1, v___x_373_);
return v___x_375_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_m_382_, lean_object* v_a_383_, lean_object* v_b_384_){
_start:
{
lean_object* v_size_385_; lean_object* v_buckets_386_; lean_object* v___x_387_; lean_object* v___x_388_; uint8_t v___x_389_; 
v_size_385_ = lean_ctor_get(v_m_382_, 0);
v_buckets_386_ = lean_ctor_get(v_m_382_, 1);
v___x_387_ = lean_unsigned_to_nat(0u);
v___x_388_ = lean_array_get_size(v_buckets_386_);
v___x_389_ = lean_nat_dec_lt(v___x_387_, v___x_388_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_b_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_inst_381_);
lean_dec_ref(v_inst_380_);
v___x_390_ = lean_box(v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v_m_382_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; uint64_t v___x_393_; uint64_t v___x_394_; uint64_t v___x_395_; uint64_t v___x_396_; uint64_t v_fold_397_; uint64_t v___x_398_; uint64_t v___x_399_; uint64_t v___x_400_; size_t v___x_401_; size_t v___x_402_; size_t v___x_403_; size_t v___x_404_; size_t v___x_405_; lean_object* v_bkt_406_; uint8_t v___x_407_; 
lean_inc_ref(v_inst_381_);
lean_inc(v_a_383_);
v___x_392_ = lean_apply_1(v_inst_381_, v_a_383_);
v___x_393_ = 32ULL;
v___x_394_ = lean_unbox_uint64(v___x_392_);
v___x_395_ = lean_uint64_shift_right(v___x_394_, v___x_393_);
v___x_396_ = lean_unbox_uint64(v___x_392_);
lean_dec_ref(v___x_392_);
v_fold_397_ = lean_uint64_xor(v___x_396_, v___x_395_);
v___x_398_ = 16ULL;
v___x_399_ = lean_uint64_shift_right(v_fold_397_, v___x_398_);
v___x_400_ = lean_uint64_xor(v_fold_397_, v___x_399_);
v___x_401_ = lean_uint64_to_usize(v___x_400_);
v___x_402_ = lean_usize_of_nat(v___x_388_);
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_sub(v___x_402_, v___x_403_);
v___x_405_ = lean_usize_land(v___x_401_, v___x_404_);
v_bkt_406_ = lean_array_uget_borrowed(v_buckets_386_, v___x_405_);
lean_inc(v_bkt_406_);
lean_inc(v_a_383_);
v___x_407_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_380_, v_a_383_, v_bkt_406_);
if (v___x_407_ == 0)
{
lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_432_; 
lean_inc_ref(v_buckets_386_);
lean_inc(v_size_385_);
v_isSharedCheck_432_ = !lean_is_exclusive(v_m_382_);
if (v_isSharedCheck_432_ == 0)
{
lean_object* v_unused_433_; lean_object* v_unused_434_; 
v_unused_433_ = lean_ctor_get(v_m_382_, 1);
lean_dec(v_unused_433_);
v_unused_434_ = lean_ctor_get(v_m_382_, 0);
lean_dec(v_unused_434_);
v___x_409_ = v_m_382_;
v_isShared_410_ = v_isSharedCheck_432_;
goto v_resetjp_408_;
}
else
{
lean_dec(v_m_382_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_432_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
lean_object* v___x_411_; lean_object* v_size_x27_412_; lean_object* v___x_413_; lean_object* v_buckets_x27_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v_size_x27_412_ = lean_nat_add(v_size_385_, v___x_411_);
lean_dec(v_size_385_);
lean_inc(v_bkt_406_);
v___x_413_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_413_, 0, v_a_383_);
lean_ctor_set(v___x_413_, 1, v_b_384_);
lean_ctor_set(v___x_413_, 2, v_bkt_406_);
v_buckets_x27_414_ = lean_array_uset(v_buckets_386_, v___x_405_, v___x_413_);
v___x_415_ = lean_unsigned_to_nat(4u);
v___x_416_ = lean_nat_mul(v_size_x27_412_, v___x_415_);
v___x_417_ = lean_unsigned_to_nat(3u);
v___x_418_ = lean_nat_div(v___x_416_, v___x_417_);
lean_dec(v___x_416_);
v___x_419_ = lean_array_get_size(v_buckets_x27_414_);
v___x_420_ = lean_nat_dec_le(v___x_418_, v___x_419_);
lean_dec(v___x_418_);
if (v___x_420_ == 0)
{
lean_object* v_val_421_; lean_object* v___x_423_; 
v_val_421_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_381_, v_buckets_x27_414_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v_val_421_);
lean_ctor_set(v___x_409_, 0, v_size_x27_412_);
v___x_423_ = v___x_409_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v_size_x27_412_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_val_421_);
v___x_423_ = v_reuseFailAlloc_426_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_424_ = lean_box(v___x_407_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v___x_424_);
lean_ctor_set(v___x_425_, 1, v___x_423_);
return v___x_425_;
}
}
else
{
lean_object* v___x_428_; 
lean_dec_ref(v_inst_381_);
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 1, v_buckets_x27_414_);
lean_ctor_set(v___x_409_, 0, v_size_x27_412_);
v___x_428_ = v___x_409_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_size_x27_412_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_buckets_x27_414_);
v___x_428_ = v_reuseFailAlloc_431_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_box(v___x_407_);
v___x_430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
lean_ctor_set(v___x_430_, 1, v___x_428_);
return v___x_430_;
}
}
}
}
else
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_b_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_inst_381_);
v___x_435_ = lean_box(v___x_407_);
v___x_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v_m_382_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_437_, lean_object* v_00_u03b2_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_m_441_, lean_object* v_a_442_, lean_object* v_b_443_){
_start:
{
lean_object* v_size_444_; lean_object* v_buckets_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v_size_444_ = lean_ctor_get(v_m_441_, 0);
v_buckets_445_ = lean_ctor_get(v_m_441_, 1);
v___x_446_ = lean_unsigned_to_nat(0u);
v___x_447_ = lean_array_get_size(v_buckets_445_);
v___x_448_ = lean_nat_dec_lt(v___x_446_, v___x_447_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; lean_object* v___x_450_; 
lean_dec(v_b_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_inst_440_);
lean_dec_ref(v_inst_439_);
v___x_449_ = lean_box(v___x_448_);
v___x_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v_m_441_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; uint64_t v___x_452_; uint64_t v___x_453_; uint64_t v___x_454_; uint64_t v___x_455_; uint64_t v_fold_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; size_t v___x_460_; size_t v___x_461_; size_t v___x_462_; size_t v___x_463_; size_t v___x_464_; lean_object* v_bkt_465_; uint8_t v___x_466_; 
lean_inc_ref(v_inst_440_);
lean_inc(v_a_442_);
v___x_451_ = lean_apply_1(v_inst_440_, v_a_442_);
v___x_452_ = 32ULL;
v___x_453_ = lean_unbox_uint64(v___x_451_);
v___x_454_ = lean_uint64_shift_right(v___x_453_, v___x_452_);
v___x_455_ = lean_unbox_uint64(v___x_451_);
lean_dec_ref(v___x_451_);
v_fold_456_ = lean_uint64_xor(v___x_455_, v___x_454_);
v___x_457_ = 16ULL;
v___x_458_ = lean_uint64_shift_right(v_fold_456_, v___x_457_);
v___x_459_ = lean_uint64_xor(v_fold_456_, v___x_458_);
v___x_460_ = lean_uint64_to_usize(v___x_459_);
v___x_461_ = lean_usize_of_nat(v___x_447_);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_sub(v___x_461_, v___x_462_);
v___x_464_ = lean_usize_land(v___x_460_, v___x_463_);
v_bkt_465_ = lean_array_uget_borrowed(v_buckets_445_, v___x_464_);
lean_inc(v_bkt_465_);
lean_inc(v_a_442_);
v___x_466_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_439_, v_a_442_, v_bkt_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_491_; 
lean_inc_ref(v_buckets_445_);
lean_inc(v_size_444_);
v_isSharedCheck_491_ = !lean_is_exclusive(v_m_441_);
if (v_isSharedCheck_491_ == 0)
{
lean_object* v_unused_492_; lean_object* v_unused_493_; 
v_unused_492_ = lean_ctor_get(v_m_441_, 1);
lean_dec(v_unused_492_);
v_unused_493_ = lean_ctor_get(v_m_441_, 0);
lean_dec(v_unused_493_);
v___x_468_ = v_m_441_;
v_isShared_469_ = v_isSharedCheck_491_;
goto v_resetjp_467_;
}
else
{
lean_dec(v_m_441_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_491_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v_size_x27_471_; lean_object* v___x_472_; lean_object* v_buckets_x27_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_470_ = lean_unsigned_to_nat(1u);
v_size_x27_471_ = lean_nat_add(v_size_444_, v___x_470_);
lean_dec(v_size_444_);
lean_inc(v_bkt_465_);
v___x_472_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_472_, 0, v_a_442_);
lean_ctor_set(v___x_472_, 1, v_b_443_);
lean_ctor_set(v___x_472_, 2, v_bkt_465_);
v_buckets_x27_473_ = lean_array_uset(v_buckets_445_, v___x_464_, v___x_472_);
v___x_474_ = lean_unsigned_to_nat(4u);
v___x_475_ = lean_nat_mul(v_size_x27_471_, v___x_474_);
v___x_476_ = lean_unsigned_to_nat(3u);
v___x_477_ = lean_nat_div(v___x_475_, v___x_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_array_get_size(v_buckets_x27_473_);
v___x_479_ = lean_nat_dec_le(v___x_477_, v___x_478_);
lean_dec(v___x_477_);
if (v___x_479_ == 0)
{
lean_object* v_val_480_; lean_object* v___x_482_; 
v_val_480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_440_, v_buckets_x27_473_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v_val_480_);
lean_ctor_set(v___x_468_, 0, v_size_x27_471_);
v___x_482_ = v___x_468_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_size_x27_471_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v_val_480_);
v___x_482_ = v_reuseFailAlloc_485_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_box(v___x_466_);
v___x_484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
lean_ctor_set(v___x_484_, 1, v___x_482_);
return v___x_484_;
}
}
else
{
lean_object* v___x_487_; 
lean_dec_ref(v_inst_440_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v_buckets_x27_473_);
lean_ctor_set(v___x_468_, 0, v_size_x27_471_);
v___x_487_ = v___x_468_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_size_x27_471_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_buckets_x27_473_);
v___x_487_ = v_reuseFailAlloc_490_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_box(v___x_466_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
return v___x_489_;
}
}
}
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec(v_b_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_inst_440_);
v___x_494_ = lean_box(v___x_466_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
lean_ctor_set(v___x_495_, 1, v_m_441_);
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_m_498_, lean_object* v_a_499_, lean_object* v_b_500_){
_start:
{
lean_object* v_size_501_; lean_object* v_buckets_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v_size_501_ = lean_ctor_get(v_m_498_, 0);
v_buckets_502_ = lean_ctor_get(v_m_498_, 1);
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_array_get_size(v_buckets_502_);
v___x_505_ = lean_nat_dec_lt(v___x_503_, v___x_504_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_b_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_inst_497_);
lean_dec_ref(v_inst_496_);
v___x_506_ = lean_box(0);
v___x_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v_m_498_);
return v___x_507_;
}
else
{
lean_object* v___x_508_; uint64_t v___x_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v_fold_513_; uint64_t v___x_514_; uint64_t v___x_515_; uint64_t v___x_516_; size_t v___x_517_; size_t v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; lean_object* v_bkt_522_; lean_object* v___x_523_; 
lean_inc_ref(v_inst_497_);
lean_inc(v_a_499_);
v___x_508_ = lean_apply_1(v_inst_497_, v_a_499_);
v___x_509_ = 32ULL;
v___x_510_ = lean_unbox_uint64(v___x_508_);
v___x_511_ = lean_uint64_shift_right(v___x_510_, v___x_509_);
v___x_512_ = lean_unbox_uint64(v___x_508_);
lean_dec_ref(v___x_508_);
v_fold_513_ = lean_uint64_xor(v___x_512_, v___x_511_);
v___x_514_ = 16ULL;
v___x_515_ = lean_uint64_shift_right(v_fold_513_, v___x_514_);
v___x_516_ = lean_uint64_xor(v_fold_513_, v___x_515_);
v___x_517_ = lean_uint64_to_usize(v___x_516_);
v___x_518_ = lean_usize_of_nat(v___x_504_);
v___x_519_ = ((size_t)1ULL);
v___x_520_ = lean_usize_sub(v___x_518_, v___x_519_);
v___x_521_ = lean_usize_land(v___x_517_, v___x_520_);
v_bkt_522_ = lean_array_uget_borrowed(v_buckets_502_, v___x_521_);
lean_inc(v_bkt_522_);
lean_inc(v_a_499_);
v___x_523_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_496_, v_a_499_, v_bkt_522_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_546_; 
lean_inc_ref(v_buckets_502_);
lean_inc(v_size_501_);
v_isSharedCheck_546_ = !lean_is_exclusive(v_m_498_);
if (v_isSharedCheck_546_ == 0)
{
lean_object* v_unused_547_; lean_object* v_unused_548_; 
v_unused_547_ = lean_ctor_get(v_m_498_, 1);
lean_dec(v_unused_547_);
v_unused_548_ = lean_ctor_get(v_m_498_, 0);
lean_dec(v_unused_548_);
v___x_525_ = v_m_498_;
v_isShared_526_ = v_isSharedCheck_546_;
goto v_resetjp_524_;
}
else
{
lean_dec(v_m_498_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_546_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v_size_x27_528_; lean_object* v___x_529_; lean_object* v_buckets_x27_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_527_ = lean_unsigned_to_nat(1u);
v_size_x27_528_ = lean_nat_add(v_size_501_, v___x_527_);
lean_dec(v_size_501_);
lean_inc(v_bkt_522_);
v___x_529_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_529_, 0, v_a_499_);
lean_ctor_set(v___x_529_, 1, v_b_500_);
lean_ctor_set(v___x_529_, 2, v_bkt_522_);
v_buckets_x27_530_ = lean_array_uset(v_buckets_502_, v___x_521_, v___x_529_);
v___x_531_ = lean_unsigned_to_nat(4u);
v___x_532_ = lean_nat_mul(v_size_x27_528_, v___x_531_);
v___x_533_ = lean_unsigned_to_nat(3u);
v___x_534_ = lean_nat_div(v___x_532_, v___x_533_);
lean_dec(v___x_532_);
v___x_535_ = lean_array_get_size(v_buckets_x27_530_);
v___x_536_ = lean_nat_dec_le(v___x_534_, v___x_535_);
lean_dec(v___x_534_);
if (v___x_536_ == 0)
{
lean_object* v_val_537_; lean_object* v___x_539_; 
v_val_537_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_497_, v_buckets_x27_530_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_val_537_);
lean_ctor_set(v___x_525_, 0, v_size_x27_528_);
v___x_539_ = v___x_525_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_size_x27_528_);
lean_ctor_set(v_reuseFailAlloc_541_, 1, v_val_537_);
v___x_539_ = v_reuseFailAlloc_541_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; 
v___x_540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_523_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
return v___x_540_;
}
}
else
{
lean_object* v___x_543_; 
lean_dec_ref(v_inst_497_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_buckets_x27_530_);
lean_ctor_set(v___x_525_, 0, v_size_x27_528_);
v___x_543_ = v___x_525_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_size_x27_528_);
lean_ctor_set(v_reuseFailAlloc_545_, 1, v_buckets_x27_530_);
v___x_543_ = v_reuseFailAlloc_545_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_544_; 
v___x_544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_544_, 0, v___x_523_);
lean_ctor_set(v___x_544_, 1, v___x_543_);
return v___x_544_;
}
}
}
}
else
{
lean_object* v___x_549_; 
lean_dec(v_b_500_);
lean_dec(v_a_499_);
lean_dec_ref(v_inst_497_);
v___x_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_523_);
lean_ctor_set(v___x_549_, 1, v_m_498_);
return v___x_549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_550_, lean_object* v_00_u03b2_551_, lean_object* v_inst_552_, lean_object* v_inst_553_, lean_object* v_m_554_, lean_object* v_a_555_, lean_object* v_b_556_){
_start:
{
lean_object* v_size_557_; lean_object* v_buckets_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_size_557_ = lean_ctor_get(v_m_554_, 0);
v_buckets_558_ = lean_ctor_get(v_m_554_, 1);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_560_ = lean_array_get_size(v_buckets_558_);
v___x_561_ = lean_nat_dec_lt(v___x_559_, v___x_560_);
if (v___x_561_ == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v_b_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_inst_553_);
lean_dec_ref(v_inst_552_);
v___x_562_ = lean_box(0);
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v___x_562_);
lean_ctor_set(v___x_563_, 1, v_m_554_);
return v___x_563_;
}
else
{
lean_object* v___x_564_; uint64_t v___x_565_; uint64_t v___x_566_; uint64_t v___x_567_; uint64_t v___x_568_; uint64_t v_fold_569_; uint64_t v___x_570_; uint64_t v___x_571_; uint64_t v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; lean_object* v_bkt_578_; lean_object* v___x_579_; 
lean_inc_ref(v_inst_553_);
lean_inc(v_a_555_);
v___x_564_ = lean_apply_1(v_inst_553_, v_a_555_);
v___x_565_ = 32ULL;
v___x_566_ = lean_unbox_uint64(v___x_564_);
v___x_567_ = lean_uint64_shift_right(v___x_566_, v___x_565_);
v___x_568_ = lean_unbox_uint64(v___x_564_);
lean_dec_ref(v___x_564_);
v_fold_569_ = lean_uint64_xor(v___x_568_, v___x_567_);
v___x_570_ = 16ULL;
v___x_571_ = lean_uint64_shift_right(v_fold_569_, v___x_570_);
v___x_572_ = lean_uint64_xor(v_fold_569_, v___x_571_);
v___x_573_ = lean_uint64_to_usize(v___x_572_);
v___x_574_ = lean_usize_of_nat(v___x_560_);
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_sub(v___x_574_, v___x_575_);
v___x_577_ = lean_usize_land(v___x_573_, v___x_576_);
v_bkt_578_ = lean_array_uget_borrowed(v_buckets_558_, v___x_577_);
lean_inc(v_bkt_578_);
lean_inc(v_a_555_);
v___x_579_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_552_, v_a_555_, v_bkt_578_);
if (lean_obj_tag(v___x_579_) == 0)
{
lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_602_; 
lean_inc_ref(v_buckets_558_);
lean_inc(v_size_557_);
v_isSharedCheck_602_ = !lean_is_exclusive(v_m_554_);
if (v_isSharedCheck_602_ == 0)
{
lean_object* v_unused_603_; lean_object* v_unused_604_; 
v_unused_603_ = lean_ctor_get(v_m_554_, 1);
lean_dec(v_unused_603_);
v_unused_604_ = lean_ctor_get(v_m_554_, 0);
lean_dec(v_unused_604_);
v___x_581_ = v_m_554_;
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
else
{
lean_dec(v_m_554_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_602_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v_size_x27_584_; lean_object* v___x_585_; lean_object* v_buckets_x27_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_583_ = lean_unsigned_to_nat(1u);
v_size_x27_584_ = lean_nat_add(v_size_557_, v___x_583_);
lean_dec(v_size_557_);
lean_inc(v_bkt_578_);
v___x_585_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_585_, 0, v_a_555_);
lean_ctor_set(v___x_585_, 1, v_b_556_);
lean_ctor_set(v___x_585_, 2, v_bkt_578_);
v_buckets_x27_586_ = lean_array_uset(v_buckets_558_, v___x_577_, v___x_585_);
v___x_587_ = lean_unsigned_to_nat(4u);
v___x_588_ = lean_nat_mul(v_size_x27_584_, v___x_587_);
v___x_589_ = lean_unsigned_to_nat(3u);
v___x_590_ = lean_nat_div(v___x_588_, v___x_589_);
lean_dec(v___x_588_);
v___x_591_ = lean_array_get_size(v_buckets_x27_586_);
v___x_592_ = lean_nat_dec_le(v___x_590_, v___x_591_);
lean_dec(v___x_590_);
if (v___x_592_ == 0)
{
lean_object* v_val_593_; lean_object* v___x_595_; 
v_val_593_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_553_, v_buckets_x27_586_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_val_593_);
lean_ctor_set(v___x_581_, 0, v_size_x27_584_);
v___x_595_ = v___x_581_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_size_x27_584_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_val_593_);
v___x_595_ = v_reuseFailAlloc_597_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
lean_object* v___x_596_; 
v___x_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_579_);
lean_ctor_set(v___x_596_, 1, v___x_595_);
return v___x_596_;
}
}
else
{
lean_object* v___x_599_; 
lean_dec_ref(v_inst_553_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_buckets_x27_586_);
lean_ctor_set(v___x_581_, 0, v_size_x27_584_);
v___x_599_ = v___x_581_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_size_x27_584_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_buckets_x27_586_);
v___x_599_ = v_reuseFailAlloc_601_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_600_, 0, v___x_579_);
lean_ctor_set(v___x_600_, 1, v___x_599_);
return v___x_600_;
}
}
}
}
else
{
lean_object* v___x_605_; 
lean_dec(v_b_556_);
lean_dec(v_a_555_);
lean_dec_ref(v_inst_553_);
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_579_);
lean_ctor_set(v___x_605_, 1, v_m_554_);
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg(lean_object* v_beq_606_, lean_object* v_inst_607_, lean_object* v_m_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_buckets_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_buckets_610_ = lean_ctor_get(v_m_608_, 1);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_array_get_size(v_buckets_610_);
v___x_613_ = lean_nat_dec_lt(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; 
lean_dec(v_a_609_);
lean_dec_ref(v_inst_607_);
lean_dec_ref(v_beq_606_);
v___x_614_ = lean_box(0);
return v___x_614_;
}
else
{
lean_object* v___x_615_; 
v___x_615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_606_, v_inst_607_, v_m_608_, v_a_609_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg___boxed(lean_object* v_beq_616_, lean_object* v_inst_617_, lean_object* v_m_618_, lean_object* v_a_619_){
_start:
{
lean_object* v_res_620_; 
v_res_620_ = l_Std_HashMap_Raw_get_x3f___redArg(v_beq_616_, v_inst_617_, v_m_618_, v_a_619_);
lean_dec_ref(v_m_618_);
return v_res_620_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f(lean_object* v_00_u03b1_621_, lean_object* v_00_u03b2_622_, lean_object* v_beq_623_, lean_object* v_inst_624_, lean_object* v_m_625_, lean_object* v_a_626_){
_start:
{
lean_object* v_buckets_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_buckets_627_ = lean_ctor_get(v_m_625_, 1);
v___x_628_ = lean_unsigned_to_nat(0u);
v___x_629_ = lean_array_get_size(v_buckets_627_);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; 
lean_dec(v_a_626_);
lean_dec_ref(v_inst_624_);
lean_dec_ref(v_beq_623_);
v___x_631_ = lean_box(0);
return v___x_631_;
}
else
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_623_, v_inst_624_, v_m_625_, v_a_626_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_633_, lean_object* v_00_u03b2_634_, lean_object* v_beq_635_, lean_object* v_inst_636_, lean_object* v_m_637_, lean_object* v_a_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Std_HashMap_Raw_get_x3f(v_00_u03b1_633_, v_00_u03b2_634_, v_beq_635_, v_inst_636_, v_m_637_, v_a_638_);
lean_dec_ref(v_m_637_);
return v_res_639_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains___redArg(lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_m_642_, lean_object* v_a_643_){
_start:
{
lean_object* v_buckets_644_; lean_object* v___x_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_buckets_644_ = lean_ctor_get(v_m_642_, 1);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = lean_array_get_size(v_buckets_644_);
v___x_647_ = lean_nat_dec_lt(v___x_645_, v___x_646_);
if (v___x_647_ == 0)
{
lean_dec(v_a_643_);
lean_dec_ref(v_inst_641_);
lean_dec_ref(v_inst_640_);
return v___x_647_;
}
else
{
uint8_t v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_640_, v_inst_641_, v_m_642_, v_a_643_);
return v___x_648_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___redArg___boxed(lean_object* v_inst_649_, lean_object* v_inst_650_, lean_object* v_m_651_, lean_object* v_a_652_){
_start:
{
uint8_t v_res_653_; lean_object* v_r_654_; 
v_res_653_ = l_Std_HashMap_Raw_contains___redArg(v_inst_649_, v_inst_650_, v_m_651_, v_a_652_);
lean_dec_ref(v_m_651_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains(lean_object* v_00_u03b1_655_, lean_object* v_00_u03b2_656_, lean_object* v_inst_657_, lean_object* v_inst_658_, lean_object* v_m_659_, lean_object* v_a_660_){
_start:
{
lean_object* v_buckets_661_; lean_object* v___x_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_buckets_661_ = lean_ctor_get(v_m_659_, 1);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_array_get_size(v_buckets_661_);
v___x_664_ = lean_nat_dec_lt(v___x_662_, v___x_663_);
if (v___x_664_ == 0)
{
lean_dec(v_a_660_);
lean_dec_ref(v_inst_658_);
lean_dec_ref(v_inst_657_);
return v___x_664_;
}
else
{
uint8_t v___x_665_; 
v___x_665_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_657_, v_inst_658_, v_m_659_, v_a_660_);
return v___x_665_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___boxed(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b2_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_m_670_, lean_object* v_a_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_Std_HashMap_Raw_contains(v_00_u03b1_666_, v_00_u03b2_667_, v_inst_668_, v_inst_669_, v_m_670_, v_a_671_);
lean_dec_ref(v_m_670_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_inst_676_, lean_object* v_inst_677_){
_start:
{
lean_object* v___x_678_; 
v___x_678_ = lean_box(0);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_679_, lean_object* v_00_u03b2_680_, lean_object* v_inst_681_, lean_object* v_inst_682_){
_start:
{
lean_object* v_res_683_; 
v_res_683_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_679_, v_00_u03b2_680_, v_inst_681_, v_inst_682_);
lean_dec_ref(v_inst_682_);
lean_dec_ref(v_inst_681_);
return v_res_683_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_684_, lean_object* v_inst_685_, lean_object* v_m_686_, lean_object* v_a_687_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_684_, v_inst_685_, v_m_686_, v_a_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_689_, lean_object* v_inst_690_, lean_object* v_m_691_, lean_object* v_a_692_){
_start:
{
uint8_t v_res_693_; lean_object* v_r_694_; 
v_res_693_ = l_Std_HashMap_Raw_instDecidableMem___redArg(v_inst_689_, v_inst_690_, v_m_691_, v_a_692_);
lean_dec_ref(v_m_691_);
v_r_694_ = lean_box(v_res_693_);
return v_r_694_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_m_699_, lean_object* v_a_700_){
_start:
{
uint8_t v___x_701_; 
v___x_701_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_697_, v_inst_698_, v_m_699_, v_a_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_702_, lean_object* v_00_u03b2_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_m_706_, lean_object* v_a_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Std_HashMap_Raw_instDecidableMem(v_00_u03b1_702_, v_00_u03b2_703_, v_inst_704_, v_inst_705_, v_m_706_, v_a_707_);
lean_dec_ref(v_m_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg(lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_m_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_710_, v_inst_711_, v_m_712_, v_a_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg___boxed(lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_m_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_HashMap_Raw_get___redArg(v_inst_715_, v_inst_716_, v_m_717_, v_a_718_);
lean_dec_ref(v_m_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get(lean_object* v_00_u03b1_720_, lean_object* v_00_u03b2_721_, lean_object* v_inst_722_, lean_object* v_inst_723_, lean_object* v_m_724_, lean_object* v_a_725_, lean_object* v_h_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_722_, v_inst_723_, v_m_724_, v_a_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___boxed(lean_object* v_00_u03b1_728_, lean_object* v_00_u03b2_729_, lean_object* v_inst_730_, lean_object* v_inst_731_, lean_object* v_m_732_, lean_object* v_a_733_, lean_object* v_h_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_HashMap_Raw_get(v_00_u03b1_728_, v_00_u03b2_729_, v_inst_730_, v_inst_731_, v_m_732_, v_a_733_, v_h_734_);
lean_dec_ref(v_m_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg(lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_m_738_, lean_object* v_a_739_, lean_object* v_fallback_740_){
_start:
{
lean_object* v_buckets_741_; lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v_buckets_741_ = lean_ctor_get(v_m_738_, 1);
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = lean_array_get_size(v_buckets_741_);
v___x_744_ = lean_nat_dec_lt(v___x_742_, v___x_743_);
if (v___x_744_ == 0)
{
lean_dec(v_a_739_);
lean_dec_ref(v_inst_737_);
lean_dec_ref(v_inst_736_);
lean_inc(v_fallback_740_);
return v_fallback_740_;
}
else
{
lean_object* v___x_745_; 
v___x_745_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_736_, v_inst_737_, v_m_738_, v_a_739_, v_fallback_740_);
return v___x_745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg___boxed(lean_object* v_inst_746_, lean_object* v_inst_747_, lean_object* v_m_748_, lean_object* v_a_749_, lean_object* v_fallback_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_Std_HashMap_Raw_getD___redArg(v_inst_746_, v_inst_747_, v_m_748_, v_a_749_, v_fallback_750_);
lean_dec(v_fallback_750_);
lean_dec_ref(v_m_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD(lean_object* v_00_u03b1_752_, lean_object* v_00_u03b2_753_, lean_object* v_inst_754_, lean_object* v_inst_755_, lean_object* v_m_756_, lean_object* v_a_757_, lean_object* v_fallback_758_){
_start:
{
lean_object* v_buckets_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_buckets_759_ = lean_ctor_get(v_m_756_, 1);
v___x_760_ = lean_unsigned_to_nat(0u);
v___x_761_ = lean_array_get_size(v_buckets_759_);
v___x_762_ = lean_nat_dec_lt(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_dec(v_a_757_);
lean_dec_ref(v_inst_755_);
lean_dec_ref(v_inst_754_);
lean_inc(v_fallback_758_);
return v_fallback_758_;
}
else
{
lean_object* v___x_763_; 
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_754_, v_inst_755_, v_m_756_, v_a_757_, v_fallback_758_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___boxed(lean_object* v_00_u03b1_764_, lean_object* v_00_u03b2_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_m_768_, lean_object* v_a_769_, lean_object* v_fallback_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Std_HashMap_Raw_getD(v_00_u03b1_764_, v_00_u03b2_765_, v_inst_766_, v_inst_767_, v_m_768_, v_a_769_, v_fallback_770_);
lean_dec(v_fallback_770_);
lean_dec_ref(v_m_768_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg(lean_object* v_inst_772_, lean_object* v_inst_773_, lean_object* v_inst_774_, lean_object* v_m_775_, lean_object* v_a_776_){
_start:
{
lean_object* v_buckets_777_; lean_object* v___x_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_buckets_777_ = lean_ctor_get(v_m_775_, 1);
v___x_778_ = lean_unsigned_to_nat(0u);
v___x_779_ = lean_array_get_size(v_buckets_777_);
v___x_780_ = lean_nat_dec_lt(v___x_778_, v___x_779_);
if (v___x_780_ == 0)
{
lean_dec(v_a_776_);
lean_dec_ref(v_inst_773_);
lean_dec_ref(v_inst_772_);
return v_inst_774_;
}
else
{
lean_object* v___x_781_; 
v___x_781_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_772_, v_inst_773_, v_inst_774_, v_m_775_, v_a_776_);
return v___x_781_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_m_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Std_HashMap_Raw_get_x21___redArg(v_inst_782_, v_inst_783_, v_inst_784_, v_m_785_, v_a_786_);
lean_dec_ref(v_m_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21(lean_object* v_00_u03b1_788_, lean_object* v_00_u03b2_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_m_793_, lean_object* v_a_794_){
_start:
{
lean_object* v_buckets_795_; lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v_buckets_795_ = lean_ctor_get(v_m_793_, 1);
v___x_796_ = lean_unsigned_to_nat(0u);
v___x_797_ = lean_array_get_size(v_buckets_795_);
v___x_798_ = lean_nat_dec_lt(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
lean_dec(v_a_794_);
lean_dec_ref(v_inst_791_);
lean_dec_ref(v_inst_790_);
return v_inst_792_;
}
else
{
lean_object* v___x_799_; 
v___x_799_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_790_, v_inst_791_, v_inst_792_, v_m_793_, v_a_794_);
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_800_, lean_object* v_00_u03b2_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_m_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_HashMap_Raw_get_x21(v_00_u03b1_800_, v_00_u03b2_801_, v_inst_802_, v_inst_803_, v_inst_804_, v_m_805_, v_a_806_);
lean_dec_ref(v_m_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_m_810_, lean_object* v_a_811_, lean_object* v_h_812_){
_start:
{
lean_object* v___x_813_; 
v___x_813_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_808_, v_inst_809_, v_m_810_, v_a_811_);
return v___x_813_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_m_816_, lean_object* v_a_817_, lean_object* v_h_818_){
_start:
{
lean_object* v_res_819_; 
v_res_819_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(v_inst_814_, v_inst_815_, v_m_816_, v_a_817_, v_h_818_);
lean_dec_ref(v_m_816_);
return v_res_819_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_m_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_buckets_824_; lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v_buckets_824_ = lean_ctor_get(v_m_822_, 1);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_array_get_size(v_buckets_824_);
v___x_827_ = lean_nat_dec_lt(v___x_825_, v___x_826_);
if (v___x_827_ == 0)
{
lean_object* v___x_828_; 
lean_dec(v_a_823_);
lean_dec_ref(v_inst_821_);
lean_dec_ref(v_inst_820_);
v___x_828_ = lean_box(0);
return v___x_828_;
}
else
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_820_, v_inst_821_, v_m_822_, v_a_823_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_m_832_, lean_object* v_a_833_){
_start:
{
lean_object* v_res_834_; 
v_res_834_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(v_inst_830_, v_inst_831_, v_m_832_, v_a_833_);
lean_dec_ref(v_m_832_);
return v_res_834_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_m_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_buckets_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v_buckets_840_ = lean_ctor_get(v_m_838_, 1);
v___x_841_ = lean_unsigned_to_nat(0u);
v___x_842_ = lean_array_get_size(v_buckets_840_);
v___x_843_ = lean_nat_dec_lt(v___x_841_, v___x_842_);
if (v___x_843_ == 0)
{
lean_dec(v_a_839_);
lean_dec_ref(v_inst_836_);
lean_dec_ref(v_inst_835_);
return v_inst_837_;
}
else
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_835_, v_inst_836_, v_inst_837_, v_m_838_, v_a_839_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_m_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_res_850_; 
v_res_850_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(v_inst_845_, v_inst_846_, v_inst_847_, v_m_848_, v_a_849_);
lean_dec_ref(v_m_848_);
return v_res_850_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(lean_object* v_inst_851_, lean_object* v_inst_852_){
_start:
{
lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___x_856_; 
lean_inc_ref(v_inst_852_);
lean_inc_ref(v_inst_851_);
v___f_853_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_853_, 0, v_inst_851_);
lean_closure_set(v___f_853_, 1, v_inst_852_);
lean_inc_ref(v_inst_852_);
lean_inc_ref(v_inst_851_);
v___f_854_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_854_, 0, v_inst_851_);
lean_closure_set(v___f_854_, 1, v_inst_852_);
v___f_855_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_855_, 0, v_inst_851_);
lean_closure_set(v___f_855_, 1, v_inst_852_);
v___x_856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_856_, 0, v___f_853_);
lean_ctor_set(v___x_856_, 1, v___f_854_);
lean_ctor_set(v___x_856_, 2, v___f_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem(lean_object* v_00_u03b1_857_, lean_object* v_00_u03b2_858_, lean_object* v_inst_859_, lean_object* v_inst_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(v_inst_859_, v_inst_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_m_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_buckets_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_buckets_866_ = lean_ctor_get(v_m_864_, 1);
v___x_867_ = lean_unsigned_to_nat(0u);
v___x_868_ = lean_array_get_size(v_buckets_866_);
v___x_869_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
lean_dec(v_a_865_);
lean_dec_ref(v_inst_863_);
lean_dec_ref(v_inst_862_);
v___x_870_ = lean_box(0);
return v___x_870_;
}
else
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_862_, v_inst_863_, v_m_864_, v_a_865_);
return v___x_871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_872_, lean_object* v_inst_873_, lean_object* v_m_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Std_HashMap_Raw_getKey_x3f___redArg(v_inst_872_, v_inst_873_, v_m_874_, v_a_875_);
lean_dec_ref(v_m_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_877_, lean_object* v_00_u03b2_878_, lean_object* v_inst_879_, lean_object* v_inst_880_, lean_object* v_m_881_, lean_object* v_a_882_){
_start:
{
lean_object* v_buckets_883_; lean_object* v___x_884_; lean_object* v___x_885_; uint8_t v___x_886_; 
v_buckets_883_ = lean_ctor_get(v_m_881_, 1);
v___x_884_ = lean_unsigned_to_nat(0u);
v___x_885_ = lean_array_get_size(v_buckets_883_);
v___x_886_ = lean_nat_dec_lt(v___x_884_, v___x_885_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; 
lean_dec(v_a_882_);
lean_dec_ref(v_inst_880_);
lean_dec_ref(v_inst_879_);
v___x_887_ = lean_box(0);
return v___x_887_;
}
else
{
lean_object* v___x_888_; 
v___x_888_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_879_, v_inst_880_, v_m_881_, v_a_882_);
return v___x_888_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_889_, lean_object* v_00_u03b2_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_m_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Std_HashMap_Raw_getKey_x3f(v_00_u03b1_889_, v_00_u03b2_890_, v_inst_891_, v_inst_892_, v_m_893_, v_a_894_);
lean_dec_ref(v_m_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg(lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_m_898_, lean_object* v_a_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_896_, v_inst_897_, v_m_898_, v_a_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v_m_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_HashMap_Raw_getKey___redArg(v_inst_901_, v_inst_902_, v_m_903_, v_a_904_);
lean_dec_ref(v_m_903_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey(lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_inst_908_, lean_object* v_inst_909_, lean_object* v_m_910_, lean_object* v_a_911_, lean_object* v_h_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_908_, v_inst_909_, v_m_910_, v_a_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_914_, lean_object* v_00_u03b2_915_, lean_object* v_inst_916_, lean_object* v_inst_917_, lean_object* v_m_918_, lean_object* v_a_919_, lean_object* v_h_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_HashMap_Raw_getKey(v_00_u03b1_914_, v_00_u03b2_915_, v_inst_916_, v_inst_917_, v_m_918_, v_a_919_, v_h_920_);
lean_dec_ref(v_m_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg(lean_object* v_inst_922_, lean_object* v_inst_923_, lean_object* v_m_924_, lean_object* v_a_925_, lean_object* v_fallback_926_){
_start:
{
lean_object* v_buckets_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_buckets_927_ = lean_ctor_get(v_m_924_, 1);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_array_get_size(v_buckets_927_);
v___x_930_ = lean_nat_dec_lt(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_dec(v_a_925_);
lean_dec_ref(v_inst_923_);
lean_dec_ref(v_inst_922_);
lean_inc(v_fallback_926_);
return v_fallback_926_;
}
else
{
lean_object* v___x_931_; 
v___x_931_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_922_, v_inst_923_, v_m_924_, v_a_925_, v_fallback_926_);
return v___x_931_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_932_, lean_object* v_inst_933_, lean_object* v_m_934_, lean_object* v_a_935_, lean_object* v_fallback_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_HashMap_Raw_getKeyD___redArg(v_inst_932_, v_inst_933_, v_m_934_, v_a_935_, v_fallback_936_);
lean_dec(v_fallback_936_);
lean_dec_ref(v_m_934_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD(lean_object* v_00_u03b1_938_, lean_object* v_00_u03b2_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_m_942_, lean_object* v_a_943_, lean_object* v_fallback_944_){
_start:
{
lean_object* v_buckets_945_; lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_buckets_945_ = lean_ctor_get(v_m_942_, 1);
v___x_946_ = lean_unsigned_to_nat(0u);
v___x_947_ = lean_array_get_size(v_buckets_945_);
v___x_948_ = lean_nat_dec_lt(v___x_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_dec(v_a_943_);
lean_dec_ref(v_inst_941_);
lean_dec_ref(v_inst_940_);
lean_inc(v_fallback_944_);
return v_fallback_944_;
}
else
{
lean_object* v___x_949_; 
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_940_, v_inst_941_, v_m_942_, v_a_943_, v_fallback_944_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_950_, lean_object* v_00_u03b2_951_, lean_object* v_inst_952_, lean_object* v_inst_953_, lean_object* v_m_954_, lean_object* v_a_955_, lean_object* v_fallback_956_){
_start:
{
lean_object* v_res_957_; 
v_res_957_ = l_Std_HashMap_Raw_getKeyD(v_00_u03b1_950_, v_00_u03b2_951_, v_inst_952_, v_inst_953_, v_m_954_, v_a_955_, v_fallback_956_);
lean_dec(v_fallback_956_);
lean_dec_ref(v_m_954_);
return v_res_957_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg(lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_m_961_, lean_object* v_a_962_){
_start:
{
lean_object* v_buckets_963_; lean_object* v___x_964_; lean_object* v___x_965_; uint8_t v___x_966_; 
v_buckets_963_ = lean_ctor_get(v_m_961_, 1);
v___x_964_ = lean_unsigned_to_nat(0u);
v___x_965_ = lean_array_get_size(v_buckets_963_);
v___x_966_ = lean_nat_dec_lt(v___x_964_, v___x_965_);
if (v___x_966_ == 0)
{
lean_dec(v_a_962_);
lean_dec_ref(v_inst_959_);
lean_dec_ref(v_inst_958_);
return v_inst_960_;
}
else
{
lean_object* v___x_967_; 
v___x_967_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_958_, v_inst_959_, v_inst_960_, v_m_961_, v_a_962_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_inst_970_, lean_object* v_m_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_HashMap_Raw_getKey_x21___redArg(v_inst_968_, v_inst_969_, v_inst_970_, v_m_971_, v_a_972_);
lean_dec_ref(v_m_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21(lean_object* v_00_u03b1_974_, lean_object* v_00_u03b2_975_, lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v_m_979_, lean_object* v_a_980_){
_start:
{
lean_object* v_buckets_981_; lean_object* v___x_982_; lean_object* v___x_983_; uint8_t v___x_984_; 
v_buckets_981_ = lean_ctor_get(v_m_979_, 1);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = lean_array_get_size(v_buckets_981_);
v___x_984_ = lean_nat_dec_lt(v___x_982_, v___x_983_);
if (v___x_984_ == 0)
{
lean_dec(v_a_980_);
lean_dec_ref(v_inst_977_);
lean_dec_ref(v_inst_976_);
return v_inst_978_;
}
else
{
lean_object* v___x_985_; 
v___x_985_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_976_, v_inst_977_, v_inst_978_, v_m_979_, v_a_980_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_986_, lean_object* v_00_u03b2_987_, lean_object* v_inst_988_, lean_object* v_inst_989_, lean_object* v_inst_990_, lean_object* v_m_991_, lean_object* v_a_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_HashMap_Raw_getKey_x21(v_00_u03b1_986_, v_00_u03b2_987_, v_inst_988_, v_inst_989_, v_inst_990_, v_m_991_, v_a_992_);
lean_dec_ref(v_m_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase___redArg(lean_object* v_inst_994_, lean_object* v_inst_995_, lean_object* v_m_996_, lean_object* v_a_997_){
_start:
{
lean_object* v_buckets_998_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v_buckets_998_ = lean_ctor_get(v_m_996_, 1);
v___x_999_ = lean_unsigned_to_nat(0u);
v___x_1000_ = lean_array_get_size(v_buckets_998_);
v___x_1001_ = lean_nat_dec_lt(v___x_999_, v___x_1000_);
if (v___x_1001_ == 0)
{
lean_dec(v_a_997_);
lean_dec_ref(v_inst_995_);
lean_dec_ref(v_inst_994_);
return v_m_996_;
}
else
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_994_, v_inst_995_, v_m_996_, v_a_997_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase(lean_object* v_00_u03b1_1003_, lean_object* v_00_u03b2_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_m_1007_, lean_object* v_a_1008_){
_start:
{
lean_object* v_buckets_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v_buckets_1009_ = lean_ctor_get(v_m_1007_, 1);
v___x_1010_ = lean_unsigned_to_nat(0u);
v___x_1011_ = lean_array_get_size(v_buckets_1009_);
v___x_1012_ = lean_nat_dec_lt(v___x_1010_, v___x_1011_);
if (v___x_1012_ == 0)
{
lean_dec(v_a_1008_);
lean_dec_ref(v_inst_1006_);
lean_dec_ref(v_inst_1005_);
return v_m_1007_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1005_, v_inst_1006_, v_m_1007_, v_a_1008_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg(lean_object* v_m_1014_){
_start:
{
lean_object* v_size_1015_; 
v_size_1015_ = lean_ctor_get(v_m_1014_, 0);
lean_inc(v_size_1015_);
return v_size_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg___boxed(lean_object* v_m_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Std_HashMap_Raw_size___redArg(v_m_1016_);
lean_dec_ref(v_m_1016_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size(lean_object* v_00_u03b1_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_m_1020_){
_start:
{
lean_object* v_size_1021_; 
v_size_1021_ = lean_ctor_get(v_m_1020_, 0);
lean_inc(v_size_1021_);
return v_size_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_m_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Std_HashMap_Raw_size(v_00_u03b1_1022_, v_00_u03b2_1023_, v_m_1024_);
lean_dec_ref(v_m_1024_);
return v_res_1025_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty___redArg(lean_object* v_m_1026_){
_start:
{
lean_object* v_size_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_size_1027_ = lean_ctor_get(v_m_1026_, 0);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = lean_nat_dec_eq(v_size_1027_, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1030_){
_start:
{
uint8_t v_res_1031_; lean_object* v_r_1032_; 
v_res_1031_ = l_Std_HashMap_Raw_isEmpty___redArg(v_m_1030_);
lean_dec_ref(v_m_1030_);
v_r_1032_ = lean_box(v_res_1031_);
return v_r_1032_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty(lean_object* v_00_u03b1_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_m_1035_){
_start:
{
lean_object* v_size_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v_size_1036_ = lean_ctor_get(v_m_1035_, 0);
v___x_1037_ = lean_unsigned_to_nat(0u);
v___x_1038_ = lean_nat_dec_eq(v_size_1036_, v___x_1037_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_00_u03b2_1040_, lean_object* v_m_1041_){
_start:
{
uint8_t v_res_1042_; lean_object* v_r_1043_; 
v_res_1042_ = l_Std_HashMap_Raw_isEmpty(v_00_u03b1_1039_, v_00_u03b2_1040_, v_m_1041_);
lean_dec_ref(v_m_1041_);
v_r_1043_ = lean_box(v_res_1042_);
return v_r_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0(lean_object* v_a_1044_, lean_object* v_b_1045_, lean_object* v_d_1046_){
_start:
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1047_, 0, v_a_1044_);
lean_ctor_set(v___x_1047_, 1, v_d_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_a_1048_, lean_object* v_b_1049_, lean_object* v_d_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Std_HashMap_Raw_keys___redArg___lam__0(v_a_1048_, v_b_1049_, v_d_1050_);
lean_dec(v_b_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__1(lean_object* v___x_1052_, lean_object* v___f_1053_, lean_object* v_l_1054_, lean_object* v_acc_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1052_, v___f_1053_, v_acc_1055_, v_l_1054_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg(lean_object* v_m_1080_){
_start:
{
lean_object* v___x_1081_; lean_object* v_buckets_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; 
v___x_1081_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1082_ = lean_ctor_get(v_m_1080_, 1);
lean_inc_ref(v_buckets_1082_);
lean_dec_ref(v_m_1080_);
v___x_1083_ = lean_box(0);
v___x_1084_ = lean_array_get_size(v_buckets_1082_);
v___x_1085_ = lean_unsigned_to_nat(0u);
v___x_1086_ = lean_nat_dec_lt(v___x_1085_, v___x_1084_);
if (v___x_1086_ == 0)
{
lean_dec_ref(v_buckets_1082_);
return v___x_1083_;
}
else
{
lean_object* v___f_1087_; size_t v___x_1088_; size_t v___x_1089_; lean_object* v___x_1090_; 
v___f_1087_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1088_ = lean_usize_of_nat(v___x_1084_);
v___x_1089_ = ((size_t)0ULL);
v___x_1090_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1081_, v___f_1087_, v_buckets_1082_, v___x_1088_, v___x_1089_, v___x_1083_);
return v___x_1090_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys(lean_object* v_00_u03b1_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_m_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v_buckets_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1094_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1095_ = lean_ctor_get(v_m_1093_, 1);
lean_inc_ref(v_buckets_1095_);
lean_dec_ref(v_m_1093_);
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_array_get_size(v_buckets_1095_);
v___x_1098_ = lean_unsigned_to_nat(0u);
v___x_1099_ = lean_nat_dec_lt(v___x_1098_, v___x_1097_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v_buckets_1095_);
return v___x_1096_;
}
else
{
lean_object* v___f_1100_; size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; 
v___f_1100_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1101_ = lean_usize_of_nat(v___x_1097_);
v___x_1102_ = ((size_t)0ULL);
v___x_1103_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1094_, v___f_1100_, v_buckets_1095_, v___x_1101_, v___x_1102_, v___x_1096_);
return v___x_1103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList___redArg(lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_l_1110_){
_start:
{
lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1111_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1112_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1112_ == 0)
{
lean_dec(v_l_1110_);
lean_dec_ref(v_inst_1109_);
lean_dec_ref(v_inst_1108_);
return v___x_1111_;
}
else
{
lean_object* v___f_1113_; lean_object* v___x_1114_; 
v___f_1113_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1114_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1113_, v_inst_1108_, v_inst_1109_, v___x_1111_, v_l_1110_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList(lean_object* v_00_u03b1_1115_, lean_object* v_00_u03b2_1116_, lean_object* v_inst_1117_, lean_object* v_inst_1118_, lean_object* v_l_1119_){
_start:
{
lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1120_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1121_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1121_ == 0)
{
lean_dec(v_l_1119_);
lean_dec_ref(v_inst_1118_);
lean_dec_ref(v_inst_1117_);
return v___x_1120_;
}
else
{
lean_object* v___f_1122_; lean_object* v___x_1123_; 
v___f_1122_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1123_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1122_, v_inst_1117_, v_inst_1118_, v___x_1120_, v_l_1119_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList___redArg(lean_object* v_inst_1124_, lean_object* v_inst_1125_, lean_object* v_l_1126_){
_start:
{
lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1127_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1128_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1128_ == 0)
{
lean_dec(v_l_1126_);
lean_dec_ref(v_inst_1125_);
lean_dec_ref(v_inst_1124_);
return v___x_1127_;
}
else
{
lean_object* v___f_1129_; lean_object* v___x_1130_; 
v___f_1129_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1130_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1129_, v_inst_1124_, v_inst_1125_, v___x_1127_, v_l_1126_);
return v___x_1130_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList(lean_object* v_00_u03b1_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_, lean_object* v_l_1134_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray___redArg(lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1147_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1147_ == 0)
{
lean_dec_ref(v_a_1145_);
lean_dec_ref(v_inst_1144_);
lean_dec_ref(v_inst_1143_);
return v___x_1146_;
}
else
{
lean_object* v___f_1148_; lean_object* v___x_1149_; 
v___f_1148_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1149_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1148_, v_inst_1143_, v_inst_1144_, v___x_1146_, v_a_1145_);
return v___x_1149_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray(lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_a_1154_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1156_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1156_ == 0)
{
lean_dec_ref(v_a_1154_);
lean_dec_ref(v_inst_1153_);
lean_dec_ref(v_inst_1152_);
return v___x_1155_;
}
else
{
lean_object* v___f_1157_; lean_object* v___x_1158_; 
v___f_1157_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1157_, v_inst_1152_, v_inst_1153_, v___x_1155_, v_a_1154_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter___redArg(lean_object* v_inst_1159_, lean_object* v_inst_1160_, lean_object* v_m_1161_, lean_object* v_a_1162_, lean_object* v_f_1163_){
_start:
{
lean_object* v_buckets_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; uint8_t v___x_1167_; 
v_buckets_1164_ = lean_ctor_get(v_m_1161_, 1);
v___x_1165_ = lean_unsigned_to_nat(0u);
v___x_1166_ = lean_array_get_size(v_buckets_1164_);
v___x_1167_ = lean_nat_dec_lt(v___x_1165_, v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
lean_dec_ref(v_f_1163_);
lean_dec(v_a_1162_);
lean_dec_ref(v_m_1161_);
lean_dec_ref(v_inst_1160_);
lean_dec_ref(v_inst_1159_);
v___x_1168_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1168_;
}
else
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1159_, v_inst_1160_, v_m_1161_, v_a_1162_, v_f_1163_);
return v___x_1169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter(lean_object* v_00_u03b1_1170_, lean_object* v_00_u03b2_1171_, lean_object* v_inst_1172_, lean_object* v_inst_1173_, lean_object* v_inst_1174_, lean_object* v_m_1175_, lean_object* v_a_1176_, lean_object* v_f_1177_){
_start:
{
lean_object* v_buckets_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; uint8_t v___x_1181_; 
v_buckets_1178_ = lean_ctor_get(v_m_1175_, 1);
v___x_1179_ = lean_unsigned_to_nat(0u);
v___x_1180_ = lean_array_get_size(v_buckets_1178_);
v___x_1181_ = lean_nat_dec_lt(v___x_1179_, v___x_1180_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_dec_ref(v_f_1177_);
lean_dec(v_a_1176_);
lean_dec_ref(v_m_1175_);
lean_dec_ref(v_inst_1174_);
lean_dec_ref(v_inst_1172_);
v___x_1182_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1182_;
}
else
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1172_, v_inst_1174_, v_m_1175_, v_a_1176_, v_f_1177_);
return v___x_1183_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify___redArg(lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_m_1186_, lean_object* v_a_1187_, lean_object* v_f_1188_){
_start:
{
lean_object* v_buckets_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v_buckets_1189_ = lean_ctor_get(v_m_1186_, 1);
v___x_1190_ = lean_unsigned_to_nat(0u);
v___x_1191_ = lean_array_get_size(v_buckets_1189_);
v___x_1192_ = lean_nat_dec_lt(v___x_1190_, v___x_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; 
lean_dec(v_f_1188_);
lean_dec(v_a_1187_);
lean_dec_ref(v_m_1186_);
lean_dec_ref(v_inst_1185_);
lean_dec_ref(v_inst_1184_);
v___x_1193_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1193_;
}
else
{
lean_object* v___x_1194_; 
v___x_1194_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1184_, v_inst_1185_, v_m_1186_, v_a_1187_, v_f_1188_);
return v___x_1194_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify(lean_object* v_00_u03b1_1195_, lean_object* v_00_u03b2_1196_, lean_object* v_inst_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_m_1200_, lean_object* v_a_1201_, lean_object* v_f_1202_){
_start:
{
lean_object* v_buckets_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
v_buckets_1203_ = lean_ctor_get(v_m_1200_, 1);
v___x_1204_ = lean_unsigned_to_nat(0u);
v___x_1205_ = lean_array_get_size(v_buckets_1203_);
v___x_1206_ = lean_nat_dec_lt(v___x_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; 
lean_dec(v_f_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_m_1200_);
lean_dec_ref(v_inst_1199_);
lean_dec_ref(v_inst_1197_);
v___x_1207_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1207_;
}
else
{
lean_object* v___x_1208_; 
v___x_1208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1197_, v_inst_1199_, v_m_1200_, v_a_1201_, v_f_1202_);
return v___x_1208_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__0(lean_object* v_a_1209_, lean_object* v_b_1210_, lean_object* v_d_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v_a_1209_);
lean_ctor_set(v___x_1212_, 1, v_b_1210_);
v___x_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v_d_1211_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__1(lean_object* v___x_1214_, lean_object* v___f_1215_, lean_object* v_l_1216_, lean_object* v_acc_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1214_, v___f_1215_, v_acc_1217_, v_l_1216_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg(lean_object* v_m_1223_){
_start:
{
lean_object* v___x_1224_; lean_object* v_buckets_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; uint8_t v___x_1229_; 
v___x_1224_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1225_ = lean_ctor_get(v_m_1223_, 1);
lean_inc_ref(v_buckets_1225_);
lean_dec_ref(v_m_1223_);
v___x_1226_ = lean_box(0);
v___x_1227_ = lean_array_get_size(v_buckets_1225_);
v___x_1228_ = lean_unsigned_to_nat(0u);
v___x_1229_ = lean_nat_dec_lt(v___x_1228_, v___x_1227_);
if (v___x_1229_ == 0)
{
lean_dec_ref(v_buckets_1225_);
return v___x_1226_;
}
else
{
lean_object* v___f_1230_; size_t v___x_1231_; size_t v___x_1232_; lean_object* v___x_1233_; 
v___f_1230_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1231_ = lean_usize_of_nat(v___x_1227_);
v___x_1232_ = ((size_t)0ULL);
v___x_1233_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1224_, v___f_1230_, v_buckets_1225_, v___x_1231_, v___x_1232_, v___x_1226_);
return v___x_1233_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList(lean_object* v_00_u03b1_1234_, lean_object* v_00_u03b2_1235_, lean_object* v_m_1236_){
_start:
{
lean_object* v___x_1237_; lean_object* v_buckets_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; 
v___x_1237_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1238_ = lean_ctor_get(v_m_1236_, 1);
lean_inc_ref(v_buckets_1238_);
lean_dec_ref(v_m_1236_);
v___x_1239_ = lean_box(0);
v___x_1240_ = lean_array_get_size(v_buckets_1238_);
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = lean_nat_dec_lt(v___x_1241_, v___x_1240_);
if (v___x_1242_ == 0)
{
lean_dec_ref(v_buckets_1238_);
return v___x_1239_;
}
else
{
lean_object* v___f_1243_; size_t v___x_1244_; size_t v___x_1245_; lean_object* v___x_1246_; 
v___f_1243_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1244_ = lean_usize_of_nat(v___x_1240_);
v___x_1245_ = ((size_t)0ULL);
v___x_1246_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1237_, v___f_1243_, v_buckets_1238_, v___x_1244_, v___x_1245_, v___x_1239_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg___lam__0(lean_object* v_inst_1247_, lean_object* v_f_1248_, lean_object* v_acc_1249_, lean_object* v_l_1250_){
_start:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1247_, v_f_1248_, v_acc_1249_, v_l_1250_);
return v___x_1251_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg(lean_object* v_inst_1252_, lean_object* v_f_1253_, lean_object* v_init_1254_, lean_object* v_b_1255_){
_start:
{
lean_object* v_buckets_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; uint8_t v___x_1259_; 
v_buckets_1256_ = lean_ctor_get(v_b_1255_, 1);
lean_inc_ref(v_buckets_1256_);
lean_dec_ref(v_b_1255_);
v___x_1257_ = lean_unsigned_to_nat(0u);
v___x_1258_ = lean_array_get_size(v_buckets_1256_);
v___x_1259_ = lean_nat_dec_lt(v___x_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
lean_object* v_toApplicative_1260_; lean_object* v_toPure_1261_; lean_object* v___x_1262_; 
lean_dec_ref(v_buckets_1256_);
lean_dec(v_f_1253_);
v_toApplicative_1260_ = lean_ctor_get(v_inst_1252_, 0);
lean_inc_ref(v_toApplicative_1260_);
lean_dec_ref(v_inst_1252_);
v_toPure_1261_ = lean_ctor_get(v_toApplicative_1260_, 1);
lean_inc(v_toPure_1261_);
lean_dec_ref(v_toApplicative_1260_);
v___x_1262_ = lean_apply_2(v_toPure_1261_, lean_box(0), v_init_1254_);
return v___x_1262_;
}
else
{
lean_object* v___f_1263_; uint8_t v___x_1264_; 
lean_inc_ref(v_inst_1252_);
v___f_1263_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1263_, 0, v_inst_1252_);
lean_closure_set(v___f_1263_, 1, v_f_1253_);
v___x_1264_ = lean_nat_dec_le(v___x_1258_, v___x_1258_);
if (v___x_1264_ == 0)
{
if (v___x_1259_ == 0)
{
lean_object* v_toApplicative_1265_; lean_object* v_toPure_1266_; lean_object* v___x_1267_; 
lean_dec_ref(v___f_1263_);
lean_dec_ref(v_buckets_1256_);
v_toApplicative_1265_ = lean_ctor_get(v_inst_1252_, 0);
lean_inc_ref(v_toApplicative_1265_);
lean_dec_ref(v_inst_1252_);
v_toPure_1266_ = lean_ctor_get(v_toApplicative_1265_, 1);
lean_inc(v_toPure_1266_);
lean_dec_ref(v_toApplicative_1265_);
v___x_1267_ = lean_apply_2(v_toPure_1266_, lean_box(0), v_init_1254_);
return v___x_1267_;
}
else
{
size_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; 
v___x_1268_ = ((size_t)0ULL);
v___x_1269_ = lean_usize_of_nat(v___x_1258_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1252_, v___f_1263_, v_buckets_1256_, v___x_1268_, v___x_1269_, v_init_1254_);
return v___x_1270_;
}
}
else
{
size_t v___x_1271_; size_t v___x_1272_; lean_object* v___x_1273_; 
v___x_1271_ = ((size_t)0ULL);
v___x_1272_ = lean_usize_of_nat(v___x_1258_);
v___x_1273_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1252_, v___f_1263_, v_buckets_1256_, v___x_1271_, v___x_1272_, v_init_1254_);
return v___x_1273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_m_1276_, lean_object* v_inst_1277_, lean_object* v_00_u03b3_1278_, lean_object* v_f_1279_, lean_object* v_init_1280_, lean_object* v_b_1281_){
_start:
{
lean_object* v_buckets_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_buckets_1282_ = lean_ctor_get(v_b_1281_, 1);
lean_inc_ref(v_buckets_1282_);
lean_dec_ref(v_b_1281_);
v___x_1283_ = lean_unsigned_to_nat(0u);
v___x_1284_ = lean_array_get_size(v_buckets_1282_);
v___x_1285_ = lean_nat_dec_lt(v___x_1283_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v_toApplicative_1286_; lean_object* v_toPure_1287_; lean_object* v___x_1288_; 
lean_dec_ref(v_buckets_1282_);
lean_dec(v_f_1279_);
v_toApplicative_1286_ = lean_ctor_get(v_inst_1277_, 0);
lean_inc_ref(v_toApplicative_1286_);
lean_dec_ref(v_inst_1277_);
v_toPure_1287_ = lean_ctor_get(v_toApplicative_1286_, 1);
lean_inc(v_toPure_1287_);
lean_dec_ref(v_toApplicative_1286_);
v___x_1288_ = lean_apply_2(v_toPure_1287_, lean_box(0), v_init_1280_);
return v___x_1288_;
}
else
{
lean_object* v___f_1289_; uint8_t v___x_1290_; 
lean_inc_ref(v_inst_1277_);
v___f_1289_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1289_, 0, v_inst_1277_);
lean_closure_set(v___f_1289_, 1, v_f_1279_);
v___x_1290_ = lean_nat_dec_le(v___x_1284_, v___x_1284_);
if (v___x_1290_ == 0)
{
if (v___x_1285_ == 0)
{
lean_object* v_toApplicative_1291_; lean_object* v_toPure_1292_; lean_object* v___x_1293_; 
lean_dec_ref(v___f_1289_);
lean_dec_ref(v_buckets_1282_);
v_toApplicative_1291_ = lean_ctor_get(v_inst_1277_, 0);
lean_inc_ref(v_toApplicative_1291_);
lean_dec_ref(v_inst_1277_);
v_toPure_1292_ = lean_ctor_get(v_toApplicative_1291_, 1);
lean_inc(v_toPure_1292_);
lean_dec_ref(v_toApplicative_1291_);
v___x_1293_ = lean_apply_2(v_toPure_1292_, lean_box(0), v_init_1280_);
return v___x_1293_;
}
else
{
size_t v___x_1294_; size_t v___x_1295_; lean_object* v___x_1296_; 
v___x_1294_ = ((size_t)0ULL);
v___x_1295_ = lean_usize_of_nat(v___x_1284_);
v___x_1296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1277_, v___f_1289_, v_buckets_1282_, v___x_1294_, v___x_1295_, v_init_1280_);
return v___x_1296_;
}
}
else
{
size_t v___x_1297_; size_t v___x_1298_; lean_object* v___x_1299_; 
v___x_1297_ = ((size_t)0ULL);
v___x_1298_ = lean_usize_of_nat(v___x_1284_);
v___x_1299_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1277_, v___f_1289_, v_buckets_1282_, v___x_1297_, v___x_1298_, v_init_1280_);
return v___x_1299_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object* v_f_1300_, lean_object* v_x1_1301_, lean_object* v_x2_1302_, lean_object* v_x3_1303_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = lean_apply_3(v_f_1300_, v_x1_1301_, v_x2_1302_, v_x3_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__1(lean_object* v___x_1305_, lean_object* v___f_1306_, lean_object* v_acc_1307_, lean_object* v_l_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1305_, v___f_1306_, v_acc_1307_, v_l_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object* v_f_1310_, lean_object* v_init_1311_, lean_object* v_b_1312_){
_start:
{
lean_object* v___x_1313_; lean_object* v_buckets_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
v___x_1313_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1314_ = lean_ctor_get(v_b_1312_, 1);
lean_inc_ref(v_buckets_1314_);
lean_dec_ref(v_b_1312_);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_array_get_size(v_buckets_1314_);
v___x_1317_ = lean_nat_dec_lt(v___x_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_dec_ref(v_buckets_1314_);
lean_dec(v_f_1310_);
return v_init_1311_;
}
else
{
lean_object* v___f_1318_; lean_object* v___f_1319_; uint8_t v___x_1320_; 
v___f_1318_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1318_, 0, v_f_1310_);
v___f_1319_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1319_, 0, v___x_1313_);
lean_closure_set(v___f_1319_, 1, v___f_1318_);
v___x_1320_ = lean_nat_dec_le(v___x_1316_, v___x_1316_);
if (v___x_1320_ == 0)
{
if (v___x_1317_ == 0)
{
lean_dec_ref(v___f_1319_);
lean_dec_ref(v_buckets_1314_);
return v_init_1311_;
}
else
{
size_t v___x_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = lean_usize_of_nat(v___x_1316_);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1313_, v___f_1319_, v_buckets_1314_, v___x_1321_, v___x_1322_, v_init_1311_);
return v___x_1323_;
}
}
else
{
size_t v___x_1324_; size_t v___x_1325_; lean_object* v___x_1326_; 
v___x_1324_ = ((size_t)0ULL);
v___x_1325_ = lean_usize_of_nat(v___x_1316_);
v___x_1326_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1313_, v___f_1319_, v_buckets_1314_, v___x_1324_, v___x_1325_, v_init_1311_);
return v___x_1326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object* v_00_u03b1_1327_, lean_object* v_00_u03b2_1328_, lean_object* v_00_u03b3_1329_, lean_object* v_f_1330_, lean_object* v_init_1331_, lean_object* v_b_1332_){
_start:
{
lean_object* v___x_1333_; lean_object* v_buckets_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1333_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1334_ = lean_ctor_get(v_b_1332_, 1);
lean_inc_ref(v_buckets_1334_);
lean_dec_ref(v_b_1332_);
v___x_1335_ = lean_unsigned_to_nat(0u);
v___x_1336_ = lean_array_get_size(v_buckets_1334_);
v___x_1337_ = lean_nat_dec_lt(v___x_1335_, v___x_1336_);
if (v___x_1337_ == 0)
{
lean_dec_ref(v_buckets_1334_);
lean_dec(v_f_1330_);
return v_init_1331_;
}
else
{
lean_object* v___f_1338_; lean_object* v___f_1339_; uint8_t v___x_1340_; 
v___f_1338_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1338_, 0, v_f_1330_);
v___f_1339_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1339_, 0, v___x_1333_);
lean_closure_set(v___f_1339_, 1, v___f_1338_);
v___x_1340_ = lean_nat_dec_le(v___x_1336_, v___x_1336_);
if (v___x_1340_ == 0)
{
if (v___x_1337_ == 0)
{
lean_dec_ref(v___f_1339_);
lean_dec_ref(v_buckets_1334_);
return v_init_1331_;
}
else
{
size_t v___x_1341_; size_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = ((size_t)0ULL);
v___x_1342_ = lean_usize_of_nat(v___x_1336_);
v___x_1343_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1333_, v___f_1339_, v_buckets_1334_, v___x_1341_, v___x_1342_, v_init_1331_);
return v___x_1343_;
}
}
else
{
size_t v___x_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((size_t)0ULL);
v___x_1345_ = lean_usize_of_nat(v___x_1336_);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1333_, v___f_1339_, v_buckets_1334_, v___x_1344_, v___x_1345_, v_init_1331_);
return v___x_1346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object* v_f_1347_, lean_object* v_x_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = lean_apply_2(v_f_1347_, v___y_1349_, v___y_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__1(lean_object* v_inst_1352_, lean_object* v___f_1353_, lean_object* v_x_1354_, lean_object* v___y_1355_){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = lean_box(0);
v___x_1357_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1352_, v___f_1353_, v___x_1356_, v___y_1355_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object* v_inst_1358_, lean_object* v_f_1359_, lean_object* v_b_1360_){
_start:
{
lean_object* v_buckets_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; uint8_t v___x_1365_; 
v_buckets_1361_ = lean_ctor_get(v_b_1360_, 1);
lean_inc_ref(v_buckets_1361_);
lean_dec_ref(v_b_1360_);
v___x_1362_ = lean_unsigned_to_nat(0u);
v___x_1363_ = lean_array_get_size(v_buckets_1361_);
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_nat_dec_lt(v___x_1362_, v___x_1363_);
if (v___x_1365_ == 0)
{
lean_object* v_toApplicative_1366_; lean_object* v_toPure_1367_; lean_object* v___x_1368_; 
lean_dec_ref(v_buckets_1361_);
lean_dec(v_f_1359_);
v_toApplicative_1366_ = lean_ctor_get(v_inst_1358_, 0);
lean_inc_ref(v_toApplicative_1366_);
lean_dec_ref(v_inst_1358_);
v_toPure_1367_ = lean_ctor_get(v_toApplicative_1366_, 1);
lean_inc(v_toPure_1367_);
lean_dec_ref(v_toApplicative_1366_);
v___x_1368_ = lean_apply_2(v_toPure_1367_, lean_box(0), v___x_1364_);
return v___x_1368_;
}
else
{
lean_object* v___f_1369_; lean_object* v___f_1370_; uint8_t v___x_1371_; 
v___f_1369_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1369_, 0, v_f_1359_);
lean_inc_ref(v_inst_1358_);
v___f_1370_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1370_, 0, v_inst_1358_);
lean_closure_set(v___f_1370_, 1, v___f_1369_);
v___x_1371_ = lean_nat_dec_le(v___x_1363_, v___x_1363_);
if (v___x_1371_ == 0)
{
if (v___x_1365_ == 0)
{
lean_object* v_toApplicative_1372_; lean_object* v_toPure_1373_; lean_object* v___x_1374_; 
lean_dec_ref(v___f_1370_);
lean_dec_ref(v_buckets_1361_);
v_toApplicative_1372_ = lean_ctor_get(v_inst_1358_, 0);
lean_inc_ref(v_toApplicative_1372_);
lean_dec_ref(v_inst_1358_);
v_toPure_1373_ = lean_ctor_get(v_toApplicative_1372_, 1);
lean_inc(v_toPure_1373_);
lean_dec_ref(v_toApplicative_1372_);
v___x_1374_ = lean_apply_2(v_toPure_1373_, lean_box(0), v___x_1364_);
return v___x_1374_;
}
else
{
size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
v___x_1375_ = ((size_t)0ULL);
v___x_1376_ = lean_usize_of_nat(v___x_1363_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1358_, v___f_1370_, v_buckets_1361_, v___x_1375_, v___x_1376_, v___x_1364_);
return v___x_1377_;
}
}
else
{
size_t v___x_1378_; size_t v___x_1379_; lean_object* v___x_1380_; 
v___x_1378_ = ((size_t)0ULL);
v___x_1379_ = lean_usize_of_nat(v___x_1363_);
v___x_1380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1358_, v___f_1370_, v_buckets_1361_, v___x_1378_, v___x_1379_, v___x_1364_);
return v___x_1380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object* v_00_u03b1_1381_, lean_object* v_00_u03b2_1382_, lean_object* v_m_1383_, lean_object* v_inst_1384_, lean_object* v_f_1385_, lean_object* v_b_1386_){
_start:
{
lean_object* v_buckets_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; 
v_buckets_1387_ = lean_ctor_get(v_b_1386_, 1);
lean_inc_ref(v_buckets_1387_);
lean_dec_ref(v_b_1386_);
v___x_1388_ = lean_unsigned_to_nat(0u);
v___x_1389_ = lean_array_get_size(v_buckets_1387_);
v___x_1390_ = lean_box(0);
v___x_1391_ = lean_nat_dec_lt(v___x_1388_, v___x_1389_);
if (v___x_1391_ == 0)
{
lean_object* v_toApplicative_1392_; lean_object* v_toPure_1393_; lean_object* v___x_1394_; 
lean_dec_ref(v_buckets_1387_);
lean_dec(v_f_1385_);
v_toApplicative_1392_ = lean_ctor_get(v_inst_1384_, 0);
lean_inc_ref(v_toApplicative_1392_);
lean_dec_ref(v_inst_1384_);
v_toPure_1393_ = lean_ctor_get(v_toApplicative_1392_, 1);
lean_inc(v_toPure_1393_);
lean_dec_ref(v_toApplicative_1392_);
v___x_1394_ = lean_apply_2(v_toPure_1393_, lean_box(0), v___x_1390_);
return v___x_1394_;
}
else
{
lean_object* v___f_1395_; lean_object* v___f_1396_; uint8_t v___x_1397_; 
v___f_1395_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1395_, 0, v_f_1385_);
lean_inc_ref(v_inst_1384_);
v___f_1396_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1396_, 0, v_inst_1384_);
lean_closure_set(v___f_1396_, 1, v___f_1395_);
v___x_1397_ = lean_nat_dec_le(v___x_1389_, v___x_1389_);
if (v___x_1397_ == 0)
{
if (v___x_1391_ == 0)
{
lean_object* v_toApplicative_1398_; lean_object* v_toPure_1399_; lean_object* v___x_1400_; 
lean_dec_ref(v___f_1396_);
lean_dec_ref(v_buckets_1387_);
v_toApplicative_1398_ = lean_ctor_get(v_inst_1384_, 0);
lean_inc_ref(v_toApplicative_1398_);
lean_dec_ref(v_inst_1384_);
v_toPure_1399_ = lean_ctor_get(v_toApplicative_1398_, 1);
lean_inc(v_toPure_1399_);
lean_dec_ref(v_toApplicative_1398_);
v___x_1400_ = lean_apply_2(v_toPure_1399_, lean_box(0), v___x_1390_);
return v___x_1400_;
}
else
{
size_t v___x_1401_; size_t v___x_1402_; lean_object* v___x_1403_; 
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = lean_usize_of_nat(v___x_1389_);
v___x_1403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1384_, v___f_1396_, v_buckets_1387_, v___x_1401_, v___x_1402_, v___x_1390_);
return v___x_1403_;
}
}
else
{
size_t v___x_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = ((size_t)0ULL);
v___x_1405_ = lean_usize_of_nat(v___x_1389_);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1384_, v___f_1396_, v_buckets_1387_, v___x_1404_, v___x_1405_, v___x_1390_);
return v___x_1406_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg___lam__0(lean_object* v_inst_1407_, lean_object* v_f_1408_, lean_object* v_a_1409_, lean_object* v_x_1410_, lean_object* v___y_1411_){
_start:
{
lean_object* v___x_1412_; 
v___x_1412_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1407_, v_f_1408_, v_a_1409_, v___y_1411_);
return v___x_1412_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object* v_inst_1413_, lean_object* v_f_1414_, lean_object* v_init_1415_, lean_object* v_b_1416_){
_start:
{
lean_object* v_buckets_1417_; lean_object* v___f_1418_; size_t v_sz_1419_; size_t v___x_1420_; lean_object* v___x_1421_; 
v_buckets_1417_ = lean_ctor_get(v_b_1416_, 1);
lean_inc_ref(v_buckets_1417_);
lean_dec_ref(v_b_1416_);
lean_inc_ref(v_inst_1413_);
v___f_1418_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1418_, 0, v_inst_1413_);
lean_closure_set(v___f_1418_, 1, v_f_1414_);
v_sz_1419_ = lean_array_size(v_buckets_1417_);
v___x_1420_ = ((size_t)0ULL);
v___x_1421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1413_, v_buckets_1417_, v___f_1418_, v_sz_1419_, v___x_1420_, v_init_1415_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object* v_00_u03b1_1422_, lean_object* v_00_u03b2_1423_, lean_object* v_m_1424_, lean_object* v_inst_1425_, lean_object* v_00_u03b3_1426_, lean_object* v_f_1427_, lean_object* v_init_1428_, lean_object* v_b_1429_){
_start:
{
lean_object* v_buckets_1430_; lean_object* v___f_1431_; size_t v_sz_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
v_buckets_1430_ = lean_ctor_get(v_b_1429_, 1);
lean_inc_ref(v_buckets_1430_);
lean_dec_ref(v_b_1429_);
lean_inc_ref(v_inst_1425_);
v___f_1431_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1431_, 0, v_inst_1425_);
lean_closure_set(v___f_1431_, 1, v_f_1427_);
v_sz_1432_ = lean_array_size(v_buckets_1430_);
v___x_1433_ = ((size_t)0ULL);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1425_, v_buckets_1430_, v___f_1431_, v_sz_1432_, v___x_1433_, v_init_1428_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1435_, lean_object* v_x_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___y_1437_);
lean_ctor_set(v___x_1439_, 1, v___y_1438_);
v___x_1440_ = lean_apply_1(v_f_1435_, v___x_1439_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1441_, lean_object* v_m_1442_, lean_object* v_f_1443_){
_start:
{
lean_object* v_buckets_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; uint8_t v___x_1448_; 
v_buckets_1444_ = lean_ctor_get(v_m_1442_, 1);
lean_inc_ref(v_buckets_1444_);
lean_dec_ref(v_m_1442_);
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = lean_array_get_size(v_buckets_1444_);
v___x_1447_ = lean_box(0);
v___x_1448_ = lean_nat_dec_lt(v___x_1445_, v___x_1446_);
if (v___x_1448_ == 0)
{
lean_object* v_toApplicative_1449_; lean_object* v_toPure_1450_; lean_object* v___x_1451_; 
lean_dec_ref(v_buckets_1444_);
lean_dec(v_f_1443_);
v_toApplicative_1449_ = lean_ctor_get(v_inst_1441_, 0);
lean_inc_ref(v_toApplicative_1449_);
lean_dec_ref(v_inst_1441_);
v_toPure_1450_ = lean_ctor_get(v_toApplicative_1449_, 1);
lean_inc(v_toPure_1450_);
lean_dec_ref(v_toApplicative_1449_);
v___x_1451_ = lean_apply_2(v_toPure_1450_, lean_box(0), v___x_1447_);
return v___x_1451_;
}
else
{
lean_object* v___f_1452_; lean_object* v___f_1453_; uint8_t v___x_1454_; 
v___f_1452_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1452_, 0, v_f_1443_);
lean_inc_ref(v_inst_1441_);
v___f_1453_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1453_, 0, v_inst_1441_);
lean_closure_set(v___f_1453_, 1, v___f_1452_);
v___x_1454_ = lean_nat_dec_le(v___x_1446_, v___x_1446_);
if (v___x_1454_ == 0)
{
if (v___x_1448_ == 0)
{
lean_object* v_toApplicative_1455_; lean_object* v_toPure_1456_; lean_object* v___x_1457_; 
lean_dec_ref(v___f_1453_);
lean_dec_ref(v_buckets_1444_);
v_toApplicative_1455_ = lean_ctor_get(v_inst_1441_, 0);
lean_inc_ref(v_toApplicative_1455_);
lean_dec_ref(v_inst_1441_);
v_toPure_1456_ = lean_ctor_get(v_toApplicative_1455_, 1);
lean_inc(v_toPure_1456_);
lean_dec_ref(v_toApplicative_1455_);
v___x_1457_ = lean_apply_2(v_toPure_1456_, lean_box(0), v___x_1447_);
return v___x_1457_;
}
else
{
size_t v___x_1458_; size_t v___x_1459_; lean_object* v___x_1460_; 
v___x_1458_ = ((size_t)0ULL);
v___x_1459_ = lean_usize_of_nat(v___x_1446_);
v___x_1460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1441_, v___f_1453_, v_buckets_1444_, v___x_1458_, v___x_1459_, v___x_1447_);
return v___x_1460_;
}
}
else
{
size_t v___x_1461_; size_t v___x_1462_; lean_object* v___x_1463_; 
v___x_1461_ = ((size_t)0ULL);
v___x_1462_ = lean_usize_of_nat(v___x_1446_);
v___x_1463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1441_, v___f_1453_, v_buckets_1444_, v___x_1461_, v___x_1462_, v___x_1447_);
return v___x_1463_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1464_){
_start:
{
lean_object* v___f_1465_; 
v___f_1465_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1465_, 0, v_inst_1464_);
return v___f_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1466_, lean_object* v_00_u03b2_1467_, lean_object* v_m_1468_, lean_object* v_inst_1469_){
_start:
{
lean_object* v___f_1470_; 
v___f_1470_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1470_, 0, v_inst_1469_);
return v___f_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1471_, lean_object* v_a_1472_, lean_object* v_b_1473_, lean_object* v_acc_1474_){
_start:
{
lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v_a_1472_);
lean_ctor_set(v___x_1475_, 1, v_b_1473_);
v___x_1476_ = lean_apply_2(v_f_1471_, v___x_1475_, v_acc_1474_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1477_, lean_object* v___f_1478_, lean_object* v_a_1479_, lean_object* v_x_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1477_, v___f_1478_, v_a_1479_, v___y_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1483_, lean_object* v_00_u03b2_1484_, lean_object* v_m_1485_, lean_object* v_init_1486_, lean_object* v_f_1487_){
_start:
{
lean_object* v_buckets_1488_; lean_object* v___f_1489_; lean_object* v___f_1490_; size_t v_sz_1491_; size_t v___x_1492_; lean_object* v___x_1493_; 
v_buckets_1488_ = lean_ctor_get(v_m_1485_, 1);
lean_inc_ref(v_buckets_1488_);
lean_dec_ref(v_m_1485_);
v___f_1489_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1489_, 0, v_f_1487_);
lean_inc_ref(v_inst_1483_);
v___f_1490_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1490_, 0, v_inst_1483_);
lean_closure_set(v___f_1490_, 1, v___f_1489_);
v_sz_1491_ = lean_array_size(v_buckets_1488_);
v___x_1492_ = ((size_t)0ULL);
v___x_1493_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1483_, v_buckets_1488_, v___f_1490_, v_sz_1491_, v___x_1492_, v_init_1486_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1494_){
_start:
{
lean_object* v___f_1495_; 
v___f_1495_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1495_, 0, v_inst_1494_);
return v___f_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1496_, lean_object* v_00_u03b2_1497_, lean_object* v_m_1498_, lean_object* v_inst_1499_){
_start:
{
lean_object* v___f_1500_; 
v___f_1500_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1500_, 0, v_inst_1499_);
return v___f_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object* v_p_1501_, lean_object* v___x_1502_, lean_object* v___x_1503_, lean_object* v_a_1504_, lean_object* v_b_1505_, lean_object* v_acc_1506_){
_start:
{
lean_object* v___x_1507_; uint8_t v___x_1508_; 
v___x_1507_ = lean_apply_2(v_p_1501_, v_a_1504_, v_b_1505_);
v___x_1508_ = lean_unbox(v___x_1507_);
if (v___x_1508_ == 0)
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec_ref(v___x_1503_);
v___x_1509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1507_);
v___x_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1502_);
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
return v___x_1511_;
}
else
{
lean_object* v___x_1512_; 
v___x_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1503_);
return v___x_1512_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1513_, lean_object* v___x_1514_, lean_object* v___x_1515_, lean_object* v_a_1516_, lean_object* v_b_1517_, lean_object* v_acc_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_Std_HashMap_Raw_all___redArg___lam__0(v_p_1513_, v___x_1514_, v___x_1515_, v_a_1516_, v_b_1517_, v_acc_1518_);
lean_dec_ref(v_acc_1518_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__1(lean_object* v___x_1520_, lean_object* v___f_1521_, lean_object* v_a_1522_, lean_object* v_x_1523_, lean_object* v___y_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1520_, v___f_1521_, v_a_1522_, v___y_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all___redArg(lean_object* v_m_1529_, lean_object* v_p_1530_){
_start:
{
lean_object* v___x_1531_; lean_object* v_buckets_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___f_1535_; lean_object* v___f_1536_; size_t v_sz_1537_; size_t v___x_1538_; lean_object* v___x_1539_; lean_object* v_fst_1540_; 
v___x_1531_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1532_ = lean_ctor_get(v_m_1529_, 1);
lean_inc_ref(v_buckets_1532_);
lean_dec_ref(v_m_1529_);
v___x_1533_ = lean_box(0);
v___x_1534_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1535_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1535_, 0, v_p_1530_);
lean_closure_set(v___f_1535_, 1, v___x_1533_);
lean_closure_set(v___f_1535_, 2, v___x_1534_);
v___f_1536_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1536_, 0, v___x_1531_);
lean_closure_set(v___f_1536_, 1, v___f_1535_);
v_sz_1537_ = lean_array_size(v_buckets_1532_);
v___x_1538_ = ((size_t)0ULL);
v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1531_, v_buckets_1532_, v___f_1536_, v_sz_1537_, v___x_1538_, v___x_1534_);
v_fst_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_fst_1540_);
lean_dec(v___x_1539_);
if (lean_obj_tag(v_fst_1540_) == 0)
{
uint8_t v___x_1541_; 
v___x_1541_ = 1;
return v___x_1541_;
}
else
{
lean_object* v_val_1542_; uint8_t v___x_1543_; 
v_val_1542_ = lean_ctor_get(v_fst_1540_, 0);
lean_inc(v_val_1542_);
lean_dec_ref(v_fst_1540_);
v___x_1543_ = lean_unbox(v_val_1542_);
lean_dec(v_val_1542_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___boxed(lean_object* v_m_1544_, lean_object* v_p_1545_){
_start:
{
uint8_t v_res_1546_; lean_object* v_r_1547_; 
v_res_1546_ = l_Std_HashMap_Raw_all___redArg(v_m_1544_, v_p_1545_);
v_r_1547_ = lean_box(v_res_1546_);
return v_r_1547_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all(lean_object* v_00_u03b1_1548_, lean_object* v_00_u03b2_1549_, lean_object* v_m_1550_, lean_object* v_p_1551_){
_start:
{
lean_object* v___x_1552_; lean_object* v_buckets_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___f_1556_; lean_object* v___f_1557_; size_t v_sz_1558_; size_t v___x_1559_; lean_object* v___x_1560_; lean_object* v_fst_1561_; 
v___x_1552_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1553_ = lean_ctor_get(v_m_1550_, 1);
lean_inc_ref(v_buckets_1553_);
lean_dec_ref(v_m_1550_);
v___x_1554_ = lean_box(0);
v___x_1555_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1556_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1556_, 0, v_p_1551_);
lean_closure_set(v___f_1556_, 1, v___x_1554_);
lean_closure_set(v___f_1556_, 2, v___x_1555_);
v___f_1557_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1557_, 0, v___x_1552_);
lean_closure_set(v___f_1557_, 1, v___f_1556_);
v_sz_1558_ = lean_array_size(v_buckets_1553_);
v___x_1559_ = ((size_t)0ULL);
v___x_1560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1552_, v_buckets_1553_, v___f_1557_, v_sz_1558_, v___x_1559_, v___x_1555_);
v_fst_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc(v_fst_1561_);
lean_dec(v___x_1560_);
if (lean_obj_tag(v_fst_1561_) == 0)
{
uint8_t v___x_1562_; 
v___x_1562_ = 1;
return v___x_1562_;
}
else
{
lean_object* v_val_1563_; uint8_t v___x_1564_; 
v_val_1563_ = lean_ctor_get(v_fst_1561_, 0);
lean_inc(v_val_1563_);
lean_dec_ref(v_fst_1561_);
v___x_1564_ = lean_unbox(v_val_1563_);
lean_dec(v_val_1563_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___boxed(lean_object* v_00_u03b1_1565_, lean_object* v_00_u03b2_1566_, lean_object* v_m_1567_, lean_object* v_p_1568_){
_start:
{
uint8_t v_res_1569_; lean_object* v_r_1570_; 
v_res_1569_ = l_Std_HashMap_Raw_all(v_00_u03b1_1565_, v_00_u03b2_1566_, v_m_1567_, v_p_1568_);
v_r_1570_ = lean_box(v_res_1569_);
return v_r_1570_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0(lean_object* v_p_1571_, lean_object* v___x_1572_, lean_object* v___x_1573_, lean_object* v_a_1574_, lean_object* v_b_1575_, lean_object* v_acc_1576_){
_start:
{
lean_object* v___x_1577_; uint8_t v___x_1578_; 
v___x_1577_ = lean_apply_2(v_p_1571_, v_a_1574_, v_b_1575_);
v___x_1578_ = lean_unbox(v___x_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; 
v___x_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1572_);
return v___x_1579_;
}
else
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
lean_dec_ref(v___x_1572_);
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1577_);
v___x_1581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1581_, 0, v___x_1580_);
lean_ctor_set(v___x_1581_, 1, v___x_1573_);
v___x_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1582_, 0, v___x_1581_);
return v___x_1582_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1583_, lean_object* v___x_1584_, lean_object* v___x_1585_, lean_object* v_a_1586_, lean_object* v_b_1587_, lean_object* v_acc_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Std_HashMap_Raw_any___redArg___lam__0(v_p_1583_, v___x_1584_, v___x_1585_, v_a_1586_, v_b_1587_, v_acc_1588_);
lean_dec_ref(v_acc_1588_);
return v_res_1589_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any___redArg(lean_object* v_m_1590_, lean_object* v_p_1591_){
_start:
{
lean_object* v___x_1592_; lean_object* v_buckets_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___f_1596_; lean_object* v___f_1597_; size_t v_sz_1598_; size_t v___x_1599_; lean_object* v___x_1600_; lean_object* v_fst_1601_; 
v___x_1592_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1593_ = lean_ctor_get(v_m_1590_, 1);
lean_inc_ref(v_buckets_1593_);
lean_dec_ref(v_m_1590_);
v___x_1594_ = lean_box(0);
v___x_1595_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1596_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1596_, 0, v_p_1591_);
lean_closure_set(v___f_1596_, 1, v___x_1595_);
lean_closure_set(v___f_1596_, 2, v___x_1594_);
v___f_1597_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1597_, 0, v___x_1592_);
lean_closure_set(v___f_1597_, 1, v___f_1596_);
v_sz_1598_ = lean_array_size(v_buckets_1593_);
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1592_, v_buckets_1593_, v___f_1597_, v_sz_1598_, v___x_1599_, v___x_1595_);
v_fst_1601_ = lean_ctor_get(v___x_1600_, 0);
lean_inc(v_fst_1601_);
lean_dec(v___x_1600_);
if (lean_obj_tag(v_fst_1601_) == 0)
{
uint8_t v___x_1602_; 
v___x_1602_ = 0;
return v___x_1602_;
}
else
{
lean_object* v_val_1603_; uint8_t v___x_1604_; 
v_val_1603_ = lean_ctor_get(v_fst_1601_, 0);
lean_inc(v_val_1603_);
lean_dec_ref(v_fst_1601_);
v___x_1604_ = lean_unbox(v_val_1603_);
lean_dec(v_val_1603_);
return v___x_1604_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___boxed(lean_object* v_m_1605_, lean_object* v_p_1606_){
_start:
{
uint8_t v_res_1607_; lean_object* v_r_1608_; 
v_res_1607_ = l_Std_HashMap_Raw_any___redArg(v_m_1605_, v_p_1606_);
v_r_1608_ = lean_box(v_res_1607_);
return v_r_1608_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any(lean_object* v_00_u03b1_1609_, lean_object* v_00_u03b2_1610_, lean_object* v_m_1611_, lean_object* v_p_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v_buckets_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___f_1617_; lean_object* v___f_1618_; size_t v_sz_1619_; size_t v___x_1620_; lean_object* v___x_1621_; lean_object* v_fst_1622_; 
v___x_1613_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1614_ = lean_ctor_get(v_m_1611_, 1);
lean_inc_ref(v_buckets_1614_);
lean_dec_ref(v_m_1611_);
v___x_1615_ = lean_box(0);
v___x_1616_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1617_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1617_, 0, v_p_1612_);
lean_closure_set(v___f_1617_, 1, v___x_1616_);
lean_closure_set(v___f_1617_, 2, v___x_1615_);
v___f_1618_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1618_, 0, v___x_1613_);
lean_closure_set(v___f_1618_, 1, v___f_1617_);
v_sz_1619_ = lean_array_size(v_buckets_1614_);
v___x_1620_ = ((size_t)0ULL);
v___x_1621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1613_, v_buckets_1614_, v___f_1618_, v_sz_1619_, v___x_1620_, v___x_1616_);
v_fst_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_fst_1622_);
lean_dec(v___x_1621_);
if (lean_obj_tag(v_fst_1622_) == 0)
{
uint8_t v___x_1623_; 
v___x_1623_ = 0;
return v___x_1623_;
}
else
{
lean_object* v_val_1624_; uint8_t v___x_1625_; 
v_val_1624_ = lean_ctor_get(v_fst_1622_, 0);
lean_inc(v_val_1624_);
lean_dec_ref(v_fst_1622_);
v___x_1625_ = lean_unbox(v_val_1624_);
lean_dec(v_val_1624_);
return v___x_1625_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___boxed(lean_object* v_00_u03b1_1626_, lean_object* v_00_u03b2_1627_, lean_object* v_m_1628_, lean_object* v_p_1629_){
_start:
{
uint8_t v_res_1630_; lean_object* v_r_1631_; 
v_res_1630_ = l_Std_HashMap_Raw_any(v_00_u03b1_1626_, v_00_u03b2_1627_, v_m_1628_, v_p_1629_);
v_r_1631_ = lean_box(v_res_1630_);
return v_r_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_a_1634_, lean_object* v_b_1635_, lean_object* v_acc_1636_){
_start:
{
lean_object* v_r_1637_; lean_object* v___x_1638_; 
v_r_1637_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1632_, v_inst_1633_, v_acc_1636_, v_a_1634_, v_b_1635_);
v___x_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1638_, 0, v_r_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__1(lean_object* v___x_1639_, lean_object* v___f_1640_, lean_object* v_a_1641_, lean_object* v_x_1642_, lean_object* v___y_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1639_, v___f_1640_, v_a_1641_, v___y_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg(lean_object* v_inst_1647_, lean_object* v_inst_1648_, lean_object* v_m_u2081_1649_, lean_object* v_m_u2082_1650_){
_start:
{
lean_object* v_size_1651_; lean_object* v_buckets_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v_size_1651_ = lean_ctor_get(v_m_u2081_1649_, 0);
v_buckets_1652_ = lean_ctor_get(v_m_u2081_1649_, 1);
v___x_1653_ = lean_unsigned_to_nat(0u);
v___x_1654_ = lean_array_get_size(v_buckets_1652_);
v___x_1655_ = lean_nat_dec_lt(v___x_1653_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_dec_ref(v_m_u2081_1649_);
lean_dec_ref(v_inst_1648_);
lean_dec_ref(v_inst_1647_);
return v_m_u2082_1650_;
}
else
{
lean_object* v_size_1656_; lean_object* v_buckets_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_size_1656_ = lean_ctor_get(v_m_u2082_1650_, 0);
v_buckets_1657_ = lean_ctor_get(v_m_u2082_1650_, 1);
v___x_1658_ = lean_array_get_size(v_buckets_1657_);
v___x_1659_ = lean_nat_dec_lt(v___x_1653_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_dec_ref(v_m_u2082_1650_);
lean_dec_ref(v_inst_1648_);
lean_dec_ref(v_inst_1647_);
return v_m_u2081_1649_;
}
else
{
uint8_t v___x_1660_; 
v___x_1660_ = lean_nat_dec_le(v_size_1651_, v_size_1656_);
if (v___x_1660_ == 0)
{
lean_object* v___f_1661_; lean_object* v___x_1662_; 
v___f_1661_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1662_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1661_, v_inst_1647_, v_inst_1648_, v_m_u2081_1649_, v_m_u2082_1650_);
return v___x_1662_;
}
else
{
lean_object* v___f_1663_; lean_object* v___x_1664_; lean_object* v___f_1665_; size_t v_sz_1666_; size_t v___x_1667_; lean_object* v___x_1668_; 
lean_inc_ref(v_buckets_1652_);
lean_dec_ref(v_m_u2081_1649_);
v___f_1663_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1663_, 0, v_inst_1647_);
lean_closure_set(v___f_1663_, 1, v_inst_1648_);
v___x_1664_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___f_1665_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1665_, 0, v___x_1664_);
lean_closure_set(v___f_1665_, 1, v___f_1663_);
v_sz_1666_ = lean_array_size(v_buckets_1652_);
v___x_1667_ = ((size_t)0ULL);
v___x_1668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1664_, v_buckets_1652_, v___f_1665_, v_sz_1666_, v___x_1667_, v_m_u2082_1650_);
return v___x_1668_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union(lean_object* v_00_u03b1_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_m_u2081_1673_, lean_object* v_m_u2082_1674_){
_start:
{
lean_object* v_size_1675_; lean_object* v_buckets_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; uint8_t v___x_1679_; 
v_size_1675_ = lean_ctor_get(v_m_u2081_1673_, 0);
v_buckets_1676_ = lean_ctor_get(v_m_u2081_1673_, 1);
v___x_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = lean_array_get_size(v_buckets_1676_);
v___x_1679_ = lean_nat_dec_lt(v___x_1677_, v___x_1678_);
if (v___x_1679_ == 0)
{
lean_dec_ref(v_m_u2081_1673_);
lean_dec_ref(v_inst_1672_);
lean_dec_ref(v_inst_1671_);
return v_m_u2082_1674_;
}
else
{
lean_object* v_size_1680_; lean_object* v_buckets_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_size_1680_ = lean_ctor_get(v_m_u2082_1674_, 0);
v_buckets_1681_ = lean_ctor_get(v_m_u2082_1674_, 1);
v___x_1682_ = lean_array_get_size(v_buckets_1681_);
v___x_1683_ = lean_nat_dec_lt(v___x_1677_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_dec_ref(v_m_u2082_1674_);
lean_dec_ref(v_inst_1672_);
lean_dec_ref(v_inst_1671_);
return v_m_u2081_1673_;
}
else
{
uint8_t v___x_1684_; 
v___x_1684_ = lean_nat_dec_le(v_size_1675_, v_size_1680_);
if (v___x_1684_ == 0)
{
lean_object* v___f_1685_; lean_object* v___x_1686_; 
v___f_1685_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1685_, v_inst_1671_, v_inst_1672_, v_m_u2081_1673_, v_m_u2082_1674_);
return v___x_1686_;
}
else
{
lean_object* v___f_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; size_t v_sz_1690_; size_t v___x_1691_; lean_object* v___x_1692_; 
lean_inc_ref(v_buckets_1676_);
lean_dec_ref(v_m_u2081_1673_);
v___f_1687_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1687_, 0, v_inst_1671_);
lean_closure_set(v___f_1687_, 1, v_inst_1672_);
v___x_1688_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___f_1689_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1689_, 0, v___x_1688_);
lean_closure_set(v___f_1689_, 1, v___f_1687_);
v_sz_1690_ = lean_array_size(v_buckets_1676_);
v___x_1691_ = ((size_t)0ULL);
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1688_, v_buckets_1676_, v___f_1689_, v_sz_1690_, v___x_1691_, v_m_u2082_1674_);
return v___x_1692_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter___redArg(lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_m_u2081_1695_, lean_object* v_m_u2082_1696_){
_start:
{
lean_object* v_buckets_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v_buckets_1697_ = lean_ctor_get(v_m_u2081_1695_, 1);
v___x_1698_ = lean_unsigned_to_nat(0u);
v___x_1699_ = lean_array_get_size(v_buckets_1697_);
v___x_1700_ = lean_nat_dec_lt(v___x_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_dec_ref(v_m_u2081_1695_);
lean_dec_ref(v_inst_1694_);
lean_dec_ref(v_inst_1693_);
return v_m_u2082_1696_;
}
else
{
lean_object* v_buckets_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_buckets_1701_ = lean_ctor_get(v_m_u2082_1696_, 1);
v___x_1702_ = lean_array_get_size(v_buckets_1701_);
v___x_1703_ = lean_nat_dec_lt(v___x_1698_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_dec_ref(v_m_u2082_1696_);
lean_dec_ref(v_inst_1694_);
lean_dec_ref(v_inst_1693_);
return v_m_u2081_1695_;
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1693_, v_inst_1694_, v_m_u2081_1695_, v_m_u2082_1696_);
return v___x_1704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter(lean_object* v_00_u03b1_1705_, lean_object* v_00_u03b2_1706_, lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_m_u2081_1709_, lean_object* v_m_u2082_1710_){
_start:
{
lean_object* v_buckets_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; uint8_t v___x_1714_; 
v_buckets_1711_ = lean_ctor_get(v_m_u2081_1709_, 1);
v___x_1712_ = lean_unsigned_to_nat(0u);
v___x_1713_ = lean_array_get_size(v_buckets_1711_);
v___x_1714_ = lean_nat_dec_lt(v___x_1712_, v___x_1713_);
if (v___x_1714_ == 0)
{
lean_dec_ref(v_m_u2081_1709_);
lean_dec_ref(v_inst_1708_);
lean_dec_ref(v_inst_1707_);
return v_m_u2082_1710_;
}
else
{
lean_object* v_buckets_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_buckets_1715_ = lean_ctor_get(v_m_u2082_1710_, 1);
v___x_1716_ = lean_array_get_size(v_buckets_1715_);
v___x_1717_ = lean_nat_dec_lt(v___x_1712_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_dec_ref(v_m_u2082_1710_);
lean_dec_ref(v_inst_1708_);
lean_dec_ref(v_inst_1707_);
return v_m_u2081_1709_;
}
else
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1707_, v_inst_1708_, v_m_u2081_1709_, v_m_u2082_1710_);
return v___x_1718_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_m_u2082_1721_, uint8_t v___x_1722_, lean_object* v_k_1723_, lean_object* v_x_1724_){
_start:
{
uint8_t v___x_1725_; 
v___x_1725_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1719_, v_inst_1720_, v_m_u2082_1721_, v_k_1723_);
if (v___x_1725_ == 0)
{
return v___x_1722_;
}
else
{
uint8_t v___x_1726_; 
v___x_1726_ = 0;
return v___x_1726_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_m_u2082_1729_, lean_object* v___x_1730_, lean_object* v_k_1731_, lean_object* v_x_1732_){
_start:
{
uint8_t v___x_91__boxed_1733_; uint8_t v_res_1734_; lean_object* v_r_1735_; 
v___x_91__boxed_1733_ = lean_unbox(v___x_1730_);
v_res_1734_ = l_Std_HashMap_Raw_diff___redArg___lam__0(v_inst_1727_, v_inst_1728_, v_m_u2082_1729_, v___x_91__boxed_1733_, v_k_1731_, v_x_1732_);
lean_dec(v_x_1732_);
lean_dec_ref(v_m_u2082_1729_);
v_r_1735_ = lean_box(v_res_1734_);
return v_r_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg(lean_object* v_inst_1736_, lean_object* v_inst_1737_, lean_object* v_m_u2081_1738_, lean_object* v_m_u2082_1739_){
_start:
{
lean_object* v_size_1740_; lean_object* v_buckets_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v_size_1740_ = lean_ctor_get(v_m_u2081_1738_, 0);
v_buckets_1741_ = lean_ctor_get(v_m_u2081_1738_, 1);
v___x_1742_ = lean_unsigned_to_nat(0u);
v___x_1743_ = lean_array_get_size(v_buckets_1741_);
v___x_1744_ = lean_nat_dec_lt(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_dec_ref(v_m_u2081_1738_);
lean_dec_ref(v_inst_1737_);
lean_dec_ref(v_inst_1736_);
return v_m_u2082_1739_;
}
else
{
lean_object* v_size_1745_; lean_object* v_buckets_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_size_1745_ = lean_ctor_get(v_m_u2082_1739_, 0);
v_buckets_1746_ = lean_ctor_get(v_m_u2082_1739_, 1);
v___x_1747_ = lean_array_get_size(v_buckets_1746_);
v___x_1748_ = lean_nat_dec_lt(v___x_1742_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_dec_ref(v_m_u2082_1739_);
lean_dec_ref(v_inst_1737_);
lean_dec_ref(v_inst_1736_);
return v_m_u2081_1738_;
}
else
{
uint8_t v___x_1749_; 
v___x_1749_ = lean_nat_dec_le(v_size_1740_, v_size_1745_);
if (v___x_1749_ == 0)
{
lean_object* v___f_1750_; lean_object* v___x_1751_; 
v___f_1750_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1751_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1750_, v_inst_1736_, v_inst_1737_, v_m_u2081_1738_, v_m_u2082_1739_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; lean_object* v___f_1753_; lean_object* v___x_1754_; 
v___x_1752_ = lean_box(v___x_1749_);
v___f_1753_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1753_, 0, v_inst_1736_);
lean_closure_set(v___f_1753_, 1, v_inst_1737_);
lean_closure_set(v___f_1753_, 2, v_m_u2082_1739_);
lean_closure_set(v___f_1753_, 3, v___x_1752_);
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1753_, v_m_u2081_1738_);
return v___x_1754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff(lean_object* v_00_u03b1_1755_, lean_object* v_00_u03b2_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_m_u2081_1759_, lean_object* v_m_u2082_1760_){
_start:
{
lean_object* v_size_1761_; lean_object* v_buckets_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v_size_1761_ = lean_ctor_get(v_m_u2081_1759_, 0);
v_buckets_1762_ = lean_ctor_get(v_m_u2081_1759_, 1);
v___x_1763_ = lean_unsigned_to_nat(0u);
v___x_1764_ = lean_array_get_size(v_buckets_1762_);
v___x_1765_ = lean_nat_dec_lt(v___x_1763_, v___x_1764_);
if (v___x_1765_ == 0)
{
lean_dec_ref(v_m_u2081_1759_);
lean_dec_ref(v_inst_1758_);
lean_dec_ref(v_inst_1757_);
return v_m_u2082_1760_;
}
else
{
lean_object* v_size_1766_; lean_object* v_buckets_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_size_1766_ = lean_ctor_get(v_m_u2082_1760_, 0);
v_buckets_1767_ = lean_ctor_get(v_m_u2082_1760_, 1);
v___x_1768_ = lean_array_get_size(v_buckets_1767_);
v___x_1769_ = lean_nat_dec_lt(v___x_1763_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_dec_ref(v_m_u2082_1760_);
lean_dec_ref(v_inst_1758_);
lean_dec_ref(v_inst_1757_);
return v_m_u2081_1759_;
}
else
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_nat_dec_le(v_size_1761_, v_size_1766_);
if (v___x_1770_ == 0)
{
lean_object* v___f_1771_; lean_object* v___x_1772_; 
v___f_1771_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1772_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1771_, v_inst_1757_, v_inst_1758_, v_m_u2081_1759_, v_m_u2082_1760_);
return v___x_1772_;
}
else
{
lean_object* v___x_1773_; lean_object* v___f_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_box(v___x_1770_);
v___f_1774_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1774_, 0, v_inst_1757_);
lean_closure_set(v___f_1774_, 1, v_inst_1758_);
lean_closure_set(v___f_1774_, 2, v_m_u2082_1760_);
lean_closure_set(v___f_1774_, 3, v___x_1773_);
v___x_1775_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1774_, v_m_u2081_1759_);
return v___x_1775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1776_, lean_object* v_inst_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1778_, 0, lean_box(0));
lean_closure_set(v___x_1778_, 1, lean_box(0));
lean_closure_set(v___x_1778_, 2, v_inst_1776_);
lean_closure_set(v___x_1778_, 3, v_inst_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1779_, lean_object* v_00_u03b2_1780_, lean_object* v_inst_1781_, lean_object* v_inst_1782_){
_start:
{
lean_object* v___x_1783_; 
v___x_1783_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1783_, 0, lean_box(0));
lean_closure_set(v___x_1783_, 1, lean_box(0));
lean_closure_set(v___x_1783_, 2, v_inst_1781_);
lean_closure_set(v___x_1783_, 3, v_inst_1782_);
return v___x_1783_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1784_, lean_object* v_inst_1785_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1786_, 0, lean_box(0));
lean_closure_set(v___x_1786_, 1, lean_box(0));
lean_closure_set(v___x_1786_, 2, v_inst_1784_);
lean_closure_set(v___x_1786_, 3, v_inst_1785_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1787_, lean_object* v_00_u03b2_1788_, lean_object* v_inst_1789_, lean_object* v_inst_1790_){
_start:
{
lean_object* v___x_1791_; 
v___x_1791_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1791_, 0, lean_box(0));
lean_closure_set(v___x_1791_, 1, lean_box(0));
lean_closure_set(v___x_1791_, 2, v_inst_1789_);
lean_closure_set(v___x_1791_, 3, v_inst_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1792_, lean_object* v_inst_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1794_, 0, lean_box(0));
lean_closure_set(v___x_1794_, 1, lean_box(0));
lean_closure_set(v___x_1794_, 2, v_inst_1792_);
lean_closure_set(v___x_1794_, 3, v_inst_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1795_, lean_object* v_00_u03b2_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1799_, 0, lean_box(0));
lean_closure_set(v___x_1799_, 1, lean_box(0));
lean_closure_set(v___x_1799_, 2, v_inst_1797_);
lean_closure_set(v___x_1799_, 3, v_inst_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq___redArg(lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_m_u2081_1803_, lean_object* v_m_u2082_1804_){
_start:
{
uint8_t v___x_1805_; 
v___x_1805_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1800_, v_inst_1801_, v_inst_1802_, v_m_u2081_1803_, v_m_u2082_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___redArg___boxed(lean_object* v_inst_1806_, lean_object* v_inst_1807_, lean_object* v_inst_1808_, lean_object* v_m_u2081_1809_, lean_object* v_m_u2082_1810_){
_start:
{
uint8_t v_res_1811_; lean_object* v_r_1812_; 
v_res_1811_ = l_Std_HashMap_Raw_beq___redArg(v_inst_1806_, v_inst_1807_, v_inst_1808_, v_m_u2081_1809_, v_m_u2082_1810_);
v_r_1812_ = lean_box(v_res_1811_);
return v_r_1812_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq(lean_object* v_00_u03b1_1813_, lean_object* v_00_u03b2_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_m_u2081_1818_, lean_object* v_m_u2082_1819_){
_start:
{
uint8_t v___x_1820_; 
v___x_1820_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1815_, v_inst_1816_, v_inst_1817_, v_m_u2081_1818_, v_m_u2082_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___boxed(lean_object* v_00_u03b1_1821_, lean_object* v_00_u03b2_1822_, lean_object* v_inst_1823_, lean_object* v_inst_1824_, lean_object* v_inst_1825_, lean_object* v_m_u2081_1826_, lean_object* v_m_u2082_1827_){
_start:
{
uint8_t v_res_1828_; lean_object* v_r_1829_; 
v_res_1828_ = l_Std_HashMap_Raw_beq(v_00_u03b1_1821_, v_00_u03b2_1822_, v_inst_1823_, v_inst_1824_, v_inst_1825_, v_m_u2081_1826_, v_m_u2082_1827_);
v_r_1829_ = lean_box(v_res_1828_);
return v_r_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1833_, 0, lean_box(0));
lean_closure_set(v___x_1833_, 1, lean_box(0));
lean_closure_set(v___x_1833_, 2, v_inst_1830_);
lean_closure_set(v___x_1833_, 3, v_inst_1831_);
lean_closure_set(v___x_1833_, 4, v_inst_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1834_, lean_object* v_00_u03b2_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_inst_1838_){
_start:
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1839_, 0, lean_box(0));
lean_closure_set(v___x_1839_, 1, lean_box(0));
lean_closure_set(v___x_1839_, 2, v_inst_1836_);
lean_closure_set(v___x_1839_, 3, v_inst_1837_);
lean_closure_set(v___x_1839_, 4, v_inst_1838_);
return v___x_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg(lean_object* v_f_1840_, lean_object* v_m_1841_){
_start:
{
lean_object* v_buckets_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; uint8_t v___x_1845_; 
v_buckets_1842_ = lean_ctor_get(v_m_1841_, 1);
v___x_1843_ = lean_unsigned_to_nat(0u);
v___x_1844_ = lean_array_get_size(v_buckets_1842_);
v___x_1845_ = lean_nat_dec_lt(v___x_1843_, v___x_1844_);
if (v___x_1845_ == 0)
{
lean_object* v___x_1846_; 
lean_dec_ref(v_m_1841_);
lean_dec_ref(v_f_1840_);
v___x_1846_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1846_;
}
else
{
lean_object* v___x_1847_; 
v___x_1847_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1840_, v_m_1841_);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object* v_00_u03b1_1848_, lean_object* v_00_u03b2_1849_, lean_object* v_00_u03b3_1850_, lean_object* v_f_1851_, lean_object* v_m_1852_){
_start:
{
lean_object* v_buckets_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v_buckets_1853_ = lean_ctor_get(v_m_1852_, 1);
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = lean_array_get_size(v_buckets_1853_);
v___x_1856_ = lean_nat_dec_lt(v___x_1854_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1857_; 
lean_dec_ref(v_m_1852_);
lean_dec_ref(v_f_1851_);
v___x_1857_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1857_;
}
else
{
lean_object* v___x_1858_; 
v___x_1858_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1851_, v_m_1852_);
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object* v_f_1859_, lean_object* v_m_1860_){
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
lean_dec(v_f_1859_);
v___x_1865_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1865_;
}
else
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1859_, v_m_1860_);
return v___x_1866_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object* v_00_u03b1_1867_, lean_object* v_00_u03b2_1868_, lean_object* v_00_u03b3_1869_, lean_object* v_f_1870_, lean_object* v_m_1871_){
_start:
{
lean_object* v_buckets_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; 
v_buckets_1872_ = lean_ctor_get(v_m_1871_, 1);
v___x_1873_ = lean_unsigned_to_nat(0u);
v___x_1874_ = lean_array_get_size(v_buckets_1872_);
v___x_1875_ = lean_nat_dec_lt(v___x_1873_, v___x_1874_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; 
lean_dec_ref(v_m_1871_);
lean_dec(v_f_1870_);
v___x_1876_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1876_;
}
else
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1870_, v_m_1871_);
return v___x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object* v_f_1878_, lean_object* v_m_1879_){
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
lean_dec_ref(v_f_1878_);
v___x_1884_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; 
v___x_1885_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1878_, v_m_1879_);
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object* v_00_u03b1_1886_, lean_object* v_00_u03b2_1887_, lean_object* v_f_1888_, lean_object* v_m_1889_){
_start:
{
lean_object* v_buckets_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v_buckets_1890_ = lean_ctor_get(v_m_1889_, 1);
v___x_1891_ = lean_unsigned_to_nat(0u);
v___x_1892_ = lean_array_get_size(v_buckets_1890_);
v___x_1893_ = lean_nat_dec_lt(v___x_1891_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v___x_1894_; 
lean_dec_ref(v_m_1889_);
lean_dec_ref(v_f_1888_);
v___x_1894_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1894_;
}
else
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1888_, v_m_1889_);
return v___x_1895_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1896_, lean_object* v_x2_1897_, lean_object* v_x3_1898_){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v_x2_1897_);
lean_ctor_set(v___x_1899_, 1, v_x3_1898_);
v___x_1900_ = lean_array_push(v_x1_1896_, v___x_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1901_, lean_object* v___f_1902_, lean_object* v_acc_1903_, lean_object* v_l_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1901_, v___f_1902_, v_acc_1903_, v_l_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object* v_m_1910_){
_start:
{
lean_object* v_size_1911_; lean_object* v_buckets_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v_size_1911_ = lean_ctor_get(v_m_1910_, 0);
lean_inc(v_size_1911_);
v_buckets_1912_ = lean_ctor_get(v_m_1910_, 1);
lean_inc_ref(v_buckets_1912_);
lean_dec_ref(v_m_1910_);
v___x_1913_ = lean_mk_empty_array_with_capacity(v_size_1911_);
lean_dec(v_size_1911_);
v___x_1914_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1915_ = lean_unsigned_to_nat(0u);
v___x_1916_ = lean_array_get_size(v_buckets_1912_);
v___x_1917_ = lean_nat_dec_lt(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_dec_ref(v_buckets_1912_);
return v___x_1913_;
}
else
{
lean_object* v___f_1918_; uint8_t v___x_1919_; 
v___f_1918_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1919_ = lean_nat_dec_le(v___x_1916_, v___x_1916_);
if (v___x_1919_ == 0)
{
if (v___x_1917_ == 0)
{
lean_dec_ref(v_buckets_1912_);
return v___x_1913_;
}
else
{
size_t v___x_1920_; size_t v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = ((size_t)0ULL);
v___x_1921_ = lean_usize_of_nat(v___x_1916_);
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1914_, v___f_1918_, v_buckets_1912_, v___x_1920_, v___x_1921_, v___x_1913_);
return v___x_1922_;
}
}
else
{
size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = lean_usize_of_nat(v___x_1916_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1914_, v___f_1918_, v_buckets_1912_, v___x_1923_, v___x_1924_, v___x_1913_);
return v___x_1925_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object* v_00_u03b1_1926_, lean_object* v_00_u03b2_1927_, lean_object* v_m_1928_){
_start:
{
lean_object* v_size_1929_; lean_object* v_buckets_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; uint8_t v___x_1935_; 
v_size_1929_ = lean_ctor_get(v_m_1928_, 0);
lean_inc(v_size_1929_);
v_buckets_1930_ = lean_ctor_get(v_m_1928_, 1);
lean_inc_ref(v_buckets_1930_);
lean_dec_ref(v_m_1928_);
v___x_1931_ = lean_mk_empty_array_with_capacity(v_size_1929_);
lean_dec(v_size_1929_);
v___x_1932_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1933_ = lean_unsigned_to_nat(0u);
v___x_1934_ = lean_array_get_size(v_buckets_1930_);
v___x_1935_ = lean_nat_dec_lt(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
lean_dec_ref(v_buckets_1930_);
return v___x_1931_;
}
else
{
lean_object* v___f_1936_; uint8_t v___x_1937_; 
v___f_1936_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1937_ = lean_nat_dec_le(v___x_1934_, v___x_1934_);
if (v___x_1937_ == 0)
{
if (v___x_1935_ == 0)
{
lean_dec_ref(v_buckets_1930_);
return v___x_1931_;
}
else
{
size_t v___x_1938_; size_t v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = ((size_t)0ULL);
v___x_1939_ = lean_usize_of_nat(v___x_1934_);
v___x_1940_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1932_, v___f_1936_, v_buckets_1930_, v___x_1938_, v___x_1939_, v___x_1931_);
return v___x_1940_;
}
}
else
{
size_t v___x_1941_; size_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = ((size_t)0ULL);
v___x_1942_ = lean_usize_of_nat(v___x_1934_);
v___x_1943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1932_, v___f_1936_, v_buckets_1930_, v___x_1941_, v___x_1942_, v___x_1931_);
return v___x_1943_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1944_, lean_object* v_x2_1945_, lean_object* v_x3_1946_){
_start:
{
lean_object* v___x_1947_; 
v___x_1947_ = lean_array_push(v_x1_1944_, v_x2_1945_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1948_, lean_object* v_x2_1949_, lean_object* v_x3_1950_){
_start:
{
lean_object* v_res_1951_; 
v_res_1951_ = l_Std_HashMap_Raw_keysArray___redArg___lam__0(v_x1_1948_, v_x2_1949_, v_x3_1950_);
lean_dec(v_x3_1950_);
return v_res_1951_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1952_, lean_object* v___f_1953_, lean_object* v_acc_1954_, lean_object* v_l_1955_){
_start:
{
lean_object* v___x_1956_; 
v___x_1956_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1952_, v___f_1953_, v_acc_1954_, v_l_1955_);
return v___x_1956_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object* v_m_1961_){
_start:
{
lean_object* v_size_1962_; lean_object* v_buckets_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v_size_1962_ = lean_ctor_get(v_m_1961_, 0);
lean_inc(v_size_1962_);
v_buckets_1963_ = lean_ctor_get(v_m_1961_, 1);
lean_inc_ref(v_buckets_1963_);
lean_dec_ref(v_m_1961_);
v___x_1964_ = lean_mk_empty_array_with_capacity(v_size_1962_);
lean_dec(v_size_1962_);
v___x_1965_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1966_ = lean_unsigned_to_nat(0u);
v___x_1967_ = lean_array_get_size(v_buckets_1963_);
v___x_1968_ = lean_nat_dec_lt(v___x_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_dec_ref(v_buckets_1963_);
return v___x_1964_;
}
else
{
lean_object* v___f_1969_; uint8_t v___x_1970_; 
v___f_1969_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1970_ = lean_nat_dec_le(v___x_1967_, v___x_1967_);
if (v___x_1970_ == 0)
{
if (v___x_1968_ == 0)
{
lean_dec_ref(v_buckets_1963_);
return v___x_1964_;
}
else
{
size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = lean_usize_of_nat(v___x_1967_);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1965_, v___f_1969_, v_buckets_1963_, v___x_1971_, v___x_1972_, v___x_1964_);
return v___x_1973_;
}
}
else
{
size_t v___x_1974_; size_t v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = ((size_t)0ULL);
v___x_1975_ = lean_usize_of_nat(v___x_1967_);
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1965_, v___f_1969_, v_buckets_1963_, v___x_1974_, v___x_1975_, v___x_1964_);
return v___x_1976_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object* v_00_u03b1_1977_, lean_object* v_00_u03b2_1978_, lean_object* v_m_1979_){
_start:
{
lean_object* v_size_1980_; lean_object* v_buckets_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v_size_1980_ = lean_ctor_get(v_m_1979_, 0);
lean_inc(v_size_1980_);
v_buckets_1981_ = lean_ctor_get(v_m_1979_, 1);
lean_inc_ref(v_buckets_1981_);
lean_dec_ref(v_m_1979_);
v___x_1982_ = lean_mk_empty_array_with_capacity(v_size_1980_);
lean_dec(v_size_1980_);
v___x_1983_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1984_ = lean_unsigned_to_nat(0u);
v___x_1985_ = lean_array_get_size(v_buckets_1981_);
v___x_1986_ = lean_nat_dec_lt(v___x_1984_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_dec_ref(v_buckets_1981_);
return v___x_1982_;
}
else
{
lean_object* v___f_1987_; uint8_t v___x_1988_; 
v___f_1987_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1988_ = lean_nat_dec_le(v___x_1985_, v___x_1985_);
if (v___x_1988_ == 0)
{
if (v___x_1986_ == 0)
{
lean_dec_ref(v_buckets_1981_);
return v___x_1982_;
}
else
{
size_t v___x_1989_; size_t v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = ((size_t)0ULL);
v___x_1990_ = lean_usize_of_nat(v___x_1985_);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1983_, v___f_1987_, v_buckets_1981_, v___x_1989_, v___x_1990_, v___x_1982_);
return v___x_1991_;
}
}
else
{
size_t v___x_1992_; size_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1992_ = ((size_t)0ULL);
v___x_1993_ = lean_usize_of_nat(v___x_1985_);
v___x_1994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1983_, v___f_1987_, v_buckets_1981_, v___x_1992_, v___x_1993_, v___x_1982_);
return v___x_1994_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object* v_a_1995_, lean_object* v_b_1996_, lean_object* v_d_1997_){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1998_, 0, v_b_1996_);
lean_ctor_set(v___x_1998_, 1, v_d_1997_);
return v___x_1998_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_1999_, lean_object* v_b_2000_, lean_object* v_d_2001_){
_start:
{
lean_object* v_res_2002_; 
v_res_2002_ = l_Std_HashMap_Raw_values___redArg___lam__0(v_a_1999_, v_b_2000_, v_d_2001_);
lean_dec(v_a_1999_);
return v_res_2002_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object* v_m_2007_){
_start:
{
lean_object* v___x_2008_; lean_object* v_buckets_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; uint8_t v___x_2013_; 
v___x_2008_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2009_ = lean_ctor_get(v_m_2007_, 1);
lean_inc_ref(v_buckets_2009_);
lean_dec_ref(v_m_2007_);
v___x_2010_ = lean_box(0);
v___x_2011_ = lean_array_get_size(v_buckets_2009_);
v___x_2012_ = lean_unsigned_to_nat(0u);
v___x_2013_ = lean_nat_dec_lt(v___x_2012_, v___x_2011_);
if (v___x_2013_ == 0)
{
lean_dec_ref(v_buckets_2009_);
return v___x_2010_;
}
else
{
lean_object* v___f_2014_; size_t v___x_2015_; size_t v___x_2016_; lean_object* v___x_2017_; 
v___f_2014_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_2015_ = lean_usize_of_nat(v___x_2011_);
v___x_2016_ = ((size_t)0ULL);
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2008_, v___f_2014_, v_buckets_2009_, v___x_2015_, v___x_2016_, v___x_2010_);
return v___x_2017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object* v_00_u03b1_2018_, lean_object* v_00_u03b2_2019_, lean_object* v_m_2020_){
_start:
{
lean_object* v___x_2021_; lean_object* v_buckets_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2021_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2022_ = lean_ctor_get(v_m_2020_, 1);
lean_inc_ref(v_buckets_2022_);
lean_dec_ref(v_m_2020_);
v___x_2023_ = lean_box(0);
v___x_2024_ = lean_array_get_size(v_buckets_2022_);
v___x_2025_ = lean_unsigned_to_nat(0u);
v___x_2026_ = lean_nat_dec_lt(v___x_2025_, v___x_2024_);
if (v___x_2026_ == 0)
{
lean_dec_ref(v_buckets_2022_);
return v___x_2023_;
}
else
{
lean_object* v___f_2027_; size_t v___x_2028_; size_t v___x_2029_; lean_object* v___x_2030_; 
v___f_2027_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_2028_ = lean_usize_of_nat(v___x_2024_);
v___x_2029_ = ((size_t)0ULL);
v___x_2030_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2021_, v___f_2027_, v_buckets_2022_, v___x_2028_, v___x_2029_, v___x_2023_);
return v___x_2030_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2031_, lean_object* v_x2_2032_, lean_object* v_x3_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_array_push(v_x1_2031_, v_x3_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2035_, lean_object* v_x2_2036_, lean_object* v_x3_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Std_HashMap_Raw_valuesArray___redArg___lam__0(v_x1_2035_, v_x2_2036_, v_x3_2037_);
lean_dec(v_x2_2036_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg(lean_object* v_m_2043_){
_start:
{
lean_object* v_size_2044_; lean_object* v_buckets_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; uint8_t v___x_2050_; 
v_size_2044_ = lean_ctor_get(v_m_2043_, 0);
lean_inc(v_size_2044_);
v_buckets_2045_ = lean_ctor_get(v_m_2043_, 1);
lean_inc_ref(v_buckets_2045_);
lean_dec_ref(v_m_2043_);
v___x_2046_ = lean_mk_empty_array_with_capacity(v_size_2044_);
lean_dec(v_size_2044_);
v___x_2047_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2048_ = lean_unsigned_to_nat(0u);
v___x_2049_ = lean_array_get_size(v_buckets_2045_);
v___x_2050_ = lean_nat_dec_lt(v___x_2048_, v___x_2049_);
if (v___x_2050_ == 0)
{
lean_dec_ref(v_buckets_2045_);
return v___x_2046_;
}
else
{
lean_object* v___f_2051_; uint8_t v___x_2052_; 
v___f_2051_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2052_ = lean_nat_dec_le(v___x_2049_, v___x_2049_);
if (v___x_2052_ == 0)
{
if (v___x_2050_ == 0)
{
lean_dec_ref(v_buckets_2045_);
return v___x_2046_;
}
else
{
size_t v___x_2053_; size_t v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = ((size_t)0ULL);
v___x_2054_ = lean_usize_of_nat(v___x_2049_);
v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2047_, v___f_2051_, v_buckets_2045_, v___x_2053_, v___x_2054_, v___x_2046_);
return v___x_2055_;
}
}
else
{
size_t v___x_2056_; size_t v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = ((size_t)0ULL);
v___x_2057_ = lean_usize_of_nat(v___x_2049_);
v___x_2058_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2047_, v___f_2051_, v_buckets_2045_, v___x_2056_, v___x_2057_, v___x_2046_);
return v___x_2058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray(lean_object* v_00_u03b1_2059_, lean_object* v_00_u03b2_2060_, lean_object* v_m_2061_){
_start:
{
lean_object* v_size_2062_; lean_object* v_buckets_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; uint8_t v___x_2068_; 
v_size_2062_ = lean_ctor_get(v_m_2061_, 0);
lean_inc(v_size_2062_);
v_buckets_2063_ = lean_ctor_get(v_m_2061_, 1);
lean_inc_ref(v_buckets_2063_);
lean_dec_ref(v_m_2061_);
v___x_2064_ = lean_mk_empty_array_with_capacity(v_size_2062_);
lean_dec(v_size_2062_);
v___x_2065_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2066_ = lean_unsigned_to_nat(0u);
v___x_2067_ = lean_array_get_size(v_buckets_2063_);
v___x_2068_ = lean_nat_dec_lt(v___x_2066_, v___x_2067_);
if (v___x_2068_ == 0)
{
lean_dec_ref(v_buckets_2063_);
return v___x_2064_;
}
else
{
lean_object* v___f_2069_; uint8_t v___x_2070_; 
v___f_2069_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2070_ = lean_nat_dec_le(v___x_2067_, v___x_2067_);
if (v___x_2070_ == 0)
{
if (v___x_2068_ == 0)
{
lean_dec_ref(v_buckets_2063_);
return v___x_2064_;
}
else
{
size_t v___x_2071_; size_t v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((size_t)0ULL);
v___x_2072_ = lean_usize_of_nat(v___x_2067_);
v___x_2073_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2065_, v___f_2069_, v_buckets_2063_, v___x_2071_, v___x_2072_, v___x_2064_);
return v___x_2073_;
}
}
else
{
size_t v___x_2074_; size_t v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = ((size_t)0ULL);
v___x_2075_ = lean_usize_of_nat(v___x_2067_);
v___x_2076_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2065_, v___f_2069_, v_buckets_2063_, v___x_2074_, v___x_2075_, v___x_2064_);
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany___redArg(lean_object* v_inst_2077_, lean_object* v_inst_2078_, lean_object* v_inst_2079_, lean_object* v_m_2080_, lean_object* v_l_2081_){
_start:
{
lean_object* v_buckets_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; uint8_t v___x_2085_; 
v_buckets_2082_ = lean_ctor_get(v_m_2080_, 1);
v___x_2083_ = lean_unsigned_to_nat(0u);
v___x_2084_ = lean_array_get_size(v_buckets_2082_);
v___x_2085_ = lean_nat_dec_lt(v___x_2083_, v___x_2084_);
if (v___x_2085_ == 0)
{
lean_dec(v_l_2081_);
lean_dec(v_inst_2079_);
lean_dec_ref(v_inst_2078_);
lean_dec_ref(v_inst_2077_);
return v_m_2080_;
}
else
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2079_, v_inst_2077_, v_inst_2078_, v_m_2080_, v_l_2081_);
return v___x_2086_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany(lean_object* v_00_u03b1_2087_, lean_object* v_00_u03b2_2088_, lean_object* v_inst_2089_, lean_object* v_inst_2090_, lean_object* v_00_u03c1_2091_, lean_object* v_inst_2092_, lean_object* v_m_2093_, lean_object* v_l_2094_){
_start:
{
lean_object* v_buckets_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; uint8_t v___x_2098_; 
v_buckets_2095_ = lean_ctor_get(v_m_2093_, 1);
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = lean_array_get_size(v_buckets_2095_);
v___x_2098_ = lean_nat_dec_lt(v___x_2096_, v___x_2097_);
if (v___x_2098_ == 0)
{
lean_dec(v_l_2094_);
lean_dec(v_inst_2092_);
lean_dec_ref(v_inst_2090_);
lean_dec_ref(v_inst_2089_);
return v_m_2093_;
}
else
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2092_, v_inst_2089_, v_inst_2090_, v_m_2093_, v_l_2094_);
return v___x_2099_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_inst_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_m_2103_, lean_object* v_l_2104_){
_start:
{
lean_object* v_buckets_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; uint8_t v___x_2108_; 
v_buckets_2105_ = lean_ctor_get(v_m_2103_, 1);
v___x_2106_ = lean_unsigned_to_nat(0u);
v___x_2107_ = lean_array_get_size(v_buckets_2105_);
v___x_2108_ = lean_nat_dec_lt(v___x_2106_, v___x_2107_);
if (v___x_2108_ == 0)
{
lean_dec(v_l_2104_);
lean_dec(v_inst_2102_);
lean_dec_ref(v_inst_2101_);
lean_dec_ref(v_inst_2100_);
return v_m_2103_;
}
else
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2102_, v_inst_2100_, v_inst_2101_, v_m_2103_, v_l_2104_);
return v___x_2109_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_00_u03c1_2113_, lean_object* v_inst_2114_, lean_object* v_m_2115_, lean_object* v_l_2116_){
_start:
{
lean_object* v_buckets_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; uint8_t v___x_2120_; 
v_buckets_2117_ = lean_ctor_get(v_m_2115_, 1);
v___x_2118_ = lean_unsigned_to_nat(0u);
v___x_2119_ = lean_array_get_size(v_buckets_2117_);
v___x_2120_ = lean_nat_dec_lt(v___x_2118_, v___x_2119_);
if (v___x_2120_ == 0)
{
lean_dec(v_l_2116_);
lean_dec(v_inst_2114_);
lean_dec_ref(v_inst_2112_);
lean_dec_ref(v_inst_2111_);
return v_m_2115_;
}
else
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2114_, v_inst_2111_, v_inst_2112_, v_m_2115_, v_l_2116_);
return v___x_2121_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray___redArg(lean_object* v_inst_2122_, lean_object* v_inst_2123_, lean_object* v_l_2124_){
_start:
{
lean_object* v___x_2125_; uint8_t v___x_2126_; 
v___x_2125_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_2126_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2126_ == 0)
{
lean_dec_ref(v_l_2124_);
lean_dec_ref(v_inst_2123_);
lean_dec_ref(v_inst_2122_);
return v___x_2125_;
}
else
{
lean_object* v___f_2127_; lean_object* v___x_2128_; 
v___f_2127_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2128_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2127_, v_inst_2122_, v_inst_2123_, v___x_2125_, v_l_2124_);
return v___x_2128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray(lean_object* v_00_u03b1_2129_, lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_l_2132_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2137_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2137_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Std_HashMap_Raw_Internal_numBuckets___redArg(v_m_2139_);
lean_dec_ref(v_m_2139_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2141_, lean_object* v_00_u03b2_2142_, lean_object* v_m_2143_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2145_, lean_object* v_00_u03b2_2146_, lean_object* v_m_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Std_HashMap_Raw_Internal_numBuckets(v_00_u03b1_2145_, v_00_u03b2_2146_, v_m_2147_);
lean_dec_ref(v_m_2147_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2152_, lean_object* v___f_2153_, lean_object* v_m_2154_, lean_object* v_prec_2155_){
_start:
{
lean_object* v___x_2156_; lean_object* v_buckets_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2177_; 
v___x_2156_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2157_ = lean_ctor_get(v_m_2154_, 1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_m_2154_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v_m_2154_, 0);
lean_dec(v_unused_2178_);
v___x_2159_ = v_m_2154_;
v_isShared_2160_ = v_isSharedCheck_2177_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_buckets_2157_);
lean_dec(v_m_2154_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2177_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v___y_2163_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2161_ = ((lean_object*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2169_ = lean_box(0);
v___x_2170_ = lean_array_get_size(v_buckets_2157_);
v___x_2171_ = lean_unsigned_to_nat(0u);
v___x_2172_ = lean_nat_dec_lt(v___x_2171_, v___x_2170_);
if (v___x_2172_ == 0)
{
lean_dec_ref(v_buckets_2157_);
lean_dec_ref(v___f_2153_);
v___y_2163_ = v___x_2169_;
goto v___jp_2162_;
}
else
{
lean_object* v___f_2173_; size_t v___x_2174_; size_t v___x_2175_; lean_object* v___x_2176_; 
v___f_2173_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2173_, 0, v___x_2156_);
lean_closure_set(v___f_2173_, 1, v___f_2153_);
v___x_2174_ = lean_usize_of_nat(v___x_2170_);
v___x_2175_ = ((size_t)0ULL);
v___x_2176_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2156_, v___f_2173_, v_buckets_2157_, v___x_2174_, v___x_2175_, v___x_2169_);
v___y_2163_ = v___x_2176_;
goto v___jp_2162_;
}
v___jp_2162_:
{
lean_object* v___x_2164_; lean_object* v___x_2166_; 
v___x_2164_ = l_List_repr___redArg(v___x_2152_, v___y_2163_);
if (v_isShared_2160_ == 0)
{
lean_ctor_set_tag(v___x_2159_, 5);
lean_ctor_set(v___x_2159_, 1, v___x_2164_);
lean_ctor_set(v___x_2159_, 0, v___x_2161_);
v___x_2166_ = v___x_2159_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2161_);
lean_ctor_set(v_reuseFailAlloc_2168_, 1, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Repr_addAppParen(v___x_2166_, v_prec_2155_);
return v___x_2167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2179_, lean_object* v___f_2180_, lean_object* v_m_2181_, lean_object* v_prec_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2(v___x_2179_, v___f_2180_, v_m_2181_, v_prec_2182_);
lean_dec(v_prec_2182_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object* v_inst_2184_, lean_object* v_inst_2185_){
_start:
{
lean_object* v___f_2186_; lean_object* v___f_2187_; lean_object* v___x_2188_; lean_object* v___f_2189_; 
v___f_2186_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__0));
v___f_2187_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2187_, 0, v_inst_2185_);
v___x_2188_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2188_, 0, lean_box(0));
lean_closure_set(v___x_2188_, 1, lean_box(0));
lean_closure_set(v___x_2188_, 2, v_inst_2184_);
lean_closure_set(v___x_2188_, 3, v___f_2187_);
v___f_2189_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2189_, 0, v___x_2188_);
lean_closure_set(v___f_2189_, 1, v___f_2186_);
return v___f_2189_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object* v_00_u03b1_2190_, lean_object* v_00_u03b2_2191_, lean_object* v_inst_2192_, lean_object* v_inst_2193_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Std_HashMap_Raw_instRepr___redArg(v_inst_2192_, v_inst_2193_);
return v___x_2194_;
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
