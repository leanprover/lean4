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
uint8_t v___x_692_; 
v___x_692_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_688_, v_inst_689_, v_m_690_, v_a_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_693_, lean_object* v_inst_694_, lean_object* v_m_695_, lean_object* v_a_696_){
_start:
{
uint8_t v_res_697_; lean_object* v_r_698_; 
v_res_697_ = l_Std_HashMap_Raw_instDecidableMem___redArg(v_inst_693_, v_inst_694_, v_m_695_, v_a_696_);
lean_dec_ref(v_m_695_);
v_r_698_ = lean_box(v_res_697_);
return v_r_698_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_inst_701_, lean_object* v_inst_702_, lean_object* v_m_703_, lean_object* v_a_704_){
_start:
{
uint8_t v___x_705_; 
v___x_705_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_701_, v_inst_702_, v_m_703_, v_a_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_706_, lean_object* v_00_u03b2_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_m_710_, lean_object* v_a_711_){
_start:
{
uint8_t v_res_712_; lean_object* v_r_713_; 
v_res_712_ = l_Std_HashMap_Raw_instDecidableMem(v_00_u03b1_706_, v_00_u03b2_707_, v_inst_708_, v_inst_709_, v_m_710_, v_a_711_);
lean_dec_ref(v_m_710_);
v_r_713_ = lean_box(v_res_712_);
return v_r_713_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg(lean_object* v_inst_714_, lean_object* v_inst_715_, lean_object* v_m_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_718_; 
v___x_718_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_714_, v_inst_715_, v_m_716_, v_a_717_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg___boxed(lean_object* v_inst_719_, lean_object* v_inst_720_, lean_object* v_m_721_, lean_object* v_a_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_Std_HashMap_Raw_get___redArg(v_inst_719_, v_inst_720_, v_m_721_, v_a_722_);
lean_dec_ref(v_m_721_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get(lean_object* v_00_u03b1_724_, lean_object* v_00_u03b2_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_m_728_, lean_object* v_a_729_, lean_object* v_h_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_726_, v_inst_727_, v_m_728_, v_a_729_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___boxed(lean_object* v_00_u03b1_732_, lean_object* v_00_u03b2_733_, lean_object* v_inst_734_, lean_object* v_inst_735_, lean_object* v_m_736_, lean_object* v_a_737_, lean_object* v_h_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Std_HashMap_Raw_get(v_00_u03b1_732_, v_00_u03b2_733_, v_inst_734_, v_inst_735_, v_m_736_, v_a_737_, v_h_738_);
lean_dec_ref(v_m_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg(lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_m_742_, lean_object* v_a_743_, lean_object* v_fallback_744_){
_start:
{
lean_object* v_buckets_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v_buckets_745_ = lean_ctor_get(v_m_742_, 1);
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_array_get_size(v_buckets_745_);
v___x_748_ = lean_nat_dec_lt(v___x_746_, v___x_747_);
if (v___x_748_ == 0)
{
lean_dec(v_a_743_);
lean_dec_ref(v_inst_741_);
lean_dec_ref(v_inst_740_);
lean_inc(v_fallback_744_);
return v_fallback_744_;
}
else
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_740_, v_inst_741_, v_m_742_, v_a_743_, v_fallback_744_);
return v___x_749_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg___boxed(lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_m_752_, lean_object* v_a_753_, lean_object* v_fallback_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Std_HashMap_Raw_getD___redArg(v_inst_750_, v_inst_751_, v_m_752_, v_a_753_, v_fallback_754_);
lean_dec(v_fallback_754_);
lean_dec_ref(v_m_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_m_760_, lean_object* v_a_761_, lean_object* v_fallback_762_){
_start:
{
lean_object* v_buckets_763_; lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; 
v_buckets_763_ = lean_ctor_get(v_m_760_, 1);
v___x_764_ = lean_unsigned_to_nat(0u);
v___x_765_ = lean_array_get_size(v_buckets_763_);
v___x_766_ = lean_nat_dec_lt(v___x_764_, v___x_765_);
if (v___x_766_ == 0)
{
lean_dec(v_a_761_);
lean_dec_ref(v_inst_759_);
lean_dec_ref(v_inst_758_);
lean_inc(v_fallback_762_);
return v_fallback_762_;
}
else
{
lean_object* v___x_767_; 
v___x_767_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_758_, v_inst_759_, v_m_760_, v_a_761_, v_fallback_762_);
return v___x_767_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___boxed(lean_object* v_00_u03b1_768_, lean_object* v_00_u03b2_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_m_772_, lean_object* v_a_773_, lean_object* v_fallback_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_HashMap_Raw_getD(v_00_u03b1_768_, v_00_u03b2_769_, v_inst_770_, v_inst_771_, v_m_772_, v_a_773_, v_fallback_774_);
lean_dec(v_fallback_774_);
lean_dec_ref(v_m_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg(lean_object* v_inst_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_m_779_, lean_object* v_a_780_){
_start:
{
lean_object* v_buckets_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_buckets_781_ = lean_ctor_get(v_m_779_, 1);
v___x_782_ = lean_unsigned_to_nat(0u);
v___x_783_ = lean_array_get_size(v_buckets_781_);
v___x_784_ = lean_nat_dec_lt(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_dec(v_a_780_);
lean_dec_ref(v_inst_777_);
lean_dec_ref(v_inst_776_);
lean_inc(v_inst_778_);
return v_inst_778_;
}
else
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_776_, v_inst_777_, v_inst_778_, v_m_779_, v_a_780_);
return v___x_785_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_inst_788_, lean_object* v_m_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_HashMap_Raw_get_x21___redArg(v_inst_786_, v_inst_787_, v_inst_788_, v_m_789_, v_a_790_);
lean_dec_ref(v_m_789_);
lean_dec(v_inst_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_m_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_buckets_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_buckets_799_ = lean_ctor_get(v_m_797_, 1);
v___x_800_ = lean_unsigned_to_nat(0u);
v___x_801_ = lean_array_get_size(v_buckets_799_);
v___x_802_ = lean_nat_dec_lt(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_dec(v_a_798_);
lean_dec_ref(v_inst_795_);
lean_dec_ref(v_inst_794_);
lean_inc(v_inst_796_);
return v_inst_796_;
}
else
{
lean_object* v___x_803_; 
v___x_803_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_794_, v_inst_795_, v_inst_796_, v_m_797_, v_a_798_);
return v___x_803_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_804_, lean_object* v_00_u03b2_805_, lean_object* v_inst_806_, lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_m_809_, lean_object* v_a_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l_Std_HashMap_Raw_get_x21(v_00_u03b1_804_, v_00_u03b2_805_, v_inst_806_, v_inst_807_, v_inst_808_, v_m_809_, v_a_810_);
lean_dec_ref(v_m_809_);
lean_dec(v_inst_808_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_812_, lean_object* v_inst_813_, lean_object* v_m_814_, lean_object* v_a_815_, lean_object* v_h_816_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_812_, v_inst_813_, v_m_814_, v_a_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_m_820_, lean_object* v_a_821_, lean_object* v_h_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(v_inst_818_, v_inst_819_, v_m_820_, v_a_821_, v_h_822_);
lean_dec_ref(v_m_820_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_m_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_buckets_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_buckets_828_ = lean_ctor_get(v_m_826_, 1);
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = lean_array_get_size(v_buckets_828_);
v___x_831_ = lean_nat_dec_lt(v___x_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; 
lean_dec(v_a_827_);
lean_dec_ref(v_inst_825_);
lean_dec_ref(v_inst_824_);
v___x_832_ = lean_box(0);
return v___x_832_;
}
else
{
lean_object* v___x_833_; 
v___x_833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_824_, v_inst_825_, v_m_826_, v_a_827_);
return v___x_833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_834_, lean_object* v_inst_835_, lean_object* v_m_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(v_inst_834_, v_inst_835_, v_m_836_, v_a_837_);
lean_dec_ref(v_m_836_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_m_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_buckets_844_; lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v_buckets_844_ = lean_ctor_get(v_m_842_, 1);
v___x_845_ = lean_unsigned_to_nat(0u);
v___x_846_ = lean_array_get_size(v_buckets_844_);
v___x_847_ = lean_nat_dec_lt(v___x_845_, v___x_846_);
if (v___x_847_ == 0)
{
lean_dec(v_a_843_);
lean_dec_ref(v_inst_840_);
lean_dec_ref(v_inst_839_);
lean_inc(v_inst_841_);
return v_inst_841_;
}
else
{
lean_object* v___x_848_; 
v___x_848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_839_, v_inst_840_, v_inst_841_, v_m_842_, v_a_843_);
return v___x_848_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_m_852_, lean_object* v_a_853_){
_start:
{
lean_object* v_res_854_; 
v_res_854_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(v_inst_849_, v_inst_850_, v_inst_851_, v_m_852_, v_a_853_);
lean_dec_ref(v_m_852_);
lean_dec(v_inst_851_);
return v_res_854_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(lean_object* v_inst_855_, lean_object* v_inst_856_){
_start:
{
lean_object* v___f_857_; lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___x_860_; 
lean_inc_ref_n(v_inst_856_, 2);
lean_inc_ref_n(v_inst_855_, 2);
v___f_857_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_857_, 0, v_inst_855_);
lean_closure_set(v___f_857_, 1, v_inst_856_);
v___f_858_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_858_, 0, v_inst_855_);
lean_closure_set(v___f_858_, 1, v_inst_856_);
v___f_859_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_859_, 0, v_inst_855_);
lean_closure_set(v___f_859_, 1, v_inst_856_);
v___x_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_860_, 0, v___f_857_);
lean_ctor_set(v___x_860_, 1, v___f_858_);
lean_ctor_set(v___x_860_, 2, v___f_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem(lean_object* v_00_u03b1_861_, lean_object* v_00_u03b2_862_, lean_object* v_inst_863_, lean_object* v_inst_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(v_inst_863_, v_inst_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_866_, lean_object* v_inst_867_, lean_object* v_m_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_buckets_870_; lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_buckets_870_ = lean_ctor_get(v_m_868_, 1);
v___x_871_ = lean_unsigned_to_nat(0u);
v___x_872_ = lean_array_get_size(v_buckets_870_);
v___x_873_ = lean_nat_dec_lt(v___x_871_, v___x_872_);
if (v___x_873_ == 0)
{
lean_object* v___x_874_; 
lean_dec(v_a_869_);
lean_dec_ref(v_inst_867_);
lean_dec_ref(v_inst_866_);
v___x_874_ = lean_box(0);
return v___x_874_;
}
else
{
lean_object* v___x_875_; 
v___x_875_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_866_, v_inst_867_, v_m_868_, v_a_869_);
return v___x_875_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_876_, lean_object* v_inst_877_, lean_object* v_m_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l_Std_HashMap_Raw_getKey_x3f___redArg(v_inst_876_, v_inst_877_, v_m_878_, v_a_879_);
lean_dec_ref(v_m_878_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_881_, lean_object* v_00_u03b2_882_, lean_object* v_inst_883_, lean_object* v_inst_884_, lean_object* v_m_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_buckets_887_; lean_object* v___x_888_; lean_object* v___x_889_; uint8_t v___x_890_; 
v_buckets_887_ = lean_ctor_get(v_m_885_, 1);
v___x_888_ = lean_unsigned_to_nat(0u);
v___x_889_ = lean_array_get_size(v_buckets_887_);
v___x_890_ = lean_nat_dec_lt(v___x_888_, v___x_889_);
if (v___x_890_ == 0)
{
lean_object* v___x_891_; 
lean_dec(v_a_886_);
lean_dec_ref(v_inst_884_);
lean_dec_ref(v_inst_883_);
v___x_891_ = lean_box(0);
return v___x_891_;
}
else
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_883_, v_inst_884_, v_m_885_, v_a_886_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_893_, lean_object* v_00_u03b2_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_m_897_, lean_object* v_a_898_){
_start:
{
lean_object* v_res_899_; 
v_res_899_ = l_Std_HashMap_Raw_getKey_x3f(v_00_u03b1_893_, v_00_u03b2_894_, v_inst_895_, v_inst_896_, v_m_897_, v_a_898_);
lean_dec_ref(v_m_897_);
return v_res_899_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg(lean_object* v_inst_900_, lean_object* v_inst_901_, lean_object* v_m_902_, lean_object* v_a_903_){
_start:
{
lean_object* v___x_904_; 
v___x_904_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_900_, v_inst_901_, v_m_902_, v_a_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_m_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l_Std_HashMap_Raw_getKey___redArg(v_inst_905_, v_inst_906_, v_m_907_, v_a_908_);
lean_dec_ref(v_m_907_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey(lean_object* v_00_u03b1_910_, lean_object* v_00_u03b2_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_m_914_, lean_object* v_a_915_, lean_object* v_h_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_912_, v_inst_913_, v_m_914_, v_a_915_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_918_, lean_object* v_00_u03b2_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_m_922_, lean_object* v_a_923_, lean_object* v_h_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Std_HashMap_Raw_getKey(v_00_u03b1_918_, v_00_u03b2_919_, v_inst_920_, v_inst_921_, v_m_922_, v_a_923_, v_h_924_);
lean_dec_ref(v_m_922_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg(lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_m_928_, lean_object* v_a_929_, lean_object* v_fallback_930_){
_start:
{
lean_object* v_buckets_931_; lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_buckets_931_ = lean_ctor_get(v_m_928_, 1);
v___x_932_ = lean_unsigned_to_nat(0u);
v___x_933_ = lean_array_get_size(v_buckets_931_);
v___x_934_ = lean_nat_dec_lt(v___x_932_, v___x_933_);
if (v___x_934_ == 0)
{
lean_dec(v_a_929_);
lean_dec_ref(v_inst_927_);
lean_dec_ref(v_inst_926_);
lean_inc(v_fallback_930_);
return v_fallback_930_;
}
else
{
lean_object* v___x_935_; 
v___x_935_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_926_, v_inst_927_, v_m_928_, v_a_929_, v_fallback_930_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_m_938_, lean_object* v_a_939_, lean_object* v_fallback_940_){
_start:
{
lean_object* v_res_941_; 
v_res_941_ = l_Std_HashMap_Raw_getKeyD___redArg(v_inst_936_, v_inst_937_, v_m_938_, v_a_939_, v_fallback_940_);
lean_dec(v_fallback_940_);
lean_dec_ref(v_m_938_);
return v_res_941_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD(lean_object* v_00_u03b1_942_, lean_object* v_00_u03b2_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_m_946_, lean_object* v_a_947_, lean_object* v_fallback_948_){
_start:
{
lean_object* v_buckets_949_; lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_buckets_949_ = lean_ctor_get(v_m_946_, 1);
v___x_950_ = lean_unsigned_to_nat(0u);
v___x_951_ = lean_array_get_size(v_buckets_949_);
v___x_952_ = lean_nat_dec_lt(v___x_950_, v___x_951_);
if (v___x_952_ == 0)
{
lean_dec(v_a_947_);
lean_dec_ref(v_inst_945_);
lean_dec_ref(v_inst_944_);
lean_inc(v_fallback_948_);
return v_fallback_948_;
}
else
{
lean_object* v___x_953_; 
v___x_953_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_944_, v_inst_945_, v_m_946_, v_a_947_, v_fallback_948_);
return v___x_953_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_954_, lean_object* v_00_u03b2_955_, lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_m_958_, lean_object* v_a_959_, lean_object* v_fallback_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Std_HashMap_Raw_getKeyD(v_00_u03b1_954_, v_00_u03b2_955_, v_inst_956_, v_inst_957_, v_m_958_, v_a_959_, v_fallback_960_);
lean_dec(v_fallback_960_);
lean_dec_ref(v_m_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg(lean_object* v_inst_962_, lean_object* v_inst_963_, lean_object* v_inst_964_, lean_object* v_m_965_, lean_object* v_a_966_){
_start:
{
lean_object* v_buckets_967_; lean_object* v___x_968_; lean_object* v___x_969_; uint8_t v___x_970_; 
v_buckets_967_ = lean_ctor_get(v_m_965_, 1);
v___x_968_ = lean_unsigned_to_nat(0u);
v___x_969_ = lean_array_get_size(v_buckets_967_);
v___x_970_ = lean_nat_dec_lt(v___x_968_, v___x_969_);
if (v___x_970_ == 0)
{
lean_dec(v_a_966_);
lean_dec_ref(v_inst_963_);
lean_dec_ref(v_inst_962_);
lean_inc(v_inst_964_);
return v_inst_964_;
}
else
{
lean_object* v___x_971_; 
v___x_971_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_962_, v_inst_963_, v_inst_964_, v_m_965_, v_a_966_);
return v___x_971_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_972_, lean_object* v_inst_973_, lean_object* v_inst_974_, lean_object* v_m_975_, lean_object* v_a_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_HashMap_Raw_getKey_x21___redArg(v_inst_972_, v_inst_973_, v_inst_974_, v_m_975_, v_a_976_);
lean_dec_ref(v_m_975_);
lean_dec(v_inst_974_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21(lean_object* v_00_u03b1_978_, lean_object* v_00_u03b2_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_m_983_, lean_object* v_a_984_){
_start:
{
lean_object* v_buckets_985_; lean_object* v___x_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_buckets_985_ = lean_ctor_get(v_m_983_, 1);
v___x_986_ = lean_unsigned_to_nat(0u);
v___x_987_ = lean_array_get_size(v_buckets_985_);
v___x_988_ = lean_nat_dec_lt(v___x_986_, v___x_987_);
if (v___x_988_ == 0)
{
lean_dec(v_a_984_);
lean_dec_ref(v_inst_981_);
lean_dec_ref(v_inst_980_);
lean_inc(v_inst_982_);
return v_inst_982_;
}
else
{
lean_object* v___x_989_; 
v___x_989_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_980_, v_inst_981_, v_inst_982_, v_m_983_, v_a_984_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_990_, lean_object* v_00_u03b2_991_, lean_object* v_inst_992_, lean_object* v_inst_993_, lean_object* v_inst_994_, lean_object* v_m_995_, lean_object* v_a_996_){
_start:
{
lean_object* v_res_997_; 
v_res_997_ = l_Std_HashMap_Raw_getKey_x21(v_00_u03b1_990_, v_00_u03b2_991_, v_inst_992_, v_inst_993_, v_inst_994_, v_m_995_, v_a_996_);
lean_dec_ref(v_m_995_);
lean_dec(v_inst_994_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase___redArg(lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_m_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_buckets_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v_buckets_1002_ = lean_ctor_get(v_m_1000_, 1);
v___x_1003_ = lean_unsigned_to_nat(0u);
v___x_1004_ = lean_array_get_size(v_buckets_1002_);
v___x_1005_ = lean_nat_dec_lt(v___x_1003_, v___x_1004_);
if (v___x_1005_ == 0)
{
lean_dec(v_a_1001_);
lean_dec_ref(v_inst_999_);
lean_dec_ref(v_inst_998_);
return v_m_1000_;
}
else
{
lean_object* v___x_1006_; 
v___x_1006_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_998_, v_inst_999_, v_m_1000_, v_a_1001_);
return v___x_1006_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase(lean_object* v_00_u03b1_1007_, lean_object* v_00_u03b2_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_m_1011_, lean_object* v_a_1012_){
_start:
{
lean_object* v_buckets_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; uint8_t v___x_1016_; 
v_buckets_1013_ = lean_ctor_get(v_m_1011_, 1);
v___x_1014_ = lean_unsigned_to_nat(0u);
v___x_1015_ = lean_array_get_size(v_buckets_1013_);
v___x_1016_ = lean_nat_dec_lt(v___x_1014_, v___x_1015_);
if (v___x_1016_ == 0)
{
lean_dec(v_a_1012_);
lean_dec_ref(v_inst_1010_);
lean_dec_ref(v_inst_1009_);
return v_m_1011_;
}
else
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1009_, v_inst_1010_, v_m_1011_, v_a_1012_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg(lean_object* v_m_1018_){
_start:
{
lean_object* v_size_1019_; 
v_size_1019_ = lean_ctor_get(v_m_1018_, 0);
lean_inc(v_size_1019_);
return v_size_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg___boxed(lean_object* v_m_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Std_HashMap_Raw_size___redArg(v_m_1020_);
lean_dec_ref(v_m_1020_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size(lean_object* v_00_u03b1_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_m_1024_){
_start:
{
lean_object* v_size_1025_; 
v_size_1025_ = lean_ctor_get(v_m_1024_, 0);
lean_inc(v_size_1025_);
return v_size_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___boxed(lean_object* v_00_u03b1_1026_, lean_object* v_00_u03b2_1027_, lean_object* v_m_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Std_HashMap_Raw_size(v_00_u03b1_1026_, v_00_u03b2_1027_, v_m_1028_);
lean_dec_ref(v_m_1028_);
return v_res_1029_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty___redArg(lean_object* v_m_1030_){
_start:
{
lean_object* v_size_1031_; lean_object* v___x_1032_; uint8_t v___x_1033_; 
v_size_1031_ = lean_ctor_get(v_m_1030_, 0);
v___x_1032_ = lean_unsigned_to_nat(0u);
v___x_1033_ = lean_nat_dec_eq(v_size_1031_, v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1034_){
_start:
{
uint8_t v_res_1035_; lean_object* v_r_1036_; 
v_res_1035_ = l_Std_HashMap_Raw_isEmpty___redArg(v_m_1034_);
lean_dec_ref(v_m_1034_);
v_r_1036_ = lean_box(v_res_1035_);
return v_r_1036_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty(lean_object* v_00_u03b1_1037_, lean_object* v_00_u03b2_1038_, lean_object* v_m_1039_){
_start:
{
lean_object* v_size_1040_; lean_object* v___x_1041_; uint8_t v___x_1042_; 
v_size_1040_ = lean_ctor_get(v_m_1039_, 0);
v___x_1041_ = lean_unsigned_to_nat(0u);
v___x_1042_ = lean_nat_dec_eq(v_size_1040_, v___x_1041_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1043_, lean_object* v_00_u03b2_1044_, lean_object* v_m_1045_){
_start:
{
uint8_t v_res_1046_; lean_object* v_r_1047_; 
v_res_1046_ = l_Std_HashMap_Raw_isEmpty(v_00_u03b1_1043_, v_00_u03b2_1044_, v_m_1045_);
lean_dec_ref(v_m_1045_);
v_r_1047_ = lean_box(v_res_1046_);
return v_r_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0(lean_object* v_a_1048_, lean_object* v_b_1049_, lean_object* v_d_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1051_, 0, v_a_1048_);
lean_ctor_set(v___x_1051_, 1, v_d_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_a_1052_, lean_object* v_b_1053_, lean_object* v_d_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Std_HashMap_Raw_keys___redArg___lam__0(v_a_1052_, v_b_1053_, v_d_1054_);
lean_dec(v_b_1053_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__1(lean_object* v___x_1056_, lean_object* v___f_1057_, lean_object* v_l_1058_, lean_object* v_acc_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1056_, v___f_1057_, v_acc_1059_, v_l_1058_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg(lean_object* v_m_1084_){
_start:
{
lean_object* v___x_1085_; lean_object* v_buckets_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1085_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1086_ = lean_ctor_get(v_m_1084_, 1);
lean_inc_ref(v_buckets_1086_);
lean_dec_ref(v_m_1084_);
v___x_1087_ = lean_box(0);
v___x_1088_ = lean_array_get_size(v_buckets_1086_);
v___x_1089_ = lean_unsigned_to_nat(0u);
v___x_1090_ = lean_nat_dec_lt(v___x_1089_, v___x_1088_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v_buckets_1086_);
return v___x_1087_;
}
else
{
lean_object* v___f_1091_; size_t v___x_1092_; size_t v___x_1093_; lean_object* v___x_1094_; 
v___f_1091_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1092_ = lean_usize_of_nat(v___x_1088_);
v___x_1093_ = ((size_t)0ULL);
v___x_1094_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1085_, v___f_1091_, v_buckets_1086_, v___x_1092_, v___x_1093_, v___x_1087_);
return v___x_1094_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys(lean_object* v_00_u03b1_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_m_1097_){
_start:
{
lean_object* v___x_1098_; lean_object* v_buckets_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1098_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1099_ = lean_ctor_get(v_m_1097_, 1);
lean_inc_ref(v_buckets_1099_);
lean_dec_ref(v_m_1097_);
v___x_1100_ = lean_box(0);
v___x_1101_ = lean_array_get_size(v_buckets_1099_);
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_nat_dec_lt(v___x_1102_, v___x_1101_);
if (v___x_1103_ == 0)
{
lean_dec_ref(v_buckets_1099_);
return v___x_1100_;
}
else
{
lean_object* v___f_1104_; size_t v___x_1105_; size_t v___x_1106_; lean_object* v___x_1107_; 
v___f_1104_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1105_ = lean_usize_of_nat(v___x_1101_);
v___x_1106_ = ((size_t)0ULL);
v___x_1107_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1098_, v___f_1104_, v_buckets_1099_, v___x_1105_, v___x_1106_, v___x_1100_);
return v___x_1107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList___redArg(lean_object* v_inst_1112_, lean_object* v_inst_1113_, lean_object* v_l_1114_){
_start:
{
lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1116_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1116_ == 0)
{
lean_dec(v_l_1114_);
lean_dec_ref(v_inst_1113_);
lean_dec_ref(v_inst_1112_);
return v___x_1115_;
}
else
{
lean_object* v___f_1117_; lean_object* v___x_1118_; 
v___f_1117_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1118_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1117_, v_inst_1112_, v_inst_1113_, v___x_1115_, v_l_1114_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList(lean_object* v_00_u03b1_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_inst_1121_, lean_object* v_inst_1122_, lean_object* v_l_1123_){
_start:
{
lean_object* v___x_1124_; uint8_t v___x_1125_; 
v___x_1124_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1125_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1125_ == 0)
{
lean_dec(v_l_1123_);
lean_dec_ref(v_inst_1122_);
lean_dec_ref(v_inst_1121_);
return v___x_1124_;
}
else
{
lean_object* v___f_1126_; lean_object* v___x_1127_; 
v___f_1126_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1127_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1126_, v_inst_1121_, v_inst_1122_, v___x_1124_, v_l_1123_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList___redArg(lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_l_1130_){
_start:
{
lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1131_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1132_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1132_ == 0)
{
lean_dec(v_l_1130_);
lean_dec_ref(v_inst_1129_);
lean_dec_ref(v_inst_1128_);
return v___x_1131_;
}
else
{
lean_object* v___f_1133_; lean_object* v___x_1134_; 
v___f_1133_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1134_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1133_, v_inst_1128_, v_inst_1129_, v___x_1131_, v_l_1130_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList(lean_object* v_00_u03b1_1135_, lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_l_1138_){
_start:
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1140_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1140_ == 0)
{
lean_dec(v_l_1138_);
lean_dec_ref(v_inst_1137_);
lean_dec_ref(v_inst_1136_);
return v___x_1139_;
}
else
{
lean_object* v___f_1141_; lean_object* v___x_1142_; 
v___f_1141_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1141_, v_inst_1136_, v_inst_1137_, v___x_1139_, v_l_1138_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray___redArg(lean_object* v_inst_1147_, lean_object* v_inst_1148_, lean_object* v_a_1149_){
_start:
{
lean_object* v___x_1150_; uint8_t v___x_1151_; 
v___x_1150_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1151_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1151_ == 0)
{
lean_dec_ref(v_a_1149_);
lean_dec_ref(v_inst_1148_);
lean_dec_ref(v_inst_1147_);
return v___x_1150_;
}
else
{
lean_object* v___f_1152_; lean_object* v___x_1153_; 
v___f_1152_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1153_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1152_, v_inst_1147_, v_inst_1148_, v___x_1150_, v_a_1149_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray(lean_object* v_00_u03b1_1154_, lean_object* v_00_u03b2_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_, lean_object* v_a_1158_){
_start:
{
lean_object* v___x_1159_; uint8_t v___x_1160_; 
v___x_1159_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1160_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1160_ == 0)
{
lean_dec_ref(v_a_1158_);
lean_dec_ref(v_inst_1157_);
lean_dec_ref(v_inst_1156_);
return v___x_1159_;
}
else
{
lean_object* v___f_1161_; lean_object* v___x_1162_; 
v___f_1161_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1162_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1161_, v_inst_1156_, v_inst_1157_, v___x_1159_, v_a_1158_);
return v___x_1162_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter___redArg(lean_object* v_inst_1163_, lean_object* v_inst_1164_, lean_object* v_m_1165_, lean_object* v_a_1166_, lean_object* v_f_1167_){
_start:
{
lean_object* v_buckets_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; uint8_t v___x_1171_; 
v_buckets_1168_ = lean_ctor_get(v_m_1165_, 1);
v___x_1169_ = lean_unsigned_to_nat(0u);
v___x_1170_ = lean_array_get_size(v_buckets_1168_);
v___x_1171_ = lean_nat_dec_lt(v___x_1169_, v___x_1170_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
lean_dec_ref(v_f_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_m_1165_);
lean_dec_ref(v_inst_1164_);
lean_dec_ref(v_inst_1163_);
v___x_1172_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
v___x_1173_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1163_, v_inst_1164_, v_m_1165_, v_a_1166_, v_f_1167_);
return v___x_1173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter(lean_object* v_00_u03b1_1174_, lean_object* v_00_u03b2_1175_, lean_object* v_inst_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_m_1179_, lean_object* v_a_1180_, lean_object* v_f_1181_){
_start:
{
lean_object* v_buckets_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; uint8_t v___x_1185_; 
v_buckets_1182_ = lean_ctor_get(v_m_1179_, 1);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = lean_array_get_size(v_buckets_1182_);
v___x_1185_ = lean_nat_dec_lt(v___x_1183_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec_ref(v_f_1181_);
lean_dec(v_a_1180_);
lean_dec_ref(v_m_1179_);
lean_dec_ref(v_inst_1178_);
lean_dec_ref(v_inst_1176_);
v___x_1186_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1186_;
}
else
{
lean_object* v___x_1187_; 
v___x_1187_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1176_, v_inst_1178_, v_m_1179_, v_a_1180_, v_f_1181_);
return v___x_1187_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify___redArg(lean_object* v_inst_1188_, lean_object* v_inst_1189_, lean_object* v_m_1190_, lean_object* v_a_1191_, lean_object* v_f_1192_){
_start:
{
lean_object* v_buckets_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v_buckets_1193_ = lean_ctor_get(v_m_1190_, 1);
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_array_get_size(v_buckets_1193_);
v___x_1196_ = lean_nat_dec_lt(v___x_1194_, v___x_1195_);
if (v___x_1196_ == 0)
{
lean_object* v___x_1197_; 
lean_dec(v_f_1192_);
lean_dec(v_a_1191_);
lean_dec_ref(v_m_1190_);
lean_dec_ref(v_inst_1189_);
lean_dec_ref(v_inst_1188_);
v___x_1197_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1197_;
}
else
{
lean_object* v___x_1198_; 
v___x_1198_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1188_, v_inst_1189_, v_m_1190_, v_a_1191_, v_f_1192_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify(lean_object* v_00_u03b1_1199_, lean_object* v_00_u03b2_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_m_1204_, lean_object* v_a_1205_, lean_object* v_f_1206_){
_start:
{
lean_object* v_buckets_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; 
v_buckets_1207_ = lean_ctor_get(v_m_1204_, 1);
v___x_1208_ = lean_unsigned_to_nat(0u);
v___x_1209_ = lean_array_get_size(v_buckets_1207_);
v___x_1210_ = lean_nat_dec_lt(v___x_1208_, v___x_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; 
lean_dec(v_f_1206_);
lean_dec(v_a_1205_);
lean_dec_ref(v_m_1204_);
lean_dec_ref(v_inst_1203_);
lean_dec_ref(v_inst_1201_);
v___x_1211_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1211_;
}
else
{
lean_object* v___x_1212_; 
v___x_1212_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1201_, v_inst_1203_, v_m_1204_, v_a_1205_, v_f_1206_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__0(lean_object* v_a_1213_, lean_object* v_b_1214_, lean_object* v_d_1215_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v_a_1213_);
lean_ctor_set(v___x_1216_, 1, v_b_1214_);
v___x_1217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1217_, 0, v___x_1216_);
lean_ctor_set(v___x_1217_, 1, v_d_1215_);
return v___x_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__1(lean_object* v___x_1218_, lean_object* v___f_1219_, lean_object* v_l_1220_, lean_object* v_acc_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1218_, v___f_1219_, v_acc_1221_, v_l_1220_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg(lean_object* v_m_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v_buckets_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1228_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1229_ = lean_ctor_get(v_m_1227_, 1);
lean_inc_ref(v_buckets_1229_);
lean_dec_ref(v_m_1227_);
v___x_1230_ = lean_box(0);
v___x_1231_ = lean_array_get_size(v_buckets_1229_);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = lean_nat_dec_lt(v___x_1232_, v___x_1231_);
if (v___x_1233_ == 0)
{
lean_dec_ref(v_buckets_1229_);
return v___x_1230_;
}
else
{
lean_object* v___f_1234_; size_t v___x_1235_; size_t v___x_1236_; lean_object* v___x_1237_; 
v___f_1234_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1235_ = lean_usize_of_nat(v___x_1231_);
v___x_1236_ = ((size_t)0ULL);
v___x_1237_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1228_, v___f_1234_, v_buckets_1229_, v___x_1235_, v___x_1236_, v___x_1230_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList(lean_object* v_00_u03b1_1238_, lean_object* v_00_u03b2_1239_, lean_object* v_m_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v_buckets_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; uint8_t v___x_1246_; 
v___x_1241_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1242_ = lean_ctor_get(v_m_1240_, 1);
lean_inc_ref(v_buckets_1242_);
lean_dec_ref(v_m_1240_);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_array_get_size(v_buckets_1242_);
v___x_1245_ = lean_unsigned_to_nat(0u);
v___x_1246_ = lean_nat_dec_lt(v___x_1245_, v___x_1244_);
if (v___x_1246_ == 0)
{
lean_dec_ref(v_buckets_1242_);
return v___x_1243_;
}
else
{
lean_object* v___f_1247_; size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v___f_1247_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1248_ = lean_usize_of_nat(v___x_1244_);
v___x_1249_ = ((size_t)0ULL);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1241_, v___f_1247_, v_buckets_1242_, v___x_1248_, v___x_1249_, v___x_1243_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg___lam__0(lean_object* v_inst_1251_, lean_object* v_f_1252_, lean_object* v_acc_1253_, lean_object* v_l_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1251_, v_f_1252_, v_acc_1253_, v_l_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg(lean_object* v_inst_1256_, lean_object* v_f_1257_, lean_object* v_init_1258_, lean_object* v_b_1259_){
_start:
{
lean_object* v_buckets_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v_buckets_1260_ = lean_ctor_get(v_b_1259_, 1);
lean_inc_ref(v_buckets_1260_);
lean_dec_ref(v_b_1259_);
v___x_1261_ = lean_unsigned_to_nat(0u);
v___x_1262_ = lean_array_get_size(v_buckets_1260_);
v___x_1263_ = lean_nat_dec_lt(v___x_1261_, v___x_1262_);
if (v___x_1263_ == 0)
{
lean_object* v_toApplicative_1264_; lean_object* v_toPure_1265_; lean_object* v___x_1266_; 
lean_dec_ref(v_buckets_1260_);
lean_dec(v_f_1257_);
v_toApplicative_1264_ = lean_ctor_get(v_inst_1256_, 0);
lean_inc_ref(v_toApplicative_1264_);
lean_dec_ref(v_inst_1256_);
v_toPure_1265_ = lean_ctor_get(v_toApplicative_1264_, 1);
lean_inc(v_toPure_1265_);
lean_dec_ref(v_toApplicative_1264_);
v___x_1266_ = lean_apply_2(v_toPure_1265_, lean_box(0), v_init_1258_);
return v___x_1266_;
}
else
{
lean_object* v___f_1267_; uint8_t v___x_1268_; 
lean_inc_ref(v_inst_1256_);
v___f_1267_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1267_, 0, v_inst_1256_);
lean_closure_set(v___f_1267_, 1, v_f_1257_);
v___x_1268_ = lean_nat_dec_le(v___x_1262_, v___x_1262_);
if (v___x_1268_ == 0)
{
if (v___x_1263_ == 0)
{
lean_object* v_toApplicative_1269_; lean_object* v_toPure_1270_; lean_object* v___x_1271_; 
lean_dec_ref(v___f_1267_);
lean_dec_ref(v_buckets_1260_);
v_toApplicative_1269_ = lean_ctor_get(v_inst_1256_, 0);
lean_inc_ref(v_toApplicative_1269_);
lean_dec_ref(v_inst_1256_);
v_toPure_1270_ = lean_ctor_get(v_toApplicative_1269_, 1);
lean_inc(v_toPure_1270_);
lean_dec_ref(v_toApplicative_1269_);
v___x_1271_ = lean_apply_2(v_toPure_1270_, lean_box(0), v_init_1258_);
return v___x_1271_;
}
else
{
size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v___x_1272_ = ((size_t)0ULL);
v___x_1273_ = lean_usize_of_nat(v___x_1262_);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1256_, v___f_1267_, v_buckets_1260_, v___x_1272_, v___x_1273_, v_init_1258_);
return v___x_1274_;
}
}
else
{
size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = lean_usize_of_nat(v___x_1262_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1256_, v___f_1267_, v_buckets_1260_, v___x_1275_, v___x_1276_, v_init_1258_);
return v___x_1277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object* v_00_u03b1_1278_, lean_object* v_00_u03b2_1279_, lean_object* v_m_1280_, lean_object* v_inst_1281_, lean_object* v_00_u03b3_1282_, lean_object* v_f_1283_, lean_object* v_init_1284_, lean_object* v_b_1285_){
_start:
{
lean_object* v_buckets_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_buckets_1286_ = lean_ctor_get(v_b_1285_, 1);
lean_inc_ref(v_buckets_1286_);
lean_dec_ref(v_b_1285_);
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = lean_array_get_size(v_buckets_1286_);
v___x_1289_ = lean_nat_dec_lt(v___x_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v_toApplicative_1290_; lean_object* v_toPure_1291_; lean_object* v___x_1292_; 
lean_dec_ref(v_buckets_1286_);
lean_dec(v_f_1283_);
v_toApplicative_1290_ = lean_ctor_get(v_inst_1281_, 0);
lean_inc_ref(v_toApplicative_1290_);
lean_dec_ref(v_inst_1281_);
v_toPure_1291_ = lean_ctor_get(v_toApplicative_1290_, 1);
lean_inc(v_toPure_1291_);
lean_dec_ref(v_toApplicative_1290_);
v___x_1292_ = lean_apply_2(v_toPure_1291_, lean_box(0), v_init_1284_);
return v___x_1292_;
}
else
{
lean_object* v___f_1293_; uint8_t v___x_1294_; 
lean_inc_ref(v_inst_1281_);
v___f_1293_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1293_, 0, v_inst_1281_);
lean_closure_set(v___f_1293_, 1, v_f_1283_);
v___x_1294_ = lean_nat_dec_le(v___x_1288_, v___x_1288_);
if (v___x_1294_ == 0)
{
if (v___x_1289_ == 0)
{
lean_object* v_toApplicative_1295_; lean_object* v_toPure_1296_; lean_object* v___x_1297_; 
lean_dec_ref(v___f_1293_);
lean_dec_ref(v_buckets_1286_);
v_toApplicative_1295_ = lean_ctor_get(v_inst_1281_, 0);
lean_inc_ref(v_toApplicative_1295_);
lean_dec_ref(v_inst_1281_);
v_toPure_1296_ = lean_ctor_get(v_toApplicative_1295_, 1);
lean_inc(v_toPure_1296_);
lean_dec_ref(v_toApplicative_1295_);
v___x_1297_ = lean_apply_2(v_toPure_1296_, lean_box(0), v_init_1284_);
return v___x_1297_;
}
else
{
size_t v___x_1298_; size_t v___x_1299_; lean_object* v___x_1300_; 
v___x_1298_ = ((size_t)0ULL);
v___x_1299_ = lean_usize_of_nat(v___x_1288_);
v___x_1300_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1281_, v___f_1293_, v_buckets_1286_, v___x_1298_, v___x_1299_, v_init_1284_);
return v___x_1300_;
}
}
else
{
size_t v___x_1301_; size_t v___x_1302_; lean_object* v___x_1303_; 
v___x_1301_ = ((size_t)0ULL);
v___x_1302_ = lean_usize_of_nat(v___x_1288_);
v___x_1303_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1281_, v___f_1293_, v_buckets_1286_, v___x_1301_, v___x_1302_, v_init_1284_);
return v___x_1303_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object* v_f_1304_, lean_object* v_x1_1305_, lean_object* v_x2_1306_, lean_object* v_x3_1307_){
_start:
{
lean_object* v___x_1308_; 
v___x_1308_ = lean_apply_3(v_f_1304_, v_x1_1305_, v_x2_1306_, v_x3_1307_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__1(lean_object* v___x_1309_, lean_object* v___f_1310_, lean_object* v_acc_1311_, lean_object* v_l_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1309_, v___f_1310_, v_acc_1311_, v_l_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object* v_f_1314_, lean_object* v_init_1315_, lean_object* v_b_1316_){
_start:
{
lean_object* v___x_1317_; lean_object* v_buckets_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1317_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1318_ = lean_ctor_get(v_b_1316_, 1);
lean_inc_ref(v_buckets_1318_);
lean_dec_ref(v_b_1316_);
v___x_1319_ = lean_unsigned_to_nat(0u);
v___x_1320_ = lean_array_get_size(v_buckets_1318_);
v___x_1321_ = lean_nat_dec_lt(v___x_1319_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_dec_ref(v_buckets_1318_);
lean_dec(v_f_1314_);
return v_init_1315_;
}
else
{
lean_object* v___f_1322_; lean_object* v___f_1323_; uint8_t v___x_1324_; 
v___f_1322_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1322_, 0, v_f_1314_);
v___f_1323_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1323_, 0, v___x_1317_);
lean_closure_set(v___f_1323_, 1, v___f_1322_);
v___x_1324_ = lean_nat_dec_le(v___x_1320_, v___x_1320_);
if (v___x_1324_ == 0)
{
if (v___x_1321_ == 0)
{
lean_dec_ref(v___f_1323_);
lean_dec_ref(v_buckets_1318_);
return v_init_1315_;
}
else
{
size_t v___x_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v___x_1325_ = ((size_t)0ULL);
v___x_1326_ = lean_usize_of_nat(v___x_1320_);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1317_, v___f_1323_, v_buckets_1318_, v___x_1325_, v___x_1326_, v_init_1315_);
return v___x_1327_;
}
}
else
{
size_t v___x_1328_; size_t v___x_1329_; lean_object* v___x_1330_; 
v___x_1328_ = ((size_t)0ULL);
v___x_1329_ = lean_usize_of_nat(v___x_1320_);
v___x_1330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1317_, v___f_1323_, v_buckets_1318_, v___x_1328_, v___x_1329_, v_init_1315_);
return v___x_1330_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object* v_00_u03b1_1331_, lean_object* v_00_u03b2_1332_, lean_object* v_00_u03b3_1333_, lean_object* v_f_1334_, lean_object* v_init_1335_, lean_object* v_b_1336_){
_start:
{
lean_object* v___x_1337_; lean_object* v_buckets_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1337_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1338_ = lean_ctor_get(v_b_1336_, 1);
lean_inc_ref(v_buckets_1338_);
lean_dec_ref(v_b_1336_);
v___x_1339_ = lean_unsigned_to_nat(0u);
v___x_1340_ = lean_array_get_size(v_buckets_1338_);
v___x_1341_ = lean_nat_dec_lt(v___x_1339_, v___x_1340_);
if (v___x_1341_ == 0)
{
lean_dec_ref(v_buckets_1338_);
lean_dec(v_f_1334_);
return v_init_1335_;
}
else
{
lean_object* v___f_1342_; lean_object* v___f_1343_; uint8_t v___x_1344_; 
v___f_1342_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1342_, 0, v_f_1334_);
v___f_1343_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1343_, 0, v___x_1337_);
lean_closure_set(v___f_1343_, 1, v___f_1342_);
v___x_1344_ = lean_nat_dec_le(v___x_1340_, v___x_1340_);
if (v___x_1344_ == 0)
{
if (v___x_1341_ == 0)
{
lean_dec_ref(v___f_1343_);
lean_dec_ref(v_buckets_1338_);
return v_init_1335_;
}
else
{
size_t v___x_1345_; size_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = lean_usize_of_nat(v___x_1340_);
v___x_1347_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1337_, v___f_1343_, v_buckets_1338_, v___x_1345_, v___x_1346_, v_init_1335_);
return v___x_1347_;
}
}
else
{
size_t v___x_1348_; size_t v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = ((size_t)0ULL);
v___x_1349_ = lean_usize_of_nat(v___x_1340_);
v___x_1350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1337_, v___f_1343_, v_buckets_1338_, v___x_1348_, v___x_1349_, v_init_1335_);
return v___x_1350_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object* v_f_1351_, lean_object* v_x_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_apply_2(v_f_1351_, v___y_1353_, v___y_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__1(lean_object* v_inst_1356_, lean_object* v___f_1357_, lean_object* v_x_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1360_ = lean_box(0);
v___x_1361_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1356_, v___f_1357_, v___x_1360_, v___y_1359_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object* v_inst_1362_, lean_object* v_f_1363_, lean_object* v_b_1364_){
_start:
{
lean_object* v_buckets_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_buckets_1365_ = lean_ctor_get(v_b_1364_, 1);
lean_inc_ref(v_buckets_1365_);
lean_dec_ref(v_b_1364_);
v___x_1366_ = lean_unsigned_to_nat(0u);
v___x_1367_ = lean_array_get_size(v_buckets_1365_);
v___x_1368_ = lean_box(0);
v___x_1369_ = lean_nat_dec_lt(v___x_1366_, v___x_1367_);
if (v___x_1369_ == 0)
{
lean_object* v_toApplicative_1370_; lean_object* v_toPure_1371_; lean_object* v___x_1372_; 
lean_dec_ref(v_buckets_1365_);
lean_dec(v_f_1363_);
v_toApplicative_1370_ = lean_ctor_get(v_inst_1362_, 0);
lean_inc_ref(v_toApplicative_1370_);
lean_dec_ref(v_inst_1362_);
v_toPure_1371_ = lean_ctor_get(v_toApplicative_1370_, 1);
lean_inc(v_toPure_1371_);
lean_dec_ref(v_toApplicative_1370_);
v___x_1372_ = lean_apply_2(v_toPure_1371_, lean_box(0), v___x_1368_);
return v___x_1372_;
}
else
{
lean_object* v___f_1373_; lean_object* v___f_1374_; uint8_t v___x_1375_; 
v___f_1373_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1373_, 0, v_f_1363_);
lean_inc_ref(v_inst_1362_);
v___f_1374_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1374_, 0, v_inst_1362_);
lean_closure_set(v___f_1374_, 1, v___f_1373_);
v___x_1375_ = lean_nat_dec_le(v___x_1367_, v___x_1367_);
if (v___x_1375_ == 0)
{
if (v___x_1369_ == 0)
{
lean_object* v_toApplicative_1376_; lean_object* v_toPure_1377_; lean_object* v___x_1378_; 
lean_dec_ref(v___f_1374_);
lean_dec_ref(v_buckets_1365_);
v_toApplicative_1376_ = lean_ctor_get(v_inst_1362_, 0);
lean_inc_ref(v_toApplicative_1376_);
lean_dec_ref(v_inst_1362_);
v_toPure_1377_ = lean_ctor_get(v_toApplicative_1376_, 1);
lean_inc(v_toPure_1377_);
lean_dec_ref(v_toApplicative_1376_);
v___x_1378_ = lean_apply_2(v_toPure_1377_, lean_box(0), v___x_1368_);
return v___x_1378_;
}
else
{
size_t v___x_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
v___x_1379_ = ((size_t)0ULL);
v___x_1380_ = lean_usize_of_nat(v___x_1367_);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1362_, v___f_1374_, v_buckets_1365_, v___x_1379_, v___x_1380_, v___x_1368_);
return v___x_1381_;
}
}
else
{
size_t v___x_1382_; size_t v___x_1383_; lean_object* v___x_1384_; 
v___x_1382_ = ((size_t)0ULL);
v___x_1383_ = lean_usize_of_nat(v___x_1367_);
v___x_1384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1362_, v___f_1374_, v_buckets_1365_, v___x_1382_, v___x_1383_, v___x_1368_);
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object* v_00_u03b1_1385_, lean_object* v_00_u03b2_1386_, lean_object* v_m_1387_, lean_object* v_inst_1388_, lean_object* v_f_1389_, lean_object* v_b_1390_){
_start:
{
lean_object* v_buckets_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_buckets_1391_ = lean_ctor_get(v_b_1390_, 1);
lean_inc_ref(v_buckets_1391_);
lean_dec_ref(v_b_1390_);
v___x_1392_ = lean_unsigned_to_nat(0u);
v___x_1393_ = lean_array_get_size(v_buckets_1391_);
v___x_1394_ = lean_box(0);
v___x_1395_ = lean_nat_dec_lt(v___x_1392_, v___x_1393_);
if (v___x_1395_ == 0)
{
lean_object* v_toApplicative_1396_; lean_object* v_toPure_1397_; lean_object* v___x_1398_; 
lean_dec_ref(v_buckets_1391_);
lean_dec(v_f_1389_);
v_toApplicative_1396_ = lean_ctor_get(v_inst_1388_, 0);
lean_inc_ref(v_toApplicative_1396_);
lean_dec_ref(v_inst_1388_);
v_toPure_1397_ = lean_ctor_get(v_toApplicative_1396_, 1);
lean_inc(v_toPure_1397_);
lean_dec_ref(v_toApplicative_1396_);
v___x_1398_ = lean_apply_2(v_toPure_1397_, lean_box(0), v___x_1394_);
return v___x_1398_;
}
else
{
lean_object* v___f_1399_; lean_object* v___f_1400_; uint8_t v___x_1401_; 
v___f_1399_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1399_, 0, v_f_1389_);
lean_inc_ref(v_inst_1388_);
v___f_1400_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1400_, 0, v_inst_1388_);
lean_closure_set(v___f_1400_, 1, v___f_1399_);
v___x_1401_ = lean_nat_dec_le(v___x_1393_, v___x_1393_);
if (v___x_1401_ == 0)
{
if (v___x_1395_ == 0)
{
lean_object* v_toApplicative_1402_; lean_object* v_toPure_1403_; lean_object* v___x_1404_; 
lean_dec_ref(v___f_1400_);
lean_dec_ref(v_buckets_1391_);
v_toApplicative_1402_ = lean_ctor_get(v_inst_1388_, 0);
lean_inc_ref(v_toApplicative_1402_);
lean_dec_ref(v_inst_1388_);
v_toPure_1403_ = lean_ctor_get(v_toApplicative_1402_, 1);
lean_inc(v_toPure_1403_);
lean_dec_ref(v_toApplicative_1402_);
v___x_1404_ = lean_apply_2(v_toPure_1403_, lean_box(0), v___x_1394_);
return v___x_1404_;
}
else
{
size_t v___x_1405_; size_t v___x_1406_; lean_object* v___x_1407_; 
v___x_1405_ = ((size_t)0ULL);
v___x_1406_ = lean_usize_of_nat(v___x_1393_);
v___x_1407_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1388_, v___f_1400_, v_buckets_1391_, v___x_1405_, v___x_1406_, v___x_1394_);
return v___x_1407_;
}
}
else
{
size_t v___x_1408_; size_t v___x_1409_; lean_object* v___x_1410_; 
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = lean_usize_of_nat(v___x_1393_);
v___x_1410_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1388_, v___f_1400_, v_buckets_1391_, v___x_1408_, v___x_1409_, v___x_1394_);
return v___x_1410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg___lam__0(lean_object* v_inst_1411_, lean_object* v_f_1412_, lean_object* v_a_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1411_, v_f_1412_, v_a_1413_, v___y_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object* v_inst_1417_, lean_object* v_f_1418_, lean_object* v_init_1419_, lean_object* v_b_1420_){
_start:
{
lean_object* v_buckets_1421_; lean_object* v___f_1422_; size_t v_sz_1423_; size_t v___x_1424_; lean_object* v___x_1425_; 
v_buckets_1421_ = lean_ctor_get(v_b_1420_, 1);
lean_inc_ref(v_buckets_1421_);
lean_dec_ref(v_b_1420_);
lean_inc_ref(v_inst_1417_);
v___f_1422_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1422_, 0, v_inst_1417_);
lean_closure_set(v___f_1422_, 1, v_f_1418_);
v_sz_1423_ = lean_array_size(v_buckets_1421_);
v___x_1424_ = ((size_t)0ULL);
v___x_1425_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1417_, v_buckets_1421_, v___f_1422_, v_sz_1423_, v___x_1424_, v_init_1419_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object* v_00_u03b1_1426_, lean_object* v_00_u03b2_1427_, lean_object* v_m_1428_, lean_object* v_inst_1429_, lean_object* v_00_u03b3_1430_, lean_object* v_f_1431_, lean_object* v_init_1432_, lean_object* v_b_1433_){
_start:
{
lean_object* v_buckets_1434_; lean_object* v___f_1435_; size_t v_sz_1436_; size_t v___x_1437_; lean_object* v___x_1438_; 
v_buckets_1434_ = lean_ctor_get(v_b_1433_, 1);
lean_inc_ref(v_buckets_1434_);
lean_dec_ref(v_b_1433_);
lean_inc_ref(v_inst_1429_);
v___f_1435_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1435_, 0, v_inst_1429_);
lean_closure_set(v___f_1435_, 1, v_f_1431_);
v_sz_1436_ = lean_array_size(v_buckets_1434_);
v___x_1437_ = ((size_t)0ULL);
v___x_1438_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1429_, v_buckets_1434_, v___f_1435_, v_sz_1436_, v___x_1437_, v_init_1432_);
return v___x_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1439_, lean_object* v_x_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___y_1441_);
lean_ctor_set(v___x_1443_, 1, v___y_1442_);
v___x_1444_ = lean_apply_1(v_f_1439_, v___x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1445_, lean_object* v_m_1446_, lean_object* v_f_1447_){
_start:
{
lean_object* v_buckets_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; uint8_t v___x_1452_; 
v_buckets_1448_ = lean_ctor_get(v_m_1446_, 1);
lean_inc_ref(v_buckets_1448_);
lean_dec_ref(v_m_1446_);
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = lean_array_get_size(v_buckets_1448_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_nat_dec_lt(v___x_1449_, v___x_1450_);
if (v___x_1452_ == 0)
{
lean_object* v_toApplicative_1453_; lean_object* v_toPure_1454_; lean_object* v___x_1455_; 
lean_dec_ref(v_buckets_1448_);
lean_dec(v_f_1447_);
v_toApplicative_1453_ = lean_ctor_get(v_inst_1445_, 0);
lean_inc_ref(v_toApplicative_1453_);
lean_dec_ref(v_inst_1445_);
v_toPure_1454_ = lean_ctor_get(v_toApplicative_1453_, 1);
lean_inc(v_toPure_1454_);
lean_dec_ref(v_toApplicative_1453_);
v___x_1455_ = lean_apply_2(v_toPure_1454_, lean_box(0), v___x_1451_);
return v___x_1455_;
}
else
{
lean_object* v___f_1456_; lean_object* v___f_1457_; uint8_t v___x_1458_; 
v___f_1456_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1456_, 0, v_f_1447_);
lean_inc_ref(v_inst_1445_);
v___f_1457_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1457_, 0, v_inst_1445_);
lean_closure_set(v___f_1457_, 1, v___f_1456_);
v___x_1458_ = lean_nat_dec_le(v___x_1450_, v___x_1450_);
if (v___x_1458_ == 0)
{
if (v___x_1452_ == 0)
{
lean_object* v_toApplicative_1459_; lean_object* v_toPure_1460_; lean_object* v___x_1461_; 
lean_dec_ref(v___f_1457_);
lean_dec_ref(v_buckets_1448_);
v_toApplicative_1459_ = lean_ctor_get(v_inst_1445_, 0);
lean_inc_ref(v_toApplicative_1459_);
lean_dec_ref(v_inst_1445_);
v_toPure_1460_ = lean_ctor_get(v_toApplicative_1459_, 1);
lean_inc(v_toPure_1460_);
lean_dec_ref(v_toApplicative_1459_);
v___x_1461_ = lean_apply_2(v_toPure_1460_, lean_box(0), v___x_1451_);
return v___x_1461_;
}
else
{
size_t v___x_1462_; size_t v___x_1463_; lean_object* v___x_1464_; 
v___x_1462_ = ((size_t)0ULL);
v___x_1463_ = lean_usize_of_nat(v___x_1450_);
v___x_1464_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1445_, v___f_1457_, v_buckets_1448_, v___x_1462_, v___x_1463_, v___x_1451_);
return v___x_1464_;
}
}
else
{
size_t v___x_1465_; size_t v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = ((size_t)0ULL);
v___x_1466_ = lean_usize_of_nat(v___x_1450_);
v___x_1467_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1445_, v___f_1457_, v_buckets_1448_, v___x_1465_, v___x_1466_, v___x_1451_);
return v___x_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1468_){
_start:
{
lean_object* v___f_1469_; 
v___f_1469_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1469_, 0, v_inst_1468_);
return v___f_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1470_, lean_object* v_00_u03b2_1471_, lean_object* v_m_1472_, lean_object* v_inst_1473_){
_start:
{
lean_object* v___f_1474_; 
v___f_1474_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1474_, 0, v_inst_1473_);
return v___f_1474_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1475_, lean_object* v_a_1476_, lean_object* v_b_1477_, lean_object* v_acc_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_a_1476_);
lean_ctor_set(v___x_1479_, 1, v_b_1477_);
v___x_1480_ = lean_apply_2(v_f_1475_, v___x_1479_, v_acc_1478_);
return v___x_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1481_, lean_object* v___f_1482_, lean_object* v_a_1483_, lean_object* v_x_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1481_, v___f_1482_, v_a_1483_, v___y_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1487_, lean_object* v_00_u03b2_1488_, lean_object* v_m_1489_, lean_object* v_init_1490_, lean_object* v_f_1491_){
_start:
{
lean_object* v_buckets_1492_; lean_object* v___f_1493_; lean_object* v___f_1494_; size_t v_sz_1495_; size_t v___x_1496_; lean_object* v___x_1497_; 
v_buckets_1492_ = lean_ctor_get(v_m_1489_, 1);
lean_inc_ref(v_buckets_1492_);
lean_dec_ref(v_m_1489_);
v___f_1493_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1493_, 0, v_f_1491_);
lean_inc_ref(v_inst_1487_);
v___f_1494_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1494_, 0, v_inst_1487_);
lean_closure_set(v___f_1494_, 1, v___f_1493_);
v_sz_1495_ = lean_array_size(v_buckets_1492_);
v___x_1496_ = ((size_t)0ULL);
v___x_1497_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1487_, v_buckets_1492_, v___f_1494_, v_sz_1495_, v___x_1496_, v_init_1490_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1498_){
_start:
{
lean_object* v___f_1499_; 
v___f_1499_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1499_, 0, v_inst_1498_);
return v___f_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1500_, lean_object* v_00_u03b2_1501_, lean_object* v_m_1502_, lean_object* v_inst_1503_){
_start:
{
lean_object* v___f_1504_; 
v___f_1504_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1504_, 0, v_inst_1503_);
return v___f_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object* v_p_1505_, lean_object* v___x_1506_, lean_object* v___x_1507_, lean_object* v_a_1508_, lean_object* v_b_1509_, lean_object* v_acc_1510_){
_start:
{
lean_object* v___x_1511_; uint8_t v___x_1512_; 
v___x_1511_ = lean_apply_2(v_p_1505_, v_a_1508_, v_b_1509_);
v___x_1512_ = lean_unbox(v___x_1511_);
if (v___x_1512_ == 0)
{
lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; 
lean_dec_ref(v___x_1507_);
v___x_1513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1511_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1506_);
v___x_1515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
return v___x_1515_;
}
else
{
lean_object* v___x_1516_; 
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1507_);
return v___x_1516_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1517_, lean_object* v___x_1518_, lean_object* v___x_1519_, lean_object* v_a_1520_, lean_object* v_b_1521_, lean_object* v_acc_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l_Std_HashMap_Raw_all___redArg___lam__0(v_p_1517_, v___x_1518_, v___x_1519_, v_a_1520_, v_b_1521_, v_acc_1522_);
lean_dec_ref(v_acc_1522_);
return v_res_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__1(lean_object* v___x_1524_, lean_object* v___f_1525_, lean_object* v_a_1526_, lean_object* v_x_1527_, lean_object* v___y_1528_){
_start:
{
lean_object* v___x_1529_; 
v___x_1529_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1524_, v___f_1525_, v_a_1526_, v___y_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all___redArg(lean_object* v_m_1533_, lean_object* v_p_1534_){
_start:
{
lean_object* v___x_1535_; lean_object* v_buckets_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___f_1539_; lean_object* v___f_1540_; size_t v_sz_1541_; size_t v___x_1542_; lean_object* v___x_1543_; lean_object* v_fst_1544_; 
v___x_1535_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1536_ = lean_ctor_get(v_m_1533_, 1);
lean_inc_ref(v_buckets_1536_);
lean_dec_ref(v_m_1533_);
v___x_1537_ = lean_box(0);
v___x_1538_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1539_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1539_, 0, v_p_1534_);
lean_closure_set(v___f_1539_, 1, v___x_1537_);
lean_closure_set(v___f_1539_, 2, v___x_1538_);
v___f_1540_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1540_, 0, v___x_1535_);
lean_closure_set(v___f_1540_, 1, v___f_1539_);
v_sz_1541_ = lean_array_size(v_buckets_1536_);
v___x_1542_ = ((size_t)0ULL);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1535_, v_buckets_1536_, v___f_1540_, v_sz_1541_, v___x_1542_, v___x_1538_);
v_fst_1544_ = lean_ctor_get(v___x_1543_, 0);
lean_inc(v_fst_1544_);
lean_dec(v___x_1543_);
if (lean_obj_tag(v_fst_1544_) == 0)
{
uint8_t v___x_1545_; 
v___x_1545_ = 1;
return v___x_1545_;
}
else
{
lean_object* v_val_1546_; uint8_t v___x_1547_; 
v_val_1546_ = lean_ctor_get(v_fst_1544_, 0);
lean_inc(v_val_1546_);
lean_dec_ref(v_fst_1544_);
v___x_1547_ = lean_unbox(v_val_1546_);
lean_dec(v_val_1546_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___boxed(lean_object* v_m_1548_, lean_object* v_p_1549_){
_start:
{
uint8_t v_res_1550_; lean_object* v_r_1551_; 
v_res_1550_ = l_Std_HashMap_Raw_all___redArg(v_m_1548_, v_p_1549_);
v_r_1551_ = lean_box(v_res_1550_);
return v_r_1551_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all(lean_object* v_00_u03b1_1552_, lean_object* v_00_u03b2_1553_, lean_object* v_m_1554_, lean_object* v_p_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v_buckets_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___f_1560_; lean_object* v___f_1561_; size_t v_sz_1562_; size_t v___x_1563_; lean_object* v___x_1564_; lean_object* v_fst_1565_; 
v___x_1556_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1557_ = lean_ctor_get(v_m_1554_, 1);
lean_inc_ref(v_buckets_1557_);
lean_dec_ref(v_m_1554_);
v___x_1558_ = lean_box(0);
v___x_1559_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1560_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1560_, 0, v_p_1555_);
lean_closure_set(v___f_1560_, 1, v___x_1558_);
lean_closure_set(v___f_1560_, 2, v___x_1559_);
v___f_1561_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1561_, 0, v___x_1556_);
lean_closure_set(v___f_1561_, 1, v___f_1560_);
v_sz_1562_ = lean_array_size(v_buckets_1557_);
v___x_1563_ = ((size_t)0ULL);
v___x_1564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1556_, v_buckets_1557_, v___f_1561_, v_sz_1562_, v___x_1563_, v___x_1559_);
v_fst_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_fst_1565_);
lean_dec(v___x_1564_);
if (lean_obj_tag(v_fst_1565_) == 0)
{
uint8_t v___x_1566_; 
v___x_1566_ = 1;
return v___x_1566_;
}
else
{
lean_object* v_val_1567_; uint8_t v___x_1568_; 
v_val_1567_ = lean_ctor_get(v_fst_1565_, 0);
lean_inc(v_val_1567_);
lean_dec_ref(v_fst_1565_);
v___x_1568_ = lean_unbox(v_val_1567_);
lean_dec(v_val_1567_);
return v___x_1568_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___boxed(lean_object* v_00_u03b1_1569_, lean_object* v_00_u03b2_1570_, lean_object* v_m_1571_, lean_object* v_p_1572_){
_start:
{
uint8_t v_res_1573_; lean_object* v_r_1574_; 
v_res_1573_ = l_Std_HashMap_Raw_all(v_00_u03b1_1569_, v_00_u03b2_1570_, v_m_1571_, v_p_1572_);
v_r_1574_ = lean_box(v_res_1573_);
return v_r_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0(lean_object* v_p_1575_, lean_object* v___x_1576_, lean_object* v___x_1577_, lean_object* v_a_1578_, lean_object* v_b_1579_, lean_object* v_acc_1580_){
_start:
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = lean_apply_2(v_p_1575_, v_a_1578_, v_b_1579_);
v___x_1582_ = lean_unbox(v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1576_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec_ref(v___x_1576_);
v___x_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1581_);
v___x_1585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___x_1577_);
v___x_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1586_, 0, v___x_1585_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1587_, lean_object* v___x_1588_, lean_object* v___x_1589_, lean_object* v_a_1590_, lean_object* v_b_1591_, lean_object* v_acc_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Std_HashMap_Raw_any___redArg___lam__0(v_p_1587_, v___x_1588_, v___x_1589_, v_a_1590_, v_b_1591_, v_acc_1592_);
lean_dec_ref(v_acc_1592_);
return v_res_1593_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any___redArg(lean_object* v_m_1594_, lean_object* v_p_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v_buckets_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___f_1600_; lean_object* v___f_1601_; size_t v_sz_1602_; size_t v___x_1603_; lean_object* v___x_1604_; lean_object* v_fst_1605_; 
v___x_1596_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1597_ = lean_ctor_get(v_m_1594_, 1);
lean_inc_ref(v_buckets_1597_);
lean_dec_ref(v_m_1594_);
v___x_1598_ = lean_box(0);
v___x_1599_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1600_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1600_, 0, v_p_1595_);
lean_closure_set(v___f_1600_, 1, v___x_1599_);
lean_closure_set(v___f_1600_, 2, v___x_1598_);
v___f_1601_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1601_, 0, v___x_1596_);
lean_closure_set(v___f_1601_, 1, v___f_1600_);
v_sz_1602_ = lean_array_size(v_buckets_1597_);
v___x_1603_ = ((size_t)0ULL);
v___x_1604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1596_, v_buckets_1597_, v___f_1601_, v_sz_1602_, v___x_1603_, v___x_1599_);
v_fst_1605_ = lean_ctor_get(v___x_1604_, 0);
lean_inc(v_fst_1605_);
lean_dec(v___x_1604_);
if (lean_obj_tag(v_fst_1605_) == 0)
{
uint8_t v___x_1606_; 
v___x_1606_ = 0;
return v___x_1606_;
}
else
{
lean_object* v_val_1607_; uint8_t v___x_1608_; 
v_val_1607_ = lean_ctor_get(v_fst_1605_, 0);
lean_inc(v_val_1607_);
lean_dec_ref(v_fst_1605_);
v___x_1608_ = lean_unbox(v_val_1607_);
lean_dec(v_val_1607_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___boxed(lean_object* v_m_1609_, lean_object* v_p_1610_){
_start:
{
uint8_t v_res_1611_; lean_object* v_r_1612_; 
v_res_1611_ = l_Std_HashMap_Raw_any___redArg(v_m_1609_, v_p_1610_);
v_r_1612_ = lean_box(v_res_1611_);
return v_r_1612_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any(lean_object* v_00_u03b1_1613_, lean_object* v_00_u03b2_1614_, lean_object* v_m_1615_, lean_object* v_p_1616_){
_start:
{
lean_object* v___x_1617_; lean_object* v_buckets_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___f_1621_; lean_object* v___f_1622_; size_t v_sz_1623_; size_t v___x_1624_; lean_object* v___x_1625_; lean_object* v_fst_1626_; 
v___x_1617_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1618_ = lean_ctor_get(v_m_1615_, 1);
lean_inc_ref(v_buckets_1618_);
lean_dec_ref(v_m_1615_);
v___x_1619_ = lean_box(0);
v___x_1620_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1621_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1621_, 0, v_p_1616_);
lean_closure_set(v___f_1621_, 1, v___x_1620_);
lean_closure_set(v___f_1621_, 2, v___x_1619_);
v___f_1622_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1622_, 0, v___x_1617_);
lean_closure_set(v___f_1622_, 1, v___f_1621_);
v_sz_1623_ = lean_array_size(v_buckets_1618_);
v___x_1624_ = ((size_t)0ULL);
v___x_1625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1617_, v_buckets_1618_, v___f_1622_, v_sz_1623_, v___x_1624_, v___x_1620_);
v_fst_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_fst_1626_);
lean_dec(v___x_1625_);
if (lean_obj_tag(v_fst_1626_) == 0)
{
uint8_t v___x_1627_; 
v___x_1627_ = 0;
return v___x_1627_;
}
else
{
lean_object* v_val_1628_; uint8_t v___x_1629_; 
v_val_1628_ = lean_ctor_get(v_fst_1626_, 0);
lean_inc(v_val_1628_);
lean_dec_ref(v_fst_1626_);
v___x_1629_ = lean_unbox(v_val_1628_);
lean_dec(v_val_1628_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___boxed(lean_object* v_00_u03b1_1630_, lean_object* v_00_u03b2_1631_, lean_object* v_m_1632_, lean_object* v_p_1633_){
_start:
{
uint8_t v_res_1634_; lean_object* v_r_1635_; 
v_res_1634_ = l_Std_HashMap_Raw_any(v_00_u03b1_1630_, v_00_u03b2_1631_, v_m_1632_, v_p_1633_);
v_r_1635_ = lean_box(v_res_1634_);
return v_r_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_a_1638_, lean_object* v_b_1639_, lean_object* v_acc_1640_){
_start:
{
lean_object* v_r_1641_; lean_object* v___x_1642_; 
v_r_1641_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1636_, v_inst_1637_, v_acc_1640_, v_a_1638_, v_b_1639_);
v___x_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1642_, 0, v_r_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__1(lean_object* v___x_1643_, lean_object* v___f_1644_, lean_object* v_a_1645_, lean_object* v_x_1646_, lean_object* v___y_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1643_, v___f_1644_, v_a_1645_, v___y_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg(lean_object* v_inst_1651_, lean_object* v_inst_1652_, lean_object* v_m_u2081_1653_, lean_object* v_m_u2082_1654_){
_start:
{
lean_object* v_size_1655_; lean_object* v_buckets_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_size_1655_ = lean_ctor_get(v_m_u2081_1653_, 0);
v_buckets_1656_ = lean_ctor_get(v_m_u2081_1653_, 1);
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = lean_array_get_size(v_buckets_1656_);
v___x_1659_ = lean_nat_dec_lt(v___x_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_dec_ref(v_m_u2081_1653_);
lean_dec_ref(v_inst_1652_);
lean_dec_ref(v_inst_1651_);
return v_m_u2082_1654_;
}
else
{
lean_object* v_size_1660_; lean_object* v_buckets_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_size_1660_ = lean_ctor_get(v_m_u2082_1654_, 0);
v_buckets_1661_ = lean_ctor_get(v_m_u2082_1654_, 1);
v___x_1662_ = lean_array_get_size(v_buckets_1661_);
v___x_1663_ = lean_nat_dec_lt(v___x_1657_, v___x_1662_);
if (v___x_1663_ == 0)
{
lean_dec_ref(v_m_u2082_1654_);
lean_dec_ref(v_inst_1652_);
lean_dec_ref(v_inst_1651_);
return v_m_u2081_1653_;
}
else
{
uint8_t v___x_1664_; 
v___x_1664_ = lean_nat_dec_le(v_size_1655_, v_size_1660_);
if (v___x_1664_ == 0)
{
lean_object* v___f_1665_; lean_object* v___x_1666_; 
v___f_1665_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1666_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1665_, v_inst_1651_, v_inst_1652_, v_m_u2081_1653_, v_m_u2082_1654_);
return v___x_1666_;
}
else
{
lean_object* v___f_1667_; lean_object* v___x_1668_; lean_object* v___f_1669_; size_t v_sz_1670_; size_t v___x_1671_; lean_object* v___x_1672_; 
lean_inc_ref(v_buckets_1656_);
lean_dec_ref(v_m_u2081_1653_);
v___f_1667_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1667_, 0, v_inst_1651_);
lean_closure_set(v___f_1667_, 1, v_inst_1652_);
v___x_1668_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___f_1669_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1669_, 0, v___x_1668_);
lean_closure_set(v___f_1669_, 1, v___f_1667_);
v_sz_1670_ = lean_array_size(v_buckets_1656_);
v___x_1671_ = ((size_t)0ULL);
v___x_1672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1668_, v_buckets_1656_, v___f_1669_, v_sz_1670_, v___x_1671_, v_m_u2082_1654_);
return v___x_1672_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union(lean_object* v_00_u03b1_1673_, lean_object* v_00_u03b2_1674_, lean_object* v_inst_1675_, lean_object* v_inst_1676_, lean_object* v_m_u2081_1677_, lean_object* v_m_u2082_1678_){
_start:
{
lean_object* v_size_1679_; lean_object* v_buckets_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; uint8_t v___x_1683_; 
v_size_1679_ = lean_ctor_get(v_m_u2081_1677_, 0);
v_buckets_1680_ = lean_ctor_get(v_m_u2081_1677_, 1);
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = lean_array_get_size(v_buckets_1680_);
v___x_1683_ = lean_nat_dec_lt(v___x_1681_, v___x_1682_);
if (v___x_1683_ == 0)
{
lean_dec_ref(v_m_u2081_1677_);
lean_dec_ref(v_inst_1676_);
lean_dec_ref(v_inst_1675_);
return v_m_u2082_1678_;
}
else
{
lean_object* v_size_1684_; lean_object* v_buckets_1685_; lean_object* v___x_1686_; uint8_t v___x_1687_; 
v_size_1684_ = lean_ctor_get(v_m_u2082_1678_, 0);
v_buckets_1685_ = lean_ctor_get(v_m_u2082_1678_, 1);
v___x_1686_ = lean_array_get_size(v_buckets_1685_);
v___x_1687_ = lean_nat_dec_lt(v___x_1681_, v___x_1686_);
if (v___x_1687_ == 0)
{
lean_dec_ref(v_m_u2082_1678_);
lean_dec_ref(v_inst_1676_);
lean_dec_ref(v_inst_1675_);
return v_m_u2081_1677_;
}
else
{
uint8_t v___x_1688_; 
v___x_1688_ = lean_nat_dec_le(v_size_1679_, v_size_1684_);
if (v___x_1688_ == 0)
{
lean_object* v___f_1689_; lean_object* v___x_1690_; 
v___f_1689_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1690_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1689_, v_inst_1675_, v_inst_1676_, v_m_u2081_1677_, v_m_u2082_1678_);
return v___x_1690_;
}
else
{
lean_object* v___f_1691_; lean_object* v___x_1692_; lean_object* v___f_1693_; size_t v_sz_1694_; size_t v___x_1695_; lean_object* v___x_1696_; 
lean_inc_ref(v_buckets_1680_);
lean_dec_ref(v_m_u2081_1677_);
v___f_1691_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1691_, 0, v_inst_1675_);
lean_closure_set(v___f_1691_, 1, v_inst_1676_);
v___x_1692_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___f_1693_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1693_, 0, v___x_1692_);
lean_closure_set(v___f_1693_, 1, v___f_1691_);
v_sz_1694_ = lean_array_size(v_buckets_1680_);
v___x_1695_ = ((size_t)0ULL);
v___x_1696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1692_, v_buckets_1680_, v___f_1693_, v_sz_1694_, v___x_1695_, v_m_u2082_1678_);
return v___x_1696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter___redArg(lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_m_u2081_1699_, lean_object* v_m_u2082_1700_){
_start:
{
lean_object* v_buckets_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v_buckets_1701_ = lean_ctor_get(v_m_u2081_1699_, 1);
v___x_1702_ = lean_unsigned_to_nat(0u);
v___x_1703_ = lean_array_get_size(v_buckets_1701_);
v___x_1704_ = lean_nat_dec_lt(v___x_1702_, v___x_1703_);
if (v___x_1704_ == 0)
{
lean_dec_ref(v_m_u2081_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec_ref(v_inst_1697_);
return v_m_u2082_1700_;
}
else
{
lean_object* v_buckets_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v_buckets_1705_ = lean_ctor_get(v_m_u2082_1700_, 1);
v___x_1706_ = lean_array_get_size(v_buckets_1705_);
v___x_1707_ = lean_nat_dec_lt(v___x_1702_, v___x_1706_);
if (v___x_1707_ == 0)
{
lean_dec_ref(v_m_u2082_1700_);
lean_dec_ref(v_inst_1698_);
lean_dec_ref(v_inst_1697_);
return v_m_u2081_1699_;
}
else
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1697_, v_inst_1698_, v_m_u2081_1699_, v_m_u2082_1700_);
return v___x_1708_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter(lean_object* v_00_u03b1_1709_, lean_object* v_00_u03b2_1710_, lean_object* v_inst_1711_, lean_object* v_inst_1712_, lean_object* v_m_u2081_1713_, lean_object* v_m_u2082_1714_){
_start:
{
lean_object* v_buckets_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v_buckets_1715_ = lean_ctor_get(v_m_u2081_1713_, 1);
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = lean_array_get_size(v_buckets_1715_);
v___x_1718_ = lean_nat_dec_lt(v___x_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_dec_ref(v_m_u2081_1713_);
lean_dec_ref(v_inst_1712_);
lean_dec_ref(v_inst_1711_);
return v_m_u2082_1714_;
}
else
{
lean_object* v_buckets_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v_buckets_1719_ = lean_ctor_get(v_m_u2082_1714_, 1);
v___x_1720_ = lean_array_get_size(v_buckets_1719_);
v___x_1721_ = lean_nat_dec_lt(v___x_1716_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_dec_ref(v_m_u2082_1714_);
lean_dec_ref(v_inst_1712_);
lean_dec_ref(v_inst_1711_);
return v_m_u2081_1713_;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1711_, v_inst_1712_, v_m_u2081_1713_, v_m_u2082_1714_);
return v___x_1722_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_m_u2082_1725_, uint8_t v___x_1726_, lean_object* v_k_1727_, lean_object* v_x_1728_){
_start:
{
uint8_t v___x_1729_; 
v___x_1729_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1723_, v_inst_1724_, v_m_u2082_1725_, v_k_1727_);
if (v___x_1729_ == 0)
{
return v___x_1726_;
}
else
{
uint8_t v___x_1730_; 
v___x_1730_ = 0;
return v___x_1730_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_m_u2082_1733_, lean_object* v___x_1734_, lean_object* v_k_1735_, lean_object* v_x_1736_){
_start:
{
uint8_t v___x_91__boxed_1737_; uint8_t v_res_1738_; lean_object* v_r_1739_; 
v___x_91__boxed_1737_ = lean_unbox(v___x_1734_);
v_res_1738_ = l_Std_HashMap_Raw_diff___redArg___lam__0(v_inst_1731_, v_inst_1732_, v_m_u2082_1733_, v___x_91__boxed_1737_, v_k_1735_, v_x_1736_);
lean_dec(v_x_1736_);
lean_dec_ref(v_m_u2082_1733_);
v_r_1739_ = lean_box(v_res_1738_);
return v_r_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg(lean_object* v_inst_1740_, lean_object* v_inst_1741_, lean_object* v_m_u2081_1742_, lean_object* v_m_u2082_1743_){
_start:
{
lean_object* v_size_1744_; lean_object* v_buckets_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_size_1744_ = lean_ctor_get(v_m_u2081_1742_, 0);
v_buckets_1745_ = lean_ctor_get(v_m_u2081_1742_, 1);
v___x_1746_ = lean_unsigned_to_nat(0u);
v___x_1747_ = lean_array_get_size(v_buckets_1745_);
v___x_1748_ = lean_nat_dec_lt(v___x_1746_, v___x_1747_);
if (v___x_1748_ == 0)
{
lean_dec_ref(v_m_u2081_1742_);
lean_dec_ref(v_inst_1741_);
lean_dec_ref(v_inst_1740_);
return v_m_u2082_1743_;
}
else
{
lean_object* v_size_1749_; lean_object* v_buckets_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v_size_1749_ = lean_ctor_get(v_m_u2082_1743_, 0);
v_buckets_1750_ = lean_ctor_get(v_m_u2082_1743_, 1);
v___x_1751_ = lean_array_get_size(v_buckets_1750_);
v___x_1752_ = lean_nat_dec_lt(v___x_1746_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec_ref(v_m_u2082_1743_);
lean_dec_ref(v_inst_1741_);
lean_dec_ref(v_inst_1740_);
return v_m_u2081_1742_;
}
else
{
uint8_t v___x_1753_; 
v___x_1753_ = lean_nat_dec_le(v_size_1744_, v_size_1749_);
if (v___x_1753_ == 0)
{
lean_object* v___f_1754_; lean_object* v___x_1755_; 
v___f_1754_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1755_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1754_, v_inst_1740_, v_inst_1741_, v_m_u2081_1742_, v_m_u2082_1743_);
return v___x_1755_;
}
else
{
lean_object* v___x_1756_; lean_object* v___f_1757_; lean_object* v___x_1758_; 
v___x_1756_ = lean_box(v___x_1753_);
v___f_1757_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1757_, 0, v_inst_1740_);
lean_closure_set(v___f_1757_, 1, v_inst_1741_);
lean_closure_set(v___f_1757_, 2, v_m_u2082_1743_);
lean_closure_set(v___f_1757_, 3, v___x_1756_);
v___x_1758_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1757_, v_m_u2081_1742_);
return v___x_1758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff(lean_object* v_00_u03b1_1759_, lean_object* v_00_u03b2_1760_, lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_m_u2081_1763_, lean_object* v_m_u2082_1764_){
_start:
{
lean_object* v_size_1765_; lean_object* v_buckets_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_size_1765_ = lean_ctor_get(v_m_u2081_1763_, 0);
v_buckets_1766_ = lean_ctor_get(v_m_u2081_1763_, 1);
v___x_1767_ = lean_unsigned_to_nat(0u);
v___x_1768_ = lean_array_get_size(v_buckets_1766_);
v___x_1769_ = lean_nat_dec_lt(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_dec_ref(v_m_u2081_1763_);
lean_dec_ref(v_inst_1762_);
lean_dec_ref(v_inst_1761_);
return v_m_u2082_1764_;
}
else
{
lean_object* v_size_1770_; lean_object* v_buckets_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_size_1770_ = lean_ctor_get(v_m_u2082_1764_, 0);
v_buckets_1771_ = lean_ctor_get(v_m_u2082_1764_, 1);
v___x_1772_ = lean_array_get_size(v_buckets_1771_);
v___x_1773_ = lean_nat_dec_lt(v___x_1767_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_dec_ref(v_m_u2082_1764_);
lean_dec_ref(v_inst_1762_);
lean_dec_ref(v_inst_1761_);
return v_m_u2081_1763_;
}
else
{
uint8_t v___x_1774_; 
v___x_1774_ = lean_nat_dec_le(v_size_1765_, v_size_1770_);
if (v___x_1774_ == 0)
{
lean_object* v___f_1775_; lean_object* v___x_1776_; 
v___f_1775_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1776_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1775_, v_inst_1761_, v_inst_1762_, v_m_u2081_1763_, v_m_u2082_1764_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; lean_object* v___f_1778_; lean_object* v___x_1779_; 
v___x_1777_ = lean_box(v___x_1774_);
v___f_1778_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1778_, 0, v_inst_1761_);
lean_closure_set(v___f_1778_, 1, v_inst_1762_);
lean_closure_set(v___f_1778_, 2, v_m_u2082_1764_);
lean_closure_set(v___f_1778_, 3, v___x_1777_);
v___x_1779_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1778_, v_m_u2081_1763_);
return v___x_1779_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1780_, lean_object* v_inst_1781_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1782_, 0, lean_box(0));
lean_closure_set(v___x_1782_, 1, lean_box(0));
lean_closure_set(v___x_1782_, 2, v_inst_1780_);
lean_closure_set(v___x_1782_, 3, v_inst_1781_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1783_, lean_object* v_00_u03b2_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1787_, 0, lean_box(0));
lean_closure_set(v___x_1787_, 1, lean_box(0));
lean_closure_set(v___x_1787_, 2, v_inst_1785_);
lean_closure_set(v___x_1787_, 3, v_inst_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1788_, lean_object* v_inst_1789_){
_start:
{
lean_object* v___x_1790_; 
v___x_1790_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1790_, 0, lean_box(0));
lean_closure_set(v___x_1790_, 1, lean_box(0));
lean_closure_set(v___x_1790_, 2, v_inst_1788_);
lean_closure_set(v___x_1790_, 3, v_inst_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1791_, lean_object* v_00_u03b2_1792_, lean_object* v_inst_1793_, lean_object* v_inst_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1795_, 0, lean_box(0));
lean_closure_set(v___x_1795_, 1, lean_box(0));
lean_closure_set(v___x_1795_, 2, v_inst_1793_);
lean_closure_set(v___x_1795_, 3, v_inst_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1796_, lean_object* v_inst_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1798_, 0, lean_box(0));
lean_closure_set(v___x_1798_, 1, lean_box(0));
lean_closure_set(v___x_1798_, 2, v_inst_1796_);
lean_closure_set(v___x_1798_, 3, v_inst_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1799_, lean_object* v_00_u03b2_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1803_, 0, lean_box(0));
lean_closure_set(v___x_1803_, 1, lean_box(0));
lean_closure_set(v___x_1803_, 2, v_inst_1801_);
lean_closure_set(v___x_1803_, 3, v_inst_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq___redArg(lean_object* v_inst_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_, lean_object* v_m_u2081_1807_, lean_object* v_m_u2082_1808_){
_start:
{
uint8_t v___x_1809_; 
v___x_1809_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1804_, v_inst_1805_, v_inst_1806_, v_m_u2081_1807_, v_m_u2082_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___redArg___boxed(lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_m_u2081_1813_, lean_object* v_m_u2082_1814_){
_start:
{
uint8_t v_res_1815_; lean_object* v_r_1816_; 
v_res_1815_ = l_Std_HashMap_Raw_beq___redArg(v_inst_1810_, v_inst_1811_, v_inst_1812_, v_m_u2081_1813_, v_m_u2082_1814_);
v_r_1816_ = lean_box(v_res_1815_);
return v_r_1816_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq(lean_object* v_00_u03b1_1817_, lean_object* v_00_u03b2_1818_, lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_m_u2081_1822_, lean_object* v_m_u2082_1823_){
_start:
{
uint8_t v___x_1824_; 
v___x_1824_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1819_, v_inst_1820_, v_inst_1821_, v_m_u2081_1822_, v_m_u2082_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___boxed(lean_object* v_00_u03b1_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_inst_1829_, lean_object* v_m_u2081_1830_, lean_object* v_m_u2082_1831_){
_start:
{
uint8_t v_res_1832_; lean_object* v_r_1833_; 
v_res_1832_ = l_Std_HashMap_Raw_beq(v_00_u03b1_1825_, v_00_u03b2_1826_, v_inst_1827_, v_inst_1828_, v_inst_1829_, v_m_u2081_1830_, v_m_u2082_1831_);
v_r_1833_ = lean_box(v_res_1832_);
return v_r_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_){
_start:
{
lean_object* v___x_1837_; 
v___x_1837_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1837_, 0, lean_box(0));
lean_closure_set(v___x_1837_, 1, lean_box(0));
lean_closure_set(v___x_1837_, 2, v_inst_1834_);
lean_closure_set(v___x_1837_, 3, v_inst_1835_);
lean_closure_set(v___x_1837_, 4, v_inst_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1838_, lean_object* v_00_u03b2_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_inst_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1843_, 0, lean_box(0));
lean_closure_set(v___x_1843_, 1, lean_box(0));
lean_closure_set(v___x_1843_, 2, v_inst_1840_);
lean_closure_set(v___x_1843_, 3, v_inst_1841_);
lean_closure_set(v___x_1843_, 4, v_inst_1842_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg(lean_object* v_f_1844_, lean_object* v_m_1845_){
_start:
{
lean_object* v_buckets_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; uint8_t v___x_1849_; 
v_buckets_1846_ = lean_ctor_get(v_m_1845_, 1);
v___x_1847_ = lean_unsigned_to_nat(0u);
v___x_1848_ = lean_array_get_size(v_buckets_1846_);
v___x_1849_ = lean_nat_dec_lt(v___x_1847_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_object* v___x_1850_; 
lean_dec_ref(v_m_1845_);
lean_dec_ref(v_f_1844_);
v___x_1850_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1844_, v_m_1845_);
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object* v_00_u03b1_1852_, lean_object* v_00_u03b2_1853_, lean_object* v_00_u03b3_1854_, lean_object* v_f_1855_, lean_object* v_m_1856_){
_start:
{
lean_object* v_buckets_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; uint8_t v___x_1860_; 
v_buckets_1857_ = lean_ctor_get(v_m_1856_, 1);
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_array_get_size(v_buckets_1857_);
v___x_1860_ = lean_nat_dec_lt(v___x_1858_, v___x_1859_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; 
lean_dec_ref(v_m_1856_);
lean_dec_ref(v_f_1855_);
v___x_1861_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1855_, v_m_1856_);
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object* v_f_1863_, lean_object* v_m_1864_){
_start:
{
lean_object* v_buckets_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; uint8_t v___x_1868_; 
v_buckets_1865_ = lean_ctor_get(v_m_1864_, 1);
v___x_1866_ = lean_unsigned_to_nat(0u);
v___x_1867_ = lean_array_get_size(v_buckets_1865_);
v___x_1868_ = lean_nat_dec_lt(v___x_1866_, v___x_1867_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; 
lean_dec_ref(v_m_1864_);
lean_dec(v_f_1863_);
v___x_1869_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1863_, v_m_1864_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_00_u03b3_1873_, lean_object* v_f_1874_, lean_object* v_m_1875_){
_start:
{
lean_object* v_buckets_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; 
v_buckets_1876_ = lean_ctor_get(v_m_1875_, 1);
v___x_1877_ = lean_unsigned_to_nat(0u);
v___x_1878_ = lean_array_get_size(v_buckets_1876_);
v___x_1879_ = lean_nat_dec_lt(v___x_1877_, v___x_1878_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_dec_ref(v_m_1875_);
lean_dec(v_f_1874_);
v___x_1880_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; 
v___x_1881_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1874_, v_m_1875_);
return v___x_1881_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object* v_f_1882_, lean_object* v_m_1883_){
_start:
{
lean_object* v_buckets_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; uint8_t v___x_1887_; 
v_buckets_1884_ = lean_ctor_get(v_m_1883_, 1);
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = lean_array_get_size(v_buckets_1884_);
v___x_1887_ = lean_nat_dec_lt(v___x_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___x_1888_; 
lean_dec_ref(v_m_1883_);
lean_dec_ref(v_f_1882_);
v___x_1888_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1888_;
}
else
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1882_, v_m_1883_);
return v___x_1889_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object* v_00_u03b1_1890_, lean_object* v_00_u03b2_1891_, lean_object* v_f_1892_, lean_object* v_m_1893_){
_start:
{
lean_object* v_buckets_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v_buckets_1894_ = lean_ctor_get(v_m_1893_, 1);
v___x_1895_ = lean_unsigned_to_nat(0u);
v___x_1896_ = lean_array_get_size(v_buckets_1894_);
v___x_1897_ = lean_nat_dec_lt(v___x_1895_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_object* v___x_1898_; 
lean_dec_ref(v_m_1893_);
lean_dec_ref(v_f_1892_);
v___x_1898_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1898_;
}
else
{
lean_object* v___x_1899_; 
v___x_1899_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1892_, v_m_1893_);
return v___x_1899_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1900_, lean_object* v_x2_1901_, lean_object* v_x3_1902_){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v_x2_1901_);
lean_ctor_set(v___x_1903_, 1, v_x3_1902_);
v___x_1904_ = lean_array_push(v_x1_1900_, v___x_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1905_, lean_object* v___f_1906_, lean_object* v_acc_1907_, lean_object* v_l_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1905_, v___f_1906_, v_acc_1907_, v_l_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object* v_m_1914_){
_start:
{
lean_object* v_size_1915_; lean_object* v_buckets_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; uint8_t v___x_1921_; 
v_size_1915_ = lean_ctor_get(v_m_1914_, 0);
lean_inc(v_size_1915_);
v_buckets_1916_ = lean_ctor_get(v_m_1914_, 1);
lean_inc_ref(v_buckets_1916_);
lean_dec_ref(v_m_1914_);
v___x_1917_ = lean_mk_empty_array_with_capacity(v_size_1915_);
lean_dec(v_size_1915_);
v___x_1918_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1919_ = lean_unsigned_to_nat(0u);
v___x_1920_ = lean_array_get_size(v_buckets_1916_);
v___x_1921_ = lean_nat_dec_lt(v___x_1919_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_dec_ref(v_buckets_1916_);
return v___x_1917_;
}
else
{
lean_object* v___f_1922_; uint8_t v___x_1923_; 
v___f_1922_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1923_ = lean_nat_dec_le(v___x_1920_, v___x_1920_);
if (v___x_1923_ == 0)
{
if (v___x_1921_ == 0)
{
lean_dec_ref(v_buckets_1916_);
return v___x_1917_;
}
else
{
size_t v___x_1924_; size_t v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((size_t)0ULL);
v___x_1925_ = lean_usize_of_nat(v___x_1920_);
v___x_1926_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1918_, v___f_1922_, v_buckets_1916_, v___x_1924_, v___x_1925_, v___x_1917_);
return v___x_1926_;
}
}
else
{
size_t v___x_1927_; size_t v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = ((size_t)0ULL);
v___x_1928_ = lean_usize_of_nat(v___x_1920_);
v___x_1929_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1918_, v___f_1922_, v_buckets_1916_, v___x_1927_, v___x_1928_, v___x_1917_);
return v___x_1929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object* v_00_u03b1_1930_, lean_object* v_00_u03b2_1931_, lean_object* v_m_1932_){
_start:
{
lean_object* v_size_1933_; lean_object* v_buckets_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v_size_1933_ = lean_ctor_get(v_m_1932_, 0);
lean_inc(v_size_1933_);
v_buckets_1934_ = lean_ctor_get(v_m_1932_, 1);
lean_inc_ref(v_buckets_1934_);
lean_dec_ref(v_m_1932_);
v___x_1935_ = lean_mk_empty_array_with_capacity(v_size_1933_);
lean_dec(v_size_1933_);
v___x_1936_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = lean_array_get_size(v_buckets_1934_);
v___x_1939_ = lean_nat_dec_lt(v___x_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_dec_ref(v_buckets_1934_);
return v___x_1935_;
}
else
{
lean_object* v___f_1940_; uint8_t v___x_1941_; 
v___f_1940_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1941_ = lean_nat_dec_le(v___x_1938_, v___x_1938_);
if (v___x_1941_ == 0)
{
if (v___x_1939_ == 0)
{
lean_dec_ref(v_buckets_1934_);
return v___x_1935_;
}
else
{
size_t v___x_1942_; size_t v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = ((size_t)0ULL);
v___x_1943_ = lean_usize_of_nat(v___x_1938_);
v___x_1944_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1936_, v___f_1940_, v_buckets_1934_, v___x_1942_, v___x_1943_, v___x_1935_);
return v___x_1944_;
}
}
else
{
size_t v___x_1945_; size_t v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = ((size_t)0ULL);
v___x_1946_ = lean_usize_of_nat(v___x_1938_);
v___x_1947_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1936_, v___f_1940_, v_buckets_1934_, v___x_1945_, v___x_1946_, v___x_1935_);
return v___x_1947_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1948_, lean_object* v_x2_1949_, lean_object* v_x3_1950_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_array_push(v_x1_1948_, v_x2_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1952_, lean_object* v_x2_1953_, lean_object* v_x3_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Std_HashMap_Raw_keysArray___redArg___lam__0(v_x1_1952_, v_x2_1953_, v_x3_1954_);
lean_dec(v_x3_1954_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1956_, lean_object* v___f_1957_, lean_object* v_acc_1958_, lean_object* v_l_1959_){
_start:
{
lean_object* v___x_1960_; 
v___x_1960_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1956_, v___f_1957_, v_acc_1958_, v_l_1959_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object* v_m_1965_){
_start:
{
lean_object* v_size_1966_; lean_object* v_buckets_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; uint8_t v___x_1972_; 
v_size_1966_ = lean_ctor_get(v_m_1965_, 0);
lean_inc(v_size_1966_);
v_buckets_1967_ = lean_ctor_get(v_m_1965_, 1);
lean_inc_ref(v_buckets_1967_);
lean_dec_ref(v_m_1965_);
v___x_1968_ = lean_mk_empty_array_with_capacity(v_size_1966_);
lean_dec(v_size_1966_);
v___x_1969_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1970_ = lean_unsigned_to_nat(0u);
v___x_1971_ = lean_array_get_size(v_buckets_1967_);
v___x_1972_ = lean_nat_dec_lt(v___x_1970_, v___x_1971_);
if (v___x_1972_ == 0)
{
lean_dec_ref(v_buckets_1967_);
return v___x_1968_;
}
else
{
lean_object* v___f_1973_; uint8_t v___x_1974_; 
v___f_1973_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1974_ = lean_nat_dec_le(v___x_1971_, v___x_1971_);
if (v___x_1974_ == 0)
{
if (v___x_1972_ == 0)
{
lean_dec_ref(v_buckets_1967_);
return v___x_1968_;
}
else
{
size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = lean_usize_of_nat(v___x_1971_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1969_, v___f_1973_, v_buckets_1967_, v___x_1975_, v___x_1976_, v___x_1968_);
return v___x_1977_;
}
}
else
{
size_t v___x_1978_; size_t v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = ((size_t)0ULL);
v___x_1979_ = lean_usize_of_nat(v___x_1971_);
v___x_1980_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1969_, v___f_1973_, v_buckets_1967_, v___x_1978_, v___x_1979_, v___x_1968_);
return v___x_1980_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object* v_00_u03b1_1981_, lean_object* v_00_u03b2_1982_, lean_object* v_m_1983_){
_start:
{
lean_object* v_size_1984_; lean_object* v_buckets_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; uint8_t v___x_1990_; 
v_size_1984_ = lean_ctor_get(v_m_1983_, 0);
lean_inc(v_size_1984_);
v_buckets_1985_ = lean_ctor_get(v_m_1983_, 1);
lean_inc_ref(v_buckets_1985_);
lean_dec_ref(v_m_1983_);
v___x_1986_ = lean_mk_empty_array_with_capacity(v_size_1984_);
lean_dec(v_size_1984_);
v___x_1987_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1988_ = lean_unsigned_to_nat(0u);
v___x_1989_ = lean_array_get_size(v_buckets_1985_);
v___x_1990_ = lean_nat_dec_lt(v___x_1988_, v___x_1989_);
if (v___x_1990_ == 0)
{
lean_dec_ref(v_buckets_1985_);
return v___x_1986_;
}
else
{
lean_object* v___f_1991_; uint8_t v___x_1992_; 
v___f_1991_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1992_ = lean_nat_dec_le(v___x_1989_, v___x_1989_);
if (v___x_1992_ == 0)
{
if (v___x_1990_ == 0)
{
lean_dec_ref(v_buckets_1985_);
return v___x_1986_;
}
else
{
size_t v___x_1993_; size_t v___x_1994_; lean_object* v___x_1995_; 
v___x_1993_ = ((size_t)0ULL);
v___x_1994_ = lean_usize_of_nat(v___x_1989_);
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1987_, v___f_1991_, v_buckets_1985_, v___x_1993_, v___x_1994_, v___x_1986_);
return v___x_1995_;
}
}
else
{
size_t v___x_1996_; size_t v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = ((size_t)0ULL);
v___x_1997_ = lean_usize_of_nat(v___x_1989_);
v___x_1998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1987_, v___f_1991_, v_buckets_1985_, v___x_1996_, v___x_1997_, v___x_1986_);
return v___x_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object* v_a_1999_, lean_object* v_b_2000_, lean_object* v_d_2001_){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2002_, 0, v_b_2000_);
lean_ctor_set(v___x_2002_, 1, v_d_2001_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_2003_, lean_object* v_b_2004_, lean_object* v_d_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Std_HashMap_Raw_values___redArg___lam__0(v_a_2003_, v_b_2004_, v_d_2005_);
lean_dec(v_a_2003_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object* v_m_2011_){
_start:
{
lean_object* v___x_2012_; lean_object* v_buckets_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2012_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2013_ = lean_ctor_get(v_m_2011_, 1);
lean_inc_ref(v_buckets_2013_);
lean_dec_ref(v_m_2011_);
v___x_2014_ = lean_box(0);
v___x_2015_ = lean_array_get_size(v_buckets_2013_);
v___x_2016_ = lean_unsigned_to_nat(0u);
v___x_2017_ = lean_nat_dec_lt(v___x_2016_, v___x_2015_);
if (v___x_2017_ == 0)
{
lean_dec_ref(v_buckets_2013_);
return v___x_2014_;
}
else
{
lean_object* v___f_2018_; size_t v___x_2019_; size_t v___x_2020_; lean_object* v___x_2021_; 
v___f_2018_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_2019_ = lean_usize_of_nat(v___x_2015_);
v___x_2020_ = ((size_t)0ULL);
v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2012_, v___f_2018_, v_buckets_2013_, v___x_2019_, v___x_2020_, v___x_2014_);
return v___x_2021_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object* v_00_u03b1_2022_, lean_object* v_00_u03b2_2023_, lean_object* v_m_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v_buckets_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2025_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2026_ = lean_ctor_get(v_m_2024_, 1);
lean_inc_ref(v_buckets_2026_);
lean_dec_ref(v_m_2024_);
v___x_2027_ = lean_box(0);
v___x_2028_ = lean_array_get_size(v_buckets_2026_);
v___x_2029_ = lean_unsigned_to_nat(0u);
v___x_2030_ = lean_nat_dec_lt(v___x_2029_, v___x_2028_);
if (v___x_2030_ == 0)
{
lean_dec_ref(v_buckets_2026_);
return v___x_2027_;
}
else
{
lean_object* v___f_2031_; size_t v___x_2032_; size_t v___x_2033_; lean_object* v___x_2034_; 
v___f_2031_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_2032_ = lean_usize_of_nat(v___x_2028_);
v___x_2033_ = ((size_t)0ULL);
v___x_2034_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2025_, v___f_2031_, v_buckets_2026_, v___x_2032_, v___x_2033_, v___x_2027_);
return v___x_2034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2035_, lean_object* v_x2_2036_, lean_object* v_x3_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_array_push(v_x1_2035_, v_x3_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2039_, lean_object* v_x2_2040_, lean_object* v_x3_2041_){
_start:
{
lean_object* v_res_2042_; 
v_res_2042_ = l_Std_HashMap_Raw_valuesArray___redArg___lam__0(v_x1_2039_, v_x2_2040_, v_x3_2041_);
lean_dec(v_x2_2040_);
return v_res_2042_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg(lean_object* v_m_2047_){
_start:
{
lean_object* v_size_2048_; lean_object* v_buckets_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v_size_2048_ = lean_ctor_get(v_m_2047_, 0);
lean_inc(v_size_2048_);
v_buckets_2049_ = lean_ctor_get(v_m_2047_, 1);
lean_inc_ref(v_buckets_2049_);
lean_dec_ref(v_m_2047_);
v___x_2050_ = lean_mk_empty_array_with_capacity(v_size_2048_);
lean_dec(v_size_2048_);
v___x_2051_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2052_ = lean_unsigned_to_nat(0u);
v___x_2053_ = lean_array_get_size(v_buckets_2049_);
v___x_2054_ = lean_nat_dec_lt(v___x_2052_, v___x_2053_);
if (v___x_2054_ == 0)
{
lean_dec_ref(v_buckets_2049_);
return v___x_2050_;
}
else
{
lean_object* v___f_2055_; uint8_t v___x_2056_; 
v___f_2055_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2056_ = lean_nat_dec_le(v___x_2053_, v___x_2053_);
if (v___x_2056_ == 0)
{
if (v___x_2054_ == 0)
{
lean_dec_ref(v_buckets_2049_);
return v___x_2050_;
}
else
{
size_t v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
v___x_2057_ = ((size_t)0ULL);
v___x_2058_ = lean_usize_of_nat(v___x_2053_);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2051_, v___f_2055_, v_buckets_2049_, v___x_2057_, v___x_2058_, v___x_2050_);
return v___x_2059_;
}
}
else
{
size_t v___x_2060_; size_t v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = ((size_t)0ULL);
v___x_2061_ = lean_usize_of_nat(v___x_2053_);
v___x_2062_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2051_, v___f_2055_, v_buckets_2049_, v___x_2060_, v___x_2061_, v___x_2050_);
return v___x_2062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray(lean_object* v_00_u03b1_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_m_2065_){
_start:
{
lean_object* v_size_2066_; lean_object* v_buckets_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; uint8_t v___x_2072_; 
v_size_2066_ = lean_ctor_get(v_m_2065_, 0);
lean_inc(v_size_2066_);
v_buckets_2067_ = lean_ctor_get(v_m_2065_, 1);
lean_inc_ref(v_buckets_2067_);
lean_dec_ref(v_m_2065_);
v___x_2068_ = lean_mk_empty_array_with_capacity(v_size_2066_);
lean_dec(v_size_2066_);
v___x_2069_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2070_ = lean_unsigned_to_nat(0u);
v___x_2071_ = lean_array_get_size(v_buckets_2067_);
v___x_2072_ = lean_nat_dec_lt(v___x_2070_, v___x_2071_);
if (v___x_2072_ == 0)
{
lean_dec_ref(v_buckets_2067_);
return v___x_2068_;
}
else
{
lean_object* v___f_2073_; uint8_t v___x_2074_; 
v___f_2073_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2074_ = lean_nat_dec_le(v___x_2071_, v___x_2071_);
if (v___x_2074_ == 0)
{
if (v___x_2072_ == 0)
{
lean_dec_ref(v_buckets_2067_);
return v___x_2068_;
}
else
{
size_t v___x_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = ((size_t)0ULL);
v___x_2076_ = lean_usize_of_nat(v___x_2071_);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2069_, v___f_2073_, v_buckets_2067_, v___x_2075_, v___x_2076_, v___x_2068_);
return v___x_2077_;
}
}
else
{
size_t v___x_2078_; size_t v___x_2079_; lean_object* v___x_2080_; 
v___x_2078_ = ((size_t)0ULL);
v___x_2079_ = lean_usize_of_nat(v___x_2071_);
v___x_2080_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2069_, v___f_2073_, v_buckets_2067_, v___x_2078_, v___x_2079_, v___x_2068_);
return v___x_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany___redArg(lean_object* v_inst_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_m_2084_, lean_object* v_l_2085_){
_start:
{
lean_object* v_buckets_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_buckets_2086_ = lean_ctor_get(v_m_2084_, 1);
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_array_get_size(v_buckets_2086_);
v___x_2089_ = lean_nat_dec_lt(v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_dec(v_l_2085_);
lean_dec(v_inst_2083_);
lean_dec_ref(v_inst_2082_);
lean_dec_ref(v_inst_2081_);
return v_m_2084_;
}
else
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2083_, v_inst_2081_, v_inst_2082_, v_m_2084_, v_l_2085_);
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany(lean_object* v_00_u03b1_2091_, lean_object* v_00_u03b2_2092_, lean_object* v_inst_2093_, lean_object* v_inst_2094_, lean_object* v_00_u03c1_2095_, lean_object* v_inst_2096_, lean_object* v_m_2097_, lean_object* v_l_2098_){
_start:
{
lean_object* v_buckets_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; uint8_t v___x_2102_; 
v_buckets_2099_ = lean_ctor_get(v_m_2097_, 1);
v___x_2100_ = lean_unsigned_to_nat(0u);
v___x_2101_ = lean_array_get_size(v_buckets_2099_);
v___x_2102_ = lean_nat_dec_lt(v___x_2100_, v___x_2101_);
if (v___x_2102_ == 0)
{
lean_dec(v_l_2098_);
lean_dec(v_inst_2096_);
lean_dec_ref(v_inst_2094_);
lean_dec_ref(v_inst_2093_);
return v_m_2097_;
}
else
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2096_, v_inst_2093_, v_inst_2094_, v_m_2097_, v_l_2098_);
return v___x_2103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_inst_2106_, lean_object* v_m_2107_, lean_object* v_l_2108_){
_start:
{
lean_object* v_buckets_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; uint8_t v___x_2112_; 
v_buckets_2109_ = lean_ctor_get(v_m_2107_, 1);
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = lean_array_get_size(v_buckets_2109_);
v___x_2112_ = lean_nat_dec_lt(v___x_2110_, v___x_2111_);
if (v___x_2112_ == 0)
{
lean_dec(v_l_2108_);
lean_dec(v_inst_2106_);
lean_dec_ref(v_inst_2105_);
lean_dec_ref(v_inst_2104_);
return v_m_2107_;
}
else
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2106_, v_inst_2104_, v_inst_2105_, v_m_2107_, v_l_2108_);
return v___x_2113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_00_u03c1_2117_, lean_object* v_inst_2118_, lean_object* v_m_2119_, lean_object* v_l_2120_){
_start:
{
lean_object* v_buckets_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; uint8_t v___x_2124_; 
v_buckets_2121_ = lean_ctor_get(v_m_2119_, 1);
v___x_2122_ = lean_unsigned_to_nat(0u);
v___x_2123_ = lean_array_get_size(v_buckets_2121_);
v___x_2124_ = lean_nat_dec_lt(v___x_2122_, v___x_2123_);
if (v___x_2124_ == 0)
{
lean_dec(v_l_2120_);
lean_dec(v_inst_2118_);
lean_dec_ref(v_inst_2116_);
lean_dec_ref(v_inst_2115_);
return v_m_2119_;
}
else
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2118_, v_inst_2115_, v_inst_2116_, v_m_2119_, v_l_2120_);
return v___x_2125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray___redArg(lean_object* v_inst_2126_, lean_object* v_inst_2127_, lean_object* v_l_2128_){
_start:
{
lean_object* v___x_2129_; uint8_t v___x_2130_; 
v___x_2129_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_2130_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2130_ == 0)
{
lean_dec_ref(v_l_2128_);
lean_dec_ref(v_inst_2127_);
lean_dec_ref(v_inst_2126_);
return v___x_2129_;
}
else
{
lean_object* v___f_2131_; lean_object* v___x_2132_; 
v___f_2131_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2132_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2131_, v_inst_2126_, v_inst_2127_, v___x_2129_, v_l_2128_);
return v___x_2132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray(lean_object* v_00_u03b1_2133_, lean_object* v_inst_2134_, lean_object* v_inst_2135_, lean_object* v_l_2136_){
_start:
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
v___x_2137_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_2138_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2138_ == 0)
{
lean_dec_ref(v_l_2136_);
lean_dec_ref(v_inst_2135_);
lean_dec_ref(v_inst_2134_);
return v___x_2137_;
}
else
{
lean_object* v___f_2139_; lean_object* v___x_2140_; 
v___f_2139_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2140_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2139_, v_inst_2134_, v_inst_2135_, v___x_2137_, v_l_2136_);
return v___x_2140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2141_){
_start:
{
lean_object* v___x_2142_; 
v___x_2142_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2141_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Std_HashMap_Raw_Internal_numBuckets___redArg(v_m_2143_);
lean_dec_ref(v_m_2143_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2145_, lean_object* v_00_u03b2_2146_, lean_object* v_m_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2149_, lean_object* v_00_u03b2_2150_, lean_object* v_m_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Std_HashMap_Raw_Internal_numBuckets(v_00_u03b1_2149_, v_00_u03b2_2150_, v_m_2151_);
lean_dec_ref(v_m_2151_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2156_, lean_object* v___f_2157_, lean_object* v_m_2158_, lean_object* v_prec_2159_){
_start:
{
lean_object* v___x_2160_; lean_object* v_buckets_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2181_; 
v___x_2160_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2161_ = lean_ctor_get(v_m_2158_, 1);
v_isSharedCheck_2181_ = !lean_is_exclusive(v_m_2158_);
if (v_isSharedCheck_2181_ == 0)
{
lean_object* v_unused_2182_; 
v_unused_2182_ = lean_ctor_get(v_m_2158_, 0);
lean_dec(v_unused_2182_);
v___x_2163_ = v_m_2158_;
v_isShared_2164_ = v_isSharedCheck_2181_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_buckets_2161_);
lean_dec(v_m_2158_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2181_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___y_2167_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v___x_2165_ = ((lean_object*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2173_ = lean_box(0);
v___x_2174_ = lean_array_get_size(v_buckets_2161_);
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_nat_dec_lt(v___x_2175_, v___x_2174_);
if (v___x_2176_ == 0)
{
lean_dec_ref(v_buckets_2161_);
lean_dec_ref(v___f_2157_);
v___y_2167_ = v___x_2173_;
goto v___jp_2166_;
}
else
{
lean_object* v___f_2177_; size_t v___x_2178_; size_t v___x_2179_; lean_object* v___x_2180_; 
v___f_2177_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2177_, 0, v___x_2160_);
lean_closure_set(v___f_2177_, 1, v___f_2157_);
v___x_2178_ = lean_usize_of_nat(v___x_2174_);
v___x_2179_ = ((size_t)0ULL);
v___x_2180_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2160_, v___f_2177_, v_buckets_2161_, v___x_2178_, v___x_2179_, v___x_2173_);
v___y_2167_ = v___x_2180_;
goto v___jp_2166_;
}
v___jp_2166_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = l_List_repr___redArg(v___x_2156_, v___y_2167_);
if (v_isShared_2164_ == 0)
{
lean_ctor_set_tag(v___x_2163_, 5);
lean_ctor_set(v___x_2163_, 1, v___x_2168_);
lean_ctor_set(v___x_2163_, 0, v___x_2165_);
v___x_2170_ = v___x_2163_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2165_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v___x_2168_);
v___x_2170_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Repr_addAppParen(v___x_2170_, v_prec_2159_);
return v___x_2171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2183_, lean_object* v___f_2184_, lean_object* v_m_2185_, lean_object* v_prec_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2(v___x_2183_, v___f_2184_, v_m_2185_, v_prec_2186_);
lean_dec(v_prec_2186_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object* v_inst_2188_, lean_object* v_inst_2189_){
_start:
{
lean_object* v___f_2190_; lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v___f_2193_; 
v___f_2190_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__0));
v___f_2191_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2191_, 0, v_inst_2189_);
v___x_2192_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2192_, 0, lean_box(0));
lean_closure_set(v___x_2192_, 1, lean_box(0));
lean_closure_set(v___x_2192_, 2, v_inst_2188_);
lean_closure_set(v___x_2192_, 3, v___f_2191_);
v___f_2193_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2193_, 0, v___x_2192_);
lean_closure_set(v___f_2193_, 1, v___f_2190_);
return v___f_2193_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object* v_00_u03b1_2194_, lean_object* v_00_u03b2_2195_, lean_object* v_inst_2196_, lean_object* v_inst_2197_){
_start:
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Std_HashMap_Raw_instRepr___redArg(v_inst_2196_, v_inst_2197_);
return v___x_2198_;
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
