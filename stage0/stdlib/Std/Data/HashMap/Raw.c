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
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_HashMap_Raw_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value)} };
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
lean_object* v_toApplicative_1260_; lean_object* v_buckets_1261_; lean_object* v_toPure_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_toApplicative_1260_ = lean_ctor_get(v_inst_1256_, 0);
v_buckets_1261_ = lean_ctor_get(v_b_1259_, 1);
lean_inc_ref(v_buckets_1261_);
lean_dec_ref(v_b_1259_);
v_toPure_1262_ = lean_ctor_get(v_toApplicative_1260_, 1);
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_array_get_size(v_buckets_1261_);
v___x_1265_ = lean_nat_dec_lt(v___x_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
lean_inc(v_toPure_1262_);
lean_dec_ref(v_buckets_1261_);
lean_dec(v_f_1257_);
lean_dec_ref(v_inst_1256_);
v___x_1266_ = lean_apply_2(v_toPure_1262_, lean_box(0), v_init_1258_);
return v___x_1266_;
}
else
{
lean_object* v___f_1267_; size_t v___x_1268_; size_t v___x_1269_; lean_object* v___x_1270_; 
lean_inc_ref(v_inst_1256_);
v___f_1267_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1267_, 0, v_inst_1256_);
lean_closure_set(v___f_1267_, 1, v_f_1257_);
v___x_1268_ = ((size_t)0ULL);
v___x_1269_ = lean_usize_of_nat(v___x_1264_);
v___x_1270_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1256_, v___f_1267_, v_buckets_1261_, v___x_1268_, v___x_1269_, v_init_1258_);
return v___x_1270_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object* v_00_u03b1_1271_, lean_object* v_00_u03b2_1272_, lean_object* v_m_1273_, lean_object* v_inst_1274_, lean_object* v_00_u03b3_1275_, lean_object* v_f_1276_, lean_object* v_init_1277_, lean_object* v_b_1278_){
_start:
{
lean_object* v_toApplicative_1279_; lean_object* v_buckets_1280_; lean_object* v_toPure_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_toApplicative_1279_ = lean_ctor_get(v_inst_1274_, 0);
v_buckets_1280_ = lean_ctor_get(v_b_1278_, 1);
lean_inc_ref(v_buckets_1280_);
lean_dec_ref(v_b_1278_);
v_toPure_1281_ = lean_ctor_get(v_toApplicative_1279_, 1);
v___x_1282_ = lean_unsigned_to_nat(0u);
v___x_1283_ = lean_array_get_size(v_buckets_1280_);
v___x_1284_ = lean_nat_dec_lt(v___x_1282_, v___x_1283_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
lean_inc(v_toPure_1281_);
lean_dec_ref(v_buckets_1280_);
lean_dec(v_f_1276_);
lean_dec_ref(v_inst_1274_);
v___x_1285_ = lean_apply_2(v_toPure_1281_, lean_box(0), v_init_1277_);
return v___x_1285_;
}
else
{
lean_object* v___f_1286_; size_t v___x_1287_; size_t v___x_1288_; lean_object* v___x_1289_; 
lean_inc_ref(v_inst_1274_);
v___f_1286_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1286_, 0, v_inst_1274_);
lean_closure_set(v___f_1286_, 1, v_f_1276_);
v___x_1287_ = ((size_t)0ULL);
v___x_1288_ = lean_usize_of_nat(v___x_1283_);
v___x_1289_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1274_, v___f_1286_, v_buckets_1280_, v___x_1287_, v___x_1288_, v_init_1277_);
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object* v_f_1290_, lean_object* v_x1_1291_, lean_object* v_x2_1292_, lean_object* v_x3_1293_){
_start:
{
lean_object* v___x_1294_; 
v___x_1294_ = lean_apply_3(v_f_1290_, v_x1_1291_, v_x2_1292_, v_x3_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__1(lean_object* v___x_1295_, lean_object* v___f_1296_, lean_object* v_acc_1297_, lean_object* v_l_1298_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1295_, v___f_1296_, v_acc_1297_, v_l_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object* v_f_1300_, lean_object* v_init_1301_, lean_object* v_b_1302_){
_start:
{
lean_object* v___x_1303_; lean_object* v_buckets_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; uint8_t v___x_1307_; 
v___x_1303_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1304_ = lean_ctor_get(v_b_1302_, 1);
lean_inc_ref(v_buckets_1304_);
lean_dec_ref(v_b_1302_);
v___x_1305_ = lean_unsigned_to_nat(0u);
v___x_1306_ = lean_array_get_size(v_buckets_1304_);
v___x_1307_ = lean_nat_dec_lt(v___x_1305_, v___x_1306_);
if (v___x_1307_ == 0)
{
lean_dec_ref(v_buckets_1304_);
lean_dec(v_f_1300_);
return v_init_1301_;
}
else
{
lean_object* v___f_1308_; lean_object* v___f_1309_; size_t v___x_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v___f_1308_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1308_, 0, v_f_1300_);
v___f_1309_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1309_, 0, v___x_1303_);
lean_closure_set(v___f_1309_, 1, v___f_1308_);
v___x_1310_ = ((size_t)0ULL);
v___x_1311_ = lean_usize_of_nat(v___x_1306_);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1303_, v___f_1309_, v_buckets_1304_, v___x_1310_, v___x_1311_, v_init_1301_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object* v_00_u03b1_1313_, lean_object* v_00_u03b2_1314_, lean_object* v_00_u03b3_1315_, lean_object* v_f_1316_, lean_object* v_init_1317_, lean_object* v_b_1318_){
_start:
{
lean_object* v___x_1319_; lean_object* v_buckets_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1319_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1320_ = lean_ctor_get(v_b_1318_, 1);
lean_inc_ref(v_buckets_1320_);
lean_dec_ref(v_b_1318_);
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_array_get_size(v_buckets_1320_);
v___x_1323_ = lean_nat_dec_lt(v___x_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_dec_ref(v_buckets_1320_);
lean_dec(v_f_1316_);
return v_init_1317_;
}
else
{
lean_object* v___f_1324_; lean_object* v___f_1325_; size_t v___x_1326_; size_t v___x_1327_; lean_object* v___x_1328_; 
v___f_1324_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1324_, 0, v_f_1316_);
v___f_1325_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1325_, 0, v___x_1319_);
lean_closure_set(v___f_1325_, 1, v___f_1324_);
v___x_1326_ = ((size_t)0ULL);
v___x_1327_ = lean_usize_of_nat(v___x_1322_);
v___x_1328_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1319_, v___f_1325_, v_buckets_1320_, v___x_1326_, v___x_1327_, v_init_1317_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object* v_f_1329_, lean_object* v_x_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = lean_apply_2(v_f_1329_, v___y_1331_, v___y_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__1(lean_object* v_inst_1334_, lean_object* v___f_1335_, lean_object* v_x_1336_, lean_object* v___y_1337_){
_start:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_box(0);
v___x_1339_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1334_, v___f_1335_, v___x_1338_, v___y_1337_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object* v_inst_1340_, lean_object* v_f_1341_, lean_object* v_b_1342_){
_start:
{
lean_object* v_toApplicative_1343_; lean_object* v_buckets_1344_; lean_object* v_toPure_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_toApplicative_1343_ = lean_ctor_get(v_inst_1340_, 0);
v_buckets_1344_ = lean_ctor_get(v_b_1342_, 1);
lean_inc_ref(v_buckets_1344_);
lean_dec_ref(v_b_1342_);
v_toPure_1345_ = lean_ctor_get(v_toApplicative_1343_, 1);
v___x_1346_ = lean_unsigned_to_nat(0u);
v___x_1347_ = lean_array_get_size(v_buckets_1344_);
v___x_1348_ = lean_box(0);
v___x_1349_ = lean_nat_dec_lt(v___x_1346_, v___x_1347_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_inc(v_toPure_1345_);
lean_dec_ref(v_buckets_1344_);
lean_dec(v_f_1341_);
lean_dec_ref(v_inst_1340_);
v___x_1350_ = lean_apply_2(v_toPure_1345_, lean_box(0), v___x_1348_);
return v___x_1350_;
}
else
{
lean_object* v___f_1351_; lean_object* v___f_1352_; size_t v___x_1353_; size_t v___x_1354_; lean_object* v___x_1355_; 
v___f_1351_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1351_, 0, v_f_1341_);
lean_inc_ref(v_inst_1340_);
v___f_1352_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1352_, 0, v_inst_1340_);
lean_closure_set(v___f_1352_, 1, v___f_1351_);
v___x_1353_ = ((size_t)0ULL);
v___x_1354_ = lean_usize_of_nat(v___x_1347_);
v___x_1355_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1340_, v___f_1352_, v_buckets_1344_, v___x_1353_, v___x_1354_, v___x_1348_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object* v_00_u03b1_1356_, lean_object* v_00_u03b2_1357_, lean_object* v_m_1358_, lean_object* v_inst_1359_, lean_object* v_f_1360_, lean_object* v_b_1361_){
_start:
{
lean_object* v_toApplicative_1362_; lean_object* v_buckets_1363_; lean_object* v_toPure_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; uint8_t v___x_1368_; 
v_toApplicative_1362_ = lean_ctor_get(v_inst_1359_, 0);
v_buckets_1363_ = lean_ctor_get(v_b_1361_, 1);
lean_inc_ref(v_buckets_1363_);
lean_dec_ref(v_b_1361_);
v_toPure_1364_ = lean_ctor_get(v_toApplicative_1362_, 1);
v___x_1365_ = lean_unsigned_to_nat(0u);
v___x_1366_ = lean_array_get_size(v_buckets_1363_);
v___x_1367_ = lean_box(0);
v___x_1368_ = lean_nat_dec_lt(v___x_1365_, v___x_1366_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
lean_inc(v_toPure_1364_);
lean_dec_ref(v_buckets_1363_);
lean_dec(v_f_1360_);
lean_dec_ref(v_inst_1359_);
v___x_1369_ = lean_apply_2(v_toPure_1364_, lean_box(0), v___x_1367_);
return v___x_1369_;
}
else
{
lean_object* v___f_1370_; lean_object* v___f_1371_; size_t v___x_1372_; size_t v___x_1373_; lean_object* v___x_1374_; 
v___f_1370_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1370_, 0, v_f_1360_);
lean_inc_ref(v_inst_1359_);
v___f_1371_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1371_, 0, v_inst_1359_);
lean_closure_set(v___f_1371_, 1, v___f_1370_);
v___x_1372_ = ((size_t)0ULL);
v___x_1373_ = lean_usize_of_nat(v___x_1366_);
v___x_1374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1359_, v___f_1371_, v_buckets_1363_, v___x_1372_, v___x_1373_, v___x_1367_);
return v___x_1374_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg___lam__0(lean_object* v_inst_1375_, lean_object* v_f_1376_, lean_object* v_a_1377_, lean_object* v_x_1378_, lean_object* v___y_1379_){
_start:
{
lean_object* v___x_1380_; 
v___x_1380_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1375_, v_f_1376_, v_a_1377_, v___y_1379_);
return v___x_1380_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object* v_inst_1381_, lean_object* v_f_1382_, lean_object* v_init_1383_, lean_object* v_b_1384_){
_start:
{
lean_object* v_buckets_1385_; lean_object* v___f_1386_; size_t v_sz_1387_; size_t v___x_1388_; lean_object* v___x_1389_; 
v_buckets_1385_ = lean_ctor_get(v_b_1384_, 1);
lean_inc_ref(v_buckets_1385_);
lean_dec_ref(v_b_1384_);
lean_inc_ref(v_inst_1381_);
v___f_1386_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1386_, 0, v_inst_1381_);
lean_closure_set(v___f_1386_, 1, v_f_1382_);
v_sz_1387_ = lean_array_size(v_buckets_1385_);
v___x_1388_ = ((size_t)0ULL);
v___x_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1381_, v_buckets_1385_, v___f_1386_, v_sz_1387_, v___x_1388_, v_init_1383_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object* v_00_u03b1_1390_, lean_object* v_00_u03b2_1391_, lean_object* v_m_1392_, lean_object* v_inst_1393_, lean_object* v_00_u03b3_1394_, lean_object* v_f_1395_, lean_object* v_init_1396_, lean_object* v_b_1397_){
_start:
{
lean_object* v_buckets_1398_; lean_object* v___f_1399_; size_t v_sz_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v_buckets_1398_ = lean_ctor_get(v_b_1397_, 1);
lean_inc_ref(v_buckets_1398_);
lean_dec_ref(v_b_1397_);
lean_inc_ref(v_inst_1393_);
v___f_1399_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1399_, 0, v_inst_1393_);
lean_closure_set(v___f_1399_, 1, v_f_1395_);
v_sz_1400_ = lean_array_size(v_buckets_1398_);
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1393_, v_buckets_1398_, v___f_1399_, v_sz_1400_, v___x_1401_, v_init_1396_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1403_, lean_object* v_x_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1407_, 0, v___y_1405_);
lean_ctor_set(v___x_1407_, 1, v___y_1406_);
v___x_1408_ = lean_apply_1(v_f_1403_, v___x_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1409_, lean_object* v_m_1410_, lean_object* v_f_1411_){
_start:
{
lean_object* v_toApplicative_1412_; lean_object* v_buckets_1413_; lean_object* v_toPure_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_toApplicative_1412_ = lean_ctor_get(v_inst_1409_, 0);
v_buckets_1413_ = lean_ctor_get(v_m_1410_, 1);
lean_inc_ref(v_buckets_1413_);
lean_dec_ref(v_m_1410_);
v_toPure_1414_ = lean_ctor_get(v_toApplicative_1412_, 1);
v___x_1415_ = lean_unsigned_to_nat(0u);
v___x_1416_ = lean_array_get_size(v_buckets_1413_);
v___x_1417_ = lean_box(0);
v___x_1418_ = lean_nat_dec_lt(v___x_1415_, v___x_1416_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
lean_inc(v_toPure_1414_);
lean_dec_ref(v_buckets_1413_);
lean_dec(v_f_1411_);
lean_dec_ref(v_inst_1409_);
v___x_1419_ = lean_apply_2(v_toPure_1414_, lean_box(0), v___x_1417_);
return v___x_1419_;
}
else
{
lean_object* v___f_1420_; lean_object* v___f_1421_; size_t v___x_1422_; size_t v___x_1423_; lean_object* v___x_1424_; 
v___f_1420_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1420_, 0, v_f_1411_);
lean_inc_ref(v_inst_1409_);
v___f_1421_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1421_, 0, v_inst_1409_);
lean_closure_set(v___f_1421_, 1, v___f_1420_);
v___x_1422_ = ((size_t)0ULL);
v___x_1423_ = lean_usize_of_nat(v___x_1416_);
v___x_1424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1409_, v___f_1421_, v_buckets_1413_, v___x_1422_, v___x_1423_, v___x_1417_);
return v___x_1424_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1425_){
_start:
{
lean_object* v___f_1426_; 
v___f_1426_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1426_, 0, v_inst_1425_);
return v___f_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1427_, lean_object* v_00_u03b2_1428_, lean_object* v_m_1429_, lean_object* v_inst_1430_){
_start:
{
lean_object* v___f_1431_; 
v___f_1431_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1431_, 0, v_inst_1430_);
return v___f_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1432_, lean_object* v_a_1433_, lean_object* v_b_1434_, lean_object* v_acc_1435_){
_start:
{
lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1433_);
lean_ctor_set(v___x_1436_, 1, v_b_1434_);
v___x_1437_ = lean_apply_2(v_f_1432_, v___x_1436_, v_acc_1435_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1438_, lean_object* v___f_1439_, lean_object* v_a_1440_, lean_object* v_x_1441_, lean_object* v___y_1442_){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1438_, v___f_1439_, v_a_1440_, v___y_1442_);
return v___x_1443_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1444_, lean_object* v_00_u03b2_1445_, lean_object* v_m_1446_, lean_object* v_init_1447_, lean_object* v_f_1448_){
_start:
{
lean_object* v_buckets_1449_; lean_object* v___f_1450_; lean_object* v___f_1451_; size_t v_sz_1452_; size_t v___x_1453_; lean_object* v___x_1454_; 
v_buckets_1449_ = lean_ctor_get(v_m_1446_, 1);
lean_inc_ref(v_buckets_1449_);
lean_dec_ref(v_m_1446_);
v___f_1450_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1450_, 0, v_f_1448_);
lean_inc_ref(v_inst_1444_);
v___f_1451_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1451_, 0, v_inst_1444_);
lean_closure_set(v___f_1451_, 1, v___f_1450_);
v_sz_1452_ = lean_array_size(v_buckets_1449_);
v___x_1453_ = ((size_t)0ULL);
v___x_1454_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1444_, v_buckets_1449_, v___f_1451_, v_sz_1452_, v___x_1453_, v_init_1447_);
return v___x_1454_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1455_){
_start:
{
lean_object* v___f_1456_; 
v___f_1456_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1456_, 0, v_inst_1455_);
return v___f_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1457_, lean_object* v_00_u03b2_1458_, lean_object* v_m_1459_, lean_object* v_inst_1460_){
_start:
{
lean_object* v___f_1461_; 
v___f_1461_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1461_, 0, v_inst_1460_);
return v___f_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object* v_p_1462_, lean_object* v___x_1463_, lean_object* v___x_1464_, lean_object* v_a_1465_, lean_object* v_b_1466_, lean_object* v_acc_1467_){
_start:
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = lean_apply_2(v_p_1462_, v_a_1465_, v_b_1466_);
v___x_1469_ = lean_unbox(v___x_1468_);
if (v___x_1469_ == 0)
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
lean_dec_ref(v___x_1464_);
v___x_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1468_);
v___x_1471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v___x_1463_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v___x_1471_);
return v___x_1472_;
}
else
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v___x_1464_);
return v___x_1473_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1474_, lean_object* v___x_1475_, lean_object* v___x_1476_, lean_object* v_a_1477_, lean_object* v_b_1478_, lean_object* v_acc_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Std_HashMap_Raw_all___redArg___lam__0(v_p_1474_, v___x_1475_, v___x_1476_, v_a_1477_, v_b_1478_, v_acc_1479_);
lean_dec_ref(v_acc_1479_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__1(lean_object* v___x_1481_, lean_object* v___f_1482_, lean_object* v_a_1483_, lean_object* v_x_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1481_, v___f_1482_, v_a_1483_, v___y_1485_);
return v___x_1486_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all___redArg(lean_object* v_m_1490_, lean_object* v_p_1491_){
_start:
{
lean_object* v___x_1492_; lean_object* v_buckets_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___f_1496_; lean_object* v___f_1497_; size_t v_sz_1498_; size_t v___x_1499_; lean_object* v___x_1500_; lean_object* v_fst_1501_; 
v___x_1492_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1493_ = lean_ctor_get(v_m_1490_, 1);
lean_inc_ref(v_buckets_1493_);
lean_dec_ref(v_m_1490_);
v___x_1494_ = lean_box(0);
v___x_1495_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1496_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1496_, 0, v_p_1491_);
lean_closure_set(v___f_1496_, 1, v___x_1494_);
lean_closure_set(v___f_1496_, 2, v___x_1495_);
v___f_1497_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1497_, 0, v___x_1492_);
lean_closure_set(v___f_1497_, 1, v___f_1496_);
v_sz_1498_ = lean_array_size(v_buckets_1493_);
v___x_1499_ = ((size_t)0ULL);
v___x_1500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1492_, v_buckets_1493_, v___f_1497_, v_sz_1498_, v___x_1499_, v___x_1495_);
v_fst_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_fst_1501_);
lean_dec(v___x_1500_);
if (lean_obj_tag(v_fst_1501_) == 0)
{
uint8_t v___x_1502_; 
v___x_1502_ = 1;
return v___x_1502_;
}
else
{
lean_object* v_val_1503_; uint8_t v___x_1504_; 
v_val_1503_ = lean_ctor_get(v_fst_1501_, 0);
lean_inc(v_val_1503_);
lean_dec_ref_known(v_fst_1501_, 1);
v___x_1504_ = lean_unbox(v_val_1503_);
lean_dec(v_val_1503_);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___boxed(lean_object* v_m_1505_, lean_object* v_p_1506_){
_start:
{
uint8_t v_res_1507_; lean_object* v_r_1508_; 
v_res_1507_ = l_Std_HashMap_Raw_all___redArg(v_m_1505_, v_p_1506_);
v_r_1508_ = lean_box(v_res_1507_);
return v_r_1508_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all(lean_object* v_00_u03b1_1509_, lean_object* v_00_u03b2_1510_, lean_object* v_m_1511_, lean_object* v_p_1512_){
_start:
{
lean_object* v___x_1513_; lean_object* v_buckets_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___f_1517_; lean_object* v___f_1518_; size_t v_sz_1519_; size_t v___x_1520_; lean_object* v___x_1521_; lean_object* v_fst_1522_; 
v___x_1513_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1514_ = lean_ctor_get(v_m_1511_, 1);
lean_inc_ref(v_buckets_1514_);
lean_dec_ref(v_m_1511_);
v___x_1515_ = lean_box(0);
v___x_1516_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1517_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1517_, 0, v_p_1512_);
lean_closure_set(v___f_1517_, 1, v___x_1515_);
lean_closure_set(v___f_1517_, 2, v___x_1516_);
v___f_1518_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1518_, 0, v___x_1513_);
lean_closure_set(v___f_1518_, 1, v___f_1517_);
v_sz_1519_ = lean_array_size(v_buckets_1514_);
v___x_1520_ = ((size_t)0ULL);
v___x_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1513_, v_buckets_1514_, v___f_1518_, v_sz_1519_, v___x_1520_, v___x_1516_);
v_fst_1522_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_fst_1522_);
lean_dec(v___x_1521_);
if (lean_obj_tag(v_fst_1522_) == 0)
{
uint8_t v___x_1523_; 
v___x_1523_ = 1;
return v___x_1523_;
}
else
{
lean_object* v_val_1524_; uint8_t v___x_1525_; 
v_val_1524_ = lean_ctor_get(v_fst_1522_, 0);
lean_inc(v_val_1524_);
lean_dec_ref_known(v_fst_1522_, 1);
v___x_1525_ = lean_unbox(v_val_1524_);
lean_dec(v_val_1524_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___boxed(lean_object* v_00_u03b1_1526_, lean_object* v_00_u03b2_1527_, lean_object* v_m_1528_, lean_object* v_p_1529_){
_start:
{
uint8_t v_res_1530_; lean_object* v_r_1531_; 
v_res_1530_ = l_Std_HashMap_Raw_all(v_00_u03b1_1526_, v_00_u03b2_1527_, v_m_1528_, v_p_1529_);
v_r_1531_ = lean_box(v_res_1530_);
return v_r_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0(lean_object* v_p_1532_, lean_object* v___x_1533_, lean_object* v___x_1534_, lean_object* v_a_1535_, lean_object* v_b_1536_, lean_object* v_acc_1537_){
_start:
{
lean_object* v___x_1538_; uint8_t v___x_1539_; 
v___x_1538_ = lean_apply_2(v_p_1532_, v_a_1535_, v_b_1536_);
v___x_1539_ = lean_unbox(v___x_1538_);
if (v___x_1539_ == 0)
{
lean_object* v___x_1540_; 
v___x_1540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1533_);
return v___x_1540_;
}
else
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
lean_dec_ref(v___x_1533_);
v___x_1541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1538_);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
lean_ctor_set(v___x_1542_, 1, v___x_1534_);
v___x_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
return v___x_1543_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1544_, lean_object* v___x_1545_, lean_object* v___x_1546_, lean_object* v_a_1547_, lean_object* v_b_1548_, lean_object* v_acc_1549_){
_start:
{
lean_object* v_res_1550_; 
v_res_1550_ = l_Std_HashMap_Raw_any___redArg___lam__0(v_p_1544_, v___x_1545_, v___x_1546_, v_a_1547_, v_b_1548_, v_acc_1549_);
lean_dec_ref(v_acc_1549_);
return v_res_1550_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any___redArg(lean_object* v_m_1551_, lean_object* v_p_1552_){
_start:
{
lean_object* v___x_1553_; lean_object* v_buckets_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___f_1557_; lean_object* v___f_1558_; size_t v_sz_1559_; size_t v___x_1560_; lean_object* v___x_1561_; lean_object* v_fst_1562_; 
v___x_1553_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1554_ = lean_ctor_get(v_m_1551_, 1);
lean_inc_ref(v_buckets_1554_);
lean_dec_ref(v_m_1551_);
v___x_1555_ = lean_box(0);
v___x_1556_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1557_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1557_, 0, v_p_1552_);
lean_closure_set(v___f_1557_, 1, v___x_1556_);
lean_closure_set(v___f_1557_, 2, v___x_1555_);
v___f_1558_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1558_, 0, v___x_1553_);
lean_closure_set(v___f_1558_, 1, v___f_1557_);
v_sz_1559_ = lean_array_size(v_buckets_1554_);
v___x_1560_ = ((size_t)0ULL);
v___x_1561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1553_, v_buckets_1554_, v___f_1558_, v_sz_1559_, v___x_1560_, v___x_1556_);
v_fst_1562_ = lean_ctor_get(v___x_1561_, 0);
lean_inc(v_fst_1562_);
lean_dec(v___x_1561_);
if (lean_obj_tag(v_fst_1562_) == 0)
{
uint8_t v___x_1563_; 
v___x_1563_ = 0;
return v___x_1563_;
}
else
{
lean_object* v_val_1564_; uint8_t v___x_1565_; 
v_val_1564_ = lean_ctor_get(v_fst_1562_, 0);
lean_inc(v_val_1564_);
lean_dec_ref_known(v_fst_1562_, 1);
v___x_1565_ = lean_unbox(v_val_1564_);
lean_dec(v_val_1564_);
return v___x_1565_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___boxed(lean_object* v_m_1566_, lean_object* v_p_1567_){
_start:
{
uint8_t v_res_1568_; lean_object* v_r_1569_; 
v_res_1568_ = l_Std_HashMap_Raw_any___redArg(v_m_1566_, v_p_1567_);
v_r_1569_ = lean_box(v_res_1568_);
return v_r_1569_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any(lean_object* v_00_u03b1_1570_, lean_object* v_00_u03b2_1571_, lean_object* v_m_1572_, lean_object* v_p_1573_){
_start:
{
lean_object* v___x_1574_; lean_object* v_buckets_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___f_1578_; lean_object* v___f_1579_; size_t v_sz_1580_; size_t v___x_1581_; lean_object* v___x_1582_; lean_object* v_fst_1583_; 
v___x_1574_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1575_ = lean_ctor_get(v_m_1572_, 1);
lean_inc_ref(v_buckets_1575_);
lean_dec_ref(v_m_1572_);
v___x_1576_ = lean_box(0);
v___x_1577_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1578_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1578_, 0, v_p_1573_);
lean_closure_set(v___f_1578_, 1, v___x_1577_);
lean_closure_set(v___f_1578_, 2, v___x_1576_);
v___f_1579_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1579_, 0, v___x_1574_);
lean_closure_set(v___f_1579_, 1, v___f_1578_);
v_sz_1580_ = lean_array_size(v_buckets_1575_);
v___x_1581_ = ((size_t)0ULL);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1574_, v_buckets_1575_, v___f_1579_, v_sz_1580_, v___x_1581_, v___x_1577_);
v_fst_1583_ = lean_ctor_get(v___x_1582_, 0);
lean_inc(v_fst_1583_);
lean_dec(v___x_1582_);
if (lean_obj_tag(v_fst_1583_) == 0)
{
uint8_t v___x_1584_; 
v___x_1584_ = 0;
return v___x_1584_;
}
else
{
lean_object* v_val_1585_; uint8_t v___x_1586_; 
v_val_1585_ = lean_ctor_get(v_fst_1583_, 0);
lean_inc(v_val_1585_);
lean_dec_ref_known(v_fst_1583_, 1);
v___x_1586_ = lean_unbox(v_val_1585_);
lean_dec(v_val_1585_);
return v___x_1586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___boxed(lean_object* v_00_u03b1_1587_, lean_object* v_00_u03b2_1588_, lean_object* v_m_1589_, lean_object* v_p_1590_){
_start:
{
uint8_t v_res_1591_; lean_object* v_r_1592_; 
v_res_1591_ = l_Std_HashMap_Raw_any(v_00_u03b1_1587_, v_00_u03b2_1588_, v_m_1589_, v_p_1590_);
v_r_1592_ = lean_box(v_res_1591_);
return v_r_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_a_1595_, lean_object* v_b_1596_, lean_object* v_acc_1597_){
_start:
{
lean_object* v_r_1598_; lean_object* v___x_1599_; 
v_r_1598_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1593_, v_inst_1594_, v_acc_1597_, v_a_1595_, v_b_1596_);
v___x_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1599_, 0, v_r_1598_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__1(lean_object* v___x_1600_, lean_object* v___f_1601_, lean_object* v_a_1602_, lean_object* v_x_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v___x_1605_; 
v___x_1605_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1600_, v___f_1601_, v_a_1602_, v___y_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg(lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_m_u2081_1610_, lean_object* v_m_u2082_1611_){
_start:
{
lean_object* v_size_1612_; lean_object* v_buckets_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; uint8_t v___x_1616_; 
v_size_1612_ = lean_ctor_get(v_m_u2081_1610_, 0);
v_buckets_1613_ = lean_ctor_get(v_m_u2081_1610_, 1);
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1615_ = lean_array_get_size(v_buckets_1613_);
v___x_1616_ = lean_nat_dec_lt(v___x_1614_, v___x_1615_);
if (v___x_1616_ == 0)
{
lean_dec_ref(v_m_u2081_1610_);
lean_dec_ref(v_inst_1609_);
lean_dec_ref(v_inst_1608_);
return v_m_u2082_1611_;
}
else
{
lean_object* v_size_1617_; lean_object* v_buckets_1618_; lean_object* v___x_1619_; uint8_t v___x_1620_; 
v_size_1617_ = lean_ctor_get(v_m_u2082_1611_, 0);
v_buckets_1618_ = lean_ctor_get(v_m_u2082_1611_, 1);
v___x_1619_ = lean_array_get_size(v_buckets_1618_);
v___x_1620_ = lean_nat_dec_lt(v___x_1614_, v___x_1619_);
if (v___x_1620_ == 0)
{
lean_dec_ref(v_m_u2082_1611_);
lean_dec_ref(v_inst_1609_);
lean_dec_ref(v_inst_1608_);
return v_m_u2081_1610_;
}
else
{
lean_object* v___x_1621_; uint8_t v___x_1622_; 
v___x_1621_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1622_ = lean_nat_dec_le(v_size_1612_, v_size_1617_);
if (v___x_1622_ == 0)
{
lean_object* v___f_1623_; lean_object* v___x_1624_; 
v___f_1623_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1624_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1623_, v_inst_1608_, v_inst_1609_, v_m_u2081_1610_, v_m_u2082_1611_);
return v___x_1624_;
}
else
{
lean_object* v___f_1625_; lean_object* v___f_1626_; size_t v_sz_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
lean_inc_ref(v_buckets_1613_);
lean_dec_ref(v_m_u2081_1610_);
v___f_1625_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1625_, 0, v_inst_1608_);
lean_closure_set(v___f_1625_, 1, v_inst_1609_);
v___f_1626_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1626_, 0, v___x_1621_);
lean_closure_set(v___f_1626_, 1, v___f_1625_);
v_sz_1627_ = lean_array_size(v_buckets_1613_);
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1621_, v_buckets_1613_, v___f_1626_, v_sz_1627_, v___x_1628_, v_m_u2082_1611_);
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union(lean_object* v_00_u03b1_1630_, lean_object* v_00_u03b2_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_m_u2081_1634_, lean_object* v_m_u2082_1635_){
_start:
{
lean_object* v_size_1636_; lean_object* v_buckets_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; uint8_t v___x_1640_; 
v_size_1636_ = lean_ctor_get(v_m_u2081_1634_, 0);
v_buckets_1637_ = lean_ctor_get(v_m_u2081_1634_, 1);
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_array_get_size(v_buckets_1637_);
v___x_1640_ = lean_nat_dec_lt(v___x_1638_, v___x_1639_);
if (v___x_1640_ == 0)
{
lean_dec_ref(v_m_u2081_1634_);
lean_dec_ref(v_inst_1633_);
lean_dec_ref(v_inst_1632_);
return v_m_u2082_1635_;
}
else
{
lean_object* v_size_1641_; lean_object* v_buckets_1642_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v_size_1641_ = lean_ctor_get(v_m_u2082_1635_, 0);
v_buckets_1642_ = lean_ctor_get(v_m_u2082_1635_, 1);
v___x_1643_ = lean_array_get_size(v_buckets_1642_);
v___x_1644_ = lean_nat_dec_lt(v___x_1638_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_dec_ref(v_m_u2082_1635_);
lean_dec_ref(v_inst_1633_);
lean_dec_ref(v_inst_1632_);
return v_m_u2081_1634_;
}
else
{
lean_object* v___x_1645_; uint8_t v___x_1646_; 
v___x_1645_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1646_ = lean_nat_dec_le(v_size_1636_, v_size_1641_);
if (v___x_1646_ == 0)
{
lean_object* v___f_1647_; lean_object* v___x_1648_; 
v___f_1647_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1648_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1647_, v_inst_1632_, v_inst_1633_, v_m_u2081_1634_, v_m_u2082_1635_);
return v___x_1648_;
}
else
{
lean_object* v___f_1649_; lean_object* v___f_1650_; size_t v_sz_1651_; size_t v___x_1652_; lean_object* v___x_1653_; 
lean_inc_ref(v_buckets_1637_);
lean_dec_ref(v_m_u2081_1634_);
v___f_1649_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1649_, 0, v_inst_1632_);
lean_closure_set(v___f_1649_, 1, v_inst_1633_);
v___f_1650_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1650_, 0, v___x_1645_);
lean_closure_set(v___f_1650_, 1, v___f_1649_);
v_sz_1651_ = lean_array_size(v_buckets_1637_);
v___x_1652_ = ((size_t)0ULL);
v___x_1653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1645_, v_buckets_1637_, v___f_1650_, v_sz_1651_, v___x_1652_, v_m_u2082_1635_);
return v___x_1653_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter___redArg(lean_object* v_inst_1654_, lean_object* v_inst_1655_, lean_object* v_m_u2081_1656_, lean_object* v_m_u2082_1657_){
_start:
{
lean_object* v_buckets_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; uint8_t v___x_1661_; 
v_buckets_1658_ = lean_ctor_get(v_m_u2081_1656_, 1);
v___x_1659_ = lean_unsigned_to_nat(0u);
v___x_1660_ = lean_array_get_size(v_buckets_1658_);
v___x_1661_ = lean_nat_dec_lt(v___x_1659_, v___x_1660_);
if (v___x_1661_ == 0)
{
lean_dec_ref(v_m_u2081_1656_);
lean_dec_ref(v_inst_1655_);
lean_dec_ref(v_inst_1654_);
return v_m_u2082_1657_;
}
else
{
lean_object* v_buckets_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v_buckets_1662_ = lean_ctor_get(v_m_u2082_1657_, 1);
v___x_1663_ = lean_array_get_size(v_buckets_1662_);
v___x_1664_ = lean_nat_dec_lt(v___x_1659_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_dec_ref(v_m_u2082_1657_);
lean_dec_ref(v_inst_1655_);
lean_dec_ref(v_inst_1654_);
return v_m_u2081_1656_;
}
else
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1654_, v_inst_1655_, v_m_u2081_1656_, v_m_u2082_1657_);
return v___x_1665_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter(lean_object* v_00_u03b1_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_inst_1668_, lean_object* v_inst_1669_, lean_object* v_m_u2081_1670_, lean_object* v_m_u2082_1671_){
_start:
{
lean_object* v_buckets_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v_buckets_1672_ = lean_ctor_get(v_m_u2081_1670_, 1);
v___x_1673_ = lean_unsigned_to_nat(0u);
v___x_1674_ = lean_array_get_size(v_buckets_1672_);
v___x_1675_ = lean_nat_dec_lt(v___x_1673_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_dec_ref(v_m_u2081_1670_);
lean_dec_ref(v_inst_1669_);
lean_dec_ref(v_inst_1668_);
return v_m_u2082_1671_;
}
else
{
lean_object* v_buckets_1676_; lean_object* v___x_1677_; uint8_t v___x_1678_; 
v_buckets_1676_ = lean_ctor_get(v_m_u2082_1671_, 1);
v___x_1677_ = lean_array_get_size(v_buckets_1676_);
v___x_1678_ = lean_nat_dec_lt(v___x_1673_, v___x_1677_);
if (v___x_1678_ == 0)
{
lean_dec_ref(v_m_u2082_1671_);
lean_dec_ref(v_inst_1669_);
lean_dec_ref(v_inst_1668_);
return v_m_u2081_1670_;
}
else
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1668_, v_inst_1669_, v_m_u2081_1670_, v_m_u2082_1671_);
return v___x_1679_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_1680_, lean_object* v_inst_1681_, lean_object* v_m_u2082_1682_, uint8_t v___x_1683_, lean_object* v_k_1684_, lean_object* v_x_1685_){
_start:
{
uint8_t v___x_1686_; 
v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1680_, v_inst_1681_, v_m_u2082_1682_, v_k_1684_);
if (v___x_1686_ == 0)
{
return v___x_1683_;
}
else
{
uint8_t v___x_1687_; 
v___x_1687_ = 0;
return v___x_1687_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1688_, lean_object* v_inst_1689_, lean_object* v_m_u2082_1690_, lean_object* v___x_1691_, lean_object* v_k_1692_, lean_object* v_x_1693_){
_start:
{
uint8_t v___x_91__boxed_1694_; uint8_t v_res_1695_; lean_object* v_r_1696_; 
v___x_91__boxed_1694_ = lean_unbox(v___x_1691_);
v_res_1695_ = l_Std_HashMap_Raw_diff___redArg___lam__0(v_inst_1688_, v_inst_1689_, v_m_u2082_1690_, v___x_91__boxed_1694_, v_k_1692_, v_x_1693_);
lean_dec(v_x_1693_);
lean_dec_ref(v_m_u2082_1690_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg(lean_object* v_inst_1697_, lean_object* v_inst_1698_, lean_object* v_m_u2081_1699_, lean_object* v_m_u2082_1700_){
_start:
{
lean_object* v_size_1701_; lean_object* v_buckets_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v_size_1701_ = lean_ctor_get(v_m_u2081_1699_, 0);
v_buckets_1702_ = lean_ctor_get(v_m_u2081_1699_, 1);
v___x_1703_ = lean_unsigned_to_nat(0u);
v___x_1704_ = lean_array_get_size(v_buckets_1702_);
v___x_1705_ = lean_nat_dec_lt(v___x_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_dec_ref(v_m_u2081_1699_);
lean_dec_ref(v_inst_1698_);
lean_dec_ref(v_inst_1697_);
return v_m_u2082_1700_;
}
else
{
lean_object* v_size_1706_; lean_object* v_buckets_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_size_1706_ = lean_ctor_get(v_m_u2082_1700_, 0);
v_buckets_1707_ = lean_ctor_get(v_m_u2082_1700_, 1);
v___x_1708_ = lean_array_get_size(v_buckets_1707_);
v___x_1709_ = lean_nat_dec_lt(v___x_1703_, v___x_1708_);
if (v___x_1709_ == 0)
{
lean_dec_ref(v_m_u2082_1700_);
lean_dec_ref(v_inst_1698_);
lean_dec_ref(v_inst_1697_);
return v_m_u2081_1699_;
}
else
{
uint8_t v___x_1710_; 
v___x_1710_ = lean_nat_dec_le(v_size_1701_, v_size_1706_);
if (v___x_1710_ == 0)
{
lean_object* v___f_1711_; lean_object* v___x_1712_; 
v___f_1711_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1712_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1711_, v_inst_1697_, v_inst_1698_, v_m_u2081_1699_, v_m_u2082_1700_);
return v___x_1712_;
}
else
{
lean_object* v___x_1713_; lean_object* v___f_1714_; lean_object* v___x_1715_; 
v___x_1713_ = lean_box(v___x_1710_);
v___f_1714_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1714_, 0, v_inst_1697_);
lean_closure_set(v___f_1714_, 1, v_inst_1698_);
lean_closure_set(v___f_1714_, 2, v_m_u2082_1700_);
lean_closure_set(v___f_1714_, 3, v___x_1713_);
v___x_1715_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1714_, v_m_u2081_1699_);
return v___x_1715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff(lean_object* v_00_u03b1_1716_, lean_object* v_00_u03b2_1717_, lean_object* v_inst_1718_, lean_object* v_inst_1719_, lean_object* v_m_u2081_1720_, lean_object* v_m_u2082_1721_){
_start:
{
lean_object* v_size_1722_; lean_object* v_buckets_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; 
v_size_1722_ = lean_ctor_get(v_m_u2081_1720_, 0);
v_buckets_1723_ = lean_ctor_get(v_m_u2081_1720_, 1);
v___x_1724_ = lean_unsigned_to_nat(0u);
v___x_1725_ = lean_array_get_size(v_buckets_1723_);
v___x_1726_ = lean_nat_dec_lt(v___x_1724_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_dec_ref(v_m_u2081_1720_);
lean_dec_ref(v_inst_1719_);
lean_dec_ref(v_inst_1718_);
return v_m_u2082_1721_;
}
else
{
lean_object* v_size_1727_; lean_object* v_buckets_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v_size_1727_ = lean_ctor_get(v_m_u2082_1721_, 0);
v_buckets_1728_ = lean_ctor_get(v_m_u2082_1721_, 1);
v___x_1729_ = lean_array_get_size(v_buckets_1728_);
v___x_1730_ = lean_nat_dec_lt(v___x_1724_, v___x_1729_);
if (v___x_1730_ == 0)
{
lean_dec_ref(v_m_u2082_1721_);
lean_dec_ref(v_inst_1719_);
lean_dec_ref(v_inst_1718_);
return v_m_u2081_1720_;
}
else
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_nat_dec_le(v_size_1722_, v_size_1727_);
if (v___x_1731_ == 0)
{
lean_object* v___f_1732_; lean_object* v___x_1733_; 
v___f_1732_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1733_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1732_, v_inst_1718_, v_inst_1719_, v_m_u2081_1720_, v_m_u2082_1721_);
return v___x_1733_;
}
else
{
lean_object* v___x_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_box(v___x_1731_);
v___f_1735_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1735_, 0, v_inst_1718_);
lean_closure_set(v___f_1735_, 1, v_inst_1719_);
lean_closure_set(v___f_1735_, 2, v_m_u2082_1721_);
lean_closure_set(v___f_1735_, 3, v___x_1734_);
v___x_1736_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1735_, v_m_u2081_1720_);
return v___x_1736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1737_, lean_object* v_inst_1738_){
_start:
{
lean_object* v___x_1739_; 
v___x_1739_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1739_, 0, lean_box(0));
lean_closure_set(v___x_1739_, 1, lean_box(0));
lean_closure_set(v___x_1739_, 2, v_inst_1737_);
lean_closure_set(v___x_1739_, 3, v_inst_1738_);
return v___x_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1744_, 0, lean_box(0));
lean_closure_set(v___x_1744_, 1, lean_box(0));
lean_closure_set(v___x_1744_, 2, v_inst_1742_);
lean_closure_set(v___x_1744_, 3, v_inst_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1745_, lean_object* v_inst_1746_){
_start:
{
lean_object* v___x_1747_; 
v___x_1747_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1747_, 0, lean_box(0));
lean_closure_set(v___x_1747_, 1, lean_box(0));
lean_closure_set(v___x_1747_, 2, v_inst_1745_);
lean_closure_set(v___x_1747_, 3, v_inst_1746_);
return v___x_1747_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1748_, lean_object* v_00_u03b2_1749_, lean_object* v_inst_1750_, lean_object* v_inst_1751_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1752_, 0, lean_box(0));
lean_closure_set(v___x_1752_, 1, lean_box(0));
lean_closure_set(v___x_1752_, 2, v_inst_1750_);
lean_closure_set(v___x_1752_, 3, v_inst_1751_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1753_, lean_object* v_inst_1754_){
_start:
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1755_, 0, lean_box(0));
lean_closure_set(v___x_1755_, 1, lean_box(0));
lean_closure_set(v___x_1755_, 2, v_inst_1753_);
lean_closure_set(v___x_1755_, 3, v_inst_1754_);
return v___x_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1756_, lean_object* v_00_u03b2_1757_, lean_object* v_inst_1758_, lean_object* v_inst_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1760_, 0, lean_box(0));
lean_closure_set(v___x_1760_, 1, lean_box(0));
lean_closure_set(v___x_1760_, 2, v_inst_1758_);
lean_closure_set(v___x_1760_, 3, v_inst_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq___redArg(lean_object* v_inst_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_m_u2081_1764_, lean_object* v_m_u2082_1765_){
_start:
{
uint8_t v___x_1766_; 
v___x_1766_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1761_, v_inst_1762_, v_inst_1763_, v_m_u2081_1764_, v_m_u2082_1765_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___redArg___boxed(lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_inst_1769_, lean_object* v_m_u2081_1770_, lean_object* v_m_u2082_1771_){
_start:
{
uint8_t v_res_1772_; lean_object* v_r_1773_; 
v_res_1772_ = l_Std_HashMap_Raw_beq___redArg(v_inst_1767_, v_inst_1768_, v_inst_1769_, v_m_u2081_1770_, v_m_u2082_1771_);
v_r_1773_ = lean_box(v_res_1772_);
return v_r_1773_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq(lean_object* v_00_u03b1_1774_, lean_object* v_00_u03b2_1775_, lean_object* v_inst_1776_, lean_object* v_inst_1777_, lean_object* v_inst_1778_, lean_object* v_m_u2081_1779_, lean_object* v_m_u2082_1780_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1776_, v_inst_1777_, v_inst_1778_, v_m_u2081_1779_, v_m_u2082_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___boxed(lean_object* v_00_u03b1_1782_, lean_object* v_00_u03b2_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_m_u2081_1787_, lean_object* v_m_u2082_1788_){
_start:
{
uint8_t v_res_1789_; lean_object* v_r_1790_; 
v_res_1789_ = l_Std_HashMap_Raw_beq(v_00_u03b1_1782_, v_00_u03b2_1783_, v_inst_1784_, v_inst_1785_, v_inst_1786_, v_m_u2081_1787_, v_m_u2082_1788_);
v_r_1790_ = lean_box(v_res_1789_);
return v_r_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1794_, 0, lean_box(0));
lean_closure_set(v___x_1794_, 1, lean_box(0));
lean_closure_set(v___x_1794_, 2, v_inst_1791_);
lean_closure_set(v___x_1794_, 3, v_inst_1792_);
lean_closure_set(v___x_1794_, 4, v_inst_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1795_, lean_object* v_00_u03b2_1796_, lean_object* v_inst_1797_, lean_object* v_inst_1798_, lean_object* v_inst_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1800_, 0, lean_box(0));
lean_closure_set(v___x_1800_, 1, lean_box(0));
lean_closure_set(v___x_1800_, 2, v_inst_1797_);
lean_closure_set(v___x_1800_, 3, v_inst_1798_);
lean_closure_set(v___x_1800_, 4, v_inst_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg(lean_object* v_f_1801_, lean_object* v_m_1802_){
_start:
{
lean_object* v_buckets_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; uint8_t v___x_1806_; 
v_buckets_1803_ = lean_ctor_get(v_m_1802_, 1);
v___x_1804_ = lean_unsigned_to_nat(0u);
v___x_1805_ = lean_array_get_size(v_buckets_1803_);
v___x_1806_ = lean_nat_dec_lt(v___x_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; 
lean_dec_ref(v_m_1802_);
lean_dec_ref(v_f_1801_);
v___x_1807_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1807_;
}
else
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1801_, v_m_1802_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object* v_00_u03b1_1809_, lean_object* v_00_u03b2_1810_, lean_object* v_00_u03b3_1811_, lean_object* v_f_1812_, lean_object* v_m_1813_){
_start:
{
lean_object* v_buckets_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_buckets_1814_ = lean_ctor_get(v_m_1813_, 1);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_array_get_size(v_buckets_1814_);
v___x_1817_ = lean_nat_dec_lt(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; 
lean_dec_ref(v_m_1813_);
lean_dec_ref(v_f_1812_);
v___x_1818_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1818_;
}
else
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1812_, v_m_1813_);
return v___x_1819_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object* v_f_1820_, lean_object* v_m_1821_){
_start:
{
lean_object* v_buckets_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v_buckets_1822_ = lean_ctor_get(v_m_1821_, 1);
v___x_1823_ = lean_unsigned_to_nat(0u);
v___x_1824_ = lean_array_get_size(v_buckets_1822_);
v___x_1825_ = lean_nat_dec_lt(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; 
lean_dec_ref(v_m_1821_);
lean_dec(v_f_1820_);
v___x_1826_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1826_;
}
else
{
lean_object* v___x_1827_; 
v___x_1827_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1820_, v_m_1821_);
return v___x_1827_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object* v_00_u03b1_1828_, lean_object* v_00_u03b2_1829_, lean_object* v_00_u03b3_1830_, lean_object* v_f_1831_, lean_object* v_m_1832_){
_start:
{
lean_object* v_buckets_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; uint8_t v___x_1836_; 
v_buckets_1833_ = lean_ctor_get(v_m_1832_, 1);
v___x_1834_ = lean_unsigned_to_nat(0u);
v___x_1835_ = lean_array_get_size(v_buckets_1833_);
v___x_1836_ = lean_nat_dec_lt(v___x_1834_, v___x_1835_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; 
lean_dec_ref(v_m_1832_);
lean_dec(v_f_1831_);
v___x_1837_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1837_;
}
else
{
lean_object* v___x_1838_; 
v___x_1838_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1831_, v_m_1832_);
return v___x_1838_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object* v_f_1839_, lean_object* v_m_1840_){
_start:
{
lean_object* v_buckets_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_buckets_1841_ = lean_ctor_get(v_m_1840_, 1);
v___x_1842_ = lean_unsigned_to_nat(0u);
v___x_1843_ = lean_array_get_size(v_buckets_1841_);
v___x_1844_ = lean_nat_dec_lt(v___x_1842_, v___x_1843_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_dec_ref(v_m_1840_);
lean_dec_ref(v_f_1839_);
v___x_1845_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; 
v___x_1846_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1839_, v_m_1840_);
return v___x_1846_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object* v_00_u03b1_1847_, lean_object* v_00_u03b2_1848_, lean_object* v_f_1849_, lean_object* v_m_1850_){
_start:
{
lean_object* v_buckets_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v_buckets_1851_ = lean_ctor_get(v_m_1850_, 1);
v___x_1852_ = lean_unsigned_to_nat(0u);
v___x_1853_ = lean_array_get_size(v_buckets_1851_);
v___x_1854_ = lean_nat_dec_lt(v___x_1852_, v___x_1853_);
if (v___x_1854_ == 0)
{
lean_object* v___x_1855_; 
lean_dec_ref(v_m_1850_);
lean_dec_ref(v_f_1849_);
v___x_1855_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1855_;
}
else
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1849_, v_m_1850_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1857_, lean_object* v_x2_1858_, lean_object* v_x3_1859_){
_start:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1860_, 0, v_x2_1858_);
lean_ctor_set(v___x_1860_, 1, v_x3_1859_);
v___x_1861_ = lean_array_push(v_x1_1857_, v___x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1862_, lean_object* v___f_1863_, lean_object* v_acc_1864_, lean_object* v_l_1865_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1862_, v___f_1863_, v_acc_1864_, v_l_1865_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object* v_m_1871_){
_start:
{
lean_object* v_size_1872_; lean_object* v_buckets_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
v_size_1872_ = lean_ctor_get(v_m_1871_, 0);
lean_inc(v_size_1872_);
v_buckets_1873_ = lean_ctor_get(v_m_1871_, 1);
lean_inc_ref(v_buckets_1873_);
lean_dec_ref(v_m_1871_);
v___x_1874_ = lean_mk_empty_array_with_capacity(v_size_1872_);
lean_dec(v_size_1872_);
v___x_1875_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_array_get_size(v_buckets_1873_);
v___x_1878_ = lean_nat_dec_lt(v___x_1876_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_dec_ref(v_buckets_1873_);
return v___x_1874_;
}
else
{
lean_object* v___f_1879_; size_t v___x_1880_; size_t v___x_1881_; lean_object* v___x_1882_; 
v___f_1879_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1880_ = ((size_t)0ULL);
v___x_1881_ = lean_usize_of_nat(v___x_1877_);
v___x_1882_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1875_, v___f_1879_, v_buckets_1873_, v___x_1880_, v___x_1881_, v___x_1874_);
return v___x_1882_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object* v_00_u03b1_1883_, lean_object* v_00_u03b2_1884_, lean_object* v_m_1885_){
_start:
{
lean_object* v_size_1886_; lean_object* v_buckets_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_size_1886_ = lean_ctor_get(v_m_1885_, 0);
lean_inc(v_size_1886_);
v_buckets_1887_ = lean_ctor_get(v_m_1885_, 1);
lean_inc_ref(v_buckets_1887_);
lean_dec_ref(v_m_1885_);
v___x_1888_ = lean_mk_empty_array_with_capacity(v_size_1886_);
lean_dec(v_size_1886_);
v___x_1889_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1890_ = lean_unsigned_to_nat(0u);
v___x_1891_ = lean_array_get_size(v_buckets_1887_);
v___x_1892_ = lean_nat_dec_lt(v___x_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_dec_ref(v_buckets_1887_);
return v___x_1888_;
}
else
{
lean_object* v___f_1893_; size_t v___x_1894_; size_t v___x_1895_; lean_object* v___x_1896_; 
v___f_1893_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1894_ = ((size_t)0ULL);
v___x_1895_ = lean_usize_of_nat(v___x_1891_);
v___x_1896_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1889_, v___f_1893_, v_buckets_1887_, v___x_1894_, v___x_1895_, v___x_1888_);
return v___x_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1897_, lean_object* v_x2_1898_, lean_object* v_x3_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_array_push(v_x1_1897_, v_x2_1898_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1901_, lean_object* v_x2_1902_, lean_object* v_x3_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Std_HashMap_Raw_keysArray___redArg___lam__0(v_x1_1901_, v_x2_1902_, v_x3_1903_);
lean_dec(v_x3_1903_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1905_, lean_object* v___f_1906_, lean_object* v_acc_1907_, lean_object* v_l_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1905_, v___f_1906_, v_acc_1907_, v_l_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object* v_m_1914_){
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
lean_object* v___f_1922_; size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v___f_1922_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = lean_usize_of_nat(v___x_1920_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1918_, v___f_1922_, v_buckets_1916_, v___x_1923_, v___x_1924_, v___x_1917_);
return v___x_1925_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object* v_00_u03b1_1926_, lean_object* v_00_u03b2_1927_, lean_object* v_m_1928_){
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
lean_object* v___f_1936_; size_t v___x_1937_; size_t v___x_1938_; lean_object* v___x_1939_; 
v___f_1936_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1937_ = ((size_t)0ULL);
v___x_1938_ = lean_usize_of_nat(v___x_1934_);
v___x_1939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1932_, v___f_1936_, v_buckets_1930_, v___x_1937_, v___x_1938_, v___x_1931_);
return v___x_1939_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object* v_a_1940_, lean_object* v_b_1941_, lean_object* v_d_1942_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1943_, 0, v_b_1941_);
lean_ctor_set(v___x_1943_, 1, v_d_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_1944_, lean_object* v_b_1945_, lean_object* v_d_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Std_HashMap_Raw_values___redArg___lam__0(v_a_1944_, v_b_1945_, v_d_1946_);
lean_dec(v_a_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object* v_m_1952_){
_start:
{
lean_object* v___x_1953_; lean_object* v_buckets_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; 
v___x_1953_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1954_ = lean_ctor_get(v_m_1952_, 1);
lean_inc_ref(v_buckets_1954_);
lean_dec_ref(v_m_1952_);
v___x_1955_ = lean_box(0);
v___x_1956_ = lean_array_get_size(v_buckets_1954_);
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_nat_dec_lt(v___x_1957_, v___x_1956_);
if (v___x_1958_ == 0)
{
lean_dec_ref(v_buckets_1954_);
return v___x_1955_;
}
else
{
lean_object* v___f_1959_; size_t v___x_1960_; size_t v___x_1961_; lean_object* v___x_1962_; 
v___f_1959_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_1960_ = lean_usize_of_nat(v___x_1956_);
v___x_1961_ = ((size_t)0ULL);
v___x_1962_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1953_, v___f_1959_, v_buckets_1954_, v___x_1960_, v___x_1961_, v___x_1955_);
return v___x_1962_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object* v_00_u03b1_1963_, lean_object* v_00_u03b2_1964_, lean_object* v_m_1965_){
_start:
{
lean_object* v___x_1966_; lean_object* v_buckets_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1966_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1967_ = lean_ctor_get(v_m_1965_, 1);
lean_inc_ref(v_buckets_1967_);
lean_dec_ref(v_m_1965_);
v___x_1968_ = lean_box(0);
v___x_1969_ = lean_array_get_size(v_buckets_1967_);
v___x_1970_ = lean_unsigned_to_nat(0u);
v___x_1971_ = lean_nat_dec_lt(v___x_1970_, v___x_1969_);
if (v___x_1971_ == 0)
{
lean_dec_ref(v_buckets_1967_);
return v___x_1968_;
}
else
{
lean_object* v___f_1972_; size_t v___x_1973_; size_t v___x_1974_; lean_object* v___x_1975_; 
v___f_1972_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_1973_ = lean_usize_of_nat(v___x_1969_);
v___x_1974_ = ((size_t)0ULL);
v___x_1975_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1966_, v___f_1972_, v_buckets_1967_, v___x_1973_, v___x_1974_, v___x_1968_);
return v___x_1975_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_1976_, lean_object* v_x2_1977_, lean_object* v_x3_1978_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_array_push(v_x1_1976_, v_x3_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_1980_, lean_object* v_x2_1981_, lean_object* v_x3_1982_){
_start:
{
lean_object* v_res_1983_; 
v_res_1983_ = l_Std_HashMap_Raw_valuesArray___redArg___lam__0(v_x1_1980_, v_x2_1981_, v_x3_1982_);
lean_dec(v_x2_1981_);
return v_res_1983_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg(lean_object* v_m_1988_){
_start:
{
lean_object* v_size_1989_; lean_object* v_buckets_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v_size_1989_ = lean_ctor_get(v_m_1988_, 0);
lean_inc(v_size_1989_);
v_buckets_1990_ = lean_ctor_get(v_m_1988_, 1);
lean_inc_ref(v_buckets_1990_);
lean_dec_ref(v_m_1988_);
v___x_1991_ = lean_mk_empty_array_with_capacity(v_size_1989_);
lean_dec(v_size_1989_);
v___x_1992_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = lean_array_get_size(v_buckets_1990_);
v___x_1995_ = lean_nat_dec_lt(v___x_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
lean_dec_ref(v_buckets_1990_);
return v___x_1991_;
}
else
{
lean_object* v___f_1996_; size_t v___x_1997_; size_t v___x_1998_; lean_object* v___x_1999_; 
v___f_1996_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_1997_ = ((size_t)0ULL);
v___x_1998_ = lean_usize_of_nat(v___x_1994_);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1992_, v___f_1996_, v_buckets_1990_, v___x_1997_, v___x_1998_, v___x_1991_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray(lean_object* v_00_u03b1_2000_, lean_object* v_00_u03b2_2001_, lean_object* v_m_2002_){
_start:
{
lean_object* v_size_2003_; lean_object* v_buckets_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_size_2003_ = lean_ctor_get(v_m_2002_, 0);
lean_inc(v_size_2003_);
v_buckets_2004_ = lean_ctor_get(v_m_2002_, 1);
lean_inc_ref(v_buckets_2004_);
lean_dec_ref(v_m_2002_);
v___x_2005_ = lean_mk_empty_array_with_capacity(v_size_2003_);
lean_dec(v_size_2003_);
v___x_2006_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2007_ = lean_unsigned_to_nat(0u);
v___x_2008_ = lean_array_get_size(v_buckets_2004_);
v___x_2009_ = lean_nat_dec_lt(v___x_2007_, v___x_2008_);
if (v___x_2009_ == 0)
{
lean_dec_ref(v_buckets_2004_);
return v___x_2005_;
}
else
{
lean_object* v___f_2010_; size_t v___x_2011_; size_t v___x_2012_; lean_object* v___x_2013_; 
v___f_2010_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2011_ = ((size_t)0ULL);
v___x_2012_ = lean_usize_of_nat(v___x_2008_);
v___x_2013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2006_, v___f_2010_, v_buckets_2004_, v___x_2011_, v___x_2012_, v___x_2005_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany___redArg(lean_object* v_inst_2014_, lean_object* v_inst_2015_, lean_object* v_inst_2016_, lean_object* v_m_2017_, lean_object* v_l_2018_){
_start:
{
lean_object* v_buckets_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; uint8_t v___x_2022_; 
v_buckets_2019_ = lean_ctor_get(v_m_2017_, 1);
v___x_2020_ = lean_unsigned_to_nat(0u);
v___x_2021_ = lean_array_get_size(v_buckets_2019_);
v___x_2022_ = lean_nat_dec_lt(v___x_2020_, v___x_2021_);
if (v___x_2022_ == 0)
{
lean_dec(v_l_2018_);
lean_dec(v_inst_2016_);
lean_dec_ref(v_inst_2015_);
lean_dec_ref(v_inst_2014_);
return v_m_2017_;
}
else
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2016_, v_inst_2014_, v_inst_2015_, v_m_2017_, v_l_2018_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany(lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_inst_2026_, lean_object* v_inst_2027_, lean_object* v_00_u03c1_2028_, lean_object* v_inst_2029_, lean_object* v_m_2030_, lean_object* v_l_2031_){
_start:
{
lean_object* v_buckets_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; uint8_t v___x_2035_; 
v_buckets_2032_ = lean_ctor_get(v_m_2030_, 1);
v___x_2033_ = lean_unsigned_to_nat(0u);
v___x_2034_ = lean_array_get_size(v_buckets_2032_);
v___x_2035_ = lean_nat_dec_lt(v___x_2033_, v___x_2034_);
if (v___x_2035_ == 0)
{
lean_dec(v_l_2031_);
lean_dec(v_inst_2029_);
lean_dec_ref(v_inst_2027_);
lean_dec_ref(v_inst_2026_);
return v_m_2030_;
}
else
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2029_, v_inst_2026_, v_inst_2027_, v_m_2030_, v_l_2031_);
return v___x_2036_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_inst_2037_, lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_m_2040_, lean_object* v_l_2041_){
_start:
{
lean_object* v_buckets_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v_buckets_2042_ = lean_ctor_get(v_m_2040_, 1);
v___x_2043_ = lean_unsigned_to_nat(0u);
v___x_2044_ = lean_array_get_size(v_buckets_2042_);
v___x_2045_ = lean_nat_dec_lt(v___x_2043_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_dec(v_l_2041_);
lean_dec(v_inst_2039_);
lean_dec_ref(v_inst_2038_);
lean_dec_ref(v_inst_2037_);
return v_m_2040_;
}
else
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2039_, v_inst_2037_, v_inst_2038_, v_m_2040_, v_l_2041_);
return v___x_2046_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2047_, lean_object* v_inst_2048_, lean_object* v_inst_2049_, lean_object* v_00_u03c1_2050_, lean_object* v_inst_2051_, lean_object* v_m_2052_, lean_object* v_l_2053_){
_start:
{
lean_object* v_buckets_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; uint8_t v___x_2057_; 
v_buckets_2054_ = lean_ctor_get(v_m_2052_, 1);
v___x_2055_ = lean_unsigned_to_nat(0u);
v___x_2056_ = lean_array_get_size(v_buckets_2054_);
v___x_2057_ = lean_nat_dec_lt(v___x_2055_, v___x_2056_);
if (v___x_2057_ == 0)
{
lean_dec(v_l_2053_);
lean_dec(v_inst_2051_);
lean_dec_ref(v_inst_2049_);
lean_dec_ref(v_inst_2048_);
return v_m_2052_;
}
else
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2051_, v_inst_2048_, v_inst_2049_, v_m_2052_, v_l_2053_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray___redArg(lean_object* v_inst_2059_, lean_object* v_inst_2060_, lean_object* v_l_2061_){
_start:
{
lean_object* v___x_2062_; uint8_t v___x_2063_; 
v___x_2062_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_2063_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2063_ == 0)
{
lean_dec_ref(v_l_2061_);
lean_dec_ref(v_inst_2060_);
lean_dec_ref(v_inst_2059_);
return v___x_2062_;
}
else
{
lean_object* v___f_2064_; lean_object* v___x_2065_; 
v___f_2064_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2064_, v_inst_2059_, v_inst_2060_, v___x_2062_, v_l_2061_);
return v___x_2065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray(lean_object* v_00_u03b1_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_l_2069_){
_start:
{
lean_object* v___x_2070_; uint8_t v___x_2071_; 
v___x_2070_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_2071_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2071_ == 0)
{
lean_dec_ref(v_l_2069_);
lean_dec_ref(v_inst_2068_);
lean_dec_ref(v_inst_2067_);
return v___x_2070_;
}
else
{
lean_object* v___f_2072_; lean_object* v___x_2073_; 
v___f_2072_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2072_, v_inst_2067_, v_inst_2068_, v___x_2070_, v_l_2069_);
return v___x_2073_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Std_HashMap_Raw_Internal_numBuckets___redArg(v_m_2076_);
lean_dec_ref(v_m_2076_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2078_, lean_object* v_00_u03b2_2079_, lean_object* v_m_2080_){
_start:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2080_);
return v___x_2081_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2082_, lean_object* v_00_u03b2_2083_, lean_object* v_m_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_Std_HashMap_Raw_Internal_numBuckets(v_00_u03b1_2082_, v_00_u03b2_2083_, v_m_2084_);
lean_dec_ref(v_m_2084_);
return v_res_2085_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2089_, lean_object* v___f_2090_, lean_object* v_m_2091_, lean_object* v_prec_2092_){
_start:
{
lean_object* v___x_2093_; lean_object* v_buckets_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2114_; 
v___x_2093_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2094_ = lean_ctor_get(v_m_2091_, 1);
v_isSharedCheck_2114_ = !lean_is_exclusive(v_m_2091_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; 
v_unused_2115_ = lean_ctor_get(v_m_2091_, 0);
lean_dec(v_unused_2115_);
v___x_2096_ = v_m_2091_;
v_isShared_2097_ = v_isSharedCheck_2114_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_buckets_2094_);
lean_dec(v_m_2091_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2114_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v___x_2098_; lean_object* v___y_2100_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; 
v___x_2098_ = ((lean_object*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2106_ = lean_box(0);
v___x_2107_ = lean_array_get_size(v_buckets_2094_);
v___x_2108_ = lean_unsigned_to_nat(0u);
v___x_2109_ = lean_nat_dec_lt(v___x_2108_, v___x_2107_);
if (v___x_2109_ == 0)
{
lean_dec_ref(v_buckets_2094_);
lean_dec_ref(v___f_2090_);
v___y_2100_ = v___x_2106_;
goto v___jp_2099_;
}
else
{
lean_object* v___f_2110_; size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
v___f_2110_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2110_, 0, v___x_2093_);
lean_closure_set(v___f_2110_, 1, v___f_2090_);
v___x_2111_ = lean_usize_of_nat(v___x_2107_);
v___x_2112_ = ((size_t)0ULL);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2093_, v___f_2110_, v_buckets_2094_, v___x_2111_, v___x_2112_, v___x_2106_);
v___y_2100_ = v___x_2113_;
goto v___jp_2099_;
}
v___jp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2103_; 
v___x_2101_ = l_List_repr___redArg(v___x_2089_, v___y_2100_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set_tag(v___x_2096_, 5);
lean_ctor_set(v___x_2096_, 1, v___x_2101_);
lean_ctor_set(v___x_2096_, 0, v___x_2098_);
v___x_2103_ = v___x_2096_;
goto v_reusejp_2102_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2098_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2101_);
v___x_2103_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2102_;
}
v_reusejp_2102_:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Repr_addAppParen(v___x_2103_, v_prec_2092_);
return v___x_2104_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2116_, lean_object* v___f_2117_, lean_object* v_m_2118_, lean_object* v_prec_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2(v___x_2116_, v___f_2117_, v_m_2118_, v_prec_2119_);
lean_dec(v_prec_2119_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object* v_inst_2121_, lean_object* v_inst_2122_){
_start:
{
lean_object* v___f_2123_; lean_object* v___f_2124_; lean_object* v___x_2125_; lean_object* v___f_2126_; 
v___f_2123_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__0));
v___f_2124_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2124_, 0, v_inst_2122_);
v___x_2125_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2125_, 0, lean_box(0));
lean_closure_set(v___x_2125_, 1, lean_box(0));
lean_closure_set(v___x_2125_, 2, v_inst_2121_);
lean_closure_set(v___x_2125_, 3, v___f_2124_);
v___f_2126_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2126_, 0, v___x_2125_);
lean_closure_set(v___f_2126_, 1, v___f_2123_);
return v___f_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object* v_00_u03b1_2127_, lean_object* v_00_u03b2_2128_, lean_object* v_inst_2129_, lean_object* v_inst_2130_){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Std_HashMap_Raw_instRepr___redArg(v_inst_2129_, v_inst_2130_);
return v___x_2131_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Raw(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
