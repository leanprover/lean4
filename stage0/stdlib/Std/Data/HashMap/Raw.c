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
lean_object* lean_array_mark_linear(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_markLinear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_markLinear(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_markLinear___redArg(lean_object* v_m_41_){
_start:
{
lean_object* v_size_42_; lean_object* v_buckets_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_size_42_ = lean_ctor_get(v_m_41_, 0);
v_buckets_43_ = lean_ctor_get(v_m_41_, 1);
v_isSharedCheck_51_ = !lean_is_exclusive(v_m_41_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v_m_41_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_buckets_43_);
lean_inc(v_size_42_);
lean_dec(v_m_41_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
v___x_47_ = lean_array_mark_linear(v_buckets_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set(v___x_45_, 1, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v_size_42_);
lean_ctor_set(v_reuseFailAlloc_50_, 1, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_markLinear(lean_object* v_00_u03b1_52_, lean_object* v_00_u03b2_53_, lean_object* v_m_54_){
_start:
{
lean_object* v_size_55_; lean_object* v_buckets_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_64_; 
v_size_55_ = lean_ctor_get(v_m_54_, 0);
v_buckets_56_ = lean_ctor_get(v_m_54_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_m_54_);
if (v_isSharedCheck_64_ == 0)
{
v___x_58_ = v_m_54_;
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_buckets_56_);
lean_inc(v_size_55_);
lean_dec(v_m_54_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = lean_array_mark_linear(v_buckets_56_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_60_);
v___x_62_ = v___x_58_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_size_55_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
static lean_object* _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5));
v___x_106_ = l_String_toRawSubstring_x27(v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(lean_object* v_x_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v___x_131_; uint8_t v___x_132_; 
v___x_131_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_128_);
v___x_132_ = l_Lean_Syntax_isOfKind(v_x_128_, v___x_131_);
if (v___x_132_ == 0)
{
lean_object* v___x_133_; lean_object* v___x_134_; 
lean_dec(v_x_128_);
v___x_133_ = lean_box(1);
v___x_134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v_a_130_);
return v___x_134_;
}
else
{
lean_object* v_quotContext_135_; lean_object* v_currMacroScope_136_; lean_object* v_ref_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v_quotContext_135_ = lean_ctor_get(v_a_129_, 1);
v_currMacroScope_136_ = lean_ctor_get(v_a_129_, 2);
v_ref_137_ = lean_ctor_get(v_a_129_, 5);
v___x_138_ = lean_unsigned_to_nat(0u);
v___x_139_ = l_Lean_Syntax_getArg(v_x_128_, v___x_138_);
v___x_140_ = lean_unsigned_to_nat(2u);
v___x_141_ = l_Lean_Syntax_getArg(v_x_128_, v___x_140_);
lean_dec(v_x_128_);
v___x_142_ = 0;
v___x_143_ = l_Lean_SourceInfo_fromRef(v_ref_137_, v___x_142_);
v___x_144_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
v___x_145_ = lean_obj_once(&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6, &l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6);
v___x_146_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_136_);
lean_inc(v_quotContext_135_);
v___x_147_ = l_Lean_addMacroScope(v_quotContext_135_, v___x_146_, v_currMacroScope_136_);
v___x_148_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12));
lean_inc_n(v___x_143_, 2);
v___x_149_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_149_, 0, v___x_143_);
lean_ctor_set(v___x_149_, 1, v___x_145_);
lean_ctor_set(v___x_149_, 2, v___x_147_);
lean_ctor_set(v___x_149_, 3, v___x_148_);
v___x_150_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14));
v___x_151_ = l_Lean_Syntax_node2(v___x_143_, v___x_150_, v___x_139_, v___x_141_);
v___x_152_ = l_Lean_Syntax_node2(v___x_143_, v___x_144_, v___x_149_, v___x_151_);
v___x_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v_a_130_);
return v___x_153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___boxed(lean_object* v_x_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(v_x_154_, v_a_155_, v_a_156_);
lean_dec_ref(v_a_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(lean_object* v_x_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
lean_inc(v_x_161_);
v___x_165_ = l_Lean_Syntax_isOfKind(v_x_161_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_x_161_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_163_);
return v___x_167_;
}
else
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
v___x_168_ = lean_unsigned_to_nat(0u);
v___x_169_ = l_Lean_Syntax_getArg(v_x_161_, v___x_168_);
v___x_170_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_169_);
v___x_171_ = l_Lean_Syntax_isOfKind(v___x_169_, v___x_170_);
if (v___x_171_ == 0)
{
lean_object* v___x_172_; lean_object* v___x_173_; 
lean_dec(v___x_169_);
lean_dec(v_x_161_);
v___x_172_ = lean_box(0);
v___x_173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_a_163_);
return v___x_173_;
}
else
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_174_ = lean_unsigned_to_nat(1u);
v___x_175_ = l_Lean_Syntax_getArg(v_x_161_, v___x_174_);
lean_dec(v_x_161_);
v___x_176_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_175_);
v___x_177_ = l_Lean_Syntax_matchesNull(v___x_175_, v___x_176_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v___x_175_);
lean_dec(v___x_169_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v_a_163_);
return v___x_179_;
}
else
{
lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_ref_182_; uint8_t v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v___x_180_ = l_Lean_Syntax_getArg(v___x_175_, v___x_168_);
v___x_181_ = l_Lean_Syntax_getArg(v___x_175_, v___x_174_);
lean_dec(v___x_175_);
v_ref_182_ = l_Lean_replaceRef(v___x_169_, v_a_162_);
lean_dec(v___x_169_);
v___x_183_ = 0;
v___x_184_ = l_Lean_SourceInfo_fromRef(v_ref_182_, v___x_183_);
lean_dec(v_ref_182_);
v___x_185_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
v___x_186_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_184_);
v___x_187_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_184_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = l_Lean_Syntax_node3(v___x_184_, v___x_185_, v___x_180_, v___x_187_, v___x_181_);
v___x_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_163_);
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___boxed(lean_object* v_x_190_, lean_object* v_a_191_, lean_object* v_a_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(v_x_190_, v_a_191_, v_a_192_);
lean_dec(v_a_191_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert___redArg(lean_object* v_beq_194_, lean_object* v_inst_195_, lean_object* v_m_196_, lean_object* v_a_197_, lean_object* v_b_198_){
_start:
{
lean_object* v_buckets_199_; lean_object* v___x_200_; lean_object* v___x_201_; uint8_t v___x_202_; 
v_buckets_199_ = lean_ctor_get(v_m_196_, 1);
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_array_get_size(v_buckets_199_);
v___x_202_ = lean_nat_dec_lt(v___x_200_, v___x_201_);
if (v___x_202_ == 0)
{
lean_dec(v_b_198_);
lean_dec(v_a_197_);
lean_dec_ref(v_inst_195_);
lean_dec_ref(v_beq_194_);
return v_m_196_;
}
else
{
lean_object* v___x_203_; 
v___x_203_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_beq_194_, v_inst_195_, v_m_196_, v_a_197_, v_b_198_);
return v___x_203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert(lean_object* v_00_u03b1_204_, lean_object* v_00_u03b2_205_, lean_object* v_beq_206_, lean_object* v_inst_207_, lean_object* v_m_208_, lean_object* v_a_209_, lean_object* v_b_210_){
_start:
{
lean_object* v_buckets_211_; lean_object* v___x_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_buckets_211_ = lean_ctor_get(v_m_208_, 1);
v___x_212_ = lean_unsigned_to_nat(0u);
v___x_213_ = lean_array_get_size(v_buckets_211_);
v___x_214_ = lean_nat_dec_lt(v___x_212_, v___x_213_);
if (v___x_214_ == 0)
{
lean_dec(v_b_210_);
lean_dec(v_a_209_);
lean_dec_ref(v_inst_207_);
lean_dec_ref(v_beq_206_);
return v_m_208_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_beq_206_, v_inst_207_, v_m_208_, v_a_209_, v_b_210_);
return v___x_215_;
}
}
}
static lean_object* _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0);
v___x_217_ = lean_array_get_size(v___x_216_);
return v___x_217_;
}
}
static uint8_t _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
v___x_218_ = lean_obj_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_nat_dec_lt(v___x_219_, v___x_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_221_, lean_object* v_inst_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_fst_224_; lean_object* v_snd_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_fst_224_ = lean_ctor_get(v_x_223_, 0);
lean_inc(v_fst_224_);
v_snd_225_ = lean_ctor_get(v_x_223_, 1);
lean_inc(v_snd_225_);
lean_dec_ref(v_x_223_);
v___x_226_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_227_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_227_ == 0)
{
lean_dec(v_snd_225_);
lean_dec(v_fst_224_);
lean_dec_ref(v_inst_222_);
lean_dec_ref(v_inst_221_);
return v___x_226_;
}
else
{
lean_object* v___x_228_; 
v___x_228_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_221_, v_inst_222_, v___x_226_, v_fst_224_, v_snd_225_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg(lean_object* v_inst_229_, lean_object* v_inst_230_){
_start:
{
lean_object* v___f_231_; 
v___f_231_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_231_, 0, v_inst_229_);
lean_closure_set(v___f_231_, 1, v_inst_230_);
return v___f_231_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable(lean_object* v_00_u03b1_232_, lean_object* v_00_u03b2_233_, lean_object* v_inst_234_, lean_object* v_inst_235_){
_start:
{
lean_object* v___f_236_; 
v___f_236_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_236_, 0, v_inst_234_);
lean_closure_set(v___f_236_, 1, v_inst_235_);
return v___f_236_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_237_, lean_object* v_inst_238_, lean_object* v_x_239_, lean_object* v_s_240_){
_start:
{
lean_object* v_fst_241_; lean_object* v_snd_242_; lean_object* v_buckets_243_; lean_object* v___x_244_; lean_object* v___x_245_; uint8_t v___x_246_; 
v_fst_241_ = lean_ctor_get(v_x_239_, 0);
lean_inc(v_fst_241_);
v_snd_242_ = lean_ctor_get(v_x_239_, 1);
lean_inc(v_snd_242_);
lean_dec_ref(v_x_239_);
v_buckets_243_ = lean_ctor_get(v_s_240_, 1);
v___x_244_ = lean_unsigned_to_nat(0u);
v___x_245_ = lean_array_get_size(v_buckets_243_);
v___x_246_ = lean_nat_dec_lt(v___x_244_, v___x_245_);
if (v___x_246_ == 0)
{
lean_dec(v_snd_242_);
lean_dec(v_fst_241_);
lean_dec_ref(v_inst_238_);
lean_dec_ref(v_inst_237_);
return v_s_240_;
}
else
{
lean_object* v___x_247_; 
v___x_247_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_237_, v_inst_238_, v_s_240_, v_fst_241_, v_snd_242_);
return v___x_247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg(lean_object* v_inst_248_, lean_object* v_inst_249_){
_start:
{
lean_object* v___f_250_; 
v___f_250_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_250_, 0, v_inst_248_);
lean_closure_set(v___f_250_, 1, v_inst_249_);
return v___f_250_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable(lean_object* v_00_u03b1_251_, lean_object* v_00_u03b2_252_, lean_object* v_inst_253_, lean_object* v_inst_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_255_, 0, v_inst_253_);
lean_closure_set(v___f_255_, 1, v_inst_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew___redArg(lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_m_258_, lean_object* v_a_259_, lean_object* v_b_260_){
_start:
{
lean_object* v_buckets_261_; lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_buckets_261_ = lean_ctor_get(v_m_258_, 1);
v___x_262_ = lean_unsigned_to_nat(0u);
v___x_263_ = lean_array_get_size(v_buckets_261_);
v___x_264_ = lean_nat_dec_lt(v___x_262_, v___x_263_);
if (v___x_264_ == 0)
{
lean_dec(v_b_260_);
lean_dec(v_a_259_);
lean_dec_ref(v_inst_257_);
lean_dec_ref(v_inst_256_);
return v_m_258_;
}
else
{
lean_object* v___x_265_; 
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_256_, v_inst_257_, v_m_258_, v_a_259_, v_b_260_);
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_inst_268_, lean_object* v_inst_269_, lean_object* v_m_270_, lean_object* v_a_271_, lean_object* v_b_272_){
_start:
{
lean_object* v_buckets_273_; lean_object* v___x_274_; lean_object* v___x_275_; uint8_t v___x_276_; 
v_buckets_273_ = lean_ctor_get(v_m_270_, 1);
v___x_274_ = lean_unsigned_to_nat(0u);
v___x_275_ = lean_array_get_size(v_buckets_273_);
v___x_276_ = lean_nat_dec_lt(v___x_274_, v___x_275_);
if (v___x_276_ == 0)
{
lean_dec(v_b_272_);
lean_dec(v_a_271_);
lean_dec_ref(v_inst_269_);
lean_dec_ref(v_inst_268_);
return v_m_270_;
}
else
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_268_, v_inst_269_, v_m_270_, v_a_271_, v_b_272_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_278_, lean_object* v_inst_279_, lean_object* v_m_280_, lean_object* v_a_281_, lean_object* v_b_282_){
_start:
{
lean_object* v_size_283_; lean_object* v_buckets_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_size_283_ = lean_ctor_get(v_m_280_, 0);
v_buckets_284_ = lean_ctor_get(v_m_280_, 1);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = lean_array_get_size(v_buckets_284_);
v___x_287_ = lean_nat_dec_lt(v___x_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; lean_object* v___x_289_; 
lean_dec(v_b_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_inst_279_);
lean_dec_ref(v_inst_278_);
v___x_288_ = lean_box(v___x_287_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v_m_280_);
return v___x_289_;
}
else
{
lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_339_; 
lean_inc_ref(v_buckets_284_);
lean_inc(v_size_283_);
v_isSharedCheck_339_ = !lean_is_exclusive(v_m_280_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; lean_object* v_unused_341_; 
v_unused_340_ = lean_ctor_get(v_m_280_, 1);
lean_dec(v_unused_340_);
v_unused_341_ = lean_ctor_get(v_m_280_, 0);
lean_dec(v_unused_341_);
v___x_291_ = v_m_280_;
v_isShared_292_ = v_isSharedCheck_339_;
goto v_resetjp_290_;
}
else
{
lean_dec(v_m_280_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_339_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_293_; uint64_t v___x_294_; uint64_t v___x_295_; uint64_t v___x_296_; uint64_t v___x_297_; uint64_t v_fold_298_; uint64_t v___x_299_; uint64_t v___x_300_; uint64_t v___x_301_; size_t v___x_302_; size_t v___x_303_; size_t v___x_304_; size_t v___x_305_; size_t v___x_306_; lean_object* v_bkt_307_; uint8_t v___x_308_; 
lean_inc_ref(v_inst_279_);
lean_inc_n(v_a_281_, 2);
v___x_293_ = lean_apply_1(v_inst_279_, v_a_281_);
v___x_294_ = 32ULL;
v___x_295_ = lean_unbox_uint64(v___x_293_);
v___x_296_ = lean_uint64_shift_right(v___x_295_, v___x_294_);
v___x_297_ = lean_unbox_uint64(v___x_293_);
lean_dec_ref(v___x_293_);
v_fold_298_ = lean_uint64_xor(v___x_297_, v___x_296_);
v___x_299_ = 16ULL;
v___x_300_ = lean_uint64_shift_right(v_fold_298_, v___x_299_);
v___x_301_ = lean_uint64_xor(v_fold_298_, v___x_300_);
v___x_302_ = lean_uint64_to_usize(v___x_301_);
v___x_303_ = lean_usize_of_nat(v___x_286_);
v___x_304_ = ((size_t)1ULL);
v___x_305_ = lean_usize_sub(v___x_303_, v___x_304_);
v___x_306_ = lean_usize_land(v___x_302_, v___x_305_);
v_bkt_307_ = lean_array_uget_borrowed(v_buckets_284_, v___x_306_);
lean_inc(v_bkt_307_);
lean_inc_ref(v_inst_278_);
v___x_308_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_278_, v_a_281_, v_bkt_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; lean_object* v_size_x27_310_; lean_object* v___x_311_; lean_object* v_buckets_x27_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
lean_dec_ref(v_inst_278_);
v___x_309_ = lean_unsigned_to_nat(1u);
v_size_x27_310_ = lean_nat_add(v_size_283_, v___x_309_);
lean_dec(v_size_283_);
lean_inc(v_bkt_307_);
v___x_311_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_311_, 0, v_a_281_);
lean_ctor_set(v___x_311_, 1, v_b_282_);
lean_ctor_set(v___x_311_, 2, v_bkt_307_);
v_buckets_x27_312_ = lean_array_uset(v_buckets_284_, v___x_306_, v___x_311_);
v___x_313_ = lean_unsigned_to_nat(4u);
v___x_314_ = lean_nat_mul(v_size_x27_310_, v___x_313_);
v___x_315_ = lean_unsigned_to_nat(3u);
v___x_316_ = lean_nat_div(v___x_314_, v___x_315_);
lean_dec(v___x_314_);
v___x_317_ = lean_array_get_size(v_buckets_x27_312_);
v___x_318_ = lean_nat_dec_le(v___x_316_, v___x_317_);
lean_dec(v___x_316_);
if (v___x_318_ == 0)
{
lean_object* v_val_319_; lean_object* v___x_321_; 
v_val_319_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_279_, v_buckets_x27_312_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v_val_319_);
lean_ctor_set(v___x_291_, 0, v_size_x27_310_);
v___x_321_ = v___x_291_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_324_; 
v_reuseFailAlloc_324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_324_, 0, v_size_x27_310_);
lean_ctor_set(v_reuseFailAlloc_324_, 1, v_val_319_);
v___x_321_ = v_reuseFailAlloc_324_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_box(v___x_308_);
v___x_323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v___x_321_);
return v___x_323_;
}
}
else
{
lean_object* v___x_326_; 
lean_dec_ref(v_inst_279_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v_buckets_x27_312_);
lean_ctor_set(v___x_291_, 0, v_size_x27_310_);
v___x_326_ = v___x_291_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_size_x27_310_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_buckets_x27_312_);
v___x_326_ = v_reuseFailAlloc_329_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_box(v___x_308_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
return v___x_328_;
}
}
}
else
{
lean_object* v___x_330_; lean_object* v_buckets_x27_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
lean_inc(v_bkt_307_);
lean_dec_ref(v_inst_279_);
v___x_330_ = lean_box(0);
v_buckets_x27_331_ = lean_array_uset(v_buckets_284_, v___x_306_, v___x_330_);
v___x_332_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_278_, v_a_281_, v_b_282_, v_bkt_307_);
v___x_333_ = lean_array_uset(v_buckets_x27_331_, v___x_306_, v___x_332_);
if (v_isShared_292_ == 0)
{
lean_ctor_set(v___x_291_, 1, v___x_333_);
v___x_335_ = v___x_291_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v_size_283_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_333_);
v___x_335_ = v_reuseFailAlloc_338_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = lean_box(v___x_308_);
v___x_337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_336_);
lean_ctor_set(v___x_337_, 1, v___x_335_);
return v___x_337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_m_346_, lean_object* v_a_347_, lean_object* v_b_348_){
_start:
{
lean_object* v_size_349_; lean_object* v_buckets_350_; lean_object* v___x_351_; lean_object* v___x_352_; uint8_t v___x_353_; 
v_size_349_ = lean_ctor_get(v_m_346_, 0);
v_buckets_350_ = lean_ctor_get(v_m_346_, 1);
v___x_351_ = lean_unsigned_to_nat(0u);
v___x_352_ = lean_array_get_size(v_buckets_350_);
v___x_353_ = lean_nat_dec_lt(v___x_351_, v___x_352_);
if (v___x_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; 
lean_dec(v_b_348_);
lean_dec(v_a_347_);
lean_dec_ref(v_inst_345_);
lean_dec_ref(v_inst_344_);
v___x_354_ = lean_box(v___x_353_);
v___x_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_354_);
lean_ctor_set(v___x_355_, 1, v_m_346_);
return v___x_355_;
}
else
{
lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_405_; 
lean_inc_ref(v_buckets_350_);
lean_inc(v_size_349_);
v_isSharedCheck_405_ = !lean_is_exclusive(v_m_346_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; lean_object* v_unused_407_; 
v_unused_406_ = lean_ctor_get(v_m_346_, 1);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_m_346_, 0);
lean_dec(v_unused_407_);
v___x_357_ = v_m_346_;
v_isShared_358_ = v_isSharedCheck_405_;
goto v_resetjp_356_;
}
else
{
lean_dec(v_m_346_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_405_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; uint64_t v___x_360_; uint64_t v___x_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v_fold_364_; uint64_t v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; size_t v___x_372_; lean_object* v_bkt_373_; uint8_t v___x_374_; 
lean_inc_ref(v_inst_345_);
lean_inc_n(v_a_347_, 2);
v___x_359_ = lean_apply_1(v_inst_345_, v_a_347_);
v___x_360_ = 32ULL;
v___x_361_ = lean_unbox_uint64(v___x_359_);
v___x_362_ = lean_uint64_shift_right(v___x_361_, v___x_360_);
v___x_363_ = lean_unbox_uint64(v___x_359_);
lean_dec_ref(v___x_359_);
v_fold_364_ = lean_uint64_xor(v___x_363_, v___x_362_);
v___x_365_ = 16ULL;
v___x_366_ = lean_uint64_shift_right(v_fold_364_, v___x_365_);
v___x_367_ = lean_uint64_xor(v_fold_364_, v___x_366_);
v___x_368_ = lean_uint64_to_usize(v___x_367_);
v___x_369_ = lean_usize_of_nat(v___x_352_);
v___x_370_ = ((size_t)1ULL);
v___x_371_ = lean_usize_sub(v___x_369_, v___x_370_);
v___x_372_ = lean_usize_land(v___x_368_, v___x_371_);
v_bkt_373_ = lean_array_uget_borrowed(v_buckets_350_, v___x_372_);
lean_inc(v_bkt_373_);
lean_inc_ref(v_inst_344_);
v___x_374_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_344_, v_a_347_, v_bkt_373_);
if (v___x_374_ == 0)
{
lean_object* v___x_375_; lean_object* v_size_x27_376_; lean_object* v___x_377_; lean_object* v_buckets_x27_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
lean_dec_ref(v_inst_344_);
v___x_375_ = lean_unsigned_to_nat(1u);
v_size_x27_376_ = lean_nat_add(v_size_349_, v___x_375_);
lean_dec(v_size_349_);
lean_inc(v_bkt_373_);
v___x_377_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_377_, 0, v_a_347_);
lean_ctor_set(v___x_377_, 1, v_b_348_);
lean_ctor_set(v___x_377_, 2, v_bkt_373_);
v_buckets_x27_378_ = lean_array_uset(v_buckets_350_, v___x_372_, v___x_377_);
v___x_379_ = lean_unsigned_to_nat(4u);
v___x_380_ = lean_nat_mul(v_size_x27_376_, v___x_379_);
v___x_381_ = lean_unsigned_to_nat(3u);
v___x_382_ = lean_nat_div(v___x_380_, v___x_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_array_get_size(v_buckets_x27_378_);
v___x_384_ = lean_nat_dec_le(v___x_382_, v___x_383_);
lean_dec(v___x_382_);
if (v___x_384_ == 0)
{
lean_object* v_val_385_; lean_object* v___x_387_; 
v_val_385_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_345_, v_buckets_x27_378_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v_val_385_);
lean_ctor_set(v___x_357_, 0, v_size_x27_376_);
v___x_387_ = v___x_357_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_size_x27_376_);
lean_ctor_set(v_reuseFailAlloc_390_, 1, v_val_385_);
v___x_387_ = v_reuseFailAlloc_390_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_388_ = lean_box(v___x_374_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_388_);
lean_ctor_set(v___x_389_, 1, v___x_387_);
return v___x_389_;
}
}
else
{
lean_object* v___x_392_; 
lean_dec_ref(v_inst_345_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v_buckets_x27_378_);
lean_ctor_set(v___x_357_, 0, v_size_x27_376_);
v___x_392_ = v___x_357_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_size_x27_376_);
lean_ctor_set(v_reuseFailAlloc_395_, 1, v_buckets_x27_378_);
v___x_392_ = v_reuseFailAlloc_395_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_393_ = lean_box(v___x_374_);
v___x_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set(v___x_394_, 1, v___x_392_);
return v___x_394_;
}
}
}
else
{
lean_object* v___x_396_; lean_object* v_buckets_x27_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_401_; 
lean_inc(v_bkt_373_);
lean_dec_ref(v_inst_345_);
v___x_396_ = lean_box(0);
v_buckets_x27_397_ = lean_array_uset(v_buckets_350_, v___x_372_, v___x_396_);
v___x_398_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_inst_344_, v_a_347_, v_b_348_, v_bkt_373_);
v___x_399_ = lean_array_uset(v_buckets_x27_397_, v___x_372_, v___x_398_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 1, v___x_399_);
v___x_401_ = v___x_357_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_size_349_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_399_);
v___x_401_ = v_reuseFailAlloc_404_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_box(v___x_374_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
return v___x_403_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_408_, lean_object* v_inst_409_, lean_object* v_m_410_, lean_object* v_a_411_, lean_object* v_b_412_){
_start:
{
lean_object* v_size_413_; lean_object* v_buckets_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v_size_413_ = lean_ctor_get(v_m_410_, 0);
v_buckets_414_ = lean_ctor_get(v_m_410_, 1);
v___x_415_ = lean_unsigned_to_nat(0u);
v___x_416_ = lean_array_get_size(v_buckets_414_);
v___x_417_ = lean_nat_dec_lt(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_b_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_inst_409_);
lean_dec_ref(v_inst_408_);
v___x_418_ = lean_box(v___x_417_);
v___x_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v_m_410_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; uint64_t v___x_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint64_t v___x_424_; uint64_t v_fold_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; lean_object* v_bkt_434_; uint8_t v___x_435_; 
lean_inc_ref(v_inst_409_);
lean_inc_n(v_a_411_, 2);
v___x_420_ = lean_apply_1(v_inst_409_, v_a_411_);
v___x_421_ = 32ULL;
v___x_422_ = lean_unbox_uint64(v___x_420_);
v___x_423_ = lean_uint64_shift_right(v___x_422_, v___x_421_);
v___x_424_ = lean_unbox_uint64(v___x_420_);
lean_dec_ref(v___x_420_);
v_fold_425_ = lean_uint64_xor(v___x_424_, v___x_423_);
v___x_426_ = 16ULL;
v___x_427_ = lean_uint64_shift_right(v_fold_425_, v___x_426_);
v___x_428_ = lean_uint64_xor(v_fold_425_, v___x_427_);
v___x_429_ = lean_uint64_to_usize(v___x_428_);
v___x_430_ = lean_usize_of_nat(v___x_416_);
v___x_431_ = ((size_t)1ULL);
v___x_432_ = lean_usize_sub(v___x_430_, v___x_431_);
v___x_433_ = lean_usize_land(v___x_429_, v___x_432_);
v_bkt_434_ = lean_array_uget_borrowed(v_buckets_414_, v___x_433_);
lean_inc(v_bkt_434_);
v___x_435_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_408_, v_a_411_, v_bkt_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_460_; 
lean_inc_ref(v_buckets_414_);
lean_inc(v_size_413_);
v_isSharedCheck_460_ = !lean_is_exclusive(v_m_410_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; lean_object* v_unused_462_; 
v_unused_461_ = lean_ctor_get(v_m_410_, 1);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_m_410_, 0);
lean_dec(v_unused_462_);
v___x_437_ = v_m_410_;
v_isShared_438_ = v_isSharedCheck_460_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_m_410_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_460_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v_size_x27_440_; lean_object* v___x_441_; lean_object* v_buckets_x27_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_439_ = lean_unsigned_to_nat(1u);
v_size_x27_440_ = lean_nat_add(v_size_413_, v___x_439_);
lean_dec(v_size_413_);
lean_inc(v_bkt_434_);
v___x_441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_441_, 0, v_a_411_);
lean_ctor_set(v___x_441_, 1, v_b_412_);
lean_ctor_set(v___x_441_, 2, v_bkt_434_);
v_buckets_x27_442_ = lean_array_uset(v_buckets_414_, v___x_433_, v___x_441_);
v___x_443_ = lean_unsigned_to_nat(4u);
v___x_444_ = lean_nat_mul(v_size_x27_440_, v___x_443_);
v___x_445_ = lean_unsigned_to_nat(3u);
v___x_446_ = lean_nat_div(v___x_444_, v___x_445_);
lean_dec(v___x_444_);
v___x_447_ = lean_array_get_size(v_buckets_x27_442_);
v___x_448_ = lean_nat_dec_le(v___x_446_, v___x_447_);
lean_dec(v___x_446_);
if (v___x_448_ == 0)
{
lean_object* v_val_449_; lean_object* v___x_451_; 
v_val_449_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_409_, v_buckets_x27_442_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v_val_449_);
lean_ctor_set(v___x_437_, 0, v_size_x27_440_);
v___x_451_ = v___x_437_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_size_x27_440_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_val_449_);
v___x_451_ = v_reuseFailAlloc_454_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_452_ = lean_box(v___x_435_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
return v___x_453_;
}
}
else
{
lean_object* v___x_456_; 
lean_dec_ref(v_inst_409_);
if (v_isShared_438_ == 0)
{
lean_ctor_set(v___x_437_, 1, v_buckets_x27_442_);
lean_ctor_set(v___x_437_, 0, v_size_x27_440_);
v___x_456_ = v___x_437_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_size_x27_440_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_buckets_x27_442_);
v___x_456_ = v_reuseFailAlloc_459_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_box(v___x_435_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v___x_457_);
lean_ctor_set(v___x_458_, 1, v___x_456_);
return v___x_458_;
}
}
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; 
lean_dec(v_b_412_);
lean_dec(v_a_411_);
lean_dec_ref(v_inst_409_);
v___x_463_ = lean_box(v___x_435_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v_m_410_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_465_, lean_object* v_00_u03b2_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_m_469_, lean_object* v_a_470_, lean_object* v_b_471_){
_start:
{
lean_object* v_size_472_; lean_object* v_buckets_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_size_472_ = lean_ctor_get(v_m_469_, 0);
v_buckets_473_ = lean_ctor_get(v_m_469_, 1);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_array_get_size(v_buckets_473_);
v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; lean_object* v___x_478_; 
lean_dec(v_b_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_inst_468_);
lean_dec_ref(v_inst_467_);
v___x_477_ = lean_box(v___x_476_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v_m_469_);
return v___x_478_;
}
else
{
lean_object* v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v___x_482_; uint64_t v___x_483_; uint64_t v_fold_484_; uint64_t v___x_485_; uint64_t v___x_486_; uint64_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; lean_object* v_bkt_493_; uint8_t v___x_494_; 
lean_inc_ref(v_inst_468_);
lean_inc_n(v_a_470_, 2);
v___x_479_ = lean_apply_1(v_inst_468_, v_a_470_);
v___x_480_ = 32ULL;
v___x_481_ = lean_unbox_uint64(v___x_479_);
v___x_482_ = lean_uint64_shift_right(v___x_481_, v___x_480_);
v___x_483_ = lean_unbox_uint64(v___x_479_);
lean_dec_ref(v___x_479_);
v_fold_484_ = lean_uint64_xor(v___x_483_, v___x_482_);
v___x_485_ = 16ULL;
v___x_486_ = lean_uint64_shift_right(v_fold_484_, v___x_485_);
v___x_487_ = lean_uint64_xor(v_fold_484_, v___x_486_);
v___x_488_ = lean_uint64_to_usize(v___x_487_);
v___x_489_ = lean_usize_of_nat(v___x_475_);
v___x_490_ = ((size_t)1ULL);
v___x_491_ = lean_usize_sub(v___x_489_, v___x_490_);
v___x_492_ = lean_usize_land(v___x_488_, v___x_491_);
v_bkt_493_ = lean_array_uget_borrowed(v_buckets_473_, v___x_492_);
lean_inc(v_bkt_493_);
v___x_494_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_inst_467_, v_a_470_, v_bkt_493_);
if (v___x_494_ == 0)
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_519_; 
lean_inc_ref(v_buckets_473_);
lean_inc(v_size_472_);
v_isSharedCheck_519_ = !lean_is_exclusive(v_m_469_);
if (v_isSharedCheck_519_ == 0)
{
lean_object* v_unused_520_; lean_object* v_unused_521_; 
v_unused_520_ = lean_ctor_get(v_m_469_, 1);
lean_dec(v_unused_520_);
v_unused_521_ = lean_ctor_get(v_m_469_, 0);
lean_dec(v_unused_521_);
v___x_496_ = v_m_469_;
v_isShared_497_ = v_isSharedCheck_519_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_m_469_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_519_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v_size_x27_499_; lean_object* v___x_500_; lean_object* v_buckets_x27_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v___x_498_ = lean_unsigned_to_nat(1u);
v_size_x27_499_ = lean_nat_add(v_size_472_, v___x_498_);
lean_dec(v_size_472_);
lean_inc(v_bkt_493_);
v___x_500_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_500_, 0, v_a_470_);
lean_ctor_set(v___x_500_, 1, v_b_471_);
lean_ctor_set(v___x_500_, 2, v_bkt_493_);
v_buckets_x27_501_ = lean_array_uset(v_buckets_473_, v___x_492_, v___x_500_);
v___x_502_ = lean_unsigned_to_nat(4u);
v___x_503_ = lean_nat_mul(v_size_x27_499_, v___x_502_);
v___x_504_ = lean_unsigned_to_nat(3u);
v___x_505_ = lean_nat_div(v___x_503_, v___x_504_);
lean_dec(v___x_503_);
v___x_506_ = lean_array_get_size(v_buckets_x27_501_);
v___x_507_ = lean_nat_dec_le(v___x_505_, v___x_506_);
lean_dec(v___x_505_);
if (v___x_507_ == 0)
{
lean_object* v_val_508_; lean_object* v___x_510_; 
v_val_508_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_468_, v_buckets_x27_501_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v_val_508_);
lean_ctor_set(v___x_496_, 0, v_size_x27_499_);
v___x_510_ = v___x_496_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_size_x27_499_);
lean_ctor_set(v_reuseFailAlloc_513_, 1, v_val_508_);
v___x_510_ = v_reuseFailAlloc_513_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_511_; lean_object* v___x_512_; 
v___x_511_ = lean_box(v___x_494_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v___x_510_);
return v___x_512_;
}
}
else
{
lean_object* v___x_515_; 
lean_dec_ref(v_inst_468_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 1, v_buckets_x27_501_);
lean_ctor_set(v___x_496_, 0, v_size_x27_499_);
v___x_515_ = v___x_496_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_size_x27_499_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_buckets_x27_501_);
v___x_515_ = v_reuseFailAlloc_518_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_box(v___x_494_);
v___x_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v___x_515_);
return v___x_517_;
}
}
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v_b_471_);
lean_dec(v_a_470_);
lean_dec_ref(v_inst_468_);
v___x_522_ = lean_box(v___x_494_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v___x_522_);
lean_ctor_set(v___x_523_, 1, v_m_469_);
return v___x_523_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_524_, lean_object* v_inst_525_, lean_object* v_m_526_, lean_object* v_a_527_, lean_object* v_b_528_){
_start:
{
lean_object* v_size_529_; lean_object* v_buckets_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_size_529_ = lean_ctor_get(v_m_526_, 0);
v_buckets_530_ = lean_ctor_get(v_m_526_, 1);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_array_get_size(v_buckets_530_);
v___x_533_ = lean_nat_dec_lt(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_object* v___x_534_; lean_object* v___x_535_; 
lean_dec(v_b_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_inst_525_);
lean_dec_ref(v_inst_524_);
v___x_534_ = lean_box(0);
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set(v___x_535_, 1, v_m_526_);
return v___x_535_;
}
else
{
lean_object* v___x_536_; uint64_t v___x_537_; uint64_t v___x_538_; uint64_t v___x_539_; uint64_t v___x_540_; uint64_t v_fold_541_; uint64_t v___x_542_; uint64_t v___x_543_; uint64_t v___x_544_; size_t v___x_545_; size_t v___x_546_; size_t v___x_547_; size_t v___x_548_; size_t v___x_549_; lean_object* v_bkt_550_; lean_object* v___x_551_; 
lean_inc_ref(v_inst_525_);
lean_inc_n(v_a_527_, 2);
v___x_536_ = lean_apply_1(v_inst_525_, v_a_527_);
v___x_537_ = 32ULL;
v___x_538_ = lean_unbox_uint64(v___x_536_);
v___x_539_ = lean_uint64_shift_right(v___x_538_, v___x_537_);
v___x_540_ = lean_unbox_uint64(v___x_536_);
lean_dec_ref(v___x_536_);
v_fold_541_ = lean_uint64_xor(v___x_540_, v___x_539_);
v___x_542_ = 16ULL;
v___x_543_ = lean_uint64_shift_right(v_fold_541_, v___x_542_);
v___x_544_ = lean_uint64_xor(v_fold_541_, v___x_543_);
v___x_545_ = lean_uint64_to_usize(v___x_544_);
v___x_546_ = lean_usize_of_nat(v___x_532_);
v___x_547_ = ((size_t)1ULL);
v___x_548_ = lean_usize_sub(v___x_546_, v___x_547_);
v___x_549_ = lean_usize_land(v___x_545_, v___x_548_);
v_bkt_550_ = lean_array_uget_borrowed(v_buckets_530_, v___x_549_);
lean_inc(v_bkt_550_);
v___x_551_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_524_, v_a_527_, v_bkt_550_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_574_; 
lean_inc_ref(v_buckets_530_);
lean_inc(v_size_529_);
v_isSharedCheck_574_ = !lean_is_exclusive(v_m_526_);
if (v_isSharedCheck_574_ == 0)
{
lean_object* v_unused_575_; lean_object* v_unused_576_; 
v_unused_575_ = lean_ctor_get(v_m_526_, 1);
lean_dec(v_unused_575_);
v_unused_576_ = lean_ctor_get(v_m_526_, 0);
lean_dec(v_unused_576_);
v___x_553_ = v_m_526_;
v_isShared_554_ = v_isSharedCheck_574_;
goto v_resetjp_552_;
}
else
{
lean_dec(v_m_526_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_574_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_555_; lean_object* v_size_x27_556_; lean_object* v___x_557_; lean_object* v_buckets_x27_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v___x_555_ = lean_unsigned_to_nat(1u);
v_size_x27_556_ = lean_nat_add(v_size_529_, v___x_555_);
lean_dec(v_size_529_);
lean_inc(v_bkt_550_);
v___x_557_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_557_, 0, v_a_527_);
lean_ctor_set(v___x_557_, 1, v_b_528_);
lean_ctor_set(v___x_557_, 2, v_bkt_550_);
v_buckets_x27_558_ = lean_array_uset(v_buckets_530_, v___x_549_, v___x_557_);
v___x_559_ = lean_unsigned_to_nat(4u);
v___x_560_ = lean_nat_mul(v_size_x27_556_, v___x_559_);
v___x_561_ = lean_unsigned_to_nat(3u);
v___x_562_ = lean_nat_div(v___x_560_, v___x_561_);
lean_dec(v___x_560_);
v___x_563_ = lean_array_get_size(v_buckets_x27_558_);
v___x_564_ = lean_nat_dec_le(v___x_562_, v___x_563_);
lean_dec(v___x_562_);
if (v___x_564_ == 0)
{
lean_object* v_val_565_; lean_object* v___x_567_; 
v_val_565_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_525_, v_buckets_x27_558_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v_val_565_);
lean_ctor_set(v___x_553_, 0, v_size_x27_556_);
v___x_567_ = v___x_553_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_569_; 
v_reuseFailAlloc_569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_569_, 0, v_size_x27_556_);
lean_ctor_set(v_reuseFailAlloc_569_, 1, v_val_565_);
v___x_567_ = v_reuseFailAlloc_569_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_568_; 
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_551_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
return v___x_568_;
}
}
else
{
lean_object* v___x_571_; 
lean_dec_ref(v_inst_525_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 1, v_buckets_x27_558_);
lean_ctor_set(v___x_553_, 0, v_size_x27_556_);
v___x_571_ = v___x_553_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_size_x27_556_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_buckets_x27_558_);
v___x_571_ = v_reuseFailAlloc_573_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; 
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_551_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
return v___x_572_;
}
}
}
}
else
{
lean_object* v___x_577_; 
lean_dec(v_b_528_);
lean_dec(v_a_527_);
lean_dec_ref(v_inst_525_);
v___x_577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_551_);
lean_ctor_set(v___x_577_, 1, v_m_526_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_578_, lean_object* v_00_u03b2_579_, lean_object* v_inst_580_, lean_object* v_inst_581_, lean_object* v_m_582_, lean_object* v_a_583_, lean_object* v_b_584_){
_start:
{
lean_object* v_size_585_; lean_object* v_buckets_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_size_585_ = lean_ctor_get(v_m_582_, 0);
v_buckets_586_ = lean_ctor_get(v_m_582_, 1);
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_array_get_size(v_buckets_586_);
v___x_589_ = lean_nat_dec_lt(v___x_587_, v___x_588_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; lean_object* v___x_591_; 
lean_dec(v_b_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_inst_581_);
lean_dec_ref(v_inst_580_);
v___x_590_ = lean_box(0);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v___x_590_);
lean_ctor_set(v___x_591_, 1, v_m_582_);
return v___x_591_;
}
else
{
lean_object* v___x_592_; uint64_t v___x_593_; uint64_t v___x_594_; uint64_t v___x_595_; uint64_t v___x_596_; uint64_t v_fold_597_; uint64_t v___x_598_; uint64_t v___x_599_; uint64_t v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v___x_604_; size_t v___x_605_; lean_object* v_bkt_606_; lean_object* v___x_607_; 
lean_inc_ref(v_inst_581_);
lean_inc_n(v_a_583_, 2);
v___x_592_ = lean_apply_1(v_inst_581_, v_a_583_);
v___x_593_ = 32ULL;
v___x_594_ = lean_unbox_uint64(v___x_592_);
v___x_595_ = lean_uint64_shift_right(v___x_594_, v___x_593_);
v___x_596_ = lean_unbox_uint64(v___x_592_);
lean_dec_ref(v___x_592_);
v_fold_597_ = lean_uint64_xor(v___x_596_, v___x_595_);
v___x_598_ = 16ULL;
v___x_599_ = lean_uint64_shift_right(v_fold_597_, v___x_598_);
v___x_600_ = lean_uint64_xor(v_fold_597_, v___x_599_);
v___x_601_ = lean_uint64_to_usize(v___x_600_);
v___x_602_ = lean_usize_of_nat(v___x_588_);
v___x_603_ = ((size_t)1ULL);
v___x_604_ = lean_usize_sub(v___x_602_, v___x_603_);
v___x_605_ = lean_usize_land(v___x_601_, v___x_604_);
v_bkt_606_ = lean_array_uget_borrowed(v_buckets_586_, v___x_605_);
lean_inc(v_bkt_606_);
v___x_607_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_inst_580_, v_a_583_, v_bkt_606_);
if (lean_obj_tag(v___x_607_) == 0)
{
lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_630_; 
lean_inc_ref(v_buckets_586_);
lean_inc(v_size_585_);
v_isSharedCheck_630_ = !lean_is_exclusive(v_m_582_);
if (v_isSharedCheck_630_ == 0)
{
lean_object* v_unused_631_; lean_object* v_unused_632_; 
v_unused_631_ = lean_ctor_get(v_m_582_, 1);
lean_dec(v_unused_631_);
v_unused_632_ = lean_ctor_get(v_m_582_, 0);
lean_dec(v_unused_632_);
v___x_609_ = v_m_582_;
v_isShared_610_ = v_isSharedCheck_630_;
goto v_resetjp_608_;
}
else
{
lean_dec(v_m_582_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_630_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v_size_x27_612_; lean_object* v___x_613_; lean_object* v_buckets_x27_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_611_ = lean_unsigned_to_nat(1u);
v_size_x27_612_ = lean_nat_add(v_size_585_, v___x_611_);
lean_dec(v_size_585_);
lean_inc(v_bkt_606_);
v___x_613_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_613_, 0, v_a_583_);
lean_ctor_set(v___x_613_, 1, v_b_584_);
lean_ctor_set(v___x_613_, 2, v_bkt_606_);
v_buckets_x27_614_ = lean_array_uset(v_buckets_586_, v___x_605_, v___x_613_);
v___x_615_ = lean_unsigned_to_nat(4u);
v___x_616_ = lean_nat_mul(v_size_x27_612_, v___x_615_);
v___x_617_ = lean_unsigned_to_nat(3u);
v___x_618_ = lean_nat_div(v___x_616_, v___x_617_);
lean_dec(v___x_616_);
v___x_619_ = lean_array_get_size(v_buckets_x27_614_);
v___x_620_ = lean_nat_dec_le(v___x_618_, v___x_619_);
lean_dec(v___x_618_);
if (v___x_620_ == 0)
{
lean_object* v_val_621_; lean_object* v___x_623_; 
v_val_621_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_581_, v_buckets_x27_614_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v_val_621_);
lean_ctor_set(v___x_609_, 0, v_size_x27_612_);
v___x_623_ = v___x_609_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_625_; 
v_reuseFailAlloc_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_625_, 0, v_size_x27_612_);
lean_ctor_set(v_reuseFailAlloc_625_, 1, v_val_621_);
v___x_623_ = v_reuseFailAlloc_625_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_624_, 0, v___x_607_);
lean_ctor_set(v___x_624_, 1, v___x_623_);
return v___x_624_;
}
}
else
{
lean_object* v___x_627_; 
lean_dec_ref(v_inst_581_);
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 1, v_buckets_x27_614_);
lean_ctor_set(v___x_609_, 0, v_size_x27_612_);
v___x_627_ = v___x_609_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v_size_x27_612_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_buckets_x27_614_);
v___x_627_ = v_reuseFailAlloc_629_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; 
v___x_628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_628_, 0, v___x_607_);
lean_ctor_set(v___x_628_, 1, v___x_627_);
return v___x_628_;
}
}
}
}
else
{
lean_object* v___x_633_; 
lean_dec(v_b_584_);
lean_dec(v_a_583_);
lean_dec_ref(v_inst_581_);
v___x_633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_607_);
lean_ctor_set(v___x_633_, 1, v_m_582_);
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg(lean_object* v_beq_634_, lean_object* v_inst_635_, lean_object* v_m_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_buckets_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_buckets_638_ = lean_ctor_get(v_m_636_, 1);
v___x_639_ = lean_unsigned_to_nat(0u);
v___x_640_ = lean_array_get_size(v_buckets_638_);
v___x_641_ = lean_nat_dec_lt(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; 
lean_dec(v_a_637_);
lean_dec_ref(v_inst_635_);
lean_dec_ref(v_beq_634_);
v___x_642_ = lean_box(0);
return v___x_642_;
}
else
{
lean_object* v___x_643_; 
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_634_, v_inst_635_, v_m_636_, v_a_637_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg___boxed(lean_object* v_beq_644_, lean_object* v_inst_645_, lean_object* v_m_646_, lean_object* v_a_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_HashMap_Raw_get_x3f___redArg(v_beq_644_, v_inst_645_, v_m_646_, v_a_647_);
lean_dec_ref(v_m_646_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_beq_651_, lean_object* v_inst_652_, lean_object* v_m_653_, lean_object* v_a_654_){
_start:
{
lean_object* v_buckets_655_; lean_object* v___x_656_; lean_object* v___x_657_; uint8_t v___x_658_; 
v_buckets_655_ = lean_ctor_get(v_m_653_, 1);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_array_get_size(v_buckets_655_);
v___x_658_ = lean_nat_dec_lt(v___x_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec(v_a_654_);
lean_dec_ref(v_inst_652_);
lean_dec_ref(v_beq_651_);
v___x_659_ = lean_box(0);
return v___x_659_;
}
else
{
lean_object* v___x_660_; 
v___x_660_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_651_, v_inst_652_, v_m_653_, v_a_654_);
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_661_, lean_object* v_00_u03b2_662_, lean_object* v_beq_663_, lean_object* v_inst_664_, lean_object* v_m_665_, lean_object* v_a_666_){
_start:
{
lean_object* v_res_667_; 
v_res_667_ = l_Std_HashMap_Raw_get_x3f(v_00_u03b1_661_, v_00_u03b2_662_, v_beq_663_, v_inst_664_, v_m_665_, v_a_666_);
lean_dec_ref(v_m_665_);
return v_res_667_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains___redArg(lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_m_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_buckets_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v_buckets_672_ = lean_ctor_get(v_m_670_, 1);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = lean_array_get_size(v_buckets_672_);
v___x_675_ = lean_nat_dec_lt(v___x_673_, v___x_674_);
if (v___x_675_ == 0)
{
lean_dec(v_a_671_);
lean_dec_ref(v_inst_669_);
lean_dec_ref(v_inst_668_);
return v___x_675_;
}
else
{
uint8_t v___x_676_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_668_, v_inst_669_, v_m_670_, v_a_671_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___redArg___boxed(lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_m_679_, lean_object* v_a_680_){
_start:
{
uint8_t v_res_681_; lean_object* v_r_682_; 
v_res_681_ = l_Std_HashMap_Raw_contains___redArg(v_inst_677_, v_inst_678_, v_m_679_, v_a_680_);
lean_dec_ref(v_m_679_);
v_r_682_ = lean_box(v_res_681_);
return v_r_682_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains(lean_object* v_00_u03b1_683_, lean_object* v_00_u03b2_684_, lean_object* v_inst_685_, lean_object* v_inst_686_, lean_object* v_m_687_, lean_object* v_a_688_){
_start:
{
lean_object* v_buckets_689_; lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_buckets_689_ = lean_ctor_get(v_m_687_, 1);
v___x_690_ = lean_unsigned_to_nat(0u);
v___x_691_ = lean_array_get_size(v_buckets_689_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_dec(v_a_688_);
lean_dec_ref(v_inst_686_);
lean_dec_ref(v_inst_685_);
return v___x_692_;
}
else
{
uint8_t v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_685_, v_inst_686_, v_m_687_, v_a_688_);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___boxed(lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_m_698_, lean_object* v_a_699_){
_start:
{
uint8_t v_res_700_; lean_object* v_r_701_; 
v_res_700_ = l_Std_HashMap_Raw_contains(v_00_u03b1_694_, v_00_u03b2_695_, v_inst_696_, v_inst_697_, v_m_698_, v_a_699_);
lean_dec_ref(v_m_698_);
v_r_701_ = lean_box(v_res_700_);
return v_r_701_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_702_, lean_object* v_00_u03b2_703_, lean_object* v_inst_704_, lean_object* v_inst_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = lean_box(0);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_707_, lean_object* v_00_u03b2_708_, lean_object* v_inst_709_, lean_object* v_inst_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_707_, v_00_u03b2_708_, v_inst_709_, v_inst_710_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v_inst_709_);
return v_res_711_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_m_714_, lean_object* v_a_715_){
_start:
{
uint8_t v___x_716_; 
v___x_716_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_712_, v_inst_713_, v_m_714_, v_a_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_717_, lean_object* v_inst_718_, lean_object* v_m_719_, lean_object* v_a_720_){
_start:
{
uint8_t v_res_721_; lean_object* v_r_722_; 
v_res_721_ = l_Std_HashMap_Raw_instDecidableMem___redArg(v_inst_717_, v_inst_718_, v_m_719_, v_a_720_);
lean_dec_ref(v_m_719_);
v_r_722_ = lean_box(v_res_721_);
return v_r_722_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_inst_725_, lean_object* v_inst_726_, lean_object* v_m_727_, lean_object* v_a_728_){
_start:
{
uint8_t v___x_729_; 
v___x_729_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_725_, v_inst_726_, v_m_727_, v_a_728_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_730_, lean_object* v_00_u03b2_731_, lean_object* v_inst_732_, lean_object* v_inst_733_, lean_object* v_m_734_, lean_object* v_a_735_){
_start:
{
uint8_t v_res_736_; lean_object* v_r_737_; 
v_res_736_ = l_Std_HashMap_Raw_instDecidableMem(v_00_u03b1_730_, v_00_u03b2_731_, v_inst_732_, v_inst_733_, v_m_734_, v_a_735_);
lean_dec_ref(v_m_734_);
v_r_737_ = lean_box(v_res_736_);
return v_r_737_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg(lean_object* v_inst_738_, lean_object* v_inst_739_, lean_object* v_m_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_742_; 
v___x_742_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_738_, v_inst_739_, v_m_740_, v_a_741_);
return v___x_742_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg___boxed(lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_m_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_HashMap_Raw_get___redArg(v_inst_743_, v_inst_744_, v_m_745_, v_a_746_);
lean_dec_ref(v_m_745_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get(lean_object* v_00_u03b1_748_, lean_object* v_00_u03b2_749_, lean_object* v_inst_750_, lean_object* v_inst_751_, lean_object* v_m_752_, lean_object* v_a_753_, lean_object* v_h_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_750_, v_inst_751_, v_m_752_, v_a_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___boxed(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_m_760_, lean_object* v_a_761_, lean_object* v_h_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_HashMap_Raw_get(v_00_u03b1_756_, v_00_u03b2_757_, v_inst_758_, v_inst_759_, v_m_760_, v_a_761_, v_h_762_);
lean_dec_ref(v_m_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg(lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_m_766_, lean_object* v_a_767_, lean_object* v_fallback_768_){
_start:
{
lean_object* v_buckets_769_; lean_object* v___x_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
v_buckets_769_ = lean_ctor_get(v_m_766_, 1);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_array_get_size(v_buckets_769_);
v___x_772_ = lean_nat_dec_lt(v___x_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_dec(v_a_767_);
lean_dec_ref(v_inst_765_);
lean_dec_ref(v_inst_764_);
lean_inc(v_fallback_768_);
return v_fallback_768_;
}
else
{
lean_object* v___x_773_; 
v___x_773_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_764_, v_inst_765_, v_m_766_, v_a_767_, v_fallback_768_);
return v___x_773_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg___boxed(lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_m_776_, lean_object* v_a_777_, lean_object* v_fallback_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Std_HashMap_Raw_getD___redArg(v_inst_774_, v_inst_775_, v_m_776_, v_a_777_, v_fallback_778_);
lean_dec(v_fallback_778_);
lean_dec_ref(v_m_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD(lean_object* v_00_u03b1_780_, lean_object* v_00_u03b2_781_, lean_object* v_inst_782_, lean_object* v_inst_783_, lean_object* v_m_784_, lean_object* v_a_785_, lean_object* v_fallback_786_){
_start:
{
lean_object* v_buckets_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v_buckets_787_ = lean_ctor_get(v_m_784_, 1);
v___x_788_ = lean_unsigned_to_nat(0u);
v___x_789_ = lean_array_get_size(v_buckets_787_);
v___x_790_ = lean_nat_dec_lt(v___x_788_, v___x_789_);
if (v___x_790_ == 0)
{
lean_dec(v_a_785_);
lean_dec_ref(v_inst_783_);
lean_dec_ref(v_inst_782_);
lean_inc(v_fallback_786_);
return v_fallback_786_;
}
else
{
lean_object* v___x_791_; 
v___x_791_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_782_, v_inst_783_, v_m_784_, v_a_785_, v_fallback_786_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___boxed(lean_object* v_00_u03b1_792_, lean_object* v_00_u03b2_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_m_796_, lean_object* v_a_797_, lean_object* v_fallback_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_Std_HashMap_Raw_getD(v_00_u03b1_792_, v_00_u03b2_793_, v_inst_794_, v_inst_795_, v_m_796_, v_a_797_, v_fallback_798_);
lean_dec(v_fallback_798_);
lean_dec_ref(v_m_796_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg(lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_inst_802_, lean_object* v_m_803_, lean_object* v_a_804_){
_start:
{
lean_object* v_buckets_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_buckets_805_ = lean_ctor_get(v_m_803_, 1);
v___x_806_ = lean_unsigned_to_nat(0u);
v___x_807_ = lean_array_get_size(v_buckets_805_);
v___x_808_ = lean_nat_dec_lt(v___x_806_, v___x_807_);
if (v___x_808_ == 0)
{
lean_dec(v_a_804_);
lean_dec_ref(v_inst_801_);
lean_dec_ref(v_inst_800_);
lean_inc(v_inst_802_);
return v_inst_802_;
}
else
{
lean_object* v___x_809_; 
v___x_809_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_800_, v_inst_801_, v_inst_802_, v_m_803_, v_a_804_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_810_, lean_object* v_inst_811_, lean_object* v_inst_812_, lean_object* v_m_813_, lean_object* v_a_814_){
_start:
{
lean_object* v_res_815_; 
v_res_815_ = l_Std_HashMap_Raw_get_x21___redArg(v_inst_810_, v_inst_811_, v_inst_812_, v_m_813_, v_a_814_);
lean_dec_ref(v_m_813_);
lean_dec(v_inst_812_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21(lean_object* v_00_u03b1_816_, lean_object* v_00_u03b2_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_m_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_buckets_823_; lean_object* v___x_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_buckets_823_ = lean_ctor_get(v_m_821_, 1);
v___x_824_ = lean_unsigned_to_nat(0u);
v___x_825_ = lean_array_get_size(v_buckets_823_);
v___x_826_ = lean_nat_dec_lt(v___x_824_, v___x_825_);
if (v___x_826_ == 0)
{
lean_dec(v_a_822_);
lean_dec_ref(v_inst_819_);
lean_dec_ref(v_inst_818_);
lean_inc(v_inst_820_);
return v_inst_820_;
}
else
{
lean_object* v___x_827_; 
v___x_827_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_818_, v_inst_819_, v_inst_820_, v_m_821_, v_a_822_);
return v___x_827_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_828_, lean_object* v_00_u03b2_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_m_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Std_HashMap_Raw_get_x21(v_00_u03b1_828_, v_00_u03b2_829_, v_inst_830_, v_inst_831_, v_inst_832_, v_m_833_, v_a_834_);
lean_dec_ref(v_m_833_);
lean_dec(v_inst_832_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_m_838_, lean_object* v_a_839_, lean_object* v_h_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_836_, v_inst_837_, v_m_838_, v_a_839_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_m_844_, lean_object* v_a_845_, lean_object* v_h_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(v_inst_842_, v_inst_843_, v_m_844_, v_a_845_, v_h_846_);
lean_dec_ref(v_m_844_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_m_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_buckets_852_; lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_buckets_852_ = lean_ctor_get(v_m_850_, 1);
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = lean_array_get_size(v_buckets_852_);
v___x_855_ = lean_nat_dec_lt(v___x_853_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec(v_a_851_);
lean_dec_ref(v_inst_849_);
lean_dec_ref(v_inst_848_);
v___x_856_ = lean_box(0);
return v___x_856_;
}
else
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_848_, v_inst_849_, v_m_850_, v_a_851_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_m_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(v_inst_858_, v_inst_859_, v_m_860_, v_a_861_);
lean_dec_ref(v_m_860_);
return v_res_862_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_m_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_buckets_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_buckets_868_ = lean_ctor_get(v_m_866_, 1);
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = lean_array_get_size(v_buckets_868_);
v___x_871_ = lean_nat_dec_lt(v___x_869_, v___x_870_);
if (v___x_871_ == 0)
{
lean_dec(v_a_867_);
lean_dec_ref(v_inst_864_);
lean_dec_ref(v_inst_863_);
lean_inc(v_inst_865_);
return v_inst_865_;
}
else
{
lean_object* v___x_872_; 
v___x_872_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_863_, v_inst_864_, v_inst_865_, v_m_866_, v_a_867_);
return v___x_872_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_inst_875_, lean_object* v_m_876_, lean_object* v_a_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(v_inst_873_, v_inst_874_, v_inst_875_, v_m_876_, v_a_877_);
lean_dec_ref(v_m_876_);
lean_dec(v_inst_875_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(lean_object* v_inst_879_, lean_object* v_inst_880_){
_start:
{
lean_object* v___f_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___x_884_; 
lean_inc_ref_n(v_inst_880_, 2);
lean_inc_ref_n(v_inst_879_, 2);
v___f_881_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_881_, 0, v_inst_879_);
lean_closure_set(v___f_881_, 1, v_inst_880_);
v___f_882_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_882_, 0, v_inst_879_);
lean_closure_set(v___f_882_, 1, v_inst_880_);
v___f_883_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_883_, 0, v_inst_879_);
lean_closure_set(v___f_883_, 1, v_inst_880_);
v___x_884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_884_, 0, v___f_881_);
lean_ctor_set(v___x_884_, 1, v___f_882_);
lean_ctor_set(v___x_884_, 2, v___f_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem(lean_object* v_00_u03b1_885_, lean_object* v_00_u03b2_886_, lean_object* v_inst_887_, lean_object* v_inst_888_){
_start:
{
lean_object* v___x_889_; 
v___x_889_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(v_inst_887_, v_inst_888_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_m_892_, lean_object* v_a_893_){
_start:
{
lean_object* v_buckets_894_; lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_buckets_894_ = lean_ctor_get(v_m_892_, 1);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_array_get_size(v_buckets_894_);
v___x_897_ = lean_nat_dec_lt(v___x_895_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_dec(v_a_893_);
lean_dec_ref(v_inst_891_);
lean_dec_ref(v_inst_890_);
v___x_898_ = lean_box(0);
return v___x_898_;
}
else
{
lean_object* v___x_899_; 
v___x_899_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_890_, v_inst_891_, v_m_892_, v_a_893_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_900_, lean_object* v_inst_901_, lean_object* v_m_902_, lean_object* v_a_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_Std_HashMap_Raw_getKey_x3f___redArg(v_inst_900_, v_inst_901_, v_m_902_, v_a_903_);
lean_dec_ref(v_m_902_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_905_, lean_object* v_00_u03b2_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_m_909_, lean_object* v_a_910_){
_start:
{
lean_object* v_buckets_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_buckets_911_ = lean_ctor_get(v_m_909_, 1);
v___x_912_ = lean_unsigned_to_nat(0u);
v___x_913_ = lean_array_get_size(v_buckets_911_);
v___x_914_ = lean_nat_dec_lt(v___x_912_, v___x_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; 
lean_dec(v_a_910_);
lean_dec_ref(v_inst_908_);
lean_dec_ref(v_inst_907_);
v___x_915_ = lean_box(0);
return v___x_915_;
}
else
{
lean_object* v___x_916_; 
v___x_916_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_907_, v_inst_908_, v_m_909_, v_a_910_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_917_, lean_object* v_00_u03b2_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_m_921_, lean_object* v_a_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_HashMap_Raw_getKey_x3f(v_00_u03b1_917_, v_00_u03b2_918_, v_inst_919_, v_inst_920_, v_m_921_, v_a_922_);
lean_dec_ref(v_m_921_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg(lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_m_926_, lean_object* v_a_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_924_, v_inst_925_, v_m_926_, v_a_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_929_, lean_object* v_inst_930_, lean_object* v_m_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Std_HashMap_Raw_getKey___redArg(v_inst_929_, v_inst_930_, v_m_931_, v_a_932_);
lean_dec_ref(v_m_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey(lean_object* v_00_u03b1_934_, lean_object* v_00_u03b2_935_, lean_object* v_inst_936_, lean_object* v_inst_937_, lean_object* v_m_938_, lean_object* v_a_939_, lean_object* v_h_940_){
_start:
{
lean_object* v___x_941_; 
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_inst_936_, v_inst_937_, v_m_938_, v_a_939_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_942_, lean_object* v_00_u03b2_943_, lean_object* v_inst_944_, lean_object* v_inst_945_, lean_object* v_m_946_, lean_object* v_a_947_, lean_object* v_h_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_HashMap_Raw_getKey(v_00_u03b1_942_, v_00_u03b2_943_, v_inst_944_, v_inst_945_, v_m_946_, v_a_947_, v_h_948_);
lean_dec_ref(v_m_946_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg(lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_m_952_, lean_object* v_a_953_, lean_object* v_fallback_954_){
_start:
{
lean_object* v_buckets_955_; lean_object* v___x_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v_buckets_955_ = lean_ctor_get(v_m_952_, 1);
v___x_956_ = lean_unsigned_to_nat(0u);
v___x_957_ = lean_array_get_size(v_buckets_955_);
v___x_958_ = lean_nat_dec_lt(v___x_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec(v_a_953_);
lean_dec_ref(v_inst_951_);
lean_dec_ref(v_inst_950_);
lean_inc(v_fallback_954_);
return v_fallback_954_;
}
else
{
lean_object* v___x_959_; 
v___x_959_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_950_, v_inst_951_, v_m_952_, v_a_953_, v_fallback_954_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_m_962_, lean_object* v_a_963_, lean_object* v_fallback_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_HashMap_Raw_getKeyD___redArg(v_inst_960_, v_inst_961_, v_m_962_, v_a_963_, v_fallback_964_);
lean_dec(v_fallback_964_);
lean_dec_ref(v_m_962_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD(lean_object* v_00_u03b1_966_, lean_object* v_00_u03b2_967_, lean_object* v_inst_968_, lean_object* v_inst_969_, lean_object* v_m_970_, lean_object* v_a_971_, lean_object* v_fallback_972_){
_start:
{
lean_object* v_buckets_973_; lean_object* v___x_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v_buckets_973_ = lean_ctor_get(v_m_970_, 1);
v___x_974_ = lean_unsigned_to_nat(0u);
v___x_975_ = lean_array_get_size(v_buckets_973_);
v___x_976_ = lean_nat_dec_lt(v___x_974_, v___x_975_);
if (v___x_976_ == 0)
{
lean_dec(v_a_971_);
lean_dec_ref(v_inst_969_);
lean_dec_ref(v_inst_968_);
lean_inc(v_fallback_972_);
return v_fallback_972_;
}
else
{
lean_object* v___x_977_; 
v___x_977_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_968_, v_inst_969_, v_m_970_, v_a_971_, v_fallback_972_);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_978_, lean_object* v_00_u03b2_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_m_982_, lean_object* v_a_983_, lean_object* v_fallback_984_){
_start:
{
lean_object* v_res_985_; 
v_res_985_ = l_Std_HashMap_Raw_getKeyD(v_00_u03b1_978_, v_00_u03b2_979_, v_inst_980_, v_inst_981_, v_m_982_, v_a_983_, v_fallback_984_);
lean_dec(v_fallback_984_);
lean_dec_ref(v_m_982_);
return v_res_985_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg(lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_m_989_, lean_object* v_a_990_){
_start:
{
lean_object* v_buckets_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_buckets_991_ = lean_ctor_get(v_m_989_, 1);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_array_get_size(v_buckets_991_);
v___x_994_ = lean_nat_dec_lt(v___x_992_, v___x_993_);
if (v___x_994_ == 0)
{
lean_dec(v_a_990_);
lean_dec_ref(v_inst_987_);
lean_dec_ref(v_inst_986_);
lean_inc(v_inst_988_);
return v_inst_988_;
}
else
{
lean_object* v___x_995_; 
v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_986_, v_inst_987_, v_inst_988_, v_m_989_, v_a_990_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_m_999_, lean_object* v_a_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Std_HashMap_Raw_getKey_x21___redArg(v_inst_996_, v_inst_997_, v_inst_998_, v_m_999_, v_a_1000_);
lean_dec_ref(v_m_999_);
lean_dec(v_inst_998_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21(lean_object* v_00_u03b1_1002_, lean_object* v_00_u03b2_1003_, lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_m_1007_, lean_object* v_a_1008_){
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
lean_dec_ref(v_inst_1005_);
lean_dec_ref(v_inst_1004_);
lean_inc(v_inst_1006_);
return v_inst_1006_;
}
else
{
lean_object* v___x_1013_; 
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1004_, v_inst_1005_, v_inst_1006_, v_m_1007_, v_a_1008_);
return v___x_1013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_inst_1018_, lean_object* v_m_1019_, lean_object* v_a_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l_Std_HashMap_Raw_getKey_x21(v_00_u03b1_1014_, v_00_u03b2_1015_, v_inst_1016_, v_inst_1017_, v_inst_1018_, v_m_1019_, v_a_1020_);
lean_dec_ref(v_m_1019_);
lean_dec(v_inst_1018_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase___redArg(lean_object* v_inst_1022_, lean_object* v_inst_1023_, lean_object* v_m_1024_, lean_object* v_a_1025_){
_start:
{
lean_object* v_buckets_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v_buckets_1026_ = lean_ctor_get(v_m_1024_, 1);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_array_get_size(v_buckets_1026_);
v___x_1029_ = lean_nat_dec_lt(v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_dec(v_a_1025_);
lean_dec_ref(v_inst_1023_);
lean_dec_ref(v_inst_1022_);
return v_m_1024_;
}
else
{
lean_object* v___x_1030_; 
v___x_1030_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1022_, v_inst_1023_, v_m_1024_, v_a_1025_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase(lean_object* v_00_u03b1_1031_, lean_object* v_00_u03b2_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_m_1035_, lean_object* v_a_1036_){
_start:
{
lean_object* v_buckets_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v_buckets_1037_ = lean_ctor_get(v_m_1035_, 1);
v___x_1038_ = lean_unsigned_to_nat(0u);
v___x_1039_ = lean_array_get_size(v_buckets_1037_);
v___x_1040_ = lean_nat_dec_lt(v___x_1038_, v___x_1039_);
if (v___x_1040_ == 0)
{
lean_dec(v_a_1036_);
lean_dec_ref(v_inst_1034_);
lean_dec_ref(v_inst_1033_);
return v_m_1035_;
}
else
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1033_, v_inst_1034_, v_m_1035_, v_a_1036_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg(lean_object* v_m_1042_){
_start:
{
lean_object* v_size_1043_; 
v_size_1043_ = lean_ctor_get(v_m_1042_, 0);
lean_inc(v_size_1043_);
return v_size_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg___boxed(lean_object* v_m_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Std_HashMap_Raw_size___redArg(v_m_1044_);
lean_dec_ref(v_m_1044_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size(lean_object* v_00_u03b1_1046_, lean_object* v_00_u03b2_1047_, lean_object* v_m_1048_){
_start:
{
lean_object* v_size_1049_; 
v_size_1049_ = lean_ctor_get(v_m_1048_, 0);
lean_inc(v_size_1049_);
return v_size_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___boxed(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_m_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Std_HashMap_Raw_size(v_00_u03b1_1050_, v_00_u03b2_1051_, v_m_1052_);
lean_dec_ref(v_m_1052_);
return v_res_1053_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty___redArg(lean_object* v_m_1054_){
_start:
{
lean_object* v_size_1055_; lean_object* v___x_1056_; uint8_t v___x_1057_; 
v_size_1055_ = lean_ctor_get(v_m_1054_, 0);
v___x_1056_ = lean_unsigned_to_nat(0u);
v___x_1057_ = lean_nat_dec_eq(v_size_1055_, v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1058_){
_start:
{
uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_res_1059_ = l_Std_HashMap_Raw_isEmpty___redArg(v_m_1058_);
lean_dec_ref(v_m_1058_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty(lean_object* v_00_u03b1_1061_, lean_object* v_00_u03b2_1062_, lean_object* v_m_1063_){
_start:
{
lean_object* v_size_1064_; lean_object* v___x_1065_; uint8_t v___x_1066_; 
v_size_1064_ = lean_ctor_get(v_m_1063_, 0);
v___x_1065_ = lean_unsigned_to_nat(0u);
v___x_1066_ = lean_nat_dec_eq(v_size_1064_, v___x_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1067_, lean_object* v_00_u03b2_1068_, lean_object* v_m_1069_){
_start:
{
uint8_t v_res_1070_; lean_object* v_r_1071_; 
v_res_1070_ = l_Std_HashMap_Raw_isEmpty(v_00_u03b1_1067_, v_00_u03b2_1068_, v_m_1069_);
lean_dec_ref(v_m_1069_);
v_r_1071_ = lean_box(v_res_1070_);
return v_r_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0(lean_object* v_a_1072_, lean_object* v_b_1073_, lean_object* v_d_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_a_1072_);
lean_ctor_set(v___x_1075_, 1, v_d_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_a_1076_, lean_object* v_b_1077_, lean_object* v_d_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Std_HashMap_Raw_keys___redArg___lam__0(v_a_1076_, v_b_1077_, v_d_1078_);
lean_dec(v_b_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__1(lean_object* v___x_1080_, lean_object* v___f_1081_, lean_object* v_l_1082_, lean_object* v_acc_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1080_, v___f_1081_, v_acc_1083_, v_l_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg(lean_object* v_m_1108_){
_start:
{
lean_object* v___x_1109_; lean_object* v_buckets_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1109_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1110_ = lean_ctor_get(v_m_1108_, 1);
lean_inc_ref(v_buckets_1110_);
lean_dec_ref(v_m_1108_);
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_array_get_size(v_buckets_1110_);
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_nat_dec_lt(v___x_1113_, v___x_1112_);
if (v___x_1114_ == 0)
{
lean_dec_ref(v_buckets_1110_);
return v___x_1111_;
}
else
{
lean_object* v___f_1115_; size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
v___f_1115_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1116_ = lean_usize_of_nat(v___x_1112_);
v___x_1117_ = ((size_t)0ULL);
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1109_, v___f_1115_, v_buckets_1110_, v___x_1116_, v___x_1117_, v___x_1111_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys(lean_object* v_00_u03b1_1119_, lean_object* v_00_u03b2_1120_, lean_object* v_m_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v_buckets_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v___x_1122_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1123_ = lean_ctor_get(v_m_1121_, 1);
lean_inc_ref(v_buckets_1123_);
lean_dec_ref(v_m_1121_);
v___x_1124_ = lean_box(0);
v___x_1125_ = lean_array_get_size(v_buckets_1123_);
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = lean_nat_dec_lt(v___x_1126_, v___x_1125_);
if (v___x_1127_ == 0)
{
lean_dec_ref(v_buckets_1123_);
return v___x_1124_;
}
else
{
lean_object* v___f_1128_; size_t v___x_1129_; size_t v___x_1130_; lean_object* v___x_1131_; 
v___f_1128_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__11));
v___x_1129_ = lean_usize_of_nat(v___x_1125_);
v___x_1130_ = ((size_t)0ULL);
v___x_1131_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1122_, v___f_1128_, v_buckets_1123_, v___x_1129_, v___x_1130_, v___x_1124_);
return v___x_1131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList___redArg(lean_object* v_inst_1136_, lean_object* v_inst_1137_, lean_object* v_l_1138_){
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
v___x_1142_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1141_, v_inst_1136_, v_inst_1137_, v___x_1139_, v_l_1138_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList(lean_object* v_00_u03b1_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_l_1147_){
_start:
{
lean_object* v___x_1148_; uint8_t v___x_1149_; 
v___x_1148_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1149_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1149_ == 0)
{
lean_dec(v_l_1147_);
lean_dec_ref(v_inst_1146_);
lean_dec_ref(v_inst_1145_);
return v___x_1148_;
}
else
{
lean_object* v___f_1150_; lean_object* v___x_1151_; 
v___f_1150_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1151_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1150_, v_inst_1145_, v_inst_1146_, v___x_1148_, v_l_1147_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList___redArg(lean_object* v_inst_1152_, lean_object* v_inst_1153_, lean_object* v_l_1154_){
_start:
{
lean_object* v___x_1155_; uint8_t v___x_1156_; 
v___x_1155_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1156_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1156_ == 0)
{
lean_dec(v_l_1154_);
lean_dec_ref(v_inst_1153_);
lean_dec_ref(v_inst_1152_);
return v___x_1155_;
}
else
{
lean_object* v___f_1157_; lean_object* v___x_1158_; 
v___f_1157_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1158_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1157_, v_inst_1152_, v_inst_1153_, v___x_1155_, v_l_1154_);
return v___x_1158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList(lean_object* v_00_u03b1_1159_, lean_object* v_inst_1160_, lean_object* v_inst_1161_, lean_object* v_l_1162_){
_start:
{
lean_object* v___x_1163_; uint8_t v___x_1164_; 
v___x_1163_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1164_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1164_ == 0)
{
lean_dec(v_l_1162_);
lean_dec_ref(v_inst_1161_);
lean_dec_ref(v_inst_1160_);
return v___x_1163_;
}
else
{
lean_object* v___f_1165_; lean_object* v___x_1166_; 
v___f_1165_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1166_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1165_, v_inst_1160_, v_inst_1161_, v___x_1163_, v_l_1162_);
return v___x_1166_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray___redArg(lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v___x_1174_; uint8_t v___x_1175_; 
v___x_1174_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1175_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1175_ == 0)
{
lean_dec_ref(v_a_1173_);
lean_dec_ref(v_inst_1172_);
lean_dec_ref(v_inst_1171_);
return v___x_1174_;
}
else
{
lean_object* v___f_1176_; lean_object* v___x_1177_; 
v___f_1176_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1176_, v_inst_1171_, v_inst_1172_, v___x_1174_, v_a_1173_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray(lean_object* v_00_u03b1_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_inst_1180_, lean_object* v_inst_1181_, lean_object* v_a_1182_){
_start:
{
lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1183_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_1184_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1184_ == 0)
{
lean_dec_ref(v_a_1182_);
lean_dec_ref(v_inst_1181_);
lean_dec_ref(v_inst_1180_);
return v___x_1183_;
}
else
{
lean_object* v___f_1185_; lean_object* v___x_1186_; 
v___f_1185_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1186_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1185_, v_inst_1180_, v_inst_1181_, v___x_1183_, v_a_1182_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter___redArg(lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_m_1189_, lean_object* v_a_1190_, lean_object* v_f_1191_){
_start:
{
lean_object* v_buckets_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; 
v_buckets_1192_ = lean_ctor_get(v_m_1189_, 1);
v___x_1193_ = lean_unsigned_to_nat(0u);
v___x_1194_ = lean_array_get_size(v_buckets_1192_);
v___x_1195_ = lean_nat_dec_lt(v___x_1193_, v___x_1194_);
if (v___x_1195_ == 0)
{
lean_object* v___x_1196_; 
lean_dec_ref(v_f_1191_);
lean_dec(v_a_1190_);
lean_dec_ref(v_m_1189_);
lean_dec_ref(v_inst_1188_);
lean_dec_ref(v_inst_1187_);
v___x_1196_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1196_;
}
else
{
lean_object* v___x_1197_; 
v___x_1197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1187_, v_inst_1188_, v_m_1189_, v_a_1190_, v_f_1191_);
return v___x_1197_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_inst_1200_, lean_object* v_inst_1201_, lean_object* v_inst_1202_, lean_object* v_m_1203_, lean_object* v_a_1204_, lean_object* v_f_1205_){
_start:
{
lean_object* v_buckets_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v_buckets_1206_ = lean_ctor_get(v_m_1203_, 1);
v___x_1207_ = lean_unsigned_to_nat(0u);
v___x_1208_ = lean_array_get_size(v_buckets_1206_);
v___x_1209_ = lean_nat_dec_lt(v___x_1207_, v___x_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; 
lean_dec_ref(v_f_1205_);
lean_dec(v_a_1204_);
lean_dec_ref(v_m_1203_);
lean_dec_ref(v_inst_1202_);
lean_dec_ref(v_inst_1200_);
v___x_1210_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1210_;
}
else
{
lean_object* v___x_1211_; 
v___x_1211_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_1200_, v_inst_1202_, v_m_1203_, v_a_1204_, v_f_1205_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify___redArg(lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_m_1214_, lean_object* v_a_1215_, lean_object* v_f_1216_){
_start:
{
lean_object* v_buckets_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; uint8_t v___x_1220_; 
v_buckets_1217_ = lean_ctor_get(v_m_1214_, 1);
v___x_1218_ = lean_unsigned_to_nat(0u);
v___x_1219_ = lean_array_get_size(v_buckets_1217_);
v___x_1220_ = lean_nat_dec_lt(v___x_1218_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; 
lean_dec(v_f_1216_);
lean_dec(v_a_1215_);
lean_dec_ref(v_m_1214_);
lean_dec_ref(v_inst_1213_);
lean_dec_ref(v_inst_1212_);
v___x_1221_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1221_;
}
else
{
lean_object* v___x_1222_; 
v___x_1222_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1212_, v_inst_1213_, v_m_1214_, v_a_1215_, v_f_1216_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify(lean_object* v_00_u03b1_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_inst_1227_, lean_object* v_m_1228_, lean_object* v_a_1229_, lean_object* v_f_1230_){
_start:
{
lean_object* v_buckets_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; uint8_t v___x_1234_; 
v_buckets_1231_ = lean_ctor_get(v_m_1228_, 1);
v___x_1232_ = lean_unsigned_to_nat(0u);
v___x_1233_ = lean_array_get_size(v_buckets_1231_);
v___x_1234_ = lean_nat_dec_lt(v___x_1232_, v___x_1233_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec(v_f_1230_);
lean_dec(v_a_1229_);
lean_dec_ref(v_m_1228_);
lean_dec_ref(v_inst_1227_);
lean_dec_ref(v_inst_1225_);
v___x_1235_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1235_;
}
else
{
lean_object* v___x_1236_; 
v___x_1236_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_inst_1225_, v_inst_1227_, v_m_1228_, v_a_1229_, v_f_1230_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__0(lean_object* v_a_1237_, lean_object* v_b_1238_, lean_object* v_d_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1240_, 0, v_a_1237_);
lean_ctor_set(v___x_1240_, 1, v_b_1238_);
v___x_1241_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v_d_1239_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__1(lean_object* v___x_1242_, lean_object* v___f_1243_, lean_object* v_l_1244_, lean_object* v_acc_1245_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1242_, v___f_1243_, v_acc_1245_, v_l_1244_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg(lean_object* v_m_1251_){
_start:
{
lean_object* v___x_1252_; lean_object* v_buckets_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v___x_1252_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1253_ = lean_ctor_get(v_m_1251_, 1);
lean_inc_ref(v_buckets_1253_);
lean_dec_ref(v_m_1251_);
v___x_1254_ = lean_box(0);
v___x_1255_ = lean_array_get_size(v_buckets_1253_);
v___x_1256_ = lean_unsigned_to_nat(0u);
v___x_1257_ = lean_nat_dec_lt(v___x_1256_, v___x_1255_);
if (v___x_1257_ == 0)
{
lean_dec_ref(v_buckets_1253_);
return v___x_1254_;
}
else
{
lean_object* v___f_1258_; size_t v___x_1259_; size_t v___x_1260_; lean_object* v___x_1261_; 
v___f_1258_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1259_ = lean_usize_of_nat(v___x_1255_);
v___x_1260_ = ((size_t)0ULL);
v___x_1261_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1252_, v___f_1258_, v_buckets_1253_, v___x_1259_, v___x_1260_, v___x_1254_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList(lean_object* v_00_u03b1_1262_, lean_object* v_00_u03b2_1263_, lean_object* v_m_1264_){
_start:
{
lean_object* v___x_1265_; lean_object* v_buckets_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v___x_1265_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1266_ = lean_ctor_get(v_m_1264_, 1);
lean_inc_ref(v_buckets_1266_);
lean_dec_ref(v_m_1264_);
v___x_1267_ = lean_box(0);
v___x_1268_ = lean_array_get_size(v_buckets_1266_);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_nat_dec_lt(v___x_1269_, v___x_1268_);
if (v___x_1270_ == 0)
{
lean_dec_ref(v_buckets_1266_);
return v___x_1267_;
}
else
{
lean_object* v___f_1271_; size_t v___x_1272_; size_t v___x_1273_; lean_object* v___x_1274_; 
v___f_1271_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__1));
v___x_1272_ = lean_usize_of_nat(v___x_1268_);
v___x_1273_ = ((size_t)0ULL);
v___x_1274_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1265_, v___f_1271_, v_buckets_1266_, v___x_1272_, v___x_1273_, v___x_1267_);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg___lam__0(lean_object* v_inst_1275_, lean_object* v_f_1276_, lean_object* v_acc_1277_, lean_object* v_l_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1275_, v_f_1276_, v_acc_1277_, v_l_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg(lean_object* v_inst_1280_, lean_object* v_f_1281_, lean_object* v_init_1282_, lean_object* v_b_1283_){
_start:
{
lean_object* v_toApplicative_1284_; lean_object* v_buckets_1285_; lean_object* v_toPure_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_toApplicative_1284_ = lean_ctor_get(v_inst_1280_, 0);
v_buckets_1285_ = lean_ctor_get(v_b_1283_, 1);
lean_inc_ref(v_buckets_1285_);
lean_dec_ref(v_b_1283_);
v_toPure_1286_ = lean_ctor_get(v_toApplicative_1284_, 1);
v___x_1287_ = lean_unsigned_to_nat(0u);
v___x_1288_ = lean_array_get_size(v_buckets_1285_);
v___x_1289_ = lean_nat_dec_lt(v___x_1287_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_inc(v_toPure_1286_);
lean_dec_ref(v_buckets_1285_);
lean_dec(v_f_1281_);
lean_dec_ref(v_inst_1280_);
v___x_1290_ = lean_apply_2(v_toPure_1286_, lean_box(0), v_init_1282_);
return v___x_1290_;
}
else
{
lean_object* v___f_1291_; size_t v___x_1292_; size_t v___x_1293_; lean_object* v___x_1294_; 
lean_inc_ref(v_inst_1280_);
v___f_1291_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1291_, 0, v_inst_1280_);
lean_closure_set(v___f_1291_, 1, v_f_1281_);
v___x_1292_ = ((size_t)0ULL);
v___x_1293_ = lean_usize_of_nat(v___x_1288_);
v___x_1294_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1280_, v___f_1291_, v_buckets_1285_, v___x_1292_, v___x_1293_, v_init_1282_);
return v___x_1294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object* v_00_u03b1_1295_, lean_object* v_00_u03b2_1296_, lean_object* v_m_1297_, lean_object* v_inst_1298_, lean_object* v_00_u03b3_1299_, lean_object* v_f_1300_, lean_object* v_init_1301_, lean_object* v_b_1302_){
_start:
{
lean_object* v_toApplicative_1303_; lean_object* v_buckets_1304_; lean_object* v_toPure_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_toApplicative_1303_ = lean_ctor_get(v_inst_1298_, 0);
v_buckets_1304_ = lean_ctor_get(v_b_1302_, 1);
lean_inc_ref(v_buckets_1304_);
lean_dec_ref(v_b_1302_);
v_toPure_1305_ = lean_ctor_get(v_toApplicative_1303_, 1);
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_array_get_size(v_buckets_1304_);
v___x_1308_ = lean_nat_dec_lt(v___x_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_inc(v_toPure_1305_);
lean_dec_ref(v_buckets_1304_);
lean_dec(v_f_1300_);
lean_dec_ref(v_inst_1298_);
v___x_1309_ = lean_apply_2(v_toPure_1305_, lean_box(0), v_init_1301_);
return v___x_1309_;
}
else
{
lean_object* v___f_1310_; size_t v___x_1311_; size_t v___x_1312_; lean_object* v___x_1313_; 
lean_inc_ref(v_inst_1298_);
v___f_1310_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1310_, 0, v_inst_1298_);
lean_closure_set(v___f_1310_, 1, v_f_1300_);
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = lean_usize_of_nat(v___x_1307_);
v___x_1313_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1298_, v___f_1310_, v_buckets_1304_, v___x_1311_, v___x_1312_, v_init_1301_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object* v_f_1314_, lean_object* v_x1_1315_, lean_object* v_x2_1316_, lean_object* v_x3_1317_){
_start:
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_apply_3(v_f_1314_, v_x1_1315_, v_x2_1316_, v_x3_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__1(lean_object* v___x_1319_, lean_object* v___f_1320_, lean_object* v_acc_1321_, lean_object* v_l_1322_){
_start:
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1319_, v___f_1320_, v_acc_1321_, v_l_1322_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object* v_f_1324_, lean_object* v_init_1325_, lean_object* v_b_1326_){
_start:
{
lean_object* v___x_1327_; lean_object* v_buckets_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1327_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1328_ = lean_ctor_get(v_b_1326_, 1);
lean_inc_ref(v_buckets_1328_);
lean_dec_ref(v_b_1326_);
v___x_1329_ = lean_unsigned_to_nat(0u);
v___x_1330_ = lean_array_get_size(v_buckets_1328_);
v___x_1331_ = lean_nat_dec_lt(v___x_1329_, v___x_1330_);
if (v___x_1331_ == 0)
{
lean_dec_ref(v_buckets_1328_);
lean_dec(v_f_1324_);
return v_init_1325_;
}
else
{
lean_object* v___f_1332_; lean_object* v___f_1333_; size_t v___x_1334_; size_t v___x_1335_; lean_object* v___x_1336_; 
v___f_1332_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1332_, 0, v_f_1324_);
v___f_1333_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1333_, 0, v___x_1327_);
lean_closure_set(v___f_1333_, 1, v___f_1332_);
v___x_1334_ = ((size_t)0ULL);
v___x_1335_ = lean_usize_of_nat(v___x_1330_);
v___x_1336_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1327_, v___f_1333_, v_buckets_1328_, v___x_1334_, v___x_1335_, v_init_1325_);
return v___x_1336_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_00_u03b3_1339_, lean_object* v_f_1340_, lean_object* v_init_1341_, lean_object* v_b_1342_){
_start:
{
lean_object* v___x_1343_; lean_object* v_buckets_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; uint8_t v___x_1347_; 
v___x_1343_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1344_ = lean_ctor_get(v_b_1342_, 1);
lean_inc_ref(v_buckets_1344_);
lean_dec_ref(v_b_1342_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_array_get_size(v_buckets_1344_);
v___x_1347_ = lean_nat_dec_lt(v___x_1345_, v___x_1346_);
if (v___x_1347_ == 0)
{
lean_dec_ref(v_buckets_1344_);
lean_dec(v_f_1340_);
return v_init_1341_;
}
else
{
lean_object* v___f_1348_; lean_object* v___f_1349_; size_t v___x_1350_; size_t v___x_1351_; lean_object* v___x_1352_; 
v___f_1348_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1348_, 0, v_f_1340_);
v___f_1349_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1349_, 0, v___x_1343_);
lean_closure_set(v___f_1349_, 1, v___f_1348_);
v___x_1350_ = ((size_t)0ULL);
v___x_1351_ = lean_usize_of_nat(v___x_1346_);
v___x_1352_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1343_, v___f_1349_, v_buckets_1344_, v___x_1350_, v___x_1351_, v_init_1341_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object* v_f_1353_, lean_object* v_x_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
lean_object* v___x_1357_; 
v___x_1357_ = lean_apply_2(v_f_1353_, v___y_1355_, v___y_1356_);
return v___x_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__1(lean_object* v_inst_1358_, lean_object* v___f_1359_, lean_object* v_x_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1358_, v___f_1359_, v___x_1362_, v___y_1361_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object* v_inst_1364_, lean_object* v_f_1365_, lean_object* v_b_1366_){
_start:
{
lean_object* v_toApplicative_1367_; lean_object* v_buckets_1368_; lean_object* v_toPure_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_toApplicative_1367_ = lean_ctor_get(v_inst_1364_, 0);
v_buckets_1368_ = lean_ctor_get(v_b_1366_, 1);
lean_inc_ref(v_buckets_1368_);
lean_dec_ref(v_b_1366_);
v_toPure_1369_ = lean_ctor_get(v_toApplicative_1367_, 1);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = lean_array_get_size(v_buckets_1368_);
v___x_1372_ = lean_box(0);
v___x_1373_ = lean_nat_dec_lt(v___x_1370_, v___x_1371_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; 
lean_inc(v_toPure_1369_);
lean_dec_ref(v_buckets_1368_);
lean_dec(v_f_1365_);
lean_dec_ref(v_inst_1364_);
v___x_1374_ = lean_apply_2(v_toPure_1369_, lean_box(0), v___x_1372_);
return v___x_1374_;
}
else
{
lean_object* v___f_1375_; lean_object* v___f_1376_; size_t v___x_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v___f_1375_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1375_, 0, v_f_1365_);
lean_inc_ref(v_inst_1364_);
v___f_1376_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1376_, 0, v_inst_1364_);
lean_closure_set(v___f_1376_, 1, v___f_1375_);
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = lean_usize_of_nat(v___x_1371_);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1364_, v___f_1376_, v_buckets_1368_, v___x_1377_, v___x_1378_, v___x_1372_);
return v___x_1379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object* v_00_u03b1_1380_, lean_object* v_00_u03b2_1381_, lean_object* v_m_1382_, lean_object* v_inst_1383_, lean_object* v_f_1384_, lean_object* v_b_1385_){
_start:
{
lean_object* v_toApplicative_1386_; lean_object* v_buckets_1387_; lean_object* v_toPure_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_toApplicative_1386_ = lean_ctor_get(v_inst_1383_, 0);
v_buckets_1387_ = lean_ctor_get(v_b_1385_, 1);
lean_inc_ref(v_buckets_1387_);
lean_dec_ref(v_b_1385_);
v_toPure_1388_ = lean_ctor_get(v_toApplicative_1386_, 1);
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = lean_array_get_size(v_buckets_1387_);
v___x_1391_ = lean_box(0);
v___x_1392_ = lean_nat_dec_lt(v___x_1389_, v___x_1390_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; 
lean_inc(v_toPure_1388_);
lean_dec_ref(v_buckets_1387_);
lean_dec(v_f_1384_);
lean_dec_ref(v_inst_1383_);
v___x_1393_ = lean_apply_2(v_toPure_1388_, lean_box(0), v___x_1391_);
return v___x_1393_;
}
else
{
lean_object* v___f_1394_; lean_object* v___f_1395_; size_t v___x_1396_; size_t v___x_1397_; lean_object* v___x_1398_; 
v___f_1394_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1394_, 0, v_f_1384_);
lean_inc_ref(v_inst_1383_);
v___f_1395_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1395_, 0, v_inst_1383_);
lean_closure_set(v___f_1395_, 1, v___f_1394_);
v___x_1396_ = ((size_t)0ULL);
v___x_1397_ = lean_usize_of_nat(v___x_1390_);
v___x_1398_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1383_, v___f_1395_, v_buckets_1387_, v___x_1396_, v___x_1397_, v___x_1391_);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg___lam__0(lean_object* v_inst_1399_, lean_object* v_f_1400_, lean_object* v_a_1401_, lean_object* v_x_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v___x_1404_; 
v___x_1404_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1399_, v_f_1400_, v_a_1401_, v___y_1403_);
return v___x_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object* v_inst_1405_, lean_object* v_f_1406_, lean_object* v_init_1407_, lean_object* v_b_1408_){
_start:
{
lean_object* v_buckets_1409_; lean_object* v___f_1410_; size_t v_sz_1411_; size_t v___x_1412_; lean_object* v___x_1413_; 
v_buckets_1409_ = lean_ctor_get(v_b_1408_, 1);
lean_inc_ref(v_buckets_1409_);
lean_dec_ref(v_b_1408_);
lean_inc_ref(v_inst_1405_);
v___f_1410_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1410_, 0, v_inst_1405_);
lean_closure_set(v___f_1410_, 1, v_f_1406_);
v_sz_1411_ = lean_array_size(v_buckets_1409_);
v___x_1412_ = ((size_t)0ULL);
v___x_1413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1405_, v_buckets_1409_, v___f_1410_, v_sz_1411_, v___x_1412_, v_init_1407_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object* v_00_u03b1_1414_, lean_object* v_00_u03b2_1415_, lean_object* v_m_1416_, lean_object* v_inst_1417_, lean_object* v_00_u03b3_1418_, lean_object* v_f_1419_, lean_object* v_init_1420_, lean_object* v_b_1421_){
_start:
{
lean_object* v_buckets_1422_; lean_object* v___f_1423_; size_t v_sz_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
v_buckets_1422_ = lean_ctor_get(v_b_1421_, 1);
lean_inc_ref(v_buckets_1422_);
lean_dec_ref(v_b_1421_);
lean_inc_ref(v_inst_1417_);
v___f_1423_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1423_, 0, v_inst_1417_);
lean_closure_set(v___f_1423_, 1, v_f_1419_);
v_sz_1424_ = lean_array_size(v_buckets_1422_);
v___x_1425_ = ((size_t)0ULL);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1417_, v_buckets_1422_, v___f_1423_, v_sz_1424_, v___x_1425_, v_init_1420_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1427_, lean_object* v_x_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___y_1429_);
lean_ctor_set(v___x_1431_, 1, v___y_1430_);
v___x_1432_ = lean_apply_1(v_f_1427_, v___x_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1433_, lean_object* v_m_1434_, lean_object* v_f_1435_){
_start:
{
lean_object* v_toApplicative_1436_; lean_object* v_buckets_1437_; lean_object* v_toPure_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; uint8_t v___x_1442_; 
v_toApplicative_1436_ = lean_ctor_get(v_inst_1433_, 0);
v_buckets_1437_ = lean_ctor_get(v_m_1434_, 1);
lean_inc_ref(v_buckets_1437_);
lean_dec_ref(v_m_1434_);
v_toPure_1438_ = lean_ctor_get(v_toApplicative_1436_, 1);
v___x_1439_ = lean_unsigned_to_nat(0u);
v___x_1440_ = lean_array_get_size(v_buckets_1437_);
v___x_1441_ = lean_box(0);
v___x_1442_ = lean_nat_dec_lt(v___x_1439_, v___x_1440_);
if (v___x_1442_ == 0)
{
lean_object* v___x_1443_; 
lean_inc(v_toPure_1438_);
lean_dec_ref(v_buckets_1437_);
lean_dec(v_f_1435_);
lean_dec_ref(v_inst_1433_);
v___x_1443_ = lean_apply_2(v_toPure_1438_, lean_box(0), v___x_1441_);
return v___x_1443_;
}
else
{
lean_object* v___f_1444_; lean_object* v___f_1445_; size_t v___x_1446_; size_t v___x_1447_; lean_object* v___x_1448_; 
v___f_1444_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1444_, 0, v_f_1435_);
lean_inc_ref(v_inst_1433_);
v___f_1445_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1445_, 0, v_inst_1433_);
lean_closure_set(v___f_1445_, 1, v___f_1444_);
v___x_1446_ = ((size_t)0ULL);
v___x_1447_ = lean_usize_of_nat(v___x_1440_);
v___x_1448_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1433_, v___f_1445_, v_buckets_1437_, v___x_1446_, v___x_1447_, v___x_1441_);
return v___x_1448_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1449_){
_start:
{
lean_object* v___f_1450_; 
v___f_1450_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1450_, 0, v_inst_1449_);
return v___f_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1451_, lean_object* v_00_u03b2_1452_, lean_object* v_m_1453_, lean_object* v_inst_1454_){
_start:
{
lean_object* v___f_1455_; 
v___f_1455_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1455_, 0, v_inst_1454_);
return v___f_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1456_, lean_object* v_a_1457_, lean_object* v_b_1458_, lean_object* v_acc_1459_){
_start:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1460_, 0, v_a_1457_);
lean_ctor_set(v___x_1460_, 1, v_b_1458_);
v___x_1461_ = lean_apply_2(v_f_1456_, v___x_1460_, v_acc_1459_);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1462_, lean_object* v___f_1463_, lean_object* v_a_1464_, lean_object* v_x_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1462_, v___f_1463_, v_a_1464_, v___y_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1468_, lean_object* v_00_u03b2_1469_, lean_object* v_m_1470_, lean_object* v_init_1471_, lean_object* v_f_1472_){
_start:
{
lean_object* v_buckets_1473_; lean_object* v___f_1474_; lean_object* v___f_1475_; size_t v_sz_1476_; size_t v___x_1477_; lean_object* v___x_1478_; 
v_buckets_1473_ = lean_ctor_get(v_m_1470_, 1);
lean_inc_ref(v_buckets_1473_);
lean_dec_ref(v_m_1470_);
v___f_1474_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1474_, 0, v_f_1472_);
lean_inc_ref(v_inst_1468_);
v___f_1475_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1475_, 0, v_inst_1468_);
lean_closure_set(v___f_1475_, 1, v___f_1474_);
v_sz_1476_ = lean_array_size(v_buckets_1473_);
v___x_1477_ = ((size_t)0ULL);
v___x_1478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1468_, v_buckets_1473_, v___f_1475_, v_sz_1476_, v___x_1477_, v_init_1471_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1479_){
_start:
{
lean_object* v___f_1480_; 
v___f_1480_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1480_, 0, v_inst_1479_);
return v___f_1480_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1481_, lean_object* v_00_u03b2_1482_, lean_object* v_m_1483_, lean_object* v_inst_1484_){
_start:
{
lean_object* v___f_1485_; 
v___f_1485_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1485_, 0, v_inst_1484_);
return v___f_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object* v_p_1486_, lean_object* v___x_1487_, lean_object* v___x_1488_, lean_object* v_a_1489_, lean_object* v_b_1490_, lean_object* v_acc_1491_){
_start:
{
lean_object* v___x_1492_; uint8_t v___x_1493_; 
v___x_1492_ = lean_apply_2(v_p_1486_, v_a_1489_, v_b_1490_);
v___x_1493_ = lean_unbox(v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
lean_dec_ref(v___x_1488_);
v___x_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1487_);
v___x_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1496_, 0, v___x_1495_);
return v___x_1496_;
}
else
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1488_);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1498_, lean_object* v___x_1499_, lean_object* v___x_1500_, lean_object* v_a_1501_, lean_object* v_b_1502_, lean_object* v_acc_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Std_HashMap_Raw_all___redArg___lam__0(v_p_1498_, v___x_1499_, v___x_1500_, v_a_1501_, v_b_1502_, v_acc_1503_);
lean_dec_ref(v_acc_1503_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__1(lean_object* v___x_1505_, lean_object* v___f_1506_, lean_object* v_a_1507_, lean_object* v_x_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1505_, v___f_1506_, v_a_1507_, v___y_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all___redArg(lean_object* v_m_1514_, lean_object* v_p_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v_buckets_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___f_1520_; lean_object* v___f_1521_; size_t v_sz_1522_; size_t v___x_1523_; lean_object* v___x_1524_; lean_object* v_fst_1525_; 
v___x_1516_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1517_ = lean_ctor_get(v_m_1514_, 1);
lean_inc_ref(v_buckets_1517_);
lean_dec_ref(v_m_1514_);
v___x_1518_ = lean_box(0);
v___x_1519_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1520_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1520_, 0, v_p_1515_);
lean_closure_set(v___f_1520_, 1, v___x_1518_);
lean_closure_set(v___f_1520_, 2, v___x_1519_);
v___f_1521_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1521_, 0, v___x_1516_);
lean_closure_set(v___f_1521_, 1, v___f_1520_);
v_sz_1522_ = lean_array_size(v_buckets_1517_);
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1516_, v_buckets_1517_, v___f_1521_, v_sz_1522_, v___x_1523_, v___x_1519_);
v_fst_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_fst_1525_);
lean_dec(v___x_1524_);
if (lean_obj_tag(v_fst_1525_) == 0)
{
uint8_t v___x_1526_; 
v___x_1526_ = 1;
return v___x_1526_;
}
else
{
lean_object* v_val_1527_; uint8_t v___x_1528_; 
v_val_1527_ = lean_ctor_get(v_fst_1525_, 0);
lean_inc(v_val_1527_);
lean_dec_ref_known(v_fst_1525_, 1);
v___x_1528_ = lean_unbox(v_val_1527_);
lean_dec(v_val_1527_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___boxed(lean_object* v_m_1529_, lean_object* v_p_1530_){
_start:
{
uint8_t v_res_1531_; lean_object* v_r_1532_; 
v_res_1531_ = l_Std_HashMap_Raw_all___redArg(v_m_1529_, v_p_1530_);
v_r_1532_ = lean_box(v_res_1531_);
return v_r_1532_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all(lean_object* v_00_u03b1_1533_, lean_object* v_00_u03b2_1534_, lean_object* v_m_1535_, lean_object* v_p_1536_){
_start:
{
lean_object* v___x_1537_; lean_object* v_buckets_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___f_1541_; lean_object* v___f_1542_; size_t v_sz_1543_; size_t v___x_1544_; lean_object* v___x_1545_; lean_object* v_fst_1546_; 
v___x_1537_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1538_ = lean_ctor_get(v_m_1535_, 1);
lean_inc_ref(v_buckets_1538_);
lean_dec_ref(v_m_1535_);
v___x_1539_ = lean_box(0);
v___x_1540_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1541_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1541_, 0, v_p_1536_);
lean_closure_set(v___f_1541_, 1, v___x_1539_);
lean_closure_set(v___f_1541_, 2, v___x_1540_);
v___f_1542_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1542_, 0, v___x_1537_);
lean_closure_set(v___f_1542_, 1, v___f_1541_);
v_sz_1543_ = lean_array_size(v_buckets_1538_);
v___x_1544_ = ((size_t)0ULL);
v___x_1545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1537_, v_buckets_1538_, v___f_1542_, v_sz_1543_, v___x_1544_, v___x_1540_);
v_fst_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_fst_1546_);
lean_dec(v___x_1545_);
if (lean_obj_tag(v_fst_1546_) == 0)
{
uint8_t v___x_1547_; 
v___x_1547_ = 1;
return v___x_1547_;
}
else
{
lean_object* v_val_1548_; uint8_t v___x_1549_; 
v_val_1548_ = lean_ctor_get(v_fst_1546_, 0);
lean_inc(v_val_1548_);
lean_dec_ref_known(v_fst_1546_, 1);
v___x_1549_ = lean_unbox(v_val_1548_);
lean_dec(v_val_1548_);
return v___x_1549_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___boxed(lean_object* v_00_u03b1_1550_, lean_object* v_00_u03b2_1551_, lean_object* v_m_1552_, lean_object* v_p_1553_){
_start:
{
uint8_t v_res_1554_; lean_object* v_r_1555_; 
v_res_1554_ = l_Std_HashMap_Raw_all(v_00_u03b1_1550_, v_00_u03b2_1551_, v_m_1552_, v_p_1553_);
v_r_1555_ = lean_box(v_res_1554_);
return v_r_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0(lean_object* v_p_1556_, lean_object* v___x_1557_, lean_object* v___x_1558_, lean_object* v_a_1559_, lean_object* v_b_1560_, lean_object* v_acc_1561_){
_start:
{
lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1562_ = lean_apply_2(v_p_1556_, v_a_1559_, v_b_1560_);
v___x_1563_ = lean_unbox(v___x_1562_);
if (v___x_1563_ == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1557_);
return v___x_1564_;
}
else
{
lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
lean_dec_ref(v___x_1557_);
v___x_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1562_);
v___x_1566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___x_1558_);
v___x_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1567_, 0, v___x_1566_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1568_, lean_object* v___x_1569_, lean_object* v___x_1570_, lean_object* v_a_1571_, lean_object* v_b_1572_, lean_object* v_acc_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_Std_HashMap_Raw_any___redArg___lam__0(v_p_1568_, v___x_1569_, v___x_1570_, v_a_1571_, v_b_1572_, v_acc_1573_);
lean_dec_ref(v_acc_1573_);
return v_res_1574_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any___redArg(lean_object* v_m_1575_, lean_object* v_p_1576_){
_start:
{
lean_object* v___x_1577_; lean_object* v_buckets_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___f_1581_; lean_object* v___f_1582_; size_t v_sz_1583_; size_t v___x_1584_; lean_object* v___x_1585_; lean_object* v_fst_1586_; 
v___x_1577_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1578_ = lean_ctor_get(v_m_1575_, 1);
lean_inc_ref(v_buckets_1578_);
lean_dec_ref(v_m_1575_);
v___x_1579_ = lean_box(0);
v___x_1580_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1581_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1581_, 0, v_p_1576_);
lean_closure_set(v___f_1581_, 1, v___x_1580_);
lean_closure_set(v___f_1581_, 2, v___x_1579_);
v___f_1582_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1582_, 0, v___x_1577_);
lean_closure_set(v___f_1582_, 1, v___f_1581_);
v_sz_1583_ = lean_array_size(v_buckets_1578_);
v___x_1584_ = ((size_t)0ULL);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1577_, v_buckets_1578_, v___f_1582_, v_sz_1583_, v___x_1584_, v___x_1580_);
v_fst_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_fst_1586_);
lean_dec(v___x_1585_);
if (lean_obj_tag(v_fst_1586_) == 0)
{
uint8_t v___x_1587_; 
v___x_1587_ = 0;
return v___x_1587_;
}
else
{
lean_object* v_val_1588_; uint8_t v___x_1589_; 
v_val_1588_ = lean_ctor_get(v_fst_1586_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v_fst_1586_, 1);
v___x_1589_ = lean_unbox(v_val_1588_);
lean_dec(v_val_1588_);
return v___x_1589_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___boxed(lean_object* v_m_1590_, lean_object* v_p_1591_){
_start:
{
uint8_t v_res_1592_; lean_object* v_r_1593_; 
v_res_1592_ = l_Std_HashMap_Raw_any___redArg(v_m_1590_, v_p_1591_);
v_r_1593_ = lean_box(v_res_1592_);
return v_r_1593_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any(lean_object* v_00_u03b1_1594_, lean_object* v_00_u03b2_1595_, lean_object* v_m_1596_, lean_object* v_p_1597_){
_start:
{
lean_object* v___x_1598_; lean_object* v_buckets_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___f_1602_; lean_object* v___f_1603_; size_t v_sz_1604_; size_t v___x_1605_; lean_object* v___x_1606_; lean_object* v_fst_1607_; 
v___x_1598_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1599_ = lean_ctor_get(v_m_1596_, 1);
lean_inc_ref(v_buckets_1599_);
lean_dec_ref(v_m_1596_);
v___x_1600_ = lean_box(0);
v___x_1601_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1602_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1602_, 0, v_p_1597_);
lean_closure_set(v___f_1602_, 1, v___x_1601_);
lean_closure_set(v___f_1602_, 2, v___x_1600_);
v___f_1603_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1603_, 0, v___x_1598_);
lean_closure_set(v___f_1603_, 1, v___f_1602_);
v_sz_1604_ = lean_array_size(v_buckets_1599_);
v___x_1605_ = ((size_t)0ULL);
v___x_1606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1598_, v_buckets_1599_, v___f_1603_, v_sz_1604_, v___x_1605_, v___x_1601_);
v_fst_1607_ = lean_ctor_get(v___x_1606_, 0);
lean_inc(v_fst_1607_);
lean_dec(v___x_1606_);
if (lean_obj_tag(v_fst_1607_) == 0)
{
uint8_t v___x_1608_; 
v___x_1608_ = 0;
return v___x_1608_;
}
else
{
lean_object* v_val_1609_; uint8_t v___x_1610_; 
v_val_1609_ = lean_ctor_get(v_fst_1607_, 0);
lean_inc(v_val_1609_);
lean_dec_ref_known(v_fst_1607_, 1);
v___x_1610_ = lean_unbox(v_val_1609_);
lean_dec(v_val_1609_);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___boxed(lean_object* v_00_u03b1_1611_, lean_object* v_00_u03b2_1612_, lean_object* v_m_1613_, lean_object* v_p_1614_){
_start:
{
uint8_t v_res_1615_; lean_object* v_r_1616_; 
v_res_1615_ = l_Std_HashMap_Raw_any(v_00_u03b1_1611_, v_00_u03b2_1612_, v_m_1613_, v_p_1614_);
v_r_1616_ = lean_box(v_res_1615_);
return v_r_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__0(lean_object* v_inst_1617_, lean_object* v_inst_1618_, lean_object* v_a_1619_, lean_object* v_b_1620_, lean_object* v_acc_1621_){
_start:
{
lean_object* v_r_1622_; lean_object* v___x_1623_; 
v_r_1622_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1617_, v_inst_1618_, v_acc_1621_, v_a_1619_, v_b_1620_);
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v_r_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__1(lean_object* v___x_1624_, lean_object* v___f_1625_, lean_object* v_a_1626_, lean_object* v_x_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1624_, v___f_1625_, v_a_1626_, v___y_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg(lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_m_u2081_1634_, lean_object* v_m_u2082_1635_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union(lean_object* v_00_u03b1_1654_, lean_object* v_00_u03b2_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_m_u2081_1658_, lean_object* v_m_u2082_1659_){
_start:
{
lean_object* v_size_1660_; lean_object* v_buckets_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v_size_1660_ = lean_ctor_get(v_m_u2081_1658_, 0);
v_buckets_1661_ = lean_ctor_get(v_m_u2081_1658_, 1);
v___x_1662_ = lean_unsigned_to_nat(0u);
v___x_1663_ = lean_array_get_size(v_buckets_1661_);
v___x_1664_ = lean_nat_dec_lt(v___x_1662_, v___x_1663_);
if (v___x_1664_ == 0)
{
lean_dec_ref(v_m_u2081_1658_);
lean_dec_ref(v_inst_1657_);
lean_dec_ref(v_inst_1656_);
return v_m_u2082_1659_;
}
else
{
lean_object* v_size_1665_; lean_object* v_buckets_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v_size_1665_ = lean_ctor_get(v_m_u2082_1659_, 0);
v_buckets_1666_ = lean_ctor_get(v_m_u2082_1659_, 1);
v___x_1667_ = lean_array_get_size(v_buckets_1666_);
v___x_1668_ = lean_nat_dec_lt(v___x_1662_, v___x_1667_);
if (v___x_1668_ == 0)
{
lean_dec_ref(v_m_u2082_1659_);
lean_dec_ref(v_inst_1657_);
lean_dec_ref(v_inst_1656_);
return v_m_u2081_1658_;
}
else
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1670_ = lean_nat_dec_le(v_size_1660_, v_size_1665_);
if (v___x_1670_ == 0)
{
lean_object* v___f_1671_; lean_object* v___x_1672_; 
v___f_1671_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1672_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1671_, v_inst_1656_, v_inst_1657_, v_m_u2081_1658_, v_m_u2082_1659_);
return v___x_1672_;
}
else
{
lean_object* v___f_1673_; lean_object* v___f_1674_; size_t v_sz_1675_; size_t v___x_1676_; lean_object* v___x_1677_; 
lean_inc_ref(v_buckets_1661_);
lean_dec_ref(v_m_u2081_1658_);
v___f_1673_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1673_, 0, v_inst_1656_);
lean_closure_set(v___f_1673_, 1, v_inst_1657_);
v___f_1674_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1674_, 0, v___x_1669_);
lean_closure_set(v___f_1674_, 1, v___f_1673_);
v_sz_1675_ = lean_array_size(v_buckets_1661_);
v___x_1676_ = ((size_t)0ULL);
v___x_1677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1669_, v_buckets_1661_, v___f_1674_, v_sz_1675_, v___x_1676_, v_m_u2082_1659_);
return v___x_1677_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter___redArg(lean_object* v_inst_1678_, lean_object* v_inst_1679_, lean_object* v_m_u2081_1680_, lean_object* v_m_u2082_1681_){
_start:
{
lean_object* v_buckets_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v_buckets_1682_ = lean_ctor_get(v_m_u2081_1680_, 1);
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_array_get_size(v_buckets_1682_);
v___x_1685_ = lean_nat_dec_lt(v___x_1683_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_dec_ref(v_m_u2081_1680_);
lean_dec_ref(v_inst_1679_);
lean_dec_ref(v_inst_1678_);
return v_m_u2082_1681_;
}
else
{
lean_object* v_buckets_1686_; lean_object* v___x_1687_; uint8_t v___x_1688_; 
v_buckets_1686_ = lean_ctor_get(v_m_u2082_1681_, 1);
v___x_1687_ = lean_array_get_size(v_buckets_1686_);
v___x_1688_ = lean_nat_dec_lt(v___x_1683_, v___x_1687_);
if (v___x_1688_ == 0)
{
lean_dec_ref(v_m_u2082_1681_);
lean_dec_ref(v_inst_1679_);
lean_dec_ref(v_inst_1678_);
return v_m_u2081_1680_;
}
else
{
lean_object* v___x_1689_; 
v___x_1689_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1678_, v_inst_1679_, v_m_u2081_1680_, v_m_u2082_1681_);
return v___x_1689_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter(lean_object* v_00_u03b1_1690_, lean_object* v_00_u03b2_1691_, lean_object* v_inst_1692_, lean_object* v_inst_1693_, lean_object* v_m_u2081_1694_, lean_object* v_m_u2082_1695_){
_start:
{
lean_object* v_buckets_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; uint8_t v___x_1699_; 
v_buckets_1696_ = lean_ctor_get(v_m_u2081_1694_, 1);
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = lean_array_get_size(v_buckets_1696_);
v___x_1699_ = lean_nat_dec_lt(v___x_1697_, v___x_1698_);
if (v___x_1699_ == 0)
{
lean_dec_ref(v_m_u2081_1694_);
lean_dec_ref(v_inst_1693_);
lean_dec_ref(v_inst_1692_);
return v_m_u2082_1695_;
}
else
{
lean_object* v_buckets_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v_buckets_1700_ = lean_ctor_get(v_m_u2082_1695_, 1);
v___x_1701_ = lean_array_get_size(v_buckets_1700_);
v___x_1702_ = lean_nat_dec_lt(v___x_1697_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_dec_ref(v_m_u2082_1695_);
lean_dec_ref(v_inst_1693_);
lean_dec_ref(v_inst_1692_);
return v_m_u2081_1694_;
}
else
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1692_, v_inst_1693_, v_m_u2081_1694_, v_m_u2082_1695_);
return v___x_1703_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_m_u2082_1706_, uint8_t v___x_1707_, lean_object* v_k_1708_, lean_object* v_x_1709_){
_start:
{
uint8_t v___x_1710_; 
v___x_1710_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1704_, v_inst_1705_, v_m_u2082_1706_, v_k_1708_);
if (v___x_1710_ == 0)
{
return v___x_1707_;
}
else
{
uint8_t v___x_1711_; 
v___x_1711_ = 0;
return v___x_1711_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1712_, lean_object* v_inst_1713_, lean_object* v_m_u2082_1714_, lean_object* v___x_1715_, lean_object* v_k_1716_, lean_object* v_x_1717_){
_start:
{
uint8_t v___x_91__boxed_1718_; uint8_t v_res_1719_; lean_object* v_r_1720_; 
v___x_91__boxed_1718_ = lean_unbox(v___x_1715_);
v_res_1719_ = l_Std_HashMap_Raw_diff___redArg___lam__0(v_inst_1712_, v_inst_1713_, v_m_u2082_1714_, v___x_91__boxed_1718_, v_k_1716_, v_x_1717_);
lean_dec(v_x_1717_);
lean_dec_ref(v_m_u2082_1714_);
v_r_1720_ = lean_box(v_res_1719_);
return v_r_1720_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg(lean_object* v_inst_1721_, lean_object* v_inst_1722_, lean_object* v_m_u2081_1723_, lean_object* v_m_u2082_1724_){
_start:
{
lean_object* v_size_1725_; lean_object* v_buckets_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_size_1725_ = lean_ctor_get(v_m_u2081_1723_, 0);
v_buckets_1726_ = lean_ctor_get(v_m_u2081_1723_, 1);
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_array_get_size(v_buckets_1726_);
v___x_1729_ = lean_nat_dec_lt(v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_dec_ref(v_m_u2081_1723_);
lean_dec_ref(v_inst_1722_);
lean_dec_ref(v_inst_1721_);
return v_m_u2082_1724_;
}
else
{
lean_object* v_size_1730_; lean_object* v_buckets_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_size_1730_ = lean_ctor_get(v_m_u2082_1724_, 0);
v_buckets_1731_ = lean_ctor_get(v_m_u2082_1724_, 1);
v___x_1732_ = lean_array_get_size(v_buckets_1731_);
v___x_1733_ = lean_nat_dec_lt(v___x_1727_, v___x_1732_);
if (v___x_1733_ == 0)
{
lean_dec_ref(v_m_u2082_1724_);
lean_dec_ref(v_inst_1722_);
lean_dec_ref(v_inst_1721_);
return v_m_u2081_1723_;
}
else
{
uint8_t v___x_1734_; 
v___x_1734_ = lean_nat_dec_le(v_size_1725_, v_size_1730_);
if (v___x_1734_ == 0)
{
lean_object* v___f_1735_; lean_object* v___x_1736_; 
v___f_1735_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1736_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1735_, v_inst_1721_, v_inst_1722_, v_m_u2081_1723_, v_m_u2082_1724_);
return v___x_1736_;
}
else
{
lean_object* v___x_1737_; lean_object* v___f_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_box(v___x_1734_);
v___f_1738_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1738_, 0, v_inst_1721_);
lean_closure_set(v___f_1738_, 1, v_inst_1722_);
lean_closure_set(v___f_1738_, 2, v_m_u2082_1724_);
lean_closure_set(v___f_1738_, 3, v___x_1737_);
v___x_1739_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1738_, v_m_u2081_1723_);
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff(lean_object* v_00_u03b1_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_inst_1742_, lean_object* v_inst_1743_, lean_object* v_m_u2081_1744_, lean_object* v_m_u2082_1745_){
_start:
{
lean_object* v_size_1746_; lean_object* v_buckets_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v_size_1746_ = lean_ctor_get(v_m_u2081_1744_, 0);
v_buckets_1747_ = lean_ctor_get(v_m_u2081_1744_, 1);
v___x_1748_ = lean_unsigned_to_nat(0u);
v___x_1749_ = lean_array_get_size(v_buckets_1747_);
v___x_1750_ = lean_nat_dec_lt(v___x_1748_, v___x_1749_);
if (v___x_1750_ == 0)
{
lean_dec_ref(v_m_u2081_1744_);
lean_dec_ref(v_inst_1743_);
lean_dec_ref(v_inst_1742_);
return v_m_u2082_1745_;
}
else
{
lean_object* v_size_1751_; lean_object* v_buckets_1752_; lean_object* v___x_1753_; uint8_t v___x_1754_; 
v_size_1751_ = lean_ctor_get(v_m_u2082_1745_, 0);
v_buckets_1752_ = lean_ctor_get(v_m_u2082_1745_, 1);
v___x_1753_ = lean_array_get_size(v_buckets_1752_);
v___x_1754_ = lean_nat_dec_lt(v___x_1748_, v___x_1753_);
if (v___x_1754_ == 0)
{
lean_dec_ref(v_m_u2082_1745_);
lean_dec_ref(v_inst_1743_);
lean_dec_ref(v_inst_1742_);
return v_m_u2081_1744_;
}
else
{
uint8_t v___x_1755_; 
v___x_1755_ = lean_nat_dec_le(v_size_1746_, v_size_1751_);
if (v___x_1755_ == 0)
{
lean_object* v___f_1756_; lean_object* v___x_1757_; 
v___f_1756_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_1757_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1756_, v_inst_1742_, v_inst_1743_, v_m_u2081_1744_, v_m_u2082_1745_);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; lean_object* v___f_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_box(v___x_1755_);
v___f_1759_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1759_, 0, v_inst_1742_);
lean_closure_set(v___f_1759_, 1, v_inst_1743_);
lean_closure_set(v___f_1759_, 2, v_m_u2082_1745_);
lean_closure_set(v___f_1759_, 3, v___x_1758_);
v___x_1760_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1759_, v_m_u2081_1744_);
return v___x_1760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1761_, lean_object* v_inst_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1763_, 0, lean_box(0));
lean_closure_set(v___x_1763_, 1, lean_box(0));
lean_closure_set(v___x_1763_, 2, v_inst_1761_);
lean_closure_set(v___x_1763_, 3, v_inst_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_1768_, 0, lean_box(0));
lean_closure_set(v___x_1768_, 1, lean_box(0));
lean_closure_set(v___x_1768_, 2, v_inst_1766_);
lean_closure_set(v___x_1768_, 3, v_inst_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1769_, lean_object* v_inst_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1771_, 0, lean_box(0));
lean_closure_set(v___x_1771_, 1, lean_box(0));
lean_closure_set(v___x_1771_, 2, v_inst_1769_);
lean_closure_set(v___x_1771_, 3, v_inst_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1772_, lean_object* v_00_u03b2_1773_, lean_object* v_inst_1774_, lean_object* v_inst_1775_){
_start:
{
lean_object* v___x_1776_; 
v___x_1776_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_1776_, 0, lean_box(0));
lean_closure_set(v___x_1776_, 1, lean_box(0));
lean_closure_set(v___x_1776_, 2, v_inst_1774_);
lean_closure_set(v___x_1776_, 3, v_inst_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1777_, lean_object* v_inst_1778_){
_start:
{
lean_object* v___x_1779_; 
v___x_1779_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1779_, 0, lean_box(0));
lean_closure_set(v___x_1779_, 1, lean_box(0));
lean_closure_set(v___x_1779_, 2, v_inst_1777_);
lean_closure_set(v___x_1779_, 3, v_inst_1778_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1780_, lean_object* v_00_u03b2_1781_, lean_object* v_inst_1782_, lean_object* v_inst_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_1784_, 0, lean_box(0));
lean_closure_set(v___x_1784_, 1, lean_box(0));
lean_closure_set(v___x_1784_, 2, v_inst_1782_);
lean_closure_set(v___x_1784_, 3, v_inst_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq___redArg(lean_object* v_inst_1785_, lean_object* v_inst_1786_, lean_object* v_inst_1787_, lean_object* v_m_u2081_1788_, lean_object* v_m_u2082_1789_){
_start:
{
uint8_t v___x_1790_; 
v___x_1790_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1785_, v_inst_1786_, v_inst_1787_, v_m_u2081_1788_, v_m_u2082_1789_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___redArg___boxed(lean_object* v_inst_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_m_u2081_1794_, lean_object* v_m_u2082_1795_){
_start:
{
uint8_t v_res_1796_; lean_object* v_r_1797_; 
v_res_1796_ = l_Std_HashMap_Raw_beq___redArg(v_inst_1791_, v_inst_1792_, v_inst_1793_, v_m_u2081_1794_, v_m_u2082_1795_);
v_r_1797_ = lean_box(v_res_1796_);
return v_r_1797_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq(lean_object* v_00_u03b1_1798_, lean_object* v_00_u03b2_1799_, lean_object* v_inst_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_m_u2081_1803_, lean_object* v_m_u2082_1804_){
_start:
{
uint8_t v___x_1805_; 
v___x_1805_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1800_, v_inst_1801_, v_inst_1802_, v_m_u2081_1803_, v_m_u2082_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___boxed(lean_object* v_00_u03b1_1806_, lean_object* v_00_u03b2_1807_, lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_m_u2081_1811_, lean_object* v_m_u2082_1812_){
_start:
{
uint8_t v_res_1813_; lean_object* v_r_1814_; 
v_res_1813_ = l_Std_HashMap_Raw_beq(v_00_u03b1_1806_, v_00_u03b2_1807_, v_inst_1808_, v_inst_1809_, v_inst_1810_, v_m_u2081_1811_, v_m_u2082_1812_);
v_r_1814_ = lean_box(v_res_1813_);
return v_r_1814_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1818_, 0, lean_box(0));
lean_closure_set(v___x_1818_, 1, lean_box(0));
lean_closure_set(v___x_1818_, 2, v_inst_1815_);
lean_closure_set(v___x_1818_, 3, v_inst_1816_);
lean_closure_set(v___x_1818_, 4, v_inst_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1819_, lean_object* v_00_u03b2_1820_, lean_object* v_inst_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_1824_, 0, lean_box(0));
lean_closure_set(v___x_1824_, 1, lean_box(0));
lean_closure_set(v___x_1824_, 2, v_inst_1821_);
lean_closure_set(v___x_1824_, 3, v_inst_1822_);
lean_closure_set(v___x_1824_, 4, v_inst_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg(lean_object* v_f_1825_, lean_object* v_m_1826_){
_start:
{
lean_object* v_buckets_1827_; lean_object* v___x_1828_; lean_object* v___x_1829_; uint8_t v___x_1830_; 
v_buckets_1827_ = lean_ctor_get(v_m_1826_, 1);
v___x_1828_ = lean_unsigned_to_nat(0u);
v___x_1829_ = lean_array_get_size(v_buckets_1827_);
v___x_1830_ = lean_nat_dec_lt(v___x_1828_, v___x_1829_);
if (v___x_1830_ == 0)
{
lean_object* v___x_1831_; 
lean_dec_ref(v_m_1826_);
lean_dec_ref(v_f_1825_);
v___x_1831_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1831_;
}
else
{
lean_object* v___x_1832_; 
v___x_1832_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1825_, v_m_1826_);
return v___x_1832_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object* v_00_u03b1_1833_, lean_object* v_00_u03b2_1834_, lean_object* v_00_u03b3_1835_, lean_object* v_f_1836_, lean_object* v_m_1837_){
_start:
{
lean_object* v_buckets_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v_buckets_1838_ = lean_ctor_get(v_m_1837_, 1);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_array_get_size(v_buckets_1838_);
v___x_1841_ = lean_nat_dec_lt(v___x_1839_, v___x_1840_);
if (v___x_1841_ == 0)
{
lean_object* v___x_1842_; 
lean_dec_ref(v_m_1837_);
lean_dec_ref(v_f_1836_);
v___x_1842_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1842_;
}
else
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_1836_, v_m_1837_);
return v___x_1843_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object* v_f_1844_, lean_object* v_m_1845_){
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
lean_dec(v_f_1844_);
v___x_1850_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1850_;
}
else
{
lean_object* v___x_1851_; 
v___x_1851_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1844_, v_m_1845_);
return v___x_1851_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object* v_00_u03b1_1852_, lean_object* v_00_u03b2_1853_, lean_object* v_00_u03b3_1854_, lean_object* v_f_1855_, lean_object* v_m_1856_){
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
lean_dec(v_f_1855_);
v___x_1861_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1861_;
}
else
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_1855_, v_m_1856_);
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object* v_f_1863_, lean_object* v_m_1864_){
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
lean_dec_ref(v_f_1863_);
v___x_1869_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1869_;
}
else
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1863_, v_m_1864_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_f_1873_, lean_object* v_m_1874_){
_start:
{
lean_object* v_buckets_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
v_buckets_1875_ = lean_ctor_get(v_m_1874_, 1);
v___x_1876_ = lean_unsigned_to_nat(0u);
v___x_1877_ = lean_array_get_size(v_buckets_1875_);
v___x_1878_ = lean_nat_dec_lt(v___x_1876_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
lean_dec_ref(v_m_1874_);
lean_dec_ref(v_f_1873_);
v___x_1879_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
return v___x_1879_;
}
else
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1873_, v_m_1874_);
return v___x_1880_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_1881_, lean_object* v_x2_1882_, lean_object* v_x3_1883_){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v_x2_1882_);
lean_ctor_set(v___x_1884_, 1, v_x3_1883_);
v___x_1885_ = lean_array_push(v_x1_1881_, v___x_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__1(lean_object* v___x_1886_, lean_object* v___f_1887_, lean_object* v_acc_1888_, lean_object* v_l_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1886_, v___f_1887_, v_acc_1888_, v_l_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object* v_m_1895_){
_start:
{
lean_object* v_size_1896_; lean_object* v_buckets_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v_size_1896_ = lean_ctor_get(v_m_1895_, 0);
lean_inc(v_size_1896_);
v_buckets_1897_ = lean_ctor_get(v_m_1895_, 1);
lean_inc_ref(v_buckets_1897_);
lean_dec_ref(v_m_1895_);
v___x_1898_ = lean_mk_empty_array_with_capacity(v_size_1896_);
lean_dec(v_size_1896_);
v___x_1899_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = lean_array_get_size(v_buckets_1897_);
v___x_1902_ = lean_nat_dec_lt(v___x_1900_, v___x_1901_);
if (v___x_1902_ == 0)
{
lean_dec_ref(v_buckets_1897_);
return v___x_1898_;
}
else
{
lean_object* v___f_1903_; size_t v___x_1904_; size_t v___x_1905_; lean_object* v___x_1906_; 
v___f_1903_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1904_ = ((size_t)0ULL);
v___x_1905_ = lean_usize_of_nat(v___x_1901_);
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1899_, v___f_1903_, v_buckets_1897_, v___x_1904_, v___x_1905_, v___x_1898_);
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object* v_00_u03b1_1907_, lean_object* v_00_u03b2_1908_, lean_object* v_m_1909_){
_start:
{
lean_object* v_size_1910_; lean_object* v_buckets_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v_size_1910_ = lean_ctor_get(v_m_1909_, 0);
lean_inc(v_size_1910_);
v_buckets_1911_ = lean_ctor_get(v_m_1909_, 1);
lean_inc_ref(v_buckets_1911_);
lean_dec_ref(v_m_1909_);
v___x_1912_ = lean_mk_empty_array_with_capacity(v_size_1910_);
lean_dec(v_size_1910_);
v___x_1913_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1914_ = lean_unsigned_to_nat(0u);
v___x_1915_ = lean_array_get_size(v_buckets_1911_);
v___x_1916_ = lean_nat_dec_lt(v___x_1914_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_dec_ref(v_buckets_1911_);
return v___x_1912_;
}
else
{
lean_object* v___f_1917_; size_t v___x_1918_; size_t v___x_1919_; lean_object* v___x_1920_; 
v___f_1917_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__1));
v___x_1918_ = ((size_t)0ULL);
v___x_1919_ = lean_usize_of_nat(v___x_1915_);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1913_, v___f_1917_, v_buckets_1911_, v___x_1918_, v___x_1919_, v___x_1912_);
return v___x_1920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_1921_, lean_object* v_x2_1922_, lean_object* v_x3_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = lean_array_push(v_x1_1921_, v_x2_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1925_, lean_object* v_x2_1926_, lean_object* v_x3_1927_){
_start:
{
lean_object* v_res_1928_; 
v_res_1928_ = l_Std_HashMap_Raw_keysArray___redArg___lam__0(v_x1_1925_, v_x2_1926_, v_x3_1927_);
lean_dec(v_x3_1927_);
return v_res_1928_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__1(lean_object* v___x_1929_, lean_object* v___f_1930_, lean_object* v_acc_1931_, lean_object* v_l_1932_){
_start:
{
lean_object* v___x_1933_; 
v___x_1933_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1929_, v___f_1930_, v_acc_1931_, v_l_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object* v_m_1938_){
_start:
{
lean_object* v_size_1939_; lean_object* v_buckets_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v_size_1939_ = lean_ctor_get(v_m_1938_, 0);
lean_inc(v_size_1939_);
v_buckets_1940_ = lean_ctor_get(v_m_1938_, 1);
lean_inc_ref(v_buckets_1940_);
lean_dec_ref(v_m_1938_);
v___x_1941_ = lean_mk_empty_array_with_capacity(v_size_1939_);
lean_dec(v_size_1939_);
v___x_1942_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1943_ = lean_unsigned_to_nat(0u);
v___x_1944_ = lean_array_get_size(v_buckets_1940_);
v___x_1945_ = lean_nat_dec_lt(v___x_1943_, v___x_1944_);
if (v___x_1945_ == 0)
{
lean_dec_ref(v_buckets_1940_);
return v___x_1941_;
}
else
{
lean_object* v___f_1946_; size_t v___x_1947_; size_t v___x_1948_; lean_object* v___x_1949_; 
v___f_1946_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = lean_usize_of_nat(v___x_1944_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1942_, v___f_1946_, v_buckets_1940_, v___x_1947_, v___x_1948_, v___x_1941_);
return v___x_1949_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object* v_00_u03b1_1950_, lean_object* v_00_u03b2_1951_, lean_object* v_m_1952_){
_start:
{
lean_object* v_size_1953_; lean_object* v_buckets_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v_size_1953_ = lean_ctor_get(v_m_1952_, 0);
lean_inc(v_size_1953_);
v_buckets_1954_ = lean_ctor_get(v_m_1952_, 1);
lean_inc_ref(v_buckets_1954_);
lean_dec_ref(v_m_1952_);
v___x_1955_ = lean_mk_empty_array_with_capacity(v_size_1953_);
lean_dec(v_size_1953_);
v___x_1956_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_1957_ = lean_unsigned_to_nat(0u);
v___x_1958_ = lean_array_get_size(v_buckets_1954_);
v___x_1959_ = lean_nat_dec_lt(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_dec_ref(v_buckets_1954_);
return v___x_1955_;
}
else
{
lean_object* v___f_1960_; size_t v___x_1961_; size_t v___x_1962_; lean_object* v___x_1963_; 
v___f_1960_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__1));
v___x_1961_ = ((size_t)0ULL);
v___x_1962_ = lean_usize_of_nat(v___x_1958_);
v___x_1963_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1956_, v___f_1960_, v_buckets_1954_, v___x_1961_, v___x_1962_, v___x_1955_);
return v___x_1963_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object* v_a_1964_, lean_object* v_b_1965_, lean_object* v_d_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1967_, 0, v_b_1965_);
lean_ctor_set(v___x_1967_, 1, v_d_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_a_1968_, lean_object* v_b_1969_, lean_object* v_d_1970_){
_start:
{
lean_object* v_res_1971_; 
v_res_1971_ = l_Std_HashMap_Raw_values___redArg___lam__0(v_a_1968_, v_b_1969_, v_d_1970_);
lean_dec(v_a_1968_);
return v_res_1971_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object* v_m_1976_){
_start:
{
lean_object* v___x_1977_; lean_object* v_buckets_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1977_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1978_ = lean_ctor_get(v_m_1976_, 1);
lean_inc_ref(v_buckets_1978_);
lean_dec_ref(v_m_1976_);
v___x_1979_ = lean_box(0);
v___x_1980_ = lean_array_get_size(v_buckets_1978_);
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = lean_nat_dec_lt(v___x_1981_, v___x_1980_);
if (v___x_1982_ == 0)
{
lean_dec_ref(v_buckets_1978_);
return v___x_1979_;
}
else
{
lean_object* v___f_1983_; size_t v___x_1984_; size_t v___x_1985_; lean_object* v___x_1986_; 
v___f_1983_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_1984_ = lean_usize_of_nat(v___x_1980_);
v___x_1985_ = ((size_t)0ULL);
v___x_1986_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1977_, v___f_1983_, v_buckets_1978_, v___x_1984_, v___x_1985_, v___x_1979_);
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object* v_00_u03b1_1987_, lean_object* v_00_u03b2_1988_, lean_object* v_m_1989_){
_start:
{
lean_object* v___x_1990_; lean_object* v_buckets_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1990_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_1991_ = lean_ctor_get(v_m_1989_, 1);
lean_inc_ref(v_buckets_1991_);
lean_dec_ref(v_m_1989_);
v___x_1992_ = lean_box(0);
v___x_1993_ = lean_array_get_size(v_buckets_1991_);
v___x_1994_ = lean_unsigned_to_nat(0u);
v___x_1995_ = lean_nat_dec_lt(v___x_1994_, v___x_1993_);
if (v___x_1995_ == 0)
{
lean_dec_ref(v_buckets_1991_);
return v___x_1992_;
}
else
{
lean_object* v___f_1996_; size_t v___x_1997_; size_t v___x_1998_; lean_object* v___x_1999_; 
v___f_1996_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__1));
v___x_1997_ = lean_usize_of_nat(v___x_1993_);
v___x_1998_ = ((size_t)0ULL);
v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1990_, v___f_1996_, v_buckets_1991_, v___x_1997_, v___x_1998_, v___x_1992_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2000_, lean_object* v_x2_2001_, lean_object* v_x3_2002_){
_start:
{
lean_object* v___x_2003_; 
v___x_2003_ = lean_array_push(v_x1_2000_, v_x3_2002_);
return v___x_2003_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2004_, lean_object* v_x2_2005_, lean_object* v_x3_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_Std_HashMap_Raw_valuesArray___redArg___lam__0(v_x1_2004_, v_x2_2005_, v_x3_2006_);
lean_dec(v_x2_2005_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg(lean_object* v_m_2012_){
_start:
{
lean_object* v_size_2013_; lean_object* v_buckets_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v_size_2013_ = lean_ctor_get(v_m_2012_, 0);
lean_inc(v_size_2013_);
v_buckets_2014_ = lean_ctor_get(v_m_2012_, 1);
lean_inc_ref(v_buckets_2014_);
lean_dec_ref(v_m_2012_);
v___x_2015_ = lean_mk_empty_array_with_capacity(v_size_2013_);
lean_dec(v_size_2013_);
v___x_2016_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = lean_array_get_size(v_buckets_2014_);
v___x_2019_ = lean_nat_dec_lt(v___x_2017_, v___x_2018_);
if (v___x_2019_ == 0)
{
lean_dec_ref(v_buckets_2014_);
return v___x_2015_;
}
else
{
lean_object* v___f_2020_; size_t v___x_2021_; size_t v___x_2022_; lean_object* v___x_2023_; 
v___f_2020_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2021_ = ((size_t)0ULL);
v___x_2022_ = lean_usize_of_nat(v___x_2018_);
v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2016_, v___f_2020_, v_buckets_2014_, v___x_2021_, v___x_2022_, v___x_2015_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray(lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_m_2026_){
_start:
{
lean_object* v_size_2027_; lean_object* v_buckets_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; uint8_t v___x_2033_; 
v_size_2027_ = lean_ctor_get(v_m_2026_, 0);
lean_inc(v_size_2027_);
v_buckets_2028_ = lean_ctor_get(v_m_2026_, 1);
lean_inc_ref(v_buckets_2028_);
lean_dec_ref(v_m_2026_);
v___x_2029_ = lean_mk_empty_array_with_capacity(v_size_2027_);
lean_dec(v_size_2027_);
v___x_2030_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v___x_2031_ = lean_unsigned_to_nat(0u);
v___x_2032_ = lean_array_get_size(v_buckets_2028_);
v___x_2033_ = lean_nat_dec_lt(v___x_2031_, v___x_2032_);
if (v___x_2033_ == 0)
{
lean_dec_ref(v_buckets_2028_);
return v___x_2029_;
}
else
{
lean_object* v___f_2034_; size_t v___x_2035_; size_t v___x_2036_; lean_object* v___x_2037_; 
v___f_2034_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__1));
v___x_2035_ = ((size_t)0ULL);
v___x_2036_ = lean_usize_of_nat(v___x_2032_);
v___x_2037_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2030_, v___f_2034_, v_buckets_2028_, v___x_2035_, v___x_2036_, v___x_2029_);
return v___x_2037_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany___redArg(lean_object* v_inst_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_m_2041_, lean_object* v_l_2042_){
_start:
{
lean_object* v_buckets_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v_buckets_2043_ = lean_ctor_get(v_m_2041_, 1);
v___x_2044_ = lean_unsigned_to_nat(0u);
v___x_2045_ = lean_array_get_size(v_buckets_2043_);
v___x_2046_ = lean_nat_dec_lt(v___x_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_dec(v_l_2042_);
lean_dec(v_inst_2040_);
lean_dec_ref(v_inst_2039_);
lean_dec_ref(v_inst_2038_);
return v_m_2041_;
}
else
{
lean_object* v___x_2047_; 
v___x_2047_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2040_, v_inst_2038_, v_inst_2039_, v_m_2041_, v_l_2042_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany(lean_object* v_00_u03b1_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_00_u03c1_2052_, lean_object* v_inst_2053_, lean_object* v_m_2054_, lean_object* v_l_2055_){
_start:
{
lean_object* v_buckets_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; 
v_buckets_2056_ = lean_ctor_get(v_m_2054_, 1);
v___x_2057_ = lean_unsigned_to_nat(0u);
v___x_2058_ = lean_array_get_size(v_buckets_2056_);
v___x_2059_ = lean_nat_dec_lt(v___x_2057_, v___x_2058_);
if (v___x_2059_ == 0)
{
lean_dec(v_l_2055_);
lean_dec(v_inst_2053_);
lean_dec_ref(v_inst_2051_);
lean_dec_ref(v_inst_2050_);
return v_m_2054_;
}
else
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2053_, v_inst_2050_, v_inst_2051_, v_m_2054_, v_l_2055_);
return v___x_2060_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_inst_2063_, lean_object* v_m_2064_, lean_object* v_l_2065_){
_start:
{
lean_object* v_buckets_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_buckets_2066_ = lean_ctor_get(v_m_2064_, 1);
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = lean_array_get_size(v_buckets_2066_);
v___x_2069_ = lean_nat_dec_lt(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_dec(v_l_2065_);
lean_dec(v_inst_2063_);
lean_dec_ref(v_inst_2062_);
lean_dec_ref(v_inst_2061_);
return v_m_2064_;
}
else
{
lean_object* v___x_2070_; 
v___x_2070_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2063_, v_inst_2061_, v_inst_2062_, v_m_2064_, v_l_2065_);
return v___x_2070_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2071_, lean_object* v_inst_2072_, lean_object* v_inst_2073_, lean_object* v_00_u03c1_2074_, lean_object* v_inst_2075_, lean_object* v_m_2076_, lean_object* v_l_2077_){
_start:
{
lean_object* v_buckets_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; uint8_t v___x_2081_; 
v_buckets_2078_ = lean_ctor_get(v_m_2076_, 1);
v___x_2079_ = lean_unsigned_to_nat(0u);
v___x_2080_ = lean_array_get_size(v_buckets_2078_);
v___x_2081_ = lean_nat_dec_lt(v___x_2079_, v___x_2080_);
if (v___x_2081_ == 0)
{
lean_dec(v_l_2077_);
lean_dec(v_inst_2075_);
lean_dec_ref(v_inst_2073_);
lean_dec_ref(v_inst_2072_);
return v_m_2076_;
}
else
{
lean_object* v___x_2082_; 
v___x_2082_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2075_, v_inst_2072_, v_inst_2073_, v_m_2076_, v_l_2077_);
return v___x_2082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray___redArg(lean_object* v_inst_2083_, lean_object* v_inst_2084_, lean_object* v_l_2085_){
_start:
{
lean_object* v___x_2086_; uint8_t v___x_2087_; 
v___x_2086_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_2087_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2087_ == 0)
{
lean_dec_ref(v_l_2085_);
lean_dec_ref(v_inst_2084_);
lean_dec_ref(v_inst_2083_);
return v___x_2086_;
}
else
{
lean_object* v___f_2088_; lean_object* v___x_2089_; 
v___f_2088_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2089_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2088_, v_inst_2083_, v_inst_2084_, v___x_2086_, v_l_2085_);
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray(lean_object* v_00_u03b1_2090_, lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_l_2093_){
_start:
{
lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2094_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_2095_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2095_ == 0)
{
lean_dec_ref(v_l_2093_);
lean_dec_ref(v_inst_2092_);
lean_dec_ref(v_inst_2091_);
return v___x_2094_;
}
else
{
lean_object* v___f_2096_; lean_object* v___x_2097_; 
v___f_2096_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2097_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2096_, v_inst_2091_, v_inst_2092_, v___x_2094_, v_l_2093_);
return v___x_2097_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2098_){
_start:
{
lean_object* v___x_2099_; 
v___x_2099_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2098_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Std_HashMap_Raw_Internal_numBuckets___redArg(v_m_2100_);
lean_dec_ref(v_m_2100_);
return v_res_2101_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2102_, lean_object* v_00_u03b2_2103_, lean_object* v_m_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2106_, lean_object* v_00_u03b2_2107_, lean_object* v_m_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Std_HashMap_Raw_Internal_numBuckets(v_00_u03b1_2106_, v_00_u03b2_2107_, v_m_2108_);
lean_dec_ref(v_m_2108_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2(lean_object* v___x_2113_, lean_object* v___f_2114_, lean_object* v_m_2115_, lean_object* v_prec_2116_){
_start:
{
lean_object* v___x_2117_; lean_object* v_buckets_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2138_; 
v___x_2117_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__9));
v_buckets_2118_ = lean_ctor_get(v_m_2115_, 1);
v_isSharedCheck_2138_ = !lean_is_exclusive(v_m_2115_);
if (v_isSharedCheck_2138_ == 0)
{
lean_object* v_unused_2139_; 
v_unused_2139_ = lean_ctor_get(v_m_2115_, 0);
lean_dec(v_unused_2139_);
v___x_2120_ = v_m_2115_;
v_isShared_2121_ = v_isSharedCheck_2138_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_buckets_2118_);
lean_dec(v_m_2115_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2138_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___y_2124_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; uint8_t v___x_2133_; 
v___x_2122_ = ((lean_object*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___closed__1));
v___x_2130_ = lean_box(0);
v___x_2131_ = lean_array_get_size(v_buckets_2118_);
v___x_2132_ = lean_unsigned_to_nat(0u);
v___x_2133_ = lean_nat_dec_lt(v___x_2132_, v___x_2131_);
if (v___x_2133_ == 0)
{
lean_dec_ref(v_buckets_2118_);
lean_dec_ref(v___f_2114_);
v___y_2124_ = v___x_2130_;
goto v___jp_2123_;
}
else
{
lean_object* v___f_2134_; size_t v___x_2135_; size_t v___x_2136_; lean_object* v___x_2137_; 
v___f_2134_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2134_, 0, v___x_2117_);
lean_closure_set(v___f_2134_, 1, v___f_2114_);
v___x_2135_ = lean_usize_of_nat(v___x_2131_);
v___x_2136_ = ((size_t)0ULL);
v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2117_, v___f_2134_, v_buckets_2118_, v___x_2135_, v___x_2136_, v___x_2130_);
v___y_2124_ = v___x_2137_;
goto v___jp_2123_;
}
v___jp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2127_; 
v___x_2125_ = l_List_repr___redArg(v___x_2113_, v___y_2124_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set_tag(v___x_2120_, 5);
lean_ctor_set(v___x_2120_, 1, v___x_2125_);
lean_ctor_set(v___x_2120_, 0, v___x_2122_);
v___x_2127_ = v___x_2120_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2129_, 1, v___x_2125_);
v___x_2127_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
lean_object* v___x_2128_; 
v___x_2128_ = l_Repr_addAppParen(v___x_2127_, v_prec_2116_);
return v___x_2128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed(lean_object* v___x_2140_, lean_object* v___f_2141_, lean_object* v_m_2142_, lean_object* v_prec_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Std_HashMap_Raw_instRepr___redArg___lam__2(v___x_2140_, v___f_2141_, v_m_2142_, v_prec_2143_);
lean_dec(v_prec_2143_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object* v_inst_2145_, lean_object* v_inst_2146_){
_start:
{
lean_object* v___f_2147_; lean_object* v___f_2148_; lean_object* v___x_2149_; lean_object* v___f_2150_; 
v___f_2147_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__0));
v___f_2148_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2148_, 0, v_inst_2146_);
v___x_2149_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2149_, 0, lean_box(0));
lean_closure_set(v___x_2149_, 1, lean_box(0));
lean_closure_set(v___x_2149_, 2, v_inst_2145_);
lean_closure_set(v___x_2149_, 3, v___f_2148_);
v___f_2150_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2150_, 0, v___x_2149_);
lean_closure_set(v___f_2150_, 1, v___f_2147_);
return v___f_2150_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object* v_00_u03b1_2151_, lean_object* v_00_u03b2_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_){
_start:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Std_HashMap_Raw_instRepr___redArg(v_inst_2153_, v_inst_2154_);
return v___x_2155_;
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
