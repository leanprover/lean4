// Lean compiler output
// Module: Std.Data.HashMap.Basic
// Imports: public import Std.Data.DHashMap.Basic public import Init.Data.List.Impl
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_foldrTR___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashMap_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_HashMap_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_instEmptyCollection___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashMap_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__0 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_HashMap_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HashMap"};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__1 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_HashMap_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__2 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__2_value;
static const lean_ctor_object l_Std_HashMap_term___x7em___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashMap_term___x7em___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_term___x7em___00__closed__3_value_aux_0),((lean_object*)&l_Std_HashMap_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 156, 61, 172, 252, 129, 143, 98)}};
static const lean_ctor_object l_Std_HashMap_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap_term___x7em___00__closed__3_value_aux_1),((lean_object*)&l_Std_HashMap_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(204, 68, 21, 240, 2, 29, 47, 144)}};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__3 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__3_value;
static const lean_string_object l_Std_HashMap_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__4 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__4_value;
static const lean_ctor_object l_Std_HashMap_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_term___x7em___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__5 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__5_value;
static const lean_string_object l_Std_HashMap_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__6 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__6_value;
static const lean_ctor_object l_Std_HashMap_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_HashMap_term___x7em___00__closed__6_value)}};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__7 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__7_value;
static const lean_string_object l_Std_HashMap_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__8 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__8_value;
static const lean_ctor_object l_Std_HashMap_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_term___x7em___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__9 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_HashMap_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_HashMap_term___x7em___00__closed__9_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__10 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_HashMap_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_HashMap_term___x7em___00__closed__5_value),((lean_object*)&l_Std_HashMap_term___x7em___00__closed__7_value),((lean_object*)&l_Std_HashMap_term___x7em___00__closed__10_value)}};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__11 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_HashMap_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_HashMap_term___x7em___00__closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Std_HashMap_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_HashMap_term___x7em___00__closed__12 = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__12_value;
LEAN_EXPORT const lean_object* l_Std_HashMap_term___x7em__ = (const lean_object*)&l_Std_HashMap_term___x7em___00__closed__12_value;
static const lean_string_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__0 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__1 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__1_value;
static const lean_string_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__2 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__3 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__3_value;
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_0),((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_1),((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value_aux_2),((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4_value;
static const lean_string_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5_value;
static lean_once_cell_t l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6;
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value_aux_0),((lean_object*)&l_Std_HashMap_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(34, 156, 61, 172, 252, 129, 143, 98)}};
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value_aux_1),((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(13, 233, 238, 90, 128, 88, 233, 155)}};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__9 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__8_value)}};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__10 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__10_value;
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__11 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__11_value;
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__9_value),((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__11_value)}};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12_value;
static const lean_string_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__13 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__13_value;
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14_value;
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__0 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1 = (const lean_object*)&l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_size(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__1_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__2 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__2_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__3 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__3_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__4 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__4_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__5 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__5_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__6 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__6_value;
static const lean_ctor_object l_Std_HashMap_keys___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__0_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__1_value)}};
static const lean_object* l_Std_HashMap_keys___redArg___closed__7 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__7_value;
static const lean_ctor_object l_Std_HashMap_keys___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__7_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__2_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__3_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__4_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__5_value)}};
static const lean_object* l_Std_HashMap_keys___redArg___closed__8 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__8_value;
static const lean_ctor_object l_Std_HashMap_keys___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__8_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__6_value)}};
static const lean_object* l_Std_HashMap_keys___redArg___closed__9 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__10 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__10_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_keys___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__10_value)} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__11 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__11_value;
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value)} };
static const lean_object* l_Std_HashMap_ofList___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_ofList___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value)} };
static const lean_object* l_Std_HashMap_ofArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_ofArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_ofArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_ofArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_ofArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_ofArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_toList___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_toList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_toList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_toList___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_toList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_toList___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_toList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_toArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_toArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_toArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_toArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_toArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_toArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_toArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_keysArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_keysArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_keysArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_keysArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_keysArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_keysArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_HashMap_all___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap_all___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_all___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_HashMap_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__2, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value)} };
static const lean_object* l_Std_HashMap_union___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instInter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instInter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashMap_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashMap_partition___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_partition___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_values___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_values___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_values___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_keys___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_values___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_values___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_values___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_values(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_values___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_valuesArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_valuesArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_keysArray___redArg___lam__1, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_valuesArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_valuesArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_valuesArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashMap_instRepr___redArg___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Std_HashMap_instRepr___redArg___lam__2___closed__0 = (const lean_object*)&l_Std_HashMap_instRepr___redArg___lam__2___closed__0_value;
static const lean_ctor_object l_Std_HashMap_instRepr___redArg___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_HashMap_instRepr___redArg___lam__2___closed__0_value)}};
static const lean_object* l_Std_HashMap_instRepr___redArg___lam__2___closed__1 = (const lean_object*)&l_Std_HashMap_instRepr___redArg___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_groupByKey___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_groupByKey___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_groupByKey___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_groupByKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_groupByKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_HashMap_emptyWithCapacity___redArg(v_capacity_11_);
lean_dec(v_capacity_11_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_inst_15_, lean_object* v_inst_16_, lean_object* v_capacity_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_18_ = lean_unsigned_to_nat(0u);
v___x_19_ = lean_unsigned_to_nat(4u);
v___x_20_ = lean_nat_mul(v_capacity_17_, v___x_19_);
v___x_21_ = lean_unsigned_to_nat(3u);
v___x_22_ = lean_nat_div(v___x_20_, v___x_21_);
lean_dec(v___x_20_);
v___x_23_ = l_Nat_nextPowerOfTwo(v___x_22_);
lean_dec(v___x_22_);
v___x_24_ = lean_box(0);
v___x_25_ = lean_mk_array(v___x_23_, v___x_24_);
v___x_26_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_26_, 0, v___x_18_);
lean_ctor_set(v___x_26_, 1, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity___boxed(lean_object* v_00_u03b1_27_, lean_object* v_00_u03b2_28_, lean_object* v_inst_29_, lean_object* v_inst_30_, lean_object* v_capacity_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_HashMap_emptyWithCapacity(v_00_u03b1_27_, v_00_u03b2_28_, v_inst_29_, v_inst_30_, v_capacity_31_);
lean_dec(v_capacity_31_);
lean_dec_ref(v_inst_30_);
lean_dec_ref(v_inst_29_);
return v_res_32_;
}
}
static lean_object* _init_l_Std_HashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_box(0);
v___x_34_ = lean_unsigned_to_nat(16u);
v___x_35_ = lean_mk_array(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l_Std_HashMap_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__0, &l_Std_HashMap_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_instEmptyCollection___closed__0);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection(lean_object* v_00_u03b1_39_, lean_object* v_00_u03b2_40_, lean_object* v_inst_41_, lean_object* v_inst_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l_Std_HashMap_instEmptyCollection(v_00_u03b1_44_, v_00_u03b2_45_, v_inst_46_, v_inst_47_);
lean_dec_ref(v_inst_47_);
lean_dec_ref(v_inst_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_inst_51_, lean_object* v_inst_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited___boxed(lean_object* v_00_u03b1_54_, lean_object* v_00_u03b2_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_HashMap_instInhabited(v_00_u03b1_54_, v_00_u03b2_55_, v_inst_56_, v_inst_57_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_56_);
return v_res_58_;
}
}
static lean_object* _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5));
v___x_98_ = l_String_toRawSubstring_x27(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(lean_object* v_x_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
lean_inc(v_x_119_);
v___x_123_ = l_Lean_Syntax_isOfKind(v_x_119_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec_ref(v_a_120_);
lean_dec(v_x_119_);
v___x_124_ = lean_box(1);
v___x_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_a_121_);
return v___x_125_;
}
else
{
lean_object* v_quotContext_126_; lean_object* v_currMacroScope_127_; lean_object* v_ref_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_quotContext_126_ = lean_ctor_get(v_a_120_, 1);
lean_inc(v_quotContext_126_);
v_currMacroScope_127_ = lean_ctor_get(v_a_120_, 2);
lean_inc(v_currMacroScope_127_);
v_ref_128_ = lean_ctor_get(v_a_120_, 5);
lean_inc(v_ref_128_);
lean_dec_ref(v_a_120_);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = l_Lean_Syntax_getArg(v_x_119_, v___x_129_);
v___x_131_ = lean_unsigned_to_nat(2u);
v___x_132_ = l_Lean_Syntax_getArg(v_x_119_, v___x_131_);
lean_dec(v_x_119_);
v___x_133_ = 0;
v___x_134_ = l_Lean_SourceInfo_fromRef(v_ref_128_, v___x_133_);
lean_dec(v_ref_128_);
v___x_135_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
v___x_136_ = lean_obj_once(&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6, &l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6_once, _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6);
v___x_137_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7));
v___x_138_ = l_Lean_addMacroScope(v_quotContext_126_, v___x_137_, v_currMacroScope_127_);
v___x_139_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12));
lean_inc(v___x_134_);
v___x_140_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_140_, 0, v___x_134_);
lean_ctor_set(v___x_140_, 1, v___x_136_);
lean_ctor_set(v___x_140_, 2, v___x_138_);
lean_ctor_set(v___x_140_, 3, v___x_139_);
v___x_141_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14));
lean_inc(v___x_134_);
v___x_142_ = l_Lean_Syntax_node2(v___x_134_, v___x_141_, v___x_130_, v___x_132_);
v___x_143_ = l_Lean_Syntax_node2(v___x_134_, v___x_135_, v___x_140_, v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_a_121_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(lean_object* v_x_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
lean_inc(v_x_148_);
v___x_152_ = l_Lean_Syntax_isOfKind(v_x_148_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; lean_object* v___x_154_; 
lean_dec(v_x_148_);
v___x_153_ = lean_box(0);
v___x_154_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v_a_150_);
return v___x_154_;
}
else
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = l_Lean_Syntax_getArg(v_x_148_, v___x_155_);
v___x_157_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1));
lean_inc(v___x_156_);
v___x_158_ = l_Lean_Syntax_isOfKind(v___x_156_, v___x_157_);
if (v___x_158_ == 0)
{
lean_object* v___x_159_; lean_object* v___x_160_; 
lean_dec(v___x_156_);
lean_dec(v_x_148_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
lean_ctor_set(v___x_160_, 1, v_a_150_);
return v___x_160_;
}
else
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; uint8_t v___x_164_; 
v___x_161_ = lean_unsigned_to_nat(1u);
v___x_162_ = l_Lean_Syntax_getArg(v_x_148_, v___x_161_);
lean_dec(v_x_148_);
v___x_163_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_162_);
v___x_164_ = l_Lean_Syntax_matchesNull(v___x_162_, v___x_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec(v___x_162_);
lean_dec(v___x_156_);
v___x_165_ = lean_box(0);
v___x_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v_a_150_);
return v___x_166_;
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_ref_169_; uint8_t v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_167_ = l_Lean_Syntax_getArg(v___x_162_, v___x_155_);
v___x_168_ = l_Lean_Syntax_getArg(v___x_162_, v___x_161_);
lean_dec(v___x_162_);
v_ref_169_ = l_Lean_replaceRef(v___x_156_, v_a_149_);
lean_dec(v___x_156_);
v___x_170_ = 0;
v___x_171_ = l_Lean_SourceInfo_fromRef(v_ref_169_, v___x_170_);
lean_dec(v_ref_169_);
v___x_172_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
v___x_173_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__6));
lean_inc(v___x_171_);
v___x_174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_171_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = l_Lean_Syntax_node3(v___x_171_, v___x_172_, v___x_167_, v___x_174_, v___x_168_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_a_150_);
return v___x_176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___boxed(lean_object* v_x_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(v_x_177_, v_a_178_, v_a_179_);
lean_dec(v_a_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___redArg(lean_object* v_x_181_, lean_object* v_x_182_, lean_object* v_m_183_, lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_181_, v_x_182_, v_m_183_, v_a_184_, v_b_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert(lean_object* v_00_u03b1_187_, lean_object* v_00_u03b2_188_, lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_m_191_, lean_object* v_a_192_, lean_object* v_b_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_189_, v_x_190_, v_m_191_, v_a_192_, v_b_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg___lam__0(lean_object* v_x_195_, lean_object* v_x_196_, lean_object* v_x_197_){
_start:
{
lean_object* v_fst_198_; lean_object* v_snd_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_fst_198_ = lean_ctor_get(v_x_197_, 0);
lean_inc(v_fst_198_);
v_snd_199_ = lean_ctor_get(v_x_197_, 1);
lean_inc(v_snd_199_);
lean_dec_ref(v_x_197_);
v___x_200_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_201_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_195_, v_x_196_, v___x_200_, v_fst_198_, v_snd_199_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg(lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
lean_object* v___f_204_; 
v___f_204_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_204_, 0, v_x_202_);
lean_closure_set(v___f_204_, 1, v_x_203_);
return v___f_204_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd(lean_object* v_00_u03b1_205_, lean_object* v_00_u03b2_206_, lean_object* v_x_207_, lean_object* v_x_208_){
_start:
{
lean_object* v___f_209_; 
v___f_209_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_209_, 0, v_x_207_);
lean_closure_set(v___f_209_, 1, v_x_208_);
return v___f_209_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg___lam__0(lean_object* v_x_210_, lean_object* v_x_211_, lean_object* v_x_212_, lean_object* v_s_213_){
_start:
{
lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_216_; 
v_fst_214_ = lean_ctor_get(v_x_212_, 0);
lean_inc(v_fst_214_);
v_snd_215_ = lean_ctor_get(v_x_212_, 1);
lean_inc(v_snd_215_);
lean_dec_ref(v_x_212_);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_210_, v_x_211_, v_s_213_, v_fst_214_, v_snd_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg(lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
lean_object* v___f_219_; 
v___f_219_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_219_, 0, v_x_217_);
lean_closure_set(v___f_219_, 1, v_x_218_);
return v___f_219_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd(lean_object* v_00_u03b1_220_, lean_object* v_00_u03b2_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
lean_object* v___f_224_; 
v___f_224_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_224_, 0, v_x_222_);
lean_closure_set(v___f_224_, 1, v_x_223_);
return v___f_224_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew___redArg(lean_object* v_x_225_, lean_object* v_x_226_, lean_object* v_m_227_, lean_object* v_a_228_, lean_object* v_b_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_225_, v_x_226_, v_m_227_, v_a_228_, v_b_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew(lean_object* v_00_u03b1_231_, lean_object* v_00_u03b2_232_, lean_object* v_x_233_, lean_object* v_x_234_, lean_object* v_m_235_, lean_object* v_a_236_, lean_object* v_b_237_){
_start:
{
lean_object* v___x_238_; 
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_233_, v_x_234_, v_m_235_, v_a_236_, v_b_237_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert___redArg(lean_object* v_x_239_, lean_object* v_x_240_, lean_object* v_m_241_, lean_object* v_a_242_, lean_object* v_b_243_){
_start:
{
lean_object* v_size_244_; lean_object* v_buckets_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_296_; 
v_size_244_ = lean_ctor_get(v_m_241_, 0);
v_buckets_245_ = lean_ctor_get(v_m_241_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_m_241_);
if (v_isSharedCheck_296_ == 0)
{
v___x_247_ = v_m_241_;
v_isShared_248_ = v_isSharedCheck_296_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_buckets_245_);
lean_inc(v_size_244_);
lean_dec(v_m_241_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_296_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_249_; lean_object* v___x_250_; uint64_t v___x_251_; uint64_t v___x_252_; uint64_t v___x_253_; uint64_t v___x_254_; uint64_t v_fold_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; size_t v___x_259_; size_t v___x_260_; size_t v___x_261_; size_t v___x_262_; size_t v___x_263_; lean_object* v_bkt_264_; uint8_t v___x_265_; 
v___x_249_ = lean_array_get_size(v_buckets_245_);
lean_inc_ref(v_x_240_);
lean_inc(v_a_242_);
v___x_250_ = lean_apply_1(v_x_240_, v_a_242_);
v___x_251_ = 32ULL;
v___x_252_ = lean_unbox_uint64(v___x_250_);
v___x_253_ = lean_uint64_shift_right(v___x_252_, v___x_251_);
v___x_254_ = lean_unbox_uint64(v___x_250_);
lean_dec_ref(v___x_250_);
v_fold_255_ = lean_uint64_xor(v___x_254_, v___x_253_);
v___x_256_ = 16ULL;
v___x_257_ = lean_uint64_shift_right(v_fold_255_, v___x_256_);
v___x_258_ = lean_uint64_xor(v_fold_255_, v___x_257_);
v___x_259_ = lean_uint64_to_usize(v___x_258_);
v___x_260_ = lean_usize_of_nat(v___x_249_);
v___x_261_ = ((size_t)1ULL);
v___x_262_ = lean_usize_sub(v___x_260_, v___x_261_);
v___x_263_ = lean_usize_land(v___x_259_, v___x_262_);
v_bkt_264_ = lean_array_uget_borrowed(v_buckets_245_, v___x_263_);
lean_inc(v_bkt_264_);
lean_inc(v_a_242_);
lean_inc_ref(v_x_239_);
v___x_265_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_239_, v_a_242_, v_bkt_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_266_; lean_object* v_size_x27_267_; lean_object* v___x_268_; lean_object* v_buckets_x27_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
lean_dec_ref(v_x_239_);
v___x_266_ = lean_unsigned_to_nat(1u);
v_size_x27_267_ = lean_nat_add(v_size_244_, v___x_266_);
lean_dec(v_size_244_);
lean_inc(v_bkt_264_);
v___x_268_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_268_, 0, v_a_242_);
lean_ctor_set(v___x_268_, 1, v_b_243_);
lean_ctor_set(v___x_268_, 2, v_bkt_264_);
v_buckets_x27_269_ = lean_array_uset(v_buckets_245_, v___x_263_, v___x_268_);
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
v_val_276_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_240_, v_buckets_x27_269_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_val_276_);
lean_ctor_set(v___x_247_, 0, v_size_x27_267_);
v___x_278_ = v___x_247_;
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
v___x_279_ = lean_box(v___x_265_);
v___x_280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
return v___x_280_;
}
}
else
{
lean_object* v___x_283_; 
lean_dec_ref(v_x_240_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v_buckets_x27_269_);
lean_ctor_set(v___x_247_, 0, v_size_x27_267_);
v___x_283_ = v___x_247_;
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
v___x_284_ = lean_box(v___x_265_);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
return v___x_285_;
}
}
}
else
{
lean_object* v___x_287_; lean_object* v_buckets_x27_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_292_; 
lean_inc(v_bkt_264_);
lean_dec_ref(v_x_240_);
v___x_287_ = lean_box(0);
v_buckets_x27_288_ = lean_array_uset(v_buckets_245_, v___x_263_, v___x_287_);
v___x_289_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_239_, v_a_242_, v_b_243_, v_bkt_264_);
v___x_290_ = lean_array_uset(v_buckets_x27_288_, v___x_263_, v___x_289_);
if (v_isShared_248_ == 0)
{
lean_ctor_set(v___x_247_, 1, v___x_290_);
v___x_292_ = v___x_247_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_size_244_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v___x_290_);
v___x_292_ = v_reuseFailAlloc_295_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_293_ = lean_box(v___x_265_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
lean_ctor_set(v___x_294_, 1, v___x_292_);
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert(lean_object* v_00_u03b1_297_, lean_object* v_00_u03b2_298_, lean_object* v_x_299_, lean_object* v_x_300_, lean_object* v_m_301_, lean_object* v_a_302_, lean_object* v_b_303_){
_start:
{
lean_object* v_size_304_; lean_object* v_buckets_305_; lean_object* v___x_307_; uint8_t v_isShared_308_; uint8_t v_isSharedCheck_356_; 
v_size_304_ = lean_ctor_get(v_m_301_, 0);
v_buckets_305_ = lean_ctor_get(v_m_301_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v_m_301_);
if (v_isSharedCheck_356_ == 0)
{
v___x_307_ = v_m_301_;
v_isShared_308_ = v_isSharedCheck_356_;
goto v_resetjp_306_;
}
else
{
lean_inc(v_buckets_305_);
lean_inc(v_size_304_);
lean_dec(v_m_301_);
v___x_307_ = lean_box(0);
v_isShared_308_ = v_isSharedCheck_356_;
goto v_resetjp_306_;
}
v_resetjp_306_:
{
lean_object* v___x_309_; lean_object* v___x_310_; uint64_t v___x_311_; uint64_t v___x_312_; uint64_t v___x_313_; uint64_t v___x_314_; uint64_t v_fold_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; size_t v___x_319_; size_t v___x_320_; size_t v___x_321_; size_t v___x_322_; size_t v___x_323_; lean_object* v_bkt_324_; uint8_t v___x_325_; 
v___x_309_ = lean_array_get_size(v_buckets_305_);
lean_inc_ref(v_x_300_);
lean_inc(v_a_302_);
v___x_310_ = lean_apply_1(v_x_300_, v_a_302_);
v___x_311_ = 32ULL;
v___x_312_ = lean_unbox_uint64(v___x_310_);
v___x_313_ = lean_uint64_shift_right(v___x_312_, v___x_311_);
v___x_314_ = lean_unbox_uint64(v___x_310_);
lean_dec_ref(v___x_310_);
v_fold_315_ = lean_uint64_xor(v___x_314_, v___x_313_);
v___x_316_ = 16ULL;
v___x_317_ = lean_uint64_shift_right(v_fold_315_, v___x_316_);
v___x_318_ = lean_uint64_xor(v_fold_315_, v___x_317_);
v___x_319_ = lean_uint64_to_usize(v___x_318_);
v___x_320_ = lean_usize_of_nat(v___x_309_);
v___x_321_ = ((size_t)1ULL);
v___x_322_ = lean_usize_sub(v___x_320_, v___x_321_);
v___x_323_ = lean_usize_land(v___x_319_, v___x_322_);
v_bkt_324_ = lean_array_uget_borrowed(v_buckets_305_, v___x_323_);
lean_inc(v_bkt_324_);
lean_inc(v_a_302_);
lean_inc_ref(v_x_299_);
v___x_325_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_299_, v_a_302_, v_bkt_324_);
if (v___x_325_ == 0)
{
lean_object* v___x_326_; lean_object* v_size_x27_327_; lean_object* v___x_328_; lean_object* v_buckets_x27_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
lean_dec_ref(v_x_299_);
v___x_326_ = lean_unsigned_to_nat(1u);
v_size_x27_327_ = lean_nat_add(v_size_304_, v___x_326_);
lean_dec(v_size_304_);
lean_inc(v_bkt_324_);
v___x_328_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_328_, 0, v_a_302_);
lean_ctor_set(v___x_328_, 1, v_b_303_);
lean_ctor_set(v___x_328_, 2, v_bkt_324_);
v_buckets_x27_329_ = lean_array_uset(v_buckets_305_, v___x_323_, v___x_328_);
v___x_330_ = lean_unsigned_to_nat(4u);
v___x_331_ = lean_nat_mul(v_size_x27_327_, v___x_330_);
v___x_332_ = lean_unsigned_to_nat(3u);
v___x_333_ = lean_nat_div(v___x_331_, v___x_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_array_get_size(v_buckets_x27_329_);
v___x_335_ = lean_nat_dec_le(v___x_333_, v___x_334_);
lean_dec(v___x_333_);
if (v___x_335_ == 0)
{
lean_object* v_val_336_; lean_object* v___x_338_; 
v_val_336_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_300_, v_buckets_x27_329_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v_val_336_);
lean_ctor_set(v___x_307_, 0, v_size_x27_327_);
v___x_338_ = v___x_307_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_size_x27_327_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v_val_336_);
v___x_338_ = v_reuseFailAlloc_341_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_box(v___x_325_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
return v___x_340_;
}
}
else
{
lean_object* v___x_343_; 
lean_dec_ref(v_x_300_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v_buckets_x27_329_);
lean_ctor_set(v___x_307_, 0, v_size_x27_327_);
v___x_343_ = v___x_307_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_346_; 
v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_346_, 0, v_size_x27_327_);
lean_ctor_set(v_reuseFailAlloc_346_, 1, v_buckets_x27_329_);
v___x_343_ = v_reuseFailAlloc_346_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_344_ = lean_box(v___x_325_);
v___x_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_344_);
lean_ctor_set(v___x_345_, 1, v___x_343_);
return v___x_345_;
}
}
}
else
{
lean_object* v___x_347_; lean_object* v_buckets_x27_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_352_; 
lean_inc(v_bkt_324_);
lean_dec_ref(v_x_300_);
v___x_347_ = lean_box(0);
v_buckets_x27_348_ = lean_array_uset(v_buckets_305_, v___x_323_, v___x_347_);
v___x_349_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_299_, v_a_302_, v_b_303_, v_bkt_324_);
v___x_350_ = lean_array_uset(v_buckets_x27_348_, v___x_323_, v___x_349_);
if (v_isShared_308_ == 0)
{
lean_ctor_set(v___x_307_, 1, v___x_350_);
v___x_352_ = v___x_307_;
goto v_reusejp_351_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_size_304_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_350_);
v___x_352_ = v_reuseFailAlloc_355_;
goto v_reusejp_351_;
}
v_reusejp_351_:
{
lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_353_ = lean_box(v___x_325_);
v___x_354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set(v___x_354_, 1, v___x_352_);
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew___redArg(lean_object* v_x_357_, lean_object* v_x_358_, lean_object* v_m_359_, lean_object* v_a_360_, lean_object* v_b_361_){
_start:
{
lean_object* v_size_362_; lean_object* v_buckets_363_; lean_object* v___x_364_; lean_object* v___x_365_; uint64_t v___x_366_; uint64_t v___x_367_; uint64_t v___x_368_; uint64_t v___x_369_; uint64_t v_fold_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; size_t v___x_374_; size_t v___x_375_; size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; lean_object* v_bkt_379_; uint8_t v___x_380_; 
v_size_362_ = lean_ctor_get(v_m_359_, 0);
v_buckets_363_ = lean_ctor_get(v_m_359_, 1);
v___x_364_ = lean_array_get_size(v_buckets_363_);
lean_inc_ref(v_x_358_);
lean_inc(v_a_360_);
v___x_365_ = lean_apply_1(v_x_358_, v_a_360_);
v___x_366_ = 32ULL;
v___x_367_ = lean_unbox_uint64(v___x_365_);
v___x_368_ = lean_uint64_shift_right(v___x_367_, v___x_366_);
v___x_369_ = lean_unbox_uint64(v___x_365_);
lean_dec_ref(v___x_365_);
v_fold_370_ = lean_uint64_xor(v___x_369_, v___x_368_);
v___x_371_ = 16ULL;
v___x_372_ = lean_uint64_shift_right(v_fold_370_, v___x_371_);
v___x_373_ = lean_uint64_xor(v_fold_370_, v___x_372_);
v___x_374_ = lean_uint64_to_usize(v___x_373_);
v___x_375_ = lean_usize_of_nat(v___x_364_);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_sub(v___x_375_, v___x_376_);
v___x_378_ = lean_usize_land(v___x_374_, v___x_377_);
v_bkt_379_ = lean_array_uget_borrowed(v_buckets_363_, v___x_378_);
lean_inc(v_bkt_379_);
lean_inc(v_a_360_);
v___x_380_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_357_, v_a_360_, v_bkt_379_);
if (v___x_380_ == 0)
{
lean_object* v___x_382_; uint8_t v_isShared_383_; uint8_t v_isSharedCheck_405_; 
lean_inc_ref(v_buckets_363_);
lean_inc(v_size_362_);
v_isSharedCheck_405_ = !lean_is_exclusive(v_m_359_);
if (v_isSharedCheck_405_ == 0)
{
lean_object* v_unused_406_; lean_object* v_unused_407_; 
v_unused_406_ = lean_ctor_get(v_m_359_, 1);
lean_dec(v_unused_406_);
v_unused_407_ = lean_ctor_get(v_m_359_, 0);
lean_dec(v_unused_407_);
v___x_382_ = v_m_359_;
v_isShared_383_ = v_isSharedCheck_405_;
goto v_resetjp_381_;
}
else
{
lean_dec(v_m_359_);
v___x_382_ = lean_box(0);
v_isShared_383_ = v_isSharedCheck_405_;
goto v_resetjp_381_;
}
v_resetjp_381_:
{
lean_object* v___x_384_; lean_object* v_size_x27_385_; lean_object* v___x_386_; lean_object* v_buckets_x27_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_384_ = lean_unsigned_to_nat(1u);
v_size_x27_385_ = lean_nat_add(v_size_362_, v___x_384_);
lean_dec(v_size_362_);
lean_inc(v_bkt_379_);
v___x_386_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_386_, 0, v_a_360_);
lean_ctor_set(v___x_386_, 1, v_b_361_);
lean_ctor_set(v___x_386_, 2, v_bkt_379_);
v_buckets_x27_387_ = lean_array_uset(v_buckets_363_, v___x_378_, v___x_386_);
v___x_388_ = lean_unsigned_to_nat(4u);
v___x_389_ = lean_nat_mul(v_size_x27_385_, v___x_388_);
v___x_390_ = lean_unsigned_to_nat(3u);
v___x_391_ = lean_nat_div(v___x_389_, v___x_390_);
lean_dec(v___x_389_);
v___x_392_ = lean_array_get_size(v_buckets_x27_387_);
v___x_393_ = lean_nat_dec_le(v___x_391_, v___x_392_);
lean_dec(v___x_391_);
if (v___x_393_ == 0)
{
lean_object* v_val_394_; lean_object* v___x_396_; 
v_val_394_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_358_, v_buckets_x27_387_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v_val_394_);
lean_ctor_set(v___x_382_, 0, v_size_x27_385_);
v___x_396_ = v___x_382_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_size_x27_385_);
lean_ctor_set(v_reuseFailAlloc_399_, 1, v_val_394_);
v___x_396_ = v_reuseFailAlloc_399_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
v___x_397_ = lean_box(v___x_380_);
v___x_398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_396_);
return v___x_398_;
}
}
else
{
lean_object* v___x_401_; 
lean_dec_ref(v_x_358_);
if (v_isShared_383_ == 0)
{
lean_ctor_set(v___x_382_, 1, v_buckets_x27_387_);
lean_ctor_set(v___x_382_, 0, v_size_x27_385_);
v___x_401_ = v___x_382_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_size_x27_385_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v_buckets_x27_387_);
v___x_401_ = v_reuseFailAlloc_404_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_402_ = lean_box(v___x_380_);
v___x_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_402_);
lean_ctor_set(v___x_403_, 1, v___x_401_);
return v___x_403_;
}
}
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_dec(v_b_361_);
lean_dec(v_a_360_);
lean_dec_ref(v_x_358_);
v___x_408_ = lean_box(v___x_380_);
v___x_409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_409_, 0, v___x_408_);
lean_ctor_set(v___x_409_, 1, v_m_359_);
return v___x_409_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_m_414_, lean_object* v_a_415_, lean_object* v_b_416_){
_start:
{
lean_object* v_size_417_; lean_object* v_buckets_418_; lean_object* v___x_419_; lean_object* v___x_420_; uint64_t v___x_421_; uint64_t v___x_422_; uint64_t v___x_423_; uint64_t v___x_424_; uint64_t v_fold_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v___x_431_; size_t v___x_432_; size_t v___x_433_; lean_object* v_bkt_434_; uint8_t v___x_435_; 
v_size_417_ = lean_ctor_get(v_m_414_, 0);
v_buckets_418_ = lean_ctor_get(v_m_414_, 1);
v___x_419_ = lean_array_get_size(v_buckets_418_);
lean_inc_ref(v_x_413_);
lean_inc(v_a_415_);
v___x_420_ = lean_apply_1(v_x_413_, v_a_415_);
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
v___x_430_ = lean_usize_of_nat(v___x_419_);
v___x_431_ = ((size_t)1ULL);
v___x_432_ = lean_usize_sub(v___x_430_, v___x_431_);
v___x_433_ = lean_usize_land(v___x_429_, v___x_432_);
v_bkt_434_ = lean_array_uget_borrowed(v_buckets_418_, v___x_433_);
lean_inc(v_bkt_434_);
lean_inc(v_a_415_);
v___x_435_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_412_, v_a_415_, v_bkt_434_);
if (v___x_435_ == 0)
{
lean_object* v___x_437_; uint8_t v_isShared_438_; uint8_t v_isSharedCheck_460_; 
lean_inc_ref(v_buckets_418_);
lean_inc(v_size_417_);
v_isSharedCheck_460_ = !lean_is_exclusive(v_m_414_);
if (v_isSharedCheck_460_ == 0)
{
lean_object* v_unused_461_; lean_object* v_unused_462_; 
v_unused_461_ = lean_ctor_get(v_m_414_, 1);
lean_dec(v_unused_461_);
v_unused_462_ = lean_ctor_get(v_m_414_, 0);
lean_dec(v_unused_462_);
v___x_437_ = v_m_414_;
v_isShared_438_ = v_isSharedCheck_460_;
goto v_resetjp_436_;
}
else
{
lean_dec(v_m_414_);
v___x_437_ = lean_box(0);
v_isShared_438_ = v_isSharedCheck_460_;
goto v_resetjp_436_;
}
v_resetjp_436_:
{
lean_object* v___x_439_; lean_object* v_size_x27_440_; lean_object* v___x_441_; lean_object* v_buckets_x27_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_439_ = lean_unsigned_to_nat(1u);
v_size_x27_440_ = lean_nat_add(v_size_417_, v___x_439_);
lean_dec(v_size_417_);
lean_inc(v_bkt_434_);
v___x_441_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_441_, 0, v_a_415_);
lean_ctor_set(v___x_441_, 1, v_b_416_);
lean_ctor_set(v___x_441_, 2, v_bkt_434_);
v_buckets_x27_442_ = lean_array_uset(v_buckets_418_, v___x_433_, v___x_441_);
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
v_val_449_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_413_, v_buckets_x27_442_);
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
lean_dec_ref(v_x_413_);
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
lean_dec(v_b_416_);
lean_dec(v_a_415_);
lean_dec_ref(v_x_413_);
v___x_463_ = lean_box(v___x_435_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v_m_414_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_m_467_, lean_object* v_a_468_, lean_object* v_b_469_){
_start:
{
lean_object* v_size_470_; lean_object* v_buckets_471_; lean_object* v___x_472_; lean_object* v___x_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; uint64_t v___x_477_; uint64_t v_fold_478_; uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; size_t v___x_482_; size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; size_t v___x_486_; lean_object* v_bkt_487_; lean_object* v___x_488_; 
v_size_470_ = lean_ctor_get(v_m_467_, 0);
v_buckets_471_ = lean_ctor_get(v_m_467_, 1);
v___x_472_ = lean_array_get_size(v_buckets_471_);
lean_inc_ref(v_x_466_);
lean_inc(v_a_468_);
v___x_473_ = lean_apply_1(v_x_466_, v_a_468_);
v___x_474_ = 32ULL;
v___x_475_ = lean_unbox_uint64(v___x_473_);
v___x_476_ = lean_uint64_shift_right(v___x_475_, v___x_474_);
v___x_477_ = lean_unbox_uint64(v___x_473_);
lean_dec_ref(v___x_473_);
v_fold_478_ = lean_uint64_xor(v___x_477_, v___x_476_);
v___x_479_ = 16ULL;
v___x_480_ = lean_uint64_shift_right(v_fold_478_, v___x_479_);
v___x_481_ = lean_uint64_xor(v_fold_478_, v___x_480_);
v___x_482_ = lean_uint64_to_usize(v___x_481_);
v___x_483_ = lean_usize_of_nat(v___x_472_);
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_sub(v___x_483_, v___x_484_);
v___x_486_ = lean_usize_land(v___x_482_, v___x_485_);
v_bkt_487_ = lean_array_uget_borrowed(v_buckets_471_, v___x_486_);
lean_inc(v_bkt_487_);
lean_inc(v_a_468_);
v___x_488_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_465_, v_a_468_, v_bkt_487_);
if (lean_obj_tag(v___x_488_) == 0)
{
lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_511_; 
lean_inc_ref(v_buckets_471_);
lean_inc(v_size_470_);
v_isSharedCheck_511_ = !lean_is_exclusive(v_m_467_);
if (v_isSharedCheck_511_ == 0)
{
lean_object* v_unused_512_; lean_object* v_unused_513_; 
v_unused_512_ = lean_ctor_get(v_m_467_, 1);
lean_dec(v_unused_512_);
v_unused_513_ = lean_ctor_get(v_m_467_, 0);
lean_dec(v_unused_513_);
v___x_490_ = v_m_467_;
v_isShared_491_ = v_isSharedCheck_511_;
goto v_resetjp_489_;
}
else
{
lean_dec(v_m_467_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_511_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v_size_x27_493_; lean_object* v___x_494_; lean_object* v_buckets_x27_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v_size_x27_493_ = lean_nat_add(v_size_470_, v___x_492_);
lean_dec(v_size_470_);
lean_inc(v_bkt_487_);
v___x_494_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_494_, 0, v_a_468_);
lean_ctor_set(v___x_494_, 1, v_b_469_);
lean_ctor_set(v___x_494_, 2, v_bkt_487_);
v_buckets_x27_495_ = lean_array_uset(v_buckets_471_, v___x_486_, v___x_494_);
v___x_496_ = lean_unsigned_to_nat(4u);
v___x_497_ = lean_nat_mul(v_size_x27_493_, v___x_496_);
v___x_498_ = lean_unsigned_to_nat(3u);
v___x_499_ = lean_nat_div(v___x_497_, v___x_498_);
lean_dec(v___x_497_);
v___x_500_ = lean_array_get_size(v_buckets_x27_495_);
v___x_501_ = lean_nat_dec_le(v___x_499_, v___x_500_);
lean_dec(v___x_499_);
if (v___x_501_ == 0)
{
lean_object* v_val_502_; lean_object* v___x_504_; 
v_val_502_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_466_, v_buckets_x27_495_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v_val_502_);
lean_ctor_set(v___x_490_, 0, v_size_x27_493_);
v___x_504_ = v___x_490_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v_size_x27_493_);
lean_ctor_set(v_reuseFailAlloc_506_, 1, v_val_502_);
v___x_504_ = v_reuseFailAlloc_506_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; 
v___x_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_488_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
return v___x_505_;
}
}
else
{
lean_object* v___x_508_; 
lean_dec_ref(v_x_466_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 1, v_buckets_x27_495_);
lean_ctor_set(v___x_490_, 0, v_size_x27_493_);
v___x_508_ = v___x_490_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_size_x27_493_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_buckets_x27_495_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_488_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
return v___x_509_;
}
}
}
}
else
{
lean_object* v___x_514_; 
lean_dec(v_b_469_);
lean_dec(v_a_468_);
lean_dec_ref(v_x_466_);
v___x_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_488_);
lean_ctor_set(v___x_514_, 1, v_m_467_);
return v___x_514_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_515_, lean_object* v_00_u03b2_516_, lean_object* v_x_517_, lean_object* v_x_518_, lean_object* v_m_519_, lean_object* v_a_520_, lean_object* v_b_521_){
_start:
{
lean_object* v_size_522_; lean_object* v_buckets_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint64_t v___x_526_; uint64_t v___x_527_; uint64_t v___x_528_; uint64_t v___x_529_; uint64_t v_fold_530_; uint64_t v___x_531_; uint64_t v___x_532_; uint64_t v___x_533_; size_t v___x_534_; size_t v___x_535_; size_t v___x_536_; size_t v___x_537_; size_t v___x_538_; lean_object* v_bkt_539_; lean_object* v___x_540_; 
v_size_522_ = lean_ctor_get(v_m_519_, 0);
v_buckets_523_ = lean_ctor_get(v_m_519_, 1);
v___x_524_ = lean_array_get_size(v_buckets_523_);
lean_inc_ref(v_x_518_);
lean_inc(v_a_520_);
v___x_525_ = lean_apply_1(v_x_518_, v_a_520_);
v___x_526_ = 32ULL;
v___x_527_ = lean_unbox_uint64(v___x_525_);
v___x_528_ = lean_uint64_shift_right(v___x_527_, v___x_526_);
v___x_529_ = lean_unbox_uint64(v___x_525_);
lean_dec_ref(v___x_525_);
v_fold_530_ = lean_uint64_xor(v___x_529_, v___x_528_);
v___x_531_ = 16ULL;
v___x_532_ = lean_uint64_shift_right(v_fold_530_, v___x_531_);
v___x_533_ = lean_uint64_xor(v_fold_530_, v___x_532_);
v___x_534_ = lean_uint64_to_usize(v___x_533_);
v___x_535_ = lean_usize_of_nat(v___x_524_);
v___x_536_ = ((size_t)1ULL);
v___x_537_ = lean_usize_sub(v___x_535_, v___x_536_);
v___x_538_ = lean_usize_land(v___x_534_, v___x_537_);
v_bkt_539_ = lean_array_uget_borrowed(v_buckets_523_, v___x_538_);
lean_inc(v_bkt_539_);
lean_inc(v_a_520_);
v___x_540_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_517_, v_a_520_, v_bkt_539_);
if (lean_obj_tag(v___x_540_) == 0)
{
lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_563_; 
lean_inc_ref(v_buckets_523_);
lean_inc(v_size_522_);
v_isSharedCheck_563_ = !lean_is_exclusive(v_m_519_);
if (v_isSharedCheck_563_ == 0)
{
lean_object* v_unused_564_; lean_object* v_unused_565_; 
v_unused_564_ = lean_ctor_get(v_m_519_, 1);
lean_dec(v_unused_564_);
v_unused_565_ = lean_ctor_get(v_m_519_, 0);
lean_dec(v_unused_565_);
v___x_542_ = v_m_519_;
v_isShared_543_ = v_isSharedCheck_563_;
goto v_resetjp_541_;
}
else
{
lean_dec(v_m_519_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_563_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_544_; lean_object* v_size_x27_545_; lean_object* v___x_546_; lean_object* v_buckets_x27_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_544_ = lean_unsigned_to_nat(1u);
v_size_x27_545_ = lean_nat_add(v_size_522_, v___x_544_);
lean_dec(v_size_522_);
lean_inc(v_bkt_539_);
v___x_546_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_546_, 0, v_a_520_);
lean_ctor_set(v___x_546_, 1, v_b_521_);
lean_ctor_set(v___x_546_, 2, v_bkt_539_);
v_buckets_x27_547_ = lean_array_uset(v_buckets_523_, v___x_538_, v___x_546_);
v___x_548_ = lean_unsigned_to_nat(4u);
v___x_549_ = lean_nat_mul(v_size_x27_545_, v___x_548_);
v___x_550_ = lean_unsigned_to_nat(3u);
v___x_551_ = lean_nat_div(v___x_549_, v___x_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_array_get_size(v_buckets_x27_547_);
v___x_553_ = lean_nat_dec_le(v___x_551_, v___x_552_);
lean_dec(v___x_551_);
if (v___x_553_ == 0)
{
lean_object* v_val_554_; lean_object* v___x_556_; 
v_val_554_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_518_, v_buckets_x27_547_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_val_554_);
lean_ctor_set(v___x_542_, 0, v_size_x27_545_);
v___x_556_ = v___x_542_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_size_x27_545_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_val_554_);
v___x_556_ = v_reuseFailAlloc_558_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; 
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_540_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
return v___x_557_;
}
}
else
{
lean_object* v___x_560_; 
lean_dec_ref(v_x_518_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_buckets_x27_547_);
lean_ctor_set(v___x_542_, 0, v_size_x27_545_);
v___x_560_ = v___x_542_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_size_x27_545_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_buckets_x27_547_);
v___x_560_ = v_reuseFailAlloc_562_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_540_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
return v___x_561_;
}
}
}
}
else
{
lean_object* v___x_566_; 
lean_dec(v_b_521_);
lean_dec(v_a_520_);
lean_dec_ref(v_x_518_);
v___x_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_566_, 0, v___x_540_);
lean_ctor_set(v___x_566_, 1, v_m_519_);
return v___x_566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg(lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_m_569_, lean_object* v_a_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_567_, v_x_568_, v_m_569_, v_a_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg___boxed(lean_object* v_x_572_, lean_object* v_x_573_, lean_object* v_m_574_, lean_object* v_a_575_){
_start:
{
lean_object* v_res_576_; 
v_res_576_ = l_Std_HashMap_get_x3f___redArg(v_x_572_, v_x_573_, v_m_574_, v_a_575_);
lean_dec_ref(v_m_574_);
return v_res_576_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f(lean_object* v_00_u03b1_577_, lean_object* v_00_u03b2_578_, lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_m_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_583_; 
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_579_, v_x_580_, v_m_581_, v_a_582_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___boxed(lean_object* v_00_u03b1_584_, lean_object* v_00_u03b2_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_m_588_, lean_object* v_a_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_HashMap_get_x3f(v_00_u03b1_584_, v_00_u03b2_585_, v_x_586_, v_x_587_, v_m_588_, v_a_589_);
lean_dec_ref(v_m_588_);
return v_res_590_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_contains___redArg(lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_m_593_, lean_object* v_a_594_){
_start:
{
uint8_t v___x_595_; 
v___x_595_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_591_, v_x_592_, v_m_593_, v_a_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___redArg___boxed(lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_m_598_, lean_object* v_a_599_){
_start:
{
uint8_t v_res_600_; lean_object* v_r_601_; 
v_res_600_ = l_Std_HashMap_contains___redArg(v_x_596_, v_x_597_, v_m_598_, v_a_599_);
lean_dec_ref(v_m_598_);
v_r_601_ = lean_box(v_res_600_);
return v_r_601_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_contains(lean_object* v_00_u03b1_602_, lean_object* v_00_u03b2_603_, lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_m_606_, lean_object* v_a_607_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_604_, v_x_605_, v_m_606_, v_a_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___boxed(lean_object* v_00_u03b1_609_, lean_object* v_00_u03b2_610_, lean_object* v_x_611_, lean_object* v_x_612_, lean_object* v_m_613_, lean_object* v_a_614_){
_start:
{
uint8_t v_res_615_; lean_object* v_r_616_; 
v_res_615_ = l_Std_HashMap_contains(v_00_u03b1_609_, v_00_u03b2_610_, v_x_611_, v_x_612_, v_m_613_, v_a_614_);
lean_dec_ref(v_m_613_);
v_r_616_ = lean_box(v_res_615_);
return v_r_616_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership(lean_object* v_00_u03b1_617_, lean_object* v_00_u03b2_618_, lean_object* v_inst_619_, lean_object* v_inst_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = lean_box(0);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___boxed(lean_object* v_00_u03b1_622_, lean_object* v_00_u03b2_623_, lean_object* v_inst_624_, lean_object* v_inst_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_HashMap_instMembership(v_00_u03b1_622_, v_00_u03b2_623_, v_inst_624_, v_inst_625_);
lean_dec_ref(v_inst_625_);
lean_dec_ref(v_inst_624_);
return v_res_626_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem___redArg(lean_object* v_inst_627_, lean_object* v_inst_628_, lean_object* v_m_629_, lean_object* v_a_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_627_, v_inst_628_, v_m_629_, v_a_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___redArg___boxed(lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_m_634_, lean_object* v_a_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Std_HashMap_instDecidableMem___redArg(v_inst_632_, v_inst_633_, v_m_634_, v_a_635_);
lean_dec_ref(v_m_634_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem(lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_m_642_, lean_object* v_a_643_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_640_, v_inst_641_, v_m_642_, v_a_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_645_, lean_object* v_00_u03b2_646_, lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_m_649_, lean_object* v_a_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_Std_HashMap_instDecidableMem(v_00_u03b1_645_, v_00_u03b2_646_, v_inst_647_, v_inst_648_, v_m_649_, v_a_650_);
lean_dec_ref(v_m_649_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg(lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_m_655_, lean_object* v_a_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_653_, v_x_654_, v_m_655_, v_a_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg___boxed(lean_object* v_x_658_, lean_object* v_x_659_, lean_object* v_m_660_, lean_object* v_a_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_HashMap_get___redArg(v_x_658_, v_x_659_, v_m_660_, v_a_661_);
lean_dec_ref(v_m_660_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get(lean_object* v_00_u03b1_663_, lean_object* v_00_u03b2_664_, lean_object* v_x_665_, lean_object* v_x_666_, lean_object* v_m_667_, lean_object* v_a_668_, lean_object* v_h_669_){
_start:
{
lean_object* v___x_670_; 
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_665_, v_x_666_, v_m_667_, v_a_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___boxed(lean_object* v_00_u03b1_671_, lean_object* v_00_u03b2_672_, lean_object* v_x_673_, lean_object* v_x_674_, lean_object* v_m_675_, lean_object* v_a_676_, lean_object* v_h_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Std_HashMap_get(v_00_u03b1_671_, v_00_u03b2_672_, v_x_673_, v_x_674_, v_m_675_, v_a_676_, v_h_677_);
lean_dec_ref(v_m_675_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg(lean_object* v_x_679_, lean_object* v_x_680_, lean_object* v_m_681_, lean_object* v_a_682_, lean_object* v_fallback_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_679_, v_x_680_, v_m_681_, v_a_682_, v_fallback_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg___boxed(lean_object* v_x_685_, lean_object* v_x_686_, lean_object* v_m_687_, lean_object* v_a_688_, lean_object* v_fallback_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Std_HashMap_getD___redArg(v_x_685_, v_x_686_, v_m_687_, v_a_688_, v_fallback_689_);
lean_dec(v_fallback_689_);
lean_dec_ref(v_m_687_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD(lean_object* v_00_u03b1_691_, lean_object* v_00_u03b2_692_, lean_object* v_x_693_, lean_object* v_x_694_, lean_object* v_m_695_, lean_object* v_a_696_, lean_object* v_fallback_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_693_, v_x_694_, v_m_695_, v_a_696_, v_fallback_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___boxed(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_m_703_, lean_object* v_a_704_, lean_object* v_fallback_705_){
_start:
{
lean_object* v_res_706_; 
v_res_706_ = l_Std_HashMap_getD(v_00_u03b1_699_, v_00_u03b2_700_, v_x_701_, v_x_702_, v_m_703_, v_a_704_, v_fallback_705_);
lean_dec(v_fallback_705_);
lean_dec_ref(v_m_703_);
return v_res_706_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg(lean_object* v_x_707_, lean_object* v_x_708_, lean_object* v_inst_709_, lean_object* v_m_710_, lean_object* v_a_711_){
_start:
{
lean_object* v___x_712_; 
v___x_712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_707_, v_x_708_, v_inst_709_, v_m_710_, v_a_711_);
return v___x_712_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg___boxed(lean_object* v_x_713_, lean_object* v_x_714_, lean_object* v_inst_715_, lean_object* v_m_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_HashMap_get_x21___redArg(v_x_713_, v_x_714_, v_inst_715_, v_m_716_, v_a_717_);
lean_dec_ref(v_m_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21(lean_object* v_00_u03b1_719_, lean_object* v_00_u03b2_720_, lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_inst_723_, lean_object* v_m_724_, lean_object* v_a_725_){
_start:
{
lean_object* v___x_726_; 
v___x_726_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_721_, v_x_722_, v_inst_723_, v_m_724_, v_a_725_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___boxed(lean_object* v_00_u03b1_727_, lean_object* v_00_u03b2_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_inst_731_, lean_object* v_m_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_Std_HashMap_get_x21(v_00_u03b1_727_, v_00_u03b2_728_, v_x_729_, v_x_730_, v_inst_731_, v_m_732_, v_a_733_);
lean_dec_ref(v_m_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_735_, lean_object* v_inst_736_, lean_object* v_m_737_, lean_object* v_a_738_, lean_object* v_h_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_735_, v_inst_736_, v_m_737_, v_a_738_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_741_, lean_object* v_inst_742_, lean_object* v_m_743_, lean_object* v_a_744_, lean_object* v_h_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(v_inst_741_, v_inst_742_, v_m_743_, v_a_744_, v_h_745_);
lean_dec_ref(v_m_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_747_, lean_object* v_inst_748_, lean_object* v_m_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_747_, v_inst_748_, v_m_749_, v_a_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_752_, lean_object* v_inst_753_, lean_object* v_m_754_, lean_object* v_a_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(v_inst_752_, v_inst_753_, v_m_754_, v_a_755_);
lean_dec_ref(v_m_754_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_m_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_757_, v_inst_758_, v_inst_759_, v_m_760_, v_a_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_m_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(v_inst_763_, v_inst_764_, v_inst_765_, v_m_766_, v_a_767_);
lean_dec_ref(v_m_766_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg(lean_object* v_inst_769_, lean_object* v_inst_770_){
_start:
{
lean_object* v___f_771_; lean_object* v___f_772_; lean_object* v___f_773_; lean_object* v___x_774_; 
lean_inc_ref(v_inst_770_);
lean_inc_ref(v_inst_769_);
v___f_771_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_771_, 0, v_inst_769_);
lean_closure_set(v___f_771_, 1, v_inst_770_);
lean_inc_ref(v_inst_770_);
lean_inc_ref(v_inst_769_);
v___f_772_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_772_, 0, v_inst_769_);
lean_closure_set(v___f_772_, 1, v_inst_770_);
v___f_773_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_773_, 0, v_inst_769_);
lean_closure_set(v___f_773_, 1, v_inst_770_);
v___x_774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_774_, 0, v___f_771_);
lean_ctor_set(v___x_774_, 1, v___f_772_);
lean_ctor_set(v___x_774_, 2, v___f_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem(lean_object* v_00_u03b1_775_, lean_object* v_00_u03b2_776_, lean_object* v_inst_777_, lean_object* v_inst_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_HashMap_instGetElem_x3fMem___redArg(v_inst_777_, v_inst_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg(lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_m_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_780_, v_x_781_, v_m_782_, v_a_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg___boxed(lean_object* v_x_785_, lean_object* v_x_786_, lean_object* v_m_787_, lean_object* v_a_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l_Std_HashMap_getKey_x3f___redArg(v_x_785_, v_x_786_, v_m_787_, v_a_788_);
lean_dec_ref(v_m_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f(lean_object* v_00_u03b1_790_, lean_object* v_00_u03b2_791_, lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_m_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_792_, v_x_793_, v_m_794_, v_a_795_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_797_, lean_object* v_00_u03b2_798_, lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_m_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_HashMap_getKey_x3f(v_00_u03b1_797_, v_00_u03b2_798_, v_x_799_, v_x_800_, v_m_801_, v_a_802_);
lean_dec_ref(v_m_801_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg(lean_object* v_x_804_, lean_object* v_x_805_, lean_object* v_m_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_804_, v_x_805_, v_m_806_, v_a_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg___boxed(lean_object* v_x_809_, lean_object* v_x_810_, lean_object* v_m_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_HashMap_getKey___redArg(v_x_809_, v_x_810_, v_m_811_, v_a_812_);
lean_dec_ref(v_m_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey(lean_object* v_00_u03b1_814_, lean_object* v_00_u03b2_815_, lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_m_818_, lean_object* v_a_819_, lean_object* v_h_820_){
_start:
{
lean_object* v___x_821_; 
v___x_821_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_816_, v_x_817_, v_m_818_, v_a_819_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___boxed(lean_object* v_00_u03b1_822_, lean_object* v_00_u03b2_823_, lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_m_826_, lean_object* v_a_827_, lean_object* v_h_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Std_HashMap_getKey(v_00_u03b1_822_, v_00_u03b2_823_, v_x_824_, v_x_825_, v_m_826_, v_a_827_, v_h_828_);
lean_dec_ref(v_m_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg(lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_m_832_, lean_object* v_a_833_, lean_object* v_fallback_834_){
_start:
{
lean_object* v___x_835_; 
v___x_835_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_830_, v_x_831_, v_m_832_, v_a_833_, v_fallback_834_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg___boxed(lean_object* v_x_836_, lean_object* v_x_837_, lean_object* v_m_838_, lean_object* v_a_839_, lean_object* v_fallback_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Std_HashMap_getKeyD___redArg(v_x_836_, v_x_837_, v_m_838_, v_a_839_, v_fallback_840_);
lean_dec(v_fallback_840_);
lean_dec_ref(v_m_838_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD(lean_object* v_00_u03b1_842_, lean_object* v_00_u03b2_843_, lean_object* v_x_844_, lean_object* v_x_845_, lean_object* v_m_846_, lean_object* v_a_847_, lean_object* v_fallback_848_){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_844_, v_x_845_, v_m_846_, v_a_847_, v_fallback_848_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___boxed(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_m_854_, lean_object* v_a_855_, lean_object* v_fallback_856_){
_start:
{
lean_object* v_res_857_; 
v_res_857_ = l_Std_HashMap_getKeyD(v_00_u03b1_850_, v_00_u03b2_851_, v_x_852_, v_x_853_, v_m_854_, v_a_855_, v_fallback_856_);
lean_dec(v_fallback_856_);
lean_dec_ref(v_m_854_);
return v_res_857_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg(lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_inst_860_, lean_object* v_m_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_863_; 
v___x_863_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_858_, v_x_859_, v_inst_860_, v_m_861_, v_a_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg___boxed(lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_inst_866_, lean_object* v_m_867_, lean_object* v_a_868_){
_start:
{
lean_object* v_res_869_; 
v_res_869_ = l_Std_HashMap_getKey_x21___redArg(v_x_864_, v_x_865_, v_inst_866_, v_m_867_, v_a_868_);
lean_dec_ref(v_m_867_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21(lean_object* v_00_u03b1_870_, lean_object* v_00_u03b2_871_, lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_inst_874_, lean_object* v_m_875_, lean_object* v_a_876_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_872_, v_x_873_, v_inst_874_, v_m_875_, v_a_876_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___boxed(lean_object* v_00_u03b1_878_, lean_object* v_00_u03b2_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_inst_882_, lean_object* v_m_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Std_HashMap_getKey_x21(v_00_u03b1_878_, v_00_u03b2_879_, v_x_880_, v_x_881_, v_inst_882_, v_m_883_, v_a_884_);
lean_dec_ref(v_m_883_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase___redArg(lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_m_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_890_; 
v___x_890_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_886_, v_x_887_, v_m_888_, v_a_889_);
return v___x_890_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase(lean_object* v_00_u03b1_891_, lean_object* v_00_u03b2_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_m_895_, lean_object* v_a_896_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_893_, v_x_894_, v_m_895_, v_a_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg(lean_object* v_m_898_){
_start:
{
lean_object* v_size_899_; 
v_size_899_ = lean_ctor_get(v_m_898_, 0);
lean_inc(v_size_899_);
return v_size_899_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg___boxed(lean_object* v_m_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_Std_HashMap_size___redArg(v_m_900_);
lean_dec_ref(v_m_900_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size(lean_object* v_00_u03b1_902_, lean_object* v_00_u03b2_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_m_906_){
_start:
{
lean_object* v_size_907_; 
v_size_907_ = lean_ctor_get(v_m_906_, 0);
lean_inc(v_size_907_);
return v_size_907_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___boxed(lean_object* v_00_u03b1_908_, lean_object* v_00_u03b2_909_, lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v_m_912_){
_start:
{
lean_object* v_res_913_; 
v_res_913_ = l_Std_HashMap_size(v_00_u03b1_908_, v_00_u03b2_909_, v_x_910_, v_x_911_, v_m_912_);
lean_dec_ref(v_m_912_);
lean_dec_ref(v_x_911_);
lean_dec_ref(v_x_910_);
return v_res_913_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty___redArg(lean_object* v_m_914_){
_start:
{
lean_object* v_size_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_size_915_ = lean_ctor_get(v_m_914_, 0);
v___x_916_ = lean_unsigned_to_nat(0u);
v___x_917_ = lean_nat_dec_eq(v_size_915_, v___x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___redArg___boxed(lean_object* v_m_918_){
_start:
{
uint8_t v_res_919_; lean_object* v_r_920_; 
v_res_919_ = l_Std_HashMap_isEmpty___redArg(v_m_918_);
lean_dec_ref(v_m_918_);
v_r_920_ = lean_box(v_res_919_);
return v_r_920_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty(lean_object* v_00_u03b1_921_, lean_object* v_00_u03b2_922_, lean_object* v_x_923_, lean_object* v_x_924_, lean_object* v_m_925_){
_start:
{
lean_object* v_size_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_size_926_ = lean_ctor_get(v_m_925_, 0);
v___x_927_ = lean_unsigned_to_nat(0u);
v___x_928_ = lean_nat_dec_eq(v_size_926_, v___x_927_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___boxed(lean_object* v_00_u03b1_929_, lean_object* v_00_u03b2_930_, lean_object* v_x_931_, lean_object* v_x_932_, lean_object* v_m_933_){
_start:
{
uint8_t v_res_934_; lean_object* v_r_935_; 
v_res_934_ = l_Std_HashMap_isEmpty(v_00_u03b1_929_, v_00_u03b2_930_, v_x_931_, v_x_932_, v_m_933_);
lean_dec_ref(v_m_933_);
lean_dec_ref(v_x_932_);
lean_dec_ref(v_x_931_);
v_r_935_ = lean_box(v_res_934_);
return v_r_935_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0(lean_object* v_a_936_, lean_object* v_b_937_, lean_object* v_d_938_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_939_, 0, v_a_936_);
lean_ctor_set(v___x_939_, 1, v_d_938_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0___boxed(lean_object* v_a_940_, lean_object* v_b_941_, lean_object* v_d_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l_Std_HashMap_keys___redArg___lam__0(v_a_940_, v_b_941_, v_d_942_);
lean_dec(v_b_941_);
return v_res_943_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__1(lean_object* v___x_944_, lean_object* v___f_945_, lean_object* v_l_946_, lean_object* v_acc_947_){
_start:
{
lean_object* v___x_948_; 
v___x_948_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_944_, v___f_945_, v_acc_947_, v_l_946_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg(lean_object* v_m_972_){
_start:
{
lean_object* v___x_973_; lean_object* v_buckets_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v___x_973_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_974_ = lean_ctor_get(v_m_972_, 1);
lean_inc_ref(v_buckets_974_);
lean_dec_ref(v_m_972_);
v___x_975_ = lean_box(0);
v___x_976_ = lean_array_get_size(v_buckets_974_);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_nat_dec_lt(v___x_977_, v___x_976_);
if (v___x_978_ == 0)
{
lean_dec_ref(v_buckets_974_);
return v___x_975_;
}
else
{
lean_object* v___f_979_; size_t v___x_980_; size_t v___x_981_; lean_object* v___x_982_; 
v___f_979_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__11));
v___x_980_ = lean_usize_of_nat(v___x_976_);
v___x_981_ = ((size_t)0ULL);
v___x_982_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_973_, v___f_979_, v_buckets_974_, v___x_980_, v___x_981_, v___x_975_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys(lean_object* v_00_u03b1_983_, lean_object* v_00_u03b2_984_, lean_object* v_x_985_, lean_object* v_x_986_, lean_object* v_m_987_){
_start:
{
lean_object* v___x_988_; lean_object* v_buckets_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; uint8_t v___x_993_; 
v___x_988_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_989_ = lean_ctor_get(v_m_987_, 1);
lean_inc_ref(v_buckets_989_);
lean_dec_ref(v_m_987_);
v___x_990_ = lean_box(0);
v___x_991_ = lean_array_get_size(v_buckets_989_);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_nat_dec_lt(v___x_992_, v___x_991_);
if (v___x_993_ == 0)
{
lean_dec_ref(v_buckets_989_);
return v___x_990_;
}
else
{
lean_object* v___f_994_; size_t v___x_995_; size_t v___x_996_; lean_object* v___x_997_; 
v___f_994_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__11));
v___x_995_ = lean_usize_of_nat(v___x_991_);
v___x_996_ = ((size_t)0ULL);
v___x_997_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_988_, v___f_994_, v_buckets_989_, v___x_995_, v___x_996_, v___x_990_);
return v___x_997_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___boxed(lean_object* v_00_u03b1_998_, lean_object* v_00_u03b2_999_, lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_m_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Std_HashMap_keys(v_00_u03b1_998_, v_00_u03b2_999_, v_x_1000_, v_x_1001_, v_m_1002_);
lean_dec_ref(v_x_1001_);
lean_dec_ref(v_x_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList___redArg(lean_object* v_inst_1008_, lean_object* v_inst_1009_, lean_object* v_l_1010_){
_start:
{
lean_object* v___f_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___f_1011_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1012_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1013_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1011_, v_inst_1008_, v_inst_1009_, v___x_1012_, v_l_1010_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_inst_1016_, lean_object* v_inst_1017_, lean_object* v_l_1018_){
_start:
{
lean_object* v___f_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___f_1019_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1020_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1021_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1019_, v_inst_1016_, v_inst_1017_, v___x_1020_, v_l_1018_);
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList___redArg(lean_object* v_inst_1022_, lean_object* v_inst_1023_, lean_object* v_l_1024_){
_start:
{
lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___f_1025_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1026_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1027_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1025_, v_inst_1022_, v_inst_1023_, v___x_1026_, v_l_1024_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList(lean_object* v_00_u03b1_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_l_1031_){
_start:
{
lean_object* v___f_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___f_1032_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1033_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1032_, v_inst_1029_, v_inst_1030_, v___x_1033_, v_l_1031_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray___redArg(lean_object* v_inst_1039_, lean_object* v_inst_1040_, lean_object* v_a_1041_){
_start:
{
lean_object* v___f_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___f_1042_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1043_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1042_, v_inst_1039_, v_inst_1040_, v___x_1043_, v_a_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray(lean_object* v_00_u03b1_1045_, lean_object* v_00_u03b2_1046_, lean_object* v_inst_1047_, lean_object* v_inst_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___f_1050_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1051_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1052_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1050_, v_inst_1047_, v_inst_1048_, v___x_1051_, v_a_1049_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__0(lean_object* v_a_1053_, lean_object* v_b_1054_, lean_object* v_d_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1056_, 0, v_a_1053_);
lean_ctor_set(v___x_1056_, 1, v_b_1054_);
v___x_1057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1057_, 0, v___x_1056_);
lean_ctor_set(v___x_1057_, 1, v_d_1055_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__1(lean_object* v___x_1058_, lean_object* v___f_1059_, lean_object* v_l_1060_, lean_object* v_acc_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1058_, v___f_1059_, v_acc_1061_, v_l_1060_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg(lean_object* v_m_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v_buckets_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1068_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1069_ = lean_ctor_get(v_m_1067_, 1);
lean_inc_ref(v_buckets_1069_);
lean_dec_ref(v_m_1067_);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_array_get_size(v_buckets_1069_);
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_nat_dec_lt(v___x_1072_, v___x_1071_);
if (v___x_1073_ == 0)
{
lean_dec_ref(v_buckets_1069_);
return v___x_1070_;
}
else
{
lean_object* v___f_1074_; size_t v___x_1075_; size_t v___x_1076_; lean_object* v___x_1077_; 
v___f_1074_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__1));
v___x_1075_ = lean_usize_of_nat(v___x_1071_);
v___x_1076_ = ((size_t)0ULL);
v___x_1077_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1068_, v___f_1074_, v_buckets_1069_, v___x_1075_, v___x_1076_, v___x_1070_);
return v___x_1077_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_m_1082_){
_start:
{
lean_object* v___x_1083_; lean_object* v_buckets_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v___x_1083_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1084_ = lean_ctor_get(v_m_1082_, 1);
lean_inc_ref(v_buckets_1084_);
lean_dec_ref(v_m_1082_);
v___x_1085_ = lean_box(0);
v___x_1086_ = lean_array_get_size(v_buckets_1084_);
v___x_1087_ = lean_unsigned_to_nat(0u);
v___x_1088_ = lean_nat_dec_lt(v___x_1087_, v___x_1086_);
if (v___x_1088_ == 0)
{
lean_dec_ref(v_buckets_1084_);
return v___x_1085_;
}
else
{
lean_object* v___f_1089_; size_t v___x_1090_; size_t v___x_1091_; lean_object* v___x_1092_; 
v___f_1089_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__1));
v___x_1090_ = lean_usize_of_nat(v___x_1086_);
v___x_1091_ = ((size_t)0ULL);
v___x_1092_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1083_, v___f_1089_, v_buckets_1084_, v___x_1090_, v___x_1091_, v___x_1085_);
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___boxed(lean_object* v_00_u03b1_1093_, lean_object* v_00_u03b2_1094_, lean_object* v_x_1095_, lean_object* v_x_1096_, lean_object* v_m_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_HashMap_toList(v_00_u03b1_1093_, v_00_u03b2_1094_, v_x_1095_, v_x_1096_, v_m_1097_);
lean_dec_ref(v_x_1096_);
lean_dec_ref(v_x_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg___lam__0(lean_object* v_inst_1099_, lean_object* v_f_1100_, lean_object* v_acc_1101_, lean_object* v_l_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1099_, v_f_1100_, v_acc_1101_, v_l_1102_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg(lean_object* v_inst_1104_, lean_object* v_f_1105_, lean_object* v_init_1106_, lean_object* v_b_1107_){
_start:
{
lean_object* v_buckets_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_buckets_1108_ = lean_ctor_get(v_b_1107_, 1);
lean_inc_ref(v_buckets_1108_);
lean_dec_ref(v_b_1107_);
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = lean_array_get_size(v_buckets_1108_);
v___x_1111_ = lean_nat_dec_lt(v___x_1109_, v___x_1110_);
if (v___x_1111_ == 0)
{
lean_object* v_toApplicative_1112_; lean_object* v_toPure_1113_; lean_object* v___x_1114_; 
lean_dec_ref(v_buckets_1108_);
lean_dec(v_f_1105_);
v_toApplicative_1112_ = lean_ctor_get(v_inst_1104_, 0);
lean_inc_ref(v_toApplicative_1112_);
lean_dec_ref(v_inst_1104_);
v_toPure_1113_ = lean_ctor_get(v_toApplicative_1112_, 1);
lean_inc(v_toPure_1113_);
lean_dec_ref(v_toApplicative_1112_);
v___x_1114_ = lean_apply_2(v_toPure_1113_, lean_box(0), v_init_1106_);
return v___x_1114_;
}
else
{
lean_object* v___f_1115_; uint8_t v___x_1116_; 
lean_inc_ref(v_inst_1104_);
v___f_1115_ = lean_alloc_closure((void*)(l_Std_HashMap_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1115_, 0, v_inst_1104_);
lean_closure_set(v___f_1115_, 1, v_f_1105_);
v___x_1116_ = lean_nat_dec_le(v___x_1110_, v___x_1110_);
if (v___x_1116_ == 0)
{
if (v___x_1111_ == 0)
{
lean_object* v_toApplicative_1117_; lean_object* v_toPure_1118_; lean_object* v___x_1119_; 
lean_dec_ref(v___f_1115_);
lean_dec_ref(v_buckets_1108_);
v_toApplicative_1117_ = lean_ctor_get(v_inst_1104_, 0);
lean_inc_ref(v_toApplicative_1117_);
lean_dec_ref(v_inst_1104_);
v_toPure_1118_ = lean_ctor_get(v_toApplicative_1117_, 1);
lean_inc(v_toPure_1118_);
lean_dec_ref(v_toApplicative_1117_);
v___x_1119_ = lean_apply_2(v_toPure_1118_, lean_box(0), v_init_1106_);
return v___x_1119_;
}
else
{
size_t v___x_1120_; size_t v___x_1121_; lean_object* v___x_1122_; 
v___x_1120_ = ((size_t)0ULL);
v___x_1121_ = lean_usize_of_nat(v___x_1110_);
v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1104_, v___f_1115_, v_buckets_1108_, v___x_1120_, v___x_1121_, v_init_1106_);
return v___x_1122_;
}
}
else
{
size_t v___x_1123_; size_t v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = ((size_t)0ULL);
v___x_1124_ = lean_usize_of_nat(v___x_1110_);
v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1104_, v___f_1115_, v_buckets_1108_, v___x_1123_, v___x_1124_, v_init_1106_);
return v___x_1125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM(lean_object* v_00_u03b1_1126_, lean_object* v_00_u03b2_1127_, lean_object* v_x_1128_, lean_object* v_x_1129_, lean_object* v_m_1130_, lean_object* v_inst_1131_, lean_object* v_00_u03b3_1132_, lean_object* v_f_1133_, lean_object* v_init_1134_, lean_object* v_b_1135_){
_start:
{
lean_object* v_buckets_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; uint8_t v___x_1139_; 
v_buckets_1136_ = lean_ctor_get(v_b_1135_, 1);
lean_inc_ref(v_buckets_1136_);
lean_dec_ref(v_b_1135_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_array_get_size(v_buckets_1136_);
v___x_1139_ = lean_nat_dec_lt(v___x_1137_, v___x_1138_);
if (v___x_1139_ == 0)
{
lean_object* v_toApplicative_1140_; lean_object* v_toPure_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v_buckets_1136_);
lean_dec(v_f_1133_);
v_toApplicative_1140_ = lean_ctor_get(v_inst_1131_, 0);
lean_inc_ref(v_toApplicative_1140_);
lean_dec_ref(v_inst_1131_);
v_toPure_1141_ = lean_ctor_get(v_toApplicative_1140_, 1);
lean_inc(v_toPure_1141_);
lean_dec_ref(v_toApplicative_1140_);
v___x_1142_ = lean_apply_2(v_toPure_1141_, lean_box(0), v_init_1134_);
return v___x_1142_;
}
else
{
lean_object* v___f_1143_; uint8_t v___x_1144_; 
lean_inc_ref(v_inst_1131_);
v___f_1143_ = lean_alloc_closure((void*)(l_Std_HashMap_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1143_, 0, v_inst_1131_);
lean_closure_set(v___f_1143_, 1, v_f_1133_);
v___x_1144_ = lean_nat_dec_le(v___x_1138_, v___x_1138_);
if (v___x_1144_ == 0)
{
if (v___x_1139_ == 0)
{
lean_object* v_toApplicative_1145_; lean_object* v_toPure_1146_; lean_object* v___x_1147_; 
lean_dec_ref(v___f_1143_);
lean_dec_ref(v_buckets_1136_);
v_toApplicative_1145_ = lean_ctor_get(v_inst_1131_, 0);
lean_inc_ref(v_toApplicative_1145_);
lean_dec_ref(v_inst_1131_);
v_toPure_1146_ = lean_ctor_get(v_toApplicative_1145_, 1);
lean_inc(v_toPure_1146_);
lean_dec_ref(v_toApplicative_1145_);
v___x_1147_ = lean_apply_2(v_toPure_1146_, lean_box(0), v_init_1134_);
return v___x_1147_;
}
else
{
size_t v___x_1148_; size_t v___x_1149_; lean_object* v___x_1150_; 
v___x_1148_ = ((size_t)0ULL);
v___x_1149_ = lean_usize_of_nat(v___x_1138_);
v___x_1150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1131_, v___f_1143_, v_buckets_1136_, v___x_1148_, v___x_1149_, v_init_1134_);
return v___x_1150_;
}
}
else
{
size_t v___x_1151_; size_t v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = ((size_t)0ULL);
v___x_1152_ = lean_usize_of_nat(v___x_1138_);
v___x_1153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1131_, v___f_1143_, v_buckets_1136_, v___x_1151_, v___x_1152_, v_init_1134_);
return v___x_1153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___boxed(lean_object* v_00_u03b1_1154_, lean_object* v_00_u03b2_1155_, lean_object* v_x_1156_, lean_object* v_x_1157_, lean_object* v_m_1158_, lean_object* v_inst_1159_, lean_object* v_00_u03b3_1160_, lean_object* v_f_1161_, lean_object* v_init_1162_, lean_object* v_b_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Std_HashMap_foldM(v_00_u03b1_1154_, v_00_u03b2_1155_, v_x_1156_, v_x_1157_, v_m_1158_, v_inst_1159_, v_00_u03b3_1160_, v_f_1161_, v_init_1162_, v_b_1163_);
lean_dec_ref(v_x_1157_);
lean_dec_ref(v_x_1156_);
return v_res_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__0(lean_object* v_f_1165_, lean_object* v_x1_1166_, lean_object* v_x2_1167_, lean_object* v_x3_1168_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_apply_3(v_f_1165_, v_x1_1166_, v_x2_1167_, v_x3_1168_);
return v___x_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__1(lean_object* v___x_1170_, lean_object* v___f_1171_, lean_object* v_acc_1172_, lean_object* v_l_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1170_, v___f_1171_, v_acc_1172_, v_l_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg(lean_object* v_f_1175_, lean_object* v_init_1176_, lean_object* v_b_1177_){
_start:
{
lean_object* v___x_1178_; lean_object* v_buckets_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; uint8_t v___x_1182_; 
v___x_1178_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1179_ = lean_ctor_get(v_b_1177_, 1);
lean_inc_ref(v_buckets_1179_);
lean_dec_ref(v_b_1177_);
v___x_1180_ = lean_unsigned_to_nat(0u);
v___x_1181_ = lean_array_get_size(v_buckets_1179_);
v___x_1182_ = lean_nat_dec_lt(v___x_1180_, v___x_1181_);
if (v___x_1182_ == 0)
{
lean_dec_ref(v_buckets_1179_);
lean_dec(v_f_1175_);
return v_init_1176_;
}
else
{
lean_object* v___f_1183_; lean_object* v___f_1184_; uint8_t v___x_1185_; 
v___f_1183_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1183_, 0, v_f_1175_);
v___f_1184_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1184_, 0, v___x_1178_);
lean_closure_set(v___f_1184_, 1, v___f_1183_);
v___x_1185_ = lean_nat_dec_le(v___x_1181_, v___x_1181_);
if (v___x_1185_ == 0)
{
if (v___x_1182_ == 0)
{
lean_dec_ref(v___f_1184_);
lean_dec_ref(v_buckets_1179_);
return v_init_1176_;
}
else
{
size_t v___x_1186_; size_t v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = ((size_t)0ULL);
v___x_1187_ = lean_usize_of_nat(v___x_1181_);
v___x_1188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1178_, v___f_1184_, v_buckets_1179_, v___x_1186_, v___x_1187_, v_init_1176_);
return v___x_1188_;
}
}
else
{
size_t v___x_1189_; size_t v___x_1190_; lean_object* v___x_1191_; 
v___x_1189_ = ((size_t)0ULL);
v___x_1190_ = lean_usize_of_nat(v___x_1181_);
v___x_1191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1178_, v___f_1184_, v_buckets_1179_, v___x_1189_, v___x_1190_, v_init_1176_);
return v___x_1191_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold(lean_object* v_00_u03b1_1192_, lean_object* v_00_u03b2_1193_, lean_object* v_x_1194_, lean_object* v_x_1195_, lean_object* v_00_u03b3_1196_, lean_object* v_f_1197_, lean_object* v_init_1198_, lean_object* v_b_1199_){
_start:
{
lean_object* v___x_1200_; lean_object* v_buckets_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1200_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1201_ = lean_ctor_get(v_b_1199_, 1);
lean_inc_ref(v_buckets_1201_);
lean_dec_ref(v_b_1199_);
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = lean_array_get_size(v_buckets_1201_);
v___x_1204_ = lean_nat_dec_lt(v___x_1202_, v___x_1203_);
if (v___x_1204_ == 0)
{
lean_dec_ref(v_buckets_1201_);
lean_dec(v_f_1197_);
return v_init_1198_;
}
else
{
lean_object* v___f_1205_; lean_object* v___f_1206_; uint8_t v___x_1207_; 
v___f_1205_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1205_, 0, v_f_1197_);
v___f_1206_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1206_, 0, v___x_1200_);
lean_closure_set(v___f_1206_, 1, v___f_1205_);
v___x_1207_ = lean_nat_dec_le(v___x_1203_, v___x_1203_);
if (v___x_1207_ == 0)
{
if (v___x_1204_ == 0)
{
lean_dec_ref(v___f_1206_);
lean_dec_ref(v_buckets_1201_);
return v_init_1198_;
}
else
{
size_t v___x_1208_; size_t v___x_1209_; lean_object* v___x_1210_; 
v___x_1208_ = ((size_t)0ULL);
v___x_1209_ = lean_usize_of_nat(v___x_1203_);
v___x_1210_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1200_, v___f_1206_, v_buckets_1201_, v___x_1208_, v___x_1209_, v_init_1198_);
return v___x_1210_;
}
}
else
{
size_t v___x_1211_; size_t v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = ((size_t)0ULL);
v___x_1212_ = lean_usize_of_nat(v___x_1203_);
v___x_1213_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1200_, v___f_1206_, v_buckets_1201_, v___x_1211_, v___x_1212_, v_init_1198_);
return v___x_1213_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___boxed(lean_object* v_00_u03b1_1214_, lean_object* v_00_u03b2_1215_, lean_object* v_x_1216_, lean_object* v_x_1217_, lean_object* v_00_u03b3_1218_, lean_object* v_f_1219_, lean_object* v_init_1220_, lean_object* v_b_1221_){
_start:
{
lean_object* v_res_1222_; 
v_res_1222_ = l_Std_HashMap_fold(v_00_u03b1_1214_, v_00_u03b2_1215_, v_x_1216_, v_x_1217_, v_00_u03b3_1218_, v_f_1219_, v_init_1220_, v_b_1221_);
lean_dec_ref(v_x_1217_);
lean_dec_ref(v_x_1216_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__0(lean_object* v_f_1223_, lean_object* v_x_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = lean_apply_2(v_f_1223_, v___y_1225_, v___y_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__1(lean_object* v_inst_1228_, lean_object* v___f_1229_, lean_object* v_x_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_box(0);
v___x_1233_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1228_, v___f_1229_, v___x_1232_, v___y_1231_);
return v___x_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg(lean_object* v_inst_1234_, lean_object* v_f_1235_, lean_object* v_b_1236_){
_start:
{
lean_object* v_buckets_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; uint8_t v___x_1241_; 
v_buckets_1237_ = lean_ctor_get(v_b_1236_, 1);
lean_inc_ref(v_buckets_1237_);
lean_dec_ref(v_b_1236_);
v___x_1238_ = lean_unsigned_to_nat(0u);
v___x_1239_ = lean_array_get_size(v_buckets_1237_);
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_nat_dec_lt(v___x_1238_, v___x_1239_);
if (v___x_1241_ == 0)
{
lean_object* v_toApplicative_1242_; lean_object* v_toPure_1243_; lean_object* v___x_1244_; 
lean_dec_ref(v_buckets_1237_);
lean_dec(v_f_1235_);
v_toApplicative_1242_ = lean_ctor_get(v_inst_1234_, 0);
lean_inc_ref(v_toApplicative_1242_);
lean_dec_ref(v_inst_1234_);
v_toPure_1243_ = lean_ctor_get(v_toApplicative_1242_, 1);
lean_inc(v_toPure_1243_);
lean_dec_ref(v_toApplicative_1242_);
v___x_1244_ = lean_apply_2(v_toPure_1243_, lean_box(0), v___x_1240_);
return v___x_1244_;
}
else
{
lean_object* v___f_1245_; lean_object* v___f_1246_; uint8_t v___x_1247_; 
v___f_1245_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1245_, 0, v_f_1235_);
lean_inc_ref(v_inst_1234_);
v___f_1246_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1246_, 0, v_inst_1234_);
lean_closure_set(v___f_1246_, 1, v___f_1245_);
v___x_1247_ = lean_nat_dec_le(v___x_1239_, v___x_1239_);
if (v___x_1247_ == 0)
{
if (v___x_1241_ == 0)
{
lean_object* v_toApplicative_1248_; lean_object* v_toPure_1249_; lean_object* v___x_1250_; 
lean_dec_ref(v___f_1246_);
lean_dec_ref(v_buckets_1237_);
v_toApplicative_1248_ = lean_ctor_get(v_inst_1234_, 0);
lean_inc_ref(v_toApplicative_1248_);
lean_dec_ref(v_inst_1234_);
v_toPure_1249_ = lean_ctor_get(v_toApplicative_1248_, 1);
lean_inc(v_toPure_1249_);
lean_dec_ref(v_toApplicative_1248_);
v___x_1250_ = lean_apply_2(v_toPure_1249_, lean_box(0), v___x_1240_);
return v___x_1250_;
}
else
{
size_t v___x_1251_; size_t v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = ((size_t)0ULL);
v___x_1252_ = lean_usize_of_nat(v___x_1239_);
v___x_1253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1234_, v___f_1246_, v_buckets_1237_, v___x_1251_, v___x_1252_, v___x_1240_);
return v___x_1253_;
}
}
else
{
size_t v___x_1254_; size_t v___x_1255_; lean_object* v___x_1256_; 
v___x_1254_ = ((size_t)0ULL);
v___x_1255_ = lean_usize_of_nat(v___x_1239_);
v___x_1256_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1234_, v___f_1246_, v_buckets_1237_, v___x_1254_, v___x_1255_, v___x_1240_);
return v___x_1256_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM(lean_object* v_00_u03b1_1257_, lean_object* v_00_u03b2_1258_, lean_object* v_x_1259_, lean_object* v_x_1260_, lean_object* v_m_1261_, lean_object* v_inst_1262_, lean_object* v_f_1263_, lean_object* v_b_1264_){
_start:
{
lean_object* v_buckets_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; uint8_t v___x_1269_; 
v_buckets_1265_ = lean_ctor_get(v_b_1264_, 1);
lean_inc_ref(v_buckets_1265_);
lean_dec_ref(v_b_1264_);
v___x_1266_ = lean_unsigned_to_nat(0u);
v___x_1267_ = lean_array_get_size(v_buckets_1265_);
v___x_1268_ = lean_box(0);
v___x_1269_ = lean_nat_dec_lt(v___x_1266_, v___x_1267_);
if (v___x_1269_ == 0)
{
lean_object* v_toApplicative_1270_; lean_object* v_toPure_1271_; lean_object* v___x_1272_; 
lean_dec_ref(v_buckets_1265_);
lean_dec(v_f_1263_);
v_toApplicative_1270_ = lean_ctor_get(v_inst_1262_, 0);
lean_inc_ref(v_toApplicative_1270_);
lean_dec_ref(v_inst_1262_);
v_toPure_1271_ = lean_ctor_get(v_toApplicative_1270_, 1);
lean_inc(v_toPure_1271_);
lean_dec_ref(v_toApplicative_1270_);
v___x_1272_ = lean_apply_2(v_toPure_1271_, lean_box(0), v___x_1268_);
return v___x_1272_;
}
else
{
lean_object* v___f_1273_; lean_object* v___f_1274_; uint8_t v___x_1275_; 
v___f_1273_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1273_, 0, v_f_1263_);
lean_inc_ref(v_inst_1262_);
v___f_1274_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1274_, 0, v_inst_1262_);
lean_closure_set(v___f_1274_, 1, v___f_1273_);
v___x_1275_ = lean_nat_dec_le(v___x_1267_, v___x_1267_);
if (v___x_1275_ == 0)
{
if (v___x_1269_ == 0)
{
lean_object* v_toApplicative_1276_; lean_object* v_toPure_1277_; lean_object* v___x_1278_; 
lean_dec_ref(v___f_1274_);
lean_dec_ref(v_buckets_1265_);
v_toApplicative_1276_ = lean_ctor_get(v_inst_1262_, 0);
lean_inc_ref(v_toApplicative_1276_);
lean_dec_ref(v_inst_1262_);
v_toPure_1277_ = lean_ctor_get(v_toApplicative_1276_, 1);
lean_inc(v_toPure_1277_);
lean_dec_ref(v_toApplicative_1276_);
v___x_1278_ = lean_apply_2(v_toPure_1277_, lean_box(0), v___x_1268_);
return v___x_1278_;
}
else
{
size_t v___x_1279_; size_t v___x_1280_; lean_object* v___x_1281_; 
v___x_1279_ = ((size_t)0ULL);
v___x_1280_ = lean_usize_of_nat(v___x_1267_);
v___x_1281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1262_, v___f_1274_, v_buckets_1265_, v___x_1279_, v___x_1280_, v___x_1268_);
return v___x_1281_;
}
}
else
{
size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v___x_1282_ = ((size_t)0ULL);
v___x_1283_ = lean_usize_of_nat(v___x_1267_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1262_, v___f_1274_, v_buckets_1265_, v___x_1282_, v___x_1283_, v___x_1268_);
return v___x_1284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___boxed(lean_object* v_00_u03b1_1285_, lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_, lean_object* v_x_1288_, lean_object* v_m_1289_, lean_object* v_inst_1290_, lean_object* v_f_1291_, lean_object* v_b_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l_Std_HashMap_forM(v_00_u03b1_1285_, v_00_u03b2_1286_, v_x_1287_, v_x_1288_, v_m_1289_, v_inst_1290_, v_f_1291_, v_b_1292_);
lean_dec_ref(v_x_1288_);
lean_dec_ref(v_x_1287_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg___lam__0(lean_object* v_inst_1294_, lean_object* v_f_1295_, lean_object* v_a_1296_, lean_object* v_x_1297_, lean_object* v___y_1298_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1294_, v_f_1295_, v_a_1296_, v___y_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg(lean_object* v_inst_1300_, lean_object* v_f_1301_, lean_object* v_init_1302_, lean_object* v_b_1303_){
_start:
{
lean_object* v_buckets_1304_; lean_object* v___f_1305_; size_t v_sz_1306_; size_t v___x_1307_; lean_object* v___x_1308_; 
v_buckets_1304_ = lean_ctor_get(v_b_1303_, 1);
lean_inc_ref(v_buckets_1304_);
lean_dec_ref(v_b_1303_);
lean_inc_ref(v_inst_1300_);
v___f_1305_ = lean_alloc_closure((void*)(l_Std_HashMap_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1305_, 0, v_inst_1300_);
lean_closure_set(v___f_1305_, 1, v_f_1301_);
v_sz_1306_ = lean_array_size(v_buckets_1304_);
v___x_1307_ = ((size_t)0ULL);
v___x_1308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1300_, v_buckets_1304_, v___f_1305_, v_sz_1306_, v___x_1307_, v_init_1302_);
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn(lean_object* v_00_u03b1_1309_, lean_object* v_00_u03b2_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_, lean_object* v_m_1313_, lean_object* v_inst_1314_, lean_object* v_00_u03b3_1315_, lean_object* v_f_1316_, lean_object* v_init_1317_, lean_object* v_b_1318_){
_start:
{
lean_object* v_buckets_1319_; lean_object* v___f_1320_; size_t v_sz_1321_; size_t v___x_1322_; lean_object* v___x_1323_; 
v_buckets_1319_ = lean_ctor_get(v_b_1318_, 1);
lean_inc_ref(v_buckets_1319_);
lean_dec_ref(v_b_1318_);
lean_inc_ref(v_inst_1314_);
v___f_1320_ = lean_alloc_closure((void*)(l_Std_HashMap_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1320_, 0, v_inst_1314_);
lean_closure_set(v___f_1320_, 1, v_f_1316_);
v_sz_1321_ = lean_array_size(v_buckets_1319_);
v___x_1322_ = ((size_t)0ULL);
v___x_1323_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1314_, v_buckets_1319_, v___f_1320_, v_sz_1321_, v___x_1322_, v_init_1317_);
return v___x_1323_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___boxed(lean_object* v_00_u03b1_1324_, lean_object* v_00_u03b2_1325_, lean_object* v_x_1326_, lean_object* v_x_1327_, lean_object* v_m_1328_, lean_object* v_inst_1329_, lean_object* v_00_u03b3_1330_, lean_object* v_f_1331_, lean_object* v_init_1332_, lean_object* v_b_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l_Std_HashMap_forIn(v_00_u03b1_1324_, v_00_u03b2_1325_, v_x_1326_, v_x_1327_, v_m_1328_, v_inst_1329_, v_00_u03b3_1330_, v_f_1331_, v_init_1332_, v_b_1333_);
lean_dec_ref(v_x_1327_);
lean_dec_ref(v_x_1326_);
return v_res_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1335_, lean_object* v_x_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1339_; lean_object* v___x_1340_; 
v___x_1339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___y_1337_);
lean_ctor_set(v___x_1339_, 1, v___y_1338_);
v___x_1340_ = lean_apply_1(v_f_1335_, v___x_1339_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1341_, lean_object* v_m_1342_, lean_object* v_f_1343_){
_start:
{
lean_object* v_buckets_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; 
v_buckets_1344_ = lean_ctor_get(v_m_1342_, 1);
lean_inc_ref(v_buckets_1344_);
lean_dec_ref(v_m_1342_);
v___x_1345_ = lean_unsigned_to_nat(0u);
v___x_1346_ = lean_array_get_size(v_buckets_1344_);
v___x_1347_ = lean_box(0);
v___x_1348_ = lean_nat_dec_lt(v___x_1345_, v___x_1346_);
if (v___x_1348_ == 0)
{
lean_object* v_toApplicative_1349_; lean_object* v_toPure_1350_; lean_object* v___x_1351_; 
lean_dec_ref(v_buckets_1344_);
lean_dec(v_f_1343_);
v_toApplicative_1349_ = lean_ctor_get(v_inst_1341_, 0);
lean_inc_ref(v_toApplicative_1349_);
lean_dec_ref(v_inst_1341_);
v_toPure_1350_ = lean_ctor_get(v_toApplicative_1349_, 1);
lean_inc(v_toPure_1350_);
lean_dec_ref(v_toApplicative_1349_);
v___x_1351_ = lean_apply_2(v_toPure_1350_, lean_box(0), v___x_1347_);
return v___x_1351_;
}
else
{
lean_object* v___f_1352_; lean_object* v___f_1353_; uint8_t v___x_1354_; 
v___f_1352_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1352_, 0, v_f_1343_);
lean_inc_ref(v_inst_1341_);
v___f_1353_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1353_, 0, v_inst_1341_);
lean_closure_set(v___f_1353_, 1, v___f_1352_);
v___x_1354_ = lean_nat_dec_le(v___x_1346_, v___x_1346_);
if (v___x_1354_ == 0)
{
if (v___x_1348_ == 0)
{
lean_object* v_toApplicative_1355_; lean_object* v_toPure_1356_; lean_object* v___x_1357_; 
lean_dec_ref(v___f_1353_);
lean_dec_ref(v_buckets_1344_);
v_toApplicative_1355_ = lean_ctor_get(v_inst_1341_, 0);
lean_inc_ref(v_toApplicative_1355_);
lean_dec_ref(v_inst_1341_);
v_toPure_1356_ = lean_ctor_get(v_toApplicative_1355_, 1);
lean_inc(v_toPure_1356_);
lean_dec_ref(v_toApplicative_1355_);
v___x_1357_ = lean_apply_2(v_toPure_1356_, lean_box(0), v___x_1347_);
return v___x_1357_;
}
else
{
size_t v___x_1358_; size_t v___x_1359_; lean_object* v___x_1360_; 
v___x_1358_ = ((size_t)0ULL);
v___x_1359_ = lean_usize_of_nat(v___x_1346_);
v___x_1360_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1341_, v___f_1353_, v_buckets_1344_, v___x_1358_, v___x_1359_, v___x_1347_);
return v___x_1360_;
}
}
else
{
size_t v___x_1361_; size_t v___x_1362_; lean_object* v___x_1363_; 
v___x_1361_ = ((size_t)0ULL);
v___x_1362_ = lean_usize_of_nat(v___x_1346_);
v___x_1363_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1341_, v___f_1353_, v_buckets_1344_, v___x_1361_, v___x_1362_, v___x_1347_);
return v___x_1363_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg(lean_object* v_inst_1364_){
_start:
{
lean_object* v___f_1365_; 
v___f_1365_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1365_, 0, v_inst_1364_);
return v___f_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad(lean_object* v_00_u03b1_1366_, lean_object* v_00_u03b2_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_m_1370_, lean_object* v_inst_1371_){
_start:
{
lean_object* v___f_1372_; 
v___f_1372_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1372_, 0, v_inst_1371_);
return v___f_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_1373_, lean_object* v_00_u03b2_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_m_1377_, lean_object* v_inst_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_HashMap_instForMProdOfMonad(v_00_u03b1_1373_, v_00_u03b2_1374_, v_inst_1375_, v_inst_1376_, v_m_1377_, v_inst_1378_);
lean_dec_ref(v_inst_1376_);
lean_dec_ref(v_inst_1375_);
return v_res_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1380_, lean_object* v_a_1381_, lean_object* v_b_1382_, lean_object* v_acc_1383_){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_a_1381_);
lean_ctor_set(v___x_1384_, 1, v_b_1382_);
v___x_1385_ = lean_apply_2(v_f_1380_, v___x_1384_, v_acc_1383_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1386_, lean_object* v___f_1387_, lean_object* v_a_1388_, lean_object* v_x_1389_, lean_object* v___y_1390_){
_start:
{
lean_object* v___x_1391_; 
v___x_1391_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1386_, v___f_1387_, v_a_1388_, v___y_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1392_, lean_object* v_00_u03b2_1393_, lean_object* v_m_1394_, lean_object* v_init_1395_, lean_object* v_f_1396_){
_start:
{
lean_object* v_buckets_1397_; lean_object* v___f_1398_; lean_object* v___f_1399_; size_t v_sz_1400_; size_t v___x_1401_; lean_object* v___x_1402_; 
v_buckets_1397_ = lean_ctor_get(v_m_1394_, 1);
lean_inc_ref(v_buckets_1397_);
lean_dec_ref(v_m_1394_);
v___f_1398_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1398_, 0, v_f_1396_);
lean_inc_ref(v_inst_1392_);
v___f_1399_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1399_, 0, v_inst_1392_);
lean_closure_set(v___f_1399_, 1, v___f_1398_);
v_sz_1400_ = lean_array_size(v_buckets_1397_);
v___x_1401_ = ((size_t)0ULL);
v___x_1402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1392_, v_buckets_1397_, v___f_1399_, v_sz_1400_, v___x_1401_, v_init_1395_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1403_){
_start:
{
lean_object* v___f_1404_; 
v___f_1404_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1404_, 0, v_inst_1403_);
return v___f_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad(lean_object* v_00_u03b1_1405_, lean_object* v_00_u03b2_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_m_1409_, lean_object* v_inst_1410_){
_start:
{
lean_object* v___f_1411_; 
v___f_1411_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1411_, 0, v_inst_1410_);
return v___f_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1412_, lean_object* v_00_u03b2_1413_, lean_object* v_inst_1414_, lean_object* v_inst_1415_, lean_object* v_m_1416_, lean_object* v_inst_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Std_HashMap_instForInProdOfMonad(v_00_u03b1_1412_, v_00_u03b2_1413_, v_inst_1414_, v_inst_1415_, v_m_1416_, v_inst_1417_);
lean_dec_ref(v_inst_1415_);
lean_dec_ref(v_inst_1414_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___redArg(lean_object* v_f_1419_, lean_object* v_m_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1419_, v_m_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter(lean_object* v_00_u03b1_1422_, lean_object* v_00_u03b2_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v_f_1426_, lean_object* v_m_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1426_, v_m_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___boxed(lean_object* v_00_u03b1_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_, lean_object* v_f_1433_, lean_object* v_m_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_Std_HashMap_filter(v_00_u03b1_1429_, v_00_u03b2_1430_, v_x_1431_, v_x_1432_, v_f_1433_, v_m_1434_);
lean_dec_ref(v_x_1432_);
lean_dec_ref(v_x_1431_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify___redArg(lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v_m_1438_, lean_object* v_a_1439_, lean_object* v_f_1440_){
_start:
{
lean_object* v___x_1441_; 
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1436_, v_x_1437_, v_m_1438_, v_a_1439_, v_f_1440_);
return v___x_1441_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify(lean_object* v_00_u03b1_1442_, lean_object* v_00_u03b2_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v_m_1446_, lean_object* v_a_1447_, lean_object* v_f_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1444_, v_x_1445_, v_m_1446_, v_a_1447_, v_f_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter___redArg(lean_object* v_x_1450_, lean_object* v_x_1451_, lean_object* v_m_1452_, lean_object* v_a_1453_, lean_object* v_f_1454_){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1450_, v_x_1451_, v_m_1452_, v_a_1453_, v_f_1454_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter(lean_object* v_00_u03b1_1456_, lean_object* v_00_u03b2_1457_, lean_object* v_x_1458_, lean_object* v_x_1459_, lean_object* v_m_1460_, lean_object* v_a_1461_, lean_object* v_f_1462_){
_start:
{
lean_object* v___x_1463_; 
v___x_1463_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1458_, v_x_1459_, v_m_1460_, v_a_1461_, v_f_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany___redArg(lean_object* v_x_1464_, lean_object* v_x_1465_, lean_object* v_inst_1466_, lean_object* v_m_1467_, lean_object* v_l_1468_){
_start:
{
lean_object* v___x_1469_; 
v___x_1469_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_1466_, v_x_1464_, v_x_1465_, v_m_1467_, v_l_1468_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany(lean_object* v_00_u03b1_1470_, lean_object* v_00_u03b2_1471_, lean_object* v_x_1472_, lean_object* v_x_1473_, lean_object* v_00_u03c1_1474_, lean_object* v_inst_1475_, lean_object* v_m_1476_, lean_object* v_l_1477_){
_start:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_1475_, v_x_1472_, v_x_1473_, v_m_1476_, v_l_1477_);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit___redArg(lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_inst_1481_, lean_object* v_m_1482_, lean_object* v_l_1483_){
_start:
{
lean_object* v___x_1484_; 
v___x_1484_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1481_, v_x_1479_, v_x_1480_, v_m_1482_, v_l_1483_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit(lean_object* v_00_u03b1_1485_, lean_object* v_x_1486_, lean_object* v_x_1487_, lean_object* v_00_u03c1_1488_, lean_object* v_inst_1489_, lean_object* v_m_1490_, lean_object* v_l_1491_){
_start:
{
lean_object* v___x_1492_; 
v___x_1492_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1489_, v_x_1486_, v_x_1487_, v_m_1490_, v_l_1491_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__0(lean_object* v_x1_1493_, lean_object* v_x2_1494_, lean_object* v_x3_1495_){
_start:
{
lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1496_, 0, v_x2_1494_);
lean_ctor_set(v___x_1496_, 1, v_x3_1495_);
v___x_1497_ = lean_array_push(v_x1_1493_, v___x_1496_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__1(lean_object* v___x_1498_, lean_object* v___f_1499_, lean_object* v_acc_1500_, lean_object* v_l_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1498_, v___f_1499_, v_acc_1500_, v_l_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg(lean_object* v_m_1507_){
_start:
{
lean_object* v_size_1508_; lean_object* v_buckets_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_size_1508_ = lean_ctor_get(v_m_1507_, 0);
lean_inc(v_size_1508_);
v_buckets_1509_ = lean_ctor_get(v_m_1507_, 1);
lean_inc_ref(v_buckets_1509_);
lean_dec_ref(v_m_1507_);
v___x_1510_ = lean_mk_empty_array_with_capacity(v_size_1508_);
lean_dec(v_size_1508_);
v___x_1511_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = lean_array_get_size(v_buckets_1509_);
v___x_1514_ = lean_nat_dec_lt(v___x_1512_, v___x_1513_);
if (v___x_1514_ == 0)
{
lean_dec_ref(v_buckets_1509_);
return v___x_1510_;
}
else
{
lean_object* v___f_1515_; uint8_t v___x_1516_; 
v___f_1515_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__1));
v___x_1516_ = lean_nat_dec_le(v___x_1513_, v___x_1513_);
if (v___x_1516_ == 0)
{
if (v___x_1514_ == 0)
{
lean_dec_ref(v_buckets_1509_);
return v___x_1510_;
}
else
{
size_t v___x_1517_; size_t v___x_1518_; lean_object* v___x_1519_; 
v___x_1517_ = ((size_t)0ULL);
v___x_1518_ = lean_usize_of_nat(v___x_1513_);
v___x_1519_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1511_, v___f_1515_, v_buckets_1509_, v___x_1517_, v___x_1518_, v___x_1510_);
return v___x_1519_;
}
}
else
{
size_t v___x_1520_; size_t v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = ((size_t)0ULL);
v___x_1521_ = lean_usize_of_nat(v___x_1513_);
v___x_1522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1511_, v___f_1515_, v_buckets_1509_, v___x_1520_, v___x_1521_, v___x_1510_);
return v___x_1522_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray(lean_object* v_00_u03b1_1523_, lean_object* v_00_u03b2_1524_, lean_object* v_x_1525_, lean_object* v_x_1526_, lean_object* v_m_1527_){
_start:
{
lean_object* v_size_1528_; lean_object* v_buckets_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v_size_1528_ = lean_ctor_get(v_m_1527_, 0);
lean_inc(v_size_1528_);
v_buckets_1529_ = lean_ctor_get(v_m_1527_, 1);
lean_inc_ref(v_buckets_1529_);
lean_dec_ref(v_m_1527_);
v___x_1530_ = lean_mk_empty_array_with_capacity(v_size_1528_);
lean_dec(v_size_1528_);
v___x_1531_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = lean_array_get_size(v_buckets_1529_);
v___x_1534_ = lean_nat_dec_lt(v___x_1532_, v___x_1533_);
if (v___x_1534_ == 0)
{
lean_dec_ref(v_buckets_1529_);
return v___x_1530_;
}
else
{
lean_object* v___f_1535_; uint8_t v___x_1536_; 
v___f_1535_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__1));
v___x_1536_ = lean_nat_dec_le(v___x_1533_, v___x_1533_);
if (v___x_1536_ == 0)
{
if (v___x_1534_ == 0)
{
lean_dec_ref(v_buckets_1529_);
return v___x_1530_;
}
else
{
size_t v___x_1537_; size_t v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = ((size_t)0ULL);
v___x_1538_ = lean_usize_of_nat(v___x_1533_);
v___x_1539_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1531_, v___f_1535_, v_buckets_1529_, v___x_1537_, v___x_1538_, v___x_1530_);
return v___x_1539_;
}
}
else
{
size_t v___x_1540_; size_t v___x_1541_; lean_object* v___x_1542_; 
v___x_1540_ = ((size_t)0ULL);
v___x_1541_ = lean_usize_of_nat(v___x_1533_);
v___x_1542_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1531_, v___f_1535_, v_buckets_1529_, v___x_1540_, v___x_1541_, v___x_1530_);
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___boxed(lean_object* v_00_u03b1_1543_, lean_object* v_00_u03b2_1544_, lean_object* v_x_1545_, lean_object* v_x_1546_, lean_object* v_m_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l_Std_HashMap_toArray(v_00_u03b1_1543_, v_00_u03b2_1544_, v_x_1545_, v_x_1546_, v_m_1547_);
lean_dec_ref(v_x_1546_);
lean_dec_ref(v_x_1545_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0(lean_object* v_x1_1549_, lean_object* v_x2_1550_, lean_object* v_x3_1551_){
_start:
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_array_push(v_x1_1549_, v_x2_1550_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1553_, lean_object* v_x2_1554_, lean_object* v_x3_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Std_HashMap_keysArray___redArg___lam__0(v_x1_1553_, v_x2_1554_, v_x3_1555_);
lean_dec(v_x3_1555_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__1(lean_object* v___x_1557_, lean_object* v___f_1558_, lean_object* v_acc_1559_, lean_object* v_l_1560_){
_start:
{
lean_object* v___x_1561_; 
v___x_1561_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1557_, v___f_1558_, v_acc_1559_, v_l_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg(lean_object* v_m_1566_){
_start:
{
lean_object* v_size_1567_; lean_object* v_buckets_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; uint8_t v___x_1573_; 
v_size_1567_ = lean_ctor_get(v_m_1566_, 0);
lean_inc(v_size_1567_);
v_buckets_1568_ = lean_ctor_get(v_m_1566_, 1);
lean_inc_ref(v_buckets_1568_);
lean_dec_ref(v_m_1566_);
v___x_1569_ = lean_mk_empty_array_with_capacity(v_size_1567_);
lean_dec(v_size_1567_);
v___x_1570_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = lean_array_get_size(v_buckets_1568_);
v___x_1573_ = lean_nat_dec_lt(v___x_1571_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_dec_ref(v_buckets_1568_);
return v___x_1569_;
}
else
{
lean_object* v___f_1574_; uint8_t v___x_1575_; 
v___f_1574_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__1));
v___x_1575_ = lean_nat_dec_le(v___x_1572_, v___x_1572_);
if (v___x_1575_ == 0)
{
if (v___x_1573_ == 0)
{
lean_dec_ref(v_buckets_1568_);
return v___x_1569_;
}
else
{
size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = lean_usize_of_nat(v___x_1572_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1570_, v___f_1574_, v_buckets_1568_, v___x_1576_, v___x_1577_, v___x_1569_);
return v___x_1578_;
}
}
else
{
size_t v___x_1579_; size_t v___x_1580_; lean_object* v___x_1581_; 
v___x_1579_ = ((size_t)0ULL);
v___x_1580_ = lean_usize_of_nat(v___x_1572_);
v___x_1581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1570_, v___f_1574_, v_buckets_1568_, v___x_1579_, v___x_1580_, v___x_1569_);
return v___x_1581_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray(lean_object* v_00_u03b1_1582_, lean_object* v_00_u03b2_1583_, lean_object* v_x_1584_, lean_object* v_x_1585_, lean_object* v_m_1586_){
_start:
{
lean_object* v_size_1587_; lean_object* v_buckets_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; uint8_t v___x_1593_; 
v_size_1587_ = lean_ctor_get(v_m_1586_, 0);
lean_inc(v_size_1587_);
v_buckets_1588_ = lean_ctor_get(v_m_1586_, 1);
lean_inc_ref(v_buckets_1588_);
lean_dec_ref(v_m_1586_);
v___x_1589_ = lean_mk_empty_array_with_capacity(v_size_1587_);
lean_dec(v_size_1587_);
v___x_1590_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1591_ = lean_unsigned_to_nat(0u);
v___x_1592_ = lean_array_get_size(v_buckets_1588_);
v___x_1593_ = lean_nat_dec_lt(v___x_1591_, v___x_1592_);
if (v___x_1593_ == 0)
{
lean_dec_ref(v_buckets_1588_);
return v___x_1589_;
}
else
{
lean_object* v___f_1594_; uint8_t v___x_1595_; 
v___f_1594_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__1));
v___x_1595_ = lean_nat_dec_le(v___x_1592_, v___x_1592_);
if (v___x_1595_ == 0)
{
if (v___x_1593_ == 0)
{
lean_dec_ref(v_buckets_1588_);
return v___x_1589_;
}
else
{
size_t v___x_1596_; size_t v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = ((size_t)0ULL);
v___x_1597_ = lean_usize_of_nat(v___x_1592_);
v___x_1598_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1590_, v___f_1594_, v_buckets_1588_, v___x_1596_, v___x_1597_, v___x_1589_);
return v___x_1598_;
}
}
else
{
size_t v___x_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = lean_usize_of_nat(v___x_1592_);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1590_, v___f_1594_, v_buckets_1588_, v___x_1599_, v___x_1600_, v___x_1589_);
return v___x_1601_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___boxed(lean_object* v_00_u03b1_1602_, lean_object* v_00_u03b2_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_, lean_object* v_m_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Std_HashMap_keysArray(v_00_u03b1_1602_, v_00_u03b2_1603_, v_x_1604_, v_x_1605_, v_m_1606_);
lean_dec_ref(v_x_1605_);
lean_dec_ref(v_x_1604_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0(lean_object* v_p_1608_, lean_object* v___x_1609_, lean_object* v___x_1610_, lean_object* v_a_1611_, lean_object* v_b_1612_, lean_object* v_acc_1613_){
_start:
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = lean_apply_2(v_p_1608_, v_a_1611_, v_b_1612_);
v___x_1615_ = lean_unbox(v___x_1614_);
if (v___x_1615_ == 0)
{
lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
lean_dec_ref(v___x_1610_);
v___x_1616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1614_);
v___x_1617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1617_, 0, v___x_1616_);
lean_ctor_set(v___x_1617_, 1, v___x_1609_);
v___x_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1618_, 0, v___x_1617_);
return v___x_1618_;
}
else
{
lean_object* v___x_1619_; 
v___x_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1619_, 0, v___x_1610_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0___boxed(lean_object* v_p_1620_, lean_object* v___x_1621_, lean_object* v___x_1622_, lean_object* v_a_1623_, lean_object* v_b_1624_, lean_object* v_acc_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_Std_HashMap_all___redArg___lam__0(v_p_1620_, v___x_1621_, v___x_1622_, v_a_1623_, v_b_1624_, v_acc_1625_);
lean_dec_ref(v_acc_1625_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__1(lean_object* v___x_1627_, lean_object* v___f_1628_, lean_object* v_a_1629_, lean_object* v_x_1630_, lean_object* v___y_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1627_, v___f_1628_, v_a_1629_, v___y_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_all___redArg(lean_object* v_m_1636_, lean_object* v_p_1637_){
_start:
{
lean_object* v___x_1638_; lean_object* v_buckets_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___f_1642_; lean_object* v___f_1643_; size_t v_sz_1644_; size_t v___x_1645_; lean_object* v___x_1646_; lean_object* v_fst_1647_; 
v___x_1638_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1639_ = lean_ctor_get(v_m_1636_, 1);
lean_inc_ref(v_buckets_1639_);
lean_dec_ref(v_m_1636_);
v___x_1640_ = lean_box(0);
v___x_1641_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1642_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1642_, 0, v_p_1637_);
lean_closure_set(v___f_1642_, 1, v___x_1640_);
lean_closure_set(v___f_1642_, 2, v___x_1641_);
v___f_1643_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1643_, 0, v___x_1638_);
lean_closure_set(v___f_1643_, 1, v___f_1642_);
v_sz_1644_ = lean_array_size(v_buckets_1639_);
v___x_1645_ = ((size_t)0ULL);
v___x_1646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1638_, v_buckets_1639_, v___f_1643_, v_sz_1644_, v___x_1645_, v___x_1641_);
v_fst_1647_ = lean_ctor_get(v___x_1646_, 0);
lean_inc(v_fst_1647_);
lean_dec(v___x_1646_);
if (lean_obj_tag(v_fst_1647_) == 0)
{
uint8_t v___x_1648_; 
v___x_1648_ = 1;
return v___x_1648_;
}
else
{
lean_object* v_val_1649_; uint8_t v___x_1650_; 
v_val_1649_ = lean_ctor_get(v_fst_1647_, 0);
lean_inc(v_val_1649_);
lean_dec_ref(v_fst_1647_);
v___x_1650_ = lean_unbox(v_val_1649_);
lean_dec(v_val_1649_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___boxed(lean_object* v_m_1651_, lean_object* v_p_1652_){
_start:
{
uint8_t v_res_1653_; lean_object* v_r_1654_; 
v_res_1653_ = l_Std_HashMap_all___redArg(v_m_1651_, v_p_1652_);
v_r_1654_ = lean_box(v_res_1653_);
return v_r_1654_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_all(lean_object* v_00_u03b1_1655_, lean_object* v_00_u03b2_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_, lean_object* v_m_1659_, lean_object* v_p_1660_){
_start:
{
lean_object* v___x_1661_; lean_object* v_buckets_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___f_1665_; lean_object* v___f_1666_; size_t v_sz_1667_; size_t v___x_1668_; lean_object* v___x_1669_; lean_object* v_fst_1670_; 
v___x_1661_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1662_ = lean_ctor_get(v_m_1659_, 1);
lean_inc_ref(v_buckets_1662_);
lean_dec_ref(v_m_1659_);
v___x_1663_ = lean_box(0);
v___x_1664_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1665_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1665_, 0, v_p_1660_);
lean_closure_set(v___f_1665_, 1, v___x_1663_);
lean_closure_set(v___f_1665_, 2, v___x_1664_);
v___f_1666_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1666_, 0, v___x_1661_);
lean_closure_set(v___f_1666_, 1, v___f_1665_);
v_sz_1667_ = lean_array_size(v_buckets_1662_);
v___x_1668_ = ((size_t)0ULL);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1661_, v_buckets_1662_, v___f_1666_, v_sz_1667_, v___x_1668_, v___x_1664_);
v_fst_1670_ = lean_ctor_get(v___x_1669_, 0);
lean_inc(v_fst_1670_);
lean_dec(v___x_1669_);
if (lean_obj_tag(v_fst_1670_) == 0)
{
uint8_t v___x_1671_; 
v___x_1671_ = 1;
return v___x_1671_;
}
else
{
lean_object* v_val_1672_; uint8_t v___x_1673_; 
v_val_1672_ = lean_ctor_get(v_fst_1670_, 0);
lean_inc(v_val_1672_);
lean_dec_ref(v_fst_1670_);
v___x_1673_ = lean_unbox(v_val_1672_);
lean_dec(v_val_1672_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___boxed(lean_object* v_00_u03b1_1674_, lean_object* v_00_u03b2_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_, lean_object* v_m_1678_, lean_object* v_p_1679_){
_start:
{
uint8_t v_res_1680_; lean_object* v_r_1681_; 
v_res_1680_ = l_Std_HashMap_all(v_00_u03b1_1674_, v_00_u03b2_1675_, v_x_1676_, v_x_1677_, v_m_1678_, v_p_1679_);
lean_dec_ref(v_x_1677_);
lean_dec_ref(v_x_1676_);
v_r_1681_ = lean_box(v_res_1680_);
return v_r_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0(lean_object* v_p_1682_, lean_object* v___x_1683_, lean_object* v___x_1684_, lean_object* v_a_1685_, lean_object* v_b_1686_, lean_object* v_acc_1687_){
_start:
{
lean_object* v___x_1688_; uint8_t v___x_1689_; 
v___x_1688_ = lean_apply_2(v_p_1682_, v_a_1685_, v_b_1686_);
v___x_1689_ = lean_unbox(v___x_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1683_);
return v___x_1690_;
}
else
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
lean_dec_ref(v___x_1683_);
v___x_1691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1691_, 0, v___x_1688_);
v___x_1692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1691_);
lean_ctor_set(v___x_1692_, 1, v___x_1684_);
v___x_1693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1692_);
return v___x_1693_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0___boxed(lean_object* v_p_1694_, lean_object* v___x_1695_, lean_object* v___x_1696_, lean_object* v_a_1697_, lean_object* v_b_1698_, lean_object* v_acc_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_HashMap_any___redArg___lam__0(v_p_1694_, v___x_1695_, v___x_1696_, v_a_1697_, v_b_1698_, v_acc_1699_);
lean_dec_ref(v_acc_1699_);
return v_res_1700_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_any___redArg(lean_object* v_m_1701_, lean_object* v_p_1702_){
_start:
{
lean_object* v___x_1703_; lean_object* v_buckets_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___f_1707_; lean_object* v___f_1708_; size_t v_sz_1709_; size_t v___x_1710_; lean_object* v___x_1711_; lean_object* v_fst_1712_; 
v___x_1703_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1704_ = lean_ctor_get(v_m_1701_, 1);
lean_inc_ref(v_buckets_1704_);
lean_dec_ref(v_m_1701_);
v___x_1705_ = lean_box(0);
v___x_1706_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1707_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1707_, 0, v_p_1702_);
lean_closure_set(v___f_1707_, 1, v___x_1706_);
lean_closure_set(v___f_1707_, 2, v___x_1705_);
v___f_1708_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1708_, 0, v___x_1703_);
lean_closure_set(v___f_1708_, 1, v___f_1707_);
v_sz_1709_ = lean_array_size(v_buckets_1704_);
v___x_1710_ = ((size_t)0ULL);
v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1703_, v_buckets_1704_, v___f_1708_, v_sz_1709_, v___x_1710_, v___x_1706_);
v_fst_1712_ = lean_ctor_get(v___x_1711_, 0);
lean_inc(v_fst_1712_);
lean_dec(v___x_1711_);
if (lean_obj_tag(v_fst_1712_) == 0)
{
uint8_t v___x_1713_; 
v___x_1713_ = 0;
return v___x_1713_;
}
else
{
lean_object* v_val_1714_; uint8_t v___x_1715_; 
v_val_1714_ = lean_ctor_get(v_fst_1712_, 0);
lean_inc(v_val_1714_);
lean_dec_ref(v_fst_1712_);
v___x_1715_ = lean_unbox(v_val_1714_);
lean_dec(v_val_1714_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___boxed(lean_object* v_m_1716_, lean_object* v_p_1717_){
_start:
{
uint8_t v_res_1718_; lean_object* v_r_1719_; 
v_res_1718_ = l_Std_HashMap_any___redArg(v_m_1716_, v_p_1717_);
v_r_1719_ = lean_box(v_res_1718_);
return v_r_1719_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_any(lean_object* v_00_u03b1_1720_, lean_object* v_00_u03b2_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_, lean_object* v_m_1724_, lean_object* v_p_1725_){
_start:
{
lean_object* v___x_1726_; lean_object* v_buckets_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___f_1730_; lean_object* v___f_1731_; size_t v_sz_1732_; size_t v___x_1733_; lean_object* v___x_1734_; lean_object* v_fst_1735_; 
v___x_1726_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1727_ = lean_ctor_get(v_m_1724_, 1);
lean_inc_ref(v_buckets_1727_);
lean_dec_ref(v_m_1724_);
v___x_1728_ = lean_box(0);
v___x_1729_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1730_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1730_, 0, v_p_1725_);
lean_closure_set(v___f_1730_, 1, v___x_1729_);
lean_closure_set(v___f_1730_, 2, v___x_1728_);
v___f_1731_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1731_, 0, v___x_1726_);
lean_closure_set(v___f_1731_, 1, v___f_1730_);
v_sz_1732_ = lean_array_size(v_buckets_1727_);
v___x_1733_ = ((size_t)0ULL);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1726_, v_buckets_1727_, v___f_1731_, v_sz_1732_, v___x_1733_, v___x_1729_);
v_fst_1735_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_fst_1735_);
lean_dec(v___x_1734_);
if (lean_obj_tag(v_fst_1735_) == 0)
{
uint8_t v___x_1736_; 
v___x_1736_ = 0;
return v___x_1736_;
}
else
{
lean_object* v_val_1737_; uint8_t v___x_1738_; 
v_val_1737_ = lean_ctor_get(v_fst_1735_, 0);
lean_inc(v_val_1737_);
lean_dec_ref(v_fst_1735_);
v___x_1738_ = lean_unbox(v_val_1737_);
lean_dec(v_val_1737_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___boxed(lean_object* v_00_u03b1_1739_, lean_object* v_00_u03b2_1740_, lean_object* v_x_1741_, lean_object* v_x_1742_, lean_object* v_m_1743_, lean_object* v_p_1744_){
_start:
{
uint8_t v_res_1745_; lean_object* v_r_1746_; 
v_res_1745_ = l_Std_HashMap_any(v_00_u03b1_1739_, v_00_u03b2_1740_, v_x_1741_, v_x_1742_, v_m_1743_, v_p_1744_);
lean_dec_ref(v_x_1742_);
lean_dec_ref(v_x_1741_);
v_r_1746_ = lean_box(v_res_1745_);
return v_r_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__0(lean_object* v_inst_1747_, lean_object* v_inst_1748_, lean_object* v_a_1749_, lean_object* v_b_1750_, lean_object* v_acc_1751_){
_start:
{
lean_object* v_r_1752_; lean_object* v___x_1753_; 
v_r_1752_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1747_, v_inst_1748_, v_acc_1751_, v_a_1749_, v_b_1750_);
v___x_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1753_, 0, v_r_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__1(lean_object* v___x_1754_, lean_object* v___f_1755_, lean_object* v_a_1756_, lean_object* v_x_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1754_, v___f_1755_, v_a_1756_, v___y_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg(lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_m_u2081_1764_, lean_object* v_m_u2082_1765_){
_start:
{
lean_object* v_size_1766_; lean_object* v_buckets_1767_; lean_object* v_size_1768_; uint8_t v___x_1769_; 
v_size_1766_ = lean_ctor_get(v_m_u2081_1764_, 0);
v_buckets_1767_ = lean_ctor_get(v_m_u2081_1764_, 1);
v_size_1768_ = lean_ctor_get(v_m_u2082_1765_, 0);
v___x_1769_ = lean_nat_dec_le(v_size_1766_, v_size_1768_);
if (v___x_1769_ == 0)
{
lean_object* v___f_1770_; lean_object* v___x_1771_; 
v___f_1770_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1771_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1770_, v_inst_1762_, v_inst_1763_, v_m_u2081_1764_, v_m_u2082_1765_);
return v___x_1771_;
}
else
{
lean_object* v___f_1772_; lean_object* v___x_1773_; lean_object* v___f_1774_; size_t v_sz_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
lean_inc_ref(v_buckets_1767_);
lean_dec_ref(v_m_u2081_1764_);
v___f_1772_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1772_, 0, v_inst_1762_);
lean_closure_set(v___f_1772_, 1, v_inst_1763_);
v___x_1773_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___f_1774_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1774_, 0, v___x_1773_);
lean_closure_set(v___f_1774_, 1, v___f_1772_);
v_sz_1775_ = lean_array_size(v_buckets_1767_);
v___x_1776_ = ((size_t)0ULL);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1773_, v_buckets_1767_, v___f_1774_, v_sz_1775_, v___x_1776_, v_m_u2082_1765_);
return v___x_1777_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union(lean_object* v_00_u03b1_1778_, lean_object* v_00_u03b2_1779_, lean_object* v_inst_1780_, lean_object* v_inst_1781_, lean_object* v_m_u2081_1782_, lean_object* v_m_u2082_1783_){
_start:
{
lean_object* v_size_1784_; lean_object* v_buckets_1785_; lean_object* v_size_1786_; uint8_t v___x_1787_; 
v_size_1784_ = lean_ctor_get(v_m_u2081_1782_, 0);
v_buckets_1785_ = lean_ctor_get(v_m_u2081_1782_, 1);
v_size_1786_ = lean_ctor_get(v_m_u2082_1783_, 0);
v___x_1787_ = lean_nat_dec_le(v_size_1784_, v_size_1786_);
if (v___x_1787_ == 0)
{
lean_object* v___f_1788_; lean_object* v___x_1789_; 
v___f_1788_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1789_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1788_, v_inst_1780_, v_inst_1781_, v_m_u2081_1782_, v_m_u2082_1783_);
return v___x_1789_;
}
else
{
lean_object* v___f_1790_; lean_object* v___x_1791_; lean_object* v___f_1792_; size_t v_sz_1793_; size_t v___x_1794_; lean_object* v___x_1795_; 
lean_inc_ref(v_buckets_1785_);
lean_dec_ref(v_m_u2081_1782_);
v___f_1790_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1790_, 0, v_inst_1780_);
lean_closure_set(v___f_1790_, 1, v_inst_1781_);
v___x_1791_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___f_1792_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1792_, 0, v___x_1791_);
lean_closure_set(v___f_1792_, 1, v___f_1790_);
v_sz_1793_ = lean_array_size(v_buckets_1785_);
v___x_1794_ = ((size_t)0ULL);
v___x_1795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1791_, v_buckets_1785_, v___f_1792_, v_sz_1793_, v___x_1794_, v_m_u2082_1783_);
return v___x_1795_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion___redArg(lean_object* v_inst_1796_, lean_object* v_inst_1797_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_alloc_closure((void*)(l_Std_HashMap_union), 6, 4);
lean_closure_set(v___x_1798_, 0, lean_box(0));
lean_closure_set(v___x_1798_, 1, lean_box(0));
lean_closure_set(v___x_1798_, 2, v_inst_1796_);
lean_closure_set(v___x_1798_, 3, v_inst_1797_);
return v___x_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion(lean_object* v_00_u03b1_1799_, lean_object* v_00_u03b2_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = lean_alloc_closure((void*)(l_Std_HashMap_union), 6, 4);
lean_closure_set(v___x_1803_, 0, lean_box(0));
lean_closure_set(v___x_1803_, 1, lean_box(0));
lean_closure_set(v___x_1803_, 2, v_inst_1801_);
lean_closure_set(v___x_1803_, 3, v_inst_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_inter___redArg(lean_object* v_inst_1804_, lean_object* v_inst_1805_, lean_object* v_m_u2081_1806_, lean_object* v_m_u2082_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1804_, v_inst_1805_, v_m_u2081_1806_, v_m_u2082_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_inter(lean_object* v_00_u03b1_1809_, lean_object* v_00_u03b2_1810_, lean_object* v_inst_1811_, lean_object* v_inst_1812_, lean_object* v_m_u2081_1813_, lean_object* v_m_u2082_1814_){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1811_, v_inst_1812_, v_m_u2081_1813_, v_m_u2082_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInter___redArg(lean_object* v_inst_1816_, lean_object* v_inst_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = lean_alloc_closure((void*)(l_Std_HashMap_inter), 6, 4);
lean_closure_set(v___x_1818_, 0, lean_box(0));
lean_closure_set(v___x_1818_, 1, lean_box(0));
lean_closure_set(v___x_1818_, 2, v_inst_1816_);
lean_closure_set(v___x_1818_, 3, v_inst_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInter(lean_object* v_00_u03b1_1819_, lean_object* v_00_u03b2_1820_, lean_object* v_inst_1821_, lean_object* v_inst_1822_){
_start:
{
lean_object* v___x_1823_; 
v___x_1823_ = lean_alloc_closure((void*)(l_Std_HashMap_inter), 6, 4);
lean_closure_set(v___x_1823_, 0, lean_box(0));
lean_closure_set(v___x_1823_, 1, lean_box(0));
lean_closure_set(v___x_1823_, 2, v_inst_1821_);
lean_closure_set(v___x_1823_, 3, v_inst_1822_);
return v___x_1823_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq___redArg(lean_object* v_x_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_m_u2081_1827_, lean_object* v_m_u2082_1828_){
_start:
{
uint8_t v___x_1829_; 
v___x_1829_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1825_, v_x_1824_, v_inst_1826_, v_m_u2081_1827_, v_m_u2082_1828_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___redArg___boxed(lean_object* v_x_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_m_u2081_1833_, lean_object* v_m_u2082_1834_){
_start:
{
uint8_t v_res_1835_; lean_object* v_r_1836_; 
v_res_1835_ = l_Std_HashMap_beq___redArg(v_x_1830_, v_inst_1831_, v_inst_1832_, v_m_u2081_1833_, v_m_u2082_1834_);
v_r_1836_ = lean_box(v_res_1835_);
return v_r_1836_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq(lean_object* v_00_u03b1_1837_, lean_object* v_x_1838_, lean_object* v_00_u03b2_1839_, lean_object* v_inst_1840_, lean_object* v_inst_1841_, lean_object* v_m_u2081_1842_, lean_object* v_m_u2082_1843_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1840_, v_x_1838_, v_inst_1841_, v_m_u2081_1842_, v_m_u2082_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___boxed(lean_object* v_00_u03b1_1845_, lean_object* v_x_1846_, lean_object* v_00_u03b2_1847_, lean_object* v_inst_1848_, lean_object* v_inst_1849_, lean_object* v_m_u2081_1850_, lean_object* v_m_u2082_1851_){
_start:
{
uint8_t v_res_1852_; lean_object* v_r_1853_; 
v_res_1852_ = l_Std_HashMap_beq(v_00_u03b1_1845_, v_x_1846_, v_00_u03b2_1847_, v_inst_1848_, v_inst_1849_, v_m_u2081_1850_, v_m_u2082_1851_);
v_r_1853_ = lean_box(v_res_1852_);
return v_r_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq___redArg(lean_object* v_x_1854_, lean_object* v_inst_1855_, lean_object* v_inst_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_1857_, 0, lean_box(0));
lean_closure_set(v___x_1857_, 1, v_x_1854_);
lean_closure_set(v___x_1857_, 2, lean_box(0));
lean_closure_set(v___x_1857_, 3, v_inst_1855_);
lean_closure_set(v___x_1857_, 4, v_inst_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq(lean_object* v_00_u03b1_1858_, lean_object* v_00_u03b2_1859_, lean_object* v_x_1860_, lean_object* v_inst_1861_, lean_object* v_inst_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_1863_, 0, lean_box(0));
lean_closure_set(v___x_1863_, 1, v_x_1860_);
lean_closure_set(v___x_1863_, 2, lean_box(0));
lean_closure_set(v___x_1863_, 3, v_inst_1861_);
lean_closure_set(v___x_1863_, 4, v_inst_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_diff___redArg___lam__0(lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_m_u2082_1866_, uint8_t v___x_1867_, lean_object* v_k_1868_, lean_object* v_x_1869_){
_start:
{
uint8_t v___x_1870_; 
v___x_1870_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1864_, v_inst_1865_, v_m_u2082_1866_, v_k_1868_);
if (v___x_1870_ == 0)
{
return v___x_1867_;
}
else
{
uint8_t v___x_1871_; 
v___x_1871_ = 0;
return v___x_1871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg___lam__0___boxed(lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_m_u2082_1874_, lean_object* v___x_1875_, lean_object* v_k_1876_, lean_object* v_x_1877_){
_start:
{
uint8_t v___x_80__boxed_1878_; uint8_t v_res_1879_; lean_object* v_r_1880_; 
v___x_80__boxed_1878_ = lean_unbox(v___x_1875_);
v_res_1879_ = l_Std_HashMap_diff___redArg___lam__0(v_inst_1872_, v_inst_1873_, v_m_u2082_1874_, v___x_80__boxed_1878_, v_k_1876_, v_x_1877_);
lean_dec(v_x_1877_);
lean_dec_ref(v_m_u2082_1874_);
v_r_1880_ = lean_box(v_res_1879_);
return v_r_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg(lean_object* v_inst_1881_, lean_object* v_inst_1882_, lean_object* v_m_u2081_1883_, lean_object* v_m_u2082_1884_){
_start:
{
lean_object* v_size_1885_; lean_object* v_size_1886_; uint8_t v___x_1887_; 
v_size_1885_ = lean_ctor_get(v_m_u2081_1883_, 0);
v_size_1886_ = lean_ctor_get(v_m_u2082_1884_, 0);
v___x_1887_ = lean_nat_dec_le(v_size_1885_, v_size_1886_);
if (v___x_1887_ == 0)
{
lean_object* v___f_1888_; lean_object* v___x_1889_; 
v___f_1888_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1889_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1888_, v_inst_1881_, v_inst_1882_, v_m_u2081_1883_, v_m_u2082_1884_);
return v___x_1889_;
}
else
{
lean_object* v___x_1890_; lean_object* v___f_1891_; lean_object* v___x_1892_; 
v___x_1890_ = lean_box(v___x_1887_);
v___f_1891_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1891_, 0, v_inst_1881_);
lean_closure_set(v___f_1891_, 1, v_inst_1882_);
lean_closure_set(v___f_1891_, 2, v_m_u2082_1884_);
lean_closure_set(v___f_1891_, 3, v___x_1890_);
v___x_1892_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1891_, v_m_u2081_1883_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff(lean_object* v_00_u03b1_1893_, lean_object* v_00_u03b2_1894_, lean_object* v_inst_1895_, lean_object* v_inst_1896_, lean_object* v_m_u2081_1897_, lean_object* v_m_u2082_1898_){
_start:
{
lean_object* v_size_1899_; lean_object* v_size_1900_; uint8_t v___x_1901_; 
v_size_1899_ = lean_ctor_get(v_m_u2081_1897_, 0);
v_size_1900_ = lean_ctor_get(v_m_u2082_1898_, 0);
v___x_1901_ = lean_nat_dec_le(v_size_1899_, v_size_1900_);
if (v___x_1901_ == 0)
{
lean_object* v___f_1902_; lean_object* v___x_1903_; 
v___f_1902_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1903_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1902_, v_inst_1895_, v_inst_1896_, v_m_u2081_1897_, v_m_u2082_1898_);
return v___x_1903_;
}
else
{
lean_object* v___x_1904_; lean_object* v___f_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_box(v___x_1901_);
v___f_1905_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1905_, 0, v_inst_1895_);
lean_closure_set(v___f_1905_, 1, v_inst_1896_);
lean_closure_set(v___f_1905_, 2, v_m_u2082_1898_);
lean_closure_set(v___f_1905_, 3, v___x_1904_);
v___x_1906_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1905_, v_m_u2081_1897_);
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff___redArg(lean_object* v_inst_1907_, lean_object* v_inst_1908_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_1909_, 0, lean_box(0));
lean_closure_set(v___x_1909_, 1, lean_box(0));
lean_closure_set(v___x_1909_, 2, v_inst_1907_);
lean_closure_set(v___x_1909_, 3, v_inst_1908_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff(lean_object* v_00_u03b1_1910_, lean_object* v_00_u03b2_1911_, lean_object* v_inst_1912_, lean_object* v_inst_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_1914_, 0, lean_box(0));
lean_closure_set(v___x_1914_, 1, lean_box(0));
lean_closure_set(v___x_1914_, 2, v_inst_1912_);
lean_closure_set(v___x_1914_, 3, v_inst_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__0(lean_object* v_f_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_, lean_object* v_x1_1918_, lean_object* v_x2_1919_, lean_object* v_x3_1920_){
_start:
{
lean_object* v_fst_1921_; lean_object* v_snd_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1936_; 
v_fst_1921_ = lean_ctor_get(v_x1_1918_, 0);
v_snd_1922_ = lean_ctor_get(v_x1_1918_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_x1_1918_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1924_ = v_x1_1918_;
v_isShared_1925_ = v_isSharedCheck_1936_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_snd_1922_);
lean_inc(v_fst_1921_);
lean_dec(v_x1_1918_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1936_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1926_; uint8_t v___x_1927_; 
lean_inc(v_x3_1920_);
lean_inc(v_x2_1919_);
v___x_1926_ = lean_apply_2(v_f_1915_, v_x2_1919_, v_x3_1920_);
v___x_1927_ = lean_unbox(v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v___x_1930_; 
v___x_1928_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1916_, v_x_1917_, v_snd_1922_, v_x2_1919_, v_x3_1920_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 1, v___x_1928_);
v___x_1930_ = v___x_1924_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_fst_1921_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v___x_1928_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
else
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1916_, v_x_1917_, v_fst_1921_, v_x2_1919_, v_x3_1920_);
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v___x_1932_);
v___x_1934_ = v___x_1924_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v___x_1932_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_snd_1922_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__1(lean_object* v___x_1937_, lean_object* v___f_1938_, lean_object* v_acc_1939_, lean_object* v_l_1940_){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1937_, v___f_1938_, v_acc_1939_, v_l_1940_);
return v___x_1941_;
}
}
static lean_object* _init_l_Std_HashMap_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v___x_1942_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg(lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_f_1946_, lean_object* v_m_1947_){
_start:
{
lean_object* v___y_1949_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v_buckets_1962_; lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1959_ = lean_unsigned_to_nat(0u);
v___x_1960_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_1961_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1962_ = lean_ctor_get(v_m_1947_, 1);
lean_inc_ref(v_buckets_1962_);
lean_dec_ref(v_m_1947_);
v___x_1963_ = lean_array_get_size(v_buckets_1962_);
v___x_1964_ = lean_nat_dec_lt(v___x_1959_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_dec_ref(v_buckets_1962_);
lean_dec_ref(v_f_1946_);
lean_dec_ref(v_x_1945_);
lean_dec_ref(v_x_1944_);
return v___x_1960_;
}
else
{
lean_object* v___f_1965_; lean_object* v___f_1966_; uint8_t v___x_1967_; 
v___f_1965_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1965_, 0, v_f_1946_);
lean_closure_set(v___f_1965_, 1, v_x_1944_);
lean_closure_set(v___f_1965_, 2, v_x_1945_);
v___f_1966_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1966_, 0, v___x_1961_);
lean_closure_set(v___f_1966_, 1, v___f_1965_);
v___x_1967_ = lean_nat_dec_le(v___x_1963_, v___x_1963_);
if (v___x_1967_ == 0)
{
if (v___x_1964_ == 0)
{
lean_dec_ref(v___f_1966_);
lean_dec_ref(v_buckets_1962_);
return v___x_1960_;
}
else
{
size_t v___x_1968_; size_t v___x_1969_; lean_object* v___x_1970_; 
v___x_1968_ = ((size_t)0ULL);
v___x_1969_ = lean_usize_of_nat(v___x_1963_);
v___x_1970_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1961_, v___f_1966_, v_buckets_1962_, v___x_1968_, v___x_1969_, v___x_1960_);
v___y_1949_ = v___x_1970_;
goto v___jp_1948_;
}
}
else
{
size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = ((size_t)0ULL);
v___x_1972_ = lean_usize_of_nat(v___x_1963_);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1961_, v___f_1966_, v_buckets_1962_, v___x_1971_, v___x_1972_, v___x_1960_);
v___y_1949_ = v___x_1973_;
goto v___jp_1948_;
}
}
v___jp_1948_:
{
lean_object* v_fst_1950_; lean_object* v_snd_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
v_fst_1950_ = lean_ctor_get(v___y_1949_, 0);
v_snd_1951_ = lean_ctor_get(v___y_1949_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___y_1949_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___y_1949_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_snd_1951_);
lean_inc(v_fst_1950_);
lean_dec(v___y_1949_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_fst_1950_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_snd_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition(lean_object* v_00_u03b1_1974_, lean_object* v_00_u03b2_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v_f_1978_, lean_object* v_m_1979_){
_start:
{
lean_object* v___y_1981_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v_buckets_1994_; lean_object* v___x_1995_; uint8_t v___x_1996_; 
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_1993_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1994_ = lean_ctor_get(v_m_1979_, 1);
lean_inc_ref(v_buckets_1994_);
lean_dec_ref(v_m_1979_);
v___x_1995_ = lean_array_get_size(v_buckets_1994_);
v___x_1996_ = lean_nat_dec_lt(v___x_1991_, v___x_1995_);
if (v___x_1996_ == 0)
{
lean_dec_ref(v_buckets_1994_);
lean_dec_ref(v_f_1978_);
lean_dec_ref(v_x_1977_);
lean_dec_ref(v_x_1976_);
return v___x_1992_;
}
else
{
lean_object* v___f_1997_; lean_object* v___f_1998_; uint8_t v___x_1999_; 
v___f_1997_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1997_, 0, v_f_1978_);
lean_closure_set(v___f_1997_, 1, v_x_1976_);
lean_closure_set(v___f_1997_, 2, v_x_1977_);
v___f_1998_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1998_, 0, v___x_1993_);
lean_closure_set(v___f_1998_, 1, v___f_1997_);
v___x_1999_ = lean_nat_dec_le(v___x_1995_, v___x_1995_);
if (v___x_1999_ == 0)
{
if (v___x_1996_ == 0)
{
lean_dec_ref(v___f_1998_);
lean_dec_ref(v_buckets_1994_);
return v___x_1992_;
}
else
{
size_t v___x_2000_; size_t v___x_2001_; lean_object* v___x_2002_; 
v___x_2000_ = ((size_t)0ULL);
v___x_2001_ = lean_usize_of_nat(v___x_1995_);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1993_, v___f_1998_, v_buckets_1994_, v___x_2000_, v___x_2001_, v___x_1992_);
v___y_1981_ = v___x_2002_;
goto v___jp_1980_;
}
}
else
{
size_t v___x_2003_; size_t v___x_2004_; lean_object* v___x_2005_; 
v___x_2003_ = ((size_t)0ULL);
v___x_2004_ = lean_usize_of_nat(v___x_1995_);
v___x_2005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1993_, v___f_1998_, v_buckets_1994_, v___x_2003_, v___x_2004_, v___x_1992_);
v___y_1981_ = v___x_2005_;
goto v___jp_1980_;
}
}
v___jp_1980_:
{
lean_object* v_fst_1982_; lean_object* v_snd_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_1990_; 
v_fst_1982_ = lean_ctor_get(v___y_1981_, 0);
v_snd_1983_ = lean_ctor_get(v___y_1981_, 1);
v_isSharedCheck_1990_ = !lean_is_exclusive(v___y_1981_);
if (v_isSharedCheck_1990_ == 0)
{
v___x_1985_ = v___y_1981_;
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_snd_1983_);
lean_inc(v_fst_1982_);
lean_dec(v___y_1981_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_1990_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
lean_object* v___x_1988_; 
if (v_isShared_1986_ == 0)
{
v___x_1988_ = v___x_1985_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_fst_1982_);
lean_ctor_set(v_reuseFailAlloc_1989_, 1, v_snd_1983_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0(lean_object* v_a_2006_, lean_object* v_b_2007_, lean_object* v_d_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2009_, 0, v_b_2007_);
lean_ctor_set(v___x_2009_, 1, v_d_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0___boxed(lean_object* v_a_2010_, lean_object* v_b_2011_, lean_object* v_d_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l_Std_HashMap_values___redArg___lam__0(v_a_2010_, v_b_2011_, v_d_2012_);
lean_dec(v_a_2010_);
return v_res_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg(lean_object* v_m_2018_){
_start:
{
lean_object* v___x_2019_; lean_object* v_buckets_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2019_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2020_ = lean_ctor_get(v_m_2018_, 1);
lean_inc_ref(v_buckets_2020_);
lean_dec_ref(v_m_2018_);
v___x_2021_ = lean_box(0);
v___x_2022_ = lean_array_get_size(v_buckets_2020_);
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = lean_nat_dec_lt(v___x_2023_, v___x_2022_);
if (v___x_2024_ == 0)
{
lean_dec_ref(v_buckets_2020_);
return v___x_2021_;
}
else
{
lean_object* v___f_2025_; size_t v___x_2026_; size_t v___x_2027_; lean_object* v___x_2028_; 
v___f_2025_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__1));
v___x_2026_ = lean_usize_of_nat(v___x_2022_);
v___x_2027_ = ((size_t)0ULL);
v___x_2028_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2019_, v___f_2025_, v_buckets_2020_, v___x_2026_, v___x_2027_, v___x_2021_);
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values(lean_object* v_00_u03b1_2029_, lean_object* v_00_u03b2_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_, lean_object* v_m_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v_buckets_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2034_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2035_ = lean_ctor_get(v_m_2033_, 1);
lean_inc_ref(v_buckets_2035_);
lean_dec_ref(v_m_2033_);
v___x_2036_ = lean_box(0);
v___x_2037_ = lean_array_get_size(v_buckets_2035_);
v___x_2038_ = lean_unsigned_to_nat(0u);
v___x_2039_ = lean_nat_dec_lt(v___x_2038_, v___x_2037_);
if (v___x_2039_ == 0)
{
lean_dec_ref(v_buckets_2035_);
return v___x_2036_;
}
else
{
lean_object* v___f_2040_; size_t v___x_2041_; size_t v___x_2042_; lean_object* v___x_2043_; 
v___f_2040_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__1));
v___x_2041_ = lean_usize_of_nat(v___x_2037_);
v___x_2042_ = ((size_t)0ULL);
v___x_2043_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2034_, v___f_2040_, v_buckets_2035_, v___x_2041_, v___x_2042_, v___x_2036_);
return v___x_2043_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___boxed(lean_object* v_00_u03b1_2044_, lean_object* v_00_u03b2_2045_, lean_object* v_x_2046_, lean_object* v_x_2047_, lean_object* v_m_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Std_HashMap_values(v_00_u03b1_2044_, v_00_u03b2_2045_, v_x_2046_, v_x_2047_, v_m_2048_);
lean_dec_ref(v_x_2047_);
lean_dec_ref(v_x_2046_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0(lean_object* v_x1_2050_, lean_object* v_x2_2051_, lean_object* v_x3_2052_){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_array_push(v_x1_2050_, v_x3_2052_);
return v___x_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2054_, lean_object* v_x2_2055_, lean_object* v_x3_2056_){
_start:
{
lean_object* v_res_2057_; 
v_res_2057_ = l_Std_HashMap_valuesArray___redArg___lam__0(v_x1_2054_, v_x2_2055_, v_x3_2056_);
lean_dec(v_x2_2055_);
return v_res_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg(lean_object* v_m_2062_){
_start:
{
lean_object* v_size_2063_; lean_object* v_buckets_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; uint8_t v___x_2069_; 
v_size_2063_ = lean_ctor_get(v_m_2062_, 0);
lean_inc(v_size_2063_);
v_buckets_2064_ = lean_ctor_get(v_m_2062_, 1);
lean_inc_ref(v_buckets_2064_);
lean_dec_ref(v_m_2062_);
v___x_2065_ = lean_mk_empty_array_with_capacity(v_size_2063_);
lean_dec(v_size_2063_);
v___x_2066_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_2067_ = lean_unsigned_to_nat(0u);
v___x_2068_ = lean_array_get_size(v_buckets_2064_);
v___x_2069_ = lean_nat_dec_lt(v___x_2067_, v___x_2068_);
if (v___x_2069_ == 0)
{
lean_dec_ref(v_buckets_2064_);
return v___x_2065_;
}
else
{
lean_object* v___f_2070_; uint8_t v___x_2071_; 
v___f_2070_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__1));
v___x_2071_ = lean_nat_dec_le(v___x_2068_, v___x_2068_);
if (v___x_2071_ == 0)
{
if (v___x_2069_ == 0)
{
lean_dec_ref(v_buckets_2064_);
return v___x_2065_;
}
else
{
size_t v___x_2072_; size_t v___x_2073_; lean_object* v___x_2074_; 
v___x_2072_ = ((size_t)0ULL);
v___x_2073_ = lean_usize_of_nat(v___x_2068_);
v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2066_, v___f_2070_, v_buckets_2064_, v___x_2072_, v___x_2073_, v___x_2065_);
return v___x_2074_;
}
}
else
{
size_t v___x_2075_; size_t v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = ((size_t)0ULL);
v___x_2076_ = lean_usize_of_nat(v___x_2068_);
v___x_2077_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2066_, v___f_2070_, v_buckets_2064_, v___x_2075_, v___x_2076_, v___x_2065_);
return v___x_2077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray(lean_object* v_00_u03b1_2078_, lean_object* v_00_u03b2_2079_, lean_object* v_x_2080_, lean_object* v_x_2081_, lean_object* v_m_2082_){
_start:
{
lean_object* v_size_2083_; lean_object* v_buckets_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; 
v_size_2083_ = lean_ctor_get(v_m_2082_, 0);
lean_inc(v_size_2083_);
v_buckets_2084_ = lean_ctor_get(v_m_2082_, 1);
lean_inc_ref(v_buckets_2084_);
lean_dec_ref(v_m_2082_);
v___x_2085_ = lean_mk_empty_array_with_capacity(v_size_2083_);
lean_dec(v_size_2083_);
v___x_2086_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_2087_ = lean_unsigned_to_nat(0u);
v___x_2088_ = lean_array_get_size(v_buckets_2084_);
v___x_2089_ = lean_nat_dec_lt(v___x_2087_, v___x_2088_);
if (v___x_2089_ == 0)
{
lean_dec_ref(v_buckets_2084_);
return v___x_2085_;
}
else
{
lean_object* v___f_2090_; uint8_t v___x_2091_; 
v___f_2090_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__1));
v___x_2091_ = lean_nat_dec_le(v___x_2088_, v___x_2088_);
if (v___x_2091_ == 0)
{
if (v___x_2089_ == 0)
{
lean_dec_ref(v_buckets_2084_);
return v___x_2085_;
}
else
{
size_t v___x_2092_; size_t v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = lean_usize_of_nat(v___x_2088_);
v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2086_, v___f_2090_, v_buckets_2084_, v___x_2092_, v___x_2093_, v___x_2085_);
return v___x_2094_;
}
}
else
{
size_t v___x_2095_; size_t v___x_2096_; lean_object* v___x_2097_; 
v___x_2095_ = ((size_t)0ULL);
v___x_2096_ = lean_usize_of_nat(v___x_2088_);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2086_, v___f_2090_, v_buckets_2084_, v___x_2095_, v___x_2096_, v___x_2085_);
return v___x_2097_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___boxed(lean_object* v_00_u03b1_2098_, lean_object* v_00_u03b2_2099_, lean_object* v_x_2100_, lean_object* v_x_2101_, lean_object* v_m_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Std_HashMap_valuesArray(v_00_u03b1_2098_, v_00_u03b2_2099_, v_x_2100_, v_x_2101_, v_m_2102_);
lean_dec_ref(v_x_2101_);
lean_dec_ref(v_x_2100_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray___redArg(lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_l_2106_){
_start:
{
lean_object* v___f_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___f_2107_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2108_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_2109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2107_, v_inst_2104_, v_inst_2105_, v___x_2108_, v_l_2106_);
return v___x_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray(lean_object* v_00_u03b1_2110_, lean_object* v_inst_2111_, lean_object* v_inst_2112_, lean_object* v_l_2113_){
_start:
{
lean_object* v___f_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___f_2114_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2115_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_2116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2114_, v_inst_2111_, v_inst_2112_, v___x_2115_, v_l_2113_);
return v___x_2116_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg(lean_object* v_m_2117_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2117_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg___boxed(lean_object* v_m_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Std_HashMap_Internal_numBuckets___redArg(v_m_2119_);
lean_dec_ref(v_m_2119_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets(lean_object* v_00_u03b1_2121_, lean_object* v_00_u03b2_2122_, lean_object* v_x_2123_, lean_object* v_x_2124_, lean_object* v_m_2125_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_00_u03b2_2128_, lean_object* v_x_2129_, lean_object* v_x_2130_, lean_object* v_m_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Std_HashMap_Internal_numBuckets(v_00_u03b1_2127_, v_00_u03b2_2128_, v_x_2129_, v_x_2130_, v_m_2131_);
lean_dec_ref(v_m_2131_);
lean_dec_ref(v_x_2130_);
lean_dec_ref(v_x_2129_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2(lean_object* v___x_2136_, lean_object* v___f_2137_, lean_object* v_m_2138_, lean_object* v_prec_2139_){
_start:
{
lean_object* v___x_2140_; lean_object* v_buckets_2141_; lean_object* v___x_2143_; uint8_t v_isShared_2144_; uint8_t v_isSharedCheck_2161_; 
v___x_2140_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2141_ = lean_ctor_get(v_m_2138_, 1);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_m_2138_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; 
v_unused_2162_ = lean_ctor_get(v_m_2138_, 0);
lean_dec(v_unused_2162_);
v___x_2143_ = v_m_2138_;
v_isShared_2144_ = v_isSharedCheck_2161_;
goto v_resetjp_2142_;
}
else
{
lean_inc(v_buckets_2141_);
lean_dec(v_m_2138_);
v___x_2143_ = lean_box(0);
v_isShared_2144_ = v_isSharedCheck_2161_;
goto v_resetjp_2142_;
}
v_resetjp_2142_:
{
lean_object* v___x_2145_; lean_object* v___y_2147_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2145_ = ((lean_object*)(l_Std_HashMap_instRepr___redArg___lam__2___closed__1));
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_array_get_size(v_buckets_2141_);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_nat_dec_lt(v___x_2155_, v___x_2154_);
if (v___x_2156_ == 0)
{
lean_dec_ref(v_buckets_2141_);
lean_dec_ref(v___f_2137_);
v___y_2147_ = v___x_2153_;
goto v___jp_2146_;
}
else
{
lean_object* v___f_2157_; size_t v___x_2158_; size_t v___x_2159_; lean_object* v___x_2160_; 
v___f_2157_ = lean_alloc_closure((void*)(l_Std_HashMap_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2157_, 0, v___x_2140_);
lean_closure_set(v___f_2157_, 1, v___f_2137_);
v___x_2158_ = lean_usize_of_nat(v___x_2154_);
v___x_2159_ = ((size_t)0ULL);
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2140_, v___f_2157_, v_buckets_2141_, v___x_2158_, v___x_2159_, v___x_2153_);
v___y_2147_ = v___x_2160_;
goto v___jp_2146_;
}
v___jp_2146_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = l_List_repr___redArg(v___x_2136_, v___y_2147_);
if (v_isShared_2144_ == 0)
{
lean_ctor_set_tag(v___x_2143_, 5);
lean_ctor_set(v___x_2143_, 1, v___x_2148_);
lean_ctor_set(v___x_2143_, 0, v___x_2145_);
v___x_2150_ = v___x_2143_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2152_, 1, v___x_2148_);
v___x_2150_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Repr_addAppParen(v___x_2150_, v_prec_2139_);
return v___x_2151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2___boxed(lean_object* v___x_2163_, lean_object* v___f_2164_, lean_object* v_m_2165_, lean_object* v_prec_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Std_HashMap_instRepr___redArg___lam__2(v___x_2163_, v___f_2164_, v_m_2165_, v_prec_2166_);
lean_dec(v_prec_2166_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg(lean_object* v_inst_2168_, lean_object* v_inst_2169_){
_start:
{
lean_object* v___f_2170_; lean_object* v___f_2171_; lean_object* v___x_2172_; lean_object* v___f_2173_; 
v___f_2170_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__0));
v___f_2171_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2171_, 0, v_inst_2169_);
v___x_2172_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2172_, 0, lean_box(0));
lean_closure_set(v___x_2172_, 1, lean_box(0));
lean_closure_set(v___x_2172_, 2, v_inst_2168_);
lean_closure_set(v___x_2172_, 3, v___f_2171_);
v___f_2173_ = lean_alloc_closure((void*)(l_Std_HashMap_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2173_, 0, v___x_2172_);
lean_closure_set(v___f_2173_, 1, v___f_2170_);
return v___f_2173_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr(lean_object* v_00_u03b1_2174_, lean_object* v_00_u03b2_2175_, lean_object* v_inst_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_inst_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Std_HashMap_instRepr___redArg(v_inst_2178_, v_inst_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_00_u03b2_2182_, lean_object* v_inst_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_, lean_object* v_inst_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Std_HashMap_instRepr(v_00_u03b1_2181_, v_00_u03b2_2182_, v_inst_2183_, v_inst_2184_, v_inst_2185_, v_inst_2186_);
lean_dec_ref(v_inst_2184_);
lean_dec_ref(v_inst_2183_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__0(lean_object* v_a_2190_, lean_object* v_x_2191_){
_start:
{
lean_object* v___y_2193_; 
if (lean_obj_tag(v_x_2191_) == 0)
{
lean_object* v___x_2196_; 
v___x_2196_ = ((lean_object*)(l_Array_groupByKey___redArg___lam__0___closed__0));
v___y_2193_ = v___x_2196_;
goto v___jp_2192_;
}
else
{
lean_object* v_val_2197_; 
v_val_2197_ = lean_ctor_get(v_x_2191_, 0);
lean_inc(v_val_2197_);
lean_dec_ref(v_x_2191_);
v___y_2193_ = v_val_2197_;
goto v___jp_2192_;
}
v___jp_2192_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
v___x_2194_ = lean_array_push(v___y_2193_, v_a_2190_);
v___x_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__1(lean_object* v_key_2198_, lean_object* v_inst_2199_, lean_object* v_inst_2200_, lean_object* v_a_2201_, lean_object* v_x_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___f_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_inc(v_a_2201_);
v___f_2204_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2204_, 0, v_a_2201_);
v___x_2205_ = lean_apply_1(v_key_2198_, v_a_2201_);
v___x_2206_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_2199_, v_inst_2200_, v___y_2203_, v___x_2205_, v___f_2204_);
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg(lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_key_2210_, lean_object* v_xs_2211_){
_start:
{
lean_object* v___f_2212_; lean_object* v___x_2213_; lean_object* v_groups_2214_; size_t v_sz_2215_; size_t v___x_2216_; lean_object* v___x_2217_; 
v___f_2212_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__1), 6, 3);
lean_closure_set(v___f_2212_, 0, v_key_2210_);
lean_closure_set(v___f_2212_, 1, v_inst_2208_);
lean_closure_set(v___f_2212_, 2, v_inst_2209_);
v___x_2213_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_groups_2214_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v_sz_2215_ = lean_array_size(v_xs_2211_);
v___x_2216_ = ((size_t)0ULL);
v___x_2217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2213_, v_xs_2211_, v___f_2212_, v_sz_2215_, v___x_2216_, v_groups_2214_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey(lean_object* v_00_u03b1_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_inst_2220_, lean_object* v_inst_2221_, lean_object* v_key_2222_, lean_object* v_xs_2223_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Array_groupByKey___redArg(v_inst_2220_, v_inst_2221_, v_key_2222_, v_xs_2223_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__0(lean_object* v_x_2225_, lean_object* v_v_2226_){
_start:
{
lean_object* v___y_2228_; 
if (lean_obj_tag(v_v_2226_) == 0)
{
lean_object* v___x_2231_; 
v___x_2231_ = lean_box(0);
v___y_2228_ = v___x_2231_;
goto v___jp_2227_;
}
else
{
lean_object* v_val_2232_; 
v_val_2232_ = lean_ctor_get(v_v_2226_, 0);
lean_inc(v_val_2232_);
lean_dec_ref(v_v_2226_);
v___y_2228_ = v_val_2232_;
goto v___jp_2227_;
}
v___jp_2227_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2229_, 0, v_x_2225_);
lean_ctor_set(v___x_2229_, 1, v___y_2228_);
v___x_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
return v___x_2230_;
}
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__1(lean_object* v_key_2233_, lean_object* v_inst_2234_, lean_object* v_inst_2235_, lean_object* v_x_2236_, lean_object* v_acc_2237_){
_start:
{
lean_object* v___f_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
lean_inc(v_x_2236_);
v___f_2238_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2238_, 0, v_x_2236_);
v___x_2239_ = lean_apply_1(v_key_2233_, v_x_2236_);
v___x_2240_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_2234_, v_inst_2235_, v_acc_2237_, v___x_2239_, v___f_2238_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg(lean_object* v_inst_2241_, lean_object* v_inst_2242_, lean_object* v_key_2243_, lean_object* v_xs_2244_){
_start:
{
lean_object* v___f_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___f_2245_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__1), 5, 3);
lean_closure_set(v___f_2245_, 0, v_key_2243_);
lean_closure_set(v___f_2245_, 1, v_inst_2241_);
lean_closure_set(v___f_2245_, 2, v_inst_2242_);
v___x_2246_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_2247_ = l_List_foldrTR___redArg(v___f_2245_, v___x_2246_, v_xs_2244_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey(lean_object* v_00_u03b1_2248_, lean_object* v_00_u03b2_2249_, lean_object* v_inst_2250_, lean_object* v_inst_2251_, lean_object* v_key_2252_, lean_object* v_xs_2253_){
_start:
{
lean_object* v___x_2254_; 
v___x_2254_ = l_List_groupByKey___redArg(v_inst_2250_, v_inst_2251_, v_key_2252_, v_xs_2253_);
return v___x_2254_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashMap_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
