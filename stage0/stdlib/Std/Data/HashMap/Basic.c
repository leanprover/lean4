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
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_HashMap_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value)} };
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
v_currMacroScope_127_ = lean_ctor_get(v_a_120_, 2);
v_ref_128_ = lean_ctor_get(v_a_120_, 5);
v___x_129_ = lean_unsigned_to_nat(0u);
v___x_130_ = l_Lean_Syntax_getArg(v_x_119_, v___x_129_);
v___x_131_ = lean_unsigned_to_nat(2u);
v___x_132_ = l_Lean_Syntax_getArg(v_x_119_, v___x_131_);
lean_dec(v_x_119_);
v___x_133_ = 0;
v___x_134_ = l_Lean_SourceInfo_fromRef(v_ref_128_, v___x_133_);
v___x_135_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
v___x_136_ = lean_obj_once(&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6, &l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6_once, _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6);
v___x_137_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_127_);
lean_inc(v_quotContext_126_);
v___x_138_ = l_Lean_addMacroScope(v_quotContext_126_, v___x_137_, v_currMacroScope_127_);
v___x_139_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12));
lean_inc_n(v___x_134_, 2);
v___x_140_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_140_, 0, v___x_134_);
lean_ctor_set(v___x_140_, 1, v___x_136_);
lean_ctor_set(v___x_140_, 2, v___x_138_);
lean_ctor_set(v___x_140_, 3, v___x_139_);
v___x_141_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14));
v___x_142_ = l_Lean_Syntax_node2(v___x_134_, v___x_141_, v___x_130_, v___x_132_);
v___x_143_ = l_Lean_Syntax_node2(v___x_134_, v___x_135_, v___x_140_, v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_a_121_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___boxed(lean_object* v_x_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(v_x_145_, v_a_146_, v_a_147_);
lean_dec_ref(v_a_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(lean_object* v_x_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
lean_inc(v_x_152_);
v___x_156_ = l_Lean_Syntax_isOfKind(v_x_152_, v___x_155_);
if (v___x_156_ == 0)
{
lean_object* v___x_157_; lean_object* v___x_158_; 
lean_dec(v_x_152_);
v___x_157_ = lean_box(0);
v___x_158_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_157_);
lean_ctor_set(v___x_158_, 1, v_a_154_);
return v___x_158_;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_159_ = lean_unsigned_to_nat(0u);
v___x_160_ = l_Lean_Syntax_getArg(v_x_152_, v___x_159_);
v___x_161_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1));
lean_inc(v___x_160_);
v___x_162_ = l_Lean_Syntax_isOfKind(v___x_160_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v___x_160_);
lean_dec(v_x_152_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_a_154_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_165_ = lean_unsigned_to_nat(1u);
v___x_166_ = l_Lean_Syntax_getArg(v_x_152_, v___x_165_);
lean_dec(v_x_152_);
v___x_167_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_166_);
v___x_168_ = l_Lean_Syntax_matchesNull(v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v___x_166_);
lean_dec(v___x_160_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_a_154_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_ref_173_; uint8_t v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_171_ = l_Lean_Syntax_getArg(v___x_166_, v___x_159_);
v___x_172_ = l_Lean_Syntax_getArg(v___x_166_, v___x_165_);
lean_dec(v___x_166_);
v_ref_173_ = l_Lean_replaceRef(v___x_160_, v_a_153_);
lean_dec(v___x_160_);
v___x_174_ = 0;
v___x_175_ = l_Lean_SourceInfo_fromRef(v_ref_173_, v___x_174_);
lean_dec(v_ref_173_);
v___x_176_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
v___x_177_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__6));
lean_inc(v___x_175_);
v___x_178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_178_, 0, v___x_175_);
lean_ctor_set(v___x_178_, 1, v___x_177_);
v___x_179_ = l_Lean_Syntax_node3(v___x_175_, v___x_176_, v___x_171_, v___x_178_, v___x_172_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_a_154_);
return v___x_180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___boxed(lean_object* v_x_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(v_x_181_, v_a_182_, v_a_183_);
lean_dec(v_a_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___redArg(lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_m_187_, lean_object* v_a_188_, lean_object* v_b_189_){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_185_, v_x_186_, v_m_187_, v_a_188_, v_b_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_x_193_, lean_object* v_x_194_, lean_object* v_m_195_, lean_object* v_a_196_, lean_object* v_b_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_193_, v_x_194_, v_m_195_, v_a_196_, v_b_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg___lam__0(lean_object* v_x_199_, lean_object* v_x_200_, lean_object* v_x_201_){
_start:
{
lean_object* v_fst_202_; lean_object* v_snd_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_fst_202_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_fst_202_);
v_snd_203_ = lean_ctor_get(v_x_201_, 1);
lean_inc(v_snd_203_);
lean_dec_ref(v_x_201_);
v___x_204_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_199_, v_x_200_, v___x_204_, v_fst_202_, v_snd_203_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg(lean_object* v_x_206_, lean_object* v_x_207_){
_start:
{
lean_object* v___f_208_; 
v___f_208_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_208_, 0, v_x_206_);
lean_closure_set(v___f_208_, 1, v_x_207_);
return v___f_208_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd(lean_object* v_00_u03b1_209_, lean_object* v_00_u03b2_210_, lean_object* v_x_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___f_213_; 
v___f_213_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_213_, 0, v_x_211_);
lean_closure_set(v___f_213_, 1, v_x_212_);
return v___f_213_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg___lam__0(lean_object* v_x_214_, lean_object* v_x_215_, lean_object* v_x_216_, lean_object* v_s_217_){
_start:
{
lean_object* v_fst_218_; lean_object* v_snd_219_; lean_object* v___x_220_; 
v_fst_218_ = lean_ctor_get(v_x_216_, 0);
lean_inc(v_fst_218_);
v_snd_219_ = lean_ctor_get(v_x_216_, 1);
lean_inc(v_snd_219_);
lean_dec_ref(v_x_216_);
v___x_220_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_214_, v_x_215_, v_s_217_, v_fst_218_, v_snd_219_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg(lean_object* v_x_221_, lean_object* v_x_222_){
_start:
{
lean_object* v___f_223_; 
v___f_223_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_223_, 0, v_x_221_);
lean_closure_set(v___f_223_, 1, v_x_222_);
return v___f_223_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd(lean_object* v_00_u03b1_224_, lean_object* v_00_u03b2_225_, lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
lean_object* v___f_228_; 
v___f_228_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_228_, 0, v_x_226_);
lean_closure_set(v___f_228_, 1, v_x_227_);
return v___f_228_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew___redArg(lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_m_231_, lean_object* v_a_232_, lean_object* v_b_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_229_, v_x_230_, v_m_231_, v_a_232_, v_b_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_m_239_, lean_object* v_a_240_, lean_object* v_b_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_237_, v_x_238_, v_m_239_, v_a_240_, v_b_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert___redArg(lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_m_245_, lean_object* v_a_246_, lean_object* v_b_247_){
_start:
{
lean_object* v_size_248_; lean_object* v_buckets_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_300_; 
v_size_248_ = lean_ctor_get(v_m_245_, 0);
v_buckets_249_ = lean_ctor_get(v_m_245_, 1);
v_isSharedCheck_300_ = !lean_is_exclusive(v_m_245_);
if (v_isSharedCheck_300_ == 0)
{
v___x_251_ = v_m_245_;
v_isShared_252_ = v_isSharedCheck_300_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_buckets_249_);
lean_inc(v_size_248_);
lean_dec(v_m_245_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_300_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; uint64_t v___x_255_; uint64_t v___x_256_; uint64_t v___x_257_; uint64_t v___x_258_; uint64_t v_fold_259_; uint64_t v___x_260_; uint64_t v___x_261_; uint64_t v___x_262_; size_t v___x_263_; size_t v___x_264_; size_t v___x_265_; size_t v___x_266_; size_t v___x_267_; lean_object* v_bkt_268_; uint8_t v___x_269_; 
v___x_253_ = lean_array_get_size(v_buckets_249_);
lean_inc_ref(v_x_244_);
lean_inc_n(v_a_246_, 2);
v___x_254_ = lean_apply_1(v_x_244_, v_a_246_);
v___x_255_ = 32ULL;
v___x_256_ = lean_unbox_uint64(v___x_254_);
v___x_257_ = lean_uint64_shift_right(v___x_256_, v___x_255_);
v___x_258_ = lean_unbox_uint64(v___x_254_);
lean_dec_ref(v___x_254_);
v_fold_259_ = lean_uint64_xor(v___x_258_, v___x_257_);
v___x_260_ = 16ULL;
v___x_261_ = lean_uint64_shift_right(v_fold_259_, v___x_260_);
v___x_262_ = lean_uint64_xor(v_fold_259_, v___x_261_);
v___x_263_ = lean_uint64_to_usize(v___x_262_);
v___x_264_ = lean_usize_of_nat(v___x_253_);
v___x_265_ = ((size_t)1ULL);
v___x_266_ = lean_usize_sub(v___x_264_, v___x_265_);
v___x_267_ = lean_usize_land(v___x_263_, v___x_266_);
v_bkt_268_ = lean_array_uget_borrowed(v_buckets_249_, v___x_267_);
lean_inc(v_bkt_268_);
lean_inc_ref(v_x_243_);
v___x_269_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_243_, v_a_246_, v_bkt_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v_size_x27_271_; lean_object* v___x_272_; lean_object* v_buckets_x27_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
lean_dec_ref(v_x_243_);
v___x_270_ = lean_unsigned_to_nat(1u);
v_size_x27_271_ = lean_nat_add(v_size_248_, v___x_270_);
lean_dec(v_size_248_);
lean_inc(v_bkt_268_);
v___x_272_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_272_, 0, v_a_246_);
lean_ctor_set(v___x_272_, 1, v_b_247_);
lean_ctor_set(v___x_272_, 2, v_bkt_268_);
v_buckets_x27_273_ = lean_array_uset(v_buckets_249_, v___x_267_, v___x_272_);
v___x_274_ = lean_unsigned_to_nat(4u);
v___x_275_ = lean_nat_mul(v_size_x27_271_, v___x_274_);
v___x_276_ = lean_unsigned_to_nat(3u);
v___x_277_ = lean_nat_div(v___x_275_, v___x_276_);
lean_dec(v___x_275_);
v___x_278_ = lean_array_get_size(v_buckets_x27_273_);
v___x_279_ = lean_nat_dec_le(v___x_277_, v___x_278_);
lean_dec(v___x_277_);
if (v___x_279_ == 0)
{
lean_object* v_val_280_; lean_object* v___x_282_; 
v_val_280_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_244_, v_buckets_x27_273_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_val_280_);
lean_ctor_set(v___x_251_, 0, v_size_x27_271_);
v___x_282_ = v___x_251_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_size_x27_271_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v_val_280_);
v___x_282_ = v_reuseFailAlloc_285_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_283_ = lean_box(v___x_269_);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v___x_282_);
return v___x_284_;
}
}
else
{
lean_object* v___x_287_; 
lean_dec_ref(v_x_244_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_buckets_x27_273_);
lean_ctor_set(v___x_251_, 0, v_size_x27_271_);
v___x_287_ = v___x_251_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_size_x27_271_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v_buckets_x27_273_);
v___x_287_ = v_reuseFailAlloc_290_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_box(v___x_269_);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___x_288_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
return v___x_289_;
}
}
}
else
{
lean_object* v___x_291_; lean_object* v_buckets_x27_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_296_; 
lean_inc(v_bkt_268_);
lean_dec_ref(v_x_244_);
v___x_291_ = lean_box(0);
v_buckets_x27_292_ = lean_array_uset(v_buckets_249_, v___x_267_, v___x_291_);
v___x_293_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_243_, v_a_246_, v_b_247_, v_bkt_268_);
v___x_294_ = lean_array_uset(v_buckets_x27_292_, v___x_267_, v___x_293_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v___x_294_);
v___x_296_ = v___x_251_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_size_248_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___x_294_);
v___x_296_ = v_reuseFailAlloc_299_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_box(v___x_269_);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_297_);
lean_ctor_set(v___x_298_, 1, v___x_296_);
return v___x_298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert(lean_object* v_00_u03b1_301_, lean_object* v_00_u03b2_302_, lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_m_305_, lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
lean_object* v_size_308_; lean_object* v_buckets_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_360_; 
v_size_308_ = lean_ctor_get(v_m_305_, 0);
v_buckets_309_ = lean_ctor_get(v_m_305_, 1);
v_isSharedCheck_360_ = !lean_is_exclusive(v_m_305_);
if (v_isSharedCheck_360_ == 0)
{
v___x_311_ = v_m_305_;
v_isShared_312_ = v_isSharedCheck_360_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_buckets_309_);
lean_inc(v_size_308_);
lean_dec(v_m_305_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_360_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; lean_object* v___x_314_; uint64_t v___x_315_; uint64_t v___x_316_; uint64_t v___x_317_; uint64_t v___x_318_; uint64_t v_fold_319_; uint64_t v___x_320_; uint64_t v___x_321_; uint64_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; size_t v___x_326_; size_t v___x_327_; lean_object* v_bkt_328_; uint8_t v___x_329_; 
v___x_313_ = lean_array_get_size(v_buckets_309_);
lean_inc_ref(v_x_304_);
lean_inc_n(v_a_306_, 2);
v___x_314_ = lean_apply_1(v_x_304_, v_a_306_);
v___x_315_ = 32ULL;
v___x_316_ = lean_unbox_uint64(v___x_314_);
v___x_317_ = lean_uint64_shift_right(v___x_316_, v___x_315_);
v___x_318_ = lean_unbox_uint64(v___x_314_);
lean_dec_ref(v___x_314_);
v_fold_319_ = lean_uint64_xor(v___x_318_, v___x_317_);
v___x_320_ = 16ULL;
v___x_321_ = lean_uint64_shift_right(v_fold_319_, v___x_320_);
v___x_322_ = lean_uint64_xor(v_fold_319_, v___x_321_);
v___x_323_ = lean_uint64_to_usize(v___x_322_);
v___x_324_ = lean_usize_of_nat(v___x_313_);
v___x_325_ = ((size_t)1ULL);
v___x_326_ = lean_usize_sub(v___x_324_, v___x_325_);
v___x_327_ = lean_usize_land(v___x_323_, v___x_326_);
v_bkt_328_ = lean_array_uget_borrowed(v_buckets_309_, v___x_327_);
lean_inc(v_bkt_328_);
lean_inc_ref(v_x_303_);
v___x_329_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_303_, v_a_306_, v_bkt_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v_size_x27_331_; lean_object* v___x_332_; lean_object* v_buckets_x27_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
lean_dec_ref(v_x_303_);
v___x_330_ = lean_unsigned_to_nat(1u);
v_size_x27_331_ = lean_nat_add(v_size_308_, v___x_330_);
lean_dec(v_size_308_);
lean_inc(v_bkt_328_);
v___x_332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_332_, 0, v_a_306_);
lean_ctor_set(v___x_332_, 1, v_b_307_);
lean_ctor_set(v___x_332_, 2, v_bkt_328_);
v_buckets_x27_333_ = lean_array_uset(v_buckets_309_, v___x_327_, v___x_332_);
v___x_334_ = lean_unsigned_to_nat(4u);
v___x_335_ = lean_nat_mul(v_size_x27_331_, v___x_334_);
v___x_336_ = lean_unsigned_to_nat(3u);
v___x_337_ = lean_nat_div(v___x_335_, v___x_336_);
lean_dec(v___x_335_);
v___x_338_ = lean_array_get_size(v_buckets_x27_333_);
v___x_339_ = lean_nat_dec_le(v___x_337_, v___x_338_);
lean_dec(v___x_337_);
if (v___x_339_ == 0)
{
lean_object* v_val_340_; lean_object* v___x_342_; 
v_val_340_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_304_, v_buckets_x27_333_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v_val_340_);
lean_ctor_set(v___x_311_, 0, v_size_x27_331_);
v___x_342_ = v___x_311_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_345_; 
v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_345_, 0, v_size_x27_331_);
lean_ctor_set(v_reuseFailAlloc_345_, 1, v_val_340_);
v___x_342_ = v_reuseFailAlloc_345_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_343_ = lean_box(v___x_329_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v___x_342_);
return v___x_344_;
}
}
else
{
lean_object* v___x_347_; 
lean_dec_ref(v_x_304_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v_buckets_x27_333_);
lean_ctor_set(v___x_311_, 0, v_size_x27_331_);
v___x_347_ = v___x_311_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_size_x27_331_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v_buckets_x27_333_);
v___x_347_ = v_reuseFailAlloc_350_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_box(v___x_329_);
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_348_);
lean_ctor_set(v___x_349_, 1, v___x_347_);
return v___x_349_;
}
}
}
else
{
lean_object* v___x_351_; lean_object* v_buckets_x27_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_356_; 
lean_inc(v_bkt_328_);
lean_dec_ref(v_x_304_);
v___x_351_ = lean_box(0);
v_buckets_x27_352_ = lean_array_uset(v_buckets_309_, v___x_327_, v___x_351_);
v___x_353_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_303_, v_a_306_, v_b_307_, v_bkt_328_);
v___x_354_ = lean_array_uset(v_buckets_x27_352_, v___x_327_, v___x_353_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_354_);
v___x_356_ = v___x_311_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_size_308_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_354_);
v___x_356_ = v_reuseFailAlloc_359_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = lean_box(v___x_329_);
v___x_358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_356_);
return v___x_358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew___redArg(lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_m_363_, lean_object* v_a_364_, lean_object* v_b_365_){
_start:
{
lean_object* v_size_366_; lean_object* v_buckets_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint64_t v___x_370_; uint64_t v___x_371_; uint64_t v___x_372_; uint64_t v___x_373_; uint64_t v_fold_374_; uint64_t v___x_375_; uint64_t v___x_376_; uint64_t v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v_bkt_383_; uint8_t v___x_384_; 
v_size_366_ = lean_ctor_get(v_m_363_, 0);
v_buckets_367_ = lean_ctor_get(v_m_363_, 1);
v___x_368_ = lean_array_get_size(v_buckets_367_);
lean_inc_ref(v_x_362_);
lean_inc_n(v_a_364_, 2);
v___x_369_ = lean_apply_1(v_x_362_, v_a_364_);
v___x_370_ = 32ULL;
v___x_371_ = lean_unbox_uint64(v___x_369_);
v___x_372_ = lean_uint64_shift_right(v___x_371_, v___x_370_);
v___x_373_ = lean_unbox_uint64(v___x_369_);
lean_dec_ref(v___x_369_);
v_fold_374_ = lean_uint64_xor(v___x_373_, v___x_372_);
v___x_375_ = 16ULL;
v___x_376_ = lean_uint64_shift_right(v_fold_374_, v___x_375_);
v___x_377_ = lean_uint64_xor(v_fold_374_, v___x_376_);
v___x_378_ = lean_uint64_to_usize(v___x_377_);
v___x_379_ = lean_usize_of_nat(v___x_368_);
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_sub(v___x_379_, v___x_380_);
v___x_382_ = lean_usize_land(v___x_378_, v___x_381_);
v_bkt_383_ = lean_array_uget_borrowed(v_buckets_367_, v___x_382_);
lean_inc(v_bkt_383_);
v___x_384_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_361_, v_a_364_, v_bkt_383_);
if (v___x_384_ == 0)
{
lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_409_; 
lean_inc_ref(v_buckets_367_);
lean_inc(v_size_366_);
v_isSharedCheck_409_ = !lean_is_exclusive(v_m_363_);
if (v_isSharedCheck_409_ == 0)
{
lean_object* v_unused_410_; lean_object* v_unused_411_; 
v_unused_410_ = lean_ctor_get(v_m_363_, 1);
lean_dec(v_unused_410_);
v_unused_411_ = lean_ctor_get(v_m_363_, 0);
lean_dec(v_unused_411_);
v___x_386_ = v_m_363_;
v_isShared_387_ = v_isSharedCheck_409_;
goto v_resetjp_385_;
}
else
{
lean_dec(v_m_363_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_409_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_388_; lean_object* v_size_x27_389_; lean_object* v___x_390_; lean_object* v_buckets_x27_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_388_ = lean_unsigned_to_nat(1u);
v_size_x27_389_ = lean_nat_add(v_size_366_, v___x_388_);
lean_dec(v_size_366_);
lean_inc(v_bkt_383_);
v___x_390_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_390_, 0, v_a_364_);
lean_ctor_set(v___x_390_, 1, v_b_365_);
lean_ctor_set(v___x_390_, 2, v_bkt_383_);
v_buckets_x27_391_ = lean_array_uset(v_buckets_367_, v___x_382_, v___x_390_);
v___x_392_ = lean_unsigned_to_nat(4u);
v___x_393_ = lean_nat_mul(v_size_x27_389_, v___x_392_);
v___x_394_ = lean_unsigned_to_nat(3u);
v___x_395_ = lean_nat_div(v___x_393_, v___x_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_array_get_size(v_buckets_x27_391_);
v___x_397_ = lean_nat_dec_le(v___x_395_, v___x_396_);
lean_dec(v___x_395_);
if (v___x_397_ == 0)
{
lean_object* v_val_398_; lean_object* v___x_400_; 
v_val_398_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_362_, v_buckets_x27_391_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_val_398_);
lean_ctor_set(v___x_386_, 0, v_size_x27_389_);
v___x_400_ = v___x_386_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_size_x27_389_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v_val_398_);
v___x_400_ = v_reuseFailAlloc_403_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_box(v___x_384_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
return v___x_402_;
}
}
else
{
lean_object* v___x_405_; 
lean_dec_ref(v_x_362_);
if (v_isShared_387_ == 0)
{
lean_ctor_set(v___x_386_, 1, v_buckets_x27_391_);
lean_ctor_set(v___x_386_, 0, v_size_x27_389_);
v___x_405_ = v___x_386_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v_size_x27_389_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v_buckets_x27_391_);
v___x_405_ = v_reuseFailAlloc_408_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_406_ = lean_box(v___x_384_);
v___x_407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v___x_405_);
return v___x_407_;
}
}
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v_b_365_);
lean_dec(v_a_364_);
lean_dec_ref(v_x_362_);
v___x_412_ = lean_box(v___x_384_);
v___x_413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_m_363_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_414_, lean_object* v_00_u03b2_415_, lean_object* v_x_416_, lean_object* v_x_417_, lean_object* v_m_418_, lean_object* v_a_419_, lean_object* v_b_420_){
_start:
{
lean_object* v_size_421_; lean_object* v_buckets_422_; lean_object* v___x_423_; lean_object* v___x_424_; uint64_t v___x_425_; uint64_t v___x_426_; uint64_t v___x_427_; uint64_t v___x_428_; uint64_t v_fold_429_; uint64_t v___x_430_; uint64_t v___x_431_; uint64_t v___x_432_; size_t v___x_433_; size_t v___x_434_; size_t v___x_435_; size_t v___x_436_; size_t v___x_437_; lean_object* v_bkt_438_; uint8_t v___x_439_; 
v_size_421_ = lean_ctor_get(v_m_418_, 0);
v_buckets_422_ = lean_ctor_get(v_m_418_, 1);
v___x_423_ = lean_array_get_size(v_buckets_422_);
lean_inc_ref(v_x_417_);
lean_inc_n(v_a_419_, 2);
v___x_424_ = lean_apply_1(v_x_417_, v_a_419_);
v___x_425_ = 32ULL;
v___x_426_ = lean_unbox_uint64(v___x_424_);
v___x_427_ = lean_uint64_shift_right(v___x_426_, v___x_425_);
v___x_428_ = lean_unbox_uint64(v___x_424_);
lean_dec_ref(v___x_424_);
v_fold_429_ = lean_uint64_xor(v___x_428_, v___x_427_);
v___x_430_ = 16ULL;
v___x_431_ = lean_uint64_shift_right(v_fold_429_, v___x_430_);
v___x_432_ = lean_uint64_xor(v_fold_429_, v___x_431_);
v___x_433_ = lean_uint64_to_usize(v___x_432_);
v___x_434_ = lean_usize_of_nat(v___x_423_);
v___x_435_ = ((size_t)1ULL);
v___x_436_ = lean_usize_sub(v___x_434_, v___x_435_);
v___x_437_ = lean_usize_land(v___x_433_, v___x_436_);
v_bkt_438_ = lean_array_uget_borrowed(v_buckets_422_, v___x_437_);
lean_inc(v_bkt_438_);
v___x_439_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_416_, v_a_419_, v_bkt_438_);
if (v___x_439_ == 0)
{
lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_464_; 
lean_inc_ref(v_buckets_422_);
lean_inc(v_size_421_);
v_isSharedCheck_464_ = !lean_is_exclusive(v_m_418_);
if (v_isSharedCheck_464_ == 0)
{
lean_object* v_unused_465_; lean_object* v_unused_466_; 
v_unused_465_ = lean_ctor_get(v_m_418_, 1);
lean_dec(v_unused_465_);
v_unused_466_ = lean_ctor_get(v_m_418_, 0);
lean_dec(v_unused_466_);
v___x_441_ = v_m_418_;
v_isShared_442_ = v_isSharedCheck_464_;
goto v_resetjp_440_;
}
else
{
lean_dec(v_m_418_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_464_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v_size_x27_444_; lean_object* v___x_445_; lean_object* v_buckets_x27_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_443_ = lean_unsigned_to_nat(1u);
v_size_x27_444_ = lean_nat_add(v_size_421_, v___x_443_);
lean_dec(v_size_421_);
lean_inc(v_bkt_438_);
v___x_445_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_445_, 0, v_a_419_);
lean_ctor_set(v___x_445_, 1, v_b_420_);
lean_ctor_set(v___x_445_, 2, v_bkt_438_);
v_buckets_x27_446_ = lean_array_uset(v_buckets_422_, v___x_437_, v___x_445_);
v___x_447_ = lean_unsigned_to_nat(4u);
v___x_448_ = lean_nat_mul(v_size_x27_444_, v___x_447_);
v___x_449_ = lean_unsigned_to_nat(3u);
v___x_450_ = lean_nat_div(v___x_448_, v___x_449_);
lean_dec(v___x_448_);
v___x_451_ = lean_array_get_size(v_buckets_x27_446_);
v___x_452_ = lean_nat_dec_le(v___x_450_, v___x_451_);
lean_dec(v___x_450_);
if (v___x_452_ == 0)
{
lean_object* v_val_453_; lean_object* v___x_455_; 
v_val_453_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_417_, v_buckets_x27_446_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v_val_453_);
lean_ctor_set(v___x_441_, 0, v_size_x27_444_);
v___x_455_ = v___x_441_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v_size_x27_444_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_val_453_);
v___x_455_ = v_reuseFailAlloc_458_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_box(v___x_439_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
return v___x_457_;
}
}
else
{
lean_object* v___x_460_; 
lean_dec_ref(v_x_417_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v_buckets_x27_446_);
lean_ctor_set(v___x_441_, 0, v_size_x27_444_);
v___x_460_ = v___x_441_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_size_x27_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_buckets_x27_446_);
v___x_460_ = v_reuseFailAlloc_463_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_box(v___x_439_);
v___x_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___x_460_);
return v___x_462_;
}
}
}
}
else
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_b_420_);
lean_dec(v_a_419_);
lean_dec_ref(v_x_417_);
v___x_467_ = lean_box(v___x_439_);
v___x_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_468_, 0, v___x_467_);
lean_ctor_set(v___x_468_, 1, v_m_418_);
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_469_, lean_object* v_x_470_, lean_object* v_m_471_, lean_object* v_a_472_, lean_object* v_b_473_){
_start:
{
lean_object* v_size_474_; lean_object* v_buckets_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint64_t v___x_478_; uint64_t v___x_479_; uint64_t v___x_480_; uint64_t v___x_481_; uint64_t v_fold_482_; uint64_t v___x_483_; uint64_t v___x_484_; uint64_t v___x_485_; size_t v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v_bkt_491_; lean_object* v___x_492_; 
v_size_474_ = lean_ctor_get(v_m_471_, 0);
v_buckets_475_ = lean_ctor_get(v_m_471_, 1);
v___x_476_ = lean_array_get_size(v_buckets_475_);
lean_inc_ref(v_x_470_);
lean_inc_n(v_a_472_, 2);
v___x_477_ = lean_apply_1(v_x_470_, v_a_472_);
v___x_478_ = 32ULL;
v___x_479_ = lean_unbox_uint64(v___x_477_);
v___x_480_ = lean_uint64_shift_right(v___x_479_, v___x_478_);
v___x_481_ = lean_unbox_uint64(v___x_477_);
lean_dec_ref(v___x_477_);
v_fold_482_ = lean_uint64_xor(v___x_481_, v___x_480_);
v___x_483_ = 16ULL;
v___x_484_ = lean_uint64_shift_right(v_fold_482_, v___x_483_);
v___x_485_ = lean_uint64_xor(v_fold_482_, v___x_484_);
v___x_486_ = lean_uint64_to_usize(v___x_485_);
v___x_487_ = lean_usize_of_nat(v___x_476_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_sub(v___x_487_, v___x_488_);
v___x_490_ = lean_usize_land(v___x_486_, v___x_489_);
v_bkt_491_ = lean_array_uget_borrowed(v_buckets_475_, v___x_490_);
lean_inc(v_bkt_491_);
v___x_492_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_469_, v_a_472_, v_bkt_491_);
if (lean_obj_tag(v___x_492_) == 0)
{
lean_object* v___x_494_; uint8_t v_isShared_495_; uint8_t v_isSharedCheck_515_; 
lean_inc_ref(v_buckets_475_);
lean_inc(v_size_474_);
v_isSharedCheck_515_ = !lean_is_exclusive(v_m_471_);
if (v_isSharedCheck_515_ == 0)
{
lean_object* v_unused_516_; lean_object* v_unused_517_; 
v_unused_516_ = lean_ctor_get(v_m_471_, 1);
lean_dec(v_unused_516_);
v_unused_517_ = lean_ctor_get(v_m_471_, 0);
lean_dec(v_unused_517_);
v___x_494_ = v_m_471_;
v_isShared_495_ = v_isSharedCheck_515_;
goto v_resetjp_493_;
}
else
{
lean_dec(v_m_471_);
v___x_494_ = lean_box(0);
v_isShared_495_ = v_isSharedCheck_515_;
goto v_resetjp_493_;
}
v_resetjp_493_:
{
lean_object* v___x_496_; lean_object* v_size_x27_497_; lean_object* v___x_498_; lean_object* v_buckets_x27_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; uint8_t v___x_505_; 
v___x_496_ = lean_unsigned_to_nat(1u);
v_size_x27_497_ = lean_nat_add(v_size_474_, v___x_496_);
lean_dec(v_size_474_);
lean_inc(v_bkt_491_);
v___x_498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_498_, 0, v_a_472_);
lean_ctor_set(v___x_498_, 1, v_b_473_);
lean_ctor_set(v___x_498_, 2, v_bkt_491_);
v_buckets_x27_499_ = lean_array_uset(v_buckets_475_, v___x_490_, v___x_498_);
v___x_500_ = lean_unsigned_to_nat(4u);
v___x_501_ = lean_nat_mul(v_size_x27_497_, v___x_500_);
v___x_502_ = lean_unsigned_to_nat(3u);
v___x_503_ = lean_nat_div(v___x_501_, v___x_502_);
lean_dec(v___x_501_);
v___x_504_ = lean_array_get_size(v_buckets_x27_499_);
v___x_505_ = lean_nat_dec_le(v___x_503_, v___x_504_);
lean_dec(v___x_503_);
if (v___x_505_ == 0)
{
lean_object* v_val_506_; lean_object* v___x_508_; 
v_val_506_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_470_, v_buckets_x27_499_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v_val_506_);
lean_ctor_set(v___x_494_, 0, v_size_x27_497_);
v___x_508_ = v___x_494_;
goto v_reusejp_507_;
}
else
{
lean_object* v_reuseFailAlloc_510_; 
v_reuseFailAlloc_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_510_, 0, v_size_x27_497_);
lean_ctor_set(v_reuseFailAlloc_510_, 1, v_val_506_);
v___x_508_ = v_reuseFailAlloc_510_;
goto v_reusejp_507_;
}
v_reusejp_507_:
{
lean_object* v___x_509_; 
v___x_509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_492_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
return v___x_509_;
}
}
else
{
lean_object* v___x_512_; 
lean_dec_ref(v_x_470_);
if (v_isShared_495_ == 0)
{
lean_ctor_set(v___x_494_, 1, v_buckets_x27_499_);
lean_ctor_set(v___x_494_, 0, v_size_x27_497_);
v___x_512_ = v___x_494_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_size_x27_497_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_buckets_x27_499_);
v___x_512_ = v_reuseFailAlloc_514_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; 
v___x_513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_492_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
return v___x_513_;
}
}
}
}
else
{
lean_object* v___x_518_; 
lean_dec(v_b_473_);
lean_dec(v_a_472_);
lean_dec_ref(v_x_470_);
v___x_518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_492_);
lean_ctor_set(v___x_518_, 1, v_m_471_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_x_521_, lean_object* v_x_522_, lean_object* v_m_523_, lean_object* v_a_524_, lean_object* v_b_525_){
_start:
{
lean_object* v_size_526_; lean_object* v_buckets_527_; lean_object* v___x_528_; lean_object* v___x_529_; uint64_t v___x_530_; uint64_t v___x_531_; uint64_t v___x_532_; uint64_t v___x_533_; uint64_t v_fold_534_; uint64_t v___x_535_; uint64_t v___x_536_; uint64_t v___x_537_; size_t v___x_538_; size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; lean_object* v_bkt_543_; lean_object* v___x_544_; 
v_size_526_ = lean_ctor_get(v_m_523_, 0);
v_buckets_527_ = lean_ctor_get(v_m_523_, 1);
v___x_528_ = lean_array_get_size(v_buckets_527_);
lean_inc_ref(v_x_522_);
lean_inc_n(v_a_524_, 2);
v___x_529_ = lean_apply_1(v_x_522_, v_a_524_);
v___x_530_ = 32ULL;
v___x_531_ = lean_unbox_uint64(v___x_529_);
v___x_532_ = lean_uint64_shift_right(v___x_531_, v___x_530_);
v___x_533_ = lean_unbox_uint64(v___x_529_);
lean_dec_ref(v___x_529_);
v_fold_534_ = lean_uint64_xor(v___x_533_, v___x_532_);
v___x_535_ = 16ULL;
v___x_536_ = lean_uint64_shift_right(v_fold_534_, v___x_535_);
v___x_537_ = lean_uint64_xor(v_fold_534_, v___x_536_);
v___x_538_ = lean_uint64_to_usize(v___x_537_);
v___x_539_ = lean_usize_of_nat(v___x_528_);
v___x_540_ = ((size_t)1ULL);
v___x_541_ = lean_usize_sub(v___x_539_, v___x_540_);
v___x_542_ = lean_usize_land(v___x_538_, v___x_541_);
v_bkt_543_ = lean_array_uget_borrowed(v_buckets_527_, v___x_542_);
lean_inc(v_bkt_543_);
v___x_544_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_521_, v_a_524_, v_bkt_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_567_; 
lean_inc_ref(v_buckets_527_);
lean_inc(v_size_526_);
v_isSharedCheck_567_ = !lean_is_exclusive(v_m_523_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; lean_object* v_unused_569_; 
v_unused_568_ = lean_ctor_get(v_m_523_, 1);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_m_523_, 0);
lean_dec(v_unused_569_);
v___x_546_ = v_m_523_;
v_isShared_547_ = v_isSharedCheck_567_;
goto v_resetjp_545_;
}
else
{
lean_dec(v_m_523_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_567_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v_size_x27_549_; lean_object* v___x_550_; lean_object* v_buckets_x27_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_548_ = lean_unsigned_to_nat(1u);
v_size_x27_549_ = lean_nat_add(v_size_526_, v___x_548_);
lean_dec(v_size_526_);
lean_inc(v_bkt_543_);
v___x_550_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_550_, 0, v_a_524_);
lean_ctor_set(v___x_550_, 1, v_b_525_);
lean_ctor_set(v___x_550_, 2, v_bkt_543_);
v_buckets_x27_551_ = lean_array_uset(v_buckets_527_, v___x_542_, v___x_550_);
v___x_552_ = lean_unsigned_to_nat(4u);
v___x_553_ = lean_nat_mul(v_size_x27_549_, v___x_552_);
v___x_554_ = lean_unsigned_to_nat(3u);
v___x_555_ = lean_nat_div(v___x_553_, v___x_554_);
lean_dec(v___x_553_);
v___x_556_ = lean_array_get_size(v_buckets_x27_551_);
v___x_557_ = lean_nat_dec_le(v___x_555_, v___x_556_);
lean_dec(v___x_555_);
if (v___x_557_ == 0)
{
lean_object* v_val_558_; lean_object* v___x_560_; 
v_val_558_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_522_, v_buckets_x27_551_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v_val_558_);
lean_ctor_set(v___x_546_, 0, v_size_x27_549_);
v___x_560_ = v___x_546_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v_size_x27_549_);
lean_ctor_set(v_reuseFailAlloc_562_, 1, v_val_558_);
v___x_560_ = v_reuseFailAlloc_562_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; 
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_544_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
return v___x_561_;
}
}
else
{
lean_object* v___x_564_; 
lean_dec_ref(v_x_522_);
if (v_isShared_547_ == 0)
{
lean_ctor_set(v___x_546_, 1, v_buckets_x27_551_);
lean_ctor_set(v___x_546_, 0, v_size_x27_549_);
v___x_564_ = v___x_546_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_size_x27_549_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_buckets_x27_551_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_565_; 
v___x_565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_565_, 0, v___x_544_);
lean_ctor_set(v___x_565_, 1, v___x_564_);
return v___x_565_;
}
}
}
}
else
{
lean_object* v___x_570_; 
lean_dec(v_b_525_);
lean_dec(v_a_524_);
lean_dec_ref(v_x_522_);
v___x_570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_570_, 0, v___x_544_);
lean_ctor_set(v___x_570_, 1, v_m_523_);
return v___x_570_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg(lean_object* v_x_571_, lean_object* v_x_572_, lean_object* v_m_573_, lean_object* v_a_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_571_, v_x_572_, v_m_573_, v_a_574_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg___boxed(lean_object* v_x_576_, lean_object* v_x_577_, lean_object* v_m_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_HashMap_get_x3f___redArg(v_x_576_, v_x_577_, v_m_578_, v_a_579_);
lean_dec_ref(v_m_578_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f(lean_object* v_00_u03b1_581_, lean_object* v_00_u03b2_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_m_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_587_; 
v___x_587_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_583_, v_x_584_, v_m_585_, v_a_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___boxed(lean_object* v_00_u03b1_588_, lean_object* v_00_u03b2_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_m_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Std_HashMap_get_x3f(v_00_u03b1_588_, v_00_u03b2_589_, v_x_590_, v_x_591_, v_m_592_, v_a_593_);
lean_dec_ref(v_m_592_);
return v_res_594_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_contains___redArg(lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_m_597_, lean_object* v_a_598_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_595_, v_x_596_, v_m_597_, v_a_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___redArg___boxed(lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_m_602_, lean_object* v_a_603_){
_start:
{
uint8_t v_res_604_; lean_object* v_r_605_; 
v_res_604_ = l_Std_HashMap_contains___redArg(v_x_600_, v_x_601_, v_m_602_, v_a_603_);
lean_dec_ref(v_m_602_);
v_r_605_ = lean_box(v_res_604_);
return v_r_605_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_contains(lean_object* v_00_u03b1_606_, lean_object* v_00_u03b2_607_, lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_m_610_, lean_object* v_a_611_){
_start:
{
uint8_t v___x_612_; 
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_608_, v_x_609_, v_m_610_, v_a_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___boxed(lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_m_617_, lean_object* v_a_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_Std_HashMap_contains(v_00_u03b1_613_, v_00_u03b2_614_, v_x_615_, v_x_616_, v_m_617_, v_a_618_);
lean_dec_ref(v_m_617_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership(lean_object* v_00_u03b1_621_, lean_object* v_00_u03b2_622_, lean_object* v_inst_623_, lean_object* v_inst_624_){
_start:
{
lean_object* v___x_625_; 
v___x_625_ = lean_box(0);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___boxed(lean_object* v_00_u03b1_626_, lean_object* v_00_u03b2_627_, lean_object* v_inst_628_, lean_object* v_inst_629_){
_start:
{
lean_object* v_res_630_; 
v_res_630_ = l_Std_HashMap_instMembership(v_00_u03b1_626_, v_00_u03b2_627_, v_inst_628_, v_inst_629_);
lean_dec_ref(v_inst_629_);
lean_dec_ref(v_inst_628_);
return v_res_630_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem___redArg(lean_object* v_inst_631_, lean_object* v_inst_632_, lean_object* v_m_633_, lean_object* v_a_634_){
_start:
{
uint8_t v___x_635_; 
v___x_635_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_631_, v_inst_632_, v_m_633_, v_a_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___redArg___boxed(lean_object* v_inst_636_, lean_object* v_inst_637_, lean_object* v_m_638_, lean_object* v_a_639_){
_start:
{
uint8_t v_res_640_; lean_object* v_r_641_; 
v_res_640_ = l_Std_HashMap_instDecidableMem___redArg(v_inst_636_, v_inst_637_, v_m_638_, v_a_639_);
lean_dec_ref(v_m_638_);
v_r_641_ = lean_box(v_res_640_);
return v_r_641_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem(lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_m_646_, lean_object* v_a_647_){
_start:
{
uint8_t v___x_648_; 
v___x_648_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_644_, v_inst_645_, v_m_646_, v_a_647_);
return v___x_648_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b2_650_, lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_m_653_, lean_object* v_a_654_){
_start:
{
uint8_t v_res_655_; lean_object* v_r_656_; 
v_res_655_ = l_Std_HashMap_instDecidableMem(v_00_u03b1_649_, v_00_u03b2_650_, v_inst_651_, v_inst_652_, v_m_653_, v_a_654_);
lean_dec_ref(v_m_653_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg(lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_m_659_, lean_object* v_a_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_657_, v_x_658_, v_m_659_, v_a_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg___boxed(lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v_m_664_, lean_object* v_a_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_HashMap_get___redArg(v_x_662_, v_x_663_, v_m_664_, v_a_665_);
lean_dec_ref(v_m_664_);
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get(lean_object* v_00_u03b1_667_, lean_object* v_00_u03b2_668_, lean_object* v_x_669_, lean_object* v_x_670_, lean_object* v_m_671_, lean_object* v_a_672_, lean_object* v_h_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_669_, v_x_670_, v_m_671_, v_a_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___boxed(lean_object* v_00_u03b1_675_, lean_object* v_00_u03b2_676_, lean_object* v_x_677_, lean_object* v_x_678_, lean_object* v_m_679_, lean_object* v_a_680_, lean_object* v_h_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Std_HashMap_get(v_00_u03b1_675_, v_00_u03b2_676_, v_x_677_, v_x_678_, v_m_679_, v_a_680_, v_h_681_);
lean_dec_ref(v_m_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg(lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_m_685_, lean_object* v_a_686_, lean_object* v_fallback_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_683_, v_x_684_, v_m_685_, v_a_686_, v_fallback_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg___boxed(lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_m_691_, lean_object* v_a_692_, lean_object* v_fallback_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Std_HashMap_getD___redArg(v_x_689_, v_x_690_, v_m_691_, v_a_692_, v_fallback_693_);
lean_dec(v_fallback_693_);
lean_dec_ref(v_m_691_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_m_699_, lean_object* v_a_700_, lean_object* v_fallback_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_697_, v_x_698_, v_m_699_, v_a_700_, v_fallback_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___boxed(lean_object* v_00_u03b1_703_, lean_object* v_00_u03b2_704_, lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_m_707_, lean_object* v_a_708_, lean_object* v_fallback_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_HashMap_getD(v_00_u03b1_703_, v_00_u03b2_704_, v_x_705_, v_x_706_, v_m_707_, v_a_708_, v_fallback_709_);
lean_dec(v_fallback_709_);
lean_dec_ref(v_m_707_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg(lean_object* v_x_711_, lean_object* v_x_712_, lean_object* v_inst_713_, lean_object* v_m_714_, lean_object* v_a_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_711_, v_x_712_, v_inst_713_, v_m_714_, v_a_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg___boxed(lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_inst_719_, lean_object* v_m_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Std_HashMap_get_x21___redArg(v_x_717_, v_x_718_, v_inst_719_, v_m_720_, v_a_721_);
lean_dec_ref(v_m_720_);
lean_dec(v_inst_719_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_x_725_, lean_object* v_x_726_, lean_object* v_inst_727_, lean_object* v_m_728_, lean_object* v_a_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_725_, v_x_726_, v_inst_727_, v_m_728_, v_a_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___boxed(lean_object* v_00_u03b1_731_, lean_object* v_00_u03b2_732_, lean_object* v_x_733_, lean_object* v_x_734_, lean_object* v_inst_735_, lean_object* v_m_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l_Std_HashMap_get_x21(v_00_u03b1_731_, v_00_u03b2_732_, v_x_733_, v_x_734_, v_inst_735_, v_m_736_, v_a_737_);
lean_dec_ref(v_m_736_);
lean_dec(v_inst_735_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_m_741_, lean_object* v_a_742_, lean_object* v_h_743_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_739_, v_inst_740_, v_m_741_, v_a_742_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_745_, lean_object* v_inst_746_, lean_object* v_m_747_, lean_object* v_a_748_, lean_object* v_h_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(v_inst_745_, v_inst_746_, v_m_747_, v_a_748_, v_h_749_);
lean_dec_ref(v_m_747_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_m_753_, lean_object* v_a_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_751_, v_inst_752_, v_m_753_, v_a_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_756_, lean_object* v_inst_757_, lean_object* v_m_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(v_inst_756_, v_inst_757_, v_m_758_, v_a_759_);
lean_dec_ref(v_m_758_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_761_, lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_m_764_, lean_object* v_a_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_761_, v_inst_762_, v_inst_763_, v_m_764_, v_a_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_m_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(v_inst_767_, v_inst_768_, v_inst_769_, v_m_770_, v_a_771_);
lean_dec_ref(v_m_770_);
lean_dec(v_inst_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg(lean_object* v_inst_773_, lean_object* v_inst_774_){
_start:
{
lean_object* v___f_775_; lean_object* v___f_776_; lean_object* v___f_777_; lean_object* v___x_778_; 
lean_inc_ref_n(v_inst_774_, 2);
lean_inc_ref_n(v_inst_773_, 2);
v___f_775_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_775_, 0, v_inst_773_);
lean_closure_set(v___f_775_, 1, v_inst_774_);
v___f_776_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_776_, 0, v_inst_773_);
lean_closure_set(v___f_776_, 1, v_inst_774_);
v___f_777_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_777_, 0, v_inst_773_);
lean_closure_set(v___f_777_, 1, v_inst_774_);
v___x_778_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_778_, 0, v___f_775_);
lean_ctor_set(v___x_778_, 1, v___f_776_);
lean_ctor_set(v___x_778_, 2, v___f_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_inst_781_, lean_object* v_inst_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_HashMap_instGetElem_x3fMem___redArg(v_inst_781_, v_inst_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg(lean_object* v_x_784_, lean_object* v_x_785_, lean_object* v_m_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_784_, v_x_785_, v_m_786_, v_a_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg___boxed(lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_m_791_, lean_object* v_a_792_){
_start:
{
lean_object* v_res_793_; 
v_res_793_ = l_Std_HashMap_getKey_x3f___redArg(v_x_789_, v_x_790_, v_m_791_, v_a_792_);
lean_dec_ref(v_m_791_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f(lean_object* v_00_u03b1_794_, lean_object* v_00_u03b2_795_, lean_object* v_x_796_, lean_object* v_x_797_, lean_object* v_m_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_796_, v_x_797_, v_m_798_, v_a_799_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_801_, lean_object* v_00_u03b2_802_, lean_object* v_x_803_, lean_object* v_x_804_, lean_object* v_m_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Std_HashMap_getKey_x3f(v_00_u03b1_801_, v_00_u03b2_802_, v_x_803_, v_x_804_, v_m_805_, v_a_806_);
lean_dec_ref(v_m_805_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg(lean_object* v_x_808_, lean_object* v_x_809_, lean_object* v_m_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_808_, v_x_809_, v_m_810_, v_a_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg___boxed(lean_object* v_x_813_, lean_object* v_x_814_, lean_object* v_m_815_, lean_object* v_a_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_Std_HashMap_getKey___redArg(v_x_813_, v_x_814_, v_m_815_, v_a_816_);
lean_dec_ref(v_m_815_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey(lean_object* v_00_u03b1_818_, lean_object* v_00_u03b2_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_m_822_, lean_object* v_a_823_, lean_object* v_h_824_){
_start:
{
lean_object* v___x_825_; 
v___x_825_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_820_, v_x_821_, v_m_822_, v_a_823_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___boxed(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_x_828_, lean_object* v_x_829_, lean_object* v_m_830_, lean_object* v_a_831_, lean_object* v_h_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Std_HashMap_getKey(v_00_u03b1_826_, v_00_u03b2_827_, v_x_828_, v_x_829_, v_m_830_, v_a_831_, v_h_832_);
lean_dec_ref(v_m_830_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg(lean_object* v_x_834_, lean_object* v_x_835_, lean_object* v_m_836_, lean_object* v_a_837_, lean_object* v_fallback_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_834_, v_x_835_, v_m_836_, v_a_837_, v_fallback_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg___boxed(lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_m_842_, lean_object* v_a_843_, lean_object* v_fallback_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Std_HashMap_getKeyD___redArg(v_x_840_, v_x_841_, v_m_842_, v_a_843_, v_fallback_844_);
lean_dec(v_fallback_844_);
lean_dec_ref(v_m_842_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD(lean_object* v_00_u03b1_846_, lean_object* v_00_u03b2_847_, lean_object* v_x_848_, lean_object* v_x_849_, lean_object* v_m_850_, lean_object* v_a_851_, lean_object* v_fallback_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_848_, v_x_849_, v_m_850_, v_a_851_, v_fallback_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___boxed(lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_m_858_, lean_object* v_a_859_, lean_object* v_fallback_860_){
_start:
{
lean_object* v_res_861_; 
v_res_861_ = l_Std_HashMap_getKeyD(v_00_u03b1_854_, v_00_u03b2_855_, v_x_856_, v_x_857_, v_m_858_, v_a_859_, v_fallback_860_);
lean_dec(v_fallback_860_);
lean_dec_ref(v_m_858_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg(lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_inst_864_, lean_object* v_m_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_862_, v_x_863_, v_inst_864_, v_m_865_, v_a_866_);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg___boxed(lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_inst_870_, lean_object* v_m_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Std_HashMap_getKey_x21___redArg(v_x_868_, v_x_869_, v_inst_870_, v_m_871_, v_a_872_);
lean_dec_ref(v_m_871_);
lean_dec(v_inst_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21(lean_object* v_00_u03b1_874_, lean_object* v_00_u03b2_875_, lean_object* v_x_876_, lean_object* v_x_877_, lean_object* v_inst_878_, lean_object* v_m_879_, lean_object* v_a_880_){
_start:
{
lean_object* v___x_881_; 
v___x_881_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_876_, v_x_877_, v_inst_878_, v_m_879_, v_a_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___boxed(lean_object* v_00_u03b1_882_, lean_object* v_00_u03b2_883_, lean_object* v_x_884_, lean_object* v_x_885_, lean_object* v_inst_886_, lean_object* v_m_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Std_HashMap_getKey_x21(v_00_u03b1_882_, v_00_u03b2_883_, v_x_884_, v_x_885_, v_inst_886_, v_m_887_, v_a_888_);
lean_dec_ref(v_m_887_);
lean_dec(v_inst_886_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase___redArg(lean_object* v_x_890_, lean_object* v_x_891_, lean_object* v_m_892_, lean_object* v_a_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_890_, v_x_891_, v_m_892_, v_a_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase(lean_object* v_00_u03b1_895_, lean_object* v_00_u03b2_896_, lean_object* v_x_897_, lean_object* v_x_898_, lean_object* v_m_899_, lean_object* v_a_900_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_897_, v_x_898_, v_m_899_, v_a_900_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg(lean_object* v_m_902_){
_start:
{
lean_object* v_size_903_; 
v_size_903_ = lean_ctor_get(v_m_902_, 0);
lean_inc(v_size_903_);
return v_size_903_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg___boxed(lean_object* v_m_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_HashMap_size___redArg(v_m_904_);
lean_dec_ref(v_m_904_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size(lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_m_910_){
_start:
{
lean_object* v_size_911_; 
v_size_911_ = lean_ctor_get(v_m_910_, 0);
lean_inc(v_size_911_);
return v_size_911_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___boxed(lean_object* v_00_u03b1_912_, lean_object* v_00_u03b2_913_, lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_m_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Std_HashMap_size(v_00_u03b1_912_, v_00_u03b2_913_, v_x_914_, v_x_915_, v_m_916_);
lean_dec_ref(v_m_916_);
lean_dec_ref(v_x_915_);
lean_dec_ref(v_x_914_);
return v_res_917_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty___redArg(lean_object* v_m_918_){
_start:
{
lean_object* v_size_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_size_919_ = lean_ctor_get(v_m_918_, 0);
v___x_920_ = lean_unsigned_to_nat(0u);
v___x_921_ = lean_nat_dec_eq(v_size_919_, v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___redArg___boxed(lean_object* v_m_922_){
_start:
{
uint8_t v_res_923_; lean_object* v_r_924_; 
v_res_923_ = l_Std_HashMap_isEmpty___redArg(v_m_922_);
lean_dec_ref(v_m_922_);
v_r_924_ = lean_box(v_res_923_);
return v_r_924_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty(lean_object* v_00_u03b1_925_, lean_object* v_00_u03b2_926_, lean_object* v_x_927_, lean_object* v_x_928_, lean_object* v_m_929_){
_start:
{
lean_object* v_size_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v_size_930_ = lean_ctor_get(v_m_929_, 0);
v___x_931_ = lean_unsigned_to_nat(0u);
v___x_932_ = lean_nat_dec_eq(v_size_930_, v___x_931_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___boxed(lean_object* v_00_u03b1_933_, lean_object* v_00_u03b2_934_, lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_m_937_){
_start:
{
uint8_t v_res_938_; lean_object* v_r_939_; 
v_res_938_ = l_Std_HashMap_isEmpty(v_00_u03b1_933_, v_00_u03b2_934_, v_x_935_, v_x_936_, v_m_937_);
lean_dec_ref(v_m_937_);
lean_dec_ref(v_x_936_);
lean_dec_ref(v_x_935_);
v_r_939_ = lean_box(v_res_938_);
return v_r_939_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0(lean_object* v_a_940_, lean_object* v_b_941_, lean_object* v_d_942_){
_start:
{
lean_object* v___x_943_; 
v___x_943_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_943_, 0, v_a_940_);
lean_ctor_set(v___x_943_, 1, v_d_942_);
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0___boxed(lean_object* v_a_944_, lean_object* v_b_945_, lean_object* v_d_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l_Std_HashMap_keys___redArg___lam__0(v_a_944_, v_b_945_, v_d_946_);
lean_dec(v_b_945_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__1(lean_object* v___x_948_, lean_object* v___f_949_, lean_object* v_l_950_, lean_object* v_acc_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_948_, v___f_949_, v_acc_951_, v_l_950_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg(lean_object* v_m_976_){
_start:
{
lean_object* v___x_977_; lean_object* v_buckets_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_977_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_978_ = lean_ctor_get(v_m_976_, 1);
lean_inc_ref(v_buckets_978_);
lean_dec_ref(v_m_976_);
v___x_979_ = lean_box(0);
v___x_980_ = lean_array_get_size(v_buckets_978_);
v___x_981_ = lean_unsigned_to_nat(0u);
v___x_982_ = lean_nat_dec_lt(v___x_981_, v___x_980_);
if (v___x_982_ == 0)
{
lean_dec_ref(v_buckets_978_);
return v___x_979_;
}
else
{
lean_object* v___f_983_; size_t v___x_984_; size_t v___x_985_; lean_object* v___x_986_; 
v___f_983_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__11));
v___x_984_ = lean_usize_of_nat(v___x_980_);
v___x_985_ = ((size_t)0ULL);
v___x_986_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_977_, v___f_983_, v_buckets_978_, v___x_984_, v___x_985_, v___x_979_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys(lean_object* v_00_u03b1_987_, lean_object* v_00_u03b2_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_m_991_){
_start:
{
lean_object* v___x_992_; lean_object* v_buckets_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_992_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_993_ = lean_ctor_get(v_m_991_, 1);
lean_inc_ref(v_buckets_993_);
lean_dec_ref(v_m_991_);
v___x_994_ = lean_box(0);
v___x_995_ = lean_array_get_size(v_buckets_993_);
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = lean_nat_dec_lt(v___x_996_, v___x_995_);
if (v___x_997_ == 0)
{
lean_dec_ref(v_buckets_993_);
return v___x_994_;
}
else
{
lean_object* v___f_998_; size_t v___x_999_; size_t v___x_1000_; lean_object* v___x_1001_; 
v___f_998_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__11));
v___x_999_ = lean_usize_of_nat(v___x_995_);
v___x_1000_ = ((size_t)0ULL);
v___x_1001_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_992_, v___f_998_, v_buckets_993_, v___x_999_, v___x_1000_, v___x_994_);
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___boxed(lean_object* v_00_u03b1_1002_, lean_object* v_00_u03b2_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_m_1006_){
_start:
{
lean_object* v_res_1007_; 
v_res_1007_ = l_Std_HashMap_keys(v_00_u03b1_1002_, v_00_u03b2_1003_, v_x_1004_, v_x_1005_, v_m_1006_);
lean_dec_ref(v_x_1005_);
lean_dec_ref(v_x_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList___redArg(lean_object* v_inst_1012_, lean_object* v_inst_1013_, lean_object* v_l_1014_){
_start:
{
lean_object* v___f_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___f_1015_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1016_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1017_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1015_, v_inst_1012_, v_inst_1013_, v___x_1016_, v_l_1014_);
return v___x_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList(lean_object* v_00_u03b1_1018_, lean_object* v_00_u03b2_1019_, lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_l_1022_){
_start:
{
lean_object* v___f_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___f_1023_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1024_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1025_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1023_, v_inst_1020_, v_inst_1021_, v___x_1024_, v_l_1022_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList___redArg(lean_object* v_inst_1026_, lean_object* v_inst_1027_, lean_object* v_l_1028_){
_start:
{
lean_object* v___f_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___f_1029_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1030_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1031_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1029_, v_inst_1026_, v_inst_1027_, v___x_1030_, v_l_1028_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList(lean_object* v_00_u03b1_1032_, lean_object* v_inst_1033_, lean_object* v_inst_1034_, lean_object* v_l_1035_){
_start:
{
lean_object* v___f_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___f_1036_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1037_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1038_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1036_, v_inst_1033_, v_inst_1034_, v___x_1037_, v_l_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray___redArg(lean_object* v_inst_1043_, lean_object* v_inst_1044_, lean_object* v_a_1045_){
_start:
{
lean_object* v___f_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___f_1046_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1047_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1048_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1046_, v_inst_1043_, v_inst_1044_, v___x_1047_, v_a_1045_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray(lean_object* v_00_u03b1_1049_, lean_object* v_00_u03b2_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v___f_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___f_1054_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1055_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1056_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1054_, v_inst_1051_, v_inst_1052_, v___x_1055_, v_a_1053_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__0(lean_object* v_a_1057_, lean_object* v_b_1058_, lean_object* v_d_1059_){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_a_1057_);
lean_ctor_set(v___x_1060_, 1, v_b_1058_);
v___x_1061_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v_d_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__1(lean_object* v___x_1062_, lean_object* v___f_1063_, lean_object* v_l_1064_, lean_object* v_acc_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1062_, v___f_1063_, v_acc_1065_, v_l_1064_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg(lean_object* v_m_1071_){
_start:
{
lean_object* v___x_1072_; lean_object* v_buckets_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1072_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1073_ = lean_ctor_get(v_m_1071_, 1);
lean_inc_ref(v_buckets_1073_);
lean_dec_ref(v_m_1071_);
v___x_1074_ = lean_box(0);
v___x_1075_ = lean_array_get_size(v_buckets_1073_);
v___x_1076_ = lean_unsigned_to_nat(0u);
v___x_1077_ = lean_nat_dec_lt(v___x_1076_, v___x_1075_);
if (v___x_1077_ == 0)
{
lean_dec_ref(v_buckets_1073_);
return v___x_1074_;
}
else
{
lean_object* v___f_1078_; size_t v___x_1079_; size_t v___x_1080_; lean_object* v___x_1081_; 
v___f_1078_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__1));
v___x_1079_ = lean_usize_of_nat(v___x_1075_);
v___x_1080_ = ((size_t)0ULL);
v___x_1081_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1072_, v___f_1078_, v_buckets_1073_, v___x_1079_, v___x_1080_, v___x_1074_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList(lean_object* v_00_u03b1_1082_, lean_object* v_00_u03b2_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_m_1086_){
_start:
{
lean_object* v___x_1087_; lean_object* v_buckets_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; uint8_t v___x_1092_; 
v___x_1087_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1088_ = lean_ctor_get(v_m_1086_, 1);
lean_inc_ref(v_buckets_1088_);
lean_dec_ref(v_m_1086_);
v___x_1089_ = lean_box(0);
v___x_1090_ = lean_array_get_size(v_buckets_1088_);
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = lean_nat_dec_lt(v___x_1091_, v___x_1090_);
if (v___x_1092_ == 0)
{
lean_dec_ref(v_buckets_1088_);
return v___x_1089_;
}
else
{
lean_object* v___f_1093_; size_t v___x_1094_; size_t v___x_1095_; lean_object* v___x_1096_; 
v___f_1093_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__1));
v___x_1094_ = lean_usize_of_nat(v___x_1090_);
v___x_1095_ = ((size_t)0ULL);
v___x_1096_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1087_, v___f_1093_, v_buckets_1088_, v___x_1094_, v___x_1095_, v___x_1089_);
return v___x_1096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___boxed(lean_object* v_00_u03b1_1097_, lean_object* v_00_u03b2_1098_, lean_object* v_x_1099_, lean_object* v_x_1100_, lean_object* v_m_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_HashMap_toList(v_00_u03b1_1097_, v_00_u03b2_1098_, v_x_1099_, v_x_1100_, v_m_1101_);
lean_dec_ref(v_x_1100_);
lean_dec_ref(v_x_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg___lam__0(lean_object* v_inst_1103_, lean_object* v_f_1104_, lean_object* v_acc_1105_, lean_object* v_l_1106_){
_start:
{
lean_object* v___x_1107_; 
v___x_1107_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1103_, v_f_1104_, v_acc_1105_, v_l_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg(lean_object* v_inst_1108_, lean_object* v_f_1109_, lean_object* v_init_1110_, lean_object* v_b_1111_){
_start:
{
lean_object* v_buckets_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v_buckets_1112_ = lean_ctor_get(v_b_1111_, 1);
lean_inc_ref(v_buckets_1112_);
lean_dec_ref(v_b_1111_);
v___x_1113_ = lean_unsigned_to_nat(0u);
v___x_1114_ = lean_array_get_size(v_buckets_1112_);
v___x_1115_ = lean_nat_dec_lt(v___x_1113_, v___x_1114_);
if (v___x_1115_ == 0)
{
lean_object* v_toApplicative_1116_; lean_object* v_toPure_1117_; lean_object* v___x_1118_; 
lean_dec_ref(v_buckets_1112_);
lean_dec(v_f_1109_);
v_toApplicative_1116_ = lean_ctor_get(v_inst_1108_, 0);
lean_inc_ref(v_toApplicative_1116_);
lean_dec_ref(v_inst_1108_);
v_toPure_1117_ = lean_ctor_get(v_toApplicative_1116_, 1);
lean_inc(v_toPure_1117_);
lean_dec_ref(v_toApplicative_1116_);
v___x_1118_ = lean_apply_2(v_toPure_1117_, lean_box(0), v_init_1110_);
return v___x_1118_;
}
else
{
lean_object* v___f_1119_; uint8_t v___x_1120_; 
lean_inc_ref(v_inst_1108_);
v___f_1119_ = lean_alloc_closure((void*)(l_Std_HashMap_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1119_, 0, v_inst_1108_);
lean_closure_set(v___f_1119_, 1, v_f_1109_);
v___x_1120_ = lean_nat_dec_le(v___x_1114_, v___x_1114_);
if (v___x_1120_ == 0)
{
if (v___x_1115_ == 0)
{
lean_object* v_toApplicative_1121_; lean_object* v_toPure_1122_; lean_object* v___x_1123_; 
lean_dec_ref(v___f_1119_);
lean_dec_ref(v_buckets_1112_);
v_toApplicative_1121_ = lean_ctor_get(v_inst_1108_, 0);
lean_inc_ref(v_toApplicative_1121_);
lean_dec_ref(v_inst_1108_);
v_toPure_1122_ = lean_ctor_get(v_toApplicative_1121_, 1);
lean_inc(v_toPure_1122_);
lean_dec_ref(v_toApplicative_1121_);
v___x_1123_ = lean_apply_2(v_toPure_1122_, lean_box(0), v_init_1110_);
return v___x_1123_;
}
else
{
size_t v___x_1124_; size_t v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((size_t)0ULL);
v___x_1125_ = lean_usize_of_nat(v___x_1114_);
v___x_1126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1108_, v___f_1119_, v_buckets_1112_, v___x_1124_, v___x_1125_, v_init_1110_);
return v___x_1126_;
}
}
else
{
size_t v___x_1127_; size_t v___x_1128_; lean_object* v___x_1129_; 
v___x_1127_ = ((size_t)0ULL);
v___x_1128_ = lean_usize_of_nat(v___x_1114_);
v___x_1129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1108_, v___f_1119_, v_buckets_1112_, v___x_1127_, v___x_1128_, v_init_1110_);
return v___x_1129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM(lean_object* v_00_u03b1_1130_, lean_object* v_00_u03b2_1131_, lean_object* v_x_1132_, lean_object* v_x_1133_, lean_object* v_m_1134_, lean_object* v_inst_1135_, lean_object* v_00_u03b3_1136_, lean_object* v_f_1137_, lean_object* v_init_1138_, lean_object* v_b_1139_){
_start:
{
lean_object* v_buckets_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v_buckets_1140_ = lean_ctor_get(v_b_1139_, 1);
lean_inc_ref(v_buckets_1140_);
lean_dec_ref(v_b_1139_);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_array_get_size(v_buckets_1140_);
v___x_1143_ = lean_nat_dec_lt(v___x_1141_, v___x_1142_);
if (v___x_1143_ == 0)
{
lean_object* v_toApplicative_1144_; lean_object* v_toPure_1145_; lean_object* v___x_1146_; 
lean_dec_ref(v_buckets_1140_);
lean_dec(v_f_1137_);
v_toApplicative_1144_ = lean_ctor_get(v_inst_1135_, 0);
lean_inc_ref(v_toApplicative_1144_);
lean_dec_ref(v_inst_1135_);
v_toPure_1145_ = lean_ctor_get(v_toApplicative_1144_, 1);
lean_inc(v_toPure_1145_);
lean_dec_ref(v_toApplicative_1144_);
v___x_1146_ = lean_apply_2(v_toPure_1145_, lean_box(0), v_init_1138_);
return v___x_1146_;
}
else
{
lean_object* v___f_1147_; uint8_t v___x_1148_; 
lean_inc_ref(v_inst_1135_);
v___f_1147_ = lean_alloc_closure((void*)(l_Std_HashMap_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1147_, 0, v_inst_1135_);
lean_closure_set(v___f_1147_, 1, v_f_1137_);
v___x_1148_ = lean_nat_dec_le(v___x_1142_, v___x_1142_);
if (v___x_1148_ == 0)
{
if (v___x_1143_ == 0)
{
lean_object* v_toApplicative_1149_; lean_object* v_toPure_1150_; lean_object* v___x_1151_; 
lean_dec_ref(v___f_1147_);
lean_dec_ref(v_buckets_1140_);
v_toApplicative_1149_ = lean_ctor_get(v_inst_1135_, 0);
lean_inc_ref(v_toApplicative_1149_);
lean_dec_ref(v_inst_1135_);
v_toPure_1150_ = lean_ctor_get(v_toApplicative_1149_, 1);
lean_inc(v_toPure_1150_);
lean_dec_ref(v_toApplicative_1149_);
v___x_1151_ = lean_apply_2(v_toPure_1150_, lean_box(0), v_init_1138_);
return v___x_1151_;
}
else
{
size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
v___x_1152_ = ((size_t)0ULL);
v___x_1153_ = lean_usize_of_nat(v___x_1142_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1135_, v___f_1147_, v_buckets_1140_, v___x_1152_, v___x_1153_, v_init_1138_);
return v___x_1154_;
}
}
else
{
size_t v___x_1155_; size_t v___x_1156_; lean_object* v___x_1157_; 
v___x_1155_ = ((size_t)0ULL);
v___x_1156_ = lean_usize_of_nat(v___x_1142_);
v___x_1157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1135_, v___f_1147_, v_buckets_1140_, v___x_1155_, v___x_1156_, v_init_1138_);
return v___x_1157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___boxed(lean_object* v_00_u03b1_1158_, lean_object* v_00_u03b2_1159_, lean_object* v_x_1160_, lean_object* v_x_1161_, lean_object* v_m_1162_, lean_object* v_inst_1163_, lean_object* v_00_u03b3_1164_, lean_object* v_f_1165_, lean_object* v_init_1166_, lean_object* v_b_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_HashMap_foldM(v_00_u03b1_1158_, v_00_u03b2_1159_, v_x_1160_, v_x_1161_, v_m_1162_, v_inst_1163_, v_00_u03b3_1164_, v_f_1165_, v_init_1166_, v_b_1167_);
lean_dec_ref(v_x_1161_);
lean_dec_ref(v_x_1160_);
return v_res_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__0(lean_object* v_f_1169_, lean_object* v_x1_1170_, lean_object* v_x2_1171_, lean_object* v_x3_1172_){
_start:
{
lean_object* v___x_1173_; 
v___x_1173_ = lean_apply_3(v_f_1169_, v_x1_1170_, v_x2_1171_, v_x3_1172_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__1(lean_object* v___x_1174_, lean_object* v___f_1175_, lean_object* v_acc_1176_, lean_object* v_l_1177_){
_start:
{
lean_object* v___x_1178_; 
v___x_1178_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1174_, v___f_1175_, v_acc_1176_, v_l_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg(lean_object* v_f_1179_, lean_object* v_init_1180_, lean_object* v_b_1181_){
_start:
{
lean_object* v___x_1182_; lean_object* v_buckets_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; uint8_t v___x_1186_; 
v___x_1182_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1183_ = lean_ctor_get(v_b_1181_, 1);
lean_inc_ref(v_buckets_1183_);
lean_dec_ref(v_b_1181_);
v___x_1184_ = lean_unsigned_to_nat(0u);
v___x_1185_ = lean_array_get_size(v_buckets_1183_);
v___x_1186_ = lean_nat_dec_lt(v___x_1184_, v___x_1185_);
if (v___x_1186_ == 0)
{
lean_dec_ref(v_buckets_1183_);
lean_dec(v_f_1179_);
return v_init_1180_;
}
else
{
lean_object* v___f_1187_; lean_object* v___f_1188_; uint8_t v___x_1189_; 
v___f_1187_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1187_, 0, v_f_1179_);
v___f_1188_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1188_, 0, v___x_1182_);
lean_closure_set(v___f_1188_, 1, v___f_1187_);
v___x_1189_ = lean_nat_dec_le(v___x_1185_, v___x_1185_);
if (v___x_1189_ == 0)
{
if (v___x_1186_ == 0)
{
lean_dec_ref(v___f_1188_);
lean_dec_ref(v_buckets_1183_);
return v_init_1180_;
}
else
{
size_t v___x_1190_; size_t v___x_1191_; lean_object* v___x_1192_; 
v___x_1190_ = ((size_t)0ULL);
v___x_1191_ = lean_usize_of_nat(v___x_1185_);
v___x_1192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1182_, v___f_1188_, v_buckets_1183_, v___x_1190_, v___x_1191_, v_init_1180_);
return v___x_1192_;
}
}
else
{
size_t v___x_1193_; size_t v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = ((size_t)0ULL);
v___x_1194_ = lean_usize_of_nat(v___x_1185_);
v___x_1195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1182_, v___f_1188_, v_buckets_1183_, v___x_1193_, v___x_1194_, v_init_1180_);
return v___x_1195_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold(lean_object* v_00_u03b1_1196_, lean_object* v_00_u03b2_1197_, lean_object* v_x_1198_, lean_object* v_x_1199_, lean_object* v_00_u03b3_1200_, lean_object* v_f_1201_, lean_object* v_init_1202_, lean_object* v_b_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v_buckets_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; uint8_t v___x_1208_; 
v___x_1204_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1205_ = lean_ctor_get(v_b_1203_, 1);
lean_inc_ref(v_buckets_1205_);
lean_dec_ref(v_b_1203_);
v___x_1206_ = lean_unsigned_to_nat(0u);
v___x_1207_ = lean_array_get_size(v_buckets_1205_);
v___x_1208_ = lean_nat_dec_lt(v___x_1206_, v___x_1207_);
if (v___x_1208_ == 0)
{
lean_dec_ref(v_buckets_1205_);
lean_dec(v_f_1201_);
return v_init_1202_;
}
else
{
lean_object* v___f_1209_; lean_object* v___f_1210_; uint8_t v___x_1211_; 
v___f_1209_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1209_, 0, v_f_1201_);
v___f_1210_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1210_, 0, v___x_1204_);
lean_closure_set(v___f_1210_, 1, v___f_1209_);
v___x_1211_ = lean_nat_dec_le(v___x_1207_, v___x_1207_);
if (v___x_1211_ == 0)
{
if (v___x_1208_ == 0)
{
lean_dec_ref(v___f_1210_);
lean_dec_ref(v_buckets_1205_);
return v_init_1202_;
}
else
{
size_t v___x_1212_; size_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = ((size_t)0ULL);
v___x_1213_ = lean_usize_of_nat(v___x_1207_);
v___x_1214_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1204_, v___f_1210_, v_buckets_1205_, v___x_1212_, v___x_1213_, v_init_1202_);
return v___x_1214_;
}
}
else
{
size_t v___x_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = ((size_t)0ULL);
v___x_1216_ = lean_usize_of_nat(v___x_1207_);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1204_, v___f_1210_, v_buckets_1205_, v___x_1215_, v___x_1216_, v_init_1202_);
return v___x_1217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___boxed(lean_object* v_00_u03b1_1218_, lean_object* v_00_u03b2_1219_, lean_object* v_x_1220_, lean_object* v_x_1221_, lean_object* v_00_u03b3_1222_, lean_object* v_f_1223_, lean_object* v_init_1224_, lean_object* v_b_1225_){
_start:
{
lean_object* v_res_1226_; 
v_res_1226_ = l_Std_HashMap_fold(v_00_u03b1_1218_, v_00_u03b2_1219_, v_x_1220_, v_x_1221_, v_00_u03b3_1222_, v_f_1223_, v_init_1224_, v_b_1225_);
lean_dec_ref(v_x_1221_);
lean_dec_ref(v_x_1220_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__0(lean_object* v_f_1227_, lean_object* v_x_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = lean_apply_2(v_f_1227_, v___y_1229_, v___y_1230_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__1(lean_object* v_inst_1232_, lean_object* v___f_1233_, lean_object* v_x_1234_, lean_object* v___y_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_box(0);
v___x_1237_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1232_, v___f_1233_, v___x_1236_, v___y_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg(lean_object* v_inst_1238_, lean_object* v_f_1239_, lean_object* v_b_1240_){
_start:
{
lean_object* v_buckets_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v_buckets_1241_ = lean_ctor_get(v_b_1240_, 1);
lean_inc_ref(v_buckets_1241_);
lean_dec_ref(v_b_1240_);
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = lean_array_get_size(v_buckets_1241_);
v___x_1244_ = lean_box(0);
v___x_1245_ = lean_nat_dec_lt(v___x_1242_, v___x_1243_);
if (v___x_1245_ == 0)
{
lean_object* v_toApplicative_1246_; lean_object* v_toPure_1247_; lean_object* v___x_1248_; 
lean_dec_ref(v_buckets_1241_);
lean_dec(v_f_1239_);
v_toApplicative_1246_ = lean_ctor_get(v_inst_1238_, 0);
lean_inc_ref(v_toApplicative_1246_);
lean_dec_ref(v_inst_1238_);
v_toPure_1247_ = lean_ctor_get(v_toApplicative_1246_, 1);
lean_inc(v_toPure_1247_);
lean_dec_ref(v_toApplicative_1246_);
v___x_1248_ = lean_apply_2(v_toPure_1247_, lean_box(0), v___x_1244_);
return v___x_1248_;
}
else
{
lean_object* v___f_1249_; lean_object* v___f_1250_; uint8_t v___x_1251_; 
v___f_1249_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1249_, 0, v_f_1239_);
lean_inc_ref(v_inst_1238_);
v___f_1250_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1250_, 0, v_inst_1238_);
lean_closure_set(v___f_1250_, 1, v___f_1249_);
v___x_1251_ = lean_nat_dec_le(v___x_1243_, v___x_1243_);
if (v___x_1251_ == 0)
{
if (v___x_1245_ == 0)
{
lean_object* v_toApplicative_1252_; lean_object* v_toPure_1253_; lean_object* v___x_1254_; 
lean_dec_ref(v___f_1250_);
lean_dec_ref(v_buckets_1241_);
v_toApplicative_1252_ = lean_ctor_get(v_inst_1238_, 0);
lean_inc_ref(v_toApplicative_1252_);
lean_dec_ref(v_inst_1238_);
v_toPure_1253_ = lean_ctor_get(v_toApplicative_1252_, 1);
lean_inc(v_toPure_1253_);
lean_dec_ref(v_toApplicative_1252_);
v___x_1254_ = lean_apply_2(v_toPure_1253_, lean_box(0), v___x_1244_);
return v___x_1254_;
}
else
{
size_t v___x_1255_; size_t v___x_1256_; lean_object* v___x_1257_; 
v___x_1255_ = ((size_t)0ULL);
v___x_1256_ = lean_usize_of_nat(v___x_1243_);
v___x_1257_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1238_, v___f_1250_, v_buckets_1241_, v___x_1255_, v___x_1256_, v___x_1244_);
return v___x_1257_;
}
}
else
{
size_t v___x_1258_; size_t v___x_1259_; lean_object* v___x_1260_; 
v___x_1258_ = ((size_t)0ULL);
v___x_1259_ = lean_usize_of_nat(v___x_1243_);
v___x_1260_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1238_, v___f_1250_, v_buckets_1241_, v___x_1258_, v___x_1259_, v___x_1244_);
return v___x_1260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM(lean_object* v_00_u03b1_1261_, lean_object* v_00_u03b2_1262_, lean_object* v_x_1263_, lean_object* v_x_1264_, lean_object* v_m_1265_, lean_object* v_inst_1266_, lean_object* v_f_1267_, lean_object* v_b_1268_){
_start:
{
lean_object* v_buckets_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; uint8_t v___x_1273_; 
v_buckets_1269_ = lean_ctor_get(v_b_1268_, 1);
lean_inc_ref(v_buckets_1269_);
lean_dec_ref(v_b_1268_);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_array_get_size(v_buckets_1269_);
v___x_1272_ = lean_box(0);
v___x_1273_ = lean_nat_dec_lt(v___x_1270_, v___x_1271_);
if (v___x_1273_ == 0)
{
lean_object* v_toApplicative_1274_; lean_object* v_toPure_1275_; lean_object* v___x_1276_; 
lean_dec_ref(v_buckets_1269_);
lean_dec(v_f_1267_);
v_toApplicative_1274_ = lean_ctor_get(v_inst_1266_, 0);
lean_inc_ref(v_toApplicative_1274_);
lean_dec_ref(v_inst_1266_);
v_toPure_1275_ = lean_ctor_get(v_toApplicative_1274_, 1);
lean_inc(v_toPure_1275_);
lean_dec_ref(v_toApplicative_1274_);
v___x_1276_ = lean_apply_2(v_toPure_1275_, lean_box(0), v___x_1272_);
return v___x_1276_;
}
else
{
lean_object* v___f_1277_; lean_object* v___f_1278_; uint8_t v___x_1279_; 
v___f_1277_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1277_, 0, v_f_1267_);
lean_inc_ref(v_inst_1266_);
v___f_1278_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1278_, 0, v_inst_1266_);
lean_closure_set(v___f_1278_, 1, v___f_1277_);
v___x_1279_ = lean_nat_dec_le(v___x_1271_, v___x_1271_);
if (v___x_1279_ == 0)
{
if (v___x_1273_ == 0)
{
lean_object* v_toApplicative_1280_; lean_object* v_toPure_1281_; lean_object* v___x_1282_; 
lean_dec_ref(v___f_1278_);
lean_dec_ref(v_buckets_1269_);
v_toApplicative_1280_ = lean_ctor_get(v_inst_1266_, 0);
lean_inc_ref(v_toApplicative_1280_);
lean_dec_ref(v_inst_1266_);
v_toPure_1281_ = lean_ctor_get(v_toApplicative_1280_, 1);
lean_inc(v_toPure_1281_);
lean_dec_ref(v_toApplicative_1280_);
v___x_1282_ = lean_apply_2(v_toPure_1281_, lean_box(0), v___x_1272_);
return v___x_1282_;
}
else
{
size_t v___x_1283_; size_t v___x_1284_; lean_object* v___x_1285_; 
v___x_1283_ = ((size_t)0ULL);
v___x_1284_ = lean_usize_of_nat(v___x_1271_);
v___x_1285_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1266_, v___f_1278_, v_buckets_1269_, v___x_1283_, v___x_1284_, v___x_1272_);
return v___x_1285_;
}
}
else
{
size_t v___x_1286_; size_t v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = ((size_t)0ULL);
v___x_1287_ = lean_usize_of_nat(v___x_1271_);
v___x_1288_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1266_, v___f_1278_, v_buckets_1269_, v___x_1286_, v___x_1287_, v___x_1272_);
return v___x_1288_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_x_1291_, lean_object* v_x_1292_, lean_object* v_m_1293_, lean_object* v_inst_1294_, lean_object* v_f_1295_, lean_object* v_b_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Std_HashMap_forM(v_00_u03b1_1289_, v_00_u03b2_1290_, v_x_1291_, v_x_1292_, v_m_1293_, v_inst_1294_, v_f_1295_, v_b_1296_);
lean_dec_ref(v_x_1292_);
lean_dec_ref(v_x_1291_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg___lam__0(lean_object* v_inst_1298_, lean_object* v_f_1299_, lean_object* v_a_1300_, lean_object* v_x_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1298_, v_f_1299_, v_a_1300_, v___y_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg(lean_object* v_inst_1304_, lean_object* v_f_1305_, lean_object* v_init_1306_, lean_object* v_b_1307_){
_start:
{
lean_object* v_buckets_1308_; lean_object* v___f_1309_; size_t v_sz_1310_; size_t v___x_1311_; lean_object* v___x_1312_; 
v_buckets_1308_ = lean_ctor_get(v_b_1307_, 1);
lean_inc_ref(v_buckets_1308_);
lean_dec_ref(v_b_1307_);
lean_inc_ref(v_inst_1304_);
v___f_1309_ = lean_alloc_closure((void*)(l_Std_HashMap_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1309_, 0, v_inst_1304_);
lean_closure_set(v___f_1309_, 1, v_f_1305_);
v_sz_1310_ = lean_array_size(v_buckets_1308_);
v___x_1311_ = ((size_t)0ULL);
v___x_1312_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1304_, v_buckets_1308_, v___f_1309_, v_sz_1310_, v___x_1311_, v_init_1306_);
return v___x_1312_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn(lean_object* v_00_u03b1_1313_, lean_object* v_00_u03b2_1314_, lean_object* v_x_1315_, lean_object* v_x_1316_, lean_object* v_m_1317_, lean_object* v_inst_1318_, lean_object* v_00_u03b3_1319_, lean_object* v_f_1320_, lean_object* v_init_1321_, lean_object* v_b_1322_){
_start:
{
lean_object* v_buckets_1323_; lean_object* v___f_1324_; size_t v_sz_1325_; size_t v___x_1326_; lean_object* v___x_1327_; 
v_buckets_1323_ = lean_ctor_get(v_b_1322_, 1);
lean_inc_ref(v_buckets_1323_);
lean_dec_ref(v_b_1322_);
lean_inc_ref(v_inst_1318_);
v___f_1324_ = lean_alloc_closure((void*)(l_Std_HashMap_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1324_, 0, v_inst_1318_);
lean_closure_set(v___f_1324_, 1, v_f_1320_);
v_sz_1325_ = lean_array_size(v_buckets_1323_);
v___x_1326_ = ((size_t)0ULL);
v___x_1327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1318_, v_buckets_1323_, v___f_1324_, v_sz_1325_, v___x_1326_, v_init_1321_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___boxed(lean_object* v_00_u03b1_1328_, lean_object* v_00_u03b2_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_, lean_object* v_m_1332_, lean_object* v_inst_1333_, lean_object* v_00_u03b3_1334_, lean_object* v_f_1335_, lean_object* v_init_1336_, lean_object* v_b_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_HashMap_forIn(v_00_u03b1_1328_, v_00_u03b2_1329_, v_x_1330_, v_x_1331_, v_m_1332_, v_inst_1333_, v_00_u03b3_1334_, v_f_1335_, v_init_1336_, v_b_1337_);
lean_dec_ref(v_x_1331_);
lean_dec_ref(v_x_1330_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1339_, lean_object* v_x_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_){
_start:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___y_1341_);
lean_ctor_set(v___x_1343_, 1, v___y_1342_);
v___x_1344_ = lean_apply_1(v_f_1339_, v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1345_, lean_object* v_m_1346_, lean_object* v_f_1347_){
_start:
{
lean_object* v_buckets_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_buckets_1348_ = lean_ctor_get(v_m_1346_, 1);
lean_inc_ref(v_buckets_1348_);
lean_dec_ref(v_m_1346_);
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_array_get_size(v_buckets_1348_);
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_nat_dec_lt(v___x_1349_, v___x_1350_);
if (v___x_1352_ == 0)
{
lean_object* v_toApplicative_1353_; lean_object* v_toPure_1354_; lean_object* v___x_1355_; 
lean_dec_ref(v_buckets_1348_);
lean_dec(v_f_1347_);
v_toApplicative_1353_ = lean_ctor_get(v_inst_1345_, 0);
lean_inc_ref(v_toApplicative_1353_);
lean_dec_ref(v_inst_1345_);
v_toPure_1354_ = lean_ctor_get(v_toApplicative_1353_, 1);
lean_inc(v_toPure_1354_);
lean_dec_ref(v_toApplicative_1353_);
v___x_1355_ = lean_apply_2(v_toPure_1354_, lean_box(0), v___x_1351_);
return v___x_1355_;
}
else
{
lean_object* v___f_1356_; lean_object* v___f_1357_; uint8_t v___x_1358_; 
v___f_1356_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1356_, 0, v_f_1347_);
lean_inc_ref(v_inst_1345_);
v___f_1357_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1357_, 0, v_inst_1345_);
lean_closure_set(v___f_1357_, 1, v___f_1356_);
v___x_1358_ = lean_nat_dec_le(v___x_1350_, v___x_1350_);
if (v___x_1358_ == 0)
{
if (v___x_1352_ == 0)
{
lean_object* v_toApplicative_1359_; lean_object* v_toPure_1360_; lean_object* v___x_1361_; 
lean_dec_ref(v___f_1357_);
lean_dec_ref(v_buckets_1348_);
v_toApplicative_1359_ = lean_ctor_get(v_inst_1345_, 0);
lean_inc_ref(v_toApplicative_1359_);
lean_dec_ref(v_inst_1345_);
v_toPure_1360_ = lean_ctor_get(v_toApplicative_1359_, 1);
lean_inc(v_toPure_1360_);
lean_dec_ref(v_toApplicative_1359_);
v___x_1361_ = lean_apply_2(v_toPure_1360_, lean_box(0), v___x_1351_);
return v___x_1361_;
}
else
{
size_t v___x_1362_; size_t v___x_1363_; lean_object* v___x_1364_; 
v___x_1362_ = ((size_t)0ULL);
v___x_1363_ = lean_usize_of_nat(v___x_1350_);
v___x_1364_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1345_, v___f_1357_, v_buckets_1348_, v___x_1362_, v___x_1363_, v___x_1351_);
return v___x_1364_;
}
}
else
{
size_t v___x_1365_; size_t v___x_1366_; lean_object* v___x_1367_; 
v___x_1365_ = ((size_t)0ULL);
v___x_1366_ = lean_usize_of_nat(v___x_1350_);
v___x_1367_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1345_, v___f_1357_, v_buckets_1348_, v___x_1365_, v___x_1366_, v___x_1351_);
return v___x_1367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg(lean_object* v_inst_1368_){
_start:
{
lean_object* v___f_1369_; 
v___f_1369_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1369_, 0, v_inst_1368_);
return v___f_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad(lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_m_1374_, lean_object* v_inst_1375_){
_start:
{
lean_object* v___f_1376_; 
v___f_1376_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1376_, 0, v_inst_1375_);
return v___f_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_m_1381_, lean_object* v_inst_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_Std_HashMap_instForMProdOfMonad(v_00_u03b1_1377_, v_00_u03b2_1378_, v_inst_1379_, v_inst_1380_, v_m_1381_, v_inst_1382_);
lean_dec_ref(v_inst_1380_);
lean_dec_ref(v_inst_1379_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1384_, lean_object* v_a_1385_, lean_object* v_b_1386_, lean_object* v_acc_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_a_1385_);
lean_ctor_set(v___x_1388_, 1, v_b_1386_);
v___x_1389_ = lean_apply_2(v_f_1384_, v___x_1388_, v_acc_1387_);
return v___x_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1390_, lean_object* v___f_1391_, lean_object* v_a_1392_, lean_object* v_x_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1390_, v___f_1391_, v_a_1392_, v___y_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1396_, lean_object* v_00_u03b2_1397_, lean_object* v_m_1398_, lean_object* v_init_1399_, lean_object* v_f_1400_){
_start:
{
lean_object* v_buckets_1401_; lean_object* v___f_1402_; lean_object* v___f_1403_; size_t v_sz_1404_; size_t v___x_1405_; lean_object* v___x_1406_; 
v_buckets_1401_ = lean_ctor_get(v_m_1398_, 1);
lean_inc_ref(v_buckets_1401_);
lean_dec_ref(v_m_1398_);
v___f_1402_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1402_, 0, v_f_1400_);
lean_inc_ref(v_inst_1396_);
v___f_1403_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1403_, 0, v_inst_1396_);
lean_closure_set(v___f_1403_, 1, v___f_1402_);
v_sz_1404_ = lean_array_size(v_buckets_1401_);
v___x_1405_ = ((size_t)0ULL);
v___x_1406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1396_, v_buckets_1401_, v___f_1403_, v_sz_1404_, v___x_1405_, v_init_1399_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1407_){
_start:
{
lean_object* v___f_1408_; 
v___f_1408_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1408_, 0, v_inst_1407_);
return v___f_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad(lean_object* v_00_u03b1_1409_, lean_object* v_00_u03b2_1410_, lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_m_1413_, lean_object* v_inst_1414_){
_start:
{
lean_object* v___f_1415_; 
v___f_1415_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1415_, 0, v_inst_1414_);
return v___f_1415_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1416_, lean_object* v_00_u03b2_1417_, lean_object* v_inst_1418_, lean_object* v_inst_1419_, lean_object* v_m_1420_, lean_object* v_inst_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Std_HashMap_instForInProdOfMonad(v_00_u03b1_1416_, v_00_u03b2_1417_, v_inst_1418_, v_inst_1419_, v_m_1420_, v_inst_1421_);
lean_dec_ref(v_inst_1419_);
lean_dec_ref(v_inst_1418_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___redArg(lean_object* v_f_1423_, lean_object* v_m_1424_){
_start:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1423_, v_m_1424_);
return v___x_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter(lean_object* v_00_u03b1_1426_, lean_object* v_00_u03b2_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v_f_1430_, lean_object* v_m_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1430_, v_m_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___boxed(lean_object* v_00_u03b1_1433_, lean_object* v_00_u03b2_1434_, lean_object* v_x_1435_, lean_object* v_x_1436_, lean_object* v_f_1437_, lean_object* v_m_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Std_HashMap_filter(v_00_u03b1_1433_, v_00_u03b2_1434_, v_x_1435_, v_x_1436_, v_f_1437_, v_m_1438_);
lean_dec_ref(v_x_1436_);
lean_dec_ref(v_x_1435_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify___redArg(lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_m_1442_, lean_object* v_a_1443_, lean_object* v_f_1444_){
_start:
{
lean_object* v___x_1445_; 
v___x_1445_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1440_, v_x_1441_, v_m_1442_, v_a_1443_, v_f_1444_);
return v___x_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify(lean_object* v_00_u03b1_1446_, lean_object* v_00_u03b2_1447_, lean_object* v_x_1448_, lean_object* v_x_1449_, lean_object* v_m_1450_, lean_object* v_a_1451_, lean_object* v_f_1452_){
_start:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1448_, v_x_1449_, v_m_1450_, v_a_1451_, v_f_1452_);
return v___x_1453_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter___redArg(lean_object* v_x_1454_, lean_object* v_x_1455_, lean_object* v_m_1456_, lean_object* v_a_1457_, lean_object* v_f_1458_){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1454_, v_x_1455_, v_m_1456_, v_a_1457_, v_f_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter(lean_object* v_00_u03b1_1460_, lean_object* v_00_u03b2_1461_, lean_object* v_x_1462_, lean_object* v_x_1463_, lean_object* v_m_1464_, lean_object* v_a_1465_, lean_object* v_f_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1462_, v_x_1463_, v_m_1464_, v_a_1465_, v_f_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany___redArg(lean_object* v_x_1468_, lean_object* v_x_1469_, lean_object* v_inst_1470_, lean_object* v_m_1471_, lean_object* v_l_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_1470_, v_x_1468_, v_x_1469_, v_m_1471_, v_l_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany(lean_object* v_00_u03b1_1474_, lean_object* v_00_u03b2_1475_, lean_object* v_x_1476_, lean_object* v_x_1477_, lean_object* v_00_u03c1_1478_, lean_object* v_inst_1479_, lean_object* v_m_1480_, lean_object* v_l_1481_){
_start:
{
lean_object* v___x_1482_; 
v___x_1482_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_1479_, v_x_1476_, v_x_1477_, v_m_1480_, v_l_1481_);
return v___x_1482_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit___redArg(lean_object* v_x_1483_, lean_object* v_x_1484_, lean_object* v_inst_1485_, lean_object* v_m_1486_, lean_object* v_l_1487_){
_start:
{
lean_object* v___x_1488_; 
v___x_1488_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1485_, v_x_1483_, v_x_1484_, v_m_1486_, v_l_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit(lean_object* v_00_u03b1_1489_, lean_object* v_x_1490_, lean_object* v_x_1491_, lean_object* v_00_u03c1_1492_, lean_object* v_inst_1493_, lean_object* v_m_1494_, lean_object* v_l_1495_){
_start:
{
lean_object* v___x_1496_; 
v___x_1496_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1493_, v_x_1490_, v_x_1491_, v_m_1494_, v_l_1495_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__0(lean_object* v_x1_1497_, lean_object* v_x2_1498_, lean_object* v_x3_1499_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v_x2_1498_);
lean_ctor_set(v___x_1500_, 1, v_x3_1499_);
v___x_1501_ = lean_array_push(v_x1_1497_, v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__1(lean_object* v___x_1502_, lean_object* v___f_1503_, lean_object* v_acc_1504_, lean_object* v_l_1505_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1502_, v___f_1503_, v_acc_1504_, v_l_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg(lean_object* v_m_1511_){
_start:
{
lean_object* v_size_1512_; lean_object* v_buckets_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; uint8_t v___x_1518_; 
v_size_1512_ = lean_ctor_get(v_m_1511_, 0);
lean_inc(v_size_1512_);
v_buckets_1513_ = lean_ctor_get(v_m_1511_, 1);
lean_inc_ref(v_buckets_1513_);
lean_dec_ref(v_m_1511_);
v___x_1514_ = lean_mk_empty_array_with_capacity(v_size_1512_);
lean_dec(v_size_1512_);
v___x_1515_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_array_get_size(v_buckets_1513_);
v___x_1518_ = lean_nat_dec_lt(v___x_1516_, v___x_1517_);
if (v___x_1518_ == 0)
{
lean_dec_ref(v_buckets_1513_);
return v___x_1514_;
}
else
{
lean_object* v___f_1519_; uint8_t v___x_1520_; 
v___f_1519_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__1));
v___x_1520_ = lean_nat_dec_le(v___x_1517_, v___x_1517_);
if (v___x_1520_ == 0)
{
if (v___x_1518_ == 0)
{
lean_dec_ref(v_buckets_1513_);
return v___x_1514_;
}
else
{
size_t v___x_1521_; size_t v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = ((size_t)0ULL);
v___x_1522_ = lean_usize_of_nat(v___x_1517_);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1515_, v___f_1519_, v_buckets_1513_, v___x_1521_, v___x_1522_, v___x_1514_);
return v___x_1523_;
}
}
else
{
size_t v___x_1524_; size_t v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = ((size_t)0ULL);
v___x_1525_ = lean_usize_of_nat(v___x_1517_);
v___x_1526_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1515_, v___f_1519_, v_buckets_1513_, v___x_1524_, v___x_1525_, v___x_1514_);
return v___x_1526_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray(lean_object* v_00_u03b1_1527_, lean_object* v_00_u03b2_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_m_1531_){
_start:
{
lean_object* v_size_1532_; lean_object* v_buckets_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; uint8_t v___x_1538_; 
v_size_1532_ = lean_ctor_get(v_m_1531_, 0);
lean_inc(v_size_1532_);
v_buckets_1533_ = lean_ctor_get(v_m_1531_, 1);
lean_inc_ref(v_buckets_1533_);
lean_dec_ref(v_m_1531_);
v___x_1534_ = lean_mk_empty_array_with_capacity(v_size_1532_);
lean_dec(v_size_1532_);
v___x_1535_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1536_ = lean_unsigned_to_nat(0u);
v___x_1537_ = lean_array_get_size(v_buckets_1533_);
v___x_1538_ = lean_nat_dec_lt(v___x_1536_, v___x_1537_);
if (v___x_1538_ == 0)
{
lean_dec_ref(v_buckets_1533_);
return v___x_1534_;
}
else
{
lean_object* v___f_1539_; uint8_t v___x_1540_; 
v___f_1539_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__1));
v___x_1540_ = lean_nat_dec_le(v___x_1537_, v___x_1537_);
if (v___x_1540_ == 0)
{
if (v___x_1538_ == 0)
{
lean_dec_ref(v_buckets_1533_);
return v___x_1534_;
}
else
{
size_t v___x_1541_; size_t v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = ((size_t)0ULL);
v___x_1542_ = lean_usize_of_nat(v___x_1537_);
v___x_1543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1535_, v___f_1539_, v_buckets_1533_, v___x_1541_, v___x_1542_, v___x_1534_);
return v___x_1543_;
}
}
else
{
size_t v___x_1544_; size_t v___x_1545_; lean_object* v___x_1546_; 
v___x_1544_ = ((size_t)0ULL);
v___x_1545_ = lean_usize_of_nat(v___x_1537_);
v___x_1546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1535_, v___f_1539_, v_buckets_1533_, v___x_1544_, v___x_1545_, v___x_1534_);
return v___x_1546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___boxed(lean_object* v_00_u03b1_1547_, lean_object* v_00_u03b2_1548_, lean_object* v_x_1549_, lean_object* v_x_1550_, lean_object* v_m_1551_){
_start:
{
lean_object* v_res_1552_; 
v_res_1552_ = l_Std_HashMap_toArray(v_00_u03b1_1547_, v_00_u03b2_1548_, v_x_1549_, v_x_1550_, v_m_1551_);
lean_dec_ref(v_x_1550_);
lean_dec_ref(v_x_1549_);
return v_res_1552_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0(lean_object* v_x1_1553_, lean_object* v_x2_1554_, lean_object* v_x3_1555_){
_start:
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_array_push(v_x1_1553_, v_x2_1554_);
return v___x_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1557_, lean_object* v_x2_1558_, lean_object* v_x3_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Std_HashMap_keysArray___redArg___lam__0(v_x1_1557_, v_x2_1558_, v_x3_1559_);
lean_dec(v_x3_1559_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__1(lean_object* v___x_1561_, lean_object* v___f_1562_, lean_object* v_acc_1563_, lean_object* v_l_1564_){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1561_, v___f_1562_, v_acc_1563_, v_l_1564_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg(lean_object* v_m_1570_){
_start:
{
lean_object* v_size_1571_; lean_object* v_buckets_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v_size_1571_ = lean_ctor_get(v_m_1570_, 0);
lean_inc(v_size_1571_);
v_buckets_1572_ = lean_ctor_get(v_m_1570_, 1);
lean_inc_ref(v_buckets_1572_);
lean_dec_ref(v_m_1570_);
v___x_1573_ = lean_mk_empty_array_with_capacity(v_size_1571_);
lean_dec(v_size_1571_);
v___x_1574_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1575_ = lean_unsigned_to_nat(0u);
v___x_1576_ = lean_array_get_size(v_buckets_1572_);
v___x_1577_ = lean_nat_dec_lt(v___x_1575_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_dec_ref(v_buckets_1572_);
return v___x_1573_;
}
else
{
lean_object* v___f_1578_; uint8_t v___x_1579_; 
v___f_1578_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__1));
v___x_1579_ = lean_nat_dec_le(v___x_1576_, v___x_1576_);
if (v___x_1579_ == 0)
{
if (v___x_1577_ == 0)
{
lean_dec_ref(v_buckets_1572_);
return v___x_1573_;
}
else
{
size_t v___x_1580_; size_t v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = ((size_t)0ULL);
v___x_1581_ = lean_usize_of_nat(v___x_1576_);
v___x_1582_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1574_, v___f_1578_, v_buckets_1572_, v___x_1580_, v___x_1581_, v___x_1573_);
return v___x_1582_;
}
}
else
{
size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = lean_usize_of_nat(v___x_1576_);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1574_, v___f_1578_, v_buckets_1572_, v___x_1583_, v___x_1584_, v___x_1573_);
return v___x_1585_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray(lean_object* v_00_u03b1_1586_, lean_object* v_00_u03b2_1587_, lean_object* v_x_1588_, lean_object* v_x_1589_, lean_object* v_m_1590_){
_start:
{
lean_object* v_size_1591_; lean_object* v_buckets_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_size_1591_ = lean_ctor_get(v_m_1590_, 0);
lean_inc(v_size_1591_);
v_buckets_1592_ = lean_ctor_get(v_m_1590_, 1);
lean_inc_ref(v_buckets_1592_);
lean_dec_ref(v_m_1590_);
v___x_1593_ = lean_mk_empty_array_with_capacity(v_size_1591_);
lean_dec(v_size_1591_);
v___x_1594_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1595_ = lean_unsigned_to_nat(0u);
v___x_1596_ = lean_array_get_size(v_buckets_1592_);
v___x_1597_ = lean_nat_dec_lt(v___x_1595_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_dec_ref(v_buckets_1592_);
return v___x_1593_;
}
else
{
lean_object* v___f_1598_; uint8_t v___x_1599_; 
v___f_1598_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__1));
v___x_1599_ = lean_nat_dec_le(v___x_1596_, v___x_1596_);
if (v___x_1599_ == 0)
{
if (v___x_1597_ == 0)
{
lean_dec_ref(v_buckets_1592_);
return v___x_1593_;
}
else
{
size_t v___x_1600_; size_t v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = ((size_t)0ULL);
v___x_1601_ = lean_usize_of_nat(v___x_1596_);
v___x_1602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1594_, v___f_1598_, v_buckets_1592_, v___x_1600_, v___x_1601_, v___x_1593_);
return v___x_1602_;
}
}
else
{
size_t v___x_1603_; size_t v___x_1604_; lean_object* v___x_1605_; 
v___x_1603_ = ((size_t)0ULL);
v___x_1604_ = lean_usize_of_nat(v___x_1596_);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1594_, v___f_1598_, v_buckets_1592_, v___x_1603_, v___x_1604_, v___x_1593_);
return v___x_1605_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___boxed(lean_object* v_00_u03b1_1606_, lean_object* v_00_u03b2_1607_, lean_object* v_x_1608_, lean_object* v_x_1609_, lean_object* v_m_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Std_HashMap_keysArray(v_00_u03b1_1606_, v_00_u03b2_1607_, v_x_1608_, v_x_1609_, v_m_1610_);
lean_dec_ref(v_x_1609_);
lean_dec_ref(v_x_1608_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0(lean_object* v_p_1612_, lean_object* v___x_1613_, lean_object* v___x_1614_, lean_object* v_a_1615_, lean_object* v_b_1616_, lean_object* v_acc_1617_){
_start:
{
lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1618_ = lean_apply_2(v_p_1612_, v_a_1615_, v_b_1616_);
v___x_1619_ = lean_unbox(v___x_1618_);
if (v___x_1619_ == 0)
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_dec_ref(v___x_1614_);
v___x_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1618_);
v___x_1621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v___x_1613_);
v___x_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
return v___x_1622_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1623_, 0, v___x_1614_);
return v___x_1623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0___boxed(lean_object* v_p_1624_, lean_object* v___x_1625_, lean_object* v___x_1626_, lean_object* v_a_1627_, lean_object* v_b_1628_, lean_object* v_acc_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Std_HashMap_all___redArg___lam__0(v_p_1624_, v___x_1625_, v___x_1626_, v_a_1627_, v_b_1628_, v_acc_1629_);
lean_dec_ref(v_acc_1629_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__1(lean_object* v___x_1631_, lean_object* v___f_1632_, lean_object* v_a_1633_, lean_object* v_x_1634_, lean_object* v___y_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1631_, v___f_1632_, v_a_1633_, v___y_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_all___redArg(lean_object* v_m_1640_, lean_object* v_p_1641_){
_start:
{
lean_object* v___x_1642_; lean_object* v_buckets_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___f_1646_; lean_object* v___f_1647_; size_t v_sz_1648_; size_t v___x_1649_; lean_object* v___x_1650_; lean_object* v_fst_1651_; 
v___x_1642_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1643_ = lean_ctor_get(v_m_1640_, 1);
lean_inc_ref(v_buckets_1643_);
lean_dec_ref(v_m_1640_);
v___x_1644_ = lean_box(0);
v___x_1645_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1646_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1646_, 0, v_p_1641_);
lean_closure_set(v___f_1646_, 1, v___x_1644_);
lean_closure_set(v___f_1646_, 2, v___x_1645_);
v___f_1647_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1647_, 0, v___x_1642_);
lean_closure_set(v___f_1647_, 1, v___f_1646_);
v_sz_1648_ = lean_array_size(v_buckets_1643_);
v___x_1649_ = ((size_t)0ULL);
v___x_1650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1642_, v_buckets_1643_, v___f_1647_, v_sz_1648_, v___x_1649_, v___x_1645_);
v_fst_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_fst_1651_);
lean_dec(v___x_1650_);
if (lean_obj_tag(v_fst_1651_) == 0)
{
uint8_t v___x_1652_; 
v___x_1652_ = 1;
return v___x_1652_;
}
else
{
lean_object* v_val_1653_; uint8_t v___x_1654_; 
v_val_1653_ = lean_ctor_get(v_fst_1651_, 0);
lean_inc(v_val_1653_);
lean_dec_ref(v_fst_1651_);
v___x_1654_ = lean_unbox(v_val_1653_);
lean_dec(v_val_1653_);
return v___x_1654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___boxed(lean_object* v_m_1655_, lean_object* v_p_1656_){
_start:
{
uint8_t v_res_1657_; lean_object* v_r_1658_; 
v_res_1657_ = l_Std_HashMap_all___redArg(v_m_1655_, v_p_1656_);
v_r_1658_ = lean_box(v_res_1657_);
return v_r_1658_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_all(lean_object* v_00_u03b1_1659_, lean_object* v_00_u03b2_1660_, lean_object* v_x_1661_, lean_object* v_x_1662_, lean_object* v_m_1663_, lean_object* v_p_1664_){
_start:
{
lean_object* v___x_1665_; lean_object* v_buckets_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___f_1669_; lean_object* v___f_1670_; size_t v_sz_1671_; size_t v___x_1672_; lean_object* v___x_1673_; lean_object* v_fst_1674_; 
v___x_1665_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1666_ = lean_ctor_get(v_m_1663_, 1);
lean_inc_ref(v_buckets_1666_);
lean_dec_ref(v_m_1663_);
v___x_1667_ = lean_box(0);
v___x_1668_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1669_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1669_, 0, v_p_1664_);
lean_closure_set(v___f_1669_, 1, v___x_1667_);
lean_closure_set(v___f_1669_, 2, v___x_1668_);
v___f_1670_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1670_, 0, v___x_1665_);
lean_closure_set(v___f_1670_, 1, v___f_1669_);
v_sz_1671_ = lean_array_size(v_buckets_1666_);
v___x_1672_ = ((size_t)0ULL);
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1665_, v_buckets_1666_, v___f_1670_, v_sz_1671_, v___x_1672_, v___x_1668_);
v_fst_1674_ = lean_ctor_get(v___x_1673_, 0);
lean_inc(v_fst_1674_);
lean_dec(v___x_1673_);
if (lean_obj_tag(v_fst_1674_) == 0)
{
uint8_t v___x_1675_; 
v___x_1675_ = 1;
return v___x_1675_;
}
else
{
lean_object* v_val_1676_; uint8_t v___x_1677_; 
v_val_1676_ = lean_ctor_get(v_fst_1674_, 0);
lean_inc(v_val_1676_);
lean_dec_ref(v_fst_1674_);
v___x_1677_ = lean_unbox(v_val_1676_);
lean_dec(v_val_1676_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___boxed(lean_object* v_00_u03b1_1678_, lean_object* v_00_u03b2_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_, lean_object* v_m_1682_, lean_object* v_p_1683_){
_start:
{
uint8_t v_res_1684_; lean_object* v_r_1685_; 
v_res_1684_ = l_Std_HashMap_all(v_00_u03b1_1678_, v_00_u03b2_1679_, v_x_1680_, v_x_1681_, v_m_1682_, v_p_1683_);
lean_dec_ref(v_x_1681_);
lean_dec_ref(v_x_1680_);
v_r_1685_ = lean_box(v_res_1684_);
return v_r_1685_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0(lean_object* v_p_1686_, lean_object* v___x_1687_, lean_object* v___x_1688_, lean_object* v_a_1689_, lean_object* v_b_1690_, lean_object* v_acc_1691_){
_start:
{
lean_object* v___x_1692_; uint8_t v___x_1693_; 
v___x_1692_ = lean_apply_2(v_p_1686_, v_a_1689_, v_b_1690_);
v___x_1693_ = lean_unbox(v___x_1692_);
if (v___x_1693_ == 0)
{
lean_object* v___x_1694_; 
v___x_1694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1687_);
return v___x_1694_;
}
else
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
lean_dec_ref(v___x_1687_);
v___x_1695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1692_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
lean_ctor_set(v___x_1696_, 1, v___x_1688_);
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0___boxed(lean_object* v_p_1698_, lean_object* v___x_1699_, lean_object* v___x_1700_, lean_object* v_a_1701_, lean_object* v_b_1702_, lean_object* v_acc_1703_){
_start:
{
lean_object* v_res_1704_; 
v_res_1704_ = l_Std_HashMap_any___redArg___lam__0(v_p_1698_, v___x_1699_, v___x_1700_, v_a_1701_, v_b_1702_, v_acc_1703_);
lean_dec_ref(v_acc_1703_);
return v_res_1704_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_any___redArg(lean_object* v_m_1705_, lean_object* v_p_1706_){
_start:
{
lean_object* v___x_1707_; lean_object* v_buckets_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___f_1711_; lean_object* v___f_1712_; size_t v_sz_1713_; size_t v___x_1714_; lean_object* v___x_1715_; lean_object* v_fst_1716_; 
v___x_1707_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1708_ = lean_ctor_get(v_m_1705_, 1);
lean_inc_ref(v_buckets_1708_);
lean_dec_ref(v_m_1705_);
v___x_1709_ = lean_box(0);
v___x_1710_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1711_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1711_, 0, v_p_1706_);
lean_closure_set(v___f_1711_, 1, v___x_1710_);
lean_closure_set(v___f_1711_, 2, v___x_1709_);
v___f_1712_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1712_, 0, v___x_1707_);
lean_closure_set(v___f_1712_, 1, v___f_1711_);
v_sz_1713_ = lean_array_size(v_buckets_1708_);
v___x_1714_ = ((size_t)0ULL);
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1707_, v_buckets_1708_, v___f_1712_, v_sz_1713_, v___x_1714_, v___x_1710_);
v_fst_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_fst_1716_);
lean_dec(v___x_1715_);
if (lean_obj_tag(v_fst_1716_) == 0)
{
uint8_t v___x_1717_; 
v___x_1717_ = 0;
return v___x_1717_;
}
else
{
lean_object* v_val_1718_; uint8_t v___x_1719_; 
v_val_1718_ = lean_ctor_get(v_fst_1716_, 0);
lean_inc(v_val_1718_);
lean_dec_ref(v_fst_1716_);
v___x_1719_ = lean_unbox(v_val_1718_);
lean_dec(v_val_1718_);
return v___x_1719_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___boxed(lean_object* v_m_1720_, lean_object* v_p_1721_){
_start:
{
uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_res_1722_ = l_Std_HashMap_any___redArg(v_m_1720_, v_p_1721_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_any(lean_object* v_00_u03b1_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_x_1726_, lean_object* v_x_1727_, lean_object* v_m_1728_, lean_object* v_p_1729_){
_start:
{
lean_object* v___x_1730_; lean_object* v_buckets_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___f_1734_; lean_object* v___f_1735_; size_t v_sz_1736_; size_t v___x_1737_; lean_object* v___x_1738_; lean_object* v_fst_1739_; 
v___x_1730_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1731_ = lean_ctor_get(v_m_1728_, 1);
lean_inc_ref(v_buckets_1731_);
lean_dec_ref(v_m_1728_);
v___x_1732_ = lean_box(0);
v___x_1733_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1734_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1734_, 0, v_p_1729_);
lean_closure_set(v___f_1734_, 1, v___x_1733_);
lean_closure_set(v___f_1734_, 2, v___x_1732_);
v___f_1735_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1735_, 0, v___x_1730_);
lean_closure_set(v___f_1735_, 1, v___f_1734_);
v_sz_1736_ = lean_array_size(v_buckets_1731_);
v___x_1737_ = ((size_t)0ULL);
v___x_1738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1730_, v_buckets_1731_, v___f_1735_, v_sz_1736_, v___x_1737_, v___x_1733_);
v_fst_1739_ = lean_ctor_get(v___x_1738_, 0);
lean_inc(v_fst_1739_);
lean_dec(v___x_1738_);
if (lean_obj_tag(v_fst_1739_) == 0)
{
uint8_t v___x_1740_; 
v___x_1740_ = 0;
return v___x_1740_;
}
else
{
lean_object* v_val_1741_; uint8_t v___x_1742_; 
v_val_1741_ = lean_ctor_get(v_fst_1739_, 0);
lean_inc(v_val_1741_);
lean_dec_ref(v_fst_1739_);
v___x_1742_ = lean_unbox(v_val_1741_);
lean_dec(v_val_1741_);
return v___x_1742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___boxed(lean_object* v_00_u03b1_1743_, lean_object* v_00_u03b2_1744_, lean_object* v_x_1745_, lean_object* v_x_1746_, lean_object* v_m_1747_, lean_object* v_p_1748_){
_start:
{
uint8_t v_res_1749_; lean_object* v_r_1750_; 
v_res_1749_ = l_Std_HashMap_any(v_00_u03b1_1743_, v_00_u03b2_1744_, v_x_1745_, v_x_1746_, v_m_1747_, v_p_1748_);
lean_dec_ref(v_x_1746_);
lean_dec_ref(v_x_1745_);
v_r_1750_ = lean_box(v_res_1749_);
return v_r_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__0(lean_object* v_inst_1751_, lean_object* v_inst_1752_, lean_object* v_a_1753_, lean_object* v_b_1754_, lean_object* v_acc_1755_){
_start:
{
lean_object* v_r_1756_; lean_object* v___x_1757_; 
v_r_1756_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1751_, v_inst_1752_, v_acc_1755_, v_a_1753_, v_b_1754_);
v___x_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1757_, 0, v_r_1756_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__1(lean_object* v___x_1758_, lean_object* v___f_1759_, lean_object* v_a_1760_, lean_object* v_x_1761_, lean_object* v___y_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1758_, v___f_1759_, v_a_1760_, v___y_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg(lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_m_u2081_1768_, lean_object* v_m_u2082_1769_){
_start:
{
lean_object* v_size_1770_; lean_object* v_buckets_1771_; lean_object* v_size_1772_; uint8_t v___x_1773_; 
v_size_1770_ = lean_ctor_get(v_m_u2081_1768_, 0);
v_buckets_1771_ = lean_ctor_get(v_m_u2081_1768_, 1);
v_size_1772_ = lean_ctor_get(v_m_u2082_1769_, 0);
v___x_1773_ = lean_nat_dec_le(v_size_1770_, v_size_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___f_1774_; lean_object* v___x_1775_; 
v___f_1774_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1775_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1774_, v_inst_1766_, v_inst_1767_, v_m_u2081_1768_, v_m_u2082_1769_);
return v___x_1775_;
}
else
{
lean_object* v___f_1776_; lean_object* v___x_1777_; lean_object* v___f_1778_; size_t v_sz_1779_; size_t v___x_1780_; lean_object* v___x_1781_; 
lean_inc_ref(v_buckets_1771_);
lean_dec_ref(v_m_u2081_1768_);
v___f_1776_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1776_, 0, v_inst_1766_);
lean_closure_set(v___f_1776_, 1, v_inst_1767_);
v___x_1777_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___f_1778_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1778_, 0, v___x_1777_);
lean_closure_set(v___f_1778_, 1, v___f_1776_);
v_sz_1779_ = lean_array_size(v_buckets_1771_);
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1777_, v_buckets_1771_, v___f_1778_, v_sz_1779_, v___x_1780_, v_m_u2082_1769_);
return v___x_1781_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union(lean_object* v_00_u03b1_1782_, lean_object* v_00_u03b2_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_m_u2081_1786_, lean_object* v_m_u2082_1787_){
_start:
{
lean_object* v_size_1788_; lean_object* v_buckets_1789_; lean_object* v_size_1790_; uint8_t v___x_1791_; 
v_size_1788_ = lean_ctor_get(v_m_u2081_1786_, 0);
v_buckets_1789_ = lean_ctor_get(v_m_u2081_1786_, 1);
v_size_1790_ = lean_ctor_get(v_m_u2082_1787_, 0);
v___x_1791_ = lean_nat_dec_le(v_size_1788_, v_size_1790_);
if (v___x_1791_ == 0)
{
lean_object* v___f_1792_; lean_object* v___x_1793_; 
v___f_1792_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1793_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1792_, v_inst_1784_, v_inst_1785_, v_m_u2081_1786_, v_m_u2082_1787_);
return v___x_1793_;
}
else
{
lean_object* v___f_1794_; lean_object* v___x_1795_; lean_object* v___f_1796_; size_t v_sz_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
lean_inc_ref(v_buckets_1789_);
lean_dec_ref(v_m_u2081_1786_);
v___f_1794_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1794_, 0, v_inst_1784_);
lean_closure_set(v___f_1794_, 1, v_inst_1785_);
v___x_1795_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___f_1796_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1796_, 0, v___x_1795_);
lean_closure_set(v___f_1796_, 1, v___f_1794_);
v_sz_1797_ = lean_array_size(v_buckets_1789_);
v___x_1798_ = ((size_t)0ULL);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1795_, v_buckets_1789_, v___f_1796_, v_sz_1797_, v___x_1798_, v_m_u2082_1787_);
return v___x_1799_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion___redArg(lean_object* v_inst_1800_, lean_object* v_inst_1801_){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_alloc_closure((void*)(l_Std_HashMap_union), 6, 4);
lean_closure_set(v___x_1802_, 0, lean_box(0));
lean_closure_set(v___x_1802_, 1, lean_box(0));
lean_closure_set(v___x_1802_, 2, v_inst_1800_);
lean_closure_set(v___x_1802_, 3, v_inst_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion(lean_object* v_00_u03b1_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_inst_1805_, lean_object* v_inst_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = lean_alloc_closure((void*)(l_Std_HashMap_union), 6, 4);
lean_closure_set(v___x_1807_, 0, lean_box(0));
lean_closure_set(v___x_1807_, 1, lean_box(0));
lean_closure_set(v___x_1807_, 2, v_inst_1805_);
lean_closure_set(v___x_1807_, 3, v_inst_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_inter___redArg(lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_m_u2081_1810_, lean_object* v_m_u2082_1811_){
_start:
{
lean_object* v___x_1812_; 
v___x_1812_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1808_, v_inst_1809_, v_m_u2081_1810_, v_m_u2082_1811_);
return v___x_1812_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_inter(lean_object* v_00_u03b1_1813_, lean_object* v_00_u03b2_1814_, lean_object* v_inst_1815_, lean_object* v_inst_1816_, lean_object* v_m_u2081_1817_, lean_object* v_m_u2082_1818_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1815_, v_inst_1816_, v_m_u2081_1817_, v_m_u2082_1818_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInter___redArg(lean_object* v_inst_1820_, lean_object* v_inst_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_alloc_closure((void*)(l_Std_HashMap_inter), 6, 4);
lean_closure_set(v___x_1822_, 0, lean_box(0));
lean_closure_set(v___x_1822_, 1, lean_box(0));
lean_closure_set(v___x_1822_, 2, v_inst_1820_);
lean_closure_set(v___x_1822_, 3, v_inst_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInter(lean_object* v_00_u03b1_1823_, lean_object* v_00_u03b2_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_alloc_closure((void*)(l_Std_HashMap_inter), 6, 4);
lean_closure_set(v___x_1827_, 0, lean_box(0));
lean_closure_set(v___x_1827_, 1, lean_box(0));
lean_closure_set(v___x_1827_, 2, v_inst_1825_);
lean_closure_set(v___x_1827_, 3, v_inst_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq___redArg(lean_object* v_x_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_m_u2081_1831_, lean_object* v_m_u2082_1832_){
_start:
{
uint8_t v___x_1833_; 
v___x_1833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1829_, v_x_1828_, v_inst_1830_, v_m_u2081_1831_, v_m_u2082_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___redArg___boxed(lean_object* v_x_1834_, lean_object* v_inst_1835_, lean_object* v_inst_1836_, lean_object* v_m_u2081_1837_, lean_object* v_m_u2082_1838_){
_start:
{
uint8_t v_res_1839_; lean_object* v_r_1840_; 
v_res_1839_ = l_Std_HashMap_beq___redArg(v_x_1834_, v_inst_1835_, v_inst_1836_, v_m_u2081_1837_, v_m_u2082_1838_);
v_r_1840_ = lean_box(v_res_1839_);
return v_r_1840_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq(lean_object* v_00_u03b1_1841_, lean_object* v_x_1842_, lean_object* v_00_u03b2_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_m_u2081_1846_, lean_object* v_m_u2082_1847_){
_start:
{
uint8_t v___x_1848_; 
v___x_1848_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1844_, v_x_1842_, v_inst_1845_, v_m_u2081_1846_, v_m_u2082_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___boxed(lean_object* v_00_u03b1_1849_, lean_object* v_x_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_, lean_object* v_m_u2081_1854_, lean_object* v_m_u2082_1855_){
_start:
{
uint8_t v_res_1856_; lean_object* v_r_1857_; 
v_res_1856_ = l_Std_HashMap_beq(v_00_u03b1_1849_, v_x_1850_, v_00_u03b2_1851_, v_inst_1852_, v_inst_1853_, v_m_u2081_1854_, v_m_u2082_1855_);
v_r_1857_ = lean_box(v_res_1856_);
return v_r_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq___redArg(lean_object* v_x_1858_, lean_object* v_inst_1859_, lean_object* v_inst_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_1861_, 0, lean_box(0));
lean_closure_set(v___x_1861_, 1, v_x_1858_);
lean_closure_set(v___x_1861_, 2, lean_box(0));
lean_closure_set(v___x_1861_, 3, v_inst_1859_);
lean_closure_set(v___x_1861_, 4, v_inst_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq(lean_object* v_00_u03b1_1862_, lean_object* v_00_u03b2_1863_, lean_object* v_x_1864_, lean_object* v_inst_1865_, lean_object* v_inst_1866_){
_start:
{
lean_object* v___x_1867_; 
v___x_1867_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_1867_, 0, lean_box(0));
lean_closure_set(v___x_1867_, 1, v_x_1864_);
lean_closure_set(v___x_1867_, 2, lean_box(0));
lean_closure_set(v___x_1867_, 3, v_inst_1865_);
lean_closure_set(v___x_1867_, 4, v_inst_1866_);
return v___x_1867_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_diff___redArg___lam__0(lean_object* v_inst_1868_, lean_object* v_inst_1869_, lean_object* v_m_u2082_1870_, uint8_t v___x_1871_, lean_object* v_k_1872_, lean_object* v_x_1873_){
_start:
{
uint8_t v___x_1874_; 
v___x_1874_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1868_, v_inst_1869_, v_m_u2082_1870_, v_k_1872_);
if (v___x_1874_ == 0)
{
return v___x_1871_;
}
else
{
uint8_t v___x_1875_; 
v___x_1875_ = 0;
return v___x_1875_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg___lam__0___boxed(lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_m_u2082_1878_, lean_object* v___x_1879_, lean_object* v_k_1880_, lean_object* v_x_1881_){
_start:
{
uint8_t v___x_80__boxed_1882_; uint8_t v_res_1883_; lean_object* v_r_1884_; 
v___x_80__boxed_1882_ = lean_unbox(v___x_1879_);
v_res_1883_ = l_Std_HashMap_diff___redArg___lam__0(v_inst_1876_, v_inst_1877_, v_m_u2082_1878_, v___x_80__boxed_1882_, v_k_1880_, v_x_1881_);
lean_dec(v_x_1881_);
lean_dec_ref(v_m_u2082_1878_);
v_r_1884_ = lean_box(v_res_1883_);
return v_r_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg(lean_object* v_inst_1885_, lean_object* v_inst_1886_, lean_object* v_m_u2081_1887_, lean_object* v_m_u2082_1888_){
_start:
{
lean_object* v_size_1889_; lean_object* v_size_1890_; uint8_t v___x_1891_; 
v_size_1889_ = lean_ctor_get(v_m_u2081_1887_, 0);
v_size_1890_ = lean_ctor_get(v_m_u2082_1888_, 0);
v___x_1891_ = lean_nat_dec_le(v_size_1889_, v_size_1890_);
if (v___x_1891_ == 0)
{
lean_object* v___f_1892_; lean_object* v___x_1893_; 
v___f_1892_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1893_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1892_, v_inst_1885_, v_inst_1886_, v_m_u2081_1887_, v_m_u2082_1888_);
return v___x_1893_;
}
else
{
lean_object* v___x_1894_; lean_object* v___f_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_box(v___x_1891_);
v___f_1895_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1895_, 0, v_inst_1885_);
lean_closure_set(v___f_1895_, 1, v_inst_1886_);
lean_closure_set(v___f_1895_, 2, v_m_u2082_1888_);
lean_closure_set(v___f_1895_, 3, v___x_1894_);
v___x_1896_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1895_, v_m_u2081_1887_);
return v___x_1896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff(lean_object* v_00_u03b1_1897_, lean_object* v_00_u03b2_1898_, lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_m_u2081_1901_, lean_object* v_m_u2082_1902_){
_start:
{
lean_object* v_size_1903_; lean_object* v_size_1904_; uint8_t v___x_1905_; 
v_size_1903_ = lean_ctor_get(v_m_u2081_1901_, 0);
v_size_1904_ = lean_ctor_get(v_m_u2082_1902_, 0);
v___x_1905_ = lean_nat_dec_le(v_size_1903_, v_size_1904_);
if (v___x_1905_ == 0)
{
lean_object* v___f_1906_; lean_object* v___x_1907_; 
v___f_1906_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1907_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1906_, v_inst_1899_, v_inst_1900_, v_m_u2081_1901_, v_m_u2082_1902_);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; lean_object* v___f_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_box(v___x_1905_);
v___f_1909_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1909_, 0, v_inst_1899_);
lean_closure_set(v___f_1909_, 1, v_inst_1900_);
lean_closure_set(v___f_1909_, 2, v_m_u2082_1902_);
lean_closure_set(v___f_1909_, 3, v___x_1908_);
v___x_1910_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1909_, v_m_u2081_1901_);
return v___x_1910_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff___redArg(lean_object* v_inst_1911_, lean_object* v_inst_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_1913_, 0, lean_box(0));
lean_closure_set(v___x_1913_, 1, lean_box(0));
lean_closure_set(v___x_1913_, 2, v_inst_1911_);
lean_closure_set(v___x_1913_, 3, v_inst_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff(lean_object* v_00_u03b1_1914_, lean_object* v_00_u03b2_1915_, lean_object* v_inst_1916_, lean_object* v_inst_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_1918_, 0, lean_box(0));
lean_closure_set(v___x_1918_, 1, lean_box(0));
lean_closure_set(v___x_1918_, 2, v_inst_1916_);
lean_closure_set(v___x_1918_, 3, v_inst_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__0(lean_object* v_f_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v_x1_1922_, lean_object* v_x2_1923_, lean_object* v_x3_1924_){
_start:
{
lean_object* v_fst_1925_; lean_object* v_snd_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1940_; 
v_fst_1925_ = lean_ctor_get(v_x1_1922_, 0);
v_snd_1926_ = lean_ctor_get(v_x1_1922_, 1);
v_isSharedCheck_1940_ = !lean_is_exclusive(v_x1_1922_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1928_ = v_x1_1922_;
v_isShared_1929_ = v_isSharedCheck_1940_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_snd_1926_);
lean_inc(v_fst_1925_);
lean_dec(v_x1_1922_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1940_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v___x_1930_; uint8_t v___x_1931_; 
lean_inc(v_x3_1924_);
lean_inc(v_x2_1923_);
v___x_1930_ = lean_apply_2(v_f_1919_, v_x2_1923_, v_x3_1924_);
v___x_1931_ = lean_unbox(v___x_1930_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; lean_object* v___x_1934_; 
v___x_1932_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1920_, v_x_1921_, v_snd_1926_, v_x2_1923_, v_x3_1924_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v___x_1932_);
v___x_1934_ = v___x_1928_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_fst_1925_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v___x_1932_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
else
{
lean_object* v___x_1936_; lean_object* v___x_1938_; 
v___x_1936_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1920_, v_x_1921_, v_fst_1925_, v_x2_1923_, v_x3_1924_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 0, v___x_1936_);
v___x_1938_ = v___x_1928_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v___x_1936_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_snd_1926_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__1(lean_object* v___x_1941_, lean_object* v___f_1942_, lean_object* v_acc_1943_, lean_object* v_l_1944_){
_start:
{
lean_object* v___x_1945_; 
v___x_1945_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1941_, v___f_1942_, v_acc_1943_, v_l_1944_);
return v___x_1945_;
}
}
static lean_object* _init_l_Std_HashMap_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1946_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1947_, 0, v___x_1946_);
lean_ctor_set(v___x_1947_, 1, v___x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg(lean_object* v_x_1948_, lean_object* v_x_1949_, lean_object* v_f_1950_, lean_object* v_m_1951_){
_start:
{
lean_object* v___y_1953_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v_buckets_1966_; lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1963_ = lean_unsigned_to_nat(0u);
v___x_1964_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_1965_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1966_ = lean_ctor_get(v_m_1951_, 1);
lean_inc_ref(v_buckets_1966_);
lean_dec_ref(v_m_1951_);
v___x_1967_ = lean_array_get_size(v_buckets_1966_);
v___x_1968_ = lean_nat_dec_lt(v___x_1963_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_dec_ref(v_buckets_1966_);
lean_dec_ref(v_f_1950_);
lean_dec_ref(v_x_1949_);
lean_dec_ref(v_x_1948_);
return v___x_1964_;
}
else
{
lean_object* v___f_1969_; lean_object* v___f_1970_; uint8_t v___x_1971_; 
v___f_1969_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1969_, 0, v_f_1950_);
lean_closure_set(v___f_1969_, 1, v_x_1948_);
lean_closure_set(v___f_1969_, 2, v_x_1949_);
v___f_1970_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1970_, 0, v___x_1965_);
lean_closure_set(v___f_1970_, 1, v___f_1969_);
v___x_1971_ = lean_nat_dec_le(v___x_1967_, v___x_1967_);
if (v___x_1971_ == 0)
{
if (v___x_1968_ == 0)
{
lean_dec_ref(v___f_1970_);
lean_dec_ref(v_buckets_1966_);
return v___x_1964_;
}
else
{
size_t v___x_1972_; size_t v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = ((size_t)0ULL);
v___x_1973_ = lean_usize_of_nat(v___x_1967_);
v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1965_, v___f_1970_, v_buckets_1966_, v___x_1972_, v___x_1973_, v___x_1964_);
v___y_1953_ = v___x_1974_;
goto v___jp_1952_;
}
}
else
{
size_t v___x_1975_; size_t v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = ((size_t)0ULL);
v___x_1976_ = lean_usize_of_nat(v___x_1967_);
v___x_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1965_, v___f_1970_, v_buckets_1966_, v___x_1975_, v___x_1976_, v___x_1964_);
v___y_1953_ = v___x_1977_;
goto v___jp_1952_;
}
}
v___jp_1952_:
{
lean_object* v_fst_1954_; lean_object* v_snd_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
v_fst_1954_ = lean_ctor_get(v___y_1953_, 0);
v_snd_1955_ = lean_ctor_get(v___y_1953_, 1);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___y_1953_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___y_1953_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_snd_1955_);
lean_inc(v_fst_1954_);
lean_dec(v___y_1953_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_fst_1954_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_snd_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition(lean_object* v_00_u03b1_1978_, lean_object* v_00_u03b2_1979_, lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v_f_1982_, lean_object* v_m_1983_){
_start:
{
lean_object* v___y_1985_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v_buckets_1998_; lean_object* v___x_1999_; uint8_t v___x_2000_; 
v___x_1995_ = lean_unsigned_to_nat(0u);
v___x_1996_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_1997_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1998_ = lean_ctor_get(v_m_1983_, 1);
lean_inc_ref(v_buckets_1998_);
lean_dec_ref(v_m_1983_);
v___x_1999_ = lean_array_get_size(v_buckets_1998_);
v___x_2000_ = lean_nat_dec_lt(v___x_1995_, v___x_1999_);
if (v___x_2000_ == 0)
{
lean_dec_ref(v_buckets_1998_);
lean_dec_ref(v_f_1982_);
lean_dec_ref(v_x_1981_);
lean_dec_ref(v_x_1980_);
return v___x_1996_;
}
else
{
lean_object* v___f_2001_; lean_object* v___f_2002_; uint8_t v___x_2003_; 
v___f_2001_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_2001_, 0, v_f_1982_);
lean_closure_set(v___f_2001_, 1, v_x_1980_);
lean_closure_set(v___f_2001_, 2, v_x_1981_);
v___f_2002_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2002_, 0, v___x_1997_);
lean_closure_set(v___f_2002_, 1, v___f_2001_);
v___x_2003_ = lean_nat_dec_le(v___x_1999_, v___x_1999_);
if (v___x_2003_ == 0)
{
if (v___x_2000_ == 0)
{
lean_dec_ref(v___f_2002_);
lean_dec_ref(v_buckets_1998_);
return v___x_1996_;
}
else
{
size_t v___x_2004_; size_t v___x_2005_; lean_object* v___x_2006_; 
v___x_2004_ = ((size_t)0ULL);
v___x_2005_ = lean_usize_of_nat(v___x_1999_);
v___x_2006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1997_, v___f_2002_, v_buckets_1998_, v___x_2004_, v___x_2005_, v___x_1996_);
v___y_1985_ = v___x_2006_;
goto v___jp_1984_;
}
}
else
{
size_t v___x_2007_; size_t v___x_2008_; lean_object* v___x_2009_; 
v___x_2007_ = ((size_t)0ULL);
v___x_2008_ = lean_usize_of_nat(v___x_1999_);
v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1997_, v___f_2002_, v_buckets_1998_, v___x_2007_, v___x_2008_, v___x_1996_);
v___y_1985_ = v___x_2009_;
goto v___jp_1984_;
}
}
v___jp_1984_:
{
lean_object* v_fst_1986_; lean_object* v_snd_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
v_fst_1986_ = lean_ctor_get(v___y_1985_, 0);
v_snd_1987_ = lean_ctor_get(v___y_1985_, 1);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___y_1985_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___y_1985_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_snd_1987_);
lean_inc(v_fst_1986_);
lean_dec(v___y_1985_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_fst_1986_);
lean_ctor_set(v_reuseFailAlloc_1993_, 1, v_snd_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0(lean_object* v_a_2010_, lean_object* v_b_2011_, lean_object* v_d_2012_){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2013_, 0, v_b_2011_);
lean_ctor_set(v___x_2013_, 1, v_d_2012_);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0___boxed(lean_object* v_a_2014_, lean_object* v_b_2015_, lean_object* v_d_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Std_HashMap_values___redArg___lam__0(v_a_2014_, v_b_2015_, v_d_2016_);
lean_dec(v_a_2014_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg(lean_object* v_m_2022_){
_start:
{
lean_object* v___x_2023_; lean_object* v_buckets_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2023_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2024_ = lean_ctor_get(v_m_2022_, 1);
lean_inc_ref(v_buckets_2024_);
lean_dec_ref(v_m_2022_);
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_array_get_size(v_buckets_2024_);
v___x_2027_ = lean_unsigned_to_nat(0u);
v___x_2028_ = lean_nat_dec_lt(v___x_2027_, v___x_2026_);
if (v___x_2028_ == 0)
{
lean_dec_ref(v_buckets_2024_);
return v___x_2025_;
}
else
{
lean_object* v___f_2029_; size_t v___x_2030_; size_t v___x_2031_; lean_object* v___x_2032_; 
v___f_2029_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__1));
v___x_2030_ = lean_usize_of_nat(v___x_2026_);
v___x_2031_ = ((size_t)0ULL);
v___x_2032_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2023_, v___f_2029_, v_buckets_2024_, v___x_2030_, v___x_2031_, v___x_2025_);
return v___x_2032_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values(lean_object* v_00_u03b1_2033_, lean_object* v_00_u03b2_2034_, lean_object* v_x_2035_, lean_object* v_x_2036_, lean_object* v_m_2037_){
_start:
{
lean_object* v___x_2038_; lean_object* v_buckets_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; uint8_t v___x_2043_; 
v___x_2038_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2039_ = lean_ctor_get(v_m_2037_, 1);
lean_inc_ref(v_buckets_2039_);
lean_dec_ref(v_m_2037_);
v___x_2040_ = lean_box(0);
v___x_2041_ = lean_array_get_size(v_buckets_2039_);
v___x_2042_ = lean_unsigned_to_nat(0u);
v___x_2043_ = lean_nat_dec_lt(v___x_2042_, v___x_2041_);
if (v___x_2043_ == 0)
{
lean_dec_ref(v_buckets_2039_);
return v___x_2040_;
}
else
{
lean_object* v___f_2044_; size_t v___x_2045_; size_t v___x_2046_; lean_object* v___x_2047_; 
v___f_2044_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__1));
v___x_2045_ = lean_usize_of_nat(v___x_2041_);
v___x_2046_ = ((size_t)0ULL);
v___x_2047_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2038_, v___f_2044_, v_buckets_2039_, v___x_2045_, v___x_2046_, v___x_2040_);
return v___x_2047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___boxed(lean_object* v_00_u03b1_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v_m_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Std_HashMap_values(v_00_u03b1_2048_, v_00_u03b2_2049_, v_x_2050_, v_x_2051_, v_m_2052_);
lean_dec_ref(v_x_2051_);
lean_dec_ref(v_x_2050_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0(lean_object* v_x1_2054_, lean_object* v_x2_2055_, lean_object* v_x3_2056_){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_array_push(v_x1_2054_, v_x3_2056_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2058_, lean_object* v_x2_2059_, lean_object* v_x3_2060_){
_start:
{
lean_object* v_res_2061_; 
v_res_2061_ = l_Std_HashMap_valuesArray___redArg___lam__0(v_x1_2058_, v_x2_2059_, v_x3_2060_);
lean_dec(v_x2_2059_);
return v_res_2061_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg(lean_object* v_m_2066_){
_start:
{
lean_object* v_size_2067_; lean_object* v_buckets_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; uint8_t v___x_2073_; 
v_size_2067_ = lean_ctor_get(v_m_2066_, 0);
lean_inc(v_size_2067_);
v_buckets_2068_ = lean_ctor_get(v_m_2066_, 1);
lean_inc_ref(v_buckets_2068_);
lean_dec_ref(v_m_2066_);
v___x_2069_ = lean_mk_empty_array_with_capacity(v_size_2067_);
lean_dec(v_size_2067_);
v___x_2070_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_array_get_size(v_buckets_2068_);
v___x_2073_ = lean_nat_dec_lt(v___x_2071_, v___x_2072_);
if (v___x_2073_ == 0)
{
lean_dec_ref(v_buckets_2068_);
return v___x_2069_;
}
else
{
lean_object* v___f_2074_; uint8_t v___x_2075_; 
v___f_2074_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__1));
v___x_2075_ = lean_nat_dec_le(v___x_2072_, v___x_2072_);
if (v___x_2075_ == 0)
{
if (v___x_2073_ == 0)
{
lean_dec_ref(v_buckets_2068_);
return v___x_2069_;
}
else
{
size_t v___x_2076_; size_t v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = ((size_t)0ULL);
v___x_2077_ = lean_usize_of_nat(v___x_2072_);
v___x_2078_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2070_, v___f_2074_, v_buckets_2068_, v___x_2076_, v___x_2077_, v___x_2069_);
return v___x_2078_;
}
}
else
{
size_t v___x_2079_; size_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = ((size_t)0ULL);
v___x_2080_ = lean_usize_of_nat(v___x_2072_);
v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2070_, v___f_2074_, v_buckets_2068_, v___x_2079_, v___x_2080_, v___x_2069_);
return v___x_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray(lean_object* v_00_u03b1_2082_, lean_object* v_00_u03b2_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_, lean_object* v_m_2086_){
_start:
{
lean_object* v_size_2087_; lean_object* v_buckets_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; uint8_t v___x_2093_; 
v_size_2087_ = lean_ctor_get(v_m_2086_, 0);
lean_inc(v_size_2087_);
v_buckets_2088_ = lean_ctor_get(v_m_2086_, 1);
lean_inc_ref(v_buckets_2088_);
lean_dec_ref(v_m_2086_);
v___x_2089_ = lean_mk_empty_array_with_capacity(v_size_2087_);
lean_dec(v_size_2087_);
v___x_2090_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_array_get_size(v_buckets_2088_);
v___x_2093_ = lean_nat_dec_lt(v___x_2091_, v___x_2092_);
if (v___x_2093_ == 0)
{
lean_dec_ref(v_buckets_2088_);
return v___x_2089_;
}
else
{
lean_object* v___f_2094_; uint8_t v___x_2095_; 
v___f_2094_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__1));
v___x_2095_ = lean_nat_dec_le(v___x_2092_, v___x_2092_);
if (v___x_2095_ == 0)
{
if (v___x_2093_ == 0)
{
lean_dec_ref(v_buckets_2088_);
return v___x_2089_;
}
else
{
size_t v___x_2096_; size_t v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = ((size_t)0ULL);
v___x_2097_ = lean_usize_of_nat(v___x_2092_);
v___x_2098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2090_, v___f_2094_, v_buckets_2088_, v___x_2096_, v___x_2097_, v___x_2089_);
return v___x_2098_;
}
}
else
{
size_t v___x_2099_; size_t v___x_2100_; lean_object* v___x_2101_; 
v___x_2099_ = ((size_t)0ULL);
v___x_2100_ = lean_usize_of_nat(v___x_2092_);
v___x_2101_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2090_, v___f_2094_, v_buckets_2088_, v___x_2099_, v___x_2100_, v___x_2089_);
return v___x_2101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___boxed(lean_object* v_00_u03b1_2102_, lean_object* v_00_u03b2_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_, lean_object* v_m_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Std_HashMap_valuesArray(v_00_u03b1_2102_, v_00_u03b2_2103_, v_x_2104_, v_x_2105_, v_m_2106_);
lean_dec_ref(v_x_2105_);
lean_dec_ref(v_x_2104_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray___redArg(lean_object* v_inst_2108_, lean_object* v_inst_2109_, lean_object* v_l_2110_){
_start:
{
lean_object* v___f_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___f_2111_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2112_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_2113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2111_, v_inst_2108_, v_inst_2109_, v___x_2112_, v_l_2110_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray(lean_object* v_00_u03b1_2114_, lean_object* v_inst_2115_, lean_object* v_inst_2116_, lean_object* v_l_2117_){
_start:
{
lean_object* v___f_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___f_2118_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2119_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_2120_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2118_, v_inst_2115_, v_inst_2116_, v___x_2119_, v_l_2117_);
return v___x_2120_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg(lean_object* v_m_2121_){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2121_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg___boxed(lean_object* v_m_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Std_HashMap_Internal_numBuckets___redArg(v_m_2123_);
lean_dec_ref(v_m_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets(lean_object* v_00_u03b1_2125_, lean_object* v_00_u03b2_2126_, lean_object* v_x_2127_, lean_object* v_x_2128_, lean_object* v_m_2129_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2129_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2131_, lean_object* v_00_u03b2_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_, lean_object* v_m_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Std_HashMap_Internal_numBuckets(v_00_u03b1_2131_, v_00_u03b2_2132_, v_x_2133_, v_x_2134_, v_m_2135_);
lean_dec_ref(v_m_2135_);
lean_dec_ref(v_x_2134_);
lean_dec_ref(v_x_2133_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2(lean_object* v___x_2140_, lean_object* v___f_2141_, lean_object* v_m_2142_, lean_object* v_prec_2143_){
_start:
{
lean_object* v___x_2144_; lean_object* v_buckets_2145_; lean_object* v___x_2147_; uint8_t v_isShared_2148_; uint8_t v_isSharedCheck_2165_; 
v___x_2144_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2145_ = lean_ctor_get(v_m_2142_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_m_2142_);
if (v_isSharedCheck_2165_ == 0)
{
lean_object* v_unused_2166_; 
v_unused_2166_ = lean_ctor_get(v_m_2142_, 0);
lean_dec(v_unused_2166_);
v___x_2147_ = v_m_2142_;
v_isShared_2148_ = v_isSharedCheck_2165_;
goto v_resetjp_2146_;
}
else
{
lean_inc(v_buckets_2145_);
lean_dec(v_m_2142_);
v___x_2147_ = lean_box(0);
v_isShared_2148_ = v_isSharedCheck_2165_;
goto v_resetjp_2146_;
}
v_resetjp_2146_:
{
lean_object* v___x_2149_; lean_object* v___y_2151_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; 
v___x_2149_ = ((lean_object*)(l_Std_HashMap_instRepr___redArg___lam__2___closed__1));
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_array_get_size(v_buckets_2145_);
v___x_2159_ = lean_unsigned_to_nat(0u);
v___x_2160_ = lean_nat_dec_lt(v___x_2159_, v___x_2158_);
if (v___x_2160_ == 0)
{
lean_dec_ref(v_buckets_2145_);
lean_dec_ref(v___f_2141_);
v___y_2151_ = v___x_2157_;
goto v___jp_2150_;
}
else
{
lean_object* v___f_2161_; size_t v___x_2162_; size_t v___x_2163_; lean_object* v___x_2164_; 
v___f_2161_ = lean_alloc_closure((void*)(l_Std_HashMap_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2161_, 0, v___x_2144_);
lean_closure_set(v___f_2161_, 1, v___f_2141_);
v___x_2162_ = lean_usize_of_nat(v___x_2158_);
v___x_2163_ = ((size_t)0ULL);
v___x_2164_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2144_, v___f_2161_, v_buckets_2145_, v___x_2162_, v___x_2163_, v___x_2157_);
v___y_2151_ = v___x_2164_;
goto v___jp_2150_;
}
v___jp_2150_:
{
lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2152_ = l_List_repr___redArg(v___x_2140_, v___y_2151_);
if (v_isShared_2148_ == 0)
{
lean_ctor_set_tag(v___x_2147_, 5);
lean_ctor_set(v___x_2147_, 1, v___x_2152_);
lean_ctor_set(v___x_2147_, 0, v___x_2149_);
v___x_2154_ = v___x_2147_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2149_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
lean_object* v___x_2155_; 
v___x_2155_ = l_Repr_addAppParen(v___x_2154_, v_prec_2143_);
return v___x_2155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2___boxed(lean_object* v___x_2167_, lean_object* v___f_2168_, lean_object* v_m_2169_, lean_object* v_prec_2170_){
_start:
{
lean_object* v_res_2171_; 
v_res_2171_ = l_Std_HashMap_instRepr___redArg___lam__2(v___x_2167_, v___f_2168_, v_m_2169_, v_prec_2170_);
lean_dec(v_prec_2170_);
return v_res_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg(lean_object* v_inst_2172_, lean_object* v_inst_2173_){
_start:
{
lean_object* v___f_2174_; lean_object* v___f_2175_; lean_object* v___x_2176_; lean_object* v___f_2177_; 
v___f_2174_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__0));
v___f_2175_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2175_, 0, v_inst_2173_);
v___x_2176_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2176_, 0, lean_box(0));
lean_closure_set(v___x_2176_, 1, lean_box(0));
lean_closure_set(v___x_2176_, 2, v_inst_2172_);
lean_closure_set(v___x_2176_, 3, v___f_2175_);
v___f_2177_ = lean_alloc_closure((void*)(l_Std_HashMap_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2177_, 0, v___x_2176_);
lean_closure_set(v___f_2177_, 1, v___f_2174_);
return v___f_2177_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr(lean_object* v_00_u03b1_2178_, lean_object* v_00_u03b2_2179_, lean_object* v_inst_2180_, lean_object* v_inst_2181_, lean_object* v_inst_2182_, lean_object* v_inst_2183_){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = l_Std_HashMap_instRepr___redArg(v_inst_2182_, v_inst_2183_);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___boxed(lean_object* v_00_u03b1_2185_, lean_object* v_00_u03b2_2186_, lean_object* v_inst_2187_, lean_object* v_inst_2188_, lean_object* v_inst_2189_, lean_object* v_inst_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Std_HashMap_instRepr(v_00_u03b1_2185_, v_00_u03b2_2186_, v_inst_2187_, v_inst_2188_, v_inst_2189_, v_inst_2190_);
lean_dec_ref(v_inst_2188_);
lean_dec_ref(v_inst_2187_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__0(lean_object* v_a_2194_, lean_object* v_x_2195_){
_start:
{
lean_object* v___y_2197_; 
if (lean_obj_tag(v_x_2195_) == 0)
{
lean_object* v___x_2200_; 
v___x_2200_ = ((lean_object*)(l_Array_groupByKey___redArg___lam__0___closed__0));
v___y_2197_ = v___x_2200_;
goto v___jp_2196_;
}
else
{
lean_object* v_val_2201_; 
v_val_2201_ = lean_ctor_get(v_x_2195_, 0);
lean_inc(v_val_2201_);
lean_dec_ref(v_x_2195_);
v___y_2197_ = v_val_2201_;
goto v___jp_2196_;
}
v___jp_2196_:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = lean_array_push(v___y_2197_, v_a_2194_);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
return v___x_2199_;
}
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__1(lean_object* v_key_2202_, lean_object* v_inst_2203_, lean_object* v_inst_2204_, lean_object* v_a_2205_, lean_object* v_x_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v___f_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_inc(v_a_2205_);
v___f_2208_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2208_, 0, v_a_2205_);
v___x_2209_ = lean_apply_1(v_key_2202_, v_a_2205_);
v___x_2210_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_2203_, v_inst_2204_, v___y_2207_, v___x_2209_, v___f_2208_);
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg(lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_key_2214_, lean_object* v_xs_2215_){
_start:
{
lean_object* v___f_2216_; lean_object* v___x_2217_; lean_object* v_groups_2218_; size_t v_sz_2219_; size_t v___x_2220_; lean_object* v___x_2221_; 
v___f_2216_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__1), 6, 3);
lean_closure_set(v___f_2216_, 0, v_key_2214_);
lean_closure_set(v___f_2216_, 1, v_inst_2212_);
lean_closure_set(v___f_2216_, 2, v_inst_2213_);
v___x_2217_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_groups_2218_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v_sz_2219_ = lean_array_size(v_xs_2215_);
v___x_2220_ = ((size_t)0ULL);
v___x_2221_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2217_, v_xs_2215_, v___f_2216_, v_sz_2219_, v___x_2220_, v_groups_2218_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey(lean_object* v_00_u03b1_2222_, lean_object* v_00_u03b2_2223_, lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_key_2226_, lean_object* v_xs_2227_){
_start:
{
lean_object* v___x_2228_; 
v___x_2228_ = l_Array_groupByKey___redArg(v_inst_2224_, v_inst_2225_, v_key_2226_, v_xs_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__0(lean_object* v_x_2229_, lean_object* v_v_2230_){
_start:
{
lean_object* v___y_2232_; 
if (lean_obj_tag(v_v_2230_) == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = lean_box(0);
v___y_2232_ = v___x_2235_;
goto v___jp_2231_;
}
else
{
lean_object* v_val_2236_; 
v_val_2236_ = lean_ctor_get(v_v_2230_, 0);
lean_inc(v_val_2236_);
lean_dec_ref(v_v_2230_);
v___y_2232_ = v_val_2236_;
goto v___jp_2231_;
}
v___jp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2233_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2233_, 0, v_x_2229_);
lean_ctor_set(v___x_2233_, 1, v___y_2232_);
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__1(lean_object* v_key_2237_, lean_object* v_inst_2238_, lean_object* v_inst_2239_, lean_object* v_x_2240_, lean_object* v_acc_2241_){
_start:
{
lean_object* v___f_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
lean_inc(v_x_2240_);
v___f_2242_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2242_, 0, v_x_2240_);
v___x_2243_ = lean_apply_1(v_key_2237_, v_x_2240_);
v___x_2244_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_2238_, v_inst_2239_, v_acc_2241_, v___x_2243_, v___f_2242_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg(lean_object* v_inst_2245_, lean_object* v_inst_2246_, lean_object* v_key_2247_, lean_object* v_xs_2248_){
_start:
{
lean_object* v___f_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___f_2249_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__1), 5, 3);
lean_closure_set(v___f_2249_, 0, v_key_2247_);
lean_closure_set(v___f_2249_, 1, v_inst_2245_);
lean_closure_set(v___f_2249_, 2, v_inst_2246_);
v___x_2250_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_2251_ = l_List_foldrTR___redArg(v___f_2249_, v___x_2250_, v_xs_2248_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey(lean_object* v_00_u03b1_2252_, lean_object* v_00_u03b2_2253_, lean_object* v_inst_2254_, lean_object* v_inst_2255_, lean_object* v_key_2256_, lean_object* v_xs_2257_){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = l_List_groupByKey___redArg(v_inst_2254_, v_inst_2255_, v_key_2256_, v_xs_2257_);
return v___x_2258_;
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
