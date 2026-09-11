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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* lean_array_mark_linear(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear___redArg(lean_object* v_m_59_){
_start:
{
lean_object* v_size_60_; lean_object* v_buckets_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_69_; 
v_size_60_ = lean_ctor_get(v_m_59_, 0);
v_buckets_61_ = lean_ctor_get(v_m_59_, 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v_m_59_);
if (v_isSharedCheck_69_ == 0)
{
v___x_63_ = v_m_59_;
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_buckets_61_);
lean_inc(v_size_60_);
lean_dec(v_m_59_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_69_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_65_ = lean_array_mark_linear(v_buckets_61_);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 1, v___x_65_);
v___x_67_ = v___x_63_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_size_60_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v___x_65_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear(lean_object* v_00_u03b1_70_, lean_object* v_00_u03b2_71_, lean_object* v_x_72_, lean_object* v_x_73_, lean_object* v_m_74_){
_start:
{
lean_object* v_size_75_; lean_object* v_buckets_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_84_; 
v_size_75_ = lean_ctor_get(v_m_74_, 0);
v_buckets_76_ = lean_ctor_get(v_m_74_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_m_74_);
if (v_isSharedCheck_84_ == 0)
{
v___x_78_ = v_m_74_;
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_buckets_76_);
lean_inc(v_size_75_);
lean_dec(v_m_74_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_84_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = lean_array_mark_linear(v_buckets_76_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v___x_80_);
v___x_82_ = v___x_78_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_size_75_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear___boxed(lean_object* v_00_u03b1_85_, lean_object* v_00_u03b2_86_, lean_object* v_x_87_, lean_object* v_x_88_, lean_object* v_m_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Std_HashMap_markLinear(v_00_u03b1_85_, v_00_u03b2_86_, v_x_87_, v_x_88_, v_m_89_);
lean_dec_ref(v_x_88_);
lean_dec_ref(v_x_87_);
return v_res_90_;
}
}
static lean_object* _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5));
v___x_130_ = l_String_toRawSubstring_x27(v___x_129_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(lean_object* v_x_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_154_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
lean_inc(v_x_151_);
v___x_155_ = l_Lean_Syntax_isOfKind(v_x_151_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v_x_151_);
v___x_156_ = lean_box(1);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_153_);
return v___x_157_;
}
else
{
lean_object* v_quotContext_158_; lean_object* v_currMacroScope_159_; lean_object* v_ref_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v_quotContext_158_ = lean_ctor_get(v_a_152_, 1);
v_currMacroScope_159_ = lean_ctor_get(v_a_152_, 2);
v_ref_160_ = lean_ctor_get(v_a_152_, 5);
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = l_Lean_Syntax_getArg(v_x_151_, v___x_161_);
v___x_163_ = lean_unsigned_to_nat(2u);
v___x_164_ = l_Lean_Syntax_getArg(v_x_151_, v___x_163_);
lean_dec(v_x_151_);
v___x_165_ = 0;
v___x_166_ = l_Lean_SourceInfo_fromRef(v_ref_160_, v___x_165_);
v___x_167_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
v___x_168_ = lean_obj_once(&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6, &l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6_once, _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6);
v___x_169_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_159_);
lean_inc(v_quotContext_158_);
v___x_170_ = l_Lean_addMacroScope(v_quotContext_158_, v___x_169_, v_currMacroScope_159_);
v___x_171_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12));
lean_inc_n(v___x_166_, 2);
v___x_172_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_172_, 0, v___x_166_);
lean_ctor_set(v___x_172_, 1, v___x_168_);
lean_ctor_set(v___x_172_, 2, v___x_170_);
lean_ctor_set(v___x_172_, 3, v___x_171_);
v___x_173_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14));
v___x_174_ = l_Lean_Syntax_node2(v___x_166_, v___x_173_, v___x_162_, v___x_164_);
v___x_175_ = l_Lean_Syntax_node2(v___x_166_, v___x_167_, v___x_172_, v___x_174_);
v___x_176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_a_153_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___boxed(lean_object* v_x_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_res_180_; 
v_res_180_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(v_x_177_, v_a_178_, v_a_179_);
lean_dec_ref(v_a_178_);
return v_res_180_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(lean_object* v_x_184_, lean_object* v_a_185_, lean_object* v_a_186_){
_start:
{
lean_object* v___x_187_; uint8_t v___x_188_; 
v___x_187_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
lean_inc(v_x_184_);
v___x_188_ = l_Lean_Syntax_isOfKind(v_x_184_, v___x_187_);
if (v___x_188_ == 0)
{
lean_object* v___x_189_; lean_object* v___x_190_; 
lean_dec(v_x_184_);
v___x_189_ = lean_box(0);
v___x_190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_186_);
return v___x_190_;
}
else
{
lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; uint8_t v___x_194_; 
v___x_191_ = lean_unsigned_to_nat(0u);
v___x_192_ = l_Lean_Syntax_getArg(v_x_184_, v___x_191_);
v___x_193_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1));
lean_inc(v___x_192_);
v___x_194_ = l_Lean_Syntax_isOfKind(v___x_192_, v___x_193_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; lean_object* v___x_196_; 
lean_dec(v___x_192_);
lean_dec(v_x_184_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_186_);
return v___x_196_;
}
else
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = l_Lean_Syntax_getArg(v_x_184_, v___x_197_);
lean_dec(v_x_184_);
v___x_199_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_198_);
v___x_200_ = l_Lean_Syntax_matchesNull(v___x_198_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v___x_198_);
lean_dec(v___x_192_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_a_186_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v_ref_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_203_ = l_Lean_Syntax_getArg(v___x_198_, v___x_191_);
v___x_204_ = l_Lean_Syntax_getArg(v___x_198_, v___x_197_);
lean_dec(v___x_198_);
v_ref_205_ = l_Lean_replaceRef(v___x_192_, v_a_185_);
lean_dec(v___x_192_);
v___x_206_ = 0;
v___x_207_ = l_Lean_SourceInfo_fromRef(v_ref_205_, v___x_206_);
lean_dec(v_ref_205_);
v___x_208_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
v___x_209_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__6));
lean_inc(v___x_207_);
v___x_210_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_207_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = l_Lean_Syntax_node3(v___x_207_, v___x_208_, v___x_203_, v___x_210_, v___x_204_);
v___x_212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v_a_186_);
return v___x_212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___boxed(lean_object* v_x_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(v_x_213_, v_a_214_, v_a_215_);
lean_dec(v_a_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___redArg(lean_object* v_x_217_, lean_object* v_x_218_, lean_object* v_m_219_, lean_object* v_a_220_, lean_object* v_b_221_){
_start:
{
lean_object* v___x_222_; 
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_217_, v_x_218_, v_m_219_, v_a_220_, v_b_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert(lean_object* v_00_u03b1_223_, lean_object* v_00_u03b2_224_, lean_object* v_x_225_, lean_object* v_x_226_, lean_object* v_m_227_, lean_object* v_a_228_, lean_object* v_b_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_225_, v_x_226_, v_m_227_, v_a_228_, v_b_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg___lam__0(lean_object* v_x_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
lean_object* v_fst_234_; lean_object* v_snd_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_fst_234_ = lean_ctor_get(v_x_233_, 0);
lean_inc(v_fst_234_);
v_snd_235_ = lean_ctor_get(v_x_233_, 1);
lean_inc(v_snd_235_);
lean_dec_ref(v_x_233_);
v___x_236_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_231_, v_x_232_, v___x_236_, v_fst_234_, v_snd_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg(lean_object* v_x_238_, lean_object* v_x_239_){
_start:
{
lean_object* v___f_240_; 
v___f_240_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_240_, 0, v_x_238_);
lean_closure_set(v___f_240_, 1, v_x_239_);
return v___f_240_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd(lean_object* v_00_u03b1_241_, lean_object* v_00_u03b2_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
lean_object* v___f_245_; 
v___f_245_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_245_, 0, v_x_243_);
lean_closure_set(v___f_245_, 1, v_x_244_);
return v___f_245_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg___lam__0(lean_object* v_x_246_, lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_s_249_){
_start:
{
lean_object* v_fst_250_; lean_object* v_snd_251_; lean_object* v___x_252_; 
v_fst_250_ = lean_ctor_get(v_x_248_, 0);
lean_inc(v_fst_250_);
v_snd_251_ = lean_ctor_get(v_x_248_, 1);
lean_inc(v_snd_251_);
lean_dec_ref(v_x_248_);
v___x_252_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_246_, v_x_247_, v_s_249_, v_fst_250_, v_snd_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg(lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_255_, 0, v_x_253_);
lean_closure_set(v___f_255_, 1, v_x_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd(lean_object* v_00_u03b1_256_, lean_object* v_00_u03b2_257_, lean_object* v_x_258_, lean_object* v_x_259_){
_start:
{
lean_object* v___f_260_; 
v___f_260_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_260_, 0, v_x_258_);
lean_closure_set(v___f_260_, 1, v_x_259_);
return v___f_260_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew___redArg(lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_m_263_, lean_object* v_a_264_, lean_object* v_b_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_261_, v_x_262_, v_m_263_, v_a_264_, v_b_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew(lean_object* v_00_u03b1_267_, lean_object* v_00_u03b2_268_, lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_m_271_, lean_object* v_a_272_, lean_object* v_b_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_269_, v_x_270_, v_m_271_, v_a_272_, v_b_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert___redArg(lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_m_277_, lean_object* v_a_278_, lean_object* v_b_279_){
_start:
{
lean_object* v_size_280_; lean_object* v_buckets_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_332_; 
v_size_280_ = lean_ctor_get(v_m_277_, 0);
v_buckets_281_ = lean_ctor_get(v_m_277_, 1);
v_isSharedCheck_332_ = !lean_is_exclusive(v_m_277_);
if (v_isSharedCheck_332_ == 0)
{
v___x_283_ = v_m_277_;
v_isShared_284_ = v_isSharedCheck_332_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_buckets_281_);
lean_inc(v_size_280_);
lean_dec(v_m_277_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_332_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; uint64_t v___x_287_; uint64_t v___x_288_; uint64_t v___x_289_; uint64_t v___x_290_; uint64_t v_fold_291_; uint64_t v___x_292_; uint64_t v___x_293_; uint64_t v___x_294_; size_t v___x_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v_bkt_300_; uint8_t v___x_301_; 
v___x_285_ = lean_array_get_size(v_buckets_281_);
lean_inc_ref(v_x_276_);
lean_inc_n(v_a_278_, 2);
v___x_286_ = lean_apply_1(v_x_276_, v_a_278_);
v___x_287_ = 32ULL;
v___x_288_ = lean_unbox_uint64(v___x_286_);
v___x_289_ = lean_uint64_shift_right(v___x_288_, v___x_287_);
v___x_290_ = lean_unbox_uint64(v___x_286_);
lean_dec_ref(v___x_286_);
v_fold_291_ = lean_uint64_xor(v___x_290_, v___x_289_);
v___x_292_ = 16ULL;
v___x_293_ = lean_uint64_shift_right(v_fold_291_, v___x_292_);
v___x_294_ = lean_uint64_xor(v_fold_291_, v___x_293_);
v___x_295_ = lean_uint64_to_usize(v___x_294_);
v___x_296_ = lean_usize_of_nat(v___x_285_);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_sub(v___x_296_, v___x_297_);
v___x_299_ = lean_usize_land(v___x_295_, v___x_298_);
v_bkt_300_ = lean_array_uget_borrowed(v_buckets_281_, v___x_299_);
lean_inc(v_bkt_300_);
lean_inc_ref(v_x_275_);
v___x_301_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_275_, v_a_278_, v_bkt_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v_size_x27_303_; lean_object* v___x_304_; lean_object* v_buckets_x27_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
lean_dec_ref(v_x_275_);
v___x_302_ = lean_unsigned_to_nat(1u);
v_size_x27_303_ = lean_nat_add(v_size_280_, v___x_302_);
lean_dec(v_size_280_);
lean_inc(v_bkt_300_);
v___x_304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_304_, 0, v_a_278_);
lean_ctor_set(v___x_304_, 1, v_b_279_);
lean_ctor_set(v___x_304_, 2, v_bkt_300_);
v_buckets_x27_305_ = lean_array_uset(v_buckets_281_, v___x_299_, v___x_304_);
v___x_306_ = lean_unsigned_to_nat(4u);
v___x_307_ = lean_nat_mul(v_size_x27_303_, v___x_306_);
v___x_308_ = lean_unsigned_to_nat(3u);
v___x_309_ = lean_nat_div(v___x_307_, v___x_308_);
lean_dec(v___x_307_);
v___x_310_ = lean_array_get_size(v_buckets_x27_305_);
v___x_311_ = lean_nat_dec_le(v___x_309_, v___x_310_);
lean_dec(v___x_309_);
if (v___x_311_ == 0)
{
lean_object* v_val_312_; lean_object* v___x_314_; 
v_val_312_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_276_, v_buckets_x27_305_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_val_312_);
lean_ctor_set(v___x_283_, 0, v_size_x27_303_);
v___x_314_ = v___x_283_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_size_x27_303_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_val_312_);
v___x_314_ = v_reuseFailAlloc_317_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; 
v___x_315_ = lean_box(v___x_301_);
v___x_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_315_);
lean_ctor_set(v___x_316_, 1, v___x_314_);
return v___x_316_;
}
}
else
{
lean_object* v___x_319_; 
lean_dec_ref(v_x_276_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v_buckets_x27_305_);
lean_ctor_set(v___x_283_, 0, v_size_x27_303_);
v___x_319_ = v___x_283_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_size_x27_303_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_buckets_x27_305_);
v___x_319_ = v_reuseFailAlloc_322_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_320_ = lean_box(v___x_301_);
v___x_321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
lean_ctor_set(v___x_321_, 1, v___x_319_);
return v___x_321_;
}
}
}
else
{
lean_object* v___x_323_; lean_object* v_buckets_x27_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
lean_inc(v_bkt_300_);
lean_dec_ref(v_x_276_);
v___x_323_ = lean_box(0);
v_buckets_x27_324_ = lean_array_uset(v_buckets_281_, v___x_299_, v___x_323_);
v___x_325_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_275_, v_a_278_, v_b_279_, v_bkt_300_);
v___x_326_ = lean_array_uset(v_buckets_x27_324_, v___x_299_, v___x_325_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 1, v___x_326_);
v___x_328_ = v___x_283_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_size_280_);
lean_ctor_set(v_reuseFailAlloc_331_, 1, v___x_326_);
v___x_328_ = v_reuseFailAlloc_331_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v___x_329_; lean_object* v___x_330_; 
v___x_329_ = lean_box(v___x_301_);
v___x_330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_329_);
lean_ctor_set(v___x_330_, 1, v___x_328_);
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert(lean_object* v_00_u03b1_333_, lean_object* v_00_u03b2_334_, lean_object* v_x_335_, lean_object* v_x_336_, lean_object* v_m_337_, lean_object* v_a_338_, lean_object* v_b_339_){
_start:
{
lean_object* v_size_340_; lean_object* v_buckets_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_392_; 
v_size_340_ = lean_ctor_get(v_m_337_, 0);
v_buckets_341_ = lean_ctor_get(v_m_337_, 1);
v_isSharedCheck_392_ = !lean_is_exclusive(v_m_337_);
if (v_isSharedCheck_392_ == 0)
{
v___x_343_ = v_m_337_;
v_isShared_344_ = v_isSharedCheck_392_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_buckets_341_);
lean_inc(v_size_340_);
lean_dec(v_m_337_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_392_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_345_; lean_object* v___x_346_; uint64_t v___x_347_; uint64_t v___x_348_; uint64_t v___x_349_; uint64_t v___x_350_; uint64_t v_fold_351_; uint64_t v___x_352_; uint64_t v___x_353_; uint64_t v___x_354_; size_t v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v___x_359_; lean_object* v_bkt_360_; uint8_t v___x_361_; 
v___x_345_ = lean_array_get_size(v_buckets_341_);
lean_inc_ref(v_x_336_);
lean_inc_n(v_a_338_, 2);
v___x_346_ = lean_apply_1(v_x_336_, v_a_338_);
v___x_347_ = 32ULL;
v___x_348_ = lean_unbox_uint64(v___x_346_);
v___x_349_ = lean_uint64_shift_right(v___x_348_, v___x_347_);
v___x_350_ = lean_unbox_uint64(v___x_346_);
lean_dec_ref(v___x_346_);
v_fold_351_ = lean_uint64_xor(v___x_350_, v___x_349_);
v___x_352_ = 16ULL;
v___x_353_ = lean_uint64_shift_right(v_fold_351_, v___x_352_);
v___x_354_ = lean_uint64_xor(v_fold_351_, v___x_353_);
v___x_355_ = lean_uint64_to_usize(v___x_354_);
v___x_356_ = lean_usize_of_nat(v___x_345_);
v___x_357_ = ((size_t)1ULL);
v___x_358_ = lean_usize_sub(v___x_356_, v___x_357_);
v___x_359_ = lean_usize_land(v___x_355_, v___x_358_);
v_bkt_360_ = lean_array_uget_borrowed(v_buckets_341_, v___x_359_);
lean_inc(v_bkt_360_);
lean_inc_ref(v_x_335_);
v___x_361_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_335_, v_a_338_, v_bkt_360_);
if (v___x_361_ == 0)
{
lean_object* v___x_362_; lean_object* v_size_x27_363_; lean_object* v___x_364_; lean_object* v_buckets_x27_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
lean_dec_ref(v_x_335_);
v___x_362_ = lean_unsigned_to_nat(1u);
v_size_x27_363_ = lean_nat_add(v_size_340_, v___x_362_);
lean_dec(v_size_340_);
lean_inc(v_bkt_360_);
v___x_364_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_364_, 0, v_a_338_);
lean_ctor_set(v___x_364_, 1, v_b_339_);
lean_ctor_set(v___x_364_, 2, v_bkt_360_);
v_buckets_x27_365_ = lean_array_uset(v_buckets_341_, v___x_359_, v___x_364_);
v___x_366_ = lean_unsigned_to_nat(4u);
v___x_367_ = lean_nat_mul(v_size_x27_363_, v___x_366_);
v___x_368_ = lean_unsigned_to_nat(3u);
v___x_369_ = lean_nat_div(v___x_367_, v___x_368_);
lean_dec(v___x_367_);
v___x_370_ = lean_array_get_size(v_buckets_x27_365_);
v___x_371_ = lean_nat_dec_le(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
if (v___x_371_ == 0)
{
lean_object* v_val_372_; lean_object* v___x_374_; 
v_val_372_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_336_, v_buckets_x27_365_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v_val_372_);
lean_ctor_set(v___x_343_, 0, v_size_x27_363_);
v___x_374_ = v___x_343_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_size_x27_363_);
lean_ctor_set(v_reuseFailAlloc_377_, 1, v_val_372_);
v___x_374_ = v_reuseFailAlloc_377_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_375_ = lean_box(v___x_361_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
return v___x_376_;
}
}
else
{
lean_object* v___x_379_; 
lean_dec_ref(v_x_336_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v_buckets_x27_365_);
lean_ctor_set(v___x_343_, 0, v_size_x27_363_);
v___x_379_ = v___x_343_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_size_x27_363_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v_buckets_x27_365_);
v___x_379_ = v_reuseFailAlloc_382_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
v___x_380_ = lean_box(v___x_361_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
lean_ctor_set(v___x_381_, 1, v___x_379_);
return v___x_381_;
}
}
}
else
{
lean_object* v___x_383_; lean_object* v_buckets_x27_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_388_; 
lean_inc(v_bkt_360_);
lean_dec_ref(v_x_336_);
v___x_383_ = lean_box(0);
v_buckets_x27_384_ = lean_array_uset(v_buckets_341_, v___x_359_, v___x_383_);
v___x_385_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_335_, v_a_338_, v_b_339_, v_bkt_360_);
v___x_386_ = lean_array_uset(v_buckets_x27_384_, v___x_359_, v___x_385_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 1, v___x_386_);
v___x_388_ = v___x_343_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_391_; 
v_reuseFailAlloc_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_391_, 0, v_size_340_);
lean_ctor_set(v_reuseFailAlloc_391_, 1, v___x_386_);
v___x_388_ = v_reuseFailAlloc_391_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = lean_box(v___x_361_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_388_);
return v___x_390_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew___redArg(lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_m_395_, lean_object* v_a_396_, lean_object* v_b_397_){
_start:
{
lean_object* v_size_398_; lean_object* v_buckets_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v_fold_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v_bkt_415_; uint8_t v___x_416_; 
v_size_398_ = lean_ctor_get(v_m_395_, 0);
v_buckets_399_ = lean_ctor_get(v_m_395_, 1);
v___x_400_ = lean_array_get_size(v_buckets_399_);
lean_inc_ref(v_x_394_);
lean_inc_n(v_a_396_, 2);
v___x_401_ = lean_apply_1(v_x_394_, v_a_396_);
v___x_402_ = 32ULL;
v___x_403_ = lean_unbox_uint64(v___x_401_);
v___x_404_ = lean_uint64_shift_right(v___x_403_, v___x_402_);
v___x_405_ = lean_unbox_uint64(v___x_401_);
lean_dec_ref(v___x_401_);
v_fold_406_ = lean_uint64_xor(v___x_405_, v___x_404_);
v___x_407_ = 16ULL;
v___x_408_ = lean_uint64_shift_right(v_fold_406_, v___x_407_);
v___x_409_ = lean_uint64_xor(v_fold_406_, v___x_408_);
v___x_410_ = lean_uint64_to_usize(v___x_409_);
v___x_411_ = lean_usize_of_nat(v___x_400_);
v___x_412_ = ((size_t)1ULL);
v___x_413_ = lean_usize_sub(v___x_411_, v___x_412_);
v___x_414_ = lean_usize_land(v___x_410_, v___x_413_);
v_bkt_415_ = lean_array_uget_borrowed(v_buckets_399_, v___x_414_);
lean_inc(v_bkt_415_);
v___x_416_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_393_, v_a_396_, v_bkt_415_);
if (v___x_416_ == 0)
{
lean_object* v___x_418_; uint8_t v_isShared_419_; uint8_t v_isSharedCheck_441_; 
lean_inc_ref(v_buckets_399_);
lean_inc(v_size_398_);
v_isSharedCheck_441_ = !lean_is_exclusive(v_m_395_);
if (v_isSharedCheck_441_ == 0)
{
lean_object* v_unused_442_; lean_object* v_unused_443_; 
v_unused_442_ = lean_ctor_get(v_m_395_, 1);
lean_dec(v_unused_442_);
v_unused_443_ = lean_ctor_get(v_m_395_, 0);
lean_dec(v_unused_443_);
v___x_418_ = v_m_395_;
v_isShared_419_ = v_isSharedCheck_441_;
goto v_resetjp_417_;
}
else
{
lean_dec(v_m_395_);
v___x_418_ = lean_box(0);
v_isShared_419_ = v_isSharedCheck_441_;
goto v_resetjp_417_;
}
v_resetjp_417_:
{
lean_object* v___x_420_; lean_object* v_size_x27_421_; lean_object* v___x_422_; lean_object* v_buckets_x27_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_420_ = lean_unsigned_to_nat(1u);
v_size_x27_421_ = lean_nat_add(v_size_398_, v___x_420_);
lean_dec(v_size_398_);
lean_inc(v_bkt_415_);
v___x_422_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_422_, 0, v_a_396_);
lean_ctor_set(v___x_422_, 1, v_b_397_);
lean_ctor_set(v___x_422_, 2, v_bkt_415_);
v_buckets_x27_423_ = lean_array_uset(v_buckets_399_, v___x_414_, v___x_422_);
v___x_424_ = lean_unsigned_to_nat(4u);
v___x_425_ = lean_nat_mul(v_size_x27_421_, v___x_424_);
v___x_426_ = lean_unsigned_to_nat(3u);
v___x_427_ = lean_nat_div(v___x_425_, v___x_426_);
lean_dec(v___x_425_);
v___x_428_ = lean_array_get_size(v_buckets_x27_423_);
v___x_429_ = lean_nat_dec_le(v___x_427_, v___x_428_);
lean_dec(v___x_427_);
if (v___x_429_ == 0)
{
lean_object* v_val_430_; lean_object* v___x_432_; 
v_val_430_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_394_, v_buckets_x27_423_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v_val_430_);
lean_ctor_set(v___x_418_, 0, v_size_x27_421_);
v___x_432_ = v___x_418_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_size_x27_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_val_430_);
v___x_432_ = v_reuseFailAlloc_435_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
v___x_433_ = lean_box(v___x_416_);
v___x_434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_434_, 0, v___x_433_);
lean_ctor_set(v___x_434_, 1, v___x_432_);
return v___x_434_;
}
}
else
{
lean_object* v___x_437_; 
lean_dec_ref(v_x_394_);
if (v_isShared_419_ == 0)
{
lean_ctor_set(v___x_418_, 1, v_buckets_x27_423_);
lean_ctor_set(v___x_418_, 0, v_size_x27_421_);
v___x_437_ = v___x_418_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_size_x27_421_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_buckets_x27_423_);
v___x_437_ = v_reuseFailAlloc_440_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_box(v___x_416_);
v___x_439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___x_437_);
return v___x_439_;
}
}
}
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; 
lean_dec(v_b_397_);
lean_dec(v_a_396_);
lean_dec_ref(v_x_394_);
v___x_444_ = lean_box(v___x_416_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v___x_444_);
lean_ctor_set(v___x_445_, 1, v_m_395_);
return v___x_445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_m_450_, lean_object* v_a_451_, lean_object* v_b_452_){
_start:
{
lean_object* v_size_453_; lean_object* v_buckets_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint64_t v___x_457_; uint64_t v___x_458_; uint64_t v___x_459_; uint64_t v___x_460_; uint64_t v_fold_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v___x_464_; size_t v___x_465_; size_t v___x_466_; size_t v___x_467_; size_t v___x_468_; size_t v___x_469_; lean_object* v_bkt_470_; uint8_t v___x_471_; 
v_size_453_ = lean_ctor_get(v_m_450_, 0);
v_buckets_454_ = lean_ctor_get(v_m_450_, 1);
v___x_455_ = lean_array_get_size(v_buckets_454_);
lean_inc_ref(v_x_449_);
lean_inc_n(v_a_451_, 2);
v___x_456_ = lean_apply_1(v_x_449_, v_a_451_);
v___x_457_ = 32ULL;
v___x_458_ = lean_unbox_uint64(v___x_456_);
v___x_459_ = lean_uint64_shift_right(v___x_458_, v___x_457_);
v___x_460_ = lean_unbox_uint64(v___x_456_);
lean_dec_ref(v___x_456_);
v_fold_461_ = lean_uint64_xor(v___x_460_, v___x_459_);
v___x_462_ = 16ULL;
v___x_463_ = lean_uint64_shift_right(v_fold_461_, v___x_462_);
v___x_464_ = lean_uint64_xor(v_fold_461_, v___x_463_);
v___x_465_ = lean_uint64_to_usize(v___x_464_);
v___x_466_ = lean_usize_of_nat(v___x_455_);
v___x_467_ = ((size_t)1ULL);
v___x_468_ = lean_usize_sub(v___x_466_, v___x_467_);
v___x_469_ = lean_usize_land(v___x_465_, v___x_468_);
v_bkt_470_ = lean_array_uget_borrowed(v_buckets_454_, v___x_469_);
lean_inc(v_bkt_470_);
v___x_471_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_448_, v_a_451_, v_bkt_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_473_; uint8_t v_isShared_474_; uint8_t v_isSharedCheck_496_; 
lean_inc_ref(v_buckets_454_);
lean_inc(v_size_453_);
v_isSharedCheck_496_ = !lean_is_exclusive(v_m_450_);
if (v_isSharedCheck_496_ == 0)
{
lean_object* v_unused_497_; lean_object* v_unused_498_; 
v_unused_497_ = lean_ctor_get(v_m_450_, 1);
lean_dec(v_unused_497_);
v_unused_498_ = lean_ctor_get(v_m_450_, 0);
lean_dec(v_unused_498_);
v___x_473_ = v_m_450_;
v_isShared_474_ = v_isSharedCheck_496_;
goto v_resetjp_472_;
}
else
{
lean_dec(v_m_450_);
v___x_473_ = lean_box(0);
v_isShared_474_ = v_isSharedCheck_496_;
goto v_resetjp_472_;
}
v_resetjp_472_:
{
lean_object* v___x_475_; lean_object* v_size_x27_476_; lean_object* v___x_477_; lean_object* v_buckets_x27_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_475_ = lean_unsigned_to_nat(1u);
v_size_x27_476_ = lean_nat_add(v_size_453_, v___x_475_);
lean_dec(v_size_453_);
lean_inc(v_bkt_470_);
v___x_477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_477_, 0, v_a_451_);
lean_ctor_set(v___x_477_, 1, v_b_452_);
lean_ctor_set(v___x_477_, 2, v_bkt_470_);
v_buckets_x27_478_ = lean_array_uset(v_buckets_454_, v___x_469_, v___x_477_);
v___x_479_ = lean_unsigned_to_nat(4u);
v___x_480_ = lean_nat_mul(v_size_x27_476_, v___x_479_);
v___x_481_ = lean_unsigned_to_nat(3u);
v___x_482_ = lean_nat_div(v___x_480_, v___x_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_array_get_size(v_buckets_x27_478_);
v___x_484_ = lean_nat_dec_le(v___x_482_, v___x_483_);
lean_dec(v___x_482_);
if (v___x_484_ == 0)
{
lean_object* v_val_485_; lean_object* v___x_487_; 
v_val_485_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_449_, v_buckets_x27_478_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v_val_485_);
lean_ctor_set(v___x_473_, 0, v_size_x27_476_);
v___x_487_ = v___x_473_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_size_x27_476_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_val_485_);
v___x_487_ = v_reuseFailAlloc_490_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_box(v___x_471_);
v___x_489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v___x_487_);
return v___x_489_;
}
}
else
{
lean_object* v___x_492_; 
lean_dec_ref(v_x_449_);
if (v_isShared_474_ == 0)
{
lean_ctor_set(v___x_473_, 1, v_buckets_x27_478_);
lean_ctor_set(v___x_473_, 0, v_size_x27_476_);
v___x_492_ = v___x_473_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_size_x27_476_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v_buckets_x27_478_);
v___x_492_ = v_reuseFailAlloc_495_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
v___x_493_ = lean_box(v___x_471_);
v___x_494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___x_492_);
return v___x_494_;
}
}
}
}
else
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec(v_b_452_);
lean_dec(v_a_451_);
lean_dec_ref(v_x_449_);
v___x_499_ = lean_box(v___x_471_);
v___x_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v_m_450_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_501_, lean_object* v_x_502_, lean_object* v_m_503_, lean_object* v_a_504_, lean_object* v_b_505_){
_start:
{
lean_object* v_size_506_; lean_object* v_buckets_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint64_t v___x_510_; uint64_t v___x_511_; uint64_t v___x_512_; uint64_t v___x_513_; uint64_t v_fold_514_; uint64_t v___x_515_; uint64_t v___x_516_; uint64_t v___x_517_; size_t v___x_518_; size_t v___x_519_; size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; lean_object* v_bkt_523_; lean_object* v___x_524_; 
v_size_506_ = lean_ctor_get(v_m_503_, 0);
v_buckets_507_ = lean_ctor_get(v_m_503_, 1);
v___x_508_ = lean_array_get_size(v_buckets_507_);
lean_inc_ref(v_x_502_);
lean_inc_n(v_a_504_, 2);
v___x_509_ = lean_apply_1(v_x_502_, v_a_504_);
v___x_510_ = 32ULL;
v___x_511_ = lean_unbox_uint64(v___x_509_);
v___x_512_ = lean_uint64_shift_right(v___x_511_, v___x_510_);
v___x_513_ = lean_unbox_uint64(v___x_509_);
lean_dec_ref(v___x_509_);
v_fold_514_ = lean_uint64_xor(v___x_513_, v___x_512_);
v___x_515_ = 16ULL;
v___x_516_ = lean_uint64_shift_right(v_fold_514_, v___x_515_);
v___x_517_ = lean_uint64_xor(v_fold_514_, v___x_516_);
v___x_518_ = lean_uint64_to_usize(v___x_517_);
v___x_519_ = lean_usize_of_nat(v___x_508_);
v___x_520_ = ((size_t)1ULL);
v___x_521_ = lean_usize_sub(v___x_519_, v___x_520_);
v___x_522_ = lean_usize_land(v___x_518_, v___x_521_);
v_bkt_523_ = lean_array_uget_borrowed(v_buckets_507_, v___x_522_);
lean_inc(v_bkt_523_);
v___x_524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_501_, v_a_504_, v_bkt_523_);
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_547_; 
lean_inc_ref(v_buckets_507_);
lean_inc(v_size_506_);
v_isSharedCheck_547_ = !lean_is_exclusive(v_m_503_);
if (v_isSharedCheck_547_ == 0)
{
lean_object* v_unused_548_; lean_object* v_unused_549_; 
v_unused_548_ = lean_ctor_get(v_m_503_, 1);
lean_dec(v_unused_548_);
v_unused_549_ = lean_ctor_get(v_m_503_, 0);
lean_dec(v_unused_549_);
v___x_526_ = v_m_503_;
v_isShared_527_ = v_isSharedCheck_547_;
goto v_resetjp_525_;
}
else
{
lean_dec(v_m_503_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_547_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
lean_object* v___x_528_; lean_object* v_size_x27_529_; lean_object* v___x_530_; lean_object* v_buckets_x27_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; uint8_t v___x_537_; 
v___x_528_ = lean_unsigned_to_nat(1u);
v_size_x27_529_ = lean_nat_add(v_size_506_, v___x_528_);
lean_dec(v_size_506_);
lean_inc(v_bkt_523_);
v___x_530_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_530_, 0, v_a_504_);
lean_ctor_set(v___x_530_, 1, v_b_505_);
lean_ctor_set(v___x_530_, 2, v_bkt_523_);
v_buckets_x27_531_ = lean_array_uset(v_buckets_507_, v___x_522_, v___x_530_);
v___x_532_ = lean_unsigned_to_nat(4u);
v___x_533_ = lean_nat_mul(v_size_x27_529_, v___x_532_);
v___x_534_ = lean_unsigned_to_nat(3u);
v___x_535_ = lean_nat_div(v___x_533_, v___x_534_);
lean_dec(v___x_533_);
v___x_536_ = lean_array_get_size(v_buckets_x27_531_);
v___x_537_ = lean_nat_dec_le(v___x_535_, v___x_536_);
lean_dec(v___x_535_);
if (v___x_537_ == 0)
{
lean_object* v_val_538_; lean_object* v___x_540_; 
v_val_538_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_502_, v_buckets_x27_531_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v_val_538_);
lean_ctor_set(v___x_526_, 0, v_size_x27_529_);
v___x_540_ = v___x_526_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_size_x27_529_);
lean_ctor_set(v_reuseFailAlloc_542_, 1, v_val_538_);
v___x_540_ = v_reuseFailAlloc_542_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v___x_541_; 
v___x_541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_524_);
lean_ctor_set(v___x_541_, 1, v___x_540_);
return v___x_541_;
}
}
else
{
lean_object* v___x_544_; 
lean_dec_ref(v_x_502_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v_buckets_x27_531_);
lean_ctor_set(v___x_526_, 0, v_size_x27_529_);
v___x_544_ = v___x_526_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_size_x27_529_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_buckets_x27_531_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_524_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
return v___x_545_;
}
}
}
}
else
{
lean_object* v___x_550_; 
lean_dec(v_b_505_);
lean_dec(v_a_504_);
lean_dec_ref(v_x_502_);
v___x_550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_524_);
lean_ctor_set(v___x_550_, 1, v_m_503_);
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_551_, lean_object* v_00_u03b2_552_, lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_m_555_, lean_object* v_a_556_, lean_object* v_b_557_){
_start:
{
lean_object* v_size_558_; lean_object* v_buckets_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint64_t v___x_562_; uint64_t v___x_563_; uint64_t v___x_564_; uint64_t v___x_565_; uint64_t v_fold_566_; uint64_t v___x_567_; uint64_t v___x_568_; uint64_t v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v___x_573_; size_t v___x_574_; lean_object* v_bkt_575_; lean_object* v___x_576_; 
v_size_558_ = lean_ctor_get(v_m_555_, 0);
v_buckets_559_ = lean_ctor_get(v_m_555_, 1);
v___x_560_ = lean_array_get_size(v_buckets_559_);
lean_inc_ref(v_x_554_);
lean_inc_n(v_a_556_, 2);
v___x_561_ = lean_apply_1(v_x_554_, v_a_556_);
v___x_562_ = 32ULL;
v___x_563_ = lean_unbox_uint64(v___x_561_);
v___x_564_ = lean_uint64_shift_right(v___x_563_, v___x_562_);
v___x_565_ = lean_unbox_uint64(v___x_561_);
lean_dec_ref(v___x_561_);
v_fold_566_ = lean_uint64_xor(v___x_565_, v___x_564_);
v___x_567_ = 16ULL;
v___x_568_ = lean_uint64_shift_right(v_fold_566_, v___x_567_);
v___x_569_ = lean_uint64_xor(v_fold_566_, v___x_568_);
v___x_570_ = lean_uint64_to_usize(v___x_569_);
v___x_571_ = lean_usize_of_nat(v___x_560_);
v___x_572_ = ((size_t)1ULL);
v___x_573_ = lean_usize_sub(v___x_571_, v___x_572_);
v___x_574_ = lean_usize_land(v___x_570_, v___x_573_);
v_bkt_575_ = lean_array_uget_borrowed(v_buckets_559_, v___x_574_);
lean_inc(v_bkt_575_);
v___x_576_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_553_, v_a_556_, v_bkt_575_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_599_; 
lean_inc_ref(v_buckets_559_);
lean_inc(v_size_558_);
v_isSharedCheck_599_ = !lean_is_exclusive(v_m_555_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; lean_object* v_unused_601_; 
v_unused_600_ = lean_ctor_get(v_m_555_, 1);
lean_dec(v_unused_600_);
v_unused_601_ = lean_ctor_get(v_m_555_, 0);
lean_dec(v_unused_601_);
v___x_578_ = v_m_555_;
v_isShared_579_ = v_isSharedCheck_599_;
goto v_resetjp_577_;
}
else
{
lean_dec(v_m_555_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_599_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
lean_object* v___x_580_; lean_object* v_size_x27_581_; lean_object* v___x_582_; lean_object* v_buckets_x27_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v_size_x27_581_ = lean_nat_add(v_size_558_, v___x_580_);
lean_dec(v_size_558_);
lean_inc(v_bkt_575_);
v___x_582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_582_, 0, v_a_556_);
lean_ctor_set(v___x_582_, 1, v_b_557_);
lean_ctor_set(v___x_582_, 2, v_bkt_575_);
v_buckets_x27_583_ = lean_array_uset(v_buckets_559_, v___x_574_, v___x_582_);
v___x_584_ = lean_unsigned_to_nat(4u);
v___x_585_ = lean_nat_mul(v_size_x27_581_, v___x_584_);
v___x_586_ = lean_unsigned_to_nat(3u);
v___x_587_ = lean_nat_div(v___x_585_, v___x_586_);
lean_dec(v___x_585_);
v___x_588_ = lean_array_get_size(v_buckets_x27_583_);
v___x_589_ = lean_nat_dec_le(v___x_587_, v___x_588_);
lean_dec(v___x_587_);
if (v___x_589_ == 0)
{
lean_object* v_val_590_; lean_object* v___x_592_; 
v_val_590_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_554_, v_buckets_x27_583_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v_val_590_);
lean_ctor_set(v___x_578_, 0, v_size_x27_581_);
v___x_592_ = v___x_578_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v_size_x27_581_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_val_590_);
v___x_592_ = v_reuseFailAlloc_594_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; 
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v___x_576_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
return v___x_593_;
}
}
else
{
lean_object* v___x_596_; 
lean_dec_ref(v_x_554_);
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 1, v_buckets_x27_583_);
lean_ctor_set(v___x_578_, 0, v_size_x27_581_);
v___x_596_ = v___x_578_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v_size_x27_581_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v_buckets_x27_583_);
v___x_596_ = v_reuseFailAlloc_598_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; 
v___x_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_597_, 0, v___x_576_);
lean_ctor_set(v___x_597_, 1, v___x_596_);
return v___x_597_;
}
}
}
}
else
{
lean_object* v___x_602_; 
lean_dec(v_b_557_);
lean_dec(v_a_556_);
lean_dec_ref(v_x_554_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_576_);
lean_ctor_set(v___x_602_, 1, v_m_555_);
return v___x_602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg(lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_m_605_, lean_object* v_a_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_603_, v_x_604_, v_m_605_, v_a_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg___boxed(lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_m_610_, lean_object* v_a_611_){
_start:
{
lean_object* v_res_612_; 
v_res_612_ = l_Std_HashMap_get_x3f___redArg(v_x_608_, v_x_609_, v_m_610_, v_a_611_);
lean_dec_ref(v_m_610_);
return v_res_612_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f(lean_object* v_00_u03b1_613_, lean_object* v_00_u03b2_614_, lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_m_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_615_, v_x_616_, v_m_617_, v_a_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___boxed(lean_object* v_00_u03b1_620_, lean_object* v_00_u03b2_621_, lean_object* v_x_622_, lean_object* v_x_623_, lean_object* v_m_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l_Std_HashMap_get_x3f(v_00_u03b1_620_, v_00_u03b2_621_, v_x_622_, v_x_623_, v_m_624_, v_a_625_);
lean_dec_ref(v_m_624_);
return v_res_626_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_contains___redArg(lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_m_629_, lean_object* v_a_630_){
_start:
{
uint8_t v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_627_, v_x_628_, v_m_629_, v_a_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___redArg___boxed(lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_m_634_, lean_object* v_a_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Std_HashMap_contains___redArg(v_x_632_, v_x_633_, v_m_634_, v_a_635_);
lean_dec_ref(v_m_634_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_contains(lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_m_642_, lean_object* v_a_643_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_640_, v_x_641_, v_m_642_, v_a_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___boxed(lean_object* v_00_u03b1_645_, lean_object* v_00_u03b2_646_, lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_m_649_, lean_object* v_a_650_){
_start:
{
uint8_t v_res_651_; lean_object* v_r_652_; 
v_res_651_ = l_Std_HashMap_contains(v_00_u03b1_645_, v_00_u03b2_646_, v_x_647_, v_x_648_, v_m_649_, v_a_650_);
lean_dec_ref(v_m_649_);
v_r_652_ = lean_box(v_res_651_);
return v_r_652_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership(lean_object* v_00_u03b1_653_, lean_object* v_00_u03b2_654_, lean_object* v_inst_655_, lean_object* v_inst_656_){
_start:
{
lean_object* v___x_657_; 
v___x_657_ = lean_box(0);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___boxed(lean_object* v_00_u03b1_658_, lean_object* v_00_u03b2_659_, lean_object* v_inst_660_, lean_object* v_inst_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_HashMap_instMembership(v_00_u03b1_658_, v_00_u03b2_659_, v_inst_660_, v_inst_661_);
lean_dec_ref(v_inst_661_);
lean_dec_ref(v_inst_660_);
return v_res_662_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem___redArg(lean_object* v_inst_663_, lean_object* v_inst_664_, lean_object* v_m_665_, lean_object* v_a_666_){
_start:
{
uint8_t v___x_667_; 
v___x_667_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_663_, v_inst_664_, v_m_665_, v_a_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___redArg___boxed(lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_m_670_, lean_object* v_a_671_){
_start:
{
uint8_t v_res_672_; lean_object* v_r_673_; 
v_res_672_ = l_Std_HashMap_instDecidableMem___redArg(v_inst_668_, v_inst_669_, v_m_670_, v_a_671_);
lean_dec_ref(v_m_670_);
v_r_673_ = lean_box(v_res_672_);
return v_r_673_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b2_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_m_678_, lean_object* v_a_679_){
_start:
{
uint8_t v___x_680_; 
v___x_680_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_676_, v_inst_677_, v_m_678_, v_a_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_681_, lean_object* v_00_u03b2_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_m_685_, lean_object* v_a_686_){
_start:
{
uint8_t v_res_687_; lean_object* v_r_688_; 
v_res_687_ = l_Std_HashMap_instDecidableMem(v_00_u03b1_681_, v_00_u03b2_682_, v_inst_683_, v_inst_684_, v_m_685_, v_a_686_);
lean_dec_ref(v_m_685_);
v_r_688_ = lean_box(v_res_687_);
return v_r_688_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg(lean_object* v_x_689_, lean_object* v_x_690_, lean_object* v_m_691_, lean_object* v_a_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_689_, v_x_690_, v_m_691_, v_a_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg___boxed(lean_object* v_x_694_, lean_object* v_x_695_, lean_object* v_m_696_, lean_object* v_a_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_HashMap_get___redArg(v_x_694_, v_x_695_, v_m_696_, v_a_697_);
lean_dec_ref(v_m_696_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get(lean_object* v_00_u03b1_699_, lean_object* v_00_u03b2_700_, lean_object* v_x_701_, lean_object* v_x_702_, lean_object* v_m_703_, lean_object* v_a_704_, lean_object* v_h_705_){
_start:
{
lean_object* v___x_706_; 
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_701_, v_x_702_, v_m_703_, v_a_704_);
return v___x_706_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___boxed(lean_object* v_00_u03b1_707_, lean_object* v_00_u03b2_708_, lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_m_711_, lean_object* v_a_712_, lean_object* v_h_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Std_HashMap_get(v_00_u03b1_707_, v_00_u03b2_708_, v_x_709_, v_x_710_, v_m_711_, v_a_712_, v_h_713_);
lean_dec_ref(v_m_711_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg(lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_m_717_, lean_object* v_a_718_, lean_object* v_fallback_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_715_, v_x_716_, v_m_717_, v_a_718_, v_fallback_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg___boxed(lean_object* v_x_721_, lean_object* v_x_722_, lean_object* v_m_723_, lean_object* v_a_724_, lean_object* v_fallback_725_){
_start:
{
lean_object* v_res_726_; 
v_res_726_ = l_Std_HashMap_getD___redArg(v_x_721_, v_x_722_, v_m_723_, v_a_724_, v_fallback_725_);
lean_dec(v_fallback_725_);
lean_dec_ref(v_m_723_);
return v_res_726_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD(lean_object* v_00_u03b1_727_, lean_object* v_00_u03b2_728_, lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_m_731_, lean_object* v_a_732_, lean_object* v_fallback_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_729_, v_x_730_, v_m_731_, v_a_732_, v_fallback_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___boxed(lean_object* v_00_u03b1_735_, lean_object* v_00_u03b2_736_, lean_object* v_x_737_, lean_object* v_x_738_, lean_object* v_m_739_, lean_object* v_a_740_, lean_object* v_fallback_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Std_HashMap_getD(v_00_u03b1_735_, v_00_u03b2_736_, v_x_737_, v_x_738_, v_m_739_, v_a_740_, v_fallback_741_);
lean_dec(v_fallback_741_);
lean_dec_ref(v_m_739_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg(lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_inst_745_, lean_object* v_m_746_, lean_object* v_a_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_743_, v_x_744_, v_inst_745_, v_m_746_, v_a_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg___boxed(lean_object* v_x_749_, lean_object* v_x_750_, lean_object* v_inst_751_, lean_object* v_m_752_, lean_object* v_a_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Std_HashMap_get_x21___redArg(v_x_749_, v_x_750_, v_inst_751_, v_m_752_, v_a_753_);
lean_dec_ref(v_m_752_);
lean_dec(v_inst_751_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21(lean_object* v_00_u03b1_755_, lean_object* v_00_u03b2_756_, lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_inst_759_, lean_object* v_m_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_757_, v_x_758_, v_inst_759_, v_m_760_, v_a_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___boxed(lean_object* v_00_u03b1_763_, lean_object* v_00_u03b2_764_, lean_object* v_x_765_, lean_object* v_x_766_, lean_object* v_inst_767_, lean_object* v_m_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Std_HashMap_get_x21(v_00_u03b1_763_, v_00_u03b2_764_, v_x_765_, v_x_766_, v_inst_767_, v_m_768_, v_a_769_);
lean_dec_ref(v_m_768_);
lean_dec(v_inst_767_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_771_, lean_object* v_inst_772_, lean_object* v_m_773_, lean_object* v_a_774_, lean_object* v_h_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_771_, v_inst_772_, v_m_773_, v_a_774_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_m_779_, lean_object* v_a_780_, lean_object* v_h_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(v_inst_777_, v_inst_778_, v_m_779_, v_a_780_, v_h_781_);
lean_dec_ref(v_m_779_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_m_785_, lean_object* v_a_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_783_, v_inst_784_, v_m_785_, v_a_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_788_, lean_object* v_inst_789_, lean_object* v_m_790_, lean_object* v_a_791_){
_start:
{
lean_object* v_res_792_; 
v_res_792_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(v_inst_788_, v_inst_789_, v_m_790_, v_a_791_);
lean_dec_ref(v_m_790_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_m_796_, lean_object* v_a_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_793_, v_inst_794_, v_inst_795_, v_m_796_, v_a_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_799_, lean_object* v_inst_800_, lean_object* v_inst_801_, lean_object* v_m_802_, lean_object* v_a_803_){
_start:
{
lean_object* v_res_804_; 
v_res_804_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(v_inst_799_, v_inst_800_, v_inst_801_, v_m_802_, v_a_803_);
lean_dec_ref(v_m_802_);
lean_dec(v_inst_801_);
return v_res_804_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg(lean_object* v_inst_805_, lean_object* v_inst_806_){
_start:
{
lean_object* v___f_807_; lean_object* v___f_808_; lean_object* v___f_809_; lean_object* v___x_810_; 
lean_inc_ref_n(v_inst_806_, 2);
lean_inc_ref_n(v_inst_805_, 2);
v___f_807_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_807_, 0, v_inst_805_);
lean_closure_set(v___f_807_, 1, v_inst_806_);
v___f_808_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_808_, 0, v_inst_805_);
lean_closure_set(v___f_808_, 1, v_inst_806_);
v___f_809_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_809_, 0, v_inst_805_);
lean_closure_set(v___f_809_, 1, v_inst_806_);
v___x_810_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_810_, 0, v___f_807_);
lean_ctor_set(v___x_810_, 1, v___f_808_);
lean_ctor_set(v___x_810_, 2, v___f_809_);
return v___x_810_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem(lean_object* v_00_u03b1_811_, lean_object* v_00_u03b2_812_, lean_object* v_inst_813_, lean_object* v_inst_814_){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = l_Std_HashMap_instGetElem_x3fMem___redArg(v_inst_813_, v_inst_814_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg(lean_object* v_x_816_, lean_object* v_x_817_, lean_object* v_m_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_816_, v_x_817_, v_m_818_, v_a_819_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg___boxed(lean_object* v_x_821_, lean_object* v_x_822_, lean_object* v_m_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_HashMap_getKey_x3f___redArg(v_x_821_, v_x_822_, v_m_823_, v_a_824_);
lean_dec_ref(v_m_823_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f(lean_object* v_00_u03b1_826_, lean_object* v_00_u03b2_827_, lean_object* v_x_828_, lean_object* v_x_829_, lean_object* v_m_830_, lean_object* v_a_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_828_, v_x_829_, v_m_830_, v_a_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_m_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_HashMap_getKey_x3f(v_00_u03b1_833_, v_00_u03b2_834_, v_x_835_, v_x_836_, v_m_837_, v_a_838_);
lean_dec_ref(v_m_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg(lean_object* v_x_840_, lean_object* v_x_841_, lean_object* v_m_842_, lean_object* v_a_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_840_, v_x_841_, v_m_842_, v_a_843_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg___boxed(lean_object* v_x_845_, lean_object* v_x_846_, lean_object* v_m_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Std_HashMap_getKey___redArg(v_x_845_, v_x_846_, v_m_847_, v_a_848_);
lean_dec_ref(v_m_847_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_x_852_, lean_object* v_x_853_, lean_object* v_m_854_, lean_object* v_a_855_, lean_object* v_h_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_852_, v_x_853_, v_m_854_, v_a_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___boxed(lean_object* v_00_u03b1_858_, lean_object* v_00_u03b2_859_, lean_object* v_x_860_, lean_object* v_x_861_, lean_object* v_m_862_, lean_object* v_a_863_, lean_object* v_h_864_){
_start:
{
lean_object* v_res_865_; 
v_res_865_ = l_Std_HashMap_getKey(v_00_u03b1_858_, v_00_u03b2_859_, v_x_860_, v_x_861_, v_m_862_, v_a_863_, v_h_864_);
lean_dec_ref(v_m_862_);
return v_res_865_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg(lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_m_868_, lean_object* v_a_869_, lean_object* v_fallback_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_866_, v_x_867_, v_m_868_, v_a_869_, v_fallback_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg___boxed(lean_object* v_x_872_, lean_object* v_x_873_, lean_object* v_m_874_, lean_object* v_a_875_, lean_object* v_fallback_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l_Std_HashMap_getKeyD___redArg(v_x_872_, v_x_873_, v_m_874_, v_a_875_, v_fallback_876_);
lean_dec(v_fallback_876_);
lean_dec_ref(v_m_874_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD(lean_object* v_00_u03b1_878_, lean_object* v_00_u03b2_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_m_882_, lean_object* v_a_883_, lean_object* v_fallback_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_880_, v_x_881_, v_m_882_, v_a_883_, v_fallback_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___boxed(lean_object* v_00_u03b1_886_, lean_object* v_00_u03b2_887_, lean_object* v_x_888_, lean_object* v_x_889_, lean_object* v_m_890_, lean_object* v_a_891_, lean_object* v_fallback_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Std_HashMap_getKeyD(v_00_u03b1_886_, v_00_u03b2_887_, v_x_888_, v_x_889_, v_m_890_, v_a_891_, v_fallback_892_);
lean_dec(v_fallback_892_);
lean_dec_ref(v_m_890_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg(lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_inst_896_, lean_object* v_m_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_894_, v_x_895_, v_inst_896_, v_m_897_, v_a_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg___boxed(lean_object* v_x_900_, lean_object* v_x_901_, lean_object* v_inst_902_, lean_object* v_m_903_, lean_object* v_a_904_){
_start:
{
lean_object* v_res_905_; 
v_res_905_ = l_Std_HashMap_getKey_x21___redArg(v_x_900_, v_x_901_, v_inst_902_, v_m_903_, v_a_904_);
lean_dec_ref(v_m_903_);
lean_dec(v_inst_902_);
return v_res_905_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21(lean_object* v_00_u03b1_906_, lean_object* v_00_u03b2_907_, lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_inst_910_, lean_object* v_m_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_908_, v_x_909_, v_inst_910_, v_m_911_, v_a_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___boxed(lean_object* v_00_u03b1_914_, lean_object* v_00_u03b2_915_, lean_object* v_x_916_, lean_object* v_x_917_, lean_object* v_inst_918_, lean_object* v_m_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Std_HashMap_getKey_x21(v_00_u03b1_914_, v_00_u03b2_915_, v_x_916_, v_x_917_, v_inst_918_, v_m_919_, v_a_920_);
lean_dec_ref(v_m_919_);
lean_dec(v_inst_918_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase___redArg(lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_m_924_, lean_object* v_a_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_922_, v_x_923_, v_m_924_, v_a_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase(lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_m_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_929_, v_x_930_, v_m_931_, v_a_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg(lean_object* v_m_934_){
_start:
{
lean_object* v_size_935_; 
v_size_935_ = lean_ctor_get(v_m_934_, 0);
lean_inc(v_size_935_);
return v_size_935_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg___boxed(lean_object* v_m_936_){
_start:
{
lean_object* v_res_937_; 
v_res_937_ = l_Std_HashMap_size___redArg(v_m_936_);
lean_dec_ref(v_m_936_);
return v_res_937_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size(lean_object* v_00_u03b1_938_, lean_object* v_00_u03b2_939_, lean_object* v_x_940_, lean_object* v_x_941_, lean_object* v_m_942_){
_start:
{
lean_object* v_size_943_; 
v_size_943_ = lean_ctor_get(v_m_942_, 0);
lean_inc(v_size_943_);
return v_size_943_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___boxed(lean_object* v_00_u03b1_944_, lean_object* v_00_u03b2_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_m_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_HashMap_size(v_00_u03b1_944_, v_00_u03b2_945_, v_x_946_, v_x_947_, v_m_948_);
lean_dec_ref(v_m_948_);
lean_dec_ref(v_x_947_);
lean_dec_ref(v_x_946_);
return v_res_949_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty___redArg(lean_object* v_m_950_){
_start:
{
lean_object* v_size_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
v_size_951_ = lean_ctor_get(v_m_950_, 0);
v___x_952_ = lean_unsigned_to_nat(0u);
v___x_953_ = lean_nat_dec_eq(v_size_951_, v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___redArg___boxed(lean_object* v_m_954_){
_start:
{
uint8_t v_res_955_; lean_object* v_r_956_; 
v_res_955_ = l_Std_HashMap_isEmpty___redArg(v_m_954_);
lean_dec_ref(v_m_954_);
v_r_956_ = lean_box(v_res_955_);
return v_r_956_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty(lean_object* v_00_u03b1_957_, lean_object* v_00_u03b2_958_, lean_object* v_x_959_, lean_object* v_x_960_, lean_object* v_m_961_){
_start:
{
lean_object* v_size_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_size_962_ = lean_ctor_get(v_m_961_, 0);
v___x_963_ = lean_unsigned_to_nat(0u);
v___x_964_ = lean_nat_dec_eq(v_size_962_, v___x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___boxed(lean_object* v_00_u03b1_965_, lean_object* v_00_u03b2_966_, lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_m_969_){
_start:
{
uint8_t v_res_970_; lean_object* v_r_971_; 
v_res_970_ = l_Std_HashMap_isEmpty(v_00_u03b1_965_, v_00_u03b2_966_, v_x_967_, v_x_968_, v_m_969_);
lean_dec_ref(v_m_969_);
lean_dec_ref(v_x_968_);
lean_dec_ref(v_x_967_);
v_r_971_ = lean_box(v_res_970_);
return v_r_971_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0(lean_object* v_a_972_, lean_object* v_b_973_, lean_object* v_d_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_975_, 0, v_a_972_);
lean_ctor_set(v___x_975_, 1, v_d_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0___boxed(lean_object* v_a_976_, lean_object* v_b_977_, lean_object* v_d_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Std_HashMap_keys___redArg___lam__0(v_a_976_, v_b_977_, v_d_978_);
lean_dec(v_b_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__1(lean_object* v___x_980_, lean_object* v___f_981_, lean_object* v_l_982_, lean_object* v_acc_983_){
_start:
{
lean_object* v___x_984_; 
v___x_984_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_980_, v___f_981_, v_acc_983_, v_l_982_);
return v___x_984_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg(lean_object* v_m_1008_){
_start:
{
lean_object* v___x_1009_; lean_object* v_buckets_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
v___x_1009_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1010_ = lean_ctor_get(v_m_1008_, 1);
lean_inc_ref(v_buckets_1010_);
lean_dec_ref(v_m_1008_);
v___x_1011_ = lean_box(0);
v___x_1012_ = lean_array_get_size(v_buckets_1010_);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_nat_dec_lt(v___x_1013_, v___x_1012_);
if (v___x_1014_ == 0)
{
lean_dec_ref(v_buckets_1010_);
return v___x_1011_;
}
else
{
lean_object* v___f_1015_; size_t v___x_1016_; size_t v___x_1017_; lean_object* v___x_1018_; 
v___f_1015_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__11));
v___x_1016_ = lean_usize_of_nat(v___x_1012_);
v___x_1017_ = ((size_t)0ULL);
v___x_1018_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1009_, v___f_1015_, v_buckets_1010_, v___x_1016_, v___x_1017_, v___x_1011_);
return v___x_1018_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys(lean_object* v_00_u03b1_1019_, lean_object* v_00_u03b2_1020_, lean_object* v_x_1021_, lean_object* v_x_1022_, lean_object* v_m_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v_buckets_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1024_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1025_ = lean_ctor_get(v_m_1023_, 1);
lean_inc_ref(v_buckets_1025_);
lean_dec_ref(v_m_1023_);
v___x_1026_ = lean_box(0);
v___x_1027_ = lean_array_get_size(v_buckets_1025_);
v___x_1028_ = lean_unsigned_to_nat(0u);
v___x_1029_ = lean_nat_dec_lt(v___x_1028_, v___x_1027_);
if (v___x_1029_ == 0)
{
lean_dec_ref(v_buckets_1025_);
return v___x_1026_;
}
else
{
lean_object* v___f_1030_; size_t v___x_1031_; size_t v___x_1032_; lean_object* v___x_1033_; 
v___f_1030_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__11));
v___x_1031_ = lean_usize_of_nat(v___x_1027_);
v___x_1032_ = ((size_t)0ULL);
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1024_, v___f_1030_, v_buckets_1025_, v___x_1031_, v___x_1032_, v___x_1026_);
return v___x_1033_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___boxed(lean_object* v_00_u03b1_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_m_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Std_HashMap_keys(v_00_u03b1_1034_, v_00_u03b2_1035_, v_x_1036_, v_x_1037_, v_m_1038_);
lean_dec_ref(v_x_1037_);
lean_dec_ref(v_x_1036_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList___redArg(lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_l_1046_){
_start:
{
lean_object* v___f_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v___f_1047_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1048_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1049_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1047_, v_inst_1044_, v_inst_1045_, v___x_1048_, v_l_1046_);
return v___x_1049_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList(lean_object* v_00_u03b1_1050_, lean_object* v_00_u03b2_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_, lean_object* v_l_1054_){
_start:
{
lean_object* v___f_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___f_1055_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1056_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1057_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1055_, v_inst_1052_, v_inst_1053_, v___x_1056_, v_l_1054_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList___redArg(lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_l_1060_){
_start:
{
lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___f_1061_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1062_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1061_, v_inst_1058_, v_inst_1059_, v___x_1062_, v_l_1060_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList(lean_object* v_00_u03b1_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_, lean_object* v_l_1067_){
_start:
{
lean_object* v___f_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___f_1068_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1069_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1070_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1068_, v_inst_1065_, v_inst_1066_, v___x_1069_, v_l_1067_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray___redArg(lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___f_1078_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1079_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1078_, v_inst_1075_, v_inst_1076_, v___x_1079_, v_a_1077_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray(lean_object* v_00_u03b1_1081_, lean_object* v_00_u03b2_1082_, lean_object* v_inst_1083_, lean_object* v_inst_1084_, lean_object* v_a_1085_){
_start:
{
lean_object* v___f_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___f_1086_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1087_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1088_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1086_, v_inst_1083_, v_inst_1084_, v___x_1087_, v_a_1085_);
return v___x_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__0(lean_object* v_a_1089_, lean_object* v_b_1090_, lean_object* v_d_1091_){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1092_, 0, v_a_1089_);
lean_ctor_set(v___x_1092_, 1, v_b_1090_);
v___x_1093_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v_d_1091_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__1(lean_object* v___x_1094_, lean_object* v___f_1095_, lean_object* v_l_1096_, lean_object* v_acc_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1094_, v___f_1095_, v_acc_1097_, v_l_1096_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg(lean_object* v_m_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v_buckets_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; uint8_t v___x_1109_; 
v___x_1104_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1105_ = lean_ctor_get(v_m_1103_, 1);
lean_inc_ref(v_buckets_1105_);
lean_dec_ref(v_m_1103_);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_array_get_size(v_buckets_1105_);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_nat_dec_lt(v___x_1108_, v___x_1107_);
if (v___x_1109_ == 0)
{
lean_dec_ref(v_buckets_1105_);
return v___x_1106_;
}
else
{
lean_object* v___f_1110_; size_t v___x_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v___f_1110_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__1));
v___x_1111_ = lean_usize_of_nat(v___x_1107_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1104_, v___f_1110_, v_buckets_1105_, v___x_1111_, v___x_1112_, v___x_1106_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList(lean_object* v_00_u03b1_1114_, lean_object* v_00_u03b2_1115_, lean_object* v_x_1116_, lean_object* v_x_1117_, lean_object* v_m_1118_){
_start:
{
lean_object* v___x_1119_; lean_object* v_buckets_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1119_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1120_ = lean_ctor_get(v_m_1118_, 1);
lean_inc_ref(v_buckets_1120_);
lean_dec_ref(v_m_1118_);
v___x_1121_ = lean_box(0);
v___x_1122_ = lean_array_get_size(v_buckets_1120_);
v___x_1123_ = lean_unsigned_to_nat(0u);
v___x_1124_ = lean_nat_dec_lt(v___x_1123_, v___x_1122_);
if (v___x_1124_ == 0)
{
lean_dec_ref(v_buckets_1120_);
return v___x_1121_;
}
else
{
lean_object* v___f_1125_; size_t v___x_1126_; size_t v___x_1127_; lean_object* v___x_1128_; 
v___f_1125_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__1));
v___x_1126_ = lean_usize_of_nat(v___x_1122_);
v___x_1127_ = ((size_t)0ULL);
v___x_1128_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1119_, v___f_1125_, v_buckets_1120_, v___x_1126_, v___x_1127_, v___x_1121_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___boxed(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_x_1131_, lean_object* v_x_1132_, lean_object* v_m_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Std_HashMap_toList(v_00_u03b1_1129_, v_00_u03b2_1130_, v_x_1131_, v_x_1132_, v_m_1133_);
lean_dec_ref(v_x_1132_);
lean_dec_ref(v_x_1131_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg___lam__0(lean_object* v_inst_1135_, lean_object* v_f_1136_, lean_object* v_acc_1137_, lean_object* v_l_1138_){
_start:
{
lean_object* v___x_1139_; 
v___x_1139_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1135_, v_f_1136_, v_acc_1137_, v_l_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg(lean_object* v_inst_1140_, lean_object* v_f_1141_, lean_object* v_init_1142_, lean_object* v_b_1143_){
_start:
{
lean_object* v_toApplicative_1144_; lean_object* v_buckets_1145_; lean_object* v_toPure_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_toApplicative_1144_ = lean_ctor_get(v_inst_1140_, 0);
v_buckets_1145_ = lean_ctor_get(v_b_1143_, 1);
lean_inc_ref(v_buckets_1145_);
lean_dec_ref(v_b_1143_);
v_toPure_1146_ = lean_ctor_get(v_toApplicative_1144_, 1);
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = lean_array_get_size(v_buckets_1145_);
v___x_1149_ = lean_nat_dec_lt(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
lean_inc(v_toPure_1146_);
lean_dec_ref(v_buckets_1145_);
lean_dec(v_f_1141_);
lean_dec_ref(v_inst_1140_);
v___x_1150_ = lean_apply_2(v_toPure_1146_, lean_box(0), v_init_1142_);
return v___x_1150_;
}
else
{
lean_object* v___f_1151_; size_t v___x_1152_; size_t v___x_1153_; lean_object* v___x_1154_; 
lean_inc_ref(v_inst_1140_);
v___f_1151_ = lean_alloc_closure((void*)(l_Std_HashMap_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1151_, 0, v_inst_1140_);
lean_closure_set(v___f_1151_, 1, v_f_1141_);
v___x_1152_ = ((size_t)0ULL);
v___x_1153_ = lean_usize_of_nat(v___x_1148_);
v___x_1154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1140_, v___f_1151_, v_buckets_1145_, v___x_1152_, v___x_1153_, v_init_1142_);
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM(lean_object* v_00_u03b1_1155_, lean_object* v_00_u03b2_1156_, lean_object* v_x_1157_, lean_object* v_x_1158_, lean_object* v_m_1159_, lean_object* v_inst_1160_, lean_object* v_00_u03b3_1161_, lean_object* v_f_1162_, lean_object* v_init_1163_, lean_object* v_b_1164_){
_start:
{
lean_object* v_toApplicative_1165_; lean_object* v_buckets_1166_; lean_object* v_toPure_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; uint8_t v___x_1170_; 
v_toApplicative_1165_ = lean_ctor_get(v_inst_1160_, 0);
v_buckets_1166_ = lean_ctor_get(v_b_1164_, 1);
lean_inc_ref(v_buckets_1166_);
lean_dec_ref(v_b_1164_);
v_toPure_1167_ = lean_ctor_get(v_toApplicative_1165_, 1);
v___x_1168_ = lean_unsigned_to_nat(0u);
v___x_1169_ = lean_array_get_size(v_buckets_1166_);
v___x_1170_ = lean_nat_dec_lt(v___x_1168_, v___x_1169_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
lean_inc(v_toPure_1167_);
lean_dec_ref(v_buckets_1166_);
lean_dec(v_f_1162_);
lean_dec_ref(v_inst_1160_);
v___x_1171_ = lean_apply_2(v_toPure_1167_, lean_box(0), v_init_1163_);
return v___x_1171_;
}
else
{
lean_object* v___f_1172_; size_t v___x_1173_; size_t v___x_1174_; lean_object* v___x_1175_; 
lean_inc_ref(v_inst_1160_);
v___f_1172_ = lean_alloc_closure((void*)(l_Std_HashMap_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1172_, 0, v_inst_1160_);
lean_closure_set(v___f_1172_, 1, v_f_1162_);
v___x_1173_ = ((size_t)0ULL);
v___x_1174_ = lean_usize_of_nat(v___x_1169_);
v___x_1175_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1160_, v___f_1172_, v_buckets_1166_, v___x_1173_, v___x_1174_, v_init_1163_);
return v___x_1175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___boxed(lean_object* v_00_u03b1_1176_, lean_object* v_00_u03b2_1177_, lean_object* v_x_1178_, lean_object* v_x_1179_, lean_object* v_m_1180_, lean_object* v_inst_1181_, lean_object* v_00_u03b3_1182_, lean_object* v_f_1183_, lean_object* v_init_1184_, lean_object* v_b_1185_){
_start:
{
lean_object* v_res_1186_; 
v_res_1186_ = l_Std_HashMap_foldM(v_00_u03b1_1176_, v_00_u03b2_1177_, v_x_1178_, v_x_1179_, v_m_1180_, v_inst_1181_, v_00_u03b3_1182_, v_f_1183_, v_init_1184_, v_b_1185_);
lean_dec_ref(v_x_1179_);
lean_dec_ref(v_x_1178_);
return v_res_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__0(lean_object* v_f_1187_, lean_object* v_x1_1188_, lean_object* v_x2_1189_, lean_object* v_x3_1190_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_apply_3(v_f_1187_, v_x1_1188_, v_x2_1189_, v_x3_1190_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__1(lean_object* v___x_1192_, lean_object* v___f_1193_, lean_object* v_acc_1194_, lean_object* v_l_1195_){
_start:
{
lean_object* v___x_1196_; 
v___x_1196_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1192_, v___f_1193_, v_acc_1194_, v_l_1195_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg(lean_object* v_f_1197_, lean_object* v_init_1198_, lean_object* v_b_1199_){
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
lean_object* v___f_1205_; lean_object* v___f_1206_; size_t v___x_1207_; size_t v___x_1208_; lean_object* v___x_1209_; 
v___f_1205_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1205_, 0, v_f_1197_);
v___f_1206_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1206_, 0, v___x_1200_);
lean_closure_set(v___f_1206_, 1, v___f_1205_);
v___x_1207_ = ((size_t)0ULL);
v___x_1208_ = lean_usize_of_nat(v___x_1203_);
v___x_1209_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1200_, v___f_1206_, v_buckets_1201_, v___x_1207_, v___x_1208_, v_init_1198_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_x_1212_, lean_object* v_x_1213_, lean_object* v_00_u03b3_1214_, lean_object* v_f_1215_, lean_object* v_init_1216_, lean_object* v_b_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v_buckets_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; uint8_t v___x_1222_; 
v___x_1218_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1219_ = lean_ctor_get(v_b_1217_, 1);
lean_inc_ref(v_buckets_1219_);
lean_dec_ref(v_b_1217_);
v___x_1220_ = lean_unsigned_to_nat(0u);
v___x_1221_ = lean_array_get_size(v_buckets_1219_);
v___x_1222_ = lean_nat_dec_lt(v___x_1220_, v___x_1221_);
if (v___x_1222_ == 0)
{
lean_dec_ref(v_buckets_1219_);
lean_dec(v_f_1215_);
return v_init_1216_;
}
else
{
lean_object* v___f_1223_; lean_object* v___f_1224_; size_t v___x_1225_; size_t v___x_1226_; lean_object* v___x_1227_; 
v___f_1223_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1223_, 0, v_f_1215_);
v___f_1224_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1224_, 0, v___x_1218_);
lean_closure_set(v___f_1224_, 1, v___f_1223_);
v___x_1225_ = ((size_t)0ULL);
v___x_1226_ = lean_usize_of_nat(v___x_1221_);
v___x_1227_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1218_, v___f_1224_, v_buckets_1219_, v___x_1225_, v___x_1226_, v_init_1216_);
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v_00_u03b3_1232_, lean_object* v_f_1233_, lean_object* v_init_1234_, lean_object* v_b_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l_Std_HashMap_fold(v_00_u03b1_1228_, v_00_u03b2_1229_, v_x_1230_, v_x_1231_, v_00_u03b3_1232_, v_f_1233_, v_init_1234_, v_b_1235_);
lean_dec_ref(v_x_1231_);
lean_dec_ref(v_x_1230_);
return v_res_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__0(lean_object* v_f_1237_, lean_object* v_x_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = lean_apply_2(v_f_1237_, v___y_1239_, v___y_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__1(lean_object* v_inst_1242_, lean_object* v___f_1243_, lean_object* v_x_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_box(0);
v___x_1247_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1242_, v___f_1243_, v___x_1246_, v___y_1245_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg(lean_object* v_inst_1248_, lean_object* v_f_1249_, lean_object* v_b_1250_){
_start:
{
lean_object* v_toApplicative_1251_; lean_object* v_buckets_1252_; lean_object* v_toPure_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; uint8_t v___x_1257_; 
v_toApplicative_1251_ = lean_ctor_get(v_inst_1248_, 0);
v_buckets_1252_ = lean_ctor_get(v_b_1250_, 1);
lean_inc_ref(v_buckets_1252_);
lean_dec_ref(v_b_1250_);
v_toPure_1253_ = lean_ctor_get(v_toApplicative_1251_, 1);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_array_get_size(v_buckets_1252_);
v___x_1256_ = lean_box(0);
v___x_1257_ = lean_nat_dec_lt(v___x_1254_, v___x_1255_);
if (v___x_1257_ == 0)
{
lean_object* v___x_1258_; 
lean_inc(v_toPure_1253_);
lean_dec_ref(v_buckets_1252_);
lean_dec(v_f_1249_);
lean_dec_ref(v_inst_1248_);
v___x_1258_ = lean_apply_2(v_toPure_1253_, lean_box(0), v___x_1256_);
return v___x_1258_;
}
else
{
lean_object* v___f_1259_; lean_object* v___f_1260_; size_t v___x_1261_; size_t v___x_1262_; lean_object* v___x_1263_; 
v___f_1259_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1259_, 0, v_f_1249_);
lean_inc_ref(v_inst_1248_);
v___f_1260_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1260_, 0, v_inst_1248_);
lean_closure_set(v___f_1260_, 1, v___f_1259_);
v___x_1261_ = ((size_t)0ULL);
v___x_1262_ = lean_usize_of_nat(v___x_1255_);
v___x_1263_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1248_, v___f_1260_, v_buckets_1252_, v___x_1261_, v___x_1262_, v___x_1256_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM(lean_object* v_00_u03b1_1264_, lean_object* v_00_u03b2_1265_, lean_object* v_x_1266_, lean_object* v_x_1267_, lean_object* v_m_1268_, lean_object* v_inst_1269_, lean_object* v_f_1270_, lean_object* v_b_1271_){
_start:
{
lean_object* v_toApplicative_1272_; lean_object* v_buckets_1273_; lean_object* v_toPure_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; uint8_t v___x_1278_; 
v_toApplicative_1272_ = lean_ctor_get(v_inst_1269_, 0);
v_buckets_1273_ = lean_ctor_get(v_b_1271_, 1);
lean_inc_ref(v_buckets_1273_);
lean_dec_ref(v_b_1271_);
v_toPure_1274_ = lean_ctor_get(v_toApplicative_1272_, 1);
v___x_1275_ = lean_unsigned_to_nat(0u);
v___x_1276_ = lean_array_get_size(v_buckets_1273_);
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_nat_dec_lt(v___x_1275_, v___x_1276_);
if (v___x_1278_ == 0)
{
lean_object* v___x_1279_; 
lean_inc(v_toPure_1274_);
lean_dec_ref(v_buckets_1273_);
lean_dec(v_f_1270_);
lean_dec_ref(v_inst_1269_);
v___x_1279_ = lean_apply_2(v_toPure_1274_, lean_box(0), v___x_1277_);
return v___x_1279_;
}
else
{
lean_object* v___f_1280_; lean_object* v___f_1281_; size_t v___x_1282_; size_t v___x_1283_; lean_object* v___x_1284_; 
v___f_1280_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1280_, 0, v_f_1270_);
lean_inc_ref(v_inst_1269_);
v___f_1281_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1281_, 0, v_inst_1269_);
lean_closure_set(v___f_1281_, 1, v___f_1280_);
v___x_1282_ = ((size_t)0ULL);
v___x_1283_ = lean_usize_of_nat(v___x_1276_);
v___x_1284_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1269_, v___f_1281_, v_buckets_1273_, v___x_1282_, v___x_1283_, v___x_1277_);
return v___x_1284_;
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
lean_object* v_toApplicative_1344_; lean_object* v_buckets_1345_; lean_object* v_toPure_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; uint8_t v___x_1350_; 
v_toApplicative_1344_ = lean_ctor_get(v_inst_1341_, 0);
v_buckets_1345_ = lean_ctor_get(v_m_1342_, 1);
lean_inc_ref(v_buckets_1345_);
lean_dec_ref(v_m_1342_);
v_toPure_1346_ = lean_ctor_get(v_toApplicative_1344_, 1);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_array_get_size(v_buckets_1345_);
v___x_1349_ = lean_box(0);
v___x_1350_ = lean_nat_dec_lt(v___x_1347_, v___x_1348_);
if (v___x_1350_ == 0)
{
lean_object* v___x_1351_; 
lean_inc(v_toPure_1346_);
lean_dec_ref(v_buckets_1345_);
lean_dec(v_f_1343_);
lean_dec_ref(v_inst_1341_);
v___x_1351_ = lean_apply_2(v_toPure_1346_, lean_box(0), v___x_1349_);
return v___x_1351_;
}
else
{
lean_object* v___f_1352_; lean_object* v___f_1353_; size_t v___x_1354_; size_t v___x_1355_; lean_object* v___x_1356_; 
v___f_1352_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1352_, 0, v_f_1343_);
lean_inc_ref(v_inst_1341_);
v___f_1353_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1353_, 0, v_inst_1341_);
lean_closure_set(v___f_1353_, 1, v___f_1352_);
v___x_1354_ = ((size_t)0ULL);
v___x_1355_ = lean_usize_of_nat(v___x_1348_);
v___x_1356_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1341_, v___f_1353_, v_buckets_1345_, v___x_1354_, v___x_1355_, v___x_1349_);
return v___x_1356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg(lean_object* v_inst_1357_){
_start:
{
lean_object* v___f_1358_; 
v___f_1358_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1358_, 0, v_inst_1357_);
return v___f_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad(lean_object* v_00_u03b1_1359_, lean_object* v_00_u03b2_1360_, lean_object* v_inst_1361_, lean_object* v_inst_1362_, lean_object* v_m_1363_, lean_object* v_inst_1364_){
_start:
{
lean_object* v___f_1365_; 
v___f_1365_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1365_, 0, v_inst_1364_);
return v___f_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_1366_, lean_object* v_00_u03b2_1367_, lean_object* v_inst_1368_, lean_object* v_inst_1369_, lean_object* v_m_1370_, lean_object* v_inst_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Std_HashMap_instForMProdOfMonad(v_00_u03b1_1366_, v_00_u03b2_1367_, v_inst_1368_, v_inst_1369_, v_m_1370_, v_inst_1371_);
lean_dec_ref(v_inst_1369_);
lean_dec_ref(v_inst_1368_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1373_, lean_object* v_a_1374_, lean_object* v_b_1375_, lean_object* v_acc_1376_){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1377_, 0, v_a_1374_);
lean_ctor_set(v___x_1377_, 1, v_b_1375_);
v___x_1378_ = lean_apply_2(v_f_1373_, v___x_1377_, v_acc_1376_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1379_, lean_object* v___f_1380_, lean_object* v_a_1381_, lean_object* v_x_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1379_, v___f_1380_, v_a_1381_, v___y_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1385_, lean_object* v_00_u03b2_1386_, lean_object* v_m_1387_, lean_object* v_init_1388_, lean_object* v_f_1389_){
_start:
{
lean_object* v_buckets_1390_; lean_object* v___f_1391_; lean_object* v___f_1392_; size_t v_sz_1393_; size_t v___x_1394_; lean_object* v___x_1395_; 
v_buckets_1390_ = lean_ctor_get(v_m_1387_, 1);
lean_inc_ref(v_buckets_1390_);
lean_dec_ref(v_m_1387_);
v___f_1391_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1391_, 0, v_f_1389_);
lean_inc_ref(v_inst_1385_);
v___f_1392_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1392_, 0, v_inst_1385_);
lean_closure_set(v___f_1392_, 1, v___f_1391_);
v_sz_1393_ = lean_array_size(v_buckets_1390_);
v___x_1394_ = ((size_t)0ULL);
v___x_1395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1385_, v_buckets_1390_, v___f_1392_, v_sz_1393_, v___x_1394_, v_init_1388_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1396_){
_start:
{
lean_object* v___f_1397_; 
v___f_1397_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1397_, 0, v_inst_1396_);
return v___f_1397_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad(lean_object* v_00_u03b1_1398_, lean_object* v_00_u03b2_1399_, lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v_m_1402_, lean_object* v_inst_1403_){
_start:
{
lean_object* v___f_1404_; 
v___f_1404_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1404_, 0, v_inst_1403_);
return v___f_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1405_, lean_object* v_00_u03b2_1406_, lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_m_1409_, lean_object* v_inst_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Std_HashMap_instForInProdOfMonad(v_00_u03b1_1405_, v_00_u03b2_1406_, v_inst_1407_, v_inst_1408_, v_m_1409_, v_inst_1410_);
lean_dec_ref(v_inst_1408_);
lean_dec_ref(v_inst_1407_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___redArg(lean_object* v_f_1412_, lean_object* v_m_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1412_, v_m_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_, lean_object* v_f_1419_, lean_object* v_m_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1419_, v_m_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___boxed(lean_object* v_00_u03b1_1422_, lean_object* v_00_u03b2_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v_f_1426_, lean_object* v_m_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Std_HashMap_filter(v_00_u03b1_1422_, v_00_u03b2_1423_, v_x_1424_, v_x_1425_, v_f_1426_, v_m_1427_);
lean_dec_ref(v_x_1425_);
lean_dec_ref(v_x_1424_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify___redArg(lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v_m_1431_, lean_object* v_a_1432_, lean_object* v_f_1433_){
_start:
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1429_, v_x_1430_, v_m_1431_, v_a_1432_, v_f_1433_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify(lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_x_1437_, lean_object* v_x_1438_, lean_object* v_m_1439_, lean_object* v_a_1440_, lean_object* v_f_1441_){
_start:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1437_, v_x_1438_, v_m_1439_, v_a_1440_, v_f_1441_);
return v___x_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter___redArg(lean_object* v_x_1443_, lean_object* v_x_1444_, lean_object* v_m_1445_, lean_object* v_a_1446_, lean_object* v_f_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1443_, v_x_1444_, v_m_1445_, v_a_1446_, v_f_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter(lean_object* v_00_u03b1_1449_, lean_object* v_00_u03b2_1450_, lean_object* v_x_1451_, lean_object* v_x_1452_, lean_object* v_m_1453_, lean_object* v_a_1454_, lean_object* v_f_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1451_, v_x_1452_, v_m_1453_, v_a_1454_, v_f_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany___redArg(lean_object* v_x_1457_, lean_object* v_x_1458_, lean_object* v_inst_1459_, lean_object* v_m_1460_, lean_object* v_l_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_1459_, v_x_1457_, v_x_1458_, v_m_1460_, v_l_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany(lean_object* v_00_u03b1_1463_, lean_object* v_00_u03b2_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_00_u03c1_1467_, lean_object* v_inst_1468_, lean_object* v_m_1469_, lean_object* v_l_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_1468_, v_x_1465_, v_x_1466_, v_m_1469_, v_l_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit___redArg(lean_object* v_x_1472_, lean_object* v_x_1473_, lean_object* v_inst_1474_, lean_object* v_m_1475_, lean_object* v_l_1476_){
_start:
{
lean_object* v___x_1477_; 
v___x_1477_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1474_, v_x_1472_, v_x_1473_, v_m_1475_, v_l_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit(lean_object* v_00_u03b1_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_00_u03c1_1481_, lean_object* v_inst_1482_, lean_object* v_m_1483_, lean_object* v_l_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1482_, v_x_1479_, v_x_1480_, v_m_1483_, v_l_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__0(lean_object* v_x1_1486_, lean_object* v_x2_1487_, lean_object* v_x3_1488_){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1489_, 0, v_x2_1487_);
lean_ctor_set(v___x_1489_, 1, v_x3_1488_);
v___x_1490_ = lean_array_push(v_x1_1486_, v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__1(lean_object* v___x_1491_, lean_object* v___f_1492_, lean_object* v_acc_1493_, lean_object* v_l_1494_){
_start:
{
lean_object* v___x_1495_; 
v___x_1495_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1491_, v___f_1492_, v_acc_1493_, v_l_1494_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg(lean_object* v_m_1500_){
_start:
{
lean_object* v_size_1501_; lean_object* v_buckets_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; uint8_t v___x_1507_; 
v_size_1501_ = lean_ctor_get(v_m_1500_, 0);
lean_inc(v_size_1501_);
v_buckets_1502_ = lean_ctor_get(v_m_1500_, 1);
lean_inc_ref(v_buckets_1502_);
lean_dec_ref(v_m_1500_);
v___x_1503_ = lean_mk_empty_array_with_capacity(v_size_1501_);
lean_dec(v_size_1501_);
v___x_1504_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1505_ = lean_unsigned_to_nat(0u);
v___x_1506_ = lean_array_get_size(v_buckets_1502_);
v___x_1507_ = lean_nat_dec_lt(v___x_1505_, v___x_1506_);
if (v___x_1507_ == 0)
{
lean_dec_ref(v_buckets_1502_);
return v___x_1503_;
}
else
{
lean_object* v___f_1508_; size_t v___x_1509_; size_t v___x_1510_; lean_object* v___x_1511_; 
v___f_1508_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__1));
v___x_1509_ = ((size_t)0ULL);
v___x_1510_ = lean_usize_of_nat(v___x_1506_);
v___x_1511_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1504_, v___f_1508_, v_buckets_1502_, v___x_1509_, v___x_1510_, v___x_1503_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray(lean_object* v_00_u03b1_1512_, lean_object* v_00_u03b2_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_m_1516_){
_start:
{
lean_object* v_size_1517_; lean_object* v_buckets_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_size_1517_ = lean_ctor_get(v_m_1516_, 0);
lean_inc(v_size_1517_);
v_buckets_1518_ = lean_ctor_get(v_m_1516_, 1);
lean_inc_ref(v_buckets_1518_);
lean_dec_ref(v_m_1516_);
v___x_1519_ = lean_mk_empty_array_with_capacity(v_size_1517_);
lean_dec(v_size_1517_);
v___x_1520_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = lean_array_get_size(v_buckets_1518_);
v___x_1523_ = lean_nat_dec_lt(v___x_1521_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_dec_ref(v_buckets_1518_);
return v___x_1519_;
}
else
{
lean_object* v___f_1524_; size_t v___x_1525_; size_t v___x_1526_; lean_object* v___x_1527_; 
v___f_1524_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__1));
v___x_1525_ = ((size_t)0ULL);
v___x_1526_ = lean_usize_of_nat(v___x_1522_);
v___x_1527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1520_, v___f_1524_, v_buckets_1518_, v___x_1525_, v___x_1526_, v___x_1519_);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___boxed(lean_object* v_00_u03b1_1528_, lean_object* v_00_u03b2_1529_, lean_object* v_x_1530_, lean_object* v_x_1531_, lean_object* v_m_1532_){
_start:
{
lean_object* v_res_1533_; 
v_res_1533_ = l_Std_HashMap_toArray(v_00_u03b1_1528_, v_00_u03b2_1529_, v_x_1530_, v_x_1531_, v_m_1532_);
lean_dec_ref(v_x_1531_);
lean_dec_ref(v_x_1530_);
return v_res_1533_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0(lean_object* v_x1_1534_, lean_object* v_x2_1535_, lean_object* v_x3_1536_){
_start:
{
lean_object* v___x_1537_; 
v___x_1537_ = lean_array_push(v_x1_1534_, v_x2_1535_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1538_, lean_object* v_x2_1539_, lean_object* v_x3_1540_){
_start:
{
lean_object* v_res_1541_; 
v_res_1541_ = l_Std_HashMap_keysArray___redArg___lam__0(v_x1_1538_, v_x2_1539_, v_x3_1540_);
lean_dec(v_x3_1540_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__1(lean_object* v___x_1542_, lean_object* v___f_1543_, lean_object* v_acc_1544_, lean_object* v_l_1545_){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1542_, v___f_1543_, v_acc_1544_, v_l_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg(lean_object* v_m_1551_){
_start:
{
lean_object* v_size_1552_; lean_object* v_buckets_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_size_1552_ = lean_ctor_get(v_m_1551_, 0);
lean_inc(v_size_1552_);
v_buckets_1553_ = lean_ctor_get(v_m_1551_, 1);
lean_inc_ref(v_buckets_1553_);
lean_dec_ref(v_m_1551_);
v___x_1554_ = lean_mk_empty_array_with_capacity(v_size_1552_);
lean_dec(v_size_1552_);
v___x_1555_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = lean_array_get_size(v_buckets_1553_);
v___x_1558_ = lean_nat_dec_lt(v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_dec_ref(v_buckets_1553_);
return v___x_1554_;
}
else
{
lean_object* v___f_1559_; size_t v___x_1560_; size_t v___x_1561_; lean_object* v___x_1562_; 
v___f_1559_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__1));
v___x_1560_ = ((size_t)0ULL);
v___x_1561_ = lean_usize_of_nat(v___x_1557_);
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1555_, v___f_1559_, v_buckets_1553_, v___x_1560_, v___x_1561_, v___x_1554_);
return v___x_1562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray(lean_object* v_00_u03b1_1563_, lean_object* v_00_u03b2_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_, lean_object* v_m_1567_){
_start:
{
lean_object* v_size_1568_; lean_object* v_buckets_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; uint8_t v___x_1574_; 
v_size_1568_ = lean_ctor_get(v_m_1567_, 0);
lean_inc(v_size_1568_);
v_buckets_1569_ = lean_ctor_get(v_m_1567_, 1);
lean_inc_ref(v_buckets_1569_);
lean_dec_ref(v_m_1567_);
v___x_1570_ = lean_mk_empty_array_with_capacity(v_size_1568_);
lean_dec(v_size_1568_);
v___x_1571_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1572_ = lean_unsigned_to_nat(0u);
v___x_1573_ = lean_array_get_size(v_buckets_1569_);
v___x_1574_ = lean_nat_dec_lt(v___x_1572_, v___x_1573_);
if (v___x_1574_ == 0)
{
lean_dec_ref(v_buckets_1569_);
return v___x_1570_;
}
else
{
lean_object* v___f_1575_; size_t v___x_1576_; size_t v___x_1577_; lean_object* v___x_1578_; 
v___f_1575_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__1));
v___x_1576_ = ((size_t)0ULL);
v___x_1577_ = lean_usize_of_nat(v___x_1573_);
v___x_1578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1571_, v___f_1575_, v_buckets_1569_, v___x_1576_, v___x_1577_, v___x_1570_);
return v___x_1578_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___boxed(lean_object* v_00_u03b1_1579_, lean_object* v_00_u03b2_1580_, lean_object* v_x_1581_, lean_object* v_x_1582_, lean_object* v_m_1583_){
_start:
{
lean_object* v_res_1584_; 
v_res_1584_ = l_Std_HashMap_keysArray(v_00_u03b1_1579_, v_00_u03b2_1580_, v_x_1581_, v_x_1582_, v_m_1583_);
lean_dec_ref(v_x_1582_);
lean_dec_ref(v_x_1581_);
return v_res_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0(lean_object* v_p_1585_, lean_object* v___x_1586_, lean_object* v___x_1587_, lean_object* v_a_1588_, lean_object* v_b_1589_, lean_object* v_acc_1590_){
_start:
{
lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1591_ = lean_apply_2(v_p_1585_, v_a_1588_, v_b_1589_);
v___x_1592_ = lean_unbox(v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
lean_dec_ref(v___x_1587_);
v___x_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
v___x_1594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1593_);
lean_ctor_set(v___x_1594_, 1, v___x_1586_);
v___x_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1595_, 0, v___x_1594_);
return v___x_1595_;
}
else
{
lean_object* v___x_1596_; 
v___x_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1587_);
return v___x_1596_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0___boxed(lean_object* v_p_1597_, lean_object* v___x_1598_, lean_object* v___x_1599_, lean_object* v_a_1600_, lean_object* v_b_1601_, lean_object* v_acc_1602_){
_start:
{
lean_object* v_res_1603_; 
v_res_1603_ = l_Std_HashMap_all___redArg___lam__0(v_p_1597_, v___x_1598_, v___x_1599_, v_a_1600_, v_b_1601_, v_acc_1602_);
lean_dec_ref(v_acc_1602_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__1(lean_object* v___x_1604_, lean_object* v___f_1605_, lean_object* v_a_1606_, lean_object* v_x_1607_, lean_object* v___y_1608_){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1604_, v___f_1605_, v_a_1606_, v___y_1608_);
return v___x_1609_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_all___redArg(lean_object* v_m_1613_, lean_object* v_p_1614_){
_start:
{
lean_object* v___x_1615_; lean_object* v_buckets_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___f_1619_; lean_object* v___f_1620_; size_t v_sz_1621_; size_t v___x_1622_; lean_object* v___x_1623_; lean_object* v_fst_1624_; 
v___x_1615_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1616_ = lean_ctor_get(v_m_1613_, 1);
lean_inc_ref(v_buckets_1616_);
lean_dec_ref(v_m_1613_);
v___x_1617_ = lean_box(0);
v___x_1618_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1619_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1619_, 0, v_p_1614_);
lean_closure_set(v___f_1619_, 1, v___x_1617_);
lean_closure_set(v___f_1619_, 2, v___x_1618_);
v___f_1620_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1620_, 0, v___x_1615_);
lean_closure_set(v___f_1620_, 1, v___f_1619_);
v_sz_1621_ = lean_array_size(v_buckets_1616_);
v___x_1622_ = ((size_t)0ULL);
v___x_1623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1615_, v_buckets_1616_, v___f_1620_, v_sz_1621_, v___x_1622_, v___x_1618_);
v_fst_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_fst_1624_);
lean_dec(v___x_1623_);
if (lean_obj_tag(v_fst_1624_) == 0)
{
uint8_t v___x_1625_; 
v___x_1625_ = 1;
return v___x_1625_;
}
else
{
lean_object* v_val_1626_; uint8_t v___x_1627_; 
v_val_1626_ = lean_ctor_get(v_fst_1624_, 0);
lean_inc(v_val_1626_);
lean_dec_ref_known(v_fst_1624_, 1);
v___x_1627_ = lean_unbox(v_val_1626_);
lean_dec(v_val_1626_);
return v___x_1627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___boxed(lean_object* v_m_1628_, lean_object* v_p_1629_){
_start:
{
uint8_t v_res_1630_; lean_object* v_r_1631_; 
v_res_1630_ = l_Std_HashMap_all___redArg(v_m_1628_, v_p_1629_);
v_r_1631_ = lean_box(v_res_1630_);
return v_r_1631_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_all(lean_object* v_00_u03b1_1632_, lean_object* v_00_u03b2_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_, lean_object* v_m_1636_, lean_object* v_p_1637_){
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
lean_dec_ref_known(v_fst_1647_, 1);
v___x_1650_ = lean_unbox(v_val_1649_);
lean_dec(v_val_1649_);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___boxed(lean_object* v_00_u03b1_1651_, lean_object* v_00_u03b2_1652_, lean_object* v_x_1653_, lean_object* v_x_1654_, lean_object* v_m_1655_, lean_object* v_p_1656_){
_start:
{
uint8_t v_res_1657_; lean_object* v_r_1658_; 
v_res_1657_ = l_Std_HashMap_all(v_00_u03b1_1651_, v_00_u03b2_1652_, v_x_1653_, v_x_1654_, v_m_1655_, v_p_1656_);
lean_dec_ref(v_x_1654_);
lean_dec_ref(v_x_1653_);
v_r_1658_ = lean_box(v_res_1657_);
return v_r_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0(lean_object* v_p_1659_, lean_object* v___x_1660_, lean_object* v___x_1661_, lean_object* v_a_1662_, lean_object* v_b_1663_, lean_object* v_acc_1664_){
_start:
{
lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1665_ = lean_apply_2(v_p_1659_, v_a_1662_, v_b_1663_);
v___x_1666_ = lean_unbox(v___x_1665_);
if (v___x_1666_ == 0)
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1667_, 0, v___x_1660_);
return v___x_1667_;
}
else
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
lean_dec_ref(v___x_1660_);
v___x_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1668_, 0, v___x_1665_);
v___x_1669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1669_, 0, v___x_1668_);
lean_ctor_set(v___x_1669_, 1, v___x_1661_);
v___x_1670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1670_, 0, v___x_1669_);
return v___x_1670_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0___boxed(lean_object* v_p_1671_, lean_object* v___x_1672_, lean_object* v___x_1673_, lean_object* v_a_1674_, lean_object* v_b_1675_, lean_object* v_acc_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l_Std_HashMap_any___redArg___lam__0(v_p_1671_, v___x_1672_, v___x_1673_, v_a_1674_, v_b_1675_, v_acc_1676_);
lean_dec_ref(v_acc_1676_);
return v_res_1677_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_any___redArg(lean_object* v_m_1678_, lean_object* v_p_1679_){
_start:
{
lean_object* v___x_1680_; lean_object* v_buckets_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___f_1684_; lean_object* v___f_1685_; size_t v_sz_1686_; size_t v___x_1687_; lean_object* v___x_1688_; lean_object* v_fst_1689_; 
v___x_1680_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1681_ = lean_ctor_get(v_m_1678_, 1);
lean_inc_ref(v_buckets_1681_);
lean_dec_ref(v_m_1678_);
v___x_1682_ = lean_box(0);
v___x_1683_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1684_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1684_, 0, v_p_1679_);
lean_closure_set(v___f_1684_, 1, v___x_1683_);
lean_closure_set(v___f_1684_, 2, v___x_1682_);
v___f_1685_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1685_, 0, v___x_1680_);
lean_closure_set(v___f_1685_, 1, v___f_1684_);
v_sz_1686_ = lean_array_size(v_buckets_1681_);
v___x_1687_ = ((size_t)0ULL);
v___x_1688_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1680_, v_buckets_1681_, v___f_1685_, v_sz_1686_, v___x_1687_, v___x_1683_);
v_fst_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_fst_1689_);
lean_dec(v___x_1688_);
if (lean_obj_tag(v_fst_1689_) == 0)
{
uint8_t v___x_1690_; 
v___x_1690_ = 0;
return v___x_1690_;
}
else
{
lean_object* v_val_1691_; uint8_t v___x_1692_; 
v_val_1691_ = lean_ctor_get(v_fst_1689_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v_fst_1689_, 1);
v___x_1692_ = lean_unbox(v_val_1691_);
lean_dec(v_val_1691_);
return v___x_1692_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___boxed(lean_object* v_m_1693_, lean_object* v_p_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l_Std_HashMap_any___redArg(v_m_1693_, v_p_1694_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_any(lean_object* v_00_u03b1_1697_, lean_object* v_00_u03b2_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_m_1701_, lean_object* v_p_1702_){
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
lean_dec_ref_known(v_fst_1712_, 1);
v___x_1715_ = lean_unbox(v_val_1714_);
lean_dec(v_val_1714_);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___boxed(lean_object* v_00_u03b1_1716_, lean_object* v_00_u03b2_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_, lean_object* v_m_1720_, lean_object* v_p_1721_){
_start:
{
uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_res_1722_ = l_Std_HashMap_any(v_00_u03b1_1716_, v_00_u03b2_1717_, v_x_1718_, v_x_1719_, v_m_1720_, v_p_1721_);
lean_dec_ref(v_x_1719_);
lean_dec_ref(v_x_1718_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__0(lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_a_1726_, lean_object* v_b_1727_, lean_object* v_acc_1728_){
_start:
{
lean_object* v_r_1729_; lean_object* v___x_1730_; 
v_r_1729_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1724_, v_inst_1725_, v_acc_1728_, v_a_1726_, v_b_1727_);
v___x_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1730_, 0, v_r_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__1(lean_object* v___x_1731_, lean_object* v___f_1732_, lean_object* v_a_1733_, lean_object* v_x_1734_, lean_object* v___y_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1731_, v___f_1732_, v_a_1733_, v___y_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg(lean_object* v_inst_1739_, lean_object* v_inst_1740_, lean_object* v_m_u2081_1741_, lean_object* v_m_u2082_1742_){
_start:
{
lean_object* v___x_1743_; lean_object* v_size_1744_; lean_object* v_buckets_1745_; lean_object* v_size_1746_; uint8_t v___x_1747_; 
v___x_1743_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_size_1744_ = lean_ctor_get(v_m_u2081_1741_, 0);
v_buckets_1745_ = lean_ctor_get(v_m_u2081_1741_, 1);
v_size_1746_ = lean_ctor_get(v_m_u2082_1742_, 0);
v___x_1747_ = lean_nat_dec_le(v_size_1744_, v_size_1746_);
if (v___x_1747_ == 0)
{
lean_object* v___f_1748_; lean_object* v___x_1749_; 
v___f_1748_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1749_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1748_, v_inst_1739_, v_inst_1740_, v_m_u2081_1741_, v_m_u2082_1742_);
return v___x_1749_;
}
else
{
lean_object* v___f_1750_; lean_object* v___f_1751_; size_t v_sz_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
lean_inc_ref(v_buckets_1745_);
lean_dec_ref(v_m_u2081_1741_);
v___f_1750_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1750_, 0, v_inst_1739_);
lean_closure_set(v___f_1750_, 1, v_inst_1740_);
v___f_1751_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1751_, 0, v___x_1743_);
lean_closure_set(v___f_1751_, 1, v___f_1750_);
v_sz_1752_ = lean_array_size(v_buckets_1745_);
v___x_1753_ = ((size_t)0ULL);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1743_, v_buckets_1745_, v___f_1751_, v_sz_1752_, v___x_1753_, v_m_u2082_1742_);
return v___x_1754_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union(lean_object* v_00_u03b1_1755_, lean_object* v_00_u03b2_1756_, lean_object* v_inst_1757_, lean_object* v_inst_1758_, lean_object* v_m_u2081_1759_, lean_object* v_m_u2082_1760_){
_start:
{
lean_object* v___x_1761_; lean_object* v_size_1762_; lean_object* v_buckets_1763_; lean_object* v_size_1764_; uint8_t v___x_1765_; 
v___x_1761_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_size_1762_ = lean_ctor_get(v_m_u2081_1759_, 0);
v_buckets_1763_ = lean_ctor_get(v_m_u2081_1759_, 1);
v_size_1764_ = lean_ctor_get(v_m_u2082_1760_, 0);
v___x_1765_ = lean_nat_dec_le(v_size_1762_, v_size_1764_);
if (v___x_1765_ == 0)
{
lean_object* v___f_1766_; lean_object* v___x_1767_; 
v___f_1766_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1767_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1766_, v_inst_1757_, v_inst_1758_, v_m_u2081_1759_, v_m_u2082_1760_);
return v___x_1767_;
}
else
{
lean_object* v___f_1768_; lean_object* v___f_1769_; size_t v_sz_1770_; size_t v___x_1771_; lean_object* v___x_1772_; 
lean_inc_ref(v_buckets_1763_);
lean_dec_ref(v_m_u2081_1759_);
v___f_1768_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1768_, 0, v_inst_1757_);
lean_closure_set(v___f_1768_, 1, v_inst_1758_);
v___f_1769_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1769_, 0, v___x_1761_);
lean_closure_set(v___f_1769_, 1, v___f_1768_);
v_sz_1770_ = lean_array_size(v_buckets_1763_);
v___x_1771_ = ((size_t)0ULL);
v___x_1772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1761_, v_buckets_1763_, v___f_1769_, v_sz_1770_, v___x_1771_, v_m_u2082_1760_);
return v___x_1772_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion___redArg(lean_object* v_inst_1773_, lean_object* v_inst_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_alloc_closure((void*)(l_Std_HashMap_union), 6, 4);
lean_closure_set(v___x_1775_, 0, lean_box(0));
lean_closure_set(v___x_1775_, 1, lean_box(0));
lean_closure_set(v___x_1775_, 2, v_inst_1773_);
lean_closure_set(v___x_1775_, 3, v_inst_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion(lean_object* v_00_u03b1_1776_, lean_object* v_00_u03b2_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = lean_alloc_closure((void*)(l_Std_HashMap_union), 6, 4);
lean_closure_set(v___x_1780_, 0, lean_box(0));
lean_closure_set(v___x_1780_, 1, lean_box(0));
lean_closure_set(v___x_1780_, 2, v_inst_1778_);
lean_closure_set(v___x_1780_, 3, v_inst_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_inter___redArg(lean_object* v_inst_1781_, lean_object* v_inst_1782_, lean_object* v_m_u2081_1783_, lean_object* v_m_u2082_1784_){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1781_, v_inst_1782_, v_m_u2081_1783_, v_m_u2082_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_inter(lean_object* v_00_u03b1_1786_, lean_object* v_00_u03b2_1787_, lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_m_u2081_1790_, lean_object* v_m_u2082_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1788_, v_inst_1789_, v_m_u2081_1790_, v_m_u2082_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInter___redArg(lean_object* v_inst_1793_, lean_object* v_inst_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = lean_alloc_closure((void*)(l_Std_HashMap_inter), 6, 4);
lean_closure_set(v___x_1795_, 0, lean_box(0));
lean_closure_set(v___x_1795_, 1, lean_box(0));
lean_closure_set(v___x_1795_, 2, v_inst_1793_);
lean_closure_set(v___x_1795_, 3, v_inst_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInter(lean_object* v_00_u03b1_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_inst_1798_, lean_object* v_inst_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = lean_alloc_closure((void*)(l_Std_HashMap_inter), 6, 4);
lean_closure_set(v___x_1800_, 0, lean_box(0));
lean_closure_set(v___x_1800_, 1, lean_box(0));
lean_closure_set(v___x_1800_, 2, v_inst_1798_);
lean_closure_set(v___x_1800_, 3, v_inst_1799_);
return v___x_1800_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq___redArg(lean_object* v_x_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_m_u2081_1804_, lean_object* v_m_u2082_1805_){
_start:
{
uint8_t v___x_1806_; 
v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1802_, v_x_1801_, v_inst_1803_, v_m_u2081_1804_, v_m_u2082_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___redArg___boxed(lean_object* v_x_1807_, lean_object* v_inst_1808_, lean_object* v_inst_1809_, lean_object* v_m_u2081_1810_, lean_object* v_m_u2082_1811_){
_start:
{
uint8_t v_res_1812_; lean_object* v_r_1813_; 
v_res_1812_ = l_Std_HashMap_beq___redArg(v_x_1807_, v_inst_1808_, v_inst_1809_, v_m_u2081_1810_, v_m_u2082_1811_);
v_r_1813_ = lean_box(v_res_1812_);
return v_r_1813_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq(lean_object* v_00_u03b1_1814_, lean_object* v_x_1815_, lean_object* v_00_u03b2_1816_, lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_m_u2081_1819_, lean_object* v_m_u2082_1820_){
_start:
{
uint8_t v___x_1821_; 
v___x_1821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1817_, v_x_1815_, v_inst_1818_, v_m_u2081_1819_, v_m_u2082_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___boxed(lean_object* v_00_u03b1_1822_, lean_object* v_x_1823_, lean_object* v_00_u03b2_1824_, lean_object* v_inst_1825_, lean_object* v_inst_1826_, lean_object* v_m_u2081_1827_, lean_object* v_m_u2082_1828_){
_start:
{
uint8_t v_res_1829_; lean_object* v_r_1830_; 
v_res_1829_ = l_Std_HashMap_beq(v_00_u03b1_1822_, v_x_1823_, v_00_u03b2_1824_, v_inst_1825_, v_inst_1826_, v_m_u2081_1827_, v_m_u2082_1828_);
v_r_1830_ = lean_box(v_res_1829_);
return v_r_1830_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq___redArg(lean_object* v_x_1831_, lean_object* v_inst_1832_, lean_object* v_inst_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_1834_, 0, lean_box(0));
lean_closure_set(v___x_1834_, 1, v_x_1831_);
lean_closure_set(v___x_1834_, 2, lean_box(0));
lean_closure_set(v___x_1834_, 3, v_inst_1832_);
lean_closure_set(v___x_1834_, 4, v_inst_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq(lean_object* v_00_u03b1_1835_, lean_object* v_00_u03b2_1836_, lean_object* v_x_1837_, lean_object* v_inst_1838_, lean_object* v_inst_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_1840_, 0, lean_box(0));
lean_closure_set(v___x_1840_, 1, v_x_1837_);
lean_closure_set(v___x_1840_, 2, lean_box(0));
lean_closure_set(v___x_1840_, 3, v_inst_1838_);
lean_closure_set(v___x_1840_, 4, v_inst_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_diff___redArg___lam__0(lean_object* v_inst_1841_, lean_object* v_inst_1842_, lean_object* v_m_u2082_1843_, uint8_t v___x_1844_, lean_object* v_k_1845_, lean_object* v_x_1846_){
_start:
{
uint8_t v___x_1847_; 
v___x_1847_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1841_, v_inst_1842_, v_m_u2082_1843_, v_k_1845_);
if (v___x_1847_ == 0)
{
return v___x_1844_;
}
else
{
uint8_t v___x_1848_; 
v___x_1848_ = 0;
return v___x_1848_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg___lam__0___boxed(lean_object* v_inst_1849_, lean_object* v_inst_1850_, lean_object* v_m_u2082_1851_, lean_object* v___x_1852_, lean_object* v_k_1853_, lean_object* v_x_1854_){
_start:
{
uint8_t v___x_78__boxed_1855_; uint8_t v_res_1856_; lean_object* v_r_1857_; 
v___x_78__boxed_1855_ = lean_unbox(v___x_1852_);
v_res_1856_ = l_Std_HashMap_diff___redArg___lam__0(v_inst_1849_, v_inst_1850_, v_m_u2082_1851_, v___x_78__boxed_1855_, v_k_1853_, v_x_1854_);
lean_dec(v_x_1854_);
lean_dec_ref(v_m_u2082_1851_);
v_r_1857_ = lean_box(v_res_1856_);
return v_r_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg(lean_object* v_inst_1858_, lean_object* v_inst_1859_, lean_object* v_m_u2081_1860_, lean_object* v_m_u2082_1861_){
_start:
{
lean_object* v_size_1862_; lean_object* v_size_1863_; uint8_t v___x_1864_; 
v_size_1862_ = lean_ctor_get(v_m_u2081_1860_, 0);
v_size_1863_ = lean_ctor_get(v_m_u2082_1861_, 0);
v___x_1864_ = lean_nat_dec_le(v_size_1862_, v_size_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___f_1865_; lean_object* v___x_1866_; 
v___f_1865_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1866_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1865_, v_inst_1858_, v_inst_1859_, v_m_u2081_1860_, v_m_u2082_1861_);
return v___x_1866_;
}
else
{
lean_object* v___x_1867_; lean_object* v___f_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_box(v___x_1864_);
v___f_1868_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1868_, 0, v_inst_1858_);
lean_closure_set(v___f_1868_, 1, v_inst_1859_);
lean_closure_set(v___f_1868_, 2, v_m_u2082_1861_);
lean_closure_set(v___f_1868_, 3, v___x_1867_);
v___x_1869_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1868_, v_m_u2081_1860_);
return v___x_1869_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff(lean_object* v_00_u03b1_1870_, lean_object* v_00_u03b2_1871_, lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_m_u2081_1874_, lean_object* v_m_u2082_1875_){
_start:
{
lean_object* v_size_1876_; lean_object* v_size_1877_; uint8_t v___x_1878_; 
v_size_1876_ = lean_ctor_get(v_m_u2081_1874_, 0);
v_size_1877_ = lean_ctor_get(v_m_u2082_1875_, 0);
v___x_1878_ = lean_nat_dec_le(v_size_1876_, v_size_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___f_1879_; lean_object* v___x_1880_; 
v___f_1879_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1880_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1879_, v_inst_1872_, v_inst_1873_, v_m_u2081_1874_, v_m_u2082_1875_);
return v___x_1880_;
}
else
{
lean_object* v___x_1881_; lean_object* v___f_1882_; lean_object* v___x_1883_; 
v___x_1881_ = lean_box(v___x_1878_);
v___f_1882_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1882_, 0, v_inst_1872_);
lean_closure_set(v___f_1882_, 1, v_inst_1873_);
lean_closure_set(v___f_1882_, 2, v_m_u2082_1875_);
lean_closure_set(v___f_1882_, 3, v___x_1881_);
v___x_1883_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1882_, v_m_u2081_1874_);
return v___x_1883_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff___redArg(lean_object* v_inst_1884_, lean_object* v_inst_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_1886_, 0, lean_box(0));
lean_closure_set(v___x_1886_, 1, lean_box(0));
lean_closure_set(v___x_1886_, 2, v_inst_1884_);
lean_closure_set(v___x_1886_, 3, v_inst_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff(lean_object* v_00_u03b1_1887_, lean_object* v_00_u03b2_1888_, lean_object* v_inst_1889_, lean_object* v_inst_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_1891_, 0, lean_box(0));
lean_closure_set(v___x_1891_, 1, lean_box(0));
lean_closure_set(v___x_1891_, 2, v_inst_1889_);
lean_closure_set(v___x_1891_, 3, v_inst_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__0(lean_object* v_f_1892_, lean_object* v_x_1893_, lean_object* v_x_1894_, lean_object* v_x1_1895_, lean_object* v_x2_1896_, lean_object* v_x3_1897_){
_start:
{
lean_object* v_fst_1898_; lean_object* v_snd_1899_; lean_object* v___x_1901_; uint8_t v_isShared_1902_; uint8_t v_isSharedCheck_1913_; 
v_fst_1898_ = lean_ctor_get(v_x1_1895_, 0);
v_snd_1899_ = lean_ctor_get(v_x1_1895_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_x1_1895_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1901_ = v_x1_1895_;
v_isShared_1902_ = v_isSharedCheck_1913_;
goto v_resetjp_1900_;
}
else
{
lean_inc(v_snd_1899_);
lean_inc(v_fst_1898_);
lean_dec(v_x1_1895_);
v___x_1901_ = lean_box(0);
v_isShared_1902_ = v_isSharedCheck_1913_;
goto v_resetjp_1900_;
}
v_resetjp_1900_:
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
lean_inc(v_x3_1897_);
lean_inc(v_x2_1896_);
v___x_1903_ = lean_apply_2(v_f_1892_, v_x2_1896_, v_x3_1897_);
v___x_1904_ = lean_unbox(v___x_1903_);
if (v___x_1904_ == 0)
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1893_, v_x_1894_, v_snd_1899_, v_x2_1896_, v_x3_1897_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 1, v___x_1905_);
v___x_1907_ = v___x_1901_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_fst_1898_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
else
{
lean_object* v___x_1909_; lean_object* v___x_1911_; 
v___x_1909_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1893_, v_x_1894_, v_fst_1898_, v_x2_1896_, v_x3_1897_);
if (v_isShared_1902_ == 0)
{
lean_ctor_set(v___x_1901_, 0, v___x_1909_);
v___x_1911_ = v___x_1901_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1909_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_snd_1899_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__1(lean_object* v___x_1914_, lean_object* v___f_1915_, lean_object* v_acc_1916_, lean_object* v_l_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1914_, v___f_1915_, v_acc_1916_, v_l_1917_);
return v___x_1918_;
}
}
static lean_object* _init_l_Std_HashMap_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1919_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_1920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
lean_ctor_set(v___x_1920_, 1, v___x_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg(lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_f_1923_, lean_object* v_m_1924_){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v_buckets_1928_; lean_object* v___x_1929_; uint8_t v___x_1930_; 
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_1927_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1928_ = lean_ctor_get(v_m_1924_, 1);
lean_inc_ref(v_buckets_1928_);
lean_dec_ref(v_m_1924_);
v___x_1929_ = lean_array_get_size(v_buckets_1928_);
v___x_1930_ = lean_nat_dec_lt(v___x_1925_, v___x_1929_);
if (v___x_1930_ == 0)
{
lean_dec_ref(v_buckets_1928_);
lean_dec_ref(v_f_1923_);
lean_dec_ref(v_x_1922_);
lean_dec_ref(v_x_1921_);
return v___x_1926_;
}
else
{
lean_object* v___f_1931_; lean_object* v___f_1932_; size_t v___x_1933_; size_t v___x_1934_; lean_object* v___x_1935_; lean_object* v_fst_1936_; lean_object* v_snd_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
v___f_1931_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1931_, 0, v_f_1923_);
lean_closure_set(v___f_1931_, 1, v_x_1921_);
lean_closure_set(v___f_1931_, 2, v_x_1922_);
v___f_1932_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1932_, 0, v___x_1927_);
lean_closure_set(v___f_1932_, 1, v___f_1931_);
v___x_1933_ = ((size_t)0ULL);
v___x_1934_ = lean_usize_of_nat(v___x_1929_);
v___x_1935_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1927_, v___f_1932_, v_buckets_1928_, v___x_1933_, v___x_1934_, v___x_1926_);
v_fst_1936_ = lean_ctor_get(v___x_1935_, 0);
v_snd_1937_ = lean_ctor_get(v___x_1935_, 1);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1935_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_snd_1937_);
lean_inc(v_fst_1936_);
lean_dec(v___x_1935_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_fst_1936_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_snd_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition(lean_object* v_00_u03b1_1945_, lean_object* v_00_u03b2_1946_, lean_object* v_x_1947_, lean_object* v_x_1948_, lean_object* v_f_1949_, lean_object* v_m_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v_buckets_1954_; lean_object* v___x_1955_; uint8_t v___x_1956_; 
v___x_1951_ = lean_unsigned_to_nat(0u);
v___x_1952_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_1953_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1954_ = lean_ctor_get(v_m_1950_, 1);
lean_inc_ref(v_buckets_1954_);
lean_dec_ref(v_m_1950_);
v___x_1955_ = lean_array_get_size(v_buckets_1954_);
v___x_1956_ = lean_nat_dec_lt(v___x_1951_, v___x_1955_);
if (v___x_1956_ == 0)
{
lean_dec_ref(v_buckets_1954_);
lean_dec_ref(v_f_1949_);
lean_dec_ref(v_x_1948_);
lean_dec_ref(v_x_1947_);
return v___x_1952_;
}
else
{
lean_object* v___f_1957_; lean_object* v___f_1958_; size_t v___x_1959_; size_t v___x_1960_; lean_object* v___x_1961_; lean_object* v_fst_1962_; lean_object* v_snd_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
v___f_1957_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1957_, 0, v_f_1949_);
lean_closure_set(v___f_1957_, 1, v_x_1947_);
lean_closure_set(v___f_1957_, 2, v_x_1948_);
v___f_1958_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1958_, 0, v___x_1953_);
lean_closure_set(v___f_1958_, 1, v___f_1957_);
v___x_1959_ = ((size_t)0ULL);
v___x_1960_ = lean_usize_of_nat(v___x_1955_);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1953_, v___f_1958_, v_buckets_1954_, v___x_1959_, v___x_1960_, v___x_1952_);
v_fst_1962_ = lean_ctor_get(v___x_1961_, 0);
v_snd_1963_ = lean_ctor_get(v___x_1961_, 1);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1961_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1961_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_snd_1963_);
lean_inc(v_fst_1962_);
lean_dec(v___x_1961_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_fst_1962_);
lean_ctor_set(v_reuseFailAlloc_1969_, 1, v_snd_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0(lean_object* v_a_1971_, lean_object* v_b_1972_, lean_object* v_d_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_b_1972_);
lean_ctor_set(v___x_1974_, 1, v_d_1973_);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0___boxed(lean_object* v_a_1975_, lean_object* v_b_1976_, lean_object* v_d_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Std_HashMap_values___redArg___lam__0(v_a_1975_, v_b_1976_, v_d_1977_);
lean_dec(v_a_1975_);
return v_res_1978_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg(lean_object* v_m_1983_){
_start:
{
lean_object* v___x_1984_; lean_object* v_buckets_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; uint8_t v___x_1989_; 
v___x_1984_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1985_ = lean_ctor_get(v_m_1983_, 1);
lean_inc_ref(v_buckets_1985_);
lean_dec_ref(v_m_1983_);
v___x_1986_ = lean_box(0);
v___x_1987_ = lean_array_get_size(v_buckets_1985_);
v___x_1988_ = lean_unsigned_to_nat(0u);
v___x_1989_ = lean_nat_dec_lt(v___x_1988_, v___x_1987_);
if (v___x_1989_ == 0)
{
lean_dec_ref(v_buckets_1985_);
return v___x_1986_;
}
else
{
lean_object* v___f_1990_; size_t v___x_1991_; size_t v___x_1992_; lean_object* v___x_1993_; 
v___f_1990_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__1));
v___x_1991_ = lean_usize_of_nat(v___x_1987_);
v___x_1992_ = ((size_t)0ULL);
v___x_1993_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1984_, v___f_1990_, v_buckets_1985_, v___x_1991_, v___x_1992_, v___x_1986_);
return v___x_1993_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values(lean_object* v_00_u03b1_1994_, lean_object* v_00_u03b2_1995_, lean_object* v_x_1996_, lean_object* v_x_1997_, lean_object* v_m_1998_){
_start:
{
lean_object* v___x_1999_; lean_object* v_buckets_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; 
v___x_1999_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2000_ = lean_ctor_get(v_m_1998_, 1);
lean_inc_ref(v_buckets_2000_);
lean_dec_ref(v_m_1998_);
v___x_2001_ = lean_box(0);
v___x_2002_ = lean_array_get_size(v_buckets_2000_);
v___x_2003_ = lean_unsigned_to_nat(0u);
v___x_2004_ = lean_nat_dec_lt(v___x_2003_, v___x_2002_);
if (v___x_2004_ == 0)
{
lean_dec_ref(v_buckets_2000_);
return v___x_2001_;
}
else
{
lean_object* v___f_2005_; size_t v___x_2006_; size_t v___x_2007_; lean_object* v___x_2008_; 
v___f_2005_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__1));
v___x_2006_ = lean_usize_of_nat(v___x_2002_);
v___x_2007_ = ((size_t)0ULL);
v___x_2008_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1999_, v___f_2005_, v_buckets_2000_, v___x_2006_, v___x_2007_, v___x_2001_);
return v___x_2008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___boxed(lean_object* v_00_u03b1_2009_, lean_object* v_00_u03b2_2010_, lean_object* v_x_2011_, lean_object* v_x_2012_, lean_object* v_m_2013_){
_start:
{
lean_object* v_res_2014_; 
v_res_2014_ = l_Std_HashMap_values(v_00_u03b1_2009_, v_00_u03b2_2010_, v_x_2011_, v_x_2012_, v_m_2013_);
lean_dec_ref(v_x_2012_);
lean_dec_ref(v_x_2011_);
return v_res_2014_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0(lean_object* v_x1_2015_, lean_object* v_x2_2016_, lean_object* v_x3_2017_){
_start:
{
lean_object* v___x_2018_; 
v___x_2018_ = lean_array_push(v_x1_2015_, v_x3_2017_);
return v___x_2018_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2019_, lean_object* v_x2_2020_, lean_object* v_x3_2021_){
_start:
{
lean_object* v_res_2022_; 
v_res_2022_ = l_Std_HashMap_valuesArray___redArg___lam__0(v_x1_2019_, v_x2_2020_, v_x3_2021_);
lean_dec(v_x2_2020_);
return v_res_2022_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg(lean_object* v_m_2027_){
_start:
{
lean_object* v_size_2028_; lean_object* v_buckets_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v_size_2028_ = lean_ctor_get(v_m_2027_, 0);
lean_inc(v_size_2028_);
v_buckets_2029_ = lean_ctor_get(v_m_2027_, 1);
lean_inc_ref(v_buckets_2029_);
lean_dec_ref(v_m_2027_);
v___x_2030_ = lean_mk_empty_array_with_capacity(v_size_2028_);
lean_dec(v_size_2028_);
v___x_2031_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_2032_ = lean_unsigned_to_nat(0u);
v___x_2033_ = lean_array_get_size(v_buckets_2029_);
v___x_2034_ = lean_nat_dec_lt(v___x_2032_, v___x_2033_);
if (v___x_2034_ == 0)
{
lean_dec_ref(v_buckets_2029_);
return v___x_2030_;
}
else
{
lean_object* v___f_2035_; size_t v___x_2036_; size_t v___x_2037_; lean_object* v___x_2038_; 
v___f_2035_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__1));
v___x_2036_ = ((size_t)0ULL);
v___x_2037_ = lean_usize_of_nat(v___x_2033_);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2031_, v___f_2035_, v_buckets_2029_, v___x_2036_, v___x_2037_, v___x_2030_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray(lean_object* v_00_u03b1_2039_, lean_object* v_00_u03b2_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v_m_2043_){
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
v___x_2047_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
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
lean_object* v___f_2051_; size_t v___x_2052_; size_t v___x_2053_; lean_object* v___x_2054_; 
v___f_2051_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__1));
v___x_2052_ = ((size_t)0ULL);
v___x_2053_ = lean_usize_of_nat(v___x_2049_);
v___x_2054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2047_, v___f_2051_, v_buckets_2045_, v___x_2052_, v___x_2053_, v___x_2046_);
return v___x_2054_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___boxed(lean_object* v_00_u03b1_2055_, lean_object* v_00_u03b2_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_, lean_object* v_m_2059_){
_start:
{
lean_object* v_res_2060_; 
v_res_2060_ = l_Std_HashMap_valuesArray(v_00_u03b1_2055_, v_00_u03b2_2056_, v_x_2057_, v_x_2058_, v_m_2059_);
lean_dec_ref(v_x_2058_);
lean_dec_ref(v_x_2057_);
return v_res_2060_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray___redArg(lean_object* v_inst_2061_, lean_object* v_inst_2062_, lean_object* v_l_2063_){
_start:
{
lean_object* v___f_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___f_2064_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2065_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_2066_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2064_, v_inst_2061_, v_inst_2062_, v___x_2065_, v_l_2063_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray(lean_object* v_00_u03b1_2067_, lean_object* v_inst_2068_, lean_object* v_inst_2069_, lean_object* v_l_2070_){
_start:
{
lean_object* v___f_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___f_2071_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2072_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_2073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2071_, v_inst_2068_, v_inst_2069_, v___x_2072_, v_l_2070_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg(lean_object* v_m_2074_){
_start:
{
lean_object* v___x_2075_; 
v___x_2075_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2074_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg___boxed(lean_object* v_m_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l_Std_HashMap_Internal_numBuckets___redArg(v_m_2076_);
lean_dec_ref(v_m_2076_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets(lean_object* v_00_u03b1_2078_, lean_object* v_00_u03b2_2079_, lean_object* v_x_2080_, lean_object* v_x_2081_, lean_object* v_m_2082_){
_start:
{
lean_object* v___x_2083_; 
v___x_2083_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2082_);
return v___x_2083_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2084_, lean_object* v_00_u03b2_2085_, lean_object* v_x_2086_, lean_object* v_x_2087_, lean_object* v_m_2088_){
_start:
{
lean_object* v_res_2089_; 
v_res_2089_ = l_Std_HashMap_Internal_numBuckets(v_00_u03b1_2084_, v_00_u03b2_2085_, v_x_2086_, v_x_2087_, v_m_2088_);
lean_dec_ref(v_m_2088_);
lean_dec_ref(v_x_2087_);
lean_dec_ref(v_x_2086_);
return v_res_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2(lean_object* v___x_2093_, lean_object* v___f_2094_, lean_object* v_m_2095_, lean_object* v_prec_2096_){
_start:
{
lean_object* v___x_2097_; lean_object* v_buckets_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2118_; 
v___x_2097_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2098_ = lean_ctor_get(v_m_2095_, 1);
v_isSharedCheck_2118_ = !lean_is_exclusive(v_m_2095_);
if (v_isSharedCheck_2118_ == 0)
{
lean_object* v_unused_2119_; 
v_unused_2119_ = lean_ctor_get(v_m_2095_, 0);
lean_dec(v_unused_2119_);
v___x_2100_ = v_m_2095_;
v_isShared_2101_ = v_isSharedCheck_2118_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_buckets_2098_);
lean_dec(v_m_2095_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2118_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v___x_2102_; lean_object* v___y_2104_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2102_ = ((lean_object*)(l_Std_HashMap_instRepr___redArg___lam__2___closed__1));
v___x_2110_ = lean_box(0);
v___x_2111_ = lean_array_get_size(v_buckets_2098_);
v___x_2112_ = lean_unsigned_to_nat(0u);
v___x_2113_ = lean_nat_dec_lt(v___x_2112_, v___x_2111_);
if (v___x_2113_ == 0)
{
lean_dec_ref(v_buckets_2098_);
lean_dec_ref(v___f_2094_);
v___y_2104_ = v___x_2110_;
goto v___jp_2103_;
}
else
{
lean_object* v___f_2114_; size_t v___x_2115_; size_t v___x_2116_; lean_object* v___x_2117_; 
v___f_2114_ = lean_alloc_closure((void*)(l_Std_HashMap_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2114_, 0, v___x_2097_);
lean_closure_set(v___f_2114_, 1, v___f_2094_);
v___x_2115_ = lean_usize_of_nat(v___x_2111_);
v___x_2116_ = ((size_t)0ULL);
v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2097_, v___f_2114_, v_buckets_2098_, v___x_2115_, v___x_2116_, v___x_2110_);
v___y_2104_ = v___x_2117_;
goto v___jp_2103_;
}
v___jp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = l_List_repr___redArg(v___x_2093_, v___y_2104_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set_tag(v___x_2100_, 5);
lean_ctor_set(v___x_2100_, 1, v___x_2105_);
lean_ctor_set(v___x_2100_, 0, v___x_2102_);
v___x_2107_ = v___x_2100_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v___x_2102_);
lean_ctor_set(v_reuseFailAlloc_2109_, 1, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_Repr_addAppParen(v___x_2107_, v_prec_2096_);
return v___x_2108_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2___boxed(lean_object* v___x_2120_, lean_object* v___f_2121_, lean_object* v_m_2122_, lean_object* v_prec_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Std_HashMap_instRepr___redArg___lam__2(v___x_2120_, v___f_2121_, v_m_2122_, v_prec_2123_);
lean_dec(v_prec_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg(lean_object* v_inst_2125_, lean_object* v_inst_2126_){
_start:
{
lean_object* v___f_2127_; lean_object* v___f_2128_; lean_object* v___x_2129_; lean_object* v___f_2130_; 
v___f_2127_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__0));
v___f_2128_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2128_, 0, v_inst_2126_);
v___x_2129_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2129_, 0, lean_box(0));
lean_closure_set(v___x_2129_, 1, lean_box(0));
lean_closure_set(v___x_2129_, 2, v_inst_2125_);
lean_closure_set(v___x_2129_, 3, v___f_2128_);
v___f_2130_ = lean_alloc_closure((void*)(l_Std_HashMap_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2130_, 0, v___x_2129_);
lean_closure_set(v___f_2130_, 1, v___f_2127_);
return v___f_2130_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr(lean_object* v_00_u03b1_2131_, lean_object* v_00_u03b2_2132_, lean_object* v_inst_2133_, lean_object* v_inst_2134_, lean_object* v_inst_2135_, lean_object* v_inst_2136_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Std_HashMap_instRepr___redArg(v_inst_2135_, v_inst_2136_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___boxed(lean_object* v_00_u03b1_2138_, lean_object* v_00_u03b2_2139_, lean_object* v_inst_2140_, lean_object* v_inst_2141_, lean_object* v_inst_2142_, lean_object* v_inst_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Std_HashMap_instRepr(v_00_u03b1_2138_, v_00_u03b2_2139_, v_inst_2140_, v_inst_2141_, v_inst_2142_, v_inst_2143_);
lean_dec_ref(v_inst_2141_);
lean_dec_ref(v_inst_2140_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__0(lean_object* v_a_2147_, lean_object* v_x_2148_){
_start:
{
lean_object* v___y_2150_; 
if (lean_obj_tag(v_x_2148_) == 0)
{
lean_object* v___x_2153_; 
v___x_2153_ = ((lean_object*)(l_Array_groupByKey___redArg___lam__0___closed__0));
v___y_2150_ = v___x_2153_;
goto v___jp_2149_;
}
else
{
lean_object* v_val_2154_; 
v_val_2154_ = lean_ctor_get(v_x_2148_, 0);
lean_inc(v_val_2154_);
lean_dec_ref_known(v_x_2148_, 1);
v___y_2150_ = v_val_2154_;
goto v___jp_2149_;
}
v___jp_2149_:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2151_ = lean_array_push(v___y_2150_, v_a_2147_);
v___x_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__1(lean_object* v_key_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_, lean_object* v_a_2158_, lean_object* v_x_2159_, lean_object* v___y_2160_){
_start:
{
lean_object* v___f_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_inc(v_a_2158_);
v___f_2161_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2161_, 0, v_a_2158_);
v___x_2162_ = lean_apply_1(v_key_2155_, v_a_2158_);
v___x_2163_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_2156_, v_inst_2157_, v___y_2160_, v___x_2162_, v___f_2161_);
v___x_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
return v___x_2164_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg(lean_object* v_inst_2165_, lean_object* v_inst_2166_, lean_object* v_key_2167_, lean_object* v_xs_2168_){
_start:
{
lean_object* v___f_2169_; lean_object* v___x_2170_; lean_object* v_groups_2171_; size_t v_sz_2172_; size_t v___x_2173_; lean_object* v___x_2174_; 
v___f_2169_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__1), 6, 3);
lean_closure_set(v___f_2169_, 0, v_key_2167_);
lean_closure_set(v___f_2169_, 1, v_inst_2165_);
lean_closure_set(v___f_2169_, 2, v_inst_2166_);
v___x_2170_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_groups_2171_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v_sz_2172_ = lean_array_size(v_xs_2168_);
v___x_2173_ = ((size_t)0ULL);
v___x_2174_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2170_, v_xs_2168_, v___f_2169_, v_sz_2172_, v___x_2173_, v_groups_2171_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey(lean_object* v_00_u03b1_2175_, lean_object* v_00_u03b2_2176_, lean_object* v_inst_2177_, lean_object* v_inst_2178_, lean_object* v_key_2179_, lean_object* v_xs_2180_){
_start:
{
lean_object* v___x_2181_; 
v___x_2181_ = l_Array_groupByKey___redArg(v_inst_2177_, v_inst_2178_, v_key_2179_, v_xs_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__0(lean_object* v_x_2182_, lean_object* v_v_2183_){
_start:
{
lean_object* v___y_2185_; 
if (lean_obj_tag(v_v_2183_) == 0)
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_box(0);
v___y_2185_ = v___x_2188_;
goto v___jp_2184_;
}
else
{
lean_object* v_val_2189_; 
v_val_2189_ = lean_ctor_get(v_v_2183_, 0);
lean_inc(v_val_2189_);
lean_dec_ref_known(v_v_2183_, 1);
v___y_2185_ = v_val_2189_;
goto v___jp_2184_;
}
v___jp_2184_:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2186_, 0, v_x_2182_);
lean_ctor_set(v___x_2186_, 1, v___y_2185_);
v___x_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
return v___x_2187_;
}
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__1(lean_object* v_key_2190_, lean_object* v_inst_2191_, lean_object* v_inst_2192_, lean_object* v_x_2193_, lean_object* v_acc_2194_){
_start:
{
lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
lean_inc(v_x_2193_);
v___f_2195_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2195_, 0, v_x_2193_);
v___x_2196_ = lean_apply_1(v_key_2190_, v_x_2193_);
v___x_2197_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_2191_, v_inst_2192_, v_acc_2194_, v___x_2196_, v___f_2195_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg(lean_object* v_inst_2198_, lean_object* v_inst_2199_, lean_object* v_key_2200_, lean_object* v_xs_2201_){
_start:
{
lean_object* v___f_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___f_2202_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__1), 5, 3);
lean_closure_set(v___f_2202_, 0, v_key_2200_);
lean_closure_set(v___f_2202_, 1, v_inst_2198_);
lean_closure_set(v___f_2202_, 2, v_inst_2199_);
v___x_2203_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_2204_ = l_List_foldrTR___redArg(v___f_2202_, v___x_2203_, v_xs_2201_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey(lean_object* v_00_u03b1_2205_, lean_object* v_00_u03b2_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_key_2209_, lean_object* v_xs_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_List_groupByKey___redArg(v_inst_2207_, v_inst_2208_, v_key_2209_, v_xs_2210_);
return v___x_2211_;
}
}
lean_object* runtime_initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Impl(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
