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
static lean_once_cell_t l_Std_HashMap_instEmptyCollection___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_instEmptyCollection___redArg___closed__0;
static lean_once_cell_t l_Std_HashMap_instEmptyCollection___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_instEmptyCollection___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection___redArg();
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_HashMap_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_instEmptyCollection___closed__0;
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited___redArg();
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited___redArg___boxed(lean_object*);
static lean_once_cell_t l_Std_HashMap_instInhabited___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_instInhabited___closed__0;
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
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___redArg();
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___redArg___boxed(lean_object*);
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
static lean_object* _init_l_Std_HashMap_instEmptyCollection___redArg___closed__0(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; 
v___x_33_ = lean_box(0);
v___x_34_ = lean_unsigned_to_nat(16u);
v___x_35_ = lean_mk_array(v___x_34_, v___x_33_);
return v___x_35_;
}
}
static lean_object* _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_36_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__0, &l_Std_HashMap_instEmptyCollection___redArg___closed__0_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__0);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Std_HashMap_instEmptyCollection___redArg();
return v_res_42_;
}
}
static lean_object* _init_l_Std_HashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Std_HashMap_instEmptyCollection___redArg();
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_, lean_object* v_inst_46_, lean_object* v_inst_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__0, &l_Std_HashMap_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_instEmptyCollection___closed__0);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_49_, lean_object* v_00_u03b2_50_, lean_object* v_inst_51_, lean_object* v_inst_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_HashMap_instEmptyCollection(v_00_u03b1_49_, v_00_u03b2_50_, v_inst_51_, v_inst_52_);
lean_dec_ref(v_inst_52_);
lean_dec_ref(v_inst_51_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited___redArg___boxed(lean_object* v___dummy_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Std_HashMap_instInhabited___redArg();
return v_res_57_;
}
}
static lean_object* _init_l_Std_HashMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_HashMap_instInhabited___redArg();
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited(lean_object* v_00_u03b1_59_, lean_object* v_00_u03b2_60_, lean_object* v_inst_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_obj_once(&l_Std_HashMap_instInhabited___closed__0, &l_Std_HashMap_instInhabited___closed__0_once, _init_l_Std_HashMap_instInhabited___closed__0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited___boxed(lean_object* v_00_u03b1_64_, lean_object* v_00_u03b2_65_, lean_object* v_inst_66_, lean_object* v_inst_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_HashMap_instInhabited(v_00_u03b1_64_, v_00_u03b2_65_, v_inst_66_, v_inst_67_);
lean_dec_ref(v_inst_67_);
lean_dec_ref(v_inst_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear___redArg(lean_object* v_m_69_){
_start:
{
lean_object* v_size_70_; lean_object* v_buckets_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_79_; 
v_size_70_ = lean_ctor_get(v_m_69_, 0);
v_buckets_71_ = lean_ctor_get(v_m_69_, 1);
v_isSharedCheck_79_ = !lean_is_exclusive(v_m_69_);
if (v_isSharedCheck_79_ == 0)
{
v___x_73_ = v_m_69_;
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_buckets_71_);
lean_inc(v_size_70_);
lean_dec(v_m_69_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_79_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_75_ = lean_array_mark_linear(v_buckets_71_);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 1, v___x_75_);
v___x_77_ = v___x_73_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v_size_70_);
lean_ctor_set(v_reuseFailAlloc_78_, 1, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear(lean_object* v_00_u03b1_80_, lean_object* v_00_u03b2_81_, lean_object* v_x_82_, lean_object* v_x_83_, lean_object* v_m_84_){
_start:
{
lean_object* v_size_85_; lean_object* v_buckets_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_94_; 
v_size_85_ = lean_ctor_get(v_m_84_, 0);
v_buckets_86_ = lean_ctor_get(v_m_84_, 1);
v_isSharedCheck_94_ = !lean_is_exclusive(v_m_84_);
if (v_isSharedCheck_94_ == 0)
{
v___x_88_ = v_m_84_;
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_buckets_86_);
lean_inc(v_size_85_);
lean_dec(v_m_84_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_94_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_90_ = lean_array_mark_linear(v_buckets_86_);
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 1, v___x_90_);
v___x_92_ = v___x_88_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_93_; 
v_reuseFailAlloc_93_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_93_, 0, v_size_85_);
lean_ctor_set(v_reuseFailAlloc_93_, 1, v___x_90_);
v___x_92_ = v_reuseFailAlloc_93_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
return v___x_92_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear___boxed(lean_object* v_00_u03b1_95_, lean_object* v_00_u03b2_96_, lean_object* v_x_97_, lean_object* v_x_98_, lean_object* v_m_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Std_HashMap_markLinear(v_00_u03b1_95_, v_00_u03b2_96_, v_x_97_, v_x_98_, v_m_99_);
lean_dec_ref(v_x_98_);
lean_dec_ref(v_x_97_);
return v_res_100_;
}
}
static lean_object* _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5));
v___x_140_ = l_String_toRawSubstring_x27(v___x_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(lean_object* v_x_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
lean_inc(v_x_161_);
v___x_165_ = l_Lean_Syntax_isOfKind(v_x_161_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; 
lean_dec(v_x_161_);
v___x_166_ = lean_box(1);
v___x_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_163_);
return v___x_167_;
}
else
{
lean_object* v_quotContext_168_; lean_object* v_currMacroScope_169_; lean_object* v_ref_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_quotContext_168_ = lean_ctor_get(v_a_162_, 1);
v_currMacroScope_169_ = lean_ctor_get(v_a_162_, 2);
v_ref_170_ = lean_ctor_get(v_a_162_, 5);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = l_Lean_Syntax_getArg(v_x_161_, v___x_171_);
v___x_173_ = lean_unsigned_to_nat(2u);
v___x_174_ = l_Lean_Syntax_getArg(v_x_161_, v___x_173_);
lean_dec(v_x_161_);
v___x_175_ = 0;
v___x_176_ = l_Lean_SourceInfo_fromRef(v_ref_170_, v___x_175_);
v___x_177_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
v___x_178_ = lean_obj_once(&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6, &l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6_once, _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6);
v___x_179_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_169_);
lean_inc(v_quotContext_168_);
v___x_180_ = l_Lean_addMacroScope(v_quotContext_168_, v___x_179_, v_currMacroScope_169_);
v___x_181_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12));
lean_inc_n(v___x_176_, 2);
v___x_182_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_182_, 0, v___x_176_);
lean_ctor_set(v___x_182_, 1, v___x_178_);
lean_ctor_set(v___x_182_, 2, v___x_180_);
lean_ctor_set(v___x_182_, 3, v___x_181_);
v___x_183_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14));
v___x_184_ = l_Lean_Syntax_node2(v___x_176_, v___x_183_, v___x_172_, v___x_174_);
v___x_185_ = l_Lean_Syntax_node2(v___x_176_, v___x_177_, v___x_182_, v___x_184_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_a_163_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___boxed(lean_object* v_x_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(v_x_187_, v_a_188_, v_a_189_);
lean_dec_ref(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(lean_object* v_x_194_, lean_object* v_a_195_, lean_object* v_a_196_){
_start:
{
lean_object* v___x_197_; uint8_t v___x_198_; 
v___x_197_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
lean_inc(v_x_194_);
v___x_198_ = l_Lean_Syntax_isOfKind(v_x_194_, v___x_197_);
if (v___x_198_ == 0)
{
lean_object* v___x_199_; lean_object* v___x_200_; 
lean_dec(v_x_194_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
lean_ctor_set(v___x_200_, 1, v_a_196_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v___x_201_ = lean_unsigned_to_nat(0u);
v___x_202_ = l_Lean_Syntax_getArg(v_x_194_, v___x_201_);
v___x_203_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1));
lean_inc(v___x_202_);
v___x_204_ = l_Lean_Syntax_isOfKind(v___x_202_, v___x_203_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v___x_202_);
lean_dec(v_x_194_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v_a_196_);
return v___x_206_;
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = l_Lean_Syntax_getArg(v_x_194_, v___x_207_);
lean_dec(v_x_194_);
v___x_209_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_208_);
v___x_210_ = l_Lean_Syntax_matchesNull(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_dec(v___x_208_);
lean_dec(v___x_202_);
v___x_211_ = lean_box(0);
v___x_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v_a_196_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_ref_215_; uint8_t v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_213_ = l_Lean_Syntax_getArg(v___x_208_, v___x_201_);
v___x_214_ = l_Lean_Syntax_getArg(v___x_208_, v___x_207_);
lean_dec(v___x_208_);
v_ref_215_ = l_Lean_replaceRef(v___x_202_, v_a_195_);
lean_dec(v___x_202_);
v___x_216_ = 0;
v___x_217_ = l_Lean_SourceInfo_fromRef(v_ref_215_, v___x_216_);
lean_dec(v_ref_215_);
v___x_218_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
v___x_219_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__6));
lean_inc(v___x_217_);
v___x_220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_217_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = l_Lean_Syntax_node3(v___x_217_, v___x_218_, v___x_213_, v___x_220_, v___x_214_);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v_a_196_);
return v___x_222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___boxed(lean_object* v_x_223_, lean_object* v_a_224_, lean_object* v_a_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(v_x_223_, v_a_224_, v_a_225_);
lean_dec(v_a_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___redArg(lean_object* v_x_227_, lean_object* v_x_228_, lean_object* v_m_229_, lean_object* v_a_230_, lean_object* v_b_231_){
_start:
{
lean_object* v___x_232_; 
v___x_232_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_227_, v_x_228_, v_m_229_, v_a_230_, v_b_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_, lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_m_237_, lean_object* v_a_238_, lean_object* v_b_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_235_, v_x_236_, v_m_237_, v_a_238_, v_b_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg___lam__0(lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
lean_object* v_fst_244_; lean_object* v_snd_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v_fst_244_ = lean_ctor_get(v_x_243_, 0);
lean_inc(v_fst_244_);
v_snd_245_ = lean_ctor_get(v_x_243_, 1);
lean_inc(v_snd_245_);
lean_dec_ref(v_x_243_);
v___x_246_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_247_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_241_, v_x_242_, v___x_246_, v_fst_244_, v_snd_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg(lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
lean_object* v___f_250_; 
v___f_250_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_250_, 0, v_x_248_);
lean_closure_set(v___f_250_, 1, v_x_249_);
return v___f_250_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd(lean_object* v_00_u03b1_251_, lean_object* v_00_u03b2_252_, lean_object* v_x_253_, lean_object* v_x_254_){
_start:
{
lean_object* v___f_255_; 
v___f_255_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_255_, 0, v_x_253_);
lean_closure_set(v___f_255_, 1, v_x_254_);
return v___f_255_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg___lam__0(lean_object* v_x_256_, lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_s_259_){
_start:
{
lean_object* v_fst_260_; lean_object* v_snd_261_; lean_object* v___x_262_; 
v_fst_260_ = lean_ctor_get(v_x_258_, 0);
lean_inc(v_fst_260_);
v_snd_261_ = lean_ctor_get(v_x_258_, 1);
lean_inc(v_snd_261_);
lean_dec_ref(v_x_258_);
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_256_, v_x_257_, v_s_259_, v_fst_260_, v_snd_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg(lean_object* v_x_263_, lean_object* v_x_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_265_, 0, v_x_263_);
lean_closure_set(v___f_265_, 1, v_x_264_);
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
lean_object* v___f_270_; 
v___f_270_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_270_, 0, v_x_268_);
lean_closure_set(v___f_270_, 1, v_x_269_);
return v___f_270_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew___redArg(lean_object* v_x_271_, lean_object* v_x_272_, lean_object* v_m_273_, lean_object* v_a_274_, lean_object* v_b_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_271_, v_x_272_, v_m_273_, v_a_274_, v_b_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_x_279_, lean_object* v_x_280_, lean_object* v_m_281_, lean_object* v_a_282_, lean_object* v_b_283_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_279_, v_x_280_, v_m_281_, v_a_282_, v_b_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert___redArg(lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_m_287_, lean_object* v_a_288_, lean_object* v_b_289_){
_start:
{
lean_object* v_size_290_; lean_object* v_buckets_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_342_; 
v_size_290_ = lean_ctor_get(v_m_287_, 0);
v_buckets_291_ = lean_ctor_get(v_m_287_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_m_287_);
if (v_isSharedCheck_342_ == 0)
{
v___x_293_ = v_m_287_;
v_isShared_294_ = v_isSharedCheck_342_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_buckets_291_);
lean_inc(v_size_290_);
lean_dec(v_m_287_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_342_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_295_; lean_object* v___x_296_; uint64_t v___x_297_; uint64_t v___x_298_; uint64_t v___x_299_; uint64_t v___x_300_; uint64_t v_fold_301_; uint64_t v___x_302_; uint64_t v___x_303_; uint64_t v___x_304_; size_t v___x_305_; size_t v___x_306_; size_t v___x_307_; size_t v___x_308_; size_t v___x_309_; lean_object* v_bkt_310_; uint8_t v___x_311_; 
v___x_295_ = lean_array_get_size(v_buckets_291_);
lean_inc_ref(v_x_286_);
lean_inc_n(v_a_288_, 2);
v___x_296_ = lean_apply_1(v_x_286_, v_a_288_);
v___x_297_ = 32ULL;
v___x_298_ = lean_unbox_uint64(v___x_296_);
v___x_299_ = lean_uint64_shift_right(v___x_298_, v___x_297_);
v___x_300_ = lean_unbox_uint64(v___x_296_);
lean_dec_ref(v___x_296_);
v_fold_301_ = lean_uint64_xor(v___x_300_, v___x_299_);
v___x_302_ = 16ULL;
v___x_303_ = lean_uint64_shift_right(v_fold_301_, v___x_302_);
v___x_304_ = lean_uint64_xor(v_fold_301_, v___x_303_);
v___x_305_ = lean_uint64_to_usize(v___x_304_);
v___x_306_ = lean_usize_of_nat(v___x_295_);
v___x_307_ = ((size_t)1ULL);
v___x_308_ = lean_usize_sub(v___x_306_, v___x_307_);
v___x_309_ = lean_usize_land(v___x_305_, v___x_308_);
v_bkt_310_ = lean_array_uget_borrowed(v_buckets_291_, v___x_309_);
lean_inc(v_bkt_310_);
lean_inc_ref(v_x_285_);
v___x_311_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_285_, v_a_288_, v_bkt_310_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v_size_x27_313_; lean_object* v___x_314_; lean_object* v_buckets_x27_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
lean_dec_ref(v_x_285_);
v___x_312_ = lean_unsigned_to_nat(1u);
v_size_x27_313_ = lean_nat_add(v_size_290_, v___x_312_);
lean_dec(v_size_290_);
lean_inc(v_bkt_310_);
v___x_314_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_314_, 0, v_a_288_);
lean_ctor_set(v___x_314_, 1, v_b_289_);
lean_ctor_set(v___x_314_, 2, v_bkt_310_);
v_buckets_x27_315_ = lean_array_uset(v_buckets_291_, v___x_309_, v___x_314_);
v___x_316_ = lean_unsigned_to_nat(4u);
v___x_317_ = lean_nat_mul(v_size_x27_313_, v___x_316_);
v___x_318_ = lean_unsigned_to_nat(3u);
v___x_319_ = lean_nat_div(v___x_317_, v___x_318_);
lean_dec(v___x_317_);
v___x_320_ = lean_array_get_size(v_buckets_x27_315_);
v___x_321_ = lean_nat_dec_le(v___x_319_, v___x_320_);
lean_dec(v___x_319_);
if (v___x_321_ == 0)
{
lean_object* v_val_322_; lean_object* v___x_324_; 
v_val_322_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_286_, v_buckets_x27_315_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_val_322_);
lean_ctor_set(v___x_293_, 0, v_size_x27_313_);
v___x_324_ = v___x_293_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_size_x27_313_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_val_322_);
v___x_324_ = v_reuseFailAlloc_327_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_box(v___x_311_);
v___x_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v___x_324_);
return v___x_326_;
}
}
else
{
lean_object* v___x_329_; 
lean_dec_ref(v_x_286_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v_buckets_x27_315_);
lean_ctor_set(v___x_293_, 0, v_size_x27_313_);
v___x_329_ = v___x_293_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v_size_x27_313_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v_buckets_x27_315_);
v___x_329_ = v_reuseFailAlloc_332_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_330_ = lean_box(v___x_311_);
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v___x_329_);
return v___x_331_;
}
}
}
else
{
lean_object* v___x_333_; lean_object* v_buckets_x27_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_338_; 
lean_inc(v_bkt_310_);
lean_dec_ref(v_x_286_);
v___x_333_ = lean_box(0);
v_buckets_x27_334_ = lean_array_uset(v_buckets_291_, v___x_309_, v___x_333_);
v___x_335_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_285_, v_a_288_, v_b_289_, v_bkt_310_);
v___x_336_ = lean_array_uset(v_buckets_x27_334_, v___x_309_, v___x_335_);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_336_);
v___x_338_ = v___x_293_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v_size_290_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_336_);
v___x_338_ = v_reuseFailAlloc_341_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_box(v___x_311_);
v___x_340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_339_);
lean_ctor_set(v___x_340_, 1, v___x_338_);
return v___x_340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert(lean_object* v_00_u03b1_343_, lean_object* v_00_u03b2_344_, lean_object* v_x_345_, lean_object* v_x_346_, lean_object* v_m_347_, lean_object* v_a_348_, lean_object* v_b_349_){
_start:
{
lean_object* v_size_350_; lean_object* v_buckets_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_402_; 
v_size_350_ = lean_ctor_get(v_m_347_, 0);
v_buckets_351_ = lean_ctor_get(v_m_347_, 1);
v_isSharedCheck_402_ = !lean_is_exclusive(v_m_347_);
if (v_isSharedCheck_402_ == 0)
{
v___x_353_ = v_m_347_;
v_isShared_354_ = v_isSharedCheck_402_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_buckets_351_);
lean_inc(v_size_350_);
lean_dec(v_m_347_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_402_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; uint64_t v___x_357_; uint64_t v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; uint64_t v_fold_361_; uint64_t v___x_362_; uint64_t v___x_363_; uint64_t v___x_364_; size_t v___x_365_; size_t v___x_366_; size_t v___x_367_; size_t v___x_368_; size_t v___x_369_; lean_object* v_bkt_370_; uint8_t v___x_371_; 
v___x_355_ = lean_array_get_size(v_buckets_351_);
lean_inc_ref(v_x_346_);
lean_inc_n(v_a_348_, 2);
v___x_356_ = lean_apply_1(v_x_346_, v_a_348_);
v___x_357_ = 32ULL;
v___x_358_ = lean_unbox_uint64(v___x_356_);
v___x_359_ = lean_uint64_shift_right(v___x_358_, v___x_357_);
v___x_360_ = lean_unbox_uint64(v___x_356_);
lean_dec_ref(v___x_356_);
v_fold_361_ = lean_uint64_xor(v___x_360_, v___x_359_);
v___x_362_ = 16ULL;
v___x_363_ = lean_uint64_shift_right(v_fold_361_, v___x_362_);
v___x_364_ = lean_uint64_xor(v_fold_361_, v___x_363_);
v___x_365_ = lean_uint64_to_usize(v___x_364_);
v___x_366_ = lean_usize_of_nat(v___x_355_);
v___x_367_ = ((size_t)1ULL);
v___x_368_ = lean_usize_sub(v___x_366_, v___x_367_);
v___x_369_ = lean_usize_land(v___x_365_, v___x_368_);
v_bkt_370_ = lean_array_uget_borrowed(v_buckets_351_, v___x_369_);
lean_inc(v_bkt_370_);
lean_inc_ref(v_x_345_);
v___x_371_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_345_, v_a_348_, v_bkt_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v_size_x27_373_; lean_object* v___x_374_; lean_object* v_buckets_x27_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; uint8_t v___x_381_; 
lean_dec_ref(v_x_345_);
v___x_372_ = lean_unsigned_to_nat(1u);
v_size_x27_373_ = lean_nat_add(v_size_350_, v___x_372_);
lean_dec(v_size_350_);
lean_inc(v_bkt_370_);
v___x_374_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_374_, 0, v_a_348_);
lean_ctor_set(v___x_374_, 1, v_b_349_);
lean_ctor_set(v___x_374_, 2, v_bkt_370_);
v_buckets_x27_375_ = lean_array_uset(v_buckets_351_, v___x_369_, v___x_374_);
v___x_376_ = lean_unsigned_to_nat(4u);
v___x_377_ = lean_nat_mul(v_size_x27_373_, v___x_376_);
v___x_378_ = lean_unsigned_to_nat(3u);
v___x_379_ = lean_nat_div(v___x_377_, v___x_378_);
lean_dec(v___x_377_);
v___x_380_ = lean_array_get_size(v_buckets_x27_375_);
v___x_381_ = lean_nat_dec_le(v___x_379_, v___x_380_);
lean_dec(v___x_379_);
if (v___x_381_ == 0)
{
lean_object* v_val_382_; lean_object* v___x_384_; 
v_val_382_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_346_, v_buckets_x27_375_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v_val_382_);
lean_ctor_set(v___x_353_, 0, v_size_x27_373_);
v___x_384_ = v___x_353_;
goto v_reusejp_383_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_size_x27_373_);
lean_ctor_set(v_reuseFailAlloc_387_, 1, v_val_382_);
v___x_384_ = v_reuseFailAlloc_387_;
goto v_reusejp_383_;
}
v_reusejp_383_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_box(v___x_371_);
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_384_);
return v___x_386_;
}
}
else
{
lean_object* v___x_389_; 
lean_dec_ref(v_x_346_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v_buckets_x27_375_);
lean_ctor_set(v___x_353_, 0, v_size_x27_373_);
v___x_389_ = v___x_353_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_392_; 
v_reuseFailAlloc_392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_392_, 0, v_size_x27_373_);
lean_ctor_set(v_reuseFailAlloc_392_, 1, v_buckets_x27_375_);
v___x_389_ = v_reuseFailAlloc_392_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
v___x_390_ = lean_box(v___x_371_);
v___x_391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
lean_ctor_set(v___x_391_, 1, v___x_389_);
return v___x_391_;
}
}
}
else
{
lean_object* v___x_393_; lean_object* v_buckets_x27_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
lean_inc(v_bkt_370_);
lean_dec_ref(v_x_346_);
v___x_393_ = lean_box(0);
v_buckets_x27_394_ = lean_array_uset(v_buckets_351_, v___x_369_, v___x_393_);
v___x_395_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_345_, v_a_348_, v_b_349_, v_bkt_370_);
v___x_396_ = lean_array_uset(v_buckets_x27_394_, v___x_369_, v___x_395_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_396_);
v___x_398_ = v___x_353_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_size_350_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v___x_396_);
v___x_398_ = v_reuseFailAlloc_401_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_399_ = lean_box(v___x_371_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___x_398_);
return v___x_400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew___redArg(lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_m_405_, lean_object* v_a_406_, lean_object* v_b_407_){
_start:
{
lean_object* v_size_408_; lean_object* v_buckets_409_; lean_object* v___x_410_; lean_object* v___x_411_; uint64_t v___x_412_; uint64_t v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v_fold_416_; uint64_t v___x_417_; uint64_t v___x_418_; uint64_t v___x_419_; size_t v___x_420_; size_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; lean_object* v_bkt_425_; uint8_t v___x_426_; 
v_size_408_ = lean_ctor_get(v_m_405_, 0);
v_buckets_409_ = lean_ctor_get(v_m_405_, 1);
v___x_410_ = lean_array_get_size(v_buckets_409_);
lean_inc_ref(v_x_404_);
lean_inc_n(v_a_406_, 2);
v___x_411_ = lean_apply_1(v_x_404_, v_a_406_);
v___x_412_ = 32ULL;
v___x_413_ = lean_unbox_uint64(v___x_411_);
v___x_414_ = lean_uint64_shift_right(v___x_413_, v___x_412_);
v___x_415_ = lean_unbox_uint64(v___x_411_);
lean_dec_ref(v___x_411_);
v_fold_416_ = lean_uint64_xor(v___x_415_, v___x_414_);
v___x_417_ = 16ULL;
v___x_418_ = lean_uint64_shift_right(v_fold_416_, v___x_417_);
v___x_419_ = lean_uint64_xor(v_fold_416_, v___x_418_);
v___x_420_ = lean_uint64_to_usize(v___x_419_);
v___x_421_ = lean_usize_of_nat(v___x_410_);
v___x_422_ = ((size_t)1ULL);
v___x_423_ = lean_usize_sub(v___x_421_, v___x_422_);
v___x_424_ = lean_usize_land(v___x_420_, v___x_423_);
v_bkt_425_ = lean_array_uget_borrowed(v_buckets_409_, v___x_424_);
lean_inc(v_bkt_425_);
v___x_426_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_403_, v_a_406_, v_bkt_425_);
if (v___x_426_ == 0)
{
lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_451_; 
lean_inc_ref(v_buckets_409_);
lean_inc(v_size_408_);
v_isSharedCheck_451_ = !lean_is_exclusive(v_m_405_);
if (v_isSharedCheck_451_ == 0)
{
lean_object* v_unused_452_; lean_object* v_unused_453_; 
v_unused_452_ = lean_ctor_get(v_m_405_, 1);
lean_dec(v_unused_452_);
v_unused_453_ = lean_ctor_get(v_m_405_, 0);
lean_dec(v_unused_453_);
v___x_428_ = v_m_405_;
v_isShared_429_ = v_isSharedCheck_451_;
goto v_resetjp_427_;
}
else
{
lean_dec(v_m_405_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_451_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v___x_430_; lean_object* v_size_x27_431_; lean_object* v___x_432_; lean_object* v_buckets_x27_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v___x_430_ = lean_unsigned_to_nat(1u);
v_size_x27_431_ = lean_nat_add(v_size_408_, v___x_430_);
lean_dec(v_size_408_);
lean_inc(v_bkt_425_);
v___x_432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_432_, 0, v_a_406_);
lean_ctor_set(v___x_432_, 1, v_b_407_);
lean_ctor_set(v___x_432_, 2, v_bkt_425_);
v_buckets_x27_433_ = lean_array_uset(v_buckets_409_, v___x_424_, v___x_432_);
v___x_434_ = lean_unsigned_to_nat(4u);
v___x_435_ = lean_nat_mul(v_size_x27_431_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(3u);
v___x_437_ = lean_nat_div(v___x_435_, v___x_436_);
lean_dec(v___x_435_);
v___x_438_ = lean_array_get_size(v_buckets_x27_433_);
v___x_439_ = lean_nat_dec_le(v___x_437_, v___x_438_);
lean_dec(v___x_437_);
if (v___x_439_ == 0)
{
lean_object* v_val_440_; lean_object* v___x_442_; 
v_val_440_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_404_, v_buckets_x27_433_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v_val_440_);
lean_ctor_set(v___x_428_, 0, v_size_x27_431_);
v___x_442_ = v___x_428_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_445_; 
v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_445_, 0, v_size_x27_431_);
lean_ctor_set(v_reuseFailAlloc_445_, 1, v_val_440_);
v___x_442_ = v_reuseFailAlloc_445_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_443_ = lean_box(v___x_426_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_442_);
return v___x_444_;
}
}
else
{
lean_object* v___x_447_; 
lean_dec_ref(v_x_404_);
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v_buckets_x27_433_);
lean_ctor_set(v___x_428_, 0, v_size_x27_431_);
v___x_447_ = v___x_428_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_size_x27_431_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_buckets_x27_433_);
v___x_447_ = v_reuseFailAlloc_450_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = lean_box(v___x_426_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v___x_447_);
return v___x_449_;
}
}
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_b_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_x_404_);
v___x_454_ = lean_box(v___x_426_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v_m_405_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_456_, lean_object* v_00_u03b2_457_, lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v_m_460_, lean_object* v_a_461_, lean_object* v_b_462_){
_start:
{
lean_object* v_size_463_; lean_object* v_buckets_464_; lean_object* v___x_465_; lean_object* v___x_466_; uint64_t v___x_467_; uint64_t v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v_fold_471_; uint64_t v___x_472_; uint64_t v___x_473_; uint64_t v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; lean_object* v_bkt_480_; uint8_t v___x_481_; 
v_size_463_ = lean_ctor_get(v_m_460_, 0);
v_buckets_464_ = lean_ctor_get(v_m_460_, 1);
v___x_465_ = lean_array_get_size(v_buckets_464_);
lean_inc_ref(v_x_459_);
lean_inc_n(v_a_461_, 2);
v___x_466_ = lean_apply_1(v_x_459_, v_a_461_);
v___x_467_ = 32ULL;
v___x_468_ = lean_unbox_uint64(v___x_466_);
v___x_469_ = lean_uint64_shift_right(v___x_468_, v___x_467_);
v___x_470_ = lean_unbox_uint64(v___x_466_);
lean_dec_ref(v___x_466_);
v_fold_471_ = lean_uint64_xor(v___x_470_, v___x_469_);
v___x_472_ = 16ULL;
v___x_473_ = lean_uint64_shift_right(v_fold_471_, v___x_472_);
v___x_474_ = lean_uint64_xor(v_fold_471_, v___x_473_);
v___x_475_ = lean_uint64_to_usize(v___x_474_);
v___x_476_ = lean_usize_of_nat(v___x_465_);
v___x_477_ = ((size_t)1ULL);
v___x_478_ = lean_usize_sub(v___x_476_, v___x_477_);
v___x_479_ = lean_usize_land(v___x_475_, v___x_478_);
v_bkt_480_ = lean_array_uget_borrowed(v_buckets_464_, v___x_479_);
lean_inc(v_bkt_480_);
v___x_481_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_458_, v_a_461_, v_bkt_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_506_; 
lean_inc_ref(v_buckets_464_);
lean_inc(v_size_463_);
v_isSharedCheck_506_ = !lean_is_exclusive(v_m_460_);
if (v_isSharedCheck_506_ == 0)
{
lean_object* v_unused_507_; lean_object* v_unused_508_; 
v_unused_507_ = lean_ctor_get(v_m_460_, 1);
lean_dec(v_unused_507_);
v_unused_508_ = lean_ctor_get(v_m_460_, 0);
lean_dec(v_unused_508_);
v___x_483_ = v_m_460_;
v_isShared_484_ = v_isSharedCheck_506_;
goto v_resetjp_482_;
}
else
{
lean_dec(v_m_460_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_506_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v_size_x27_486_; lean_object* v___x_487_; lean_object* v_buckets_x27_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v_size_x27_486_ = lean_nat_add(v_size_463_, v___x_485_);
lean_dec(v_size_463_);
lean_inc(v_bkt_480_);
v___x_487_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_487_, 0, v_a_461_);
lean_ctor_set(v___x_487_, 1, v_b_462_);
lean_ctor_set(v___x_487_, 2, v_bkt_480_);
v_buckets_x27_488_ = lean_array_uset(v_buckets_464_, v___x_479_, v___x_487_);
v___x_489_ = lean_unsigned_to_nat(4u);
v___x_490_ = lean_nat_mul(v_size_x27_486_, v___x_489_);
v___x_491_ = lean_unsigned_to_nat(3u);
v___x_492_ = lean_nat_div(v___x_490_, v___x_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_array_get_size(v_buckets_x27_488_);
v___x_494_ = lean_nat_dec_le(v___x_492_, v___x_493_);
lean_dec(v___x_492_);
if (v___x_494_ == 0)
{
lean_object* v_val_495_; lean_object* v___x_497_; 
v_val_495_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_459_, v_buckets_x27_488_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v_val_495_);
lean_ctor_set(v___x_483_, 0, v_size_x27_486_);
v___x_497_ = v___x_483_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_size_x27_486_);
lean_ctor_set(v_reuseFailAlloc_500_, 1, v_val_495_);
v___x_497_ = v_reuseFailAlloc_500_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = lean_box(v___x_481_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_497_);
return v___x_499_;
}
}
else
{
lean_object* v___x_502_; 
lean_dec_ref(v_x_459_);
if (v_isShared_484_ == 0)
{
lean_ctor_set(v___x_483_, 1, v_buckets_x27_488_);
lean_ctor_set(v___x_483_, 0, v_size_x27_486_);
v___x_502_ = v___x_483_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v_size_x27_486_);
lean_ctor_set(v_reuseFailAlloc_505_, 1, v_buckets_x27_488_);
v___x_502_ = v_reuseFailAlloc_505_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_box(v___x_481_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v___x_502_);
return v___x_504_;
}
}
}
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v_b_462_);
lean_dec(v_a_461_);
lean_dec_ref(v_x_459_);
v___x_509_ = lean_box(v___x_481_);
v___x_510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v_m_460_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_511_, lean_object* v_x_512_, lean_object* v_m_513_, lean_object* v_a_514_, lean_object* v_b_515_){
_start:
{
lean_object* v_size_516_; lean_object* v_buckets_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint64_t v___x_520_; uint64_t v___x_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v_fold_524_; uint64_t v___x_525_; uint64_t v___x_526_; uint64_t v___x_527_; size_t v___x_528_; size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; lean_object* v_bkt_533_; lean_object* v___x_534_; 
v_size_516_ = lean_ctor_get(v_m_513_, 0);
v_buckets_517_ = lean_ctor_get(v_m_513_, 1);
v___x_518_ = lean_array_get_size(v_buckets_517_);
lean_inc_ref(v_x_512_);
lean_inc_n(v_a_514_, 2);
v___x_519_ = lean_apply_1(v_x_512_, v_a_514_);
v___x_520_ = 32ULL;
v___x_521_ = lean_unbox_uint64(v___x_519_);
v___x_522_ = lean_uint64_shift_right(v___x_521_, v___x_520_);
v___x_523_ = lean_unbox_uint64(v___x_519_);
lean_dec_ref(v___x_519_);
v_fold_524_ = lean_uint64_xor(v___x_523_, v___x_522_);
v___x_525_ = 16ULL;
v___x_526_ = lean_uint64_shift_right(v_fold_524_, v___x_525_);
v___x_527_ = lean_uint64_xor(v_fold_524_, v___x_526_);
v___x_528_ = lean_uint64_to_usize(v___x_527_);
v___x_529_ = lean_usize_of_nat(v___x_518_);
v___x_530_ = ((size_t)1ULL);
v___x_531_ = lean_usize_sub(v___x_529_, v___x_530_);
v___x_532_ = lean_usize_land(v___x_528_, v___x_531_);
v_bkt_533_ = lean_array_uget_borrowed(v_buckets_517_, v___x_532_);
lean_inc(v_bkt_533_);
v___x_534_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_511_, v_a_514_, v_bkt_533_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_object* v___x_536_; uint8_t v_isShared_537_; uint8_t v_isSharedCheck_557_; 
lean_inc_ref(v_buckets_517_);
lean_inc(v_size_516_);
v_isSharedCheck_557_ = !lean_is_exclusive(v_m_513_);
if (v_isSharedCheck_557_ == 0)
{
lean_object* v_unused_558_; lean_object* v_unused_559_; 
v_unused_558_ = lean_ctor_get(v_m_513_, 1);
lean_dec(v_unused_558_);
v_unused_559_ = lean_ctor_get(v_m_513_, 0);
lean_dec(v_unused_559_);
v___x_536_ = v_m_513_;
v_isShared_537_ = v_isSharedCheck_557_;
goto v_resetjp_535_;
}
else
{
lean_dec(v_m_513_);
v___x_536_ = lean_box(0);
v_isShared_537_ = v_isSharedCheck_557_;
goto v_resetjp_535_;
}
v_resetjp_535_:
{
lean_object* v___x_538_; lean_object* v_size_x27_539_; lean_object* v___x_540_; lean_object* v_buckets_x27_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; uint8_t v___x_547_; 
v___x_538_ = lean_unsigned_to_nat(1u);
v_size_x27_539_ = lean_nat_add(v_size_516_, v___x_538_);
lean_dec(v_size_516_);
lean_inc(v_bkt_533_);
v___x_540_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_540_, 0, v_a_514_);
lean_ctor_set(v___x_540_, 1, v_b_515_);
lean_ctor_set(v___x_540_, 2, v_bkt_533_);
v_buckets_x27_541_ = lean_array_uset(v_buckets_517_, v___x_532_, v___x_540_);
v___x_542_ = lean_unsigned_to_nat(4u);
v___x_543_ = lean_nat_mul(v_size_x27_539_, v___x_542_);
v___x_544_ = lean_unsigned_to_nat(3u);
v___x_545_ = lean_nat_div(v___x_543_, v___x_544_);
lean_dec(v___x_543_);
v___x_546_ = lean_array_get_size(v_buckets_x27_541_);
v___x_547_ = lean_nat_dec_le(v___x_545_, v___x_546_);
lean_dec(v___x_545_);
if (v___x_547_ == 0)
{
lean_object* v_val_548_; lean_object* v___x_550_; 
v_val_548_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_512_, v_buckets_x27_541_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v_val_548_);
lean_ctor_set(v___x_536_, 0, v_size_x27_539_);
v___x_550_ = v___x_536_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_size_x27_539_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_val_548_);
v___x_550_ = v_reuseFailAlloc_552_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_534_);
lean_ctor_set(v___x_551_, 1, v___x_550_);
return v___x_551_;
}
}
else
{
lean_object* v___x_554_; 
lean_dec_ref(v_x_512_);
if (v_isShared_537_ == 0)
{
lean_ctor_set(v___x_536_, 1, v_buckets_x27_541_);
lean_ctor_set(v___x_536_, 0, v_size_x27_539_);
v___x_554_ = v___x_536_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_size_x27_539_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_buckets_x27_541_);
v___x_554_ = v_reuseFailAlloc_556_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; 
v___x_555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_555_, 0, v___x_534_);
lean_ctor_set(v___x_555_, 1, v___x_554_);
return v___x_555_;
}
}
}
}
else
{
lean_object* v___x_560_; 
lean_dec(v_b_515_);
lean_dec(v_a_514_);
lean_dec_ref(v_x_512_);
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_534_);
lean_ctor_set(v___x_560_, 1, v_m_513_);
return v___x_560_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_561_, lean_object* v_00_u03b2_562_, lean_object* v_x_563_, lean_object* v_x_564_, lean_object* v_m_565_, lean_object* v_a_566_, lean_object* v_b_567_){
_start:
{
lean_object* v_size_568_; lean_object* v_buckets_569_; lean_object* v___x_570_; lean_object* v___x_571_; uint64_t v___x_572_; uint64_t v___x_573_; uint64_t v___x_574_; uint64_t v___x_575_; uint64_t v_fold_576_; uint64_t v___x_577_; uint64_t v___x_578_; uint64_t v___x_579_; size_t v___x_580_; size_t v___x_581_; size_t v___x_582_; size_t v___x_583_; size_t v___x_584_; lean_object* v_bkt_585_; lean_object* v___x_586_; 
v_size_568_ = lean_ctor_get(v_m_565_, 0);
v_buckets_569_ = lean_ctor_get(v_m_565_, 1);
v___x_570_ = lean_array_get_size(v_buckets_569_);
lean_inc_ref(v_x_564_);
lean_inc_n(v_a_566_, 2);
v___x_571_ = lean_apply_1(v_x_564_, v_a_566_);
v___x_572_ = 32ULL;
v___x_573_ = lean_unbox_uint64(v___x_571_);
v___x_574_ = lean_uint64_shift_right(v___x_573_, v___x_572_);
v___x_575_ = lean_unbox_uint64(v___x_571_);
lean_dec_ref(v___x_571_);
v_fold_576_ = lean_uint64_xor(v___x_575_, v___x_574_);
v___x_577_ = 16ULL;
v___x_578_ = lean_uint64_shift_right(v_fold_576_, v___x_577_);
v___x_579_ = lean_uint64_xor(v_fold_576_, v___x_578_);
v___x_580_ = lean_uint64_to_usize(v___x_579_);
v___x_581_ = lean_usize_of_nat(v___x_570_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_sub(v___x_581_, v___x_582_);
v___x_584_ = lean_usize_land(v___x_580_, v___x_583_);
v_bkt_585_ = lean_array_uget_borrowed(v_buckets_569_, v___x_584_);
lean_inc(v_bkt_585_);
v___x_586_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_563_, v_a_566_, v_bkt_585_);
if (lean_obj_tag(v___x_586_) == 0)
{
lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_609_; 
lean_inc_ref(v_buckets_569_);
lean_inc(v_size_568_);
v_isSharedCheck_609_ = !lean_is_exclusive(v_m_565_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; lean_object* v_unused_611_; 
v_unused_610_ = lean_ctor_get(v_m_565_, 1);
lean_dec(v_unused_610_);
v_unused_611_ = lean_ctor_get(v_m_565_, 0);
lean_dec(v_unused_611_);
v___x_588_ = v_m_565_;
v_isShared_589_ = v_isSharedCheck_609_;
goto v_resetjp_587_;
}
else
{
lean_dec(v_m_565_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_609_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; lean_object* v_size_x27_591_; lean_object* v___x_592_; lean_object* v_buckets_x27_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_590_ = lean_unsigned_to_nat(1u);
v_size_x27_591_ = lean_nat_add(v_size_568_, v___x_590_);
lean_dec(v_size_568_);
lean_inc(v_bkt_585_);
v___x_592_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_592_, 0, v_a_566_);
lean_ctor_set(v___x_592_, 1, v_b_567_);
lean_ctor_set(v___x_592_, 2, v_bkt_585_);
v_buckets_x27_593_ = lean_array_uset(v_buckets_569_, v___x_584_, v___x_592_);
v___x_594_ = lean_unsigned_to_nat(4u);
v___x_595_ = lean_nat_mul(v_size_x27_591_, v___x_594_);
v___x_596_ = lean_unsigned_to_nat(3u);
v___x_597_ = lean_nat_div(v___x_595_, v___x_596_);
lean_dec(v___x_595_);
v___x_598_ = lean_array_get_size(v_buckets_x27_593_);
v___x_599_ = lean_nat_dec_le(v___x_597_, v___x_598_);
lean_dec(v___x_597_);
if (v___x_599_ == 0)
{
lean_object* v_val_600_; lean_object* v___x_602_; 
v_val_600_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_564_, v_buckets_x27_593_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v_val_600_);
lean_ctor_set(v___x_588_, 0, v_size_x27_591_);
v___x_602_ = v___x_588_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_size_x27_591_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_val_600_);
v___x_602_ = v_reuseFailAlloc_604_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; 
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_586_);
lean_ctor_set(v___x_603_, 1, v___x_602_);
return v___x_603_;
}
}
else
{
lean_object* v___x_606_; 
lean_dec_ref(v_x_564_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v_buckets_x27_593_);
lean_ctor_set(v___x_588_, 0, v_size_x27_591_);
v___x_606_ = v___x_588_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_size_x27_591_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_buckets_x27_593_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; 
v___x_607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_586_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
return v___x_607_;
}
}
}
}
else
{
lean_object* v___x_612_; 
lean_dec(v_b_567_);
lean_dec(v_a_566_);
lean_dec_ref(v_x_564_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_586_);
lean_ctor_set(v___x_612_, 1, v_m_565_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg(lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_m_615_, lean_object* v_a_616_){
_start:
{
lean_object* v___x_617_; 
v___x_617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_613_, v_x_614_, v_m_615_, v_a_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg___boxed(lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_m_620_, lean_object* v_a_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l_Std_HashMap_get_x3f___redArg(v_x_618_, v_x_619_, v_m_620_, v_a_621_);
lean_dec_ref(v_m_620_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f(lean_object* v_00_u03b1_623_, lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_m_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_625_, v_x_626_, v_m_627_, v_a_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___boxed(lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_m_634_, lean_object* v_a_635_){
_start:
{
lean_object* v_res_636_; 
v_res_636_ = l_Std_HashMap_get_x3f(v_00_u03b1_630_, v_00_u03b2_631_, v_x_632_, v_x_633_, v_m_634_, v_a_635_);
lean_dec_ref(v_m_634_);
return v_res_636_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_contains___redArg(lean_object* v_x_637_, lean_object* v_x_638_, lean_object* v_m_639_, lean_object* v_a_640_){
_start:
{
uint8_t v___x_641_; 
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_637_, v_x_638_, v_m_639_, v_a_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___redArg___boxed(lean_object* v_x_642_, lean_object* v_x_643_, lean_object* v_m_644_, lean_object* v_a_645_){
_start:
{
uint8_t v_res_646_; lean_object* v_r_647_; 
v_res_646_ = l_Std_HashMap_contains___redArg(v_x_642_, v_x_643_, v_m_644_, v_a_645_);
lean_dec_ref(v_m_644_);
v_r_647_ = lean_box(v_res_646_);
return v_r_647_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_contains(lean_object* v_00_u03b1_648_, lean_object* v_00_u03b2_649_, lean_object* v_x_650_, lean_object* v_x_651_, lean_object* v_m_652_, lean_object* v_a_653_){
_start:
{
uint8_t v___x_654_; 
v___x_654_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_650_, v_x_651_, v_m_652_, v_a_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___boxed(lean_object* v_00_u03b1_655_, lean_object* v_00_u03b2_656_, lean_object* v_x_657_, lean_object* v_x_658_, lean_object* v_m_659_, lean_object* v_a_660_){
_start:
{
uint8_t v_res_661_; lean_object* v_r_662_; 
v_res_661_ = l_Std_HashMap_contains(v_00_u03b1_655_, v_00_u03b2_656_, v_x_657_, v_x_658_, v_m_659_, v_a_660_);
lean_dec_ref(v_m_659_);
v_r_662_ = lean_box(v_res_661_);
return v_r_662_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___redArg(){
_start:
{
lean_object* v___x_664_; 
v___x_664_ = lean_box(0);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___redArg___boxed(lean_object* v___dummy_665_){
_start:
{
lean_object* v_res_666_; 
v_res_666_ = l_Std_HashMap_instMembership___redArg();
return v_res_666_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership(lean_object* v_00_u03b1_667_, lean_object* v_00_u03b2_668_, lean_object* v_inst_669_, lean_object* v_inst_670_){
_start:
{
lean_object* v___x_671_; 
v___x_671_ = lean_box(0);
return v___x_671_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___boxed(lean_object* v_00_u03b1_672_, lean_object* v_00_u03b2_673_, lean_object* v_inst_674_, lean_object* v_inst_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Std_HashMap_instMembership(v_00_u03b1_672_, v_00_u03b2_673_, v_inst_674_, v_inst_675_);
lean_dec_ref(v_inst_675_);
lean_dec_ref(v_inst_674_);
return v_res_676_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem___redArg(lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_m_679_, lean_object* v_a_680_){
_start:
{
uint8_t v___x_681_; 
v___x_681_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_677_, v_inst_678_, v_m_679_, v_a_680_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___redArg___boxed(lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_m_684_, lean_object* v_a_685_){
_start:
{
uint8_t v_res_686_; lean_object* v_r_687_; 
v_res_686_ = l_Std_HashMap_instDecidableMem___redArg(v_inst_682_, v_inst_683_, v_m_684_, v_a_685_);
lean_dec_ref(v_m_684_);
v_r_687_ = lean_box(v_res_686_);
return v_r_687_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem(lean_object* v_00_u03b1_688_, lean_object* v_00_u03b2_689_, lean_object* v_inst_690_, lean_object* v_inst_691_, lean_object* v_m_692_, lean_object* v_a_693_){
_start:
{
uint8_t v___x_694_; 
v___x_694_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_690_, v_inst_691_, v_m_692_, v_a_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_695_, lean_object* v_00_u03b2_696_, lean_object* v_inst_697_, lean_object* v_inst_698_, lean_object* v_m_699_, lean_object* v_a_700_){
_start:
{
uint8_t v_res_701_; lean_object* v_r_702_; 
v_res_701_ = l_Std_HashMap_instDecidableMem(v_00_u03b1_695_, v_00_u03b2_696_, v_inst_697_, v_inst_698_, v_m_699_, v_a_700_);
lean_dec_ref(v_m_699_);
v_r_702_ = lean_box(v_res_701_);
return v_r_702_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg(lean_object* v_x_703_, lean_object* v_x_704_, lean_object* v_m_705_, lean_object* v_a_706_){
_start:
{
lean_object* v___x_707_; 
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_703_, v_x_704_, v_m_705_, v_a_706_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg___boxed(lean_object* v_x_708_, lean_object* v_x_709_, lean_object* v_m_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Std_HashMap_get___redArg(v_x_708_, v_x_709_, v_m_710_, v_a_711_);
lean_dec_ref(v_m_710_);
return v_res_712_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get(lean_object* v_00_u03b1_713_, lean_object* v_00_u03b2_714_, lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_m_717_, lean_object* v_a_718_, lean_object* v_h_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_715_, v_x_716_, v_m_717_, v_a_718_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___boxed(lean_object* v_00_u03b1_721_, lean_object* v_00_u03b2_722_, lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v_m_725_, lean_object* v_a_726_, lean_object* v_h_727_){
_start:
{
lean_object* v_res_728_; 
v_res_728_ = l_Std_HashMap_get(v_00_u03b1_721_, v_00_u03b2_722_, v_x_723_, v_x_724_, v_m_725_, v_a_726_, v_h_727_);
lean_dec_ref(v_m_725_);
return v_res_728_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg(lean_object* v_x_729_, lean_object* v_x_730_, lean_object* v_m_731_, lean_object* v_a_732_, lean_object* v_fallback_733_){
_start:
{
lean_object* v___x_734_; 
v___x_734_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_729_, v_x_730_, v_m_731_, v_a_732_, v_fallback_733_);
return v___x_734_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg___boxed(lean_object* v_x_735_, lean_object* v_x_736_, lean_object* v_m_737_, lean_object* v_a_738_, lean_object* v_fallback_739_){
_start:
{
lean_object* v_res_740_; 
v_res_740_ = l_Std_HashMap_getD___redArg(v_x_735_, v_x_736_, v_m_737_, v_a_738_, v_fallback_739_);
lean_dec(v_fallback_739_);
lean_dec_ref(v_m_737_);
return v_res_740_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD(lean_object* v_00_u03b1_741_, lean_object* v_00_u03b2_742_, lean_object* v_x_743_, lean_object* v_x_744_, lean_object* v_m_745_, lean_object* v_a_746_, lean_object* v_fallback_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_743_, v_x_744_, v_m_745_, v_a_746_, v_fallback_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___boxed(lean_object* v_00_u03b1_749_, lean_object* v_00_u03b2_750_, lean_object* v_x_751_, lean_object* v_x_752_, lean_object* v_m_753_, lean_object* v_a_754_, lean_object* v_fallback_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_HashMap_getD(v_00_u03b1_749_, v_00_u03b2_750_, v_x_751_, v_x_752_, v_m_753_, v_a_754_, v_fallback_755_);
lean_dec(v_fallback_755_);
lean_dec_ref(v_m_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg(lean_object* v_x_757_, lean_object* v_x_758_, lean_object* v_inst_759_, lean_object* v_m_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_757_, v_x_758_, v_inst_759_, v_m_760_, v_a_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg___boxed(lean_object* v_x_763_, lean_object* v_x_764_, lean_object* v_inst_765_, lean_object* v_m_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_HashMap_get_x21___redArg(v_x_763_, v_x_764_, v_inst_765_, v_m_766_, v_a_767_);
lean_dec_ref(v_m_766_);
lean_dec(v_inst_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21(lean_object* v_00_u03b1_769_, lean_object* v_00_u03b2_770_, lean_object* v_x_771_, lean_object* v_x_772_, lean_object* v_inst_773_, lean_object* v_m_774_, lean_object* v_a_775_){
_start:
{
lean_object* v___x_776_; 
v___x_776_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_771_, v_x_772_, v_inst_773_, v_m_774_, v_a_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___boxed(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_inst_781_, lean_object* v_m_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Std_HashMap_get_x21(v_00_u03b1_777_, v_00_u03b2_778_, v_x_779_, v_x_780_, v_inst_781_, v_m_782_, v_a_783_);
lean_dec_ref(v_m_782_);
lean_dec(v_inst_781_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_m_787_, lean_object* v_a_788_, lean_object* v_h_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_785_, v_inst_786_, v_m_787_, v_a_788_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_m_793_, lean_object* v_a_794_, lean_object* v_h_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(v_inst_791_, v_inst_792_, v_m_793_, v_a_794_, v_h_795_);
lean_dec_ref(v_m_793_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_m_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_797_, v_inst_798_, v_m_799_, v_a_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_m_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(v_inst_802_, v_inst_803_, v_m_804_, v_a_805_);
lean_dec_ref(v_m_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_m_810_, lean_object* v_a_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_807_, v_inst_808_, v_inst_809_, v_m_810_, v_a_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_m_816_, lean_object* v_a_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(v_inst_813_, v_inst_814_, v_inst_815_, v_m_816_, v_a_817_);
lean_dec_ref(v_m_816_);
lean_dec(v_inst_815_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg(lean_object* v_inst_819_, lean_object* v_inst_820_){
_start:
{
lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___x_824_; 
lean_inc_ref_n(v_inst_820_, 2);
lean_inc_ref_n(v_inst_819_, 2);
v___f_821_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_821_, 0, v_inst_819_);
lean_closure_set(v___f_821_, 1, v_inst_820_);
v___f_822_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_822_, 0, v_inst_819_);
lean_closure_set(v___f_822_, 1, v_inst_820_);
v___f_823_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_823_, 0, v_inst_819_);
lean_closure_set(v___f_823_, 1, v_inst_820_);
v___x_824_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_824_, 0, v___f_821_);
lean_ctor_set(v___x_824_, 1, v___f_822_);
lean_ctor_set(v___x_824_, 2, v___f_823_);
return v___x_824_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem(lean_object* v_00_u03b1_825_, lean_object* v_00_u03b2_826_, lean_object* v_inst_827_, lean_object* v_inst_828_){
_start:
{
lean_object* v___x_829_; 
v___x_829_ = l_Std_HashMap_instGetElem_x3fMem___redArg(v_inst_827_, v_inst_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg(lean_object* v_x_830_, lean_object* v_x_831_, lean_object* v_m_832_, lean_object* v_a_833_){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_830_, v_x_831_, v_m_832_, v_a_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg___boxed(lean_object* v_x_835_, lean_object* v_x_836_, lean_object* v_m_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_HashMap_getKey_x3f___redArg(v_x_835_, v_x_836_, v_m_837_, v_a_838_);
lean_dec_ref(v_m_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f(lean_object* v_00_u03b1_840_, lean_object* v_00_u03b2_841_, lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_m_844_, lean_object* v_a_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_842_, v_x_843_, v_m_844_, v_a_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_m_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Std_HashMap_getKey_x3f(v_00_u03b1_847_, v_00_u03b2_848_, v_x_849_, v_x_850_, v_m_851_, v_a_852_);
lean_dec_ref(v_m_851_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg(lean_object* v_x_854_, lean_object* v_x_855_, lean_object* v_m_856_, lean_object* v_a_857_){
_start:
{
lean_object* v___x_858_; 
v___x_858_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_854_, v_x_855_, v_m_856_, v_a_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg___boxed(lean_object* v_x_859_, lean_object* v_x_860_, lean_object* v_m_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Std_HashMap_getKey___redArg(v_x_859_, v_x_860_, v_m_861_, v_a_862_);
lean_dec_ref(v_m_861_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey(lean_object* v_00_u03b1_864_, lean_object* v_00_u03b2_865_, lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_m_868_, lean_object* v_a_869_, lean_object* v_h_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_866_, v_x_867_, v_m_868_, v_a_869_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___boxed(lean_object* v_00_u03b1_872_, lean_object* v_00_u03b2_873_, lean_object* v_x_874_, lean_object* v_x_875_, lean_object* v_m_876_, lean_object* v_a_877_, lean_object* v_h_878_){
_start:
{
lean_object* v_res_879_; 
v_res_879_ = l_Std_HashMap_getKey(v_00_u03b1_872_, v_00_u03b2_873_, v_x_874_, v_x_875_, v_m_876_, v_a_877_, v_h_878_);
lean_dec_ref(v_m_876_);
return v_res_879_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg(lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_m_882_, lean_object* v_a_883_, lean_object* v_fallback_884_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_880_, v_x_881_, v_m_882_, v_a_883_, v_fallback_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg___boxed(lean_object* v_x_886_, lean_object* v_x_887_, lean_object* v_m_888_, lean_object* v_a_889_, lean_object* v_fallback_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Std_HashMap_getKeyD___redArg(v_x_886_, v_x_887_, v_m_888_, v_a_889_, v_fallback_890_);
lean_dec(v_fallback_890_);
lean_dec_ref(v_m_888_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD(lean_object* v_00_u03b1_892_, lean_object* v_00_u03b2_893_, lean_object* v_x_894_, lean_object* v_x_895_, lean_object* v_m_896_, lean_object* v_a_897_, lean_object* v_fallback_898_){
_start:
{
lean_object* v___x_899_; 
v___x_899_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_894_, v_x_895_, v_m_896_, v_a_897_, v_fallback_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___boxed(lean_object* v_00_u03b1_900_, lean_object* v_00_u03b2_901_, lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_m_904_, lean_object* v_a_905_, lean_object* v_fallback_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l_Std_HashMap_getKeyD(v_00_u03b1_900_, v_00_u03b2_901_, v_x_902_, v_x_903_, v_m_904_, v_a_905_, v_fallback_906_);
lean_dec(v_fallback_906_);
lean_dec_ref(v_m_904_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg(lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_inst_910_, lean_object* v_m_911_, lean_object* v_a_912_){
_start:
{
lean_object* v___x_913_; 
v___x_913_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_908_, v_x_909_, v_inst_910_, v_m_911_, v_a_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg___boxed(lean_object* v_x_914_, lean_object* v_x_915_, lean_object* v_inst_916_, lean_object* v_m_917_, lean_object* v_a_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_HashMap_getKey_x21___redArg(v_x_914_, v_x_915_, v_inst_916_, v_m_917_, v_a_918_);
lean_dec_ref(v_m_917_);
lean_dec(v_inst_916_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21(lean_object* v_00_u03b1_920_, lean_object* v_00_u03b2_921_, lean_object* v_x_922_, lean_object* v_x_923_, lean_object* v_inst_924_, lean_object* v_m_925_, lean_object* v_a_926_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_922_, v_x_923_, v_inst_924_, v_m_925_, v_a_926_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___boxed(lean_object* v_00_u03b1_928_, lean_object* v_00_u03b2_929_, lean_object* v_x_930_, lean_object* v_x_931_, lean_object* v_inst_932_, lean_object* v_m_933_, lean_object* v_a_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Std_HashMap_getKey_x21(v_00_u03b1_928_, v_00_u03b2_929_, v_x_930_, v_x_931_, v_inst_932_, v_m_933_, v_a_934_);
lean_dec_ref(v_m_933_);
lean_dec(v_inst_932_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase___redArg(lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_m_938_, lean_object* v_a_939_){
_start:
{
lean_object* v___x_940_; 
v___x_940_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_936_, v_x_937_, v_m_938_, v_a_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase(lean_object* v_00_u03b1_941_, lean_object* v_00_u03b2_942_, lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_m_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_943_, v_x_944_, v_m_945_, v_a_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg(lean_object* v_m_948_){
_start:
{
lean_object* v_size_949_; 
v_size_949_ = lean_ctor_get(v_m_948_, 0);
lean_inc(v_size_949_);
return v_size_949_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg___boxed(lean_object* v_m_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Std_HashMap_size___redArg(v_m_950_);
lean_dec_ref(v_m_950_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size(lean_object* v_00_u03b1_952_, lean_object* v_00_u03b2_953_, lean_object* v_x_954_, lean_object* v_x_955_, lean_object* v_m_956_){
_start:
{
lean_object* v_size_957_; 
v_size_957_ = lean_ctor_get(v_m_956_, 0);
lean_inc(v_size_957_);
return v_size_957_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___boxed(lean_object* v_00_u03b1_958_, lean_object* v_00_u03b2_959_, lean_object* v_x_960_, lean_object* v_x_961_, lean_object* v_m_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l_Std_HashMap_size(v_00_u03b1_958_, v_00_u03b2_959_, v_x_960_, v_x_961_, v_m_962_);
lean_dec_ref(v_m_962_);
lean_dec_ref(v_x_961_);
lean_dec_ref(v_x_960_);
return v_res_963_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty___redArg(lean_object* v_m_964_){
_start:
{
lean_object* v_size_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v_size_965_ = lean_ctor_get(v_m_964_, 0);
v___x_966_ = lean_unsigned_to_nat(0u);
v___x_967_ = lean_nat_dec_eq(v_size_965_, v___x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___redArg___boxed(lean_object* v_m_968_){
_start:
{
uint8_t v_res_969_; lean_object* v_r_970_; 
v_res_969_ = l_Std_HashMap_isEmpty___redArg(v_m_968_);
lean_dec_ref(v_m_968_);
v_r_970_ = lean_box(v_res_969_);
return v_r_970_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty(lean_object* v_00_u03b1_971_, lean_object* v_00_u03b2_972_, lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v_m_975_){
_start:
{
lean_object* v_size_976_; lean_object* v___x_977_; uint8_t v___x_978_; 
v_size_976_ = lean_ctor_get(v_m_975_, 0);
v___x_977_ = lean_unsigned_to_nat(0u);
v___x_978_ = lean_nat_dec_eq(v_size_976_, v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___boxed(lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_m_983_){
_start:
{
uint8_t v_res_984_; lean_object* v_r_985_; 
v_res_984_ = l_Std_HashMap_isEmpty(v_00_u03b1_979_, v_00_u03b2_980_, v_x_981_, v_x_982_, v_m_983_);
lean_dec_ref(v_m_983_);
lean_dec_ref(v_x_982_);
lean_dec_ref(v_x_981_);
v_r_985_ = lean_box(v_res_984_);
return v_r_985_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0(lean_object* v_a_986_, lean_object* v_b_987_, lean_object* v_d_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_989_, 0, v_a_986_);
lean_ctor_set(v___x_989_, 1, v_d_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0___boxed(lean_object* v_a_990_, lean_object* v_b_991_, lean_object* v_d_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_HashMap_keys___redArg___lam__0(v_a_990_, v_b_991_, v_d_992_);
lean_dec(v_b_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__1(lean_object* v___x_994_, lean_object* v___f_995_, lean_object* v_l_996_, lean_object* v_acc_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_994_, v___f_995_, v_acc_997_, v_l_996_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg(lean_object* v_m_1022_){
_start:
{
lean_object* v___x_1023_; lean_object* v_buckets_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1023_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1024_ = lean_ctor_get(v_m_1022_, 1);
lean_inc_ref(v_buckets_1024_);
lean_dec_ref(v_m_1022_);
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_array_get_size(v_buckets_1024_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = lean_nat_dec_lt(v___x_1027_, v___x_1026_);
if (v___x_1028_ == 0)
{
lean_dec_ref(v_buckets_1024_);
return v___x_1025_;
}
else
{
lean_object* v___f_1029_; size_t v___x_1030_; size_t v___x_1031_; lean_object* v___x_1032_; 
v___f_1029_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__11));
v___x_1030_ = lean_usize_of_nat(v___x_1026_);
v___x_1031_ = ((size_t)0ULL);
v___x_1032_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1023_, v___f_1029_, v_buckets_1024_, v___x_1030_, v___x_1031_, v___x_1025_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys(lean_object* v_00_u03b1_1033_, lean_object* v_00_u03b2_1034_, lean_object* v_x_1035_, lean_object* v_x_1036_, lean_object* v_m_1037_){
_start:
{
lean_object* v___x_1038_; lean_object* v_buckets_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1038_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1039_ = lean_ctor_get(v_m_1037_, 1);
lean_inc_ref(v_buckets_1039_);
lean_dec_ref(v_m_1037_);
v___x_1040_ = lean_box(0);
v___x_1041_ = lean_array_get_size(v_buckets_1039_);
v___x_1042_ = lean_unsigned_to_nat(0u);
v___x_1043_ = lean_nat_dec_lt(v___x_1042_, v___x_1041_);
if (v___x_1043_ == 0)
{
lean_dec_ref(v_buckets_1039_);
return v___x_1040_;
}
else
{
lean_object* v___f_1044_; size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v___f_1044_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__11));
v___x_1045_ = lean_usize_of_nat(v___x_1041_);
v___x_1046_ = ((size_t)0ULL);
v___x_1047_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1038_, v___f_1044_, v_buckets_1039_, v___x_1045_, v___x_1046_, v___x_1040_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___boxed(lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_m_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Std_HashMap_keys(v_00_u03b1_1048_, v_00_u03b2_1049_, v_x_1050_, v_x_1051_, v_m_1052_);
lean_dec_ref(v_x_1051_);
lean_dec_ref(v_x_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList___redArg(lean_object* v_inst_1058_, lean_object* v_inst_1059_, lean_object* v_l_1060_){
_start:
{
lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___f_1061_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1062_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1063_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1061_, v_inst_1058_, v_inst_1059_, v___x_1062_, v_l_1060_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_inst_1066_, lean_object* v_inst_1067_, lean_object* v_l_1068_){
_start:
{
lean_object* v___f_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v___f_1069_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1070_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1071_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1069_, v_inst_1066_, v_inst_1067_, v___x_1070_, v_l_1068_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList___redArg(lean_object* v_inst_1072_, lean_object* v_inst_1073_, lean_object* v_l_1074_){
_start:
{
lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___f_1075_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1076_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1077_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1075_, v_inst_1072_, v_inst_1073_, v___x_1076_, v_l_1074_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList(lean_object* v_00_u03b1_1078_, lean_object* v_inst_1079_, lean_object* v_inst_1080_, lean_object* v_l_1081_){
_start:
{
lean_object* v___f_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___f_1082_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1083_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1084_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1082_, v_inst_1079_, v_inst_1080_, v___x_1083_, v_l_1081_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray___redArg(lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___f_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___f_1092_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1093_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1092_, v_inst_1089_, v_inst_1090_, v___x_1093_, v_a_1091_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray(lean_object* v_00_u03b1_1095_, lean_object* v_00_u03b2_1096_, lean_object* v_inst_1097_, lean_object* v_inst_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v___f_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___f_1100_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1101_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1102_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1100_, v_inst_1097_, v_inst_1098_, v___x_1101_, v_a_1099_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__0(lean_object* v_a_1103_, lean_object* v_b_1104_, lean_object* v_d_1105_){
_start:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1106_, 0, v_a_1103_);
lean_ctor_set(v___x_1106_, 1, v_b_1104_);
v___x_1107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v_d_1105_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__1(lean_object* v___x_1108_, lean_object* v___f_1109_, lean_object* v_l_1110_, lean_object* v_acc_1111_){
_start:
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1108_, v___f_1109_, v_acc_1111_, v_l_1110_);
return v___x_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg(lean_object* v_m_1117_){
_start:
{
lean_object* v___x_1118_; lean_object* v_buckets_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1118_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1119_ = lean_ctor_get(v_m_1117_, 1);
lean_inc_ref(v_buckets_1119_);
lean_dec_ref(v_m_1117_);
v___x_1120_ = lean_box(0);
v___x_1121_ = lean_array_get_size(v_buckets_1119_);
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_nat_dec_lt(v___x_1122_, v___x_1121_);
if (v___x_1123_ == 0)
{
lean_dec_ref(v_buckets_1119_);
return v___x_1120_;
}
else
{
lean_object* v___f_1124_; size_t v___x_1125_; size_t v___x_1126_; lean_object* v___x_1127_; 
v___f_1124_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__1));
v___x_1125_ = lean_usize_of_nat(v___x_1121_);
v___x_1126_ = ((size_t)0ULL);
v___x_1127_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1118_, v___f_1124_, v_buckets_1119_, v___x_1125_, v___x_1126_, v___x_1120_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList(lean_object* v_00_u03b1_1128_, lean_object* v_00_u03b2_1129_, lean_object* v_x_1130_, lean_object* v_x_1131_, lean_object* v_m_1132_){
_start:
{
lean_object* v___x_1133_; lean_object* v_buckets_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; uint8_t v___x_1138_; 
v___x_1133_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1134_ = lean_ctor_get(v_m_1132_, 1);
lean_inc_ref(v_buckets_1134_);
lean_dec_ref(v_m_1132_);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_array_get_size(v_buckets_1134_);
v___x_1137_ = lean_unsigned_to_nat(0u);
v___x_1138_ = lean_nat_dec_lt(v___x_1137_, v___x_1136_);
if (v___x_1138_ == 0)
{
lean_dec_ref(v_buckets_1134_);
return v___x_1135_;
}
else
{
lean_object* v___f_1139_; size_t v___x_1140_; size_t v___x_1141_; lean_object* v___x_1142_; 
v___f_1139_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__1));
v___x_1140_ = lean_usize_of_nat(v___x_1136_);
v___x_1141_ = ((size_t)0ULL);
v___x_1142_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1133_, v___f_1139_, v_buckets_1134_, v___x_1140_, v___x_1141_, v___x_1135_);
return v___x_1142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___boxed(lean_object* v_00_u03b1_1143_, lean_object* v_00_u03b2_1144_, lean_object* v_x_1145_, lean_object* v_x_1146_, lean_object* v_m_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Std_HashMap_toList(v_00_u03b1_1143_, v_00_u03b2_1144_, v_x_1145_, v_x_1146_, v_m_1147_);
lean_dec_ref(v_x_1146_);
lean_dec_ref(v_x_1145_);
return v_res_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg___lam__0(lean_object* v_inst_1149_, lean_object* v_f_1150_, lean_object* v_acc_1151_, lean_object* v_l_1152_){
_start:
{
lean_object* v___x_1153_; 
v___x_1153_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1149_, v_f_1150_, v_acc_1151_, v_l_1152_);
return v___x_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg(lean_object* v_inst_1154_, lean_object* v_f_1155_, lean_object* v_init_1156_, lean_object* v_b_1157_){
_start:
{
lean_object* v_toApplicative_1158_; lean_object* v_buckets_1159_; lean_object* v_toPure_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; uint8_t v___x_1163_; 
v_toApplicative_1158_ = lean_ctor_get(v_inst_1154_, 0);
v_buckets_1159_ = lean_ctor_get(v_b_1157_, 1);
lean_inc_ref(v_buckets_1159_);
lean_dec_ref(v_b_1157_);
v_toPure_1160_ = lean_ctor_get(v_toApplicative_1158_, 1);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = lean_array_get_size(v_buckets_1159_);
v___x_1163_ = lean_nat_dec_lt(v___x_1161_, v___x_1162_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
lean_inc(v_toPure_1160_);
lean_dec_ref(v_buckets_1159_);
lean_dec(v_f_1155_);
lean_dec_ref(v_inst_1154_);
v___x_1164_ = lean_apply_2(v_toPure_1160_, lean_box(0), v_init_1156_);
return v___x_1164_;
}
else
{
lean_object* v___f_1165_; size_t v___x_1166_; size_t v___x_1167_; lean_object* v___x_1168_; 
lean_inc_ref(v_inst_1154_);
v___f_1165_ = lean_alloc_closure((void*)(l_Std_HashMap_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1165_, 0, v_inst_1154_);
lean_closure_set(v___f_1165_, 1, v_f_1155_);
v___x_1166_ = ((size_t)0ULL);
v___x_1167_ = lean_usize_of_nat(v___x_1162_);
v___x_1168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1154_, v___f_1165_, v_buckets_1159_, v___x_1166_, v___x_1167_, v_init_1156_);
return v___x_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM(lean_object* v_00_u03b1_1169_, lean_object* v_00_u03b2_1170_, lean_object* v_x_1171_, lean_object* v_x_1172_, lean_object* v_m_1173_, lean_object* v_inst_1174_, lean_object* v_00_u03b3_1175_, lean_object* v_f_1176_, lean_object* v_init_1177_, lean_object* v_b_1178_){
_start:
{
lean_object* v_toApplicative_1179_; lean_object* v_buckets_1180_; lean_object* v_toPure_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v_toApplicative_1179_ = lean_ctor_get(v_inst_1174_, 0);
v_buckets_1180_ = lean_ctor_get(v_b_1178_, 1);
lean_inc_ref(v_buckets_1180_);
lean_dec_ref(v_b_1178_);
v_toPure_1181_ = lean_ctor_get(v_toApplicative_1179_, 1);
v___x_1182_ = lean_unsigned_to_nat(0u);
v___x_1183_ = lean_array_get_size(v_buckets_1180_);
v___x_1184_ = lean_nat_dec_lt(v___x_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v___x_1185_; 
lean_inc(v_toPure_1181_);
lean_dec_ref(v_buckets_1180_);
lean_dec(v_f_1176_);
lean_dec_ref(v_inst_1174_);
v___x_1185_ = lean_apply_2(v_toPure_1181_, lean_box(0), v_init_1177_);
return v___x_1185_;
}
else
{
lean_object* v___f_1186_; size_t v___x_1187_; size_t v___x_1188_; lean_object* v___x_1189_; 
lean_inc_ref(v_inst_1174_);
v___f_1186_ = lean_alloc_closure((void*)(l_Std_HashMap_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1186_, 0, v_inst_1174_);
lean_closure_set(v___f_1186_, 1, v_f_1176_);
v___x_1187_ = ((size_t)0ULL);
v___x_1188_ = lean_usize_of_nat(v___x_1183_);
v___x_1189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1174_, v___f_1186_, v_buckets_1180_, v___x_1187_, v___x_1188_, v_init_1177_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___boxed(lean_object* v_00_u03b1_1190_, lean_object* v_00_u03b2_1191_, lean_object* v_x_1192_, lean_object* v_x_1193_, lean_object* v_m_1194_, lean_object* v_inst_1195_, lean_object* v_00_u03b3_1196_, lean_object* v_f_1197_, lean_object* v_init_1198_, lean_object* v_b_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_HashMap_foldM(v_00_u03b1_1190_, v_00_u03b2_1191_, v_x_1192_, v_x_1193_, v_m_1194_, v_inst_1195_, v_00_u03b3_1196_, v_f_1197_, v_init_1198_, v_b_1199_);
lean_dec_ref(v_x_1193_);
lean_dec_ref(v_x_1192_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__0(lean_object* v_f_1201_, lean_object* v_x1_1202_, lean_object* v_x2_1203_, lean_object* v_x3_1204_){
_start:
{
lean_object* v___x_1205_; 
v___x_1205_ = lean_apply_3(v_f_1201_, v_x1_1202_, v_x2_1203_, v_x3_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__1(lean_object* v___x_1206_, lean_object* v___f_1207_, lean_object* v_acc_1208_, lean_object* v_l_1209_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1206_, v___f_1207_, v_acc_1208_, v_l_1209_);
return v___x_1210_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg(lean_object* v_f_1211_, lean_object* v_init_1212_, lean_object* v_b_1213_){
_start:
{
lean_object* v___x_1214_; lean_object* v_buckets_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; uint8_t v___x_1218_; 
v___x_1214_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1215_ = lean_ctor_get(v_b_1213_, 1);
lean_inc_ref(v_buckets_1215_);
lean_dec_ref(v_b_1213_);
v___x_1216_ = lean_unsigned_to_nat(0u);
v___x_1217_ = lean_array_get_size(v_buckets_1215_);
v___x_1218_ = lean_nat_dec_lt(v___x_1216_, v___x_1217_);
if (v___x_1218_ == 0)
{
lean_dec_ref(v_buckets_1215_);
lean_dec(v_f_1211_);
return v_init_1212_;
}
else
{
lean_object* v___f_1219_; lean_object* v___f_1220_; size_t v___x_1221_; size_t v___x_1222_; lean_object* v___x_1223_; 
v___f_1219_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1219_, 0, v_f_1211_);
v___f_1220_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1220_, 0, v___x_1214_);
lean_closure_set(v___f_1220_, 1, v___f_1219_);
v___x_1221_ = ((size_t)0ULL);
v___x_1222_ = lean_usize_of_nat(v___x_1217_);
v___x_1223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1214_, v___f_1220_, v_buckets_1215_, v___x_1221_, v___x_1222_, v_init_1212_);
return v___x_1223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_x_1226_, lean_object* v_x_1227_, lean_object* v_00_u03b3_1228_, lean_object* v_f_1229_, lean_object* v_init_1230_, lean_object* v_b_1231_){
_start:
{
lean_object* v___x_1232_; lean_object* v_buckets_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; uint8_t v___x_1236_; 
v___x_1232_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1233_ = lean_ctor_get(v_b_1231_, 1);
lean_inc_ref(v_buckets_1233_);
lean_dec_ref(v_b_1231_);
v___x_1234_ = lean_unsigned_to_nat(0u);
v___x_1235_ = lean_array_get_size(v_buckets_1233_);
v___x_1236_ = lean_nat_dec_lt(v___x_1234_, v___x_1235_);
if (v___x_1236_ == 0)
{
lean_dec_ref(v_buckets_1233_);
lean_dec(v_f_1229_);
return v_init_1230_;
}
else
{
lean_object* v___f_1237_; lean_object* v___f_1238_; size_t v___x_1239_; size_t v___x_1240_; lean_object* v___x_1241_; 
v___f_1237_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1237_, 0, v_f_1229_);
v___f_1238_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1238_, 0, v___x_1232_);
lean_closure_set(v___f_1238_, 1, v___f_1237_);
v___x_1239_ = ((size_t)0ULL);
v___x_1240_ = lean_usize_of_nat(v___x_1235_);
v___x_1241_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1232_, v___f_1238_, v_buckets_1233_, v___x_1239_, v___x_1240_, v_init_1230_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___boxed(lean_object* v_00_u03b1_1242_, lean_object* v_00_u03b2_1243_, lean_object* v_x_1244_, lean_object* v_x_1245_, lean_object* v_00_u03b3_1246_, lean_object* v_f_1247_, lean_object* v_init_1248_, lean_object* v_b_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l_Std_HashMap_fold(v_00_u03b1_1242_, v_00_u03b2_1243_, v_x_1244_, v_x_1245_, v_00_u03b3_1246_, v_f_1247_, v_init_1248_, v_b_1249_);
lean_dec_ref(v_x_1245_);
lean_dec_ref(v_x_1244_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__0(lean_object* v_f_1251_, lean_object* v_x_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = lean_apply_2(v_f_1251_, v___y_1253_, v___y_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__1(lean_object* v_inst_1256_, lean_object* v___f_1257_, lean_object* v_x_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_box(0);
v___x_1261_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1256_, v___f_1257_, v___x_1260_, v___y_1259_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg(lean_object* v_inst_1262_, lean_object* v_f_1263_, lean_object* v_b_1264_){
_start:
{
lean_object* v_toApplicative_1265_; lean_object* v_buckets_1266_; lean_object* v_toPure_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; uint8_t v___x_1271_; 
v_toApplicative_1265_ = lean_ctor_get(v_inst_1262_, 0);
v_buckets_1266_ = lean_ctor_get(v_b_1264_, 1);
lean_inc_ref(v_buckets_1266_);
lean_dec_ref(v_b_1264_);
v_toPure_1267_ = lean_ctor_get(v_toApplicative_1265_, 1);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_array_get_size(v_buckets_1266_);
v___x_1270_ = lean_box(0);
v___x_1271_ = lean_nat_dec_lt(v___x_1268_, v___x_1269_);
if (v___x_1271_ == 0)
{
lean_object* v___x_1272_; 
lean_inc(v_toPure_1267_);
lean_dec_ref(v_buckets_1266_);
lean_dec(v_f_1263_);
lean_dec_ref(v_inst_1262_);
v___x_1272_ = lean_apply_2(v_toPure_1267_, lean_box(0), v___x_1270_);
return v___x_1272_;
}
else
{
lean_object* v___f_1273_; lean_object* v___f_1274_; size_t v___x_1275_; size_t v___x_1276_; lean_object* v___x_1277_; 
v___f_1273_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1273_, 0, v_f_1263_);
lean_inc_ref(v_inst_1262_);
v___f_1274_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1274_, 0, v_inst_1262_);
lean_closure_set(v___f_1274_, 1, v___f_1273_);
v___x_1275_ = ((size_t)0ULL);
v___x_1276_ = lean_usize_of_nat(v___x_1269_);
v___x_1277_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1262_, v___f_1274_, v_buckets_1266_, v___x_1275_, v___x_1276_, v___x_1270_);
return v___x_1277_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM(lean_object* v_00_u03b1_1278_, lean_object* v_00_u03b2_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_m_1282_, lean_object* v_inst_1283_, lean_object* v_f_1284_, lean_object* v_b_1285_){
_start:
{
lean_object* v_toApplicative_1286_; lean_object* v_buckets_1287_; lean_object* v_toPure_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; uint8_t v___x_1292_; 
v_toApplicative_1286_ = lean_ctor_get(v_inst_1283_, 0);
v_buckets_1287_ = lean_ctor_get(v_b_1285_, 1);
lean_inc_ref(v_buckets_1287_);
lean_dec_ref(v_b_1285_);
v_toPure_1288_ = lean_ctor_get(v_toApplicative_1286_, 1);
v___x_1289_ = lean_unsigned_to_nat(0u);
v___x_1290_ = lean_array_get_size(v_buckets_1287_);
v___x_1291_ = lean_box(0);
v___x_1292_ = lean_nat_dec_lt(v___x_1289_, v___x_1290_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
lean_inc(v_toPure_1288_);
lean_dec_ref(v_buckets_1287_);
lean_dec(v_f_1284_);
lean_dec_ref(v_inst_1283_);
v___x_1293_ = lean_apply_2(v_toPure_1288_, lean_box(0), v___x_1291_);
return v___x_1293_;
}
else
{
lean_object* v___f_1294_; lean_object* v___f_1295_; size_t v___x_1296_; size_t v___x_1297_; lean_object* v___x_1298_; 
v___f_1294_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1294_, 0, v_f_1284_);
lean_inc_ref(v_inst_1283_);
v___f_1295_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1295_, 0, v_inst_1283_);
lean_closure_set(v___f_1295_, 1, v___f_1294_);
v___x_1296_ = ((size_t)0ULL);
v___x_1297_ = lean_usize_of_nat(v___x_1290_);
v___x_1298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1283_, v___f_1295_, v_buckets_1287_, v___x_1296_, v___x_1297_, v___x_1291_);
return v___x_1298_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___boxed(lean_object* v_00_u03b1_1299_, lean_object* v_00_u03b2_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_, lean_object* v_m_1303_, lean_object* v_inst_1304_, lean_object* v_f_1305_, lean_object* v_b_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Std_HashMap_forM(v_00_u03b1_1299_, v_00_u03b2_1300_, v_x_1301_, v_x_1302_, v_m_1303_, v_inst_1304_, v_f_1305_, v_b_1306_);
lean_dec_ref(v_x_1302_);
lean_dec_ref(v_x_1301_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg___lam__0(lean_object* v_inst_1308_, lean_object* v_f_1309_, lean_object* v_a_1310_, lean_object* v_x_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1313_; 
v___x_1313_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1308_, v_f_1309_, v_a_1310_, v___y_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg(lean_object* v_inst_1314_, lean_object* v_f_1315_, lean_object* v_init_1316_, lean_object* v_b_1317_){
_start:
{
lean_object* v_buckets_1318_; lean_object* v___f_1319_; size_t v_sz_1320_; size_t v___x_1321_; lean_object* v___x_1322_; 
v_buckets_1318_ = lean_ctor_get(v_b_1317_, 1);
lean_inc_ref(v_buckets_1318_);
lean_dec_ref(v_b_1317_);
lean_inc_ref(v_inst_1314_);
v___f_1319_ = lean_alloc_closure((void*)(l_Std_HashMap_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1319_, 0, v_inst_1314_);
lean_closure_set(v___f_1319_, 1, v_f_1315_);
v_sz_1320_ = lean_array_size(v_buckets_1318_);
v___x_1321_ = ((size_t)0ULL);
v___x_1322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1314_, v_buckets_1318_, v___f_1319_, v_sz_1320_, v___x_1321_, v_init_1316_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn(lean_object* v_00_u03b1_1323_, lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_, lean_object* v_m_1327_, lean_object* v_inst_1328_, lean_object* v_00_u03b3_1329_, lean_object* v_f_1330_, lean_object* v_init_1331_, lean_object* v_b_1332_){
_start:
{
lean_object* v_buckets_1333_; lean_object* v___f_1334_; size_t v_sz_1335_; size_t v___x_1336_; lean_object* v___x_1337_; 
v_buckets_1333_ = lean_ctor_get(v_b_1332_, 1);
lean_inc_ref(v_buckets_1333_);
lean_dec_ref(v_b_1332_);
lean_inc_ref(v_inst_1328_);
v___f_1334_ = lean_alloc_closure((void*)(l_Std_HashMap_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1334_, 0, v_inst_1328_);
lean_closure_set(v___f_1334_, 1, v_f_1330_);
v_sz_1335_ = lean_array_size(v_buckets_1333_);
v___x_1336_ = ((size_t)0ULL);
v___x_1337_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1328_, v_buckets_1333_, v___f_1334_, v_sz_1335_, v___x_1336_, v_init_1331_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___boxed(lean_object* v_00_u03b1_1338_, lean_object* v_00_u03b2_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_, lean_object* v_m_1342_, lean_object* v_inst_1343_, lean_object* v_00_u03b3_1344_, lean_object* v_f_1345_, lean_object* v_init_1346_, lean_object* v_b_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l_Std_HashMap_forIn(v_00_u03b1_1338_, v_00_u03b2_1339_, v_x_1340_, v_x_1341_, v_m_1342_, v_inst_1343_, v_00_u03b3_1344_, v_f_1345_, v_init_1346_, v_b_1347_);
lean_dec_ref(v_x_1341_);
lean_dec_ref(v_x_1340_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1349_, lean_object* v_x_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___y_1351_);
lean_ctor_set(v___x_1353_, 1, v___y_1352_);
v___x_1354_ = lean_apply_1(v_f_1349_, v___x_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1355_, lean_object* v_m_1356_, lean_object* v_f_1357_){
_start:
{
lean_object* v_toApplicative_1358_; lean_object* v_buckets_1359_; lean_object* v_toPure_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_toApplicative_1358_ = lean_ctor_get(v_inst_1355_, 0);
v_buckets_1359_ = lean_ctor_get(v_m_1356_, 1);
lean_inc_ref(v_buckets_1359_);
lean_dec_ref(v_m_1356_);
v_toPure_1360_ = lean_ctor_get(v_toApplicative_1358_, 1);
v___x_1361_ = lean_unsigned_to_nat(0u);
v___x_1362_ = lean_array_get_size(v_buckets_1359_);
v___x_1363_ = lean_box(0);
v___x_1364_ = lean_nat_dec_lt(v___x_1361_, v___x_1362_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; 
lean_inc(v_toPure_1360_);
lean_dec_ref(v_buckets_1359_);
lean_dec(v_f_1357_);
lean_dec_ref(v_inst_1355_);
v___x_1365_ = lean_apply_2(v_toPure_1360_, lean_box(0), v___x_1363_);
return v___x_1365_;
}
else
{
lean_object* v___f_1366_; lean_object* v___f_1367_; size_t v___x_1368_; size_t v___x_1369_; lean_object* v___x_1370_; 
v___f_1366_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1366_, 0, v_f_1357_);
lean_inc_ref(v_inst_1355_);
v___f_1367_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1367_, 0, v_inst_1355_);
lean_closure_set(v___f_1367_, 1, v___f_1366_);
v___x_1368_ = ((size_t)0ULL);
v___x_1369_ = lean_usize_of_nat(v___x_1362_);
v___x_1370_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1355_, v___f_1367_, v_buckets_1359_, v___x_1368_, v___x_1369_, v___x_1363_);
return v___x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg(lean_object* v_inst_1371_){
_start:
{
lean_object* v___f_1372_; 
v___f_1372_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1372_, 0, v_inst_1371_);
return v___f_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad(lean_object* v_00_u03b1_1373_, lean_object* v_00_u03b2_1374_, lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_m_1377_, lean_object* v_inst_1378_){
_start:
{
lean_object* v___f_1379_; 
v___f_1379_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1379_, 0, v_inst_1378_);
return v___f_1379_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_1380_, lean_object* v_00_u03b2_1381_, lean_object* v_inst_1382_, lean_object* v_inst_1383_, lean_object* v_m_1384_, lean_object* v_inst_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Std_HashMap_instForMProdOfMonad(v_00_u03b1_1380_, v_00_u03b2_1381_, v_inst_1382_, v_inst_1383_, v_m_1384_, v_inst_1385_);
lean_dec_ref(v_inst_1383_);
lean_dec_ref(v_inst_1382_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1387_, lean_object* v_a_1388_, lean_object* v_b_1389_, lean_object* v_acc_1390_){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___x_1391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1391_, 0, v_a_1388_);
lean_ctor_set(v___x_1391_, 1, v_b_1389_);
v___x_1392_ = lean_apply_2(v_f_1387_, v___x_1391_, v_acc_1390_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1393_, lean_object* v___f_1394_, lean_object* v_a_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1393_, v___f_1394_, v_a_1395_, v___y_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1399_, lean_object* v_00_u03b2_1400_, lean_object* v_m_1401_, lean_object* v_init_1402_, lean_object* v_f_1403_){
_start:
{
lean_object* v_buckets_1404_; lean_object* v___f_1405_; lean_object* v___f_1406_; size_t v_sz_1407_; size_t v___x_1408_; lean_object* v___x_1409_; 
v_buckets_1404_ = lean_ctor_get(v_m_1401_, 1);
lean_inc_ref(v_buckets_1404_);
lean_dec_ref(v_m_1401_);
v___f_1405_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1405_, 0, v_f_1403_);
lean_inc_ref(v_inst_1399_);
v___f_1406_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1406_, 0, v_inst_1399_);
lean_closure_set(v___f_1406_, 1, v___f_1405_);
v_sz_1407_ = lean_array_size(v_buckets_1404_);
v___x_1408_ = ((size_t)0ULL);
v___x_1409_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1399_, v_buckets_1404_, v___f_1406_, v_sz_1407_, v___x_1408_, v_init_1402_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1410_){
_start:
{
lean_object* v___f_1411_; 
v___f_1411_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1411_, 0, v_inst_1410_);
return v___f_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad(lean_object* v_00_u03b1_1412_, lean_object* v_00_u03b2_1413_, lean_object* v_inst_1414_, lean_object* v_inst_1415_, lean_object* v_m_1416_, lean_object* v_inst_1417_){
_start:
{
lean_object* v___f_1418_; 
v___f_1418_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1418_, 0, v_inst_1417_);
return v___f_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1419_, lean_object* v_00_u03b2_1420_, lean_object* v_inst_1421_, lean_object* v_inst_1422_, lean_object* v_m_1423_, lean_object* v_inst_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_Std_HashMap_instForInProdOfMonad(v_00_u03b1_1419_, v_00_u03b2_1420_, v_inst_1421_, v_inst_1422_, v_m_1423_, v_inst_1424_);
lean_dec_ref(v_inst_1422_);
lean_dec_ref(v_inst_1421_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___redArg(lean_object* v_f_1426_, lean_object* v_m_1427_){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1426_, v_m_1427_);
return v___x_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter(lean_object* v_00_u03b1_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_, lean_object* v_f_1433_, lean_object* v_m_1434_){
_start:
{
lean_object* v___x_1435_; 
v___x_1435_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1433_, v_m_1434_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___boxed(lean_object* v_00_u03b1_1436_, lean_object* v_00_u03b2_1437_, lean_object* v_x_1438_, lean_object* v_x_1439_, lean_object* v_f_1440_, lean_object* v_m_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Std_HashMap_filter(v_00_u03b1_1436_, v_00_u03b2_1437_, v_x_1438_, v_x_1439_, v_f_1440_, v_m_1441_);
lean_dec_ref(v_x_1439_);
lean_dec_ref(v_x_1438_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify___redArg(lean_object* v_x_1443_, lean_object* v_x_1444_, lean_object* v_m_1445_, lean_object* v_a_1446_, lean_object* v_f_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1443_, v_x_1444_, v_m_1445_, v_a_1446_, v_f_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify(lean_object* v_00_u03b1_1449_, lean_object* v_00_u03b2_1450_, lean_object* v_x_1451_, lean_object* v_x_1452_, lean_object* v_m_1453_, lean_object* v_a_1454_, lean_object* v_f_1455_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1451_, v_x_1452_, v_m_1453_, v_a_1454_, v_f_1455_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter___redArg(lean_object* v_x_1457_, lean_object* v_x_1458_, lean_object* v_m_1459_, lean_object* v_a_1460_, lean_object* v_f_1461_){
_start:
{
lean_object* v___x_1462_; 
v___x_1462_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1457_, v_x_1458_, v_m_1459_, v_a_1460_, v_f_1461_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter(lean_object* v_00_u03b1_1463_, lean_object* v_00_u03b2_1464_, lean_object* v_x_1465_, lean_object* v_x_1466_, lean_object* v_m_1467_, lean_object* v_a_1468_, lean_object* v_f_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1465_, v_x_1466_, v_m_1467_, v_a_1468_, v_f_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany___redArg(lean_object* v_x_1471_, lean_object* v_x_1472_, lean_object* v_inst_1473_, lean_object* v_m_1474_, lean_object* v_l_1475_){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_1473_, v_x_1471_, v_x_1472_, v_m_1474_, v_l_1475_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany(lean_object* v_00_u03b1_1477_, lean_object* v_00_u03b2_1478_, lean_object* v_x_1479_, lean_object* v_x_1480_, lean_object* v_00_u03c1_1481_, lean_object* v_inst_1482_, lean_object* v_m_1483_, lean_object* v_l_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_1482_, v_x_1479_, v_x_1480_, v_m_1483_, v_l_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit___redArg(lean_object* v_x_1486_, lean_object* v_x_1487_, lean_object* v_inst_1488_, lean_object* v_m_1489_, lean_object* v_l_1490_){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1488_, v_x_1486_, v_x_1487_, v_m_1489_, v_l_1490_);
return v___x_1491_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit(lean_object* v_00_u03b1_1492_, lean_object* v_x_1493_, lean_object* v_x_1494_, lean_object* v_00_u03c1_1495_, lean_object* v_inst_1496_, lean_object* v_m_1497_, lean_object* v_l_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1496_, v_x_1493_, v_x_1494_, v_m_1497_, v_l_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__0(lean_object* v_x1_1500_, lean_object* v_x2_1501_, lean_object* v_x3_1502_){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1503_, 0, v_x2_1501_);
lean_ctor_set(v___x_1503_, 1, v_x3_1502_);
v___x_1504_ = lean_array_push(v_x1_1500_, v___x_1503_);
return v___x_1504_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__1(lean_object* v___x_1505_, lean_object* v___f_1506_, lean_object* v_acc_1507_, lean_object* v_l_1508_){
_start:
{
lean_object* v___x_1509_; 
v___x_1509_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1505_, v___f_1506_, v_acc_1507_, v_l_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg(lean_object* v_m_1514_){
_start:
{
lean_object* v_size_1515_; lean_object* v_buckets_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; uint8_t v___x_1521_; 
v_size_1515_ = lean_ctor_get(v_m_1514_, 0);
lean_inc(v_size_1515_);
v_buckets_1516_ = lean_ctor_get(v_m_1514_, 1);
lean_inc_ref(v_buckets_1516_);
lean_dec_ref(v_m_1514_);
v___x_1517_ = lean_mk_empty_array_with_capacity(v_size_1515_);
lean_dec(v_size_1515_);
v___x_1518_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1519_ = lean_unsigned_to_nat(0u);
v___x_1520_ = lean_array_get_size(v_buckets_1516_);
v___x_1521_ = lean_nat_dec_lt(v___x_1519_, v___x_1520_);
if (v___x_1521_ == 0)
{
lean_dec_ref(v_buckets_1516_);
return v___x_1517_;
}
else
{
lean_object* v___f_1522_; size_t v___x_1523_; size_t v___x_1524_; lean_object* v___x_1525_; 
v___f_1522_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__1));
v___x_1523_ = ((size_t)0ULL);
v___x_1524_ = lean_usize_of_nat(v___x_1520_);
v___x_1525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1518_, v___f_1522_, v_buckets_1516_, v___x_1523_, v___x_1524_, v___x_1517_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray(lean_object* v_00_u03b1_1526_, lean_object* v_00_u03b2_1527_, lean_object* v_x_1528_, lean_object* v_x_1529_, lean_object* v_m_1530_){
_start:
{
lean_object* v_size_1531_; lean_object* v_buckets_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v_size_1531_ = lean_ctor_get(v_m_1530_, 0);
lean_inc(v_size_1531_);
v_buckets_1532_ = lean_ctor_get(v_m_1530_, 1);
lean_inc_ref(v_buckets_1532_);
lean_dec_ref(v_m_1530_);
v___x_1533_ = lean_mk_empty_array_with_capacity(v_size_1531_);
lean_dec(v_size_1531_);
v___x_1534_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1535_ = lean_unsigned_to_nat(0u);
v___x_1536_ = lean_array_get_size(v_buckets_1532_);
v___x_1537_ = lean_nat_dec_lt(v___x_1535_, v___x_1536_);
if (v___x_1537_ == 0)
{
lean_dec_ref(v_buckets_1532_);
return v___x_1533_;
}
else
{
lean_object* v___f_1538_; size_t v___x_1539_; size_t v___x_1540_; lean_object* v___x_1541_; 
v___f_1538_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__1));
v___x_1539_ = ((size_t)0ULL);
v___x_1540_ = lean_usize_of_nat(v___x_1536_);
v___x_1541_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1534_, v___f_1538_, v_buckets_1532_, v___x_1539_, v___x_1540_, v___x_1533_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___boxed(lean_object* v_00_u03b1_1542_, lean_object* v_00_u03b2_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_m_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Std_HashMap_toArray(v_00_u03b1_1542_, v_00_u03b2_1543_, v_x_1544_, v_x_1545_, v_m_1546_);
lean_dec_ref(v_x_1545_);
lean_dec_ref(v_x_1544_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0(lean_object* v_x1_1548_, lean_object* v_x2_1549_, lean_object* v_x3_1550_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = lean_array_push(v_x1_1548_, v_x2_1549_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1552_, lean_object* v_x2_1553_, lean_object* v_x3_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Std_HashMap_keysArray___redArg___lam__0(v_x1_1552_, v_x2_1553_, v_x3_1554_);
lean_dec(v_x3_1554_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__1(lean_object* v___x_1556_, lean_object* v___f_1557_, lean_object* v_acc_1558_, lean_object* v_l_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1556_, v___f_1557_, v_acc_1558_, v_l_1559_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg(lean_object* v_m_1565_){
_start:
{
lean_object* v_size_1566_; lean_object* v_buckets_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; uint8_t v___x_1572_; 
v_size_1566_ = lean_ctor_get(v_m_1565_, 0);
lean_inc(v_size_1566_);
v_buckets_1567_ = lean_ctor_get(v_m_1565_, 1);
lean_inc_ref(v_buckets_1567_);
lean_dec_ref(v_m_1565_);
v___x_1568_ = lean_mk_empty_array_with_capacity(v_size_1566_);
lean_dec(v_size_1566_);
v___x_1569_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1570_ = lean_unsigned_to_nat(0u);
v___x_1571_ = lean_array_get_size(v_buckets_1567_);
v___x_1572_ = lean_nat_dec_lt(v___x_1570_, v___x_1571_);
if (v___x_1572_ == 0)
{
lean_dec_ref(v_buckets_1567_);
return v___x_1568_;
}
else
{
lean_object* v___f_1573_; size_t v___x_1574_; size_t v___x_1575_; lean_object* v___x_1576_; 
v___f_1573_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__1));
v___x_1574_ = ((size_t)0ULL);
v___x_1575_ = lean_usize_of_nat(v___x_1571_);
v___x_1576_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1569_, v___f_1573_, v_buckets_1567_, v___x_1574_, v___x_1575_, v___x_1568_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray(lean_object* v_00_u03b1_1577_, lean_object* v_00_u03b2_1578_, lean_object* v_x_1579_, lean_object* v_x_1580_, lean_object* v_m_1581_){
_start:
{
lean_object* v_size_1582_; lean_object* v_buckets_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; uint8_t v___x_1588_; 
v_size_1582_ = lean_ctor_get(v_m_1581_, 0);
lean_inc(v_size_1582_);
v_buckets_1583_ = lean_ctor_get(v_m_1581_, 1);
lean_inc_ref(v_buckets_1583_);
lean_dec_ref(v_m_1581_);
v___x_1584_ = lean_mk_empty_array_with_capacity(v_size_1582_);
lean_dec(v_size_1582_);
v___x_1585_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1586_ = lean_unsigned_to_nat(0u);
v___x_1587_ = lean_array_get_size(v_buckets_1583_);
v___x_1588_ = lean_nat_dec_lt(v___x_1586_, v___x_1587_);
if (v___x_1588_ == 0)
{
lean_dec_ref(v_buckets_1583_);
return v___x_1584_;
}
else
{
lean_object* v___f_1589_; size_t v___x_1590_; size_t v___x_1591_; lean_object* v___x_1592_; 
v___f_1589_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__1));
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = lean_usize_of_nat(v___x_1587_);
v___x_1592_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1585_, v___f_1589_, v_buckets_1583_, v___x_1590_, v___x_1591_, v___x_1584_);
return v___x_1592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___boxed(lean_object* v_00_u03b1_1593_, lean_object* v_00_u03b2_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_, lean_object* v_m_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_Std_HashMap_keysArray(v_00_u03b1_1593_, v_00_u03b2_1594_, v_x_1595_, v_x_1596_, v_m_1597_);
lean_dec_ref(v_x_1596_);
lean_dec_ref(v_x_1595_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0(lean_object* v_p_1599_, lean_object* v___x_1600_, lean_object* v___x_1601_, lean_object* v_a_1602_, lean_object* v_b_1603_, lean_object* v_acc_1604_){
_start:
{
lean_object* v___x_1605_; uint8_t v___x_1606_; 
v___x_1605_ = lean_apply_2(v_p_1599_, v_a_1602_, v_b_1603_);
v___x_1606_ = lean_unbox(v___x_1605_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec_ref(v___x_1601_);
v___x_1607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1605_);
v___x_1608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
lean_ctor_set(v___x_1608_, 1, v___x_1600_);
v___x_1609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1609_, 0, v___x_1608_);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1601_);
return v___x_1610_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0___boxed(lean_object* v_p_1611_, lean_object* v___x_1612_, lean_object* v___x_1613_, lean_object* v_a_1614_, lean_object* v_b_1615_, lean_object* v_acc_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_Std_HashMap_all___redArg___lam__0(v_p_1611_, v___x_1612_, v___x_1613_, v_a_1614_, v_b_1615_, v_acc_1616_);
lean_dec_ref(v_acc_1616_);
return v_res_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__1(lean_object* v___x_1618_, lean_object* v___f_1619_, lean_object* v_a_1620_, lean_object* v_x_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1618_, v___f_1619_, v_a_1620_, v___y_1622_);
return v___x_1623_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_all___redArg(lean_object* v_m_1627_, lean_object* v_p_1628_){
_start:
{
lean_object* v___x_1629_; lean_object* v_buckets_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___f_1633_; lean_object* v___f_1634_; size_t v_sz_1635_; size_t v___x_1636_; lean_object* v___x_1637_; lean_object* v_fst_1638_; 
v___x_1629_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1630_ = lean_ctor_get(v_m_1627_, 1);
lean_inc_ref(v_buckets_1630_);
lean_dec_ref(v_m_1627_);
v___x_1631_ = lean_box(0);
v___x_1632_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1633_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1633_, 0, v_p_1628_);
lean_closure_set(v___f_1633_, 1, v___x_1631_);
lean_closure_set(v___f_1633_, 2, v___x_1632_);
v___f_1634_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1634_, 0, v___x_1629_);
lean_closure_set(v___f_1634_, 1, v___f_1633_);
v_sz_1635_ = lean_array_size(v_buckets_1630_);
v___x_1636_ = ((size_t)0ULL);
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1629_, v_buckets_1630_, v___f_1634_, v_sz_1635_, v___x_1636_, v___x_1632_);
v_fst_1638_ = lean_ctor_get(v___x_1637_, 0);
lean_inc(v_fst_1638_);
lean_dec(v___x_1637_);
if (lean_obj_tag(v_fst_1638_) == 0)
{
uint8_t v___x_1639_; 
v___x_1639_ = 1;
return v___x_1639_;
}
else
{
lean_object* v_val_1640_; uint8_t v___x_1641_; 
v_val_1640_ = lean_ctor_get(v_fst_1638_, 0);
lean_inc(v_val_1640_);
lean_dec_ref_known(v_fst_1638_, 1);
v___x_1641_ = lean_unbox(v_val_1640_);
lean_dec(v_val_1640_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___boxed(lean_object* v_m_1642_, lean_object* v_p_1643_){
_start:
{
uint8_t v_res_1644_; lean_object* v_r_1645_; 
v_res_1644_ = l_Std_HashMap_all___redArg(v_m_1642_, v_p_1643_);
v_r_1645_ = lean_box(v_res_1644_);
return v_r_1645_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_all(lean_object* v_00_u03b1_1646_, lean_object* v_00_u03b2_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_m_1650_, lean_object* v_p_1651_){
_start:
{
lean_object* v___x_1652_; lean_object* v_buckets_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___f_1656_; lean_object* v___f_1657_; size_t v_sz_1658_; size_t v___x_1659_; lean_object* v___x_1660_; lean_object* v_fst_1661_; 
v___x_1652_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1653_ = lean_ctor_get(v_m_1650_, 1);
lean_inc_ref(v_buckets_1653_);
lean_dec_ref(v_m_1650_);
v___x_1654_ = lean_box(0);
v___x_1655_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1656_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1656_, 0, v_p_1651_);
lean_closure_set(v___f_1656_, 1, v___x_1654_);
lean_closure_set(v___f_1656_, 2, v___x_1655_);
v___f_1657_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1657_, 0, v___x_1652_);
lean_closure_set(v___f_1657_, 1, v___f_1656_);
v_sz_1658_ = lean_array_size(v_buckets_1653_);
v___x_1659_ = ((size_t)0ULL);
v___x_1660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1652_, v_buckets_1653_, v___f_1657_, v_sz_1658_, v___x_1659_, v___x_1655_);
v_fst_1661_ = lean_ctor_get(v___x_1660_, 0);
lean_inc(v_fst_1661_);
lean_dec(v___x_1660_);
if (lean_obj_tag(v_fst_1661_) == 0)
{
uint8_t v___x_1662_; 
v___x_1662_ = 1;
return v___x_1662_;
}
else
{
lean_object* v_val_1663_; uint8_t v___x_1664_; 
v_val_1663_ = lean_ctor_get(v_fst_1661_, 0);
lean_inc(v_val_1663_);
lean_dec_ref_known(v_fst_1661_, 1);
v___x_1664_ = lean_unbox(v_val_1663_);
lean_dec(v_val_1663_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___boxed(lean_object* v_00_u03b1_1665_, lean_object* v_00_u03b2_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_m_1669_, lean_object* v_p_1670_){
_start:
{
uint8_t v_res_1671_; lean_object* v_r_1672_; 
v_res_1671_ = l_Std_HashMap_all(v_00_u03b1_1665_, v_00_u03b2_1666_, v_x_1667_, v_x_1668_, v_m_1669_, v_p_1670_);
lean_dec_ref(v_x_1668_);
lean_dec_ref(v_x_1667_);
v_r_1672_ = lean_box(v_res_1671_);
return v_r_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0(lean_object* v_p_1673_, lean_object* v___x_1674_, lean_object* v___x_1675_, lean_object* v_a_1676_, lean_object* v_b_1677_, lean_object* v_acc_1678_){
_start:
{
lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = lean_apply_2(v_p_1673_, v_a_1676_, v_b_1677_);
v___x_1680_ = lean_unbox(v___x_1679_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; 
v___x_1681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1681_, 0, v___x_1674_);
return v___x_1681_;
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
lean_dec_ref(v___x_1674_);
v___x_1682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1682_, 0, v___x_1679_);
v___x_1683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1683_, 0, v___x_1682_);
lean_ctor_set(v___x_1683_, 1, v___x_1675_);
v___x_1684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1684_, 0, v___x_1683_);
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0___boxed(lean_object* v_p_1685_, lean_object* v___x_1686_, lean_object* v___x_1687_, lean_object* v_a_1688_, lean_object* v_b_1689_, lean_object* v_acc_1690_){
_start:
{
lean_object* v_res_1691_; 
v_res_1691_ = l_Std_HashMap_any___redArg___lam__0(v_p_1685_, v___x_1686_, v___x_1687_, v_a_1688_, v_b_1689_, v_acc_1690_);
lean_dec_ref(v_acc_1690_);
return v_res_1691_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_any___redArg(lean_object* v_m_1692_, lean_object* v_p_1693_){
_start:
{
lean_object* v___x_1694_; lean_object* v_buckets_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___f_1698_; lean_object* v___f_1699_; size_t v_sz_1700_; size_t v___x_1701_; lean_object* v___x_1702_; lean_object* v_fst_1703_; 
v___x_1694_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1695_ = lean_ctor_get(v_m_1692_, 1);
lean_inc_ref(v_buckets_1695_);
lean_dec_ref(v_m_1692_);
v___x_1696_ = lean_box(0);
v___x_1697_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1698_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1698_, 0, v_p_1693_);
lean_closure_set(v___f_1698_, 1, v___x_1697_);
lean_closure_set(v___f_1698_, 2, v___x_1696_);
v___f_1699_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1699_, 0, v___x_1694_);
lean_closure_set(v___f_1699_, 1, v___f_1698_);
v_sz_1700_ = lean_array_size(v_buckets_1695_);
v___x_1701_ = ((size_t)0ULL);
v___x_1702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1694_, v_buckets_1695_, v___f_1699_, v_sz_1700_, v___x_1701_, v___x_1697_);
v_fst_1703_ = lean_ctor_get(v___x_1702_, 0);
lean_inc(v_fst_1703_);
lean_dec(v___x_1702_);
if (lean_obj_tag(v_fst_1703_) == 0)
{
uint8_t v___x_1704_; 
v___x_1704_ = 0;
return v___x_1704_;
}
else
{
lean_object* v_val_1705_; uint8_t v___x_1706_; 
v_val_1705_ = lean_ctor_get(v_fst_1703_, 0);
lean_inc(v_val_1705_);
lean_dec_ref_known(v_fst_1703_, 1);
v___x_1706_ = lean_unbox(v_val_1705_);
lean_dec(v_val_1705_);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___boxed(lean_object* v_m_1707_, lean_object* v_p_1708_){
_start:
{
uint8_t v_res_1709_; lean_object* v_r_1710_; 
v_res_1709_ = l_Std_HashMap_any___redArg(v_m_1707_, v_p_1708_);
v_r_1710_ = lean_box(v_res_1709_);
return v_r_1710_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_any(lean_object* v_00_u03b1_1711_, lean_object* v_00_u03b2_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_, lean_object* v_m_1715_, lean_object* v_p_1716_){
_start:
{
lean_object* v___x_1717_; lean_object* v_buckets_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___f_1721_; lean_object* v___f_1722_; size_t v_sz_1723_; size_t v___x_1724_; lean_object* v___x_1725_; lean_object* v_fst_1726_; 
v___x_1717_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1718_ = lean_ctor_get(v_m_1715_, 1);
lean_inc_ref(v_buckets_1718_);
lean_dec_ref(v_m_1715_);
v___x_1719_ = lean_box(0);
v___x_1720_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1721_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1721_, 0, v_p_1716_);
lean_closure_set(v___f_1721_, 1, v___x_1720_);
lean_closure_set(v___f_1721_, 2, v___x_1719_);
v___f_1722_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1722_, 0, v___x_1717_);
lean_closure_set(v___f_1722_, 1, v___f_1721_);
v_sz_1723_ = lean_array_size(v_buckets_1718_);
v___x_1724_ = ((size_t)0ULL);
v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1717_, v_buckets_1718_, v___f_1722_, v_sz_1723_, v___x_1724_, v___x_1720_);
v_fst_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_fst_1726_);
lean_dec(v___x_1725_);
if (lean_obj_tag(v_fst_1726_) == 0)
{
uint8_t v___x_1727_; 
v___x_1727_ = 0;
return v___x_1727_;
}
else
{
lean_object* v_val_1728_; uint8_t v___x_1729_; 
v_val_1728_ = lean_ctor_get(v_fst_1726_, 0);
lean_inc(v_val_1728_);
lean_dec_ref_known(v_fst_1726_, 1);
v___x_1729_ = lean_unbox(v_val_1728_);
lean_dec(v_val_1728_);
return v___x_1729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___boxed(lean_object* v_00_u03b1_1730_, lean_object* v_00_u03b2_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_, lean_object* v_m_1734_, lean_object* v_p_1735_){
_start:
{
uint8_t v_res_1736_; lean_object* v_r_1737_; 
v_res_1736_ = l_Std_HashMap_any(v_00_u03b1_1730_, v_00_u03b2_1731_, v_x_1732_, v_x_1733_, v_m_1734_, v_p_1735_);
lean_dec_ref(v_x_1733_);
lean_dec_ref(v_x_1732_);
v_r_1737_ = lean_box(v_res_1736_);
return v_r_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__0(lean_object* v_inst_1738_, lean_object* v_inst_1739_, lean_object* v_a_1740_, lean_object* v_b_1741_, lean_object* v_acc_1742_){
_start:
{
lean_object* v_r_1743_; lean_object* v___x_1744_; 
v_r_1743_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_inst_1738_, v_inst_1739_, v_acc_1742_, v_a_1740_, v_b_1741_);
v___x_1744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_r_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__1(lean_object* v___x_1745_, lean_object* v___f_1746_, lean_object* v_a_1747_, lean_object* v_x_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v___x_1750_; 
v___x_1750_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v___x_1745_, v___f_1746_, v_a_1747_, v___y_1749_);
return v___x_1750_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg(lean_object* v_inst_1753_, lean_object* v_inst_1754_, lean_object* v_m_u2081_1755_, lean_object* v_m_u2082_1756_){
_start:
{
lean_object* v___x_1757_; lean_object* v_size_1758_; lean_object* v_buckets_1759_; lean_object* v_size_1760_; uint8_t v___x_1761_; 
v___x_1757_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_size_1758_ = lean_ctor_get(v_m_u2081_1755_, 0);
v_buckets_1759_ = lean_ctor_get(v_m_u2081_1755_, 1);
v_size_1760_ = lean_ctor_get(v_m_u2082_1756_, 0);
v___x_1761_ = lean_nat_dec_le(v_size_1758_, v_size_1760_);
if (v___x_1761_ == 0)
{
lean_object* v___f_1762_; lean_object* v___x_1763_; 
v___f_1762_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1763_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1762_, v_inst_1753_, v_inst_1754_, v_m_u2081_1755_, v_m_u2082_1756_);
return v___x_1763_;
}
else
{
lean_object* v___f_1764_; lean_object* v___f_1765_; size_t v_sz_1766_; size_t v___x_1767_; lean_object* v___x_1768_; 
lean_inc_ref(v_buckets_1759_);
lean_dec_ref(v_m_u2081_1755_);
v___f_1764_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1764_, 0, v_inst_1753_);
lean_closure_set(v___f_1764_, 1, v_inst_1754_);
v___f_1765_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1765_, 0, v___x_1757_);
lean_closure_set(v___f_1765_, 1, v___f_1764_);
v_sz_1766_ = lean_array_size(v_buckets_1759_);
v___x_1767_ = ((size_t)0ULL);
v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1757_, v_buckets_1759_, v___f_1765_, v_sz_1766_, v___x_1767_, v_m_u2082_1756_);
return v___x_1768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union(lean_object* v_00_u03b1_1769_, lean_object* v_00_u03b2_1770_, lean_object* v_inst_1771_, lean_object* v_inst_1772_, lean_object* v_m_u2081_1773_, lean_object* v_m_u2082_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v_size_1776_; lean_object* v_buckets_1777_; lean_object* v_size_1778_; uint8_t v___x_1779_; 
v___x_1775_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_size_1776_ = lean_ctor_get(v_m_u2081_1773_, 0);
v_buckets_1777_ = lean_ctor_get(v_m_u2081_1773_, 1);
v_size_1778_ = lean_ctor_get(v_m_u2082_1774_, 0);
v___x_1779_ = lean_nat_dec_le(v_size_1776_, v_size_1778_);
if (v___x_1779_ == 0)
{
lean_object* v___f_1780_; lean_object* v___x_1781_; 
v___f_1780_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1781_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1780_, v_inst_1771_, v_inst_1772_, v_m_u2081_1773_, v_m_u2082_1774_);
return v___x_1781_;
}
else
{
lean_object* v___f_1782_; lean_object* v___f_1783_; size_t v_sz_1784_; size_t v___x_1785_; lean_object* v___x_1786_; 
lean_inc_ref(v_buckets_1777_);
lean_dec_ref(v_m_u2081_1773_);
v___f_1782_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1782_, 0, v_inst_1771_);
lean_closure_set(v___f_1782_, 1, v_inst_1772_);
v___f_1783_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1783_, 0, v___x_1775_);
lean_closure_set(v___f_1783_, 1, v___f_1782_);
v_sz_1784_ = lean_array_size(v_buckets_1777_);
v___x_1785_ = ((size_t)0ULL);
v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1775_, v_buckets_1777_, v___f_1783_, v_sz_1784_, v___x_1785_, v_m_u2082_1774_);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion___redArg(lean_object* v_inst_1787_, lean_object* v_inst_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = lean_alloc_closure((void*)(l_Std_HashMap_union), 6, 4);
lean_closure_set(v___x_1789_, 0, lean_box(0));
lean_closure_set(v___x_1789_, 1, lean_box(0));
lean_closure_set(v___x_1789_, 2, v_inst_1787_);
lean_closure_set(v___x_1789_, 3, v_inst_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion(lean_object* v_00_u03b1_1790_, lean_object* v_00_u03b2_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_alloc_closure((void*)(l_Std_HashMap_union), 6, 4);
lean_closure_set(v___x_1794_, 0, lean_box(0));
lean_closure_set(v___x_1794_, 1, lean_box(0));
lean_closure_set(v___x_1794_, 2, v_inst_1792_);
lean_closure_set(v___x_1794_, 3, v_inst_1793_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_inter___redArg(lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_m_u2081_1797_, lean_object* v_m_u2082_1798_){
_start:
{
lean_object* v___x_1799_; 
v___x_1799_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1795_, v_inst_1796_, v_m_u2081_1797_, v_m_u2082_1798_);
return v___x_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_inter(lean_object* v_00_u03b1_1800_, lean_object* v_00_u03b2_1801_, lean_object* v_inst_1802_, lean_object* v_inst_1803_, lean_object* v_m_u2081_1804_, lean_object* v_m_u2082_1805_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1802_, v_inst_1803_, v_m_u2081_1804_, v_m_u2082_1805_);
return v___x_1806_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInter___redArg(lean_object* v_inst_1807_, lean_object* v_inst_1808_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = lean_alloc_closure((void*)(l_Std_HashMap_inter), 6, 4);
lean_closure_set(v___x_1809_, 0, lean_box(0));
lean_closure_set(v___x_1809_, 1, lean_box(0));
lean_closure_set(v___x_1809_, 2, v_inst_1807_);
lean_closure_set(v___x_1809_, 3, v_inst_1808_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInter(lean_object* v_00_u03b1_1810_, lean_object* v_00_u03b2_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_){
_start:
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_closure((void*)(l_Std_HashMap_inter), 6, 4);
lean_closure_set(v___x_1814_, 0, lean_box(0));
lean_closure_set(v___x_1814_, 1, lean_box(0));
lean_closure_set(v___x_1814_, 2, v_inst_1812_);
lean_closure_set(v___x_1814_, 3, v_inst_1813_);
return v___x_1814_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq___redArg(lean_object* v_x_1815_, lean_object* v_inst_1816_, lean_object* v_inst_1817_, lean_object* v_m_u2081_1818_, lean_object* v_m_u2082_1819_){
_start:
{
uint8_t v___x_1820_; 
v___x_1820_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1816_, v_x_1815_, v_inst_1817_, v_m_u2081_1818_, v_m_u2082_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___redArg___boxed(lean_object* v_x_1821_, lean_object* v_inst_1822_, lean_object* v_inst_1823_, lean_object* v_m_u2081_1824_, lean_object* v_m_u2082_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l_Std_HashMap_beq___redArg(v_x_1821_, v_inst_1822_, v_inst_1823_, v_m_u2081_1824_, v_m_u2082_1825_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq(lean_object* v_00_u03b1_1828_, lean_object* v_x_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_inst_1831_, lean_object* v_inst_1832_, lean_object* v_m_u2081_1833_, lean_object* v_m_u2082_1834_){
_start:
{
uint8_t v___x_1835_; 
v___x_1835_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1831_, v_x_1829_, v_inst_1832_, v_m_u2081_1833_, v_m_u2082_1834_);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___boxed(lean_object* v_00_u03b1_1836_, lean_object* v_x_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_m_u2081_1841_, lean_object* v_m_u2082_1842_){
_start:
{
uint8_t v_res_1843_; lean_object* v_r_1844_; 
v_res_1843_ = l_Std_HashMap_beq(v_00_u03b1_1836_, v_x_1837_, v_00_u03b2_1838_, v_inst_1839_, v_inst_1840_, v_m_u2081_1841_, v_m_u2082_1842_);
v_r_1844_ = lean_box(v_res_1843_);
return v_r_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq___redArg(lean_object* v_x_1845_, lean_object* v_inst_1846_, lean_object* v_inst_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_1848_, 0, lean_box(0));
lean_closure_set(v___x_1848_, 1, v_x_1845_);
lean_closure_set(v___x_1848_, 2, lean_box(0));
lean_closure_set(v___x_1848_, 3, v_inst_1846_);
lean_closure_set(v___x_1848_, 4, v_inst_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq(lean_object* v_00_u03b1_1849_, lean_object* v_00_u03b2_1850_, lean_object* v_x_1851_, lean_object* v_inst_1852_, lean_object* v_inst_1853_){
_start:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_1854_, 0, lean_box(0));
lean_closure_set(v___x_1854_, 1, v_x_1851_);
lean_closure_set(v___x_1854_, 2, lean_box(0));
lean_closure_set(v___x_1854_, 3, v_inst_1852_);
lean_closure_set(v___x_1854_, 4, v_inst_1853_);
return v___x_1854_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_diff___redArg___lam__0(lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_m_u2082_1857_, uint8_t v___x_1858_, lean_object* v_k_1859_, lean_object* v_x_1860_){
_start:
{
uint8_t v___x_1861_; 
v___x_1861_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1855_, v_inst_1856_, v_m_u2082_1857_, v_k_1859_);
if (v___x_1861_ == 0)
{
return v___x_1858_;
}
else
{
uint8_t v___x_1862_; 
v___x_1862_ = 0;
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg___lam__0___boxed(lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_m_u2082_1865_, lean_object* v___x_1866_, lean_object* v_k_1867_, lean_object* v_x_1868_){
_start:
{
uint8_t v___x_81__boxed_1869_; uint8_t v_res_1870_; lean_object* v_r_1871_; 
v___x_81__boxed_1869_ = lean_unbox(v___x_1866_);
v_res_1870_ = l_Std_HashMap_diff___redArg___lam__0(v_inst_1863_, v_inst_1864_, v_m_u2082_1865_, v___x_81__boxed_1869_, v_k_1867_, v_x_1868_);
lean_dec(v_x_1868_);
lean_dec_ref(v_m_u2082_1865_);
v_r_1871_ = lean_box(v_res_1870_);
return v_r_1871_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg(lean_object* v_inst_1872_, lean_object* v_inst_1873_, lean_object* v_m_u2081_1874_, lean_object* v_m_u2082_1875_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_diff(lean_object* v_00_u03b1_1884_, lean_object* v_00_u03b2_1885_, lean_object* v_inst_1886_, lean_object* v_inst_1887_, lean_object* v_m_u2081_1888_, lean_object* v_m_u2082_1889_){
_start:
{
lean_object* v_size_1890_; lean_object* v_size_1891_; uint8_t v___x_1892_; 
v_size_1890_ = lean_ctor_get(v_m_u2081_1888_, 0);
v_size_1891_ = lean_ctor_get(v_m_u2082_1889_, 0);
v___x_1892_ = lean_nat_dec_le(v_size_1890_, v_size_1891_);
if (v___x_1892_ == 0)
{
lean_object* v___f_1893_; lean_object* v___x_1894_; 
v___f_1893_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1894_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1893_, v_inst_1886_, v_inst_1887_, v_m_u2081_1888_, v_m_u2082_1889_);
return v___x_1894_;
}
else
{
lean_object* v___x_1895_; lean_object* v___f_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_box(v___x_1892_);
v___f_1896_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1896_, 0, v_inst_1886_);
lean_closure_set(v___f_1896_, 1, v_inst_1887_);
lean_closure_set(v___f_1896_, 2, v_m_u2082_1889_);
lean_closure_set(v___f_1896_, 3, v___x_1895_);
v___x_1897_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1896_, v_m_u2081_1888_);
return v___x_1897_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff___redArg(lean_object* v_inst_1898_, lean_object* v_inst_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_1900_, 0, lean_box(0));
lean_closure_set(v___x_1900_, 1, lean_box(0));
lean_closure_set(v___x_1900_, 2, v_inst_1898_);
lean_closure_set(v___x_1900_, 3, v_inst_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff(lean_object* v_00_u03b1_1901_, lean_object* v_00_u03b2_1902_, lean_object* v_inst_1903_, lean_object* v_inst_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_1905_, 0, lean_box(0));
lean_closure_set(v___x_1905_, 1, lean_box(0));
lean_closure_set(v___x_1905_, 2, v_inst_1903_);
lean_closure_set(v___x_1905_, 3, v_inst_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__0(lean_object* v_f_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_, lean_object* v_x1_1909_, lean_object* v_x2_1910_, lean_object* v_x3_1911_){
_start:
{
lean_object* v_fst_1912_; lean_object* v_snd_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1927_; 
v_fst_1912_ = lean_ctor_get(v_x1_1909_, 0);
v_snd_1913_ = lean_ctor_get(v_x1_1909_, 1);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_x1_1909_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1915_ = v_x1_1909_;
v_isShared_1916_ = v_isSharedCheck_1927_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_snd_1913_);
lean_inc(v_fst_1912_);
lean_dec(v_x1_1909_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1927_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; uint8_t v___x_1918_; 
lean_inc(v_x3_1911_);
lean_inc(v_x2_1910_);
v___x_1917_ = lean_apply_2(v_f_1906_, v_x2_1910_, v_x3_1911_);
v___x_1918_ = lean_unbox(v___x_1917_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; lean_object* v___x_1921_; 
v___x_1919_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1907_, v_x_1908_, v_snd_1913_, v_x2_1910_, v_x3_1911_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v___x_1919_);
v___x_1921_ = v___x_1915_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_fst_1912_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v___x_1919_);
v___x_1921_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
return v___x_1921_;
}
}
else
{
lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1923_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1907_, v_x_1908_, v_fst_1912_, v_x2_1910_, v_x3_1911_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 0, v___x_1923_);
v___x_1925_ = v___x_1915_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_snd_1913_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__1(lean_object* v___x_1928_, lean_object* v___f_1929_, lean_object* v_acc_1930_, lean_object* v_l_1931_){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1928_, v___f_1929_, v_acc_1930_, v_l_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l_Std_HashMap_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1933_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg(lean_object* v_x_1935_, lean_object* v_x_1936_, lean_object* v_f_1937_, lean_object* v_m_1938_){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v_buckets_1942_; lean_object* v___x_1943_; uint8_t v___x_1944_; 
v___x_1939_ = lean_unsigned_to_nat(0u);
v___x_1940_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_1941_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1942_ = lean_ctor_get(v_m_1938_, 1);
lean_inc_ref(v_buckets_1942_);
lean_dec_ref(v_m_1938_);
v___x_1943_ = lean_array_get_size(v_buckets_1942_);
v___x_1944_ = lean_nat_dec_lt(v___x_1939_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_dec_ref(v_buckets_1942_);
lean_dec_ref(v_f_1937_);
lean_dec_ref(v_x_1936_);
lean_dec_ref(v_x_1935_);
return v___x_1940_;
}
else
{
lean_object* v___f_1945_; lean_object* v___f_1946_; size_t v___x_1947_; size_t v___x_1948_; lean_object* v___x_1949_; lean_object* v_fst_1950_; lean_object* v_snd_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
v___f_1945_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1945_, 0, v_f_1937_);
lean_closure_set(v___f_1945_, 1, v_x_1935_);
lean_closure_set(v___f_1945_, 2, v_x_1936_);
v___f_1946_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1946_, 0, v___x_1941_);
lean_closure_set(v___f_1946_, 1, v___f_1945_);
v___x_1947_ = ((size_t)0ULL);
v___x_1948_ = lean_usize_of_nat(v___x_1943_);
v___x_1949_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1941_, v___f_1946_, v_buckets_1942_, v___x_1947_, v___x_1948_, v___x_1940_);
v_fst_1950_ = lean_ctor_get(v___x_1949_, 0);
v_snd_1951_ = lean_ctor_get(v___x_1949_, 1);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1949_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1949_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_snd_1951_);
lean_inc(v_fst_1950_);
lean_dec(v___x_1949_);
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
LEAN_EXPORT lean_object* l_Std_HashMap_partition(lean_object* v_00_u03b1_1959_, lean_object* v_00_u03b2_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_, lean_object* v_f_1963_, lean_object* v_m_1964_){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v_buckets_1968_; lean_object* v___x_1969_; uint8_t v___x_1970_; 
v___x_1965_ = lean_unsigned_to_nat(0u);
v___x_1966_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_1967_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1968_ = lean_ctor_get(v_m_1964_, 1);
lean_inc_ref(v_buckets_1968_);
lean_dec_ref(v_m_1964_);
v___x_1969_ = lean_array_get_size(v_buckets_1968_);
v___x_1970_ = lean_nat_dec_lt(v___x_1965_, v___x_1969_);
if (v___x_1970_ == 0)
{
lean_dec_ref(v_buckets_1968_);
lean_dec_ref(v_f_1963_);
lean_dec_ref(v_x_1962_);
lean_dec_ref(v_x_1961_);
return v___x_1966_;
}
else
{
lean_object* v___f_1971_; lean_object* v___f_1972_; size_t v___x_1973_; size_t v___x_1974_; lean_object* v___x_1975_; lean_object* v_fst_1976_; lean_object* v_snd_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1984_; 
v___f_1971_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1971_, 0, v_f_1963_);
lean_closure_set(v___f_1971_, 1, v_x_1961_);
lean_closure_set(v___f_1971_, 2, v_x_1962_);
v___f_1972_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1972_, 0, v___x_1967_);
lean_closure_set(v___f_1972_, 1, v___f_1971_);
v___x_1973_ = ((size_t)0ULL);
v___x_1974_ = lean_usize_of_nat(v___x_1969_);
v___x_1975_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1967_, v___f_1972_, v_buckets_1968_, v___x_1973_, v___x_1974_, v___x_1966_);
v_fst_1976_ = lean_ctor_get(v___x_1975_, 0);
v_snd_1977_ = lean_ctor_get(v___x_1975_, 1);
v_isSharedCheck_1984_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1979_ = v___x_1975_;
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_snd_1977_);
lean_inc(v_fst_1976_);
lean_dec(v___x_1975_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1984_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v___x_1982_; 
if (v_isShared_1980_ == 0)
{
v___x_1982_ = v___x_1979_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_fst_1976_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_snd_1977_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0(lean_object* v_a_1985_, lean_object* v_b_1986_, lean_object* v_d_1987_){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1988_, 0, v_b_1986_);
lean_ctor_set(v___x_1988_, 1, v_d_1987_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0___boxed(lean_object* v_a_1989_, lean_object* v_b_1990_, lean_object* v_d_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_Std_HashMap_values___redArg___lam__0(v_a_1989_, v_b_1990_, v_d_1991_);
lean_dec(v_a_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg(lean_object* v_m_1997_){
_start:
{
lean_object* v___x_1998_; lean_object* v_buckets_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; uint8_t v___x_2003_; 
v___x_1998_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1999_ = lean_ctor_get(v_m_1997_, 1);
lean_inc_ref(v_buckets_1999_);
lean_dec_ref(v_m_1997_);
v___x_2000_ = lean_box(0);
v___x_2001_ = lean_array_get_size(v_buckets_1999_);
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = lean_nat_dec_lt(v___x_2002_, v___x_2001_);
if (v___x_2003_ == 0)
{
lean_dec_ref(v_buckets_1999_);
return v___x_2000_;
}
else
{
lean_object* v___f_2004_; size_t v___x_2005_; size_t v___x_2006_; lean_object* v___x_2007_; 
v___f_2004_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__1));
v___x_2005_ = lean_usize_of_nat(v___x_2001_);
v___x_2006_ = ((size_t)0ULL);
v___x_2007_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1998_, v___f_2004_, v_buckets_1999_, v___x_2005_, v___x_2006_, v___x_2000_);
return v___x_2007_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values(lean_object* v_00_u03b1_2008_, lean_object* v_00_u03b2_2009_, lean_object* v_x_2010_, lean_object* v_x_2011_, lean_object* v_m_2012_){
_start:
{
lean_object* v___x_2013_; lean_object* v_buckets_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2013_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2014_ = lean_ctor_get(v_m_2012_, 1);
lean_inc_ref(v_buckets_2014_);
lean_dec_ref(v_m_2012_);
v___x_2015_ = lean_box(0);
v___x_2016_ = lean_array_get_size(v_buckets_2014_);
v___x_2017_ = lean_unsigned_to_nat(0u);
v___x_2018_ = lean_nat_dec_lt(v___x_2017_, v___x_2016_);
if (v___x_2018_ == 0)
{
lean_dec_ref(v_buckets_2014_);
return v___x_2015_;
}
else
{
lean_object* v___f_2019_; size_t v___x_2020_; size_t v___x_2021_; lean_object* v___x_2022_; 
v___f_2019_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__1));
v___x_2020_ = lean_usize_of_nat(v___x_2016_);
v___x_2021_ = ((size_t)0ULL);
v___x_2022_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2013_, v___f_2019_, v_buckets_2014_, v___x_2020_, v___x_2021_, v___x_2015_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___boxed(lean_object* v_00_u03b1_2023_, lean_object* v_00_u03b2_2024_, lean_object* v_x_2025_, lean_object* v_x_2026_, lean_object* v_m_2027_){
_start:
{
lean_object* v_res_2028_; 
v_res_2028_ = l_Std_HashMap_values(v_00_u03b1_2023_, v_00_u03b2_2024_, v_x_2025_, v_x_2026_, v_m_2027_);
lean_dec_ref(v_x_2026_);
lean_dec_ref(v_x_2025_);
return v_res_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0(lean_object* v_x1_2029_, lean_object* v_x2_2030_, lean_object* v_x3_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = lean_array_push(v_x1_2029_, v_x3_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2033_, lean_object* v_x2_2034_, lean_object* v_x3_2035_){
_start:
{
lean_object* v_res_2036_; 
v_res_2036_ = l_Std_HashMap_valuesArray___redArg___lam__0(v_x1_2033_, v_x2_2034_, v_x3_2035_);
lean_dec(v_x2_2034_);
return v_res_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg(lean_object* v_m_2041_){
_start:
{
lean_object* v_size_2042_; lean_object* v_buckets_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; uint8_t v___x_2048_; 
v_size_2042_ = lean_ctor_get(v_m_2041_, 0);
lean_inc(v_size_2042_);
v_buckets_2043_ = lean_ctor_get(v_m_2041_, 1);
lean_inc_ref(v_buckets_2043_);
lean_dec_ref(v_m_2041_);
v___x_2044_ = lean_mk_empty_array_with_capacity(v_size_2042_);
lean_dec(v_size_2042_);
v___x_2045_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_2046_ = lean_unsigned_to_nat(0u);
v___x_2047_ = lean_array_get_size(v_buckets_2043_);
v___x_2048_ = lean_nat_dec_lt(v___x_2046_, v___x_2047_);
if (v___x_2048_ == 0)
{
lean_dec_ref(v_buckets_2043_);
return v___x_2044_;
}
else
{
lean_object* v___f_2049_; size_t v___x_2050_; size_t v___x_2051_; lean_object* v___x_2052_; 
v___f_2049_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__1));
v___x_2050_ = ((size_t)0ULL);
v___x_2051_ = lean_usize_of_nat(v___x_2047_);
v___x_2052_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2045_, v___f_2049_, v_buckets_2043_, v___x_2050_, v___x_2051_, v___x_2044_);
return v___x_2052_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray(lean_object* v_00_u03b1_2053_, lean_object* v_00_u03b2_2054_, lean_object* v_x_2055_, lean_object* v_x_2056_, lean_object* v_m_2057_){
_start:
{
lean_object* v_size_2058_; lean_object* v_buckets_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v_size_2058_ = lean_ctor_get(v_m_2057_, 0);
lean_inc(v_size_2058_);
v_buckets_2059_ = lean_ctor_get(v_m_2057_, 1);
lean_inc_ref(v_buckets_2059_);
lean_dec_ref(v_m_2057_);
v___x_2060_ = lean_mk_empty_array_with_capacity(v_size_2058_);
lean_dec(v_size_2058_);
v___x_2061_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_2062_ = lean_unsigned_to_nat(0u);
v___x_2063_ = lean_array_get_size(v_buckets_2059_);
v___x_2064_ = lean_nat_dec_lt(v___x_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_dec_ref(v_buckets_2059_);
return v___x_2060_;
}
else
{
lean_object* v___f_2065_; size_t v___x_2066_; size_t v___x_2067_; lean_object* v___x_2068_; 
v___f_2065_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__1));
v___x_2066_ = ((size_t)0ULL);
v___x_2067_ = lean_usize_of_nat(v___x_2063_);
v___x_2068_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2061_, v___f_2065_, v_buckets_2059_, v___x_2066_, v___x_2067_, v___x_2060_);
return v___x_2068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_00_u03b2_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v_m_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Std_HashMap_valuesArray(v_00_u03b1_2069_, v_00_u03b2_2070_, v_x_2071_, v_x_2072_, v_m_2073_);
lean_dec_ref(v_x_2072_);
lean_dec_ref(v_x_2071_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray___redArg(lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_l_2077_){
_start:
{
lean_object* v___f_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___f_2078_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2079_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_2080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2078_, v_inst_2075_, v_inst_2076_, v___x_2079_, v_l_2077_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray(lean_object* v_00_u03b1_2081_, lean_object* v_inst_2082_, lean_object* v_inst_2083_, lean_object* v_l_2084_){
_start:
{
lean_object* v___f_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___f_2085_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2086_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_2087_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2085_, v_inst_2082_, v_inst_2083_, v___x_2086_, v_l_2084_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg(lean_object* v_m_2088_){
_start:
{
lean_object* v___x_2089_; 
v___x_2089_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2088_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg___boxed(lean_object* v_m_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Std_HashMap_Internal_numBuckets___redArg(v_m_2090_);
lean_dec_ref(v_m_2090_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets(lean_object* v_00_u03b1_2092_, lean_object* v_00_u03b2_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_, lean_object* v_m_2096_){
_start:
{
lean_object* v___x_2097_; 
v___x_2097_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2096_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2098_, lean_object* v_00_u03b2_2099_, lean_object* v_x_2100_, lean_object* v_x_2101_, lean_object* v_m_2102_){
_start:
{
lean_object* v_res_2103_; 
v_res_2103_ = l_Std_HashMap_Internal_numBuckets(v_00_u03b1_2098_, v_00_u03b2_2099_, v_x_2100_, v_x_2101_, v_m_2102_);
lean_dec_ref(v_m_2102_);
lean_dec_ref(v_x_2101_);
lean_dec_ref(v_x_2100_);
return v_res_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2(lean_object* v___x_2107_, lean_object* v___f_2108_, lean_object* v_m_2109_, lean_object* v_prec_2110_){
_start:
{
lean_object* v___x_2111_; lean_object* v_buckets_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2132_; 
v___x_2111_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2112_ = lean_ctor_get(v_m_2109_, 1);
v_isSharedCheck_2132_ = !lean_is_exclusive(v_m_2109_);
if (v_isSharedCheck_2132_ == 0)
{
lean_object* v_unused_2133_; 
v_unused_2133_ = lean_ctor_get(v_m_2109_, 0);
lean_dec(v_unused_2133_);
v___x_2114_ = v_m_2109_;
v_isShared_2115_ = v_isSharedCheck_2132_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_buckets_2112_);
lean_dec(v_m_2109_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2132_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___y_2118_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; uint8_t v___x_2127_; 
v___x_2116_ = ((lean_object*)(l_Std_HashMap_instRepr___redArg___lam__2___closed__1));
v___x_2124_ = lean_box(0);
v___x_2125_ = lean_array_get_size(v_buckets_2112_);
v___x_2126_ = lean_unsigned_to_nat(0u);
v___x_2127_ = lean_nat_dec_lt(v___x_2126_, v___x_2125_);
if (v___x_2127_ == 0)
{
lean_dec_ref(v_buckets_2112_);
lean_dec_ref(v___f_2108_);
v___y_2118_ = v___x_2124_;
goto v___jp_2117_;
}
else
{
lean_object* v___f_2128_; size_t v___x_2129_; size_t v___x_2130_; lean_object* v___x_2131_; 
v___f_2128_ = lean_alloc_closure((void*)(l_Std_HashMap_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2128_, 0, v___x_2111_);
lean_closure_set(v___f_2128_, 1, v___f_2108_);
v___x_2129_ = lean_usize_of_nat(v___x_2125_);
v___x_2130_ = ((size_t)0ULL);
v___x_2131_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2111_, v___f_2128_, v_buckets_2112_, v___x_2129_, v___x_2130_, v___x_2124_);
v___y_2118_ = v___x_2131_;
goto v___jp_2117_;
}
v___jp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2119_ = l_List_repr___redArg(v___x_2107_, v___y_2118_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set_tag(v___x_2114_, 5);
lean_ctor_set(v___x_2114_, 1, v___x_2119_);
lean_ctor_set(v___x_2114_, 0, v___x_2116_);
v___x_2121_ = v___x_2114_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Repr_addAppParen(v___x_2121_, v_prec_2110_);
return v___x_2122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2___boxed(lean_object* v___x_2134_, lean_object* v___f_2135_, lean_object* v_m_2136_, lean_object* v_prec_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Std_HashMap_instRepr___redArg___lam__2(v___x_2134_, v___f_2135_, v_m_2136_, v_prec_2137_);
lean_dec(v_prec_2137_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg(lean_object* v_inst_2139_, lean_object* v_inst_2140_){
_start:
{
lean_object* v___f_2141_; lean_object* v___f_2142_; lean_object* v___x_2143_; lean_object* v___f_2144_; 
v___f_2141_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__0));
v___f_2142_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2142_, 0, v_inst_2140_);
v___x_2143_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2143_, 0, lean_box(0));
lean_closure_set(v___x_2143_, 1, lean_box(0));
lean_closure_set(v___x_2143_, 2, v_inst_2139_);
lean_closure_set(v___x_2143_, 3, v___f_2142_);
v___f_2144_ = lean_alloc_closure((void*)(l_Std_HashMap_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2144_, 0, v___x_2143_);
lean_closure_set(v___f_2144_, 1, v___f_2141_);
return v___f_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr(lean_object* v_00_u03b1_2145_, lean_object* v_00_u03b2_2146_, lean_object* v_inst_2147_, lean_object* v_inst_2148_, lean_object* v_inst_2149_, lean_object* v_inst_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Std_HashMap_instRepr___redArg(v_inst_2149_, v_inst_2150_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___boxed(lean_object* v_00_u03b1_2152_, lean_object* v_00_u03b2_2153_, lean_object* v_inst_2154_, lean_object* v_inst_2155_, lean_object* v_inst_2156_, lean_object* v_inst_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Std_HashMap_instRepr(v_00_u03b1_2152_, v_00_u03b2_2153_, v_inst_2154_, v_inst_2155_, v_inst_2156_, v_inst_2157_);
lean_dec_ref(v_inst_2155_);
lean_dec_ref(v_inst_2154_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__0(lean_object* v_a_2161_, lean_object* v_x_2162_){
_start:
{
lean_object* v___y_2164_; 
if (lean_obj_tag(v_x_2162_) == 0)
{
lean_object* v___x_2167_; 
v___x_2167_ = ((lean_object*)(l_Array_groupByKey___redArg___lam__0___closed__0));
v___y_2164_ = v___x_2167_;
goto v___jp_2163_;
}
else
{
lean_object* v_val_2168_; 
v_val_2168_ = lean_ctor_get(v_x_2162_, 0);
lean_inc(v_val_2168_);
lean_dec_ref_known(v_x_2162_, 1);
v___y_2164_ = v_val_2168_;
goto v___jp_2163_;
}
v___jp_2163_:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_array_push(v___y_2164_, v_a_2161_);
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__1(lean_object* v_key_2169_, lean_object* v_inst_2170_, lean_object* v_inst_2171_, lean_object* v_a_2172_, lean_object* v_x_2173_, lean_object* v___y_2174_){
_start:
{
lean_object* v___f_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_inc(v_a_2172_);
v___f_2175_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2175_, 0, v_a_2172_);
v___x_2176_ = lean_apply_1(v_key_2169_, v_a_2172_);
v___x_2177_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_2170_, v_inst_2171_, v___y_2174_, v___x_2176_, v___f_2175_);
v___x_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2177_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg(lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_key_2181_, lean_object* v_xs_2182_){
_start:
{
lean_object* v___f_2183_; lean_object* v___x_2184_; lean_object* v_groups_2185_; size_t v_sz_2186_; size_t v___x_2187_; lean_object* v___x_2188_; 
v___f_2183_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__1), 6, 3);
lean_closure_set(v___f_2183_, 0, v_key_2181_);
lean_closure_set(v___f_2183_, 1, v_inst_2179_);
lean_closure_set(v___f_2183_, 2, v_inst_2180_);
v___x_2184_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_groups_2185_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v_sz_2186_ = lean_array_size(v_xs_2182_);
v___x_2187_ = ((size_t)0ULL);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2184_, v_xs_2182_, v___f_2183_, v_sz_2186_, v___x_2187_, v_groups_2185_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey(lean_object* v_00_u03b1_2189_, lean_object* v_00_u03b2_2190_, lean_object* v_inst_2191_, lean_object* v_inst_2192_, lean_object* v_key_2193_, lean_object* v_xs_2194_){
_start:
{
lean_object* v___x_2195_; 
v___x_2195_ = l_Array_groupByKey___redArg(v_inst_2191_, v_inst_2192_, v_key_2193_, v_xs_2194_);
return v___x_2195_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__0(lean_object* v_x_2196_, lean_object* v_v_2197_){
_start:
{
lean_object* v___y_2199_; 
if (lean_obj_tag(v_v_2197_) == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_box(0);
v___y_2199_ = v___x_2202_;
goto v___jp_2198_;
}
else
{
lean_object* v_val_2203_; 
v_val_2203_ = lean_ctor_get(v_v_2197_, 0);
lean_inc(v_val_2203_);
lean_dec_ref_known(v_v_2197_, 1);
v___y_2199_ = v_val_2203_;
goto v___jp_2198_;
}
v___jp_2198_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_x_2196_);
lean_ctor_set(v___x_2200_, 1, v___y_2199_);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__1(lean_object* v_key_2204_, lean_object* v_inst_2205_, lean_object* v_inst_2206_, lean_object* v_x_2207_, lean_object* v_acc_2208_){
_start:
{
lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_inc(v_x_2207_);
v___f_2209_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2209_, 0, v_x_2207_);
v___x_2210_ = lean_apply_1(v_key_2204_, v_x_2207_);
v___x_2211_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_2205_, v_inst_2206_, v_acc_2208_, v___x_2210_, v___f_2209_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg(lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_key_2214_, lean_object* v_xs_2215_){
_start:
{
lean_object* v___f_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___f_2216_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__1), 5, 3);
lean_closure_set(v___f_2216_, 0, v_key_2214_);
lean_closure_set(v___f_2216_, 1, v_inst_2212_);
lean_closure_set(v___f_2216_, 2, v_inst_2213_);
v___x_2217_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_2218_ = l_List_foldrTR___redArg(v___f_2216_, v___x_2217_, v_xs_2215_);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey(lean_object* v_00_u03b1_2219_, lean_object* v_00_u03b2_2220_, lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_key_2223_, lean_object* v_xs_2224_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_List_groupByKey___redArg(v_inst_2221_, v_inst_2222_, v_key_2223_, v_xs_2224_);
return v___x_2225_;
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
