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
lean_object* l_Std_HashMap_instEmptyCollection___redArg(){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
return v___x_40_;
}
}
LEAN_EXPORT void l_Std_HashMap_instEmptyCollection___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_41_;
v_res_41_ = l_Std_HashMap_instEmptyCollection___redArg();
stack->m_obj
 = v_res_41_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection___redArg___boxed(lean_object* v___dummy_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Std_HashMap_instEmptyCollection___redArg();
return v_res_43_;
}
}
static lean_object* _init_l_Std_HashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_HashMap_instEmptyCollection___redArg();
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_inst_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__0, &l_Std_HashMap_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_instEmptyCollection___closed__0);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection___boxed(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_inst_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Std_HashMap_instEmptyCollection(v_00_u03b1_50_, v_00_u03b2_51_, v_inst_52_, v_inst_53_);
lean_dec_ref(v_inst_53_);
lean_dec_ref(v_inst_52_);
return v_res_54_;
}
}
lean_object* l_Std_HashMap_instInhabited___redArg(){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
return v___x_56_;
}
}
LEAN_EXPORT void l_Std_HashMap_instInhabited___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_57_;
v_res_57_ = l_Std_HashMap_instInhabited___redArg();
stack->m_obj
 = v_res_57_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited___redArg___boxed(lean_object* v___dummy_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Std_HashMap_instInhabited___redArg();
return v_res_59_;
}
}
static lean_object* _init_l_Std_HashMap_instInhabited___closed__0(void){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = l_Std_HashMap_instInhabited___redArg();
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited(lean_object* v_00_u03b1_61_, lean_object* v_00_u03b2_62_, lean_object* v_inst_63_, lean_object* v_inst_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lean_obj_once(&l_Std_HashMap_instInhabited___closed__0, &l_Std_HashMap_instInhabited___closed__0_once, _init_l_Std_HashMap_instInhabited___closed__0);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited___boxed(lean_object* v_00_u03b1_66_, lean_object* v_00_u03b2_67_, lean_object* v_inst_68_, lean_object* v_inst_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_HashMap_instInhabited(v_00_u03b1_66_, v_00_u03b2_67_, v_inst_68_, v_inst_69_);
lean_dec_ref(v_inst_69_);
lean_dec_ref(v_inst_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear___redArg(lean_object* v_m_71_){
_start:
{
lean_object* v_size_72_; lean_object* v_buckets_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_81_; 
v_size_72_ = lean_ctor_get(v_m_71_, 0);
v_buckets_73_ = lean_ctor_get(v_m_71_, 1);
v_isSharedCheck_81_ = !lean_is_exclusive(v_m_71_);
if (v_isSharedCheck_81_ == 0)
{
v___x_75_ = v_m_71_;
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_buckets_73_);
lean_inc(v_size_72_);
lean_dec(v_m_71_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_81_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_79_; 
v___x_77_ = lean_array_mark_linear(v_buckets_73_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_77_);
v___x_79_ = v___x_75_;
goto v_reusejp_78_;
}
else
{
lean_object* v_reuseFailAlloc_80_; 
v_reuseFailAlloc_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_80_, 0, v_size_72_);
lean_ctor_set(v_reuseFailAlloc_80_, 1, v___x_77_);
v___x_79_ = v_reuseFailAlloc_80_;
goto v_reusejp_78_;
}
v_reusejp_78_:
{
return v___x_79_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear(lean_object* v_00_u03b1_82_, lean_object* v_00_u03b2_83_, lean_object* v_x_84_, lean_object* v_x_85_, lean_object* v_m_86_){
_start:
{
lean_object* v_size_87_; lean_object* v_buckets_88_; lean_object* v___x_90_; uint8_t v_isShared_91_; uint8_t v_isSharedCheck_96_; 
v_size_87_ = lean_ctor_get(v_m_86_, 0);
v_buckets_88_ = lean_ctor_get(v_m_86_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_m_86_);
if (v_isSharedCheck_96_ == 0)
{
v___x_90_ = v_m_86_;
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
else
{
lean_inc(v_buckets_88_);
lean_inc(v_size_87_);
lean_dec(v_m_86_);
v___x_90_ = lean_box(0);
v_isShared_91_ = v_isSharedCheck_96_;
goto v_resetjp_89_;
}
v_resetjp_89_:
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = lean_array_mark_linear(v_buckets_88_);
if (v_isShared_91_ == 0)
{
lean_ctor_set(v___x_90_, 1, v___x_92_);
v___x_94_ = v___x_90_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_size_87_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_markLinear___boxed(lean_object* v_00_u03b1_97_, lean_object* v_00_u03b2_98_, lean_object* v_x_99_, lean_object* v_x_100_, lean_object* v_m_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_HashMap_markLinear(v_00_u03b1_97_, v_00_u03b2_98_, v_x_99_, v_x_100_, v_m_101_);
lean_dec_ref(v_x_100_);
lean_dec_ref(v_x_99_);
return v_res_102_;
}
}
static lean_object* _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5));
v___x_142_ = l_String_toRawSubstring_x27(v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(lean_object* v_x_163_, lean_object* v_a_164_, lean_object* v_a_165_){
_start:
{
lean_object* v___x_166_; uint8_t v___x_167_; 
v___x_166_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
lean_inc(v_x_163_);
v___x_167_ = l_Lean_Syntax_isOfKind(v_x_163_, v___x_166_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_x_163_);
v___x_168_ = lean_box(1);
v___x_169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_a_165_);
return v___x_169_;
}
else
{
lean_object* v_quotContext_170_; lean_object* v_currMacroScope_171_; lean_object* v_ref_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; uint8_t v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_quotContext_170_ = lean_ctor_get(v_a_164_, 1);
v_currMacroScope_171_ = lean_ctor_get(v_a_164_, 2);
v_ref_172_ = lean_ctor_get(v_a_164_, 5);
v___x_173_ = lean_unsigned_to_nat(0u);
v___x_174_ = l_Lean_Syntax_getArg(v_x_163_, v___x_173_);
v___x_175_ = lean_unsigned_to_nat(2u);
v___x_176_ = l_Lean_Syntax_getArg(v_x_163_, v___x_175_);
lean_dec(v_x_163_);
v___x_177_ = 0;
v___x_178_ = l_Lean_SourceInfo_fromRef(v_ref_172_, v___x_177_);
v___x_179_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
v___x_180_ = lean_obj_once(&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6, &l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6_once, _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6);
v___x_181_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_171_);
lean_inc(v_quotContext_170_);
v___x_182_ = l_Lean_addMacroScope(v_quotContext_170_, v___x_181_, v_currMacroScope_171_);
v___x_183_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12));
lean_inc_n(v___x_178_, 2);
v___x_184_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_184_, 0, v___x_178_);
lean_ctor_set(v___x_184_, 1, v___x_180_);
lean_ctor_set(v___x_184_, 2, v___x_182_);
lean_ctor_set(v___x_184_, 3, v___x_183_);
v___x_185_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14));
v___x_186_ = l_Lean_Syntax_node2(v___x_178_, v___x_185_, v___x_174_, v___x_176_);
v___x_187_ = l_Lean_Syntax_node2(v___x_178_, v___x_179_, v___x_184_, v___x_186_);
v___x_188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_a_165_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___boxed(lean_object* v_x_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(v_x_189_, v_a_190_, v_a_191_);
lean_dec_ref(v_a_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(lean_object* v_x_196_, lean_object* v_a_197_, lean_object* v_a_198_){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
lean_inc(v_x_196_);
v___x_200_ = l_Lean_Syntax_isOfKind(v_x_196_, v___x_199_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_x_196_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_a_198_);
return v___x_202_;
}
else
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; 
v___x_203_ = lean_unsigned_to_nat(0u);
v___x_204_ = l_Lean_Syntax_getArg(v_x_196_, v___x_203_);
v___x_205_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1));
lean_inc(v___x_204_);
v___x_206_ = l_Lean_Syntax_isOfKind(v___x_204_, v___x_205_);
if (v___x_206_ == 0)
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v___x_204_);
lean_dec(v_x_196_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
lean_ctor_set(v___x_208_, 1, v_a_198_);
return v___x_208_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; 
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = l_Lean_Syntax_getArg(v_x_196_, v___x_209_);
lean_dec(v_x_196_);
v___x_211_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_210_);
v___x_212_ = l_Lean_Syntax_matchesNull(v___x_210_, v___x_211_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v___x_210_);
lean_dec(v___x_204_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v_a_198_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v_ref_217_; uint8_t v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_215_ = l_Lean_Syntax_getArg(v___x_210_, v___x_203_);
v___x_216_ = l_Lean_Syntax_getArg(v___x_210_, v___x_209_);
lean_dec(v___x_210_);
v_ref_217_ = l_Lean_replaceRef(v___x_204_, v_a_197_);
lean_dec(v___x_204_);
v___x_218_ = 0;
v___x_219_ = l_Lean_SourceInfo_fromRef(v_ref_217_, v___x_218_);
lean_dec(v_ref_217_);
v___x_220_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
v___x_221_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__6));
lean_inc(v___x_219_);
v___x_222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_219_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
v___x_223_ = l_Lean_Syntax_node3(v___x_219_, v___x_220_, v___x_215_, v___x_222_, v___x_216_);
v___x_224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v_a_198_);
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___boxed(lean_object* v_x_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(v_x_225_, v_a_226_, v_a_227_);
lean_dec(v_a_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___redArg(lean_object* v_x_229_, lean_object* v_x_230_, lean_object* v_m_231_, lean_object* v_a_232_, lean_object* v_b_233_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_229_, v_x_230_, v_m_231_, v_a_232_, v_b_233_);
return v___x_234_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_x_237_, lean_object* v_x_238_, lean_object* v_m_239_, lean_object* v_a_240_, lean_object* v_b_241_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_237_, v_x_238_, v_m_239_, v_a_240_, v_b_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg___lam__0(lean_object* v_x_243_, lean_object* v_x_244_, lean_object* v_x_245_){
_start:
{
lean_object* v_fst_246_; lean_object* v_snd_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_fst_246_ = lean_ctor_get(v_x_245_, 0);
lean_inc(v_fst_246_);
v_snd_247_ = lean_ctor_get(v_x_245_, 1);
lean_inc(v_snd_247_);
lean_dec_ref(v_x_245_);
v___x_248_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_249_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_243_, v_x_244_, v___x_248_, v_fst_246_, v_snd_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg(lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
lean_object* v___f_252_; 
v___f_252_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_252_, 0, v_x_250_);
lean_closure_set(v___f_252_, 1, v_x_251_);
return v___f_252_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_x_255_, lean_object* v_x_256_){
_start:
{
lean_object* v___f_257_; 
v___f_257_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_257_, 0, v_x_255_);
lean_closure_set(v___f_257_, 1, v_x_256_);
return v___f_257_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg___lam__0(lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_s_261_){
_start:
{
lean_object* v_fst_262_; lean_object* v_snd_263_; lean_object* v___x_264_; 
v_fst_262_ = lean_ctor_get(v_x_260_, 0);
lean_inc(v_fst_262_);
v_snd_263_ = lean_ctor_get(v_x_260_, 1);
lean_inc(v_snd_263_);
lean_dec_ref(v_x_260_);
v___x_264_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_258_, v_x_259_, v_s_261_, v_fst_262_, v_snd_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg(lean_object* v_x_265_, lean_object* v_x_266_){
_start:
{
lean_object* v___f_267_; 
v___f_267_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_267_, 0, v_x_265_);
lean_closure_set(v___f_267_, 1, v_x_266_);
return v___f_267_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd(lean_object* v_00_u03b1_268_, lean_object* v_00_u03b2_269_, lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
lean_object* v___f_272_; 
v___f_272_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_272_, 0, v_x_270_);
lean_closure_set(v___f_272_, 1, v_x_271_);
return v___f_272_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew___redArg(lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_m_275_, lean_object* v_a_276_, lean_object* v_b_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_273_, v_x_274_, v_m_275_, v_a_276_, v_b_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew(lean_object* v_00_u03b1_279_, lean_object* v_00_u03b2_280_, lean_object* v_x_281_, lean_object* v_x_282_, lean_object* v_m_283_, lean_object* v_a_284_, lean_object* v_b_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___redArg(v_x_281_, v_x_282_, v_m_283_, v_a_284_, v_b_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert___redArg(lean_object* v_x_287_, lean_object* v_x_288_, lean_object* v_m_289_, lean_object* v_a_290_, lean_object* v_b_291_){
_start:
{
lean_object* v_size_292_; lean_object* v_buckets_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_344_; 
v_size_292_ = lean_ctor_get(v_m_289_, 0);
v_buckets_293_ = lean_ctor_get(v_m_289_, 1);
v_isSharedCheck_344_ = !lean_is_exclusive(v_m_289_);
if (v_isSharedCheck_344_ == 0)
{
v___x_295_ = v_m_289_;
v_isShared_296_ = v_isSharedCheck_344_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_buckets_293_);
lean_inc(v_size_292_);
lean_dec(v_m_289_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_344_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_297_; lean_object* v___x_298_; uint64_t v___x_299_; uint64_t v___x_300_; uint64_t v___x_301_; uint64_t v___x_302_; uint64_t v_fold_303_; uint64_t v___x_304_; uint64_t v___x_305_; uint64_t v___x_306_; size_t v___x_307_; size_t v___x_308_; size_t v___x_309_; size_t v___x_310_; size_t v___x_311_; lean_object* v_bkt_312_; uint8_t v___x_313_; 
v___x_297_ = lean_array_get_size(v_buckets_293_);
lean_inc_ref(v_x_288_);
lean_inc_n(v_a_290_, 2);
v___x_298_ = lean_apply_1(v_x_288_, v_a_290_);
v___x_299_ = 32ULL;
v___x_300_ = lean_unbox_uint64(v___x_298_);
v___x_301_ = lean_uint64_shift_right(v___x_300_, v___x_299_);
v___x_302_ = lean_unbox_uint64(v___x_298_);
lean_dec_ref(v___x_298_);
v_fold_303_ = lean_uint64_xor(v___x_302_, v___x_301_);
v___x_304_ = 16ULL;
v___x_305_ = lean_uint64_shift_right(v_fold_303_, v___x_304_);
v___x_306_ = lean_uint64_xor(v_fold_303_, v___x_305_);
v___x_307_ = lean_uint64_to_usize(v___x_306_);
v___x_308_ = lean_usize_of_nat(v___x_297_);
v___x_309_ = ((size_t)1ULL);
v___x_310_ = lean_usize_sub(v___x_308_, v___x_309_);
v___x_311_ = lean_usize_land(v___x_307_, v___x_310_);
v_bkt_312_ = lean_array_uget_borrowed(v_buckets_293_, v___x_311_);
lean_inc(v_bkt_312_);
lean_inc_ref(v_x_287_);
v___x_313_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_287_, v_a_290_, v_bkt_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v_size_x27_315_; lean_object* v___x_316_; lean_object* v_buckets_x27_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
lean_dec_ref(v_x_287_);
v___x_314_ = lean_unsigned_to_nat(1u);
v_size_x27_315_ = lean_nat_add(v_size_292_, v___x_314_);
lean_dec(v_size_292_);
lean_inc(v_bkt_312_);
v___x_316_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_316_, 0, v_a_290_);
lean_ctor_set(v___x_316_, 1, v_b_291_);
lean_ctor_set(v___x_316_, 2, v_bkt_312_);
v_buckets_x27_317_ = lean_array_uset(v_buckets_293_, v___x_311_, v___x_316_);
v___x_318_ = lean_unsigned_to_nat(4u);
v___x_319_ = lean_nat_mul(v_size_x27_315_, v___x_318_);
v___x_320_ = lean_unsigned_to_nat(3u);
v___x_321_ = lean_nat_div(v___x_319_, v___x_320_);
lean_dec(v___x_319_);
v___x_322_ = lean_array_get_size(v_buckets_x27_317_);
v___x_323_ = lean_nat_dec_le(v___x_321_, v___x_322_);
lean_dec(v___x_321_);
if (v___x_323_ == 0)
{
lean_object* v_val_324_; lean_object* v___x_326_; 
v_val_324_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_288_, v_buckets_x27_317_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v_val_324_);
lean_ctor_set(v___x_295_, 0, v_size_x27_315_);
v___x_326_ = v___x_295_;
goto v_reusejp_325_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_size_x27_315_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_val_324_);
v___x_326_ = v_reuseFailAlloc_329_;
goto v_reusejp_325_;
}
v_reusejp_325_:
{
lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_327_ = lean_box(v___x_313_);
v___x_328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_327_);
lean_ctor_set(v___x_328_, 1, v___x_326_);
return v___x_328_;
}
}
else
{
lean_object* v___x_331_; 
lean_dec_ref(v_x_288_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v_buckets_x27_317_);
lean_ctor_set(v___x_295_, 0, v_size_x27_315_);
v___x_331_ = v___x_295_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_size_x27_315_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_buckets_x27_317_);
v___x_331_ = v_reuseFailAlloc_334_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = lean_box(v___x_313_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v___x_331_);
return v___x_333_;
}
}
}
else
{
lean_object* v___x_335_; lean_object* v_buckets_x27_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
lean_inc(v_bkt_312_);
lean_dec_ref(v_x_288_);
v___x_335_ = lean_box(0);
v_buckets_x27_336_ = lean_array_uset(v_buckets_293_, v___x_311_, v___x_335_);
v___x_337_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_287_, v_a_290_, v_b_291_, v_bkt_312_);
v___x_338_ = lean_array_uset(v_buckets_x27_336_, v___x_311_, v___x_337_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v___x_338_);
v___x_340_ = v___x_295_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_size_292_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_343_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = lean_box(v___x_313_);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert(lean_object* v_00_u03b1_345_, lean_object* v_00_u03b2_346_, lean_object* v_x_347_, lean_object* v_x_348_, lean_object* v_m_349_, lean_object* v_a_350_, lean_object* v_b_351_){
_start:
{
lean_object* v_size_352_; lean_object* v_buckets_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_404_; 
v_size_352_ = lean_ctor_get(v_m_349_, 0);
v_buckets_353_ = lean_ctor_get(v_m_349_, 1);
v_isSharedCheck_404_ = !lean_is_exclusive(v_m_349_);
if (v_isSharedCheck_404_ == 0)
{
v___x_355_ = v_m_349_;
v_isShared_356_ = v_isSharedCheck_404_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_buckets_353_);
lean_inc(v_size_352_);
lean_dec(v_m_349_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_404_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; uint64_t v___x_359_; uint64_t v___x_360_; uint64_t v___x_361_; uint64_t v___x_362_; uint64_t v_fold_363_; uint64_t v___x_364_; uint64_t v___x_365_; uint64_t v___x_366_; size_t v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v___x_371_; lean_object* v_bkt_372_; uint8_t v___x_373_; 
v___x_357_ = lean_array_get_size(v_buckets_353_);
lean_inc_ref(v_x_348_);
lean_inc_n(v_a_350_, 2);
v___x_358_ = lean_apply_1(v_x_348_, v_a_350_);
v___x_359_ = 32ULL;
v___x_360_ = lean_unbox_uint64(v___x_358_);
v___x_361_ = lean_uint64_shift_right(v___x_360_, v___x_359_);
v___x_362_ = lean_unbox_uint64(v___x_358_);
lean_dec_ref(v___x_358_);
v_fold_363_ = lean_uint64_xor(v___x_362_, v___x_361_);
v___x_364_ = 16ULL;
v___x_365_ = lean_uint64_shift_right(v_fold_363_, v___x_364_);
v___x_366_ = lean_uint64_xor(v_fold_363_, v___x_365_);
v___x_367_ = lean_uint64_to_usize(v___x_366_);
v___x_368_ = lean_usize_of_nat(v___x_357_);
v___x_369_ = ((size_t)1ULL);
v___x_370_ = lean_usize_sub(v___x_368_, v___x_369_);
v___x_371_ = lean_usize_land(v___x_367_, v___x_370_);
v_bkt_372_ = lean_array_uget_borrowed(v_buckets_353_, v___x_371_);
lean_inc(v_bkt_372_);
lean_inc_ref(v_x_347_);
v___x_373_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_347_, v_a_350_, v_bkt_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; lean_object* v_size_x27_375_; lean_object* v___x_376_; lean_object* v_buckets_x27_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
lean_dec_ref(v_x_347_);
v___x_374_ = lean_unsigned_to_nat(1u);
v_size_x27_375_ = lean_nat_add(v_size_352_, v___x_374_);
lean_dec(v_size_352_);
lean_inc(v_bkt_372_);
v___x_376_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_376_, 0, v_a_350_);
lean_ctor_set(v___x_376_, 1, v_b_351_);
lean_ctor_set(v___x_376_, 2, v_bkt_372_);
v_buckets_x27_377_ = lean_array_uset(v_buckets_353_, v___x_371_, v___x_376_);
v___x_378_ = lean_unsigned_to_nat(4u);
v___x_379_ = lean_nat_mul(v_size_x27_375_, v___x_378_);
v___x_380_ = lean_unsigned_to_nat(3u);
v___x_381_ = lean_nat_div(v___x_379_, v___x_380_);
lean_dec(v___x_379_);
v___x_382_ = lean_array_get_size(v_buckets_x27_377_);
v___x_383_ = lean_nat_dec_le(v___x_381_, v___x_382_);
lean_dec(v___x_381_);
if (v___x_383_ == 0)
{
lean_object* v_val_384_; lean_object* v___x_386_; 
v_val_384_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_348_, v_buckets_x27_377_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v_val_384_);
lean_ctor_set(v___x_355_, 0, v_size_x27_375_);
v___x_386_ = v___x_355_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_size_x27_375_);
lean_ctor_set(v_reuseFailAlloc_389_, 1, v_val_384_);
v___x_386_ = v_reuseFailAlloc_389_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_box(v___x_373_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v___x_387_);
lean_ctor_set(v___x_388_, 1, v___x_386_);
return v___x_388_;
}
}
else
{
lean_object* v___x_391_; 
lean_dec_ref(v_x_348_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v_buckets_x27_377_);
lean_ctor_set(v___x_355_, 0, v_size_x27_375_);
v___x_391_ = v___x_355_;
goto v_reusejp_390_;
}
else
{
lean_object* v_reuseFailAlloc_394_; 
v_reuseFailAlloc_394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_394_, 0, v_size_x27_375_);
lean_ctor_set(v_reuseFailAlloc_394_, 1, v_buckets_x27_377_);
v___x_391_ = v_reuseFailAlloc_394_;
goto v_reusejp_390_;
}
v_reusejp_390_:
{
lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_392_ = lean_box(v___x_373_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v___x_391_);
return v___x_393_;
}
}
}
else
{
lean_object* v___x_395_; lean_object* v_buckets_x27_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
lean_inc(v_bkt_372_);
lean_dec_ref(v_x_348_);
v___x_395_ = lean_box(0);
v_buckets_x27_396_ = lean_array_uset(v_buckets_353_, v___x_371_, v___x_395_);
v___x_397_ = l_Std_DHashMap_Internal_AssocList_replace___redArg(v_x_347_, v_a_350_, v_b_351_, v_bkt_372_);
v___x_398_ = lean_array_uset(v_buckets_x27_396_, v___x_371_, v___x_397_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v___x_398_);
v___x_400_ = v___x_355_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_size_352_);
lean_ctor_set(v_reuseFailAlloc_403_, 1, v___x_398_);
v___x_400_ = v_reuseFailAlloc_403_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; 
v___x_401_ = lean_box(v___x_373_);
v___x_402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set(v___x_402_, 1, v___x_400_);
return v___x_402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew___redArg(lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_m_407_, lean_object* v_a_408_, lean_object* v_b_409_){
_start:
{
lean_object* v_size_410_; lean_object* v_buckets_411_; lean_object* v___x_412_; lean_object* v___x_413_; uint64_t v___x_414_; uint64_t v___x_415_; uint64_t v___x_416_; uint64_t v___x_417_; uint64_t v_fold_418_; uint64_t v___x_419_; uint64_t v___x_420_; uint64_t v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v___x_425_; size_t v___x_426_; lean_object* v_bkt_427_; uint8_t v___x_428_; 
v_size_410_ = lean_ctor_get(v_m_407_, 0);
v_buckets_411_ = lean_ctor_get(v_m_407_, 1);
v___x_412_ = lean_array_get_size(v_buckets_411_);
lean_inc_ref(v_x_406_);
lean_inc_n(v_a_408_, 2);
v___x_413_ = lean_apply_1(v_x_406_, v_a_408_);
v___x_414_ = 32ULL;
v___x_415_ = lean_unbox_uint64(v___x_413_);
v___x_416_ = lean_uint64_shift_right(v___x_415_, v___x_414_);
v___x_417_ = lean_unbox_uint64(v___x_413_);
lean_dec_ref(v___x_413_);
v_fold_418_ = lean_uint64_xor(v___x_417_, v___x_416_);
v___x_419_ = 16ULL;
v___x_420_ = lean_uint64_shift_right(v_fold_418_, v___x_419_);
v___x_421_ = lean_uint64_xor(v_fold_418_, v___x_420_);
v___x_422_ = lean_uint64_to_usize(v___x_421_);
v___x_423_ = lean_usize_of_nat(v___x_412_);
v___x_424_ = ((size_t)1ULL);
v___x_425_ = lean_usize_sub(v___x_423_, v___x_424_);
v___x_426_ = lean_usize_land(v___x_422_, v___x_425_);
v_bkt_427_ = lean_array_uget_borrowed(v_buckets_411_, v___x_426_);
lean_inc(v_bkt_427_);
v___x_428_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_405_, v_a_408_, v_bkt_427_);
if (v___x_428_ == 0)
{
lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_453_; 
lean_inc_ref(v_buckets_411_);
lean_inc(v_size_410_);
v_isSharedCheck_453_ = !lean_is_exclusive(v_m_407_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; lean_object* v_unused_455_; 
v_unused_454_ = lean_ctor_get(v_m_407_, 1);
lean_dec(v_unused_454_);
v_unused_455_ = lean_ctor_get(v_m_407_, 0);
lean_dec(v_unused_455_);
v___x_430_ = v_m_407_;
v_isShared_431_ = v_isSharedCheck_453_;
goto v_resetjp_429_;
}
else
{
lean_dec(v_m_407_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_453_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v_size_x27_433_; lean_object* v___x_434_; lean_object* v_buckets_x27_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; uint8_t v___x_441_; 
v___x_432_ = lean_unsigned_to_nat(1u);
v_size_x27_433_ = lean_nat_add(v_size_410_, v___x_432_);
lean_dec(v_size_410_);
lean_inc(v_bkt_427_);
v___x_434_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_434_, 0, v_a_408_);
lean_ctor_set(v___x_434_, 1, v_b_409_);
lean_ctor_set(v___x_434_, 2, v_bkt_427_);
v_buckets_x27_435_ = lean_array_uset(v_buckets_411_, v___x_426_, v___x_434_);
v___x_436_ = lean_unsigned_to_nat(4u);
v___x_437_ = lean_nat_mul(v_size_x27_433_, v___x_436_);
v___x_438_ = lean_unsigned_to_nat(3u);
v___x_439_ = lean_nat_div(v___x_437_, v___x_438_);
lean_dec(v___x_437_);
v___x_440_ = lean_array_get_size(v_buckets_x27_435_);
v___x_441_ = lean_nat_dec_le(v___x_439_, v___x_440_);
lean_dec(v___x_439_);
if (v___x_441_ == 0)
{
lean_object* v_val_442_; lean_object* v___x_444_; 
v_val_442_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_406_, v_buckets_x27_435_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v_val_442_);
lean_ctor_set(v___x_430_, 0, v_size_x27_433_);
v___x_444_ = v___x_430_;
goto v_reusejp_443_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_size_x27_433_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_val_442_);
v___x_444_ = v_reuseFailAlloc_447_;
goto v_reusejp_443_;
}
v_reusejp_443_:
{
lean_object* v___x_445_; lean_object* v___x_446_; 
v___x_445_ = lean_box(v___x_428_);
v___x_446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_446_, 0, v___x_445_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
return v___x_446_;
}
}
else
{
lean_object* v___x_449_; 
lean_dec_ref(v_x_406_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 1, v_buckets_x27_435_);
lean_ctor_set(v___x_430_, 0, v_size_x27_433_);
v___x_449_ = v___x_430_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_size_x27_433_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_buckets_x27_435_);
v___x_449_ = v_reuseFailAlloc_452_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_box(v___x_428_);
v___x_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
return v___x_451_;
}
}
}
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; 
lean_dec(v_b_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_x_406_);
v___x_456_ = lean_box(v___x_428_);
v___x_457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v_m_407_);
return v___x_457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_458_, lean_object* v_00_u03b2_459_, lean_object* v_x_460_, lean_object* v_x_461_, lean_object* v_m_462_, lean_object* v_a_463_, lean_object* v_b_464_){
_start:
{
lean_object* v_size_465_; lean_object* v_buckets_466_; lean_object* v___x_467_; lean_object* v___x_468_; uint64_t v___x_469_; uint64_t v___x_470_; uint64_t v___x_471_; uint64_t v___x_472_; uint64_t v_fold_473_; uint64_t v___x_474_; uint64_t v___x_475_; uint64_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v_bkt_482_; uint8_t v___x_483_; 
v_size_465_ = lean_ctor_get(v_m_462_, 0);
v_buckets_466_ = lean_ctor_get(v_m_462_, 1);
v___x_467_ = lean_array_get_size(v_buckets_466_);
lean_inc_ref(v_x_461_);
lean_inc_n(v_a_463_, 2);
v___x_468_ = lean_apply_1(v_x_461_, v_a_463_);
v___x_469_ = 32ULL;
v___x_470_ = lean_unbox_uint64(v___x_468_);
v___x_471_ = lean_uint64_shift_right(v___x_470_, v___x_469_);
v___x_472_ = lean_unbox_uint64(v___x_468_);
lean_dec_ref(v___x_468_);
v_fold_473_ = lean_uint64_xor(v___x_472_, v___x_471_);
v___x_474_ = 16ULL;
v___x_475_ = lean_uint64_shift_right(v_fold_473_, v___x_474_);
v___x_476_ = lean_uint64_xor(v_fold_473_, v___x_475_);
v___x_477_ = lean_uint64_to_usize(v___x_476_);
v___x_478_ = lean_usize_of_nat(v___x_467_);
v___x_479_ = ((size_t)1ULL);
v___x_480_ = lean_usize_sub(v___x_478_, v___x_479_);
v___x_481_ = lean_usize_land(v___x_477_, v___x_480_);
v_bkt_482_ = lean_array_uget_borrowed(v_buckets_466_, v___x_481_);
lean_inc(v_bkt_482_);
v___x_483_ = l_Std_DHashMap_Internal_AssocList_contains___redArg(v_x_460_, v_a_463_, v_bkt_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_508_; 
lean_inc_ref(v_buckets_466_);
lean_inc(v_size_465_);
v_isSharedCheck_508_ = !lean_is_exclusive(v_m_462_);
if (v_isSharedCheck_508_ == 0)
{
lean_object* v_unused_509_; lean_object* v_unused_510_; 
v_unused_509_ = lean_ctor_get(v_m_462_, 1);
lean_dec(v_unused_509_);
v_unused_510_ = lean_ctor_get(v_m_462_, 0);
lean_dec(v_unused_510_);
v___x_485_ = v_m_462_;
v_isShared_486_ = v_isSharedCheck_508_;
goto v_resetjp_484_;
}
else
{
lean_dec(v_m_462_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_508_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v_size_x27_488_; lean_object* v___x_489_; lean_object* v_buckets_x27_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v_size_x27_488_ = lean_nat_add(v_size_465_, v___x_487_);
lean_dec(v_size_465_);
lean_inc(v_bkt_482_);
v___x_489_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_489_, 0, v_a_463_);
lean_ctor_set(v___x_489_, 1, v_b_464_);
lean_ctor_set(v___x_489_, 2, v_bkt_482_);
v_buckets_x27_490_ = lean_array_uset(v_buckets_466_, v___x_481_, v___x_489_);
v___x_491_ = lean_unsigned_to_nat(4u);
v___x_492_ = lean_nat_mul(v_size_x27_488_, v___x_491_);
v___x_493_ = lean_unsigned_to_nat(3u);
v___x_494_ = lean_nat_div(v___x_492_, v___x_493_);
lean_dec(v___x_492_);
v___x_495_ = lean_array_get_size(v_buckets_x27_490_);
v___x_496_ = lean_nat_dec_le(v___x_494_, v___x_495_);
lean_dec(v___x_494_);
if (v___x_496_ == 0)
{
lean_object* v_val_497_; lean_object* v___x_499_; 
v_val_497_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_461_, v_buckets_x27_490_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v_val_497_);
lean_ctor_set(v___x_485_, 0, v_size_x27_488_);
v___x_499_ = v___x_485_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_size_x27_488_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_val_497_);
v___x_499_ = v_reuseFailAlloc_502_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_box(v___x_483_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
lean_ctor_set(v___x_501_, 1, v___x_499_);
return v___x_501_;
}
}
else
{
lean_object* v___x_504_; 
lean_dec_ref(v_x_461_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 1, v_buckets_x27_490_);
lean_ctor_set(v___x_485_, 0, v_size_x27_488_);
v___x_504_ = v___x_485_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v_size_x27_488_);
lean_ctor_set(v_reuseFailAlloc_507_, 1, v_buckets_x27_490_);
v___x_504_ = v_reuseFailAlloc_507_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_box(v___x_483_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
return v___x_506_;
}
}
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_b_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_x_461_);
v___x_511_ = lean_box(v___x_483_);
v___x_512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_512_, 0, v___x_511_);
lean_ctor_set(v___x_512_, 1, v_m_462_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_513_, lean_object* v_x_514_, lean_object* v_m_515_, lean_object* v_a_516_, lean_object* v_b_517_){
_start:
{
lean_object* v_size_518_; lean_object* v_buckets_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint64_t v___x_522_; uint64_t v___x_523_; uint64_t v___x_524_; uint64_t v___x_525_; uint64_t v_fold_526_; uint64_t v___x_527_; uint64_t v___x_528_; uint64_t v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; lean_object* v_bkt_535_; lean_object* v___x_536_; 
v_size_518_ = lean_ctor_get(v_m_515_, 0);
v_buckets_519_ = lean_ctor_get(v_m_515_, 1);
v___x_520_ = lean_array_get_size(v_buckets_519_);
lean_inc_ref(v_x_514_);
lean_inc_n(v_a_516_, 2);
v___x_521_ = lean_apply_1(v_x_514_, v_a_516_);
v___x_522_ = 32ULL;
v___x_523_ = lean_unbox_uint64(v___x_521_);
v___x_524_ = lean_uint64_shift_right(v___x_523_, v___x_522_);
v___x_525_ = lean_unbox_uint64(v___x_521_);
lean_dec_ref(v___x_521_);
v_fold_526_ = lean_uint64_xor(v___x_525_, v___x_524_);
v___x_527_ = 16ULL;
v___x_528_ = lean_uint64_shift_right(v_fold_526_, v___x_527_);
v___x_529_ = lean_uint64_xor(v_fold_526_, v___x_528_);
v___x_530_ = lean_uint64_to_usize(v___x_529_);
v___x_531_ = lean_usize_of_nat(v___x_520_);
v___x_532_ = ((size_t)1ULL);
v___x_533_ = lean_usize_sub(v___x_531_, v___x_532_);
v___x_534_ = lean_usize_land(v___x_530_, v___x_533_);
v_bkt_535_ = lean_array_uget_borrowed(v_buckets_519_, v___x_534_);
lean_inc(v_bkt_535_);
v___x_536_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_513_, v_a_516_, v_bkt_535_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_559_; 
lean_inc_ref(v_buckets_519_);
lean_inc(v_size_518_);
v_isSharedCheck_559_ = !lean_is_exclusive(v_m_515_);
if (v_isSharedCheck_559_ == 0)
{
lean_object* v_unused_560_; lean_object* v_unused_561_; 
v_unused_560_ = lean_ctor_get(v_m_515_, 1);
lean_dec(v_unused_560_);
v_unused_561_ = lean_ctor_get(v_m_515_, 0);
lean_dec(v_unused_561_);
v___x_538_ = v_m_515_;
v_isShared_539_ = v_isSharedCheck_559_;
goto v_resetjp_537_;
}
else
{
lean_dec(v_m_515_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_559_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v_size_x27_541_; lean_object* v___x_542_; lean_object* v_buckets_x27_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_540_ = lean_unsigned_to_nat(1u);
v_size_x27_541_ = lean_nat_add(v_size_518_, v___x_540_);
lean_dec(v_size_518_);
lean_inc(v_bkt_535_);
v___x_542_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_542_, 0, v_a_516_);
lean_ctor_set(v___x_542_, 1, v_b_517_);
lean_ctor_set(v___x_542_, 2, v_bkt_535_);
v_buckets_x27_543_ = lean_array_uset(v_buckets_519_, v___x_534_, v___x_542_);
v___x_544_ = lean_unsigned_to_nat(4u);
v___x_545_ = lean_nat_mul(v_size_x27_541_, v___x_544_);
v___x_546_ = lean_unsigned_to_nat(3u);
v___x_547_ = lean_nat_div(v___x_545_, v___x_546_);
lean_dec(v___x_545_);
v___x_548_ = lean_array_get_size(v_buckets_x27_543_);
v___x_549_ = lean_nat_dec_le(v___x_547_, v___x_548_);
lean_dec(v___x_547_);
if (v___x_549_ == 0)
{
lean_object* v_val_550_; lean_object* v___x_552_; 
v_val_550_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_514_, v_buckets_x27_543_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v_val_550_);
lean_ctor_set(v___x_538_, 0, v_size_x27_541_);
v___x_552_ = v___x_538_;
goto v_reusejp_551_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_size_x27_541_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_val_550_);
v___x_552_ = v_reuseFailAlloc_554_;
goto v_reusejp_551_;
}
v_reusejp_551_:
{
lean_object* v___x_553_; 
v___x_553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_553_, 0, v___x_536_);
lean_ctor_set(v___x_553_, 1, v___x_552_);
return v___x_553_;
}
}
else
{
lean_object* v___x_556_; 
lean_dec_ref(v_x_514_);
if (v_isShared_539_ == 0)
{
lean_ctor_set(v___x_538_, 1, v_buckets_x27_543_);
lean_ctor_set(v___x_538_, 0, v_size_x27_541_);
v___x_556_ = v___x_538_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_size_x27_541_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_buckets_x27_543_);
v___x_556_ = v_reuseFailAlloc_558_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; 
v___x_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_536_);
lean_ctor_set(v___x_557_, 1, v___x_556_);
return v___x_557_;
}
}
}
}
else
{
lean_object* v___x_562_; 
lean_dec(v_b_517_);
lean_dec(v_a_516_);
lean_dec_ref(v_x_514_);
v___x_562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_562_, 0, v___x_536_);
lean_ctor_set(v___x_562_, 1, v_m_515_);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_563_, lean_object* v_00_u03b2_564_, lean_object* v_x_565_, lean_object* v_x_566_, lean_object* v_m_567_, lean_object* v_a_568_, lean_object* v_b_569_){
_start:
{
lean_object* v_size_570_; lean_object* v_buckets_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint64_t v___x_574_; uint64_t v___x_575_; uint64_t v___x_576_; uint64_t v___x_577_; uint64_t v_fold_578_; uint64_t v___x_579_; uint64_t v___x_580_; uint64_t v___x_581_; size_t v___x_582_; size_t v___x_583_; size_t v___x_584_; size_t v___x_585_; size_t v___x_586_; lean_object* v_bkt_587_; lean_object* v___x_588_; 
v_size_570_ = lean_ctor_get(v_m_567_, 0);
v_buckets_571_ = lean_ctor_get(v_m_567_, 1);
v___x_572_ = lean_array_get_size(v_buckets_571_);
lean_inc_ref(v_x_566_);
lean_inc_n(v_a_568_, 2);
v___x_573_ = lean_apply_1(v_x_566_, v_a_568_);
v___x_574_ = 32ULL;
v___x_575_ = lean_unbox_uint64(v___x_573_);
v___x_576_ = lean_uint64_shift_right(v___x_575_, v___x_574_);
v___x_577_ = lean_unbox_uint64(v___x_573_);
lean_dec_ref(v___x_573_);
v_fold_578_ = lean_uint64_xor(v___x_577_, v___x_576_);
v___x_579_ = 16ULL;
v___x_580_ = lean_uint64_shift_right(v_fold_578_, v___x_579_);
v___x_581_ = lean_uint64_xor(v_fold_578_, v___x_580_);
v___x_582_ = lean_uint64_to_usize(v___x_581_);
v___x_583_ = lean_usize_of_nat(v___x_572_);
v___x_584_ = ((size_t)1ULL);
v___x_585_ = lean_usize_sub(v___x_583_, v___x_584_);
v___x_586_ = lean_usize_land(v___x_582_, v___x_585_);
v_bkt_587_ = lean_array_uget_borrowed(v_buckets_571_, v___x_586_);
lean_inc(v_bkt_587_);
v___x_588_ = l_Std_DHashMap_Internal_AssocList_get_x3f___redArg(v_x_565_, v_a_568_, v_bkt_587_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_611_; 
lean_inc_ref(v_buckets_571_);
lean_inc(v_size_570_);
v_isSharedCheck_611_ = !lean_is_exclusive(v_m_567_);
if (v_isSharedCheck_611_ == 0)
{
lean_object* v_unused_612_; lean_object* v_unused_613_; 
v_unused_612_ = lean_ctor_get(v_m_567_, 1);
lean_dec(v_unused_612_);
v_unused_613_ = lean_ctor_get(v_m_567_, 0);
lean_dec(v_unused_613_);
v___x_590_ = v_m_567_;
v_isShared_591_ = v_isSharedCheck_611_;
goto v_resetjp_589_;
}
else
{
lean_dec(v_m_567_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_611_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v_size_x27_593_; lean_object* v___x_594_; lean_object* v_buckets_x27_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v___x_592_ = lean_unsigned_to_nat(1u);
v_size_x27_593_ = lean_nat_add(v_size_570_, v___x_592_);
lean_dec(v_size_570_);
lean_inc(v_bkt_587_);
v___x_594_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_594_, 0, v_a_568_);
lean_ctor_set(v___x_594_, 1, v_b_569_);
lean_ctor_set(v___x_594_, 2, v_bkt_587_);
v_buckets_x27_595_ = lean_array_uset(v_buckets_571_, v___x_586_, v___x_594_);
v___x_596_ = lean_unsigned_to_nat(4u);
v___x_597_ = lean_nat_mul(v_size_x27_593_, v___x_596_);
v___x_598_ = lean_unsigned_to_nat(3u);
v___x_599_ = lean_nat_div(v___x_597_, v___x_598_);
lean_dec(v___x_597_);
v___x_600_ = lean_array_get_size(v_buckets_x27_595_);
v___x_601_ = lean_nat_dec_le(v___x_599_, v___x_600_);
lean_dec(v___x_599_);
if (v___x_601_ == 0)
{
lean_object* v_val_602_; lean_object* v___x_604_; 
v_val_602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_566_, v_buckets_x27_595_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_val_602_);
lean_ctor_set(v___x_590_, 0, v_size_x27_593_);
v___x_604_ = v___x_590_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_size_x27_593_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_val_602_);
v___x_604_ = v_reuseFailAlloc_606_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_588_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
return v___x_605_;
}
}
else
{
lean_object* v___x_608_; 
lean_dec_ref(v_x_566_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v_buckets_x27_595_);
lean_ctor_set(v___x_590_, 0, v_size_x27_593_);
v___x_608_ = v___x_590_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_size_x27_593_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_buckets_x27_595_);
v___x_608_ = v_reuseFailAlloc_610_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_609_, 0, v___x_588_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
return v___x_609_;
}
}
}
}
else
{
lean_object* v___x_614_; 
lean_dec(v_b_569_);
lean_dec(v_a_568_);
lean_dec_ref(v_x_566_);
v___x_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_588_);
lean_ctor_set(v___x_614_, 1, v_m_567_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg(lean_object* v_x_615_, lean_object* v_x_616_, lean_object* v_m_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_615_, v_x_616_, v_m_617_, v_a_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg___boxed(lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_m_622_, lean_object* v_a_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Std_HashMap_get_x3f___redArg(v_x_620_, v_x_621_, v_m_622_, v_a_623_);
lean_dec_ref(v_m_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f(lean_object* v_00_u03b1_625_, lean_object* v_00_u03b2_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_m_629_, lean_object* v_a_630_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_627_, v_x_628_, v_m_629_, v_a_630_);
return v___x_631_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___boxed(lean_object* v_00_u03b1_632_, lean_object* v_00_u03b2_633_, lean_object* v_x_634_, lean_object* v_x_635_, lean_object* v_m_636_, lean_object* v_a_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Std_HashMap_get_x3f(v_00_u03b1_632_, v_00_u03b2_633_, v_x_634_, v_x_635_, v_m_636_, v_a_637_);
lean_dec_ref(v_m_636_);
return v_res_638_;
}
}
uint8_t l_Std_HashMap_contains___redArg(lean_object* v_x_639_, lean_object* v_x_640_, lean_object* v_m_641_, lean_object* v_a_642_){
_start:
{
uint8_t v___x_643_; 
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_639_, v_x_640_, v_m_641_, v_a_642_);
return v___x_643_;
}
}
LEAN_EXPORT void l_Std_HashMap_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_639_ = stack[0].m_obj;
lean_object* v_x_640_ = stack[1].m_obj;
lean_object* v_m_641_ = stack[2].m_obj;
lean_object* v_a_642_ = stack[3].m_obj;
uint8_t v_res_644_;
v_res_644_ = l_Std_HashMap_contains___redArg(v_x_639_, v_x_640_, v_m_641_, v_a_642_);
stack->m_num = v_res_644_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___redArg___boxed(lean_object* v_x_645_, lean_object* v_x_646_, lean_object* v_m_647_, lean_object* v_a_648_){
_start:
{
uint8_t v_res_649_; lean_object* v_r_650_; 
v_res_649_ = l_Std_HashMap_contains___redArg(v_x_645_, v_x_646_, v_m_647_, v_a_648_);
lean_dec_ref(v_m_647_);
v_r_650_ = lean_box(v_res_649_);
return v_r_650_;
}
}
uint8_t l_Std_HashMap_contains(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b2_652_, lean_object* v_x_653_, lean_object* v_x_654_, lean_object* v_m_655_, lean_object* v_a_656_){
_start:
{
uint8_t v___x_657_; 
v___x_657_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_653_, v_x_654_, v_m_655_, v_a_656_);
return v___x_657_;
}
}
LEAN_EXPORT void l_Std_HashMap_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_653_ = stack[2].m_obj;
lean_object* v_x_654_ = stack[3].m_obj;
lean_object* v_m_655_ = stack[4].m_obj;
lean_object* v_a_656_ = stack[5].m_obj;
uint8_t v_res_658_;
v_res_658_ = l_Std_HashMap_contains(lean_box(0), lean_box(0), v_x_653_, v_x_654_, v_m_655_, v_a_656_);
stack->m_num = v_res_658_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___boxed(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b2_660_, lean_object* v_x_661_, lean_object* v_x_662_, lean_object* v_m_663_, lean_object* v_a_664_){
_start:
{
uint8_t v_res_665_; lean_object* v_r_666_; 
v_res_665_ = l_Std_HashMap_contains(v_00_u03b1_659_, v_00_u03b2_660_, v_x_661_, v_x_662_, v_m_663_, v_a_664_);
lean_dec_ref(v_m_663_);
v_r_666_ = lean_box(v_res_665_);
return v_r_666_;
}
}
lean_object* l_Std_HashMap_instMembership___redArg(){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = lean_box(0);
return v___x_668_;
}
}
LEAN_EXPORT void l_Std_HashMap_instMembership___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_669_;
v_res_669_ = l_Std_HashMap_instMembership___redArg();
stack->m_obj
 = v_res_669_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___redArg___boxed(lean_object* v___dummy_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_Std_HashMap_instMembership___redArg();
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership(lean_object* v_00_u03b1_672_, lean_object* v_00_u03b2_673_, lean_object* v_inst_674_, lean_object* v_inst_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = lean_box(0);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___boxed(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_inst_679_, lean_object* v_inst_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Std_HashMap_instMembership(v_00_u03b1_677_, v_00_u03b2_678_, v_inst_679_, v_inst_680_);
lean_dec_ref(v_inst_680_);
lean_dec_ref(v_inst_679_);
return v_res_681_;
}
}
uint8_t l_Std_HashMap_instDecidableMem___redArg(lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_m_684_, lean_object* v_a_685_){
_start:
{
uint8_t v___x_686_; 
v___x_686_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_682_, v_inst_683_, v_m_684_, v_a_685_);
return v___x_686_;
}
}
LEAN_EXPORT void l_Std_HashMap_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_682_ = stack[0].m_obj;
lean_object* v_inst_683_ = stack[1].m_obj;
lean_object* v_m_684_ = stack[2].m_obj;
lean_object* v_a_685_ = stack[3].m_obj;
uint8_t v_res_687_;
v_res_687_ = l_Std_HashMap_instDecidableMem___redArg(v_inst_682_, v_inst_683_, v_m_684_, v_a_685_);
stack->m_num = v_res_687_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___redArg___boxed(lean_object* v_inst_688_, lean_object* v_inst_689_, lean_object* v_m_690_, lean_object* v_a_691_){
_start:
{
uint8_t v_res_692_; lean_object* v_r_693_; 
v_res_692_ = l_Std_HashMap_instDecidableMem___redArg(v_inst_688_, v_inst_689_, v_m_690_, v_a_691_);
lean_dec_ref(v_m_690_);
v_r_693_ = lean_box(v_res_692_);
return v_r_693_;
}
}
uint8_t l_Std_HashMap_instDecidableMem(lean_object* v_00_u03b1_694_, lean_object* v_00_u03b2_695_, lean_object* v_inst_696_, lean_object* v_inst_697_, lean_object* v_m_698_, lean_object* v_a_699_){
_start:
{
uint8_t v___x_700_; 
v___x_700_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_696_, v_inst_697_, v_m_698_, v_a_699_);
return v___x_700_;
}
}
LEAN_EXPORT void l_Std_HashMap_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_696_ = stack[2].m_obj;
lean_object* v_inst_697_ = stack[3].m_obj;
lean_object* v_m_698_ = stack[4].m_obj;
lean_object* v_a_699_ = stack[5].m_obj;
uint8_t v_res_701_;
v_res_701_ = l_Std_HashMap_instDecidableMem(lean_box(0), lean_box(0), v_inst_696_, v_inst_697_, v_m_698_, v_a_699_);
stack->m_num = v_res_701_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_702_, lean_object* v_00_u03b2_703_, lean_object* v_inst_704_, lean_object* v_inst_705_, lean_object* v_m_706_, lean_object* v_a_707_){
_start:
{
uint8_t v_res_708_; lean_object* v_r_709_; 
v_res_708_ = l_Std_HashMap_instDecidableMem(v_00_u03b1_702_, v_00_u03b2_703_, v_inst_704_, v_inst_705_, v_m_706_, v_a_707_);
lean_dec_ref(v_m_706_);
v_r_709_ = lean_box(v_res_708_);
return v_r_709_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg(lean_object* v_x_710_, lean_object* v_x_711_, lean_object* v_m_712_, lean_object* v_a_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_710_, v_x_711_, v_m_712_, v_a_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg___boxed(lean_object* v_x_715_, lean_object* v_x_716_, lean_object* v_m_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Std_HashMap_get___redArg(v_x_715_, v_x_716_, v_m_717_, v_a_718_);
lean_dec_ref(v_m_717_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get(lean_object* v_00_u03b1_720_, lean_object* v_00_u03b2_721_, lean_object* v_x_722_, lean_object* v_x_723_, lean_object* v_m_724_, lean_object* v_a_725_, lean_object* v_h_726_){
_start:
{
lean_object* v___x_727_; 
v___x_727_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_x_722_, v_x_723_, v_m_724_, v_a_725_);
return v___x_727_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___boxed(lean_object* v_00_u03b1_728_, lean_object* v_00_u03b2_729_, lean_object* v_x_730_, lean_object* v_x_731_, lean_object* v_m_732_, lean_object* v_a_733_, lean_object* v_h_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Std_HashMap_get(v_00_u03b1_728_, v_00_u03b2_729_, v_x_730_, v_x_731_, v_m_732_, v_a_733_, v_h_734_);
lean_dec_ref(v_m_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg(lean_object* v_x_736_, lean_object* v_x_737_, lean_object* v_m_738_, lean_object* v_a_739_, lean_object* v_fallback_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_736_, v_x_737_, v_m_738_, v_a_739_, v_fallback_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg___boxed(lean_object* v_x_742_, lean_object* v_x_743_, lean_object* v_m_744_, lean_object* v_a_745_, lean_object* v_fallback_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Std_HashMap_getD___redArg(v_x_742_, v_x_743_, v_m_744_, v_a_745_, v_fallback_746_);
lean_dec(v_fallback_746_);
lean_dec_ref(v_m_744_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD(lean_object* v_00_u03b1_748_, lean_object* v_00_u03b2_749_, lean_object* v_x_750_, lean_object* v_x_751_, lean_object* v_m_752_, lean_object* v_a_753_, lean_object* v_fallback_754_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_750_, v_x_751_, v_m_752_, v_a_753_, v_fallback_754_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___boxed(lean_object* v_00_u03b1_756_, lean_object* v_00_u03b2_757_, lean_object* v_x_758_, lean_object* v_x_759_, lean_object* v_m_760_, lean_object* v_a_761_, lean_object* v_fallback_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Std_HashMap_getD(v_00_u03b1_756_, v_00_u03b2_757_, v_x_758_, v_x_759_, v_m_760_, v_a_761_, v_fallback_762_);
lean_dec(v_fallback_762_);
lean_dec_ref(v_m_760_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg(lean_object* v_x_764_, lean_object* v_x_765_, lean_object* v_inst_766_, lean_object* v_m_767_, lean_object* v_a_768_){
_start:
{
lean_object* v___x_769_; 
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_764_, v_x_765_, v_inst_766_, v_m_767_, v_a_768_);
return v___x_769_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg___boxed(lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_inst_772_, lean_object* v_m_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Std_HashMap_get_x21___redArg(v_x_770_, v_x_771_, v_inst_772_, v_m_773_, v_a_774_);
lean_dec_ref(v_m_773_);
lean_dec(v_inst_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21(lean_object* v_00_u03b1_776_, lean_object* v_00_u03b2_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_inst_780_, lean_object* v_m_781_, lean_object* v_a_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_778_, v_x_779_, v_inst_780_, v_m_781_, v_a_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___boxed(lean_object* v_00_u03b1_784_, lean_object* v_00_u03b2_785_, lean_object* v_x_786_, lean_object* v_x_787_, lean_object* v_inst_788_, lean_object* v_m_789_, lean_object* v_a_790_){
_start:
{
lean_object* v_res_791_; 
v_res_791_ = l_Std_HashMap_get_x21(v_00_u03b1_784_, v_00_u03b2_785_, v_x_786_, v_x_787_, v_inst_788_, v_m_789_, v_a_790_);
lean_dec_ref(v_m_789_);
lean_dec(v_inst_788_);
return v_res_791_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_m_794_, lean_object* v_a_795_, lean_object* v_h_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get___redArg(v_inst_792_, v_inst_793_, v_m_794_, v_a_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_m_800_, lean_object* v_a_801_, lean_object* v_h_802_){
_start:
{
lean_object* v_res_803_; 
v_res_803_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(v_inst_798_, v_inst_799_, v_m_800_, v_a_801_, v_h_802_);
lean_dec_ref(v_m_800_);
return v_res_803_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_m_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_804_, v_inst_805_, v_m_806_, v_a_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_809_, lean_object* v_inst_810_, lean_object* v_m_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(v_inst_809_, v_inst_810_, v_m_811_, v_a_812_);
lean_dec_ref(v_m_811_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_m_817_, lean_object* v_a_818_){
_start:
{
lean_object* v___x_819_; 
v___x_819_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_814_, v_inst_815_, v_inst_816_, v_m_817_, v_a_818_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_inst_822_, lean_object* v_m_823_, lean_object* v_a_824_){
_start:
{
lean_object* v_res_825_; 
v_res_825_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(v_inst_820_, v_inst_821_, v_inst_822_, v_m_823_, v_a_824_);
lean_dec_ref(v_m_823_);
lean_dec(v_inst_822_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg(lean_object* v_inst_826_, lean_object* v_inst_827_){
_start:
{
lean_object* v___f_828_; lean_object* v___f_829_; lean_object* v___f_830_; lean_object* v___x_831_; 
lean_inc_ref_n(v_inst_827_, 2);
lean_inc_ref_n(v_inst_826_, 2);
v___f_828_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_828_, 0, v_inst_826_);
lean_closure_set(v___f_828_, 1, v_inst_827_);
v___f_829_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_829_, 0, v_inst_826_);
lean_closure_set(v___f_829_, 1, v_inst_827_);
v___f_830_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_830_, 0, v_inst_826_);
lean_closure_set(v___f_830_, 1, v_inst_827_);
v___x_831_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_831_, 0, v___f_828_);
lean_ctor_set(v___x_831_, 1, v___f_829_);
lean_ctor_set(v___x_831_, 2, v___f_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem(lean_object* v_00_u03b1_832_, lean_object* v_00_u03b2_833_, lean_object* v_inst_834_, lean_object* v_inst_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Std_HashMap_instGetElem_x3fMem___redArg(v_inst_834_, v_inst_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg(lean_object* v_x_837_, lean_object* v_x_838_, lean_object* v_m_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_837_, v_x_838_, v_m_839_, v_a_840_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg___boxed(lean_object* v_x_842_, lean_object* v_x_843_, lean_object* v_m_844_, lean_object* v_a_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Std_HashMap_getKey_x3f___redArg(v_x_842_, v_x_843_, v_m_844_, v_a_845_);
lean_dec_ref(v_m_844_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f(lean_object* v_00_u03b1_847_, lean_object* v_00_u03b2_848_, lean_object* v_x_849_, lean_object* v_x_850_, lean_object* v_m_851_, lean_object* v_a_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_849_, v_x_850_, v_m_851_, v_a_852_);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_854_, lean_object* v_00_u03b2_855_, lean_object* v_x_856_, lean_object* v_x_857_, lean_object* v_m_858_, lean_object* v_a_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_HashMap_getKey_x3f(v_00_u03b1_854_, v_00_u03b2_855_, v_x_856_, v_x_857_, v_m_858_, v_a_859_);
lean_dec_ref(v_m_858_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg(lean_object* v_x_861_, lean_object* v_x_862_, lean_object* v_m_863_, lean_object* v_a_864_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_861_, v_x_862_, v_m_863_, v_a_864_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg___boxed(lean_object* v_x_866_, lean_object* v_x_867_, lean_object* v_m_868_, lean_object* v_a_869_){
_start:
{
lean_object* v_res_870_; 
v_res_870_ = l_Std_HashMap_getKey___redArg(v_x_866_, v_x_867_, v_m_868_, v_a_869_);
lean_dec_ref(v_m_868_);
return v_res_870_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey(lean_object* v_00_u03b1_871_, lean_object* v_00_u03b2_872_, lean_object* v_x_873_, lean_object* v_x_874_, lean_object* v_m_875_, lean_object* v_a_876_, lean_object* v_h_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_getKey___redArg(v_x_873_, v_x_874_, v_m_875_, v_a_876_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___boxed(lean_object* v_00_u03b1_879_, lean_object* v_00_u03b2_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_m_883_, lean_object* v_a_884_, lean_object* v_h_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l_Std_HashMap_getKey(v_00_u03b1_879_, v_00_u03b2_880_, v_x_881_, v_x_882_, v_m_883_, v_a_884_, v_h_885_);
lean_dec_ref(v_m_883_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg(lean_object* v_x_887_, lean_object* v_x_888_, lean_object* v_m_889_, lean_object* v_a_890_, lean_object* v_fallback_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_887_, v_x_888_, v_m_889_, v_a_890_, v_fallback_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg___boxed(lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_m_895_, lean_object* v_a_896_, lean_object* v_fallback_897_){
_start:
{
lean_object* v_res_898_; 
v_res_898_ = l_Std_HashMap_getKeyD___redArg(v_x_893_, v_x_894_, v_m_895_, v_a_896_, v_fallback_897_);
lean_dec(v_fallback_897_);
lean_dec_ref(v_m_895_);
return v_res_898_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD(lean_object* v_00_u03b1_899_, lean_object* v_00_u03b2_900_, lean_object* v_x_901_, lean_object* v_x_902_, lean_object* v_m_903_, lean_object* v_a_904_, lean_object* v_fallback_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_901_, v_x_902_, v_m_903_, v_a_904_, v_fallback_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___boxed(lean_object* v_00_u03b1_907_, lean_object* v_00_u03b2_908_, lean_object* v_x_909_, lean_object* v_x_910_, lean_object* v_m_911_, lean_object* v_a_912_, lean_object* v_fallback_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_HashMap_getKeyD(v_00_u03b1_907_, v_00_u03b2_908_, v_x_909_, v_x_910_, v_m_911_, v_a_912_, v_fallback_913_);
lean_dec(v_fallback_913_);
lean_dec_ref(v_m_911_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg(lean_object* v_x_915_, lean_object* v_x_916_, lean_object* v_inst_917_, lean_object* v_m_918_, lean_object* v_a_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_915_, v_x_916_, v_inst_917_, v_m_918_, v_a_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg___boxed(lean_object* v_x_921_, lean_object* v_x_922_, lean_object* v_inst_923_, lean_object* v_m_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Std_HashMap_getKey_x21___redArg(v_x_921_, v_x_922_, v_inst_923_, v_m_924_, v_a_925_);
lean_dec_ref(v_m_924_);
lean_dec(v_inst_923_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21(lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_x_929_, lean_object* v_x_930_, lean_object* v_inst_931_, lean_object* v_m_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_929_, v_x_930_, v_inst_931_, v_m_932_, v_a_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___boxed(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_x_937_, lean_object* v_x_938_, lean_object* v_inst_939_, lean_object* v_m_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Std_HashMap_getKey_x21(v_00_u03b1_935_, v_00_u03b2_936_, v_x_937_, v_x_938_, v_inst_939_, v_m_940_, v_a_941_);
lean_dec_ref(v_m_940_);
lean_dec(v_inst_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase___redArg(lean_object* v_x_943_, lean_object* v_x_944_, lean_object* v_m_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_943_, v_x_944_, v_m_945_, v_a_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase(lean_object* v_00_u03b1_948_, lean_object* v_00_u03b2_949_, lean_object* v_x_950_, lean_object* v_x_951_, lean_object* v_m_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_954_; 
v___x_954_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_950_, v_x_951_, v_m_952_, v_a_953_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg(lean_object* v_m_955_){
_start:
{
lean_object* v_size_956_; 
v_size_956_ = lean_ctor_get(v_m_955_, 0);
lean_inc(v_size_956_);
return v_size_956_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg___boxed(lean_object* v_m_957_){
_start:
{
lean_object* v_res_958_; 
v_res_958_ = l_Std_HashMap_size___redArg(v_m_957_);
lean_dec_ref(v_m_957_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size(lean_object* v_00_u03b1_959_, lean_object* v_00_u03b2_960_, lean_object* v_x_961_, lean_object* v_x_962_, lean_object* v_m_963_){
_start:
{
lean_object* v_size_964_; 
v_size_964_ = lean_ctor_get(v_m_963_, 0);
lean_inc(v_size_964_);
return v_size_964_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___boxed(lean_object* v_00_u03b1_965_, lean_object* v_00_u03b2_966_, lean_object* v_x_967_, lean_object* v_x_968_, lean_object* v_m_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_HashMap_size(v_00_u03b1_965_, v_00_u03b2_966_, v_x_967_, v_x_968_, v_m_969_);
lean_dec_ref(v_m_969_);
lean_dec_ref(v_x_968_);
lean_dec_ref(v_x_967_);
return v_res_970_;
}
}
uint8_t l_Std_HashMap_isEmpty___redArg(lean_object* v_m_971_){
_start:
{
lean_object* v_size_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v_size_972_ = lean_ctor_get(v_m_971_, 0);
v___x_973_ = lean_unsigned_to_nat(0u);
v___x_974_ = lean_nat_dec_eq(v_size_972_, v___x_973_);
return v___x_974_;
}
}
LEAN_EXPORT void l_Std_HashMap_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_971_ = stack[0].m_obj;
uint8_t v_res_975_;
v_res_975_ = l_Std_HashMap_isEmpty___redArg(v_m_971_);
stack->m_num = v_res_975_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___redArg___boxed(lean_object* v_m_976_){
_start:
{
uint8_t v_res_977_; lean_object* v_r_978_; 
v_res_977_ = l_Std_HashMap_isEmpty___redArg(v_m_976_);
lean_dec_ref(v_m_976_);
v_r_978_ = lean_box(v_res_977_);
return v_r_978_;
}
}
uint8_t l_Std_HashMap_isEmpty(lean_object* v_00_u03b1_979_, lean_object* v_00_u03b2_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_m_983_){
_start:
{
lean_object* v_size_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_size_984_ = lean_ctor_get(v_m_983_, 0);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = lean_nat_dec_eq(v_size_984_, v___x_985_);
return v___x_986_;
}
}
LEAN_EXPORT void l_Std_HashMap_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_981_ = stack[2].m_obj;
lean_object* v_x_982_ = stack[3].m_obj;
lean_object* v_m_983_ = stack[4].m_obj;
uint8_t v_res_987_;
v_res_987_ = l_Std_HashMap_isEmpty(lean_box(0), lean_box(0), v_x_981_, v_x_982_, v_m_983_);
stack->m_num = v_res_987_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___boxed(lean_object* v_00_u03b1_988_, lean_object* v_00_u03b2_989_, lean_object* v_x_990_, lean_object* v_x_991_, lean_object* v_m_992_){
_start:
{
uint8_t v_res_993_; lean_object* v_r_994_; 
v_res_993_ = l_Std_HashMap_isEmpty(v_00_u03b1_988_, v_00_u03b2_989_, v_x_990_, v_x_991_, v_m_992_);
lean_dec_ref(v_m_992_);
lean_dec_ref(v_x_991_);
lean_dec_ref(v_x_990_);
v_r_994_ = lean_box(v_res_993_);
return v_r_994_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0(lean_object* v_a_995_, lean_object* v_b_996_, lean_object* v_d_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_998_, 0, v_a_995_);
lean_ctor_set(v___x_998_, 1, v_d_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0___boxed(lean_object* v_a_999_, lean_object* v_b_1000_, lean_object* v_d_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Std_HashMap_keys___redArg___lam__0(v_a_999_, v_b_1000_, v_d_1001_);
lean_dec(v_b_1000_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__1(lean_object* v___x_1003_, lean_object* v___f_1004_, lean_object* v_l_1005_, lean_object* v_acc_1006_){
_start:
{
lean_object* v___x_1007_; 
v___x_1007_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1003_, v___f_1004_, v_acc_1006_, v_l_1005_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg(lean_object* v_m_1031_){
_start:
{
lean_object* v___x_1032_; lean_object* v_buckets_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1032_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1033_ = lean_ctor_get(v_m_1031_, 1);
lean_inc_ref(v_buckets_1033_);
lean_dec_ref(v_m_1031_);
v___x_1034_ = lean_box(0);
v___x_1035_ = lean_array_get_size(v_buckets_1033_);
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = lean_nat_dec_lt(v___x_1036_, v___x_1035_);
if (v___x_1037_ == 0)
{
lean_dec_ref(v_buckets_1033_);
return v___x_1034_;
}
else
{
lean_object* v___f_1038_; size_t v___x_1039_; size_t v___x_1040_; lean_object* v___x_1041_; 
v___f_1038_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__11));
v___x_1039_ = lean_usize_of_nat(v___x_1035_);
v___x_1040_ = ((size_t)0ULL);
v___x_1041_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1032_, v___f_1038_, v_buckets_1033_, v___x_1039_, v___x_1040_, v___x_1034_);
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_m_1046_){
_start:
{
lean_object* v___x_1047_; lean_object* v_buckets_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1047_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1048_ = lean_ctor_get(v_m_1046_, 1);
lean_inc_ref(v_buckets_1048_);
lean_dec_ref(v_m_1046_);
v___x_1049_ = lean_box(0);
v___x_1050_ = lean_array_get_size(v_buckets_1048_);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = lean_nat_dec_lt(v___x_1051_, v___x_1050_);
if (v___x_1052_ == 0)
{
lean_dec_ref(v_buckets_1048_);
return v___x_1049_;
}
else
{
lean_object* v___f_1053_; size_t v___x_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v___f_1053_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__11));
v___x_1054_ = lean_usize_of_nat(v___x_1050_);
v___x_1055_ = ((size_t)0ULL);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1047_, v___f_1053_, v_buckets_1048_, v___x_1054_, v___x_1055_, v___x_1049_);
return v___x_1056_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___boxed(lean_object* v_00_u03b1_1057_, lean_object* v_00_u03b2_1058_, lean_object* v_x_1059_, lean_object* v_x_1060_, lean_object* v_m_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Std_HashMap_keys(v_00_u03b1_1057_, v_00_u03b2_1058_, v_x_1059_, v_x_1060_, v_m_1061_);
lean_dec_ref(v_x_1060_);
lean_dec_ref(v_x_1059_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList___redArg(lean_object* v_inst_1067_, lean_object* v_inst_1068_, lean_object* v_l_1069_){
_start:
{
lean_object* v___f_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___f_1070_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1071_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1070_, v_inst_1067_, v_inst_1068_, v___x_1071_, v_l_1069_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList(lean_object* v_00_u03b1_1073_, lean_object* v_00_u03b2_1074_, lean_object* v_inst_1075_, lean_object* v_inst_1076_, lean_object* v_l_1077_){
_start:
{
lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; 
v___f_1078_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1079_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1080_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1078_, v_inst_1075_, v_inst_1076_, v___x_1079_, v_l_1077_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList___redArg(lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_l_1083_){
_start:
{
lean_object* v___f_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___f_1084_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1085_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1086_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1084_, v_inst_1081_, v_inst_1082_, v___x_1085_, v_l_1083_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList(lean_object* v_00_u03b1_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_l_1090_){
_start:
{
lean_object* v___f_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___f_1091_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1092_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1093_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1091_, v_inst_1088_, v_inst_1089_, v___x_1092_, v_l_1090_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray___redArg(lean_object* v_inst_1098_, lean_object* v_inst_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___f_1101_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1102_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1103_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1101_, v_inst_1098_, v_inst_1099_, v___x_1102_, v_a_1100_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___f_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___f_1109_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1110_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1109_, v_inst_1106_, v_inst_1107_, v___x_1110_, v_a_1108_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__0(lean_object* v_a_1112_, lean_object* v_b_1113_, lean_object* v_d_1114_){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_a_1112_);
lean_ctor_set(v___x_1115_, 1, v_b_1113_);
v___x_1116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1115_);
lean_ctor_set(v___x_1116_, 1, v_d_1114_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__1(lean_object* v___x_1117_, lean_object* v___f_1118_, lean_object* v_l_1119_, lean_object* v_acc_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = l_Std_DHashMap_Internal_AssocList_foldrM___redArg(v___x_1117_, v___f_1118_, v_acc_1120_, v_l_1119_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg(lean_object* v_m_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v_buckets_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1127_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1128_ = lean_ctor_get(v_m_1126_, 1);
lean_inc_ref(v_buckets_1128_);
lean_dec_ref(v_m_1126_);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_array_get_size(v_buckets_1128_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_nat_dec_lt(v___x_1131_, v___x_1130_);
if (v___x_1132_ == 0)
{
lean_dec_ref(v_buckets_1128_);
return v___x_1129_;
}
else
{
lean_object* v___f_1133_; size_t v___x_1134_; size_t v___x_1135_; lean_object* v___x_1136_; 
v___f_1133_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__1));
v___x_1134_ = lean_usize_of_nat(v___x_1130_);
v___x_1135_ = ((size_t)0ULL);
v___x_1136_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1127_, v___f_1133_, v_buckets_1128_, v___x_1134_, v___x_1135_, v___x_1129_);
return v___x_1136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList(lean_object* v_00_u03b1_1137_, lean_object* v_00_u03b2_1138_, lean_object* v_x_1139_, lean_object* v_x_1140_, lean_object* v_m_1141_){
_start:
{
lean_object* v___x_1142_; lean_object* v_buckets_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; uint8_t v___x_1147_; 
v___x_1142_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1143_ = lean_ctor_get(v_m_1141_, 1);
lean_inc_ref(v_buckets_1143_);
lean_dec_ref(v_m_1141_);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_array_get_size(v_buckets_1143_);
v___x_1146_ = lean_unsigned_to_nat(0u);
v___x_1147_ = lean_nat_dec_lt(v___x_1146_, v___x_1145_);
if (v___x_1147_ == 0)
{
lean_dec_ref(v_buckets_1143_);
return v___x_1144_;
}
else
{
lean_object* v___f_1148_; size_t v___x_1149_; size_t v___x_1150_; lean_object* v___x_1151_; 
v___f_1148_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__1));
v___x_1149_ = lean_usize_of_nat(v___x_1145_);
v___x_1150_ = ((size_t)0ULL);
v___x_1151_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1142_, v___f_1148_, v_buckets_1143_, v___x_1149_, v___x_1150_, v___x_1144_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___boxed(lean_object* v_00_u03b1_1152_, lean_object* v_00_u03b2_1153_, lean_object* v_x_1154_, lean_object* v_x_1155_, lean_object* v_m_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Std_HashMap_toList(v_00_u03b1_1152_, v_00_u03b2_1153_, v_x_1154_, v_x_1155_, v_m_1156_);
lean_dec_ref(v_x_1155_);
lean_dec_ref(v_x_1154_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg___lam__0(lean_object* v_inst_1158_, lean_object* v_f_1159_, lean_object* v_acc_1160_, lean_object* v_l_1161_){
_start:
{
lean_object* v___x_1162_; 
v___x_1162_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1158_, v_f_1159_, v_acc_1160_, v_l_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg(lean_object* v_inst_1163_, lean_object* v_f_1164_, lean_object* v_init_1165_, lean_object* v_b_1166_){
_start:
{
lean_object* v_toApplicative_1167_; lean_object* v_buckets_1168_; lean_object* v_toPure_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; uint8_t v___x_1172_; 
v_toApplicative_1167_ = lean_ctor_get(v_inst_1163_, 0);
v_buckets_1168_ = lean_ctor_get(v_b_1166_, 1);
lean_inc_ref(v_buckets_1168_);
lean_dec_ref(v_b_1166_);
v_toPure_1169_ = lean_ctor_get(v_toApplicative_1167_, 1);
v___x_1170_ = lean_unsigned_to_nat(0u);
v___x_1171_ = lean_array_get_size(v_buckets_1168_);
v___x_1172_ = lean_nat_dec_lt(v___x_1170_, v___x_1171_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
lean_inc(v_toPure_1169_);
lean_dec_ref(v_buckets_1168_);
lean_dec(v_f_1164_);
lean_dec_ref(v_inst_1163_);
v___x_1173_ = lean_apply_2(v_toPure_1169_, lean_box(0), v_init_1165_);
return v___x_1173_;
}
else
{
lean_object* v___f_1174_; size_t v___x_1175_; size_t v___x_1176_; lean_object* v___x_1177_; 
lean_inc_ref(v_inst_1163_);
v___f_1174_ = lean_alloc_closure((void*)(l_Std_HashMap_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1174_, 0, v_inst_1163_);
lean_closure_set(v___f_1174_, 1, v_f_1164_);
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = lean_usize_of_nat(v___x_1171_);
v___x_1177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1163_, v___f_1174_, v_buckets_1168_, v___x_1175_, v___x_1176_, v_init_1165_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM(lean_object* v_00_u03b1_1178_, lean_object* v_00_u03b2_1179_, lean_object* v_x_1180_, lean_object* v_x_1181_, lean_object* v_m_1182_, lean_object* v_inst_1183_, lean_object* v_00_u03b3_1184_, lean_object* v_f_1185_, lean_object* v_init_1186_, lean_object* v_b_1187_){
_start:
{
lean_object* v_toApplicative_1188_; lean_object* v_buckets_1189_; lean_object* v_toPure_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_toApplicative_1188_ = lean_ctor_get(v_inst_1183_, 0);
v_buckets_1189_ = lean_ctor_get(v_b_1187_, 1);
lean_inc_ref(v_buckets_1189_);
lean_dec_ref(v_b_1187_);
v_toPure_1190_ = lean_ctor_get(v_toApplicative_1188_, 1);
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_array_get_size(v_buckets_1189_);
v___x_1193_ = lean_nat_dec_lt(v___x_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_inc(v_toPure_1190_);
lean_dec_ref(v_buckets_1189_);
lean_dec(v_f_1185_);
lean_dec_ref(v_inst_1183_);
v___x_1194_ = lean_apply_2(v_toPure_1190_, lean_box(0), v_init_1186_);
return v___x_1194_;
}
else
{
lean_object* v___f_1195_; size_t v___x_1196_; size_t v___x_1197_; lean_object* v___x_1198_; 
lean_inc_ref(v_inst_1183_);
v___f_1195_ = lean_alloc_closure((void*)(l_Std_HashMap_foldM___redArg___lam__0), 4, 2);
lean_closure_set(v___f_1195_, 0, v_inst_1183_);
lean_closure_set(v___f_1195_, 1, v_f_1185_);
v___x_1196_ = ((size_t)0ULL);
v___x_1197_ = lean_usize_of_nat(v___x_1192_);
v___x_1198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1183_, v___f_1195_, v_buckets_1189_, v___x_1196_, v___x_1197_, v_init_1186_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___boxed(lean_object* v_00_u03b1_1199_, lean_object* v_00_u03b2_1200_, lean_object* v_x_1201_, lean_object* v_x_1202_, lean_object* v_m_1203_, lean_object* v_inst_1204_, lean_object* v_00_u03b3_1205_, lean_object* v_f_1206_, lean_object* v_init_1207_, lean_object* v_b_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Std_HashMap_foldM(v_00_u03b1_1199_, v_00_u03b2_1200_, v_x_1201_, v_x_1202_, v_m_1203_, v_inst_1204_, v_00_u03b3_1205_, v_f_1206_, v_init_1207_, v_b_1208_);
lean_dec_ref(v_x_1202_);
lean_dec_ref(v_x_1201_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__0(lean_object* v_f_1210_, lean_object* v_x1_1211_, lean_object* v_x2_1212_, lean_object* v_x3_1213_){
_start:
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_apply_3(v_f_1210_, v_x1_1211_, v_x2_1212_, v_x3_1213_);
return v___x_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__1(lean_object* v___x_1215_, lean_object* v___f_1216_, lean_object* v_acc_1217_, lean_object* v_l_1218_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1215_, v___f_1216_, v_acc_1217_, v_l_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg(lean_object* v_f_1220_, lean_object* v_init_1221_, lean_object* v_b_1222_){
_start:
{
lean_object* v___x_1223_; lean_object* v_buckets_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; uint8_t v___x_1227_; 
v___x_1223_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1224_ = lean_ctor_get(v_b_1222_, 1);
lean_inc_ref(v_buckets_1224_);
lean_dec_ref(v_b_1222_);
v___x_1225_ = lean_unsigned_to_nat(0u);
v___x_1226_ = lean_array_get_size(v_buckets_1224_);
v___x_1227_ = lean_nat_dec_lt(v___x_1225_, v___x_1226_);
if (v___x_1227_ == 0)
{
lean_dec_ref(v_buckets_1224_);
lean_dec(v_f_1220_);
return v_init_1221_;
}
else
{
lean_object* v___f_1228_; lean_object* v___f_1229_; size_t v___x_1230_; size_t v___x_1231_; lean_object* v___x_1232_; 
v___f_1228_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1228_, 0, v_f_1220_);
v___f_1229_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1229_, 0, v___x_1223_);
lean_closure_set(v___f_1229_, 1, v___f_1228_);
v___x_1230_ = ((size_t)0ULL);
v___x_1231_ = lean_usize_of_nat(v___x_1226_);
v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1223_, v___f_1229_, v_buckets_1224_, v___x_1230_, v___x_1231_, v_init_1221_);
return v___x_1232_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold(lean_object* v_00_u03b1_1233_, lean_object* v_00_u03b2_1234_, lean_object* v_x_1235_, lean_object* v_x_1236_, lean_object* v_00_u03b3_1237_, lean_object* v_f_1238_, lean_object* v_init_1239_, lean_object* v_b_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v_buckets_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; uint8_t v___x_1245_; 
v___x_1241_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1242_ = lean_ctor_get(v_b_1240_, 1);
lean_inc_ref(v_buckets_1242_);
lean_dec_ref(v_b_1240_);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_array_get_size(v_buckets_1242_);
v___x_1245_ = lean_nat_dec_lt(v___x_1243_, v___x_1244_);
if (v___x_1245_ == 0)
{
lean_dec_ref(v_buckets_1242_);
lean_dec(v_f_1238_);
return v_init_1239_;
}
else
{
lean_object* v___f_1246_; lean_object* v___f_1247_; size_t v___x_1248_; size_t v___x_1249_; lean_object* v___x_1250_; 
v___f_1246_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1246_, 0, v_f_1238_);
v___f_1247_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1247_, 0, v___x_1241_);
lean_closure_set(v___f_1247_, 1, v___f_1246_);
v___x_1248_ = ((size_t)0ULL);
v___x_1249_ = lean_usize_of_nat(v___x_1244_);
v___x_1250_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1241_, v___f_1247_, v_buckets_1242_, v___x_1248_, v___x_1249_, v_init_1239_);
return v___x_1250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___boxed(lean_object* v_00_u03b1_1251_, lean_object* v_00_u03b2_1252_, lean_object* v_x_1253_, lean_object* v_x_1254_, lean_object* v_00_u03b3_1255_, lean_object* v_f_1256_, lean_object* v_init_1257_, lean_object* v_b_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Std_HashMap_fold(v_00_u03b1_1251_, v_00_u03b2_1252_, v_x_1253_, v_x_1254_, v_00_u03b3_1255_, v_f_1256_, v_init_1257_, v_b_1258_);
lean_dec_ref(v_x_1254_);
lean_dec_ref(v_x_1253_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__0(lean_object* v_f_1260_, lean_object* v_x_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_apply_2(v_f_1260_, v___y_1262_, v___y_1263_);
return v___x_1264_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__1(lean_object* v_inst_1265_, lean_object* v___f_1266_, lean_object* v_x_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_box(0);
v___x_1270_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_1265_, v___f_1266_, v___x_1269_, v___y_1268_);
return v___x_1270_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg(lean_object* v_inst_1271_, lean_object* v_f_1272_, lean_object* v_b_1273_){
_start:
{
lean_object* v_toApplicative_1274_; lean_object* v_buckets_1275_; lean_object* v_toPure_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_toApplicative_1274_ = lean_ctor_get(v_inst_1271_, 0);
v_buckets_1275_ = lean_ctor_get(v_b_1273_, 1);
lean_inc_ref(v_buckets_1275_);
lean_dec_ref(v_b_1273_);
v_toPure_1276_ = lean_ctor_get(v_toApplicative_1274_, 1);
v___x_1277_ = lean_unsigned_to_nat(0u);
v___x_1278_ = lean_array_get_size(v_buckets_1275_);
v___x_1279_ = lean_box(0);
v___x_1280_ = lean_nat_dec_lt(v___x_1277_, v___x_1278_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; 
lean_inc(v_toPure_1276_);
lean_dec_ref(v_buckets_1275_);
lean_dec(v_f_1272_);
lean_dec_ref(v_inst_1271_);
v___x_1281_ = lean_apply_2(v_toPure_1276_, lean_box(0), v___x_1279_);
return v___x_1281_;
}
else
{
lean_object* v___f_1282_; lean_object* v___f_1283_; size_t v___x_1284_; size_t v___x_1285_; lean_object* v___x_1286_; 
v___f_1282_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1282_, 0, v_f_1272_);
lean_inc_ref(v_inst_1271_);
v___f_1283_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1283_, 0, v_inst_1271_);
lean_closure_set(v___f_1283_, 1, v___f_1282_);
v___x_1284_ = ((size_t)0ULL);
v___x_1285_ = lean_usize_of_nat(v___x_1278_);
v___x_1286_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1271_, v___f_1283_, v_buckets_1275_, v___x_1284_, v___x_1285_, v___x_1279_);
return v___x_1286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM(lean_object* v_00_u03b1_1287_, lean_object* v_00_u03b2_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_, lean_object* v_m_1291_, lean_object* v_inst_1292_, lean_object* v_f_1293_, lean_object* v_b_1294_){
_start:
{
lean_object* v_toApplicative_1295_; lean_object* v_buckets_1296_; lean_object* v_toPure_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_toApplicative_1295_ = lean_ctor_get(v_inst_1292_, 0);
v_buckets_1296_ = lean_ctor_get(v_b_1294_, 1);
lean_inc_ref(v_buckets_1296_);
lean_dec_ref(v_b_1294_);
v_toPure_1297_ = lean_ctor_get(v_toApplicative_1295_, 1);
v___x_1298_ = lean_unsigned_to_nat(0u);
v___x_1299_ = lean_array_get_size(v_buckets_1296_);
v___x_1300_ = lean_box(0);
v___x_1301_ = lean_nat_dec_lt(v___x_1298_, v___x_1299_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; 
lean_inc(v_toPure_1297_);
lean_dec_ref(v_buckets_1296_);
lean_dec(v_f_1293_);
lean_dec_ref(v_inst_1292_);
v___x_1302_ = lean_apply_2(v_toPure_1297_, lean_box(0), v___x_1300_);
return v___x_1302_;
}
else
{
lean_object* v___f_1303_; lean_object* v___f_1304_; size_t v___x_1305_; size_t v___x_1306_; lean_object* v___x_1307_; 
v___f_1303_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1303_, 0, v_f_1293_);
lean_inc_ref(v_inst_1292_);
v___f_1304_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1304_, 0, v_inst_1292_);
lean_closure_set(v___f_1304_, 1, v___f_1303_);
v___x_1305_ = ((size_t)0ULL);
v___x_1306_ = lean_usize_of_nat(v___x_1299_);
v___x_1307_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1292_, v___f_1304_, v_buckets_1296_, v___x_1305_, v___x_1306_, v___x_1300_);
return v___x_1307_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___boxed(lean_object* v_00_u03b1_1308_, lean_object* v_00_u03b2_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_, lean_object* v_m_1312_, lean_object* v_inst_1313_, lean_object* v_f_1314_, lean_object* v_b_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_Std_HashMap_forM(v_00_u03b1_1308_, v_00_u03b2_1309_, v_x_1310_, v_x_1311_, v_m_1312_, v_inst_1313_, v_f_1314_, v_b_1315_);
lean_dec_ref(v_x_1311_);
lean_dec_ref(v_x_1310_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg___lam__0(lean_object* v_inst_1317_, lean_object* v_f_1318_, lean_object* v_a_1319_, lean_object* v_x_1320_, lean_object* v___y_1321_){
_start:
{
lean_object* v___x_1322_; 
v___x_1322_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1317_, v_f_1318_, v_a_1319_, v___y_1321_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg(lean_object* v_inst_1323_, lean_object* v_f_1324_, lean_object* v_init_1325_, lean_object* v_b_1326_){
_start:
{
lean_object* v_buckets_1327_; lean_object* v___f_1328_; size_t v_sz_1329_; size_t v___x_1330_; lean_object* v___x_1331_; 
v_buckets_1327_ = lean_ctor_get(v_b_1326_, 1);
lean_inc_ref(v_buckets_1327_);
lean_dec_ref(v_b_1326_);
lean_inc_ref(v_inst_1323_);
v___f_1328_ = lean_alloc_closure((void*)(l_Std_HashMap_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1328_, 0, v_inst_1323_);
lean_closure_set(v___f_1328_, 1, v_f_1324_);
v_sz_1329_ = lean_array_size(v_buckets_1327_);
v___x_1330_ = ((size_t)0ULL);
v___x_1331_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1323_, v_buckets_1327_, v___f_1328_, v_sz_1329_, v___x_1330_, v_init_1325_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn(lean_object* v_00_u03b1_1332_, lean_object* v_00_u03b2_1333_, lean_object* v_x_1334_, lean_object* v_x_1335_, lean_object* v_m_1336_, lean_object* v_inst_1337_, lean_object* v_00_u03b3_1338_, lean_object* v_f_1339_, lean_object* v_init_1340_, lean_object* v_b_1341_){
_start:
{
lean_object* v_buckets_1342_; lean_object* v___f_1343_; size_t v_sz_1344_; size_t v___x_1345_; lean_object* v___x_1346_; 
v_buckets_1342_ = lean_ctor_get(v_b_1341_, 1);
lean_inc_ref(v_buckets_1342_);
lean_dec_ref(v_b_1341_);
lean_inc_ref(v_inst_1337_);
v___f_1343_ = lean_alloc_closure((void*)(l_Std_HashMap_forIn___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1343_, 0, v_inst_1337_);
lean_closure_set(v___f_1343_, 1, v_f_1339_);
v_sz_1344_ = lean_array_size(v_buckets_1342_);
v___x_1345_ = ((size_t)0ULL);
v___x_1346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1337_, v_buckets_1342_, v___f_1343_, v_sz_1344_, v___x_1345_, v_init_1340_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___boxed(lean_object* v_00_u03b1_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v_m_1351_, lean_object* v_inst_1352_, lean_object* v_00_u03b3_1353_, lean_object* v_f_1354_, lean_object* v_init_1355_, lean_object* v_b_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Std_HashMap_forIn(v_00_u03b1_1347_, v_00_u03b2_1348_, v_x_1349_, v_x_1350_, v_m_1351_, v_inst_1352_, v_00_u03b3_1353_, v_f_1354_, v_init_1355_, v_b_1356_);
lean_dec_ref(v_x_1350_);
lean_dec_ref(v_x_1349_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1358_, lean_object* v_x_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___y_1360_);
lean_ctor_set(v___x_1362_, 1, v___y_1361_);
v___x_1363_ = lean_apply_1(v_f_1358_, v___x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__2(lean_object* v_inst_1364_, lean_object* v_m_1365_, lean_object* v_f_1366_){
_start:
{
lean_object* v_toApplicative_1367_; lean_object* v_buckets_1368_; lean_object* v_toPure_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_toApplicative_1367_ = lean_ctor_get(v_inst_1364_, 0);
v_buckets_1368_ = lean_ctor_get(v_m_1365_, 1);
lean_inc_ref(v_buckets_1368_);
lean_dec_ref(v_m_1365_);
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
lean_dec(v_f_1366_);
lean_dec_ref(v_inst_1364_);
v___x_1374_ = lean_apply_2(v_toPure_1369_, lean_box(0), v___x_1372_);
return v___x_1374_;
}
else
{
lean_object* v___f_1375_; lean_object* v___f_1376_; size_t v___x_1377_; size_t v___x_1378_; lean_object* v___x_1379_; 
v___f_1375_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1375_, 0, v_f_1366_);
lean_inc_ref(v_inst_1364_);
v___f_1376_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1376_, 0, v_inst_1364_);
lean_closure_set(v___f_1376_, 1, v___f_1375_);
v___x_1377_ = ((size_t)0ULL);
v___x_1378_ = lean_usize_of_nat(v___x_1371_);
v___x_1379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v_inst_1364_, v___f_1376_, v_buckets_1368_, v___x_1377_, v___x_1378_, v___x_1372_);
return v___x_1379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg(lean_object* v_inst_1380_){
_start:
{
lean_object* v___f_1381_; 
v___f_1381_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1381_, 0, v_inst_1380_);
return v___f_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad(lean_object* v_00_u03b1_1382_, lean_object* v_00_u03b2_1383_, lean_object* v_inst_1384_, lean_object* v_inst_1385_, lean_object* v_m_1386_, lean_object* v_inst_1387_){
_start:
{
lean_object* v___f_1388_; 
v___f_1388_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__2), 3, 1);
lean_closure_set(v___f_1388_, 0, v_inst_1387_);
return v___f_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_1389_, lean_object* v_00_u03b2_1390_, lean_object* v_inst_1391_, lean_object* v_inst_1392_, lean_object* v_m_1393_, lean_object* v_inst_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Std_HashMap_instForMProdOfMonad(v_00_u03b1_1389_, v_00_u03b2_1390_, v_inst_1391_, v_inst_1392_, v_m_1393_, v_inst_1394_);
lean_dec_ref(v_inst_1392_);
lean_dec_ref(v_inst_1391_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1396_, lean_object* v_a_1397_, lean_object* v_b_1398_, lean_object* v_acc_1399_){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1400_, 0, v_a_1397_);
lean_ctor_set(v___x_1400_, 1, v_b_1398_);
v___x_1401_ = lean_apply_2(v_f_1396_, v___x_1400_, v_acc_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1402_, lean_object* v___f_1403_, lean_object* v_a_1404_, lean_object* v_x_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go(lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_inst_1402_, v___f_1403_, v_a_1404_, v___y_1406_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__2(lean_object* v_inst_1408_, lean_object* v_00_u03b2_1409_, lean_object* v_m_1410_, lean_object* v_init_1411_, lean_object* v_f_1412_){
_start:
{
lean_object* v_buckets_1413_; lean_object* v___f_1414_; lean_object* v___f_1415_; size_t v_sz_1416_; size_t v___x_1417_; lean_object* v___x_1418_; 
v_buckets_1413_ = lean_ctor_get(v_m_1410_, 1);
lean_inc_ref(v_buckets_1413_);
lean_dec_ref(v_m_1410_);
v___f_1414_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1414_, 0, v_f_1412_);
lean_inc_ref(v_inst_1408_);
v___f_1415_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1415_, 0, v_inst_1408_);
lean_closure_set(v___f_1415_, 1, v___f_1414_);
v_sz_1416_ = lean_array_size(v_buckets_1413_);
v___x_1417_ = ((size_t)0ULL);
v___x_1418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v_inst_1408_, v_buckets_1413_, v___f_1415_, v_sz_1416_, v___x_1417_, v_init_1411_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1419_){
_start:
{
lean_object* v___f_1420_; 
v___f_1420_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1420_, 0, v_inst_1419_);
return v___f_1420_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad(lean_object* v_00_u03b1_1421_, lean_object* v_00_u03b2_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_m_1425_, lean_object* v_inst_1426_){
_start:
{
lean_object* v___f_1427_; 
v___f_1427_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_1427_, 0, v_inst_1426_);
return v___f_1427_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1428_, lean_object* v_00_u03b2_1429_, lean_object* v_inst_1430_, lean_object* v_inst_1431_, lean_object* v_m_1432_, lean_object* v_inst_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_Std_HashMap_instForInProdOfMonad(v_00_u03b1_1428_, v_00_u03b2_1429_, v_inst_1430_, v_inst_1431_, v_m_1432_, v_inst_1433_);
lean_dec_ref(v_inst_1431_);
lean_dec_ref(v_inst_1430_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___redArg(lean_object* v_f_1435_, lean_object* v_m_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1435_, v_m_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter(lean_object* v_00_u03b1_1438_, lean_object* v_00_u03b2_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_f_1442_, lean_object* v_m_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1442_, v_m_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___boxed(lean_object* v_00_u03b1_1445_, lean_object* v_00_u03b2_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_, lean_object* v_f_1449_, lean_object* v_m_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Std_HashMap_filter(v_00_u03b1_1445_, v_00_u03b2_1446_, v_x_1447_, v_x_1448_, v_f_1449_, v_m_1450_);
lean_dec_ref(v_x_1448_);
lean_dec_ref(v_x_1447_);
return v_res_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify___redArg(lean_object* v_x_1452_, lean_object* v_x_1453_, lean_object* v_m_1454_, lean_object* v_a_1455_, lean_object* v_f_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1452_, v_x_1453_, v_m_1454_, v_a_1455_, v_f_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify(lean_object* v_00_u03b1_1458_, lean_object* v_00_u03b2_1459_, lean_object* v_x_1460_, lean_object* v_x_1461_, lean_object* v_m_1462_, lean_object* v_a_1463_, lean_object* v_f_1464_){
_start:
{
lean_object* v___x_1465_; 
v___x_1465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_modify___redArg(v_x_1460_, v_x_1461_, v_m_1462_, v_a_1463_, v_f_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter___redArg(lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v_m_1468_, lean_object* v_a_1469_, lean_object* v_f_1470_){
_start:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1466_, v_x_1467_, v_m_1468_, v_a_1469_, v_f_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter(lean_object* v_00_u03b1_1472_, lean_object* v_00_u03b2_1473_, lean_object* v_x_1474_, lean_object* v_x_1475_, lean_object* v_m_1476_, lean_object* v_a_1477_, lean_object* v_f_1478_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_x_1474_, v_x_1475_, v_m_1476_, v_a_1477_, v_f_1478_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany___redArg(lean_object* v_x_1480_, lean_object* v_x_1481_, lean_object* v_inst_1482_, lean_object* v_m_1483_, lean_object* v_l_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_1482_, v_x_1480_, v_x_1481_, v_m_1483_, v_l_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany(lean_object* v_00_u03b1_1486_, lean_object* v_00_u03b2_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v_00_u03c1_1490_, lean_object* v_inst_1491_, lean_object* v_m_1492_, lean_object* v_l_1493_){
_start:
{
lean_object* v___x_1494_; 
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_1491_, v_x_1488_, v_x_1489_, v_m_1492_, v_l_1493_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit___redArg(lean_object* v_x_1495_, lean_object* v_x_1496_, lean_object* v_inst_1497_, lean_object* v_m_1498_, lean_object* v_l_1499_){
_start:
{
lean_object* v___x_1500_; 
v___x_1500_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1497_, v_x_1495_, v_x_1496_, v_m_1498_, v_l_1499_);
return v___x_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit(lean_object* v_00_u03b1_1501_, lean_object* v_x_1502_, lean_object* v_x_1503_, lean_object* v_00_u03c1_1504_, lean_object* v_inst_1505_, lean_object* v_m_1506_, lean_object* v_l_1507_){
_start:
{
lean_object* v___x_1508_; 
v___x_1508_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1505_, v_x_1502_, v_x_1503_, v_m_1506_, v_l_1507_);
return v___x_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__0(lean_object* v_x1_1509_, lean_object* v_x2_1510_, lean_object* v_x3_1511_){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v_x2_1510_);
lean_ctor_set(v___x_1512_, 1, v_x3_1511_);
v___x_1513_ = lean_array_push(v_x1_1509_, v___x_1512_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__1(lean_object* v___x_1514_, lean_object* v___f_1515_, lean_object* v_acc_1516_, lean_object* v_l_1517_){
_start:
{
lean_object* v___x_1518_; 
v___x_1518_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1514_, v___f_1515_, v_acc_1516_, v_l_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg(lean_object* v_m_1523_){
_start:
{
lean_object* v_size_1524_; lean_object* v_buckets_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; uint8_t v___x_1530_; 
v_size_1524_ = lean_ctor_get(v_m_1523_, 0);
lean_inc(v_size_1524_);
v_buckets_1525_ = lean_ctor_get(v_m_1523_, 1);
lean_inc_ref(v_buckets_1525_);
lean_dec_ref(v_m_1523_);
v___x_1526_ = lean_mk_empty_array_with_capacity(v_size_1524_);
lean_dec(v_size_1524_);
v___x_1527_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = lean_array_get_size(v_buckets_1525_);
v___x_1530_ = lean_nat_dec_lt(v___x_1528_, v___x_1529_);
if (v___x_1530_ == 0)
{
lean_dec_ref(v_buckets_1525_);
return v___x_1526_;
}
else
{
lean_object* v___f_1531_; size_t v___x_1532_; size_t v___x_1533_; lean_object* v___x_1534_; 
v___f_1531_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__1));
v___x_1532_ = ((size_t)0ULL);
v___x_1533_ = lean_usize_of_nat(v___x_1529_);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1527_, v___f_1531_, v_buckets_1525_, v___x_1532_, v___x_1533_, v___x_1526_);
return v___x_1534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray(lean_object* v_00_u03b1_1535_, lean_object* v_00_u03b2_1536_, lean_object* v_x_1537_, lean_object* v_x_1538_, lean_object* v_m_1539_){
_start:
{
lean_object* v_size_1540_; lean_object* v_buckets_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
v_size_1540_ = lean_ctor_get(v_m_1539_, 0);
lean_inc(v_size_1540_);
v_buckets_1541_ = lean_ctor_get(v_m_1539_, 1);
lean_inc_ref(v_buckets_1541_);
lean_dec_ref(v_m_1539_);
v___x_1542_ = lean_mk_empty_array_with_capacity(v_size_1540_);
lean_dec(v_size_1540_);
v___x_1543_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1544_ = lean_unsigned_to_nat(0u);
v___x_1545_ = lean_array_get_size(v_buckets_1541_);
v___x_1546_ = lean_nat_dec_lt(v___x_1544_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_dec_ref(v_buckets_1541_);
return v___x_1542_;
}
else
{
lean_object* v___f_1547_; size_t v___x_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
v___f_1547_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__1));
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = lean_usize_of_nat(v___x_1545_);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1543_, v___f_1547_, v_buckets_1541_, v___x_1548_, v___x_1549_, v___x_1542_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___boxed(lean_object* v_00_u03b1_1551_, lean_object* v_00_u03b2_1552_, lean_object* v_x_1553_, lean_object* v_x_1554_, lean_object* v_m_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Std_HashMap_toArray(v_00_u03b1_1551_, v_00_u03b2_1552_, v_x_1553_, v_x_1554_, v_m_1555_);
lean_dec_ref(v_x_1554_);
lean_dec_ref(v_x_1553_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0(lean_object* v_x1_1557_, lean_object* v_x2_1558_, lean_object* v_x3_1559_){
_start:
{
lean_object* v___x_1560_; 
v___x_1560_ = lean_array_push(v_x1_1557_, v_x2_1558_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0___boxed(lean_object* v_x1_1561_, lean_object* v_x2_1562_, lean_object* v_x3_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Std_HashMap_keysArray___redArg___lam__0(v_x1_1561_, v_x2_1562_, v_x3_1563_);
lean_dec(v_x3_1563_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__1(lean_object* v___x_1565_, lean_object* v___f_1566_, lean_object* v_acc_1567_, lean_object* v_l_1568_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1565_, v___f_1566_, v_acc_1567_, v_l_1568_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg(lean_object* v_m_1574_){
_start:
{
lean_object* v_size_1575_; lean_object* v_buckets_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v_size_1575_ = lean_ctor_get(v_m_1574_, 0);
lean_inc(v_size_1575_);
v_buckets_1576_ = lean_ctor_get(v_m_1574_, 1);
lean_inc_ref(v_buckets_1576_);
lean_dec_ref(v_m_1574_);
v___x_1577_ = lean_mk_empty_array_with_capacity(v_size_1575_);
lean_dec(v_size_1575_);
v___x_1578_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_1579_ = lean_unsigned_to_nat(0u);
v___x_1580_ = lean_array_get_size(v_buckets_1576_);
v___x_1581_ = lean_nat_dec_lt(v___x_1579_, v___x_1580_);
if (v___x_1581_ == 0)
{
lean_dec_ref(v_buckets_1576_);
return v___x_1577_;
}
else
{
lean_object* v___f_1582_; size_t v___x_1583_; size_t v___x_1584_; lean_object* v___x_1585_; 
v___f_1582_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__1));
v___x_1583_ = ((size_t)0ULL);
v___x_1584_ = lean_usize_of_nat(v___x_1580_);
v___x_1585_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1578_, v___f_1582_, v_buckets_1576_, v___x_1583_, v___x_1584_, v___x_1577_);
return v___x_1585_;
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
lean_object* v___f_1598_; size_t v___x_1599_; size_t v___x_1600_; lean_object* v___x_1601_; 
v___f_1598_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__1));
v___x_1599_ = ((size_t)0ULL);
v___x_1600_ = lean_usize_of_nat(v___x_1596_);
v___x_1601_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1594_, v___f_1598_, v_buckets_1592_, v___x_1599_, v___x_1600_, v___x_1593_);
return v___x_1601_;
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
uint8_t l_Std_HashMap_all___redArg(lean_object* v_m_1636_, lean_object* v_p_1637_){
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
LEAN_EXPORT void l_Std_HashMap_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1636_ = stack[0].m_obj;
lean_object* v_p_1637_ = stack[1].m_obj;
uint8_t v_res_1651_;
v_res_1651_ = l_Std_HashMap_all___redArg(v_m_1636_, v_p_1637_);
stack->m_num = v_res_1651_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___boxed(lean_object* v_m_1652_, lean_object* v_p_1653_){
_start:
{
uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_res_1654_ = l_Std_HashMap_all___redArg(v_m_1652_, v_p_1653_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
uint8_t l_Std_HashMap_all(lean_object* v_00_u03b1_1656_, lean_object* v_00_u03b2_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_, lean_object* v_m_1660_, lean_object* v_p_1661_){
_start:
{
lean_object* v___x_1662_; lean_object* v_buckets_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___f_1666_; lean_object* v___f_1667_; size_t v_sz_1668_; size_t v___x_1669_; lean_object* v___x_1670_; lean_object* v_fst_1671_; 
v___x_1662_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1663_ = lean_ctor_get(v_m_1660_, 1);
lean_inc_ref(v_buckets_1663_);
lean_dec_ref(v_m_1660_);
v___x_1664_ = lean_box(0);
v___x_1665_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1666_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1666_, 0, v_p_1661_);
lean_closure_set(v___f_1666_, 1, v___x_1664_);
lean_closure_set(v___f_1666_, 2, v___x_1665_);
v___f_1667_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1667_, 0, v___x_1662_);
lean_closure_set(v___f_1667_, 1, v___f_1666_);
v_sz_1668_ = lean_array_size(v_buckets_1663_);
v___x_1669_ = ((size_t)0ULL);
v___x_1670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1662_, v_buckets_1663_, v___f_1667_, v_sz_1668_, v___x_1669_, v___x_1665_);
v_fst_1671_ = lean_ctor_get(v___x_1670_, 0);
lean_inc(v_fst_1671_);
lean_dec(v___x_1670_);
if (lean_obj_tag(v_fst_1671_) == 0)
{
uint8_t v___x_1672_; 
v___x_1672_ = 1;
return v___x_1672_;
}
else
{
lean_object* v_val_1673_; uint8_t v___x_1674_; 
v_val_1673_ = lean_ctor_get(v_fst_1671_, 0);
lean_inc(v_val_1673_);
lean_dec_ref_known(v_fst_1671_, 1);
v___x_1674_ = lean_unbox(v_val_1673_);
lean_dec(v_val_1673_);
return v___x_1674_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1658_ = stack[2].m_obj;
lean_object* v_x_1659_ = stack[3].m_obj;
lean_object* v_m_1660_ = stack[4].m_obj;
lean_object* v_p_1661_ = stack[5].m_obj;
uint8_t v_res_1675_;
v_res_1675_ = l_Std_HashMap_all(lean_box(0), lean_box(0), v_x_1658_, v_x_1659_, v_m_1660_, v_p_1661_);
stack->m_num = v_res_1675_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___boxed(lean_object* v_00_u03b1_1676_, lean_object* v_00_u03b2_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_m_1680_, lean_object* v_p_1681_){
_start:
{
uint8_t v_res_1682_; lean_object* v_r_1683_; 
v_res_1682_ = l_Std_HashMap_all(v_00_u03b1_1676_, v_00_u03b2_1677_, v_x_1678_, v_x_1679_, v_m_1680_, v_p_1681_);
lean_dec_ref(v_x_1679_);
lean_dec_ref(v_x_1678_);
v_r_1683_ = lean_box(v_res_1682_);
return v_r_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0(lean_object* v_p_1684_, lean_object* v___x_1685_, lean_object* v___x_1686_, lean_object* v_a_1687_, lean_object* v_b_1688_, lean_object* v_acc_1689_){
_start:
{
lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___x_1690_ = lean_apply_2(v_p_1684_, v_a_1687_, v_b_1688_);
v___x_1691_ = lean_unbox(v___x_1690_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1692_, 0, v___x_1685_);
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
lean_dec_ref(v___x_1685_);
v___x_1693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1690_);
v___x_1694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1694_, 0, v___x_1693_);
lean_ctor_set(v___x_1694_, 1, v___x_1686_);
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0___boxed(lean_object* v_p_1696_, lean_object* v___x_1697_, lean_object* v___x_1698_, lean_object* v_a_1699_, lean_object* v_b_1700_, lean_object* v_acc_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Std_HashMap_any___redArg___lam__0(v_p_1696_, v___x_1697_, v___x_1698_, v_a_1699_, v_b_1700_, v_acc_1701_);
lean_dec_ref(v_acc_1701_);
return v_res_1702_;
}
}
uint8_t l_Std_HashMap_any___redArg(lean_object* v_m_1703_, lean_object* v_p_1704_){
_start:
{
lean_object* v___x_1705_; lean_object* v_buckets_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___f_1709_; lean_object* v___f_1710_; size_t v_sz_1711_; size_t v___x_1712_; lean_object* v___x_1713_; lean_object* v_fst_1714_; 
v___x_1705_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1706_ = lean_ctor_get(v_m_1703_, 1);
lean_inc_ref(v_buckets_1706_);
lean_dec_ref(v_m_1703_);
v___x_1707_ = lean_box(0);
v___x_1708_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1709_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1709_, 0, v_p_1704_);
lean_closure_set(v___f_1709_, 1, v___x_1708_);
lean_closure_set(v___f_1709_, 2, v___x_1707_);
v___f_1710_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1710_, 0, v___x_1705_);
lean_closure_set(v___f_1710_, 1, v___f_1709_);
v_sz_1711_ = lean_array_size(v_buckets_1706_);
v___x_1712_ = ((size_t)0ULL);
v___x_1713_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1705_, v_buckets_1706_, v___f_1710_, v_sz_1711_, v___x_1712_, v___x_1708_);
v_fst_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_fst_1714_);
lean_dec(v___x_1713_);
if (lean_obj_tag(v_fst_1714_) == 0)
{
uint8_t v___x_1715_; 
v___x_1715_ = 0;
return v___x_1715_;
}
else
{
lean_object* v_val_1716_; uint8_t v___x_1717_; 
v_val_1716_ = lean_ctor_get(v_fst_1714_, 0);
lean_inc(v_val_1716_);
lean_dec_ref_known(v_fst_1714_, 1);
v___x_1717_ = lean_unbox(v_val_1716_);
lean_dec(v_val_1716_);
return v___x_1717_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_m_1703_ = stack[0].m_obj;
lean_object* v_p_1704_ = stack[1].m_obj;
uint8_t v_res_1718_;
v_res_1718_ = l_Std_HashMap_any___redArg(v_m_1703_, v_p_1704_);
stack->m_num = v_res_1718_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___boxed(lean_object* v_m_1719_, lean_object* v_p_1720_){
_start:
{
uint8_t v_res_1721_; lean_object* v_r_1722_; 
v_res_1721_ = l_Std_HashMap_any___redArg(v_m_1719_, v_p_1720_);
v_r_1722_ = lean_box(v_res_1721_);
return v_r_1722_;
}
}
uint8_t l_Std_HashMap_any(lean_object* v_00_u03b1_1723_, lean_object* v_00_u03b2_1724_, lean_object* v_x_1725_, lean_object* v_x_1726_, lean_object* v_m_1727_, lean_object* v_p_1728_){
_start:
{
lean_object* v___x_1729_; lean_object* v_buckets_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___f_1733_; lean_object* v___f_1734_; size_t v_sz_1735_; size_t v___x_1736_; lean_object* v___x_1737_; lean_object* v_fst_1738_; 
v___x_1729_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1730_ = lean_ctor_get(v_m_1727_, 1);
lean_inc_ref(v_buckets_1730_);
lean_dec_ref(v_m_1727_);
v___x_1731_ = lean_box(0);
v___x_1732_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_1733_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1733_, 0, v_p_1728_);
lean_closure_set(v___f_1733_, 1, v___x_1732_);
lean_closure_set(v___f_1733_, 2, v___x_1731_);
v___f_1734_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1734_, 0, v___x_1729_);
lean_closure_set(v___f_1734_, 1, v___f_1733_);
v_sz_1735_ = lean_array_size(v_buckets_1730_);
v___x_1736_ = ((size_t)0ULL);
v___x_1737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1729_, v_buckets_1730_, v___f_1734_, v_sz_1735_, v___x_1736_, v___x_1732_);
v_fst_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_fst_1738_);
lean_dec(v___x_1737_);
if (lean_obj_tag(v_fst_1738_) == 0)
{
uint8_t v___x_1739_; 
v___x_1739_ = 0;
return v___x_1739_;
}
else
{
lean_object* v_val_1740_; uint8_t v___x_1741_; 
v_val_1740_ = lean_ctor_get(v_fst_1738_, 0);
lean_inc(v_val_1740_);
lean_dec_ref_known(v_fst_1738_, 1);
v___x_1741_ = lean_unbox(v_val_1740_);
lean_dec(v_val_1740_);
return v___x_1741_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1725_ = stack[2].m_obj;
lean_object* v_x_1726_ = stack[3].m_obj;
lean_object* v_m_1727_ = stack[4].m_obj;
lean_object* v_p_1728_ = stack[5].m_obj;
uint8_t v_res_1742_;
v_res_1742_ = l_Std_HashMap_any(lean_box(0), lean_box(0), v_x_1725_, v_x_1726_, v_m_1727_, v_p_1728_);
stack->m_num = v_res_1742_;
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
lean_object* v___x_1770_; lean_object* v_size_1771_; lean_object* v_buckets_1772_; lean_object* v_size_1773_; uint8_t v___x_1774_; 
v___x_1770_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_size_1771_ = lean_ctor_get(v_m_u2081_1768_, 0);
v_buckets_1772_ = lean_ctor_get(v_m_u2081_1768_, 1);
v_size_1773_ = lean_ctor_get(v_m_u2082_1769_, 0);
v___x_1774_ = lean_nat_dec_le(v_size_1771_, v_size_1773_);
if (v___x_1774_ == 0)
{
lean_object* v___f_1775_; lean_object* v___x_1776_; 
v___f_1775_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1776_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1775_, v_inst_1766_, v_inst_1767_, v_m_u2081_1768_, v_m_u2082_1769_);
return v___x_1776_;
}
else
{
lean_object* v___f_1777_; lean_object* v___f_1778_; size_t v_sz_1779_; size_t v___x_1780_; lean_object* v___x_1781_; 
lean_inc_ref(v_buckets_1772_);
lean_dec_ref(v_m_u2081_1768_);
v___f_1777_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1777_, 0, v_inst_1766_);
lean_closure_set(v___f_1777_, 1, v_inst_1767_);
v___f_1778_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1778_, 0, v___x_1770_);
lean_closure_set(v___f_1778_, 1, v___f_1777_);
v_sz_1779_ = lean_array_size(v_buckets_1772_);
v___x_1780_ = ((size_t)0ULL);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1770_, v_buckets_1772_, v___f_1778_, v_sz_1779_, v___x_1780_, v_m_u2082_1769_);
return v___x_1781_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union(lean_object* v_00_u03b1_1782_, lean_object* v_00_u03b2_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_m_u2081_1786_, lean_object* v_m_u2082_1787_){
_start:
{
lean_object* v___x_1788_; lean_object* v_size_1789_; lean_object* v_buckets_1790_; lean_object* v_size_1791_; uint8_t v___x_1792_; 
v___x_1788_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_size_1789_ = lean_ctor_get(v_m_u2081_1786_, 0);
v_buckets_1790_ = lean_ctor_get(v_m_u2081_1786_, 1);
v_size_1791_ = lean_ctor_get(v_m_u2082_1787_, 0);
v___x_1792_ = lean_nat_dec_le(v_size_1789_, v_size_1791_);
if (v___x_1792_ == 0)
{
lean_object* v___f_1793_; lean_object* v___x_1794_; 
v___f_1793_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1794_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1793_, v_inst_1784_, v_inst_1785_, v_m_u2081_1786_, v_m_u2082_1787_);
return v___x_1794_;
}
else
{
lean_object* v___f_1795_; lean_object* v___f_1796_; size_t v_sz_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
lean_inc_ref(v_buckets_1790_);
lean_dec_ref(v_m_u2081_1786_);
v___f_1795_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1795_, 0, v_inst_1784_);
lean_closure_set(v___f_1795_, 1, v_inst_1785_);
v___f_1796_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__1), 5, 2);
lean_closure_set(v___f_1796_, 0, v___x_1788_);
lean_closure_set(v___f_1796_, 1, v___f_1795_);
v_sz_1797_ = lean_array_size(v_buckets_1790_);
v___x_1798_ = ((size_t)0ULL);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_1788_, v_buckets_1790_, v___f_1796_, v_sz_1797_, v___x_1798_, v_m_u2082_1787_);
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
uint8_t l_Std_HashMap_beq___redArg(lean_object* v_x_1828_, lean_object* v_inst_1829_, lean_object* v_inst_1830_, lean_object* v_m_u2081_1831_, lean_object* v_m_u2082_1832_){
_start:
{
uint8_t v___x_1833_; 
v___x_1833_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1829_, v_x_1828_, v_inst_1830_, v_m_u2081_1831_, v_m_u2082_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT void l_Std_HashMap_beq___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1828_ = stack[0].m_obj;
lean_object* v_inst_1829_ = stack[1].m_obj;
lean_object* v_inst_1830_ = stack[2].m_obj;
lean_object* v_m_u2081_1831_ = stack[3].m_obj;
lean_object* v_m_u2082_1832_ = stack[4].m_obj;
uint8_t v_res_1834_;
v_res_1834_ = l_Std_HashMap_beq___redArg(v_x_1828_, v_inst_1829_, v_inst_1830_, v_m_u2081_1831_, v_m_u2082_1832_);
stack->m_num = v_res_1834_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___redArg___boxed(lean_object* v_x_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_m_u2081_1838_, lean_object* v_m_u2082_1839_){
_start:
{
uint8_t v_res_1840_; lean_object* v_r_1841_; 
v_res_1840_ = l_Std_HashMap_beq___redArg(v_x_1835_, v_inst_1836_, v_inst_1837_, v_m_u2081_1838_, v_m_u2082_1839_);
v_r_1841_ = lean_box(v_res_1840_);
return v_r_1841_;
}
}
uint8_t l_Std_HashMap_beq(lean_object* v_00_u03b1_1842_, lean_object* v_x_1843_, lean_object* v_00_u03b2_1844_, lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_m_u2081_1847_, lean_object* v_m_u2082_1848_){
_start:
{
uint8_t v___x_1849_; 
v___x_1849_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1845_, v_x_1843_, v_inst_1846_, v_m_u2081_1847_, v_m_u2082_1848_);
return v___x_1849_;
}
}
LEAN_EXPORT void l_Std_HashMap_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1843_ = stack[1].m_obj;
lean_object* v_inst_1845_ = stack[3].m_obj;
lean_object* v_inst_1846_ = stack[4].m_obj;
lean_object* v_m_u2081_1847_ = stack[5].m_obj;
lean_object* v_m_u2082_1848_ = stack[6].m_obj;
uint8_t v_res_1850_;
v_res_1850_ = l_Std_HashMap_beq(lean_box(0), v_x_1843_, lean_box(0), v_inst_1845_, v_inst_1846_, v_m_u2081_1847_, v_m_u2082_1848_);
stack->m_num = v_res_1850_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___boxed(lean_object* v_00_u03b1_1851_, lean_object* v_x_1852_, lean_object* v_00_u03b2_1853_, lean_object* v_inst_1854_, lean_object* v_inst_1855_, lean_object* v_m_u2081_1856_, lean_object* v_m_u2082_1857_){
_start:
{
uint8_t v_res_1858_; lean_object* v_r_1859_; 
v_res_1858_ = l_Std_HashMap_beq(v_00_u03b1_1851_, v_x_1852_, v_00_u03b2_1853_, v_inst_1854_, v_inst_1855_, v_m_u2081_1856_, v_m_u2082_1857_);
v_r_1859_ = lean_box(v_res_1858_);
return v_r_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq___redArg(lean_object* v_x_1860_, lean_object* v_inst_1861_, lean_object* v_inst_1862_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq(lean_object* v_00_u03b1_1864_, lean_object* v_00_u03b2_1865_, lean_object* v_x_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_1869_, 0, lean_box(0));
lean_closure_set(v___x_1869_, 1, v_x_1866_);
lean_closure_set(v___x_1869_, 2, lean_box(0));
lean_closure_set(v___x_1869_, 3, v_inst_1867_);
lean_closure_set(v___x_1869_, 4, v_inst_1868_);
return v___x_1869_;
}
}
uint8_t l_Std_HashMap_diff___redArg___lam__0(lean_object* v_inst_1870_, lean_object* v_inst_1871_, lean_object* v_m_u2082_1872_, uint8_t v___x_1873_, lean_object* v_k_1874_, lean_object* v_x_1875_){
_start:
{
uint8_t v___x_1876_; 
v___x_1876_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1870_, v_inst_1871_, v_m_u2082_1872_, v_k_1874_);
if (v___x_1876_ == 0)
{
return v___x_1873_;
}
else
{
uint8_t v___x_1877_; 
v___x_1877_ = 0;
return v___x_1877_;
}
}
}
LEAN_EXPORT void l_Std_HashMap_diff___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1870_ = stack[0].m_obj;
lean_object* v_inst_1871_ = stack[1].m_obj;
lean_object* v_m_u2082_1872_ = stack[2].m_obj;
uint8_t v___x_1873_ = stack[3].m_num;
lean_object* v_k_1874_ = stack[4].m_obj;
lean_object* v_x_1875_ = stack[5].m_obj;
uint8_t v_res_1878_;
v_res_1878_ = l_Std_HashMap_diff___redArg___lam__0(v_inst_1870_, v_inst_1871_, v_m_u2082_1872_, v___x_1873_, v_k_1874_, v_x_1875_);
stack->m_num = v_res_1878_;
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg___lam__0___boxed(lean_object* v_inst_1879_, lean_object* v_inst_1880_, lean_object* v_m_u2082_1881_, lean_object* v___x_1882_, lean_object* v_k_1883_, lean_object* v_x_1884_){
_start:
{
uint8_t v___x_81__boxed_1885_; uint8_t v_res_1886_; lean_object* v_r_1887_; 
v___x_81__boxed_1885_ = lean_unbox(v___x_1882_);
v_res_1886_ = l_Std_HashMap_diff___redArg___lam__0(v_inst_1879_, v_inst_1880_, v_m_u2082_1881_, v___x_81__boxed_1885_, v_k_1883_, v_x_1884_);
lean_dec(v_x_1884_);
lean_dec_ref(v_m_u2082_1881_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg(lean_object* v_inst_1888_, lean_object* v_inst_1889_, lean_object* v_m_u2081_1890_, lean_object* v_m_u2082_1891_){
_start:
{
lean_object* v_size_1892_; lean_object* v_size_1893_; uint8_t v___x_1894_; 
v_size_1892_ = lean_ctor_get(v_m_u2081_1890_, 0);
v_size_1893_ = lean_ctor_get(v_m_u2082_1891_, 0);
v___x_1894_ = lean_nat_dec_le(v_size_1892_, v_size_1893_);
if (v___x_1894_ == 0)
{
lean_object* v___f_1895_; lean_object* v___x_1896_; 
v___f_1895_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1896_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1895_, v_inst_1888_, v_inst_1889_, v_m_u2081_1890_, v_m_u2082_1891_);
return v___x_1896_;
}
else
{
lean_object* v___x_1897_; lean_object* v___f_1898_; lean_object* v___x_1899_; 
v___x_1897_ = lean_box(v___x_1894_);
v___f_1898_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1898_, 0, v_inst_1888_);
lean_closure_set(v___f_1898_, 1, v_inst_1889_);
lean_closure_set(v___f_1898_, 2, v_m_u2082_1891_);
lean_closure_set(v___f_1898_, 3, v___x_1897_);
v___x_1899_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1898_, v_m_u2081_1890_);
return v___x_1899_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff(lean_object* v_00_u03b1_1900_, lean_object* v_00_u03b2_1901_, lean_object* v_inst_1902_, lean_object* v_inst_1903_, lean_object* v_m_u2081_1904_, lean_object* v_m_u2082_1905_){
_start:
{
lean_object* v_size_1906_; lean_object* v_size_1907_; uint8_t v___x_1908_; 
v_size_1906_ = lean_ctor_get(v_m_u2081_1904_, 0);
v_size_1907_ = lean_ctor_get(v_m_u2082_1905_, 0);
v___x_1908_ = lean_nat_dec_le(v_size_1906_, v_size_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___f_1909_; lean_object* v___x_1910_; 
v___f_1909_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_1910_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1909_, v_inst_1902_, v_inst_1903_, v_m_u2081_1904_, v_m_u2082_1905_);
return v___x_1910_;
}
else
{
lean_object* v___x_1911_; lean_object* v___f_1912_; lean_object* v___x_1913_; 
v___x_1911_ = lean_box(v___x_1908_);
v___f_1912_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1912_, 0, v_inst_1902_);
lean_closure_set(v___f_1912_, 1, v_inst_1903_);
lean_closure_set(v___f_1912_, 2, v_m_u2082_1905_);
lean_closure_set(v___f_1912_, 3, v___x_1911_);
v___x_1913_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1912_, v_m_u2081_1904_);
return v___x_1913_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff___redArg(lean_object* v_inst_1914_, lean_object* v_inst_1915_){
_start:
{
lean_object* v___x_1916_; 
v___x_1916_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_1916_, 0, lean_box(0));
lean_closure_set(v___x_1916_, 1, lean_box(0));
lean_closure_set(v___x_1916_, 2, v_inst_1914_);
lean_closure_set(v___x_1916_, 3, v_inst_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff(lean_object* v_00_u03b1_1917_, lean_object* v_00_u03b2_1918_, lean_object* v_inst_1919_, lean_object* v_inst_1920_){
_start:
{
lean_object* v___x_1921_; 
v___x_1921_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_1921_, 0, lean_box(0));
lean_closure_set(v___x_1921_, 1, lean_box(0));
lean_closure_set(v___x_1921_, 2, v_inst_1919_);
lean_closure_set(v___x_1921_, 3, v_inst_1920_);
return v___x_1921_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__0(lean_object* v_f_1922_, lean_object* v_x_1923_, lean_object* v_x_1924_, lean_object* v_x1_1925_, lean_object* v_x2_1926_, lean_object* v_x3_1927_){
_start:
{
lean_object* v_fst_1928_; lean_object* v_snd_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1943_; 
v_fst_1928_ = lean_ctor_get(v_x1_1925_, 0);
v_snd_1929_ = lean_ctor_get(v_x1_1925_, 1);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_x1_1925_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1931_ = v_x1_1925_;
v_isShared_1932_ = v_isSharedCheck_1943_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_snd_1929_);
lean_inc(v_fst_1928_);
lean_dec(v_x1_1925_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1943_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1933_; uint8_t v___x_1934_; 
lean_inc(v_x3_1927_);
lean_inc(v_x2_1926_);
v___x_1933_ = lean_apply_2(v_f_1922_, v_x2_1926_, v_x3_1927_);
v___x_1934_ = lean_unbox(v___x_1933_);
if (v___x_1934_ == 0)
{
lean_object* v___x_1935_; lean_object* v___x_1937_; 
v___x_1935_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1923_, v_x_1924_, v_snd_1929_, v_x2_1926_, v_x3_1927_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 1, v___x_1935_);
v___x_1937_ = v___x_1931_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_fst_1928_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v___x_1935_);
v___x_1937_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
return v___x_1937_;
}
}
else
{
lean_object* v___x_1939_; lean_object* v___x_1941_; 
v___x_1939_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_x_1923_, v_x_1924_, v_fst_1928_, v_x2_1926_, v_x3_1927_);
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v___x_1939_);
v___x_1941_ = v___x_1931_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_snd_1929_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__1(lean_object* v___x_1944_, lean_object* v___f_1945_, lean_object* v_acc_1946_, lean_object* v_l_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_1944_, v___f_1945_, v_acc_1946_, v_l_1947_);
return v___x_1948_;
}
}
static lean_object* _init_l_Std_HashMap_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1949_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg(lean_object* v_x_1951_, lean_object* v_x_1952_, lean_object* v_f_1953_, lean_object* v_m_1954_){
_start:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v_buckets_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1955_ = lean_unsigned_to_nat(0u);
v___x_1956_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_1957_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1958_ = lean_ctor_get(v_m_1954_, 1);
lean_inc_ref(v_buckets_1958_);
lean_dec_ref(v_m_1954_);
v___x_1959_ = lean_array_get_size(v_buckets_1958_);
v___x_1960_ = lean_nat_dec_lt(v___x_1955_, v___x_1959_);
if (v___x_1960_ == 0)
{
lean_dec_ref(v_buckets_1958_);
lean_dec_ref(v_f_1953_);
lean_dec_ref(v_x_1952_);
lean_dec_ref(v_x_1951_);
return v___x_1956_;
}
else
{
lean_object* v___f_1961_; lean_object* v___f_1962_; size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; lean_object* v_fst_1966_; lean_object* v_snd_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
v___f_1961_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1961_, 0, v_f_1953_);
lean_closure_set(v___f_1961_, 1, v_x_1951_);
lean_closure_set(v___f_1961_, 2, v_x_1952_);
v___f_1962_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1962_, 0, v___x_1957_);
lean_closure_set(v___f_1962_, 1, v___f_1961_);
v___x_1963_ = ((size_t)0ULL);
v___x_1964_ = lean_usize_of_nat(v___x_1959_);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1957_, v___f_1962_, v_buckets_1958_, v___x_1963_, v___x_1964_, v___x_1956_);
v_fst_1966_ = lean_ctor_get(v___x_1965_, 0);
v_snd_1967_ = lean_ctor_get(v___x_1965_, 1);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1965_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_snd_1967_);
lean_inc(v_fst_1966_);
lean_dec(v___x_1965_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_fst_1966_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v_snd_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition(lean_object* v_00_u03b1_1975_, lean_object* v_00_u03b2_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_, lean_object* v_f_1979_, lean_object* v_m_1980_){
_start:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v_buckets_1984_; lean_object* v___x_1985_; uint8_t v___x_1986_; 
v___x_1981_ = lean_unsigned_to_nat(0u);
v___x_1982_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_1983_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_1984_ = lean_ctor_get(v_m_1980_, 1);
lean_inc_ref(v_buckets_1984_);
lean_dec_ref(v_m_1980_);
v___x_1985_ = lean_array_get_size(v_buckets_1984_);
v___x_1986_ = lean_nat_dec_lt(v___x_1981_, v___x_1985_);
if (v___x_1986_ == 0)
{
lean_dec_ref(v_buckets_1984_);
lean_dec_ref(v_f_1979_);
lean_dec_ref(v_x_1978_);
lean_dec_ref(v_x_1977_);
return v___x_1982_;
}
else
{
lean_object* v___f_1987_; lean_object* v___f_1988_; size_t v___x_1989_; size_t v___x_1990_; lean_object* v___x_1991_; lean_object* v_fst_1992_; lean_object* v_snd_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2000_; 
v___f_1987_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1987_, 0, v_f_1979_);
lean_closure_set(v___f_1987_, 1, v_x_1977_);
lean_closure_set(v___f_1987_, 2, v_x_1978_);
v___f_1988_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__1), 4, 2);
lean_closure_set(v___f_1988_, 0, v___x_1983_);
lean_closure_set(v___f_1988_, 1, v___f_1987_);
v___x_1989_ = ((size_t)0ULL);
v___x_1990_ = lean_usize_of_nat(v___x_1985_);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_1983_, v___f_1988_, v_buckets_1984_, v___x_1989_, v___x_1990_, v___x_1982_);
v_fst_1992_ = lean_ctor_get(v___x_1991_, 0);
v_snd_1993_ = lean_ctor_get(v___x_1991_, 1);
v_isSharedCheck_2000_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2000_ == 0)
{
v___x_1995_ = v___x_1991_;
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_snd_1993_);
lean_inc(v_fst_1992_);
lean_dec(v___x_1991_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2000_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v___x_1998_; 
if (v_isShared_1996_ == 0)
{
v___x_1998_ = v___x_1995_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v_fst_1992_);
lean_ctor_set(v_reuseFailAlloc_1999_, 1, v_snd_1993_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0(lean_object* v_a_2001_, lean_object* v_b_2002_, lean_object* v_d_2003_){
_start:
{
lean_object* v___x_2004_; 
v___x_2004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2004_, 0, v_b_2002_);
lean_ctor_set(v___x_2004_, 1, v_d_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0___boxed(lean_object* v_a_2005_, lean_object* v_b_2006_, lean_object* v_d_2007_){
_start:
{
lean_object* v_res_2008_; 
v_res_2008_ = l_Std_HashMap_values___redArg___lam__0(v_a_2005_, v_b_2006_, v_d_2007_);
lean_dec(v_a_2005_);
return v_res_2008_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg(lean_object* v_m_2013_){
_start:
{
lean_object* v___x_2014_; lean_object* v_buckets_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; uint8_t v___x_2019_; 
v___x_2014_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2015_ = lean_ctor_get(v_m_2013_, 1);
lean_inc_ref(v_buckets_2015_);
lean_dec_ref(v_m_2013_);
v___x_2016_ = lean_box(0);
v___x_2017_ = lean_array_get_size(v_buckets_2015_);
v___x_2018_ = lean_unsigned_to_nat(0u);
v___x_2019_ = lean_nat_dec_lt(v___x_2018_, v___x_2017_);
if (v___x_2019_ == 0)
{
lean_dec_ref(v_buckets_2015_);
return v___x_2016_;
}
else
{
lean_object* v___f_2020_; size_t v___x_2021_; size_t v___x_2022_; lean_object* v___x_2023_; 
v___f_2020_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__1));
v___x_2021_ = lean_usize_of_nat(v___x_2017_);
v___x_2022_ = ((size_t)0ULL);
v___x_2023_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2014_, v___f_2020_, v_buckets_2015_, v___x_2021_, v___x_2022_, v___x_2016_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values(lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_m_2028_){
_start:
{
lean_object* v___x_2029_; lean_object* v_buckets_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2029_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
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
v___f_2035_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__1));
v___x_2036_ = lean_usize_of_nat(v___x_2032_);
v___x_2037_ = ((size_t)0ULL);
v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2029_, v___f_2035_, v_buckets_2030_, v___x_2036_, v___x_2037_, v___x_2031_);
return v___x_2038_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___boxed(lean_object* v_00_u03b1_2039_, lean_object* v_00_u03b2_2040_, lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v_m_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Std_HashMap_values(v_00_u03b1_2039_, v_00_u03b2_2040_, v_x_2041_, v_x_2042_, v_m_2043_);
lean_dec_ref(v_x_2042_);
lean_dec_ref(v_x_2041_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0(lean_object* v_x1_2045_, lean_object* v_x2_2046_, lean_object* v_x3_2047_){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_array_push(v_x1_2045_, v_x3_2047_);
return v___x_2048_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2049_, lean_object* v_x2_2050_, lean_object* v_x3_2051_){
_start:
{
lean_object* v_res_2052_; 
v_res_2052_ = l_Std_HashMap_valuesArray___redArg___lam__0(v_x1_2049_, v_x2_2050_, v_x3_2051_);
lean_dec(v_x2_2050_);
return v_res_2052_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg(lean_object* v_m_2057_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray(lean_object* v_00_u03b1_2069_, lean_object* v_00_u03b2_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v_m_2073_){
_start:
{
lean_object* v_size_2074_; lean_object* v_buckets_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; uint8_t v___x_2080_; 
v_size_2074_ = lean_ctor_get(v_m_2073_, 0);
lean_inc(v_size_2074_);
v_buckets_2075_ = lean_ctor_get(v_m_2073_, 1);
lean_inc_ref(v_buckets_2075_);
lean_dec_ref(v_m_2073_);
v___x_2076_ = lean_mk_empty_array_with_capacity(v_size_2074_);
lean_dec(v_size_2074_);
v___x_2077_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v___x_2078_ = lean_unsigned_to_nat(0u);
v___x_2079_ = lean_array_get_size(v_buckets_2075_);
v___x_2080_ = lean_nat_dec_lt(v___x_2078_, v___x_2079_);
if (v___x_2080_ == 0)
{
lean_dec_ref(v_buckets_2075_);
return v___x_2076_;
}
else
{
lean_object* v___f_2081_; size_t v___x_2082_; size_t v___x_2083_; lean_object* v___x_2084_; 
v___f_2081_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__1));
v___x_2082_ = ((size_t)0ULL);
v___x_2083_ = lean_usize_of_nat(v___x_2079_);
v___x_2084_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2077_, v___f_2081_, v_buckets_2075_, v___x_2082_, v___x_2083_, v___x_2076_);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___boxed(lean_object* v_00_u03b1_2085_, lean_object* v_00_u03b2_2086_, lean_object* v_x_2087_, lean_object* v_x_2088_, lean_object* v_m_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_HashMap_valuesArray(v_00_u03b1_2085_, v_00_u03b2_2086_, v_x_2087_, v_x_2088_, v_m_2089_);
lean_dec_ref(v_x_2088_);
lean_dec_ref(v_x_2087_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray___redArg(lean_object* v_inst_2091_, lean_object* v_inst_2092_, lean_object* v_l_2093_){
_start:
{
lean_object* v___f_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; 
v___f_2094_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2095_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_2096_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2094_, v_inst_2091_, v_inst_2092_, v___x_2095_, v_l_2093_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray(lean_object* v_00_u03b1_2097_, lean_object* v_inst_2098_, lean_object* v_inst_2099_, lean_object* v_l_2100_){
_start:
{
lean_object* v___f_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___f_2101_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2102_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_2103_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2101_, v_inst_2098_, v_inst_2099_, v___x_2102_, v_l_2100_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg(lean_object* v_m_2104_){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2104_);
return v___x_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg___boxed(lean_object* v_m_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l_Std_HashMap_Internal_numBuckets___redArg(v_m_2106_);
lean_dec_ref(v_m_2106_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets(lean_object* v_00_u03b1_2108_, lean_object* v_00_u03b2_2109_, lean_object* v_x_2110_, lean_object* v_x_2111_, lean_object* v_m_2112_){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2112_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2114_, lean_object* v_00_u03b2_2115_, lean_object* v_x_2116_, lean_object* v_x_2117_, lean_object* v_m_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Std_HashMap_Internal_numBuckets(v_00_u03b1_2114_, v_00_u03b2_2115_, v_x_2116_, v_x_2117_, v_m_2118_);
lean_dec_ref(v_m_2118_);
lean_dec_ref(v_x_2117_);
lean_dec_ref(v_x_2116_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2(lean_object* v___x_2123_, lean_object* v___f_2124_, lean_object* v_m_2125_, lean_object* v_prec_2126_){
_start:
{
lean_object* v___x_2127_; lean_object* v_buckets_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2148_; 
v___x_2127_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_buckets_2128_ = lean_ctor_get(v_m_2125_, 1);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_m_2125_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; 
v_unused_2149_ = lean_ctor_get(v_m_2125_, 0);
lean_dec(v_unused_2149_);
v___x_2130_ = v_m_2125_;
v_isShared_2131_ = v_isSharedCheck_2148_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_buckets_2128_);
lean_dec(v_m_2125_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2148_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2132_; lean_object* v___y_2134_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
v___x_2132_ = ((lean_object*)(l_Std_HashMap_instRepr___redArg___lam__2___closed__1));
v___x_2140_ = lean_box(0);
v___x_2141_ = lean_array_get_size(v_buckets_2128_);
v___x_2142_ = lean_unsigned_to_nat(0u);
v___x_2143_ = lean_nat_dec_lt(v___x_2142_, v___x_2141_);
if (v___x_2143_ == 0)
{
lean_dec_ref(v_buckets_2128_);
lean_dec_ref(v___f_2124_);
v___y_2134_ = v___x_2140_;
goto v___jp_2133_;
}
else
{
lean_object* v___f_2144_; size_t v___x_2145_; size_t v___x_2146_; lean_object* v___x_2147_; 
v___f_2144_ = lean_alloc_closure((void*)(l_Std_HashMap_toList___redArg___lam__1), 4, 2);
lean_closure_set(v___f_2144_, 0, v___x_2127_);
lean_closure_set(v___f_2144_, 1, v___f_2124_);
v___x_2145_ = lean_usize_of_nat(v___x_2141_);
v___x_2146_ = ((size_t)0ULL);
v___x_2147_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), v___x_2127_, v___f_2144_, v_buckets_2128_, v___x_2145_, v___x_2146_, v___x_2140_);
v___y_2134_ = v___x_2147_;
goto v___jp_2133_;
}
v___jp_2133_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = l_List_repr___redArg(v___x_2123_, v___y_2134_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set_tag(v___x_2130_, 5);
lean_ctor_set(v___x_2130_, 1, v___x_2135_);
lean_ctor_set(v___x_2130_, 0, v___x_2132_);
v___x_2137_ = v___x_2130_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2132_);
lean_ctor_set(v_reuseFailAlloc_2139_, 1, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Repr_addAppParen(v___x_2137_, v_prec_2126_);
return v___x_2138_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__2___boxed(lean_object* v___x_2150_, lean_object* v___f_2151_, lean_object* v_m_2152_, lean_object* v_prec_2153_){
_start:
{
lean_object* v_res_2154_; 
v_res_2154_ = l_Std_HashMap_instRepr___redArg___lam__2(v___x_2150_, v___f_2151_, v_m_2152_, v_prec_2153_);
lean_dec(v_prec_2153_);
return v_res_2154_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg(lean_object* v_inst_2155_, lean_object* v_inst_2156_){
_start:
{
lean_object* v___f_2157_; lean_object* v___f_2158_; lean_object* v___x_2159_; lean_object* v___f_2160_; 
v___f_2157_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__0));
v___f_2158_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2158_, 0, v_inst_2156_);
v___x_2159_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2159_, 0, lean_box(0));
lean_closure_set(v___x_2159_, 1, lean_box(0));
lean_closure_set(v___x_2159_, 2, v_inst_2155_);
lean_closure_set(v___x_2159_, 3, v___f_2158_);
v___f_2160_ = lean_alloc_closure((void*)(l_Std_HashMap_instRepr___redArg___lam__2___boxed), 4, 2);
lean_closure_set(v___f_2160_, 0, v___x_2159_);
lean_closure_set(v___f_2160_, 1, v___f_2157_);
return v___f_2160_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr(lean_object* v_00_u03b1_2161_, lean_object* v_00_u03b2_2162_, lean_object* v_inst_2163_, lean_object* v_inst_2164_, lean_object* v_inst_2165_, lean_object* v_inst_2166_){
_start:
{
lean_object* v___x_2167_; 
v___x_2167_ = l_Std_HashMap_instRepr___redArg(v_inst_2165_, v_inst_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___boxed(lean_object* v_00_u03b1_2168_, lean_object* v_00_u03b2_2169_, lean_object* v_inst_2170_, lean_object* v_inst_2171_, lean_object* v_inst_2172_, lean_object* v_inst_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Std_HashMap_instRepr(v_00_u03b1_2168_, v_00_u03b2_2169_, v_inst_2170_, v_inst_2171_, v_inst_2172_, v_inst_2173_);
lean_dec_ref(v_inst_2171_);
lean_dec_ref(v_inst_2170_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__0(lean_object* v_a_2177_, lean_object* v_x_2178_){
_start:
{
lean_object* v___y_2180_; 
if (lean_obj_tag(v_x_2178_) == 0)
{
lean_object* v___x_2183_; 
v___x_2183_ = ((lean_object*)(l_Array_groupByKey___redArg___lam__0___closed__0));
v___y_2180_ = v___x_2183_;
goto v___jp_2179_;
}
else
{
lean_object* v_val_2184_; 
v_val_2184_ = lean_ctor_get(v_x_2178_, 0);
lean_inc(v_val_2184_);
lean_dec_ref_known(v_x_2178_, 1);
v___y_2180_ = v_val_2184_;
goto v___jp_2179_;
}
v___jp_2179_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_array_push(v___y_2180_, v_a_2177_);
v___x_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__1(lean_object* v_key_2185_, lean_object* v_inst_2186_, lean_object* v_inst_2187_, lean_object* v_a_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v___f_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
lean_inc(v_a_2188_);
v___f_2191_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2191_, 0, v_a_2188_);
v___x_2192_ = lean_apply_1(v_key_2185_, v_a_2188_);
v___x_2193_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_2186_, v_inst_2187_, v___y_2190_, v___x_2192_, v___f_2191_);
v___x_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2193_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg(lean_object* v_inst_2195_, lean_object* v_inst_2196_, lean_object* v_key_2197_, lean_object* v_xs_2198_){
_start:
{
lean_object* v___f_2199_; lean_object* v___x_2200_; lean_object* v_groups_2201_; size_t v_sz_2202_; size_t v___x_2203_; lean_object* v___x_2204_; 
v___f_2199_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__1), 6, 3);
lean_closure_set(v___f_2199_, 0, v_key_2197_);
lean_closure_set(v___f_2199_, 1, v_inst_2195_);
lean_closure_set(v___f_2199_, 2, v_inst_2196_);
v___x_2200_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__9));
v_groups_2201_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v_sz_2202_ = lean_array_size(v_xs_2198_);
v___x_2203_ = ((size_t)0ULL);
v___x_2204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2200_, v_xs_2198_, v___f_2199_, v_sz_2202_, v___x_2203_, v_groups_2201_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey(lean_object* v_00_u03b1_2205_, lean_object* v_00_u03b2_2206_, lean_object* v_inst_2207_, lean_object* v_inst_2208_, lean_object* v_key_2209_, lean_object* v_xs_2210_){
_start:
{
lean_object* v___x_2211_; 
v___x_2211_ = l_Array_groupByKey___redArg(v_inst_2207_, v_inst_2208_, v_key_2209_, v_xs_2210_);
return v___x_2211_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__0(lean_object* v_x_2212_, lean_object* v_v_2213_){
_start:
{
lean_object* v___y_2215_; 
if (lean_obj_tag(v_v_2213_) == 0)
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_box(0);
v___y_2215_ = v___x_2218_;
goto v___jp_2214_;
}
else
{
lean_object* v_val_2219_; 
v_val_2219_ = lean_ctor_get(v_v_2213_, 0);
lean_inc(v_val_2219_);
lean_dec_ref_known(v_v_2213_, 1);
v___y_2215_ = v_val_2219_;
goto v___jp_2214_;
}
v___jp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2216_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2216_, 0, v_x_2212_);
lean_ctor_set(v___x_2216_, 1, v___y_2215_);
v___x_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
return v___x_2217_;
}
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__1(lean_object* v_key_2220_, lean_object* v_inst_2221_, lean_object* v_inst_2222_, lean_object* v_x_2223_, lean_object* v_acc_2224_){
_start:
{
lean_object* v___f_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_inc(v_x_2223_);
v___f_2225_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__0), 2, 1);
lean_closure_set(v___f_2225_, 0, v_x_2223_);
v___x_2226_ = lean_apply_1(v_key_2220_, v_x_2223_);
v___x_2227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_alter___redArg(v_inst_2221_, v_inst_2222_, v_acc_2224_, v___x_2226_, v___f_2225_);
return v___x_2227_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg(lean_object* v_inst_2228_, lean_object* v_inst_2229_, lean_object* v_key_2230_, lean_object* v_xs_2231_){
_start:
{
lean_object* v___f_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___f_2232_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__1), 5, 3);
lean_closure_set(v___f_2232_, 0, v_key_2230_);
lean_closure_set(v___f_2232_, 1, v_inst_2228_);
lean_closure_set(v___f_2232_, 2, v_inst_2229_);
v___x_2233_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___redArg___closed__1, &l_Std_HashMap_instEmptyCollection___redArg___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___redArg___closed__1);
v___x_2234_ = l_List_foldrTR___redArg(v___f_2232_, v___x_2233_, v_xs_2231_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey(lean_object* v_00_u03b1_2235_, lean_object* v_00_u03b2_2236_, lean_object* v_inst_2237_, lean_object* v_inst_2238_, lean_object* v_key_2239_, lean_object* v_xs_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_List_groupByKey___redArg(v_inst_2237_, v_inst_2238_, v_key_2239_, v_xs_2240_);
return v___x_2241_;
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
