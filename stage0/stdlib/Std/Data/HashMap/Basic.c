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
lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_HashMap_instEmptyCollection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_instEmptyCollection___closed__2;
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
static lean_once_cell_t l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__1;
static lean_once_cell_t l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__2;
static lean_once_cell_t l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__3;
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
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__1_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__2 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__2_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__3 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__3_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__4 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__4_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__5 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__5_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__6 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__6_value;
static const lean_closure_object l_Std_HashMap_keys___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keys___redArg___closed__7 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__7_value;
static const lean_ctor_object l_Std_HashMap_keys___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__1_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__2_value)}};
static const lean_object* l_Std_HashMap_keys___redArg___closed__8 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__8_value;
static const lean_ctor_object l_Std_HashMap_keys___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__8_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__3_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__4_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__5_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__6_value)}};
static const lean_object* l_Std_HashMap_keys___redArg___closed__9 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value;
static const lean_ctor_object l_Std_HashMap_keys___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_keys___redArg___closed__7_value)}};
static const lean_object* l_Std_HashMap_keys___redArg___closed__10 = (const lean_object*)&l_Std_HashMap_keys___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keys(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keys___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__10_value)} };
static const lean_object* l_Std_HashMap_ofList___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_ofList___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashMap_unitOfList___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_unitOfList___redArg___closed__0;
static lean_once_cell_t l_Std_HashMap_unitOfList___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_unitOfList___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__10_value)} };
static const lean_object* l_Std_HashMap_ofArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_ofArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_ofArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_ofArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_ofArray___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_ofArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_toList___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_filter___redArg___boxed(lean_object*, lean_object*);
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
static const lean_closure_object l_Std_HashMap_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_toArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_keysArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_HashMap_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_keys___redArg___closed__10_value)} };
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
static lean_once_cell_t l_Std_HashMap_partition___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_partition___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_values___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_values(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_values___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_valuesArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashMap_instRepr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashMap.ofList "};
static const lean_object* l_Std_HashMap_instRepr___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_HashMap_instRepr___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_HashMap_instRepr___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_HashMap_instRepr___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_HashMap_instRepr___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_HashMap_instRepr___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_groupByKey___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_groupByKey___redArg___lam__0___closed__0 = (const lean_object*)&l_Array_groupByKey___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Array_groupByKey___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___redArg___closed__0;
static lean_once_cell_t l_Array_groupByKey___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_groupByKey___redArg___closed__1;
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_groupByKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_groupByKey___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_groupByKey___redArg___closed__0;
static lean_once_cell_t l_List_groupByKey___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_groupByKey___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_groupByKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_groupByKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v_cellCount_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_2_ = lean_unsigned_to_nat(4u);
v___x_3_ = lean_nat_mul(v_capacity_1_, v___x_2_);
v___x_4_ = lean_unsigned_to_nat(2u);
v___x_5_ = lean_nat_add(v___x_3_, v___x_4_);
lean_dec(v___x_3_);
v___x_6_ = lean_unsigned_to_nat(3u);
v___x_7_ = lean_nat_div(v___x_5_, v___x_6_);
lean_dec(v___x_5_);
v_cellCount_8_ = l_Nat_nextPowerOfTwo(v___x_7_);
lean_dec(v___x_7_);
v___x_9_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_8_);
v___x_10_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_8_);
v___x_11_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_8_);
v___x_12_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_12_, 0, v___x_9_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_HashMap_emptyWithCapacity___redArg(v_capacity_13_);
lean_dec(v_capacity_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity(lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_inst_17_, lean_object* v_inst_18_, lean_object* v_capacity_19_){
_start:
{
lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v_cellCount_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_20_ = lean_unsigned_to_nat(4u);
v___x_21_ = lean_nat_mul(v_capacity_19_, v___x_20_);
v___x_22_ = lean_unsigned_to_nat(2u);
v___x_23_ = lean_nat_add(v___x_21_, v___x_22_);
lean_dec(v___x_21_);
v___x_24_ = lean_unsigned_to_nat(3u);
v___x_25_ = lean_nat_div(v___x_23_, v___x_24_);
lean_dec(v___x_23_);
v_cellCount_26_ = l_Nat_nextPowerOfTwo(v___x_25_);
lean_dec(v___x_25_);
v___x_27_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_26_);
v___x_28_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_26_);
v___x_29_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_26_);
v___x_30_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_30_, 0, v___x_27_);
lean_ctor_set(v___x_30_, 1, v___x_28_);
lean_ctor_set(v___x_30_, 2, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_emptyWithCapacity___boxed(lean_object* v_00_u03b1_31_, lean_object* v_00_u03b2_32_, lean_object* v_inst_33_, lean_object* v_inst_34_, lean_object* v_capacity_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Std_HashMap_emptyWithCapacity(v_00_u03b1_31_, v_00_u03b2_32_, v_inst_33_, v_inst_34_, v_capacity_35_);
lean_dec(v_capacity_35_);
lean_dec_ref(v_inst_34_);
lean_dec_ref(v_inst_33_);
return v_res_36_;
}
}
static lean_object* _init_l_Std_HashMap_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v_cellCount_37_; lean_object* v___x_38_; 
v_cellCount_37_ = lean_unsigned_to_nat(16u);
v___x_38_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_HashMap_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v_cellCount_39_; lean_object* v___x_40_; 
v_cellCount_39_ = lean_unsigned_to_nat(16u);
v___x_40_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_39_);
return v___x_40_;
}
}
static lean_object* _init_l_Std_HashMap_instEmptyCollection___closed__2(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_41_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__1, &l_Std_HashMap_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_instEmptyCollection___closed__1);
v___x_42_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__0, &l_Std_HashMap_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_instEmptyCollection___closed__0);
v___x_43_ = lean_unsigned_to_nat(0u);
v___x_44_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_44_, 0, v___x_43_);
lean_ctor_set(v___x_44_, 1, v___x_42_);
lean_ctor_set(v___x_44_, 2, v___x_41_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instEmptyCollection(lean_object* v_00_u03b1_45_, lean_object* v_00_u03b2_46_, lean_object* v_inst_47_, lean_object* v_inst_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__2, &l_Std_HashMap_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_instEmptyCollection___closed__2);
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
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited(lean_object* v_00_u03b1_55_, lean_object* v_00_u03b2_56_, lean_object* v_inst_57_, lean_object* v_inst_58_){
_start:
{
lean_object* v___x_59_; 
v___x_59_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__2, &l_Std_HashMap_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_instEmptyCollection___closed__2);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInhabited___boxed(lean_object* v_00_u03b1_60_, lean_object* v_00_u03b2_61_, lean_object* v_inst_62_, lean_object* v_inst_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Std_HashMap_instInhabited(v_00_u03b1_60_, v_00_u03b2_61_, v_inst_62_, v_inst_63_);
lean_dec_ref(v_inst_63_);
lean_dec_ref(v_inst_62_);
return v_res_64_;
}
}
static lean_object* _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_103_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__5));
v___x_104_ = l_String_toRawSubstring_x27(v___x_103_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(lean_object* v_x_125_, lean_object* v_a_126_, lean_object* v_a_127_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
lean_inc(v_x_125_);
v___x_129_ = l_Lean_Syntax_isOfKind(v_x_125_, v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; lean_object* v___x_131_; 
lean_dec(v_x_125_);
v___x_130_ = lean_box(1);
v___x_131_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_127_);
return v___x_131_;
}
else
{
lean_object* v_quotContext_132_; lean_object* v_currMacroScope_133_; lean_object* v_ref_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v_quotContext_132_ = lean_ctor_get(v_a_126_, 1);
v_currMacroScope_133_ = lean_ctor_get(v_a_126_, 2);
v_ref_134_ = lean_ctor_get(v_a_126_, 5);
v___x_135_ = lean_unsigned_to_nat(0u);
v___x_136_ = l_Lean_Syntax_getArg(v_x_125_, v___x_135_);
v___x_137_ = lean_unsigned_to_nat(2u);
v___x_138_ = l_Lean_Syntax_getArg(v_x_125_, v___x_137_);
lean_dec(v_x_125_);
v___x_139_ = 0;
v___x_140_ = l_Lean_SourceInfo_fromRef(v_ref_134_, v___x_139_);
v___x_141_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
v___x_142_ = lean_obj_once(&l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6, &l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6_once, _init_l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__6);
v___x_143_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_133_);
lean_inc(v_quotContext_132_);
v___x_144_ = l_Lean_addMacroScope(v_quotContext_132_, v___x_143_, v_currMacroScope_133_);
v___x_145_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__12));
lean_inc_n(v___x_140_, 2);
v___x_146_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_146_, 0, v___x_140_);
lean_ctor_set(v___x_146_, 1, v___x_142_);
lean_ctor_set(v___x_146_, 2, v___x_144_);
lean_ctor_set(v___x_146_, 3, v___x_145_);
v___x_147_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__14));
v___x_148_ = l_Lean_Syntax_node2(v___x_140_, v___x_147_, v___x_136_, v___x_138_);
v___x_149_ = l_Lean_Syntax_node2(v___x_140_, v___x_141_, v___x_146_, v___x_148_);
v___x_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set(v___x_150_, 1, v_a_127_);
return v___x_150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___boxed(lean_object* v_x_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1(v_x_151_, v_a_152_, v_a_153_);
lean_dec_ref(v_a_152_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(lean_object* v_x_158_, lean_object* v_a_159_, lean_object* v_a_160_){
_start:
{
lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_161_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______macroRules__Std__HashMap__term___x7em____1___closed__4));
lean_inc(v_x_158_);
v___x_162_ = l_Lean_Syntax_isOfKind(v_x_158_, v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec(v_x_158_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_a_160_);
return v___x_164_;
}
else
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v___x_165_ = lean_unsigned_to_nat(0u);
v___x_166_ = l_Lean_Syntax_getArg(v_x_158_, v___x_165_);
v___x_167_ = ((lean_object*)(l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___closed__1));
lean_inc(v___x_166_);
v___x_168_ = l_Lean_Syntax_isOfKind(v___x_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_object* v___x_169_; lean_object* v___x_170_; 
lean_dec(v___x_166_);
lean_dec(v_x_158_);
v___x_169_ = lean_box(0);
v___x_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_a_160_);
return v___x_170_;
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; uint8_t v___x_174_; 
v___x_171_ = lean_unsigned_to_nat(1u);
v___x_172_ = l_Lean_Syntax_getArg(v_x_158_, v___x_171_);
lean_dec(v_x_158_);
v___x_173_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_172_);
v___x_174_ = l_Lean_Syntax_matchesNull(v___x_172_, v___x_173_);
if (v___x_174_ == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v___x_172_);
lean_dec(v___x_166_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_a_160_);
return v___x_176_;
}
else
{
lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v_ref_179_; uint8_t v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_177_ = l_Lean_Syntax_getArg(v___x_172_, v___x_165_);
v___x_178_ = l_Lean_Syntax_getArg(v___x_172_, v___x_171_);
lean_dec(v___x_172_);
v_ref_179_ = l_Lean_replaceRef(v___x_166_, v_a_159_);
lean_dec(v___x_166_);
v___x_180_ = 0;
v___x_181_ = l_Lean_SourceInfo_fromRef(v_ref_179_, v___x_180_);
lean_dec(v_ref_179_);
v___x_182_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__3));
v___x_183_ = ((lean_object*)(l_Std_HashMap_term___x7em___00__closed__6));
lean_inc(v___x_181_);
v___x_184_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_181_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = l_Lean_Syntax_node3(v___x_181_, v___x_182_, v___x_177_, v___x_184_, v___x_178_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_a_160_);
return v___x_186_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1___boxed(lean_object* v_x_187_, lean_object* v_a_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_Std_HashMap___aux__Std__Data__HashMap__Basic______unexpand__Std__HashMap__Equiv__1(v_x_187_, v_a_188_, v_a_189_);
lean_dec(v_a_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert___redArg(lean_object* v_x_191_, lean_object* v_x_192_, lean_object* v_m_193_, lean_object* v_a_194_, lean_object* v_b_195_){
_start:
{
lean_object* v___y_197_; lean_object* v_i_198_; lean_object* v___y_214_; lean_object* v_i_215_; lean_object* v___y_221_; lean_object* v___x_230_; 
lean_inc(v_a_194_);
lean_inc_ref(v_x_192_);
lean_inc_ref(v_x_191_);
v___x_230_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_191_, v_x_192_, v_m_193_, v_a_194_);
switch(lean_obj_tag(v___x_230_))
{
case 0:
{
lean_object* v_index_231_; lean_object* v_size_232_; lean_object* v___x_233_; 
lean_dec_ref(v_x_192_);
lean_dec_ref(v_x_191_);
v_index_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_index_231_);
lean_dec_ref_known(v___x_230_, 3);
v_size_232_ = lean_ctor_get(v_m_193_, 0);
lean_inc(v_size_232_);
v___x_233_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_193_, v_size_232_, v_index_231_, v_a_194_, v_b_195_);
lean_dec(v_index_231_);
return v___x_233_;
}
case 1:
{
lean_object* v_index_234_; lean_object* v_size_235_; lean_object* v_keyArray_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v_index_234_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_index_234_);
lean_dec_ref_known(v___x_230_, 1);
v_size_235_ = lean_ctor_get(v_m_193_, 0);
v_keyArray_236_ = lean_ctor_get(v_m_193_, 1);
v___x_237_ = lean_unsigned_to_nat(1u);
v___x_238_ = lean_nat_add(v_size_235_, v___x_237_);
v___x_239_ = lean_array_get_size(v_keyArray_236_);
v___x_240_ = lean_nat_dec_lt(v___x_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_dec(v___x_238_);
lean_dec(v_index_234_);
goto v___jp_203_;
}
else
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_241_ = lean_unsigned_to_nat(4u);
v___x_242_ = lean_nat_mul(v___x_238_, v___x_241_);
v___x_243_ = lean_unsigned_to_nat(3u);
v___x_244_ = lean_nat_mul(v___x_239_, v___x_243_);
v___x_245_ = lean_nat_dec_le(v___x_242_, v___x_244_);
lean_dec(v___x_244_);
lean_dec(v___x_242_);
if (v___x_245_ == 0)
{
lean_dec(v___x_238_);
lean_dec(v_index_234_);
goto v___jp_203_;
}
else
{
lean_object* v___x_246_; 
lean_dec_ref(v_x_192_);
lean_dec_ref(v_x_191_);
v___x_246_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_193_, v___x_238_, v_index_234_, v_a_194_, v_b_195_);
lean_dec(v_index_234_);
return v___x_246_;
}
}
}
default: 
{
lean_object* v_size_247_; lean_object* v_keyArray_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; uint8_t v___x_252_; 
v_size_247_ = lean_ctor_get(v_m_193_, 0);
v_keyArray_248_ = lean_ctor_get(v_m_193_, 1);
v___x_249_ = lean_unsigned_to_nat(1u);
v___x_250_ = lean_nat_add(v_size_247_, v___x_249_);
v___x_251_ = lean_array_get_size(v_keyArray_248_);
v___x_252_ = lean_nat_dec_lt(v___x_250_, v___x_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v___x_250_);
lean_inc_ref(v_x_192_);
lean_inc_ref(v_x_191_);
v___x_253_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_191_, v_x_192_, v_m_193_);
v___y_221_ = v___x_253_;
goto v___jp_220_;
}
else
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_254_ = lean_unsigned_to_nat(4u);
v___x_255_ = lean_nat_mul(v___x_250_, v___x_254_);
lean_dec(v___x_250_);
v___x_256_ = lean_unsigned_to_nat(3u);
v___x_257_ = lean_nat_mul(v___x_251_, v___x_256_);
v___x_258_ = lean_nat_dec_le(v___x_255_, v___x_257_);
lean_dec(v___x_257_);
lean_dec(v___x_255_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_inc_ref(v_x_192_);
lean_inc_ref(v_x_191_);
v___x_259_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_191_, v_x_192_, v_m_193_);
v___y_221_ = v___x_259_;
goto v___jp_220_;
}
else
{
v___y_221_ = v_m_193_;
goto v___jp_220_;
}
}
}
}
v___jp_196_:
{
lean_object* v_size_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_size_199_ = lean_ctor_get(v___y_197_, 0);
v___x_200_ = lean_unsigned_to_nat(1u);
v___x_201_ = lean_nat_add(v_size_199_, v___x_200_);
v___x_202_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_197_, v___x_201_, v_i_198_, v_a_194_, v_b_195_);
lean_dec(v_i_198_);
return v___x_202_;
}
v___jp_203_:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_inc_ref(v_x_192_);
lean_inc_ref(v_x_191_);
v___x_204_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_191_, v_x_192_, v_m_193_);
lean_inc(v_a_194_);
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_191_, v_x_192_, v___x_204_, v_a_194_);
switch(lean_obj_tag(v___x_205_))
{
case 0:
{
lean_object* v_index_206_; lean_object* v_size_207_; lean_object* v___x_208_; 
v_index_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_index_206_);
lean_dec_ref_known(v___x_205_, 3);
v_size_207_ = lean_ctor_get(v___x_204_, 0);
lean_inc(v_size_207_);
v___x_208_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_204_, v_size_207_, v_index_206_, v_a_194_, v_b_195_);
lean_dec(v_index_206_);
return v___x_208_;
}
case 1:
{
lean_object* v_index_209_; 
v_index_209_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_index_209_);
lean_dec_ref_known(v___x_205_, 1);
v___y_197_ = v___x_204_;
v_i_198_ = v_index_209_;
goto v___jp_196_;
}
default: 
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_204_, v___x_210_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_index_212_; 
v_index_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_index_212_);
lean_dec_ref_known(v___x_211_, 1);
v___y_197_ = v___x_204_;
v_i_198_ = v_index_212_;
goto v___jp_196_;
}
else
{
lean_dec(v_b_195_);
lean_dec(v_a_194_);
return v___x_204_;
}
}
}
}
v___jp_213_:
{
lean_object* v_size_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_size_216_ = lean_ctor_get(v___y_214_, 0);
v___x_217_ = lean_unsigned_to_nat(1u);
v___x_218_ = lean_nat_add(v_size_216_, v___x_217_);
v___x_219_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_214_, v___x_218_, v_i_215_, v_a_194_, v_b_195_);
lean_dec(v_i_215_);
return v___x_219_;
}
v___jp_220_:
{
lean_object* v___x_222_; 
lean_inc(v_a_194_);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_191_, v_x_192_, v___y_221_, v_a_194_);
switch(lean_obj_tag(v___x_222_))
{
case 0:
{
lean_object* v_index_223_; lean_object* v_size_224_; lean_object* v___x_225_; 
v_index_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_index_223_);
lean_dec_ref_known(v___x_222_, 3);
v_size_224_ = lean_ctor_get(v___y_221_, 0);
lean_inc(v_size_224_);
v___x_225_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_221_, v_size_224_, v_index_223_, v_a_194_, v_b_195_);
lean_dec(v_index_223_);
return v___x_225_;
}
case 1:
{
lean_object* v_index_226_; 
v_index_226_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_index_226_);
lean_dec_ref_known(v___x_222_, 1);
v___y_214_ = v___y_221_;
v_i_215_ = v_index_226_;
goto v___jp_213_;
}
default: 
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_unsigned_to_nat(0u);
v___x_228_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_221_, v___x_227_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_index_229_; 
v_index_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_index_229_);
lean_dec_ref_known(v___x_228_, 1);
v___y_214_ = v___y_221_;
v_i_215_ = v_index_229_;
goto v___jp_213_;
}
else
{
lean_dec(v_b_195_);
lean_dec(v_a_194_);
return v___y_221_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insert(lean_object* v_00_u03b1_260_, lean_object* v_00_u03b2_261_, lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_m_264_, lean_object* v_a_265_, lean_object* v_b_266_){
_start:
{
lean_object* v___y_268_; lean_object* v_i_269_; lean_object* v___y_285_; lean_object* v_i_286_; lean_object* v___y_292_; lean_object* v___x_301_; 
lean_inc(v_a_265_);
lean_inc_ref(v_x_263_);
lean_inc_ref(v_x_262_);
v___x_301_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_262_, v_x_263_, v_m_264_, v_a_265_);
switch(lean_obj_tag(v___x_301_))
{
case 0:
{
lean_object* v_index_302_; lean_object* v_size_303_; lean_object* v___x_304_; 
lean_dec_ref(v_x_263_);
lean_dec_ref(v_x_262_);
v_index_302_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_index_302_);
lean_dec_ref_known(v___x_301_, 3);
v_size_303_ = lean_ctor_get(v_m_264_, 0);
lean_inc(v_size_303_);
v___x_304_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_264_, v_size_303_, v_index_302_, v_a_265_, v_b_266_);
lean_dec(v_index_302_);
return v___x_304_;
}
case 1:
{
lean_object* v_index_305_; lean_object* v_size_306_; lean_object* v_keyArray_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_index_305_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_index_305_);
lean_dec_ref_known(v___x_301_, 1);
v_size_306_ = lean_ctor_get(v_m_264_, 0);
v_keyArray_307_ = lean_ctor_get(v_m_264_, 1);
v___x_308_ = lean_unsigned_to_nat(1u);
v___x_309_ = lean_nat_add(v_size_306_, v___x_308_);
v___x_310_ = lean_array_get_size(v_keyArray_307_);
v___x_311_ = lean_nat_dec_lt(v___x_309_, v___x_310_);
if (v___x_311_ == 0)
{
lean_dec(v___x_309_);
lean_dec(v_index_305_);
goto v___jp_274_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_312_ = lean_unsigned_to_nat(4u);
v___x_313_ = lean_nat_mul(v___x_309_, v___x_312_);
v___x_314_ = lean_unsigned_to_nat(3u);
v___x_315_ = lean_nat_mul(v___x_310_, v___x_314_);
v___x_316_ = lean_nat_dec_le(v___x_313_, v___x_315_);
lean_dec(v___x_315_);
lean_dec(v___x_313_);
if (v___x_316_ == 0)
{
lean_dec(v___x_309_);
lean_dec(v_index_305_);
goto v___jp_274_;
}
else
{
lean_object* v___x_317_; 
lean_dec_ref(v_x_263_);
lean_dec_ref(v_x_262_);
v___x_317_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_264_, v___x_309_, v_index_305_, v_a_265_, v_b_266_);
lean_dec(v_index_305_);
return v___x_317_;
}
}
}
default: 
{
lean_object* v_size_318_; lean_object* v_keyArray_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v_size_318_ = lean_ctor_get(v_m_264_, 0);
v_keyArray_319_ = lean_ctor_get(v_m_264_, 1);
v___x_320_ = lean_unsigned_to_nat(1u);
v___x_321_ = lean_nat_add(v_size_318_, v___x_320_);
v___x_322_ = lean_array_get_size(v_keyArray_319_);
v___x_323_ = lean_nat_dec_lt(v___x_321_, v___x_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_324_; 
lean_dec(v___x_321_);
lean_inc_ref(v_x_263_);
lean_inc_ref(v_x_262_);
v___x_324_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_262_, v_x_263_, v_m_264_);
v___y_292_ = v___x_324_;
goto v___jp_291_;
}
else
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_325_ = lean_unsigned_to_nat(4u);
v___x_326_ = lean_nat_mul(v___x_321_, v___x_325_);
lean_dec(v___x_321_);
v___x_327_ = lean_unsigned_to_nat(3u);
v___x_328_ = lean_nat_mul(v___x_322_, v___x_327_);
v___x_329_ = lean_nat_dec_le(v___x_326_, v___x_328_);
lean_dec(v___x_328_);
lean_dec(v___x_326_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; 
lean_inc_ref(v_x_263_);
lean_inc_ref(v_x_262_);
v___x_330_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_262_, v_x_263_, v_m_264_);
v___y_292_ = v___x_330_;
goto v___jp_291_;
}
else
{
v___y_292_ = v_m_264_;
goto v___jp_291_;
}
}
}
}
v___jp_267_:
{
lean_object* v_size_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_size_270_ = lean_ctor_get(v___y_268_, 0);
v___x_271_ = lean_unsigned_to_nat(1u);
v___x_272_ = lean_nat_add(v_size_270_, v___x_271_);
v___x_273_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_268_, v___x_272_, v_i_269_, v_a_265_, v_b_266_);
lean_dec(v_i_269_);
return v___x_273_;
}
v___jp_274_:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_inc_ref(v_x_263_);
lean_inc_ref(v_x_262_);
v___x_275_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_262_, v_x_263_, v_m_264_);
lean_inc(v_a_265_);
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_262_, v_x_263_, v___x_275_, v_a_265_);
switch(lean_obj_tag(v___x_276_))
{
case 0:
{
lean_object* v_index_277_; lean_object* v_size_278_; lean_object* v___x_279_; 
v_index_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_index_277_);
lean_dec_ref_known(v___x_276_, 3);
v_size_278_ = lean_ctor_get(v___x_275_, 0);
lean_inc(v_size_278_);
v___x_279_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_275_, v_size_278_, v_index_277_, v_a_265_, v_b_266_);
lean_dec(v_index_277_);
return v___x_279_;
}
case 1:
{
lean_object* v_index_280_; 
v_index_280_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_index_280_);
lean_dec_ref_known(v___x_276_, 1);
v___y_268_ = v___x_275_;
v_i_269_ = v_index_280_;
goto v___jp_267_;
}
default: 
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_275_, v___x_281_);
if (lean_obj_tag(v___x_282_) == 0)
{
lean_object* v_index_283_; 
v_index_283_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_index_283_);
lean_dec_ref_known(v___x_282_, 1);
v___y_268_ = v___x_275_;
v_i_269_ = v_index_283_;
goto v___jp_267_;
}
else
{
lean_dec(v_b_266_);
lean_dec(v_a_265_);
return v___x_275_;
}
}
}
}
v___jp_284_:
{
lean_object* v_size_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_size_287_ = lean_ctor_get(v___y_285_, 0);
v___x_288_ = lean_unsigned_to_nat(1u);
v___x_289_ = lean_nat_add(v_size_287_, v___x_288_);
v___x_290_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_285_, v___x_289_, v_i_286_, v_a_265_, v_b_266_);
lean_dec(v_i_286_);
return v___x_290_;
}
v___jp_291_:
{
lean_object* v___x_293_; 
lean_inc(v_a_265_);
v___x_293_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_262_, v_x_263_, v___y_292_, v_a_265_);
switch(lean_obj_tag(v___x_293_))
{
case 0:
{
lean_object* v_index_294_; lean_object* v_size_295_; lean_object* v___x_296_; 
v_index_294_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_index_294_);
lean_dec_ref_known(v___x_293_, 3);
v_size_295_ = lean_ctor_get(v___y_292_, 0);
lean_inc(v_size_295_);
v___x_296_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_292_, v_size_295_, v_index_294_, v_a_265_, v_b_266_);
lean_dec(v_index_294_);
return v___x_296_;
}
case 1:
{
lean_object* v_index_297_; 
v_index_297_ = lean_ctor_get(v___x_293_, 0);
lean_inc(v_index_297_);
lean_dec_ref_known(v___x_293_, 1);
v___y_285_ = v___y_292_;
v_i_286_ = v_index_297_;
goto v___jp_284_;
}
default: 
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_292_, v___x_298_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_index_300_; 
v_index_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_index_300_);
lean_dec_ref_known(v___x_299_, 1);
v___y_285_ = v___y_292_;
v_i_286_ = v_index_300_;
goto v___jp_284_;
}
else
{
lean_dec(v_b_266_);
lean_dec(v_a_265_);
return v___y_292_;
}
}
}
}
}
}
static lean_object* _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__0, &l_Std_HashMap_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_instEmptyCollection___closed__0);
v___x_332_ = lean_array_get_size(v___x_331_);
return v___x_332_;
}
}
static uint8_t _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_333_; lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_333_ = lean_obj_once(&l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__0, &l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__0_once, _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__0);
v___x_334_ = lean_unsigned_to_nat(1u);
v___x_335_ = lean_nat_dec_lt(v___x_334_, v___x_333_);
return v___x_335_;
}
}
static lean_object* _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_336_ = lean_unsigned_to_nat(3u);
v___x_337_ = lean_obj_once(&l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__0, &l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__0_once, _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__0);
v___x_338_ = lean_nat_mul(v___x_337_, v___x_336_);
return v___x_338_;
}
}
static uint8_t _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; 
v___x_339_ = lean_obj_once(&l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__2, &l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__2_once, _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__2);
v___x_340_ = lean_unsigned_to_nat(4u);
v___x_341_ = lean_nat_dec_le(v___x_340_, v___x_339_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg___lam__0(lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
lean_object* v_fst_345_; lean_object* v_snd_346_; lean_object* v___y_348_; lean_object* v_i_349_; lean_object* v___y_355_; lean_object* v_i_356_; lean_object* v___y_362_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_382_; 
v_fst_345_ = lean_ctor_get(v_x_344_, 0);
lean_inc_n(v_fst_345_, 2);
v_snd_346_ = lean_ctor_get(v_x_344_, 1);
lean_inc(v_snd_346_);
lean_dec_ref(v_x_344_);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__2, &l_Std_HashMap_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_instEmptyCollection___closed__2);
lean_inc_ref(v_x_343_);
lean_inc_ref(v_x_342_);
v___x_382_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_342_, v_x_343_, v___x_372_, v_fst_345_);
switch(lean_obj_tag(v___x_382_))
{
case 0:
{
lean_object* v_index_383_; lean_object* v___x_384_; 
lean_dec_ref(v_x_343_);
lean_dec_ref(v_x_342_);
v_index_383_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_index_383_);
lean_dec_ref_known(v___x_382_, 3);
v___x_384_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_372_, v___x_371_, v_index_383_, v_fst_345_, v_snd_346_);
lean_dec(v_index_383_);
return v___x_384_;
}
case 1:
{
lean_object* v_index_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_index_385_ = lean_ctor_get(v___x_382_, 0);
lean_inc(v_index_385_);
lean_dec_ref_known(v___x_382_, 1);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = lean_uint8_once(&l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__1, &l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__1);
if (v___x_387_ == 0)
{
lean_dec(v_index_385_);
goto v___jp_373_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = lean_uint8_once(&l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__3, &l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__3_once, _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__3);
if (v___x_388_ == 0)
{
lean_dec(v_index_385_);
goto v___jp_373_;
}
else
{
lean_object* v___x_389_; 
lean_dec_ref(v_x_343_);
lean_dec_ref(v_x_342_);
v___x_389_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_372_, v___x_386_, v_index_385_, v_fst_345_, v_snd_346_);
lean_dec(v_index_385_);
return v___x_389_;
}
}
}
default: 
{
uint8_t v___x_390_; 
v___x_390_ = lean_uint8_once(&l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__1, &l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__1);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; 
lean_inc_ref(v_x_343_);
lean_inc_ref(v_x_342_);
v___x_391_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_342_, v_x_343_, v___x_372_);
v___y_362_ = v___x_391_;
goto v___jp_361_;
}
else
{
uint8_t v___x_392_; 
v___x_392_ = lean_uint8_once(&l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__3, &l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__3_once, _init_l_Std_HashMap_instSingletonProd___redArg___lam__0___closed__3);
if (v___x_392_ == 0)
{
lean_object* v___x_393_; 
lean_inc_ref(v_x_343_);
lean_inc_ref(v_x_342_);
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_342_, v_x_343_, v___x_372_);
v___y_362_ = v___x_393_;
goto v___jp_361_;
}
else
{
v___y_362_ = v___x_372_;
goto v___jp_361_;
}
}
}
}
v___jp_347_:
{
lean_object* v_size_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v_size_350_ = lean_ctor_get(v___y_348_, 0);
v___x_351_ = lean_unsigned_to_nat(1u);
v___x_352_ = lean_nat_add(v_size_350_, v___x_351_);
v___x_353_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_348_, v___x_352_, v_i_349_, v_fst_345_, v_snd_346_);
lean_dec(v_i_349_);
return v___x_353_;
}
v___jp_354_:
{
lean_object* v_size_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v_size_357_ = lean_ctor_get(v___y_355_, 0);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_add(v_size_357_, v___x_358_);
v___x_360_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_355_, v___x_359_, v_i_356_, v_fst_345_, v_snd_346_);
lean_dec(v_i_356_);
return v___x_360_;
}
v___jp_361_:
{
lean_object* v___x_363_; 
lean_inc(v_fst_345_);
v___x_363_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_342_, v_x_343_, v___y_362_, v_fst_345_);
switch(lean_obj_tag(v___x_363_))
{
case 0:
{
lean_object* v_index_364_; lean_object* v_size_365_; lean_object* v___x_366_; 
v_index_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_index_364_);
lean_dec_ref_known(v___x_363_, 3);
v_size_365_ = lean_ctor_get(v___y_362_, 0);
lean_inc(v_size_365_);
v___x_366_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_362_, v_size_365_, v_index_364_, v_fst_345_, v_snd_346_);
lean_dec(v_index_364_);
return v___x_366_;
}
case 1:
{
lean_object* v_index_367_; 
v_index_367_ = lean_ctor_get(v___x_363_, 0);
lean_inc(v_index_367_);
lean_dec_ref_known(v___x_363_, 1);
v___y_355_ = v___y_362_;
v_i_356_ = v_index_367_;
goto v___jp_354_;
}
default: 
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_362_, v___x_368_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_index_370_; 
v_index_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_index_370_);
lean_dec_ref_known(v___x_369_, 1);
v___y_355_ = v___y_362_;
v_i_356_ = v_index_370_;
goto v___jp_354_;
}
else
{
lean_dec(v_snd_346_);
lean_dec(v_fst_345_);
return v___y_362_;
}
}
}
}
v___jp_373_:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
lean_inc_ref(v_x_343_);
lean_inc_ref(v_x_342_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_342_, v_x_343_, v___x_372_);
lean_inc(v_fst_345_);
v___x_375_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_342_, v_x_343_, v___x_374_, v_fst_345_);
switch(lean_obj_tag(v___x_375_))
{
case 0:
{
lean_object* v_index_376_; lean_object* v_size_377_; lean_object* v___x_378_; 
v_index_376_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_index_376_);
lean_dec_ref_known(v___x_375_, 3);
v_size_377_ = lean_ctor_get(v___x_374_, 0);
lean_inc(v_size_377_);
v___x_378_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_374_, v_size_377_, v_index_376_, v_fst_345_, v_snd_346_);
lean_dec(v_index_376_);
return v___x_378_;
}
case 1:
{
lean_object* v_index_379_; 
v_index_379_ = lean_ctor_get(v___x_375_, 0);
lean_inc(v_index_379_);
lean_dec_ref_known(v___x_375_, 1);
v___y_348_ = v___x_374_;
v_i_349_ = v_index_379_;
goto v___jp_347_;
}
default: 
{
lean_object* v___x_380_; 
v___x_380_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_374_, v___x_371_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_index_381_; 
v_index_381_ = lean_ctor_get(v___x_380_, 0);
lean_inc(v_index_381_);
lean_dec_ref_known(v___x_380_, 1);
v___y_348_ = v___x_374_;
v_i_349_ = v_index_381_;
goto v___jp_347_;
}
else
{
lean_dec(v_snd_346_);
lean_dec(v_fst_345_);
return v___x_374_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd___redArg(lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
lean_object* v___f_396_; 
v___f_396_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_396_, 0, v_x_394_);
lean_closure_set(v___f_396_, 1, v_x_395_);
return v___f_396_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSingletonProd(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
lean_object* v___f_401_; 
v___f_401_ = lean_alloc_closure((void*)(l_Std_HashMap_instSingletonProd___redArg___lam__0), 3, 2);
lean_closure_set(v___f_401_, 0, v_x_399_);
lean_closure_set(v___f_401_, 1, v_x_400_);
return v___f_401_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg___lam__0(lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_s_405_){
_start:
{
lean_object* v_fst_406_; lean_object* v_snd_407_; lean_object* v___y_409_; lean_object* v_i_410_; lean_object* v___y_416_; lean_object* v___y_426_; lean_object* v_i_427_; lean_object* v___x_442_; 
v_fst_406_ = lean_ctor_get(v_x_404_, 0);
lean_inc_n(v_fst_406_, 2);
v_snd_407_ = lean_ctor_get(v_x_404_, 1);
lean_inc(v_snd_407_);
lean_dec_ref(v_x_404_);
lean_inc_ref(v_x_403_);
lean_inc_ref(v_x_402_);
v___x_442_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_402_, v_x_403_, v_s_405_, v_fst_406_);
switch(lean_obj_tag(v___x_442_))
{
case 0:
{
lean_object* v_index_443_; lean_object* v_size_444_; lean_object* v___x_445_; 
lean_dec_ref(v_x_403_);
lean_dec_ref(v_x_402_);
v_index_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_index_443_);
lean_dec_ref_known(v___x_442_, 3);
v_size_444_ = lean_ctor_get(v_s_405_, 0);
lean_inc(v_size_444_);
v___x_445_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_405_, v_size_444_, v_index_443_, v_fst_406_, v_snd_407_);
lean_dec(v_index_443_);
return v___x_445_;
}
case 1:
{
lean_object* v_index_446_; lean_object* v_size_447_; lean_object* v_keyArray_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v_index_446_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_index_446_);
lean_dec_ref_known(v___x_442_, 1);
v_size_447_ = lean_ctor_get(v_s_405_, 0);
v_keyArray_448_ = lean_ctor_get(v_s_405_, 1);
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_add(v_size_447_, v___x_449_);
v___x_451_ = lean_array_get_size(v_keyArray_448_);
v___x_452_ = lean_nat_dec_lt(v___x_450_, v___x_451_);
if (v___x_452_ == 0)
{
lean_dec(v___x_450_);
lean_dec(v_index_446_);
goto v___jp_432_;
}
else
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_453_ = lean_unsigned_to_nat(4u);
v___x_454_ = lean_nat_mul(v___x_450_, v___x_453_);
v___x_455_ = lean_unsigned_to_nat(3u);
v___x_456_ = lean_nat_mul(v___x_451_, v___x_455_);
v___x_457_ = lean_nat_dec_le(v___x_454_, v___x_456_);
lean_dec(v___x_456_);
lean_dec(v___x_454_);
if (v___x_457_ == 0)
{
lean_dec(v___x_450_);
lean_dec(v_index_446_);
goto v___jp_432_;
}
else
{
lean_object* v___x_458_; 
lean_dec_ref(v_x_403_);
lean_dec_ref(v_x_402_);
v___x_458_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_405_, v___x_450_, v_index_446_, v_fst_406_, v_snd_407_);
lean_dec(v_index_446_);
return v___x_458_;
}
}
}
default: 
{
lean_object* v_size_459_; lean_object* v_keyArray_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v_size_459_ = lean_ctor_get(v_s_405_, 0);
v_keyArray_460_ = lean_ctor_get(v_s_405_, 1);
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = lean_nat_add(v_size_459_, v___x_461_);
v___x_463_ = lean_array_get_size(v_keyArray_460_);
v___x_464_ = lean_nat_dec_lt(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_465_; 
lean_dec(v___x_462_);
lean_inc_ref(v_x_403_);
lean_inc_ref(v_x_402_);
v___x_465_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_402_, v_x_403_, v_s_405_);
v___y_416_ = v___x_465_;
goto v___jp_415_;
}
else
{
lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v___x_466_ = lean_unsigned_to_nat(4u);
v___x_467_ = lean_nat_mul(v___x_462_, v___x_466_);
lean_dec(v___x_462_);
v___x_468_ = lean_unsigned_to_nat(3u);
v___x_469_ = lean_nat_mul(v___x_463_, v___x_468_);
v___x_470_ = lean_nat_dec_le(v___x_467_, v___x_469_);
lean_dec(v___x_469_);
lean_dec(v___x_467_);
if (v___x_470_ == 0)
{
lean_object* v___x_471_; 
lean_inc_ref(v_x_403_);
lean_inc_ref(v_x_402_);
v___x_471_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_402_, v_x_403_, v_s_405_);
v___y_416_ = v___x_471_;
goto v___jp_415_;
}
else
{
v___y_416_ = v_s_405_;
goto v___jp_415_;
}
}
}
}
v___jp_408_:
{
lean_object* v_size_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_size_411_ = lean_ctor_get(v___y_409_, 0);
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_nat_add(v_size_411_, v___x_412_);
v___x_414_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_409_, v___x_413_, v_i_410_, v_fst_406_, v_snd_407_);
lean_dec(v_i_410_);
return v___x_414_;
}
v___jp_415_:
{
lean_object* v___x_417_; 
lean_inc(v_fst_406_);
v___x_417_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_402_, v_x_403_, v___y_416_, v_fst_406_);
switch(lean_obj_tag(v___x_417_))
{
case 0:
{
lean_object* v_index_418_; lean_object* v_size_419_; lean_object* v___x_420_; 
v_index_418_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_index_418_);
lean_dec_ref_known(v___x_417_, 3);
v_size_419_ = lean_ctor_get(v___y_416_, 0);
lean_inc(v_size_419_);
v___x_420_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_416_, v_size_419_, v_index_418_, v_fst_406_, v_snd_407_);
lean_dec(v_index_418_);
return v___x_420_;
}
case 1:
{
lean_object* v_index_421_; 
v_index_421_ = lean_ctor_get(v___x_417_, 0);
lean_inc(v_index_421_);
lean_dec_ref_known(v___x_417_, 1);
v___y_409_ = v___y_416_;
v_i_410_ = v_index_421_;
goto v___jp_408_;
}
default: 
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_416_, v___x_422_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_index_424_; 
v_index_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_index_424_);
lean_dec_ref_known(v___x_423_, 1);
v___y_409_ = v___y_416_;
v_i_410_ = v_index_424_;
goto v___jp_408_;
}
else
{
lean_dec(v_snd_407_);
lean_dec(v_fst_406_);
return v___y_416_;
}
}
}
}
v___jp_425_:
{
lean_object* v_size_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_size_428_ = lean_ctor_get(v___y_426_, 0);
v___x_429_ = lean_unsigned_to_nat(1u);
v___x_430_ = lean_nat_add(v_size_428_, v___x_429_);
v___x_431_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_426_, v___x_430_, v_i_427_, v_fst_406_, v_snd_407_);
lean_dec(v_i_427_);
return v___x_431_;
}
v___jp_432_:
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_inc_ref(v_x_403_);
lean_inc_ref(v_x_402_);
v___x_433_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_402_, v_x_403_, v_s_405_);
lean_inc(v_fst_406_);
v___x_434_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_402_, v_x_403_, v___x_433_, v_fst_406_);
switch(lean_obj_tag(v___x_434_))
{
case 0:
{
lean_object* v_index_435_; lean_object* v_size_436_; lean_object* v___x_437_; 
v_index_435_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_index_435_);
lean_dec_ref_known(v___x_434_, 3);
v_size_436_ = lean_ctor_get(v___x_433_, 0);
lean_inc(v_size_436_);
v___x_437_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_433_, v_size_436_, v_index_435_, v_fst_406_, v_snd_407_);
lean_dec(v_index_435_);
return v___x_437_;
}
case 1:
{
lean_object* v_index_438_; 
v_index_438_ = lean_ctor_get(v___x_434_, 0);
lean_inc(v_index_438_);
lean_dec_ref_known(v___x_434_, 1);
v___y_426_ = v___x_433_;
v_i_427_ = v_index_438_;
goto v___jp_425_;
}
default: 
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_unsigned_to_nat(0u);
v___x_440_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_433_, v___x_439_);
if (lean_obj_tag(v___x_440_) == 0)
{
lean_object* v_index_441_; 
v_index_441_ = lean_ctor_get(v___x_440_, 0);
lean_inc(v_index_441_);
lean_dec_ref_known(v___x_440_, 1);
v___y_426_ = v___x_433_;
v_i_427_ = v_index_441_;
goto v___jp_425_;
}
else
{
lean_dec(v_snd_407_);
lean_dec(v_fst_406_);
return v___x_433_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd___redArg(lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v___f_474_; 
v___f_474_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_474_, 0, v_x_472_);
lean_closure_set(v___f_474_, 1, v_x_473_);
return v___f_474_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInsertProd(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
lean_object* v___f_479_; 
v___f_479_ = lean_alloc_closure((void*)(l_Std_HashMap_instInsertProd___redArg___lam__0), 4, 2);
lean_closure_set(v___f_479_, 0, v_x_477_);
lean_closure_set(v___f_479_, 1, v_x_478_);
return v___f_479_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew___redArg(lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_m_482_, lean_object* v_a_483_, lean_object* v_b_484_){
_start:
{
lean_object* v___y_486_; lean_object* v_i_487_; lean_object* v___y_503_; lean_object* v_i_504_; lean_object* v___y_510_; lean_object* v___x_519_; 
lean_inc(v_a_483_);
lean_inc_ref(v_x_481_);
lean_inc_ref(v_x_480_);
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_480_, v_x_481_, v_m_482_, v_a_483_);
switch(lean_obj_tag(v___x_519_))
{
case 0:
{
lean_dec_ref_known(v___x_519_, 3);
lean_dec(v_b_484_);
lean_dec(v_a_483_);
lean_dec_ref(v_x_481_);
lean_dec_ref(v_x_480_);
return v_m_482_;
}
case 1:
{
lean_object* v_index_520_; lean_object* v_size_521_; lean_object* v_keyArray_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_index_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_index_520_);
lean_dec_ref_known(v___x_519_, 1);
v_size_521_ = lean_ctor_get(v_m_482_, 0);
v_keyArray_522_ = lean_ctor_get(v_m_482_, 1);
v___x_523_ = lean_unsigned_to_nat(1u);
v___x_524_ = lean_nat_add(v_size_521_, v___x_523_);
v___x_525_ = lean_array_get_size(v_keyArray_522_);
v___x_526_ = lean_nat_dec_lt(v___x_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec(v___x_524_);
lean_dec(v_index_520_);
goto v___jp_492_;
}
else
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_527_ = lean_unsigned_to_nat(4u);
v___x_528_ = lean_nat_mul(v___x_524_, v___x_527_);
v___x_529_ = lean_unsigned_to_nat(3u);
v___x_530_ = lean_nat_mul(v___x_525_, v___x_529_);
v___x_531_ = lean_nat_dec_le(v___x_528_, v___x_530_);
lean_dec(v___x_530_);
lean_dec(v___x_528_);
if (v___x_531_ == 0)
{
lean_dec(v___x_524_);
lean_dec(v_index_520_);
goto v___jp_492_;
}
else
{
lean_object* v___x_532_; 
lean_dec_ref(v_x_481_);
lean_dec_ref(v_x_480_);
v___x_532_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_482_, v___x_524_, v_index_520_, v_a_483_, v_b_484_);
lean_dec(v_index_520_);
return v___x_532_;
}
}
}
default: 
{
lean_object* v_size_533_; lean_object* v_keyArray_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v_size_533_ = lean_ctor_get(v_m_482_, 0);
v_keyArray_534_ = lean_ctor_get(v_m_482_, 1);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_size_533_, v___x_535_);
v___x_537_ = lean_array_get_size(v_keyArray_534_);
v___x_538_ = lean_nat_dec_lt(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; 
lean_dec(v___x_536_);
lean_inc_ref(v_x_481_);
lean_inc_ref(v_x_480_);
v___x_539_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_480_, v_x_481_, v_m_482_);
v___y_510_ = v___x_539_;
goto v___jp_509_;
}
else
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_540_ = lean_unsigned_to_nat(4u);
v___x_541_ = lean_nat_mul(v___x_536_, v___x_540_);
lean_dec(v___x_536_);
v___x_542_ = lean_unsigned_to_nat(3u);
v___x_543_ = lean_nat_mul(v___x_537_, v___x_542_);
v___x_544_ = lean_nat_dec_le(v___x_541_, v___x_543_);
lean_dec(v___x_543_);
lean_dec(v___x_541_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; 
lean_inc_ref(v_x_481_);
lean_inc_ref(v_x_480_);
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_480_, v_x_481_, v_m_482_);
v___y_510_ = v___x_545_;
goto v___jp_509_;
}
else
{
v___y_510_ = v_m_482_;
goto v___jp_509_;
}
}
}
}
v___jp_485_:
{
lean_object* v_size_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v_size_488_ = lean_ctor_get(v___y_486_, 0);
v___x_489_ = lean_unsigned_to_nat(1u);
v___x_490_ = lean_nat_add(v_size_488_, v___x_489_);
v___x_491_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_486_, v___x_490_, v_i_487_, v_a_483_, v_b_484_);
lean_dec(v_i_487_);
return v___x_491_;
}
v___jp_492_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_inc_ref(v_x_481_);
lean_inc_ref(v_x_480_);
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_480_, v_x_481_, v_m_482_);
lean_inc(v_a_483_);
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_480_, v_x_481_, v___x_493_, v_a_483_);
switch(lean_obj_tag(v___x_494_))
{
case 0:
{
lean_object* v_index_495_; lean_object* v_size_496_; lean_object* v___x_497_; 
v_index_495_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_index_495_);
lean_dec_ref_known(v___x_494_, 3);
v_size_496_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_size_496_);
v___x_497_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_493_, v_size_496_, v_index_495_, v_a_483_, v_b_484_);
lean_dec(v_index_495_);
return v___x_497_;
}
case 1:
{
lean_object* v_index_498_; 
v_index_498_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_index_498_);
lean_dec_ref_known(v___x_494_, 1);
v___y_486_ = v___x_493_;
v_i_487_ = v_index_498_;
goto v___jp_485_;
}
default: 
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(0u);
v___x_500_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_493_, v___x_499_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_index_501_; 
v_index_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_index_501_);
lean_dec_ref_known(v___x_500_, 1);
v___y_486_ = v___x_493_;
v_i_487_ = v_index_501_;
goto v___jp_485_;
}
else
{
lean_dec(v_b_484_);
lean_dec(v_a_483_);
return v___x_493_;
}
}
}
}
v___jp_502_:
{
lean_object* v_size_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; 
v_size_505_ = lean_ctor_get(v___y_503_, 0);
v___x_506_ = lean_unsigned_to_nat(1u);
v___x_507_ = lean_nat_add(v_size_505_, v___x_506_);
v___x_508_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_503_, v___x_507_, v_i_504_, v_a_483_, v_b_484_);
lean_dec(v_i_504_);
return v___x_508_;
}
v___jp_509_:
{
lean_object* v___x_511_; 
lean_inc(v_a_483_);
v___x_511_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_480_, v_x_481_, v___y_510_, v_a_483_);
switch(lean_obj_tag(v___x_511_))
{
case 0:
{
lean_object* v_index_512_; lean_object* v_size_513_; lean_object* v___x_514_; 
v_index_512_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_index_512_);
lean_dec_ref_known(v___x_511_, 3);
v_size_513_ = lean_ctor_get(v___y_510_, 0);
lean_inc(v_size_513_);
v___x_514_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_510_, v_size_513_, v_index_512_, v_a_483_, v_b_484_);
lean_dec(v_index_512_);
return v___x_514_;
}
case 1:
{
lean_object* v_index_515_; 
v_index_515_ = lean_ctor_get(v___x_511_, 0);
lean_inc(v_index_515_);
lean_dec_ref_known(v___x_511_, 1);
v___y_503_ = v___y_510_;
v_i_504_ = v_index_515_;
goto v___jp_502_;
}
default: 
{
lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_516_ = lean_unsigned_to_nat(0u);
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_510_, v___x_516_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_object* v_index_518_; 
v_index_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_index_518_);
lean_dec_ref_known(v___x_517_, 1);
v___y_503_ = v___y_510_;
v_i_504_ = v_index_518_;
goto v___jp_502_;
}
else
{
lean_dec(v_b_484_);
lean_dec(v_a_483_);
return v___y_510_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertIfNew(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_x_548_, lean_object* v_x_549_, lean_object* v_m_550_, lean_object* v_a_551_, lean_object* v_b_552_){
_start:
{
lean_object* v___y_554_; lean_object* v_i_555_; lean_object* v___y_571_; lean_object* v_i_572_; lean_object* v___y_578_; lean_object* v___x_587_; 
lean_inc(v_a_551_);
lean_inc_ref(v_x_549_);
lean_inc_ref(v_x_548_);
v___x_587_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_548_, v_x_549_, v_m_550_, v_a_551_);
switch(lean_obj_tag(v___x_587_))
{
case 0:
{
lean_dec_ref_known(v___x_587_, 3);
lean_dec(v_b_552_);
lean_dec(v_a_551_);
lean_dec_ref(v_x_549_);
lean_dec_ref(v_x_548_);
return v_m_550_;
}
case 1:
{
lean_object* v_index_588_; lean_object* v_size_589_; lean_object* v_keyArray_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_index_588_ = lean_ctor_get(v___x_587_, 0);
lean_inc(v_index_588_);
lean_dec_ref_known(v___x_587_, 1);
v_size_589_ = lean_ctor_get(v_m_550_, 0);
v_keyArray_590_ = lean_ctor_get(v_m_550_, 1);
v___x_591_ = lean_unsigned_to_nat(1u);
v___x_592_ = lean_nat_add(v_size_589_, v___x_591_);
v___x_593_ = lean_array_get_size(v_keyArray_590_);
v___x_594_ = lean_nat_dec_lt(v___x_592_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec(v___x_592_);
lean_dec(v_index_588_);
goto v___jp_560_;
}
else
{
lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v___x_595_ = lean_unsigned_to_nat(4u);
v___x_596_ = lean_nat_mul(v___x_592_, v___x_595_);
v___x_597_ = lean_unsigned_to_nat(3u);
v___x_598_ = lean_nat_mul(v___x_593_, v___x_597_);
v___x_599_ = lean_nat_dec_le(v___x_596_, v___x_598_);
lean_dec(v___x_598_);
lean_dec(v___x_596_);
if (v___x_599_ == 0)
{
lean_dec(v___x_592_);
lean_dec(v_index_588_);
goto v___jp_560_;
}
else
{
lean_object* v___x_600_; 
lean_dec_ref(v_x_549_);
lean_dec_ref(v_x_548_);
v___x_600_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_550_, v___x_592_, v_index_588_, v_a_551_, v_b_552_);
lean_dec(v_index_588_);
return v___x_600_;
}
}
}
default: 
{
lean_object* v_size_601_; lean_object* v_keyArray_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; uint8_t v___x_606_; 
v_size_601_ = lean_ctor_get(v_m_550_, 0);
v_keyArray_602_ = lean_ctor_get(v_m_550_, 1);
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_add(v_size_601_, v___x_603_);
v___x_605_ = lean_array_get_size(v_keyArray_602_);
v___x_606_ = lean_nat_dec_lt(v___x_604_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; 
lean_dec(v___x_604_);
lean_inc_ref(v_x_549_);
lean_inc_ref(v_x_548_);
v___x_607_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_548_, v_x_549_, v_m_550_);
v___y_578_ = v___x_607_;
goto v___jp_577_;
}
else
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; uint8_t v___x_612_; 
v___x_608_ = lean_unsigned_to_nat(4u);
v___x_609_ = lean_nat_mul(v___x_604_, v___x_608_);
lean_dec(v___x_604_);
v___x_610_ = lean_unsigned_to_nat(3u);
v___x_611_ = lean_nat_mul(v___x_605_, v___x_610_);
v___x_612_ = lean_nat_dec_le(v___x_609_, v___x_611_);
lean_dec(v___x_611_);
lean_dec(v___x_609_);
if (v___x_612_ == 0)
{
lean_object* v___x_613_; 
lean_inc_ref(v_x_549_);
lean_inc_ref(v_x_548_);
v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_548_, v_x_549_, v_m_550_);
v___y_578_ = v___x_613_;
goto v___jp_577_;
}
else
{
v___y_578_ = v_m_550_;
goto v___jp_577_;
}
}
}
}
v___jp_553_:
{
lean_object* v_size_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v_size_556_ = lean_ctor_get(v___y_554_, 0);
v___x_557_ = lean_unsigned_to_nat(1u);
v___x_558_ = lean_nat_add(v_size_556_, v___x_557_);
v___x_559_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_554_, v___x_558_, v_i_555_, v_a_551_, v_b_552_);
lean_dec(v_i_555_);
return v___x_559_;
}
v___jp_560_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_inc_ref(v_x_549_);
lean_inc_ref(v_x_548_);
v___x_561_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_548_, v_x_549_, v_m_550_);
lean_inc(v_a_551_);
v___x_562_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_548_, v_x_549_, v___x_561_, v_a_551_);
switch(lean_obj_tag(v___x_562_))
{
case 0:
{
lean_object* v_index_563_; lean_object* v_size_564_; lean_object* v___x_565_; 
v_index_563_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_index_563_);
lean_dec_ref_known(v___x_562_, 3);
v_size_564_ = lean_ctor_get(v___x_561_, 0);
lean_inc(v_size_564_);
v___x_565_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_561_, v_size_564_, v_index_563_, v_a_551_, v_b_552_);
lean_dec(v_index_563_);
return v___x_565_;
}
case 1:
{
lean_object* v_index_566_; 
v_index_566_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_index_566_);
lean_dec_ref_known(v___x_562_, 1);
v___y_554_ = v___x_561_;
v_i_555_ = v_index_566_;
goto v___jp_553_;
}
default: 
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_561_, v___x_567_);
if (lean_obj_tag(v___x_568_) == 0)
{
lean_object* v_index_569_; 
v_index_569_ = lean_ctor_get(v___x_568_, 0);
lean_inc(v_index_569_);
lean_dec_ref_known(v___x_568_, 1);
v___y_554_ = v___x_561_;
v_i_555_ = v_index_569_;
goto v___jp_553_;
}
else
{
lean_dec(v_b_552_);
lean_dec(v_a_551_);
return v___x_561_;
}
}
}
}
v___jp_570_:
{
lean_object* v_size_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_size_573_ = lean_ctor_get(v___y_571_, 0);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_add(v_size_573_, v___x_574_);
v___x_576_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_571_, v___x_575_, v_i_572_, v_a_551_, v_b_552_);
lean_dec(v_i_572_);
return v___x_576_;
}
v___jp_577_:
{
lean_object* v___x_579_; 
lean_inc(v_a_551_);
v___x_579_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_548_, v_x_549_, v___y_578_, v_a_551_);
switch(lean_obj_tag(v___x_579_))
{
case 0:
{
lean_object* v_index_580_; lean_object* v_size_581_; lean_object* v___x_582_; 
v_index_580_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_index_580_);
lean_dec_ref_known(v___x_579_, 3);
v_size_581_ = lean_ctor_get(v___y_578_, 0);
lean_inc(v_size_581_);
v___x_582_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_578_, v_size_581_, v_index_580_, v_a_551_, v_b_552_);
lean_dec(v_index_580_);
return v___x_582_;
}
case 1:
{
lean_object* v_index_583_; 
v_index_583_ = lean_ctor_get(v___x_579_, 0);
lean_inc(v_index_583_);
lean_dec_ref_known(v___x_579_, 1);
v___y_571_ = v___y_578_;
v_i_572_ = v_index_583_;
goto v___jp_570_;
}
default: 
{
lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_584_ = lean_unsigned_to_nat(0u);
v___x_585_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_578_, v___x_584_);
if (lean_obj_tag(v___x_585_) == 0)
{
lean_object* v_index_586_; 
v_index_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_index_586_);
lean_dec_ref_known(v___x_585_, 1);
v___y_571_ = v___y_578_;
v_i_572_ = v_index_586_;
goto v___jp_570_;
}
else
{
lean_dec(v_b_552_);
lean_dec(v_a_551_);
return v___y_578_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert___redArg(lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v_m_616_, lean_object* v_a_617_, lean_object* v_b_618_){
_start:
{
lean_object* v___x_619_; 
lean_inc(v_a_617_);
lean_inc_ref(v_x_615_);
lean_inc_ref(v_x_614_);
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_614_, v_x_615_, v_m_616_, v_a_617_);
switch(lean_obj_tag(v___x_619_))
{
case 0:
{
lean_object* v_index_620_; lean_object* v_size_621_; uint8_t v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec_ref(v_x_615_);
lean_dec_ref(v_x_614_);
v_index_620_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_index_620_);
lean_dec_ref_known(v___x_619_, 3);
v_size_621_ = lean_ctor_get(v_m_616_, 0);
lean_inc(v_size_621_);
v___x_622_ = 1;
v___x_623_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_616_, v_size_621_, v_index_620_, v_a_617_, v_b_618_);
lean_dec(v_index_620_);
v___x_624_ = lean_box(v___x_622_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
return v___x_625_;
}
case 1:
{
lean_object* v_index_626_; lean_object* v_size_627_; lean_object* v_keyArray_628_; uint8_t v___x_629_; lean_object* v___y_631_; lean_object* v_i_632_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_index_626_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_index_626_);
lean_dec_ref_known(v___x_619_, 1);
v_size_627_ = lean_ctor_get(v_m_616_, 0);
v_keyArray_628_ = lean_ctor_get(v_m_616_, 1);
v___x_629_ = 0;
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = lean_nat_add(v_size_627_, v___x_653_);
v___x_655_ = lean_array_get_size(v_keyArray_628_);
v___x_656_ = lean_nat_dec_lt(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_dec(v___x_654_);
lean_dec(v_index_626_);
goto v___jp_639_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; uint8_t v___x_661_; 
v___x_657_ = lean_unsigned_to_nat(4u);
v___x_658_ = lean_nat_mul(v___x_654_, v___x_657_);
v___x_659_ = lean_unsigned_to_nat(3u);
v___x_660_ = lean_nat_mul(v___x_655_, v___x_659_);
v___x_661_ = lean_nat_dec_le(v___x_658_, v___x_660_);
lean_dec(v___x_660_);
lean_dec(v___x_658_);
if (v___x_661_ == 0)
{
lean_dec(v___x_654_);
lean_dec(v_index_626_);
goto v___jp_639_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec_ref(v_x_615_);
lean_dec_ref(v_x_614_);
v___x_662_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_616_, v___x_654_, v_index_626_, v_a_617_, v_b_618_);
lean_dec(v_index_626_);
v___x_663_ = lean_box(v___x_629_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___x_662_);
return v___x_664_;
}
}
v___jp_630_:
{
lean_object* v_size_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_size_633_ = lean_ctor_get(v___y_631_, 0);
v___x_634_ = lean_unsigned_to_nat(1u);
v___x_635_ = lean_nat_add(v_size_633_, v___x_634_);
v___x_636_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_631_, v___x_635_, v_i_632_, v_a_617_, v_b_618_);
lean_dec(v_i_632_);
v___x_637_ = lean_box(v___x_629_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v___x_636_);
return v___x_638_;
}
v___jp_639_:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
lean_inc_ref(v_x_615_);
lean_inc_ref(v_x_614_);
v___x_640_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_614_, v_x_615_, v_m_616_);
lean_inc(v_a_617_);
v___x_641_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_614_, v_x_615_, v___x_640_, v_a_617_);
switch(lean_obj_tag(v___x_641_))
{
case 0:
{
lean_object* v_index_642_; lean_object* v_size_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v_index_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_index_642_);
lean_dec_ref_known(v___x_641_, 3);
v_size_643_ = lean_ctor_get(v___x_640_, 0);
lean_inc(v_size_643_);
v___x_644_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_640_, v_size_643_, v_index_642_, v_a_617_, v_b_618_);
lean_dec(v_index_642_);
v___x_645_ = lean_box(v___x_629_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
return v___x_646_;
}
case 1:
{
lean_object* v_index_647_; 
v_index_647_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_index_647_);
lean_dec_ref_known(v___x_641_, 1);
v___y_631_ = v___x_640_;
v_i_632_ = v_index_647_;
goto v___jp_630_;
}
default: 
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = lean_unsigned_to_nat(0u);
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_640_, v___x_648_);
if (lean_obj_tag(v___x_649_) == 0)
{
lean_object* v_index_650_; 
v_index_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc(v_index_650_);
lean_dec_ref_known(v___x_649_, 1);
v___y_631_ = v___x_640_;
v_i_632_ = v_index_650_;
goto v___jp_630_;
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec(v_b_618_);
lean_dec(v_a_617_);
v___x_651_ = lean_box(v___x_629_);
v___x_652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v___x_640_);
return v___x_652_;
}
}
}
}
}
default: 
{
lean_object* v_size_665_; lean_object* v_keyArray_666_; uint8_t v___x_667_; lean_object* v___y_669_; lean_object* v_i_670_; lean_object* v___y_678_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; uint8_t v___x_694_; 
v_size_665_ = lean_ctor_get(v_m_616_, 0);
v_keyArray_666_ = lean_ctor_get(v_m_616_, 1);
v___x_667_ = 0;
v___x_691_ = lean_unsigned_to_nat(1u);
v___x_692_ = lean_nat_add(v_size_665_, v___x_691_);
v___x_693_ = lean_array_get_size(v_keyArray_666_);
v___x_694_ = lean_nat_dec_lt(v___x_692_, v___x_693_);
if (v___x_694_ == 0)
{
lean_object* v___x_695_; 
lean_dec(v___x_692_);
lean_inc_ref(v_x_615_);
lean_inc_ref(v_x_614_);
v___x_695_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_614_, v_x_615_, v_m_616_);
v___y_678_ = v___x_695_;
goto v___jp_677_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_696_ = lean_unsigned_to_nat(4u);
v___x_697_ = lean_nat_mul(v___x_692_, v___x_696_);
lean_dec(v___x_692_);
v___x_698_ = lean_unsigned_to_nat(3u);
v___x_699_ = lean_nat_mul(v___x_693_, v___x_698_);
v___x_700_ = lean_nat_dec_le(v___x_697_, v___x_699_);
lean_dec(v___x_699_);
lean_dec(v___x_697_);
if (v___x_700_ == 0)
{
lean_object* v___x_701_; 
lean_inc_ref(v_x_615_);
lean_inc_ref(v_x_614_);
v___x_701_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_614_, v_x_615_, v_m_616_);
v___y_678_ = v___x_701_;
goto v___jp_677_;
}
else
{
v___y_678_ = v_m_616_;
goto v___jp_677_;
}
}
v___jp_668_:
{
lean_object* v_size_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v_size_671_ = lean_ctor_get(v___y_669_, 0);
v___x_672_ = lean_unsigned_to_nat(1u);
v___x_673_ = lean_nat_add(v_size_671_, v___x_672_);
v___x_674_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_669_, v___x_673_, v_i_670_, v_a_617_, v_b_618_);
lean_dec(v_i_670_);
v___x_675_ = lean_box(v___x_667_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
lean_ctor_set(v___x_676_, 1, v___x_674_);
return v___x_676_;
}
v___jp_677_:
{
lean_object* v___x_679_; 
lean_inc(v_a_617_);
v___x_679_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_614_, v_x_615_, v___y_678_, v_a_617_);
switch(lean_obj_tag(v___x_679_))
{
case 0:
{
lean_object* v_index_680_; lean_object* v_size_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v_index_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_index_680_);
lean_dec_ref_known(v___x_679_, 3);
v_size_681_ = lean_ctor_get(v___y_678_, 0);
lean_inc(v_size_681_);
v___x_682_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_678_, v_size_681_, v_index_680_, v_a_617_, v_b_618_);
lean_dec(v_index_680_);
v___x_683_ = lean_box(v___x_667_);
v___x_684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_684_, 0, v___x_683_);
lean_ctor_set(v___x_684_, 1, v___x_682_);
return v___x_684_;
}
case 1:
{
lean_object* v_index_685_; 
v_index_685_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_index_685_);
lean_dec_ref_known(v___x_679_, 1);
v___y_669_ = v___y_678_;
v_i_670_ = v_index_685_;
goto v___jp_668_;
}
default: 
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_678_, v___x_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_index_688_; 
v_index_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_index_688_);
lean_dec_ref_known(v___x_687_, 1);
v___y_669_ = v___y_678_;
v_i_670_ = v_index_688_;
goto v___jp_668_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec(v_b_618_);
lean_dec(v_a_617_);
v___x_689_ = lean_box(v___x_667_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___y_678_);
return v___x_690_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsert(lean_object* v_00_u03b1_702_, lean_object* v_00_u03b2_703_, lean_object* v_x_704_, lean_object* v_x_705_, lean_object* v_m_706_, lean_object* v_a_707_, lean_object* v_b_708_){
_start:
{
lean_object* v___x_709_; 
lean_inc(v_a_707_);
lean_inc_ref(v_x_705_);
lean_inc_ref(v_x_704_);
v___x_709_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_704_, v_x_705_, v_m_706_, v_a_707_);
switch(lean_obj_tag(v___x_709_))
{
case 0:
{
lean_object* v_index_710_; lean_object* v_size_711_; uint8_t v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
lean_dec_ref(v_x_705_);
lean_dec_ref(v_x_704_);
v_index_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_index_710_);
lean_dec_ref_known(v___x_709_, 3);
v_size_711_ = lean_ctor_get(v_m_706_, 0);
lean_inc(v_size_711_);
v___x_712_ = 1;
v___x_713_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_706_, v_size_711_, v_index_710_, v_a_707_, v_b_708_);
lean_dec(v_index_710_);
v___x_714_ = lean_box(v___x_712_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
lean_ctor_set(v___x_715_, 1, v___x_713_);
return v___x_715_;
}
case 1:
{
lean_object* v_index_716_; lean_object* v_size_717_; lean_object* v_keyArray_718_; uint8_t v___x_719_; lean_object* v___y_721_; lean_object* v_i_722_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v_index_716_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_index_716_);
lean_dec_ref_known(v___x_709_, 1);
v_size_717_ = lean_ctor_get(v_m_706_, 0);
v_keyArray_718_ = lean_ctor_get(v_m_706_, 1);
v___x_719_ = 0;
v___x_743_ = lean_unsigned_to_nat(1u);
v___x_744_ = lean_nat_add(v_size_717_, v___x_743_);
v___x_745_ = lean_array_get_size(v_keyArray_718_);
v___x_746_ = lean_nat_dec_lt(v___x_744_, v___x_745_);
if (v___x_746_ == 0)
{
lean_dec(v___x_744_);
lean_dec(v_index_716_);
goto v___jp_729_;
}
else
{
lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_747_ = lean_unsigned_to_nat(4u);
v___x_748_ = lean_nat_mul(v___x_744_, v___x_747_);
v___x_749_ = lean_unsigned_to_nat(3u);
v___x_750_ = lean_nat_mul(v___x_745_, v___x_749_);
v___x_751_ = lean_nat_dec_le(v___x_748_, v___x_750_);
lean_dec(v___x_750_);
lean_dec(v___x_748_);
if (v___x_751_ == 0)
{
lean_dec(v___x_744_);
lean_dec(v_index_716_);
goto v___jp_729_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; 
lean_dec_ref(v_x_705_);
lean_dec_ref(v_x_704_);
v___x_752_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_706_, v___x_744_, v_index_716_, v_a_707_, v_b_708_);
lean_dec(v_index_716_);
v___x_753_ = lean_box(v___x_719_);
v___x_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_754_, 0, v___x_753_);
lean_ctor_set(v___x_754_, 1, v___x_752_);
return v___x_754_;
}
}
v___jp_720_:
{
lean_object* v_size_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
v_size_723_ = lean_ctor_get(v___y_721_, 0);
v___x_724_ = lean_unsigned_to_nat(1u);
v___x_725_ = lean_nat_add(v_size_723_, v___x_724_);
v___x_726_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_721_, v___x_725_, v_i_722_, v_a_707_, v_b_708_);
lean_dec(v_i_722_);
v___x_727_ = lean_box(v___x_719_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
return v___x_728_;
}
v___jp_729_:
{
lean_object* v___x_730_; lean_object* v___x_731_; 
lean_inc_ref(v_x_705_);
lean_inc_ref(v_x_704_);
v___x_730_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_704_, v_x_705_, v_m_706_);
lean_inc(v_a_707_);
v___x_731_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_704_, v_x_705_, v___x_730_, v_a_707_);
switch(lean_obj_tag(v___x_731_))
{
case 0:
{
lean_object* v_index_732_; lean_object* v_size_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v_index_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_index_732_);
lean_dec_ref_known(v___x_731_, 3);
v_size_733_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_size_733_);
v___x_734_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_730_, v_size_733_, v_index_732_, v_a_707_, v_b_708_);
lean_dec(v_index_732_);
v___x_735_ = lean_box(v___x_719_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_734_);
return v___x_736_;
}
case 1:
{
lean_object* v_index_737_; 
v_index_737_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_index_737_);
lean_dec_ref_known(v___x_731_, 1);
v___y_721_ = v___x_730_;
v_i_722_ = v_index_737_;
goto v___jp_720_;
}
default: 
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_unsigned_to_nat(0u);
v___x_739_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_730_, v___x_738_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_index_740_; 
v_index_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_index_740_);
lean_dec_ref_known(v___x_739_, 1);
v___y_721_ = v___x_730_;
v_i_722_ = v_index_740_;
goto v___jp_720_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; 
lean_dec(v_b_708_);
lean_dec(v_a_707_);
v___x_741_ = lean_box(v___x_719_);
v___x_742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_741_);
lean_ctor_set(v___x_742_, 1, v___x_730_);
return v___x_742_;
}
}
}
}
}
default: 
{
lean_object* v_size_755_; lean_object* v_keyArray_756_; uint8_t v___x_757_; lean_object* v___y_759_; lean_object* v_i_760_; lean_object* v___y_768_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; uint8_t v___x_784_; 
v_size_755_ = lean_ctor_get(v_m_706_, 0);
v_keyArray_756_ = lean_ctor_get(v_m_706_, 1);
v___x_757_ = 0;
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_size_755_, v___x_781_);
v___x_783_ = lean_array_get_size(v_keyArray_756_);
v___x_784_ = lean_nat_dec_lt(v___x_782_, v___x_783_);
if (v___x_784_ == 0)
{
lean_object* v___x_785_; 
lean_dec(v___x_782_);
lean_inc_ref(v_x_705_);
lean_inc_ref(v_x_704_);
v___x_785_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_704_, v_x_705_, v_m_706_);
v___y_768_ = v___x_785_;
goto v___jp_767_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_786_ = lean_unsigned_to_nat(4u);
v___x_787_ = lean_nat_mul(v___x_782_, v___x_786_);
lean_dec(v___x_782_);
v___x_788_ = lean_unsigned_to_nat(3u);
v___x_789_ = lean_nat_mul(v___x_783_, v___x_788_);
v___x_790_ = lean_nat_dec_le(v___x_787_, v___x_789_);
lean_dec(v___x_789_);
lean_dec(v___x_787_);
if (v___x_790_ == 0)
{
lean_object* v___x_791_; 
lean_inc_ref(v_x_705_);
lean_inc_ref(v_x_704_);
v___x_791_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_704_, v_x_705_, v_m_706_);
v___y_768_ = v___x_791_;
goto v___jp_767_;
}
else
{
v___y_768_ = v_m_706_;
goto v___jp_767_;
}
}
v___jp_758_:
{
lean_object* v_size_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v_size_761_ = lean_ctor_get(v___y_759_, 0);
v___x_762_ = lean_unsigned_to_nat(1u);
v___x_763_ = lean_nat_add(v_size_761_, v___x_762_);
v___x_764_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_759_, v___x_763_, v_i_760_, v_a_707_, v_b_708_);
lean_dec(v_i_760_);
v___x_765_ = lean_box(v___x_757_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
return v___x_766_;
}
v___jp_767_:
{
lean_object* v___x_769_; 
lean_inc(v_a_707_);
v___x_769_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_704_, v_x_705_, v___y_768_, v_a_707_);
switch(lean_obj_tag(v___x_769_))
{
case 0:
{
lean_object* v_index_770_; lean_object* v_size_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v_index_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_index_770_);
lean_dec_ref_known(v___x_769_, 3);
v_size_771_ = lean_ctor_get(v___y_768_, 0);
lean_inc(v_size_771_);
v___x_772_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_768_, v_size_771_, v_index_770_, v_a_707_, v_b_708_);
lean_dec(v_index_770_);
v___x_773_ = lean_box(v___x_757_);
v___x_774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
return v___x_774_;
}
case 1:
{
lean_object* v_index_775_; 
v_index_775_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_index_775_);
lean_dec_ref_known(v___x_769_, 1);
v___y_759_ = v___y_768_;
v_i_760_ = v_index_775_;
goto v___jp_758_;
}
default: 
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_unsigned_to_nat(0u);
v___x_777_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_768_, v___x_776_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_index_778_; 
v_index_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_index_778_);
lean_dec_ref_known(v___x_777_, 1);
v___y_759_ = v___y_768_;
v_i_760_ = v_index_778_;
goto v___jp_758_;
}
else
{
lean_object* v___x_779_; lean_object* v___x_780_; 
lean_dec(v_b_708_);
lean_dec(v_a_707_);
v___x_779_ = lean_box(v___x_757_);
v___x_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_780_, 0, v___x_779_);
lean_ctor_set(v___x_780_, 1, v___y_768_);
return v___x_780_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew___redArg(lean_object* v_x_792_, lean_object* v_x_793_, lean_object* v_m_794_, lean_object* v_a_795_, lean_object* v_b_796_){
_start:
{
lean_object* v___x_797_; 
lean_inc(v_a_795_);
lean_inc_ref(v_x_793_);
lean_inc_ref(v_x_792_);
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_792_, v_x_793_, v_m_794_, v_a_795_);
switch(lean_obj_tag(v___x_797_))
{
case 0:
{
uint8_t v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec_ref_known(v___x_797_, 3);
lean_dec(v_b_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_x_793_);
lean_dec_ref(v_x_792_);
v___x_798_ = 1;
v___x_799_ = lean_box(v___x_798_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v_m_794_);
return v___x_800_;
}
case 1:
{
lean_object* v_index_801_; lean_object* v_size_802_; lean_object* v_keyArray_803_; uint8_t v___x_804_; lean_object* v___y_806_; lean_object* v_i_807_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; uint8_t v___x_831_; 
v_index_801_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_index_801_);
lean_dec_ref_known(v___x_797_, 1);
v_size_802_ = lean_ctor_get(v_m_794_, 0);
v_keyArray_803_ = lean_ctor_get(v_m_794_, 1);
v___x_804_ = 0;
v___x_828_ = lean_unsigned_to_nat(1u);
v___x_829_ = lean_nat_add(v_size_802_, v___x_828_);
v___x_830_ = lean_array_get_size(v_keyArray_803_);
v___x_831_ = lean_nat_dec_lt(v___x_829_, v___x_830_);
if (v___x_831_ == 0)
{
lean_dec(v___x_829_);
lean_dec(v_index_801_);
goto v___jp_814_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v___x_832_ = lean_unsigned_to_nat(4u);
v___x_833_ = lean_nat_mul(v___x_829_, v___x_832_);
v___x_834_ = lean_unsigned_to_nat(3u);
v___x_835_ = lean_nat_mul(v___x_830_, v___x_834_);
v___x_836_ = lean_nat_dec_le(v___x_833_, v___x_835_);
lean_dec(v___x_835_);
lean_dec(v___x_833_);
if (v___x_836_ == 0)
{
lean_dec(v___x_829_);
lean_dec(v_index_801_);
goto v___jp_814_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec_ref(v_x_793_);
lean_dec_ref(v_x_792_);
v___x_837_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_794_, v___x_829_, v_index_801_, v_a_795_, v_b_796_);
lean_dec(v_index_801_);
v___x_838_ = lean_box(v___x_804_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v___x_837_);
return v___x_839_;
}
}
v___jp_805_:
{
lean_object* v_size_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; 
v_size_808_ = lean_ctor_get(v___y_806_, 0);
v___x_809_ = lean_unsigned_to_nat(1u);
v___x_810_ = lean_nat_add(v_size_808_, v___x_809_);
v___x_811_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_806_, v___x_810_, v_i_807_, v_a_795_, v_b_796_);
lean_dec(v_i_807_);
v___x_812_ = lean_box(v___x_804_);
v___x_813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_812_);
lean_ctor_set(v___x_813_, 1, v___x_811_);
return v___x_813_;
}
v___jp_814_:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
lean_inc_ref(v_x_793_);
lean_inc_ref(v_x_792_);
v___x_815_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_792_, v_x_793_, v_m_794_);
lean_inc(v_a_795_);
v___x_816_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_792_, v_x_793_, v___x_815_, v_a_795_);
switch(lean_obj_tag(v___x_816_))
{
case 0:
{
lean_object* v_index_817_; lean_object* v_size_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_index_817_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_index_817_);
lean_dec_ref_known(v___x_816_, 3);
v_size_818_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_size_818_);
v___x_819_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_815_, v_size_818_, v_index_817_, v_a_795_, v_b_796_);
lean_dec(v_index_817_);
v___x_820_ = lean_box(v___x_804_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_819_);
return v___x_821_;
}
case 1:
{
lean_object* v_index_822_; 
v_index_822_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_index_822_);
lean_dec_ref_known(v___x_816_, 1);
v___y_806_ = v___x_815_;
v_i_807_ = v_index_822_;
goto v___jp_805_;
}
default: 
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(0u);
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_815_, v___x_823_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_index_825_; 
v_index_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_index_825_);
lean_dec_ref_known(v___x_824_, 1);
v___y_806_ = v___x_815_;
v_i_807_ = v_index_825_;
goto v___jp_805_;
}
else
{
lean_object* v___x_826_; lean_object* v___x_827_; 
lean_dec(v_b_796_);
lean_dec(v_a_795_);
v___x_826_ = lean_box(v___x_804_);
v___x_827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_827_, 0, v___x_826_);
lean_ctor_set(v___x_827_, 1, v___x_815_);
return v___x_827_;
}
}
}
}
}
default: 
{
lean_object* v_size_840_; lean_object* v_keyArray_841_; uint8_t v___x_842_; lean_object* v___y_844_; lean_object* v_i_845_; lean_object* v___y_853_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_size_840_ = lean_ctor_get(v_m_794_, 0);
v_keyArray_841_ = lean_ctor_get(v_m_794_, 1);
v___x_842_ = 0;
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_nat_add(v_size_840_, v___x_866_);
v___x_868_ = lean_array_get_size(v_keyArray_841_);
v___x_869_ = lean_nat_dec_lt(v___x_867_, v___x_868_);
if (v___x_869_ == 0)
{
lean_object* v___x_870_; 
lean_dec(v___x_867_);
lean_inc_ref(v_x_793_);
lean_inc_ref(v_x_792_);
v___x_870_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_792_, v_x_793_, v_m_794_);
v___y_853_ = v___x_870_;
goto v___jp_852_;
}
else
{
lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v___x_871_ = lean_unsigned_to_nat(4u);
v___x_872_ = lean_nat_mul(v___x_867_, v___x_871_);
lean_dec(v___x_867_);
v___x_873_ = lean_unsigned_to_nat(3u);
v___x_874_ = lean_nat_mul(v___x_868_, v___x_873_);
v___x_875_ = lean_nat_dec_le(v___x_872_, v___x_874_);
lean_dec(v___x_874_);
lean_dec(v___x_872_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; 
lean_inc_ref(v_x_793_);
lean_inc_ref(v_x_792_);
v___x_876_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_792_, v_x_793_, v_m_794_);
v___y_853_ = v___x_876_;
goto v___jp_852_;
}
else
{
v___y_853_ = v_m_794_;
goto v___jp_852_;
}
}
v___jp_843_:
{
lean_object* v_size_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v_size_846_ = lean_ctor_get(v___y_844_, 0);
v___x_847_ = lean_unsigned_to_nat(1u);
v___x_848_ = lean_nat_add(v_size_846_, v___x_847_);
v___x_849_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_844_, v___x_848_, v_i_845_, v_a_795_, v_b_796_);
lean_dec(v_i_845_);
v___x_850_ = lean_box(v___x_842_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_849_);
return v___x_851_;
}
v___jp_852_:
{
lean_object* v___x_854_; 
lean_inc(v_a_795_);
v___x_854_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_792_, v_x_793_, v___y_853_, v_a_795_);
switch(lean_obj_tag(v___x_854_))
{
case 0:
{
lean_object* v_index_855_; lean_object* v_size_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_index_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_index_855_);
lean_dec_ref_known(v___x_854_, 3);
v_size_856_ = lean_ctor_get(v___y_853_, 0);
lean_inc(v_size_856_);
v___x_857_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_853_, v_size_856_, v_index_855_, v_a_795_, v_b_796_);
lean_dec(v_index_855_);
v___x_858_ = lean_box(v___x_842_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v___x_857_);
return v___x_859_;
}
case 1:
{
lean_object* v_index_860_; 
v_index_860_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_index_860_);
lean_dec_ref_known(v___x_854_, 1);
v___y_844_ = v___y_853_;
v_i_845_ = v_index_860_;
goto v___jp_843_;
}
default: 
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_unsigned_to_nat(0u);
v___x_862_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_853_, v___x_861_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_index_863_; 
v_index_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_index_863_);
lean_dec_ref_known(v___x_862_, 1);
v___y_844_ = v___y_853_;
v_i_845_ = v_index_863_;
goto v___jp_843_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; 
lean_dec(v_b_796_);
lean_dec(v_a_795_);
v___x_864_ = lean_box(v___x_842_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___y_853_);
return v___x_865_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_containsThenInsertIfNew(lean_object* v_00_u03b1_877_, lean_object* v_00_u03b2_878_, lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_m_881_, lean_object* v_a_882_, lean_object* v_b_883_){
_start:
{
lean_object* v___x_884_; 
lean_inc(v_a_882_);
lean_inc_ref(v_x_880_);
lean_inc_ref(v_x_879_);
v___x_884_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_879_, v_x_880_, v_m_881_, v_a_882_);
switch(lean_obj_tag(v___x_884_))
{
case 0:
{
uint8_t v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
lean_dec_ref_known(v___x_884_, 3);
lean_dec(v_b_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_x_880_);
lean_dec_ref(v_x_879_);
v___x_885_ = 1;
v___x_886_ = lean_box(v___x_885_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v_m_881_);
return v___x_887_;
}
case 1:
{
lean_object* v_index_888_; lean_object* v_size_889_; lean_object* v_keyArray_890_; uint8_t v___x_891_; lean_object* v___y_893_; lean_object* v_i_894_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_index_888_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_index_888_);
lean_dec_ref_known(v___x_884_, 1);
v_size_889_ = lean_ctor_get(v_m_881_, 0);
v_keyArray_890_ = lean_ctor_get(v_m_881_, 1);
v___x_891_ = 0;
v___x_915_ = lean_unsigned_to_nat(1u);
v___x_916_ = lean_nat_add(v_size_889_, v___x_915_);
v___x_917_ = lean_array_get_size(v_keyArray_890_);
v___x_918_ = lean_nat_dec_lt(v___x_916_, v___x_917_);
if (v___x_918_ == 0)
{
lean_dec(v___x_916_);
lean_dec(v_index_888_);
goto v___jp_901_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v___x_919_ = lean_unsigned_to_nat(4u);
v___x_920_ = lean_nat_mul(v___x_916_, v___x_919_);
v___x_921_ = lean_unsigned_to_nat(3u);
v___x_922_ = lean_nat_mul(v___x_917_, v___x_921_);
v___x_923_ = lean_nat_dec_le(v___x_920_, v___x_922_);
lean_dec(v___x_922_);
lean_dec(v___x_920_);
if (v___x_923_ == 0)
{
lean_dec(v___x_916_);
lean_dec(v_index_888_);
goto v___jp_901_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; 
lean_dec_ref(v_x_880_);
lean_dec_ref(v_x_879_);
v___x_924_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_881_, v___x_916_, v_index_888_, v_a_882_, v_b_883_);
lean_dec(v_index_888_);
v___x_925_ = lean_box(v___x_891_);
v___x_926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_925_);
lean_ctor_set(v___x_926_, 1, v___x_924_);
return v___x_926_;
}
}
v___jp_892_:
{
lean_object* v_size_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_size_895_ = lean_ctor_get(v___y_893_, 0);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_nat_add(v_size_895_, v___x_896_);
v___x_898_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_893_, v___x_897_, v_i_894_, v_a_882_, v_b_883_);
lean_dec(v_i_894_);
v___x_899_ = lean_box(v___x_891_);
v___x_900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
lean_ctor_set(v___x_900_, 1, v___x_898_);
return v___x_900_;
}
v___jp_901_:
{
lean_object* v___x_902_; lean_object* v___x_903_; 
lean_inc_ref(v_x_880_);
lean_inc_ref(v_x_879_);
v___x_902_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_879_, v_x_880_, v_m_881_);
lean_inc(v_a_882_);
v___x_903_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_879_, v_x_880_, v___x_902_, v_a_882_);
switch(lean_obj_tag(v___x_903_))
{
case 0:
{
lean_object* v_index_904_; lean_object* v_size_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; 
v_index_904_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_index_904_);
lean_dec_ref_known(v___x_903_, 3);
v_size_905_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_size_905_);
v___x_906_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_902_, v_size_905_, v_index_904_, v_a_882_, v_b_883_);
lean_dec(v_index_904_);
v___x_907_ = lean_box(v___x_891_);
v___x_908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v___x_906_);
return v___x_908_;
}
case 1:
{
lean_object* v_index_909_; 
v_index_909_ = lean_ctor_get(v___x_903_, 0);
lean_inc(v_index_909_);
lean_dec_ref_known(v___x_903_, 1);
v___y_893_ = v___x_902_;
v_i_894_ = v_index_909_;
goto v___jp_892_;
}
default: 
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_unsigned_to_nat(0u);
v___x_911_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_902_, v___x_910_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_index_912_; 
v_index_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_index_912_);
lean_dec_ref_known(v___x_911_, 1);
v___y_893_ = v___x_902_;
v_i_894_ = v_index_912_;
goto v___jp_892_;
}
else
{
lean_object* v___x_913_; lean_object* v___x_914_; 
lean_dec(v_b_883_);
lean_dec(v_a_882_);
v___x_913_ = lean_box(v___x_891_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_902_);
return v___x_914_;
}
}
}
}
}
default: 
{
lean_object* v_size_927_; lean_object* v_keyArray_928_; uint8_t v___x_929_; lean_object* v___y_931_; lean_object* v_i_932_; lean_object* v___y_940_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_size_927_ = lean_ctor_get(v_m_881_, 0);
v_keyArray_928_ = lean_ctor_get(v_m_881_, 1);
v___x_929_ = 0;
v___x_953_ = lean_unsigned_to_nat(1u);
v___x_954_ = lean_nat_add(v_size_927_, v___x_953_);
v___x_955_ = lean_array_get_size(v_keyArray_928_);
v___x_956_ = lean_nat_dec_lt(v___x_954_, v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
lean_dec(v___x_954_);
lean_inc_ref(v_x_880_);
lean_inc_ref(v_x_879_);
v___x_957_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_879_, v_x_880_, v_m_881_);
v___y_940_ = v___x_957_;
goto v___jp_939_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v___x_958_ = lean_unsigned_to_nat(4u);
v___x_959_ = lean_nat_mul(v___x_954_, v___x_958_);
lean_dec(v___x_954_);
v___x_960_ = lean_unsigned_to_nat(3u);
v___x_961_ = lean_nat_mul(v___x_955_, v___x_960_);
v___x_962_ = lean_nat_dec_le(v___x_959_, v___x_961_);
lean_dec(v___x_961_);
lean_dec(v___x_959_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_inc_ref(v_x_880_);
lean_inc_ref(v_x_879_);
v___x_963_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_879_, v_x_880_, v_m_881_);
v___y_940_ = v___x_963_;
goto v___jp_939_;
}
else
{
v___y_940_ = v_m_881_;
goto v___jp_939_;
}
}
v___jp_930_:
{
lean_object* v_size_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v_size_933_ = lean_ctor_get(v___y_931_, 0);
v___x_934_ = lean_unsigned_to_nat(1u);
v___x_935_ = lean_nat_add(v_size_933_, v___x_934_);
v___x_936_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_931_, v___x_935_, v_i_932_, v_a_882_, v_b_883_);
lean_dec(v_i_932_);
v___x_937_ = lean_box(v___x_929_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
return v___x_938_;
}
v___jp_939_:
{
lean_object* v___x_941_; 
lean_inc(v_a_882_);
v___x_941_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_879_, v_x_880_, v___y_940_, v_a_882_);
switch(lean_obj_tag(v___x_941_))
{
case 0:
{
lean_object* v_index_942_; lean_object* v_size_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_index_942_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_index_942_);
lean_dec_ref_known(v___x_941_, 3);
v_size_943_ = lean_ctor_get(v___y_940_, 0);
lean_inc(v_size_943_);
v___x_944_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_940_, v_size_943_, v_index_942_, v_a_882_, v_b_883_);
lean_dec(v_index_942_);
v___x_945_ = lean_box(v___x_929_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
return v___x_946_;
}
case 1:
{
lean_object* v_index_947_; 
v_index_947_ = lean_ctor_get(v___x_941_, 0);
lean_inc(v_index_947_);
lean_dec_ref_known(v___x_941_, 1);
v___y_931_ = v___y_940_;
v_i_932_ = v_index_947_;
goto v___jp_930_;
}
default: 
{
lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_948_ = lean_unsigned_to_nat(0u);
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_940_, v___x_948_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_index_950_; 
v_index_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_index_950_);
lean_dec_ref_known(v___x_949_, 1);
v___y_931_ = v___y_940_;
v_i_932_ = v_index_950_;
goto v___jp_930_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec(v_b_883_);
lean_dec(v_a_882_);
v___x_951_ = lean_box(v___x_929_);
v___x_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_951_);
lean_ctor_set(v___x_952_, 1, v___y_940_);
return v___x_952_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f___redArg(lean_object* v_x_964_, lean_object* v_x_965_, lean_object* v_m_966_, lean_object* v_a_967_, lean_object* v_b_968_){
_start:
{
lean_object* v___x_969_; 
lean_inc(v_a_967_);
lean_inc_ref(v_x_965_);
lean_inc_ref(v_x_964_);
v___x_969_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_964_, v_x_965_, v_m_966_, v_a_967_);
switch(lean_obj_tag(v___x_969_))
{
case 0:
{
lean_object* v_value_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
lean_dec(v_b_968_);
lean_dec(v_a_967_);
lean_dec_ref(v_x_965_);
lean_dec_ref(v_x_964_);
v_value_970_ = lean_ctor_get(v___x_969_, 2);
lean_inc(v_value_970_);
lean_dec_ref_known(v___x_969_, 3);
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v_value_970_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v_m_966_);
return v___x_972_;
}
case 1:
{
lean_object* v_index_973_; lean_object* v_size_974_; lean_object* v_keyArray_975_; lean_object* v___x_976_; lean_object* v___y_978_; lean_object* v_i_979_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v_index_973_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_index_973_);
lean_dec_ref_known(v___x_969_, 1);
v_size_974_ = lean_ctor_get(v_m_966_, 0);
v_keyArray_975_ = lean_ctor_get(v_m_966_, 1);
v___x_976_ = lean_box(0);
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_size_974_, v___x_997_);
v___x_999_ = lean_array_get_size(v_keyArray_975_);
v___x_1000_ = lean_nat_dec_lt(v___x_998_, v___x_999_);
if (v___x_1000_ == 0)
{
lean_dec(v___x_998_);
lean_dec(v_index_973_);
goto v___jp_985_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1001_ = lean_unsigned_to_nat(4u);
v___x_1002_ = lean_nat_mul(v___x_998_, v___x_1001_);
v___x_1003_ = lean_unsigned_to_nat(3u);
v___x_1004_ = lean_nat_mul(v___x_999_, v___x_1003_);
v___x_1005_ = lean_nat_dec_le(v___x_1002_, v___x_1004_);
lean_dec(v___x_1004_);
lean_dec(v___x_1002_);
if (v___x_1005_ == 0)
{
lean_dec(v___x_998_);
lean_dec(v_index_973_);
goto v___jp_985_;
}
else
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
lean_dec_ref(v_x_965_);
lean_dec_ref(v_x_964_);
v___x_1006_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_966_, v___x_998_, v_index_973_, v_a_967_, v_b_968_);
lean_dec(v_index_973_);
v___x_1007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_976_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
return v___x_1007_;
}
}
v___jp_977_:
{
lean_object* v_size_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v_size_980_ = lean_ctor_get(v___y_978_, 0);
v___x_981_ = lean_unsigned_to_nat(1u);
v___x_982_ = lean_nat_add(v_size_980_, v___x_981_);
v___x_983_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_978_, v___x_982_, v_i_979_, v_a_967_, v_b_968_);
lean_dec(v_i_979_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_976_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
return v___x_984_;
}
v___jp_985_:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
lean_inc_ref(v_x_965_);
lean_inc_ref(v_x_964_);
v___x_986_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_964_, v_x_965_, v_m_966_);
lean_inc(v_a_967_);
v___x_987_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_964_, v_x_965_, v___x_986_, v_a_967_);
switch(lean_obj_tag(v___x_987_))
{
case 0:
{
lean_object* v_index_988_; lean_object* v_size_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_index_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_index_988_);
lean_dec_ref_known(v___x_987_, 3);
v_size_989_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_size_989_);
v___x_990_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_986_, v_size_989_, v_index_988_, v_a_967_, v_b_968_);
lean_dec(v_index_988_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_976_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
return v___x_991_;
}
case 1:
{
lean_object* v_index_992_; 
v_index_992_ = lean_ctor_get(v___x_987_, 0);
lean_inc(v_index_992_);
lean_dec_ref_known(v___x_987_, 1);
v___y_978_ = v___x_986_;
v_i_979_ = v_index_992_;
goto v___jp_977_;
}
default: 
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_unsigned_to_nat(0u);
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_986_, v___x_993_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_index_995_; 
v_index_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_index_995_);
lean_dec_ref_known(v___x_994_, 1);
v___y_978_ = v___x_986_;
v_i_979_ = v_index_995_;
goto v___jp_977_;
}
else
{
lean_object* v___x_996_; 
lean_dec(v_b_968_);
lean_dec(v_a_967_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_976_);
lean_ctor_set(v___x_996_, 1, v___x_986_);
return v___x_996_;
}
}
}
}
}
default: 
{
lean_object* v_size_1008_; lean_object* v_keyArray_1009_; lean_object* v___x_1010_; lean_object* v___y_1012_; lean_object* v_i_1013_; lean_object* v___y_1020_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v_size_1008_ = lean_ctor_get(v_m_966_, 0);
v_keyArray_1009_ = lean_ctor_get(v_m_966_, 1);
v___x_1010_ = lean_box(0);
v___x_1031_ = lean_unsigned_to_nat(1u);
v___x_1032_ = lean_nat_add(v_size_1008_, v___x_1031_);
v___x_1033_ = lean_array_get_size(v_keyArray_1009_);
v___x_1034_ = lean_nat_dec_lt(v___x_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_dec(v___x_1032_);
lean_inc_ref(v_x_965_);
lean_inc_ref(v_x_964_);
v___x_1035_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_964_, v_x_965_, v_m_966_);
v___y_1020_ = v___x_1035_;
goto v___jp_1019_;
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; uint8_t v___x_1040_; 
v___x_1036_ = lean_unsigned_to_nat(4u);
v___x_1037_ = lean_nat_mul(v___x_1032_, v___x_1036_);
lean_dec(v___x_1032_);
v___x_1038_ = lean_unsigned_to_nat(3u);
v___x_1039_ = lean_nat_mul(v___x_1033_, v___x_1038_);
v___x_1040_ = lean_nat_dec_le(v___x_1037_, v___x_1039_);
lean_dec(v___x_1039_);
lean_dec(v___x_1037_);
if (v___x_1040_ == 0)
{
lean_object* v___x_1041_; 
lean_inc_ref(v_x_965_);
lean_inc_ref(v_x_964_);
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_964_, v_x_965_, v_m_966_);
v___y_1020_ = v___x_1041_;
goto v___jp_1019_;
}
else
{
v___y_1020_ = v_m_966_;
goto v___jp_1019_;
}
}
v___jp_1011_:
{
lean_object* v_size_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_size_1014_ = lean_ctor_get(v___y_1012_, 0);
v___x_1015_ = lean_unsigned_to_nat(1u);
v___x_1016_ = lean_nat_add(v_size_1014_, v___x_1015_);
v___x_1017_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1012_, v___x_1016_, v_i_1013_, v_a_967_, v_b_968_);
lean_dec(v_i_1013_);
v___x_1018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1010_);
lean_ctor_set(v___x_1018_, 1, v___x_1017_);
return v___x_1018_;
}
v___jp_1019_:
{
lean_object* v___x_1021_; 
lean_inc(v_a_967_);
v___x_1021_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_964_, v_x_965_, v___y_1020_, v_a_967_);
switch(lean_obj_tag(v___x_1021_))
{
case 0:
{
lean_object* v_index_1022_; lean_object* v_size_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v_index_1022_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_index_1022_);
lean_dec_ref_known(v___x_1021_, 3);
v_size_1023_ = lean_ctor_get(v___y_1020_, 0);
lean_inc(v_size_1023_);
v___x_1024_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1020_, v_size_1023_, v_index_1022_, v_a_967_, v_b_968_);
lean_dec(v_index_1022_);
v___x_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1025_, 0, v___x_1010_);
lean_ctor_set(v___x_1025_, 1, v___x_1024_);
return v___x_1025_;
}
case 1:
{
lean_object* v_index_1026_; 
v_index_1026_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_index_1026_);
lean_dec_ref_known(v___x_1021_, 1);
v___y_1012_ = v___y_1020_;
v_i_1013_ = v_index_1026_;
goto v___jp_1011_;
}
default: 
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1020_, v___x_1027_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_index_1029_; 
v_index_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_index_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v___y_1012_ = v___y_1020_;
v_i_1013_ = v_index_1029_;
goto v___jp_1011_;
}
else
{
lean_object* v___x_1030_; 
lean_dec(v_b_968_);
lean_dec(v_a_967_);
v___x_1030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1010_);
lean_ctor_set(v___x_1030_, 1, v___y_1020_);
return v___x_1030_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1042_, lean_object* v_00_u03b2_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_m_1046_, lean_object* v_a_1047_, lean_object* v_b_1048_){
_start:
{
lean_object* v___x_1049_; 
lean_inc(v_a_1047_);
lean_inc_ref(v_x_1045_);
lean_inc_ref(v_x_1044_);
v___x_1049_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1044_, v_x_1045_, v_m_1046_, v_a_1047_);
switch(lean_obj_tag(v___x_1049_))
{
case 0:
{
lean_object* v_value_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec(v_b_1048_);
lean_dec(v_a_1047_);
lean_dec_ref(v_x_1045_);
lean_dec_ref(v_x_1044_);
v_value_1050_ = lean_ctor_get(v___x_1049_, 2);
lean_inc(v_value_1050_);
lean_dec_ref_known(v___x_1049_, 3);
v___x_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1051_, 0, v_value_1050_);
v___x_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
lean_ctor_set(v___x_1052_, 1, v_m_1046_);
return v___x_1052_;
}
case 1:
{
lean_object* v_index_1053_; lean_object* v_size_1054_; lean_object* v_keyArray_1055_; lean_object* v___x_1056_; lean_object* v___y_1058_; lean_object* v_i_1059_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_index_1053_ = lean_ctor_get(v___x_1049_, 0);
lean_inc(v_index_1053_);
lean_dec_ref_known(v___x_1049_, 1);
v_size_1054_ = lean_ctor_get(v_m_1046_, 0);
v_keyArray_1055_ = lean_ctor_get(v_m_1046_, 1);
v___x_1056_ = lean_box(0);
v___x_1077_ = lean_unsigned_to_nat(1u);
v___x_1078_ = lean_nat_add(v_size_1054_, v___x_1077_);
v___x_1079_ = lean_array_get_size(v_keyArray_1055_);
v___x_1080_ = lean_nat_dec_lt(v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec(v___x_1078_);
lean_dec(v_index_1053_);
goto v___jp_1065_;
}
else
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; uint8_t v___x_1085_; 
v___x_1081_ = lean_unsigned_to_nat(4u);
v___x_1082_ = lean_nat_mul(v___x_1078_, v___x_1081_);
v___x_1083_ = lean_unsigned_to_nat(3u);
v___x_1084_ = lean_nat_mul(v___x_1079_, v___x_1083_);
v___x_1085_ = lean_nat_dec_le(v___x_1082_, v___x_1084_);
lean_dec(v___x_1084_);
lean_dec(v___x_1082_);
if (v___x_1085_ == 0)
{
lean_dec(v___x_1078_);
lean_dec(v_index_1053_);
goto v___jp_1065_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec_ref(v_x_1045_);
lean_dec_ref(v_x_1044_);
v___x_1086_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1046_, v___x_1078_, v_index_1053_, v_a_1047_, v_b_1048_);
lean_dec(v_index_1053_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1056_);
lean_ctor_set(v___x_1087_, 1, v___x_1086_);
return v___x_1087_;
}
}
v___jp_1057_:
{
lean_object* v_size_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_size_1060_ = lean_ctor_get(v___y_1058_, 0);
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_add(v_size_1060_, v___x_1061_);
v___x_1063_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1058_, v___x_1062_, v_i_1059_, v_a_1047_, v_b_1048_);
lean_dec(v_i_1059_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1056_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
return v___x_1064_;
}
v___jp_1065_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_inc_ref(v_x_1045_);
lean_inc_ref(v_x_1044_);
v___x_1066_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1044_, v_x_1045_, v_m_1046_);
lean_inc(v_a_1047_);
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1044_, v_x_1045_, v___x_1066_, v_a_1047_);
switch(lean_obj_tag(v___x_1067_))
{
case 0:
{
lean_object* v_index_1068_; lean_object* v_size_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_index_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1068_);
lean_dec_ref_known(v___x_1067_, 3);
v_size_1069_ = lean_ctor_get(v___x_1066_, 0);
lean_inc(v_size_1069_);
v___x_1070_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1066_, v_size_1069_, v_index_1068_, v_a_1047_, v_b_1048_);
lean_dec(v_index_1068_);
v___x_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1056_);
lean_ctor_set(v___x_1071_, 1, v___x_1070_);
return v___x_1071_;
}
case 1:
{
lean_object* v_index_1072_; 
v_index_1072_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1072_);
lean_dec_ref_known(v___x_1067_, 1);
v___y_1058_ = v___x_1066_;
v_i_1059_ = v_index_1072_;
goto v___jp_1057_;
}
default: 
{
lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1073_ = lean_unsigned_to_nat(0u);
v___x_1074_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1066_, v___x_1073_);
if (lean_obj_tag(v___x_1074_) == 0)
{
lean_object* v_index_1075_; 
v_index_1075_ = lean_ctor_get(v___x_1074_, 0);
lean_inc(v_index_1075_);
lean_dec_ref_known(v___x_1074_, 1);
v___y_1058_ = v___x_1066_;
v_i_1059_ = v_index_1075_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1076_; 
lean_dec(v_b_1048_);
lean_dec(v_a_1047_);
v___x_1076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1056_);
lean_ctor_set(v___x_1076_, 1, v___x_1066_);
return v___x_1076_;
}
}
}
}
}
default: 
{
lean_object* v_size_1088_; lean_object* v_keyArray_1089_; lean_object* v___x_1090_; lean_object* v___y_1092_; lean_object* v_i_1093_; lean_object* v___y_1100_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_size_1088_ = lean_ctor_get(v_m_1046_, 0);
v_keyArray_1089_ = lean_ctor_get(v_m_1046_, 1);
v___x_1090_ = lean_box(0);
v___x_1111_ = lean_unsigned_to_nat(1u);
v___x_1112_ = lean_nat_add(v_size_1088_, v___x_1111_);
v___x_1113_ = lean_array_get_size(v_keyArray_1089_);
v___x_1114_ = lean_nat_dec_lt(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec(v___x_1112_);
lean_inc_ref(v_x_1045_);
lean_inc_ref(v_x_1044_);
v___x_1115_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1044_, v_x_1045_, v_m_1046_);
v___y_1100_ = v___x_1115_;
goto v___jp_1099_;
}
else
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v___x_1116_ = lean_unsigned_to_nat(4u);
v___x_1117_ = lean_nat_mul(v___x_1112_, v___x_1116_);
lean_dec(v___x_1112_);
v___x_1118_ = lean_unsigned_to_nat(3u);
v___x_1119_ = lean_nat_mul(v___x_1113_, v___x_1118_);
v___x_1120_ = lean_nat_dec_le(v___x_1117_, v___x_1119_);
lean_dec(v___x_1119_);
lean_dec(v___x_1117_);
if (v___x_1120_ == 0)
{
lean_object* v___x_1121_; 
lean_inc_ref(v_x_1045_);
lean_inc_ref(v_x_1044_);
v___x_1121_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1044_, v_x_1045_, v_m_1046_);
v___y_1100_ = v___x_1121_;
goto v___jp_1099_;
}
else
{
v___y_1100_ = v_m_1046_;
goto v___jp_1099_;
}
}
v___jp_1091_:
{
lean_object* v_size_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_size_1094_ = lean_ctor_get(v___y_1092_, 0);
v___x_1095_ = lean_unsigned_to_nat(1u);
v___x_1096_ = lean_nat_add(v_size_1094_, v___x_1095_);
v___x_1097_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1092_, v___x_1096_, v_i_1093_, v_a_1047_, v_b_1048_);
lean_dec(v_i_1093_);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1090_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
return v___x_1098_;
}
v___jp_1099_:
{
lean_object* v___x_1101_; 
lean_inc(v_a_1047_);
v___x_1101_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1044_, v_x_1045_, v___y_1100_, v_a_1047_);
switch(lean_obj_tag(v___x_1101_))
{
case 0:
{
lean_object* v_index_1102_; lean_object* v_size_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v_index_1102_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_index_1102_);
lean_dec_ref_known(v___x_1101_, 3);
v_size_1103_ = lean_ctor_get(v___y_1100_, 0);
lean_inc(v_size_1103_);
v___x_1104_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1100_, v_size_1103_, v_index_1102_, v_a_1047_, v_b_1048_);
lean_dec(v_index_1102_);
v___x_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1105_, 0, v___x_1090_);
lean_ctor_set(v___x_1105_, 1, v___x_1104_);
return v___x_1105_;
}
case 1:
{
lean_object* v_index_1106_; 
v_index_1106_ = lean_ctor_get(v___x_1101_, 0);
lean_inc(v_index_1106_);
lean_dec_ref_known(v___x_1101_, 1);
v___y_1092_ = v___y_1100_;
v_i_1093_ = v_index_1106_;
goto v___jp_1091_;
}
default: 
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = lean_unsigned_to_nat(0u);
v___x_1108_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1100_, v___x_1107_);
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_index_1109_; 
v_index_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_index_1109_);
lean_dec_ref_known(v___x_1108_, 1);
v___y_1092_ = v___y_1100_;
v_i_1093_ = v_index_1109_;
goto v___jp_1091_;
}
else
{
lean_object* v___x_1110_; 
lean_dec(v_b_1048_);
lean_dec(v_a_1047_);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1090_);
lean_ctor_set(v___x_1110_, 1, v___y_1100_);
return v___x_1110_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg(lean_object* v_x_1122_, lean_object* v_x_1123_, lean_object* v_m_1124_, lean_object* v_a_1125_){
_start:
{
lean_object* v___x_1126_; 
v___x_1126_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1122_, v_x_1123_, v_m_1124_, v_a_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___redArg___boxed(lean_object* v_x_1127_, lean_object* v_x_1128_, lean_object* v_m_1129_, lean_object* v_a_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_Std_HashMap_get_x3f___redArg(v_x_1127_, v_x_1128_, v_m_1129_, v_a_1130_);
lean_dec_ref(v_m_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f(lean_object* v_00_u03b1_1132_, lean_object* v_00_u03b2_1133_, lean_object* v_x_1134_, lean_object* v_x_1135_, lean_object* v_m_1136_, lean_object* v_a_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1134_, v_x_1135_, v_m_1136_, v_a_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x3f___boxed(lean_object* v_00_u03b1_1139_, lean_object* v_00_u03b2_1140_, lean_object* v_x_1141_, lean_object* v_x_1142_, lean_object* v_m_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v_res_1145_; 
v_res_1145_ = l_Std_HashMap_get_x3f(v_00_u03b1_1139_, v_00_u03b2_1140_, v_x_1141_, v_x_1142_, v_m_1143_, v_a_1144_);
lean_dec_ref(v_m_1143_);
return v_res_1145_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_contains___redArg(lean_object* v_x_1146_, lean_object* v_x_1147_, lean_object* v_m_1148_, lean_object* v_a_1149_){
_start:
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1146_, v_x_1147_, v_m_1148_, v_a_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___redArg___boxed(lean_object* v_x_1151_, lean_object* v_x_1152_, lean_object* v_m_1153_, lean_object* v_a_1154_){
_start:
{
uint8_t v_res_1155_; lean_object* v_r_1156_; 
v_res_1155_ = l_Std_HashMap_contains___redArg(v_x_1151_, v_x_1152_, v_m_1153_, v_a_1154_);
lean_dec_ref(v_m_1153_);
v_r_1156_ = lean_box(v_res_1155_);
return v_r_1156_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_contains(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_x_1159_, lean_object* v_x_1160_, lean_object* v_m_1161_, lean_object* v_a_1162_){
_start:
{
uint8_t v___x_1163_; 
v___x_1163_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_1159_, v_x_1160_, v_m_1161_, v_a_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_contains___boxed(lean_object* v_00_u03b1_1164_, lean_object* v_00_u03b2_1165_, lean_object* v_x_1166_, lean_object* v_x_1167_, lean_object* v_m_1168_, lean_object* v_a_1169_){
_start:
{
uint8_t v_res_1170_; lean_object* v_r_1171_; 
v_res_1170_ = l_Std_HashMap_contains(v_00_u03b1_1164_, v_00_u03b2_1165_, v_x_1166_, v_x_1167_, v_m_1168_, v_a_1169_);
lean_dec_ref(v_m_1168_);
v_r_1171_ = lean_box(v_res_1170_);
return v_r_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership(lean_object* v_00_u03b1_1172_, lean_object* v_00_u03b2_1173_, lean_object* v_inst_1174_, lean_object* v_inst_1175_){
_start:
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_box(0);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instMembership___boxed(lean_object* v_00_u03b1_1177_, lean_object* v_00_u03b2_1178_, lean_object* v_inst_1179_, lean_object* v_inst_1180_){
_start:
{
lean_object* v_res_1181_; 
v_res_1181_ = l_Std_HashMap_instMembership(v_00_u03b1_1177_, v_00_u03b2_1178_, v_inst_1179_, v_inst_1180_);
lean_dec_ref(v_inst_1180_);
lean_dec_ref(v_inst_1179_);
return v_res_1181_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem___redArg(lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_m_1184_, lean_object* v_a_1185_){
_start:
{
uint8_t v___x_1186_; 
v___x_1186_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1182_, v_inst_1183_, v_m_1184_, v_a_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___redArg___boxed(lean_object* v_inst_1187_, lean_object* v_inst_1188_, lean_object* v_m_1189_, lean_object* v_a_1190_){
_start:
{
uint8_t v_res_1191_; lean_object* v_r_1192_; 
v_res_1191_ = l_Std_HashMap_instDecidableMem___redArg(v_inst_1187_, v_inst_1188_, v_m_1189_, v_a_1190_);
lean_dec_ref(v_m_1189_);
v_r_1192_ = lean_box(v_res_1191_);
return v_r_1192_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_instDecidableMem(lean_object* v_00_u03b1_1193_, lean_object* v_00_u03b2_1194_, lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_m_1197_, lean_object* v_a_1198_){
_start:
{
uint8_t v___x_1199_; 
v___x_1199_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1195_, v_inst_1196_, v_m_1197_, v_a_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instDecidableMem___boxed(lean_object* v_00_u03b1_1200_, lean_object* v_00_u03b2_1201_, lean_object* v_inst_1202_, lean_object* v_inst_1203_, lean_object* v_m_1204_, lean_object* v_a_1205_){
_start:
{
uint8_t v_res_1206_; lean_object* v_r_1207_; 
v_res_1206_ = l_Std_HashMap_instDecidableMem(v_00_u03b1_1200_, v_00_u03b2_1201_, v_inst_1202_, v_inst_1203_, v_m_1204_, v_a_1205_);
lean_dec_ref(v_m_1204_);
v_r_1207_ = lean_box(v_res_1206_);
return v_r_1207_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg(lean_object* v_x_1208_, lean_object* v_x_1209_, lean_object* v_m_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v_val_1213_; 
v___x_1212_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1208_, v_x_1209_, v_m_1210_, v_a_1211_);
v_val_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_val_1213_);
lean_dec(v___x_1212_);
return v_val_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___redArg___boxed(lean_object* v_x_1214_, lean_object* v_x_1215_, lean_object* v_m_1216_, lean_object* v_a_1217_){
_start:
{
lean_object* v_res_1218_; 
v_res_1218_ = l_Std_HashMap_get___redArg(v_x_1214_, v_x_1215_, v_m_1216_, v_a_1217_);
lean_dec_ref(v_m_1216_);
return v_res_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_x_1221_, lean_object* v_x_1222_, lean_object* v_m_1223_, lean_object* v_a_1224_, lean_object* v_h_1225_){
_start:
{
lean_object* v___x_1226_; lean_object* v_val_1227_; 
v___x_1226_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_x_1221_, v_x_1222_, v_m_1223_, v_a_1224_);
v_val_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_val_1227_);
lean_dec(v___x_1226_);
return v_val_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_x_1230_, lean_object* v_x_1231_, lean_object* v_m_1232_, lean_object* v_a_1233_, lean_object* v_h_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_HashMap_get(v_00_u03b1_1228_, v_00_u03b2_1229_, v_x_1230_, v_x_1231_, v_m_1232_, v_a_1233_, v_h_1234_);
lean_dec_ref(v_m_1232_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg(lean_object* v_x_1236_, lean_object* v_x_1237_, lean_object* v_m_1238_, lean_object* v_a_1239_, lean_object* v_fallback_1240_){
_start:
{
lean_object* v___x_1241_; 
v___x_1241_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_1236_, v_x_1237_, v_m_1238_, v_a_1239_, v_fallback_1240_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___redArg___boxed(lean_object* v_x_1242_, lean_object* v_x_1243_, lean_object* v_m_1244_, lean_object* v_a_1245_, lean_object* v_fallback_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l_Std_HashMap_getD___redArg(v_x_1242_, v_x_1243_, v_m_1244_, v_a_1245_, v_fallback_1246_);
lean_dec(v_fallback_1246_);
lean_dec_ref(v_m_1244_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD(lean_object* v_00_u03b1_1248_, lean_object* v_00_u03b2_1249_, lean_object* v_x_1250_, lean_object* v_x_1251_, lean_object* v_m_1252_, lean_object* v_a_1253_, lean_object* v_fallback_1254_){
_start:
{
lean_object* v___x_1255_; 
v___x_1255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_x_1250_, v_x_1251_, v_m_1252_, v_a_1253_, v_fallback_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getD___boxed(lean_object* v_00_u03b1_1256_, lean_object* v_00_u03b2_1257_, lean_object* v_x_1258_, lean_object* v_x_1259_, lean_object* v_m_1260_, lean_object* v_a_1261_, lean_object* v_fallback_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Std_HashMap_getD(v_00_u03b1_1256_, v_00_u03b2_1257_, v_x_1258_, v_x_1259_, v_m_1260_, v_a_1261_, v_fallback_1262_);
lean_dec(v_fallback_1262_);
lean_dec_ref(v_m_1260_);
return v_res_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg(lean_object* v_x_1264_, lean_object* v_x_1265_, lean_object* v_inst_1266_, lean_object* v_m_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_1264_, v_x_1265_, v_inst_1266_, v_m_1267_, v_a_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___redArg___boxed(lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_inst_1272_, lean_object* v_m_1273_, lean_object* v_a_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_Std_HashMap_get_x21___redArg(v_x_1270_, v_x_1271_, v_inst_1272_, v_m_1273_, v_a_1274_);
lean_dec_ref(v_m_1273_);
lean_dec(v_inst_1272_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21(lean_object* v_00_u03b1_1276_, lean_object* v_00_u03b2_1277_, lean_object* v_x_1278_, lean_object* v_x_1279_, lean_object* v_inst_1280_, lean_object* v_m_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_x_1278_, v_x_1279_, v_inst_1280_, v_m_1281_, v_a_1282_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_get_x21___boxed(lean_object* v_00_u03b1_1284_, lean_object* v_00_u03b2_1285_, lean_object* v_x_1286_, lean_object* v_x_1287_, lean_object* v_inst_1288_, lean_object* v_m_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Std_HashMap_get_x21(v_00_u03b1_1284_, v_00_u03b2_1285_, v_x_1286_, v_x_1287_, v_inst_1288_, v_m_1289_, v_a_1290_);
lean_dec_ref(v_m_1289_);
lean_dec(v_inst_1288_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_1292_, lean_object* v_inst_1293_, lean_object* v_m_1294_, lean_object* v_a_1295_, lean_object* v_h_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v_val_1298_; 
v___x_1297_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1292_, v_inst_1293_, v_m_1294_, v_a_1295_);
v_val_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_val_1298_);
lean_dec(v___x_1297_);
return v_val_1298_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_m_1301_, lean_object* v_a_1302_, lean_object* v_h_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0(v_inst_1299_, v_inst_1300_, v_m_1301_, v_a_1302_, v_h_1303_);
lean_dec_ref(v_m_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_m_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1305_, v_inst_1306_, v_m_1307_, v_a_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_1310_, lean_object* v_inst_1311_, lean_object* v_m_1312_, lean_object* v_a_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1(v_inst_1310_, v_inst_1311_, v_m_1312_, v_a_1313_);
lean_dec_ref(v_m_1312_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_m_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_1315_, v_inst_1316_, v_inst_1317_, v_m_1318_, v_a_1319_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_1321_, lean_object* v_inst_1322_, lean_object* v_inst_1323_, lean_object* v_m_1324_, lean_object* v_a_1325_){
_start:
{
lean_object* v_res_1326_; 
v_res_1326_ = l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2(v_inst_1321_, v_inst_1322_, v_inst_1323_, v_m_1324_, v_a_1325_);
lean_dec_ref(v_m_1324_);
lean_dec(v_inst_1323_);
return v_res_1326_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem___redArg(lean_object* v_inst_1327_, lean_object* v_inst_1328_){
_start:
{
lean_object* v___f_1329_; lean_object* v___f_1330_; lean_object* v___f_1331_; lean_object* v___x_1332_; 
lean_inc_ref_n(v_inst_1328_, 2);
lean_inc_ref_n(v_inst_1327_, 2);
v___f_1329_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1329_, 0, v_inst_1327_);
lean_closure_set(v___f_1329_, 1, v_inst_1328_);
v___f_1330_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1330_, 0, v_inst_1327_);
lean_closure_set(v___f_1330_, 1, v_inst_1328_);
v___f_1331_ = lean_alloc_closure((void*)(l_Std_HashMap_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_1331_, 0, v_inst_1327_);
lean_closure_set(v___f_1331_, 1, v_inst_1328_);
v___x_1332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1332_, 0, v___f_1329_);
lean_ctor_set(v___x_1332_, 1, v___f_1330_);
lean_ctor_set(v___x_1332_, 2, v___f_1331_);
return v___x_1332_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instGetElem_x3fMem(lean_object* v_00_u03b1_1333_, lean_object* v_00_u03b2_1334_, lean_object* v_inst_1335_, lean_object* v_inst_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_HashMap_instGetElem_x3fMem___redArg(v_inst_1335_, v_inst_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg(lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_m_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1338_, v_x_1339_, v_m_1340_, v_a_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___redArg___boxed(lean_object* v_x_1343_, lean_object* v_x_1344_, lean_object* v_m_1345_, lean_object* v_a_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_HashMap_getKey_x3f___redArg(v_x_1343_, v_x_1344_, v_m_1345_, v_a_1346_);
lean_dec_ref(v_m_1345_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f(lean_object* v_00_u03b1_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_, lean_object* v_m_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1350_, v_x_1351_, v_m_1352_, v_a_1353_);
return v___x_1354_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x3f___boxed(lean_object* v_00_u03b1_1355_, lean_object* v_00_u03b2_1356_, lean_object* v_x_1357_, lean_object* v_x_1358_, lean_object* v_m_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Std_HashMap_getKey_x3f(v_00_u03b1_1355_, v_00_u03b2_1356_, v_x_1357_, v_x_1358_, v_m_1359_, v_a_1360_);
lean_dec_ref(v_m_1359_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg(lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v_m_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v___x_1366_; lean_object* v_val_1367_; 
v___x_1366_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1362_, v_x_1363_, v_m_1364_, v_a_1365_);
v_val_1367_ = lean_ctor_get(v___x_1366_, 0);
lean_inc(v_val_1367_);
lean_dec(v___x_1366_);
return v_val_1367_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___redArg___boxed(lean_object* v_x_1368_, lean_object* v_x_1369_, lean_object* v_m_1370_, lean_object* v_a_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_Std_HashMap_getKey___redArg(v_x_1368_, v_x_1369_, v_m_1370_, v_a_1371_);
lean_dec_ref(v_m_1370_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey(lean_object* v_00_u03b1_1373_, lean_object* v_00_u03b2_1374_, lean_object* v_x_1375_, lean_object* v_x_1376_, lean_object* v_m_1377_, lean_object* v_a_1378_, lean_object* v_h_1379_){
_start:
{
lean_object* v___x_1380_; lean_object* v_val_1381_; 
v___x_1380_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_1375_, v_x_1376_, v_m_1377_, v_a_1378_);
v_val_1381_ = lean_ctor_get(v___x_1380_, 0);
lean_inc(v_val_1381_);
lean_dec(v___x_1380_);
return v_val_1381_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey___boxed(lean_object* v_00_u03b1_1382_, lean_object* v_00_u03b2_1383_, lean_object* v_x_1384_, lean_object* v_x_1385_, lean_object* v_m_1386_, lean_object* v_a_1387_, lean_object* v_h_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Std_HashMap_getKey(v_00_u03b1_1382_, v_00_u03b2_1383_, v_x_1384_, v_x_1385_, v_m_1386_, v_a_1387_, v_h_1388_);
lean_dec_ref(v_m_1386_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg(lean_object* v_x_1390_, lean_object* v_x_1391_, lean_object* v_m_1392_, lean_object* v_a_1393_, lean_object* v_fallback_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1390_, v_x_1391_, v_m_1392_, v_a_1393_, v_fallback_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___redArg___boxed(lean_object* v_x_1396_, lean_object* v_x_1397_, lean_object* v_m_1398_, lean_object* v_a_1399_, lean_object* v_fallback_1400_){
_start:
{
lean_object* v_res_1401_; 
v_res_1401_ = l_Std_HashMap_getKeyD___redArg(v_x_1396_, v_x_1397_, v_m_1398_, v_a_1399_, v_fallback_1400_);
lean_dec(v_fallback_1400_);
lean_dec_ref(v_m_1398_);
return v_res_1401_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD(lean_object* v_00_u03b1_1402_, lean_object* v_00_u03b2_1403_, lean_object* v_x_1404_, lean_object* v_x_1405_, lean_object* v_m_1406_, lean_object* v_a_1407_, lean_object* v_fallback_1408_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_x_1404_, v_x_1405_, v_m_1406_, v_a_1407_, v_fallback_1408_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKeyD___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_00_u03b2_1411_, lean_object* v_x_1412_, lean_object* v_x_1413_, lean_object* v_m_1414_, lean_object* v_a_1415_, lean_object* v_fallback_1416_){
_start:
{
lean_object* v_res_1417_; 
v_res_1417_ = l_Std_HashMap_getKeyD(v_00_u03b1_1410_, v_00_u03b2_1411_, v_x_1412_, v_x_1413_, v_m_1414_, v_a_1415_, v_fallback_1416_);
lean_dec(v_fallback_1416_);
lean_dec_ref(v_m_1414_);
return v_res_1417_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg(lean_object* v_x_1418_, lean_object* v_x_1419_, lean_object* v_inst_1420_, lean_object* v_m_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1418_, v_x_1419_, v_inst_1420_, v_m_1421_, v_a_1422_);
return v___x_1423_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___redArg___boxed(lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v_inst_1426_, lean_object* v_m_1427_, lean_object* v_a_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Std_HashMap_getKey_x21___redArg(v_x_1424_, v_x_1425_, v_inst_1426_, v_m_1427_, v_a_1428_);
lean_dec_ref(v_m_1427_);
lean_dec(v_inst_1426_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21(lean_object* v_00_u03b1_1430_, lean_object* v_00_u03b2_1431_, lean_object* v_x_1432_, lean_object* v_x_1433_, lean_object* v_inst_1434_, lean_object* v_m_1435_, lean_object* v_a_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_x_1432_, v_x_1433_, v_inst_1434_, v_m_1435_, v_a_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getKey_x21___boxed(lean_object* v_00_u03b1_1438_, lean_object* v_00_u03b2_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v_inst_1442_, lean_object* v_m_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Std_HashMap_getKey_x21(v_00_u03b1_1438_, v_00_u03b2_1439_, v_x_1440_, v_x_1441_, v_inst_1442_, v_m_1443_, v_a_1444_);
lean_dec_ref(v_m_1443_);
lean_dec(v_inst_1442_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase___redArg(lean_object* v_x_1446_, lean_object* v_x_1447_, lean_object* v_m_1448_, lean_object* v_a_1449_){
_start:
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_1446_, v_x_1447_, v_m_1448_, v_a_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_erase(lean_object* v_00_u03b1_1451_, lean_object* v_00_u03b2_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v_m_1455_, lean_object* v_a_1456_){
_start:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_1453_, v_x_1454_, v_m_1455_, v_a_1456_);
return v___x_1457_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg(lean_object* v_m_1458_){
_start:
{
lean_object* v_size_1459_; 
v_size_1459_ = lean_ctor_get(v_m_1458_, 0);
lean_inc(v_size_1459_);
return v_size_1459_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___redArg___boxed(lean_object* v_m_1460_){
_start:
{
lean_object* v_res_1461_; 
v_res_1461_ = l_Std_HashMap_size___redArg(v_m_1460_);
lean_dec_ref(v_m_1460_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size(lean_object* v_00_u03b1_1462_, lean_object* v_00_u03b2_1463_, lean_object* v_x_1464_, lean_object* v_x_1465_, lean_object* v_m_1466_){
_start:
{
lean_object* v_size_1467_; 
v_size_1467_ = lean_ctor_get(v_m_1466_, 0);
lean_inc(v_size_1467_);
return v_size_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_size___boxed(lean_object* v_00_u03b1_1468_, lean_object* v_00_u03b2_1469_, lean_object* v_x_1470_, lean_object* v_x_1471_, lean_object* v_m_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l_Std_HashMap_size(v_00_u03b1_1468_, v_00_u03b2_1469_, v_x_1470_, v_x_1471_, v_m_1472_);
lean_dec_ref(v_m_1472_);
lean_dec_ref(v_x_1471_);
lean_dec_ref(v_x_1470_);
return v_res_1473_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty___redArg(lean_object* v_m_1474_){
_start:
{
lean_object* v_size_1475_; lean_object* v___x_1476_; uint8_t v___x_1477_; 
v_size_1475_ = lean_ctor_get(v_m_1474_, 0);
v___x_1476_ = lean_unsigned_to_nat(0u);
v___x_1477_ = lean_nat_dec_eq(v_size_1475_, v___x_1476_);
return v___x_1477_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___redArg___boxed(lean_object* v_m_1478_){
_start:
{
uint8_t v_res_1479_; lean_object* v_r_1480_; 
v_res_1479_ = l_Std_HashMap_isEmpty___redArg(v_m_1478_);
lean_dec_ref(v_m_1478_);
v_r_1480_ = lean_box(v_res_1479_);
return v_r_1480_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_isEmpty(lean_object* v_00_u03b1_1481_, lean_object* v_00_u03b2_1482_, lean_object* v_x_1483_, lean_object* v_x_1484_, lean_object* v_m_1485_){
_start:
{
lean_object* v_size_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v_size_1486_ = lean_ctor_get(v_m_1485_, 0);
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = lean_nat_dec_eq(v_size_1486_, v___x_1487_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_isEmpty___boxed(lean_object* v_00_u03b1_1489_, lean_object* v_00_u03b2_1490_, lean_object* v_x_1491_, lean_object* v_x_1492_, lean_object* v_m_1493_){
_start:
{
uint8_t v_res_1494_; lean_object* v_r_1495_; 
v_res_1494_ = l_Std_HashMap_isEmpty(v_00_u03b1_1489_, v_00_u03b2_1490_, v_x_1491_, v_x_1492_, v_m_1493_);
lean_dec_ref(v_m_1493_);
lean_dec_ref(v_x_1492_);
lean_dec_ref(v_x_1491_);
v_r_1495_ = lean_box(v_res_1494_);
return v_r_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0(lean_object* v_x1_1496_, lean_object* v_x2_1497_, lean_object* v_x3_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1499_, 0, v_x2_1497_);
lean_ctor_set(v___x_1499_, 1, v_x1_1496_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___lam__0___boxed(lean_object* v_x1_1500_, lean_object* v_x2_1501_, lean_object* v_x3_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Std_HashMap_keys___redArg___lam__0(v_x1_1500_, v_x2_1501_, v_x3_1502_);
lean_dec(v_x3_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg(lean_object* v_m_1524_){
_start:
{
lean_object* v___f_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___f_1525_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__0));
v___x_1526_ = lean_box(0);
v___x_1527_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_1528_ = lean_unsigned_to_nat(0u);
v___x_1529_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_1527_, v___f_1525_, v_m_1524_, v___x_1526_, v___x_1528_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___redArg___boxed(lean_object* v_m_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Std_HashMap_keys___redArg(v_m_1530_);
lean_dec_ref(v_m_1530_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys(lean_object* v_00_u03b1_1532_, lean_object* v_00_u03b2_1533_, lean_object* v_x_1534_, lean_object* v_x_1535_, lean_object* v_m_1536_){
_start:
{
lean_object* v___f_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___f_1537_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__0));
v___x_1538_ = lean_box(0);
v___x_1539_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_1540_ = lean_unsigned_to_nat(0u);
v___x_1541_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_1539_, v___f_1537_, v_m_1536_, v___x_1538_, v___x_1540_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keys___boxed(lean_object* v_00_u03b1_1542_, lean_object* v_00_u03b2_1543_, lean_object* v_x_1544_, lean_object* v_x_1545_, lean_object* v_m_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Std_HashMap_keys(v_00_u03b1_1542_, v_00_u03b2_1543_, v_x_1544_, v_x_1545_, v_m_1546_);
lean_dec_ref(v_m_1546_);
lean_dec_ref(v_x_1545_);
lean_dec_ref(v_x_1544_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList___redArg(lean_object* v_inst_1552_, lean_object* v_inst_1553_, lean_object* v_l_1554_){
_start:
{
lean_object* v___f_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___f_1555_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1556_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__2, &l_Std_HashMap_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_instEmptyCollection___closed__2);
v___x_1557_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1555_, v_inst_1552_, v_inst_1553_, v___x_1556_, v_l_1554_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofList(lean_object* v_00_u03b1_1558_, lean_object* v_00_u03b2_1559_, lean_object* v_inst_1560_, lean_object* v_inst_1561_, lean_object* v_l_1562_){
_start:
{
lean_object* v___f_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___f_1563_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1564_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__2, &l_Std_HashMap_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_instEmptyCollection___closed__2);
v___x_1565_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1563_, v_inst_1560_, v_inst_1561_, v___x_1564_, v_l_1562_);
return v___x_1565_;
}
}
static lean_object* _init_l_Std_HashMap_unitOfList___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_1566_; lean_object* v___x_1567_; 
v_cellCount_1566_ = lean_unsigned_to_nat(16u);
v___x_1567_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1566_);
return v___x_1567_;
}
}
static lean_object* _init_l_Std_HashMap_unitOfList___redArg___closed__1(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1568_ = lean_obj_once(&l_Std_HashMap_unitOfList___redArg___closed__0, &l_Std_HashMap_unitOfList___redArg___closed__0_once, _init_l_Std_HashMap_unitOfList___redArg___closed__0);
v___x_1569_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__0, &l_Std_HashMap_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_instEmptyCollection___closed__0);
v___x_1570_ = lean_unsigned_to_nat(0u);
v___x_1571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1571_, 0, v___x_1570_);
lean_ctor_set(v___x_1571_, 1, v___x_1569_);
lean_ctor_set(v___x_1571_, 2, v___x_1568_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList___redArg(lean_object* v_inst_1572_, lean_object* v_inst_1573_, lean_object* v_l_1574_){
_start:
{
lean_object* v___f_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___f_1575_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1576_ = lean_obj_once(&l_Std_HashMap_unitOfList___redArg___closed__1, &l_Std_HashMap_unitOfList___redArg___closed__1_once, _init_l_Std_HashMap_unitOfList___redArg___closed__1);
v___x_1577_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1575_, v_inst_1572_, v_inst_1573_, v___x_1576_, v_l_1574_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfList(lean_object* v_00_u03b1_1578_, lean_object* v_inst_1579_, lean_object* v_inst_1580_, lean_object* v_l_1581_){
_start:
{
lean_object* v___f_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___f_1582_ = ((lean_object*)(l_Std_HashMap_ofList___redArg___closed__1));
v___x_1583_ = lean_obj_once(&l_Std_HashMap_unitOfList___redArg___closed__1, &l_Std_HashMap_unitOfList___redArg___closed__1_once, _init_l_Std_HashMap_unitOfList___redArg___closed__1);
v___x_1584_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1582_, v_inst_1579_, v_inst_1580_, v___x_1583_, v_l_1581_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray___redArg(lean_object* v_inst_1589_, lean_object* v_inst_1590_, lean_object* v_a_1591_){
_start:
{
lean_object* v___f_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___f_1592_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1593_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__2, &l_Std_HashMap_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_instEmptyCollection___closed__2);
v___x_1594_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1592_, v_inst_1589_, v_inst_1590_, v___x_1593_, v_a_1591_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_ofArray(lean_object* v_00_u03b1_1595_, lean_object* v_00_u03b2_1596_, lean_object* v_inst_1597_, lean_object* v_inst_1598_, lean_object* v_a_1599_){
_start:
{
lean_object* v___f_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___f_1600_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_1601_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__2, &l_Std_HashMap_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_instEmptyCollection___closed__2);
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1600_, v_inst_1597_, v_inst_1598_, v___x_1601_, v_a_1599_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___lam__0(lean_object* v_x1_1603_, lean_object* v_x2_1604_, lean_object* v_x3_1605_){
_start:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1606_, 0, v_x2_1604_);
lean_ctor_set(v___x_1606_, 1, v_x3_1605_);
v___x_1607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
lean_ctor_set(v___x_1607_, 1, v_x1_1603_);
return v___x_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg(lean_object* v_m_1609_){
_start:
{
lean_object* v___f_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___f_1610_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__0));
v___x_1611_ = lean_box(0);
v___x_1612_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_1613_ = lean_unsigned_to_nat(0u);
v___x_1614_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_1612_, v___f_1610_, v_m_1609_, v___x_1611_, v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___redArg___boxed(lean_object* v_m_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Std_HashMap_toList___redArg(v_m_1615_);
lean_dec_ref(v_m_1615_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList(lean_object* v_00_u03b1_1617_, lean_object* v_00_u03b2_1618_, lean_object* v_x_1619_, lean_object* v_x_1620_, lean_object* v_m_1621_){
_start:
{
lean_object* v___f_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___f_1622_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__0));
v___x_1623_ = lean_box(0);
v___x_1624_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_1624_, v___f_1622_, v_m_1621_, v___x_1623_, v___x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toList___boxed(lean_object* v_00_u03b1_1627_, lean_object* v_00_u03b2_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_m_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Std_HashMap_toList(v_00_u03b1_1627_, v_00_u03b2_1628_, v_x_1629_, v_x_1630_, v_m_1631_);
lean_dec_ref(v_m_1631_);
lean_dec_ref(v_x_1630_);
lean_dec_ref(v_x_1629_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___redArg(lean_object* v_inst_1633_, lean_object* v_f_1634_, lean_object* v_init_1635_, lean_object* v_b_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1633_, v_f_1634_, v_init_1635_, v_b_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM(lean_object* v_00_u03b1_1638_, lean_object* v_00_u03b2_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_, lean_object* v_m_1642_, lean_object* v_inst_1643_, lean_object* v_00_u03b3_1644_, lean_object* v_f_1645_, lean_object* v_init_1646_, lean_object* v_b_1647_){
_start:
{
lean_object* v___x_1648_; 
v___x_1648_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1643_, v_f_1645_, v_init_1646_, v_b_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_foldM___boxed(lean_object* v_00_u03b1_1649_, lean_object* v_00_u03b2_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_m_1653_, lean_object* v_inst_1654_, lean_object* v_00_u03b3_1655_, lean_object* v_f_1656_, lean_object* v_init_1657_, lean_object* v_b_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_HashMap_foldM(v_00_u03b1_1649_, v_00_u03b2_1650_, v_x_1651_, v_x_1652_, v_m_1653_, v_inst_1654_, v_00_u03b3_1655_, v_f_1656_, v_init_1657_, v_b_1658_);
lean_dec_ref(v_x_1652_);
lean_dec_ref(v_x_1651_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg___lam__0(lean_object* v_f_1660_, lean_object* v_x1_1661_, lean_object* v_x2_1662_, lean_object* v_x3_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_apply_3(v_f_1660_, v_x1_1661_, v_x2_1662_, v_x3_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___redArg(lean_object* v_f_1665_, lean_object* v_init_1666_, lean_object* v_b_1667_){
_start:
{
lean_object* v___f_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___f_1668_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1668_, 0, v_f_1665_);
v___x_1669_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_1670_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1669_, v___f_1668_, v_init_1666_, v_b_1667_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold(lean_object* v_00_u03b1_1671_, lean_object* v_00_u03b2_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_, lean_object* v_00_u03b3_1675_, lean_object* v_f_1676_, lean_object* v_init_1677_, lean_object* v_b_1678_){
_start:
{
lean_object* v___f_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___f_1679_ = lean_alloc_closure((void*)(l_Std_HashMap_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1679_, 0, v_f_1676_);
v___x_1680_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_1681_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1680_, v___f_1679_, v_init_1677_, v_b_1678_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fold___boxed(lean_object* v_00_u03b1_1682_, lean_object* v_00_u03b2_1683_, lean_object* v_x_1684_, lean_object* v_x_1685_, lean_object* v_00_u03b3_1686_, lean_object* v_f_1687_, lean_object* v_init_1688_, lean_object* v_b_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Std_HashMap_fold(v_00_u03b1_1682_, v_00_u03b2_1683_, v_x_1684_, v_x_1685_, v_00_u03b3_1686_, v_f_1687_, v_init_1688_, v_b_1689_);
lean_dec_ref(v_x_1685_);
lean_dec_ref(v_x_1684_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg___lam__0(lean_object* v_f_1691_, lean_object* v_x_1692_, lean_object* v_a_1693_, lean_object* v_v_1694_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_apply_2(v_f_1691_, v_a_1693_, v_v_1694_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___redArg(lean_object* v_inst_1696_, lean_object* v_f_1697_, lean_object* v_b_1698_){
_start:
{
lean_object* v___f_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___f_1699_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1699_, 0, v_f_1697_);
v___x_1700_ = lean_box(0);
v___x_1701_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1696_, v___f_1699_, v___x_1700_, v_b_1698_);
return v___x_1701_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM(lean_object* v_00_u03b1_1702_, lean_object* v_00_u03b2_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_, lean_object* v_m_1706_, lean_object* v_inst_1707_, lean_object* v_f_1708_, lean_object* v_b_1709_){
_start:
{
lean_object* v___f_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___f_1710_ = lean_alloc_closure((void*)(l_Std_HashMap_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1710_, 0, v_f_1708_);
v___x_1711_ = lean_box(0);
v___x_1712_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1707_, v___f_1710_, v___x_1711_, v_b_1709_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forM___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_00_u03b2_1714_, lean_object* v_x_1715_, lean_object* v_x_1716_, lean_object* v_m_1717_, lean_object* v_inst_1718_, lean_object* v_f_1719_, lean_object* v_b_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Std_HashMap_forM(v_00_u03b1_1713_, v_00_u03b2_1714_, v_x_1715_, v_x_1716_, v_m_1717_, v_inst_1718_, v_f_1719_, v_b_1720_);
lean_dec_ref(v_x_1716_);
lean_dec_ref(v_x_1715_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___redArg(lean_object* v_inst_1722_, lean_object* v_f_1723_, lean_object* v_init_1724_, lean_object* v_b_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_1722_, v_f_1723_, v_init_1724_, v_b_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn(lean_object* v_00_u03b1_1727_, lean_object* v_00_u03b2_1728_, lean_object* v_x_1729_, lean_object* v_x_1730_, lean_object* v_m_1731_, lean_object* v_inst_1732_, lean_object* v_00_u03b3_1733_, lean_object* v_f_1734_, lean_object* v_init_1735_, lean_object* v_b_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_1732_, v_f_1734_, v_init_1735_, v_b_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_forIn___boxed(lean_object* v_00_u03b1_1738_, lean_object* v_00_u03b2_1739_, lean_object* v_x_1740_, lean_object* v_x_1741_, lean_object* v_m_1742_, lean_object* v_inst_1743_, lean_object* v_00_u03b3_1744_, lean_object* v_f_1745_, lean_object* v_init_1746_, lean_object* v_b_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Std_HashMap_forIn(v_00_u03b1_1738_, v_00_u03b2_1739_, v_x_1740_, v_x_1741_, v_m_1742_, v_inst_1743_, v_00_u03b3_1744_, v_f_1745_, v_init_1746_, v_b_1747_);
lean_dec_ref(v_x_1741_);
lean_dec_ref(v_x_1740_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1749_, lean_object* v_x_1750_, lean_object* v_a_1751_, lean_object* v_v_1752_){
_start:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1753_, 0, v_a_1751_);
lean_ctor_set(v___x_1753_, 1, v_v_1752_);
v___x_1754_ = lean_apply_1(v_f_1749_, v___x_1753_);
return v___x_1754_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_1755_, lean_object* v_m_1756_, lean_object* v_f_1757_){
_start:
{
lean_object* v___f_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___f_1758_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1758_, 0, v_f_1757_);
v___x_1759_ = lean_box(0);
v___x_1760_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1755_, v___f_1758_, v___x_1759_, v_m_1756_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___redArg(lean_object* v_inst_1761_){
_start:
{
lean_object* v___f_1762_; 
v___f_1762_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1762_, 0, v_inst_1761_);
return v___f_1762_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad(lean_object* v_00_u03b1_1763_, lean_object* v_00_u03b2_1764_, lean_object* v_inst_1765_, lean_object* v_inst_1766_, lean_object* v_m_1767_, lean_object* v_inst_1768_){
_start:
{
lean_object* v___f_1769_; 
v___f_1769_ = lean_alloc_closure((void*)(l_Std_HashMap_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1769_, 0, v_inst_1768_);
return v___f_1769_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForMProdOfMonad___boxed(lean_object* v_00_u03b1_1770_, lean_object* v_00_u03b2_1771_, lean_object* v_inst_1772_, lean_object* v_inst_1773_, lean_object* v_m_1774_, lean_object* v_inst_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_HashMap_instForMProdOfMonad(v_00_u03b1_1770_, v_00_u03b2_1771_, v_inst_1772_, v_inst_1773_, v_m_1774_, v_inst_1775_);
lean_dec_ref(v_inst_1773_);
lean_dec_ref(v_inst_1772_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1777_, lean_object* v_a_1778_, lean_object* v_b_1779_, lean_object* v_acc_1780_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1781_, 0, v_a_1778_);
lean_ctor_set(v___x_1781_, 1, v_b_1779_);
v___x_1782_ = lean_apply_2(v_f_1777_, v___x_1781_, v_acc_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1783_, lean_object* v_00_u03b2_1784_, lean_object* v_m_1785_, lean_object* v_init_1786_, lean_object* v_f_1787_){
_start:
{
lean_object* v___f_1788_; lean_object* v___x_1789_; 
v___f_1788_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1788_, 0, v_f_1787_);
v___x_1789_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_1783_, v___f_1788_, v_init_1786_, v_m_1785_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___redArg(lean_object* v_inst_1790_){
_start:
{
lean_object* v___f_1791_; 
v___f_1791_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1791_, 0, v_inst_1790_);
return v___f_1791_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad(lean_object* v_00_u03b1_1792_, lean_object* v_00_u03b2_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_m_1796_, lean_object* v_inst_1797_){
_start:
{
lean_object* v___f_1798_; 
v___f_1798_ = lean_alloc_closure((void*)(l_Std_HashMap_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1798_, 0, v_inst_1797_);
return v___f_1798_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instForInProdOfMonad___boxed(lean_object* v_00_u03b1_1799_, lean_object* v_00_u03b2_1800_, lean_object* v_inst_1801_, lean_object* v_inst_1802_, lean_object* v_m_1803_, lean_object* v_inst_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Std_HashMap_instForInProdOfMonad(v_00_u03b1_1799_, v_00_u03b2_1800_, v_inst_1801_, v_inst_1802_, v_m_1803_, v_inst_1804_);
lean_dec_ref(v_inst_1802_);
lean_dec_ref(v_inst_1801_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___redArg(lean_object* v_f_1806_, lean_object* v_m_1807_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1806_, v_m_1807_);
return v___x_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___redArg___boxed(lean_object* v_f_1809_, lean_object* v_m_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Std_HashMap_filter___redArg(v_f_1809_, v_m_1810_);
lean_dec_ref(v_m_1810_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter(lean_object* v_00_u03b1_1812_, lean_object* v_00_u03b2_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_, lean_object* v_f_1816_, lean_object* v_m_1817_){
_start:
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_1816_, v_m_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_filter___boxed(lean_object* v_00_u03b1_1819_, lean_object* v_00_u03b2_1820_, lean_object* v_x_1821_, lean_object* v_x_1822_, lean_object* v_f_1823_, lean_object* v_m_1824_){
_start:
{
lean_object* v_res_1825_; 
v_res_1825_ = l_Std_HashMap_filter(v_00_u03b1_1819_, v_00_u03b2_1820_, v_x_1821_, v_x_1822_, v_f_1823_, v_m_1824_);
lean_dec_ref(v_m_1824_);
lean_dec_ref(v_x_1822_);
lean_dec_ref(v_x_1821_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify___redArg(lean_object* v_x_1826_, lean_object* v_x_1827_, lean_object* v_m_1828_, lean_object* v_a_1829_, lean_object* v_f_1830_){
_start:
{
lean_object* v___x_1831_; 
lean_inc(v_a_1829_);
v___x_1831_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1826_, v_x_1827_, v_m_1828_, v_a_1829_);
if (lean_obj_tag(v___x_1831_) == 0)
{
lean_object* v_index_1832_; lean_object* v_value_1833_; lean_object* v_size_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v_index_1832_ = lean_ctor_get(v___x_1831_, 0);
lean_inc(v_index_1832_);
v_value_1833_ = lean_ctor_get(v___x_1831_, 2);
lean_inc(v_value_1833_);
lean_dec_ref_known(v___x_1831_, 3);
v_size_1834_ = lean_ctor_get(v_m_1828_, 0);
lean_inc(v_size_1834_);
v___x_1835_ = lean_apply_1(v_f_1830_, v_value_1833_);
v___x_1836_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1828_, v_size_1834_, v_index_1832_, v_a_1829_, v___x_1835_);
lean_dec(v_index_1832_);
return v___x_1836_;
}
else
{
lean_dec(v___x_1831_);
lean_dec(v_f_1830_);
lean_dec(v_a_1829_);
return v_m_1828_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify(lean_object* v_00_u03b1_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_x_1839_, lean_object* v_x_1840_, lean_object* v_m_1841_, lean_object* v_a_1842_, lean_object* v_f_1843_){
_start:
{
lean_object* v___x_1844_; 
lean_inc(v_a_1842_);
v___x_1844_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1839_, v_x_1840_, v_m_1841_, v_a_1842_);
if (lean_obj_tag(v___x_1844_) == 0)
{
lean_object* v_index_1845_; lean_object* v_value_1846_; lean_object* v_size_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_index_1845_ = lean_ctor_get(v___x_1844_, 0);
lean_inc(v_index_1845_);
v_value_1846_ = lean_ctor_get(v___x_1844_, 2);
lean_inc(v_value_1846_);
lean_dec_ref_known(v___x_1844_, 3);
v_size_1847_ = lean_ctor_get(v_m_1841_, 0);
lean_inc(v_size_1847_);
v___x_1848_ = lean_apply_1(v_f_1843_, v_value_1846_);
v___x_1849_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1841_, v_size_1847_, v_index_1845_, v_a_1842_, v___x_1848_);
lean_dec(v_index_1845_);
return v___x_1849_;
}
else
{
lean_dec(v___x_1844_);
lean_dec(v_f_1843_);
lean_dec(v_a_1842_);
return v_m_1841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter___redArg(lean_object* v_x_1850_, lean_object* v_x_1851_, lean_object* v_m_1852_, lean_object* v_a_1853_, lean_object* v_f_1854_){
_start:
{
lean_object* v___x_1855_; 
lean_inc(v_a_1853_);
lean_inc_ref(v_x_1851_);
lean_inc_ref(v_x_1850_);
v___x_1855_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1850_, v_x_1851_, v_m_1852_, v_a_1853_);
switch(lean_obj_tag(v___x_1855_))
{
case 0:
{
lean_object* v_index_1856_; lean_object* v_value_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref(v_x_1851_);
lean_dec_ref(v_x_1850_);
v_index_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_index_1856_);
v_value_1857_ = lean_ctor_get(v___x_1855_, 2);
lean_inc(v_value_1857_);
lean_dec_ref_known(v___x_1855_, 3);
v___x_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1858_, 0, v_value_1857_);
v___x_1859_ = lean_apply_1(v_f_1854_, v___x_1858_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v_size_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
lean_dec(v_a_1853_);
v_size_1860_ = lean_ctor_get(v_m_1852_, 0);
v___x_1861_ = lean_unsigned_to_nat(1u);
v___x_1862_ = lean_nat_sub(v_size_1860_, v___x_1861_);
v___x_1863_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1852_, v___x_1862_, v_index_1856_);
lean_dec(v_index_1856_);
return v___x_1863_;
}
else
{
lean_object* v_val_1864_; lean_object* v_size_1865_; lean_object* v___x_1866_; 
v_val_1864_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v___x_1859_, 1);
v_size_1865_ = lean_ctor_get(v_m_1852_, 0);
lean_inc(v_size_1865_);
v___x_1866_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1852_, v_size_1865_, v_index_1856_, v_a_1853_, v_val_1864_);
lean_dec(v_index_1856_);
return v___x_1866_;
}
}
case 1:
{
lean_object* v_index_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v_index_1867_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_index_1867_);
lean_dec_ref_known(v___x_1855_, 1);
v___x_1868_ = lean_box(0);
v___x_1869_ = lean_apply_1(v_f_1854_, v___x_1868_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_dec(v_index_1867_);
lean_dec(v_a_1853_);
lean_dec_ref(v_x_1851_);
lean_dec_ref(v_x_1850_);
return v_m_1852_;
}
else
{
lean_object* v_val_1870_; lean_object* v___y_1872_; lean_object* v_i_1873_; lean_object* v_size_1888_; lean_object* v_keyArray_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v_val_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_val_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v_size_1888_ = lean_ctor_get(v_m_1852_, 0);
v_keyArray_1889_ = lean_ctor_get(v_m_1852_, 1);
v___x_1890_ = lean_unsigned_to_nat(1u);
v___x_1891_ = lean_nat_add(v_size_1888_, v___x_1890_);
v___x_1892_ = lean_array_get_size(v_keyArray_1889_);
v___x_1893_ = lean_nat_dec_lt(v___x_1891_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_dec(v___x_1891_);
lean_dec(v_index_1867_);
goto v___jp_1878_;
}
else
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1894_ = lean_unsigned_to_nat(4u);
v___x_1895_ = lean_nat_mul(v___x_1891_, v___x_1894_);
v___x_1896_ = lean_unsigned_to_nat(3u);
v___x_1897_ = lean_nat_mul(v___x_1892_, v___x_1896_);
v___x_1898_ = lean_nat_dec_le(v___x_1895_, v___x_1897_);
lean_dec(v___x_1897_);
lean_dec(v___x_1895_);
if (v___x_1898_ == 0)
{
lean_dec(v___x_1891_);
lean_dec(v_index_1867_);
goto v___jp_1878_;
}
else
{
lean_object* v___x_1899_; 
lean_dec_ref(v_x_1851_);
lean_dec_ref(v_x_1850_);
v___x_1899_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1852_, v___x_1891_, v_index_1867_, v_a_1853_, v_val_1870_);
lean_dec(v_index_1867_);
return v___x_1899_;
}
}
v___jp_1871_:
{
lean_object* v_size_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v_size_1874_ = lean_ctor_get(v___y_1872_, 0);
v___x_1875_ = lean_unsigned_to_nat(1u);
v___x_1876_ = lean_nat_add(v_size_1874_, v___x_1875_);
v___x_1877_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1872_, v___x_1876_, v_i_1873_, v_a_1853_, v_val_1870_);
lean_dec(v_i_1873_);
return v___x_1877_;
}
v___jp_1878_:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
lean_inc_ref(v_x_1851_);
lean_inc_ref(v_x_1850_);
v___x_1879_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1850_, v_x_1851_, v_m_1852_);
lean_inc(v_a_1853_);
v___x_1880_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1850_, v_x_1851_, v___x_1879_, v_a_1853_);
switch(lean_obj_tag(v___x_1880_))
{
case 0:
{
lean_object* v_index_1881_; lean_object* v_size_1882_; lean_object* v___x_1883_; 
v_index_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_index_1881_);
lean_dec_ref_known(v___x_1880_, 3);
v_size_1882_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_size_1882_);
v___x_1883_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1879_, v_size_1882_, v_index_1881_, v_a_1853_, v_val_1870_);
lean_dec(v_index_1881_);
return v___x_1883_;
}
case 1:
{
lean_object* v_index_1884_; 
v_index_1884_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_index_1884_);
lean_dec_ref_known(v___x_1880_, 1);
v___y_1872_ = v___x_1879_;
v_i_1873_ = v_index_1884_;
goto v___jp_1871_;
}
default: 
{
lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1885_ = lean_unsigned_to_nat(0u);
v___x_1886_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1879_, v___x_1885_);
if (lean_obj_tag(v___x_1886_) == 0)
{
lean_object* v_index_1887_; 
v_index_1887_ = lean_ctor_get(v___x_1886_, 0);
lean_inc(v_index_1887_);
lean_dec_ref_known(v___x_1886_, 1);
v___y_1872_ = v___x_1879_;
v_i_1873_ = v_index_1887_;
goto v___jp_1871_;
}
else
{
lean_dec(v_val_1870_);
lean_dec(v_a_1853_);
return v___x_1879_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_apply_1(v_f_1854_, v___x_1900_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_dec(v_a_1853_);
lean_dec_ref(v_x_1851_);
lean_dec_ref(v_x_1850_);
return v_m_1852_;
}
else
{
lean_object* v_val_1902_; lean_object* v___y_1904_; lean_object* v_i_1905_; lean_object* v___y_1911_; lean_object* v_size_1920_; lean_object* v_keyArray_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; uint8_t v___x_1925_; 
v_val_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_val_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v_size_1920_ = lean_ctor_get(v_m_1852_, 0);
v_keyArray_1921_ = lean_ctor_get(v_m_1852_, 1);
v___x_1922_ = lean_unsigned_to_nat(1u);
v___x_1923_ = lean_nat_add(v_size_1920_, v___x_1922_);
v___x_1924_ = lean_array_get_size(v_keyArray_1921_);
v___x_1925_ = lean_nat_dec_lt(v___x_1923_, v___x_1924_);
if (v___x_1925_ == 0)
{
lean_object* v___x_1926_; 
lean_dec(v___x_1923_);
lean_inc_ref(v_x_1851_);
lean_inc_ref(v_x_1850_);
v___x_1926_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1850_, v_x_1851_, v_m_1852_);
v___y_1911_ = v___x_1926_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v___x_1927_ = lean_unsigned_to_nat(4u);
v___x_1928_ = lean_nat_mul(v___x_1923_, v___x_1927_);
lean_dec(v___x_1923_);
v___x_1929_ = lean_unsigned_to_nat(3u);
v___x_1930_ = lean_nat_mul(v___x_1924_, v___x_1929_);
v___x_1931_ = lean_nat_dec_le(v___x_1928_, v___x_1930_);
lean_dec(v___x_1930_);
lean_dec(v___x_1928_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; 
lean_inc_ref(v_x_1851_);
lean_inc_ref(v_x_1850_);
v___x_1932_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1850_, v_x_1851_, v_m_1852_);
v___y_1911_ = v___x_1932_;
goto v___jp_1910_;
}
else
{
v___y_1911_ = v_m_1852_;
goto v___jp_1910_;
}
}
v___jp_1903_:
{
lean_object* v_size_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v_size_1906_ = lean_ctor_get(v___y_1904_, 0);
v___x_1907_ = lean_unsigned_to_nat(1u);
v___x_1908_ = lean_nat_add(v_size_1906_, v___x_1907_);
v___x_1909_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1904_, v___x_1908_, v_i_1905_, v_a_1853_, v_val_1902_);
lean_dec(v_i_1905_);
return v___x_1909_;
}
v___jp_1910_:
{
lean_object* v___x_1912_; 
lean_inc(v_a_1853_);
v___x_1912_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1850_, v_x_1851_, v___y_1911_, v_a_1853_);
switch(lean_obj_tag(v___x_1912_))
{
case 0:
{
lean_object* v_index_1913_; lean_object* v_size_1914_; lean_object* v___x_1915_; 
v_index_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_index_1913_);
lean_dec_ref_known(v___x_1912_, 3);
v_size_1914_ = lean_ctor_get(v___y_1911_, 0);
lean_inc(v_size_1914_);
v___x_1915_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1911_, v_size_1914_, v_index_1913_, v_a_1853_, v_val_1902_);
lean_dec(v_index_1913_);
return v___x_1915_;
}
case 1:
{
lean_object* v_index_1916_; 
v_index_1916_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_index_1916_);
lean_dec_ref_known(v___x_1912_, 1);
v___y_1904_ = v___y_1911_;
v_i_1905_ = v_index_1916_;
goto v___jp_1903_;
}
default: 
{
lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1917_ = lean_unsigned_to_nat(0u);
v___x_1918_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1911_, v___x_1917_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_index_1919_; 
v_index_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_index_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v___y_1904_ = v___y_1911_;
v_i_1905_ = v_index_1919_;
goto v___jp_1903_;
}
else
{
lean_dec(v_val_1902_);
lean_dec(v_a_1853_);
return v___y_1911_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_alter(lean_object* v_00_u03b1_1933_, lean_object* v_00_u03b2_1934_, lean_object* v_x_1935_, lean_object* v_x_1936_, lean_object* v_m_1937_, lean_object* v_a_1938_, lean_object* v_f_1939_){
_start:
{
lean_object* v___x_1940_; 
lean_inc(v_a_1938_);
lean_inc_ref(v_x_1936_);
lean_inc_ref(v_x_1935_);
v___x_1940_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1935_, v_x_1936_, v_m_1937_, v_a_1938_);
switch(lean_obj_tag(v___x_1940_))
{
case 0:
{
lean_object* v_index_1941_; lean_object* v_value_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec_ref(v_x_1936_);
lean_dec_ref(v_x_1935_);
v_index_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_index_1941_);
v_value_1942_ = lean_ctor_get(v___x_1940_, 2);
lean_inc(v_value_1942_);
lean_dec_ref_known(v___x_1940_, 3);
v___x_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1943_, 0, v_value_1942_);
v___x_1944_ = lean_apply_1(v_f_1939_, v___x_1943_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v_size_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
lean_dec(v_a_1938_);
v_size_1945_ = lean_ctor_get(v_m_1937_, 0);
v___x_1946_ = lean_unsigned_to_nat(1u);
v___x_1947_ = lean_nat_sub(v_size_1945_, v___x_1946_);
v___x_1948_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1937_, v___x_1947_, v_index_1941_);
lean_dec(v_index_1941_);
return v___x_1948_;
}
else
{
lean_object* v_val_1949_; lean_object* v_size_1950_; lean_object* v___x_1951_; 
v_val_1949_ = lean_ctor_get(v___x_1944_, 0);
lean_inc(v_val_1949_);
lean_dec_ref_known(v___x_1944_, 1);
v_size_1950_ = lean_ctor_get(v_m_1937_, 0);
lean_inc(v_size_1950_);
v___x_1951_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1937_, v_size_1950_, v_index_1941_, v_a_1938_, v_val_1949_);
lean_dec(v_index_1941_);
return v___x_1951_;
}
}
case 1:
{
lean_object* v_index_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v_index_1952_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_index_1952_);
lean_dec_ref_known(v___x_1940_, 1);
v___x_1953_ = lean_box(0);
v___x_1954_ = lean_apply_1(v_f_1939_, v___x_1953_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_dec(v_index_1952_);
lean_dec(v_a_1938_);
lean_dec_ref(v_x_1936_);
lean_dec_ref(v_x_1935_);
return v_m_1937_;
}
else
{
lean_object* v_val_1955_; lean_object* v___y_1957_; lean_object* v_i_1958_; lean_object* v_size_1973_; lean_object* v_keyArray_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_val_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_val_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v_size_1973_ = lean_ctor_get(v_m_1937_, 0);
v_keyArray_1974_ = lean_ctor_get(v_m_1937_, 1);
v___x_1975_ = lean_unsigned_to_nat(1u);
v___x_1976_ = lean_nat_add(v_size_1973_, v___x_1975_);
v___x_1977_ = lean_array_get_size(v_keyArray_1974_);
v___x_1978_ = lean_nat_dec_lt(v___x_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_dec(v___x_1976_);
lean_dec(v_index_1952_);
goto v___jp_1963_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; 
v___x_1979_ = lean_unsigned_to_nat(4u);
v___x_1980_ = lean_nat_mul(v___x_1976_, v___x_1979_);
v___x_1981_ = lean_unsigned_to_nat(3u);
v___x_1982_ = lean_nat_mul(v___x_1977_, v___x_1981_);
v___x_1983_ = lean_nat_dec_le(v___x_1980_, v___x_1982_);
lean_dec(v___x_1982_);
lean_dec(v___x_1980_);
if (v___x_1983_ == 0)
{
lean_dec(v___x_1976_);
lean_dec(v_index_1952_);
goto v___jp_1963_;
}
else
{
lean_object* v___x_1984_; 
lean_dec_ref(v_x_1936_);
lean_dec_ref(v_x_1935_);
v___x_1984_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1937_, v___x_1976_, v_index_1952_, v_a_1938_, v_val_1955_);
lean_dec(v_index_1952_);
return v___x_1984_;
}
}
v___jp_1956_:
{
lean_object* v_size_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v_size_1959_ = lean_ctor_get(v___y_1957_, 0);
v___x_1960_ = lean_unsigned_to_nat(1u);
v___x_1961_ = lean_nat_add(v_size_1959_, v___x_1960_);
v___x_1962_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1957_, v___x_1961_, v_i_1958_, v_a_1938_, v_val_1955_);
lean_dec(v_i_1958_);
return v___x_1962_;
}
v___jp_1963_:
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_inc_ref(v_x_1936_);
lean_inc_ref(v_x_1935_);
v___x_1964_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1935_, v_x_1936_, v_m_1937_);
lean_inc(v_a_1938_);
v___x_1965_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1935_, v_x_1936_, v___x_1964_, v_a_1938_);
switch(lean_obj_tag(v___x_1965_))
{
case 0:
{
lean_object* v_index_1966_; lean_object* v_size_1967_; lean_object* v___x_1968_; 
v_index_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_index_1966_);
lean_dec_ref_known(v___x_1965_, 3);
v_size_1967_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_size_1967_);
v___x_1968_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1964_, v_size_1967_, v_index_1966_, v_a_1938_, v_val_1955_);
lean_dec(v_index_1966_);
return v___x_1968_;
}
case 1:
{
lean_object* v_index_1969_; 
v_index_1969_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_index_1969_);
lean_dec_ref_known(v___x_1965_, 1);
v___y_1957_ = v___x_1964_;
v_i_1958_ = v_index_1969_;
goto v___jp_1956_;
}
default: 
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1970_ = lean_unsigned_to_nat(0u);
v___x_1971_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1964_, v___x_1970_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_index_1972_; 
v_index_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_index_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___y_1957_ = v___x_1964_;
v_i_1958_ = v_index_1972_;
goto v___jp_1956_;
}
else
{
lean_dec(v_val_1955_);
lean_dec(v_a_1938_);
return v___x_1964_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1985_ = lean_box(0);
v___x_1986_ = lean_apply_1(v_f_1939_, v___x_1985_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_dec(v_a_1938_);
lean_dec_ref(v_x_1936_);
lean_dec_ref(v_x_1935_);
return v_m_1937_;
}
else
{
lean_object* v_val_1987_; lean_object* v___y_1989_; lean_object* v_i_1990_; lean_object* v___y_1996_; lean_object* v_size_2005_; lean_object* v_keyArray_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v_val_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_val_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v_size_2005_ = lean_ctor_get(v_m_1937_, 0);
v_keyArray_2006_ = lean_ctor_get(v_m_1937_, 1);
v___x_2007_ = lean_unsigned_to_nat(1u);
v___x_2008_ = lean_nat_add(v_size_2005_, v___x_2007_);
v___x_2009_ = lean_array_get_size(v_keyArray_2006_);
v___x_2010_ = lean_nat_dec_lt(v___x_2008_, v___x_2009_);
if (v___x_2010_ == 0)
{
lean_object* v___x_2011_; 
lean_dec(v___x_2008_);
lean_inc_ref(v_x_1936_);
lean_inc_ref(v_x_1935_);
v___x_2011_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1935_, v_x_1936_, v_m_1937_);
v___y_1996_ = v___x_2011_;
goto v___jp_1995_;
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2012_ = lean_unsigned_to_nat(4u);
v___x_2013_ = lean_nat_mul(v___x_2008_, v___x_2012_);
lean_dec(v___x_2008_);
v___x_2014_ = lean_unsigned_to_nat(3u);
v___x_2015_ = lean_nat_mul(v___x_2009_, v___x_2014_);
v___x_2016_ = lean_nat_dec_le(v___x_2013_, v___x_2015_);
lean_dec(v___x_2015_);
lean_dec(v___x_2013_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; 
lean_inc_ref(v_x_1936_);
lean_inc_ref(v_x_1935_);
v___x_2017_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1935_, v_x_1936_, v_m_1937_);
v___y_1996_ = v___x_2017_;
goto v___jp_1995_;
}
else
{
v___y_1996_ = v_m_1937_;
goto v___jp_1995_;
}
}
v___jp_1988_:
{
lean_object* v_size_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_size_1991_ = lean_ctor_get(v___y_1989_, 0);
v___x_1992_ = lean_unsigned_to_nat(1u);
v___x_1993_ = lean_nat_add(v_size_1991_, v___x_1992_);
v___x_1994_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1989_, v___x_1993_, v_i_1990_, v_a_1938_, v_val_1987_);
lean_dec(v_i_1990_);
return v___x_1994_;
}
v___jp_1995_:
{
lean_object* v___x_1997_; 
lean_inc(v_a_1938_);
v___x_1997_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1935_, v_x_1936_, v___y_1996_, v_a_1938_);
switch(lean_obj_tag(v___x_1997_))
{
case 0:
{
lean_object* v_index_1998_; lean_object* v_size_1999_; lean_object* v___x_2000_; 
v_index_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_index_1998_);
lean_dec_ref_known(v___x_1997_, 3);
v_size_1999_ = lean_ctor_get(v___y_1996_, 0);
lean_inc(v_size_1999_);
v___x_2000_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1996_, v_size_1999_, v_index_1998_, v_a_1938_, v_val_1987_);
lean_dec(v_index_1998_);
return v___x_2000_;
}
case 1:
{
lean_object* v_index_2001_; 
v_index_2001_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_index_2001_);
lean_dec_ref_known(v___x_1997_, 1);
v___y_1989_ = v___y_1996_;
v_i_1990_ = v_index_2001_;
goto v___jp_1988_;
}
default: 
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
v___x_2002_ = lean_unsigned_to_nat(0u);
v___x_2003_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1996_, v___x_2002_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_index_2004_; 
v_index_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_index_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___y_1989_ = v___y_1996_;
v_i_1990_ = v_index_2004_;
goto v___jp_1988_;
}
else
{
lean_dec(v_val_1987_);
lean_dec(v_a_1938_);
return v___y_1996_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany___redArg(lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v_inst_2020_, lean_object* v_m_2021_, lean_object* v_l_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2020_, v_x_2018_, v_x_2019_, v_m_2021_, v_l_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertMany(lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_, lean_object* v_00_u03c1_2028_, lean_object* v_inst_2029_, lean_object* v_m_2030_, lean_object* v_l_2031_){
_start:
{
lean_object* v___x_2032_; 
v___x_2032_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2029_, v_x_2026_, v_x_2027_, v_m_2030_, v_l_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit___redArg(lean_object* v_x_2033_, lean_object* v_x_2034_, lean_object* v_inst_2035_, lean_object* v_m_2036_, lean_object* v_l_2037_){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2035_, v_x_2033_, v_x_2034_, v_m_2036_, v_l_2037_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_insertManyIfNewUnit(lean_object* v_00_u03b1_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_, lean_object* v_00_u03c1_2042_, lean_object* v_inst_2043_, lean_object* v_m_2044_, lean_object* v_l_2045_){
_start:
{
lean_object* v___x_2046_; 
v___x_2046_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2043_, v_x_2040_, v_x_2041_, v_m_2044_, v_l_2045_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg___lam__0(lean_object* v_x1_2047_, lean_object* v_x2_2048_, lean_object* v_x3_2049_){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2050_, 0, v_x2_2048_);
lean_ctor_set(v___x_2050_, 1, v_x3_2049_);
v___x_2051_ = lean_array_push(v_x1_2047_, v___x_2050_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___redArg(lean_object* v_m_2053_){
_start:
{
lean_object* v_size_2054_; lean_object* v___f_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v_size_2054_ = lean_ctor_get(v_m_2053_, 0);
v___f_2055_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__0));
v___x_2056_ = lean_mk_empty_array_with_capacity(v_size_2054_);
v___x_2057_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2058_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2057_, v___f_2055_, v___x_2056_, v_m_2053_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray(lean_object* v_00_u03b1_2059_, lean_object* v_00_u03b2_2060_, lean_object* v_x_2061_, lean_object* v_x_2062_, lean_object* v_m_2063_){
_start:
{
lean_object* v_size_2064_; lean_object* v___f_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v_size_2064_ = lean_ctor_get(v_m_2063_, 0);
v___f_2065_ = ((lean_object*)(l_Std_HashMap_toArray___redArg___closed__0));
v___x_2066_ = lean_mk_empty_array_with_capacity(v_size_2064_);
v___x_2067_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2068_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2067_, v___f_2065_, v___x_2066_, v_m_2063_);
return v___x_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_toArray___boxed(lean_object* v_00_u03b1_2069_, lean_object* v_00_u03b2_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_, lean_object* v_m_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l_Std_HashMap_toArray(v_00_u03b1_2069_, v_00_u03b2_2070_, v_x_2071_, v_x_2072_, v_m_2073_);
lean_dec_ref(v_x_2072_);
lean_dec_ref(v_x_2071_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0(lean_object* v_x1_2075_, lean_object* v_x2_2076_, lean_object* v_x3_2077_){
_start:
{
lean_object* v___x_2078_; 
v___x_2078_ = lean_array_push(v_x1_2075_, v_x2_2076_);
return v___x_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg___lam__0___boxed(lean_object* v_x1_2079_, lean_object* v_x2_2080_, lean_object* v_x3_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Std_HashMap_keysArray___redArg___lam__0(v_x1_2079_, v_x2_2080_, v_x3_2081_);
lean_dec(v_x3_2081_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___redArg(lean_object* v_m_2084_){
_start:
{
lean_object* v_size_2085_; lean_object* v___f_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_size_2085_ = lean_ctor_get(v_m_2084_, 0);
v___f_2086_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__0));
v___x_2087_ = lean_mk_empty_array_with_capacity(v_size_2085_);
v___x_2088_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2089_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2088_, v___f_2086_, v___x_2087_, v_m_2084_);
return v___x_2089_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray(lean_object* v_00_u03b1_2090_, lean_object* v_00_u03b2_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_, lean_object* v_m_2094_){
_start:
{
lean_object* v_size_2095_; lean_object* v___f_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v_size_2095_ = lean_ctor_get(v_m_2094_, 0);
v___f_2096_ = ((lean_object*)(l_Std_HashMap_keysArray___redArg___closed__0));
v___x_2097_ = lean_mk_empty_array_with_capacity(v_size_2095_);
v___x_2098_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2099_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2098_, v___f_2096_, v___x_2097_, v_m_2094_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_keysArray___boxed(lean_object* v_00_u03b1_2100_, lean_object* v_00_u03b2_2101_, lean_object* v_x_2102_, lean_object* v_x_2103_, lean_object* v_m_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Std_HashMap_keysArray(v_00_u03b1_2100_, v_00_u03b2_2101_, v_x_2102_, v_x_2103_, v_m_2104_);
lean_dec_ref(v_x_2103_);
lean_dec_ref(v_x_2102_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0(lean_object* v_p_2106_, lean_object* v___x_2107_, lean_object* v___x_2108_, lean_object* v_a_2109_, lean_object* v_b_2110_, lean_object* v_acc_2111_){
_start:
{
lean_object* v___x_2112_; uint8_t v___x_2113_; 
v___x_2112_ = lean_apply_2(v_p_2106_, v_a_2109_, v_b_2110_);
v___x_2113_ = lean_unbox(v___x_2112_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v___x_2108_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
lean_ctor_set(v___x_2115_, 1, v___x_2107_);
v___x_2116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; 
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2108_);
return v___x_2117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___lam__0___boxed(lean_object* v_p_2118_, lean_object* v___x_2119_, lean_object* v___x_2120_, lean_object* v_a_2121_, lean_object* v_b_2122_, lean_object* v_acc_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Std_HashMap_all___redArg___lam__0(v_p_2118_, v___x_2119_, v___x_2120_, v_a_2121_, v_b_2122_, v_acc_2123_);
lean_dec_ref(v_acc_2123_);
return v_res_2124_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_all___redArg(lean_object* v_m_2128_, lean_object* v_p_2129_){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; lean_object* v_fst_2135_; 
v___x_2130_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2131_ = lean_box(0);
v___x_2132_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_2133_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2133_, 0, v_p_2129_);
lean_closure_set(v___f_2133_, 1, v___x_2131_);
lean_closure_set(v___f_2133_, 2, v___x_2132_);
v___x_2134_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2130_, v___f_2133_, v___x_2132_, v_m_2128_);
v_fst_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_fst_2135_);
lean_dec(v___x_2134_);
if (lean_obj_tag(v_fst_2135_) == 0)
{
uint8_t v___x_2136_; 
v___x_2136_ = 1;
return v___x_2136_;
}
else
{
lean_object* v_val_2137_; uint8_t v___x_2138_; 
v_val_2137_ = lean_ctor_get(v_fst_2135_, 0);
lean_inc(v_val_2137_);
lean_dec_ref_known(v_fst_2135_, 1);
v___x_2138_ = lean_unbox(v_val_2137_);
lean_dec(v_val_2137_);
return v___x_2138_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___redArg___boxed(lean_object* v_m_2139_, lean_object* v_p_2140_){
_start:
{
uint8_t v_res_2141_; lean_object* v_r_2142_; 
v_res_2141_ = l_Std_HashMap_all___redArg(v_m_2139_, v_p_2140_);
v_r_2142_ = lean_box(v_res_2141_);
return v_r_2142_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_all(lean_object* v_00_u03b1_2143_, lean_object* v_00_u03b2_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_, lean_object* v_m_2147_, lean_object* v_p_2148_){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___f_2152_; lean_object* v___x_2153_; lean_object* v_fst_2154_; 
v___x_2149_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2150_ = lean_box(0);
v___x_2151_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_2152_ = lean_alloc_closure((void*)(l_Std_HashMap_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2152_, 0, v_p_2148_);
lean_closure_set(v___f_2152_, 1, v___x_2150_);
lean_closure_set(v___f_2152_, 2, v___x_2151_);
v___x_2153_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2149_, v___f_2152_, v___x_2151_, v_m_2147_);
v_fst_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_fst_2154_);
lean_dec(v___x_2153_);
if (lean_obj_tag(v_fst_2154_) == 0)
{
uint8_t v___x_2155_; 
v___x_2155_ = 1;
return v___x_2155_;
}
else
{
lean_object* v_val_2156_; uint8_t v___x_2157_; 
v_val_2156_ = lean_ctor_get(v_fst_2154_, 0);
lean_inc(v_val_2156_);
lean_dec_ref_known(v_fst_2154_, 1);
v___x_2157_ = lean_unbox(v_val_2156_);
lean_dec(v_val_2156_);
return v___x_2157_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_all___boxed(lean_object* v_00_u03b1_2158_, lean_object* v_00_u03b2_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_, lean_object* v_m_2162_, lean_object* v_p_2163_){
_start:
{
uint8_t v_res_2164_; lean_object* v_r_2165_; 
v_res_2164_ = l_Std_HashMap_all(v_00_u03b1_2158_, v_00_u03b2_2159_, v_x_2160_, v_x_2161_, v_m_2162_, v_p_2163_);
lean_dec_ref(v_x_2161_);
lean_dec_ref(v_x_2160_);
v_r_2165_ = lean_box(v_res_2164_);
return v_r_2165_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0(lean_object* v_p_2166_, lean_object* v___x_2167_, lean_object* v___x_2168_, lean_object* v_a_2169_, lean_object* v_b_2170_, lean_object* v_acc_2171_){
_start:
{
lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2172_ = lean_apply_2(v_p_2166_, v_a_2169_, v_b_2170_);
v___x_2173_ = lean_unbox(v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2167_);
return v___x_2174_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; 
lean_dec_ref(v___x_2167_);
v___x_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2172_);
v___x_2176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v___x_2168_);
v___x_2177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2176_);
return v___x_2177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___lam__0___boxed(lean_object* v_p_2178_, lean_object* v___x_2179_, lean_object* v___x_2180_, lean_object* v_a_2181_, lean_object* v_b_2182_, lean_object* v_acc_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Std_HashMap_any___redArg___lam__0(v_p_2178_, v___x_2179_, v___x_2180_, v_a_2181_, v_b_2182_, v_acc_2183_);
lean_dec_ref(v_acc_2183_);
return v_res_2184_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_any___redArg(lean_object* v_m_2185_, lean_object* v_p_2186_){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___f_2190_; lean_object* v___x_2191_; lean_object* v_fst_2192_; 
v___x_2187_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2188_ = lean_box(0);
v___x_2189_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_2190_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2190_, 0, v_p_2186_);
lean_closure_set(v___f_2190_, 1, v___x_2189_);
lean_closure_set(v___f_2190_, 2, v___x_2188_);
v___x_2191_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2187_, v___f_2190_, v___x_2189_, v_m_2185_);
v_fst_2192_ = lean_ctor_get(v___x_2191_, 0);
lean_inc(v_fst_2192_);
lean_dec(v___x_2191_);
if (lean_obj_tag(v_fst_2192_) == 0)
{
uint8_t v___x_2193_; 
v___x_2193_ = 0;
return v___x_2193_;
}
else
{
lean_object* v_val_2194_; uint8_t v___x_2195_; 
v_val_2194_ = lean_ctor_get(v_fst_2192_, 0);
lean_inc(v_val_2194_);
lean_dec_ref_known(v_fst_2192_, 1);
v___x_2195_ = lean_unbox(v_val_2194_);
lean_dec(v_val_2194_);
return v___x_2195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___redArg___boxed(lean_object* v_m_2196_, lean_object* v_p_2197_){
_start:
{
uint8_t v_res_2198_; lean_object* v_r_2199_; 
v_res_2198_ = l_Std_HashMap_any___redArg(v_m_2196_, v_p_2197_);
v_r_2199_ = lean_box(v_res_2198_);
return v_r_2199_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_any(lean_object* v_00_u03b1_2200_, lean_object* v_00_u03b2_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_, lean_object* v_m_2204_, lean_object* v_p_2205_){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___f_2209_; lean_object* v___x_2210_; lean_object* v_fst_2211_; 
v___x_2206_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2207_ = lean_box(0);
v___x_2208_ = ((lean_object*)(l_Std_HashMap_all___redArg___closed__0));
v___f_2209_ = lean_alloc_closure((void*)(l_Std_HashMap_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2209_, 0, v_p_2205_);
lean_closure_set(v___f_2209_, 1, v___x_2208_);
lean_closure_set(v___f_2209_, 2, v___x_2207_);
v___x_2210_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2206_, v___f_2209_, v___x_2208_, v_m_2204_);
v_fst_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_fst_2211_);
lean_dec(v___x_2210_);
if (lean_obj_tag(v_fst_2211_) == 0)
{
uint8_t v___x_2212_; 
v___x_2212_ = 0;
return v___x_2212_;
}
else
{
lean_object* v_val_2213_; uint8_t v___x_2214_; 
v_val_2213_ = lean_ctor_get(v_fst_2211_, 0);
lean_inc(v_val_2213_);
lean_dec_ref_known(v_fst_2211_, 1);
v___x_2214_ = lean_unbox(v_val_2213_);
lean_dec(v_val_2213_);
return v___x_2214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_any___boxed(lean_object* v_00_u03b1_2215_, lean_object* v_00_u03b2_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_m_2219_, lean_object* v_p_2220_){
_start:
{
uint8_t v_res_2221_; lean_object* v_r_2222_; 
v_res_2221_ = l_Std_HashMap_any(v_00_u03b1_2215_, v_00_u03b2_2216_, v_x_2217_, v_x_2218_, v_m_2219_, v_p_2220_);
lean_dec_ref(v_x_2218_);
lean_dec_ref(v_x_2217_);
v_r_2222_ = lean_box(v_res_2221_);
return v_r_2222_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg___lam__0(lean_object* v_inst_2223_, lean_object* v_inst_2224_, lean_object* v_a_2225_, lean_object* v_b_2226_, lean_object* v_acc_2227_){
_start:
{
lean_object* v___y_2229_; lean_object* v_i_2230_; lean_object* v___y_2249_; lean_object* v_i_2250_; lean_object* v___y_2257_; lean_object* v___x_2268_; 
lean_inc(v_a_2225_);
lean_inc_ref(v_inst_2224_);
lean_inc_ref(v_inst_2223_);
v___x_2268_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2223_, v_inst_2224_, v_acc_2227_, v_a_2225_);
switch(lean_obj_tag(v___x_2268_))
{
case 0:
{
lean_object* v___x_2269_; 
lean_dec_ref_known(v___x_2268_, 3);
lean_dec(v_b_2226_);
lean_dec(v_a_2225_);
lean_dec_ref(v_inst_2224_);
lean_dec_ref(v_inst_2223_);
v___x_2269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2269_, 0, v_acc_2227_);
return v___x_2269_;
}
case 1:
{
lean_object* v_index_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2289_; 
v_index_2270_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2272_ = v___x_2268_;
v_isShared_2273_ = v_isSharedCheck_2289_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_index_2270_);
lean_dec(v___x_2268_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2289_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v_size_2274_; lean_object* v_keyArray_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; uint8_t v___x_2279_; 
v_size_2274_ = lean_ctor_get(v_acc_2227_, 0);
v_keyArray_2275_ = lean_ctor_get(v_acc_2227_, 1);
v___x_2276_ = lean_unsigned_to_nat(1u);
v___x_2277_ = lean_nat_add(v_size_2274_, v___x_2276_);
v___x_2278_ = lean_array_get_size(v_keyArray_2275_);
v___x_2279_ = lean_nat_dec_lt(v___x_2277_, v___x_2278_);
if (v___x_2279_ == 0)
{
lean_dec(v___x_2277_);
lean_del_object(v___x_2272_);
lean_dec(v_index_2270_);
goto v___jp_2236_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; uint8_t v___x_2284_; 
v___x_2280_ = lean_unsigned_to_nat(4u);
v___x_2281_ = lean_nat_mul(v___x_2277_, v___x_2280_);
v___x_2282_ = lean_unsigned_to_nat(3u);
v___x_2283_ = lean_nat_mul(v___x_2278_, v___x_2282_);
v___x_2284_ = lean_nat_dec_le(v___x_2281_, v___x_2283_);
lean_dec(v___x_2283_);
lean_dec(v___x_2281_);
if (v___x_2284_ == 0)
{
lean_dec(v___x_2277_);
lean_del_object(v___x_2272_);
lean_dec(v_index_2270_);
goto v___jp_2236_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2287_; 
lean_dec_ref(v_inst_2224_);
lean_dec_ref(v_inst_2223_);
v___x_2285_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2227_, v___x_2277_, v_index_2270_, v_a_2225_, v_b_2226_);
lean_dec(v_index_2270_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2285_);
v___x_2287_ = v___x_2272_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2285_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
default: 
{
lean_object* v_size_2290_; lean_object* v_keyArray_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; uint8_t v___x_2295_; 
v_size_2290_ = lean_ctor_get(v_acc_2227_, 0);
v_keyArray_2291_ = lean_ctor_get(v_acc_2227_, 1);
v___x_2292_ = lean_unsigned_to_nat(1u);
v___x_2293_ = lean_nat_add(v_size_2290_, v___x_2292_);
v___x_2294_ = lean_array_get_size(v_keyArray_2291_);
v___x_2295_ = lean_nat_dec_lt(v___x_2293_, v___x_2294_);
if (v___x_2295_ == 0)
{
lean_object* v___x_2296_; 
lean_dec(v___x_2293_);
lean_inc_ref(v_inst_2224_);
lean_inc_ref(v_inst_2223_);
v___x_2296_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2223_, v_inst_2224_, v_acc_2227_);
v___y_2257_ = v___x_2296_;
goto v___jp_2256_;
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v___x_2297_ = lean_unsigned_to_nat(4u);
v___x_2298_ = lean_nat_mul(v___x_2293_, v___x_2297_);
lean_dec(v___x_2293_);
v___x_2299_ = lean_unsigned_to_nat(3u);
v___x_2300_ = lean_nat_mul(v___x_2294_, v___x_2299_);
v___x_2301_ = lean_nat_dec_le(v___x_2298_, v___x_2300_);
lean_dec(v___x_2300_);
lean_dec(v___x_2298_);
if (v___x_2301_ == 0)
{
lean_object* v___x_2302_; 
lean_inc_ref(v_inst_2224_);
lean_inc_ref(v_inst_2223_);
v___x_2302_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2223_, v_inst_2224_, v_acc_2227_);
v___y_2257_ = v___x_2302_;
goto v___jp_2256_;
}
else
{
v___y_2257_ = v_acc_2227_;
goto v___jp_2256_;
}
}
}
}
v___jp_2228_:
{
lean_object* v_size_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_size_2231_ = lean_ctor_get(v___y_2229_, 0);
v___x_2232_ = lean_unsigned_to_nat(1u);
v___x_2233_ = lean_nat_add(v_size_2231_, v___x_2232_);
v___x_2234_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2229_, v___x_2233_, v_i_2230_, v_a_2225_, v_b_2226_);
lean_dec(v_i_2230_);
v___x_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
return v___x_2235_;
}
v___jp_2236_:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_inc_ref(v_inst_2224_);
lean_inc_ref(v_inst_2223_);
v___x_2237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2223_, v_inst_2224_, v_acc_2227_);
lean_inc(v_a_2225_);
v___x_2238_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2223_, v_inst_2224_, v___x_2237_, v_a_2225_);
switch(lean_obj_tag(v___x_2238_))
{
case 0:
{
lean_object* v_index_2239_; lean_object* v_size_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; 
v_index_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_index_2239_);
lean_dec_ref_known(v___x_2238_, 3);
v_size_2240_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_size_2240_);
v___x_2241_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2237_, v_size_2240_, v_index_2239_, v_a_2225_, v_b_2226_);
lean_dec(v_index_2239_);
v___x_2242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2241_);
return v___x_2242_;
}
case 1:
{
lean_object* v_index_2243_; 
v_index_2243_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_index_2243_);
lean_dec_ref_known(v___x_2238_, 1);
v___y_2229_ = v___x_2237_;
v_i_2230_ = v_index_2243_;
goto v___jp_2228_;
}
default: 
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2237_, v___x_2244_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_index_2246_; 
v_index_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_index_2246_);
lean_dec_ref_known(v___x_2245_, 1);
v___y_2229_ = v___x_2237_;
v_i_2230_ = v_index_2246_;
goto v___jp_2228_;
}
else
{
lean_object* v___x_2247_; 
lean_dec(v_b_2226_);
lean_dec(v_a_2225_);
v___x_2247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2237_);
return v___x_2247_;
}
}
}
}
v___jp_2248_:
{
lean_object* v_size_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_size_2251_ = lean_ctor_get(v___y_2249_, 0);
v___x_2252_ = lean_unsigned_to_nat(1u);
v___x_2253_ = lean_nat_add(v_size_2251_, v___x_2252_);
v___x_2254_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2249_, v___x_2253_, v_i_2250_, v_a_2225_, v_b_2226_);
lean_dec(v_i_2250_);
v___x_2255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
return v___x_2255_;
}
v___jp_2256_:
{
lean_object* v___x_2258_; 
lean_inc(v_a_2225_);
v___x_2258_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2223_, v_inst_2224_, v___y_2257_, v_a_2225_);
switch(lean_obj_tag(v___x_2258_))
{
case 0:
{
lean_object* v_index_2259_; lean_object* v_size_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v_index_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_index_2259_);
lean_dec_ref_known(v___x_2258_, 3);
v_size_2260_ = lean_ctor_get(v___y_2257_, 0);
lean_inc(v_size_2260_);
v___x_2261_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2257_, v_size_2260_, v_index_2259_, v_a_2225_, v_b_2226_);
lean_dec(v_index_2259_);
v___x_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
case 1:
{
lean_object* v_index_2263_; 
v_index_2263_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_index_2263_);
lean_dec_ref_known(v___x_2258_, 1);
v___y_2249_ = v___y_2257_;
v_i_2250_ = v_index_2263_;
goto v___jp_2248_;
}
default: 
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = lean_unsigned_to_nat(0u);
v___x_2265_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2257_, v___x_2264_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_index_2266_; 
v_index_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_index_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___y_2249_ = v___y_2257_;
v_i_2250_ = v_index_2266_;
goto v___jp_2248_;
}
else
{
lean_object* v___x_2267_; 
lean_dec(v_b_2226_);
lean_dec(v_a_2225_);
v___x_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2267_, 0, v___y_2257_);
return v___x_2267_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union___redArg(lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_m_u2081_2307_, lean_object* v_m_u2082_2308_){
_start:
{
lean_object* v_size_2309_; lean_object* v_size_2310_; uint8_t v___x_2311_; 
v_size_2309_ = lean_ctor_get(v_m_u2081_2307_, 0);
v_size_2310_ = lean_ctor_get(v_m_u2082_2308_, 0);
v___x_2311_ = lean_nat_dec_le(v_size_2309_, v_size_2310_);
if (v___x_2311_ == 0)
{
lean_object* v___f_2312_; lean_object* v___x_2313_; 
v___f_2312_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_2313_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2312_, v_inst_2305_, v_inst_2306_, v_m_u2081_2307_, v_m_u2082_2308_);
return v___x_2313_;
}
else
{
lean_object* v___f_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v___f_2314_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2314_, 0, v_inst_2305_);
lean_closure_set(v___f_2314_, 1, v_inst_2306_);
v___x_2315_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2316_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2315_, v___f_2314_, v_m_u2082_2308_, v_m_u2081_2307_);
return v___x_2316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_union(lean_object* v_00_u03b1_2317_, lean_object* v_00_u03b2_2318_, lean_object* v_inst_2319_, lean_object* v_inst_2320_, lean_object* v_m_u2081_2321_, lean_object* v_m_u2082_2322_){
_start:
{
lean_object* v_size_2323_; lean_object* v_size_2324_; uint8_t v___x_2325_; 
v_size_2323_ = lean_ctor_get(v_m_u2081_2321_, 0);
v_size_2324_ = lean_ctor_get(v_m_u2082_2322_, 0);
v___x_2325_ = lean_nat_dec_le(v_size_2323_, v_size_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___f_2326_; lean_object* v___x_2327_; 
v___f_2326_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_2327_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2326_, v_inst_2319_, v_inst_2320_, v_m_u2081_2321_, v_m_u2082_2322_);
return v___x_2327_;
}
else
{
lean_object* v___f_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___f_2328_ = lean_alloc_closure((void*)(l_Std_HashMap_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2328_, 0, v_inst_2319_);
lean_closure_set(v___f_2328_, 1, v_inst_2320_);
v___x_2329_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2330_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2329_, v___f_2328_, v_m_u2082_2322_, v_m_u2081_2321_);
return v___x_2330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion___redArg(lean_object* v_inst_2331_, lean_object* v_inst_2332_){
_start:
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_alloc_closure((void*)(l_Std_HashMap_union), 6, 4);
lean_closure_set(v___x_2333_, 0, lean_box(0));
lean_closure_set(v___x_2333_, 1, lean_box(0));
lean_closure_set(v___x_2333_, 2, v_inst_2331_);
lean_closure_set(v___x_2333_, 3, v_inst_2332_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instUnion(lean_object* v_00_u03b1_2334_, lean_object* v_00_u03b2_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_alloc_closure((void*)(l_Std_HashMap_union), 6, 4);
lean_closure_set(v___x_2338_, 0, lean_box(0));
lean_closure_set(v___x_2338_, 1, lean_box(0));
lean_closure_set(v___x_2338_, 2, v_inst_2336_);
lean_closure_set(v___x_2338_, 3, v_inst_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_inter___redArg(lean_object* v_inst_2339_, lean_object* v_inst_2340_, lean_object* v_m_u2081_2341_, lean_object* v_m_u2082_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2339_, v_inst_2340_, v_m_u2081_2341_, v_m_u2082_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_inter(lean_object* v_00_u03b1_2344_, lean_object* v_00_u03b2_2345_, lean_object* v_inst_2346_, lean_object* v_inst_2347_, lean_object* v_m_u2081_2348_, lean_object* v_m_u2082_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2346_, v_inst_2347_, v_m_u2081_2348_, v_m_u2082_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInter___redArg(lean_object* v_inst_2351_, lean_object* v_inst_2352_){
_start:
{
lean_object* v___x_2353_; 
v___x_2353_ = lean_alloc_closure((void*)(l_Std_HashMap_inter), 6, 4);
lean_closure_set(v___x_2353_, 0, lean_box(0));
lean_closure_set(v___x_2353_, 1, lean_box(0));
lean_closure_set(v___x_2353_, 2, v_inst_2351_);
lean_closure_set(v___x_2353_, 3, v_inst_2352_);
return v___x_2353_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instInter(lean_object* v_00_u03b1_2354_, lean_object* v_00_u03b2_2355_, lean_object* v_inst_2356_, lean_object* v_inst_2357_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = lean_alloc_closure((void*)(l_Std_HashMap_inter), 6, 4);
lean_closure_set(v___x_2358_, 0, lean_box(0));
lean_closure_set(v___x_2358_, 1, lean_box(0));
lean_closure_set(v___x_2358_, 2, v_inst_2356_);
lean_closure_set(v___x_2358_, 3, v_inst_2357_);
return v___x_2358_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq___redArg(lean_object* v_x_2359_, lean_object* v_inst_2360_, lean_object* v_inst_2361_, lean_object* v_m_u2081_2362_, lean_object* v_m_u2082_2363_){
_start:
{
uint8_t v___x_2364_; 
v___x_2364_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_2360_, v_x_2359_, v_inst_2361_, v_m_u2081_2362_, v_m_u2082_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___redArg___boxed(lean_object* v_x_2365_, lean_object* v_inst_2366_, lean_object* v_inst_2367_, lean_object* v_m_u2081_2368_, lean_object* v_m_u2082_2369_){
_start:
{
uint8_t v_res_2370_; lean_object* v_r_2371_; 
v_res_2370_ = l_Std_HashMap_beq___redArg(v_x_2365_, v_inst_2366_, v_inst_2367_, v_m_u2081_2368_, v_m_u2082_2369_);
v_r_2371_ = lean_box(v_res_2370_);
return v_r_2371_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_beq(lean_object* v_00_u03b1_2372_, lean_object* v_x_2373_, lean_object* v_00_u03b2_2374_, lean_object* v_inst_2375_, lean_object* v_inst_2376_, lean_object* v_m_u2081_2377_, lean_object* v_m_u2082_2378_){
_start:
{
uint8_t v___x_2379_; 
v___x_2379_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_2375_, v_x_2373_, v_inst_2376_, v_m_u2081_2377_, v_m_u2082_2378_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_beq___boxed(lean_object* v_00_u03b1_2380_, lean_object* v_x_2381_, lean_object* v_00_u03b2_2382_, lean_object* v_inst_2383_, lean_object* v_inst_2384_, lean_object* v_m_u2081_2385_, lean_object* v_m_u2082_2386_){
_start:
{
uint8_t v_res_2387_; lean_object* v_r_2388_; 
v_res_2387_ = l_Std_HashMap_beq(v_00_u03b1_2380_, v_x_2381_, v_00_u03b2_2382_, v_inst_2383_, v_inst_2384_, v_m_u2081_2385_, v_m_u2082_2386_);
v_r_2388_ = lean_box(v_res_2387_);
return v_r_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq___redArg(lean_object* v_x_2389_, lean_object* v_inst_2390_, lean_object* v_inst_2391_){
_start:
{
lean_object* v___x_2392_; 
v___x_2392_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_2392_, 0, lean_box(0));
lean_closure_set(v___x_2392_, 1, v_x_2389_);
lean_closure_set(v___x_2392_, 2, lean_box(0));
lean_closure_set(v___x_2392_, 3, v_inst_2390_);
lean_closure_set(v___x_2392_, 4, v_inst_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instBEq(lean_object* v_00_u03b1_2393_, lean_object* v_00_u03b2_2394_, lean_object* v_x_2395_, lean_object* v_inst_2396_, lean_object* v_inst_2397_){
_start:
{
lean_object* v___x_2398_; 
v___x_2398_ = lean_alloc_closure((void*)(l_Std_HashMap_beq___boxed), 7, 5);
lean_closure_set(v___x_2398_, 0, lean_box(0));
lean_closure_set(v___x_2398_, 1, v_x_2395_);
lean_closure_set(v___x_2398_, 2, lean_box(0));
lean_closure_set(v___x_2398_, 3, v_inst_2396_);
lean_closure_set(v___x_2398_, 4, v_inst_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_diff___redArg___lam__0(lean_object* v_inst_2399_, lean_object* v_inst_2400_, lean_object* v_m_u2082_2401_, uint8_t v___x_2402_, lean_object* v_k_2403_, lean_object* v_x_2404_){
_start:
{
uint8_t v___x_2405_; 
v___x_2405_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_2399_, v_inst_2400_, v_m_u2082_2401_, v_k_2403_);
if (v___x_2405_ == 0)
{
return v___x_2402_;
}
else
{
uint8_t v___x_2406_; 
v___x_2406_ = 0;
return v___x_2406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg___lam__0___boxed(lean_object* v_inst_2407_, lean_object* v_inst_2408_, lean_object* v_m_u2082_2409_, lean_object* v___x_2410_, lean_object* v_k_2411_, lean_object* v_x_2412_){
_start:
{
uint8_t v___x_80__boxed_2413_; uint8_t v_res_2414_; lean_object* v_r_2415_; 
v___x_80__boxed_2413_ = lean_unbox(v___x_2410_);
v_res_2414_ = l_Std_HashMap_diff___redArg___lam__0(v_inst_2407_, v_inst_2408_, v_m_u2082_2409_, v___x_80__boxed_2413_, v_k_2411_, v_x_2412_);
lean_dec(v_x_2412_);
lean_dec_ref(v_m_u2082_2409_);
v_r_2415_ = lean_box(v_res_2414_);
return v_r_2415_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff___redArg(lean_object* v_inst_2416_, lean_object* v_inst_2417_, lean_object* v_m_u2081_2418_, lean_object* v_m_u2082_2419_){
_start:
{
lean_object* v_size_2420_; lean_object* v_size_2421_; uint8_t v___x_2422_; 
v_size_2420_ = lean_ctor_get(v_m_u2081_2418_, 0);
v_size_2421_ = lean_ctor_get(v_m_u2082_2419_, 0);
v___x_2422_ = lean_nat_dec_le(v_size_2420_, v_size_2421_);
if (v___x_2422_ == 0)
{
lean_object* v___f_2423_; lean_object* v___x_2424_; 
v___f_2423_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_2424_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2423_, v_inst_2416_, v_inst_2417_, v_m_u2081_2418_, v_m_u2082_2419_);
return v___x_2424_;
}
else
{
lean_object* v___x_2425_; lean_object* v___f_2426_; lean_object* v___x_2427_; 
v___x_2425_ = lean_box(v___x_2422_);
v___f_2426_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2426_, 0, v_inst_2416_);
lean_closure_set(v___f_2426_, 1, v_inst_2417_);
lean_closure_set(v___f_2426_, 2, v_m_u2082_2419_);
lean_closure_set(v___f_2426_, 3, v___x_2425_);
v___x_2427_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2426_, v_m_u2081_2418_);
lean_dec_ref(v_m_u2081_2418_);
return v___x_2427_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_diff(lean_object* v_00_u03b1_2428_, lean_object* v_00_u03b2_2429_, lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_m_u2081_2432_, lean_object* v_m_u2082_2433_){
_start:
{
lean_object* v_size_2434_; lean_object* v_size_2435_; uint8_t v___x_2436_; 
v_size_2434_ = lean_ctor_get(v_m_u2081_2432_, 0);
v_size_2435_ = lean_ctor_get(v_m_u2082_2433_, 0);
v___x_2436_ = lean_nat_dec_le(v_size_2434_, v_size_2435_);
if (v___x_2436_ == 0)
{
lean_object* v___f_2437_; lean_object* v___x_2438_; 
v___f_2437_ = ((lean_object*)(l_Std_HashMap_union___redArg___closed__0));
v___x_2438_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2437_, v_inst_2430_, v_inst_2431_, v_m_u2081_2432_, v_m_u2082_2433_);
return v___x_2438_;
}
else
{
lean_object* v___x_2439_; lean_object* v___f_2440_; lean_object* v___x_2441_; 
v___x_2439_ = lean_box(v___x_2436_);
v___f_2440_ = lean_alloc_closure((void*)(l_Std_HashMap_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2440_, 0, v_inst_2430_);
lean_closure_set(v___f_2440_, 1, v_inst_2431_);
lean_closure_set(v___f_2440_, 2, v_m_u2082_2433_);
lean_closure_set(v___f_2440_, 3, v___x_2439_);
v___x_2441_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2440_, v_m_u2081_2432_);
lean_dec_ref(v_m_u2081_2432_);
return v___x_2441_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff___redArg(lean_object* v_inst_2442_, lean_object* v_inst_2443_){
_start:
{
lean_object* v___x_2444_; 
v___x_2444_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_2444_, 0, lean_box(0));
lean_closure_set(v___x_2444_, 1, lean_box(0));
lean_closure_set(v___x_2444_, 2, v_inst_2442_);
lean_closure_set(v___x_2444_, 3, v_inst_2443_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instSDiff(lean_object* v_00_u03b1_2445_, lean_object* v_00_u03b2_2446_, lean_object* v_inst_2447_, lean_object* v_inst_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = lean_alloc_closure((void*)(l_Std_HashMap_diff), 6, 4);
lean_closure_set(v___x_2449_, 0, lean_box(0));
lean_closure_set(v___x_2449_, 1, lean_box(0));
lean_closure_set(v___x_2449_, 2, v_inst_2447_);
lean_closure_set(v___x_2449_, 3, v_inst_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg___lam__0(lean_object* v_f_2450_, lean_object* v_x_2451_, lean_object* v_x_2452_, lean_object* v_x1_2453_, lean_object* v_x2_2454_, lean_object* v_x3_2455_){
_start:
{
lean_object* v_fst_2456_; lean_object* v_snd_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2609_; 
v_fst_2456_ = lean_ctor_get(v_x1_2453_, 0);
v_snd_2457_ = lean_ctor_get(v_x1_2453_, 1);
v_isSharedCheck_2609_ = !lean_is_exclusive(v_x1_2453_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2459_ = v_x1_2453_;
v_isShared_2460_ = v_isSharedCheck_2609_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_snd_2457_);
lean_inc(v_fst_2456_);
lean_dec(v_x1_2453_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2609_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___y_2462_; lean_object* v_i_2463_; lean_object* v___y_2472_; lean_object* v_i_2473_; lean_object* v___y_2480_; lean_object* v___y_2504_; lean_object* v_i_2505_; lean_object* v___y_2512_; lean_object* v___y_2524_; lean_object* v_i_2525_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
lean_inc(v_x3_2455_);
lean_inc(v_x2_2454_);
v___x_2543_ = lean_apply_2(v_f_2450_, v_x2_2454_, v_x3_2455_);
v___x_2544_ = lean_unbox(v___x_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; 
lean_del_object(v___x_2459_);
lean_inc(v_x2_2454_);
lean_inc_ref(v_x_2452_);
lean_inc_ref(v_x_2451_);
v___x_2545_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2451_, v_x_2452_, v_snd_2457_, v_x2_2454_);
switch(lean_obj_tag(v___x_2545_))
{
case 0:
{
lean_object* v_index_2546_; lean_object* v_size_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
lean_dec_ref(v_x_2452_);
lean_dec_ref(v_x_2451_);
v_index_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_index_2546_);
lean_dec_ref_known(v___x_2545_, 3);
v_size_2547_ = lean_ctor_get(v_snd_2457_, 0);
lean_inc(v_size_2547_);
v___x_2548_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_2457_, v_size_2547_, v_index_2546_, v_x2_2454_, v_x3_2455_);
lean_dec(v_index_2546_);
v___x_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2549_, 0, v_fst_2456_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
return v___x_2549_;
}
case 1:
{
lean_object* v_index_2550_; lean_object* v_size_2551_; lean_object* v_keyArray_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; uint8_t v___x_2556_; 
v_index_2550_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_index_2550_);
lean_dec_ref_known(v___x_2545_, 1);
v_size_2551_ = lean_ctor_get(v_snd_2457_, 0);
v_keyArray_2552_ = lean_ctor_get(v_snd_2457_, 1);
v___x_2553_ = lean_unsigned_to_nat(1u);
v___x_2554_ = lean_nat_add(v_size_2551_, v___x_2553_);
v___x_2555_ = lean_array_get_size(v_keyArray_2552_);
v___x_2556_ = lean_nat_dec_lt(v___x_2554_, v___x_2555_);
if (v___x_2556_ == 0)
{
lean_dec(v___x_2554_);
lean_dec(v_index_2550_);
goto v___jp_2531_;
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; 
v___x_2557_ = lean_unsigned_to_nat(4u);
v___x_2558_ = lean_nat_mul(v___x_2554_, v___x_2557_);
v___x_2559_ = lean_unsigned_to_nat(3u);
v___x_2560_ = lean_nat_mul(v___x_2555_, v___x_2559_);
v___x_2561_ = lean_nat_dec_le(v___x_2558_, v___x_2560_);
lean_dec(v___x_2560_);
lean_dec(v___x_2558_);
if (v___x_2561_ == 0)
{
lean_dec(v___x_2554_);
lean_dec(v_index_2550_);
goto v___jp_2531_;
}
else
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
lean_dec_ref(v_x_2452_);
lean_dec_ref(v_x_2451_);
v___x_2562_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_2457_, v___x_2554_, v_index_2550_, v_x2_2454_, v_x3_2455_);
lean_dec(v_index_2550_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v_fst_2456_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
return v___x_2563_;
}
}
}
default: 
{
lean_object* v_size_2564_; lean_object* v_keyArray_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_size_2564_ = lean_ctor_get(v_snd_2457_, 0);
v_keyArray_2565_ = lean_ctor_get(v_snd_2457_, 1);
v___x_2566_ = lean_unsigned_to_nat(1u);
v___x_2567_ = lean_nat_add(v_size_2564_, v___x_2566_);
v___x_2568_ = lean_array_get_size(v_keyArray_2565_);
v___x_2569_ = lean_nat_dec_lt(v___x_2567_, v___x_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; 
lean_dec(v___x_2567_);
lean_inc_ref(v_x_2452_);
lean_inc_ref(v_x_2451_);
v___x_2570_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2451_, v_x_2452_, v_snd_2457_);
v___y_2512_ = v___x_2570_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2571_ = lean_unsigned_to_nat(4u);
v___x_2572_ = lean_nat_mul(v___x_2567_, v___x_2571_);
lean_dec(v___x_2567_);
v___x_2573_ = lean_unsigned_to_nat(3u);
v___x_2574_ = lean_nat_mul(v___x_2568_, v___x_2573_);
v___x_2575_ = lean_nat_dec_le(v___x_2572_, v___x_2574_);
lean_dec(v___x_2574_);
lean_dec(v___x_2572_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; 
lean_inc_ref(v_x_2452_);
lean_inc_ref(v_x_2451_);
v___x_2576_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2451_, v_x_2452_, v_snd_2457_);
v___y_2512_ = v___x_2576_;
goto v___jp_2511_;
}
else
{
v___y_2512_ = v_snd_2457_;
goto v___jp_2511_;
}
}
}
}
}
else
{
lean_object* v___x_2577_; 
lean_inc(v_x2_2454_);
lean_inc_ref(v_x_2452_);
lean_inc_ref(v_x_2451_);
v___x_2577_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2451_, v_x_2452_, v_fst_2456_, v_x2_2454_);
switch(lean_obj_tag(v___x_2577_))
{
case 0:
{
lean_object* v_index_2578_; lean_object* v_size_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_del_object(v___x_2459_);
lean_dec_ref(v_x_2452_);
lean_dec_ref(v_x_2451_);
v_index_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_index_2578_);
lean_dec_ref_known(v___x_2577_, 3);
v_size_2579_ = lean_ctor_get(v_fst_2456_, 0);
lean_inc(v_size_2579_);
v___x_2580_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_2456_, v_size_2579_, v_index_2578_, v_x2_2454_, v_x3_2455_);
lean_dec(v_index_2578_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v_snd_2457_);
return v___x_2581_;
}
case 1:
{
lean_object* v_index_2582_; lean_object* v_size_2583_; lean_object* v_keyArray_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; 
v_index_2582_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_index_2582_);
lean_dec_ref_known(v___x_2577_, 1);
v_size_2583_ = lean_ctor_get(v_fst_2456_, 0);
v_keyArray_2584_ = lean_ctor_get(v_fst_2456_, 1);
v___x_2585_ = lean_unsigned_to_nat(1u);
v___x_2586_ = lean_nat_add(v_size_2583_, v___x_2585_);
v___x_2587_ = lean_array_get_size(v_keyArray_2584_);
v___x_2588_ = lean_nat_dec_lt(v___x_2586_, v___x_2587_);
if (v___x_2588_ == 0)
{
lean_dec(v___x_2586_);
lean_dec(v_index_2582_);
goto v___jp_2491_;
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v___x_2589_ = lean_unsigned_to_nat(4u);
v___x_2590_ = lean_nat_mul(v___x_2586_, v___x_2589_);
v___x_2591_ = lean_unsigned_to_nat(3u);
v___x_2592_ = lean_nat_mul(v___x_2587_, v___x_2591_);
v___x_2593_ = lean_nat_dec_le(v___x_2590_, v___x_2592_);
lean_dec(v___x_2592_);
lean_dec(v___x_2590_);
if (v___x_2593_ == 0)
{
lean_dec(v___x_2586_);
lean_dec(v_index_2582_);
goto v___jp_2491_;
}
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_del_object(v___x_2459_);
lean_dec_ref(v_x_2452_);
lean_dec_ref(v_x_2451_);
v___x_2594_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_2456_, v___x_2586_, v_index_2582_, v_x2_2454_, v_x3_2455_);
lean_dec(v_index_2582_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v_snd_2457_);
return v___x_2595_;
}
}
}
default: 
{
lean_object* v_size_2596_; lean_object* v_keyArray_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; uint8_t v___x_2601_; 
lean_del_object(v___x_2459_);
v_size_2596_ = lean_ctor_get(v_fst_2456_, 0);
v_keyArray_2597_ = lean_ctor_get(v_fst_2456_, 1);
v___x_2598_ = lean_unsigned_to_nat(1u);
v___x_2599_ = lean_nat_add(v_size_2596_, v___x_2598_);
v___x_2600_ = lean_array_get_size(v_keyArray_2597_);
v___x_2601_ = lean_nat_dec_lt(v___x_2599_, v___x_2600_);
if (v___x_2601_ == 0)
{
lean_object* v___x_2602_; 
lean_dec(v___x_2599_);
lean_inc_ref(v_x_2452_);
lean_inc_ref(v_x_2451_);
v___x_2602_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2451_, v_x_2452_, v_fst_2456_);
v___y_2480_ = v___x_2602_;
goto v___jp_2479_;
}
else
{
lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2603_ = lean_unsigned_to_nat(4u);
v___x_2604_ = lean_nat_mul(v___x_2599_, v___x_2603_);
lean_dec(v___x_2599_);
v___x_2605_ = lean_unsigned_to_nat(3u);
v___x_2606_ = lean_nat_mul(v___x_2600_, v___x_2605_);
v___x_2607_ = lean_nat_dec_le(v___x_2604_, v___x_2606_);
lean_dec(v___x_2606_);
lean_dec(v___x_2604_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; 
lean_inc_ref(v_x_2452_);
lean_inc_ref(v_x_2451_);
v___x_2608_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2451_, v_x_2452_, v_fst_2456_);
v___y_2480_ = v___x_2608_;
goto v___jp_2479_;
}
else
{
v___y_2480_ = v_fst_2456_;
goto v___jp_2479_;
}
}
}
}
}
v___jp_2461_:
{
lean_object* v_size_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2469_; 
v_size_2464_ = lean_ctor_get(v___y_2462_, 0);
v___x_2465_ = lean_unsigned_to_nat(1u);
v___x_2466_ = lean_nat_add(v_size_2464_, v___x_2465_);
v___x_2467_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2462_, v___x_2466_, v_i_2463_, v_x2_2454_, v_x3_2455_);
lean_dec(v_i_2463_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2467_);
v___x_2469_ = v___x_2459_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2470_, 1, v_snd_2457_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
v___jp_2471_:
{
lean_object* v_size_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v_size_2474_ = lean_ctor_get(v___y_2472_, 0);
v___x_2475_ = lean_unsigned_to_nat(1u);
v___x_2476_ = lean_nat_add(v_size_2474_, v___x_2475_);
v___x_2477_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2472_, v___x_2476_, v_i_2473_, v_x2_2454_, v_x3_2455_);
lean_dec(v_i_2473_);
v___x_2478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2477_);
lean_ctor_set(v___x_2478_, 1, v_snd_2457_);
return v___x_2478_;
}
v___jp_2479_:
{
lean_object* v___x_2481_; 
lean_inc(v_x2_2454_);
v___x_2481_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2451_, v_x_2452_, v___y_2480_, v_x2_2454_);
switch(lean_obj_tag(v___x_2481_))
{
case 0:
{
lean_object* v_index_2482_; lean_object* v_size_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; 
v_index_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_index_2482_);
lean_dec_ref_known(v___x_2481_, 3);
v_size_2483_ = lean_ctor_get(v___y_2480_, 0);
lean_inc(v_size_2483_);
v___x_2484_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2480_, v_size_2483_, v_index_2482_, v_x2_2454_, v_x3_2455_);
lean_dec(v_index_2482_);
v___x_2485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2484_);
lean_ctor_set(v___x_2485_, 1, v_snd_2457_);
return v___x_2485_;
}
case 1:
{
lean_object* v_index_2486_; 
v_index_2486_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_index_2486_);
lean_dec_ref_known(v___x_2481_, 1);
v___y_2472_ = v___y_2480_;
v_i_2473_ = v_index_2486_;
goto v___jp_2471_;
}
default: 
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2480_, v___x_2487_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v_index_2489_; 
v_index_2489_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_index_2489_);
lean_dec_ref_known(v___x_2488_, 1);
v___y_2472_ = v___y_2480_;
v_i_2473_ = v_index_2489_;
goto v___jp_2471_;
}
else
{
lean_object* v___x_2490_; 
lean_dec(v_x3_2455_);
lean_dec(v_x2_2454_);
v___x_2490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2490_, 0, v___y_2480_);
lean_ctor_set(v___x_2490_, 1, v_snd_2457_);
return v___x_2490_;
}
}
}
}
v___jp_2491_:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
lean_inc_ref(v_x_2452_);
lean_inc_ref(v_x_2451_);
v___x_2492_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2451_, v_x_2452_, v_fst_2456_);
lean_inc(v_x2_2454_);
v___x_2493_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2451_, v_x_2452_, v___x_2492_, v_x2_2454_);
switch(lean_obj_tag(v___x_2493_))
{
case 0:
{
lean_object* v_index_2494_; lean_object* v_size_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
lean_del_object(v___x_2459_);
v_index_2494_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_index_2494_);
lean_dec_ref_known(v___x_2493_, 3);
v_size_2495_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_size_2495_);
v___x_2496_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2492_, v_size_2495_, v_index_2494_, v_x2_2454_, v_x3_2455_);
lean_dec(v_index_2494_);
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2496_);
lean_ctor_set(v___x_2497_, 1, v_snd_2457_);
return v___x_2497_;
}
case 1:
{
lean_object* v_index_2498_; 
v_index_2498_ = lean_ctor_get(v___x_2493_, 0);
lean_inc(v_index_2498_);
lean_dec_ref_known(v___x_2493_, 1);
v___y_2462_ = v___x_2492_;
v_i_2463_ = v_index_2498_;
goto v___jp_2461_;
}
default: 
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = lean_unsigned_to_nat(0u);
v___x_2500_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2492_, v___x_2499_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v_index_2501_; 
v_index_2501_ = lean_ctor_get(v___x_2500_, 0);
lean_inc(v_index_2501_);
lean_dec_ref_known(v___x_2500_, 1);
v___y_2462_ = v___x_2492_;
v_i_2463_ = v_index_2501_;
goto v___jp_2461_;
}
else
{
lean_object* v___x_2502_; 
lean_del_object(v___x_2459_);
lean_dec(v_x3_2455_);
lean_dec(v_x2_2454_);
v___x_2502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2492_);
lean_ctor_set(v___x_2502_, 1, v_snd_2457_);
return v___x_2502_;
}
}
}
}
v___jp_2503_:
{
lean_object* v_size_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; 
v_size_2506_ = lean_ctor_get(v___y_2504_, 0);
v___x_2507_ = lean_unsigned_to_nat(1u);
v___x_2508_ = lean_nat_add(v_size_2506_, v___x_2507_);
v___x_2509_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2504_, v___x_2508_, v_i_2505_, v_x2_2454_, v_x3_2455_);
lean_dec(v_i_2505_);
v___x_2510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2510_, 0, v_fst_2456_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
return v___x_2510_;
}
v___jp_2511_:
{
lean_object* v___x_2513_; 
lean_inc(v_x2_2454_);
v___x_2513_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2451_, v_x_2452_, v___y_2512_, v_x2_2454_);
switch(lean_obj_tag(v___x_2513_))
{
case 0:
{
lean_object* v_index_2514_; lean_object* v_size_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v_index_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_index_2514_);
lean_dec_ref_known(v___x_2513_, 3);
v_size_2515_ = lean_ctor_get(v___y_2512_, 0);
lean_inc(v_size_2515_);
v___x_2516_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2512_, v_size_2515_, v_index_2514_, v_x2_2454_, v_x3_2455_);
lean_dec(v_index_2514_);
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v_fst_2456_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
return v___x_2517_;
}
case 1:
{
lean_object* v_index_2518_; 
v_index_2518_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_index_2518_);
lean_dec_ref_known(v___x_2513_, 1);
v___y_2504_ = v___y_2512_;
v_i_2505_ = v_index_2518_;
goto v___jp_2503_;
}
default: 
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_unsigned_to_nat(0u);
v___x_2520_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2512_, v___x_2519_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v_index_2521_; 
v_index_2521_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_index_2521_);
lean_dec_ref_known(v___x_2520_, 1);
v___y_2504_ = v___y_2512_;
v_i_2505_ = v_index_2521_;
goto v___jp_2503_;
}
else
{
lean_object* v___x_2522_; 
lean_dec(v_x3_2455_);
lean_dec(v_x2_2454_);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v_fst_2456_);
lean_ctor_set(v___x_2522_, 1, v___y_2512_);
return v___x_2522_;
}
}
}
}
v___jp_2523_:
{
lean_object* v_size_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v_size_2526_ = lean_ctor_get(v___y_2524_, 0);
v___x_2527_ = lean_unsigned_to_nat(1u);
v___x_2528_ = lean_nat_add(v_size_2526_, v___x_2527_);
v___x_2529_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2524_, v___x_2528_, v_i_2525_, v_x2_2454_, v_x3_2455_);
lean_dec(v_i_2525_);
v___x_2530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2530_, 0, v_fst_2456_);
lean_ctor_set(v___x_2530_, 1, v___x_2529_);
return v___x_2530_;
}
v___jp_2531_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
lean_inc_ref(v_x_2452_);
lean_inc_ref(v_x_2451_);
v___x_2532_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_2451_, v_x_2452_, v_snd_2457_);
lean_inc(v_x2_2454_);
v___x_2533_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_2451_, v_x_2452_, v___x_2532_, v_x2_2454_);
switch(lean_obj_tag(v___x_2533_))
{
case 0:
{
lean_object* v_index_2534_; lean_object* v_size_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v_index_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_index_2534_);
lean_dec_ref_known(v___x_2533_, 3);
v_size_2535_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_size_2535_);
v___x_2536_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2532_, v_size_2535_, v_index_2534_, v_x2_2454_, v_x3_2455_);
lean_dec(v_index_2534_);
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v_fst_2456_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
return v___x_2537_;
}
case 1:
{
lean_object* v_index_2538_; 
v_index_2538_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_index_2538_);
lean_dec_ref_known(v___x_2533_, 1);
v___y_2524_ = v___x_2532_;
v_i_2525_ = v_index_2538_;
goto v___jp_2523_;
}
default: 
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_unsigned_to_nat(0u);
v___x_2540_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2532_, v___x_2539_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_index_2541_; 
v_index_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_index_2541_);
lean_dec_ref_known(v___x_2540_, 1);
v___y_2524_ = v___x_2532_;
v_i_2525_ = v_index_2541_;
goto v___jp_2523_;
}
else
{
lean_object* v___x_2542_; 
lean_dec(v_x3_2455_);
lean_dec(v_x2_2454_);
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v_fst_2456_);
lean_ctor_set(v___x_2542_, 1, v___x_2532_);
return v___x_2542_;
}
}
}
}
}
}
}
static lean_object* _init_l_Std_HashMap_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__2, &l_Std_HashMap_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_instEmptyCollection___closed__2);
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
return v___x_2611_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition___redArg(lean_object* v_x_2612_, lean_object* v_x_2613_, lean_object* v_f_2614_, lean_object* v_m_2615_){
_start:
{
lean_object* v___f_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v_fst_2620_; lean_object* v_snd_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
v___f_2616_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_2616_, 0, v_f_2614_);
lean_closure_set(v___f_2616_, 1, v_x_2612_);
lean_closure_set(v___f_2616_, 2, v_x_2613_);
v___x_2617_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_2618_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2619_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2618_, v___f_2616_, v___x_2617_, v_m_2615_);
v_fst_2620_ = lean_ctor_get(v___x_2619_, 0);
v_snd_2621_ = lean_ctor_get(v___x_2619_, 1);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2619_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2619_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_snd_2621_);
lean_inc(v_fst_2620_);
lean_dec(v___x_2619_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_fst_2620_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_snd_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_partition(lean_object* v_00_u03b1_2629_, lean_object* v_00_u03b2_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_, lean_object* v_f_2633_, lean_object* v_m_2634_){
_start:
{
lean_object* v___f_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v_fst_2639_; lean_object* v_snd_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
v___f_2635_ = lean_alloc_closure((void*)(l_Std_HashMap_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_2635_, 0, v_f_2633_);
lean_closure_set(v___f_2635_, 1, v_x_2631_);
lean_closure_set(v___f_2635_, 2, v_x_2632_);
v___x_2636_ = lean_obj_once(&l_Std_HashMap_partition___redArg___closed__0, &l_Std_HashMap_partition___redArg___closed__0_once, _init_l_Std_HashMap_partition___redArg___closed__0);
v___x_2637_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2638_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2637_, v___f_2635_, v___x_2636_, v_m_2634_);
v_fst_2639_ = lean_ctor_get(v___x_2638_, 0);
v_snd_2640_ = lean_ctor_get(v___x_2638_, 1);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2638_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_snd_2640_);
lean_inc(v_fst_2639_);
lean_dec(v___x_2638_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_fst_2639_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_snd_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0(lean_object* v_x1_2648_, lean_object* v_x2_2649_, lean_object* v_x3_2650_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2651_, 0, v_x3_2650_);
lean_ctor_set(v___x_2651_, 1, v_x1_2648_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___lam__0___boxed(lean_object* v_x1_2652_, lean_object* v_x2_2653_, lean_object* v_x3_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Std_HashMap_values___redArg___lam__0(v_x1_2652_, v_x2_2653_, v_x3_2654_);
lean_dec(v_x2_2653_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg(lean_object* v_m_2657_){
_start:
{
lean_object* v___f_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
v___f_2658_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__0));
v___x_2659_ = lean_box(0);
v___x_2660_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2661_ = lean_unsigned_to_nat(0u);
v___x_2662_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2660_, v___f_2658_, v_m_2657_, v___x_2659_, v___x_2661_);
return v___x_2662_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___redArg___boxed(lean_object* v_m_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l_Std_HashMap_values___redArg(v_m_2663_);
lean_dec_ref(v_m_2663_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values(lean_object* v_00_u03b1_2665_, lean_object* v_00_u03b2_2666_, lean_object* v_x_2667_, lean_object* v_x_2668_, lean_object* v_m_2669_){
_start:
{
lean_object* v___f_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___f_2670_ = ((lean_object*)(l_Std_HashMap_values___redArg___closed__0));
v___x_2671_ = lean_box(0);
v___x_2672_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2673_ = lean_unsigned_to_nat(0u);
v___x_2674_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2672_, v___f_2670_, v_m_2669_, v___x_2671_, v___x_2673_);
return v___x_2674_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_values___boxed(lean_object* v_00_u03b1_2675_, lean_object* v_00_u03b2_2676_, lean_object* v_x_2677_, lean_object* v_x_2678_, lean_object* v_m_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l_Std_HashMap_values(v_00_u03b1_2675_, v_00_u03b2_2676_, v_x_2677_, v_x_2678_, v_m_2679_);
lean_dec_ref(v_m_2679_);
lean_dec_ref(v_x_2678_);
lean_dec_ref(v_x_2677_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0(lean_object* v_x1_2681_, lean_object* v_x2_2682_, lean_object* v_x3_2683_){
_start:
{
lean_object* v___x_2684_; 
v___x_2684_ = lean_array_push(v_x1_2681_, v_x3_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2685_, lean_object* v_x2_2686_, lean_object* v_x3_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_Std_HashMap_valuesArray___redArg___lam__0(v_x1_2685_, v_x2_2686_, v_x3_2687_);
lean_dec(v_x2_2686_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___redArg(lean_object* v_m_2690_){
_start:
{
lean_object* v_size_2691_; lean_object* v___f_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_size_2691_ = lean_ctor_get(v_m_2690_, 0);
v___f_2692_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__0));
v___x_2693_ = lean_mk_empty_array_with_capacity(v_size_2691_);
v___x_2694_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2695_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2694_, v___f_2692_, v___x_2693_, v_m_2690_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray(lean_object* v_00_u03b1_2696_, lean_object* v_00_u03b2_2697_, lean_object* v_x_2698_, lean_object* v_x_2699_, lean_object* v_m_2700_){
_start:
{
lean_object* v_size_2701_; lean_object* v___f_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v_size_2701_ = lean_ctor_get(v_m_2700_, 0);
v___f_2702_ = ((lean_object*)(l_Std_HashMap_valuesArray___redArg___closed__0));
v___x_2703_ = lean_mk_empty_array_with_capacity(v_size_2701_);
v___x_2704_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2705_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2704_, v___f_2702_, v___x_2703_, v_m_2700_);
return v___x_2705_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_valuesArray___boxed(lean_object* v_00_u03b1_2706_, lean_object* v_00_u03b2_2707_, lean_object* v_x_2708_, lean_object* v_x_2709_, lean_object* v_m_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Std_HashMap_valuesArray(v_00_u03b1_2706_, v_00_u03b2_2707_, v_x_2708_, v_x_2709_, v_m_2710_);
lean_dec_ref(v_x_2709_);
lean_dec_ref(v_x_2708_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray___redArg(lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_l_2714_){
_start:
{
lean_object* v___f_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___f_2715_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2716_ = lean_obj_once(&l_Std_HashMap_unitOfList___redArg___closed__1, &l_Std_HashMap_unitOfList___redArg___closed__1_once, _init_l_Std_HashMap_unitOfList___redArg___closed__1);
v___x_2717_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2715_, v_inst_2712_, v_inst_2713_, v___x_2716_, v_l_2714_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_unitOfArray(lean_object* v_00_u03b1_2718_, lean_object* v_inst_2719_, lean_object* v_inst_2720_, lean_object* v_l_2721_){
_start:
{
lean_object* v___f_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; 
v___f_2722_ = ((lean_object*)(l_Std_HashMap_ofArray___redArg___closed__1));
v___x_2723_ = lean_obj_once(&l_Std_HashMap_unitOfList___redArg___closed__1, &l_Std_HashMap_unitOfList___redArg___closed__1_once, _init_l_Std_HashMap_unitOfList___redArg___closed__1);
v___x_2724_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2722_, v_inst_2719_, v_inst_2720_, v___x_2723_, v_l_2721_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg(lean_object* v_m_2725_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2725_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___redArg___boxed(lean_object* v_m_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Std_HashMap_Internal_numBuckets___redArg(v_m_2727_);
lean_dec_ref(v_m_2727_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets(lean_object* v_00_u03b1_2729_, lean_object* v_00_u03b2_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_, lean_object* v_m_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2733_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2735_, lean_object* v_00_u03b2_2736_, lean_object* v_x_2737_, lean_object* v_x_2738_, lean_object* v_m_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Std_HashMap_Internal_numBuckets(v_00_u03b1_2735_, v_00_u03b2_2736_, v_x_2737_, v_x_2738_, v_m_2739_);
lean_dec_ref(v_m_2739_);
lean_dec_ref(v_x_2738_);
lean_dec_ref(v_x_2737_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__1(lean_object* v___f_2744_, lean_object* v___x_2745_, lean_object* v_m_2746_, lean_object* v_prec_2747_){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2748_ = ((lean_object*)(l_Std_HashMap_instRepr___redArg___lam__1___closed__1));
v___x_2749_ = lean_box(0);
v___x_2750_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v___x_2751_ = lean_unsigned_to_nat(0u);
v___x_2752_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2750_, v___f_2744_, v_m_2746_, v___x_2749_, v___x_2751_);
v___x_2753_ = l_List_repr___redArg(v___x_2745_, v___x_2752_);
v___x_2754_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2748_);
lean_ctor_set(v___x_2754_, 1, v___x_2753_);
v___x_2755_ = l_Repr_addAppParen(v___x_2754_, v_prec_2747_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg___lam__1___boxed(lean_object* v___f_2756_, lean_object* v___x_2757_, lean_object* v_m_2758_, lean_object* v_prec_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Std_HashMap_instRepr___redArg___lam__1(v___f_2756_, v___x_2757_, v_m_2758_, v_prec_2759_);
lean_dec(v_prec_2759_);
lean_dec_ref(v_m_2758_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___redArg(lean_object* v_inst_2761_, lean_object* v_inst_2762_){
_start:
{
lean_object* v___f_2763_; lean_object* v___f_2764_; lean_object* v___x_2765_; lean_object* v___f_2766_; 
v___f_2763_ = ((lean_object*)(l_Std_HashMap_toList___redArg___closed__0));
v___f_2764_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2764_, 0, v_inst_2762_);
v___x_2765_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2765_, 0, lean_box(0));
lean_closure_set(v___x_2765_, 1, lean_box(0));
lean_closure_set(v___x_2765_, 2, v_inst_2761_);
lean_closure_set(v___x_2765_, 3, v___f_2764_);
v___f_2766_ = lean_alloc_closure((void*)(l_Std_HashMap_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2766_, 0, v___f_2763_);
lean_closure_set(v___f_2766_, 1, v___x_2765_);
return v___f_2766_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr(lean_object* v_00_u03b1_2767_, lean_object* v_00_u03b2_2768_, lean_object* v_inst_2769_, lean_object* v_inst_2770_, lean_object* v_inst_2771_, lean_object* v_inst_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Std_HashMap_instRepr___redArg(v_inst_2771_, v_inst_2772_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_instRepr___boxed(lean_object* v_00_u03b1_2774_, lean_object* v_00_u03b2_2775_, lean_object* v_inst_2776_, lean_object* v_inst_2777_, lean_object* v_inst_2778_, lean_object* v_inst_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Std_HashMap_instRepr(v_00_u03b1_2774_, v_00_u03b2_2775_, v_inst_2776_, v_inst_2777_, v_inst_2778_, v_inst_2779_);
lean_dec_ref(v_inst_2777_);
lean_dec_ref(v_inst_2776_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__0(lean_object* v_a_2783_, lean_object* v_x_2784_){
_start:
{
lean_object* v___y_2786_; 
if (lean_obj_tag(v_x_2784_) == 0)
{
lean_object* v___x_2789_; 
v___x_2789_ = ((lean_object*)(l_Array_groupByKey___redArg___lam__0___closed__0));
v___y_2786_ = v___x_2789_;
goto v___jp_2785_;
}
else
{
lean_object* v_val_2790_; 
v_val_2790_ = lean_ctor_get(v_x_2784_, 0);
lean_inc(v_val_2790_);
lean_dec_ref_known(v_x_2784_, 1);
v___y_2786_ = v_val_2790_;
goto v___jp_2785_;
}
v___jp_2785_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_array_push(v___y_2786_, v_a_2783_);
v___x_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2787_);
return v___x_2788_;
}
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg___lam__1(lean_object* v_key_2791_, lean_object* v_inst_2792_, lean_object* v_inst_2793_, lean_object* v_a_2794_, lean_object* v_x_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
lean_inc(v_a_2794_);
v___x_2797_ = lean_apply_1(v_key_2791_, v_a_2794_);
lean_inc(v___x_2797_);
lean_inc_ref(v_inst_2793_);
lean_inc_ref(v_inst_2792_);
v___x_2798_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2792_, v_inst_2793_, v___y_2796_, v___x_2797_);
switch(lean_obj_tag(v___x_2798_))
{
case 0:
{
lean_object* v_index_2799_; lean_object* v_value_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v_val_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2812_; 
lean_dec_ref(v_inst_2793_);
lean_dec_ref(v_inst_2792_);
v_index_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_index_2799_);
v_value_2800_ = lean_ctor_get(v___x_2798_, 2);
lean_inc(v_value_2800_);
lean_dec_ref_known(v___x_2798_, 3);
v___x_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2801_, 0, v_value_2800_);
v___x_2802_ = l_Array_groupByKey___redArg___lam__0(v_a_2794_, v___x_2801_);
v_val_2803_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2805_ = v___x_2802_;
v_isShared_2806_ = v_isSharedCheck_2812_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_val_2803_);
lean_dec(v___x_2802_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2812_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v_size_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; 
v_size_2807_ = lean_ctor_get(v___y_2796_, 0);
lean_inc(v_size_2807_);
v___x_2808_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2796_, v_size_2807_, v_index_2799_, v___x_2797_, v_val_2803_);
lean_dec(v_index_2799_);
if (v_isShared_2806_ == 0)
{
lean_ctor_set(v___x_2805_, 0, v___x_2808_);
v___x_2810_ = v___x_2805_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v___x_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
case 1:
{
lean_object* v_index_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2863_; 
v_index_2813_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2815_ = v___x_2798_;
v_isShared_2816_ = v_isSharedCheck_2863_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_index_2813_);
lean_dec(v___x_2798_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2863_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v_val_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2862_; 
v___x_2817_ = lean_box(0);
v___x_2818_ = l_Array_groupByKey___redArg___lam__0(v_a_2794_, v___x_2817_);
v_val_2819_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2821_ = v___x_2818_;
v_isShared_2822_ = v_isSharedCheck_2862_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_val_2819_);
lean_dec(v___x_2818_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2862_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___y_2824_; lean_object* v_i_2825_; lean_object* v_size_2849_; lean_object* v_keyArray_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v_size_2849_ = lean_ctor_get(v___y_2796_, 0);
v_keyArray_2850_ = lean_ctor_get(v___y_2796_, 1);
v___x_2851_ = lean_unsigned_to_nat(1u);
v___x_2852_ = lean_nat_add(v_size_2849_, v___x_2851_);
v___x_2853_ = lean_array_get_size(v_keyArray_2850_);
v___x_2854_ = lean_nat_dec_lt(v___x_2852_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_dec(v___x_2852_);
lean_dec(v_index_2813_);
goto v___jp_2833_;
}
else
{
lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2855_ = lean_unsigned_to_nat(4u);
v___x_2856_ = lean_nat_mul(v___x_2852_, v___x_2855_);
v___x_2857_ = lean_unsigned_to_nat(3u);
v___x_2858_ = lean_nat_mul(v___x_2853_, v___x_2857_);
v___x_2859_ = lean_nat_dec_le(v___x_2856_, v___x_2858_);
lean_dec(v___x_2858_);
lean_dec(v___x_2856_);
if (v___x_2859_ == 0)
{
lean_dec(v___x_2852_);
lean_dec(v_index_2813_);
goto v___jp_2833_;
}
else
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
lean_del_object(v___x_2821_);
lean_del_object(v___x_2815_);
lean_dec_ref(v_inst_2793_);
lean_dec_ref(v_inst_2792_);
v___x_2860_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2796_, v___x_2852_, v_index_2813_, v___x_2797_, v_val_2819_);
lean_dec(v_index_2813_);
v___x_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2861_, 0, v___x_2860_);
return v___x_2861_;
}
}
v___jp_2823_:
{
lean_object* v_size_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; 
v_size_2826_ = lean_ctor_get(v___y_2824_, 0);
v___x_2827_ = lean_unsigned_to_nat(1u);
v___x_2828_ = lean_nat_add(v_size_2826_, v___x_2827_);
v___x_2829_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2824_, v___x_2828_, v_i_2825_, v___x_2797_, v_val_2819_);
lean_dec(v_i_2825_);
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v___x_2829_);
v___x_2831_ = v___x_2821_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v___x_2829_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
v___jp_2833_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
lean_inc_ref(v_inst_2793_);
lean_inc_ref(v_inst_2792_);
v___x_2834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2792_, v_inst_2793_, v___y_2796_);
lean_inc(v___x_2797_);
v___x_2835_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2792_, v_inst_2793_, v___x_2834_, v___x_2797_);
switch(lean_obj_tag(v___x_2835_))
{
case 0:
{
lean_object* v_index_2836_; lean_object* v_size_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
lean_del_object(v___x_2821_);
v_index_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_index_2836_);
lean_dec_ref_known(v___x_2835_, 3);
v_size_2837_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_size_2837_);
v___x_2838_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2834_, v_size_2837_, v_index_2836_, v___x_2797_, v_val_2819_);
lean_dec(v_index_2836_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2838_);
v___x_2840_ = v___x_2815_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
case 1:
{
lean_object* v_index_2842_; 
lean_del_object(v___x_2815_);
v_index_2842_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_index_2842_);
lean_dec_ref_known(v___x_2835_, 1);
v___y_2824_ = v___x_2834_;
v_i_2825_ = v_index_2842_;
goto v___jp_2823_;
}
default: 
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_unsigned_to_nat(0u);
v___x_2844_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2834_, v___x_2843_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_index_2845_; 
lean_del_object(v___x_2815_);
v_index_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_index_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v___y_2824_ = v___x_2834_;
v_i_2825_ = v_index_2845_;
goto v___jp_2823_;
}
else
{
lean_object* v___x_2847_; 
lean_del_object(v___x_2821_);
lean_dec(v_val_2819_);
lean_dec(v___x_2797_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2834_);
v___x_2847_ = v___x_2815_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2834_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
}
}
}
}
default: 
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v_val_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2905_; 
v___x_2864_ = lean_box(0);
v___x_2865_ = l_Array_groupByKey___redArg___lam__0(v_a_2794_, v___x_2864_);
v_val_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2905_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_val_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2905_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___y_2871_; lean_object* v_i_2872_; lean_object* v___y_2881_; lean_object* v_size_2892_; lean_object* v_keyArray_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; uint8_t v___x_2897_; 
v_size_2892_ = lean_ctor_get(v___y_2796_, 0);
v_keyArray_2893_ = lean_ctor_get(v___y_2796_, 1);
v___x_2894_ = lean_unsigned_to_nat(1u);
v___x_2895_ = lean_nat_add(v_size_2892_, v___x_2894_);
v___x_2896_ = lean_array_get_size(v_keyArray_2893_);
v___x_2897_ = lean_nat_dec_lt(v___x_2895_, v___x_2896_);
if (v___x_2897_ == 0)
{
lean_object* v___x_2898_; 
lean_dec(v___x_2895_);
lean_inc_ref(v_inst_2793_);
lean_inc_ref(v_inst_2792_);
v___x_2898_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2792_, v_inst_2793_, v___y_2796_);
v___y_2881_ = v___x_2898_;
goto v___jp_2880_;
}
else
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2899_ = lean_unsigned_to_nat(4u);
v___x_2900_ = lean_nat_mul(v___x_2895_, v___x_2899_);
lean_dec(v___x_2895_);
v___x_2901_ = lean_unsigned_to_nat(3u);
v___x_2902_ = lean_nat_mul(v___x_2896_, v___x_2901_);
v___x_2903_ = lean_nat_dec_le(v___x_2900_, v___x_2902_);
lean_dec(v___x_2902_);
lean_dec(v___x_2900_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; 
lean_inc_ref(v_inst_2793_);
lean_inc_ref(v_inst_2792_);
v___x_2904_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2792_, v_inst_2793_, v___y_2796_);
v___y_2881_ = v___x_2904_;
goto v___jp_2880_;
}
else
{
v___y_2881_ = v___y_2796_;
goto v___jp_2880_;
}
}
v___jp_2870_:
{
lean_object* v_size_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v_size_2873_ = lean_ctor_get(v___y_2871_, 0);
v___x_2874_ = lean_unsigned_to_nat(1u);
v___x_2875_ = lean_nat_add(v_size_2873_, v___x_2874_);
v___x_2876_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2871_, v___x_2875_, v_i_2872_, v___x_2797_, v_val_2866_);
lean_dec(v_i_2872_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v___x_2876_);
v___x_2878_ = v___x_2868_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
v___jp_2880_:
{
lean_object* v___x_2882_; 
lean_inc(v___x_2797_);
v___x_2882_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2792_, v_inst_2793_, v___y_2881_, v___x_2797_);
switch(lean_obj_tag(v___x_2882_))
{
case 0:
{
lean_object* v_index_2883_; lean_object* v_size_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; 
lean_del_object(v___x_2868_);
v_index_2883_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_index_2883_);
lean_dec_ref_known(v___x_2882_, 3);
v_size_2884_ = lean_ctor_get(v___y_2881_, 0);
lean_inc(v_size_2884_);
v___x_2885_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2881_, v_size_2884_, v_index_2883_, v___x_2797_, v_val_2866_);
lean_dec(v_index_2883_);
v___x_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2885_);
return v___x_2886_;
}
case 1:
{
lean_object* v_index_2887_; 
v_index_2887_ = lean_ctor_get(v___x_2882_, 0);
lean_inc(v_index_2887_);
lean_dec_ref_known(v___x_2882_, 1);
v___y_2871_ = v___y_2881_;
v_i_2872_ = v_index_2887_;
goto v___jp_2870_;
}
default: 
{
lean_object* v___x_2888_; lean_object* v___x_2889_; 
v___x_2888_ = lean_unsigned_to_nat(0u);
v___x_2889_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2881_, v___x_2888_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_index_2890_; 
v_index_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_index_2890_);
lean_dec_ref_known(v___x_2889_, 1);
v___y_2871_ = v___y_2881_;
v_i_2872_ = v_index_2890_;
goto v___jp_2870_;
}
else
{
lean_object* v___x_2891_; 
lean_del_object(v___x_2868_);
lean_dec(v_val_2866_);
lean_dec(v___x_2797_);
v___x_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2891_, 0, v___y_2881_);
return v___x_2891_;
}
}
}
}
}
}
}
}
}
static lean_object* _init_l_Array_groupByKey___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_2906_; lean_object* v___x_2907_; 
v_cellCount_2906_ = lean_unsigned_to_nat(16u);
v___x_2907_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_2906_);
return v___x_2907_;
}
}
static lean_object* _init_l_Array_groupByKey___redArg___closed__1(void){
_start:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v_groups_2911_; 
v___x_2908_ = lean_obj_once(&l_Array_groupByKey___redArg___closed__0, &l_Array_groupByKey___redArg___closed__0_once, _init_l_Array_groupByKey___redArg___closed__0);
v___x_2909_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__0, &l_Std_HashMap_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_instEmptyCollection___closed__0);
v___x_2910_ = lean_unsigned_to_nat(0u);
v_groups_2911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_groups_2911_, 0, v___x_2910_);
lean_ctor_set(v_groups_2911_, 1, v___x_2909_);
lean_ctor_set(v_groups_2911_, 2, v___x_2908_);
return v_groups_2911_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey___redArg(lean_object* v_inst_2912_, lean_object* v_inst_2913_, lean_object* v_key_2914_, lean_object* v_xs_2915_){
_start:
{
lean_object* v___f_2916_; lean_object* v___x_2917_; lean_object* v_groups_2918_; size_t v_sz_2919_; size_t v___x_2920_; lean_object* v___x_2921_; 
v___f_2916_ = lean_alloc_closure((void*)(l_Array_groupByKey___redArg___lam__1), 6, 3);
lean_closure_set(v___f_2916_, 0, v_key_2914_);
lean_closure_set(v___f_2916_, 1, v_inst_2912_);
lean_closure_set(v___f_2916_, 2, v_inst_2913_);
v___x_2917_ = ((lean_object*)(l_Std_HashMap_keys___redArg___closed__10));
v_groups_2918_ = lean_obj_once(&l_Array_groupByKey___redArg___closed__1, &l_Array_groupByKey___redArg___closed__1_once, _init_l_Array_groupByKey___redArg___closed__1);
v_sz_2919_ = lean_array_size(v_xs_2915_);
v___x_2920_ = ((size_t)0ULL);
v___x_2921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(lean_box(0), lean_box(0), lean_box(0), v___x_2917_, v_xs_2915_, v___f_2916_, v_sz_2919_, v___x_2920_, v_groups_2918_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Array_groupByKey(lean_object* v_00_u03b1_2922_, lean_object* v_00_u03b2_2923_, lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_key_2926_, lean_object* v_xs_2927_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_Array_groupByKey___redArg(v_inst_2924_, v_inst_2925_, v_key_2926_, v_xs_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__0(lean_object* v_x_2929_, lean_object* v_v_2930_){
_start:
{
lean_object* v___y_2932_; 
if (lean_obj_tag(v_v_2930_) == 0)
{
lean_object* v___x_2935_; 
v___x_2935_ = lean_box(0);
v___y_2932_ = v___x_2935_;
goto v___jp_2931_;
}
else
{
lean_object* v_val_2936_; 
v_val_2936_ = lean_ctor_get(v_v_2930_, 0);
lean_inc(v_val_2936_);
lean_dec_ref_known(v_v_2930_, 1);
v___y_2932_ = v_val_2936_;
goto v___jp_2931_;
}
v___jp_2931_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2933_, 0, v_x_2929_);
lean_ctor_set(v___x_2933_, 1, v___y_2932_);
v___x_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg___lam__1(lean_object* v_key_2937_, lean_object* v_inst_2938_, lean_object* v_inst_2939_, lean_object* v_x_2940_, lean_object* v_acc_2941_){
_start:
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
lean_inc(v_x_2940_);
v___x_2942_ = lean_apply_1(v_key_2937_, v_x_2940_);
lean_inc(v___x_2942_);
lean_inc_ref(v_inst_2939_);
lean_inc_ref(v_inst_2938_);
v___x_2943_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2938_, v_inst_2939_, v_acc_2941_, v___x_2942_);
switch(lean_obj_tag(v___x_2943_))
{
case 0:
{
lean_object* v_index_2944_; lean_object* v_value_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v_val_2948_; lean_object* v_size_2949_; lean_object* v___x_2950_; 
lean_dec_ref(v_inst_2939_);
lean_dec_ref(v_inst_2938_);
v_index_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_index_2944_);
v_value_2945_ = lean_ctor_get(v___x_2943_, 2);
lean_inc(v_value_2945_);
lean_dec_ref_known(v___x_2943_, 3);
v___x_2946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2946_, 0, v_value_2945_);
v___x_2947_ = l_List_groupByKey___redArg___lam__0(v_x_2940_, v___x_2946_);
v_val_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_val_2948_);
lean_dec(v___x_2947_);
v_size_2949_ = lean_ctor_get(v_acc_2941_, 0);
lean_inc(v_size_2949_);
v___x_2950_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2941_, v_size_2949_, v_index_2944_, v___x_2942_, v_val_2948_);
lean_dec(v_index_2944_);
return v___x_2950_;
}
case 1:
{
lean_object* v_index_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_val_2954_; lean_object* v___y_2956_; lean_object* v_i_2957_; lean_object* v_size_2972_; lean_object* v_keyArray_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v_index_2951_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_index_2951_);
lean_dec_ref_known(v___x_2943_, 1);
v___x_2952_ = lean_box(0);
v___x_2953_ = l_List_groupByKey___redArg___lam__0(v_x_2940_, v___x_2952_);
v_val_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_val_2954_);
lean_dec(v___x_2953_);
v_size_2972_ = lean_ctor_get(v_acc_2941_, 0);
v_keyArray_2973_ = lean_ctor_get(v_acc_2941_, 1);
v___x_2974_ = lean_unsigned_to_nat(1u);
v___x_2975_ = lean_nat_add(v_size_2972_, v___x_2974_);
v___x_2976_ = lean_array_get_size(v_keyArray_2973_);
v___x_2977_ = lean_nat_dec_lt(v___x_2975_, v___x_2976_);
if (v___x_2977_ == 0)
{
lean_dec(v___x_2975_);
lean_dec(v_index_2951_);
goto v___jp_2962_;
}
else
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; uint8_t v___x_2982_; 
v___x_2978_ = lean_unsigned_to_nat(4u);
v___x_2979_ = lean_nat_mul(v___x_2975_, v___x_2978_);
v___x_2980_ = lean_unsigned_to_nat(3u);
v___x_2981_ = lean_nat_mul(v___x_2976_, v___x_2980_);
v___x_2982_ = lean_nat_dec_le(v___x_2979_, v___x_2981_);
lean_dec(v___x_2981_);
lean_dec(v___x_2979_);
if (v___x_2982_ == 0)
{
lean_dec(v___x_2975_);
lean_dec(v_index_2951_);
goto v___jp_2962_;
}
else
{
lean_object* v___x_2983_; 
lean_dec_ref(v_inst_2939_);
lean_dec_ref(v_inst_2938_);
v___x_2983_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2941_, v___x_2975_, v_index_2951_, v___x_2942_, v_val_2954_);
lean_dec(v_index_2951_);
return v___x_2983_;
}
}
v___jp_2955_:
{
lean_object* v_size_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; 
v_size_2958_ = lean_ctor_get(v___y_2956_, 0);
v___x_2959_ = lean_unsigned_to_nat(1u);
v___x_2960_ = lean_nat_add(v_size_2958_, v___x_2959_);
v___x_2961_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2956_, v___x_2960_, v_i_2957_, v___x_2942_, v_val_2954_);
lean_dec(v_i_2957_);
return v___x_2961_;
}
v___jp_2962_:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; 
lean_inc_ref(v_inst_2939_);
lean_inc_ref(v_inst_2938_);
v___x_2963_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2938_, v_inst_2939_, v_acc_2941_);
lean_inc(v___x_2942_);
v___x_2964_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2938_, v_inst_2939_, v___x_2963_, v___x_2942_);
switch(lean_obj_tag(v___x_2964_))
{
case 0:
{
lean_object* v_index_2965_; lean_object* v_size_2966_; lean_object* v___x_2967_; 
v_index_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_index_2965_);
lean_dec_ref_known(v___x_2964_, 3);
v_size_2966_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_size_2966_);
v___x_2967_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2963_, v_size_2966_, v_index_2965_, v___x_2942_, v_val_2954_);
lean_dec(v_index_2965_);
return v___x_2967_;
}
case 1:
{
lean_object* v_index_2968_; 
v_index_2968_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_index_2968_);
lean_dec_ref_known(v___x_2964_, 1);
v___y_2956_ = v___x_2963_;
v_i_2957_ = v_index_2968_;
goto v___jp_2955_;
}
default: 
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_unsigned_to_nat(0u);
v___x_2970_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2963_, v___x_2969_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v_index_2971_; 
v_index_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_index_2971_);
lean_dec_ref_known(v___x_2970_, 1);
v___y_2956_ = v___x_2963_;
v_i_2957_ = v_index_2971_;
goto v___jp_2955_;
}
else
{
lean_dec(v_val_2954_);
lean_dec(v___x_2942_);
return v___x_2963_;
}
}
}
}
}
default: 
{
lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v_val_2986_; lean_object* v___y_2988_; lean_object* v_i_2989_; lean_object* v___y_2995_; lean_object* v_size_3004_; lean_object* v_keyArray_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v___x_2984_ = lean_box(0);
v___x_2985_ = l_List_groupByKey___redArg___lam__0(v_x_2940_, v___x_2984_);
v_val_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_val_2986_);
lean_dec(v___x_2985_);
v_size_3004_ = lean_ctor_get(v_acc_2941_, 0);
v_keyArray_3005_ = lean_ctor_get(v_acc_2941_, 1);
v___x_3006_ = lean_unsigned_to_nat(1u);
v___x_3007_ = lean_nat_add(v_size_3004_, v___x_3006_);
v___x_3008_ = lean_array_get_size(v_keyArray_3005_);
v___x_3009_ = lean_nat_dec_lt(v___x_3007_, v___x_3008_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; 
lean_dec(v___x_3007_);
lean_inc_ref(v_inst_2939_);
lean_inc_ref(v_inst_2938_);
v___x_3010_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2938_, v_inst_2939_, v_acc_2941_);
v___y_2995_ = v___x_3010_;
goto v___jp_2994_;
}
else
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v___x_3011_ = lean_unsigned_to_nat(4u);
v___x_3012_ = lean_nat_mul(v___x_3007_, v___x_3011_);
lean_dec(v___x_3007_);
v___x_3013_ = lean_unsigned_to_nat(3u);
v___x_3014_ = lean_nat_mul(v___x_3008_, v___x_3013_);
v___x_3015_ = lean_nat_dec_le(v___x_3012_, v___x_3014_);
lean_dec(v___x_3014_);
lean_dec(v___x_3012_);
if (v___x_3015_ == 0)
{
lean_object* v___x_3016_; 
lean_inc_ref(v_inst_2939_);
lean_inc_ref(v_inst_2938_);
v___x_3016_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2938_, v_inst_2939_, v_acc_2941_);
v___y_2995_ = v___x_3016_;
goto v___jp_2994_;
}
else
{
v___y_2995_ = v_acc_2941_;
goto v___jp_2994_;
}
}
v___jp_2987_:
{
lean_object* v_size_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; 
v_size_2990_ = lean_ctor_get(v___y_2988_, 0);
v___x_2991_ = lean_unsigned_to_nat(1u);
v___x_2992_ = lean_nat_add(v_size_2990_, v___x_2991_);
v___x_2993_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2988_, v___x_2992_, v_i_2989_, v___x_2942_, v_val_2986_);
lean_dec(v_i_2989_);
return v___x_2993_;
}
v___jp_2994_:
{
lean_object* v___x_2996_; 
lean_inc(v___x_2942_);
v___x_2996_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2938_, v_inst_2939_, v___y_2995_, v___x_2942_);
switch(lean_obj_tag(v___x_2996_))
{
case 0:
{
lean_object* v_index_2997_; lean_object* v_size_2998_; lean_object* v___x_2999_; 
v_index_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_index_2997_);
lean_dec_ref_known(v___x_2996_, 3);
v_size_2998_ = lean_ctor_get(v___y_2995_, 0);
lean_inc(v_size_2998_);
v___x_2999_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2995_, v_size_2998_, v_index_2997_, v___x_2942_, v_val_2986_);
lean_dec(v_index_2997_);
return v___x_2999_;
}
case 1:
{
lean_object* v_index_3000_; 
v_index_3000_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_index_3000_);
lean_dec_ref_known(v___x_2996_, 1);
v___y_2988_ = v___y_2995_;
v_i_2989_ = v_index_3000_;
goto v___jp_2987_;
}
default: 
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_unsigned_to_nat(0u);
v___x_3002_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2995_, v___x_3001_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_index_3003_; 
v_index_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_index_3003_);
lean_dec_ref_known(v___x_3002_, 1);
v___y_2988_ = v___y_2995_;
v_i_2989_ = v_index_3003_;
goto v___jp_2987_;
}
else
{
lean_dec(v_val_2986_);
lean_dec(v___x_2942_);
return v___y_2995_;
}
}
}
}
}
}
}
}
static lean_object* _init_l_List_groupByKey___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_3017_; lean_object* v___x_3018_; 
v_cellCount_3017_ = lean_unsigned_to_nat(16u);
v___x_3018_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3017_);
return v___x_3018_;
}
}
static lean_object* _init_l_List_groupByKey___redArg___closed__1(void){
_start:
{
lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3019_ = lean_obj_once(&l_List_groupByKey___redArg___closed__0, &l_List_groupByKey___redArg___closed__0_once, _init_l_List_groupByKey___redArg___closed__0);
v___x_3020_ = lean_obj_once(&l_Std_HashMap_instEmptyCollection___closed__0, &l_Std_HashMap_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_instEmptyCollection___closed__0);
v___x_3021_ = lean_unsigned_to_nat(0u);
v___x_3022_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v___x_3020_);
lean_ctor_set(v___x_3022_, 2, v___x_3019_);
return v___x_3022_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey___redArg(lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_key_3025_, lean_object* v_xs_3026_){
_start:
{
lean_object* v___f_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___f_3027_ = lean_alloc_closure((void*)(l_List_groupByKey___redArg___lam__1), 5, 3);
lean_closure_set(v___f_3027_, 0, v_key_3025_);
lean_closure_set(v___f_3027_, 1, v_inst_3023_);
lean_closure_set(v___f_3027_, 2, v_inst_3024_);
v___x_3028_ = lean_obj_once(&l_List_groupByKey___redArg___closed__1, &l_List_groupByKey___redArg___closed__1_once, _init_l_List_groupByKey___redArg___closed__1);
v___x_3029_ = l_List_foldrTR___redArg(v___f_3027_, v___x_3028_, v_xs_3026_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_List_groupByKey(lean_object* v_00_u03b1_3030_, lean_object* v_00_u03b2_3031_, lean_object* v_inst_3032_, lean_object* v_inst_3033_, lean_object* v_key_3034_, lean_object* v_xs_3035_){
_start:
{
lean_object* v___x_3036_; 
v___x_3036_ = l_List_groupByKey___redArg(v_inst_3032_, v_inst_3033_, v_key_3034_, v_xs_3035_);
return v___x_3036_;
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
