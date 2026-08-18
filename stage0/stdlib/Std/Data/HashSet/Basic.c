// Lean compiler output
// Module: Std.Data.HashSet.Basic
// Imports: public import Std.Data.HashMap.Basic
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_HashSet_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instEmptyCollection___closed__1;
static lean_once_cell_t l_Std_HashSet_instEmptyCollection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instEmptyCollection___closed__2;
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__0 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HashSet"};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__1 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__2 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__2_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__3_value_aux_0),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 195, 212, 176, 236, 184, 63, 58)}};
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__3_value_aux_1),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(31, 188, 56, 164, 219, 178, 234, 183)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__3 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__3_value;
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__4 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__4_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__5 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__5_value;
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__6 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__6_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__6_value)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__7 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__7_value;
static const lean_string_object l_Std_HashSet_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__8 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__8_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__9 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__9_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__10 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__5_value),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__7_value),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__10_value)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__11 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_HashSet_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_HashSet_term___x7em___00__closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_HashSet_term___x7em___00__closed__12 = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__12_value;
LEAN_EXPORT const lean_object* l_Std_HashSet_term___x7em__ = (const lean_object*)&l_Std_HashSet_term___x7em___00__closed__12_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_0),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_1),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value_aux_2),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value;
static lean_once_cell_t l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_0),((lean_object*)&l_Std_HashSet_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 195, 212, 176, 236, 184, 63, 58)}};
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value_aux_1),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(222, 215, 188, 50, 207, 199, 108, 184)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__8_value)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__9_value),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__11_value)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12_value;
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14_value;
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1 = (const lean_object*)&l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_instSingleton___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instSingleton___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_HashSet_instSingleton___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashSet_instSingleton___redArg___lam__0___closed__1;
static lean_once_cell_t l_Std_HashSet_instSingleton___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_instSingleton___redArg___lam__0___closed__2;
static lean_once_cell_t l_Std_HashSet_instSingleton___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashSet_instSingleton___redArg___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_size___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__1_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__2 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__2_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__3 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__3_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__4 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__4_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__5 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__5_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__6 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__6_value;
static const lean_closure_object l_Std_HashSet_toList___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toList___redArg___closed__7 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__7_value;
static const lean_ctor_object l_Std_HashSet_toList___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__1_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__2_value)}};
static const lean_object* l_Std_HashSet_toList___redArg___closed__8 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__8_value;
static const lean_ctor_object l_Std_HashSet_toList___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__8_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__3_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__4_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__5_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__6_value)}};
static const lean_object* l_Std_HashSet_toList___redArg___closed__9 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__9_value;
static const lean_ctor_object l_Std_HashSet_toList___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__9_value),((lean_object*)&l_Std_HashSet_toList___redArg___closed__7_value)}};
static const lean_object* l_Std_HashSet_toList___redArg___closed__10 = (const lean_object*)&l_Std_HashSet_toList___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toList___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__10_value)} };
static const lean_object* l_Std_HashSet_ofList___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashSet_ofList___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_fold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_toArray___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_HashSet_all___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet_all___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_all___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_HashSet_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_all(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__10_value)} };
static const lean_object* l_Std_HashSet_union___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instInter(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_beq___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_beq___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_HashSet_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_partition___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_partition___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_partition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_toList___redArg___closed__10_value)} };
static const lean_object* l_Std_HashSet_ofArray___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_ofArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_ofArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_ofArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashSet_ofArray___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_ofArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashSet_instRepr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.HashSet.ofList "};
static const lean_object* l_Std_HashSet_instRepr___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_HashSet_instRepr___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_HashSet_instRepr___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_HashSet_instRepr___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_HashSet_instRepr___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_HashSet_instRepr___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_HashSet_emptyWithCapacity___redArg(v_capacity_13_);
lean_dec(v_capacity_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity(lean_object* v_00_u03b1_15_, lean_object* v_inst_16_, lean_object* v_inst_17_, lean_object* v_capacity_18_){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v_cellCount_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_19_ = lean_unsigned_to_nat(4u);
v___x_20_ = lean_nat_mul(v_capacity_18_, v___x_19_);
v___x_21_ = lean_unsigned_to_nat(2u);
v___x_22_ = lean_nat_add(v___x_20_, v___x_21_);
lean_dec(v___x_20_);
v___x_23_ = lean_unsigned_to_nat(3u);
v___x_24_ = lean_nat_div(v___x_22_, v___x_23_);
lean_dec(v___x_22_);
v_cellCount_25_ = l_Nat_nextPowerOfTwo(v___x_24_);
lean_dec(v___x_24_);
v___x_26_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_25_);
v___x_27_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_25_);
v___x_28_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_25_);
v___x_29_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_29_, 0, v___x_26_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
lean_ctor_set(v___x_29_, 2, v___x_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_emptyWithCapacity___boxed(lean_object* v_00_u03b1_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_capacity_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Std_HashSet_emptyWithCapacity(v_00_u03b1_30_, v_inst_31_, v_inst_32_, v_capacity_33_);
lean_dec(v_capacity_33_);
lean_dec_ref(v_inst_32_);
lean_dec_ref(v_inst_31_);
return v_res_34_;
}
}
static lean_object* _init_l_Std_HashSet_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v_cellCount_35_; lean_object* v___x_36_; 
v_cellCount_35_ = lean_unsigned_to_nat(16u);
v___x_36_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_HashSet_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v_cellCount_37_; lean_object* v___x_38_; 
v_cellCount_37_ = lean_unsigned_to_nat(16u);
v___x_38_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_37_);
return v___x_38_;
}
}
static lean_object* _init_l_Std_HashSet_instEmptyCollection___closed__2(void){
_start:
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_39_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__1, &l_Std_HashSet_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_instEmptyCollection___closed__1);
v___x_40_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__0, &l_Std_HashSet_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_instEmptyCollection___closed__0);
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_42_, 0, v___x_41_);
lean_ctor_set(v___x_42_, 1, v___x_40_);
lean_ctor_set(v___x_42_, 2, v___x_39_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection(lean_object* v_00_u03b1_43_, lean_object* v_inst_44_, lean_object* v_inst_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__2, &l_Std_HashSet_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_instEmptyCollection___closed__2);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instEmptyCollection___boxed(lean_object* v_00_u03b1_47_, lean_object* v_inst_48_, lean_object* v_inst_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Std_HashSet_instEmptyCollection(v_00_u03b1_47_, v_inst_48_, v_inst_49_);
lean_dec_ref(v_inst_49_);
lean_dec_ref(v_inst_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited(lean_object* v_00_u03b1_51_, lean_object* v_inst_52_, lean_object* v_inst_53_){
_start:
{
lean_object* v___x_54_; 
v___x_54_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__2, &l_Std_HashSet_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_instEmptyCollection___closed__2);
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInhabited___boxed(lean_object* v_00_u03b1_55_, lean_object* v_inst_56_, lean_object* v_inst_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l_Std_HashSet_instInhabited(v_00_u03b1_55_, v_inst_56_, v_inst_57_);
lean_dec_ref(v_inst_57_);
lean_dec_ref(v_inst_56_);
return v_res_58_;
}
}
static lean_object* _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_97_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__5));
v___x_98_ = l_String_toRawSubstring_x27(v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(lean_object* v_x_119_, lean_object* v_a_120_, lean_object* v_a_121_){
_start:
{
lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_122_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__3));
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
v___x_135_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4));
v___x_136_ = lean_obj_once(&l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6, &l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6_once, _init_l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__6);
v___x_137_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_127_);
lean_inc(v_quotContext_126_);
v___x_138_ = l_Lean_addMacroScope(v_quotContext_126_, v___x_137_, v_currMacroScope_127_);
v___x_139_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__12));
lean_inc_n(v___x_134_, 2);
v___x_140_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_140_, 0, v___x_134_);
lean_ctor_set(v___x_140_, 1, v___x_136_);
lean_ctor_set(v___x_140_, 2, v___x_138_);
lean_ctor_set(v___x_140_, 3, v___x_139_);
v___x_141_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__14));
v___x_142_ = l_Lean_Syntax_node2(v___x_134_, v___x_141_, v___x_130_, v___x_132_);
v___x_143_ = l_Lean_Syntax_node2(v___x_134_, v___x_135_, v___x_140_, v___x_142_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v_a_121_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___boxed(lean_object* v_x_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1(v_x_145_, v_a_146_, v_a_147_);
lean_dec_ref(v_a_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(lean_object* v_x_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v___x_155_; uint8_t v___x_156_; 
v___x_155_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______macroRules__Std__HashSet__term___x7em____1___closed__4));
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
v___x_161_ = ((lean_object*)(l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___closed__1));
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
v___x_176_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__3));
v___x_177_ = ((lean_object*)(l_Std_HashSet_term___x7em___00__closed__6));
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
LEAN_EXPORT lean_object* l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1___boxed(lean_object* v_x_181_, lean_object* v_a_182_, lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Std_HashSet___aux__Std__Data__HashSet__Basic______unexpand__Std__HashSet__Equiv__1(v_x_181_, v_a_182_, v_a_183_);
lean_dec(v_a_182_);
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert___redArg(lean_object* v_x_185_, lean_object* v_x_186_, lean_object* v_m_187_, lean_object* v_a_188_){
_start:
{
lean_object* v___x_189_; lean_object* v___y_191_; lean_object* v_i_192_; lean_object* v___y_198_; lean_object* v___y_208_; lean_object* v_i_209_; lean_object* v___x_224_; 
v___x_189_ = lean_box(0);
lean_inc(v_a_188_);
lean_inc_ref(v_x_186_);
lean_inc_ref(v_x_185_);
v___x_224_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_185_, v_x_186_, v_m_187_, v_a_188_);
switch(lean_obj_tag(v___x_224_))
{
case 0:
{
lean_dec_ref_known(v___x_224_, 3);
lean_dec(v_a_188_);
lean_dec_ref(v_x_186_);
lean_dec_ref(v_x_185_);
return v_m_187_;
}
case 1:
{
lean_object* v_index_225_; lean_object* v_size_226_; lean_object* v_keyArray_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; uint8_t v___x_231_; 
v_index_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_index_225_);
lean_dec_ref_known(v___x_224_, 1);
v_size_226_ = lean_ctor_get(v_m_187_, 0);
v_keyArray_227_ = lean_ctor_get(v_m_187_, 1);
v___x_228_ = lean_unsigned_to_nat(1u);
v___x_229_ = lean_nat_add(v_size_226_, v___x_228_);
v___x_230_ = lean_array_get_size(v_keyArray_227_);
v___x_231_ = lean_nat_dec_lt(v___x_229_, v___x_230_);
if (v___x_231_ == 0)
{
lean_dec(v___x_229_);
lean_dec(v_index_225_);
goto v___jp_214_;
}
else
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_232_ = lean_unsigned_to_nat(4u);
v___x_233_ = lean_nat_mul(v___x_229_, v___x_232_);
v___x_234_ = lean_unsigned_to_nat(3u);
v___x_235_ = lean_nat_mul(v___x_230_, v___x_234_);
v___x_236_ = lean_nat_dec_le(v___x_233_, v___x_235_);
lean_dec(v___x_235_);
lean_dec(v___x_233_);
if (v___x_236_ == 0)
{
lean_dec(v___x_229_);
lean_dec(v_index_225_);
goto v___jp_214_;
}
else
{
lean_object* v___x_237_; 
lean_dec_ref(v_x_186_);
lean_dec_ref(v_x_185_);
v___x_237_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_187_, v___x_229_, v_index_225_, v_a_188_, v___x_189_);
lean_dec(v_index_225_);
return v___x_237_;
}
}
}
default: 
{
lean_object* v_size_238_; lean_object* v_keyArray_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; 
v_size_238_ = lean_ctor_get(v_m_187_, 0);
v_keyArray_239_ = lean_ctor_get(v_m_187_, 1);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = lean_nat_add(v_size_238_, v___x_240_);
v___x_242_ = lean_array_get_size(v_keyArray_239_);
v___x_243_ = lean_nat_dec_lt(v___x_241_, v___x_242_);
if (v___x_243_ == 0)
{
lean_object* v___x_244_; 
lean_dec(v___x_241_);
lean_inc_ref(v_x_186_);
lean_inc_ref(v_x_185_);
v___x_244_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_185_, v_x_186_, v_m_187_);
v___y_198_ = v___x_244_;
goto v___jp_197_;
}
else
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_245_ = lean_unsigned_to_nat(4u);
v___x_246_ = lean_nat_mul(v___x_241_, v___x_245_);
lean_dec(v___x_241_);
v___x_247_ = lean_unsigned_to_nat(3u);
v___x_248_ = lean_nat_mul(v___x_242_, v___x_247_);
v___x_249_ = lean_nat_dec_le(v___x_246_, v___x_248_);
lean_dec(v___x_248_);
lean_dec(v___x_246_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_inc_ref(v_x_186_);
lean_inc_ref(v_x_185_);
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_185_, v_x_186_, v_m_187_);
v___y_198_ = v___x_250_;
goto v___jp_197_;
}
else
{
v___y_198_ = v_m_187_;
goto v___jp_197_;
}
}
}
}
v___jp_190_:
{
lean_object* v_size_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_size_193_ = lean_ctor_get(v___y_191_, 0);
v___x_194_ = lean_unsigned_to_nat(1u);
v___x_195_ = lean_nat_add(v_size_193_, v___x_194_);
v___x_196_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_191_, v___x_195_, v_i_192_, v_a_188_, v___x_189_);
lean_dec(v_i_192_);
return v___x_196_;
}
v___jp_197_:
{
lean_object* v___x_199_; 
lean_inc(v_a_188_);
v___x_199_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_185_, v_x_186_, v___y_198_, v_a_188_);
switch(lean_obj_tag(v___x_199_))
{
case 0:
{
lean_object* v_index_200_; lean_object* v_size_201_; lean_object* v___x_202_; 
v_index_200_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_index_200_);
lean_dec_ref_known(v___x_199_, 3);
v_size_201_ = lean_ctor_get(v___y_198_, 0);
lean_inc(v_size_201_);
v___x_202_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_198_, v_size_201_, v_index_200_, v_a_188_, v___x_189_);
lean_dec(v_index_200_);
return v___x_202_;
}
case 1:
{
lean_object* v_index_203_; 
v_index_203_ = lean_ctor_get(v___x_199_, 0);
lean_inc(v_index_203_);
lean_dec_ref_known(v___x_199_, 1);
v___y_191_ = v___y_198_;
v_i_192_ = v_index_203_;
goto v___jp_190_;
}
default: 
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_198_, v___x_204_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_object* v_index_206_; 
v_index_206_ = lean_ctor_get(v___x_205_, 0);
lean_inc(v_index_206_);
lean_dec_ref_known(v___x_205_, 1);
v___y_191_ = v___y_198_;
v_i_192_ = v_index_206_;
goto v___jp_190_;
}
else
{
lean_dec(v_a_188_);
return v___y_198_;
}
}
}
}
v___jp_207_:
{
lean_object* v_size_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v_size_210_ = lean_ctor_get(v___y_208_, 0);
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_nat_add(v_size_210_, v___x_211_);
v___x_213_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_208_, v___x_212_, v_i_209_, v_a_188_, v___x_189_);
lean_dec(v_i_209_);
return v___x_213_;
}
v___jp_214_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_inc_ref(v_x_186_);
lean_inc_ref(v_x_185_);
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_185_, v_x_186_, v_m_187_);
lean_inc(v_a_188_);
v___x_216_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_185_, v_x_186_, v___x_215_, v_a_188_);
switch(lean_obj_tag(v___x_216_))
{
case 0:
{
lean_object* v_index_217_; lean_object* v_size_218_; lean_object* v___x_219_; 
v_index_217_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_217_);
lean_dec_ref_known(v___x_216_, 3);
v_size_218_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_size_218_);
v___x_219_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_215_, v_size_218_, v_index_217_, v_a_188_, v___x_189_);
lean_dec(v_index_217_);
return v___x_219_;
}
case 1:
{
lean_object* v_index_220_; 
v_index_220_ = lean_ctor_get(v___x_216_, 0);
lean_inc(v_index_220_);
lean_dec_ref_known(v___x_216_, 1);
v___y_208_ = v___x_215_;
v_i_209_ = v_index_220_;
goto v___jp_207_;
}
default: 
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_215_, v___x_221_);
if (lean_obj_tag(v___x_222_) == 0)
{
lean_object* v_index_223_; 
v_index_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_index_223_);
lean_dec_ref_known(v___x_222_, 1);
v___y_208_ = v___x_215_;
v_i_209_ = v_index_223_;
goto v___jp_207_;
}
else
{
lean_dec(v_a_188_);
return v___x_215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insert(lean_object* v_00_u03b1_251_, lean_object* v_x_252_, lean_object* v_x_253_, lean_object* v_m_254_, lean_object* v_a_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___y_258_; lean_object* v_i_259_; lean_object* v___y_265_; lean_object* v___y_275_; lean_object* v_i_276_; lean_object* v___x_291_; 
v___x_256_ = lean_box(0);
lean_inc(v_a_255_);
lean_inc_ref(v_x_253_);
lean_inc_ref(v_x_252_);
v___x_291_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_252_, v_x_253_, v_m_254_, v_a_255_);
switch(lean_obj_tag(v___x_291_))
{
case 0:
{
lean_dec_ref_known(v___x_291_, 3);
lean_dec(v_a_255_);
lean_dec_ref(v_x_253_);
lean_dec_ref(v_x_252_);
return v_m_254_;
}
case 1:
{
lean_object* v_index_292_; lean_object* v_size_293_; lean_object* v_keyArray_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v_index_292_ = lean_ctor_get(v___x_291_, 0);
lean_inc(v_index_292_);
lean_dec_ref_known(v___x_291_, 1);
v_size_293_ = lean_ctor_get(v_m_254_, 0);
v_keyArray_294_ = lean_ctor_get(v_m_254_, 1);
v___x_295_ = lean_unsigned_to_nat(1u);
v___x_296_ = lean_nat_add(v_size_293_, v___x_295_);
v___x_297_ = lean_array_get_size(v_keyArray_294_);
v___x_298_ = lean_nat_dec_lt(v___x_296_, v___x_297_);
if (v___x_298_ == 0)
{
lean_dec(v___x_296_);
lean_dec(v_index_292_);
goto v___jp_281_;
}
else
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_299_ = lean_unsigned_to_nat(4u);
v___x_300_ = lean_nat_mul(v___x_296_, v___x_299_);
v___x_301_ = lean_unsigned_to_nat(3u);
v___x_302_ = lean_nat_mul(v___x_297_, v___x_301_);
v___x_303_ = lean_nat_dec_le(v___x_300_, v___x_302_);
lean_dec(v___x_302_);
lean_dec(v___x_300_);
if (v___x_303_ == 0)
{
lean_dec(v___x_296_);
lean_dec(v_index_292_);
goto v___jp_281_;
}
else
{
lean_object* v___x_304_; 
lean_dec_ref(v_x_253_);
lean_dec_ref(v_x_252_);
v___x_304_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_254_, v___x_296_, v_index_292_, v_a_255_, v___x_256_);
lean_dec(v_index_292_);
return v___x_304_;
}
}
}
default: 
{
lean_object* v_size_305_; lean_object* v_keyArray_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v_size_305_ = lean_ctor_get(v_m_254_, 0);
v_keyArray_306_ = lean_ctor_get(v_m_254_, 1);
v___x_307_ = lean_unsigned_to_nat(1u);
v___x_308_ = lean_nat_add(v_size_305_, v___x_307_);
v___x_309_ = lean_array_get_size(v_keyArray_306_);
v___x_310_ = lean_nat_dec_lt(v___x_308_, v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec(v___x_308_);
lean_inc_ref(v_x_253_);
lean_inc_ref(v_x_252_);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_252_, v_x_253_, v_m_254_);
v___y_265_ = v___x_311_;
goto v___jp_264_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_312_ = lean_unsigned_to_nat(4u);
v___x_313_ = lean_nat_mul(v___x_308_, v___x_312_);
lean_dec(v___x_308_);
v___x_314_ = lean_unsigned_to_nat(3u);
v___x_315_ = lean_nat_mul(v___x_309_, v___x_314_);
v___x_316_ = lean_nat_dec_le(v___x_313_, v___x_315_);
lean_dec(v___x_315_);
lean_dec(v___x_313_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_inc_ref(v_x_253_);
lean_inc_ref(v_x_252_);
v___x_317_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_252_, v_x_253_, v_m_254_);
v___y_265_ = v___x_317_;
goto v___jp_264_;
}
else
{
v___y_265_ = v_m_254_;
goto v___jp_264_;
}
}
}
}
v___jp_257_:
{
lean_object* v_size_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v_size_260_ = lean_ctor_get(v___y_258_, 0);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_add(v_size_260_, v___x_261_);
v___x_263_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_258_, v___x_262_, v_i_259_, v_a_255_, v___x_256_);
lean_dec(v_i_259_);
return v___x_263_;
}
v___jp_264_:
{
lean_object* v___x_266_; 
lean_inc(v_a_255_);
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_252_, v_x_253_, v___y_265_, v_a_255_);
switch(lean_obj_tag(v___x_266_))
{
case 0:
{
lean_object* v_index_267_; lean_object* v_size_268_; lean_object* v___x_269_; 
v_index_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_index_267_);
lean_dec_ref_known(v___x_266_, 3);
v_size_268_ = lean_ctor_get(v___y_265_, 0);
lean_inc(v_size_268_);
v___x_269_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_265_, v_size_268_, v_index_267_, v_a_255_, v___x_256_);
lean_dec(v_index_267_);
return v___x_269_;
}
case 1:
{
lean_object* v_index_270_; 
v_index_270_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_index_270_);
lean_dec_ref_known(v___x_266_, 1);
v___y_258_ = v___y_265_;
v_i_259_ = v_index_270_;
goto v___jp_257_;
}
default: 
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_265_, v___x_271_);
if (lean_obj_tag(v___x_272_) == 0)
{
lean_object* v_index_273_; 
v_index_273_ = lean_ctor_get(v___x_272_, 0);
lean_inc(v_index_273_);
lean_dec_ref_known(v___x_272_, 1);
v___y_258_ = v___y_265_;
v_i_259_ = v_index_273_;
goto v___jp_257_;
}
else
{
lean_dec(v_a_255_);
return v___y_265_;
}
}
}
}
v___jp_274_:
{
lean_object* v_size_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v_size_277_ = lean_ctor_get(v___y_275_, 0);
v___x_278_ = lean_unsigned_to_nat(1u);
v___x_279_ = lean_nat_add(v_size_277_, v___x_278_);
v___x_280_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_275_, v___x_279_, v_i_276_, v_a_255_, v___x_256_);
lean_dec(v_i_276_);
return v___x_280_;
}
v___jp_281_:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
lean_inc_ref(v_x_253_);
lean_inc_ref(v_x_252_);
v___x_282_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_252_, v_x_253_, v_m_254_);
lean_inc(v_a_255_);
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_252_, v_x_253_, v___x_282_, v_a_255_);
switch(lean_obj_tag(v___x_283_))
{
case 0:
{
lean_object* v_index_284_; lean_object* v_size_285_; lean_object* v___x_286_; 
v_index_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_index_284_);
lean_dec_ref_known(v___x_283_, 3);
v_size_285_ = lean_ctor_get(v___x_282_, 0);
lean_inc(v_size_285_);
v___x_286_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_282_, v_size_285_, v_index_284_, v_a_255_, v___x_256_);
lean_dec(v_index_284_);
return v___x_286_;
}
case 1:
{
lean_object* v_index_287_; 
v_index_287_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_index_287_);
lean_dec_ref_known(v___x_283_, 1);
v___y_275_ = v___x_282_;
v_i_276_ = v_index_287_;
goto v___jp_274_;
}
default: 
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_282_, v___x_288_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_index_290_; 
v_index_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_index_290_);
lean_dec_ref_known(v___x_289_, 1);
v___y_275_ = v___x_282_;
v_i_276_ = v_index_290_;
goto v___jp_274_;
}
else
{
lean_dec(v_a_255_);
return v___x_282_;
}
}
}
}
}
}
static lean_object* _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__0, &l_Std_HashSet_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_instEmptyCollection___closed__0);
v___x_319_ = lean_array_get_size(v___x_318_);
return v___x_319_;
}
}
static uint8_t _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_320_ = lean_obj_once(&l_Std_HashSet_instSingleton___redArg___lam__0___closed__0, &l_Std_HashSet_instSingleton___redArg___lam__0___closed__0_once, _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__0);
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = lean_nat_dec_lt(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_unsigned_to_nat(3u);
v___x_324_ = lean_obj_once(&l_Std_HashSet_instSingleton___redArg___lam__0___closed__0, &l_Std_HashSet_instSingleton___redArg___lam__0___closed__0_once, _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__0);
v___x_325_ = lean_nat_mul(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static uint8_t _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_326_ = lean_obj_once(&l_Std_HashSet_instSingleton___redArg___lam__0___closed__2, &l_Std_HashSet_instSingleton___redArg___lam__0___closed__2_once, _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__2);
v___x_327_ = lean_unsigned_to_nat(4u);
v___x_328_ = lean_nat_dec_le(v___x_327_, v___x_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg___lam__0(lean_object* v_x_329_, lean_object* v_x_330_, lean_object* v_a_331_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___y_336_; lean_object* v_i_337_; lean_object* v___y_343_; lean_object* v___y_352_; lean_object* v_i_353_; lean_object* v___x_367_; 
v___x_332_ = lean_unsigned_to_nat(0u);
v___x_333_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__2, &l_Std_HashSet_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_instEmptyCollection___closed__2);
v___x_334_ = lean_box(0);
lean_inc(v_a_331_);
lean_inc_ref(v_x_330_);
lean_inc_ref(v_x_329_);
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_329_, v_x_330_, v___x_333_, v_a_331_);
switch(lean_obj_tag(v___x_367_))
{
case 0:
{
lean_dec_ref_known(v___x_367_, 3);
lean_dec(v_a_331_);
lean_dec_ref(v_x_330_);
lean_dec_ref(v_x_329_);
return v___x_333_;
}
case 1:
{
lean_object* v_index_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_index_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_index_368_);
lean_dec_ref_known(v___x_367_, 1);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_uint8_once(&l_Std_HashSet_instSingleton___redArg___lam__0___closed__1, &l_Std_HashSet_instSingleton___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__1);
if (v___x_370_ == 0)
{
lean_dec(v_index_368_);
goto v___jp_358_;
}
else
{
uint8_t v___x_371_; 
v___x_371_ = lean_uint8_once(&l_Std_HashSet_instSingleton___redArg___lam__0___closed__3, &l_Std_HashSet_instSingleton___redArg___lam__0___closed__3_once, _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__3);
if (v___x_371_ == 0)
{
lean_dec(v_index_368_);
goto v___jp_358_;
}
else
{
lean_object* v___x_372_; 
lean_dec_ref(v_x_330_);
lean_dec_ref(v_x_329_);
v___x_372_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_333_, v___x_369_, v_index_368_, v_a_331_, v___x_334_);
lean_dec(v_index_368_);
return v___x_372_;
}
}
}
default: 
{
uint8_t v___x_373_; 
v___x_373_ = lean_uint8_once(&l_Std_HashSet_instSingleton___redArg___lam__0___closed__1, &l_Std_HashSet_instSingleton___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__1);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_inc_ref(v_x_330_);
lean_inc_ref(v_x_329_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_329_, v_x_330_, v___x_333_);
v___y_343_ = v___x_374_;
goto v___jp_342_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = lean_uint8_once(&l_Std_HashSet_instSingleton___redArg___lam__0___closed__3, &l_Std_HashSet_instSingleton___redArg___lam__0___closed__3_once, _init_l_Std_HashSet_instSingleton___redArg___lam__0___closed__3);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_inc_ref(v_x_330_);
lean_inc_ref(v_x_329_);
v___x_376_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_329_, v_x_330_, v___x_333_);
v___y_343_ = v___x_376_;
goto v___jp_342_;
}
else
{
v___y_343_ = v___x_333_;
goto v___jp_342_;
}
}
}
}
v___jp_335_:
{
lean_object* v_size_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; 
v_size_338_ = lean_ctor_get(v___y_336_, 0);
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_size_338_, v___x_339_);
v___x_341_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_336_, v___x_340_, v_i_337_, v_a_331_, v___x_334_);
lean_dec(v_i_337_);
return v___x_341_;
}
v___jp_342_:
{
lean_object* v___x_344_; 
lean_inc(v_a_331_);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_329_, v_x_330_, v___y_343_, v_a_331_);
switch(lean_obj_tag(v___x_344_))
{
case 0:
{
lean_object* v_index_345_; lean_object* v_size_346_; lean_object* v___x_347_; 
v_index_345_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_index_345_);
lean_dec_ref_known(v___x_344_, 3);
v_size_346_ = lean_ctor_get(v___y_343_, 0);
lean_inc(v_size_346_);
v___x_347_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_343_, v_size_346_, v_index_345_, v_a_331_, v___x_334_);
lean_dec(v_index_345_);
return v___x_347_;
}
case 1:
{
lean_object* v_index_348_; 
v_index_348_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_index_348_);
lean_dec_ref_known(v___x_344_, 1);
v___y_336_ = v___y_343_;
v_i_337_ = v_index_348_;
goto v___jp_335_;
}
default: 
{
lean_object* v___x_349_; 
v___x_349_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_343_, v___x_332_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_index_350_; 
v_index_350_ = lean_ctor_get(v___x_349_, 0);
lean_inc(v_index_350_);
lean_dec_ref_known(v___x_349_, 1);
v___y_336_ = v___y_343_;
v_i_337_ = v_index_350_;
goto v___jp_335_;
}
else
{
lean_dec(v_a_331_);
return v___y_343_;
}
}
}
}
v___jp_351_:
{
lean_object* v_size_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v_size_354_ = lean_ctor_get(v___y_352_, 0);
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_size_354_, v___x_355_);
v___x_357_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_352_, v___x_356_, v_i_353_, v_a_331_, v___x_334_);
lean_dec(v_i_353_);
return v___x_357_;
}
v___jp_358_:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
lean_inc_ref(v_x_330_);
lean_inc_ref(v_x_329_);
v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_329_, v_x_330_, v___x_333_);
lean_inc(v_a_331_);
v___x_360_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_329_, v_x_330_, v___x_359_, v_a_331_);
switch(lean_obj_tag(v___x_360_))
{
case 0:
{
lean_object* v_index_361_; lean_object* v_size_362_; lean_object* v___x_363_; 
v_index_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_index_361_);
lean_dec_ref_known(v___x_360_, 3);
v_size_362_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_size_362_);
v___x_363_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_359_, v_size_362_, v_index_361_, v_a_331_, v___x_334_);
lean_dec(v_index_361_);
return v___x_363_;
}
case 1:
{
lean_object* v_index_364_; 
v_index_364_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_index_364_);
lean_dec_ref_known(v___x_360_, 1);
v___y_352_ = v___x_359_;
v_i_353_ = v_index_364_;
goto v___jp_351_;
}
default: 
{
lean_object* v___x_365_; 
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_359_, v___x_332_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_object* v_index_366_; 
v_index_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_index_366_);
lean_dec_ref_known(v___x_365_, 1);
v___y_352_ = v___x_359_;
v_i_353_ = v_index_366_;
goto v___jp_351_;
}
else
{
lean_dec(v_a_331_);
return v___x_359_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton___redArg(lean_object* v_x_377_, lean_object* v_x_378_){
_start:
{
lean_object* v___f_379_; 
v___f_379_ = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(v___f_379_, 0, v_x_377_);
lean_closure_set(v___f_379_, 1, v_x_378_);
return v___f_379_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSingleton(lean_object* v_00_u03b1_380_, lean_object* v_x_381_, lean_object* v_x_382_){
_start:
{
lean_object* v___f_383_; 
v___f_383_ = lean_alloc_closure((void*)(l_Std_HashSet_instSingleton___redArg___lam__0), 3, 2);
lean_closure_set(v___f_383_, 0, v_x_381_);
lean_closure_set(v___f_383_, 1, v_x_382_);
return v___f_383_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg___lam__0(lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_a_386_, lean_object* v_s_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___y_390_; lean_object* v_i_391_; lean_object* v___y_397_; lean_object* v___y_407_; lean_object* v_i_408_; lean_object* v___x_423_; 
v___x_388_ = lean_box(0);
lean_inc(v_a_386_);
lean_inc_ref(v_x_385_);
lean_inc_ref(v_x_384_);
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_384_, v_x_385_, v_s_387_, v_a_386_);
switch(lean_obj_tag(v___x_423_))
{
case 0:
{
lean_dec_ref_known(v___x_423_, 3);
lean_dec(v_a_386_);
lean_dec_ref(v_x_385_);
lean_dec_ref(v_x_384_);
return v_s_387_;
}
case 1:
{
lean_object* v_index_424_; lean_object* v_size_425_; lean_object* v_keyArray_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_index_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_index_424_);
lean_dec_ref_known(v___x_423_, 1);
v_size_425_ = lean_ctor_get(v_s_387_, 0);
v_keyArray_426_ = lean_ctor_get(v_s_387_, 1);
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_add(v_size_425_, v___x_427_);
v___x_429_ = lean_array_get_size(v_keyArray_426_);
v___x_430_ = lean_nat_dec_lt(v___x_428_, v___x_429_);
if (v___x_430_ == 0)
{
lean_dec(v___x_428_);
lean_dec(v_index_424_);
goto v___jp_413_;
}
else
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v___x_431_ = lean_unsigned_to_nat(4u);
v___x_432_ = lean_nat_mul(v___x_428_, v___x_431_);
v___x_433_ = lean_unsigned_to_nat(3u);
v___x_434_ = lean_nat_mul(v___x_429_, v___x_433_);
v___x_435_ = lean_nat_dec_le(v___x_432_, v___x_434_);
lean_dec(v___x_434_);
lean_dec(v___x_432_);
if (v___x_435_ == 0)
{
lean_dec(v___x_428_);
lean_dec(v_index_424_);
goto v___jp_413_;
}
else
{
lean_object* v___x_436_; 
lean_dec_ref(v_x_385_);
lean_dec_ref(v_x_384_);
v___x_436_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_387_, v___x_428_, v_index_424_, v_a_386_, v___x_388_);
lean_dec(v_index_424_);
return v___x_436_;
}
}
}
default: 
{
lean_object* v_size_437_; lean_object* v_keyArray_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_size_437_ = lean_ctor_get(v_s_387_, 0);
v_keyArray_438_ = lean_ctor_get(v_s_387_, 1);
v___x_439_ = lean_unsigned_to_nat(1u);
v___x_440_ = lean_nat_add(v_size_437_, v___x_439_);
v___x_441_ = lean_array_get_size(v_keyArray_438_);
v___x_442_ = lean_nat_dec_lt(v___x_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_object* v___x_443_; 
lean_dec(v___x_440_);
lean_inc_ref(v_x_385_);
lean_inc_ref(v_x_384_);
v___x_443_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_384_, v_x_385_, v_s_387_);
v___y_397_ = v___x_443_;
goto v___jp_396_;
}
else
{
lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; uint8_t v___x_448_; 
v___x_444_ = lean_unsigned_to_nat(4u);
v___x_445_ = lean_nat_mul(v___x_440_, v___x_444_);
lean_dec(v___x_440_);
v___x_446_ = lean_unsigned_to_nat(3u);
v___x_447_ = lean_nat_mul(v___x_441_, v___x_446_);
v___x_448_ = lean_nat_dec_le(v___x_445_, v___x_447_);
lean_dec(v___x_447_);
lean_dec(v___x_445_);
if (v___x_448_ == 0)
{
lean_object* v___x_449_; 
lean_inc_ref(v_x_385_);
lean_inc_ref(v_x_384_);
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_384_, v_x_385_, v_s_387_);
v___y_397_ = v___x_449_;
goto v___jp_396_;
}
else
{
v___y_397_ = v_s_387_;
goto v___jp_396_;
}
}
}
}
v___jp_389_:
{
lean_object* v_size_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v_size_392_ = lean_ctor_get(v___y_390_, 0);
v___x_393_ = lean_unsigned_to_nat(1u);
v___x_394_ = lean_nat_add(v_size_392_, v___x_393_);
v___x_395_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_390_, v___x_394_, v_i_391_, v_a_386_, v___x_388_);
lean_dec(v_i_391_);
return v___x_395_;
}
v___jp_396_:
{
lean_object* v___x_398_; 
lean_inc(v_a_386_);
v___x_398_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_384_, v_x_385_, v___y_397_, v_a_386_);
switch(lean_obj_tag(v___x_398_))
{
case 0:
{
lean_object* v_index_399_; lean_object* v_size_400_; lean_object* v___x_401_; 
v_index_399_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_index_399_);
lean_dec_ref_known(v___x_398_, 3);
v_size_400_ = lean_ctor_get(v___y_397_, 0);
lean_inc(v_size_400_);
v___x_401_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_397_, v_size_400_, v_index_399_, v_a_386_, v___x_388_);
lean_dec(v_index_399_);
return v___x_401_;
}
case 1:
{
lean_object* v_index_402_; 
v_index_402_ = lean_ctor_get(v___x_398_, 0);
lean_inc(v_index_402_);
lean_dec_ref_known(v___x_398_, 1);
v___y_390_ = v___y_397_;
v_i_391_ = v_index_402_;
goto v___jp_389_;
}
default: 
{
lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_397_, v___x_403_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_index_405_; 
v_index_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_index_405_);
lean_dec_ref_known(v___x_404_, 1);
v___y_390_ = v___y_397_;
v_i_391_ = v_index_405_;
goto v___jp_389_;
}
else
{
lean_dec(v_a_386_);
return v___y_397_;
}
}
}
}
v___jp_406_:
{
lean_object* v_size_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
v_size_409_ = lean_ctor_get(v___y_407_, 0);
v___x_410_ = lean_unsigned_to_nat(1u);
v___x_411_ = lean_nat_add(v_size_409_, v___x_410_);
v___x_412_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_407_, v___x_411_, v_i_408_, v_a_386_, v___x_388_);
lean_dec(v_i_408_);
return v___x_412_;
}
v___jp_413_:
{
lean_object* v___x_414_; lean_object* v___x_415_; 
lean_inc_ref(v_x_385_);
lean_inc_ref(v_x_384_);
v___x_414_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_384_, v_x_385_, v_s_387_);
lean_inc(v_a_386_);
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_384_, v_x_385_, v___x_414_, v_a_386_);
switch(lean_obj_tag(v___x_415_))
{
case 0:
{
lean_object* v_index_416_; lean_object* v_size_417_; lean_object* v___x_418_; 
v_index_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_index_416_);
lean_dec_ref_known(v___x_415_, 3);
v_size_417_ = lean_ctor_get(v___x_414_, 0);
lean_inc(v_size_417_);
v___x_418_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_414_, v_size_417_, v_index_416_, v_a_386_, v___x_388_);
lean_dec(v_index_416_);
return v___x_418_;
}
case 1:
{
lean_object* v_index_419_; 
v_index_419_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_index_419_);
lean_dec_ref_known(v___x_415_, 1);
v___y_407_ = v___x_414_;
v_i_408_ = v_index_419_;
goto v___jp_406_;
}
default: 
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(0u);
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_414_, v___x_420_);
if (lean_obj_tag(v___x_421_) == 0)
{
lean_object* v_index_422_; 
v_index_422_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_index_422_);
lean_dec_ref_known(v___x_421_, 1);
v___y_407_ = v___x_414_;
v_i_408_ = v_index_422_;
goto v___jp_406_;
}
else
{
lean_dec(v_a_386_);
return v___x_414_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert___redArg(lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
lean_object* v___f_452_; 
v___f_452_ = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(v___f_452_, 0, v_x_450_);
lean_closure_set(v___f_452_, 1, v_x_451_);
return v___f_452_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInsert(lean_object* v_00_u03b1_453_, lean_object* v_x_454_, lean_object* v_x_455_){
_start:
{
lean_object* v___f_456_; 
v___f_456_ = lean_alloc_closure((void*)(l_Std_HashSet_instInsert___redArg___lam__0), 4, 2);
lean_closure_set(v___f_456_, 0, v_x_454_);
lean_closure_set(v___f_456_, 1, v_x_455_);
return v___f_456_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert___redArg(lean_object* v_x_457_, lean_object* v_x_458_, lean_object* v_m_459_, lean_object* v_a_460_){
_start:
{
lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_461_ = lean_box(0);
lean_inc(v_a_460_);
lean_inc_ref(v_x_458_);
lean_inc_ref(v_x_457_);
v___x_462_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_457_, v_x_458_, v_m_459_, v_a_460_);
switch(lean_obj_tag(v___x_462_))
{
case 0:
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
lean_dec_ref_known(v___x_462_, 3);
lean_dec(v_a_460_);
lean_dec_ref(v_x_458_);
lean_dec_ref(v_x_457_);
v___x_463_ = 1;
v___x_464_ = lean_box(v___x_463_);
v___x_465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_465_, 0, v___x_464_);
lean_ctor_set(v___x_465_, 1, v_m_459_);
return v___x_465_;
}
case 1:
{
lean_object* v_index_466_; lean_object* v_size_467_; lean_object* v_keyArray_468_; uint8_t v___x_469_; lean_object* v___y_471_; lean_object* v_i_472_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
v_index_466_ = lean_ctor_get(v___x_462_, 0);
lean_inc(v_index_466_);
lean_dec_ref_known(v___x_462_, 1);
v_size_467_ = lean_ctor_get(v_m_459_, 0);
v_keyArray_468_ = lean_ctor_get(v_m_459_, 1);
v___x_469_ = 0;
v___x_493_ = lean_unsigned_to_nat(1u);
v___x_494_ = lean_nat_add(v_size_467_, v___x_493_);
v___x_495_ = lean_array_get_size(v_keyArray_468_);
v___x_496_ = lean_nat_dec_lt(v___x_494_, v___x_495_);
if (v___x_496_ == 0)
{
lean_dec(v___x_494_);
lean_dec(v_index_466_);
goto v___jp_479_;
}
else
{
lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v___x_497_ = lean_unsigned_to_nat(4u);
v___x_498_ = lean_nat_mul(v___x_494_, v___x_497_);
v___x_499_ = lean_unsigned_to_nat(3u);
v___x_500_ = lean_nat_mul(v___x_495_, v___x_499_);
v___x_501_ = lean_nat_dec_le(v___x_498_, v___x_500_);
lean_dec(v___x_500_);
lean_dec(v___x_498_);
if (v___x_501_ == 0)
{
lean_dec(v___x_494_);
lean_dec(v_index_466_);
goto v___jp_479_;
}
else
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec_ref(v_x_458_);
lean_dec_ref(v_x_457_);
v___x_502_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_459_, v___x_494_, v_index_466_, v_a_460_, v___x_461_);
lean_dec(v_index_466_);
v___x_503_ = lean_box(v___x_469_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set(v___x_504_, 1, v___x_502_);
return v___x_504_;
}
}
v___jp_470_:
{
lean_object* v_size_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v_size_473_ = lean_ctor_get(v___y_471_, 0);
v___x_474_ = lean_unsigned_to_nat(1u);
v___x_475_ = lean_nat_add(v_size_473_, v___x_474_);
v___x_476_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_471_, v___x_475_, v_i_472_, v_a_460_, v___x_461_);
lean_dec(v_i_472_);
v___x_477_ = lean_box(v___x_469_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___x_476_);
return v___x_478_;
}
v___jp_479_:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
lean_inc_ref(v_x_458_);
lean_inc_ref(v_x_457_);
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_457_, v_x_458_, v_m_459_);
lean_inc(v_a_460_);
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_457_, v_x_458_, v___x_480_, v_a_460_);
switch(lean_obj_tag(v___x_481_))
{
case 0:
{
lean_object* v_index_482_; lean_object* v_size_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; 
v_index_482_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_index_482_);
lean_dec_ref_known(v___x_481_, 3);
v_size_483_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_size_483_);
v___x_484_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_480_, v_size_483_, v_index_482_, v_a_460_, v___x_461_);
lean_dec(v_index_482_);
v___x_485_ = lean_box(v___x_469_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v___x_484_);
return v___x_486_;
}
case 1:
{
lean_object* v_index_487_; 
v_index_487_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_index_487_);
lean_dec_ref_known(v___x_481_, 1);
v___y_471_ = v___x_480_;
v_i_472_ = v_index_487_;
goto v___jp_470_;
}
default: 
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_480_, v___x_488_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_index_490_; 
v_index_490_ = lean_ctor_get(v___x_489_, 0);
lean_inc(v_index_490_);
lean_dec_ref_known(v___x_489_, 1);
v___y_471_ = v___x_480_;
v_i_472_ = v_index_490_;
goto v___jp_470_;
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; 
lean_dec(v_a_460_);
v___x_491_ = lean_box(v___x_469_);
v___x_492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
lean_ctor_set(v___x_492_, 1, v___x_480_);
return v___x_492_;
}
}
}
}
}
default: 
{
lean_object* v_size_505_; lean_object* v_keyArray_506_; uint8_t v___x_507_; lean_object* v___y_509_; lean_object* v_i_510_; lean_object* v___y_518_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_size_505_ = lean_ctor_get(v_m_459_, 0);
v_keyArray_506_ = lean_ctor_get(v_m_459_, 1);
v___x_507_ = 0;
v___x_531_ = lean_unsigned_to_nat(1u);
v___x_532_ = lean_nat_add(v_size_505_, v___x_531_);
v___x_533_ = lean_array_get_size(v_keyArray_506_);
v___x_534_ = lean_nat_dec_lt(v___x_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; 
lean_dec(v___x_532_);
lean_inc_ref(v_x_458_);
lean_inc_ref(v_x_457_);
v___x_535_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_457_, v_x_458_, v_m_459_);
v___y_518_ = v___x_535_;
goto v___jp_517_;
}
else
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_536_ = lean_unsigned_to_nat(4u);
v___x_537_ = lean_nat_mul(v___x_532_, v___x_536_);
lean_dec(v___x_532_);
v___x_538_ = lean_unsigned_to_nat(3u);
v___x_539_ = lean_nat_mul(v___x_533_, v___x_538_);
v___x_540_ = lean_nat_dec_le(v___x_537_, v___x_539_);
lean_dec(v___x_539_);
lean_dec(v___x_537_);
if (v___x_540_ == 0)
{
lean_object* v___x_541_; 
lean_inc_ref(v_x_458_);
lean_inc_ref(v_x_457_);
v___x_541_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_457_, v_x_458_, v_m_459_);
v___y_518_ = v___x_541_;
goto v___jp_517_;
}
else
{
v___y_518_ = v_m_459_;
goto v___jp_517_;
}
}
v___jp_508_:
{
lean_object* v_size_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_size_511_ = lean_ctor_get(v___y_509_, 0);
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_add(v_size_511_, v___x_512_);
v___x_514_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_509_, v___x_513_, v_i_510_, v_a_460_, v___x_461_);
lean_dec(v_i_510_);
v___x_515_ = lean_box(v___x_507_);
v___x_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_515_);
lean_ctor_set(v___x_516_, 1, v___x_514_);
return v___x_516_;
}
v___jp_517_:
{
lean_object* v___x_519_; 
lean_inc(v_a_460_);
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_457_, v_x_458_, v___y_518_, v_a_460_);
switch(lean_obj_tag(v___x_519_))
{
case 0:
{
lean_object* v_index_520_; lean_object* v_size_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_index_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_index_520_);
lean_dec_ref_known(v___x_519_, 3);
v_size_521_ = lean_ctor_get(v___y_518_, 0);
lean_inc(v_size_521_);
v___x_522_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_518_, v_size_521_, v_index_520_, v_a_460_, v___x_461_);
lean_dec(v_index_520_);
v___x_523_ = lean_box(v___x_507_);
v___x_524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_523_);
lean_ctor_set(v___x_524_, 1, v___x_522_);
return v___x_524_;
}
case 1:
{
lean_object* v_index_525_; 
v_index_525_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_index_525_);
lean_dec_ref_known(v___x_519_, 1);
v___y_509_ = v___y_518_;
v_i_510_ = v_index_525_;
goto v___jp_508_;
}
default: 
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_518_, v___x_526_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_index_528_; 
v_index_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_index_528_);
lean_dec_ref_known(v___x_527_, 1);
v___y_509_ = v___y_518_;
v_i_510_ = v_index_528_;
goto v___jp_508_;
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v_a_460_);
v___x_529_ = lean_box(v___x_507_);
v___x_530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
lean_ctor_set(v___x_530_, 1, v___y_518_);
return v___x_530_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_containsThenInsert(lean_object* v_00_u03b1_542_, lean_object* v_x_543_, lean_object* v_x_544_, lean_object* v_m_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_box(0);
lean_inc(v_a_546_);
lean_inc_ref(v_x_544_);
lean_inc_ref(v_x_543_);
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_543_, v_x_544_, v_m_545_, v_a_546_);
switch(lean_obj_tag(v___x_548_))
{
case 0:
{
uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; 
lean_dec_ref_known(v___x_548_, 3);
lean_dec(v_a_546_);
lean_dec_ref(v_x_544_);
lean_dec_ref(v_x_543_);
v___x_549_ = 1;
v___x_550_ = lean_box(v___x_549_);
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v___x_550_);
lean_ctor_set(v___x_551_, 1, v_m_545_);
return v___x_551_;
}
case 1:
{
lean_object* v_index_552_; lean_object* v_size_553_; lean_object* v_keyArray_554_; uint8_t v___x_555_; lean_object* v___y_557_; lean_object* v_i_558_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_index_552_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_index_552_);
lean_dec_ref_known(v___x_548_, 1);
v_size_553_ = lean_ctor_get(v_m_545_, 0);
v_keyArray_554_ = lean_ctor_get(v_m_545_, 1);
v___x_555_ = 0;
v___x_579_ = lean_unsigned_to_nat(1u);
v___x_580_ = lean_nat_add(v_size_553_, v___x_579_);
v___x_581_ = lean_array_get_size(v_keyArray_554_);
v___x_582_ = lean_nat_dec_lt(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_dec(v___x_580_);
lean_dec(v_index_552_);
goto v___jp_565_;
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_583_ = lean_unsigned_to_nat(4u);
v___x_584_ = lean_nat_mul(v___x_580_, v___x_583_);
v___x_585_ = lean_unsigned_to_nat(3u);
v___x_586_ = lean_nat_mul(v___x_581_, v___x_585_);
v___x_587_ = lean_nat_dec_le(v___x_584_, v___x_586_);
lean_dec(v___x_586_);
lean_dec(v___x_584_);
if (v___x_587_ == 0)
{
lean_dec(v___x_580_);
lean_dec(v_index_552_);
goto v___jp_565_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
lean_dec_ref(v_x_544_);
lean_dec_ref(v_x_543_);
v___x_588_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_545_, v___x_580_, v_index_552_, v_a_546_, v___x_547_);
lean_dec(v_index_552_);
v___x_589_ = lean_box(v___x_555_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
return v___x_590_;
}
}
v___jp_556_:
{
lean_object* v_size_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v_size_559_ = lean_ctor_get(v___y_557_, 0);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_add(v_size_559_, v___x_560_);
v___x_562_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_557_, v___x_561_, v_i_558_, v_a_546_, v___x_547_);
lean_dec(v_i_558_);
v___x_563_ = lean_box(v___x_555_);
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___x_563_);
lean_ctor_set(v___x_564_, 1, v___x_562_);
return v___x_564_;
}
v___jp_565_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_inc_ref(v_x_544_);
lean_inc_ref(v_x_543_);
v___x_566_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_543_, v_x_544_, v_m_545_);
lean_inc(v_a_546_);
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_543_, v_x_544_, v___x_566_, v_a_546_);
switch(lean_obj_tag(v___x_567_))
{
case 0:
{
lean_object* v_index_568_; lean_object* v_size_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_index_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_index_568_);
lean_dec_ref_known(v___x_567_, 3);
v_size_569_ = lean_ctor_get(v___x_566_, 0);
lean_inc(v_size_569_);
v___x_570_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_566_, v_size_569_, v_index_568_, v_a_546_, v___x_547_);
lean_dec(v_index_568_);
v___x_571_ = lean_box(v___x_555_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___x_570_);
return v___x_572_;
}
case 1:
{
lean_object* v_index_573_; 
v_index_573_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_index_573_);
lean_dec_ref_known(v___x_567_, 1);
v___y_557_ = v___x_566_;
v_i_558_ = v_index_573_;
goto v___jp_556_;
}
default: 
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_566_, v___x_574_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v_index_576_; 
v_index_576_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_index_576_);
lean_dec_ref_known(v___x_575_, 1);
v___y_557_ = v___x_566_;
v_i_558_ = v_index_576_;
goto v___jp_556_;
}
else
{
lean_object* v___x_577_; lean_object* v___x_578_; 
lean_dec(v_a_546_);
v___x_577_ = lean_box(v___x_555_);
v___x_578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v___x_566_);
return v___x_578_;
}
}
}
}
}
default: 
{
lean_object* v_size_591_; lean_object* v_keyArray_592_; uint8_t v___x_593_; lean_object* v___y_595_; lean_object* v_i_596_; lean_object* v___y_604_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_size_591_ = lean_ctor_get(v_m_545_, 0);
v_keyArray_592_ = lean_ctor_get(v_m_545_, 1);
v___x_593_ = 0;
v___x_617_ = lean_unsigned_to_nat(1u);
v___x_618_ = lean_nat_add(v_size_591_, v___x_617_);
v___x_619_ = lean_array_get_size(v_keyArray_592_);
v___x_620_ = lean_nat_dec_lt(v___x_618_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; 
lean_dec(v___x_618_);
lean_inc_ref(v_x_544_);
lean_inc_ref(v_x_543_);
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_543_, v_x_544_, v_m_545_);
v___y_604_ = v___x_621_;
goto v___jp_603_;
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v___x_622_ = lean_unsigned_to_nat(4u);
v___x_623_ = lean_nat_mul(v___x_618_, v___x_622_);
lean_dec(v___x_618_);
v___x_624_ = lean_unsigned_to_nat(3u);
v___x_625_ = lean_nat_mul(v___x_619_, v___x_624_);
v___x_626_ = lean_nat_dec_le(v___x_623_, v___x_625_);
lean_dec(v___x_625_);
lean_dec(v___x_623_);
if (v___x_626_ == 0)
{
lean_object* v___x_627_; 
lean_inc_ref(v_x_544_);
lean_inc_ref(v_x_543_);
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_543_, v_x_544_, v_m_545_);
v___y_604_ = v___x_627_;
goto v___jp_603_;
}
else
{
v___y_604_ = v_m_545_;
goto v___jp_603_;
}
}
v___jp_594_:
{
lean_object* v_size_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; 
v_size_597_ = lean_ctor_get(v___y_595_, 0);
v___x_598_ = lean_unsigned_to_nat(1u);
v___x_599_ = lean_nat_add(v_size_597_, v___x_598_);
v___x_600_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_595_, v___x_599_, v_i_596_, v_a_546_, v___x_547_);
lean_dec(v_i_596_);
v___x_601_ = lean_box(v___x_593_);
v___x_602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_602_, 0, v___x_601_);
lean_ctor_set(v___x_602_, 1, v___x_600_);
return v___x_602_;
}
v___jp_603_:
{
lean_object* v___x_605_; 
lean_inc(v_a_546_);
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_543_, v_x_544_, v___y_604_, v_a_546_);
switch(lean_obj_tag(v___x_605_))
{
case 0:
{
lean_object* v_index_606_; lean_object* v_size_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; 
v_index_606_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_index_606_);
lean_dec_ref_known(v___x_605_, 3);
v_size_607_ = lean_ctor_get(v___y_604_, 0);
lean_inc(v_size_607_);
v___x_608_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_604_, v_size_607_, v_index_606_, v_a_546_, v___x_547_);
lean_dec(v_index_606_);
v___x_609_ = lean_box(v___x_593_);
v___x_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_610_, 0, v___x_609_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
return v___x_610_;
}
case 1:
{
lean_object* v_index_611_; 
v_index_611_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_index_611_);
lean_dec_ref_known(v___x_605_, 1);
v___y_595_ = v___y_604_;
v_i_596_ = v_index_611_;
goto v___jp_594_;
}
default: 
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(0u);
v___x_613_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_604_, v___x_612_);
if (lean_obj_tag(v___x_613_) == 0)
{
lean_object* v_index_614_; 
v_index_614_ = lean_ctor_get(v___x_613_, 0);
lean_inc(v_index_614_);
lean_dec_ref_known(v___x_613_, 1);
v___y_595_ = v___y_604_;
v_i_596_ = v_index_614_;
goto v___jp_594_;
}
else
{
lean_object* v___x_615_; lean_object* v___x_616_; 
lean_dec(v_a_546_);
v___x_615_ = lean_box(v___x_593_);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v___y_604_);
return v___x_616_;
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_contains___redArg(lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_m_630_, lean_object* v_a_631_){
_start:
{
uint8_t v___x_632_; 
v___x_632_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_628_, v_x_629_, v_m_630_, v_a_631_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___redArg___boxed(lean_object* v_x_633_, lean_object* v_x_634_, lean_object* v_m_635_, lean_object* v_a_636_){
_start:
{
uint8_t v_res_637_; lean_object* v_r_638_; 
v_res_637_ = l_Std_HashSet_contains___redArg(v_x_633_, v_x_634_, v_m_635_, v_a_636_);
lean_dec_ref(v_m_635_);
v_r_638_ = lean_box(v_res_637_);
return v_r_638_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_contains(lean_object* v_00_u03b1_639_, lean_object* v_x_640_, lean_object* v_x_641_, lean_object* v_m_642_, lean_object* v_a_643_){
_start:
{
uint8_t v___x_644_; 
v___x_644_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_x_640_, v_x_641_, v_m_642_, v_a_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_contains___boxed(lean_object* v_00_u03b1_645_, lean_object* v_x_646_, lean_object* v_x_647_, lean_object* v_m_648_, lean_object* v_a_649_){
_start:
{
uint8_t v_res_650_; lean_object* v_r_651_; 
v_res_650_ = l_Std_HashSet_contains(v_00_u03b1_645_, v_x_646_, v_x_647_, v_m_648_, v_a_649_);
lean_dec_ref(v_m_648_);
v_r_651_ = lean_box(v_res_650_);
return v_r_651_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership(lean_object* v_00_u03b1_652_, lean_object* v_inst_653_, lean_object* v_inst_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = lean_box(0);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instMembership___boxed(lean_object* v_00_u03b1_656_, lean_object* v_inst_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l_Std_HashSet_instMembership(v_00_u03b1_656_, v_inst_657_, v_inst_658_);
lean_dec_ref(v_inst_658_);
lean_dec_ref(v_inst_657_);
return v_res_659_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem___redArg(lean_object* v_inst_660_, lean_object* v_inst_661_, lean_object* v_m_662_, lean_object* v_a_663_){
_start:
{
uint8_t v___x_664_; 
v___x_664_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_660_, v_inst_661_, v_m_662_, v_a_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___redArg___boxed(lean_object* v_inst_665_, lean_object* v_inst_666_, lean_object* v_m_667_, lean_object* v_a_668_){
_start:
{
uint8_t v_res_669_; lean_object* v_r_670_; 
v_res_669_ = l_Std_HashSet_instDecidableMem___redArg(v_inst_665_, v_inst_666_, v_m_667_, v_a_668_);
lean_dec_ref(v_m_667_);
v_r_670_ = lean_box(v_res_669_);
return v_r_670_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_instDecidableMem(lean_object* v_00_u03b1_671_, lean_object* v_inst_672_, lean_object* v_inst_673_, lean_object* v_m_674_, lean_object* v_a_675_){
_start:
{
uint8_t v___x_676_; 
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_672_, v_inst_673_, v_m_674_, v_a_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instDecidableMem___boxed(lean_object* v_00_u03b1_677_, lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_m_680_, lean_object* v_a_681_){
_start:
{
uint8_t v_res_682_; lean_object* v_r_683_; 
v_res_682_ = l_Std_HashSet_instDecidableMem(v_00_u03b1_677_, v_inst_678_, v_inst_679_, v_m_680_, v_a_681_);
lean_dec_ref(v_m_680_);
v_r_683_ = lean_box(v_res_682_);
return v_r_683_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase___redArg(lean_object* v_x_684_, lean_object* v_x_685_, lean_object* v_m_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_684_, v_x_685_, v_m_686_, v_a_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_erase(lean_object* v_00_u03b1_689_, lean_object* v_x_690_, lean_object* v_x_691_, lean_object* v_m_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_694_; 
v___x_694_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_x_690_, v_x_691_, v_m_692_, v_a_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg(lean_object* v_m_695_){
_start:
{
lean_object* v_size_696_; 
v_size_696_ = lean_ctor_get(v_m_695_, 0);
lean_inc(v_size_696_);
return v_size_696_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___redArg___boxed(lean_object* v_m_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_HashSet_size___redArg(v_m_697_);
lean_dec_ref(v_m_697_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size(lean_object* v_00_u03b1_699_, lean_object* v_x_700_, lean_object* v_x_701_, lean_object* v_m_702_){
_start:
{
lean_object* v_size_703_; 
v_size_703_ = lean_ctor_get(v_m_702_, 0);
lean_inc(v_size_703_);
return v_size_703_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_size___boxed(lean_object* v_00_u03b1_704_, lean_object* v_x_705_, lean_object* v_x_706_, lean_object* v_m_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Std_HashSet_size(v_00_u03b1_704_, v_x_705_, v_x_706_, v_m_707_);
lean_dec_ref(v_m_707_);
lean_dec_ref(v_x_706_);
lean_dec_ref(v_x_705_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg(lean_object* v_x_709_, lean_object* v_x_710_, lean_object* v_m_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_709_, v_x_710_, v_m_711_, v_a_712_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___redArg___boxed(lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v_m_716_, lean_object* v_a_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_HashSet_get_x3f___redArg(v_x_714_, v_x_715_, v_m_716_, v_a_717_);
lean_dec_ref(v_m_716_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f(lean_object* v_00_u03b1_719_, lean_object* v_x_720_, lean_object* v_x_721_, lean_object* v_m_722_, lean_object* v_a_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_x_720_, v_x_721_, v_m_722_, v_a_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x3f___boxed(lean_object* v_00_u03b1_725_, lean_object* v_x_726_, lean_object* v_x_727_, lean_object* v_m_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_HashSet_get_x3f(v_00_u03b1_725_, v_x_726_, v_x_727_, v_m_728_, v_a_729_);
lean_dec_ref(v_m_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg(lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_m_733_, lean_object* v_a_734_){
_start:
{
lean_object* v___x_735_; lean_object* v_val_736_; 
v___x_735_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_731_, v_inst_732_, v_m_733_, v_a_734_);
v_val_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_val_736_);
lean_dec(v___x_735_);
return v_val_736_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___redArg___boxed(lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_m_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_HashSet_get___redArg(v_inst_737_, v_inst_738_, v_m_739_, v_a_740_);
lean_dec_ref(v_m_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get(lean_object* v_00_u03b1_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_m_745_, lean_object* v_a_746_, lean_object* v_h_747_){
_start:
{
lean_object* v___x_748_; lean_object* v_val_749_; 
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_743_, v_inst_744_, v_m_745_, v_a_746_);
v_val_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_val_749_);
lean_dec(v___x_748_);
return v_val_749_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get___boxed(lean_object* v_00_u03b1_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_m_753_, lean_object* v_a_754_, lean_object* v_h_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_HashSet_get(v_00_u03b1_750_, v_inst_751_, v_inst_752_, v_m_753_, v_a_754_, v_h_755_);
lean_dec_ref(v_m_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg(lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_m_759_, lean_object* v_a_760_, lean_object* v_fallback_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_757_, v_inst_758_, v_m_759_, v_a_760_, v_fallback_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___redArg___boxed(lean_object* v_inst_763_, lean_object* v_inst_764_, lean_object* v_m_765_, lean_object* v_a_766_, lean_object* v_fallback_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Std_HashSet_getD___redArg(v_inst_763_, v_inst_764_, v_m_765_, v_a_766_, v_fallback_767_);
lean_dec(v_fallback_767_);
lean_dec_ref(v_m_765_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD(lean_object* v_00_u03b1_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_m_772_, lean_object* v_a_773_, lean_object* v_fallback_774_){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_770_, v_inst_771_, v_m_772_, v_a_773_, v_fallback_774_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_getD___boxed(lean_object* v_00_u03b1_776_, lean_object* v_inst_777_, lean_object* v_inst_778_, lean_object* v_m_779_, lean_object* v_a_780_, lean_object* v_fallback_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Std_HashSet_getD(v_00_u03b1_776_, v_inst_777_, v_inst_778_, v_m_779_, v_a_780_, v_fallback_781_);
lean_dec(v_fallback_781_);
lean_dec_ref(v_m_779_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg(lean_object* v_inst_783_, lean_object* v_inst_784_, lean_object* v_inst_785_, lean_object* v_m_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_783_, v_inst_784_, v_inst_785_, v_m_786_, v_a_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___redArg___boxed(lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_, lean_object* v_m_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_Std_HashSet_get_x21___redArg(v_inst_789_, v_inst_790_, v_inst_791_, v_m_792_, v_a_793_);
lean_dec_ref(v_m_792_);
lean_dec(v_inst_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21(lean_object* v_00_u03b1_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_m_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_796_, v_inst_797_, v_inst_798_, v_m_799_, v_a_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_get_x21___boxed(lean_object* v_00_u03b1_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_, lean_object* v_m_806_, lean_object* v_a_807_){
_start:
{
lean_object* v_res_808_; 
v_res_808_ = l_Std_HashSet_get_x21(v_00_u03b1_802_, v_inst_803_, v_inst_804_, v_inst_805_, v_m_806_, v_a_807_);
lean_dec_ref(v_m_806_);
lean_dec(v_inst_805_);
return v_res_808_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty___redArg(lean_object* v_m_809_){
_start:
{
lean_object* v_size_810_; lean_object* v___x_811_; uint8_t v___x_812_; 
v_size_810_ = lean_ctor_get(v_m_809_, 0);
v___x_811_ = lean_unsigned_to_nat(0u);
v___x_812_ = lean_nat_dec_eq(v_size_810_, v___x_811_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___redArg___boxed(lean_object* v_m_813_){
_start:
{
uint8_t v_res_814_; lean_object* v_r_815_; 
v_res_814_ = l_Std_HashSet_isEmpty___redArg(v_m_813_);
lean_dec_ref(v_m_813_);
v_r_815_ = lean_box(v_res_814_);
return v_r_815_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_isEmpty(lean_object* v_00_u03b1_816_, lean_object* v_x_817_, lean_object* v_x_818_, lean_object* v_m_819_){
_start:
{
lean_object* v_size_820_; lean_object* v___x_821_; uint8_t v___x_822_; 
v_size_820_ = lean_ctor_get(v_m_819_, 0);
v___x_821_ = lean_unsigned_to_nat(0u);
v___x_822_ = lean_nat_dec_eq(v_size_820_, v___x_821_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_isEmpty___boxed(lean_object* v_00_u03b1_823_, lean_object* v_x_824_, lean_object* v_x_825_, lean_object* v_m_826_){
_start:
{
uint8_t v_res_827_; lean_object* v_r_828_; 
v_res_827_ = l_Std_HashSet_isEmpty(v_00_u03b1_823_, v_x_824_, v_x_825_, v_m_826_);
lean_dec_ref(v_m_826_);
lean_dec_ref(v_x_825_);
lean_dec_ref(v_x_824_);
v_r_828_ = lean_box(v_res_827_);
return v_r_828_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___lam__0(lean_object* v_x1_829_, lean_object* v_x2_830_, lean_object* v_x3_831_){
_start:
{
lean_object* v___x_832_; 
v___x_832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_832_, 0, v_x2_830_);
lean_ctor_set(v___x_832_, 1, v_x1_829_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg(lean_object* v_m_853_){
_start:
{
lean_object* v___f_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___f_854_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__0));
v___x_855_ = lean_box(0);
v___x_856_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_856_, v___f_854_, v_m_853_, v___x_855_, v___x_857_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___redArg___boxed(lean_object* v_m_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l_Std_HashSet_toList___redArg(v_m_859_);
lean_dec_ref(v_m_859_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList(lean_object* v_00_u03b1_861_, lean_object* v_x_862_, lean_object* v_x_863_, lean_object* v_m_864_){
_start:
{
lean_object* v___f_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v___f_865_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__0));
v___x_866_ = lean_box(0);
v___x_867_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_868_ = lean_unsigned_to_nat(0u);
v___x_869_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_867_, v___f_865_, v_m_864_, v___x_866_, v___x_868_);
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toList___boxed(lean_object* v_00_u03b1_870_, lean_object* v_x_871_, lean_object* v_x_872_, lean_object* v_m_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l_Std_HashSet_toList(v_00_u03b1_870_, v_x_871_, v_x_872_, v_m_873_);
lean_dec_ref(v_m_873_);
lean_dec_ref(v_x_872_);
lean_dec_ref(v_x_871_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList___redArg(lean_object* v_inst_879_, lean_object* v_inst_880_, lean_object* v_l_881_){
_start:
{
lean_object* v___f_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___f_882_ = ((lean_object*)(l_Std_HashSet_ofList___redArg___closed__1));
v___x_883_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__2, &l_Std_HashSet_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_instEmptyCollection___closed__2);
v___x_884_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_882_, v_inst_879_, v_inst_880_, v___x_883_, v_l_881_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofList(lean_object* v_00_u03b1_885_, lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v_l_888_){
_start:
{
lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___f_889_ = ((lean_object*)(l_Std_HashSet_ofList___redArg___closed__1));
v___x_890_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__2, &l_Std_HashSet_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_instEmptyCollection___closed__2);
v___x_891_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_889_, v_inst_886_, v_inst_887_, v___x_890_, v_l_888_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg___lam__0(lean_object* v_f_892_, lean_object* v_b_893_, lean_object* v_a_894_, lean_object* v_x_895_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = lean_apply_2(v_f_892_, v_b_893_, v_a_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___redArg(lean_object* v_inst_897_, lean_object* v_f_898_, lean_object* v_init_899_, lean_object* v_b_900_){
_start:
{
lean_object* v___f_901_; lean_object* v___x_902_; 
v___f_901_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_901_, 0, v_f_898_);
v___x_902_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_897_, v___f_901_, v_init_899_, v_b_900_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM(lean_object* v_00_u03b1_903_, lean_object* v_x_904_, lean_object* v_x_905_, lean_object* v_m_906_, lean_object* v_inst_907_, lean_object* v_00_u03b2_908_, lean_object* v_f_909_, lean_object* v_init_910_, lean_object* v_b_911_){
_start:
{
lean_object* v___f_912_; lean_object* v___x_913_; 
v___f_912_ = lean_alloc_closure((void*)(l_Std_HashSet_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_912_, 0, v_f_909_);
v___x_913_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_907_, v___f_912_, v_init_910_, v_b_911_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_foldM___boxed(lean_object* v_00_u03b1_914_, lean_object* v_x_915_, lean_object* v_x_916_, lean_object* v_m_917_, lean_object* v_inst_918_, lean_object* v_00_u03b2_919_, lean_object* v_f_920_, lean_object* v_init_921_, lean_object* v_b_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Std_HashSet_foldM(v_00_u03b1_914_, v_x_915_, v_x_916_, v_m_917_, v_inst_918_, v_00_u03b2_919_, v_f_920_, v_init_921_, v_b_922_);
lean_dec_ref(v_x_916_);
lean_dec_ref(v_x_915_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg___lam__0(lean_object* v_f_924_, lean_object* v_x1_925_, lean_object* v_x2_926_, lean_object* v_x3_927_){
_start:
{
lean_object* v___x_928_; 
v___x_928_ = lean_apply_2(v_f_924_, v_x1_925_, v_x2_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___redArg(lean_object* v_f_929_, lean_object* v_init_930_, lean_object* v_m_931_){
_start:
{
lean_object* v___f_932_; lean_object* v___x_933_; lean_object* v___x_934_; 
v___f_932_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_932_, 0, v_f_929_);
v___x_933_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_934_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_933_, v___f_932_, v_init_930_, v_m_931_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold(lean_object* v_00_u03b1_935_, lean_object* v_x_936_, lean_object* v_x_937_, lean_object* v_00_u03b2_938_, lean_object* v_f_939_, lean_object* v_init_940_, lean_object* v_m_941_){
_start:
{
lean_object* v___f_942_; lean_object* v___x_943_; lean_object* v___x_944_; 
v___f_942_ = lean_alloc_closure((void*)(l_Std_HashSet_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_942_, 0, v_f_939_);
v___x_943_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_944_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_943_, v___f_942_, v_init_940_, v_m_941_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_fold___boxed(lean_object* v_00_u03b1_945_, lean_object* v_x_946_, lean_object* v_x_947_, lean_object* v_00_u03b2_948_, lean_object* v_f_949_, lean_object* v_init_950_, lean_object* v_m_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Std_HashSet_fold(v_00_u03b1_945_, v_x_946_, v_x_947_, v_00_u03b2_948_, v_f_949_, v_init_950_, v_m_951_);
lean_dec_ref(v_x_947_);
lean_dec_ref(v_x_946_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg___lam__0(lean_object* v_f_953_, lean_object* v_x_954_, lean_object* v_a_955_, lean_object* v_v_956_){
_start:
{
lean_object* v___x_957_; 
v___x_957_ = lean_apply_1(v_f_953_, v_a_955_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___redArg(lean_object* v_inst_958_, lean_object* v_f_959_, lean_object* v_b_960_){
_start:
{
lean_object* v___f_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___f_961_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_961_, 0, v_f_959_);
v___x_962_ = lean_box(0);
v___x_963_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_958_, v___f_961_, v___x_962_, v_b_960_);
return v___x_963_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM(lean_object* v_00_u03b1_964_, lean_object* v_x_965_, lean_object* v_x_966_, lean_object* v_m_967_, lean_object* v_inst_968_, lean_object* v_f_969_, lean_object* v_b_970_){
_start:
{
lean_object* v___f_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___f_971_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_971_, 0, v_f_969_);
v___x_972_ = lean_box(0);
v___x_973_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_968_, v___f_971_, v___x_972_, v_b_970_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forM___boxed(lean_object* v_00_u03b1_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_m_977_, lean_object* v_inst_978_, lean_object* v_f_979_, lean_object* v_b_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_HashSet_forM(v_00_u03b1_974_, v_x_975_, v_x_976_, v_m_977_, v_inst_978_, v_f_979_, v_b_980_);
lean_dec_ref(v_x_976_);
lean_dec_ref(v_x_975_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg___lam__0(lean_object* v_f_982_, lean_object* v_a_983_, lean_object* v_x_984_, lean_object* v_acc_985_){
_start:
{
lean_object* v___x_986_; 
v___x_986_ = lean_apply_2(v_f_982_, v_a_983_, v_acc_985_);
return v___x_986_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___redArg(lean_object* v_inst_987_, lean_object* v_f_988_, lean_object* v_init_989_, lean_object* v_b_990_){
_start:
{
lean_object* v___f_991_; lean_object* v___x_992_; 
v___f_991_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_991_, 0, v_f_988_);
v___x_992_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_987_, v___f_991_, v_init_989_, v_b_990_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn(lean_object* v_00_u03b1_993_, lean_object* v_x_994_, lean_object* v_x_995_, lean_object* v_m_996_, lean_object* v_inst_997_, lean_object* v_00_u03b2_998_, lean_object* v_f_999_, lean_object* v_init_1000_, lean_object* v_b_1001_){
_start:
{
lean_object* v___f_1002_; lean_object* v___x_1003_; 
v___f_1002_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1002_, 0, v_f_999_);
v___x_1003_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_997_, v___f_1002_, v_init_1000_, v_b_1001_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_forIn___boxed(lean_object* v_00_u03b1_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_m_1007_, lean_object* v_inst_1008_, lean_object* v_00_u03b2_1009_, lean_object* v_f_1010_, lean_object* v_init_1011_, lean_object* v_b_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l_Std_HashSet_forIn(v_00_u03b1_1004_, v_x_1005_, v_x_1006_, v_m_1007_, v_inst_1008_, v_00_u03b2_1009_, v_f_1010_, v_init_1011_, v_b_1012_);
lean_dec_ref(v_x_1006_);
lean_dec_ref(v_x_1005_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg___lam__1(lean_object* v_inst_1014_, lean_object* v_m_1015_, lean_object* v_f_1016_){
_start:
{
lean_object* v___f_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___f_1017_ = lean_alloc_closure((void*)(l_Std_HashSet_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1017_, 0, v_f_1016_);
v___x_1018_ = lean_box(0);
v___x_1019_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1014_, v___f_1017_, v___x_1018_, v_m_1015_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___redArg(lean_object* v_inst_1020_){
_start:
{
lean_object* v___f_1021_; 
v___f_1021_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1021_, 0, v_inst_1020_);
return v___f_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad(lean_object* v_00_u03b1_1022_, lean_object* v_inst_1023_, lean_object* v_inst_1024_, lean_object* v_m_1025_, lean_object* v_inst_1026_){
_start:
{
lean_object* v___f_1027_; 
v___f_1027_ = lean_alloc_closure((void*)(l_Std_HashSet_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1027_, 0, v_inst_1026_);
return v___f_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForMOfMonad___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_inst_1029_, lean_object* v_inst_1030_, lean_object* v_m_1031_, lean_object* v_inst_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Std_HashSet_instForMOfMonad(v_00_u03b1_1028_, v_inst_1029_, v_inst_1030_, v_m_1031_, v_inst_1032_);
lean_dec_ref(v_inst_1030_);
lean_dec_ref(v_inst_1029_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg___lam__1(lean_object* v_inst_1034_, lean_object* v_00_u03b2_1035_, lean_object* v_m_1036_, lean_object* v_init_1037_, lean_object* v_f_1038_){
_start:
{
lean_object* v___f_1039_; lean_object* v___x_1040_; 
v___f_1039_ = lean_alloc_closure((void*)(l_Std_HashSet_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1039_, 0, v_f_1038_);
v___x_1040_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_1034_, v___f_1039_, v_init_1037_, v_m_1036_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___redArg(lean_object* v_inst_1041_){
_start:
{
lean_object* v___f_1042_; 
v___f_1042_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1042_, 0, v_inst_1041_);
return v___f_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad(lean_object* v_00_u03b1_1043_, lean_object* v_inst_1044_, lean_object* v_inst_1045_, lean_object* v_m_1046_, lean_object* v_inst_1047_){
_start:
{
lean_object* v___f_1048_; 
v___f_1048_ = lean_alloc_closure((void*)(l_Std_HashSet_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1048_, 0, v_inst_1047_);
return v___f_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instForInOfMonad___boxed(lean_object* v_00_u03b1_1049_, lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_m_1052_, lean_object* v_inst_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Std_HashSet_instForInOfMonad(v_00_u03b1_1049_, v_inst_1050_, v_inst_1051_, v_m_1052_, v_inst_1053_);
lean_dec_ref(v_inst_1051_);
lean_dec_ref(v_inst_1050_);
return v_res_1054_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_filter___redArg___lam__0(lean_object* v_f_1055_, lean_object* v_a_1056_, lean_object* v_x_1057_){
_start:
{
lean_object* v___x_1058_; uint8_t v___x_1059_; 
v___x_1058_ = lean_apply_1(v_f_1055_, v_a_1056_);
v___x_1059_ = lean_unbox(v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___lam__0___boxed(lean_object* v_f_1060_, lean_object* v_a_1061_, lean_object* v_x_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l_Std_HashSet_filter___redArg___lam__0(v_f_1060_, v_a_1061_, v_x_1062_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg(lean_object* v_f_1065_, lean_object* v_m_1066_){
_start:
{
lean_object* v___f_1067_; lean_object* v___x_1068_; 
v___f_1067_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1067_, 0, v_f_1065_);
v___x_1068_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1067_, v_m_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___redArg___boxed(lean_object* v_f_1069_, lean_object* v_m_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Std_HashSet_filter___redArg(v_f_1069_, v_m_1070_);
lean_dec_ref(v_m_1070_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter(lean_object* v_00_u03b1_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_, lean_object* v_f_1075_, lean_object* v_m_1076_){
_start:
{
lean_object* v___f_1077_; lean_object* v___x_1078_; 
v___f_1077_ = lean_alloc_closure((void*)(l_Std_HashSet_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1077_, 0, v_f_1075_);
v___x_1078_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1077_, v_m_1076_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_filter___boxed(lean_object* v_00_u03b1_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_f_1082_, lean_object* v_m_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Std_HashSet_filter(v_00_u03b1_1079_, v_x_1080_, v_x_1081_, v_f_1082_, v_m_1083_);
lean_dec_ref(v_m_1083_);
lean_dec_ref(v_x_1081_);
lean_dec_ref(v_x_1080_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany___redArg(lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_inst_1087_, lean_object* v_m_1088_, lean_object* v_l_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1087_, v_x_1085_, v_x_1086_, v_m_1088_, v_l_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_insertMany(lean_object* v_00_u03b1_1091_, lean_object* v_x_1092_, lean_object* v_x_1093_, lean_object* v_00_u03c1_1094_, lean_object* v_inst_1095_, lean_object* v_m_1096_, lean_object* v_l_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1095_, v_x_1092_, v_x_1093_, v_m_1096_, v_l_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg___lam__0(lean_object* v_x1_1099_, lean_object* v_x2_1100_, lean_object* v_x3_1101_){
_start:
{
lean_object* v___x_1102_; 
v___x_1102_ = lean_array_push(v_x1_1099_, v_x2_1100_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___redArg(lean_object* v_m_1104_){
_start:
{
lean_object* v_size_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v_size_1105_ = lean_ctor_get(v_m_1104_, 0);
v___f_1106_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__0));
v___x_1107_ = lean_mk_empty_array_with_capacity(v_size_1105_);
v___x_1108_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1109_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1108_, v___f_1106_, v___x_1107_, v_m_1104_);
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray(lean_object* v_00_u03b1_1110_, lean_object* v_x_1111_, lean_object* v_x_1112_, lean_object* v_m_1113_){
_start:
{
lean_object* v_size_1114_; lean_object* v___f_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_size_1114_ = lean_ctor_get(v_m_1113_, 0);
v___f_1115_ = ((lean_object*)(l_Std_HashSet_toArray___redArg___closed__0));
v___x_1116_ = lean_mk_empty_array_with_capacity(v_size_1114_);
v___x_1117_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1118_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1117_, v___f_1115_, v___x_1116_, v_m_1113_);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_toArray___boxed(lean_object* v_00_u03b1_1119_, lean_object* v_x_1120_, lean_object* v_x_1121_, lean_object* v_m_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_HashSet_toArray(v_00_u03b1_1119_, v_x_1120_, v_x_1121_, v_m_1122_);
lean_dec_ref(v_x_1121_);
lean_dec_ref(v_x_1120_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0(lean_object* v_p_1124_, lean_object* v___x_1125_, lean_object* v___x_1126_, lean_object* v_a_1127_, lean_object* v_b_1128_, lean_object* v_acc_1129_){
_start:
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = lean_apply_1(v_p_1124_, v_a_1127_);
v___x_1131_ = lean_unbox(v___x_1130_);
if (v___x_1131_ == 0)
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v___x_1126_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v___x_1125_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
else
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1126_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___lam__0___boxed(lean_object* v_p_1136_, lean_object* v___x_1137_, lean_object* v___x_1138_, lean_object* v_a_1139_, lean_object* v_b_1140_, lean_object* v_acc_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_HashSet_all___redArg___lam__0(v_p_1136_, v___x_1137_, v___x_1138_, v_a_1139_, v_b_1140_, v_acc_1141_);
lean_dec_ref(v_acc_1141_);
return v_res_1142_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all___redArg(lean_object* v_m_1146_, lean_object* v_p_1147_){
_start:
{
lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___f_1151_; lean_object* v___x_1152_; lean_object* v_fst_1153_; 
v___x_1148_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1149_ = lean_box(0);
v___x_1150_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1151_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1151_, 0, v_p_1147_);
lean_closure_set(v___f_1151_, 1, v___x_1149_);
lean_closure_set(v___f_1151_, 2, v___x_1150_);
v___x_1152_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1148_, v___f_1151_, v___x_1150_, v_m_1146_);
v_fst_1153_ = lean_ctor_get(v___x_1152_, 0);
lean_inc(v_fst_1153_);
lean_dec(v___x_1152_);
if (lean_obj_tag(v_fst_1153_) == 0)
{
uint8_t v___x_1154_; 
v___x_1154_ = 1;
return v___x_1154_;
}
else
{
lean_object* v_val_1155_; uint8_t v___x_1156_; 
v_val_1155_ = lean_ctor_get(v_fst_1153_, 0);
lean_inc(v_val_1155_);
lean_dec_ref_known(v_fst_1153_, 1);
v___x_1156_ = lean_unbox(v_val_1155_);
lean_dec(v_val_1155_);
return v___x_1156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___redArg___boxed(lean_object* v_m_1157_, lean_object* v_p_1158_){
_start:
{
uint8_t v_res_1159_; lean_object* v_r_1160_; 
v_res_1159_ = l_Std_HashSet_all___redArg(v_m_1157_, v_p_1158_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_all(lean_object* v_00_u03b1_1161_, lean_object* v_x_1162_, lean_object* v_x_1163_, lean_object* v_m_1164_, lean_object* v_p_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___f_1169_; lean_object* v___x_1170_; lean_object* v_fst_1171_; 
v___x_1166_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1167_ = lean_box(0);
v___x_1168_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1169_ = lean_alloc_closure((void*)(l_Std_HashSet_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1169_, 0, v_p_1165_);
lean_closure_set(v___f_1169_, 1, v___x_1167_);
lean_closure_set(v___f_1169_, 2, v___x_1168_);
v___x_1170_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1166_, v___f_1169_, v___x_1168_, v_m_1164_);
v_fst_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_fst_1171_);
lean_dec(v___x_1170_);
if (lean_obj_tag(v_fst_1171_) == 0)
{
uint8_t v___x_1172_; 
v___x_1172_ = 1;
return v___x_1172_;
}
else
{
lean_object* v_val_1173_; uint8_t v___x_1174_; 
v_val_1173_ = lean_ctor_get(v_fst_1171_, 0);
lean_inc(v_val_1173_);
lean_dec_ref_known(v_fst_1171_, 1);
v___x_1174_ = lean_unbox(v_val_1173_);
lean_dec(v_val_1173_);
return v___x_1174_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_all___boxed(lean_object* v_00_u03b1_1175_, lean_object* v_x_1176_, lean_object* v_x_1177_, lean_object* v_m_1178_, lean_object* v_p_1179_){
_start:
{
uint8_t v_res_1180_; lean_object* v_r_1181_; 
v_res_1180_ = l_Std_HashSet_all(v_00_u03b1_1175_, v_x_1176_, v_x_1177_, v_m_1178_, v_p_1179_);
lean_dec_ref(v_x_1177_);
lean_dec_ref(v_x_1176_);
v_r_1181_ = lean_box(v_res_1180_);
return v_r_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0(lean_object* v_p_1182_, lean_object* v___x_1183_, lean_object* v___x_1184_, lean_object* v_a_1185_, lean_object* v_b_1186_, lean_object* v_acc_1187_){
_start:
{
lean_object* v___x_1188_; uint8_t v___x_1189_; 
v___x_1188_ = lean_apply_1(v_p_1182_, v_a_1185_);
v___x_1189_ = lean_unbox(v___x_1188_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1190_, 0, v___x_1183_);
return v___x_1190_;
}
else
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
lean_dec_ref(v___x_1183_);
v___x_1191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1188_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1191_);
lean_ctor_set(v___x_1192_, 1, v___x_1184_);
v___x_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1192_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___lam__0___boxed(lean_object* v_p_1194_, lean_object* v___x_1195_, lean_object* v___x_1196_, lean_object* v_a_1197_, lean_object* v_b_1198_, lean_object* v_acc_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_HashSet_any___redArg___lam__0(v_p_1194_, v___x_1195_, v___x_1196_, v_a_1197_, v_b_1198_, v_acc_1199_);
lean_dec_ref(v_acc_1199_);
return v_res_1200_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any___redArg(lean_object* v_m_1201_, lean_object* v_p_1202_){
_start:
{
lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___x_1207_; lean_object* v_fst_1208_; 
v___x_1203_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1204_ = lean_box(0);
v___x_1205_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1206_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1206_, 0, v_p_1202_);
lean_closure_set(v___f_1206_, 1, v___x_1205_);
lean_closure_set(v___f_1206_, 2, v___x_1204_);
v___x_1207_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1203_, v___f_1206_, v___x_1205_, v_m_1201_);
v_fst_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_fst_1208_);
lean_dec(v___x_1207_);
if (lean_obj_tag(v_fst_1208_) == 0)
{
uint8_t v___x_1209_; 
v___x_1209_ = 0;
return v___x_1209_;
}
else
{
lean_object* v_val_1210_; uint8_t v___x_1211_; 
v_val_1210_ = lean_ctor_get(v_fst_1208_, 0);
lean_inc(v_val_1210_);
lean_dec_ref_known(v_fst_1208_, 1);
v___x_1211_ = lean_unbox(v_val_1210_);
lean_dec(v_val_1210_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___redArg___boxed(lean_object* v_m_1212_, lean_object* v_p_1213_){
_start:
{
uint8_t v_res_1214_; lean_object* v_r_1215_; 
v_res_1214_ = l_Std_HashSet_any___redArg(v_m_1212_, v_p_1213_);
v_r_1215_ = lean_box(v_res_1214_);
return v_r_1215_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_any(lean_object* v_00_u03b1_1216_, lean_object* v_x_1217_, lean_object* v_x_1218_, lean_object* v_m_1219_, lean_object* v_p_1220_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v_fst_1226_; 
v___x_1221_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1222_ = lean_box(0);
v___x_1223_ = ((lean_object*)(l_Std_HashSet_all___redArg___closed__0));
v___f_1224_ = lean_alloc_closure((void*)(l_Std_HashSet_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1224_, 0, v_p_1220_);
lean_closure_set(v___f_1224_, 1, v___x_1223_);
lean_closure_set(v___f_1224_, 2, v___x_1222_);
v___x_1225_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1221_, v___f_1224_, v___x_1223_, v_m_1219_);
v_fst_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_fst_1226_);
lean_dec(v___x_1225_);
if (lean_obj_tag(v_fst_1226_) == 0)
{
uint8_t v___x_1227_; 
v___x_1227_ = 0;
return v___x_1227_;
}
else
{
lean_object* v_val_1228_; uint8_t v___x_1229_; 
v_val_1228_ = lean_ctor_get(v_fst_1226_, 0);
lean_inc(v_val_1228_);
lean_dec_ref_known(v_fst_1226_, 1);
v___x_1229_ = lean_unbox(v_val_1228_);
lean_dec(v_val_1228_);
return v___x_1229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_any___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_x_1231_, lean_object* v_x_1232_, lean_object* v_m_1233_, lean_object* v_p_1234_){
_start:
{
uint8_t v_res_1235_; lean_object* v_r_1236_; 
v_res_1235_ = l_Std_HashSet_any(v_00_u03b1_1230_, v_x_1231_, v_x_1232_, v_m_1233_, v_p_1234_);
lean_dec_ref(v_x_1232_);
lean_dec_ref(v_x_1231_);
v_r_1236_ = lean_box(v_res_1235_);
return v_r_1236_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg___lam__0(lean_object* v_inst_1237_, lean_object* v_inst_1238_, lean_object* v_a_1239_, lean_object* v_b_1240_, lean_object* v_acc_1241_){
_start:
{
lean_object* v___y_1243_; lean_object* v_i_1244_; lean_object* v___y_1263_; lean_object* v_i_1264_; lean_object* v___y_1271_; lean_object* v___x_1282_; 
lean_inc(v_a_1239_);
lean_inc_ref(v_inst_1238_);
lean_inc_ref(v_inst_1237_);
v___x_1282_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1237_, v_inst_1238_, v_acc_1241_, v_a_1239_);
switch(lean_obj_tag(v___x_1282_))
{
case 0:
{
lean_object* v___x_1283_; 
lean_dec_ref_known(v___x_1282_, 3);
lean_dec(v_a_1239_);
lean_dec_ref(v_inst_1238_);
lean_dec_ref(v_inst_1237_);
v___x_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1283_, 0, v_acc_1241_);
return v___x_1283_;
}
case 1:
{
lean_object* v_index_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1303_; 
v_index_1284_ = lean_ctor_get(v___x_1282_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1282_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1286_ = v___x_1282_;
v_isShared_1287_ = v_isSharedCheck_1303_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_index_1284_);
lean_dec(v___x_1282_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1303_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v_size_1288_; lean_object* v_keyArray_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_size_1288_ = lean_ctor_get(v_acc_1241_, 0);
v_keyArray_1289_ = lean_ctor_get(v_acc_1241_, 1);
v___x_1290_ = lean_unsigned_to_nat(1u);
v___x_1291_ = lean_nat_add(v_size_1288_, v___x_1290_);
v___x_1292_ = lean_array_get_size(v_keyArray_1289_);
v___x_1293_ = lean_nat_dec_lt(v___x_1291_, v___x_1292_);
if (v___x_1293_ == 0)
{
lean_dec(v___x_1291_);
lean_del_object(v___x_1286_);
lean_dec(v_index_1284_);
goto v___jp_1250_;
}
else
{
lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1294_ = lean_unsigned_to_nat(4u);
v___x_1295_ = lean_nat_mul(v___x_1291_, v___x_1294_);
v___x_1296_ = lean_unsigned_to_nat(3u);
v___x_1297_ = lean_nat_mul(v___x_1292_, v___x_1296_);
v___x_1298_ = lean_nat_dec_le(v___x_1295_, v___x_1297_);
lean_dec(v___x_1297_);
lean_dec(v___x_1295_);
if (v___x_1298_ == 0)
{
lean_dec(v___x_1291_);
lean_del_object(v___x_1286_);
lean_dec(v_index_1284_);
goto v___jp_1250_;
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
lean_dec_ref(v_inst_1238_);
lean_dec_ref(v_inst_1237_);
v___x_1299_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1241_, v___x_1291_, v_index_1284_, v_a_1239_, v_b_1240_);
lean_dec(v_index_1284_);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1299_);
v___x_1301_ = v___x_1286_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
default: 
{
lean_object* v_size_1304_; lean_object* v_keyArray_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_size_1304_ = lean_ctor_get(v_acc_1241_, 0);
v_keyArray_1305_ = lean_ctor_get(v_acc_1241_, 1);
v___x_1306_ = lean_unsigned_to_nat(1u);
v___x_1307_ = lean_nat_add(v_size_1304_, v___x_1306_);
v___x_1308_ = lean_array_get_size(v_keyArray_1305_);
v___x_1309_ = lean_nat_dec_lt(v___x_1307_, v___x_1308_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
lean_dec(v___x_1307_);
lean_inc_ref(v_inst_1238_);
lean_inc_ref(v_inst_1237_);
v___x_1310_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1237_, v_inst_1238_, v_acc_1241_);
v___y_1271_ = v___x_1310_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1311_ = lean_unsigned_to_nat(4u);
v___x_1312_ = lean_nat_mul(v___x_1307_, v___x_1311_);
lean_dec(v___x_1307_);
v___x_1313_ = lean_unsigned_to_nat(3u);
v___x_1314_ = lean_nat_mul(v___x_1308_, v___x_1313_);
v___x_1315_ = lean_nat_dec_le(v___x_1312_, v___x_1314_);
lean_dec(v___x_1314_);
lean_dec(v___x_1312_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_inc_ref(v_inst_1238_);
lean_inc_ref(v_inst_1237_);
v___x_1316_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1237_, v_inst_1238_, v_acc_1241_);
v___y_1271_ = v___x_1316_;
goto v___jp_1270_;
}
else
{
v___y_1271_ = v_acc_1241_;
goto v___jp_1270_;
}
}
}
}
v___jp_1242_:
{
lean_object* v_size_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; 
v_size_1245_ = lean_ctor_get(v___y_1243_, 0);
v___x_1246_ = lean_unsigned_to_nat(1u);
v___x_1247_ = lean_nat_add(v_size_1245_, v___x_1246_);
v___x_1248_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1243_, v___x_1247_, v_i_1244_, v_a_1239_, v_b_1240_);
lean_dec(v_i_1244_);
v___x_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1249_, 0, v___x_1248_);
return v___x_1249_;
}
v___jp_1250_:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_inc_ref(v_inst_1238_);
lean_inc_ref(v_inst_1237_);
v___x_1251_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1237_, v_inst_1238_, v_acc_1241_);
lean_inc(v_a_1239_);
v___x_1252_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1237_, v_inst_1238_, v___x_1251_, v_a_1239_);
switch(lean_obj_tag(v___x_1252_))
{
case 0:
{
lean_object* v_index_1253_; lean_object* v_size_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_index_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_index_1253_);
lean_dec_ref_known(v___x_1252_, 3);
v_size_1254_ = lean_ctor_get(v___x_1251_, 0);
lean_inc(v_size_1254_);
v___x_1255_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1251_, v_size_1254_, v_index_1253_, v_a_1239_, v_b_1240_);
lean_dec(v_index_1253_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
case 1:
{
lean_object* v_index_1257_; 
v_index_1257_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_index_1257_);
lean_dec_ref_known(v___x_1252_, 1);
v___y_1243_ = v___x_1251_;
v_i_1244_ = v_index_1257_;
goto v___jp_1242_;
}
default: 
{
lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1258_ = lean_unsigned_to_nat(0u);
v___x_1259_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1251_, v___x_1258_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_object* v_index_1260_; 
v_index_1260_ = lean_ctor_get(v___x_1259_, 0);
lean_inc(v_index_1260_);
lean_dec_ref_known(v___x_1259_, 1);
v___y_1243_ = v___x_1251_;
v_i_1244_ = v_index_1260_;
goto v___jp_1242_;
}
else
{
lean_object* v___x_1261_; 
lean_dec(v_a_1239_);
v___x_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1251_);
return v___x_1261_;
}
}
}
}
v___jp_1262_:
{
lean_object* v_size_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v_size_1265_ = lean_ctor_get(v___y_1263_, 0);
v___x_1266_ = lean_unsigned_to_nat(1u);
v___x_1267_ = lean_nat_add(v_size_1265_, v___x_1266_);
v___x_1268_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1263_, v___x_1267_, v_i_1264_, v_a_1239_, v_b_1240_);
lean_dec(v_i_1264_);
v___x_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
return v___x_1269_;
}
v___jp_1270_:
{
lean_object* v___x_1272_; 
lean_inc(v_a_1239_);
v___x_1272_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1237_, v_inst_1238_, v___y_1271_, v_a_1239_);
switch(lean_obj_tag(v___x_1272_))
{
case 0:
{
lean_object* v_index_1273_; lean_object* v_size_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
v_index_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_index_1273_);
lean_dec_ref_known(v___x_1272_, 3);
v_size_1274_ = lean_ctor_get(v___y_1271_, 0);
lean_inc(v_size_1274_);
v___x_1275_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1271_, v_size_1274_, v_index_1273_, v_a_1239_, v_b_1240_);
lean_dec(v_index_1273_);
v___x_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
return v___x_1276_;
}
case 1:
{
lean_object* v_index_1277_; 
v_index_1277_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_index_1277_);
lean_dec_ref_known(v___x_1272_, 1);
v___y_1263_ = v___y_1271_;
v_i_1264_ = v_index_1277_;
goto v___jp_1262_;
}
default: 
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1271_, v___x_1278_);
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_index_1280_; 
v_index_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_index_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___y_1263_ = v___y_1271_;
v_i_1264_ = v_index_1280_;
goto v___jp_1262_;
}
else
{
lean_object* v___x_1281_; 
lean_dec(v_a_1239_);
v___x_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___y_1271_);
return v___x_1281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union___redArg(lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_m_u2081_1321_, lean_object* v_m_u2082_1322_){
_start:
{
lean_object* v_size_1323_; lean_object* v_size_1324_; uint8_t v___x_1325_; 
v_size_1323_ = lean_ctor_get(v_m_u2081_1321_, 0);
v_size_1324_ = lean_ctor_get(v_m_u2082_1322_, 0);
v___x_1325_ = lean_nat_dec_le(v_size_1323_, v_size_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___f_1326_; lean_object* v___x_1327_; 
v___f_1326_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1327_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1326_, v_inst_1319_, v_inst_1320_, v_m_u2081_1321_, v_m_u2082_1322_);
return v___x_1327_;
}
else
{
lean_object* v___f_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___f_1328_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1328_, 0, v_inst_1319_);
lean_closure_set(v___f_1328_, 1, v_inst_1320_);
v___x_1329_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1330_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1329_, v___f_1328_, v_m_u2082_1322_, v_m_u2081_1321_);
return v___x_1330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_union(lean_object* v_00_u03b1_1331_, lean_object* v_inst_1332_, lean_object* v_inst_1333_, lean_object* v_m_u2081_1334_, lean_object* v_m_u2082_1335_){
_start:
{
lean_object* v_size_1336_; lean_object* v_size_1337_; uint8_t v___x_1338_; 
v_size_1336_ = lean_ctor_get(v_m_u2081_1334_, 0);
v_size_1337_ = lean_ctor_get(v_m_u2082_1335_, 0);
v___x_1338_ = lean_nat_dec_le(v_size_1336_, v_size_1337_);
if (v___x_1338_ == 0)
{
lean_object* v___f_1339_; lean_object* v___x_1340_; 
v___f_1339_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1340_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1339_, v_inst_1332_, v_inst_1333_, v_m_u2081_1334_, v_m_u2082_1335_);
return v___x_1340_;
}
else
{
lean_object* v___f_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___f_1341_ = lean_alloc_closure((void*)(l_Std_HashSet_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1341_, 0, v_inst_1332_);
lean_closure_set(v___f_1341_, 1, v_inst_1333_);
v___x_1342_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1343_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1342_, v___f_1341_, v_m_u2082_1335_, v_m_u2081_1334_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion___redArg(lean_object* v_inst_1344_, lean_object* v_inst_1345_){
_start:
{
lean_object* v___x_1346_; 
v___x_1346_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1346_, 0, lean_box(0));
lean_closure_set(v___x_1346_, 1, v_inst_1344_);
lean_closure_set(v___x_1346_, 2, v_inst_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instUnion(lean_object* v_00_u03b1_1347_, lean_object* v_inst_1348_, lean_object* v_inst_1349_){
_start:
{
lean_object* v___x_1350_; 
v___x_1350_ = lean_alloc_closure((void*)(l_Std_HashSet_union), 5, 3);
lean_closure_set(v___x_1350_, 0, lean_box(0));
lean_closure_set(v___x_1350_, 1, v_inst_1348_);
lean_closure_set(v___x_1350_, 2, v_inst_1349_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter___redArg(lean_object* v_inst_1351_, lean_object* v_inst_1352_, lean_object* v_m_u2081_1353_, lean_object* v_m_u2082_1354_){
_start:
{
lean_object* v___x_1355_; 
v___x_1355_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1351_, v_inst_1352_, v_m_u2081_1353_, v_m_u2082_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_inter(lean_object* v_00_u03b1_1356_, lean_object* v_inst_1357_, lean_object* v_inst_1358_, lean_object* v_m_u2081_1359_, lean_object* v_m_u2082_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1357_, v_inst_1358_, v_m_u2081_1359_, v_m_u2082_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter___redArg(lean_object* v_inst_1362_, lean_object* v_inst_1363_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1364_, 0, lean_box(0));
lean_closure_set(v___x_1364_, 1, v_inst_1362_);
lean_closure_set(v___x_1364_, 2, v_inst_1363_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instInter(lean_object* v_00_u03b1_1365_, lean_object* v_inst_1366_, lean_object* v_inst_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_alloc_closure((void*)(l_Std_HashSet_inter), 5, 3);
lean_closure_set(v___x_1368_, 0, lean_box(0));
lean_closure_set(v___x_1368_, 1, v_inst_1366_);
lean_closure_set(v___x_1368_, 2, v_inst_1367_);
return v___x_1368_;
}
}
static lean_object* _init_l_Std_HashSet_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___f_1370_; 
v___x_1369_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1370_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1370_, 0, v___x_1369_);
return v___f_1370_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq___redArg(lean_object* v_x_1371_, lean_object* v_inst_1372_, lean_object* v_m_u2081_1373_, lean_object* v_m_u2082_1374_){
_start:
{
lean_object* v___f_1375_; uint8_t v___x_1376_; 
v___f_1375_ = lean_obj_once(&l_Std_HashSet_beq___redArg___closed__0, &l_Std_HashSet_beq___redArg___closed__0_once, _init_l_Std_HashSet_beq___redArg___closed__0);
v___x_1376_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_1372_, v_x_1371_, v___f_1375_, v_m_u2081_1373_, v_m_u2082_1374_);
return v___x_1376_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___redArg___boxed(lean_object* v_x_1377_, lean_object* v_inst_1378_, lean_object* v_m_u2081_1379_, lean_object* v_m_u2082_1380_){
_start:
{
uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_res_1381_ = l_Std_HashSet_beq___redArg(v_x_1377_, v_inst_1378_, v_m_u2081_1379_, v_m_u2082_1380_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_beq(lean_object* v_00_u03b1_1383_, lean_object* v_x_1384_, lean_object* v_inst_1385_, lean_object* v_m_u2081_1386_, lean_object* v_m_u2082_1387_){
_start:
{
uint8_t v___x_1388_; 
v___x_1388_ = l_Std_HashSet_beq___redArg(v_x_1384_, v_inst_1385_, v_m_u2081_1386_, v_m_u2082_1387_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_beq___boxed(lean_object* v_00_u03b1_1389_, lean_object* v_x_1390_, lean_object* v_inst_1391_, lean_object* v_m_u2081_1392_, lean_object* v_m_u2082_1393_){
_start:
{
uint8_t v_res_1394_; lean_object* v_r_1395_; 
v_res_1394_ = l_Std_HashSet_beq(v_00_u03b1_1389_, v_x_1390_, v_inst_1391_, v_m_u2081_1392_, v_m_u2082_1393_);
v_r_1395_ = lean_box(v_res_1394_);
return v_r_1395_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq___redArg(lean_object* v_x_1396_, lean_object* v_inst_1397_){
_start:
{
lean_object* v___x_1398_; 
v___x_1398_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1398_, 0, lean_box(0));
lean_closure_set(v___x_1398_, 1, v_x_1396_);
lean_closure_set(v___x_1398_, 2, v_inst_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instBEq(lean_object* v_00_u03b1_1399_, lean_object* v_x_1400_, lean_object* v_inst_1401_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = lean_alloc_closure((void*)(l_Std_HashSet_beq___boxed), 5, 3);
lean_closure_set(v___x_1402_, 0, lean_box(0));
lean_closure_set(v___x_1402_, 1, v_x_1400_);
lean_closure_set(v___x_1402_, 2, v_inst_1401_);
return v___x_1402_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_diff___redArg___lam__0(lean_object* v_inst_1403_, lean_object* v_inst_1404_, lean_object* v_m_u2082_1405_, uint8_t v___x_1406_, lean_object* v_k_1407_, lean_object* v_x_1408_){
_start:
{
uint8_t v___x_1409_; 
v___x_1409_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1403_, v_inst_1404_, v_m_u2082_1405_, v_k_1407_);
if (v___x_1409_ == 0)
{
return v___x_1406_;
}
else
{
uint8_t v___x_1410_; 
v___x_1410_ = 0;
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg___lam__0___boxed(lean_object* v_inst_1411_, lean_object* v_inst_1412_, lean_object* v_m_u2082_1413_, lean_object* v___x_1414_, lean_object* v_k_1415_, lean_object* v_x_1416_){
_start:
{
uint8_t v___x_83__boxed_1417_; uint8_t v_res_1418_; lean_object* v_r_1419_; 
v___x_83__boxed_1417_ = lean_unbox(v___x_1414_);
v_res_1418_ = l_Std_HashSet_diff___redArg___lam__0(v_inst_1411_, v_inst_1412_, v_m_u2082_1413_, v___x_83__boxed_1417_, v_k_1415_, v_x_1416_);
lean_dec_ref(v_m_u2082_1413_);
v_r_1419_ = lean_box(v_res_1418_);
return v_r_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff___redArg(lean_object* v_inst_1420_, lean_object* v_inst_1421_, lean_object* v_m_u2081_1422_, lean_object* v_m_u2082_1423_){
_start:
{
lean_object* v_size_1424_; lean_object* v_size_1425_; uint8_t v___x_1426_; 
v_size_1424_ = lean_ctor_get(v_m_u2081_1422_, 0);
v_size_1425_ = lean_ctor_get(v_m_u2082_1423_, 0);
v___x_1426_ = lean_nat_dec_le(v_size_1424_, v_size_1425_);
if (v___x_1426_ == 0)
{
lean_object* v___f_1427_; lean_object* v___x_1428_; 
v___f_1427_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1428_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1427_, v_inst_1420_, v_inst_1421_, v_m_u2081_1422_, v_m_u2082_1423_);
return v___x_1428_;
}
else
{
lean_object* v___x_1429_; lean_object* v___f_1430_; lean_object* v___x_1431_; 
v___x_1429_ = lean_box(v___x_1426_);
v___f_1430_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1430_, 0, v_inst_1420_);
lean_closure_set(v___f_1430_, 1, v_inst_1421_);
lean_closure_set(v___f_1430_, 2, v_m_u2082_1423_);
lean_closure_set(v___f_1430_, 3, v___x_1429_);
v___x_1431_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1430_, v_m_u2081_1422_);
lean_dec_ref(v_m_u2081_1422_);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_diff(lean_object* v_00_u03b1_1432_, lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_m_u2081_1435_, lean_object* v_m_u2082_1436_){
_start:
{
lean_object* v_size_1437_; lean_object* v_size_1438_; uint8_t v___x_1439_; 
v_size_1437_ = lean_ctor_get(v_m_u2081_1435_, 0);
v_size_1438_ = lean_ctor_get(v_m_u2082_1436_, 0);
v___x_1439_ = lean_nat_dec_le(v_size_1437_, v_size_1438_);
if (v___x_1439_ == 0)
{
lean_object* v___f_1440_; lean_object* v___x_1441_; 
v___f_1440_ = ((lean_object*)(l_Std_HashSet_union___redArg___closed__0));
v___x_1441_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1440_, v_inst_1433_, v_inst_1434_, v_m_u2081_1435_, v_m_u2082_1436_);
return v___x_1441_;
}
else
{
lean_object* v___x_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; 
v___x_1442_ = lean_box(v___x_1439_);
v___f_1443_ = lean_alloc_closure((void*)(l_Std_HashSet_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1443_, 0, v_inst_1433_);
lean_closure_set(v___f_1443_, 1, v_inst_1434_);
lean_closure_set(v___f_1443_, 2, v_m_u2082_1436_);
lean_closure_set(v___f_1443_, 3, v___x_1442_);
v___x_1444_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1443_, v_m_u2081_1435_);
lean_dec_ref(v_m_u2081_1435_);
return v___x_1444_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff___redArg(lean_object* v_inst_1445_, lean_object* v_inst_1446_){
_start:
{
lean_object* v___x_1447_; 
v___x_1447_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1447_, 0, lean_box(0));
lean_closure_set(v___x_1447_, 1, v_inst_1445_);
lean_closure_set(v___x_1447_, 2, v_inst_1446_);
return v___x_1447_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instSDiff(lean_object* v_00_u03b1_1448_, lean_object* v_inst_1449_, lean_object* v_inst_1450_){
_start:
{
lean_object* v___x_1451_; 
v___x_1451_ = lean_alloc_closure((void*)(l_Std_HashSet_diff), 5, 3);
lean_closure_set(v___x_1451_, 0, lean_box(0));
lean_closure_set(v___x_1451_, 1, v_inst_1449_);
lean_closure_set(v___x_1451_, 2, v_inst_1450_);
return v___x_1451_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg___lam__0(lean_object* v_f_1452_, lean_object* v_x_1453_, lean_object* v_x_1454_, lean_object* v_x1_1455_, lean_object* v_x2_1456_, lean_object* v_x3_1457_){
_start:
{
lean_object* v_fst_1458_; lean_object* v_snd_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1611_; 
v_fst_1458_ = lean_ctor_get(v_x1_1455_, 0);
v_snd_1459_ = lean_ctor_get(v_x1_1455_, 1);
v_isSharedCheck_1611_ = !lean_is_exclusive(v_x1_1455_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1461_ = v_x1_1455_;
v_isShared_1462_ = v_isSharedCheck_1611_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_snd_1459_);
lean_inc(v_fst_1458_);
lean_dec(v_x1_1455_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1611_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___y_1464_; lean_object* v_i_1465_; lean_object* v___y_1474_; lean_object* v_i_1475_; lean_object* v___y_1482_; lean_object* v___y_1506_; lean_object* v_i_1507_; lean_object* v___y_1514_; lean_object* v___y_1526_; lean_object* v_i_1527_; lean_object* v___x_1545_; uint8_t v___x_1546_; 
lean_inc(v_x2_1456_);
v___x_1545_ = lean_apply_1(v_f_1452_, v_x2_1456_);
v___x_1546_ = lean_unbox(v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; 
lean_del_object(v___x_1461_);
lean_inc(v_x2_1456_);
lean_inc_ref(v_x_1454_);
lean_inc_ref(v_x_1453_);
v___x_1547_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1453_, v_x_1454_, v_snd_1459_, v_x2_1456_);
switch(lean_obj_tag(v___x_1547_))
{
case 0:
{
lean_object* v_index_1548_; lean_object* v_size_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
lean_dec_ref(v_x_1454_);
lean_dec_ref(v_x_1453_);
v_index_1548_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_index_1548_);
lean_dec_ref_known(v___x_1547_, 3);
v_size_1549_ = lean_ctor_get(v_snd_1459_, 0);
lean_inc(v_size_1549_);
v___x_1550_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1459_, v_size_1549_, v_index_1548_, v_x2_1456_, v_x3_1457_);
lean_dec(v_index_1548_);
v___x_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1551_, 0, v_fst_1458_);
lean_ctor_set(v___x_1551_, 1, v___x_1550_);
return v___x_1551_;
}
case 1:
{
lean_object* v_index_1552_; lean_object* v_size_1553_; lean_object* v_keyArray_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; uint8_t v___x_1558_; 
v_index_1552_ = lean_ctor_get(v___x_1547_, 0);
lean_inc(v_index_1552_);
lean_dec_ref_known(v___x_1547_, 1);
v_size_1553_ = lean_ctor_get(v_snd_1459_, 0);
v_keyArray_1554_ = lean_ctor_get(v_snd_1459_, 1);
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_add(v_size_1553_, v___x_1555_);
v___x_1557_ = lean_array_get_size(v_keyArray_1554_);
v___x_1558_ = lean_nat_dec_lt(v___x_1556_, v___x_1557_);
if (v___x_1558_ == 0)
{
lean_dec(v___x_1556_);
lean_dec(v_index_1552_);
goto v___jp_1533_;
}
else
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; uint8_t v___x_1563_; 
v___x_1559_ = lean_unsigned_to_nat(4u);
v___x_1560_ = lean_nat_mul(v___x_1556_, v___x_1559_);
v___x_1561_ = lean_unsigned_to_nat(3u);
v___x_1562_ = lean_nat_mul(v___x_1557_, v___x_1561_);
v___x_1563_ = lean_nat_dec_le(v___x_1560_, v___x_1562_);
lean_dec(v___x_1562_);
lean_dec(v___x_1560_);
if (v___x_1563_ == 0)
{
lean_dec(v___x_1556_);
lean_dec(v_index_1552_);
goto v___jp_1533_;
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
lean_dec_ref(v_x_1454_);
lean_dec_ref(v_x_1453_);
v___x_1564_ = l_Std_DHashMap_Raw_setEntry___redArg(v_snd_1459_, v___x_1556_, v_index_1552_, v_x2_1456_, v_x3_1457_);
lean_dec(v_index_1552_);
v___x_1565_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1565_, 0, v_fst_1458_);
lean_ctor_set(v___x_1565_, 1, v___x_1564_);
return v___x_1565_;
}
}
}
default: 
{
lean_object* v_size_1566_; lean_object* v_keyArray_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; uint8_t v___x_1571_; 
v_size_1566_ = lean_ctor_get(v_snd_1459_, 0);
v_keyArray_1567_ = lean_ctor_get(v_snd_1459_, 1);
v___x_1568_ = lean_unsigned_to_nat(1u);
v___x_1569_ = lean_nat_add(v_size_1566_, v___x_1568_);
v___x_1570_ = lean_array_get_size(v_keyArray_1567_);
v___x_1571_ = lean_nat_dec_lt(v___x_1569_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; 
lean_dec(v___x_1569_);
lean_inc_ref(v_x_1454_);
lean_inc_ref(v_x_1453_);
v___x_1572_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1453_, v_x_1454_, v_snd_1459_);
v___y_1514_ = v___x_1572_;
goto v___jp_1513_;
}
else
{
lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1573_ = lean_unsigned_to_nat(4u);
v___x_1574_ = lean_nat_mul(v___x_1569_, v___x_1573_);
lean_dec(v___x_1569_);
v___x_1575_ = lean_unsigned_to_nat(3u);
v___x_1576_ = lean_nat_mul(v___x_1570_, v___x_1575_);
v___x_1577_ = lean_nat_dec_le(v___x_1574_, v___x_1576_);
lean_dec(v___x_1576_);
lean_dec(v___x_1574_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
lean_inc_ref(v_x_1454_);
lean_inc_ref(v_x_1453_);
v___x_1578_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1453_, v_x_1454_, v_snd_1459_);
v___y_1514_ = v___x_1578_;
goto v___jp_1513_;
}
else
{
v___y_1514_ = v_snd_1459_;
goto v___jp_1513_;
}
}
}
}
}
else
{
lean_object* v___x_1579_; 
lean_inc(v_x2_1456_);
lean_inc_ref(v_x_1454_);
lean_inc_ref(v_x_1453_);
v___x_1579_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1453_, v_x_1454_, v_fst_1458_, v_x2_1456_);
switch(lean_obj_tag(v___x_1579_))
{
case 0:
{
lean_object* v_index_1580_; lean_object* v_size_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
lean_del_object(v___x_1461_);
lean_dec_ref(v_x_1454_);
lean_dec_ref(v_x_1453_);
v_index_1580_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_index_1580_);
lean_dec_ref_known(v___x_1579_, 3);
v_size_1581_ = lean_ctor_get(v_fst_1458_, 0);
lean_inc(v_size_1581_);
v___x_1582_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1458_, v_size_1581_, v_index_1580_, v_x2_1456_, v_x3_1457_);
lean_dec(v_index_1580_);
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v___x_1582_);
lean_ctor_set(v___x_1583_, 1, v_snd_1459_);
return v___x_1583_;
}
case 1:
{
lean_object* v_index_1584_; lean_object* v_size_1585_; lean_object* v_keyArray_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_index_1584_ = lean_ctor_get(v___x_1579_, 0);
lean_inc(v_index_1584_);
lean_dec_ref_known(v___x_1579_, 1);
v_size_1585_ = lean_ctor_get(v_fst_1458_, 0);
v_keyArray_1586_ = lean_ctor_get(v_fst_1458_, 1);
v___x_1587_ = lean_unsigned_to_nat(1u);
v___x_1588_ = lean_nat_add(v_size_1585_, v___x_1587_);
v___x_1589_ = lean_array_get_size(v_keyArray_1586_);
v___x_1590_ = lean_nat_dec_lt(v___x_1588_, v___x_1589_);
if (v___x_1590_ == 0)
{
lean_dec(v___x_1588_);
lean_dec(v_index_1584_);
goto v___jp_1493_;
}
else
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; uint8_t v___x_1595_; 
v___x_1591_ = lean_unsigned_to_nat(4u);
v___x_1592_ = lean_nat_mul(v___x_1588_, v___x_1591_);
v___x_1593_ = lean_unsigned_to_nat(3u);
v___x_1594_ = lean_nat_mul(v___x_1589_, v___x_1593_);
v___x_1595_ = lean_nat_dec_le(v___x_1592_, v___x_1594_);
lean_dec(v___x_1594_);
lean_dec(v___x_1592_);
if (v___x_1595_ == 0)
{
lean_dec(v___x_1588_);
lean_dec(v_index_1584_);
goto v___jp_1493_;
}
else
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
lean_del_object(v___x_1461_);
lean_dec_ref(v_x_1454_);
lean_dec_ref(v_x_1453_);
v___x_1596_ = l_Std_DHashMap_Raw_setEntry___redArg(v_fst_1458_, v___x_1588_, v_index_1584_, v_x2_1456_, v_x3_1457_);
lean_dec(v_index_1584_);
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v_snd_1459_);
return v___x_1597_;
}
}
}
default: 
{
lean_object* v_size_1598_; lean_object* v_keyArray_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; uint8_t v___x_1603_; 
lean_del_object(v___x_1461_);
v_size_1598_ = lean_ctor_get(v_fst_1458_, 0);
v_keyArray_1599_ = lean_ctor_get(v_fst_1458_, 1);
v___x_1600_ = lean_unsigned_to_nat(1u);
v___x_1601_ = lean_nat_add(v_size_1598_, v___x_1600_);
v___x_1602_ = lean_array_get_size(v_keyArray_1599_);
v___x_1603_ = lean_nat_dec_lt(v___x_1601_, v___x_1602_);
if (v___x_1603_ == 0)
{
lean_object* v___x_1604_; 
lean_dec(v___x_1601_);
lean_inc_ref(v_x_1454_);
lean_inc_ref(v_x_1453_);
v___x_1604_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1453_, v_x_1454_, v_fst_1458_);
v___y_1482_ = v___x_1604_;
goto v___jp_1481_;
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; uint8_t v___x_1609_; 
v___x_1605_ = lean_unsigned_to_nat(4u);
v___x_1606_ = lean_nat_mul(v___x_1601_, v___x_1605_);
lean_dec(v___x_1601_);
v___x_1607_ = lean_unsigned_to_nat(3u);
v___x_1608_ = lean_nat_mul(v___x_1602_, v___x_1607_);
v___x_1609_ = lean_nat_dec_le(v___x_1606_, v___x_1608_);
lean_dec(v___x_1608_);
lean_dec(v___x_1606_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_inc_ref(v_x_1454_);
lean_inc_ref(v_x_1453_);
v___x_1610_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1453_, v_x_1454_, v_fst_1458_);
v___y_1482_ = v___x_1610_;
goto v___jp_1481_;
}
else
{
v___y_1482_ = v_fst_1458_;
goto v___jp_1481_;
}
}
}
}
}
v___jp_1463_:
{
lean_object* v_size_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1471_; 
v_size_1466_ = lean_ctor_get(v___y_1464_, 0);
v___x_1467_ = lean_unsigned_to_nat(1u);
v___x_1468_ = lean_nat_add(v_size_1466_, v___x_1467_);
v___x_1469_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1464_, v___x_1468_, v_i_1465_, v_x2_1456_, v_x3_1457_);
lean_dec(v_i_1465_);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1469_);
v___x_1471_ = v___x_1461_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v___x_1469_);
lean_ctor_set(v_reuseFailAlloc_1472_, 1, v_snd_1459_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
v___jp_1473_:
{
lean_object* v_size_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_size_1476_ = lean_ctor_get(v___y_1474_, 0);
v___x_1477_ = lean_unsigned_to_nat(1u);
v___x_1478_ = lean_nat_add(v_size_1476_, v___x_1477_);
v___x_1479_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1474_, v___x_1478_, v_i_1475_, v_x2_1456_, v_x3_1457_);
lean_dec(v_i_1475_);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___x_1479_);
lean_ctor_set(v___x_1480_, 1, v_snd_1459_);
return v___x_1480_;
}
v___jp_1481_:
{
lean_object* v___x_1483_; 
lean_inc(v_x2_1456_);
v___x_1483_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1453_, v_x_1454_, v___y_1482_, v_x2_1456_);
switch(lean_obj_tag(v___x_1483_))
{
case 0:
{
lean_object* v_index_1484_; lean_object* v_size_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_index_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_index_1484_);
lean_dec_ref_known(v___x_1483_, 3);
v_size_1485_ = lean_ctor_get(v___y_1482_, 0);
lean_inc(v_size_1485_);
v___x_1486_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1482_, v_size_1485_, v_index_1484_, v_x2_1456_, v_x3_1457_);
lean_dec(v_index_1484_);
v___x_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1487_, 0, v___x_1486_);
lean_ctor_set(v___x_1487_, 1, v_snd_1459_);
return v___x_1487_;
}
case 1:
{
lean_object* v_index_1488_; 
v_index_1488_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_index_1488_);
lean_dec_ref_known(v___x_1483_, 1);
v___y_1474_ = v___y_1482_;
v_i_1475_ = v_index_1488_;
goto v___jp_1473_;
}
default: 
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = lean_unsigned_to_nat(0u);
v___x_1490_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1482_, v___x_1489_);
if (lean_obj_tag(v___x_1490_) == 0)
{
lean_object* v_index_1491_; 
v_index_1491_ = lean_ctor_get(v___x_1490_, 0);
lean_inc(v_index_1491_);
lean_dec_ref_known(v___x_1490_, 1);
v___y_1474_ = v___y_1482_;
v_i_1475_ = v_index_1491_;
goto v___jp_1473_;
}
else
{
lean_object* v___x_1492_; 
lean_dec(v_x2_1456_);
v___x_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1492_, 0, v___y_1482_);
lean_ctor_set(v___x_1492_, 1, v_snd_1459_);
return v___x_1492_;
}
}
}
}
v___jp_1493_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_inc_ref(v_x_1454_);
lean_inc_ref(v_x_1453_);
v___x_1494_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1453_, v_x_1454_, v_fst_1458_);
lean_inc(v_x2_1456_);
v___x_1495_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1453_, v_x_1454_, v___x_1494_, v_x2_1456_);
switch(lean_obj_tag(v___x_1495_))
{
case 0:
{
lean_object* v_index_1496_; lean_object* v_size_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; 
lean_del_object(v___x_1461_);
v_index_1496_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_index_1496_);
lean_dec_ref_known(v___x_1495_, 3);
v_size_1497_ = lean_ctor_get(v___x_1494_, 0);
lean_inc(v_size_1497_);
v___x_1498_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1494_, v_size_1497_, v_index_1496_, v_x2_1456_, v_x3_1457_);
lean_dec(v_index_1496_);
v___x_1499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1499_, 0, v___x_1498_);
lean_ctor_set(v___x_1499_, 1, v_snd_1459_);
return v___x_1499_;
}
case 1:
{
lean_object* v_index_1500_; 
v_index_1500_ = lean_ctor_get(v___x_1495_, 0);
lean_inc(v_index_1500_);
lean_dec_ref_known(v___x_1495_, 1);
v___y_1464_ = v___x_1494_;
v_i_1465_ = v_index_1500_;
goto v___jp_1463_;
}
default: 
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_unsigned_to_nat(0u);
v___x_1502_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1494_, v___x_1501_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v_index_1503_; 
v_index_1503_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_index_1503_);
lean_dec_ref_known(v___x_1502_, 1);
v___y_1464_ = v___x_1494_;
v_i_1465_ = v_index_1503_;
goto v___jp_1463_;
}
else
{
lean_object* v___x_1504_; 
lean_del_object(v___x_1461_);
lean_dec(v_x2_1456_);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1494_);
lean_ctor_set(v___x_1504_, 1, v_snd_1459_);
return v___x_1504_;
}
}
}
}
v___jp_1505_:
{
lean_object* v_size_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_size_1508_ = lean_ctor_get(v___y_1506_, 0);
v___x_1509_ = lean_unsigned_to_nat(1u);
v___x_1510_ = lean_nat_add(v_size_1508_, v___x_1509_);
v___x_1511_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1506_, v___x_1510_, v_i_1507_, v_x2_1456_, v_x3_1457_);
lean_dec(v_i_1507_);
v___x_1512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1512_, 0, v_fst_1458_);
lean_ctor_set(v___x_1512_, 1, v___x_1511_);
return v___x_1512_;
}
v___jp_1513_:
{
lean_object* v___x_1515_; 
lean_inc(v_x2_1456_);
v___x_1515_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1453_, v_x_1454_, v___y_1514_, v_x2_1456_);
switch(lean_obj_tag(v___x_1515_))
{
case 0:
{
lean_object* v_index_1516_; lean_object* v_size_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; 
v_index_1516_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_index_1516_);
lean_dec_ref_known(v___x_1515_, 3);
v_size_1517_ = lean_ctor_get(v___y_1514_, 0);
lean_inc(v_size_1517_);
v___x_1518_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1514_, v_size_1517_, v_index_1516_, v_x2_1456_, v_x3_1457_);
lean_dec(v_index_1516_);
v___x_1519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1519_, 0, v_fst_1458_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
return v___x_1519_;
}
case 1:
{
lean_object* v_index_1520_; 
v_index_1520_ = lean_ctor_get(v___x_1515_, 0);
lean_inc(v_index_1520_);
lean_dec_ref_known(v___x_1515_, 1);
v___y_1506_ = v___y_1514_;
v_i_1507_ = v_index_1520_;
goto v___jp_1505_;
}
default: 
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1514_, v___x_1521_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_index_1523_; 
v_index_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_index_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___y_1506_ = v___y_1514_;
v_i_1507_ = v_index_1523_;
goto v___jp_1505_;
}
else
{
lean_object* v___x_1524_; 
lean_dec(v_x2_1456_);
v___x_1524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1524_, 0, v_fst_1458_);
lean_ctor_set(v___x_1524_, 1, v___y_1514_);
return v___x_1524_;
}
}
}
}
v___jp_1525_:
{
lean_object* v_size_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v_size_1528_ = lean_ctor_get(v___y_1526_, 0);
v___x_1529_ = lean_unsigned_to_nat(1u);
v___x_1530_ = lean_nat_add(v_size_1528_, v___x_1529_);
v___x_1531_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1526_, v___x_1530_, v_i_1527_, v_x2_1456_, v_x3_1457_);
lean_dec(v_i_1527_);
v___x_1532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_fst_1458_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
return v___x_1532_;
}
v___jp_1533_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
lean_inc_ref(v_x_1454_);
lean_inc_ref(v_x_1453_);
v___x_1534_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_x_1453_, v_x_1454_, v_snd_1459_);
lean_inc(v_x2_1456_);
v___x_1535_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_x_1453_, v_x_1454_, v___x_1534_, v_x2_1456_);
switch(lean_obj_tag(v___x_1535_))
{
case 0:
{
lean_object* v_index_1536_; lean_object* v_size_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v_index_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_index_1536_);
lean_dec_ref_known(v___x_1535_, 3);
v_size_1537_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_size_1537_);
v___x_1538_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1534_, v_size_1537_, v_index_1536_, v_x2_1456_, v_x3_1457_);
lean_dec(v_index_1536_);
v___x_1539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1539_, 0, v_fst_1458_);
lean_ctor_set(v___x_1539_, 1, v___x_1538_);
return v___x_1539_;
}
case 1:
{
lean_object* v_index_1540_; 
v_index_1540_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_index_1540_);
lean_dec_ref_known(v___x_1535_, 1);
v___y_1526_ = v___x_1534_;
v_i_1527_ = v_index_1540_;
goto v___jp_1525_;
}
default: 
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1542_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1534_, v___x_1541_);
if (lean_obj_tag(v___x_1542_) == 0)
{
lean_object* v_index_1543_; 
v_index_1543_ = lean_ctor_get(v___x_1542_, 0);
lean_inc(v_index_1543_);
lean_dec_ref_known(v___x_1542_, 1);
v___y_1526_ = v___x_1534_;
v_i_1527_ = v_index_1543_;
goto v___jp_1525_;
}
else
{
lean_object* v___x_1544_; 
lean_dec(v_x2_1456_);
v___x_1544_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1544_, 0, v_fst_1458_);
lean_ctor_set(v___x_1544_, 1, v___x_1534_);
return v___x_1544_;
}
}
}
}
}
}
}
static lean_object* _init_l_Std_HashSet_partition___redArg___closed__0(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; 
v___x_1612_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__2, &l_Std_HashSet_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_instEmptyCollection___closed__2);
v___x_1613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1613_, 0, v___x_1612_);
lean_ctor_set(v___x_1613_, 1, v___x_1612_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition___redArg(lean_object* v_x_1614_, lean_object* v_x_1615_, lean_object* v_f_1616_, lean_object* v_m_1617_){
_start:
{
lean_object* v___f_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v_fst_1622_; lean_object* v_snd_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
v___f_1618_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1618_, 0, v_f_1616_);
lean_closure_set(v___f_1618_, 1, v_x_1614_);
lean_closure_set(v___f_1618_, 2, v_x_1615_);
v___x_1619_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1620_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1621_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1620_, v___f_1618_, v___x_1619_, v_m_1617_);
v_fst_1622_ = lean_ctor_get(v___x_1621_, 0);
v_snd_1623_ = lean_ctor_get(v___x_1621_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1621_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1621_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_snd_1623_);
lean_inc(v_fst_1622_);
lean_dec(v___x_1621_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_fst_1622_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_snd_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_partition(lean_object* v_00_u03b1_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_, lean_object* v_f_1634_, lean_object* v_m_1635_){
_start:
{
lean_object* v___f_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_fst_1640_; lean_object* v_snd_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1648_; 
v___f_1636_ = lean_alloc_closure((void*)(l_Std_HashSet_partition___redArg___lam__0), 6, 3);
lean_closure_set(v___f_1636_, 0, v_f_1634_);
lean_closure_set(v___f_1636_, 1, v_x_1632_);
lean_closure_set(v___f_1636_, 2, v_x_1633_);
v___x_1637_ = lean_obj_once(&l_Std_HashSet_partition___redArg___closed__0, &l_Std_HashSet_partition___redArg___closed__0_once, _init_l_Std_HashSet_partition___redArg___closed__0);
v___x_1638_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1639_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1638_, v___f_1636_, v___x_1637_, v_m_1635_);
v_fst_1640_ = lean_ctor_get(v___x_1639_, 0);
v_snd_1641_ = lean_ctor_get(v___x_1639_, 1);
v_isSharedCheck_1648_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1643_ = v___x_1639_;
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
else
{
lean_inc(v_snd_1641_);
lean_inc(v_fst_1640_);
lean_dec(v___x_1639_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1648_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1646_; 
if (v_isShared_1644_ == 0)
{
v___x_1646_ = v___x_1643_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_fst_1640_);
lean_ctor_set(v_reuseFailAlloc_1647_, 1, v_snd_1641_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
return v___x_1646_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray___redArg(lean_object* v_inst_1653_, lean_object* v_inst_1654_, lean_object* v_l_1655_){
_start:
{
lean_object* v___f_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___f_1656_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1657_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__2, &l_Std_HashSet_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_instEmptyCollection___closed__2);
v___x_1658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1656_, v_inst_1653_, v_inst_1654_, v___x_1657_, v_l_1655_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_ofArray(lean_object* v_00_u03b1_1659_, lean_object* v_inst_1660_, lean_object* v_inst_1661_, lean_object* v_l_1662_){
_start:
{
lean_object* v___f_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___f_1663_ = ((lean_object*)(l_Std_HashSet_ofArray___redArg___closed__1));
v___x_1664_ = lean_obj_once(&l_Std_HashSet_instEmptyCollection___closed__2, &l_Std_HashSet_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_instEmptyCollection___closed__2);
v___x_1665_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1663_, v_inst_1660_, v_inst_1661_, v___x_1664_, v_l_1662_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg(lean_object* v_m_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___redArg___boxed(lean_object* v_m_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Std_HashSet_Internal_numBuckets___redArg(v_m_1668_);
lean_dec_ref(v_m_1668_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets(lean_object* v_00_u03b1_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v_m_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_, lean_object* v_m_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Std_HashSet_Internal_numBuckets(v_00_u03b1_1675_, v_x_1676_, v_x_1677_, v_m_1678_);
lean_dec_ref(v_m_1678_);
lean_dec_ref(v_x_1677_);
lean_dec_ref(v_x_1676_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__1(lean_object* v___f_1683_, lean_object* v_inst_1684_, lean_object* v_m_1685_, lean_object* v_prec_1686_){
_start:
{
lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1687_ = ((lean_object*)(l_Std_HashSet_instRepr___redArg___lam__1___closed__1));
v___x_1688_ = lean_box(0);
v___x_1689_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__10));
v___x_1690_ = lean_unsigned_to_nat(0u);
v___x_1691_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_1689_, v___f_1683_, v_m_1685_, v___x_1688_, v___x_1690_);
v___x_1692_ = l_List_repr___redArg(v_inst_1684_, v___x_1691_);
v___x_1693_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1693_, 0, v___x_1687_);
lean_ctor_set(v___x_1693_, 1, v___x_1692_);
v___x_1694_ = l_Repr_addAppParen(v___x_1693_, v_prec_1686_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg___lam__1___boxed(lean_object* v___f_1695_, lean_object* v_inst_1696_, lean_object* v_m_1697_, lean_object* v_prec_1698_){
_start:
{
lean_object* v_res_1699_; 
v_res_1699_ = l_Std_HashSet_instRepr___redArg___lam__1(v___f_1695_, v_inst_1696_, v_m_1697_, v_prec_1698_);
lean_dec(v_prec_1698_);
lean_dec_ref(v_m_1697_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___redArg(lean_object* v_inst_1700_){
_start:
{
lean_object* v___f_1701_; lean_object* v___f_1702_; 
v___f_1701_ = ((lean_object*)(l_Std_HashSet_toList___redArg___closed__0));
v___f_1702_ = lean_alloc_closure((void*)(l_Std_HashSet_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1702_, 0, v___f_1701_);
lean_closure_set(v___f_1702_, 1, v_inst_1700_);
return v___f_1702_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr(lean_object* v_00_u03b1_1703_, lean_object* v_inst_1704_, lean_object* v_inst_1705_, lean_object* v_inst_1706_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Std_HashSet_instRepr___redArg(v_inst_1706_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_instRepr___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_inst_1709_, lean_object* v_inst_1710_, lean_object* v_inst_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Std_HashSet_instRepr(v_00_u03b1_1708_, v_inst_1709_, v_inst_1710_, v_inst_1711_);
lean_dec_ref(v_inst_1710_);
lean_dec_ref(v_inst_1709_);
return v_res_1712_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashSet_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashSet_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashSet_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
