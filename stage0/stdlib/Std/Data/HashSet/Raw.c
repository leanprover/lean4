// Lean compiler output
// Module: Std.Data.HashSet.Raw
// Imports: public import Std.Data.HashMap.Raw
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
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqPUnit___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_Raw_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_HashSet_Raw_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instEmptyCollection___closed__1;
static lean_once_cell_t l_Std_HashSet_Raw_instEmptyCollection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instEmptyCollection___closed__2;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited(lean_object*);
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__0 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "HashSet"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__1 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__2 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__2_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__3 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__3_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_0),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 195, 212, 176, 236, 184, 63, 58)}};
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_1),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(186, 185, 85, 79, 168, 190, 254, 250)}};
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__4_value_aux_2),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(84, 53, 251, 222, 148, 252, 181, 241)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__4 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__4_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__5 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__5_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__6 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__6_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__7 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__7_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__7_value)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__8 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__8_value;
static const lean_string_object l_Std_HashSet_Raw_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__9 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__10 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__10_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__11 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__6_value),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__8_value),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__12 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__12_value;
static const lean_ctor_object l_Std_HashSet_Raw_term___x7em___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__4_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__12_value)}};
static const lean_object* l_Std_HashSet_Raw_term___x7em___00__closed__13 = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Std_HashSet_Raw_term___x7em__ = (const lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__13_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_0),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_1),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value_aux_2),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value;
static lean_once_cell_t l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_0),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 195, 212, 176, 236, 184, 63, 58)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_1),((lean_object*)&l_Std_HashSet_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(186, 185, 85, 79, 168, 190, 254, 250)}};
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value_aux_2),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(149, 151, 195, 206, 178, 68, 5, 119)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__8_value)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__9_value),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__11_value)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12_value;
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1 = (const lean_object*)&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1;
static lean_once_cell_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__2;
static lean_once_cell_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__3;
static lean_once_cell_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_Raw_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__1_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__2 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__2_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__3 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__3_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__4 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__4_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__5 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__5_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__6 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__6_value;
static const lean_closure_object l_Std_HashSet_Raw_toList___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__7 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__7_value;
static const lean_ctor_object l_Std_HashSet_Raw_toList___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__1_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__2_value)}};
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__8 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__8_value;
static const lean_ctor_object l_Std_HashSet_Raw_toList___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__8_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__3_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__4_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__5_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__6_value)}};
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__9 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__9_value;
static const lean_ctor_object l_Std_HashSet_Raw_toList___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__9_value),((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__7_value)}};
static const lean_object* l_Std_HashSet_Raw_toList___redArg___closed__10 = (const lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_Raw_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__10_value)} };
static const lean_object* l_Std_HashSet_Raw_ofList___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_Raw_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashSet_Raw_ofList___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_Raw_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_filter___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_Raw_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashSet_Raw_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashSet_Raw_toArray___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_Raw_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__10_value)} };
static const lean_object* l_Std_HashSet_Raw_union___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashSet_Raw_beq___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashSet_Raw_beq___redArg___closed__0;
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_HashSet_Raw_all___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashSet_Raw_all___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_all___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashSet_Raw_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_toList___redArg___closed__10_value)} };
static const lean_object* l_Std_HashSet_Raw_ofArray___redArg___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_ofArray___redArg___closed__0_value;
static const lean_closure_object l_Std_HashSet_Raw_ofArray___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_ofArray___redArg___closed__0_value)} };
static const lean_object* l_Std_HashSet_Raw_ofArray___redArg___closed__1 = (const lean_object*)&l_Std_HashSet_Raw_ofArray___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___boxed(lean_object*, lean_object*);
static const lean_string_object l_Std_HashSet_Raw_instRepr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.HashSet.Raw.ofList "};
static const lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_HashSet_Raw_instRepr___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_HashSet_Raw_instRepr___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_HashSet_Raw_instRepr___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_HashSet_Raw_instRepr___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_HashSet_Raw_emptyWithCapacity___redArg(v_capacity_13_);
lean_dec(v_capacity_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity(lean_object* v_00_u03b1_15_, lean_object* v_capacity_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v_cellCount_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; 
v___x_17_ = lean_unsigned_to_nat(4u);
v___x_18_ = lean_nat_mul(v_capacity_16_, v___x_17_);
v___x_19_ = lean_unsigned_to_nat(2u);
v___x_20_ = lean_nat_add(v___x_18_, v___x_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_unsigned_to_nat(3u);
v___x_22_ = lean_nat_div(v___x_20_, v___x_21_);
lean_dec(v___x_20_);
v_cellCount_23_ = l_Nat_nextPowerOfTwo(v___x_22_);
lean_dec(v___x_22_);
v___x_24_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_23_);
v___x_25_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_23_);
v___x_26_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_23_);
v___x_27_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_27_, 0, v___x_24_);
lean_ctor_set(v___x_27_, 1, v___x_25_);
lean_ctor_set(v___x_27_, 2, v___x_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_emptyWithCapacity___boxed(lean_object* v_00_u03b1_28_, lean_object* v_capacity_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Std_HashSet_Raw_emptyWithCapacity(v_00_u03b1_28_, v_capacity_29_);
lean_dec(v_capacity_29_);
return v_res_30_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v_cellCount_31_; lean_object* v___x_32_; 
v_cellCount_31_ = lean_unsigned_to_nat(16u);
v___x_32_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_31_);
return v___x_32_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v_cellCount_33_; lean_object* v___x_34_; 
v_cellCount_33_ = lean_unsigned_to_nat(16u);
v___x_34_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instEmptyCollection___closed__2(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_35_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__1, &l_Std_HashSet_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__1);
v___x_36_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__0, &l_Std_HashSet_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0);
v___x_37_ = lean_unsigned_to_nat(0u);
v___x_38_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instEmptyCollection(lean_object* v_00_u03b1_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__2, &l_Std_HashSet_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__2);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInhabited(lean_object* v_00_u03b1_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__2, &l_Std_HashSet_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__2);
return v___x_42_;
}
}
static lean_object* _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_83_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__5));
v___x_84_ = l_String_toRawSubstring_x27(v___x_83_);
return v___x_84_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(lean_object* v_x_106_, lean_object* v_a_107_, lean_object* v_a_108_){
_start:
{
lean_object* v___x_109_; uint8_t v___x_110_; 
v___x_109_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__4));
lean_inc(v_x_106_);
v___x_110_ = l_Lean_Syntax_isOfKind(v_x_106_, v___x_109_);
if (v___x_110_ == 0)
{
lean_object* v___x_111_; lean_object* v___x_112_; 
lean_dec(v_x_106_);
v___x_111_ = lean_box(1);
v___x_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set(v___x_112_, 1, v_a_108_);
return v___x_112_;
}
else
{
lean_object* v_quotContext_113_; lean_object* v_currMacroScope_114_; lean_object* v_ref_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; uint8_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v_quotContext_113_ = lean_ctor_get(v_a_107_, 1);
v_currMacroScope_114_ = lean_ctor_get(v_a_107_, 2);
v_ref_115_ = lean_ctor_get(v_a_107_, 5);
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = l_Lean_Syntax_getArg(v_x_106_, v___x_116_);
v___x_118_ = lean_unsigned_to_nat(2u);
v___x_119_ = l_Lean_Syntax_getArg(v_x_106_, v___x_118_);
lean_dec(v_x_106_);
v___x_120_ = 0;
v___x_121_ = l_Lean_SourceInfo_fromRef(v_ref_115_, v___x_120_);
v___x_122_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4));
v___x_123_ = lean_obj_once(&l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6, &l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__6);
v___x_124_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_114_);
lean_inc(v_quotContext_113_);
v___x_125_ = l_Lean_addMacroScope(v_quotContext_113_, v___x_124_, v_currMacroScope_114_);
v___x_126_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__12));
lean_inc_n(v___x_121_, 2);
v___x_127_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_127_, 0, v___x_121_);
lean_ctor_set(v___x_127_, 1, v___x_123_);
lean_ctor_set(v___x_127_, 2, v___x_125_);
lean_ctor_set(v___x_127_, 3, v___x_126_);
v___x_128_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__14));
v___x_129_ = l_Lean_Syntax_node2(v___x_121_, v___x_128_, v___x_117_, v___x_119_);
v___x_130_ = l_Lean_Syntax_node2(v___x_121_, v___x_122_, v___x_127_, v___x_129_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_108_);
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___boxed(lean_object* v_x_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1(v_x_132_, v_a_133_, v_a_134_);
lean_dec_ref(v_a_133_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(lean_object* v_x_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_142_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______macroRules__Std__HashSet__Raw__term___x7em____1___closed__4));
lean_inc(v_x_139_);
v___x_143_ = l_Lean_Syntax_isOfKind(v_x_139_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v_x_139_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_a_141_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_146_ = lean_unsigned_to_nat(0u);
v___x_147_ = l_Lean_Syntax_getArg(v_x_139_, v___x_146_);
v___x_148_ = ((lean_object*)(l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___closed__1));
lean_inc(v___x_147_);
v___x_149_ = l_Lean_Syntax_isOfKind(v___x_147_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v___x_147_);
lean_dec(v_x_139_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_a_141_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = l_Lean_Syntax_getArg(v_x_139_, v___x_152_);
lean_dec(v_x_139_);
v___x_154_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_153_);
v___x_155_ = l_Lean_Syntax_matchesNull(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v___x_153_);
lean_dec(v___x_147_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_141_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v_ref_160_; uint8_t v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_158_ = l_Lean_Syntax_getArg(v___x_153_, v___x_146_);
v___x_159_ = l_Lean_Syntax_getArg(v___x_153_, v___x_152_);
lean_dec(v___x_153_);
v_ref_160_ = l_Lean_replaceRef(v___x_147_, v_a_140_);
lean_dec(v___x_147_);
v___x_161_ = 0;
v___x_162_ = l_Lean_SourceInfo_fromRef(v_ref_160_, v___x_161_);
lean_dec(v_ref_160_);
v___x_163_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__4));
v___x_164_ = ((lean_object*)(l_Std_HashSet_Raw_term___x7em___00__closed__7));
lean_inc(v___x_162_);
v___x_165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_162_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = l_Lean_Syntax_node3(v___x_162_, v___x_163_, v___x_158_, v___x_165_, v___x_159_);
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_141_);
return v___x_167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1___boxed(lean_object* v_x_168_, lean_object* v_a_169_, lean_object* v_a_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Std_HashSet_Raw___aux__Std__Data__HashSet__Raw______unexpand__Std__HashSet__Raw__Equiv__1(v_x_168_, v_a_169_, v_a_170_);
lean_dec(v_a_169_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert___redArg(lean_object* v_inst_172_, lean_object* v_inst_173_, lean_object* v_m_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_size_176_; lean_object* v_keyArray_177_; lean_object* v___x_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_size_176_ = lean_ctor_get(v_m_174_, 0);
v_keyArray_177_ = lean_ctor_get(v_m_174_, 1);
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_179_ = lean_array_get_size(v_keyArray_177_);
v___x_180_ = lean_nat_dec_lt(v___x_178_, v___x_179_);
if (v___x_180_ == 0)
{
lean_dec(v_a_175_);
lean_dec_ref(v_inst_173_);
lean_dec_ref(v_inst_172_);
return v_m_174_;
}
else
{
lean_object* v___x_181_; lean_object* v___y_183_; lean_object* v_i_184_; lean_object* v___y_190_; lean_object* v___y_199_; lean_object* v_i_200_; lean_object* v___x_214_; 
v___x_181_ = lean_box(0);
lean_inc(v_a_175_);
lean_inc_ref(v_inst_173_);
lean_inc_ref(v_inst_172_);
v___x_214_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_172_, v_inst_173_, v_m_174_, v_a_175_);
switch(lean_obj_tag(v___x_214_))
{
case 0:
{
lean_dec_ref_known(v___x_214_, 3);
lean_dec(v_a_175_);
lean_dec_ref(v_inst_173_);
lean_dec_ref(v_inst_172_);
return v_m_174_;
}
case 1:
{
lean_object* v_index_215_; lean_object* v___x_216_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_index_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_index_215_);
lean_dec_ref_known(v___x_214_, 1);
v___x_216_ = lean_unsigned_to_nat(1u);
v___x_217_ = lean_nat_add(v_size_176_, v___x_216_);
v___x_218_ = lean_nat_dec_lt(v___x_217_, v___x_179_);
if (v___x_218_ == 0)
{
lean_dec(v___x_217_);
lean_dec(v_index_215_);
goto v___jp_205_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v___x_219_ = lean_unsigned_to_nat(4u);
v___x_220_ = lean_nat_mul(v___x_217_, v___x_219_);
v___x_221_ = lean_unsigned_to_nat(3u);
v___x_222_ = lean_nat_mul(v___x_179_, v___x_221_);
v___x_223_ = lean_nat_dec_le(v___x_220_, v___x_222_);
lean_dec(v___x_222_);
lean_dec(v___x_220_);
if (v___x_223_ == 0)
{
lean_dec(v___x_217_);
lean_dec(v_index_215_);
goto v___jp_205_;
}
else
{
lean_object* v___x_224_; 
lean_dec_ref(v_inst_173_);
lean_dec_ref(v_inst_172_);
v___x_224_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_174_, v___x_217_, v_index_215_, v_a_175_, v___x_181_);
lean_dec(v_index_215_);
return v___x_224_;
}
}
}
default: 
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_size_176_, v___x_225_);
v___x_227_ = lean_nat_dec_lt(v___x_226_, v___x_179_);
if (v___x_227_ == 0)
{
lean_object* v___x_228_; 
lean_dec(v___x_226_);
lean_inc_ref(v_inst_173_);
lean_inc_ref(v_inst_172_);
v___x_228_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_172_, v_inst_173_, v_m_174_);
v___y_190_ = v___x_228_;
goto v___jp_189_;
}
else
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_229_ = lean_unsigned_to_nat(4u);
v___x_230_ = lean_nat_mul(v___x_226_, v___x_229_);
lean_dec(v___x_226_);
v___x_231_ = lean_unsigned_to_nat(3u);
v___x_232_ = lean_nat_mul(v___x_179_, v___x_231_);
v___x_233_ = lean_nat_dec_le(v___x_230_, v___x_232_);
lean_dec(v___x_232_);
lean_dec(v___x_230_);
if (v___x_233_ == 0)
{
lean_object* v___x_234_; 
lean_inc_ref(v_inst_173_);
lean_inc_ref(v_inst_172_);
v___x_234_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_172_, v_inst_173_, v_m_174_);
v___y_190_ = v___x_234_;
goto v___jp_189_;
}
else
{
v___y_190_ = v_m_174_;
goto v___jp_189_;
}
}
}
}
v___jp_182_:
{
lean_object* v_size_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_size_185_ = lean_ctor_get(v___y_183_, 0);
v___x_186_ = lean_unsigned_to_nat(1u);
v___x_187_ = lean_nat_add(v_size_185_, v___x_186_);
v___x_188_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_183_, v___x_187_, v_i_184_, v_a_175_, v___x_181_);
lean_dec(v_i_184_);
return v___x_188_;
}
v___jp_189_:
{
lean_object* v___x_191_; 
lean_inc(v_a_175_);
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_172_, v_inst_173_, v___y_190_, v_a_175_);
switch(lean_obj_tag(v___x_191_))
{
case 0:
{
lean_object* v_index_192_; lean_object* v_size_193_; lean_object* v___x_194_; 
v_index_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_index_192_);
lean_dec_ref_known(v___x_191_, 3);
v_size_193_ = lean_ctor_get(v___y_190_, 0);
lean_inc(v_size_193_);
v___x_194_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_190_, v_size_193_, v_index_192_, v_a_175_, v___x_181_);
lean_dec(v_index_192_);
return v___x_194_;
}
case 1:
{
lean_object* v_index_195_; 
v_index_195_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_index_195_);
lean_dec_ref_known(v___x_191_, 1);
v___y_183_ = v___y_190_;
v_i_184_ = v_index_195_;
goto v___jp_182_;
}
default: 
{
lean_object* v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_190_, v___x_178_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_index_197_; 
v_index_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_index_197_);
lean_dec_ref_known(v___x_196_, 1);
v___y_183_ = v___y_190_;
v_i_184_ = v_index_197_;
goto v___jp_182_;
}
else
{
lean_dec(v_a_175_);
return v___y_190_;
}
}
}
}
v___jp_198_:
{
lean_object* v_size_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v_size_201_ = lean_ctor_get(v___y_199_, 0);
v___x_202_ = lean_unsigned_to_nat(1u);
v___x_203_ = lean_nat_add(v_size_201_, v___x_202_);
v___x_204_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_199_, v___x_203_, v_i_200_, v_a_175_, v___x_181_);
lean_dec(v_i_200_);
return v___x_204_;
}
v___jp_205_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_inc_ref(v_inst_173_);
lean_inc_ref(v_inst_172_);
v___x_206_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_172_, v_inst_173_, v_m_174_);
lean_inc(v_a_175_);
v___x_207_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_172_, v_inst_173_, v___x_206_, v_a_175_);
switch(lean_obj_tag(v___x_207_))
{
case 0:
{
lean_object* v_index_208_; lean_object* v_size_209_; lean_object* v___x_210_; 
v_index_208_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_index_208_);
lean_dec_ref_known(v___x_207_, 3);
v_size_209_ = lean_ctor_get(v___x_206_, 0);
lean_inc(v_size_209_);
v___x_210_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_206_, v_size_209_, v_index_208_, v_a_175_, v___x_181_);
lean_dec(v_index_208_);
return v___x_210_;
}
case 1:
{
lean_object* v_index_211_; 
v_index_211_ = lean_ctor_get(v___x_207_, 0);
lean_inc(v_index_211_);
lean_dec_ref_known(v___x_207_, 1);
v___y_199_ = v___x_206_;
v_i_200_ = v_index_211_;
goto v___jp_198_;
}
default: 
{
lean_object* v___x_212_; 
v___x_212_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_206_, v___x_178_);
if (lean_obj_tag(v___x_212_) == 0)
{
lean_object* v_index_213_; 
v_index_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_index_213_);
lean_dec_ref_known(v___x_212_, 1);
v___y_199_ = v___x_206_;
v_i_200_ = v_index_213_;
goto v___jp_198_;
}
else
{
lean_dec(v_a_175_);
return v___x_206_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insert(lean_object* v_00_u03b1_235_, lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_m_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_size_240_; lean_object* v_keyArray_241_; lean_object* v___x_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_size_240_ = lean_ctor_get(v_m_238_, 0);
v_keyArray_241_ = lean_ctor_get(v_m_238_, 1);
v___x_242_ = lean_unsigned_to_nat(0u);
v___x_243_ = lean_array_get_size(v_keyArray_241_);
v___x_244_ = lean_nat_dec_lt(v___x_242_, v___x_243_);
if (v___x_244_ == 0)
{
lean_dec(v_a_239_);
lean_dec_ref(v_inst_237_);
lean_dec_ref(v_inst_236_);
return v_m_238_;
}
else
{
lean_object* v___x_245_; lean_object* v___y_247_; lean_object* v_i_248_; lean_object* v___y_254_; lean_object* v___y_263_; lean_object* v_i_264_; lean_object* v___x_278_; 
v___x_245_ = lean_box(0);
lean_inc(v_a_239_);
lean_inc_ref(v_inst_237_);
lean_inc_ref(v_inst_236_);
v___x_278_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_236_, v_inst_237_, v_m_238_, v_a_239_);
switch(lean_obj_tag(v___x_278_))
{
case 0:
{
lean_dec_ref_known(v___x_278_, 3);
lean_dec(v_a_239_);
lean_dec_ref(v_inst_237_);
lean_dec_ref(v_inst_236_);
return v_m_238_;
}
case 1:
{
lean_object* v_index_279_; lean_object* v___x_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_index_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_index_279_);
lean_dec_ref_known(v___x_278_, 1);
v___x_280_ = lean_unsigned_to_nat(1u);
v___x_281_ = lean_nat_add(v_size_240_, v___x_280_);
v___x_282_ = lean_nat_dec_lt(v___x_281_, v___x_243_);
if (v___x_282_ == 0)
{
lean_dec(v___x_281_);
lean_dec(v_index_279_);
goto v___jp_269_;
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_283_ = lean_unsigned_to_nat(4u);
v___x_284_ = lean_nat_mul(v___x_281_, v___x_283_);
v___x_285_ = lean_unsigned_to_nat(3u);
v___x_286_ = lean_nat_mul(v___x_243_, v___x_285_);
v___x_287_ = lean_nat_dec_le(v___x_284_, v___x_286_);
lean_dec(v___x_286_);
lean_dec(v___x_284_);
if (v___x_287_ == 0)
{
lean_dec(v___x_281_);
lean_dec(v_index_279_);
goto v___jp_269_;
}
else
{
lean_object* v___x_288_; 
lean_dec_ref(v_inst_237_);
lean_dec_ref(v_inst_236_);
v___x_288_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_238_, v___x_281_, v_index_279_, v_a_239_, v___x_245_);
lean_dec(v_index_279_);
return v___x_288_;
}
}
}
default: 
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_size_240_, v___x_289_);
v___x_291_ = lean_nat_dec_lt(v___x_290_, v___x_243_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
lean_dec(v___x_290_);
lean_inc_ref(v_inst_237_);
lean_inc_ref(v_inst_236_);
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_236_, v_inst_237_, v_m_238_);
v___y_254_ = v___x_292_;
goto v___jp_253_;
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; 
v___x_293_ = lean_unsigned_to_nat(4u);
v___x_294_ = lean_nat_mul(v___x_290_, v___x_293_);
lean_dec(v___x_290_);
v___x_295_ = lean_unsigned_to_nat(3u);
v___x_296_ = lean_nat_mul(v___x_243_, v___x_295_);
v___x_297_ = lean_nat_dec_le(v___x_294_, v___x_296_);
lean_dec(v___x_296_);
lean_dec(v___x_294_);
if (v___x_297_ == 0)
{
lean_object* v___x_298_; 
lean_inc_ref(v_inst_237_);
lean_inc_ref(v_inst_236_);
v___x_298_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_236_, v_inst_237_, v_m_238_);
v___y_254_ = v___x_298_;
goto v___jp_253_;
}
else
{
v___y_254_ = v_m_238_;
goto v___jp_253_;
}
}
}
}
v___jp_246_:
{
lean_object* v_size_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_size_249_ = lean_ctor_get(v___y_247_, 0);
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_nat_add(v_size_249_, v___x_250_);
v___x_252_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_247_, v___x_251_, v_i_248_, v_a_239_, v___x_245_);
lean_dec(v_i_248_);
return v___x_252_;
}
v___jp_253_:
{
lean_object* v___x_255_; 
lean_inc(v_a_239_);
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_236_, v_inst_237_, v___y_254_, v_a_239_);
switch(lean_obj_tag(v___x_255_))
{
case 0:
{
lean_object* v_index_256_; lean_object* v_size_257_; lean_object* v___x_258_; 
v_index_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_index_256_);
lean_dec_ref_known(v___x_255_, 3);
v_size_257_ = lean_ctor_get(v___y_254_, 0);
lean_inc(v_size_257_);
v___x_258_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_254_, v_size_257_, v_index_256_, v_a_239_, v___x_245_);
lean_dec(v_index_256_);
return v___x_258_;
}
case 1:
{
lean_object* v_index_259_; 
v_index_259_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_index_259_);
lean_dec_ref_known(v___x_255_, 1);
v___y_247_ = v___y_254_;
v_i_248_ = v_index_259_;
goto v___jp_246_;
}
default: 
{
lean_object* v___x_260_; 
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_254_, v___x_242_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v_index_261_; 
v_index_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_index_261_);
lean_dec_ref_known(v___x_260_, 1);
v___y_247_ = v___y_254_;
v_i_248_ = v_index_261_;
goto v___jp_246_;
}
else
{
lean_dec(v_a_239_);
return v___y_254_;
}
}
}
}
v___jp_262_:
{
lean_object* v_size_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v_size_265_ = lean_ctor_get(v___y_263_, 0);
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_nat_add(v_size_265_, v___x_266_);
v___x_268_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_263_, v___x_267_, v_i_264_, v_a_239_, v___x_245_);
lean_dec(v_i_264_);
return v___x_268_;
}
v___jp_269_:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
lean_inc_ref(v_inst_237_);
lean_inc_ref(v_inst_236_);
v___x_270_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_236_, v_inst_237_, v_m_238_);
lean_inc(v_a_239_);
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_236_, v_inst_237_, v___x_270_, v_a_239_);
switch(lean_obj_tag(v___x_271_))
{
case 0:
{
lean_object* v_index_272_; lean_object* v_size_273_; lean_object* v___x_274_; 
v_index_272_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_index_272_);
lean_dec_ref_known(v___x_271_, 3);
v_size_273_ = lean_ctor_get(v___x_270_, 0);
lean_inc(v_size_273_);
v___x_274_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_270_, v_size_273_, v_index_272_, v_a_239_, v___x_245_);
lean_dec(v_index_272_);
return v___x_274_;
}
case 1:
{
lean_object* v_index_275_; 
v_index_275_ = lean_ctor_get(v___x_271_, 0);
lean_inc(v_index_275_);
lean_dec_ref_known(v___x_271_, 1);
v___y_263_ = v___x_270_;
v_i_264_ = v_index_275_;
goto v___jp_262_;
}
default: 
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_270_, v___x_242_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_index_277_; 
v_index_277_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_index_277_);
lean_dec_ref_known(v___x_276_, 1);
v___y_263_ = v___x_270_;
v_i_264_ = v_index_277_;
goto v___jp_262_;
}
else
{
lean_dec(v_a_239_);
return v___x_270_;
}
}
}
}
}
}
}
static lean_object* _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__0, &l_Std_HashSet_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__0);
v___x_300_ = lean_array_get_size(v___x_299_);
return v___x_300_;
}
}
static uint8_t _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v___x_301_ = lean_obj_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_302_ = lean_unsigned_to_nat(0u);
v___x_303_ = lean_nat_dec_lt(v___x_302_, v___x_301_);
return v___x_303_;
}
}
static uint8_t _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_obj_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_305_ = lean_unsigned_to_nat(1u);
v___x_306_ = lean_nat_dec_lt(v___x_305_, v___x_304_);
return v___x_306_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_307_ = lean_unsigned_to_nat(3u);
v___x_308_ = lean_obj_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_309_ = lean_nat_mul(v___x_308_, v___x_307_);
return v___x_309_;
}
}
static uint8_t _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_310_ = lean_obj_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__3, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__3_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__3);
v___x_311_ = lean_unsigned_to_nat(4u);
v___x_312_ = lean_nat_dec_le(v___x_311_, v___x_310_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_316_ = lean_unsigned_to_nat(0u);
v___x_317_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__2, &l_Std_HashSet_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__2);
v___x_318_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_318_ == 0)
{
lean_dec(v_a_315_);
lean_dec_ref(v_inst_314_);
lean_dec_ref(v_inst_313_);
return v___x_317_;
}
else
{
lean_object* v___x_319_; lean_object* v___y_321_; lean_object* v_i_322_; lean_object* v___y_328_; lean_object* v___y_337_; lean_object* v_i_338_; lean_object* v___x_352_; 
v___x_319_ = lean_box(0);
lean_inc(v_a_315_);
lean_inc_ref(v_inst_314_);
lean_inc_ref(v_inst_313_);
v___x_352_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_313_, v_inst_314_, v___x_317_, v_a_315_);
switch(lean_obj_tag(v___x_352_))
{
case 0:
{
lean_dec_ref_known(v___x_352_, 3);
lean_dec(v_a_315_);
lean_dec_ref(v_inst_314_);
lean_dec_ref(v_inst_313_);
return v___x_317_;
}
case 1:
{
lean_object* v_index_353_; lean_object* v___x_354_; uint8_t v___x_355_; 
v_index_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_index_353_);
lean_dec_ref_known(v___x_352_, 1);
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__2, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__2_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__2);
if (v___x_355_ == 0)
{
lean_dec(v_index_353_);
goto v___jp_343_;
}
else
{
uint8_t v___x_356_; 
v___x_356_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__4, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__4_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__4);
if (v___x_356_ == 0)
{
lean_dec(v_index_353_);
goto v___jp_343_;
}
else
{
lean_object* v___x_357_; 
lean_dec_ref(v_inst_314_);
lean_dec_ref(v_inst_313_);
v___x_357_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_317_, v___x_354_, v_index_353_, v_a_315_, v___x_319_);
lean_dec(v_index_353_);
return v___x_357_;
}
}
}
default: 
{
uint8_t v___x_358_; 
v___x_358_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__2, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__2_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__2);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; 
lean_inc_ref(v_inst_314_);
lean_inc_ref(v_inst_313_);
v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_313_, v_inst_314_, v___x_317_);
v___y_328_ = v___x_359_;
goto v___jp_327_;
}
else
{
uint8_t v___x_360_; 
v___x_360_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__4, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__4_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__4);
if (v___x_360_ == 0)
{
lean_object* v___x_361_; 
lean_inc_ref(v_inst_314_);
lean_inc_ref(v_inst_313_);
v___x_361_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_313_, v_inst_314_, v___x_317_);
v___y_328_ = v___x_361_;
goto v___jp_327_;
}
else
{
v___y_328_ = v___x_317_;
goto v___jp_327_;
}
}
}
}
v___jp_320_:
{
lean_object* v_size_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v_size_323_ = lean_ctor_get(v___y_321_, 0);
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_nat_add(v_size_323_, v___x_324_);
v___x_326_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_321_, v___x_325_, v_i_322_, v_a_315_, v___x_319_);
lean_dec(v_i_322_);
return v___x_326_;
}
v___jp_327_:
{
lean_object* v___x_329_; 
lean_inc(v_a_315_);
v___x_329_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_313_, v_inst_314_, v___y_328_, v_a_315_);
switch(lean_obj_tag(v___x_329_))
{
case 0:
{
lean_object* v_index_330_; lean_object* v_size_331_; lean_object* v___x_332_; 
v_index_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_index_330_);
lean_dec_ref_known(v___x_329_, 3);
v_size_331_ = lean_ctor_get(v___y_328_, 0);
lean_inc(v_size_331_);
v___x_332_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_328_, v_size_331_, v_index_330_, v_a_315_, v___x_319_);
lean_dec(v_index_330_);
return v___x_332_;
}
case 1:
{
lean_object* v_index_333_; 
v_index_333_ = lean_ctor_get(v___x_329_, 0);
lean_inc(v_index_333_);
lean_dec_ref_known(v___x_329_, 1);
v___y_321_ = v___y_328_;
v_i_322_ = v_index_333_;
goto v___jp_320_;
}
default: 
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_328_, v___x_316_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_index_335_; 
v_index_335_ = lean_ctor_get(v___x_334_, 0);
lean_inc(v_index_335_);
lean_dec_ref_known(v___x_334_, 1);
v___y_321_ = v___y_328_;
v_i_322_ = v_index_335_;
goto v___jp_320_;
}
else
{
lean_dec(v_a_315_);
return v___y_328_;
}
}
}
}
v___jp_336_:
{
lean_object* v_size_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_size_339_ = lean_ctor_get(v___y_337_, 0);
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_add(v_size_339_, v___x_340_);
v___x_342_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_337_, v___x_341_, v_i_338_, v_a_315_, v___x_319_);
lean_dec(v_i_338_);
return v___x_342_;
}
v___jp_343_:
{
lean_object* v___x_344_; lean_object* v___x_345_; 
lean_inc_ref(v_inst_314_);
lean_inc_ref(v_inst_313_);
v___x_344_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_313_, v_inst_314_, v___x_317_);
lean_inc(v_a_315_);
v___x_345_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_313_, v_inst_314_, v___x_344_, v_a_315_);
switch(lean_obj_tag(v___x_345_))
{
case 0:
{
lean_object* v_index_346_; lean_object* v_size_347_; lean_object* v___x_348_; 
v_index_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_index_346_);
lean_dec_ref_known(v___x_345_, 3);
v_size_347_ = lean_ctor_get(v___x_344_, 0);
lean_inc(v_size_347_);
v___x_348_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_344_, v_size_347_, v_index_346_, v_a_315_, v___x_319_);
lean_dec(v_index_346_);
return v___x_348_;
}
case 1:
{
lean_object* v_index_349_; 
v_index_349_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_index_349_);
lean_dec_ref_known(v___x_345_, 1);
v___y_337_ = v___x_344_;
v_i_338_ = v_index_349_;
goto v___jp_336_;
}
default: 
{
lean_object* v___x_350_; 
v___x_350_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_344_, v___x_316_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_index_351_; 
v_index_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_index_351_);
lean_dec_ref_known(v___x_350_, 1);
v___y_337_ = v___x_344_;
v_i_338_ = v_index_351_;
goto v___jp_336_;
}
else
{
lean_dec(v_a_315_);
return v___x_344_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg(lean_object* v_inst_362_, lean_object* v_inst_363_){
_start:
{
lean_object* v___f_364_; 
v___f_364_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_364_, 0, v_inst_362_);
lean_closure_set(v___f_364_, 1, v_inst_363_);
return v___f_364_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSingletonOfBEqOfHashable(lean_object* v_00_u03b1_365_, lean_object* v_inst_366_, lean_object* v_inst_367_){
_start:
{
lean_object* v___f_368_; 
v___f_368_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_368_, 0, v_inst_366_);
lean_closure_set(v___f_368_, 1, v_inst_367_);
return v___f_368_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_a_371_, lean_object* v_s_372_){
_start:
{
lean_object* v_size_373_; lean_object* v_keyArray_374_; lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_size_373_ = lean_ctor_get(v_s_372_, 0);
v_keyArray_374_ = lean_ctor_get(v_s_372_, 1);
v___x_375_ = lean_unsigned_to_nat(0u);
v___x_376_ = lean_array_get_size(v_keyArray_374_);
v___x_377_ = lean_nat_dec_lt(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
lean_dec(v_a_371_);
lean_dec_ref(v_inst_370_);
lean_dec_ref(v_inst_369_);
return v_s_372_;
}
else
{
lean_object* v___x_378_; lean_object* v___y_380_; lean_object* v_i_381_; lean_object* v___y_387_; lean_object* v___y_396_; lean_object* v_i_397_; lean_object* v___x_411_; 
v___x_378_ = lean_box(0);
lean_inc(v_a_371_);
lean_inc_ref(v_inst_370_);
lean_inc_ref(v_inst_369_);
v___x_411_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_369_, v_inst_370_, v_s_372_, v_a_371_);
switch(lean_obj_tag(v___x_411_))
{
case 0:
{
lean_dec_ref_known(v___x_411_, 3);
lean_dec(v_a_371_);
lean_dec_ref(v_inst_370_);
lean_dec_ref(v_inst_369_);
return v_s_372_;
}
case 1:
{
lean_object* v_index_412_; lean_object* v___x_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_index_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_index_412_);
lean_dec_ref_known(v___x_411_, 1);
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_nat_add(v_size_373_, v___x_413_);
v___x_415_ = lean_nat_dec_lt(v___x_414_, v___x_376_);
if (v___x_415_ == 0)
{
lean_dec(v___x_414_);
lean_dec(v_index_412_);
goto v___jp_402_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_416_ = lean_unsigned_to_nat(4u);
v___x_417_ = lean_nat_mul(v___x_414_, v___x_416_);
v___x_418_ = lean_unsigned_to_nat(3u);
v___x_419_ = lean_nat_mul(v___x_376_, v___x_418_);
v___x_420_ = lean_nat_dec_le(v___x_417_, v___x_419_);
lean_dec(v___x_419_);
lean_dec(v___x_417_);
if (v___x_420_ == 0)
{
lean_dec(v___x_414_);
lean_dec(v_index_412_);
goto v___jp_402_;
}
else
{
lean_object* v___x_421_; 
lean_dec_ref(v_inst_370_);
lean_dec_ref(v_inst_369_);
v___x_421_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_372_, v___x_414_, v_index_412_, v_a_371_, v___x_378_);
lean_dec(v_index_412_);
return v___x_421_;
}
}
}
default: 
{
lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_422_ = lean_unsigned_to_nat(1u);
v___x_423_ = lean_nat_add(v_size_373_, v___x_422_);
v___x_424_ = lean_nat_dec_lt(v___x_423_, v___x_376_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; 
lean_dec(v___x_423_);
lean_inc_ref(v_inst_370_);
lean_inc_ref(v_inst_369_);
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_369_, v_inst_370_, v_s_372_);
v___y_387_ = v___x_425_;
goto v___jp_386_;
}
else
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v___x_426_ = lean_unsigned_to_nat(4u);
v___x_427_ = lean_nat_mul(v___x_423_, v___x_426_);
lean_dec(v___x_423_);
v___x_428_ = lean_unsigned_to_nat(3u);
v___x_429_ = lean_nat_mul(v___x_376_, v___x_428_);
v___x_430_ = lean_nat_dec_le(v___x_427_, v___x_429_);
lean_dec(v___x_429_);
lean_dec(v___x_427_);
if (v___x_430_ == 0)
{
lean_object* v___x_431_; 
lean_inc_ref(v_inst_370_);
lean_inc_ref(v_inst_369_);
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_369_, v_inst_370_, v_s_372_);
v___y_387_ = v___x_431_;
goto v___jp_386_;
}
else
{
v___y_387_ = v_s_372_;
goto v___jp_386_;
}
}
}
}
v___jp_379_:
{
lean_object* v_size_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_size_382_ = lean_ctor_get(v___y_380_, 0);
v___x_383_ = lean_unsigned_to_nat(1u);
v___x_384_ = lean_nat_add(v_size_382_, v___x_383_);
v___x_385_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_380_, v___x_384_, v_i_381_, v_a_371_, v___x_378_);
lean_dec(v_i_381_);
return v___x_385_;
}
v___jp_386_:
{
lean_object* v___x_388_; 
lean_inc(v_a_371_);
v___x_388_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_369_, v_inst_370_, v___y_387_, v_a_371_);
switch(lean_obj_tag(v___x_388_))
{
case 0:
{
lean_object* v_index_389_; lean_object* v_size_390_; lean_object* v___x_391_; 
v_index_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_index_389_);
lean_dec_ref_known(v___x_388_, 3);
v_size_390_ = lean_ctor_get(v___y_387_, 0);
lean_inc(v_size_390_);
v___x_391_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_387_, v_size_390_, v_index_389_, v_a_371_, v___x_378_);
lean_dec(v_index_389_);
return v___x_391_;
}
case 1:
{
lean_object* v_index_392_; 
v_index_392_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_index_392_);
lean_dec_ref_known(v___x_388_, 1);
v___y_380_ = v___y_387_;
v_i_381_ = v_index_392_;
goto v___jp_379_;
}
default: 
{
lean_object* v___x_393_; 
v___x_393_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_387_, v___x_375_);
if (lean_obj_tag(v___x_393_) == 0)
{
lean_object* v_index_394_; 
v_index_394_ = lean_ctor_get(v___x_393_, 0);
lean_inc(v_index_394_);
lean_dec_ref_known(v___x_393_, 1);
v___y_380_ = v___y_387_;
v_i_381_ = v_index_394_;
goto v___jp_379_;
}
else
{
lean_dec(v_a_371_);
return v___y_387_;
}
}
}
}
v___jp_395_:
{
lean_object* v_size_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; 
v_size_398_ = lean_ctor_get(v___y_396_, 0);
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = lean_nat_add(v_size_398_, v___x_399_);
v___x_401_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_396_, v___x_400_, v_i_397_, v_a_371_, v___x_378_);
lean_dec(v_i_397_);
return v___x_401_;
}
v___jp_402_:
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_inc_ref(v_inst_370_);
lean_inc_ref(v_inst_369_);
v___x_403_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_369_, v_inst_370_, v_s_372_);
lean_inc(v_a_371_);
v___x_404_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_369_, v_inst_370_, v___x_403_, v_a_371_);
switch(lean_obj_tag(v___x_404_))
{
case 0:
{
lean_object* v_index_405_; lean_object* v_size_406_; lean_object* v___x_407_; 
v_index_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_index_405_);
lean_dec_ref_known(v___x_404_, 3);
v_size_406_ = lean_ctor_get(v___x_403_, 0);
lean_inc(v_size_406_);
v___x_407_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_403_, v_size_406_, v_index_405_, v_a_371_, v___x_378_);
lean_dec(v_index_405_);
return v___x_407_;
}
case 1:
{
lean_object* v_index_408_; 
v_index_408_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_index_408_);
lean_dec_ref_known(v___x_404_, 1);
v___y_396_ = v___x_403_;
v_i_397_ = v_index_408_;
goto v___jp_395_;
}
default: 
{
lean_object* v___x_409_; 
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_403_, v___x_375_);
if (lean_obj_tag(v___x_409_) == 0)
{
lean_object* v_index_410_; 
v_index_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_index_410_);
lean_dec_ref_known(v___x_409_, 1);
v___y_396_ = v___x_403_;
v_i_397_ = v_index_410_;
goto v___jp_395_;
}
else
{
lean_dec(v_a_371_);
return v___x_403_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg(lean_object* v_inst_432_, lean_object* v_inst_433_){
_start:
{
lean_object* v___f_434_; 
v___f_434_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_434_, 0, v_inst_432_);
lean_closure_set(v___f_434_, 1, v_inst_433_);
return v___f_434_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInsertOfBEqOfHashable(lean_object* v_00_u03b1_435_, lean_object* v_inst_436_, lean_object* v_inst_437_){
_start:
{
lean_object* v___f_438_; 
v___f_438_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instInsertOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_438_, 0, v_inst_436_);
lean_closure_set(v___f_438_, 1, v_inst_437_);
return v___f_438_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert___redArg(lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_m_441_, lean_object* v_a_442_){
_start:
{
lean_object* v_size_443_; lean_object* v_keyArray_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_size_443_ = lean_ctor_get(v_m_441_, 0);
v_keyArray_444_ = lean_ctor_get(v_m_441_, 1);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_array_get_size(v_keyArray_444_);
v___x_447_ = lean_nat_dec_lt(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v_a_442_);
lean_dec_ref(v_inst_440_);
lean_dec_ref(v_inst_439_);
v___x_448_ = lean_box(v___x_447_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v_m_441_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = lean_box(0);
lean_inc(v_a_442_);
lean_inc_ref(v_inst_440_);
lean_inc_ref(v_inst_439_);
v___x_451_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_439_, v_inst_440_, v_m_441_, v_a_442_);
switch(lean_obj_tag(v___x_451_))
{
case 0:
{
lean_object* v___x_452_; lean_object* v___x_453_; 
lean_dec_ref_known(v___x_451_, 3);
lean_dec(v_a_442_);
lean_dec_ref(v_inst_440_);
lean_dec_ref(v_inst_439_);
v___x_452_ = lean_box(v___x_447_);
v___x_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v_m_441_);
return v___x_453_;
}
case 1:
{
lean_object* v_index_454_; uint8_t v___x_455_; lean_object* v___y_457_; lean_object* v_i_458_; lean_object* v___x_478_; lean_object* v___x_479_; uint8_t v___x_480_; 
v_index_454_ = lean_ctor_get(v___x_451_, 0);
lean_inc(v_index_454_);
lean_dec_ref_known(v___x_451_, 1);
v___x_455_ = 0;
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_nat_add(v_size_443_, v___x_478_);
v___x_480_ = lean_nat_dec_lt(v___x_479_, v___x_446_);
if (v___x_480_ == 0)
{
lean_dec(v___x_479_);
lean_dec(v_index_454_);
goto v___jp_465_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_481_ = lean_unsigned_to_nat(4u);
v___x_482_ = lean_nat_mul(v___x_479_, v___x_481_);
v___x_483_ = lean_unsigned_to_nat(3u);
v___x_484_ = lean_nat_mul(v___x_446_, v___x_483_);
v___x_485_ = lean_nat_dec_le(v___x_482_, v___x_484_);
lean_dec(v___x_484_);
lean_dec(v___x_482_);
if (v___x_485_ == 0)
{
lean_dec(v___x_479_);
lean_dec(v_index_454_);
goto v___jp_465_;
}
else
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
lean_dec_ref(v_inst_440_);
lean_dec_ref(v_inst_439_);
v___x_486_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_441_, v___x_479_, v_index_454_, v_a_442_, v___x_450_);
lean_dec(v_index_454_);
v___x_487_ = lean_box(v___x_455_);
v___x_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___x_486_);
return v___x_488_;
}
}
v___jp_456_:
{
lean_object* v_size_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; 
v_size_459_ = lean_ctor_get(v___y_457_, 0);
v___x_460_ = lean_unsigned_to_nat(1u);
v___x_461_ = lean_nat_add(v_size_459_, v___x_460_);
v___x_462_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_457_, v___x_461_, v_i_458_, v_a_442_, v___x_450_);
lean_dec(v_i_458_);
v___x_463_ = lean_box(v___x_455_);
v___x_464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_464_, 0, v___x_463_);
lean_ctor_set(v___x_464_, 1, v___x_462_);
return v___x_464_;
}
v___jp_465_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
lean_inc_ref(v_inst_440_);
lean_inc_ref(v_inst_439_);
v___x_466_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_439_, v_inst_440_, v_m_441_);
lean_inc(v_a_442_);
v___x_467_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_439_, v_inst_440_, v___x_466_, v_a_442_);
switch(lean_obj_tag(v___x_467_))
{
case 0:
{
lean_object* v_index_468_; lean_object* v_size_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v_index_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_index_468_);
lean_dec_ref_known(v___x_467_, 3);
v_size_469_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_size_469_);
v___x_470_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_466_, v_size_469_, v_index_468_, v_a_442_, v___x_450_);
lean_dec(v_index_468_);
v___x_471_ = lean_box(v___x_455_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
lean_ctor_set(v___x_472_, 1, v___x_470_);
return v___x_472_;
}
case 1:
{
lean_object* v_index_473_; 
v_index_473_ = lean_ctor_get(v___x_467_, 0);
lean_inc(v_index_473_);
lean_dec_ref_known(v___x_467_, 1);
v___y_457_ = v___x_466_;
v_i_458_ = v_index_473_;
goto v___jp_456_;
}
default: 
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_466_, v___x_445_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_index_475_; 
v_index_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_index_475_);
lean_dec_ref_known(v___x_474_, 1);
v___y_457_ = v___x_466_;
v_i_458_ = v_index_475_;
goto v___jp_456_;
}
else
{
lean_object* v___x_476_; lean_object* v___x_477_; 
lean_dec(v_a_442_);
v___x_476_ = lean_box(v___x_455_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v___x_476_);
lean_ctor_set(v___x_477_, 1, v___x_466_);
return v___x_477_;
}
}
}
}
}
default: 
{
uint8_t v___x_489_; lean_object* v___y_491_; lean_object* v_i_492_; lean_object* v___y_500_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_489_ = 0;
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_add(v_size_443_, v___x_512_);
v___x_514_ = lean_nat_dec_lt(v___x_513_, v___x_446_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; 
lean_dec(v___x_513_);
lean_inc_ref(v_inst_440_);
lean_inc_ref(v_inst_439_);
v___x_515_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_439_, v_inst_440_, v_m_441_);
v___y_500_ = v___x_515_;
goto v___jp_499_;
}
else
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_516_ = lean_unsigned_to_nat(4u);
v___x_517_ = lean_nat_mul(v___x_513_, v___x_516_);
lean_dec(v___x_513_);
v___x_518_ = lean_unsigned_to_nat(3u);
v___x_519_ = lean_nat_mul(v___x_446_, v___x_518_);
v___x_520_ = lean_nat_dec_le(v___x_517_, v___x_519_);
lean_dec(v___x_519_);
lean_dec(v___x_517_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; 
lean_inc_ref(v_inst_440_);
lean_inc_ref(v_inst_439_);
v___x_521_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_439_, v_inst_440_, v_m_441_);
v___y_500_ = v___x_521_;
goto v___jp_499_;
}
else
{
v___y_500_ = v_m_441_;
goto v___jp_499_;
}
}
v___jp_490_:
{
lean_object* v_size_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_size_493_ = lean_ctor_get(v___y_491_, 0);
v___x_494_ = lean_unsigned_to_nat(1u);
v___x_495_ = lean_nat_add(v_size_493_, v___x_494_);
v___x_496_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_491_, v___x_495_, v_i_492_, v_a_442_, v___x_450_);
lean_dec(v_i_492_);
v___x_497_ = lean_box(v___x_489_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
lean_ctor_set(v___x_498_, 1, v___x_496_);
return v___x_498_;
}
v___jp_499_:
{
lean_object* v___x_501_; 
lean_inc(v_a_442_);
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_439_, v_inst_440_, v___y_500_, v_a_442_);
switch(lean_obj_tag(v___x_501_))
{
case 0:
{
lean_object* v_index_502_; lean_object* v_size_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_index_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_index_502_);
lean_dec_ref_known(v___x_501_, 3);
v_size_503_ = lean_ctor_get(v___y_500_, 0);
lean_inc(v_size_503_);
v___x_504_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_500_, v_size_503_, v_index_502_, v_a_442_, v___x_450_);
lean_dec(v_index_502_);
v___x_505_ = lean_box(v___x_489_);
v___x_506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_504_);
return v___x_506_;
}
case 1:
{
lean_object* v_index_507_; 
v_index_507_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_index_507_);
lean_dec_ref_known(v___x_501_, 1);
v___y_491_ = v___y_500_;
v_i_492_ = v_index_507_;
goto v___jp_490_;
}
default: 
{
lean_object* v___x_508_; 
v___x_508_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_500_, v___x_445_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v_index_509_; 
v_index_509_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_index_509_);
lean_dec_ref_known(v___x_508_, 1);
v___y_491_ = v___y_500_;
v_i_492_ = v_index_509_;
goto v___jp_490_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_dec(v_a_442_);
v___x_510_ = lean_box(v___x_489_);
v___x_511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
lean_ctor_set(v___x_511_, 1, v___y_500_);
return v___x_511_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_containsThenInsert(lean_object* v_00_u03b1_522_, lean_object* v_inst_523_, lean_object* v_inst_524_, lean_object* v_m_525_, lean_object* v_a_526_){
_start:
{
lean_object* v_size_527_; lean_object* v_keyArray_528_; lean_object* v___x_529_; lean_object* v___x_530_; uint8_t v___x_531_; 
v_size_527_ = lean_ctor_get(v_m_525_, 0);
v_keyArray_528_ = lean_ctor_get(v_m_525_, 1);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_array_get_size(v_keyArray_528_);
v___x_531_ = lean_nat_dec_lt(v___x_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_dec(v_a_526_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_inst_523_);
v___x_532_ = lean_box(v___x_531_);
v___x_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
lean_ctor_set(v___x_533_, 1, v_m_525_);
return v___x_533_;
}
else
{
lean_object* v___x_534_; lean_object* v___x_535_; 
v___x_534_ = lean_box(0);
lean_inc(v_a_526_);
lean_inc_ref(v_inst_524_);
lean_inc_ref(v_inst_523_);
v___x_535_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_523_, v_inst_524_, v_m_525_, v_a_526_);
switch(lean_obj_tag(v___x_535_))
{
case 0:
{
lean_object* v___x_536_; lean_object* v___x_537_; 
lean_dec_ref_known(v___x_535_, 3);
lean_dec(v_a_526_);
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_inst_523_);
v___x_536_ = lean_box(v___x_531_);
v___x_537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v_m_525_);
return v___x_537_;
}
case 1:
{
lean_object* v_index_538_; uint8_t v___x_539_; lean_object* v___y_541_; lean_object* v_i_542_; lean_object* v___x_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_index_538_ = lean_ctor_get(v___x_535_, 0);
lean_inc(v_index_538_);
lean_dec_ref_known(v___x_535_, 1);
v___x_539_ = 0;
v___x_562_ = lean_unsigned_to_nat(1u);
v___x_563_ = lean_nat_add(v_size_527_, v___x_562_);
v___x_564_ = lean_nat_dec_lt(v___x_563_, v___x_530_);
if (v___x_564_ == 0)
{
lean_dec(v___x_563_);
lean_dec(v_index_538_);
goto v___jp_549_;
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_565_ = lean_unsigned_to_nat(4u);
v___x_566_ = lean_nat_mul(v___x_563_, v___x_565_);
v___x_567_ = lean_unsigned_to_nat(3u);
v___x_568_ = lean_nat_mul(v___x_530_, v___x_567_);
v___x_569_ = lean_nat_dec_le(v___x_566_, v___x_568_);
lean_dec(v___x_568_);
lean_dec(v___x_566_);
if (v___x_569_ == 0)
{
lean_dec(v___x_563_);
lean_dec(v_index_538_);
goto v___jp_549_;
}
else
{
lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec_ref(v_inst_524_);
lean_dec_ref(v_inst_523_);
v___x_570_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_525_, v___x_563_, v_index_538_, v_a_526_, v___x_534_);
lean_dec(v_index_538_);
v___x_571_ = lean_box(v___x_539_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
lean_ctor_set(v___x_572_, 1, v___x_570_);
return v___x_572_;
}
}
v___jp_540_:
{
lean_object* v_size_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_size_543_ = lean_ctor_get(v___y_541_, 0);
v___x_544_ = lean_unsigned_to_nat(1u);
v___x_545_ = lean_nat_add(v_size_543_, v___x_544_);
v___x_546_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_541_, v___x_545_, v_i_542_, v_a_526_, v___x_534_);
lean_dec(v_i_542_);
v___x_547_ = lean_box(v___x_539_);
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v___x_547_);
lean_ctor_set(v___x_548_, 1, v___x_546_);
return v___x_548_;
}
v___jp_549_:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
lean_inc_ref(v_inst_524_);
lean_inc_ref(v_inst_523_);
v___x_550_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_523_, v_inst_524_, v_m_525_);
lean_inc(v_a_526_);
v___x_551_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_523_, v_inst_524_, v___x_550_, v_a_526_);
switch(lean_obj_tag(v___x_551_))
{
case 0:
{
lean_object* v_index_552_; lean_object* v_size_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_index_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_index_552_);
lean_dec_ref_known(v___x_551_, 3);
v_size_553_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_size_553_);
v___x_554_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_550_, v_size_553_, v_index_552_, v_a_526_, v___x_534_);
lean_dec(v_index_552_);
v___x_555_ = lean_box(v___x_539_);
v___x_556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_556_, 0, v___x_555_);
lean_ctor_set(v___x_556_, 1, v___x_554_);
return v___x_556_;
}
case 1:
{
lean_object* v_index_557_; 
v_index_557_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_index_557_);
lean_dec_ref_known(v___x_551_, 1);
v___y_541_ = v___x_550_;
v_i_542_ = v_index_557_;
goto v___jp_540_;
}
default: 
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_550_, v___x_529_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_index_559_; 
v_index_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_index_559_);
lean_dec_ref_known(v___x_558_, 1);
v___y_541_ = v___x_550_;
v_i_542_ = v_index_559_;
goto v___jp_540_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_a_526_);
v___x_560_ = lean_box(v___x_539_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set(v___x_561_, 1, v___x_550_);
return v___x_561_;
}
}
}
}
}
default: 
{
uint8_t v___x_573_; lean_object* v___y_575_; lean_object* v_i_576_; lean_object* v___y_584_; lean_object* v___x_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_573_ = 0;
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v_size_527_, v___x_596_);
v___x_598_ = lean_nat_dec_lt(v___x_597_, v___x_530_);
if (v___x_598_ == 0)
{
lean_object* v___x_599_; 
lean_dec(v___x_597_);
lean_inc_ref(v_inst_524_);
lean_inc_ref(v_inst_523_);
v___x_599_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_523_, v_inst_524_, v_m_525_);
v___y_584_ = v___x_599_;
goto v___jp_583_;
}
else
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_600_ = lean_unsigned_to_nat(4u);
v___x_601_ = lean_nat_mul(v___x_597_, v___x_600_);
lean_dec(v___x_597_);
v___x_602_ = lean_unsigned_to_nat(3u);
v___x_603_ = lean_nat_mul(v___x_530_, v___x_602_);
v___x_604_ = lean_nat_dec_le(v___x_601_, v___x_603_);
lean_dec(v___x_603_);
lean_dec(v___x_601_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; 
lean_inc_ref(v_inst_524_);
lean_inc_ref(v_inst_523_);
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_523_, v_inst_524_, v_m_525_);
v___y_584_ = v___x_605_;
goto v___jp_583_;
}
else
{
v___y_584_ = v_m_525_;
goto v___jp_583_;
}
}
v___jp_574_:
{
lean_object* v_size_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v_size_577_ = lean_ctor_get(v___y_575_, 0);
v___x_578_ = lean_unsigned_to_nat(1u);
v___x_579_ = lean_nat_add(v_size_577_, v___x_578_);
v___x_580_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_575_, v___x_579_, v_i_576_, v_a_526_, v___x_534_);
lean_dec(v_i_576_);
v___x_581_ = lean_box(v___x_573_);
v___x_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_580_);
return v___x_582_;
}
v___jp_583_:
{
lean_object* v___x_585_; 
lean_inc(v_a_526_);
v___x_585_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_523_, v_inst_524_, v___y_584_, v_a_526_);
switch(lean_obj_tag(v___x_585_))
{
case 0:
{
lean_object* v_index_586_; lean_object* v_size_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; 
v_index_586_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_index_586_);
lean_dec_ref_known(v___x_585_, 3);
v_size_587_ = lean_ctor_get(v___y_584_, 0);
lean_inc(v_size_587_);
v___x_588_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_584_, v_size_587_, v_index_586_, v_a_526_, v___x_534_);
lean_dec(v_index_586_);
v___x_589_ = lean_box(v___x_573_);
v___x_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_590_, 0, v___x_589_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
return v___x_590_;
}
case 1:
{
lean_object* v_index_591_; 
v_index_591_ = lean_ctor_get(v___x_585_, 0);
lean_inc(v_index_591_);
lean_dec_ref_known(v___x_585_, 1);
v___y_575_ = v___y_584_;
v_i_576_ = v_index_591_;
goto v___jp_574_;
}
default: 
{
lean_object* v___x_592_; 
v___x_592_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_584_, v___x_529_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_object* v_index_593_; 
v_index_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_index_593_);
lean_dec_ref_known(v___x_592_, 1);
v___y_575_ = v___y_584_;
v_i_576_ = v_index_593_;
goto v___jp_574_;
}
else
{
lean_object* v___x_594_; lean_object* v___x_595_; 
lean_dec(v_a_526_);
v___x_594_ = lean_box(v___x_573_);
v___x_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
lean_ctor_set(v___x_595_, 1, v___y_584_);
return v___x_595_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains___redArg(lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_m_608_, lean_object* v_a_609_){
_start:
{
lean_object* v_keyArray_610_; lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_keyArray_610_ = lean_ctor_get(v_m_608_, 1);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_array_get_size(v_keyArray_610_);
v___x_613_ = lean_nat_dec_lt(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_dec(v_a_609_);
lean_dec_ref(v_inst_607_);
lean_dec_ref(v_inst_606_);
return v___x_613_;
}
else
{
uint8_t v___x_614_; 
v___x_614_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_606_, v_inst_607_, v_m_608_, v_a_609_);
return v___x_614_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___redArg___boxed(lean_object* v_inst_615_, lean_object* v_inst_616_, lean_object* v_m_617_, lean_object* v_a_618_){
_start:
{
uint8_t v_res_619_; lean_object* v_r_620_; 
v_res_619_ = l_Std_HashSet_Raw_contains___redArg(v_inst_615_, v_inst_616_, v_m_617_, v_a_618_);
lean_dec_ref(v_m_617_);
v_r_620_ = lean_box(v_res_619_);
return v_r_620_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_contains(lean_object* v_00_u03b1_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_m_624_, lean_object* v_a_625_){
_start:
{
lean_object* v_keyArray_626_; lean_object* v___x_627_; lean_object* v___x_628_; uint8_t v___x_629_; 
v_keyArray_626_ = lean_ctor_get(v_m_624_, 1);
v___x_627_ = lean_unsigned_to_nat(0u);
v___x_628_ = lean_array_get_size(v_keyArray_626_);
v___x_629_ = lean_nat_dec_lt(v___x_627_, v___x_628_);
if (v___x_629_ == 0)
{
lean_dec(v_a_625_);
lean_dec_ref(v_inst_623_);
lean_dec_ref(v_inst_622_);
return v___x_629_;
}
else
{
uint8_t v___x_630_; 
v___x_630_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_622_, v_inst_623_, v_m_624_, v_a_625_);
return v___x_630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_contains___boxed(lean_object* v_00_u03b1_631_, lean_object* v_inst_632_, lean_object* v_inst_633_, lean_object* v_m_634_, lean_object* v_a_635_){
_start:
{
uint8_t v_res_636_; lean_object* v_r_637_; 
v_res_636_ = l_Std_HashSet_Raw_contains(v_00_u03b1_631_, v_inst_632_, v_inst_633_, v_m_634_, v_a_635_);
lean_dec_ref(v_m_634_);
v_r_637_ = lean_box(v_res_636_);
return v_r_637_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_638_, lean_object* v_inst_639_, lean_object* v_inst_640_){
_start:
{
lean_object* v___x_641_; 
v___x_641_ = lean_box(0);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_642_, lean_object* v_inst_643_, lean_object* v_inst_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_HashSet_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_642_, v_inst_643_, v_inst_644_);
lean_dec_ref(v_inst_644_);
lean_dec_ref(v_inst_643_);
return v_res_645_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem___redArg(lean_object* v_inst_646_, lean_object* v_inst_647_, lean_object* v_m_648_, lean_object* v_a_649_){
_start:
{
uint8_t v___x_650_; 
v___x_650_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_646_, v_inst_647_, v_m_648_, v_a_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_m_653_, lean_object* v_a_654_){
_start:
{
uint8_t v_res_655_; lean_object* v_r_656_; 
v_res_655_ = l_Std_HashSet_Raw_instDecidableMem___redArg(v_inst_651_, v_inst_652_, v_m_653_, v_a_654_);
lean_dec_ref(v_m_653_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_instDecidableMem(lean_object* v_00_u03b1_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_m_660_, lean_object* v_a_661_){
_start:
{
uint8_t v___x_662_; 
v___x_662_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_658_, v_inst_659_, v_m_660_, v_a_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_663_, lean_object* v_inst_664_, lean_object* v_inst_665_, lean_object* v_m_666_, lean_object* v_a_667_){
_start:
{
uint8_t v_res_668_; lean_object* v_r_669_; 
v_res_668_ = l_Std_HashSet_Raw_instDecidableMem(v_00_u03b1_663_, v_inst_664_, v_inst_665_, v_m_666_, v_a_667_);
lean_dec_ref(v_m_666_);
v_r_669_ = lean_box(v_res_668_);
return v_r_669_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase___redArg(lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_m_672_, lean_object* v_a_673_){
_start:
{
lean_object* v_keyArray_674_; lean_object* v___x_675_; lean_object* v___x_676_; uint8_t v___x_677_; 
v_keyArray_674_ = lean_ctor_get(v_m_672_, 1);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = lean_array_get_size(v_keyArray_674_);
v___x_677_ = lean_nat_dec_lt(v___x_675_, v___x_676_);
if (v___x_677_ == 0)
{
lean_dec(v_a_673_);
lean_dec_ref(v_inst_671_);
lean_dec_ref(v_inst_670_);
return v_m_672_;
}
else
{
lean_object* v___x_678_; 
v___x_678_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_670_, v_inst_671_, v_m_672_, v_a_673_);
return v___x_678_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_erase(lean_object* v_00_u03b1_679_, lean_object* v_inst_680_, lean_object* v_inst_681_, lean_object* v_m_682_, lean_object* v_a_683_){
_start:
{
lean_object* v_keyArray_684_; lean_object* v___x_685_; lean_object* v___x_686_; uint8_t v___x_687_; 
v_keyArray_684_ = lean_ctor_get(v_m_682_, 1);
v___x_685_ = lean_unsigned_to_nat(0u);
v___x_686_ = lean_array_get_size(v_keyArray_684_);
v___x_687_ = lean_nat_dec_lt(v___x_685_, v___x_686_);
if (v___x_687_ == 0)
{
lean_dec(v_a_683_);
lean_dec_ref(v_inst_681_);
lean_dec_ref(v_inst_680_);
return v_m_682_;
}
else
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_680_, v_inst_681_, v_m_682_, v_a_683_);
return v___x_688_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg(lean_object* v_m_689_){
_start:
{
lean_object* v_size_690_; 
v_size_690_ = lean_ctor_get(v_m_689_, 0);
lean_inc(v_size_690_);
return v_size_690_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___redArg___boxed(lean_object* v_m_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Std_HashSet_Raw_size___redArg(v_m_691_);
lean_dec_ref(v_m_691_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size(lean_object* v_00_u03b1_693_, lean_object* v_m_694_){
_start:
{
lean_object* v_size_695_; 
v_size_695_ = lean_ctor_get(v_m_694_, 0);
lean_inc(v_size_695_);
return v_size_695_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_size___boxed(lean_object* v_00_u03b1_696_, lean_object* v_m_697_){
_start:
{
lean_object* v_res_698_; 
v_res_698_ = l_Std_HashSet_Raw_size(v_00_u03b1_696_, v_m_697_);
lean_dec_ref(v_m_697_);
return v_res_698_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg(lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_m_701_, lean_object* v_a_702_){
_start:
{
lean_object* v_keyArray_703_; lean_object* v___x_704_; lean_object* v___x_705_; uint8_t v___x_706_; 
v_keyArray_703_ = lean_ctor_get(v_m_701_, 1);
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_array_get_size(v_keyArray_703_);
v___x_706_ = lean_nat_dec_lt(v___x_704_, v___x_705_);
if (v___x_706_ == 0)
{
lean_object* v___x_707_; 
lean_dec(v_a_702_);
lean_dec_ref(v_inst_700_);
lean_dec_ref(v_inst_699_);
v___x_707_ = lean_box(0);
return v___x_707_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_699_, v_inst_700_, v_m_701_, v_a_702_);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___redArg___boxed(lean_object* v_inst_709_, lean_object* v_inst_710_, lean_object* v_m_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Std_HashSet_Raw_get_x3f___redArg(v_inst_709_, v_inst_710_, v_m_711_, v_a_712_);
lean_dec_ref(v_m_711_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f(lean_object* v_00_u03b1_714_, lean_object* v_inst_715_, lean_object* v_inst_716_, lean_object* v_m_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_keyArray_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_keyArray_719_ = lean_ctor_get(v_m_717_, 1);
v___x_720_ = lean_unsigned_to_nat(0u);
v___x_721_ = lean_array_get_size(v_keyArray_719_);
v___x_722_ = lean_nat_dec_lt(v___x_720_, v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec(v_a_718_);
lean_dec_ref(v_inst_716_);
lean_dec_ref(v_inst_715_);
v___x_723_ = lean_box(0);
return v___x_723_;
}
else
{
lean_object* v___x_724_; 
v___x_724_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_715_, v_inst_716_, v_m_717_, v_a_718_);
return v___x_724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x3f___boxed(lean_object* v_00_u03b1_725_, lean_object* v_inst_726_, lean_object* v_inst_727_, lean_object* v_m_728_, lean_object* v_a_729_){
_start:
{
lean_object* v_res_730_; 
v_res_730_ = l_Std_HashSet_Raw_get_x3f(v_00_u03b1_725_, v_inst_726_, v_inst_727_, v_m_728_, v_a_729_);
lean_dec_ref(v_m_728_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg(lean_object* v_inst_731_, lean_object* v_inst_732_, lean_object* v_m_733_, lean_object* v_a_734_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___redArg___boxed(lean_object* v_inst_737_, lean_object* v_inst_738_, lean_object* v_m_739_, lean_object* v_a_740_){
_start:
{
lean_object* v_res_741_; 
v_res_741_ = l_Std_HashSet_Raw_get___redArg(v_inst_737_, v_inst_738_, v_m_739_, v_a_740_);
lean_dec_ref(v_m_739_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get(lean_object* v_00_u03b1_742_, lean_object* v_inst_743_, lean_object* v_inst_744_, lean_object* v_m_745_, lean_object* v_a_746_, lean_object* v_h_747_){
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
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get___boxed(lean_object* v_00_u03b1_750_, lean_object* v_inst_751_, lean_object* v_inst_752_, lean_object* v_m_753_, lean_object* v_a_754_, lean_object* v_h_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Std_HashSet_Raw_get(v_00_u03b1_750_, v_inst_751_, v_inst_752_, v_m_753_, v_a_754_, v_h_755_);
lean_dec_ref(v_m_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg(lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_m_759_, lean_object* v_a_760_, lean_object* v_fallback_761_){
_start:
{
lean_object* v_keyArray_762_; lean_object* v___x_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
v_keyArray_762_ = lean_ctor_get(v_m_759_, 1);
v___x_763_ = lean_unsigned_to_nat(0u);
v___x_764_ = lean_array_get_size(v_keyArray_762_);
v___x_765_ = lean_nat_dec_lt(v___x_763_, v___x_764_);
if (v___x_765_ == 0)
{
lean_dec(v_a_760_);
lean_dec_ref(v_inst_758_);
lean_dec_ref(v_inst_757_);
lean_inc(v_fallback_761_);
return v_fallback_761_;
}
else
{
lean_object* v___x_766_; 
v___x_766_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_757_, v_inst_758_, v_m_759_, v_a_760_, v_fallback_761_);
return v___x_766_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___redArg___boxed(lean_object* v_inst_767_, lean_object* v_inst_768_, lean_object* v_m_769_, lean_object* v_a_770_, lean_object* v_fallback_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Std_HashSet_Raw_getD___redArg(v_inst_767_, v_inst_768_, v_m_769_, v_a_770_, v_fallback_771_);
lean_dec(v_fallback_771_);
lean_dec_ref(v_m_769_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD(lean_object* v_00_u03b1_773_, lean_object* v_inst_774_, lean_object* v_inst_775_, lean_object* v_m_776_, lean_object* v_a_777_, lean_object* v_fallback_778_){
_start:
{
lean_object* v_keyArray_779_; lean_object* v___x_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_keyArray_779_ = lean_ctor_get(v_m_776_, 1);
v___x_780_ = lean_unsigned_to_nat(0u);
v___x_781_ = lean_array_get_size(v_keyArray_779_);
v___x_782_ = lean_nat_dec_lt(v___x_780_, v___x_781_);
if (v___x_782_ == 0)
{
lean_dec(v_a_777_);
lean_dec_ref(v_inst_775_);
lean_dec_ref(v_inst_774_);
lean_inc(v_fallback_778_);
return v_fallback_778_;
}
else
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_774_, v_inst_775_, v_m_776_, v_a_777_, v_fallback_778_);
return v___x_783_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_getD___boxed(lean_object* v_00_u03b1_784_, lean_object* v_inst_785_, lean_object* v_inst_786_, lean_object* v_m_787_, lean_object* v_a_788_, lean_object* v_fallback_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_Std_HashSet_Raw_getD(v_00_u03b1_784_, v_inst_785_, v_inst_786_, v_m_787_, v_a_788_, v_fallback_789_);
lean_dec(v_fallback_789_);
lean_dec_ref(v_m_787_);
return v_res_790_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg(lean_object* v_inst_791_, lean_object* v_inst_792_, lean_object* v_inst_793_, lean_object* v_m_794_, lean_object* v_a_795_){
_start:
{
lean_object* v_keyArray_796_; lean_object* v___x_797_; lean_object* v___x_798_; uint8_t v___x_799_; 
v_keyArray_796_ = lean_ctor_get(v_m_794_, 1);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_array_get_size(v_keyArray_796_);
v___x_799_ = lean_nat_dec_lt(v___x_797_, v___x_798_);
if (v___x_799_ == 0)
{
lean_dec(v_a_795_);
lean_dec_ref(v_inst_792_);
lean_dec_ref(v_inst_791_);
lean_inc(v_inst_793_);
return v_inst_793_;
}
else
{
lean_object* v___x_800_; 
v___x_800_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_791_, v_inst_792_, v_inst_793_, v_m_794_, v_a_795_);
return v___x_800_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___redArg___boxed(lean_object* v_inst_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_m_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Std_HashSet_Raw_get_x21___redArg(v_inst_801_, v_inst_802_, v_inst_803_, v_m_804_, v_a_805_);
lean_dec_ref(v_m_804_);
lean_dec(v_inst_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21(lean_object* v_00_u03b1_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_inst_810_, lean_object* v_m_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_keyArray_813_; lean_object* v___x_814_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_keyArray_813_ = lean_ctor_get(v_m_811_, 1);
v___x_814_ = lean_unsigned_to_nat(0u);
v___x_815_ = lean_array_get_size(v_keyArray_813_);
v___x_816_ = lean_nat_dec_lt(v___x_814_, v___x_815_);
if (v___x_816_ == 0)
{
lean_dec(v_a_812_);
lean_dec_ref(v_inst_809_);
lean_dec_ref(v_inst_808_);
lean_inc(v_inst_810_);
return v_inst_810_;
}
else
{
lean_object* v___x_817_; 
v___x_817_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_808_, v_inst_809_, v_inst_810_, v_m_811_, v_a_812_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_get_x21___boxed(lean_object* v_00_u03b1_818_, lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_inst_821_, lean_object* v_m_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Std_HashSet_Raw_get_x21(v_00_u03b1_818_, v_inst_819_, v_inst_820_, v_inst_821_, v_m_822_, v_a_823_);
lean_dec_ref(v_m_822_);
lean_dec(v_inst_821_);
return v_res_824_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty___redArg(lean_object* v_m_825_){
_start:
{
lean_object* v_size_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_size_826_ = lean_ctor_get(v_m_825_, 0);
v___x_827_ = lean_unsigned_to_nat(0u);
v___x_828_ = lean_nat_dec_eq(v_size_826_, v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___redArg___boxed(lean_object* v_m_829_){
_start:
{
uint8_t v_res_830_; lean_object* v_r_831_; 
v_res_830_ = l_Std_HashSet_Raw_isEmpty___redArg(v_m_829_);
lean_dec_ref(v_m_829_);
v_r_831_ = lean_box(v_res_830_);
return v_r_831_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_isEmpty(lean_object* v_00_u03b1_832_, lean_object* v_m_833_){
_start:
{
lean_object* v_size_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_size_834_ = lean_ctor_get(v_m_833_, 0);
v___x_835_ = lean_unsigned_to_nat(0u);
v___x_836_ = lean_nat_dec_eq(v_size_834_, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_isEmpty___boxed(lean_object* v_00_u03b1_837_, lean_object* v_m_838_){
_start:
{
uint8_t v_res_839_; lean_object* v_r_840_; 
v_res_839_ = l_Std_HashSet_Raw_isEmpty(v_00_u03b1_837_, v_m_838_);
lean_dec_ref(v_m_838_);
v_r_840_ = lean_box(v_res_839_);
return v_r_840_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___lam__0(lean_object* v_x1_841_, lean_object* v_x2_842_, lean_object* v_x3_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_844_, 0, v_x2_842_);
lean_ctor_set(v___x_844_, 1, v_x1_841_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg(lean_object* v_m_865_){
_start:
{
lean_object* v___f_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___f_866_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__0));
v___x_867_ = lean_box(0);
v___x_868_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_869_ = lean_unsigned_to_nat(0u);
v___x_870_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_868_, v___f_866_, v_m_865_, v___x_867_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___redArg___boxed(lean_object* v_m_871_){
_start:
{
lean_object* v_res_872_; 
v_res_872_ = l_Std_HashSet_Raw_toList___redArg(v_m_871_);
lean_dec_ref(v_m_871_);
return v_res_872_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList(lean_object* v_00_u03b1_873_, lean_object* v_m_874_){
_start:
{
lean_object* v___f_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___f_875_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__0));
v___x_876_ = lean_box(0);
v___x_877_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_878_ = lean_unsigned_to_nat(0u);
v___x_879_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_877_, v___f_875_, v_m_874_, v___x_876_, v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toList___boxed(lean_object* v_00_u03b1_880_, lean_object* v_m_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_HashSet_Raw_toList(v_00_u03b1_880_, v_m_881_);
lean_dec_ref(v_m_881_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList___redArg(lean_object* v_inst_887_, lean_object* v_inst_888_, lean_object* v_l_889_){
_start:
{
lean_object* v___x_890_; uint8_t v___x_891_; 
v___x_890_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__2, &l_Std_HashSet_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__2);
v___x_891_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_891_ == 0)
{
lean_dec(v_l_889_);
lean_dec_ref(v_inst_888_);
lean_dec_ref(v_inst_887_);
return v___x_890_;
}
else
{
lean_object* v___f_892_; lean_object* v___x_893_; 
v___f_892_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_893_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_892_, v_inst_887_, v_inst_888_, v___x_890_, v_l_889_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofList(lean_object* v_00_u03b1_894_, lean_object* v_inst_895_, lean_object* v_inst_896_, lean_object* v_l_897_){
_start:
{
lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_898_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__2, &l_Std_HashSet_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__2);
v___x_899_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_899_ == 0)
{
lean_dec(v_l_897_);
lean_dec_ref(v_inst_896_);
lean_dec_ref(v_inst_895_);
return v___x_898_;
}
else
{
lean_object* v___f_900_; lean_object* v___x_901_; 
v___f_900_ = ((lean_object*)(l_Std_HashSet_Raw_ofList___redArg___closed__1));
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_900_, v_inst_895_, v_inst_896_, v___x_898_, v_l_897_);
return v___x_901_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg___lam__0(lean_object* v_f_902_, lean_object* v_b_903_, lean_object* v_a_904_, lean_object* v_x_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = lean_apply_2(v_f_902_, v_b_903_, v_a_904_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM___redArg(lean_object* v_inst_907_, lean_object* v_f_908_, lean_object* v_init_909_, lean_object* v_b_910_){
_start:
{
lean_object* v___f_911_; lean_object* v___x_912_; 
v___f_911_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_911_, 0, v_f_908_);
v___x_912_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_907_, v___f_911_, v_init_909_, v_b_910_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_foldM(lean_object* v_00_u03b1_913_, lean_object* v_m_914_, lean_object* v_inst_915_, lean_object* v_00_u03b2_916_, lean_object* v_f_917_, lean_object* v_init_918_, lean_object* v_b_919_){
_start:
{
lean_object* v___f_920_; lean_object* v___x_921_; 
v___f_920_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_foldM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_920_, 0, v_f_917_);
v___x_921_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_915_, v___f_920_, v_init_918_, v_b_919_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg___lam__0(lean_object* v_f_922_, lean_object* v_x1_923_, lean_object* v_x2_924_, lean_object* v_x3_925_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = lean_apply_2(v_f_922_, v_x1_923_, v_x2_924_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold___redArg(lean_object* v_f_927_, lean_object* v_init_928_, lean_object* v_m_929_){
_start:
{
lean_object* v___f_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___f_930_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_930_, 0, v_f_927_);
v___x_931_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_932_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_931_, v___f_930_, v_init_928_, v_m_929_);
return v___x_932_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_fold(lean_object* v_00_u03b1_933_, lean_object* v_00_u03b2_934_, lean_object* v_f_935_, lean_object* v_init_936_, lean_object* v_m_937_){
_start:
{
lean_object* v___f_938_; lean_object* v___x_939_; lean_object* v___x_940_; 
v___f_938_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_938_, 0, v_f_935_);
v___x_939_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_940_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_939_, v___f_938_, v_init_936_, v_m_937_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg___lam__0(lean_object* v_f_941_, lean_object* v_x_942_, lean_object* v_a_943_, lean_object* v_v_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = lean_apply_1(v_f_941_, v_a_943_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM___redArg(lean_object* v_inst_946_, lean_object* v_f_947_, lean_object* v_b_948_){
_start:
{
lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___f_949_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_949_, 0, v_f_947_);
v___x_950_ = lean_box(0);
v___x_951_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_946_, v___f_949_, v___x_950_, v_b_948_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forM(lean_object* v_00_u03b1_952_, lean_object* v_m_953_, lean_object* v_inst_954_, lean_object* v_f_955_, lean_object* v_b_956_){
_start:
{
lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___f_957_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_957_, 0, v_f_955_);
v___x_958_ = lean_box(0);
v___x_959_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_954_, v___f_957_, v___x_958_, v_b_956_);
return v___x_959_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg___lam__0(lean_object* v_f_960_, lean_object* v_a_961_, lean_object* v_x_962_, lean_object* v_acc_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = lean_apply_2(v_f_960_, v_a_961_, v_acc_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn___redArg(lean_object* v_inst_965_, lean_object* v_f_966_, lean_object* v_init_967_, lean_object* v_b_968_){
_start:
{
lean_object* v___f_969_; lean_object* v___x_970_; 
v___f_969_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_969_, 0, v_f_966_);
v___x_970_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_965_, v___f_969_, v_init_967_, v_b_968_);
return v___x_970_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_forIn(lean_object* v_00_u03b1_971_, lean_object* v_m_972_, lean_object* v_inst_973_, lean_object* v_00_u03b2_974_, lean_object* v_f_975_, lean_object* v_init_976_, lean_object* v_b_977_){
_start:
{
lean_object* v___f_978_; lean_object* v___x_979_; 
v___f_978_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_978_, 0, v_f_975_);
v___x_979_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_973_, v___f_978_, v_init_976_, v_b_977_);
return v___x_979_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__1(lean_object* v_inst_980_, lean_object* v_m_981_, lean_object* v_f_982_){
_start:
{
lean_object* v___f_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v___f_983_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_983_, 0, v_f_982_);
v___x_984_ = lean_box(0);
v___x_985_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_980_, v___f_983_, v___x_984_, v_m_981_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad___redArg(lean_object* v_inst_986_){
_start:
{
lean_object* v___f_987_; 
v___f_987_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_987_, 0, v_inst_986_);
return v___f_987_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForMOfMonad(lean_object* v_00_u03b1_988_, lean_object* v_m_989_, lean_object* v_inst_990_){
_start:
{
lean_object* v___f_991_; 
v___f_991_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForMOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_991_, 0, v_inst_990_);
return v___f_991_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__1(lean_object* v_inst_992_, lean_object* v_00_u03b2_993_, lean_object* v_m_994_, lean_object* v_init_995_, lean_object* v_f_996_){
_start:
{
lean_object* v___f_997_; lean_object* v___x_998_; 
v___f_997_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_forIn___redArg___lam__0), 4, 1);
lean_closure_set(v___f_997_, 0, v_f_996_);
v___x_998_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_992_, v___f_997_, v_init_995_, v_m_994_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad___redArg(lean_object* v_inst_999_){
_start:
{
lean_object* v___f_1000_; 
v___f_1000_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1000_, 0, v_inst_999_);
return v___f_1000_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instForInOfMonad(lean_object* v_00_u03b1_1001_, lean_object* v_m_1002_, lean_object* v_inst_1003_){
_start:
{
lean_object* v___f_1004_; 
v___f_1004_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instForInOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1004_, 0, v_inst_1003_);
return v___f_1004_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_filter___redArg___lam__0(lean_object* v_f_1005_, lean_object* v_a_1006_, lean_object* v_x_1007_){
_start:
{
lean_object* v___x_1008_; uint8_t v___x_1009_; 
v___x_1008_ = lean_apply_1(v_f_1005_, v_a_1006_);
v___x_1009_ = lean_unbox(v___x_1008_);
return v___x_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___lam__0___boxed(lean_object* v_f_1010_, lean_object* v_a_1011_, lean_object* v_x_1012_){
_start:
{
uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_res_1013_ = l_Std_HashSet_Raw_filter___redArg___lam__0(v_f_1010_, v_a_1011_, v_x_1012_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg(lean_object* v_f_1015_, lean_object* v_m_1016_){
_start:
{
lean_object* v_keyArray_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; uint8_t v___x_1020_; 
v_keyArray_1017_ = lean_ctor_get(v_m_1016_, 1);
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = lean_array_get_size(v_keyArray_1017_);
v___x_1020_ = lean_nat_dec_lt(v___x_1018_, v___x_1019_);
if (v___x_1020_ == 0)
{
lean_object* v___x_1021_; 
lean_dec_ref(v_f_1015_);
v___x_1021_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__2, &l_Std_HashSet_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__2);
return v___x_1021_;
}
else
{
lean_object* v___f_1022_; lean_object* v___x_1023_; 
v___f_1022_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1022_, 0, v_f_1015_);
v___x_1023_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1022_, v_m_1016_);
return v___x_1023_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___redArg___boxed(lean_object* v_f_1024_, lean_object* v_m_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Std_HashSet_Raw_filter___redArg(v_f_1024_, v_m_1025_);
lean_dec_ref(v_m_1025_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter(lean_object* v_00_u03b1_1027_, lean_object* v_inst_1028_, lean_object* v_inst_1029_, lean_object* v_f_1030_, lean_object* v_m_1031_){
_start:
{
lean_object* v_keyArray_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
v_keyArray_1032_ = lean_ctor_get(v_m_1031_, 1);
v___x_1033_ = lean_unsigned_to_nat(0u);
v___x_1034_ = lean_array_get_size(v_keyArray_1032_);
v___x_1035_ = lean_nat_dec_lt(v___x_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
lean_dec_ref(v_f_1030_);
v___x_1036_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__2, &l_Std_HashSet_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__2);
return v___x_1036_;
}
else
{
lean_object* v___f_1037_; lean_object* v___x_1038_; 
v___f_1037_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_filter___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1037_, 0, v_f_1030_);
v___x_1038_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1037_, v_m_1031_);
return v___x_1038_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_filter___boxed(lean_object* v_00_u03b1_1039_, lean_object* v_inst_1040_, lean_object* v_inst_1041_, lean_object* v_f_1042_, lean_object* v_m_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Std_HashSet_Raw_filter(v_00_u03b1_1039_, v_inst_1040_, v_inst_1041_, v_f_1042_, v_m_1043_);
lean_dec_ref(v_m_1043_);
lean_dec_ref(v_inst_1041_);
lean_dec_ref(v_inst_1040_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg___lam__0(lean_object* v_x1_1045_, lean_object* v_x2_1046_, lean_object* v_x3_1047_){
_start:
{
lean_object* v___x_1048_; 
v___x_1048_ = lean_array_push(v_x1_1045_, v_x2_1046_);
return v___x_1048_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray___redArg(lean_object* v_m_1050_){
_start:
{
lean_object* v_size_1051_; lean_object* v___f_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_size_1051_ = lean_ctor_get(v_m_1050_, 0);
v___f_1052_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__0));
v___x_1053_ = lean_mk_empty_array_with_capacity(v_size_1051_);
v___x_1054_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_1055_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1054_, v___f_1052_, v___x_1053_, v_m_1050_);
return v___x_1055_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_toArray(lean_object* v_00_u03b1_1056_, lean_object* v_m_1057_){
_start:
{
lean_object* v_size_1058_; lean_object* v___f_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_size_1058_ = lean_ctor_get(v_m_1057_, 0);
v___f_1059_ = ((lean_object*)(l_Std_HashSet_Raw_toArray___redArg___closed__0));
v___x_1060_ = lean_mk_empty_array_with_capacity(v_size_1058_);
v___x_1061_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_1062_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1061_, v___f_1059_, v___x_1060_, v_m_1057_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg___lam__0(lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_a_1065_, lean_object* v_b_1066_, lean_object* v_acc_1067_){
_start:
{
lean_object* v___y_1069_; lean_object* v_i_1070_; lean_object* v___y_1089_; lean_object* v_i_1090_; lean_object* v___y_1097_; lean_object* v___x_1108_; 
lean_inc(v_a_1065_);
lean_inc_ref(v_inst_1064_);
lean_inc_ref(v_inst_1063_);
v___x_1108_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1063_, v_inst_1064_, v_acc_1067_, v_a_1065_);
switch(lean_obj_tag(v___x_1108_))
{
case 0:
{
lean_object* v___x_1109_; 
lean_dec_ref_known(v___x_1108_, 3);
lean_dec(v_a_1065_);
lean_dec_ref(v_inst_1064_);
lean_dec_ref(v_inst_1063_);
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_acc_1067_);
return v___x_1109_;
}
case 1:
{
lean_object* v_index_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1129_; 
v_index_1110_ = lean_ctor_get(v___x_1108_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1108_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1112_ = v___x_1108_;
v_isShared_1113_ = v_isSharedCheck_1129_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_index_1110_);
lean_dec(v___x_1108_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1129_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_size_1114_; lean_object* v_keyArray_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v_size_1114_ = lean_ctor_get(v_acc_1067_, 0);
v_keyArray_1115_ = lean_ctor_get(v_acc_1067_, 1);
v___x_1116_ = lean_unsigned_to_nat(1u);
v___x_1117_ = lean_nat_add(v_size_1114_, v___x_1116_);
v___x_1118_ = lean_array_get_size(v_keyArray_1115_);
v___x_1119_ = lean_nat_dec_lt(v___x_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec(v___x_1117_);
lean_del_object(v___x_1112_);
lean_dec(v_index_1110_);
goto v___jp_1076_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1120_ = lean_unsigned_to_nat(4u);
v___x_1121_ = lean_nat_mul(v___x_1117_, v___x_1120_);
v___x_1122_ = lean_unsigned_to_nat(3u);
v___x_1123_ = lean_nat_mul(v___x_1118_, v___x_1122_);
v___x_1124_ = lean_nat_dec_le(v___x_1121_, v___x_1123_);
lean_dec(v___x_1123_);
lean_dec(v___x_1121_);
if (v___x_1124_ == 0)
{
lean_dec(v___x_1117_);
lean_del_object(v___x_1112_);
lean_dec(v_index_1110_);
goto v___jp_1076_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1127_; 
lean_dec_ref(v_inst_1064_);
lean_dec_ref(v_inst_1063_);
v___x_1125_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_1067_, v___x_1117_, v_index_1110_, v_a_1065_, v_b_1066_);
lean_dec(v_index_1110_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v___x_1125_);
v___x_1127_ = v___x_1112_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
default: 
{
lean_object* v_size_1130_; lean_object* v_keyArray_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v_size_1130_ = lean_ctor_get(v_acc_1067_, 0);
v_keyArray_1131_ = lean_ctor_get(v_acc_1067_, 1);
v___x_1132_ = lean_unsigned_to_nat(1u);
v___x_1133_ = lean_nat_add(v_size_1130_, v___x_1132_);
v___x_1134_ = lean_array_get_size(v_keyArray_1131_);
v___x_1135_ = lean_nat_dec_lt(v___x_1133_, v___x_1134_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; 
lean_dec(v___x_1133_);
lean_inc_ref(v_inst_1064_);
lean_inc_ref(v_inst_1063_);
v___x_1136_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1063_, v_inst_1064_, v_acc_1067_);
v___y_1097_ = v___x_1136_;
goto v___jp_1096_;
}
else
{
lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; uint8_t v___x_1141_; 
v___x_1137_ = lean_unsigned_to_nat(4u);
v___x_1138_ = lean_nat_mul(v___x_1133_, v___x_1137_);
lean_dec(v___x_1133_);
v___x_1139_ = lean_unsigned_to_nat(3u);
v___x_1140_ = lean_nat_mul(v___x_1134_, v___x_1139_);
v___x_1141_ = lean_nat_dec_le(v___x_1138_, v___x_1140_);
lean_dec(v___x_1140_);
lean_dec(v___x_1138_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; 
lean_inc_ref(v_inst_1064_);
lean_inc_ref(v_inst_1063_);
v___x_1142_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1063_, v_inst_1064_, v_acc_1067_);
v___y_1097_ = v___x_1142_;
goto v___jp_1096_;
}
else
{
v___y_1097_ = v_acc_1067_;
goto v___jp_1096_;
}
}
}
}
v___jp_1068_:
{
lean_object* v_size_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v_size_1071_ = lean_ctor_get(v___y_1069_, 0);
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_nat_add(v_size_1071_, v___x_1072_);
v___x_1074_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1069_, v___x_1073_, v_i_1070_, v_a_1065_, v_b_1066_);
lean_dec(v_i_1070_);
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
v___jp_1076_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_inc_ref(v_inst_1064_);
lean_inc_ref(v_inst_1063_);
v___x_1077_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1063_, v_inst_1064_, v_acc_1067_);
lean_inc(v_a_1065_);
v___x_1078_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1063_, v_inst_1064_, v___x_1077_, v_a_1065_);
switch(lean_obj_tag(v___x_1078_))
{
case 0:
{
lean_object* v_index_1079_; lean_object* v_size_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v_index_1079_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_index_1079_);
lean_dec_ref_known(v___x_1078_, 3);
v_size_1080_ = lean_ctor_get(v___x_1077_, 0);
lean_inc(v_size_1080_);
v___x_1081_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1077_, v_size_1080_, v_index_1079_, v_a_1065_, v_b_1066_);
lean_dec(v_index_1079_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
case 1:
{
lean_object* v_index_1083_; 
v_index_1083_ = lean_ctor_get(v___x_1078_, 0);
lean_inc(v_index_1083_);
lean_dec_ref_known(v___x_1078_, 1);
v___y_1069_ = v___x_1077_;
v_i_1070_ = v_index_1083_;
goto v___jp_1068_;
}
default: 
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = lean_unsigned_to_nat(0u);
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1077_, v___x_1084_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_index_1086_; 
v_index_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_index_1086_);
lean_dec_ref_known(v___x_1085_, 1);
v___y_1069_ = v___x_1077_;
v_i_1070_ = v_index_1086_;
goto v___jp_1068_;
}
else
{
lean_object* v___x_1087_; 
lean_dec(v_a_1065_);
v___x_1087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1077_);
return v___x_1087_;
}
}
}
}
v___jp_1088_:
{
lean_object* v_size_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v_size_1091_ = lean_ctor_get(v___y_1089_, 0);
v___x_1092_ = lean_unsigned_to_nat(1u);
v___x_1093_ = lean_nat_add(v_size_1091_, v___x_1092_);
v___x_1094_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1089_, v___x_1093_, v_i_1090_, v_a_1065_, v_b_1066_);
lean_dec(v_i_1090_);
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
v___jp_1096_:
{
lean_object* v___x_1098_; 
lean_inc(v_a_1065_);
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1063_, v_inst_1064_, v___y_1097_, v_a_1065_);
switch(lean_obj_tag(v___x_1098_))
{
case 0:
{
lean_object* v_index_1099_; lean_object* v_size_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_index_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_index_1099_);
lean_dec_ref_known(v___x_1098_, 3);
v_size_1100_ = lean_ctor_get(v___y_1097_, 0);
lean_inc(v_size_1100_);
v___x_1101_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1097_, v_size_1100_, v_index_1099_, v_a_1065_, v_b_1066_);
lean_dec(v_index_1099_);
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
case 1:
{
lean_object* v_index_1103_; 
v_index_1103_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_index_1103_);
lean_dec_ref_known(v___x_1098_, 1);
v___y_1089_ = v___y_1097_;
v_i_1090_ = v_index_1103_;
goto v___jp_1088_;
}
default: 
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_unsigned_to_nat(0u);
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1097_, v___x_1104_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_index_1106_; 
v_index_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_index_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v___y_1089_ = v___y_1097_;
v_i_1090_ = v_index_1106_;
goto v___jp_1088_;
}
else
{
lean_object* v___x_1107_; 
lean_dec(v_a_1065_);
v___x_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1107_, 0, v___y_1097_);
return v___x_1107_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union___redArg(lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_m_u2081_1147_, lean_object* v_m_u2082_1148_){
_start:
{
lean_object* v_size_1149_; lean_object* v_keyArray_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; uint8_t v___x_1153_; 
v_size_1149_ = lean_ctor_get(v_m_u2081_1147_, 0);
v_keyArray_1150_ = lean_ctor_get(v_m_u2081_1147_, 1);
v___x_1151_ = lean_unsigned_to_nat(0u);
v___x_1152_ = lean_array_get_size(v_keyArray_1150_);
v___x_1153_ = lean_nat_dec_lt(v___x_1151_, v___x_1152_);
if (v___x_1153_ == 0)
{
lean_dec_ref(v_m_u2081_1147_);
lean_dec_ref(v_inst_1146_);
lean_dec_ref(v_inst_1145_);
return v_m_u2082_1148_;
}
else
{
lean_object* v_size_1154_; lean_object* v_keyArray_1155_; lean_object* v___x_1156_; uint8_t v___x_1157_; 
v_size_1154_ = lean_ctor_get(v_m_u2082_1148_, 0);
v_keyArray_1155_ = lean_ctor_get(v_m_u2082_1148_, 1);
v___x_1156_ = lean_array_get_size(v_keyArray_1155_);
v___x_1157_ = lean_nat_dec_lt(v___x_1151_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_dec_ref(v_m_u2082_1148_);
lean_dec_ref(v_inst_1146_);
lean_dec_ref(v_inst_1145_);
return v_m_u2081_1147_;
}
else
{
uint8_t v___x_1158_; 
v___x_1158_ = lean_nat_dec_le(v_size_1149_, v_size_1154_);
if (v___x_1158_ == 0)
{
lean_object* v___f_1159_; lean_object* v___x_1160_; 
v___f_1159_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1160_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1159_, v_inst_1145_, v_inst_1146_, v_m_u2081_1147_, v_m_u2082_1148_);
return v___x_1160_;
}
else
{
lean_object* v___f_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___f_1161_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1161_, 0, v_inst_1145_);
lean_closure_set(v___f_1161_, 1, v_inst_1146_);
v___x_1162_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_1163_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1162_, v___f_1161_, v_m_u2082_1148_, v_m_u2081_1147_);
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_union(lean_object* v_00_u03b1_1164_, lean_object* v_inst_1165_, lean_object* v_inst_1166_, lean_object* v_m_u2081_1167_, lean_object* v_m_u2082_1168_){
_start:
{
lean_object* v_size_1169_; lean_object* v_keyArray_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; uint8_t v___x_1173_; 
v_size_1169_ = lean_ctor_get(v_m_u2081_1167_, 0);
v_keyArray_1170_ = lean_ctor_get(v_m_u2081_1167_, 1);
v___x_1171_ = lean_unsigned_to_nat(0u);
v___x_1172_ = lean_array_get_size(v_keyArray_1170_);
v___x_1173_ = lean_nat_dec_lt(v___x_1171_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_dec_ref(v_m_u2081_1167_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
return v_m_u2082_1168_;
}
else
{
lean_object* v_size_1174_; lean_object* v_keyArray_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_size_1174_ = lean_ctor_get(v_m_u2082_1168_, 0);
v_keyArray_1175_ = lean_ctor_get(v_m_u2082_1168_, 1);
v___x_1176_ = lean_array_get_size(v_keyArray_1175_);
v___x_1177_ = lean_nat_dec_lt(v___x_1171_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_dec_ref(v_m_u2082_1168_);
lean_dec_ref(v_inst_1166_);
lean_dec_ref(v_inst_1165_);
return v_m_u2081_1167_;
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_nat_dec_le(v_size_1169_, v_size_1174_);
if (v___x_1178_ == 0)
{
lean_object* v___f_1179_; lean_object* v___x_1180_; 
v___f_1179_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1180_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_1179_, v_inst_1165_, v_inst_1166_, v_m_u2081_1167_, v_m_u2082_1168_);
return v___x_1180_;
}
else
{
lean_object* v___f_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___f_1181_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_1181_, 0, v_inst_1165_);
lean_closure_set(v___f_1181_, 1, v_inst_1166_);
v___x_1182_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_1183_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1182_, v___f_1181_, v_m_u2082_1168_, v_m_u2081_1167_);
return v___x_1183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_1184_, lean_object* v_inst_1185_){
_start:
{
lean_object* v___x_1186_; 
v___x_1186_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_1186_, 0, lean_box(0));
lean_closure_set(v___x_1186_, 1, v_inst_1184_);
lean_closure_set(v___x_1186_, 2, v_inst_1185_);
return v___x_1186_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_1187_, lean_object* v_inst_1188_, lean_object* v_inst_1189_){
_start:
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_union), 5, 3);
lean_closure_set(v___x_1190_, 0, lean_box(0));
lean_closure_set(v___x_1190_, 1, v_inst_1188_);
lean_closure_set(v___x_1190_, 2, v_inst_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter___redArg(lean_object* v_inst_1191_, lean_object* v_inst_1192_, lean_object* v_m_u2081_1193_, lean_object* v_m_u2082_1194_){
_start:
{
lean_object* v_keyArray_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v_keyArray_1195_ = lean_ctor_get(v_m_u2081_1193_, 1);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_array_get_size(v_keyArray_1195_);
v___x_1198_ = lean_nat_dec_lt(v___x_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_dec_ref(v_m_u2081_1193_);
lean_dec_ref(v_inst_1192_);
lean_dec_ref(v_inst_1191_);
return v_m_u2082_1194_;
}
else
{
lean_object* v_keyArray_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v_keyArray_1199_ = lean_ctor_get(v_m_u2082_1194_, 1);
v___x_1200_ = lean_array_get_size(v_keyArray_1199_);
v___x_1201_ = lean_nat_dec_lt(v___x_1196_, v___x_1200_);
if (v___x_1201_ == 0)
{
lean_dec_ref(v_m_u2082_1194_);
lean_dec_ref(v_inst_1192_);
lean_dec_ref(v_inst_1191_);
return v_m_u2081_1193_;
}
else
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1191_, v_inst_1192_, v_m_u2081_1193_, v_m_u2082_1194_);
return v___x_1202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_inter(lean_object* v_00_u03b1_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_m_u2081_1206_, lean_object* v_m_u2082_1207_){
_start:
{
lean_object* v_keyArray_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_keyArray_1208_ = lean_ctor_get(v_m_u2081_1206_, 1);
v___x_1209_ = lean_unsigned_to_nat(0u);
v___x_1210_ = lean_array_get_size(v_keyArray_1208_);
v___x_1211_ = lean_nat_dec_lt(v___x_1209_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_dec_ref(v_m_u2081_1206_);
lean_dec_ref(v_inst_1205_);
lean_dec_ref(v_inst_1204_);
return v_m_u2082_1207_;
}
else
{
lean_object* v_keyArray_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_keyArray_1212_ = lean_ctor_get(v_m_u2082_1207_, 1);
v___x_1213_ = lean_array_get_size(v_keyArray_1212_);
v___x_1214_ = lean_nat_dec_lt(v___x_1209_, v___x_1213_);
if (v___x_1214_ == 0)
{
lean_dec_ref(v_m_u2082_1207_);
lean_dec_ref(v_inst_1205_);
lean_dec_ref(v_inst_1204_);
return v_m_u2081_1206_;
}
else
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_1204_, v_inst_1205_, v_m_u2081_1206_, v_m_u2082_1207_);
return v___x_1215_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_1216_, lean_object* v_inst_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1218_, 0, lean_box(0));
lean_closure_set(v___x_1218_, 1, v_inst_1216_);
lean_closure_set(v___x_1218_, 2, v_inst_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_1219_, lean_object* v_inst_1220_, lean_object* v_inst_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_inter), 5, 3);
lean_closure_set(v___x_1222_, 0, lean_box(0));
lean_closure_set(v___x_1222_, 1, v_inst_1220_);
lean_closure_set(v___x_1222_, 2, v_inst_1221_);
return v___x_1222_;
}
}
static lean_object* _init_l_Std_HashSet_Raw_beq___redArg___closed__0(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___f_1224_; 
v___x_1223_ = lean_alloc_closure((void*)(l_instDecidableEqPUnit___boxed), 2, 0);
v___f_1224_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_1224_, 0, v___x_1223_);
return v___f_1224_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq___redArg(lean_object* v_inst_1225_, lean_object* v_inst_1226_, lean_object* v_m_u2081_1227_, lean_object* v_m_u2082_1228_){
_start:
{
lean_object* v___f_1229_; uint8_t v___x_1230_; 
v___f_1229_ = lean_obj_once(&l_Std_HashSet_Raw_beq___redArg___closed__0, &l_Std_HashSet_Raw_beq___redArg___closed__0_once, _init_l_Std_HashSet_Raw_beq___redArg___closed__0);
v___x_1230_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_1225_, v_inst_1226_, v___f_1229_, v_m_u2081_1227_, v_m_u2082_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___redArg___boxed(lean_object* v_inst_1231_, lean_object* v_inst_1232_, lean_object* v_m_u2081_1233_, lean_object* v_m_u2082_1234_){
_start:
{
uint8_t v_res_1235_; lean_object* v_r_1236_; 
v_res_1235_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1231_, v_inst_1232_, v_m_u2081_1233_, v_m_u2082_1234_);
v_r_1236_ = lean_box(v_res_1235_);
return v_r_1236_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_beq(lean_object* v_00_u03b1_1237_, lean_object* v_inst_1238_, lean_object* v_inst_1239_, lean_object* v_m_u2081_1240_, lean_object* v_m_u2082_1241_){
_start:
{
uint8_t v___x_1242_; 
v___x_1242_ = l_Std_HashSet_Raw_beq___redArg(v_inst_1238_, v_inst_1239_, v_m_u2081_1240_, v_m_u2082_1241_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_beq___boxed(lean_object* v_00_u03b1_1243_, lean_object* v_inst_1244_, lean_object* v_inst_1245_, lean_object* v_m_u2081_1246_, lean_object* v_m_u2082_1247_){
_start:
{
uint8_t v_res_1248_; lean_object* v_r_1249_; 
v_res_1248_ = l_Std_HashSet_Raw_beq(v_00_u03b1_1243_, v_inst_1244_, v_inst_1245_, v_m_u2081_1246_, v_m_u2082_1247_);
v_r_1249_ = lean_box(v_res_1248_);
return v_r_1249_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable___redArg(lean_object* v_inst_1250_, lean_object* v_inst_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1252_, 0, lean_box(0));
lean_closure_set(v___x_1252_, 1, v_inst_1250_);
lean_closure_set(v___x_1252_, 2, v_inst_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instBEqOfHashable(lean_object* v_00_u03b1_1253_, lean_object* v_inst_1254_, lean_object* v_inst_1255_){
_start:
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_beq___boxed), 5, 3);
lean_closure_set(v___x_1256_, 0, lean_box(0));
lean_closure_set(v___x_1256_, 1, v_inst_1254_);
lean_closure_set(v___x_1256_, 2, v_inst_1255_);
return v___x_1256_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_diff___redArg___lam__0(lean_object* v_inst_1257_, lean_object* v_inst_1258_, lean_object* v_m_u2082_1259_, uint8_t v___x_1260_, lean_object* v_k_1261_, lean_object* v_x_1262_){
_start:
{
uint8_t v___x_1263_; 
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1257_, v_inst_1258_, v_m_u2082_1259_, v_k_1261_);
if (v___x_1263_ == 0)
{
return v___x_1260_;
}
else
{
uint8_t v___x_1264_; 
v___x_1264_ = 0;
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_m_u2082_1267_, lean_object* v___x_1268_, lean_object* v_k_1269_, lean_object* v_x_1270_){
_start:
{
uint8_t v___x_97__boxed_1271_; uint8_t v_res_1272_; lean_object* v_r_1273_; 
v___x_97__boxed_1271_ = lean_unbox(v___x_1268_);
v_res_1272_ = l_Std_HashSet_Raw_diff___redArg___lam__0(v_inst_1265_, v_inst_1266_, v_m_u2082_1267_, v___x_97__boxed_1271_, v_k_1269_, v_x_1270_);
lean_dec_ref(v_m_u2082_1267_);
v_r_1273_ = lean_box(v_res_1272_);
return v_r_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff___redArg(lean_object* v_inst_1274_, lean_object* v_inst_1275_, lean_object* v_m_u2081_1276_, lean_object* v_m_u2082_1277_){
_start:
{
lean_object* v_size_1278_; lean_object* v_keyArray_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; uint8_t v___x_1282_; 
v_size_1278_ = lean_ctor_get(v_m_u2081_1276_, 0);
v_keyArray_1279_ = lean_ctor_get(v_m_u2081_1276_, 1);
v___x_1280_ = lean_unsigned_to_nat(0u);
v___x_1281_ = lean_array_get_size(v_keyArray_1279_);
v___x_1282_ = lean_nat_dec_lt(v___x_1280_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_dec_ref(v_m_u2081_1276_);
lean_dec_ref(v_inst_1275_);
lean_dec_ref(v_inst_1274_);
return v_m_u2082_1277_;
}
else
{
lean_object* v_size_1283_; lean_object* v_keyArray_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_size_1283_ = lean_ctor_get(v_m_u2082_1277_, 0);
v_keyArray_1284_ = lean_ctor_get(v_m_u2082_1277_, 1);
v___x_1285_ = lean_array_get_size(v_keyArray_1284_);
v___x_1286_ = lean_nat_dec_lt(v___x_1280_, v___x_1285_);
if (v___x_1286_ == 0)
{
lean_dec_ref(v_m_u2082_1277_);
lean_dec_ref(v_inst_1275_);
lean_dec_ref(v_inst_1274_);
return v_m_u2081_1276_;
}
else
{
uint8_t v___x_1287_; 
v___x_1287_ = lean_nat_dec_le(v_size_1278_, v_size_1283_);
if (v___x_1287_ == 0)
{
lean_object* v___f_1288_; lean_object* v___x_1289_; 
v___f_1288_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1289_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1288_, v_inst_1274_, v_inst_1275_, v_m_u2081_1276_, v_m_u2082_1277_);
return v___x_1289_;
}
else
{
lean_object* v___x_1290_; lean_object* v___f_1291_; lean_object* v___x_1292_; 
v___x_1290_ = lean_box(v___x_1287_);
v___f_1291_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1291_, 0, v_inst_1274_);
lean_closure_set(v___f_1291_, 1, v_inst_1275_);
lean_closure_set(v___f_1291_, 2, v_m_u2082_1277_);
lean_closure_set(v___f_1291_, 3, v___x_1290_);
v___x_1292_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1291_, v_m_u2081_1276_);
lean_dec_ref(v_m_u2081_1276_);
return v___x_1292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_diff(lean_object* v_00_u03b1_1293_, lean_object* v_inst_1294_, lean_object* v_inst_1295_, lean_object* v_m_u2081_1296_, lean_object* v_m_u2082_1297_){
_start:
{
lean_object* v_size_1298_; lean_object* v_keyArray_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_size_1298_ = lean_ctor_get(v_m_u2081_1296_, 0);
v_keyArray_1299_ = lean_ctor_get(v_m_u2081_1296_, 1);
v___x_1300_ = lean_unsigned_to_nat(0u);
v___x_1301_ = lean_array_get_size(v_keyArray_1299_);
v___x_1302_ = lean_nat_dec_lt(v___x_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec_ref(v_m_u2081_1296_);
lean_dec_ref(v_inst_1295_);
lean_dec_ref(v_inst_1294_);
return v_m_u2082_1297_;
}
else
{
lean_object* v_size_1303_; lean_object* v_keyArray_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_size_1303_ = lean_ctor_get(v_m_u2082_1297_, 0);
v_keyArray_1304_ = lean_ctor_get(v_m_u2082_1297_, 1);
v___x_1305_ = lean_array_get_size(v_keyArray_1304_);
v___x_1306_ = lean_nat_dec_lt(v___x_1300_, v___x_1305_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v_m_u2082_1297_);
lean_dec_ref(v_inst_1295_);
lean_dec_ref(v_inst_1294_);
return v_m_u2081_1296_;
}
else
{
uint8_t v___x_1307_; 
v___x_1307_ = lean_nat_dec_le(v_size_1298_, v_size_1303_);
if (v___x_1307_ == 0)
{
lean_object* v___f_1308_; lean_object* v___x_1309_; 
v___f_1308_ = ((lean_object*)(l_Std_HashSet_Raw_union___redArg___closed__0));
v___x_1309_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_1308_, v_inst_1294_, v_inst_1295_, v_m_u2081_1296_, v_m_u2082_1297_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; lean_object* v___f_1311_; lean_object* v___x_1312_; 
v___x_1310_ = lean_box(v___x_1307_);
v___f_1311_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_1311_, 0, v_inst_1294_);
lean_closure_set(v___f_1311_, 1, v_inst_1295_);
lean_closure_set(v___f_1311_, 2, v_m_u2082_1297_);
lean_closure_set(v___f_1311_, 3, v___x_1310_);
v___x_1312_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_1311_, v_m_u2081_1296_);
lean_dec_ref(v_m_u2081_1296_);
return v___x_1312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_1313_, lean_object* v_inst_1314_){
_start:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1315_, 0, lean_box(0));
lean_closure_set(v___x_1315_, 1, v_inst_1313_);
lean_closure_set(v___x_1315_, 2, v_inst_1314_);
return v___x_1315_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_1316_, lean_object* v_inst_1317_, lean_object* v_inst_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_diff), 5, 3);
lean_closure_set(v___x_1319_, 0, lean_box(0));
lean_closure_set(v___x_1319_, 1, v_inst_1317_);
lean_closure_set(v___x_1319_, 2, v_inst_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0(lean_object* v_p_1320_, lean_object* v___x_1321_, lean_object* v___x_1322_, lean_object* v_a_1323_, lean_object* v_b_1324_, lean_object* v_acc_1325_){
_start:
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = lean_apply_1(v_p_1320_, v_a_1323_);
v___x_1327_ = lean_unbox(v___x_1326_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v___x_1322_);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v___x_1321_);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
else
{
lean_object* v___x_1331_; 
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1322_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1332_, lean_object* v___x_1333_, lean_object* v___x_1334_, lean_object* v_a_1335_, lean_object* v_b_1336_, lean_object* v_acc_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_Std_HashSet_Raw_all___redArg___lam__0(v_p_1332_, v___x_1333_, v___x_1334_, v_a_1335_, v_b_1336_, v_acc_1337_);
lean_dec_ref(v_acc_1337_);
return v_res_1338_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all___redArg(lean_object* v_m_1342_, lean_object* v_p_1343_){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v_fst_1349_; 
v___x_1344_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_1345_ = lean_box(0);
v___x_1346_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1347_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1347_, 0, v_p_1343_);
lean_closure_set(v___f_1347_, 1, v___x_1345_);
lean_closure_set(v___f_1347_, 2, v___x_1346_);
v___x_1348_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1344_, v___f_1347_, v___x_1346_, v_m_1342_);
v_fst_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_fst_1349_);
lean_dec(v___x_1348_);
if (lean_obj_tag(v_fst_1349_) == 0)
{
uint8_t v___x_1350_; 
v___x_1350_ = 1;
return v___x_1350_;
}
else
{
lean_object* v_val_1351_; uint8_t v___x_1352_; 
v_val_1351_ = lean_ctor_get(v_fst_1349_, 0);
lean_inc(v_val_1351_);
lean_dec_ref_known(v_fst_1349_, 1);
v___x_1352_ = lean_unbox(v_val_1351_);
lean_dec(v_val_1351_);
return v___x_1352_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___redArg___boxed(lean_object* v_m_1353_, lean_object* v_p_1354_){
_start:
{
uint8_t v_res_1355_; lean_object* v_r_1356_; 
v_res_1355_ = l_Std_HashSet_Raw_all___redArg(v_m_1353_, v_p_1354_);
v_r_1356_ = lean_box(v_res_1355_);
return v_r_1356_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_all(lean_object* v_00_u03b1_1357_, lean_object* v_m_1358_, lean_object* v_p_1359_){
_start:
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___f_1363_; lean_object* v___x_1364_; lean_object* v_fst_1365_; 
v___x_1360_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_1361_ = lean_box(0);
v___x_1362_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1363_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1363_, 0, v_p_1359_);
lean_closure_set(v___f_1363_, 1, v___x_1361_);
lean_closure_set(v___f_1363_, 2, v___x_1362_);
v___x_1364_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1360_, v___f_1363_, v___x_1362_, v_m_1358_);
v_fst_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_fst_1365_);
lean_dec(v___x_1364_);
if (lean_obj_tag(v_fst_1365_) == 0)
{
uint8_t v___x_1366_; 
v___x_1366_ = 1;
return v___x_1366_;
}
else
{
lean_object* v_val_1367_; uint8_t v___x_1368_; 
v_val_1367_ = lean_ctor_get(v_fst_1365_, 0);
lean_inc(v_val_1367_);
lean_dec_ref_known(v_fst_1365_, 1);
v___x_1368_ = lean_unbox(v_val_1367_);
lean_dec(v_val_1367_);
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_all___boxed(lean_object* v_00_u03b1_1369_, lean_object* v_m_1370_, lean_object* v_p_1371_){
_start:
{
uint8_t v_res_1372_; lean_object* v_r_1373_; 
v_res_1372_ = l_Std_HashSet_Raw_all(v_00_u03b1_1369_, v_m_1370_, v_p_1371_);
v_r_1373_ = lean_box(v_res_1372_);
return v_r_1373_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0(lean_object* v_p_1374_, lean_object* v___x_1375_, lean_object* v___x_1376_, lean_object* v_a_1377_, lean_object* v_b_1378_, lean_object* v_acc_1379_){
_start:
{
lean_object* v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = lean_apply_1(v_p_1374_, v_a_1377_);
v___x_1381_ = lean_unbox(v___x_1380_);
if (v___x_1381_ == 0)
{
lean_object* v___x_1382_; 
v___x_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1375_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec_ref(v___x_1375_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1380_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v___x_1383_);
lean_ctor_set(v___x_1384_, 1, v___x_1376_);
v___x_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___lam__0___boxed(lean_object* v_p_1386_, lean_object* v___x_1387_, lean_object* v___x_1388_, lean_object* v_a_1389_, lean_object* v_b_1390_, lean_object* v_acc_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_Std_HashSet_Raw_any___redArg___lam__0(v_p_1386_, v___x_1387_, v___x_1388_, v_a_1389_, v_b_1390_, v_acc_1391_);
lean_dec_ref(v_acc_1391_);
return v_res_1392_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any___redArg(lean_object* v_m_1393_, lean_object* v_p_1394_){
_start:
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___f_1398_; lean_object* v___x_1399_; lean_object* v_fst_1400_; 
v___x_1395_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_1396_ = lean_box(0);
v___x_1397_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1398_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1398_, 0, v_p_1394_);
lean_closure_set(v___f_1398_, 1, v___x_1397_);
lean_closure_set(v___f_1398_, 2, v___x_1396_);
v___x_1399_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1395_, v___f_1398_, v___x_1397_, v_m_1393_);
v_fst_1400_ = lean_ctor_get(v___x_1399_, 0);
lean_inc(v_fst_1400_);
lean_dec(v___x_1399_);
if (lean_obj_tag(v_fst_1400_) == 0)
{
uint8_t v___x_1401_; 
v___x_1401_ = 0;
return v___x_1401_;
}
else
{
lean_object* v_val_1402_; uint8_t v___x_1403_; 
v_val_1402_ = lean_ctor_get(v_fst_1400_, 0);
lean_inc(v_val_1402_);
lean_dec_ref_known(v_fst_1400_, 1);
v___x_1403_ = lean_unbox(v_val_1402_);
lean_dec(v_val_1402_);
return v___x_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___redArg___boxed(lean_object* v_m_1404_, lean_object* v_p_1405_){
_start:
{
uint8_t v_res_1406_; lean_object* v_r_1407_; 
v_res_1406_ = l_Std_HashSet_Raw_any___redArg(v_m_1404_, v_p_1405_);
v_r_1407_ = lean_box(v_res_1406_);
return v_r_1407_;
}
}
LEAN_EXPORT uint8_t l_Std_HashSet_Raw_any(lean_object* v_00_u03b1_1408_, lean_object* v_m_1409_, lean_object* v_p_1410_){
_start:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___f_1414_; lean_object* v___x_1415_; lean_object* v_fst_1416_; 
v___x_1411_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_1412_ = lean_box(0);
v___x_1413_ = ((lean_object*)(l_Std_HashSet_Raw_all___redArg___closed__0));
v___f_1414_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1414_, 0, v_p_1410_);
lean_closure_set(v___f_1414_, 1, v___x_1413_);
lean_closure_set(v___f_1414_, 2, v___x_1412_);
v___x_1415_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1411_, v___f_1414_, v___x_1413_, v_m_1409_);
v_fst_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_fst_1416_);
lean_dec(v___x_1415_);
if (lean_obj_tag(v_fst_1416_) == 0)
{
uint8_t v___x_1417_; 
v___x_1417_ = 0;
return v___x_1417_;
}
else
{
lean_object* v_val_1418_; uint8_t v___x_1419_; 
v_val_1418_ = lean_ctor_get(v_fst_1416_, 0);
lean_inc(v_val_1418_);
lean_dec_ref_known(v_fst_1416_, 1);
v___x_1419_ = lean_unbox(v_val_1418_);
lean_dec(v_val_1418_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_any___boxed(lean_object* v_00_u03b1_1420_, lean_object* v_m_1421_, lean_object* v_p_1422_){
_start:
{
uint8_t v_res_1423_; lean_object* v_r_1424_; 
v_res_1423_ = l_Std_HashSet_Raw_any(v_00_u03b1_1420_, v_m_1421_, v_p_1422_);
v_r_1424_ = lean_box(v_res_1423_);
return v_r_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany___redArg(lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_m_1428_, lean_object* v_l_1429_){
_start:
{
lean_object* v_keyArray_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v_keyArray_1430_ = lean_ctor_get(v_m_1428_, 1);
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_array_get_size(v_keyArray_1430_);
v___x_1433_ = lean_nat_dec_lt(v___x_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_dec(v_l_1429_);
lean_dec(v_inst_1427_);
lean_dec_ref(v_inst_1426_);
lean_dec_ref(v_inst_1425_);
return v_m_1428_;
}
else
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1427_, v_inst_1425_, v_inst_1426_, v_m_1428_, v_l_1429_);
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_insertMany(lean_object* v_00_u03b1_1435_, lean_object* v_inst_1436_, lean_object* v_inst_1437_, lean_object* v_00_u03c1_1438_, lean_object* v_inst_1439_, lean_object* v_m_1440_, lean_object* v_l_1441_){
_start:
{
lean_object* v_keyArray_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_keyArray_1442_ = lean_ctor_get(v_m_1440_, 1);
v___x_1443_ = lean_unsigned_to_nat(0u);
v___x_1444_ = lean_array_get_size(v_keyArray_1442_);
v___x_1445_ = lean_nat_dec_lt(v___x_1443_, v___x_1444_);
if (v___x_1445_ == 0)
{
lean_dec(v_l_1441_);
lean_dec(v_inst_1439_);
lean_dec_ref(v_inst_1437_);
lean_dec_ref(v_inst_1436_);
return v_m_1440_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_1439_, v_inst_1436_, v_inst_1437_, v_m_1440_, v_l_1441_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray___redArg(lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_l_1453_){
_start:
{
lean_object* v___x_1454_; uint8_t v___x_1455_; 
v___x_1454_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__2, &l_Std_HashSet_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__2);
v___x_1455_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1455_ == 0)
{
lean_dec_ref(v_l_1453_);
lean_dec_ref(v_inst_1452_);
lean_dec_ref(v_inst_1451_);
return v___x_1454_;
}
else
{
lean_object* v___f_1456_; lean_object* v___x_1457_; 
v___f_1456_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1457_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1456_, v_inst_1451_, v_inst_1452_, v___x_1454_, v_l_1453_);
return v___x_1457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_ofArray(lean_object* v_00_u03b1_1458_, lean_object* v_inst_1459_, lean_object* v_inst_1460_, lean_object* v_l_1461_){
_start:
{
lean_object* v___x_1462_; uint8_t v___x_1463_; 
v___x_1462_ = lean_obj_once(&l_Std_HashSet_Raw_instEmptyCollection___closed__2, &l_Std_HashSet_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashSet_Raw_instEmptyCollection___closed__2);
v___x_1463_ = lean_uint8_once(&l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashSet_Raw_instSingletonOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1463_ == 0)
{
lean_dec_ref(v_l_1461_);
lean_dec_ref(v_inst_1460_);
lean_dec_ref(v_inst_1459_);
return v___x_1462_;
}
else
{
lean_object* v___f_1464_; lean_object* v___x_1465_; 
v___f_1464_ = ((lean_object*)(l_Std_HashSet_Raw_ofArray___redArg___closed__1));
v___x_1465_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1464_, v_inst_1459_, v_inst_1460_, v___x_1462_, v_l_1461_);
return v___x_1465_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg(lean_object* v_m_1466_){
_start:
{
lean_object* v___x_1467_; 
v___x_1467_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1466_);
return v___x_1467_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Std_HashSet_Raw_Internal_numBuckets___redArg(v_m_1468_);
lean_dec_ref(v_m_1468_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets(lean_object* v_00_u03b1_1470_, lean_object* v_m_1471_){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_1471_);
return v___x_1472_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_1473_, lean_object* v_m_1474_){
_start:
{
lean_object* v_res_1475_; 
v_res_1475_ = l_Std_HashSet_Raw_Internal_numBuckets(v_00_u03b1_1473_, v_m_1474_);
lean_dec_ref(v_m_1474_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__1(lean_object* v___f_1479_, lean_object* v_inst_1480_, lean_object* v_m_1481_, lean_object* v_prec_1482_){
_start:
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1483_ = ((lean_object*)(l_Std_HashSet_Raw_instRepr___redArg___lam__1___closed__1));
v___x_1484_ = lean_box(0);
v___x_1485_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__10));
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_1485_, v___f_1479_, v_m_1481_, v___x_1484_, v___x_1486_);
v___x_1488_ = l_List_repr___redArg(v_inst_1480_, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1483_);
lean_ctor_set(v___x_1489_, 1, v___x_1488_);
v___x_1490_ = l_Repr_addAppParen(v___x_1489_, v_prec_1482_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_1491_, lean_object* v_inst_1492_, lean_object* v_m_1493_, lean_object* v_prec_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Std_HashSet_Raw_instRepr___redArg___lam__1(v___f_1491_, v_inst_1492_, v_m_1493_, v_prec_1494_);
lean_dec(v_prec_1494_);
lean_dec_ref(v_m_1493_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr___redArg(lean_object* v_inst_1496_){
_start:
{
lean_object* v___f_1497_; lean_object* v___f_1498_; 
v___f_1497_ = ((lean_object*)(l_Std_HashSet_Raw_toList___redArg___closed__0));
v___f_1498_ = lean_alloc_closure((void*)(l_Std_HashSet_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1498_, 0, v___f_1497_);
lean_closure_set(v___f_1498_, 1, v_inst_1496_);
return v___f_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_HashSet_Raw_instRepr(lean_object* v_00_u03b1_1499_, lean_object* v_inst_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Std_HashSet_Raw_instRepr___redArg(v_inst_1500_);
return v___x_1501_;
}
}
lean_object* runtime_initialize_Std_Data_HashMap_Raw(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_HashSet_Raw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_HashSet_Raw(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_HashMap_Raw(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_HashSet_Raw(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_HashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_HashSet_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_HashSet_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_HashSet_Raw(builtin);
}
#ifdef __cplusplus
}
#endif
