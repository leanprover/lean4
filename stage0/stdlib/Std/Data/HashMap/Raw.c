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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_HashMap_Raw_instEmptyCollection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_instEmptyCollection___closed__2;
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
static lean_once_cell_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__2;
static lean_once_cell_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__3;
static lean_once_cell_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__4;
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
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__1_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__2 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__2_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__3 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__3_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__4 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__4_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__5 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__5_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__6 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__6_value;
static const lean_closure_object l_Std_HashMap_Raw_keys___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__7 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__7_value;
static const lean_ctor_object l_Std_HashMap_Raw_keys___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__1_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__2_value)}};
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__8 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__8_value;
static const lean_ctor_object l_Std_HashMap_Raw_keys___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__8_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__3_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__4_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__5_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__6_value)}};
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__9 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value;
static const lean_ctor_object l_Std_HashMap_Raw_keys___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__7_value)}};
static const lean_object* l_Std_HashMap_Raw_keys___redArg___closed__10 = (const lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__10_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__10_value)} };
static const lean_object* l_Std_HashMap_Raw_ofList___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_Raw_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_Raw_ofList___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_HashMap_Raw_unitOfList___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_unitOfList___redArg___closed__0;
static lean_once_cell_t l_Std_HashMap_Raw_unitOfList___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_HashMap_Raw_unitOfList___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_ofArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__10_value)} };
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
static const lean_closure_object l_Std_HashMap_Raw_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_toList___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Std_HashMap_Raw_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_keys___redArg___closed__10_value)} };
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_toArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_keysArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_values___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_Raw_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_valuesArray___redArg___closed__0_value;
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
static const lean_string_object l_Std_HashMap_Raw_instRepr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Std.HashMap.Raw.ofList "};
static const lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_HashMap_Raw_instRepr___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_HashMap_Raw_instRepr___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_HashMap_Raw_instRepr___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_HashMap_Raw_instRepr___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
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
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_HashMap_Raw_emptyWithCapacity___redArg(v_capacity_13_);
lean_dec(v_capacity_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity(lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_capacity_17_){
_start:
{
lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v_cellCount_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_18_ = lean_unsigned_to_nat(4u);
v___x_19_ = lean_nat_mul(v_capacity_17_, v___x_18_);
v___x_20_ = lean_unsigned_to_nat(2u);
v___x_21_ = lean_nat_add(v___x_19_, v___x_20_);
lean_dec(v___x_19_);
v___x_22_ = lean_unsigned_to_nat(3u);
v___x_23_ = lean_nat_div(v___x_21_, v___x_22_);
lean_dec(v___x_21_);
v_cellCount_24_ = l_Nat_nextPowerOfTwo(v___x_23_);
lean_dec(v___x_23_);
v___x_25_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_24_);
v___x_26_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_24_);
v___x_27_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_24_);
v___x_28_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_28_, 0, v___x_25_);
lean_ctor_set(v___x_28_, 1, v___x_26_);
lean_ctor_set(v___x_28_, 2, v___x_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_emptyWithCapacity___boxed(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_capacity_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_HashMap_Raw_emptyWithCapacity(v_00_u03b1_29_, v_00_u03b2_30_, v_capacity_31_);
lean_dec(v_capacity_31_);
return v_res_32_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v_cellCount_33_; lean_object* v___x_34_; 
v_cellCount_33_ = lean_unsigned_to_nat(16u);
v___x_34_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v_cellCount_35_; lean_object* v___x_36_; 
v_cellCount_35_ = lean_unsigned_to_nat(16u);
v___x_36_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_37_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__1, &l_Std_HashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__1);
v___x_38_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0);
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
lean_ctor_set(v___x_40_, 2, v___x_37_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInhabited(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_46_;
}
}
static lean_object* _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__5));
v___x_88_ = l_String_toRawSubstring_x27(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(lean_object* v_x_110_, lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_113_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_110_);
v___x_114_ = l_Lean_Syntax_isOfKind(v_x_110_, v___x_113_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; lean_object* v___x_116_; 
lean_dec(v_x_110_);
v___x_115_ = lean_box(1);
v___x_116_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_a_112_);
return v___x_116_;
}
else
{
lean_object* v_quotContext_117_; lean_object* v_currMacroScope_118_; lean_object* v_ref_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_quotContext_117_ = lean_ctor_get(v_a_111_, 1);
v_currMacroScope_118_ = lean_ctor_get(v_a_111_, 2);
v_ref_119_ = lean_ctor_get(v_a_111_, 5);
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = l_Lean_Syntax_getArg(v_x_110_, v___x_120_);
v___x_122_ = lean_unsigned_to_nat(2u);
v___x_123_ = l_Lean_Syntax_getArg(v_x_110_, v___x_122_);
lean_dec(v_x_110_);
v___x_124_ = 0;
v___x_125_ = l_Lean_SourceInfo_fromRef(v_ref_119_, v___x_124_);
v___x_126_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
v___x_127_ = lean_obj_once(&l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6, &l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__6);
v___x_128_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_118_);
lean_inc(v_quotContext_117_);
v___x_129_ = l_Lean_addMacroScope(v_quotContext_117_, v___x_128_, v_currMacroScope_118_);
v___x_130_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__12));
lean_inc_n(v___x_125_, 2);
v___x_131_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_131_, 0, v___x_125_);
lean_ctor_set(v___x_131_, 1, v___x_127_);
lean_ctor_set(v___x_131_, 2, v___x_129_);
lean_ctor_set(v___x_131_, 3, v___x_130_);
v___x_132_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__14));
v___x_133_ = l_Lean_Syntax_node2(v___x_125_, v___x_132_, v___x_121_, v___x_123_);
v___x_134_ = l_Lean_Syntax_node2(v___x_125_, v___x_126_, v___x_131_, v___x_133_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_a_112_);
return v___x_135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___boxed(lean_object* v_x_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1(v_x_136_, v_a_137_, v_a_138_);
lean_dec_ref(v_a_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______macroRules__Std__HashMap__Raw__term___x7em____1___closed__4));
lean_inc(v_x_143_);
v___x_147_ = l_Lean_Syntax_isOfKind(v_x_143_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_x_143_);
v___x_148_ = lean_box(0);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_a_145_);
return v___x_149_;
}
else
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_150_ = lean_unsigned_to_nat(0u);
v___x_151_ = l_Lean_Syntax_getArg(v_x_143_, v___x_150_);
v___x_152_ = ((lean_object*)(l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_151_);
v___x_153_ = l_Lean_Syntax_isOfKind(v___x_151_, v___x_152_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v___x_151_);
lean_dec(v_x_143_);
v___x_154_ = lean_box(0);
v___x_155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_145_);
return v___x_155_;
}
else
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = l_Lean_Syntax_getArg(v_x_143_, v___x_156_);
lean_dec(v_x_143_);
v___x_158_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_157_);
v___x_159_ = l_Lean_Syntax_matchesNull(v___x_157_, v___x_158_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v___x_161_; 
lean_dec(v___x_157_);
lean_dec(v___x_151_);
v___x_160_ = lean_box(0);
v___x_161_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_160_);
lean_ctor_set(v___x_161_, 1, v_a_145_);
return v___x_161_;
}
else
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v_ref_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_162_ = l_Lean_Syntax_getArg(v___x_157_, v___x_150_);
v___x_163_ = l_Lean_Syntax_getArg(v___x_157_, v___x_156_);
lean_dec(v___x_157_);
v_ref_164_ = l_Lean_replaceRef(v___x_151_, v_a_144_);
lean_dec(v___x_151_);
v___x_165_ = 0;
v___x_166_ = l_Lean_SourceInfo_fromRef(v_ref_164_, v___x_165_);
lean_dec(v_ref_164_);
v___x_167_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__4));
v___x_168_ = ((lean_object*)(l_Std_HashMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_166_);
v___x_169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_166_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
v___x_170_ = l_Lean_Syntax_node3(v___x_166_, v___x_167_, v___x_162_, v___x_169_, v___x_163_);
v___x_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_a_145_);
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1___boxed(lean_object* v_x_172_, lean_object* v_a_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Std_HashMap_Raw___aux__Std__Data__HashMap__Raw______unexpand__Std__HashMap__Raw__Equiv__1(v_x_172_, v_a_173_, v_a_174_);
lean_dec(v_a_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert___redArg(lean_object* v_beq_176_, lean_object* v_inst_177_, lean_object* v_m_178_, lean_object* v_a_179_, lean_object* v_b_180_){
_start:
{
lean_object* v___y_182_; lean_object* v_i_183_; lean_object* v___y_189_; lean_object* v___y_199_; lean_object* v_i_200_; lean_object* v_size_205_; lean_object* v_keyArray_206_; lean_object* v___x_207_; lean_object* v___x_217_; uint8_t v___x_218_; 
v_size_205_ = lean_ctor_get(v_m_178_, 0);
v_keyArray_206_ = lean_ctor_get(v_m_178_, 1);
v___x_207_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_array_get_size(v_keyArray_206_);
v___x_218_ = lean_nat_dec_lt(v___x_207_, v___x_217_);
if (v___x_218_ == 0)
{
lean_dec(v_b_180_);
lean_dec(v_a_179_);
lean_dec_ref(v_inst_177_);
lean_dec_ref(v_beq_176_);
return v_m_178_;
}
else
{
lean_object* v___x_219_; 
lean_inc(v_a_179_);
lean_inc_ref(v_inst_177_);
lean_inc_ref(v_beq_176_);
v___x_219_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_beq_176_, v_inst_177_, v_m_178_, v_a_179_);
switch(lean_obj_tag(v___x_219_))
{
case 0:
{
lean_object* v_index_220_; lean_object* v___x_221_; 
lean_inc(v_size_205_);
lean_dec_ref(v_inst_177_);
lean_dec_ref(v_beq_176_);
v_index_220_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_index_220_);
lean_dec_ref_known(v___x_219_, 3);
v___x_221_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_178_, v_size_205_, v_index_220_, v_a_179_, v_b_180_);
lean_dec(v_index_220_);
return v___x_221_;
}
case 1:
{
lean_object* v_index_222_; lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v_index_222_ = lean_ctor_get(v___x_219_, 0);
lean_inc(v_index_222_);
lean_dec_ref_known(v___x_219_, 1);
v___x_223_ = lean_unsigned_to_nat(1u);
v___x_224_ = lean_nat_add(v_size_205_, v___x_223_);
v___x_225_ = lean_nat_dec_lt(v___x_224_, v___x_217_);
if (v___x_225_ == 0)
{
lean_dec(v___x_224_);
lean_dec(v_index_222_);
goto v___jp_208_;
}
else
{
lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; 
v___x_226_ = lean_unsigned_to_nat(4u);
v___x_227_ = lean_nat_mul(v___x_224_, v___x_226_);
v___x_228_ = lean_unsigned_to_nat(3u);
v___x_229_ = lean_nat_mul(v___x_217_, v___x_228_);
v___x_230_ = lean_nat_dec_le(v___x_227_, v___x_229_);
lean_dec(v___x_229_);
lean_dec(v___x_227_);
if (v___x_230_ == 0)
{
lean_dec(v___x_224_);
lean_dec(v_index_222_);
goto v___jp_208_;
}
else
{
lean_object* v___x_231_; 
lean_dec_ref(v_inst_177_);
lean_dec_ref(v_beq_176_);
v___x_231_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_178_, v___x_224_, v_index_222_, v_a_179_, v_b_180_);
lean_dec(v_index_222_);
return v___x_231_;
}
}
}
default: 
{
lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v___x_232_ = lean_unsigned_to_nat(1u);
v___x_233_ = lean_nat_add(v_size_205_, v___x_232_);
v___x_234_ = lean_nat_dec_lt(v___x_233_, v___x_217_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
lean_dec(v___x_233_);
lean_inc_ref(v_inst_177_);
lean_inc_ref(v_beq_176_);
v___x_235_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_beq_176_, v_inst_177_, v_m_178_);
v___y_189_ = v___x_235_;
goto v___jp_188_;
}
else
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; uint8_t v___x_240_; 
v___x_236_ = lean_unsigned_to_nat(4u);
v___x_237_ = lean_nat_mul(v___x_233_, v___x_236_);
lean_dec(v___x_233_);
v___x_238_ = lean_unsigned_to_nat(3u);
v___x_239_ = lean_nat_mul(v___x_217_, v___x_238_);
v___x_240_ = lean_nat_dec_le(v___x_237_, v___x_239_);
lean_dec(v___x_239_);
lean_dec(v___x_237_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
lean_inc_ref(v_inst_177_);
lean_inc_ref(v_beq_176_);
v___x_241_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_beq_176_, v_inst_177_, v_m_178_);
v___y_189_ = v___x_241_;
goto v___jp_188_;
}
else
{
v___y_189_ = v_m_178_;
goto v___jp_188_;
}
}
}
}
}
v___jp_181_:
{
lean_object* v_size_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v_size_184_ = lean_ctor_get(v___y_182_, 0);
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_add(v_size_184_, v___x_185_);
v___x_187_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_182_, v___x_186_, v_i_183_, v_a_179_, v_b_180_);
lean_dec(v_i_183_);
return v___x_187_;
}
v___jp_188_:
{
lean_object* v___x_190_; 
lean_inc(v_a_179_);
v___x_190_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_beq_176_, v_inst_177_, v___y_189_, v_a_179_);
switch(lean_obj_tag(v___x_190_))
{
case 0:
{
lean_object* v_index_191_; lean_object* v_size_192_; lean_object* v___x_193_; 
v_index_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_index_191_);
lean_dec_ref_known(v___x_190_, 3);
v_size_192_ = lean_ctor_get(v___y_189_, 0);
lean_inc(v_size_192_);
v___x_193_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_189_, v_size_192_, v_index_191_, v_a_179_, v_b_180_);
lean_dec(v_index_191_);
return v___x_193_;
}
case 1:
{
lean_object* v_index_194_; 
v_index_194_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_index_194_);
lean_dec_ref_known(v___x_190_, 1);
v___y_182_ = v___y_189_;
v_i_183_ = v_index_194_;
goto v___jp_181_;
}
default: 
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = lean_unsigned_to_nat(0u);
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_189_, v___x_195_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_index_197_; 
v_index_197_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_index_197_);
lean_dec_ref_known(v___x_196_, 1);
v___y_182_ = v___y_189_;
v_i_183_ = v_index_197_;
goto v___jp_181_;
}
else
{
lean_dec(v_b_180_);
lean_dec(v_a_179_);
return v___y_189_;
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
v___x_204_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_199_, v___x_203_, v_i_200_, v_a_179_, v_b_180_);
lean_dec(v_i_200_);
return v___x_204_;
}
v___jp_208_:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
lean_inc_ref(v_inst_177_);
lean_inc_ref(v_beq_176_);
v___x_209_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_beq_176_, v_inst_177_, v_m_178_);
lean_inc(v_a_179_);
v___x_210_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_beq_176_, v_inst_177_, v___x_209_, v_a_179_);
switch(lean_obj_tag(v___x_210_))
{
case 0:
{
lean_object* v_index_211_; lean_object* v_size_212_; lean_object* v___x_213_; 
v_index_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_index_211_);
lean_dec_ref_known(v___x_210_, 3);
v_size_212_ = lean_ctor_get(v___x_209_, 0);
lean_inc(v_size_212_);
v___x_213_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_209_, v_size_212_, v_index_211_, v_a_179_, v_b_180_);
lean_dec(v_index_211_);
return v___x_213_;
}
case 1:
{
lean_object* v_index_214_; 
v_index_214_ = lean_ctor_get(v___x_210_, 0);
lean_inc(v_index_214_);
lean_dec_ref_known(v___x_210_, 1);
v___y_199_ = v___x_209_;
v_i_200_ = v_index_214_;
goto v___jp_198_;
}
default: 
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_209_, v___x_207_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_index_216_; 
v_index_216_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_index_216_);
lean_dec_ref_known(v___x_215_, 1);
v___y_199_ = v___x_209_;
v_i_200_ = v_index_216_;
goto v___jp_198_;
}
else
{
lean_dec(v_b_180_);
lean_dec(v_a_179_);
return v___x_209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insert(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_beq_244_, lean_object* v_inst_245_, lean_object* v_m_246_, lean_object* v_a_247_, lean_object* v_b_248_){
_start:
{
lean_object* v___y_250_; lean_object* v_i_251_; lean_object* v___y_257_; lean_object* v___y_267_; lean_object* v_i_268_; lean_object* v_size_273_; lean_object* v_keyArray_274_; lean_object* v___x_275_; lean_object* v___x_285_; uint8_t v___x_286_; 
v_size_273_ = lean_ctor_get(v_m_246_, 0);
v_keyArray_274_ = lean_ctor_get(v_m_246_, 1);
v___x_275_ = lean_unsigned_to_nat(0u);
v___x_285_ = lean_array_get_size(v_keyArray_274_);
v___x_286_ = lean_nat_dec_lt(v___x_275_, v___x_285_);
if (v___x_286_ == 0)
{
lean_dec(v_b_248_);
lean_dec(v_a_247_);
lean_dec_ref(v_inst_245_);
lean_dec_ref(v_beq_244_);
return v_m_246_;
}
else
{
lean_object* v___x_287_; 
lean_inc(v_a_247_);
lean_inc_ref(v_inst_245_);
lean_inc_ref(v_beq_244_);
v___x_287_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_beq_244_, v_inst_245_, v_m_246_, v_a_247_);
switch(lean_obj_tag(v___x_287_))
{
case 0:
{
lean_object* v_index_288_; lean_object* v___x_289_; 
lean_inc(v_size_273_);
lean_dec_ref(v_inst_245_);
lean_dec_ref(v_beq_244_);
v_index_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_index_288_);
lean_dec_ref_known(v___x_287_, 3);
v___x_289_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_246_, v_size_273_, v_index_288_, v_a_247_, v_b_248_);
lean_dec(v_index_288_);
return v___x_289_;
}
case 1:
{
lean_object* v_index_290_; lean_object* v___x_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_index_290_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_index_290_);
lean_dec_ref_known(v___x_287_, 1);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_size_273_, v___x_291_);
v___x_293_ = lean_nat_dec_lt(v___x_292_, v___x_285_);
if (v___x_293_ == 0)
{
lean_dec(v___x_292_);
lean_dec(v_index_290_);
goto v___jp_276_;
}
else
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; uint8_t v___x_298_; 
v___x_294_ = lean_unsigned_to_nat(4u);
v___x_295_ = lean_nat_mul(v___x_292_, v___x_294_);
v___x_296_ = lean_unsigned_to_nat(3u);
v___x_297_ = lean_nat_mul(v___x_285_, v___x_296_);
v___x_298_ = lean_nat_dec_le(v___x_295_, v___x_297_);
lean_dec(v___x_297_);
lean_dec(v___x_295_);
if (v___x_298_ == 0)
{
lean_dec(v___x_292_);
lean_dec(v_index_290_);
goto v___jp_276_;
}
else
{
lean_object* v___x_299_; 
lean_dec_ref(v_inst_245_);
lean_dec_ref(v_beq_244_);
v___x_299_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_246_, v___x_292_, v_index_290_, v_a_247_, v_b_248_);
lean_dec(v_index_290_);
return v___x_299_;
}
}
}
default: 
{
lean_object* v___x_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v___x_300_ = lean_unsigned_to_nat(1u);
v___x_301_ = lean_nat_add(v_size_273_, v___x_300_);
v___x_302_ = lean_nat_dec_lt(v___x_301_, v___x_285_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
lean_dec(v___x_301_);
lean_inc_ref(v_inst_245_);
lean_inc_ref(v_beq_244_);
v___x_303_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_beq_244_, v_inst_245_, v_m_246_);
v___y_257_ = v___x_303_;
goto v___jp_256_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_304_ = lean_unsigned_to_nat(4u);
v___x_305_ = lean_nat_mul(v___x_301_, v___x_304_);
lean_dec(v___x_301_);
v___x_306_ = lean_unsigned_to_nat(3u);
v___x_307_ = lean_nat_mul(v___x_285_, v___x_306_);
v___x_308_ = lean_nat_dec_le(v___x_305_, v___x_307_);
lean_dec(v___x_307_);
lean_dec(v___x_305_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; 
lean_inc_ref(v_inst_245_);
lean_inc_ref(v_beq_244_);
v___x_309_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_beq_244_, v_inst_245_, v_m_246_);
v___y_257_ = v___x_309_;
goto v___jp_256_;
}
else
{
v___y_257_ = v_m_246_;
goto v___jp_256_;
}
}
}
}
}
v___jp_249_:
{
lean_object* v_size_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v_size_252_ = lean_ctor_get(v___y_250_, 0);
v___x_253_ = lean_unsigned_to_nat(1u);
v___x_254_ = lean_nat_add(v_size_252_, v___x_253_);
v___x_255_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_250_, v___x_254_, v_i_251_, v_a_247_, v_b_248_);
lean_dec(v_i_251_);
return v___x_255_;
}
v___jp_256_:
{
lean_object* v___x_258_; 
lean_inc(v_a_247_);
v___x_258_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_beq_244_, v_inst_245_, v___y_257_, v_a_247_);
switch(lean_obj_tag(v___x_258_))
{
case 0:
{
lean_object* v_index_259_; lean_object* v_size_260_; lean_object* v___x_261_; 
v_index_259_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_index_259_);
lean_dec_ref_known(v___x_258_, 3);
v_size_260_ = lean_ctor_get(v___y_257_, 0);
lean_inc(v_size_260_);
v___x_261_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_257_, v_size_260_, v_index_259_, v_a_247_, v_b_248_);
lean_dec(v_index_259_);
return v___x_261_;
}
case 1:
{
lean_object* v_index_262_; 
v_index_262_ = lean_ctor_get(v___x_258_, 0);
lean_inc(v_index_262_);
lean_dec_ref_known(v___x_258_, 1);
v___y_250_ = v___y_257_;
v_i_251_ = v_index_262_;
goto v___jp_249_;
}
default: 
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_257_, v___x_263_);
if (lean_obj_tag(v___x_264_) == 0)
{
lean_object* v_index_265_; 
v_index_265_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_index_265_);
lean_dec_ref_known(v___x_264_, 1);
v___y_250_ = v___y_257_;
v_i_251_ = v_index_265_;
goto v___jp_249_;
}
else
{
lean_dec(v_b_248_);
lean_dec(v_a_247_);
return v___y_257_;
}
}
}
}
v___jp_266_:
{
lean_object* v_size_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_size_269_ = lean_ctor_get(v___y_267_, 0);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_size_269_, v___x_270_);
v___x_272_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_267_, v___x_271_, v_i_268_, v_a_247_, v_b_248_);
lean_dec(v_i_268_);
return v___x_272_;
}
v___jp_276_:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_inc_ref(v_inst_245_);
lean_inc_ref(v_beq_244_);
v___x_277_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_beq_244_, v_inst_245_, v_m_246_);
lean_inc(v_a_247_);
v___x_278_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_beq_244_, v_inst_245_, v___x_277_, v_a_247_);
switch(lean_obj_tag(v___x_278_))
{
case 0:
{
lean_object* v_index_279_; lean_object* v_size_280_; lean_object* v___x_281_; 
v_index_279_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_index_279_);
lean_dec_ref_known(v___x_278_, 3);
v_size_280_ = lean_ctor_get(v___x_277_, 0);
lean_inc(v_size_280_);
v___x_281_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_277_, v_size_280_, v_index_279_, v_a_247_, v_b_248_);
lean_dec(v_index_279_);
return v___x_281_;
}
case 1:
{
lean_object* v_index_282_; 
v_index_282_ = lean_ctor_get(v___x_278_, 0);
lean_inc(v_index_282_);
lean_dec_ref_known(v___x_278_, 1);
v___y_267_ = v___x_277_;
v_i_268_ = v_index_282_;
goto v___jp_266_;
}
default: 
{
lean_object* v___x_283_; 
v___x_283_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_277_, v___x_275_);
if (lean_obj_tag(v___x_283_) == 0)
{
lean_object* v_index_284_; 
v_index_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_index_284_);
lean_dec_ref_known(v___x_283_, 1);
v___y_267_ = v___x_277_;
v_i_268_ = v_index_284_;
goto v___jp_266_;
}
else
{
lean_dec(v_b_248_);
lean_dec(v_a_247_);
return v___x_277_;
}
}
}
}
}
}
static lean_object* _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_310_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0);
v___x_311_ = lean_array_get_size(v___x_310_);
return v___x_311_;
}
}
static uint8_t _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_312_ = lean_obj_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_313_ = lean_unsigned_to_nat(0u);
v___x_314_ = lean_nat_dec_lt(v___x_313_, v___x_312_);
return v___x_314_;
}
}
static uint8_t _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_315_ = lean_obj_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_dec_lt(v___x_316_, v___x_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_318_ = lean_unsigned_to_nat(3u);
v___x_319_ = lean_obj_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_320_ = lean_nat_mul(v___x_319_, v___x_318_);
return v___x_320_;
}
}
static uint8_t _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; uint8_t v___x_323_; 
v___x_321_ = lean_obj_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__3, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__3_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__3);
v___x_322_ = lean_unsigned_to_nat(4u);
v___x_323_ = lean_nat_dec_le(v___x_322_, v___x_321_);
return v___x_323_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_x_326_){
_start:
{
lean_object* v_fst_327_; lean_object* v_snd_328_; lean_object* v___y_330_; lean_object* v_i_331_; lean_object* v___y_337_; lean_object* v_i_338_; lean_object* v___y_344_; lean_object* v___x_353_; lean_object* v___x_354_; uint8_t v___x_364_; 
v_fst_327_ = lean_ctor_get(v_x_326_, 0);
lean_inc(v_fst_327_);
v_snd_328_ = lean_ctor_get(v_x_326_, 1);
lean_inc(v_snd_328_);
lean_dec_ref(v_x_326_);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
v___x_364_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_364_ == 0)
{
lean_dec(v_snd_328_);
lean_dec(v_fst_327_);
lean_dec_ref(v_inst_325_);
lean_dec_ref(v_inst_324_);
return v___x_354_;
}
else
{
lean_object* v___x_365_; 
lean_inc(v_fst_327_);
lean_inc_ref(v_inst_325_);
lean_inc_ref(v_inst_324_);
v___x_365_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_324_, v_inst_325_, v___x_354_, v_fst_327_);
switch(lean_obj_tag(v___x_365_))
{
case 0:
{
lean_object* v_index_366_; lean_object* v___x_367_; 
lean_dec_ref(v_inst_325_);
lean_dec_ref(v_inst_324_);
v_index_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_index_366_);
lean_dec_ref_known(v___x_365_, 3);
v___x_367_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_354_, v___x_353_, v_index_366_, v_fst_327_, v_snd_328_);
lean_dec(v_index_366_);
return v___x_367_;
}
case 1:
{
lean_object* v_index_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_index_368_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_index_368_);
lean_dec_ref_known(v___x_365_, 1);
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__2, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__2_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__2);
if (v___x_370_ == 0)
{
lean_dec(v_index_368_);
goto v___jp_355_;
}
else
{
uint8_t v___x_371_; 
v___x_371_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__4, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__4_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__4);
if (v___x_371_ == 0)
{
lean_dec(v_index_368_);
goto v___jp_355_;
}
else
{
lean_object* v___x_372_; 
lean_dec_ref(v_inst_325_);
lean_dec_ref(v_inst_324_);
v___x_372_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_354_, v___x_369_, v_index_368_, v_fst_327_, v_snd_328_);
lean_dec(v_index_368_);
return v___x_372_;
}
}
}
default: 
{
uint8_t v___x_373_; 
v___x_373_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__2, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__2_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__2);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; 
lean_inc_ref(v_inst_325_);
lean_inc_ref(v_inst_324_);
v___x_374_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_324_, v_inst_325_, v___x_354_);
v___y_344_ = v___x_374_;
goto v___jp_343_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__4, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__4_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__4);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_inc_ref(v_inst_325_);
lean_inc_ref(v_inst_324_);
v___x_376_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_324_, v_inst_325_, v___x_354_);
v___y_344_ = v___x_376_;
goto v___jp_343_;
}
else
{
v___y_344_ = v___x_354_;
goto v___jp_343_;
}
}
}
}
}
v___jp_329_:
{
lean_object* v_size_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v_size_332_ = lean_ctor_get(v___y_330_, 0);
v___x_333_ = lean_unsigned_to_nat(1u);
v___x_334_ = lean_nat_add(v_size_332_, v___x_333_);
v___x_335_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_330_, v___x_334_, v_i_331_, v_fst_327_, v_snd_328_);
lean_dec(v_i_331_);
return v___x_335_;
}
v___jp_336_:
{
lean_object* v_size_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_size_339_ = lean_ctor_get(v___y_337_, 0);
v___x_340_ = lean_unsigned_to_nat(1u);
v___x_341_ = lean_nat_add(v_size_339_, v___x_340_);
v___x_342_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_337_, v___x_341_, v_i_338_, v_fst_327_, v_snd_328_);
lean_dec(v_i_338_);
return v___x_342_;
}
v___jp_343_:
{
lean_object* v___x_345_; 
lean_inc(v_fst_327_);
v___x_345_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_324_, v_inst_325_, v___y_344_, v_fst_327_);
switch(lean_obj_tag(v___x_345_))
{
case 0:
{
lean_object* v_index_346_; lean_object* v_size_347_; lean_object* v___x_348_; 
v_index_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_index_346_);
lean_dec_ref_known(v___x_345_, 3);
v_size_347_ = lean_ctor_get(v___y_344_, 0);
lean_inc(v_size_347_);
v___x_348_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_344_, v_size_347_, v_index_346_, v_fst_327_, v_snd_328_);
lean_dec(v_index_346_);
return v___x_348_;
}
case 1:
{
lean_object* v_index_349_; 
v_index_349_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_index_349_);
lean_dec_ref_known(v___x_345_, 1);
v___y_337_ = v___y_344_;
v_i_338_ = v_index_349_;
goto v___jp_336_;
}
default: 
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_unsigned_to_nat(0u);
v___x_351_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_344_, v___x_350_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_index_352_; 
v_index_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_index_352_);
lean_dec_ref_known(v___x_351_, 1);
v___y_337_ = v___y_344_;
v_i_338_ = v_index_352_;
goto v___jp_336_;
}
else
{
lean_dec(v_snd_328_);
lean_dec(v_fst_327_);
return v___y_344_;
}
}
}
}
v___jp_355_:
{
lean_object* v___x_356_; lean_object* v___x_357_; 
lean_inc_ref(v_inst_325_);
lean_inc_ref(v_inst_324_);
v___x_356_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_324_, v_inst_325_, v___x_354_);
lean_inc(v_fst_327_);
v___x_357_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_324_, v_inst_325_, v___x_356_, v_fst_327_);
switch(lean_obj_tag(v___x_357_))
{
case 0:
{
lean_object* v_index_358_; lean_object* v_size_359_; lean_object* v___x_360_; 
v_index_358_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_index_358_);
lean_dec_ref_known(v___x_357_, 3);
v_size_359_ = lean_ctor_get(v___x_356_, 0);
lean_inc(v_size_359_);
v___x_360_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_356_, v_size_359_, v_index_358_, v_fst_327_, v_snd_328_);
lean_dec(v_index_358_);
return v___x_360_;
}
case 1:
{
lean_object* v_index_361_; 
v_index_361_ = lean_ctor_get(v___x_357_, 0);
lean_inc(v_index_361_);
lean_dec_ref_known(v___x_357_, 1);
v___y_330_ = v___x_356_;
v_i_331_ = v_index_361_;
goto v___jp_329_;
}
default: 
{
lean_object* v___x_362_; 
v___x_362_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_356_, v___x_353_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_index_363_; 
v_index_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_index_363_);
lean_dec_ref_known(v___x_362_, 1);
v___y_330_ = v___x_356_;
v_i_331_ = v_index_363_;
goto v___jp_329_;
}
else
{
lean_dec(v_snd_328_);
lean_dec(v_fst_327_);
return v___x_356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg(lean_object* v_inst_377_, lean_object* v_inst_378_){
_start:
{
lean_object* v___f_379_; 
v___f_379_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_379_, 0, v_inst_377_);
lean_closure_set(v___f_379_, 1, v_inst_378_);
return v___f_379_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable(lean_object* v_00_u03b1_380_, lean_object* v_00_u03b2_381_, lean_object* v_inst_382_, lean_object* v_inst_383_){
_start:
{
lean_object* v___f_384_; 
v___f_384_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_384_, 0, v_inst_382_);
lean_closure_set(v___f_384_, 1, v_inst_383_);
return v___f_384_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_x_387_, lean_object* v_s_388_){
_start:
{
lean_object* v_fst_389_; lean_object* v_snd_390_; lean_object* v___y_392_; lean_object* v_i_393_; lean_object* v___y_399_; lean_object* v_i_400_; lean_object* v___y_406_; lean_object* v_size_415_; lean_object* v_keyArray_416_; lean_object* v___x_417_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_fst_389_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_fst_389_);
v_snd_390_ = lean_ctor_get(v_x_387_, 1);
lean_inc(v_snd_390_);
lean_dec_ref(v_x_387_);
v_size_415_ = lean_ctor_get(v_s_388_, 0);
v_keyArray_416_ = lean_ctor_get(v_s_388_, 1);
v___x_417_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_array_get_size(v_keyArray_416_);
v___x_428_ = lean_nat_dec_lt(v___x_417_, v___x_427_);
if (v___x_428_ == 0)
{
lean_dec(v_snd_390_);
lean_dec(v_fst_389_);
lean_dec_ref(v_inst_386_);
lean_dec_ref(v_inst_385_);
return v_s_388_;
}
else
{
lean_object* v___x_429_; 
lean_inc(v_fst_389_);
lean_inc_ref(v_inst_386_);
lean_inc_ref(v_inst_385_);
v___x_429_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_385_, v_inst_386_, v_s_388_, v_fst_389_);
switch(lean_obj_tag(v___x_429_))
{
case 0:
{
lean_object* v_index_430_; lean_object* v___x_431_; 
lean_inc(v_size_415_);
lean_dec_ref(v_inst_386_);
lean_dec_ref(v_inst_385_);
v_index_430_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_index_430_);
lean_dec_ref_known(v___x_429_, 3);
v___x_431_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_388_, v_size_415_, v_index_430_, v_fst_389_, v_snd_390_);
lean_dec(v_index_430_);
return v___x_431_;
}
case 1:
{
lean_object* v_index_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_index_432_ = lean_ctor_get(v___x_429_, 0);
lean_inc(v_index_432_);
lean_dec_ref_known(v___x_429_, 1);
v___x_433_ = lean_unsigned_to_nat(1u);
v___x_434_ = lean_nat_add(v_size_415_, v___x_433_);
v___x_435_ = lean_nat_dec_lt(v___x_434_, v___x_427_);
if (v___x_435_ == 0)
{
lean_dec(v___x_434_);
lean_dec(v_index_432_);
goto v___jp_418_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; uint8_t v___x_440_; 
v___x_436_ = lean_unsigned_to_nat(4u);
v___x_437_ = lean_nat_mul(v___x_434_, v___x_436_);
v___x_438_ = lean_unsigned_to_nat(3u);
v___x_439_ = lean_nat_mul(v___x_427_, v___x_438_);
v___x_440_ = lean_nat_dec_le(v___x_437_, v___x_439_);
lean_dec(v___x_439_);
lean_dec(v___x_437_);
if (v___x_440_ == 0)
{
lean_dec(v___x_434_);
lean_dec(v_index_432_);
goto v___jp_418_;
}
else
{
lean_object* v___x_441_; 
lean_dec_ref(v_inst_386_);
lean_dec_ref(v_inst_385_);
v___x_441_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_388_, v___x_434_, v_index_432_, v_fst_389_, v_snd_390_);
lean_dec(v_index_432_);
return v___x_441_;
}
}
}
default: 
{
lean_object* v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_442_ = lean_unsigned_to_nat(1u);
v___x_443_ = lean_nat_add(v_size_415_, v___x_442_);
v___x_444_ = lean_nat_dec_lt(v___x_443_, v___x_427_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec(v___x_443_);
lean_inc_ref(v_inst_386_);
lean_inc_ref(v_inst_385_);
v___x_445_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_385_, v_inst_386_, v_s_388_);
v___y_406_ = v___x_445_;
goto v___jp_405_;
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_446_ = lean_unsigned_to_nat(4u);
v___x_447_ = lean_nat_mul(v___x_443_, v___x_446_);
lean_dec(v___x_443_);
v___x_448_ = lean_unsigned_to_nat(3u);
v___x_449_ = lean_nat_mul(v___x_427_, v___x_448_);
v___x_450_ = lean_nat_dec_le(v___x_447_, v___x_449_);
lean_dec(v___x_449_);
lean_dec(v___x_447_);
if (v___x_450_ == 0)
{
lean_object* v___x_451_; 
lean_inc_ref(v_inst_386_);
lean_inc_ref(v_inst_385_);
v___x_451_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_385_, v_inst_386_, v_s_388_);
v___y_406_ = v___x_451_;
goto v___jp_405_;
}
else
{
v___y_406_ = v_s_388_;
goto v___jp_405_;
}
}
}
}
}
v___jp_391_:
{
lean_object* v_size_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_size_394_ = lean_ctor_get(v___y_392_, 0);
v___x_395_ = lean_unsigned_to_nat(1u);
v___x_396_ = lean_nat_add(v_size_394_, v___x_395_);
v___x_397_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_392_, v___x_396_, v_i_393_, v_fst_389_, v_snd_390_);
lean_dec(v_i_393_);
return v___x_397_;
}
v___jp_398_:
{
lean_object* v_size_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v_size_401_ = lean_ctor_get(v___y_399_, 0);
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = lean_nat_add(v_size_401_, v___x_402_);
v___x_404_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_399_, v___x_403_, v_i_400_, v_fst_389_, v_snd_390_);
lean_dec(v_i_400_);
return v___x_404_;
}
v___jp_405_:
{
lean_object* v___x_407_; 
lean_inc(v_fst_389_);
v___x_407_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_385_, v_inst_386_, v___y_406_, v_fst_389_);
switch(lean_obj_tag(v___x_407_))
{
case 0:
{
lean_object* v_index_408_; lean_object* v_size_409_; lean_object* v___x_410_; 
v_index_408_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_index_408_);
lean_dec_ref_known(v___x_407_, 3);
v_size_409_ = lean_ctor_get(v___y_406_, 0);
lean_inc(v_size_409_);
v___x_410_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_406_, v_size_409_, v_index_408_, v_fst_389_, v_snd_390_);
lean_dec(v_index_408_);
return v___x_410_;
}
case 1:
{
lean_object* v_index_411_; 
v_index_411_ = lean_ctor_get(v___x_407_, 0);
lean_inc(v_index_411_);
lean_dec_ref_known(v___x_407_, 1);
v___y_399_ = v___y_406_;
v_i_400_ = v_index_411_;
goto v___jp_398_;
}
default: 
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_406_, v___x_412_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_index_414_; 
v_index_414_ = lean_ctor_get(v___x_413_, 0);
lean_inc(v_index_414_);
lean_dec_ref_known(v___x_413_, 1);
v___y_399_ = v___y_406_;
v_i_400_ = v_index_414_;
goto v___jp_398_;
}
else
{
lean_dec(v_snd_390_);
lean_dec(v_fst_389_);
return v___y_406_;
}
}
}
}
v___jp_418_:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
lean_inc_ref(v_inst_386_);
lean_inc_ref(v_inst_385_);
v___x_419_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_385_, v_inst_386_, v_s_388_);
lean_inc(v_fst_389_);
v___x_420_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_385_, v_inst_386_, v___x_419_, v_fst_389_);
switch(lean_obj_tag(v___x_420_))
{
case 0:
{
lean_object* v_index_421_; lean_object* v_size_422_; lean_object* v___x_423_; 
v_index_421_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_index_421_);
lean_dec_ref_known(v___x_420_, 3);
v_size_422_ = lean_ctor_get(v___x_419_, 0);
lean_inc(v_size_422_);
v___x_423_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_419_, v_size_422_, v_index_421_, v_fst_389_, v_snd_390_);
lean_dec(v_index_421_);
return v___x_423_;
}
case 1:
{
lean_object* v_index_424_; 
v_index_424_ = lean_ctor_get(v___x_420_, 0);
lean_inc(v_index_424_);
lean_dec_ref_known(v___x_420_, 1);
v___y_392_ = v___x_419_;
v_i_393_ = v_index_424_;
goto v___jp_391_;
}
default: 
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_419_, v___x_417_);
if (lean_obj_tag(v___x_425_) == 0)
{
lean_object* v_index_426_; 
v_index_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc(v_index_426_);
lean_dec_ref_known(v___x_425_, 1);
v___y_392_ = v___x_419_;
v_i_393_ = v_index_426_;
goto v___jp_391_;
}
else
{
lean_dec(v_snd_390_);
lean_dec(v_fst_389_);
return v___x_419_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg(lean_object* v_inst_452_, lean_object* v_inst_453_){
_start:
{
lean_object* v___f_454_; 
v___f_454_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_454_, 0, v_inst_452_);
lean_closure_set(v___f_454_, 1, v_inst_453_);
return v___f_454_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable(lean_object* v_00_u03b1_455_, lean_object* v_00_u03b2_456_, lean_object* v_inst_457_, lean_object* v_inst_458_){
_start:
{
lean_object* v___f_459_; 
v___f_459_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instInsertProdOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_459_, 0, v_inst_457_);
lean_closure_set(v___f_459_, 1, v_inst_458_);
return v___f_459_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew___redArg(lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_m_462_, lean_object* v_a_463_, lean_object* v_b_464_){
_start:
{
lean_object* v___y_466_; lean_object* v_i_467_; lean_object* v___y_473_; lean_object* v___y_483_; lean_object* v_i_484_; lean_object* v_size_489_; lean_object* v_keyArray_490_; lean_object* v___x_491_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_size_489_ = lean_ctor_get(v_m_462_, 0);
v_keyArray_490_ = lean_ctor_get(v_m_462_, 1);
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_501_ = lean_array_get_size(v_keyArray_490_);
v___x_502_ = lean_nat_dec_lt(v___x_491_, v___x_501_);
if (v___x_502_ == 0)
{
lean_dec(v_b_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_inst_461_);
lean_dec_ref(v_inst_460_);
return v_m_462_;
}
else
{
lean_object* v___x_503_; 
lean_inc(v_a_463_);
lean_inc_ref(v_inst_461_);
lean_inc_ref(v_inst_460_);
v___x_503_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_460_, v_inst_461_, v_m_462_, v_a_463_);
switch(lean_obj_tag(v___x_503_))
{
case 0:
{
lean_dec_ref_known(v___x_503_, 3);
lean_dec(v_b_464_);
lean_dec(v_a_463_);
lean_dec_ref(v_inst_461_);
lean_dec_ref(v_inst_460_);
return v_m_462_;
}
case 1:
{
lean_object* v_index_504_; lean_object* v___x_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_index_504_ = lean_ctor_get(v___x_503_, 0);
lean_inc(v_index_504_);
lean_dec_ref_known(v___x_503_, 1);
v___x_505_ = lean_unsigned_to_nat(1u);
v___x_506_ = lean_nat_add(v_size_489_, v___x_505_);
v___x_507_ = lean_nat_dec_lt(v___x_506_, v___x_501_);
if (v___x_507_ == 0)
{
lean_dec(v___x_506_);
lean_dec(v_index_504_);
goto v___jp_492_;
}
else
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_508_ = lean_unsigned_to_nat(4u);
v___x_509_ = lean_nat_mul(v___x_506_, v___x_508_);
v___x_510_ = lean_unsigned_to_nat(3u);
v___x_511_ = lean_nat_mul(v___x_501_, v___x_510_);
v___x_512_ = lean_nat_dec_le(v___x_509_, v___x_511_);
lean_dec(v___x_511_);
lean_dec(v___x_509_);
if (v___x_512_ == 0)
{
lean_dec(v___x_506_);
lean_dec(v_index_504_);
goto v___jp_492_;
}
else
{
lean_object* v___x_513_; 
lean_dec_ref(v_inst_461_);
lean_dec_ref(v_inst_460_);
v___x_513_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_462_, v___x_506_, v_index_504_, v_a_463_, v_b_464_);
lean_dec(v_index_504_);
return v___x_513_;
}
}
}
default: 
{
lean_object* v___x_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
v___x_514_ = lean_unsigned_to_nat(1u);
v___x_515_ = lean_nat_add(v_size_489_, v___x_514_);
v___x_516_ = lean_nat_dec_lt(v___x_515_, v___x_501_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
lean_dec(v___x_515_);
lean_inc_ref(v_inst_461_);
lean_inc_ref(v_inst_460_);
v___x_517_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_460_, v_inst_461_, v_m_462_);
v___y_473_ = v___x_517_;
goto v___jp_472_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v___x_522_; 
v___x_518_ = lean_unsigned_to_nat(4u);
v___x_519_ = lean_nat_mul(v___x_515_, v___x_518_);
lean_dec(v___x_515_);
v___x_520_ = lean_unsigned_to_nat(3u);
v___x_521_ = lean_nat_mul(v___x_501_, v___x_520_);
v___x_522_ = lean_nat_dec_le(v___x_519_, v___x_521_);
lean_dec(v___x_521_);
lean_dec(v___x_519_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; 
lean_inc_ref(v_inst_461_);
lean_inc_ref(v_inst_460_);
v___x_523_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_460_, v_inst_461_, v_m_462_);
v___y_473_ = v___x_523_;
goto v___jp_472_;
}
else
{
v___y_473_ = v_m_462_;
goto v___jp_472_;
}
}
}
}
}
v___jp_465_:
{
lean_object* v_size_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v_size_468_ = lean_ctor_get(v___y_466_, 0);
v___x_469_ = lean_unsigned_to_nat(1u);
v___x_470_ = lean_nat_add(v_size_468_, v___x_469_);
v___x_471_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_466_, v___x_470_, v_i_467_, v_a_463_, v_b_464_);
lean_dec(v_i_467_);
return v___x_471_;
}
v___jp_472_:
{
lean_object* v___x_474_; 
lean_inc(v_a_463_);
v___x_474_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_460_, v_inst_461_, v___y_473_, v_a_463_);
switch(lean_obj_tag(v___x_474_))
{
case 0:
{
lean_object* v_index_475_; lean_object* v_size_476_; lean_object* v___x_477_; 
v_index_475_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_index_475_);
lean_dec_ref_known(v___x_474_, 3);
v_size_476_ = lean_ctor_get(v___y_473_, 0);
lean_inc(v_size_476_);
v___x_477_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_473_, v_size_476_, v_index_475_, v_a_463_, v_b_464_);
lean_dec(v_index_475_);
return v___x_477_;
}
case 1:
{
lean_object* v_index_478_; 
v_index_478_ = lean_ctor_get(v___x_474_, 0);
lean_inc(v_index_478_);
lean_dec_ref_known(v___x_474_, 1);
v___y_466_ = v___y_473_;
v_i_467_ = v_index_478_;
goto v___jp_465_;
}
default: 
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_473_, v___x_479_);
if (lean_obj_tag(v___x_480_) == 0)
{
lean_object* v_index_481_; 
v_index_481_ = lean_ctor_get(v___x_480_, 0);
lean_inc(v_index_481_);
lean_dec_ref_known(v___x_480_, 1);
v___y_466_ = v___y_473_;
v_i_467_ = v_index_481_;
goto v___jp_465_;
}
else
{
lean_dec(v_b_464_);
lean_dec(v_a_463_);
return v___y_473_;
}
}
}
}
v___jp_482_:
{
lean_object* v_size_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_size_485_ = lean_ctor_get(v___y_483_, 0);
v___x_486_ = lean_unsigned_to_nat(1u);
v___x_487_ = lean_nat_add(v_size_485_, v___x_486_);
v___x_488_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_483_, v___x_487_, v_i_484_, v_a_463_, v_b_464_);
lean_dec(v_i_484_);
return v___x_488_;
}
v___jp_492_:
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_inc_ref(v_inst_461_);
lean_inc_ref(v_inst_460_);
v___x_493_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_460_, v_inst_461_, v_m_462_);
lean_inc(v_a_463_);
v___x_494_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_460_, v_inst_461_, v___x_493_, v_a_463_);
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
v___x_497_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_493_, v_size_496_, v_index_495_, v_a_463_, v_b_464_);
lean_dec(v_index_495_);
return v___x_497_;
}
case 1:
{
lean_object* v_index_498_; 
v_index_498_ = lean_ctor_get(v___x_494_, 0);
lean_inc(v_index_498_);
lean_dec_ref_known(v___x_494_, 1);
v___y_483_ = v___x_493_;
v_i_484_ = v_index_498_;
goto v___jp_482_;
}
default: 
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_493_, v___x_491_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_index_500_; 
v_index_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_index_500_);
lean_dec_ref_known(v___x_499_, 1);
v___y_483_ = v___x_493_;
v_i_484_ = v_index_500_;
goto v___jp_482_;
}
else
{
lean_dec(v_b_464_);
lean_dec(v_a_463_);
return v___x_493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertIfNew(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_inst_526_, lean_object* v_inst_527_, lean_object* v_m_528_, lean_object* v_a_529_, lean_object* v_b_530_){
_start:
{
lean_object* v___y_532_; lean_object* v_i_533_; lean_object* v___y_539_; lean_object* v___y_549_; lean_object* v_i_550_; lean_object* v_size_555_; lean_object* v_keyArray_556_; lean_object* v___x_557_; lean_object* v___x_567_; uint8_t v___x_568_; 
v_size_555_ = lean_ctor_get(v_m_528_, 0);
v_keyArray_556_ = lean_ctor_get(v_m_528_, 1);
v___x_557_ = lean_unsigned_to_nat(0u);
v___x_567_ = lean_array_get_size(v_keyArray_556_);
v___x_568_ = lean_nat_dec_lt(v___x_557_, v___x_567_);
if (v___x_568_ == 0)
{
lean_dec(v_b_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
return v_m_528_;
}
else
{
lean_object* v___x_569_; 
lean_inc(v_a_529_);
lean_inc_ref(v_inst_527_);
lean_inc_ref(v_inst_526_);
v___x_569_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_526_, v_inst_527_, v_m_528_, v_a_529_);
switch(lean_obj_tag(v___x_569_))
{
case 0:
{
lean_dec_ref_known(v___x_569_, 3);
lean_dec(v_b_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
return v_m_528_;
}
case 1:
{
lean_object* v_index_570_; lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v_index_570_ = lean_ctor_get(v___x_569_, 0);
lean_inc(v_index_570_);
lean_dec_ref_known(v___x_569_, 1);
v___x_571_ = lean_unsigned_to_nat(1u);
v___x_572_ = lean_nat_add(v_size_555_, v___x_571_);
v___x_573_ = lean_nat_dec_lt(v___x_572_, v___x_567_);
if (v___x_573_ == 0)
{
lean_dec(v___x_572_);
lean_dec(v_index_570_);
goto v___jp_558_;
}
else
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_574_ = lean_unsigned_to_nat(4u);
v___x_575_ = lean_nat_mul(v___x_572_, v___x_574_);
v___x_576_ = lean_unsigned_to_nat(3u);
v___x_577_ = lean_nat_mul(v___x_567_, v___x_576_);
v___x_578_ = lean_nat_dec_le(v___x_575_, v___x_577_);
lean_dec(v___x_577_);
lean_dec(v___x_575_);
if (v___x_578_ == 0)
{
lean_dec(v___x_572_);
lean_dec(v_index_570_);
goto v___jp_558_;
}
else
{
lean_object* v___x_579_; 
lean_dec_ref(v_inst_527_);
lean_dec_ref(v_inst_526_);
v___x_579_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_528_, v___x_572_, v_index_570_, v_a_529_, v_b_530_);
lean_dec(v_index_570_);
return v___x_579_;
}
}
}
default: 
{
lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_580_ = lean_unsigned_to_nat(1u);
v___x_581_ = lean_nat_add(v_size_555_, v___x_580_);
v___x_582_ = lean_nat_dec_lt(v___x_581_, v___x_567_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; 
lean_dec(v___x_581_);
lean_inc_ref(v_inst_527_);
lean_inc_ref(v_inst_526_);
v___x_583_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_526_, v_inst_527_, v_m_528_);
v___y_539_ = v___x_583_;
goto v___jp_538_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v___x_584_ = lean_unsigned_to_nat(4u);
v___x_585_ = lean_nat_mul(v___x_581_, v___x_584_);
lean_dec(v___x_581_);
v___x_586_ = lean_unsigned_to_nat(3u);
v___x_587_ = lean_nat_mul(v___x_567_, v___x_586_);
v___x_588_ = lean_nat_dec_le(v___x_585_, v___x_587_);
lean_dec(v___x_587_);
lean_dec(v___x_585_);
if (v___x_588_ == 0)
{
lean_object* v___x_589_; 
lean_inc_ref(v_inst_527_);
lean_inc_ref(v_inst_526_);
v___x_589_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_526_, v_inst_527_, v_m_528_);
v___y_539_ = v___x_589_;
goto v___jp_538_;
}
else
{
v___y_539_ = v_m_528_;
goto v___jp_538_;
}
}
}
}
}
v___jp_531_:
{
lean_object* v_size_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; 
v_size_534_ = lean_ctor_get(v___y_532_, 0);
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_size_534_, v___x_535_);
v___x_537_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_532_, v___x_536_, v_i_533_, v_a_529_, v_b_530_);
lean_dec(v_i_533_);
return v___x_537_;
}
v___jp_538_:
{
lean_object* v___x_540_; 
lean_inc(v_a_529_);
v___x_540_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_526_, v_inst_527_, v___y_539_, v_a_529_);
switch(lean_obj_tag(v___x_540_))
{
case 0:
{
lean_object* v_index_541_; lean_object* v_size_542_; lean_object* v___x_543_; 
v_index_541_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_index_541_);
lean_dec_ref_known(v___x_540_, 3);
v_size_542_ = lean_ctor_get(v___y_539_, 0);
lean_inc(v_size_542_);
v___x_543_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_539_, v_size_542_, v_index_541_, v_a_529_, v_b_530_);
lean_dec(v_index_541_);
return v___x_543_;
}
case 1:
{
lean_object* v_index_544_; 
v_index_544_ = lean_ctor_get(v___x_540_, 0);
lean_inc(v_index_544_);
lean_dec_ref_known(v___x_540_, 1);
v___y_532_ = v___y_539_;
v_i_533_ = v_index_544_;
goto v___jp_531_;
}
default: 
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_539_, v___x_545_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v_index_547_; 
v_index_547_ = lean_ctor_get(v___x_546_, 0);
lean_inc(v_index_547_);
lean_dec_ref_known(v___x_546_, 1);
v___y_532_ = v___y_539_;
v_i_533_ = v_index_547_;
goto v___jp_531_;
}
else
{
lean_dec(v_b_530_);
lean_dec(v_a_529_);
return v___y_539_;
}
}
}
}
v___jp_548_:
{
lean_object* v_size_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v_size_551_ = lean_ctor_get(v___y_549_, 0);
v___x_552_ = lean_unsigned_to_nat(1u);
v___x_553_ = lean_nat_add(v_size_551_, v___x_552_);
v___x_554_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_549_, v___x_553_, v_i_550_, v_a_529_, v_b_530_);
lean_dec(v_i_550_);
return v___x_554_;
}
v___jp_558_:
{
lean_object* v___x_559_; lean_object* v___x_560_; 
lean_inc_ref(v_inst_527_);
lean_inc_ref(v_inst_526_);
v___x_559_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_526_, v_inst_527_, v_m_528_);
lean_inc(v_a_529_);
v___x_560_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_526_, v_inst_527_, v___x_559_, v_a_529_);
switch(lean_obj_tag(v___x_560_))
{
case 0:
{
lean_object* v_index_561_; lean_object* v_size_562_; lean_object* v___x_563_; 
v_index_561_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_index_561_);
lean_dec_ref_known(v___x_560_, 3);
v_size_562_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_size_562_);
v___x_563_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_559_, v_size_562_, v_index_561_, v_a_529_, v_b_530_);
lean_dec(v_index_561_);
return v___x_563_;
}
case 1:
{
lean_object* v_index_564_; 
v_index_564_ = lean_ctor_get(v___x_560_, 0);
lean_inc(v_index_564_);
lean_dec_ref_known(v___x_560_, 1);
v___y_549_ = v___x_559_;
v_i_550_ = v_index_564_;
goto v___jp_548_;
}
default: 
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_559_, v___x_557_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_index_566_; 
v_index_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_index_566_);
lean_dec_ref_known(v___x_565_, 1);
v___y_549_ = v___x_559_;
v_i_550_ = v_index_566_;
goto v___jp_548_;
}
else
{
lean_dec(v_b_530_);
lean_dec(v_a_529_);
return v___x_559_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_590_, lean_object* v_inst_591_, lean_object* v_m_592_, lean_object* v_a_593_, lean_object* v_b_594_){
_start:
{
lean_object* v_size_595_; lean_object* v_keyArray_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_size_595_ = lean_ctor_get(v_m_592_, 0);
v_keyArray_596_ = lean_ctor_get(v_m_592_, 1);
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_array_get_size(v_keyArray_596_);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; lean_object* v___x_601_; 
lean_dec(v_b_594_);
lean_dec(v_a_593_);
lean_dec_ref(v_inst_591_);
lean_dec_ref(v_inst_590_);
v___x_600_ = lean_box(v___x_599_);
v___x_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v_m_592_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; 
lean_inc(v_a_593_);
lean_inc_ref(v_inst_591_);
lean_inc_ref(v_inst_590_);
v___x_602_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_590_, v_inst_591_, v_m_592_, v_a_593_);
switch(lean_obj_tag(v___x_602_))
{
case 0:
{
lean_object* v_index_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
lean_inc(v_size_595_);
lean_dec_ref(v_inst_591_);
lean_dec_ref(v_inst_590_);
v_index_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_index_603_);
lean_dec_ref_known(v___x_602_, 3);
v___x_604_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_592_, v_size_595_, v_index_603_, v_a_593_, v_b_594_);
lean_dec(v_index_603_);
v___x_605_ = lean_box(v___x_599_);
v___x_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
return v___x_606_;
}
case 1:
{
lean_object* v_index_607_; uint8_t v___x_608_; lean_object* v___y_610_; lean_object* v_i_611_; lean_object* v___x_631_; lean_object* v___x_632_; uint8_t v___x_633_; 
v_index_607_ = lean_ctor_get(v___x_602_, 0);
lean_inc(v_index_607_);
lean_dec_ref_known(v___x_602_, 1);
v___x_608_ = 0;
v___x_631_ = lean_unsigned_to_nat(1u);
v___x_632_ = lean_nat_add(v_size_595_, v___x_631_);
v___x_633_ = lean_nat_dec_lt(v___x_632_, v___x_598_);
if (v___x_633_ == 0)
{
lean_dec(v___x_632_);
lean_dec(v_index_607_);
goto v___jp_618_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v___x_634_ = lean_unsigned_to_nat(4u);
v___x_635_ = lean_nat_mul(v___x_632_, v___x_634_);
v___x_636_ = lean_unsigned_to_nat(3u);
v___x_637_ = lean_nat_mul(v___x_598_, v___x_636_);
v___x_638_ = lean_nat_dec_le(v___x_635_, v___x_637_);
lean_dec(v___x_637_);
lean_dec(v___x_635_);
if (v___x_638_ == 0)
{
lean_dec(v___x_632_);
lean_dec(v_index_607_);
goto v___jp_618_;
}
else
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec_ref(v_inst_591_);
lean_dec_ref(v_inst_590_);
v___x_639_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_592_, v___x_632_, v_index_607_, v_a_593_, v_b_594_);
lean_dec(v_index_607_);
v___x_640_ = lean_box(v___x_608_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
return v___x_641_;
}
}
v___jp_609_:
{
lean_object* v_size_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v_size_612_ = lean_ctor_get(v___y_610_, 0);
v___x_613_ = lean_unsigned_to_nat(1u);
v___x_614_ = lean_nat_add(v_size_612_, v___x_613_);
v___x_615_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_610_, v___x_614_, v_i_611_, v_a_593_, v_b_594_);
lean_dec(v_i_611_);
v___x_616_ = lean_box(v___x_608_);
v___x_617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
return v___x_617_;
}
v___jp_618_:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_inc_ref(v_inst_591_);
lean_inc_ref(v_inst_590_);
v___x_619_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_590_, v_inst_591_, v_m_592_);
lean_inc(v_a_593_);
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_590_, v_inst_591_, v___x_619_, v_a_593_);
switch(lean_obj_tag(v___x_620_))
{
case 0:
{
lean_object* v_index_621_; lean_object* v_size_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v_index_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_index_621_);
lean_dec_ref_known(v___x_620_, 3);
v_size_622_ = lean_ctor_get(v___x_619_, 0);
lean_inc(v_size_622_);
v___x_623_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_619_, v_size_622_, v_index_621_, v_a_593_, v_b_594_);
lean_dec(v_index_621_);
v___x_624_ = lean_box(v___x_608_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_624_);
lean_ctor_set(v___x_625_, 1, v___x_623_);
return v___x_625_;
}
case 1:
{
lean_object* v_index_626_; 
v_index_626_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_index_626_);
lean_dec_ref_known(v___x_620_, 1);
v___y_610_ = v___x_619_;
v_i_611_ = v_index_626_;
goto v___jp_609_;
}
default: 
{
lean_object* v___x_627_; 
v___x_627_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_619_, v___x_597_);
if (lean_obj_tag(v___x_627_) == 0)
{
lean_object* v_index_628_; 
v_index_628_ = lean_ctor_get(v___x_627_, 0);
lean_inc(v_index_628_);
lean_dec_ref_known(v___x_627_, 1);
v___y_610_ = v___x_619_;
v_i_611_ = v_index_628_;
goto v___jp_609_;
}
else
{
lean_object* v___x_629_; lean_object* v___x_630_; 
lean_dec(v_b_594_);
lean_dec(v_a_593_);
v___x_629_ = lean_box(v___x_608_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_619_);
return v___x_630_;
}
}
}
}
}
default: 
{
uint8_t v___x_642_; lean_object* v___y_644_; lean_object* v_i_645_; lean_object* v___y_653_; lean_object* v___x_665_; lean_object* v___x_666_; uint8_t v___x_667_; 
v___x_642_ = 0;
v___x_665_ = lean_unsigned_to_nat(1u);
v___x_666_ = lean_nat_add(v_size_595_, v___x_665_);
v___x_667_ = lean_nat_dec_lt(v___x_666_, v___x_598_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec(v___x_666_);
lean_inc_ref(v_inst_591_);
lean_inc_ref(v_inst_590_);
v___x_668_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_590_, v_inst_591_, v_m_592_);
v___y_653_ = v___x_668_;
goto v___jp_652_;
}
else
{
lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v___x_669_ = lean_unsigned_to_nat(4u);
v___x_670_ = lean_nat_mul(v___x_666_, v___x_669_);
lean_dec(v___x_666_);
v___x_671_ = lean_unsigned_to_nat(3u);
v___x_672_ = lean_nat_mul(v___x_598_, v___x_671_);
v___x_673_ = lean_nat_dec_le(v___x_670_, v___x_672_);
lean_dec(v___x_672_);
lean_dec(v___x_670_);
if (v___x_673_ == 0)
{
lean_object* v___x_674_; 
lean_inc_ref(v_inst_591_);
lean_inc_ref(v_inst_590_);
v___x_674_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_590_, v_inst_591_, v_m_592_);
v___y_653_ = v___x_674_;
goto v___jp_652_;
}
else
{
v___y_653_ = v_m_592_;
goto v___jp_652_;
}
}
v___jp_643_:
{
lean_object* v_size_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
v_size_646_ = lean_ctor_get(v___y_644_, 0);
v___x_647_ = lean_unsigned_to_nat(1u);
v___x_648_ = lean_nat_add(v_size_646_, v___x_647_);
v___x_649_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_644_, v___x_648_, v_i_645_, v_a_593_, v_b_594_);
lean_dec(v_i_645_);
v___x_650_ = lean_box(v___x_642_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___x_649_);
return v___x_651_;
}
v___jp_652_:
{
lean_object* v___x_654_; 
lean_inc(v_a_593_);
v___x_654_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_590_, v_inst_591_, v___y_653_, v_a_593_);
switch(lean_obj_tag(v___x_654_))
{
case 0:
{
lean_object* v_index_655_; lean_object* v_size_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_index_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_index_655_);
lean_dec_ref_known(v___x_654_, 3);
v_size_656_ = lean_ctor_get(v___y_653_, 0);
lean_inc(v_size_656_);
v___x_657_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_653_, v_size_656_, v_index_655_, v_a_593_, v_b_594_);
lean_dec(v_index_655_);
v___x_658_ = lean_box(v___x_642_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v___x_657_);
return v___x_659_;
}
case 1:
{
lean_object* v_index_660_; 
v_index_660_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_index_660_);
lean_dec_ref_known(v___x_654_, 1);
v___y_644_ = v___y_653_;
v_i_645_ = v_index_660_;
goto v___jp_643_;
}
default: 
{
lean_object* v___x_661_; 
v___x_661_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_653_, v___x_597_);
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_index_662_; 
v_index_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_index_662_);
lean_dec_ref_known(v___x_661_, 1);
v___y_644_ = v___y_653_;
v_i_645_ = v_index_662_;
goto v___jp_643_;
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec(v_b_594_);
lean_dec(v_a_593_);
v___x_663_ = lean_box(v___x_642_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v___y_653_);
return v___x_664_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_675_, lean_object* v_00_u03b2_676_, lean_object* v_inst_677_, lean_object* v_inst_678_, lean_object* v_m_679_, lean_object* v_a_680_, lean_object* v_b_681_){
_start:
{
lean_object* v_size_682_; lean_object* v_keyArray_683_; lean_object* v___x_684_; lean_object* v___x_685_; uint8_t v___x_686_; 
v_size_682_ = lean_ctor_get(v_m_679_, 0);
v_keyArray_683_ = lean_ctor_get(v_m_679_, 1);
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_array_get_size(v_keyArray_683_);
v___x_686_ = lean_nat_dec_lt(v___x_684_, v___x_685_);
if (v___x_686_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
lean_dec(v_b_681_);
lean_dec(v_a_680_);
lean_dec_ref(v_inst_678_);
lean_dec_ref(v_inst_677_);
v___x_687_ = lean_box(v___x_686_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v_m_679_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; 
lean_inc(v_a_680_);
lean_inc_ref(v_inst_678_);
lean_inc_ref(v_inst_677_);
v___x_689_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_677_, v_inst_678_, v_m_679_, v_a_680_);
switch(lean_obj_tag(v___x_689_))
{
case 0:
{
lean_object* v_index_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
lean_inc(v_size_682_);
lean_dec_ref(v_inst_678_);
lean_dec_ref(v_inst_677_);
v_index_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_index_690_);
lean_dec_ref_known(v___x_689_, 3);
v___x_691_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_679_, v_size_682_, v_index_690_, v_a_680_, v_b_681_);
lean_dec(v_index_690_);
v___x_692_ = lean_box(v___x_686_);
v___x_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
lean_ctor_set(v___x_693_, 1, v___x_691_);
return v___x_693_;
}
case 1:
{
lean_object* v_index_694_; uint8_t v___x_695_; lean_object* v___y_697_; lean_object* v_i_698_; lean_object* v___x_718_; lean_object* v___x_719_; uint8_t v___x_720_; 
v_index_694_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_index_694_);
lean_dec_ref_known(v___x_689_, 1);
v___x_695_ = 0;
v___x_718_ = lean_unsigned_to_nat(1u);
v___x_719_ = lean_nat_add(v_size_682_, v___x_718_);
v___x_720_ = lean_nat_dec_lt(v___x_719_, v___x_685_);
if (v___x_720_ == 0)
{
lean_dec(v___x_719_);
lean_dec(v_index_694_);
goto v___jp_705_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_721_ = lean_unsigned_to_nat(4u);
v___x_722_ = lean_nat_mul(v___x_719_, v___x_721_);
v___x_723_ = lean_unsigned_to_nat(3u);
v___x_724_ = lean_nat_mul(v___x_685_, v___x_723_);
v___x_725_ = lean_nat_dec_le(v___x_722_, v___x_724_);
lean_dec(v___x_724_);
lean_dec(v___x_722_);
if (v___x_725_ == 0)
{
lean_dec(v___x_719_);
lean_dec(v_index_694_);
goto v___jp_705_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
lean_dec_ref(v_inst_678_);
lean_dec_ref(v_inst_677_);
v___x_726_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_679_, v___x_719_, v_index_694_, v_a_680_, v_b_681_);
lean_dec(v_index_694_);
v___x_727_ = lean_box(v___x_695_);
v___x_728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
return v___x_728_;
}
}
v___jp_696_:
{
lean_object* v_size_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v_size_699_ = lean_ctor_get(v___y_697_, 0);
v___x_700_ = lean_unsigned_to_nat(1u);
v___x_701_ = lean_nat_add(v_size_699_, v___x_700_);
v___x_702_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_697_, v___x_701_, v_i_698_, v_a_680_, v_b_681_);
lean_dec(v_i_698_);
v___x_703_ = lean_box(v___x_695_);
v___x_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
lean_ctor_set(v___x_704_, 1, v___x_702_);
return v___x_704_;
}
v___jp_705_:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
lean_inc_ref(v_inst_678_);
lean_inc_ref(v_inst_677_);
v___x_706_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_677_, v_inst_678_, v_m_679_);
lean_inc(v_a_680_);
v___x_707_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_677_, v_inst_678_, v___x_706_, v_a_680_);
switch(lean_obj_tag(v___x_707_))
{
case 0:
{
lean_object* v_index_708_; lean_object* v_size_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v_index_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_index_708_);
lean_dec_ref_known(v___x_707_, 3);
v_size_709_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_size_709_);
v___x_710_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_706_, v_size_709_, v_index_708_, v_a_680_, v_b_681_);
lean_dec(v_index_708_);
v___x_711_ = lean_box(v___x_695_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_711_);
lean_ctor_set(v___x_712_, 1, v___x_710_);
return v___x_712_;
}
case 1:
{
lean_object* v_index_713_; 
v_index_713_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_index_713_);
lean_dec_ref_known(v___x_707_, 1);
v___y_697_ = v___x_706_;
v_i_698_ = v_index_713_;
goto v___jp_696_;
}
default: 
{
lean_object* v___x_714_; 
v___x_714_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_706_, v___x_684_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v_index_715_; 
v_index_715_ = lean_ctor_get(v___x_714_, 0);
lean_inc(v_index_715_);
lean_dec_ref_known(v___x_714_, 1);
v___y_697_ = v___x_706_;
v_i_698_ = v_index_715_;
goto v___jp_696_;
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; 
lean_dec(v_b_681_);
lean_dec(v_a_680_);
v___x_716_ = lean_box(v___x_695_);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
lean_ctor_set(v___x_717_, 1, v___x_706_);
return v___x_717_;
}
}
}
}
}
default: 
{
uint8_t v___x_729_; lean_object* v___y_731_; lean_object* v_i_732_; lean_object* v___y_740_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_729_ = 0;
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_add(v_size_682_, v___x_752_);
v___x_754_ = lean_nat_dec_lt(v___x_753_, v___x_685_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; 
lean_dec(v___x_753_);
lean_inc_ref(v_inst_678_);
lean_inc_ref(v_inst_677_);
v___x_755_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_677_, v_inst_678_, v_m_679_);
v___y_740_ = v___x_755_;
goto v___jp_739_;
}
else
{
lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_756_ = lean_unsigned_to_nat(4u);
v___x_757_ = lean_nat_mul(v___x_753_, v___x_756_);
lean_dec(v___x_753_);
v___x_758_ = lean_unsigned_to_nat(3u);
v___x_759_ = lean_nat_mul(v___x_685_, v___x_758_);
v___x_760_ = lean_nat_dec_le(v___x_757_, v___x_759_);
lean_dec(v___x_759_);
lean_dec(v___x_757_);
if (v___x_760_ == 0)
{
lean_object* v___x_761_; 
lean_inc_ref(v_inst_678_);
lean_inc_ref(v_inst_677_);
v___x_761_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_677_, v_inst_678_, v_m_679_);
v___y_740_ = v___x_761_;
goto v___jp_739_;
}
else
{
v___y_740_ = v_m_679_;
goto v___jp_739_;
}
}
v___jp_730_:
{
lean_object* v_size_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v_size_733_ = lean_ctor_get(v___y_731_, 0);
v___x_734_ = lean_unsigned_to_nat(1u);
v___x_735_ = lean_nat_add(v_size_733_, v___x_734_);
v___x_736_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_731_, v___x_735_, v_i_732_, v_a_680_, v_b_681_);
lean_dec(v_i_732_);
v___x_737_ = lean_box(v___x_729_);
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_737_);
lean_ctor_set(v___x_738_, 1, v___x_736_);
return v___x_738_;
}
v___jp_739_:
{
lean_object* v___x_741_; 
lean_inc(v_a_680_);
v___x_741_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_677_, v_inst_678_, v___y_740_, v_a_680_);
switch(lean_obj_tag(v___x_741_))
{
case 0:
{
lean_object* v_index_742_; lean_object* v_size_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v_index_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_index_742_);
lean_dec_ref_known(v___x_741_, 3);
v_size_743_ = lean_ctor_get(v___y_740_, 0);
lean_inc(v_size_743_);
v___x_744_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_740_, v_size_743_, v_index_742_, v_a_680_, v_b_681_);
lean_dec(v_index_742_);
v___x_745_ = lean_box(v___x_729_);
v___x_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v___x_744_);
return v___x_746_;
}
case 1:
{
lean_object* v_index_747_; 
v_index_747_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_index_747_);
lean_dec_ref_known(v___x_741_, 1);
v___y_731_ = v___y_740_;
v_i_732_ = v_index_747_;
goto v___jp_730_;
}
default: 
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_740_, v___x_684_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_object* v_index_749_; 
v_index_749_ = lean_ctor_get(v___x_748_, 0);
lean_inc(v_index_749_);
lean_dec_ref_known(v___x_748_, 1);
v___y_731_ = v___y_740_;
v_i_732_ = v_index_749_;
goto v___jp_730_;
}
else
{
lean_object* v___x_750_; lean_object* v___x_751_; 
lean_dec(v_b_681_);
lean_dec(v_a_680_);
v___x_750_ = lean_box(v___x_729_);
v___x_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_751_, 0, v___x_750_);
lean_ctor_set(v___x_751_, 1, v___y_740_);
return v___x_751_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_762_, lean_object* v_inst_763_, lean_object* v_m_764_, lean_object* v_a_765_, lean_object* v_b_766_){
_start:
{
lean_object* v_size_767_; lean_object* v_keyArray_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_size_767_ = lean_ctor_get(v_m_764_, 0);
v_keyArray_768_ = lean_ctor_get(v_m_764_, 1);
v___x_769_ = lean_unsigned_to_nat(0u);
v___x_770_ = lean_array_get_size(v_keyArray_768_);
v___x_771_ = lean_nat_dec_lt(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_object* v___x_772_; lean_object* v___x_773_; 
lean_dec(v_b_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_inst_763_);
lean_dec_ref(v_inst_762_);
v___x_772_ = lean_box(v___x_771_);
v___x_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_773_, 0, v___x_772_);
lean_ctor_set(v___x_773_, 1, v_m_764_);
return v___x_773_;
}
else
{
lean_object* v___x_774_; 
lean_inc(v_a_765_);
lean_inc_ref(v_inst_763_);
lean_inc_ref(v_inst_762_);
v___x_774_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_762_, v_inst_763_, v_m_764_, v_a_765_);
switch(lean_obj_tag(v___x_774_))
{
case 0:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
lean_dec_ref_known(v___x_774_, 3);
lean_dec(v_b_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_inst_763_);
lean_dec_ref(v_inst_762_);
v___x_775_ = lean_box(v___x_771_);
v___x_776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_775_);
lean_ctor_set(v___x_776_, 1, v_m_764_);
return v___x_776_;
}
case 1:
{
lean_object* v_index_777_; uint8_t v___x_778_; lean_object* v___y_780_; lean_object* v_i_781_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_index_777_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_index_777_);
lean_dec_ref_known(v___x_774_, 1);
v___x_778_ = 0;
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_size_767_, v___x_801_);
v___x_803_ = lean_nat_dec_lt(v___x_802_, v___x_770_);
if (v___x_803_ == 0)
{
lean_dec(v___x_802_);
lean_dec(v_index_777_);
goto v___jp_788_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_804_ = lean_unsigned_to_nat(4u);
v___x_805_ = lean_nat_mul(v___x_802_, v___x_804_);
v___x_806_ = lean_unsigned_to_nat(3u);
v___x_807_ = lean_nat_mul(v___x_770_, v___x_806_);
v___x_808_ = lean_nat_dec_le(v___x_805_, v___x_807_);
lean_dec(v___x_807_);
lean_dec(v___x_805_);
if (v___x_808_ == 0)
{
lean_dec(v___x_802_);
lean_dec(v_index_777_);
goto v___jp_788_;
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec_ref(v_inst_763_);
lean_dec_ref(v_inst_762_);
v___x_809_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_764_, v___x_802_, v_index_777_, v_a_765_, v_b_766_);
lean_dec(v_index_777_);
v___x_810_ = lean_box(v___x_778_);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v___x_809_);
return v___x_811_;
}
}
v___jp_779_:
{
lean_object* v_size_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
v_size_782_ = lean_ctor_get(v___y_780_, 0);
v___x_783_ = lean_unsigned_to_nat(1u);
v___x_784_ = lean_nat_add(v_size_782_, v___x_783_);
v___x_785_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_780_, v___x_784_, v_i_781_, v_a_765_, v_b_766_);
lean_dec(v_i_781_);
v___x_786_ = lean_box(v___x_778_);
v___x_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_786_);
lean_ctor_set(v___x_787_, 1, v___x_785_);
return v___x_787_;
}
v___jp_788_:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
lean_inc_ref(v_inst_763_);
lean_inc_ref(v_inst_762_);
v___x_789_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_762_, v_inst_763_, v_m_764_);
lean_inc(v_a_765_);
v___x_790_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_762_, v_inst_763_, v___x_789_, v_a_765_);
switch(lean_obj_tag(v___x_790_))
{
case 0:
{
lean_object* v_index_791_; lean_object* v_size_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_index_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_index_791_);
lean_dec_ref_known(v___x_790_, 3);
v_size_792_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_size_792_);
v___x_793_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_789_, v_size_792_, v_index_791_, v_a_765_, v_b_766_);
lean_dec(v_index_791_);
v___x_794_ = lean_box(v___x_778_);
v___x_795_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_795_, 0, v___x_794_);
lean_ctor_set(v___x_795_, 1, v___x_793_);
return v___x_795_;
}
case 1:
{
lean_object* v_index_796_; 
v_index_796_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_index_796_);
lean_dec_ref_known(v___x_790_, 1);
v___y_780_ = v___x_789_;
v_i_781_ = v_index_796_;
goto v___jp_779_;
}
default: 
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_789_, v___x_769_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_index_798_; 
v_index_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_index_798_);
lean_dec_ref_known(v___x_797_, 1);
v___y_780_ = v___x_789_;
v_i_781_ = v_index_798_;
goto v___jp_779_;
}
else
{
lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v_b_766_);
lean_dec(v_a_765_);
v___x_799_ = lean_box(v___x_778_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
lean_ctor_set(v___x_800_, 1, v___x_789_);
return v___x_800_;
}
}
}
}
}
default: 
{
uint8_t v___x_812_; lean_object* v___y_814_; lean_object* v_i_815_; lean_object* v___y_823_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_812_ = 0;
v___x_835_ = lean_unsigned_to_nat(1u);
v___x_836_ = lean_nat_add(v_size_767_, v___x_835_);
v___x_837_ = lean_nat_dec_lt(v___x_836_, v___x_770_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; 
lean_dec(v___x_836_);
lean_inc_ref(v_inst_763_);
lean_inc_ref(v_inst_762_);
v___x_838_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_762_, v_inst_763_, v_m_764_);
v___y_823_ = v___x_838_;
goto v___jp_822_;
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_839_ = lean_unsigned_to_nat(4u);
v___x_840_ = lean_nat_mul(v___x_836_, v___x_839_);
lean_dec(v___x_836_);
v___x_841_ = lean_unsigned_to_nat(3u);
v___x_842_ = lean_nat_mul(v___x_770_, v___x_841_);
v___x_843_ = lean_nat_dec_le(v___x_840_, v___x_842_);
lean_dec(v___x_842_);
lean_dec(v___x_840_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_inc_ref(v_inst_763_);
lean_inc_ref(v_inst_762_);
v___x_844_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_762_, v_inst_763_, v_m_764_);
v___y_823_ = v___x_844_;
goto v___jp_822_;
}
else
{
v___y_823_ = v_m_764_;
goto v___jp_822_;
}
}
v___jp_813_:
{
lean_object* v_size_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v_size_816_ = lean_ctor_get(v___y_814_, 0);
v___x_817_ = lean_unsigned_to_nat(1u);
v___x_818_ = lean_nat_add(v_size_816_, v___x_817_);
v___x_819_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_814_, v___x_818_, v_i_815_, v_a_765_, v_b_766_);
lean_dec(v_i_815_);
v___x_820_ = lean_box(v___x_812_);
v___x_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v___x_819_);
return v___x_821_;
}
v___jp_822_:
{
lean_object* v___x_824_; 
lean_inc(v_a_765_);
v___x_824_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_762_, v_inst_763_, v___y_823_, v_a_765_);
switch(lean_obj_tag(v___x_824_))
{
case 0:
{
lean_object* v_index_825_; lean_object* v_size_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_index_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_index_825_);
lean_dec_ref_known(v___x_824_, 3);
v_size_826_ = lean_ctor_get(v___y_823_, 0);
lean_inc(v_size_826_);
v___x_827_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_823_, v_size_826_, v_index_825_, v_a_765_, v_b_766_);
lean_dec(v_index_825_);
v___x_828_ = lean_box(v___x_812_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_828_);
lean_ctor_set(v___x_829_, 1, v___x_827_);
return v___x_829_;
}
case 1:
{
lean_object* v_index_830_; 
v_index_830_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_index_830_);
lean_dec_ref_known(v___x_824_, 1);
v___y_814_ = v___y_823_;
v_i_815_ = v_index_830_;
goto v___jp_813_;
}
default: 
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_823_, v___x_769_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_index_832_; 
v_index_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_index_832_);
lean_dec_ref_known(v___x_831_, 1);
v___y_814_ = v___y_823_;
v_i_815_ = v_index_832_;
goto v___jp_813_;
}
else
{
lean_object* v___x_833_; lean_object* v___x_834_; 
lean_dec(v_b_766_);
lean_dec(v_a_765_);
v___x_833_ = lean_box(v___x_812_);
v___x_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_834_, 0, v___x_833_);
lean_ctor_set(v___x_834_, 1, v___y_823_);
return v___x_834_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_845_, lean_object* v_00_u03b2_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_m_849_, lean_object* v_a_850_, lean_object* v_b_851_){
_start:
{
lean_object* v_size_852_; lean_object* v_keyArray_853_; lean_object* v___x_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_size_852_ = lean_ctor_get(v_m_849_, 0);
v_keyArray_853_ = lean_ctor_get(v_m_849_, 1);
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_array_get_size(v_keyArray_853_);
v___x_856_ = lean_nat_dec_lt(v___x_854_, v___x_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; lean_object* v___x_858_; 
lean_dec(v_b_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_inst_848_);
lean_dec_ref(v_inst_847_);
v___x_857_ = lean_box(v___x_856_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v_m_849_);
return v___x_858_;
}
else
{
lean_object* v___x_859_; 
lean_inc(v_a_850_);
lean_inc_ref(v_inst_848_);
lean_inc_ref(v_inst_847_);
v___x_859_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_847_, v_inst_848_, v_m_849_, v_a_850_);
switch(lean_obj_tag(v___x_859_))
{
case 0:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec_ref_known(v___x_859_, 3);
lean_dec(v_b_851_);
lean_dec(v_a_850_);
lean_dec_ref(v_inst_848_);
lean_dec_ref(v_inst_847_);
v___x_860_ = lean_box(v___x_856_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v_m_849_);
return v___x_861_;
}
case 1:
{
lean_object* v_index_862_; uint8_t v___x_863_; lean_object* v___y_865_; lean_object* v_i_866_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v_index_862_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_index_862_);
lean_dec_ref_known(v___x_859_, 1);
v___x_863_ = 0;
v___x_886_ = lean_unsigned_to_nat(1u);
v___x_887_ = lean_nat_add(v_size_852_, v___x_886_);
v___x_888_ = lean_nat_dec_lt(v___x_887_, v___x_855_);
if (v___x_888_ == 0)
{
lean_dec(v___x_887_);
lean_dec(v_index_862_);
goto v___jp_873_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; uint8_t v___x_893_; 
v___x_889_ = lean_unsigned_to_nat(4u);
v___x_890_ = lean_nat_mul(v___x_887_, v___x_889_);
v___x_891_ = lean_unsigned_to_nat(3u);
v___x_892_ = lean_nat_mul(v___x_855_, v___x_891_);
v___x_893_ = lean_nat_dec_le(v___x_890_, v___x_892_);
lean_dec(v___x_892_);
lean_dec(v___x_890_);
if (v___x_893_ == 0)
{
lean_dec(v___x_887_);
lean_dec(v_index_862_);
goto v___jp_873_;
}
else
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
lean_dec_ref(v_inst_848_);
lean_dec_ref(v_inst_847_);
v___x_894_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_849_, v___x_887_, v_index_862_, v_a_850_, v_b_851_);
lean_dec(v_index_862_);
v___x_895_ = lean_box(v___x_863_);
v___x_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
lean_ctor_set(v___x_896_, 1, v___x_894_);
return v___x_896_;
}
}
v___jp_864_:
{
lean_object* v_size_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
v_size_867_ = lean_ctor_get(v___y_865_, 0);
v___x_868_ = lean_unsigned_to_nat(1u);
v___x_869_ = lean_nat_add(v_size_867_, v___x_868_);
v___x_870_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_865_, v___x_869_, v_i_866_, v_a_850_, v_b_851_);
lean_dec(v_i_866_);
v___x_871_ = lean_box(v___x_863_);
v___x_872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v___x_870_);
return v___x_872_;
}
v___jp_873_:
{
lean_object* v___x_874_; lean_object* v___x_875_; 
lean_inc_ref(v_inst_848_);
lean_inc_ref(v_inst_847_);
v___x_874_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_847_, v_inst_848_, v_m_849_);
lean_inc(v_a_850_);
v___x_875_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_847_, v_inst_848_, v___x_874_, v_a_850_);
switch(lean_obj_tag(v___x_875_))
{
case 0:
{
lean_object* v_index_876_; lean_object* v_size_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; 
v_index_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_index_876_);
lean_dec_ref_known(v___x_875_, 3);
v_size_877_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_size_877_);
v___x_878_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_874_, v_size_877_, v_index_876_, v_a_850_, v_b_851_);
lean_dec(v_index_876_);
v___x_879_ = lean_box(v___x_863_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_879_);
lean_ctor_set(v___x_880_, 1, v___x_878_);
return v___x_880_;
}
case 1:
{
lean_object* v_index_881_; 
v_index_881_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_index_881_);
lean_dec_ref_known(v___x_875_, 1);
v___y_865_ = v___x_874_;
v_i_866_ = v_index_881_;
goto v___jp_864_;
}
default: 
{
lean_object* v___x_882_; 
v___x_882_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_874_, v___x_854_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_index_883_; 
v_index_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_index_883_);
lean_dec_ref_known(v___x_882_, 1);
v___y_865_ = v___x_874_;
v_i_866_ = v_index_883_;
goto v___jp_864_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec(v_b_851_);
lean_dec(v_a_850_);
v___x_884_ = lean_box(v___x_863_);
v___x_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
lean_ctor_set(v___x_885_, 1, v___x_874_);
return v___x_885_;
}
}
}
}
}
default: 
{
uint8_t v___x_897_; lean_object* v___y_899_; lean_object* v_i_900_; lean_object* v___y_908_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v___x_897_ = 0;
v___x_920_ = lean_unsigned_to_nat(1u);
v___x_921_ = lean_nat_add(v_size_852_, v___x_920_);
v___x_922_ = lean_nat_dec_lt(v___x_921_, v___x_855_);
if (v___x_922_ == 0)
{
lean_object* v___x_923_; 
lean_dec(v___x_921_);
lean_inc_ref(v_inst_848_);
lean_inc_ref(v_inst_847_);
v___x_923_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_847_, v_inst_848_, v_m_849_);
v___y_908_ = v___x_923_;
goto v___jp_907_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v___x_924_ = lean_unsigned_to_nat(4u);
v___x_925_ = lean_nat_mul(v___x_921_, v___x_924_);
lean_dec(v___x_921_);
v___x_926_ = lean_unsigned_to_nat(3u);
v___x_927_ = lean_nat_mul(v___x_855_, v___x_926_);
v___x_928_ = lean_nat_dec_le(v___x_925_, v___x_927_);
lean_dec(v___x_927_);
lean_dec(v___x_925_);
if (v___x_928_ == 0)
{
lean_object* v___x_929_; 
lean_inc_ref(v_inst_848_);
lean_inc_ref(v_inst_847_);
v___x_929_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_847_, v_inst_848_, v_m_849_);
v___y_908_ = v___x_929_;
goto v___jp_907_;
}
else
{
v___y_908_ = v_m_849_;
goto v___jp_907_;
}
}
v___jp_898_:
{
lean_object* v_size_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_size_901_ = lean_ctor_get(v___y_899_, 0);
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_add(v_size_901_, v___x_902_);
v___x_904_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_899_, v___x_903_, v_i_900_, v_a_850_, v_b_851_);
lean_dec(v_i_900_);
v___x_905_ = lean_box(v___x_897_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v___x_904_);
return v___x_906_;
}
v___jp_907_:
{
lean_object* v___x_909_; 
lean_inc(v_a_850_);
v___x_909_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_847_, v_inst_848_, v___y_908_, v_a_850_);
switch(lean_obj_tag(v___x_909_))
{
case 0:
{
lean_object* v_index_910_; lean_object* v_size_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v_index_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_index_910_);
lean_dec_ref_known(v___x_909_, 3);
v_size_911_ = lean_ctor_get(v___y_908_, 0);
lean_inc(v_size_911_);
v___x_912_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_908_, v_size_911_, v_index_910_, v_a_850_, v_b_851_);
lean_dec(v_index_910_);
v___x_913_ = lean_box(v___x_897_);
v___x_914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
lean_ctor_set(v___x_914_, 1, v___x_912_);
return v___x_914_;
}
case 1:
{
lean_object* v_index_915_; 
v_index_915_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_index_915_);
lean_dec_ref_known(v___x_909_, 1);
v___y_899_ = v___y_908_;
v_i_900_ = v_index_915_;
goto v___jp_898_;
}
default: 
{
lean_object* v___x_916_; 
v___x_916_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_908_, v___x_854_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_index_917_; 
v_index_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_index_917_);
lean_dec_ref_known(v___x_916_, 1);
v___y_899_ = v___y_908_;
v_i_900_ = v_index_917_;
goto v___jp_898_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec(v_b_851_);
lean_dec(v_a_850_);
v___x_918_ = lean_box(v___x_897_);
v___x_919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
lean_ctor_set(v___x_919_, 1, v___y_908_);
return v___x_919_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_m_932_, lean_object* v_a_933_, lean_object* v_b_934_){
_start:
{
lean_object* v_size_935_; lean_object* v_keyArray_936_; lean_object* v___x_937_; lean_object* v___x_938_; uint8_t v___x_939_; 
v_size_935_ = lean_ctor_get(v_m_932_, 0);
v_keyArray_936_ = lean_ctor_get(v_m_932_, 1);
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_array_get_size(v_keyArray_936_);
v___x_939_ = lean_nat_dec_lt(v___x_937_, v___x_938_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_941_; 
lean_dec(v_b_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_inst_931_);
lean_dec_ref(v_inst_930_);
v___x_940_ = lean_box(0);
v___x_941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_940_);
lean_ctor_set(v___x_941_, 1, v_m_932_);
return v___x_941_;
}
else
{
lean_object* v___x_942_; 
lean_inc(v_a_933_);
lean_inc_ref(v_inst_931_);
lean_inc_ref(v_inst_930_);
v___x_942_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_930_, v_inst_931_, v_m_932_, v_a_933_);
switch(lean_obj_tag(v___x_942_))
{
case 0:
{
lean_object* v_value_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_b_934_);
lean_dec(v_a_933_);
lean_dec_ref(v_inst_931_);
lean_dec_ref(v_inst_930_);
v_value_943_ = lean_ctor_get(v___x_942_, 2);
lean_inc(v_value_943_);
lean_dec_ref_known(v___x_942_, 3);
v___x_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_944_, 0, v_value_943_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v_m_932_);
return v___x_945_;
}
case 1:
{
lean_object* v_index_946_; lean_object* v___x_947_; lean_object* v___y_949_; lean_object* v_i_950_; lean_object* v___x_967_; lean_object* v___x_968_; uint8_t v___x_969_; 
v_index_946_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_index_946_);
lean_dec_ref_known(v___x_942_, 1);
v___x_947_ = lean_box(0);
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_add(v_size_935_, v___x_967_);
v___x_969_ = lean_nat_dec_lt(v___x_968_, v___x_938_);
if (v___x_969_ == 0)
{
lean_dec(v___x_968_);
lean_dec(v_index_946_);
goto v___jp_956_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; 
v___x_970_ = lean_unsigned_to_nat(4u);
v___x_971_ = lean_nat_mul(v___x_968_, v___x_970_);
v___x_972_ = lean_unsigned_to_nat(3u);
v___x_973_ = lean_nat_mul(v___x_938_, v___x_972_);
v___x_974_ = lean_nat_dec_le(v___x_971_, v___x_973_);
lean_dec(v___x_973_);
lean_dec(v___x_971_);
if (v___x_974_ == 0)
{
lean_dec(v___x_968_);
lean_dec(v_index_946_);
goto v___jp_956_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec_ref(v_inst_931_);
lean_dec_ref(v_inst_930_);
v___x_975_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_932_, v___x_968_, v_index_946_, v_a_933_, v_b_934_);
lean_dec(v_index_946_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_947_);
lean_ctor_set(v___x_976_, 1, v___x_975_);
return v___x_976_;
}
}
v___jp_948_:
{
lean_object* v_size_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; 
v_size_951_ = lean_ctor_get(v___y_949_, 0);
v___x_952_ = lean_unsigned_to_nat(1u);
v___x_953_ = lean_nat_add(v_size_951_, v___x_952_);
v___x_954_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_949_, v___x_953_, v_i_950_, v_a_933_, v_b_934_);
lean_dec(v_i_950_);
v___x_955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_947_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
return v___x_955_;
}
v___jp_956_:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
lean_inc_ref(v_inst_931_);
lean_inc_ref(v_inst_930_);
v___x_957_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_930_, v_inst_931_, v_m_932_);
lean_inc(v_a_933_);
v___x_958_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_930_, v_inst_931_, v___x_957_, v_a_933_);
switch(lean_obj_tag(v___x_958_))
{
case 0:
{
lean_object* v_index_959_; lean_object* v_size_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
v_index_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_index_959_);
lean_dec_ref_known(v___x_958_, 3);
v_size_960_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_size_960_);
v___x_961_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_957_, v_size_960_, v_index_959_, v_a_933_, v_b_934_);
lean_dec(v_index_959_);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_947_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
return v___x_962_;
}
case 1:
{
lean_object* v_index_963_; 
v_index_963_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_index_963_);
lean_dec_ref_known(v___x_958_, 1);
v___y_949_ = v___x_957_;
v_i_950_ = v_index_963_;
goto v___jp_948_;
}
default: 
{
lean_object* v___x_964_; 
v___x_964_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_957_, v___x_937_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_object* v_index_965_; 
v_index_965_ = lean_ctor_get(v___x_964_, 0);
lean_inc(v_index_965_);
lean_dec_ref_known(v___x_964_, 1);
v___y_949_ = v___x_957_;
v_i_950_ = v_index_965_;
goto v___jp_948_;
}
else
{
lean_object* v___x_966_; 
lean_dec(v_b_934_);
lean_dec(v_a_933_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_947_);
lean_ctor_set(v___x_966_, 1, v___x_957_);
return v___x_966_;
}
}
}
}
}
default: 
{
lean_object* v___x_977_; lean_object* v___y_979_; lean_object* v_i_980_; lean_object* v___y_987_; lean_object* v___x_997_; lean_object* v___x_998_; uint8_t v___x_999_; 
v___x_977_ = lean_box(0);
v___x_997_ = lean_unsigned_to_nat(1u);
v___x_998_ = lean_nat_add(v_size_935_, v___x_997_);
v___x_999_ = lean_nat_dec_lt(v___x_998_, v___x_938_);
if (v___x_999_ == 0)
{
lean_object* v___x_1000_; 
lean_dec(v___x_998_);
lean_inc_ref(v_inst_931_);
lean_inc_ref(v_inst_930_);
v___x_1000_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_930_, v_inst_931_, v_m_932_);
v___y_987_ = v___x_1000_;
goto v___jp_986_;
}
else
{
lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; 
v___x_1001_ = lean_unsigned_to_nat(4u);
v___x_1002_ = lean_nat_mul(v___x_998_, v___x_1001_);
lean_dec(v___x_998_);
v___x_1003_ = lean_unsigned_to_nat(3u);
v___x_1004_ = lean_nat_mul(v___x_938_, v___x_1003_);
v___x_1005_ = lean_nat_dec_le(v___x_1002_, v___x_1004_);
lean_dec(v___x_1004_);
lean_dec(v___x_1002_);
if (v___x_1005_ == 0)
{
lean_object* v___x_1006_; 
lean_inc_ref(v_inst_931_);
lean_inc_ref(v_inst_930_);
v___x_1006_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_930_, v_inst_931_, v_m_932_);
v___y_987_ = v___x_1006_;
goto v___jp_986_;
}
else
{
v___y_987_ = v_m_932_;
goto v___jp_986_;
}
}
v___jp_978_:
{
lean_object* v_size_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_size_981_ = lean_ctor_get(v___y_979_, 0);
v___x_982_ = lean_unsigned_to_nat(1u);
v___x_983_ = lean_nat_add(v_size_981_, v___x_982_);
v___x_984_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_979_, v___x_983_, v_i_980_, v_a_933_, v_b_934_);
lean_dec(v_i_980_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_977_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
return v___x_985_;
}
v___jp_986_:
{
lean_object* v___x_988_; 
lean_inc(v_a_933_);
v___x_988_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_930_, v_inst_931_, v___y_987_, v_a_933_);
switch(lean_obj_tag(v___x_988_))
{
case 0:
{
lean_object* v_index_989_; lean_object* v_size_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_index_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_index_989_);
lean_dec_ref_known(v___x_988_, 3);
v_size_990_ = lean_ctor_get(v___y_987_, 0);
lean_inc(v_size_990_);
v___x_991_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_987_, v_size_990_, v_index_989_, v_a_933_, v_b_934_);
lean_dec(v_index_989_);
v___x_992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_992_, 0, v___x_977_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
return v___x_992_;
}
case 1:
{
lean_object* v_index_993_; 
v_index_993_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_index_993_);
lean_dec_ref_known(v___x_988_, 1);
v___y_979_ = v___y_987_;
v_i_980_ = v_index_993_;
goto v___jp_978_;
}
default: 
{
lean_object* v___x_994_; 
v___x_994_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_987_, v___x_937_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_index_995_; 
v_index_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_index_995_);
lean_dec_ref_known(v___x_994_, 1);
v___y_979_ = v___y_987_;
v_i_980_ = v_index_995_;
goto v___jp_978_;
}
else
{
lean_object* v___x_996_; 
lean_dec(v_b_934_);
lean_dec(v_a_933_);
v___x_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_977_);
lean_ctor_set(v___x_996_, 1, v___y_987_);
return v___x_996_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1007_, lean_object* v_00_u03b2_1008_, lean_object* v_inst_1009_, lean_object* v_inst_1010_, lean_object* v_m_1011_, lean_object* v_a_1012_, lean_object* v_b_1013_){
_start:
{
lean_object* v_size_1014_; lean_object* v_keyArray_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; uint8_t v___x_1018_; 
v_size_1014_ = lean_ctor_get(v_m_1011_, 0);
v_keyArray_1015_ = lean_ctor_get(v_m_1011_, 1);
v___x_1016_ = lean_unsigned_to_nat(0u);
v___x_1017_ = lean_array_get_size(v_keyArray_1015_);
v___x_1018_ = lean_nat_dec_lt(v___x_1016_, v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v_b_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_inst_1010_);
lean_dec_ref(v_inst_1009_);
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_m_1011_);
return v___x_1020_;
}
else
{
lean_object* v___x_1021_; 
lean_inc(v_a_1012_);
lean_inc_ref(v_inst_1010_);
lean_inc_ref(v_inst_1009_);
v___x_1021_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1009_, v_inst_1010_, v_m_1011_, v_a_1012_);
switch(lean_obj_tag(v___x_1021_))
{
case 0:
{
lean_object* v_value_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; 
lean_dec(v_b_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_inst_1010_);
lean_dec_ref(v_inst_1009_);
v_value_1022_ = lean_ctor_get(v___x_1021_, 2);
lean_inc(v_value_1022_);
lean_dec_ref_known(v___x_1021_, 3);
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v_value_1022_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_m_1011_);
return v___x_1024_;
}
case 1:
{
lean_object* v_index_1025_; lean_object* v___x_1026_; lean_object* v___y_1028_; lean_object* v_i_1029_; lean_object* v___x_1046_; lean_object* v___x_1047_; uint8_t v___x_1048_; 
v_index_1025_ = lean_ctor_get(v___x_1021_, 0);
lean_inc(v_index_1025_);
lean_dec_ref_known(v___x_1021_, 1);
v___x_1026_ = lean_box(0);
v___x_1046_ = lean_unsigned_to_nat(1u);
v___x_1047_ = lean_nat_add(v_size_1014_, v___x_1046_);
v___x_1048_ = lean_nat_dec_lt(v___x_1047_, v___x_1017_);
if (v___x_1048_ == 0)
{
lean_dec(v___x_1047_);
lean_dec(v_index_1025_);
goto v___jp_1035_;
}
else
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; uint8_t v___x_1053_; 
v___x_1049_ = lean_unsigned_to_nat(4u);
v___x_1050_ = lean_nat_mul(v___x_1047_, v___x_1049_);
v___x_1051_ = lean_unsigned_to_nat(3u);
v___x_1052_ = lean_nat_mul(v___x_1017_, v___x_1051_);
v___x_1053_ = lean_nat_dec_le(v___x_1050_, v___x_1052_);
lean_dec(v___x_1052_);
lean_dec(v___x_1050_);
if (v___x_1053_ == 0)
{
lean_dec(v___x_1047_);
lean_dec(v_index_1025_);
goto v___jp_1035_;
}
else
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref(v_inst_1010_);
lean_dec_ref(v_inst_1009_);
v___x_1054_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1011_, v___x_1047_, v_index_1025_, v_a_1012_, v_b_1013_);
lean_dec(v_index_1025_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1026_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
return v___x_1055_;
}
}
v___jp_1027_:
{
lean_object* v_size_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v_size_1030_ = lean_ctor_get(v___y_1028_, 0);
v___x_1031_ = lean_unsigned_to_nat(1u);
v___x_1032_ = lean_nat_add(v_size_1030_, v___x_1031_);
v___x_1033_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1028_, v___x_1032_, v_i_1029_, v_a_1012_, v_b_1013_);
lean_dec(v_i_1029_);
v___x_1034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1026_);
lean_ctor_set(v___x_1034_, 1, v___x_1033_);
return v___x_1034_;
}
v___jp_1035_:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
lean_inc_ref(v_inst_1010_);
lean_inc_ref(v_inst_1009_);
v___x_1036_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1009_, v_inst_1010_, v_m_1011_);
lean_inc(v_a_1012_);
v___x_1037_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1009_, v_inst_1010_, v___x_1036_, v_a_1012_);
switch(lean_obj_tag(v___x_1037_))
{
case 0:
{
lean_object* v_index_1038_; lean_object* v_size_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v_index_1038_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_index_1038_);
lean_dec_ref_known(v___x_1037_, 3);
v_size_1039_ = lean_ctor_get(v___x_1036_, 0);
lean_inc(v_size_1039_);
v___x_1040_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1036_, v_size_1039_, v_index_1038_, v_a_1012_, v_b_1013_);
lean_dec(v_index_1038_);
v___x_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1026_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
return v___x_1041_;
}
case 1:
{
lean_object* v_index_1042_; 
v_index_1042_ = lean_ctor_get(v___x_1037_, 0);
lean_inc(v_index_1042_);
lean_dec_ref_known(v___x_1037_, 1);
v___y_1028_ = v___x_1036_;
v_i_1029_ = v_index_1042_;
goto v___jp_1027_;
}
default: 
{
lean_object* v___x_1043_; 
v___x_1043_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1036_, v___x_1016_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_object* v_index_1044_; 
v_index_1044_ = lean_ctor_get(v___x_1043_, 0);
lean_inc(v_index_1044_);
lean_dec_ref_known(v___x_1043_, 1);
v___y_1028_ = v___x_1036_;
v_i_1029_ = v_index_1044_;
goto v___jp_1027_;
}
else
{
lean_object* v___x_1045_; 
lean_dec(v_b_1013_);
lean_dec(v_a_1012_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1026_);
lean_ctor_set(v___x_1045_, 1, v___x_1036_);
return v___x_1045_;
}
}
}
}
}
default: 
{
lean_object* v___x_1056_; lean_object* v___y_1058_; lean_object* v_i_1059_; lean_object* v___y_1066_; lean_object* v___x_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1056_ = lean_box(0);
v___x_1076_ = lean_unsigned_to_nat(1u);
v___x_1077_ = lean_nat_add(v_size_1014_, v___x_1076_);
v___x_1078_ = lean_nat_dec_lt(v___x_1077_, v___x_1017_);
if (v___x_1078_ == 0)
{
lean_object* v___x_1079_; 
lean_dec(v___x_1077_);
lean_inc_ref(v_inst_1010_);
lean_inc_ref(v_inst_1009_);
v___x_1079_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1009_, v_inst_1010_, v_m_1011_);
v___y_1066_ = v___x_1079_;
goto v___jp_1065_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; uint8_t v___x_1084_; 
v___x_1080_ = lean_unsigned_to_nat(4u);
v___x_1081_ = lean_nat_mul(v___x_1077_, v___x_1080_);
lean_dec(v___x_1077_);
v___x_1082_ = lean_unsigned_to_nat(3u);
v___x_1083_ = lean_nat_mul(v___x_1017_, v___x_1082_);
v___x_1084_ = lean_nat_dec_le(v___x_1081_, v___x_1083_);
lean_dec(v___x_1083_);
lean_dec(v___x_1081_);
if (v___x_1084_ == 0)
{
lean_object* v___x_1085_; 
lean_inc_ref(v_inst_1010_);
lean_inc_ref(v_inst_1009_);
v___x_1085_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1009_, v_inst_1010_, v_m_1011_);
v___y_1066_ = v___x_1085_;
goto v___jp_1065_;
}
else
{
v___y_1066_ = v_m_1011_;
goto v___jp_1065_;
}
}
v___jp_1057_:
{
lean_object* v_size_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_size_1060_ = lean_ctor_get(v___y_1058_, 0);
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_add(v_size_1060_, v___x_1061_);
v___x_1063_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1058_, v___x_1062_, v_i_1059_, v_a_1012_, v_b_1013_);
lean_dec(v_i_1059_);
v___x_1064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1056_);
lean_ctor_set(v___x_1064_, 1, v___x_1063_);
return v___x_1064_;
}
v___jp_1065_:
{
lean_object* v___x_1067_; 
lean_inc(v_a_1012_);
v___x_1067_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1009_, v_inst_1010_, v___y_1066_, v_a_1012_);
switch(lean_obj_tag(v___x_1067_))
{
case 0:
{
lean_object* v_index_1068_; lean_object* v_size_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_index_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_index_1068_);
lean_dec_ref_known(v___x_1067_, 3);
v_size_1069_ = lean_ctor_get(v___y_1066_, 0);
lean_inc(v_size_1069_);
v___x_1070_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1066_, v_size_1069_, v_index_1068_, v_a_1012_, v_b_1013_);
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
v___y_1058_ = v___y_1066_;
v_i_1059_ = v_index_1072_;
goto v___jp_1057_;
}
default: 
{
lean_object* v___x_1073_; 
v___x_1073_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1066_, v___x_1016_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_index_1074_; 
v_index_1074_ = lean_ctor_get(v___x_1073_, 0);
lean_inc(v_index_1074_);
lean_dec_ref_known(v___x_1073_, 1);
v___y_1058_ = v___y_1066_;
v_i_1059_ = v_index_1074_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1075_; 
lean_dec(v_b_1013_);
lean_dec(v_a_1012_);
v___x_1075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1056_);
lean_ctor_set(v___x_1075_, 1, v___y_1066_);
return v___x_1075_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg(lean_object* v_beq_1086_, lean_object* v_inst_1087_, lean_object* v_m_1088_, lean_object* v_a_1089_){
_start:
{
lean_object* v_keyArray_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; uint8_t v___x_1093_; 
v_keyArray_1090_ = lean_ctor_get(v_m_1088_, 1);
v___x_1091_ = lean_unsigned_to_nat(0u);
v___x_1092_ = lean_array_get_size(v_keyArray_1090_);
v___x_1093_ = lean_nat_dec_lt(v___x_1091_, v___x_1092_);
if (v___x_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec(v_a_1089_);
lean_dec_ref(v_inst_1087_);
lean_dec_ref(v_beq_1086_);
v___x_1094_ = lean_box(0);
return v___x_1094_;
}
else
{
lean_object* v___x_1095_; 
v___x_1095_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_1086_, v_inst_1087_, v_m_1088_, v_a_1089_);
return v___x_1095_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___redArg___boxed(lean_object* v_beq_1096_, lean_object* v_inst_1097_, lean_object* v_m_1098_, lean_object* v_a_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Std_HashMap_Raw_get_x3f___redArg(v_beq_1096_, v_inst_1097_, v_m_1098_, v_a_1099_);
lean_dec_ref(v_m_1098_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f(lean_object* v_00_u03b1_1101_, lean_object* v_00_u03b2_1102_, lean_object* v_beq_1103_, lean_object* v_inst_1104_, lean_object* v_m_1105_, lean_object* v_a_1106_){
_start:
{
lean_object* v_keyArray_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_keyArray_1107_ = lean_ctor_get(v_m_1105_, 1);
v___x_1108_ = lean_unsigned_to_nat(0u);
v___x_1109_ = lean_array_get_size(v_keyArray_1107_);
v___x_1110_ = lean_nat_dec_lt(v___x_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec(v_a_1106_);
lean_dec_ref(v_inst_1104_);
lean_dec_ref(v_beq_1103_);
v___x_1111_ = lean_box(0);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_beq_1103_, v_inst_1104_, v_m_1105_, v_a_1106_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_1113_, lean_object* v_00_u03b2_1114_, lean_object* v_beq_1115_, lean_object* v_inst_1116_, lean_object* v_m_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v_res_1119_; 
v_res_1119_ = l_Std_HashMap_Raw_get_x3f(v_00_u03b1_1113_, v_00_u03b2_1114_, v_beq_1115_, v_inst_1116_, v_m_1117_, v_a_1118_);
lean_dec_ref(v_m_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains___redArg(lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_m_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_keyArray_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; uint8_t v___x_1127_; 
v_keyArray_1124_ = lean_ctor_get(v_m_1122_, 1);
v___x_1125_ = lean_unsigned_to_nat(0u);
v___x_1126_ = lean_array_get_size(v_keyArray_1124_);
v___x_1127_ = lean_nat_dec_lt(v___x_1125_, v___x_1126_);
if (v___x_1127_ == 0)
{
lean_dec(v_a_1123_);
lean_dec_ref(v_inst_1121_);
lean_dec_ref(v_inst_1120_);
return v___x_1127_;
}
else
{
uint8_t v___x_1128_; 
v___x_1128_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1120_, v_inst_1121_, v_m_1122_, v_a_1123_);
return v___x_1128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___redArg___boxed(lean_object* v_inst_1129_, lean_object* v_inst_1130_, lean_object* v_m_1131_, lean_object* v_a_1132_){
_start:
{
uint8_t v_res_1133_; lean_object* v_r_1134_; 
v_res_1133_ = l_Std_HashMap_Raw_contains___redArg(v_inst_1129_, v_inst_1130_, v_m_1131_, v_a_1132_);
lean_dec_ref(v_m_1131_);
v_r_1134_ = lean_box(v_res_1133_);
return v_r_1134_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_contains(lean_object* v_00_u03b1_1135_, lean_object* v_00_u03b2_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_m_1139_, lean_object* v_a_1140_){
_start:
{
lean_object* v_keyArray_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v_keyArray_1141_ = lean_ctor_get(v_m_1139_, 1);
v___x_1142_ = lean_unsigned_to_nat(0u);
v___x_1143_ = lean_array_get_size(v_keyArray_1141_);
v___x_1144_ = lean_nat_dec_lt(v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
lean_dec(v_a_1140_);
lean_dec_ref(v_inst_1138_);
lean_dec_ref(v_inst_1137_);
return v___x_1144_;
}
else
{
uint8_t v___x_1145_; 
v___x_1145_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1137_, v_inst_1138_, v_m_1139_, v_a_1140_);
return v___x_1145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_contains___boxed(lean_object* v_00_u03b1_1146_, lean_object* v_00_u03b2_1147_, lean_object* v_inst_1148_, lean_object* v_inst_1149_, lean_object* v_m_1150_, lean_object* v_a_1151_){
_start:
{
uint8_t v_res_1152_; lean_object* v_r_1153_; 
v_res_1152_ = l_Std_HashMap_Raw_contains(v_00_u03b1_1146_, v_00_u03b2_1147_, v_inst_1148_, v_inst_1149_, v_m_1150_, v_a_1151_);
lean_dec_ref(v_m_1150_);
v_r_1153_ = lean_box(v_res_1152_);
return v_r_1153_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_1154_, lean_object* v_00_u03b2_1155_, lean_object* v_inst_1156_, lean_object* v_inst_1157_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = lean_box(0);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_1159_, lean_object* v_00_u03b2_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_HashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_1159_, v_00_u03b2_1160_, v_inst_1161_, v_inst_1162_);
lean_dec_ref(v_inst_1162_);
lean_dec_ref(v_inst_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_m_1166_, lean_object* v_a_1167_){
_start:
{
uint8_t v___x_1168_; 
v___x_1168_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_1164_, v_inst_1165_, v_m_1166_, v_a_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_m_1171_, lean_object* v_a_1172_){
_start:
{
uint8_t v_res_1173_; lean_object* v_r_1174_; 
v_res_1173_ = l_Std_HashMap_Raw_instDecidableMem___redArg(v_inst_1169_, v_inst_1170_, v_m_1171_, v_a_1172_);
lean_dec_ref(v_m_1171_);
v_r_1174_ = lean_box(v_res_1173_);
return v_r_1174_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_1175_, lean_object* v_00_u03b2_1176_, lean_object* v_inst_1177_, lean_object* v_inst_1178_, lean_object* v_m_1179_, lean_object* v_a_1180_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_1177_, v_inst_1178_, v_m_1179_, v_a_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_1182_, lean_object* v_00_u03b2_1183_, lean_object* v_inst_1184_, lean_object* v_inst_1185_, lean_object* v_m_1186_, lean_object* v_a_1187_){
_start:
{
uint8_t v_res_1188_; lean_object* v_r_1189_; 
v_res_1188_ = l_Std_HashMap_Raw_instDecidableMem(v_00_u03b1_1182_, v_00_u03b2_1183_, v_inst_1184_, v_inst_1185_, v_m_1186_, v_a_1187_);
lean_dec_ref(v_m_1186_);
v_r_1189_ = lean_box(v_res_1188_);
return v_r_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg(lean_object* v_inst_1190_, lean_object* v_inst_1191_, lean_object* v_m_1192_, lean_object* v_a_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v_val_1195_; 
v___x_1194_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1190_, v_inst_1191_, v_m_1192_, v_a_1193_);
v_val_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_val_1195_);
lean_dec(v___x_1194_);
return v_val_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___redArg___boxed(lean_object* v_inst_1196_, lean_object* v_inst_1197_, lean_object* v_m_1198_, lean_object* v_a_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Std_HashMap_Raw_get___redArg(v_inst_1196_, v_inst_1197_, v_m_1198_, v_a_1199_);
lean_dec_ref(v_m_1198_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get(lean_object* v_00_u03b1_1201_, lean_object* v_00_u03b2_1202_, lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_m_1205_, lean_object* v_a_1206_, lean_object* v_h_1207_){
_start:
{
lean_object* v___x_1208_; lean_object* v_val_1209_; 
v___x_1208_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1203_, v_inst_1204_, v_m_1205_, v_a_1206_);
v_val_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_val_1209_);
lean_dec(v___x_1208_);
return v_val_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get___boxed(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_m_1214_, lean_object* v_a_1215_, lean_object* v_h_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l_Std_HashMap_Raw_get(v_00_u03b1_1210_, v_00_u03b2_1211_, v_inst_1212_, v_inst_1213_, v_m_1214_, v_a_1215_, v_h_1216_);
lean_dec_ref(v_m_1214_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg(lean_object* v_inst_1218_, lean_object* v_inst_1219_, lean_object* v_m_1220_, lean_object* v_a_1221_, lean_object* v_fallback_1222_){
_start:
{
lean_object* v_keyArray_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; uint8_t v___x_1226_; 
v_keyArray_1223_ = lean_ctor_get(v_m_1220_, 1);
v___x_1224_ = lean_unsigned_to_nat(0u);
v___x_1225_ = lean_array_get_size(v_keyArray_1223_);
v___x_1226_ = lean_nat_dec_lt(v___x_1224_, v___x_1225_);
if (v___x_1226_ == 0)
{
lean_dec(v_a_1221_);
lean_dec_ref(v_inst_1219_);
lean_dec_ref(v_inst_1218_);
lean_inc(v_fallback_1222_);
return v_fallback_1222_;
}
else
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_1218_, v_inst_1219_, v_m_1220_, v_a_1221_, v_fallback_1222_);
return v___x_1227_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___redArg___boxed(lean_object* v_inst_1228_, lean_object* v_inst_1229_, lean_object* v_m_1230_, lean_object* v_a_1231_, lean_object* v_fallback_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Std_HashMap_Raw_getD___redArg(v_inst_1228_, v_inst_1229_, v_m_1230_, v_a_1231_, v_fallback_1232_);
lean_dec(v_fallback_1232_);
lean_dec_ref(v_m_1230_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD(lean_object* v_00_u03b1_1234_, lean_object* v_00_u03b2_1235_, lean_object* v_inst_1236_, lean_object* v_inst_1237_, lean_object* v_m_1238_, lean_object* v_a_1239_, lean_object* v_fallback_1240_){
_start:
{
lean_object* v_keyArray_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_keyArray_1241_ = lean_ctor_get(v_m_1238_, 1);
v___x_1242_ = lean_unsigned_to_nat(0u);
v___x_1243_ = lean_array_get_size(v_keyArray_1241_);
v___x_1244_ = lean_nat_dec_lt(v___x_1242_, v___x_1243_);
if (v___x_1244_ == 0)
{
lean_dec(v_a_1239_);
lean_dec_ref(v_inst_1237_);
lean_dec_ref(v_inst_1236_);
lean_inc(v_fallback_1240_);
return v_fallback_1240_;
}
else
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_1236_, v_inst_1237_, v_m_1238_, v_a_1239_, v_fallback_1240_);
return v___x_1245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getD___boxed(lean_object* v_00_u03b1_1246_, lean_object* v_00_u03b2_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_m_1250_, lean_object* v_a_1251_, lean_object* v_fallback_1252_){
_start:
{
lean_object* v_res_1253_; 
v_res_1253_ = l_Std_HashMap_Raw_getD(v_00_u03b1_1246_, v_00_u03b2_1247_, v_inst_1248_, v_inst_1249_, v_m_1250_, v_a_1251_, v_fallback_1252_);
lean_dec(v_fallback_1252_);
lean_dec_ref(v_m_1250_);
return v_res_1253_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg(lean_object* v_inst_1254_, lean_object* v_inst_1255_, lean_object* v_inst_1256_, lean_object* v_m_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v_keyArray_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_keyArray_1259_ = lean_ctor_get(v_m_1257_, 1);
v___x_1260_ = lean_unsigned_to_nat(0u);
v___x_1261_ = lean_array_get_size(v_keyArray_1259_);
v___x_1262_ = lean_nat_dec_lt(v___x_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_dec(v_a_1258_);
lean_dec_ref(v_inst_1255_);
lean_dec_ref(v_inst_1254_);
lean_inc(v_inst_1256_);
return v_inst_1256_;
}
else
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_1254_, v_inst_1255_, v_inst_1256_, v_m_1257_, v_a_1258_);
return v___x_1263_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_inst_1266_, lean_object* v_m_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l_Std_HashMap_Raw_get_x21___redArg(v_inst_1264_, v_inst_1265_, v_inst_1266_, v_m_1267_, v_a_1268_);
lean_dec_ref(v_m_1267_);
lean_dec(v_inst_1266_);
return v_res_1269_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21(lean_object* v_00_u03b1_1270_, lean_object* v_00_u03b2_1271_, lean_object* v_inst_1272_, lean_object* v_inst_1273_, lean_object* v_inst_1274_, lean_object* v_m_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_keyArray_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; uint8_t v___x_1280_; 
v_keyArray_1277_ = lean_ctor_get(v_m_1275_, 1);
v___x_1278_ = lean_unsigned_to_nat(0u);
v___x_1279_ = lean_array_get_size(v_keyArray_1277_);
v___x_1280_ = lean_nat_dec_lt(v___x_1278_, v___x_1279_);
if (v___x_1280_ == 0)
{
lean_dec(v_a_1276_);
lean_dec_ref(v_inst_1273_);
lean_dec_ref(v_inst_1272_);
lean_inc(v_inst_1274_);
return v_inst_1274_;
}
else
{
lean_object* v___x_1281_; 
v___x_1281_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_1272_, v_inst_1273_, v_inst_1274_, v_m_1275_, v_a_1276_);
return v___x_1281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_1282_, lean_object* v_00_u03b2_1283_, lean_object* v_inst_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_m_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Std_HashMap_Raw_get_x21(v_00_u03b1_1282_, v_00_u03b2_1283_, v_inst_1284_, v_inst_1285_, v_inst_1286_, v_m_1287_, v_a_1288_);
lean_dec_ref(v_m_1287_);
lean_dec(v_inst_1286_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(lean_object* v_inst_1290_, lean_object* v_inst_1291_, lean_object* v_m_1292_, lean_object* v_a_1293_, lean_object* v_h_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v_val_1296_; 
v___x_1295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1290_, v_inst_1291_, v_m_1292_, v_a_1293_);
v_val_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_val_1296_);
lean_dec(v___x_1295_);
return v_val_1296_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed(lean_object* v_inst_1297_, lean_object* v_inst_1298_, lean_object* v_m_1299_, lean_object* v_a_1300_, lean_object* v_h_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0(v_inst_1297_, v_inst_1298_, v_m_1299_, v_a_1300_, v_h_1301_);
lean_dec_ref(v_m_1299_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(lean_object* v_inst_1303_, lean_object* v_inst_1304_, lean_object* v_m_1305_, lean_object* v_a_1306_){
_start:
{
lean_object* v_keyArray_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; uint8_t v___x_1310_; 
v_keyArray_1307_ = lean_ctor_get(v_m_1305_, 1);
v___x_1308_ = lean_unsigned_to_nat(0u);
v___x_1309_ = lean_array_get_size(v_keyArray_1307_);
v___x_1310_ = lean_nat_dec_lt(v___x_1308_, v___x_1309_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
lean_dec(v_a_1306_);
lean_dec_ref(v_inst_1304_);
lean_dec_ref(v_inst_1303_);
v___x_1311_ = lean_box(0);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1303_, v_inst_1304_, v_m_1305_, v_a_1306_);
return v___x_1312_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed(lean_object* v_inst_1313_, lean_object* v_inst_1314_, lean_object* v_m_1315_, lean_object* v_a_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1(v_inst_1313_, v_inst_1314_, v_m_1315_, v_a_1316_);
lean_dec_ref(v_m_1315_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(lean_object* v_inst_1318_, lean_object* v_inst_1319_, lean_object* v_inst_1320_, lean_object* v_m_1321_, lean_object* v_a_1322_){
_start:
{
lean_object* v_keyArray_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_keyArray_1323_ = lean_ctor_get(v_m_1321_, 1);
v___x_1324_ = lean_unsigned_to_nat(0u);
v___x_1325_ = lean_array_get_size(v_keyArray_1323_);
v___x_1326_ = lean_nat_dec_lt(v___x_1324_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_dec(v_a_1322_);
lean_dec_ref(v_inst_1319_);
lean_dec_ref(v_inst_1318_);
lean_inc(v_inst_1320_);
return v_inst_1320_;
}
else
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_1318_, v_inst_1319_, v_inst_1320_, v_m_1321_, v_a_1322_);
return v___x_1327_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed(lean_object* v_inst_1328_, lean_object* v_inst_1329_, lean_object* v_inst_1330_, lean_object* v_m_1331_, lean_object* v_a_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2(v_inst_1328_, v_inst_1329_, v_inst_1330_, v_m_1331_, v_a_1332_);
lean_dec_ref(v_m_1331_);
lean_dec(v_inst_1330_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(lean_object* v_inst_1334_, lean_object* v_inst_1335_){
_start:
{
lean_object* v___f_1336_; lean_object* v___f_1337_; lean_object* v___f_1338_; lean_object* v___x_1339_; 
lean_inc_ref_n(v_inst_1335_, 2);
lean_inc_ref_n(v_inst_1334_, 2);
v___f_1336_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__0___boxed), 5, 2);
lean_closure_set(v___f_1336_, 0, v_inst_1334_);
lean_closure_set(v___f_1336_, 1, v_inst_1335_);
v___f_1337_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1337_, 0, v_inst_1334_);
lean_closure_set(v___f_1337_, 1, v_inst_1335_);
v___f_1338_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instGetElem_x3fMem___redArg___lam__2___boxed), 5, 2);
lean_closure_set(v___f_1338_, 0, v_inst_1334_);
lean_closure_set(v___f_1338_, 1, v_inst_1335_);
v___x_1339_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1339_, 0, v___f_1336_);
lean_ctor_set(v___x_1339_, 1, v___f_1337_);
lean_ctor_set(v___x_1339_, 2, v___f_1338_);
return v___x_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instGetElem_x3fMem(lean_object* v_00_u03b1_1340_, lean_object* v_00_u03b2_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Std_HashMap_Raw_instGetElem_x3fMem___redArg(v_inst_1342_, v_inst_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_1345_, lean_object* v_inst_1346_, lean_object* v_m_1347_, lean_object* v_a_1348_){
_start:
{
lean_object* v_keyArray_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; uint8_t v___x_1352_; 
v_keyArray_1349_ = lean_ctor_get(v_m_1347_, 1);
v___x_1350_ = lean_unsigned_to_nat(0u);
v___x_1351_ = lean_array_get_size(v_keyArray_1349_);
v___x_1352_ = lean_nat_dec_lt(v___x_1350_, v___x_1351_);
if (v___x_1352_ == 0)
{
lean_object* v___x_1353_; 
lean_dec(v_a_1348_);
lean_dec_ref(v_inst_1346_);
lean_dec_ref(v_inst_1345_);
v___x_1353_ = lean_box(0);
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; 
v___x_1354_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1345_, v_inst_1346_, v_m_1347_, v_a_1348_);
return v___x_1354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_1355_, lean_object* v_inst_1356_, lean_object* v_m_1357_, lean_object* v_a_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Std_HashMap_Raw_getKey_x3f___redArg(v_inst_1355_, v_inst_1356_, v_m_1357_, v_a_1358_);
lean_dec_ref(v_m_1357_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_1360_, lean_object* v_00_u03b2_1361_, lean_object* v_inst_1362_, lean_object* v_inst_1363_, lean_object* v_m_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v_keyArray_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_keyArray_1366_ = lean_ctor_get(v_m_1364_, 1);
v___x_1367_ = lean_unsigned_to_nat(0u);
v___x_1368_ = lean_array_get_size(v_keyArray_1366_);
v___x_1369_ = lean_nat_dec_lt(v___x_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
lean_dec(v_a_1365_);
lean_dec_ref(v_inst_1363_);
lean_dec_ref(v_inst_1362_);
v___x_1370_ = lean_box(0);
return v___x_1370_;
}
else
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1362_, v_inst_1363_, v_m_1364_, v_a_1365_);
return v___x_1371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_1372_, lean_object* v_00_u03b2_1373_, lean_object* v_inst_1374_, lean_object* v_inst_1375_, lean_object* v_m_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Std_HashMap_Raw_getKey_x3f(v_00_u03b1_1372_, v_00_u03b2_1373_, v_inst_1374_, v_inst_1375_, v_m_1376_, v_a_1377_);
lean_dec_ref(v_m_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg(lean_object* v_inst_1379_, lean_object* v_inst_1380_, lean_object* v_m_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1383_; lean_object* v_val_1384_; 
v___x_1383_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1379_, v_inst_1380_, v_m_1381_, v_a_1382_);
v_val_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_val_1384_);
lean_dec(v___x_1383_);
return v_val_1384_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_1385_, lean_object* v_inst_1386_, lean_object* v_m_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Std_HashMap_Raw_getKey___redArg(v_inst_1385_, v_inst_1386_, v_m_1387_, v_a_1388_);
lean_dec_ref(v_m_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey(lean_object* v_00_u03b1_1390_, lean_object* v_00_u03b2_1391_, lean_object* v_inst_1392_, lean_object* v_inst_1393_, lean_object* v_m_1394_, lean_object* v_a_1395_, lean_object* v_h_1396_){
_start:
{
lean_object* v___x_1397_; lean_object* v_val_1398_; 
v___x_1397_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1392_, v_inst_1393_, v_m_1394_, v_a_1395_);
v_val_1398_ = lean_ctor_get(v___x_1397_, 0);
lean_inc(v_val_1398_);
lean_dec(v___x_1397_);
return v_val_1398_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_1399_, lean_object* v_00_u03b2_1400_, lean_object* v_inst_1401_, lean_object* v_inst_1402_, lean_object* v_m_1403_, lean_object* v_a_1404_, lean_object* v_h_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_Std_HashMap_Raw_getKey(v_00_u03b1_1399_, v_00_u03b2_1400_, v_inst_1401_, v_inst_1402_, v_m_1403_, v_a_1404_, v_h_1405_);
lean_dec_ref(v_m_1403_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg(lean_object* v_inst_1407_, lean_object* v_inst_1408_, lean_object* v_m_1409_, lean_object* v_a_1410_, lean_object* v_fallback_1411_){
_start:
{
lean_object* v_keyArray_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; 
v_keyArray_1412_ = lean_ctor_get(v_m_1409_, 1);
v___x_1413_ = lean_unsigned_to_nat(0u);
v___x_1414_ = lean_array_get_size(v_keyArray_1412_);
v___x_1415_ = lean_nat_dec_lt(v___x_1413_, v___x_1414_);
if (v___x_1415_ == 0)
{
lean_dec(v_a_1410_);
lean_dec_ref(v_inst_1408_);
lean_dec_ref(v_inst_1407_);
lean_inc(v_fallback_1411_);
return v_fallback_1411_;
}
else
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1407_, v_inst_1408_, v_m_1409_, v_a_1410_, v_fallback_1411_);
return v___x_1416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_m_1419_, lean_object* v_a_1420_, lean_object* v_fallback_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Std_HashMap_Raw_getKeyD___redArg(v_inst_1417_, v_inst_1418_, v_m_1419_, v_a_1420_, v_fallback_1421_);
lean_dec(v_fallback_1421_);
lean_dec_ref(v_m_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD(lean_object* v_00_u03b1_1423_, lean_object* v_00_u03b2_1424_, lean_object* v_inst_1425_, lean_object* v_inst_1426_, lean_object* v_m_1427_, lean_object* v_a_1428_, lean_object* v_fallback_1429_){
_start:
{
lean_object* v_keyArray_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; uint8_t v___x_1433_; 
v_keyArray_1430_ = lean_ctor_get(v_m_1427_, 1);
v___x_1431_ = lean_unsigned_to_nat(0u);
v___x_1432_ = lean_array_get_size(v_keyArray_1430_);
v___x_1433_ = lean_nat_dec_lt(v___x_1431_, v___x_1432_);
if (v___x_1433_ == 0)
{
lean_dec(v_a_1428_);
lean_dec_ref(v_inst_1426_);
lean_dec_ref(v_inst_1425_);
lean_inc(v_fallback_1429_);
return v_fallback_1429_;
}
else
{
lean_object* v___x_1434_; 
v___x_1434_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1425_, v_inst_1426_, v_m_1427_, v_a_1428_, v_fallback_1429_);
return v___x_1434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_1435_, lean_object* v_00_u03b2_1436_, lean_object* v_inst_1437_, lean_object* v_inst_1438_, lean_object* v_m_1439_, lean_object* v_a_1440_, lean_object* v_fallback_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Std_HashMap_Raw_getKeyD(v_00_u03b1_1435_, v_00_u03b2_1436_, v_inst_1437_, v_inst_1438_, v_m_1439_, v_a_1440_, v_fallback_1441_);
lean_dec(v_fallback_1441_);
lean_dec_ref(v_m_1439_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg(lean_object* v_inst_1443_, lean_object* v_inst_1444_, lean_object* v_inst_1445_, lean_object* v_m_1446_, lean_object* v_a_1447_){
_start:
{
lean_object* v_keyArray_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; uint8_t v___x_1451_; 
v_keyArray_1448_ = lean_ctor_get(v_m_1446_, 1);
v___x_1449_ = lean_unsigned_to_nat(0u);
v___x_1450_ = lean_array_get_size(v_keyArray_1448_);
v___x_1451_ = lean_nat_dec_lt(v___x_1449_, v___x_1450_);
if (v___x_1451_ == 0)
{
lean_dec(v_a_1447_);
lean_dec_ref(v_inst_1444_);
lean_dec_ref(v_inst_1443_);
lean_inc(v_inst_1445_);
return v_inst_1445_;
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1443_, v_inst_1444_, v_inst_1445_, v_m_1446_, v_a_1447_);
return v___x_1452_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_m_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Std_HashMap_Raw_getKey_x21___redArg(v_inst_1453_, v_inst_1454_, v_inst_1455_, v_m_1456_, v_a_1457_);
lean_dec_ref(v_m_1456_);
lean_dec(v_inst_1455_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21(lean_object* v_00_u03b1_1459_, lean_object* v_00_u03b2_1460_, lean_object* v_inst_1461_, lean_object* v_inst_1462_, lean_object* v_inst_1463_, lean_object* v_m_1464_, lean_object* v_a_1465_){
_start:
{
lean_object* v_keyArray_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; uint8_t v___x_1469_; 
v_keyArray_1466_ = lean_ctor_get(v_m_1464_, 1);
v___x_1467_ = lean_unsigned_to_nat(0u);
v___x_1468_ = lean_array_get_size(v_keyArray_1466_);
v___x_1469_ = lean_nat_dec_lt(v___x_1467_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_dec(v_a_1465_);
lean_dec_ref(v_inst_1462_);
lean_dec_ref(v_inst_1461_);
lean_inc(v_inst_1463_);
return v_inst_1463_;
}
else
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1461_, v_inst_1462_, v_inst_1463_, v_m_1464_, v_a_1465_);
return v___x_1470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_1471_, lean_object* v_00_u03b2_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_inst_1475_, lean_object* v_m_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Std_HashMap_Raw_getKey_x21(v_00_u03b1_1471_, v_00_u03b2_1472_, v_inst_1473_, v_inst_1474_, v_inst_1475_, v_m_1476_, v_a_1477_);
lean_dec_ref(v_m_1476_);
lean_dec(v_inst_1475_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase___redArg(lean_object* v_inst_1479_, lean_object* v_inst_1480_, lean_object* v_m_1481_, lean_object* v_a_1482_){
_start:
{
lean_object* v_keyArray_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; uint8_t v___x_1486_; 
v_keyArray_1483_ = lean_ctor_get(v_m_1481_, 1);
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = lean_array_get_size(v_keyArray_1483_);
v___x_1486_ = lean_nat_dec_lt(v___x_1484_, v___x_1485_);
if (v___x_1486_ == 0)
{
lean_dec(v_a_1482_);
lean_dec_ref(v_inst_1480_);
lean_dec_ref(v_inst_1479_);
return v_m_1481_;
}
else
{
lean_object* v___x_1487_; 
v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1479_, v_inst_1480_, v_m_1481_, v_a_1482_);
return v___x_1487_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_erase(lean_object* v_00_u03b1_1488_, lean_object* v_00_u03b2_1489_, lean_object* v_inst_1490_, lean_object* v_inst_1491_, lean_object* v_m_1492_, lean_object* v_a_1493_){
_start:
{
lean_object* v_keyArray_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; uint8_t v___x_1497_; 
v_keyArray_1494_ = lean_ctor_get(v_m_1492_, 1);
v___x_1495_ = lean_unsigned_to_nat(0u);
v___x_1496_ = lean_array_get_size(v_keyArray_1494_);
v___x_1497_ = lean_nat_dec_lt(v___x_1495_, v___x_1496_);
if (v___x_1497_ == 0)
{
lean_dec(v_a_1493_);
lean_dec_ref(v_inst_1491_);
lean_dec_ref(v_inst_1490_);
return v_m_1492_;
}
else
{
lean_object* v___x_1498_; 
v___x_1498_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1490_, v_inst_1491_, v_m_1492_, v_a_1493_);
return v___x_1498_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg(lean_object* v_m_1499_){
_start:
{
lean_object* v_size_1500_; 
v_size_1500_ = lean_ctor_get(v_m_1499_, 0);
lean_inc(v_size_1500_);
return v_size_1500_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___redArg___boxed(lean_object* v_m_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Std_HashMap_Raw_size___redArg(v_m_1501_);
lean_dec_ref(v_m_1501_);
return v_res_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size(lean_object* v_00_u03b1_1503_, lean_object* v_00_u03b2_1504_, lean_object* v_m_1505_){
_start:
{
lean_object* v_size_1506_; 
v_size_1506_ = lean_ctor_get(v_m_1505_, 0);
lean_inc(v_size_1506_);
return v_size_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_size___boxed(lean_object* v_00_u03b1_1507_, lean_object* v_00_u03b2_1508_, lean_object* v_m_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Std_HashMap_Raw_size(v_00_u03b1_1507_, v_00_u03b2_1508_, v_m_1509_);
lean_dec_ref(v_m_1509_);
return v_res_1510_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty___redArg(lean_object* v_m_1511_){
_start:
{
lean_object* v_size_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_size_1512_ = lean_ctor_get(v_m_1511_, 0);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = lean_nat_dec_eq(v_size_1512_, v___x_1513_);
return v___x_1514_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1515_){
_start:
{
uint8_t v_res_1516_; lean_object* v_r_1517_; 
v_res_1516_ = l_Std_HashMap_Raw_isEmpty___redArg(v_m_1515_);
lean_dec_ref(v_m_1515_);
v_r_1517_ = lean_box(v_res_1516_);
return v_r_1517_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_isEmpty(lean_object* v_00_u03b1_1518_, lean_object* v_00_u03b2_1519_, lean_object* v_m_1520_){
_start:
{
lean_object* v_size_1521_; lean_object* v___x_1522_; uint8_t v___x_1523_; 
v_size_1521_ = lean_ctor_get(v_m_1520_, 0);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = lean_nat_dec_eq(v_size_1521_, v___x_1522_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1524_, lean_object* v_00_u03b2_1525_, lean_object* v_m_1526_){
_start:
{
uint8_t v_res_1527_; lean_object* v_r_1528_; 
v_res_1527_ = l_Std_HashMap_Raw_isEmpty(v_00_u03b1_1524_, v_00_u03b2_1525_, v_m_1526_);
lean_dec_ref(v_m_1526_);
v_r_1528_ = lean_box(v_res_1527_);
return v_r_1528_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0(lean_object* v_x1_1529_, lean_object* v_x2_1530_, lean_object* v_x3_1531_){
_start:
{
lean_object* v___x_1532_; 
v___x_1532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1532_, 0, v_x2_1530_);
lean_ctor_set(v___x_1532_, 1, v_x1_1529_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_x1_1533_, lean_object* v_x2_1534_, lean_object* v_x3_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Std_HashMap_Raw_keys___redArg___lam__0(v_x1_1533_, v_x2_1534_, v_x3_1535_);
lean_dec(v_x3_1535_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg(lean_object* v_m_1557_){
_start:
{
lean_object* v___f_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___f_1558_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__0));
v___x_1559_ = lean_box(0);
v___x_1560_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_1561_ = lean_unsigned_to_nat(0u);
v___x_1562_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_1560_, v___f_1558_, v_m_1557_, v___x_1559_, v___x_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___redArg___boxed(lean_object* v_m_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_Std_HashMap_Raw_keys___redArg(v_m_1563_);
lean_dec_ref(v_m_1563_);
return v_res_1564_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys(lean_object* v_00_u03b1_1565_, lean_object* v_00_u03b2_1566_, lean_object* v_m_1567_){
_start:
{
lean_object* v___f_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___f_1568_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__0));
v___x_1569_ = lean_box(0);
v___x_1570_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_1570_, v___f_1568_, v_m_1567_, v___x_1569_, v___x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keys___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_00_u03b2_1574_, lean_object* v_m_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Std_HashMap_Raw_keys(v_00_u03b1_1573_, v_00_u03b2_1574_, v_m_1575_);
lean_dec_ref(v_m_1575_);
return v_res_1576_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList___redArg(lean_object* v_inst_1581_, lean_object* v_inst_1582_, lean_object* v_l_1583_){
_start:
{
lean_object* v___x_1584_; uint8_t v___x_1585_; 
v___x_1584_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
v___x_1585_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1585_ == 0)
{
lean_dec(v_l_1583_);
lean_dec_ref(v_inst_1582_);
lean_dec_ref(v_inst_1581_);
return v___x_1584_;
}
else
{
lean_object* v___f_1586_; lean_object* v___x_1587_; 
v___f_1586_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1587_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1586_, v_inst_1581_, v_inst_1582_, v___x_1584_, v_l_1583_);
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofList(lean_object* v_00_u03b1_1588_, lean_object* v_00_u03b2_1589_, lean_object* v_inst_1590_, lean_object* v_inst_1591_, lean_object* v_l_1592_){
_start:
{
lean_object* v___x_1593_; uint8_t v___x_1594_; 
v___x_1593_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
v___x_1594_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1594_ == 0)
{
lean_dec(v_l_1592_);
lean_dec_ref(v_inst_1591_);
lean_dec_ref(v_inst_1590_);
return v___x_1593_;
}
else
{
lean_object* v___f_1595_; lean_object* v___x_1596_; 
v___f_1595_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1596_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1595_, v_inst_1590_, v_inst_1591_, v___x_1593_, v_l_1592_);
return v___x_1596_;
}
}
}
static lean_object* _init_l_Std_HashMap_Raw_unitOfList___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_1597_; lean_object* v___x_1598_; 
v_cellCount_1597_ = lean_unsigned_to_nat(16u);
v___x_1598_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_1597_);
return v___x_1598_;
}
}
static lean_object* _init_l_Std_HashMap_Raw_unitOfList___redArg___closed__1(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1599_ = lean_obj_once(&l_Std_HashMap_Raw_unitOfList___redArg___closed__0, &l_Std_HashMap_Raw_unitOfList___redArg___closed__0_once, _init_l_Std_HashMap_Raw_unitOfList___redArg___closed__0);
v___x_1600_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__0, &l_Std_HashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__0);
v___x_1601_ = lean_unsigned_to_nat(0u);
v___x_1602_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
lean_ctor_set(v___x_1602_, 1, v___x_1600_);
lean_ctor_set(v___x_1602_, 2, v___x_1599_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList___redArg(lean_object* v_inst_1603_, lean_object* v_inst_1604_, lean_object* v_l_1605_){
_start:
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = lean_obj_once(&l_Std_HashMap_Raw_unitOfList___redArg___closed__1, &l_Std_HashMap_Raw_unitOfList___redArg___closed__1_once, _init_l_Std_HashMap_Raw_unitOfList___redArg___closed__1);
v___x_1607_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1607_ == 0)
{
lean_dec(v_l_1605_);
lean_dec_ref(v_inst_1604_);
lean_dec_ref(v_inst_1603_);
return v___x_1606_;
}
else
{
lean_object* v___f_1608_; lean_object* v___x_1609_; 
v___f_1608_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1609_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1608_, v_inst_1603_, v_inst_1604_, v___x_1606_, v_l_1605_);
return v___x_1609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfList(lean_object* v_00_u03b1_1610_, lean_object* v_inst_1611_, lean_object* v_inst_1612_, lean_object* v_l_1613_){
_start:
{
lean_object* v___x_1614_; uint8_t v___x_1615_; 
v___x_1614_ = lean_obj_once(&l_Std_HashMap_Raw_unitOfList___redArg___closed__1, &l_Std_HashMap_Raw_unitOfList___redArg___closed__1_once, _init_l_Std_HashMap_Raw_unitOfList___redArg___closed__1);
v___x_1615_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1615_ == 0)
{
lean_dec(v_l_1613_);
lean_dec_ref(v_inst_1612_);
lean_dec_ref(v_inst_1611_);
return v___x_1614_;
}
else
{
lean_object* v___f_1616_; lean_object* v___x_1617_; 
v___f_1616_ = ((lean_object*)(l_Std_HashMap_Raw_ofList___redArg___closed__1));
v___x_1617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_1616_, v_inst_1611_, v_inst_1612_, v___x_1614_, v_l_1613_);
return v___x_1617_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray___redArg(lean_object* v_inst_1622_, lean_object* v_inst_1623_, lean_object* v_a_1624_){
_start:
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
v___x_1626_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1626_ == 0)
{
lean_dec_ref(v_a_1624_);
lean_dec_ref(v_inst_1623_);
lean_dec_ref(v_inst_1622_);
return v___x_1625_;
}
else
{
lean_object* v___f_1627_; lean_object* v___x_1628_; 
v___f_1627_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1628_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1627_, v_inst_1622_, v_inst_1623_, v___x_1625_, v_a_1624_);
return v___x_1628_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_ofArray(lean_object* v_00_u03b1_1629_, lean_object* v_00_u03b2_1630_, lean_object* v_inst_1631_, lean_object* v_inst_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1634_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
v___x_1635_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_1635_ == 0)
{
lean_dec_ref(v_a_1633_);
lean_dec_ref(v_inst_1632_);
lean_dec_ref(v_inst_1631_);
return v___x_1634_;
}
else
{
lean_object* v___f_1636_; lean_object* v___x_1637_; 
v___f_1636_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_1637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_1636_, v_inst_1631_, v_inst_1632_, v___x_1634_, v_a_1633_);
return v___x_1637_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter___redArg(lean_object* v_inst_1638_, lean_object* v_inst_1639_, lean_object* v_m_1640_, lean_object* v_a_1641_, lean_object* v_f_1642_){
_start:
{
lean_object* v_size_1643_; lean_object* v_keyArray_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_size_1643_ = lean_ctor_get(v_m_1640_, 0);
v_keyArray_1644_ = lean_ctor_get(v_m_1640_, 1);
v___x_1645_ = lean_unsigned_to_nat(0u);
v___x_1646_ = lean_array_get_size(v_keyArray_1644_);
v___x_1647_ = lean_nat_dec_lt(v___x_1645_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_dec_ref(v_f_1642_);
lean_dec(v_a_1641_);
lean_dec_ref(v_m_1640_);
lean_dec_ref(v_inst_1639_);
lean_dec_ref(v_inst_1638_);
v___x_1648_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_1648_;
}
else
{
lean_object* v___x_1649_; 
lean_inc(v_a_1641_);
lean_inc_ref(v_inst_1639_);
lean_inc_ref(v_inst_1638_);
v___x_1649_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1638_, v_inst_1639_, v_m_1640_, v_a_1641_);
switch(lean_obj_tag(v___x_1649_))
{
case 0:
{
lean_object* v_index_1650_; lean_object* v_value_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
lean_dec_ref(v_inst_1639_);
lean_dec_ref(v_inst_1638_);
v_index_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_index_1650_);
v_value_1651_ = lean_ctor_get(v___x_1649_, 2);
lean_inc(v_value_1651_);
lean_dec_ref_known(v___x_1649_, 3);
v___x_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1652_, 0, v_value_1651_);
v___x_1653_ = lean_apply_1(v_f_1642_, v___x_1652_);
if (lean_obj_tag(v___x_1653_) == 0)
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
lean_dec(v_a_1641_);
v___x_1654_ = lean_unsigned_to_nat(1u);
v___x_1655_ = lean_nat_sub(v_size_1643_, v___x_1654_);
v___x_1656_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1640_, v___x_1655_, v_index_1650_);
lean_dec(v_index_1650_);
return v___x_1656_;
}
else
{
lean_object* v_val_1657_; lean_object* v___x_1658_; 
lean_inc(v_size_1643_);
v_val_1657_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v___x_1653_, 1);
v___x_1658_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1640_, v_size_1643_, v_index_1650_, v_a_1641_, v_val_1657_);
lean_dec(v_index_1650_);
return v___x_1658_;
}
}
case 1:
{
lean_object* v_index_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_index_1659_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_index_1659_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1660_ = lean_box(0);
v___x_1661_ = lean_apply_1(v_f_1642_, v___x_1660_);
if (lean_obj_tag(v___x_1661_) == 0)
{
lean_dec(v_index_1659_);
lean_dec(v_a_1641_);
lean_dec_ref(v_inst_1639_);
lean_dec_ref(v_inst_1638_);
return v_m_1640_;
}
else
{
lean_object* v_val_1662_; lean_object* v___y_1664_; lean_object* v_i_1665_; lean_object* v___x_1679_; lean_object* v___x_1680_; uint8_t v___x_1681_; 
v_val_1662_ = lean_ctor_get(v___x_1661_, 0);
lean_inc(v_val_1662_);
lean_dec_ref_known(v___x_1661_, 1);
v___x_1679_ = lean_unsigned_to_nat(1u);
v___x_1680_ = lean_nat_add(v_size_1643_, v___x_1679_);
v___x_1681_ = lean_nat_dec_lt(v___x_1680_, v___x_1646_);
if (v___x_1681_ == 0)
{
lean_dec(v___x_1680_);
lean_dec(v_index_1659_);
goto v___jp_1670_;
}
else
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; uint8_t v___x_1686_; 
v___x_1682_ = lean_unsigned_to_nat(4u);
v___x_1683_ = lean_nat_mul(v___x_1680_, v___x_1682_);
v___x_1684_ = lean_unsigned_to_nat(3u);
v___x_1685_ = lean_nat_mul(v___x_1646_, v___x_1684_);
v___x_1686_ = lean_nat_dec_le(v___x_1683_, v___x_1685_);
lean_dec(v___x_1685_);
lean_dec(v___x_1683_);
if (v___x_1686_ == 0)
{
lean_dec(v___x_1680_);
lean_dec(v_index_1659_);
goto v___jp_1670_;
}
else
{
lean_object* v___x_1687_; 
lean_dec_ref(v_inst_1639_);
lean_dec_ref(v_inst_1638_);
v___x_1687_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1640_, v___x_1680_, v_index_1659_, v_a_1641_, v_val_1662_);
lean_dec(v_index_1659_);
return v___x_1687_;
}
}
v___jp_1663_:
{
lean_object* v_size_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; 
v_size_1666_ = lean_ctor_get(v___y_1664_, 0);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_add(v_size_1666_, v___x_1667_);
v___x_1669_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1664_, v___x_1668_, v_i_1665_, v_a_1641_, v_val_1662_);
lean_dec(v_i_1665_);
return v___x_1669_;
}
v___jp_1670_:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
lean_inc_ref(v_inst_1639_);
lean_inc_ref(v_inst_1638_);
v___x_1671_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1638_, v_inst_1639_, v_m_1640_);
lean_inc(v_a_1641_);
v___x_1672_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1638_, v_inst_1639_, v___x_1671_, v_a_1641_);
switch(lean_obj_tag(v___x_1672_))
{
case 0:
{
lean_object* v_index_1673_; lean_object* v_size_1674_; lean_object* v___x_1675_; 
v_index_1673_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_index_1673_);
lean_dec_ref_known(v___x_1672_, 3);
v_size_1674_ = lean_ctor_get(v___x_1671_, 0);
lean_inc(v_size_1674_);
v___x_1675_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1671_, v_size_1674_, v_index_1673_, v_a_1641_, v_val_1662_);
lean_dec(v_index_1673_);
return v___x_1675_;
}
case 1:
{
lean_object* v_index_1676_; 
v_index_1676_ = lean_ctor_get(v___x_1672_, 0);
lean_inc(v_index_1676_);
lean_dec_ref_known(v___x_1672_, 1);
v___y_1664_ = v___x_1671_;
v_i_1665_ = v_index_1676_;
goto v___jp_1663_;
}
default: 
{
lean_object* v___x_1677_; 
v___x_1677_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1671_, v___x_1645_);
if (lean_obj_tag(v___x_1677_) == 0)
{
lean_object* v_index_1678_; 
v_index_1678_ = lean_ctor_get(v___x_1677_, 0);
lean_inc(v_index_1678_);
lean_dec_ref_known(v___x_1677_, 1);
v___y_1664_ = v___x_1671_;
v_i_1665_ = v_index_1678_;
goto v___jp_1663_;
}
else
{
lean_dec(v_val_1662_);
lean_dec(v_a_1641_);
return v___x_1671_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_box(0);
v___x_1689_ = lean_apply_1(v_f_1642_, v___x_1688_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_dec(v_a_1641_);
lean_dec_ref(v_inst_1639_);
lean_dec_ref(v_inst_1638_);
return v_m_1640_;
}
else
{
lean_object* v_val_1690_; lean_object* v___y_1692_; lean_object* v_i_1693_; lean_object* v___y_1699_; lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_val_1690_ = lean_ctor_get(v___x_1689_, 0);
lean_inc(v_val_1690_);
lean_dec_ref_known(v___x_1689_, 1);
v___x_1707_ = lean_unsigned_to_nat(1u);
v___x_1708_ = lean_nat_add(v_size_1643_, v___x_1707_);
v___x_1709_ = lean_nat_dec_lt(v___x_1708_, v___x_1646_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
lean_dec(v___x_1708_);
lean_inc_ref(v_inst_1639_);
lean_inc_ref(v_inst_1638_);
v___x_1710_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1638_, v_inst_1639_, v_m_1640_);
v___y_1699_ = v___x_1710_;
goto v___jp_1698_;
}
else
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; uint8_t v___x_1715_; 
v___x_1711_ = lean_unsigned_to_nat(4u);
v___x_1712_ = lean_nat_mul(v___x_1708_, v___x_1711_);
lean_dec(v___x_1708_);
v___x_1713_ = lean_unsigned_to_nat(3u);
v___x_1714_ = lean_nat_mul(v___x_1646_, v___x_1713_);
v___x_1715_ = lean_nat_dec_le(v___x_1712_, v___x_1714_);
lean_dec(v___x_1714_);
lean_dec(v___x_1712_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; 
lean_inc_ref(v_inst_1639_);
lean_inc_ref(v_inst_1638_);
v___x_1716_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1638_, v_inst_1639_, v_m_1640_);
v___y_1699_ = v___x_1716_;
goto v___jp_1698_;
}
else
{
v___y_1699_ = v_m_1640_;
goto v___jp_1698_;
}
}
v___jp_1691_:
{
lean_object* v_size_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_size_1694_ = lean_ctor_get(v___y_1692_, 0);
v___x_1695_ = lean_unsigned_to_nat(1u);
v___x_1696_ = lean_nat_add(v_size_1694_, v___x_1695_);
v___x_1697_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1692_, v___x_1696_, v_i_1693_, v_a_1641_, v_val_1690_);
lean_dec(v_i_1693_);
return v___x_1697_;
}
v___jp_1698_:
{
lean_object* v___x_1700_; 
lean_inc(v_a_1641_);
v___x_1700_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1638_, v_inst_1639_, v___y_1699_, v_a_1641_);
switch(lean_obj_tag(v___x_1700_))
{
case 0:
{
lean_object* v_index_1701_; lean_object* v_size_1702_; lean_object* v___x_1703_; 
v_index_1701_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_index_1701_);
lean_dec_ref_known(v___x_1700_, 3);
v_size_1702_ = lean_ctor_get(v___y_1699_, 0);
lean_inc(v_size_1702_);
v___x_1703_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1699_, v_size_1702_, v_index_1701_, v_a_1641_, v_val_1690_);
lean_dec(v_index_1701_);
return v___x_1703_;
}
case 1:
{
lean_object* v_index_1704_; 
v_index_1704_ = lean_ctor_get(v___x_1700_, 0);
lean_inc(v_index_1704_);
lean_dec_ref_known(v___x_1700_, 1);
v___y_1692_ = v___y_1699_;
v_i_1693_ = v_index_1704_;
goto v___jp_1691_;
}
default: 
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1699_, v___x_1645_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_index_1706_; 
v_index_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_index_1706_);
lean_dec_ref_known(v___x_1705_, 1);
v___y_1692_ = v___y_1699_;
v_i_1693_ = v_index_1706_;
goto v___jp_1691_;
}
else
{
lean_dec(v_val_1690_);
lean_dec(v_a_1641_);
return v___y_1699_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_alter(lean_object* v_00_u03b1_1717_, lean_object* v_00_u03b2_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_inst_1721_, lean_object* v_m_1722_, lean_object* v_a_1723_, lean_object* v_f_1724_){
_start:
{
lean_object* v_size_1725_; lean_object* v_keyArray_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_size_1725_ = lean_ctor_get(v_m_1722_, 0);
v_keyArray_1726_ = lean_ctor_get(v_m_1722_, 1);
v___x_1727_ = lean_unsigned_to_nat(0u);
v___x_1728_ = lean_array_get_size(v_keyArray_1726_);
v___x_1729_ = lean_nat_dec_lt(v___x_1727_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v___x_1730_; 
lean_dec_ref(v_f_1724_);
lean_dec(v_a_1723_);
lean_dec_ref(v_m_1722_);
lean_dec_ref(v_inst_1721_);
lean_dec_ref(v_inst_1719_);
v___x_1730_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; 
lean_inc(v_a_1723_);
lean_inc_ref(v_inst_1721_);
lean_inc_ref(v_inst_1719_);
v___x_1731_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1719_, v_inst_1721_, v_m_1722_, v_a_1723_);
switch(lean_obj_tag(v___x_1731_))
{
case 0:
{
lean_object* v_index_1732_; lean_object* v_value_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
lean_dec_ref(v_inst_1721_);
lean_dec_ref(v_inst_1719_);
v_index_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_index_1732_);
v_value_1733_ = lean_ctor_get(v___x_1731_, 2);
lean_inc(v_value_1733_);
lean_dec_ref_known(v___x_1731_, 3);
v___x_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1734_, 0, v_value_1733_);
v___x_1735_ = lean_apply_1(v_f_1724_, v___x_1734_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
lean_dec(v_a_1723_);
v___x_1736_ = lean_unsigned_to_nat(1u);
v___x_1737_ = lean_nat_sub(v_size_1725_, v___x_1736_);
v___x_1738_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1722_, v___x_1737_, v_index_1732_);
lean_dec(v_index_1732_);
return v___x_1738_;
}
else
{
lean_object* v_val_1739_; lean_object* v___x_1740_; 
lean_inc(v_size_1725_);
v_val_1739_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_val_1739_);
lean_dec_ref_known(v___x_1735_, 1);
v___x_1740_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1722_, v_size_1725_, v_index_1732_, v_a_1723_, v_val_1739_);
lean_dec(v_index_1732_);
return v___x_1740_;
}
}
case 1:
{
lean_object* v_index_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v_index_1741_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_index_1741_);
lean_dec_ref_known(v___x_1731_, 1);
v___x_1742_ = lean_box(0);
v___x_1743_ = lean_apply_1(v_f_1724_, v___x_1742_);
if (lean_obj_tag(v___x_1743_) == 0)
{
lean_dec(v_index_1741_);
lean_dec(v_a_1723_);
lean_dec_ref(v_inst_1721_);
lean_dec_ref(v_inst_1719_);
return v_m_1722_;
}
else
{
lean_object* v_val_1744_; lean_object* v___y_1746_; lean_object* v_i_1747_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_val_1744_ = lean_ctor_get(v___x_1743_, 0);
lean_inc(v_val_1744_);
lean_dec_ref_known(v___x_1743_, 1);
v___x_1761_ = lean_unsigned_to_nat(1u);
v___x_1762_ = lean_nat_add(v_size_1725_, v___x_1761_);
v___x_1763_ = lean_nat_dec_lt(v___x_1762_, v___x_1728_);
if (v___x_1763_ == 0)
{
lean_dec(v___x_1762_);
lean_dec(v_index_1741_);
goto v___jp_1752_;
}
else
{
lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1764_ = lean_unsigned_to_nat(4u);
v___x_1765_ = lean_nat_mul(v___x_1762_, v___x_1764_);
v___x_1766_ = lean_unsigned_to_nat(3u);
v___x_1767_ = lean_nat_mul(v___x_1728_, v___x_1766_);
v___x_1768_ = lean_nat_dec_le(v___x_1765_, v___x_1767_);
lean_dec(v___x_1767_);
lean_dec(v___x_1765_);
if (v___x_1768_ == 0)
{
lean_dec(v___x_1762_);
lean_dec(v_index_1741_);
goto v___jp_1752_;
}
else
{
lean_object* v___x_1769_; 
lean_dec_ref(v_inst_1721_);
lean_dec_ref(v_inst_1719_);
v___x_1769_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1722_, v___x_1762_, v_index_1741_, v_a_1723_, v_val_1744_);
lean_dec(v_index_1741_);
return v___x_1769_;
}
}
v___jp_1745_:
{
lean_object* v_size_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; 
v_size_1748_ = lean_ctor_get(v___y_1746_, 0);
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = lean_nat_add(v_size_1748_, v___x_1749_);
v___x_1751_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1746_, v___x_1750_, v_i_1747_, v_a_1723_, v_val_1744_);
lean_dec(v_i_1747_);
return v___x_1751_;
}
v___jp_1752_:
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_inc_ref(v_inst_1721_);
lean_inc_ref(v_inst_1719_);
v___x_1753_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1719_, v_inst_1721_, v_m_1722_);
lean_inc(v_a_1723_);
v___x_1754_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1719_, v_inst_1721_, v___x_1753_, v_a_1723_);
switch(lean_obj_tag(v___x_1754_))
{
case 0:
{
lean_object* v_index_1755_; lean_object* v_size_1756_; lean_object* v___x_1757_; 
v_index_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_index_1755_);
lean_dec_ref_known(v___x_1754_, 3);
v_size_1756_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_size_1756_);
v___x_1757_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1753_, v_size_1756_, v_index_1755_, v_a_1723_, v_val_1744_);
lean_dec(v_index_1755_);
return v___x_1757_;
}
case 1:
{
lean_object* v_index_1758_; 
v_index_1758_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_index_1758_);
lean_dec_ref_known(v___x_1754_, 1);
v___y_1746_ = v___x_1753_;
v_i_1747_ = v_index_1758_;
goto v___jp_1745_;
}
default: 
{
lean_object* v___x_1759_; 
v___x_1759_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1753_, v___x_1727_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_index_1760_; 
v_index_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_index_1760_);
lean_dec_ref_known(v___x_1759_, 1);
v___y_1746_ = v___x_1753_;
v_i_1747_ = v_index_1760_;
goto v___jp_1745_;
}
else
{
lean_dec(v_val_1744_);
lean_dec(v_a_1723_);
return v___x_1753_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1770_ = lean_box(0);
v___x_1771_ = lean_apply_1(v_f_1724_, v___x_1770_);
if (lean_obj_tag(v___x_1771_) == 0)
{
lean_dec(v_a_1723_);
lean_dec_ref(v_inst_1721_);
lean_dec_ref(v_inst_1719_);
return v_m_1722_;
}
else
{
lean_object* v_val_1772_; lean_object* v___y_1774_; lean_object* v_i_1775_; lean_object* v___y_1781_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_val_1772_ = lean_ctor_get(v___x_1771_, 0);
lean_inc(v_val_1772_);
lean_dec_ref_known(v___x_1771_, 1);
v___x_1789_ = lean_unsigned_to_nat(1u);
v___x_1790_ = lean_nat_add(v_size_1725_, v___x_1789_);
v___x_1791_ = lean_nat_dec_lt(v___x_1790_, v___x_1728_);
if (v___x_1791_ == 0)
{
lean_object* v___x_1792_; 
lean_dec(v___x_1790_);
lean_inc_ref(v_inst_1721_);
lean_inc_ref(v_inst_1719_);
v___x_1792_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1719_, v_inst_1721_, v_m_1722_);
v___y_1781_ = v___x_1792_;
goto v___jp_1780_;
}
else
{
lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; uint8_t v___x_1797_; 
v___x_1793_ = lean_unsigned_to_nat(4u);
v___x_1794_ = lean_nat_mul(v___x_1790_, v___x_1793_);
lean_dec(v___x_1790_);
v___x_1795_ = lean_unsigned_to_nat(3u);
v___x_1796_ = lean_nat_mul(v___x_1728_, v___x_1795_);
v___x_1797_ = lean_nat_dec_le(v___x_1794_, v___x_1796_);
lean_dec(v___x_1796_);
lean_dec(v___x_1794_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
lean_inc_ref(v_inst_1721_);
lean_inc_ref(v_inst_1719_);
v___x_1798_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1719_, v_inst_1721_, v_m_1722_);
v___y_1781_ = v___x_1798_;
goto v___jp_1780_;
}
else
{
v___y_1781_ = v_m_1722_;
goto v___jp_1780_;
}
}
v___jp_1773_:
{
lean_object* v_size_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v_size_1776_ = lean_ctor_get(v___y_1774_, 0);
v___x_1777_ = lean_unsigned_to_nat(1u);
v___x_1778_ = lean_nat_add(v_size_1776_, v___x_1777_);
v___x_1779_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1774_, v___x_1778_, v_i_1775_, v_a_1723_, v_val_1772_);
lean_dec(v_i_1775_);
return v___x_1779_;
}
v___jp_1780_:
{
lean_object* v___x_1782_; 
lean_inc(v_a_1723_);
v___x_1782_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1719_, v_inst_1721_, v___y_1781_, v_a_1723_);
switch(lean_obj_tag(v___x_1782_))
{
case 0:
{
lean_object* v_index_1783_; lean_object* v_size_1784_; lean_object* v___x_1785_; 
v_index_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_index_1783_);
lean_dec_ref_known(v___x_1782_, 3);
v_size_1784_ = lean_ctor_get(v___y_1781_, 0);
lean_inc(v_size_1784_);
v___x_1785_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1781_, v_size_1784_, v_index_1783_, v_a_1723_, v_val_1772_);
lean_dec(v_index_1783_);
return v___x_1785_;
}
case 1:
{
lean_object* v_index_1786_; 
v_index_1786_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_index_1786_);
lean_dec_ref_known(v___x_1782_, 1);
v___y_1774_ = v___y_1781_;
v_i_1775_ = v_index_1786_;
goto v___jp_1773_;
}
default: 
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1781_, v___x_1727_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_index_1788_; 
v_index_1788_ = lean_ctor_get(v___x_1787_, 0);
lean_inc(v_index_1788_);
lean_dec_ref_known(v___x_1787_, 1);
v___y_1774_ = v___y_1781_;
v_i_1775_ = v_index_1788_;
goto v___jp_1773_;
}
else
{
lean_dec(v_val_1772_);
lean_dec(v_a_1723_);
return v___y_1781_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify___redArg(lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_m_1801_, lean_object* v_a_1802_, lean_object* v_f_1803_){
_start:
{
lean_object* v_size_1804_; lean_object* v_keyArray_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; uint8_t v___x_1808_; 
v_size_1804_ = lean_ctor_get(v_m_1801_, 0);
v_keyArray_1805_ = lean_ctor_get(v_m_1801_, 1);
v___x_1806_ = lean_unsigned_to_nat(0u);
v___x_1807_ = lean_array_get_size(v_keyArray_1805_);
v___x_1808_ = lean_nat_dec_lt(v___x_1806_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
lean_dec(v_f_1803_);
lean_dec(v_a_1802_);
lean_dec_ref(v_m_1801_);
lean_dec_ref(v_inst_1800_);
lean_dec_ref(v_inst_1799_);
v___x_1809_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_1809_;
}
else
{
lean_object* v___x_1810_; 
lean_inc(v_a_1802_);
v___x_1810_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1799_, v_inst_1800_, v_m_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v_index_1811_; lean_object* v_value_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
lean_inc(v_size_1804_);
v_index_1811_ = lean_ctor_get(v___x_1810_, 0);
lean_inc(v_index_1811_);
v_value_1812_ = lean_ctor_get(v___x_1810_, 2);
lean_inc(v_value_1812_);
lean_dec_ref_known(v___x_1810_, 3);
v___x_1813_ = lean_apply_1(v_f_1803_, v_value_1812_);
v___x_1814_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1801_, v_size_1804_, v_index_1811_, v_a_1802_, v___x_1813_);
lean_dec(v_index_1811_);
return v___x_1814_;
}
else
{
lean_dec(v___x_1810_);
lean_dec(v_f_1803_);
lean_dec(v_a_1802_);
return v_m_1801_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_modify(lean_object* v_00_u03b1_1815_, lean_object* v_00_u03b2_1816_, lean_object* v_inst_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_m_1820_, lean_object* v_a_1821_, lean_object* v_f_1822_){
_start:
{
lean_object* v_size_1823_; lean_object* v_keyArray_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; uint8_t v___x_1827_; 
v_size_1823_ = lean_ctor_get(v_m_1820_, 0);
v_keyArray_1824_ = lean_ctor_get(v_m_1820_, 1);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = lean_array_get_size(v_keyArray_1824_);
v___x_1827_ = lean_nat_dec_lt(v___x_1825_, v___x_1826_);
if (v___x_1827_ == 0)
{
lean_object* v___x_1828_; 
lean_dec(v_f_1822_);
lean_dec(v_a_1821_);
lean_dec_ref(v_m_1820_);
lean_dec_ref(v_inst_1819_);
lean_dec_ref(v_inst_1817_);
v___x_1828_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_1828_;
}
else
{
lean_object* v___x_1829_; 
lean_inc(v_a_1821_);
v___x_1829_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1817_, v_inst_1819_, v_m_1820_, v_a_1821_);
if (lean_obj_tag(v___x_1829_) == 0)
{
lean_object* v_index_1830_; lean_object* v_value_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_inc(v_size_1823_);
v_index_1830_ = lean_ctor_get(v___x_1829_, 0);
lean_inc(v_index_1830_);
v_value_1831_ = lean_ctor_get(v___x_1829_, 2);
lean_inc(v_value_1831_);
lean_dec_ref_known(v___x_1829_, 3);
v___x_1832_ = lean_apply_1(v_f_1822_, v_value_1831_);
v___x_1833_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1820_, v_size_1823_, v_index_1830_, v_a_1821_, v___x_1832_);
lean_dec(v_index_1830_);
return v___x_1833_;
}
else
{
lean_dec(v___x_1829_);
lean_dec(v_f_1822_);
lean_dec(v_a_1821_);
return v_m_1820_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___lam__0(lean_object* v_x1_1834_, lean_object* v_x2_1835_, lean_object* v_x3_1836_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_x2_1835_);
lean_ctor_set(v___x_1837_, 1, v_x3_1836_);
v___x_1838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1837_);
lean_ctor_set(v___x_1838_, 1, v_x1_1834_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg(lean_object* v_m_1840_){
_start:
{
lean_object* v___f_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___f_1841_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__0));
v___x_1842_ = lean_box(0);
v___x_1843_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_1843_, v___f_1841_, v_m_1840_, v___x_1842_, v___x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___redArg___boxed(lean_object* v_m_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Std_HashMap_Raw_toList___redArg(v_m_1846_);
lean_dec_ref(v_m_1846_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList(lean_object* v_00_u03b1_1848_, lean_object* v_00_u03b2_1849_, lean_object* v_m_1850_){
_start:
{
lean_object* v___f_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___f_1851_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__0));
v___x_1852_ = lean_box(0);
v___x_1853_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_1853_, v___f_1851_, v_m_1850_, v___x_1852_, v___x_1854_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toList___boxed(lean_object* v_00_u03b1_1856_, lean_object* v_00_u03b2_1857_, lean_object* v_m_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Std_HashMap_Raw_toList(v_00_u03b1_1856_, v_00_u03b2_1857_, v_m_1858_);
lean_dec_ref(v_m_1858_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM___redArg(lean_object* v_inst_1860_, lean_object* v_f_1861_, lean_object* v_init_1862_, lean_object* v_b_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1860_, v_f_1861_, v_init_1862_, v_b_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_foldM(lean_object* v_00_u03b1_1865_, lean_object* v_00_u03b2_1866_, lean_object* v_m_1867_, lean_object* v_inst_1868_, lean_object* v_00_u03b3_1869_, lean_object* v_f_1870_, lean_object* v_init_1871_, lean_object* v_b_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1868_, v_f_1870_, v_init_1871_, v_b_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg___lam__0(lean_object* v_f_1874_, lean_object* v_x1_1875_, lean_object* v_x2_1876_, lean_object* v_x3_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_apply_3(v_f_1874_, v_x1_1875_, v_x2_1876_, v_x3_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold___redArg(lean_object* v_f_1879_, lean_object* v_init_1880_, lean_object* v_b_1881_){
_start:
{
lean_object* v___f_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___f_1882_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1882_, 0, v_f_1879_);
v___x_1883_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_1884_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1883_, v___f_1882_, v_init_1880_, v_b_1881_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_fold(lean_object* v_00_u03b1_1885_, lean_object* v_00_u03b2_1886_, lean_object* v_00_u03b3_1887_, lean_object* v_f_1888_, lean_object* v_init_1889_, lean_object* v_b_1890_){
_start:
{
lean_object* v___f_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___f_1891_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_fold___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1891_, 0, v_f_1888_);
v___x_1892_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_1893_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_1892_, v___f_1891_, v_init_1889_, v_b_1890_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg___lam__0(lean_object* v_f_1894_, lean_object* v_x_1895_, lean_object* v_a_1896_, lean_object* v_v_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_apply_2(v_f_1894_, v_a_1896_, v_v_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM___redArg(lean_object* v_inst_1899_, lean_object* v_f_1900_, lean_object* v_b_1901_){
_start:
{
lean_object* v___f_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___f_1902_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1902_, 0, v_f_1900_);
v___x_1903_ = lean_box(0);
v___x_1904_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1899_, v___f_1902_, v___x_1903_, v_b_1901_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forM(lean_object* v_00_u03b1_1905_, lean_object* v_00_u03b2_1906_, lean_object* v_m_1907_, lean_object* v_inst_1908_, lean_object* v_f_1909_, lean_object* v_b_1910_){
_start:
{
lean_object* v___f_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___f_1911_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1911_, 0, v_f_1909_);
v___x_1912_ = lean_box(0);
v___x_1913_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1908_, v___f_1911_, v___x_1912_, v_b_1910_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn___redArg(lean_object* v_inst_1914_, lean_object* v_f_1915_, lean_object* v_init_1916_, lean_object* v_b_1917_){
_start:
{
lean_object* v___x_1918_; 
v___x_1918_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_1914_, v_f_1915_, v_init_1916_, v_b_1917_);
return v___x_1918_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_forIn(lean_object* v_00_u03b1_1919_, lean_object* v_00_u03b2_1920_, lean_object* v_m_1921_, lean_object* v_inst_1922_, lean_object* v_00_u03b3_1923_, lean_object* v_f_1924_, lean_object* v_init_1925_, lean_object* v_b_1926_){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_1922_, v_f_1924_, v_init_1925_, v_b_1926_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0(lean_object* v_f_1928_, lean_object* v_x_1929_, lean_object* v_a_1930_, lean_object* v_v_1931_){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v_a_1930_);
lean_ctor_set(v___x_1932_, 1, v_v_1931_);
v___x_1933_ = lean_apply_1(v_f_1928_, v___x_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__1(lean_object* v_inst_1934_, lean_object* v_m_1935_, lean_object* v_f_1936_){
_start:
{
lean_object* v___f_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___f_1937_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1937_, 0, v_f_1936_);
v___x_1938_ = lean_box(0);
v___x_1939_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_1934_, v___f_1937_, v___x_1938_, v_m_1935_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad___redArg(lean_object* v_inst_1940_){
_start:
{
lean_object* v___f_1941_; 
v___f_1941_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1941_, 0, v_inst_1940_);
return v___f_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForMProdOfMonad(lean_object* v_00_u03b1_1942_, lean_object* v_00_u03b2_1943_, lean_object* v_m_1944_, lean_object* v_inst_1945_){
_start:
{
lean_object* v___f_1946_; 
v___f_1946_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForMProdOfMonad___redArg___lam__1), 3, 1);
lean_closure_set(v___f_1946_, 0, v_inst_1945_);
return v___f_1946_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0(lean_object* v_f_1947_, lean_object* v_a_1948_, lean_object* v_b_1949_, lean_object* v_acc_1950_){
_start:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v_a_1948_);
lean_ctor_set(v___x_1951_, 1, v_b_1949_);
v___x_1952_ = lean_apply_2(v_f_1947_, v___x_1951_, v_acc_1950_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1(lean_object* v_inst_1953_, lean_object* v_00_u03b2_1954_, lean_object* v_m_1955_, lean_object* v_init_1956_, lean_object* v_f_1957_){
_start:
{
lean_object* v___f_1958_; lean_object* v___x_1959_; 
v___f_1958_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_1958_, 0, v_f_1957_);
v___x_1959_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_1953_, v___f_1958_, v_init_1956_, v_m_1955_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad___redArg(lean_object* v_inst_1960_){
_start:
{
lean_object* v___f_1961_; 
v___f_1961_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1961_, 0, v_inst_1960_);
return v___f_1961_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instForInProdOfMonad(lean_object* v_00_u03b1_1962_, lean_object* v_00_u03b2_1963_, lean_object* v_m_1964_, lean_object* v_inst_1965_){
_start:
{
lean_object* v___f_1966_; 
v___f_1966_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instForInProdOfMonad___redArg___lam__1), 5, 1);
lean_closure_set(v___f_1966_, 0, v_inst_1965_);
return v___f_1966_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0(lean_object* v_p_1967_, lean_object* v___x_1968_, lean_object* v___x_1969_, lean_object* v_a_1970_, lean_object* v_b_1971_, lean_object* v_acc_1972_){
_start:
{
lean_object* v___x_1973_; uint8_t v___x_1974_; 
v___x_1973_ = lean_apply_2(v_p_1967_, v_a_1970_, v_b_1971_);
v___x_1974_ = lean_unbox(v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec_ref(v___x_1969_);
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v___x_1968_);
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
return v___x_1977_;
}
else
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1969_);
return v___x_1978_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___lam__0___boxed(lean_object* v_p_1979_, lean_object* v___x_1980_, lean_object* v___x_1981_, lean_object* v_a_1982_, lean_object* v_b_1983_, lean_object* v_acc_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Std_HashMap_Raw_all___redArg___lam__0(v_p_1979_, v___x_1980_, v___x_1981_, v_a_1982_, v_b_1983_, v_acc_1984_);
lean_dec_ref(v_acc_1984_);
return v_res_1985_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all___redArg(lean_object* v_m_1989_, lean_object* v_p_1990_){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___f_1994_; lean_object* v___x_1995_; lean_object* v_fst_1996_; 
v___x_1991_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_1992_ = lean_box(0);
v___x_1993_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_1994_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1994_, 0, v_p_1990_);
lean_closure_set(v___f_1994_, 1, v___x_1992_);
lean_closure_set(v___f_1994_, 2, v___x_1993_);
v___x_1995_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_1991_, v___f_1994_, v___x_1993_, v_m_1989_);
v_fst_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_fst_1996_);
lean_dec(v___x_1995_);
if (lean_obj_tag(v_fst_1996_) == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = 1;
return v___x_1997_;
}
else
{
lean_object* v_val_1998_; uint8_t v___x_1999_; 
v_val_1998_ = lean_ctor_get(v_fst_1996_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v_fst_1996_, 1);
v___x_1999_ = lean_unbox(v_val_1998_);
lean_dec(v_val_1998_);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___redArg___boxed(lean_object* v_m_2000_, lean_object* v_p_2001_){
_start:
{
uint8_t v_res_2002_; lean_object* v_r_2003_; 
v_res_2002_ = l_Std_HashMap_Raw_all___redArg(v_m_2000_, v_p_2001_);
v_r_2003_ = lean_box(v_res_2002_);
return v_r_2003_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_all(lean_object* v_00_u03b1_2004_, lean_object* v_00_u03b2_2005_, lean_object* v_m_2006_, lean_object* v_p_2007_){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___f_2011_; lean_object* v___x_2012_; lean_object* v_fst_2013_; 
v___x_2008_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2009_ = lean_box(0);
v___x_2010_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_2011_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2011_, 0, v_p_2007_);
lean_closure_set(v___f_2011_, 1, v___x_2009_);
lean_closure_set(v___f_2011_, 2, v___x_2010_);
v___x_2012_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2008_, v___f_2011_, v___x_2010_, v_m_2006_);
v_fst_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_fst_2013_);
lean_dec(v___x_2012_);
if (lean_obj_tag(v_fst_2013_) == 0)
{
uint8_t v___x_2014_; 
v___x_2014_ = 1;
return v___x_2014_;
}
else
{
lean_object* v_val_2015_; uint8_t v___x_2016_; 
v_val_2015_ = lean_ctor_get(v_fst_2013_, 0);
lean_inc(v_val_2015_);
lean_dec_ref_known(v_fst_2013_, 1);
v___x_2016_ = lean_unbox(v_val_2015_);
lean_dec(v_val_2015_);
return v___x_2016_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_all___boxed(lean_object* v_00_u03b1_2017_, lean_object* v_00_u03b2_2018_, lean_object* v_m_2019_, lean_object* v_p_2020_){
_start:
{
uint8_t v_res_2021_; lean_object* v_r_2022_; 
v_res_2021_ = l_Std_HashMap_Raw_all(v_00_u03b1_2017_, v_00_u03b2_2018_, v_m_2019_, v_p_2020_);
v_r_2022_ = lean_box(v_res_2021_);
return v_r_2022_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0(lean_object* v_p_2023_, lean_object* v___x_2024_, lean_object* v___x_2025_, lean_object* v_a_2026_, lean_object* v_b_2027_, lean_object* v_acc_2028_){
_start:
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = lean_apply_2(v_p_2023_, v_a_2026_, v_b_2027_);
v___x_2030_ = lean_unbox(v___x_2029_);
if (v___x_2030_ == 0)
{
lean_object* v___x_2031_; 
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2024_);
return v___x_2031_;
}
else
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec_ref(v___x_2024_);
v___x_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2029_);
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v___x_2025_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
return v___x_2034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___lam__0___boxed(lean_object* v_p_2035_, lean_object* v___x_2036_, lean_object* v___x_2037_, lean_object* v_a_2038_, lean_object* v_b_2039_, lean_object* v_acc_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Std_HashMap_Raw_any___redArg___lam__0(v_p_2035_, v___x_2036_, v___x_2037_, v_a_2038_, v_b_2039_, v_acc_2040_);
lean_dec_ref(v_acc_2040_);
return v_res_2041_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any___redArg(lean_object* v_m_2042_, lean_object* v_p_2043_){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___f_2047_; lean_object* v___x_2048_; lean_object* v_fst_2049_; 
v___x_2044_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2045_ = lean_box(0);
v___x_2046_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_2047_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2047_, 0, v_p_2043_);
lean_closure_set(v___f_2047_, 1, v___x_2046_);
lean_closure_set(v___f_2047_, 2, v___x_2045_);
v___x_2048_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2044_, v___f_2047_, v___x_2046_, v_m_2042_);
v_fst_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_fst_2049_);
lean_dec(v___x_2048_);
if (lean_obj_tag(v_fst_2049_) == 0)
{
uint8_t v___x_2050_; 
v___x_2050_ = 0;
return v___x_2050_;
}
else
{
lean_object* v_val_2051_; uint8_t v___x_2052_; 
v_val_2051_ = lean_ctor_get(v_fst_2049_, 0);
lean_inc(v_val_2051_);
lean_dec_ref_known(v_fst_2049_, 1);
v___x_2052_ = lean_unbox(v_val_2051_);
lean_dec(v_val_2051_);
return v___x_2052_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___redArg___boxed(lean_object* v_m_2053_, lean_object* v_p_2054_){
_start:
{
uint8_t v_res_2055_; lean_object* v_r_2056_; 
v_res_2055_ = l_Std_HashMap_Raw_any___redArg(v_m_2053_, v_p_2054_);
v_r_2056_ = lean_box(v_res_2055_);
return v_r_2056_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_any(lean_object* v_00_u03b1_2057_, lean_object* v_00_u03b2_2058_, lean_object* v_m_2059_, lean_object* v_p_2060_){
_start:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___f_2064_; lean_object* v___x_2065_; lean_object* v_fst_2066_; 
v___x_2061_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2062_ = lean_box(0);
v___x_2063_ = ((lean_object*)(l_Std_HashMap_Raw_all___redArg___closed__0));
v___f_2064_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_2064_, 0, v_p_2060_);
lean_closure_set(v___f_2064_, 1, v___x_2063_);
lean_closure_set(v___f_2064_, 2, v___x_2062_);
v___x_2065_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2061_, v___f_2064_, v___x_2063_, v_m_2059_);
v_fst_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_fst_2066_);
lean_dec(v___x_2065_);
if (lean_obj_tag(v_fst_2066_) == 0)
{
uint8_t v___x_2067_; 
v___x_2067_ = 0;
return v___x_2067_;
}
else
{
lean_object* v_val_2068_; uint8_t v___x_2069_; 
v_val_2068_ = lean_ctor_get(v_fst_2066_, 0);
lean_inc(v_val_2068_);
lean_dec_ref_known(v_fst_2066_, 1);
v___x_2069_ = lean_unbox(v_val_2068_);
lean_dec(v_val_2068_);
return v___x_2069_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_any___boxed(lean_object* v_00_u03b1_2070_, lean_object* v_00_u03b2_2071_, lean_object* v_m_2072_, lean_object* v_p_2073_){
_start:
{
uint8_t v_res_2074_; lean_object* v_r_2075_; 
v_res_2074_ = l_Std_HashMap_Raw_any(v_00_u03b1_2070_, v_00_u03b2_2071_, v_m_2072_, v_p_2073_);
v_r_2075_ = lean_box(v_res_2074_);
return v_r_2075_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg___lam__0(lean_object* v_inst_2076_, lean_object* v_inst_2077_, lean_object* v_a_2078_, lean_object* v_b_2079_, lean_object* v_acc_2080_){
_start:
{
lean_object* v___y_2082_; lean_object* v_i_2083_; lean_object* v___y_2102_; lean_object* v_i_2103_; lean_object* v___y_2110_; lean_object* v___x_2121_; 
lean_inc(v_a_2078_);
lean_inc_ref(v_inst_2077_);
lean_inc_ref(v_inst_2076_);
v___x_2121_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2076_, v_inst_2077_, v_acc_2080_, v_a_2078_);
switch(lean_obj_tag(v___x_2121_))
{
case 0:
{
lean_object* v___x_2122_; 
lean_dec_ref_known(v___x_2121_, 3);
lean_dec(v_b_2079_);
lean_dec(v_a_2078_);
lean_dec_ref(v_inst_2077_);
lean_dec_ref(v_inst_2076_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v_acc_2080_);
return v___x_2122_;
}
case 1:
{
lean_object* v_index_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2142_; 
v_index_2123_ = lean_ctor_get(v___x_2121_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2121_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2125_ = v___x_2121_;
v_isShared_2126_ = v_isSharedCheck_2142_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_index_2123_);
lean_dec(v___x_2121_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2142_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_size_2127_; lean_object* v_keyArray_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; uint8_t v___x_2132_; 
v_size_2127_ = lean_ctor_get(v_acc_2080_, 0);
v_keyArray_2128_ = lean_ctor_get(v_acc_2080_, 1);
v___x_2129_ = lean_unsigned_to_nat(1u);
v___x_2130_ = lean_nat_add(v_size_2127_, v___x_2129_);
v___x_2131_ = lean_array_get_size(v_keyArray_2128_);
v___x_2132_ = lean_nat_dec_lt(v___x_2130_, v___x_2131_);
if (v___x_2132_ == 0)
{
lean_dec(v___x_2130_);
lean_del_object(v___x_2125_);
lean_dec(v_index_2123_);
goto v___jp_2089_;
}
else
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; uint8_t v___x_2137_; 
v___x_2133_ = lean_unsigned_to_nat(4u);
v___x_2134_ = lean_nat_mul(v___x_2130_, v___x_2133_);
v___x_2135_ = lean_unsigned_to_nat(3u);
v___x_2136_ = lean_nat_mul(v___x_2131_, v___x_2135_);
v___x_2137_ = lean_nat_dec_le(v___x_2134_, v___x_2136_);
lean_dec(v___x_2136_);
lean_dec(v___x_2134_);
if (v___x_2137_ == 0)
{
lean_dec(v___x_2130_);
lean_del_object(v___x_2125_);
lean_dec(v_index_2123_);
goto v___jp_2089_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
lean_dec_ref(v_inst_2077_);
lean_dec_ref(v_inst_2076_);
v___x_2138_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2080_, v___x_2130_, v_index_2123_, v_a_2078_, v_b_2079_);
lean_dec(v_index_2123_);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2138_);
v___x_2140_ = v___x_2125_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2138_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
}
default: 
{
lean_object* v_size_2143_; lean_object* v_keyArray_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
v_size_2143_ = lean_ctor_get(v_acc_2080_, 0);
v_keyArray_2144_ = lean_ctor_get(v_acc_2080_, 1);
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_add(v_size_2143_, v___x_2145_);
v___x_2147_ = lean_array_get_size(v_keyArray_2144_);
v___x_2148_ = lean_nat_dec_lt(v___x_2146_, v___x_2147_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; 
lean_dec(v___x_2146_);
lean_inc_ref(v_inst_2077_);
lean_inc_ref(v_inst_2076_);
v___x_2149_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2076_, v_inst_2077_, v_acc_2080_);
v___y_2110_ = v___x_2149_;
goto v___jp_2109_;
}
else
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; 
v___x_2150_ = lean_unsigned_to_nat(4u);
v___x_2151_ = lean_nat_mul(v___x_2146_, v___x_2150_);
lean_dec(v___x_2146_);
v___x_2152_ = lean_unsigned_to_nat(3u);
v___x_2153_ = lean_nat_mul(v___x_2147_, v___x_2152_);
v___x_2154_ = lean_nat_dec_le(v___x_2151_, v___x_2153_);
lean_dec(v___x_2153_);
lean_dec(v___x_2151_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; 
lean_inc_ref(v_inst_2077_);
lean_inc_ref(v_inst_2076_);
v___x_2155_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2076_, v_inst_2077_, v_acc_2080_);
v___y_2110_ = v___x_2155_;
goto v___jp_2109_;
}
else
{
v___y_2110_ = v_acc_2080_;
goto v___jp_2109_;
}
}
}
}
v___jp_2081_:
{
lean_object* v_size_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v_size_2084_ = lean_ctor_get(v___y_2082_, 0);
v___x_2085_ = lean_unsigned_to_nat(1u);
v___x_2086_ = lean_nat_add(v_size_2084_, v___x_2085_);
v___x_2087_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2082_, v___x_2086_, v_i_2083_, v_a_2078_, v_b_2079_);
lean_dec(v_i_2083_);
v___x_2088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
v___jp_2089_:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
lean_inc_ref(v_inst_2077_);
lean_inc_ref(v_inst_2076_);
v___x_2090_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2076_, v_inst_2077_, v_acc_2080_);
lean_inc(v_a_2078_);
v___x_2091_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2076_, v_inst_2077_, v___x_2090_, v_a_2078_);
switch(lean_obj_tag(v___x_2091_))
{
case 0:
{
lean_object* v_index_2092_; lean_object* v_size_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v_index_2092_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_index_2092_);
lean_dec_ref_known(v___x_2091_, 3);
v_size_2093_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_size_2093_);
v___x_2094_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2090_, v_size_2093_, v_index_2092_, v_a_2078_, v_b_2079_);
lean_dec(v_index_2092_);
v___x_2095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
return v___x_2095_;
}
case 1:
{
lean_object* v_index_2096_; 
v_index_2096_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_index_2096_);
lean_dec_ref_known(v___x_2091_, 1);
v___y_2082_ = v___x_2090_;
v_i_2083_ = v_index_2096_;
goto v___jp_2081_;
}
default: 
{
lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2090_, v___x_2097_);
if (lean_obj_tag(v___x_2098_) == 0)
{
lean_object* v_index_2099_; 
v_index_2099_ = lean_ctor_get(v___x_2098_, 0);
lean_inc(v_index_2099_);
lean_dec_ref_known(v___x_2098_, 1);
v___y_2082_ = v___x_2090_;
v_i_2083_ = v_index_2099_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2100_; 
lean_dec(v_b_2079_);
lean_dec(v_a_2078_);
v___x_2100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2100_, 0, v___x_2090_);
return v___x_2100_;
}
}
}
}
v___jp_2101_:
{
lean_object* v_size_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v_size_2104_ = lean_ctor_get(v___y_2102_, 0);
v___x_2105_ = lean_unsigned_to_nat(1u);
v___x_2106_ = lean_nat_add(v_size_2104_, v___x_2105_);
v___x_2107_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2102_, v___x_2106_, v_i_2103_, v_a_2078_, v_b_2079_);
lean_dec(v_i_2103_);
v___x_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2108_, 0, v___x_2107_);
return v___x_2108_;
}
v___jp_2109_:
{
lean_object* v___x_2111_; 
lean_inc(v_a_2078_);
v___x_2111_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2076_, v_inst_2077_, v___y_2110_, v_a_2078_);
switch(lean_obj_tag(v___x_2111_))
{
case 0:
{
lean_object* v_index_2112_; lean_object* v_size_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_index_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_index_2112_);
lean_dec_ref_known(v___x_2111_, 3);
v_size_2113_ = lean_ctor_get(v___y_2110_, 0);
lean_inc(v_size_2113_);
v___x_2114_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2110_, v_size_2113_, v_index_2112_, v_a_2078_, v_b_2079_);
lean_dec(v_index_2112_);
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
return v___x_2115_;
}
case 1:
{
lean_object* v_index_2116_; 
v_index_2116_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_index_2116_);
lean_dec_ref_known(v___x_2111_, 1);
v___y_2102_ = v___y_2110_;
v_i_2103_ = v_index_2116_;
goto v___jp_2101_;
}
default: 
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2110_, v___x_2117_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_index_2119_; 
v_index_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_index_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___y_2102_ = v___y_2110_;
v_i_2103_ = v_index_2119_;
goto v___jp_2101_;
}
else
{
lean_object* v___x_2120_; 
lean_dec(v_b_2079_);
lean_dec(v_a_2078_);
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___y_2110_);
return v___x_2120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union___redArg(lean_object* v_inst_2158_, lean_object* v_inst_2159_, lean_object* v_m_u2081_2160_, lean_object* v_m_u2082_2161_){
_start:
{
lean_object* v_size_2162_; lean_object* v_keyArray_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; uint8_t v___x_2166_; 
v_size_2162_ = lean_ctor_get(v_m_u2081_2160_, 0);
v_keyArray_2163_ = lean_ctor_get(v_m_u2081_2160_, 1);
v___x_2164_ = lean_unsigned_to_nat(0u);
v___x_2165_ = lean_array_get_size(v_keyArray_2163_);
v___x_2166_ = lean_nat_dec_lt(v___x_2164_, v___x_2165_);
if (v___x_2166_ == 0)
{
lean_dec_ref(v_m_u2081_2160_);
lean_dec_ref(v_inst_2159_);
lean_dec_ref(v_inst_2158_);
return v_m_u2082_2161_;
}
else
{
lean_object* v_size_2167_; lean_object* v_keyArray_2168_; lean_object* v___x_2169_; uint8_t v___x_2170_; 
v_size_2167_ = lean_ctor_get(v_m_u2082_2161_, 0);
v_keyArray_2168_ = lean_ctor_get(v_m_u2082_2161_, 1);
v___x_2169_ = lean_array_get_size(v_keyArray_2168_);
v___x_2170_ = lean_nat_dec_lt(v___x_2164_, v___x_2169_);
if (v___x_2170_ == 0)
{
lean_dec_ref(v_m_u2082_2161_);
lean_dec_ref(v_inst_2159_);
lean_dec_ref(v_inst_2158_);
return v_m_u2081_2160_;
}
else
{
uint8_t v___x_2171_; 
v___x_2171_ = lean_nat_dec_le(v_size_2162_, v_size_2167_);
if (v___x_2171_ == 0)
{
lean_object* v___f_2172_; lean_object* v___x_2173_; 
v___f_2172_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_2173_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2172_, v_inst_2158_, v_inst_2159_, v_m_u2081_2160_, v_m_u2082_2161_);
return v___x_2173_;
}
else
{
lean_object* v___f_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___f_2174_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2174_, 0, v_inst_2158_);
lean_closure_set(v___f_2174_, 1, v_inst_2159_);
v___x_2175_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2176_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2175_, v___f_2174_, v_m_u2082_2161_, v_m_u2081_2160_);
return v___x_2176_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_union(lean_object* v_00_u03b1_2177_, lean_object* v_00_u03b2_2178_, lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_m_u2081_2181_, lean_object* v_m_u2082_2182_){
_start:
{
lean_object* v_size_2183_; lean_object* v_keyArray_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v_size_2183_ = lean_ctor_get(v_m_u2081_2181_, 0);
v_keyArray_2184_ = lean_ctor_get(v_m_u2081_2181_, 1);
v___x_2185_ = lean_unsigned_to_nat(0u);
v___x_2186_ = lean_array_get_size(v_keyArray_2184_);
v___x_2187_ = lean_nat_dec_lt(v___x_2185_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_dec_ref(v_m_u2081_2181_);
lean_dec_ref(v_inst_2180_);
lean_dec_ref(v_inst_2179_);
return v_m_u2082_2182_;
}
else
{
lean_object* v_size_2188_; lean_object* v_keyArray_2189_; lean_object* v___x_2190_; uint8_t v___x_2191_; 
v_size_2188_ = lean_ctor_get(v_m_u2082_2182_, 0);
v_keyArray_2189_ = lean_ctor_get(v_m_u2082_2182_, 1);
v___x_2190_ = lean_array_get_size(v_keyArray_2189_);
v___x_2191_ = lean_nat_dec_lt(v___x_2185_, v___x_2190_);
if (v___x_2191_ == 0)
{
lean_dec_ref(v_m_u2082_2182_);
lean_dec_ref(v_inst_2180_);
lean_dec_ref(v_inst_2179_);
return v_m_u2081_2181_;
}
else
{
uint8_t v___x_2192_; 
v___x_2192_ = lean_nat_dec_le(v_size_2183_, v_size_2188_);
if (v___x_2192_ == 0)
{
lean_object* v___f_2193_; lean_object* v___x_2194_; 
v___f_2193_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_2194_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2193_, v_inst_2179_, v_inst_2180_, v_m_u2081_2181_, v_m_u2082_2182_);
return v___x_2194_;
}
else
{
lean_object* v___f_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___f_2195_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2195_, 0, v_inst_2179_);
lean_closure_set(v___f_2195_, 1, v_inst_2180_);
v___x_2196_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2197_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2196_, v___f_2195_, v_m_u2082_2182_, v_m_u2081_2181_);
return v___x_2197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter___redArg(lean_object* v_inst_2198_, lean_object* v_inst_2199_, lean_object* v_m_u2081_2200_, lean_object* v_m_u2082_2201_){
_start:
{
lean_object* v_keyArray_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; uint8_t v___x_2205_; 
v_keyArray_2202_ = lean_ctor_get(v_m_u2081_2200_, 1);
v___x_2203_ = lean_unsigned_to_nat(0u);
v___x_2204_ = lean_array_get_size(v_keyArray_2202_);
v___x_2205_ = lean_nat_dec_lt(v___x_2203_, v___x_2204_);
if (v___x_2205_ == 0)
{
lean_dec_ref(v_m_u2081_2200_);
lean_dec_ref(v_inst_2199_);
lean_dec_ref(v_inst_2198_);
return v_m_u2082_2201_;
}
else
{
lean_object* v_keyArray_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; 
v_keyArray_2206_ = lean_ctor_get(v_m_u2082_2201_, 1);
v___x_2207_ = lean_array_get_size(v_keyArray_2206_);
v___x_2208_ = lean_nat_dec_lt(v___x_2203_, v___x_2207_);
if (v___x_2208_ == 0)
{
lean_dec_ref(v_m_u2082_2201_);
lean_dec_ref(v_inst_2199_);
lean_dec_ref(v_inst_2198_);
return v_m_u2081_2200_;
}
else
{
lean_object* v___x_2209_; 
v___x_2209_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2198_, v_inst_2199_, v_m_u2081_2200_, v_m_u2082_2201_);
return v___x_2209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_inter(lean_object* v_00_u03b1_2210_, lean_object* v_00_u03b2_2211_, lean_object* v_inst_2212_, lean_object* v_inst_2213_, lean_object* v_m_u2081_2214_, lean_object* v_m_u2082_2215_){
_start:
{
lean_object* v_keyArray_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; uint8_t v___x_2219_; 
v_keyArray_2216_ = lean_ctor_get(v_m_u2081_2214_, 1);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_array_get_size(v_keyArray_2216_);
v___x_2219_ = lean_nat_dec_lt(v___x_2217_, v___x_2218_);
if (v___x_2219_ == 0)
{
lean_dec_ref(v_m_u2081_2214_);
lean_dec_ref(v_inst_2213_);
lean_dec_ref(v_inst_2212_);
return v_m_u2082_2215_;
}
else
{
lean_object* v_keyArray_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v_keyArray_2220_ = lean_ctor_get(v_m_u2082_2215_, 1);
v___x_2221_ = lean_array_get_size(v_keyArray_2220_);
v___x_2222_ = lean_nat_dec_lt(v___x_2217_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_dec_ref(v_m_u2082_2215_);
lean_dec_ref(v_inst_2213_);
lean_dec_ref(v_inst_2212_);
return v_m_u2081_2214_;
}
else
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2212_, v_inst_2213_, v_m_u2081_2214_, v_m_u2082_2215_);
return v___x_2223_;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_2224_, lean_object* v_inst_2225_, lean_object* v_m_u2082_2226_, uint8_t v___x_2227_, lean_object* v_k_2228_, lean_object* v_x_2229_){
_start:
{
uint8_t v___x_2230_; 
v___x_2230_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_2224_, v_inst_2225_, v_m_u2082_2226_, v_k_2228_);
if (v___x_2230_ == 0)
{
return v___x_2227_;
}
else
{
uint8_t v___x_2231_; 
v___x_2231_ = 0;
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_2232_, lean_object* v_inst_2233_, lean_object* v_m_u2082_2234_, lean_object* v___x_2235_, lean_object* v_k_2236_, lean_object* v_x_2237_){
_start:
{
uint8_t v___x_91__boxed_2238_; uint8_t v_res_2239_; lean_object* v_r_2240_; 
v___x_91__boxed_2238_ = lean_unbox(v___x_2235_);
v_res_2239_ = l_Std_HashMap_Raw_diff___redArg___lam__0(v_inst_2232_, v_inst_2233_, v_m_u2082_2234_, v___x_91__boxed_2238_, v_k_2236_, v_x_2237_);
lean_dec(v_x_2237_);
lean_dec_ref(v_m_u2082_2234_);
v_r_2240_ = lean_box(v_res_2239_);
return v_r_2240_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff___redArg(lean_object* v_inst_2241_, lean_object* v_inst_2242_, lean_object* v_m_u2081_2243_, lean_object* v_m_u2082_2244_){
_start:
{
lean_object* v_size_2245_; lean_object* v_keyArray_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; 
v_size_2245_ = lean_ctor_get(v_m_u2081_2243_, 0);
v_keyArray_2246_ = lean_ctor_get(v_m_u2081_2243_, 1);
v___x_2247_ = lean_unsigned_to_nat(0u);
v___x_2248_ = lean_array_get_size(v_keyArray_2246_);
v___x_2249_ = lean_nat_dec_lt(v___x_2247_, v___x_2248_);
if (v___x_2249_ == 0)
{
lean_dec_ref(v_m_u2081_2243_);
lean_dec_ref(v_inst_2242_);
lean_dec_ref(v_inst_2241_);
return v_m_u2082_2244_;
}
else
{
lean_object* v_size_2250_; lean_object* v_keyArray_2251_; lean_object* v___x_2252_; uint8_t v___x_2253_; 
v_size_2250_ = lean_ctor_get(v_m_u2082_2244_, 0);
v_keyArray_2251_ = lean_ctor_get(v_m_u2082_2244_, 1);
v___x_2252_ = lean_array_get_size(v_keyArray_2251_);
v___x_2253_ = lean_nat_dec_lt(v___x_2247_, v___x_2252_);
if (v___x_2253_ == 0)
{
lean_dec_ref(v_m_u2082_2244_);
lean_dec_ref(v_inst_2242_);
lean_dec_ref(v_inst_2241_);
return v_m_u2081_2243_;
}
else
{
uint8_t v___x_2254_; 
v___x_2254_ = lean_nat_dec_le(v_size_2245_, v_size_2250_);
if (v___x_2254_ == 0)
{
lean_object* v___f_2255_; lean_object* v___x_2256_; 
v___f_2255_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_2256_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2255_, v_inst_2241_, v_inst_2242_, v_m_u2081_2243_, v_m_u2082_2244_);
return v___x_2256_;
}
else
{
lean_object* v___x_2257_; lean_object* v___f_2258_; lean_object* v___x_2259_; 
v___x_2257_ = lean_box(v___x_2254_);
v___f_2258_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2258_, 0, v_inst_2241_);
lean_closure_set(v___f_2258_, 1, v_inst_2242_);
lean_closure_set(v___f_2258_, 2, v_m_u2082_2244_);
lean_closure_set(v___f_2258_, 3, v___x_2257_);
v___x_2259_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2258_, v_m_u2081_2243_);
lean_dec_ref(v_m_u2081_2243_);
return v___x_2259_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_diff(lean_object* v_00_u03b1_2260_, lean_object* v_00_u03b2_2261_, lean_object* v_inst_2262_, lean_object* v_inst_2263_, lean_object* v_m_u2081_2264_, lean_object* v_m_u2082_2265_){
_start:
{
lean_object* v_size_2266_; lean_object* v_keyArray_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; uint8_t v___x_2270_; 
v_size_2266_ = lean_ctor_get(v_m_u2081_2264_, 0);
v_keyArray_2267_ = lean_ctor_get(v_m_u2081_2264_, 1);
v___x_2268_ = lean_unsigned_to_nat(0u);
v___x_2269_ = lean_array_get_size(v_keyArray_2267_);
v___x_2270_ = lean_nat_dec_lt(v___x_2268_, v___x_2269_);
if (v___x_2270_ == 0)
{
lean_dec_ref(v_m_u2081_2264_);
lean_dec_ref(v_inst_2263_);
lean_dec_ref(v_inst_2262_);
return v_m_u2082_2265_;
}
else
{
lean_object* v_size_2271_; lean_object* v_keyArray_2272_; lean_object* v___x_2273_; uint8_t v___x_2274_; 
v_size_2271_ = lean_ctor_get(v_m_u2082_2265_, 0);
v_keyArray_2272_ = lean_ctor_get(v_m_u2082_2265_, 1);
v___x_2273_ = lean_array_get_size(v_keyArray_2272_);
v___x_2274_ = lean_nat_dec_lt(v___x_2268_, v___x_2273_);
if (v___x_2274_ == 0)
{
lean_dec_ref(v_m_u2082_2265_);
lean_dec_ref(v_inst_2263_);
lean_dec_ref(v_inst_2262_);
return v_m_u2081_2264_;
}
else
{
uint8_t v___x_2275_; 
v___x_2275_ = lean_nat_dec_le(v_size_2266_, v_size_2271_);
if (v___x_2275_ == 0)
{
lean_object* v___f_2276_; lean_object* v___x_2277_; 
v___f_2276_ = ((lean_object*)(l_Std_HashMap_Raw_union___redArg___closed__0));
v___x_2277_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2276_, v_inst_2262_, v_inst_2263_, v_m_u2081_2264_, v_m_u2082_2265_);
return v___x_2277_;
}
else
{
lean_object* v___x_2278_; lean_object* v___f_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_box(v___x_2275_);
v___f_2279_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2279_, 0, v_inst_2262_);
lean_closure_set(v___f_2279_, 1, v_inst_2263_);
lean_closure_set(v___f_2279_, 2, v_m_u2082_2265_);
lean_closure_set(v___f_2279_, 3, v___x_2278_);
v___x_2280_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2279_, v_m_u2081_2264_);
lean_dec_ref(v_m_u2081_2264_);
return v___x_2280_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_2281_, lean_object* v_inst_2282_){
_start:
{
lean_object* v___x_2283_; 
v___x_2283_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_2283_, 0, lean_box(0));
lean_closure_set(v___x_2283_, 1, lean_box(0));
lean_closure_set(v___x_2283_, 2, v_inst_2281_);
lean_closure_set(v___x_2283_, 3, v_inst_2282_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_2284_, lean_object* v_00_u03b2_2285_, lean_object* v_inst_2286_, lean_object* v_inst_2287_){
_start:
{
lean_object* v___x_2288_; 
v___x_2288_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_union), 6, 4);
lean_closure_set(v___x_2288_, 0, lean_box(0));
lean_closure_set(v___x_2288_, 1, lean_box(0));
lean_closure_set(v___x_2288_, 2, v_inst_2286_);
lean_closure_set(v___x_2288_, 3, v_inst_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_2289_, lean_object* v_inst_2290_){
_start:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2291_, 0, lean_box(0));
lean_closure_set(v___x_2291_, 1, lean_box(0));
lean_closure_set(v___x_2291_, 2, v_inst_2289_);
lean_closure_set(v___x_2291_, 3, v_inst_2290_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_2292_, lean_object* v_00_u03b2_2293_, lean_object* v_inst_2294_, lean_object* v_inst_2295_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2296_, 0, lean_box(0));
lean_closure_set(v___x_2296_, 1, lean_box(0));
lean_closure_set(v___x_2296_, 2, v_inst_2294_);
lean_closure_set(v___x_2296_, 3, v_inst_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_2297_, lean_object* v_inst_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2299_, 0, lean_box(0));
lean_closure_set(v___x_2299_, 1, lean_box(0));
lean_closure_set(v___x_2299_, 2, v_inst_2297_);
lean_closure_set(v___x_2299_, 3, v_inst_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_2300_, lean_object* v_00_u03b2_2301_, lean_object* v_inst_2302_, lean_object* v_inst_2303_){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2304_, 0, lean_box(0));
lean_closure_set(v___x_2304_, 1, lean_box(0));
lean_closure_set(v___x_2304_, 2, v_inst_2302_);
lean_closure_set(v___x_2304_, 3, v_inst_2303_);
return v___x_2304_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq___redArg(lean_object* v_inst_2305_, lean_object* v_inst_2306_, lean_object* v_inst_2307_, lean_object* v_m_u2081_2308_, lean_object* v_m_u2082_2309_){
_start:
{
uint8_t v___x_2310_; 
v___x_2310_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2305_, v_inst_2306_, v_inst_2307_, v_m_u2081_2308_, v_m_u2082_2309_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___redArg___boxed(lean_object* v_inst_2311_, lean_object* v_inst_2312_, lean_object* v_inst_2313_, lean_object* v_m_u2081_2314_, lean_object* v_m_u2082_2315_){
_start:
{
uint8_t v_res_2316_; lean_object* v_r_2317_; 
v_res_2316_ = l_Std_HashMap_Raw_beq___redArg(v_inst_2311_, v_inst_2312_, v_inst_2313_, v_m_u2081_2314_, v_m_u2082_2315_);
v_r_2317_ = lean_box(v_res_2316_);
return v_r_2317_;
}
}
LEAN_EXPORT uint8_t l_Std_HashMap_Raw_beq(lean_object* v_00_u03b1_2318_, lean_object* v_00_u03b2_2319_, lean_object* v_inst_2320_, lean_object* v_inst_2321_, lean_object* v_inst_2322_, lean_object* v_m_u2081_2323_, lean_object* v_m_u2082_2324_){
_start:
{
uint8_t v___x_2325_; 
v___x_2325_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2320_, v_inst_2321_, v_inst_2322_, v_m_u2081_2323_, v_m_u2082_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_beq___boxed(lean_object* v_00_u03b1_2326_, lean_object* v_00_u03b2_2327_, lean_object* v_inst_2328_, lean_object* v_inst_2329_, lean_object* v_inst_2330_, lean_object* v_m_u2081_2331_, lean_object* v_m_u2082_2332_){
_start:
{
uint8_t v_res_2333_; lean_object* v_r_2334_; 
v_res_2333_ = l_Std_HashMap_Raw_beq(v_00_u03b1_2326_, v_00_u03b2_2327_, v_inst_2328_, v_inst_2329_, v_inst_2330_, v_m_u2081_2331_, v_m_u2082_2332_);
v_r_2334_ = lean_box(v_res_2333_);
return v_r_2334_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable___redArg(lean_object* v_inst_2335_, lean_object* v_inst_2336_, lean_object* v_inst_2337_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_2338_, 0, lean_box(0));
lean_closure_set(v___x_2338_, 1, lean_box(0));
lean_closure_set(v___x_2338_, 2, v_inst_2335_);
lean_closure_set(v___x_2338_, 3, v_inst_2336_);
lean_closure_set(v___x_2338_, 4, v_inst_2337_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instBEqOfHashable(lean_object* v_00_u03b1_2339_, lean_object* v_00_u03b2_2340_, lean_object* v_inst_2341_, lean_object* v_inst_2342_, lean_object* v_inst_2343_){
_start:
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_beq___boxed), 7, 5);
lean_closure_set(v___x_2344_, 0, lean_box(0));
lean_closure_set(v___x_2344_, 1, lean_box(0));
lean_closure_set(v___x_2344_, 2, v_inst_2341_);
lean_closure_set(v___x_2344_, 3, v_inst_2342_);
lean_closure_set(v___x_2344_, 4, v_inst_2343_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg(lean_object* v_f_2345_, lean_object* v_m_2346_){
_start:
{
lean_object* v_keyArray_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; 
v_keyArray_2347_ = lean_ctor_get(v_m_2346_, 1);
v___x_2348_ = lean_unsigned_to_nat(0u);
v___x_2349_ = lean_array_get_size(v_keyArray_2347_);
v___x_2350_ = lean_nat_dec_lt(v___x_2348_, v___x_2349_);
if (v___x_2350_ == 0)
{
lean_object* v___x_2351_; 
lean_dec_ref(v_f_2345_);
v___x_2351_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_2351_;
}
else
{
lean_object* v___x_2352_; 
v___x_2352_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2345_, v_m_2346_);
return v___x_2352_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___redArg___boxed(lean_object* v_f_2353_, lean_object* v_m_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Std_HashMap_Raw_filterMap___redArg(v_f_2353_, v_m_2354_);
lean_dec_ref(v_m_2354_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap(lean_object* v_00_u03b1_2356_, lean_object* v_00_u03b2_2357_, lean_object* v_00_u03b3_2358_, lean_object* v_f_2359_, lean_object* v_m_2360_){
_start:
{
lean_object* v_keyArray_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; uint8_t v___x_2364_; 
v_keyArray_2361_ = lean_ctor_get(v_m_2360_, 1);
v___x_2362_ = lean_unsigned_to_nat(0u);
v___x_2363_ = lean_array_get_size(v_keyArray_2361_);
v___x_2364_ = lean_nat_dec_lt(v___x_2362_, v___x_2363_);
if (v___x_2364_ == 0)
{
lean_object* v___x_2365_; 
lean_dec_ref(v_f_2359_);
v___x_2365_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_2365_;
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2359_, v_m_2360_);
return v___x_2366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filterMap___boxed(lean_object* v_00_u03b1_2367_, lean_object* v_00_u03b2_2368_, lean_object* v_00_u03b3_2369_, lean_object* v_f_2370_, lean_object* v_m_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Std_HashMap_Raw_filterMap(v_00_u03b1_2367_, v_00_u03b2_2368_, v_00_u03b3_2369_, v_f_2370_, v_m_2371_);
lean_dec_ref(v_m_2371_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg(lean_object* v_f_2373_, lean_object* v_m_2374_){
_start:
{
lean_object* v_keyArray_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; uint8_t v___x_2378_; 
v_keyArray_2375_ = lean_ctor_get(v_m_2374_, 1);
v___x_2376_ = lean_unsigned_to_nat(0u);
v___x_2377_ = lean_array_get_size(v_keyArray_2375_);
v___x_2378_ = lean_nat_dec_lt(v___x_2376_, v___x_2377_);
if (v___x_2378_ == 0)
{
lean_object* v___x_2379_; 
lean_dec(v_f_2373_);
v___x_2379_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_2379_;
}
else
{
lean_object* v___x_2380_; 
v___x_2380_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2373_, v_m_2374_);
return v___x_2380_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___redArg___boxed(lean_object* v_f_2381_, lean_object* v_m_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Std_HashMap_Raw_map___redArg(v_f_2381_, v_m_2382_);
lean_dec_ref(v_m_2382_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map(lean_object* v_00_u03b1_2384_, lean_object* v_00_u03b2_2385_, lean_object* v_00_u03b3_2386_, lean_object* v_f_2387_, lean_object* v_m_2388_){
_start:
{
lean_object* v_keyArray_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; 
v_keyArray_2389_ = lean_ctor_get(v_m_2388_, 1);
v___x_2390_ = lean_unsigned_to_nat(0u);
v___x_2391_ = lean_array_get_size(v_keyArray_2389_);
v___x_2392_ = lean_nat_dec_lt(v___x_2390_, v___x_2391_);
if (v___x_2392_ == 0)
{
lean_object* v___x_2393_; 
lean_dec(v_f_2387_);
v___x_2393_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_2393_;
}
else
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2387_, v_m_2388_);
return v___x_2394_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_map___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_00_u03b2_2396_, lean_object* v_00_u03b3_2397_, lean_object* v_f_2398_, lean_object* v_m_2399_){
_start:
{
lean_object* v_res_2400_; 
v_res_2400_ = l_Std_HashMap_Raw_map(v_00_u03b1_2395_, v_00_u03b2_2396_, v_00_u03b3_2397_, v_f_2398_, v_m_2399_);
lean_dec_ref(v_m_2399_);
return v_res_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg(lean_object* v_f_2401_, lean_object* v_m_2402_){
_start:
{
lean_object* v_keyArray_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; 
v_keyArray_2403_ = lean_ctor_get(v_m_2402_, 1);
v___x_2404_ = lean_unsigned_to_nat(0u);
v___x_2405_ = lean_array_get_size(v_keyArray_2403_);
v___x_2406_ = lean_nat_dec_lt(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; 
lean_dec_ref(v_f_2401_);
v___x_2407_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_2407_;
}
else
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2401_, v_m_2402_);
return v___x_2408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___redArg___boxed(lean_object* v_f_2409_, lean_object* v_m_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Std_HashMap_Raw_filter___redArg(v_f_2409_, v_m_2410_);
lean_dec_ref(v_m_2410_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter(lean_object* v_00_u03b1_2412_, lean_object* v_00_u03b2_2413_, lean_object* v_f_2414_, lean_object* v_m_2415_){
_start:
{
lean_object* v_keyArray_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; uint8_t v___x_2419_; 
v_keyArray_2416_ = lean_ctor_get(v_m_2415_, 1);
v___x_2417_ = lean_unsigned_to_nat(0u);
v___x_2418_ = lean_array_get_size(v_keyArray_2416_);
v___x_2419_ = lean_nat_dec_lt(v___x_2417_, v___x_2418_);
if (v___x_2419_ == 0)
{
lean_object* v___x_2420_; 
lean_dec_ref(v_f_2414_);
v___x_2420_ = lean_obj_once(&l_Std_HashMap_Raw_instEmptyCollection___closed__2, &l_Std_HashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_HashMap_Raw_instEmptyCollection___closed__2);
return v___x_2420_;
}
else
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2414_, v_m_2415_);
return v___x_2421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_filter___boxed(lean_object* v_00_u03b1_2422_, lean_object* v_00_u03b2_2423_, lean_object* v_f_2424_, lean_object* v_m_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Std_HashMap_Raw_filter(v_00_u03b1_2422_, v_00_u03b2_2423_, v_f_2424_, v_m_2425_);
lean_dec_ref(v_m_2425_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_2427_, lean_object* v_x2_2428_, lean_object* v_x3_2429_){
_start:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; 
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_x2_2428_);
lean_ctor_set(v___x_2430_, 1, v_x3_2429_);
v___x_2431_ = lean_array_push(v_x1_2427_, v___x_2430_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray___redArg(lean_object* v_m_2433_){
_start:
{
lean_object* v_size_2434_; lean_object* v___f_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_size_2434_ = lean_ctor_get(v_m_2433_, 0);
v___f_2435_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__0));
v___x_2436_ = lean_mk_empty_array_with_capacity(v_size_2434_);
v___x_2437_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2438_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2437_, v___f_2435_, v___x_2436_, v_m_2433_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_toArray(lean_object* v_00_u03b1_2439_, lean_object* v_00_u03b2_2440_, lean_object* v_m_2441_){
_start:
{
lean_object* v_size_2442_; lean_object* v___f_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_size_2442_ = lean_ctor_get(v_m_2441_, 0);
v___f_2443_ = ((lean_object*)(l_Std_HashMap_Raw_toArray___redArg___closed__0));
v___x_2444_ = lean_mk_empty_array_with_capacity(v_size_2442_);
v___x_2445_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2446_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2445_, v___f_2443_, v___x_2444_, v_m_2441_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_2447_, lean_object* v_x2_2448_, lean_object* v_x3_2449_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = lean_array_push(v_x1_2447_, v_x2_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_2451_, lean_object* v_x2_2452_, lean_object* v_x3_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Std_HashMap_Raw_keysArray___redArg___lam__0(v_x1_2451_, v_x2_2452_, v_x3_2453_);
lean_dec(v_x3_2453_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray___redArg(lean_object* v_m_2456_){
_start:
{
lean_object* v_size_2457_; lean_object* v___f_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v_size_2457_ = lean_ctor_get(v_m_2456_, 0);
v___f_2458_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__0));
v___x_2459_ = lean_mk_empty_array_with_capacity(v_size_2457_);
v___x_2460_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2461_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2460_, v___f_2458_, v___x_2459_, v_m_2456_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_keysArray(lean_object* v_00_u03b1_2462_, lean_object* v_00_u03b2_2463_, lean_object* v_m_2464_){
_start:
{
lean_object* v_size_2465_; lean_object* v___f_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v_size_2465_ = lean_ctor_get(v_m_2464_, 0);
v___f_2466_ = ((lean_object*)(l_Std_HashMap_Raw_keysArray___redArg___closed__0));
v___x_2467_ = lean_mk_empty_array_with_capacity(v_size_2465_);
v___x_2468_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2469_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2468_, v___f_2466_, v___x_2467_, v_m_2464_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0(lean_object* v_x1_2470_, lean_object* v_x2_2471_, lean_object* v_x3_2472_){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2473_, 0, v_x3_2472_);
lean_ctor_set(v___x_2473_, 1, v_x1_2470_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_x1_2474_, lean_object* v_x2_2475_, lean_object* v_x3_2476_){
_start:
{
lean_object* v_res_2477_; 
v_res_2477_ = l_Std_HashMap_Raw_values___redArg___lam__0(v_x1_2474_, v_x2_2475_, v_x3_2476_);
lean_dec(v_x2_2475_);
return v_res_2477_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg(lean_object* v_m_2479_){
_start:
{
lean_object* v___f_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___f_2480_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__0));
v___x_2481_ = lean_box(0);
v___x_2482_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2483_ = lean_unsigned_to_nat(0u);
v___x_2484_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2482_, v___f_2480_, v_m_2479_, v___x_2481_, v___x_2483_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___redArg___boxed(lean_object* v_m_2485_){
_start:
{
lean_object* v_res_2486_; 
v_res_2486_ = l_Std_HashMap_Raw_values___redArg(v_m_2485_);
lean_dec_ref(v_m_2485_);
return v_res_2486_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values(lean_object* v_00_u03b1_2487_, lean_object* v_00_u03b2_2488_, lean_object* v_m_2489_){
_start:
{
lean_object* v___f_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v___f_2490_ = ((lean_object*)(l_Std_HashMap_Raw_values___redArg___closed__0));
v___x_2491_ = lean_box(0);
v___x_2492_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2493_ = lean_unsigned_to_nat(0u);
v___x_2494_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2492_, v___f_2490_, v_m_2489_, v___x_2491_, v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_values___boxed(lean_object* v_00_u03b1_2495_, lean_object* v_00_u03b2_2496_, lean_object* v_m_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Std_HashMap_Raw_values(v_00_u03b1_2495_, v_00_u03b2_2496_, v_m_2497_);
lean_dec_ref(v_m_2497_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2499_, lean_object* v_x2_2500_, lean_object* v_x3_2501_){
_start:
{
lean_object* v___x_2502_; 
v___x_2502_ = lean_array_push(v_x1_2499_, v_x3_2501_);
return v___x_2502_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2503_, lean_object* v_x2_2504_, lean_object* v_x3_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Std_HashMap_Raw_valuesArray___redArg___lam__0(v_x1_2503_, v_x2_2504_, v_x3_2505_);
lean_dec(v_x2_2504_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray___redArg(lean_object* v_m_2508_){
_start:
{
lean_object* v_size_2509_; lean_object* v___f_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; 
v_size_2509_ = lean_ctor_get(v_m_2508_, 0);
v___f_2510_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__0));
v___x_2511_ = lean_mk_empty_array_with_capacity(v_size_2509_);
v___x_2512_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2513_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2512_, v___f_2510_, v___x_2511_, v_m_2508_);
return v___x_2513_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_valuesArray(lean_object* v_00_u03b1_2514_, lean_object* v_00_u03b2_2515_, lean_object* v_m_2516_){
_start:
{
lean_object* v_size_2517_; lean_object* v___f_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v_size_2517_ = lean_ctor_get(v_m_2516_, 0);
v___f_2518_ = ((lean_object*)(l_Std_HashMap_Raw_valuesArray___redArg___closed__0));
v___x_2519_ = lean_mk_empty_array_with_capacity(v_size_2517_);
v___x_2520_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2521_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2520_, v___f_2518_, v___x_2519_, v_m_2516_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany___redArg(lean_object* v_inst_2522_, lean_object* v_inst_2523_, lean_object* v_inst_2524_, lean_object* v_m_2525_, lean_object* v_l_2526_){
_start:
{
lean_object* v_keyArray_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; uint8_t v___x_2530_; 
v_keyArray_2527_ = lean_ctor_get(v_m_2525_, 1);
v___x_2528_ = lean_unsigned_to_nat(0u);
v___x_2529_ = lean_array_get_size(v_keyArray_2527_);
v___x_2530_ = lean_nat_dec_lt(v___x_2528_, v___x_2529_);
if (v___x_2530_ == 0)
{
lean_dec(v_l_2526_);
lean_dec(v_inst_2524_);
lean_dec_ref(v_inst_2523_);
lean_dec_ref(v_inst_2522_);
return v_m_2525_;
}
else
{
lean_object* v___x_2531_; 
v___x_2531_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2524_, v_inst_2522_, v_inst_2523_, v_m_2525_, v_l_2526_);
return v___x_2531_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertMany(lean_object* v_00_u03b1_2532_, lean_object* v_00_u03b2_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_00_u03c1_2536_, lean_object* v_inst_2537_, lean_object* v_m_2538_, lean_object* v_l_2539_){
_start:
{
lean_object* v_keyArray_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; uint8_t v___x_2543_; 
v_keyArray_2540_ = lean_ctor_get(v_m_2538_, 1);
v___x_2541_ = lean_unsigned_to_nat(0u);
v___x_2542_ = lean_array_get_size(v_keyArray_2540_);
v___x_2543_ = lean_nat_dec_lt(v___x_2541_, v___x_2542_);
if (v___x_2543_ == 0)
{
lean_dec(v_l_2539_);
lean_dec(v_inst_2537_);
lean_dec_ref(v_inst_2535_);
lean_dec_ref(v_inst_2534_);
return v_m_2538_;
}
else
{
lean_object* v___x_2544_; 
v___x_2544_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_2537_, v_inst_2534_, v_inst_2535_, v_m_2538_, v_l_2539_);
return v___x_2544_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit___redArg(lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_inst_2547_, lean_object* v_m_2548_, lean_object* v_l_2549_){
_start:
{
lean_object* v_keyArray_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; uint8_t v___x_2553_; 
v_keyArray_2550_ = lean_ctor_get(v_m_2548_, 1);
v___x_2551_ = lean_unsigned_to_nat(0u);
v___x_2552_ = lean_array_get_size(v_keyArray_2550_);
v___x_2553_ = lean_nat_dec_lt(v___x_2551_, v___x_2552_);
if (v___x_2553_ == 0)
{
lean_dec(v_l_2549_);
lean_dec(v_inst_2547_);
lean_dec_ref(v_inst_2546_);
lean_dec_ref(v_inst_2545_);
return v_m_2548_;
}
else
{
lean_object* v___x_2554_; 
v___x_2554_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2547_, v_inst_2545_, v_inst_2546_, v_m_2548_, v_l_2549_);
return v___x_2554_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_insertManyIfNewUnit(lean_object* v_00_u03b1_2555_, lean_object* v_inst_2556_, lean_object* v_inst_2557_, lean_object* v_00_u03c1_2558_, lean_object* v_inst_2559_, lean_object* v_m_2560_, lean_object* v_l_2561_){
_start:
{
lean_object* v_keyArray_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; 
v_keyArray_2562_ = lean_ctor_get(v_m_2560_, 1);
v___x_2563_ = lean_unsigned_to_nat(0u);
v___x_2564_ = lean_array_get_size(v_keyArray_2562_);
v___x_2565_ = lean_nat_dec_lt(v___x_2563_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_dec(v_l_2561_);
lean_dec(v_inst_2559_);
lean_dec_ref(v_inst_2557_);
lean_dec_ref(v_inst_2556_);
return v_m_2560_;
}
else
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_2559_, v_inst_2556_, v_inst_2557_, v_m_2560_, v_l_2561_);
return v___x_2566_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray___redArg(lean_object* v_inst_2567_, lean_object* v_inst_2568_, lean_object* v_l_2569_){
_start:
{
lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2570_ = lean_obj_once(&l_Std_HashMap_Raw_unitOfList___redArg___closed__1, &l_Std_HashMap_Raw_unitOfList___redArg___closed__1_once, _init_l_Std_HashMap_Raw_unitOfList___redArg___closed__1);
v___x_2571_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2571_ == 0)
{
lean_dec_ref(v_l_2569_);
lean_dec_ref(v_inst_2568_);
lean_dec_ref(v_inst_2567_);
return v___x_2570_;
}
else
{
lean_object* v___f_2572_; lean_object* v___x_2573_; 
v___f_2572_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2573_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2572_, v_inst_2567_, v_inst_2568_, v___x_2570_, v_l_2569_);
return v___x_2573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_unitOfArray(lean_object* v_00_u03b1_2574_, lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_l_2577_){
_start:
{
lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2578_ = lean_obj_once(&l_Std_HashMap_Raw_unitOfList___redArg___closed__1, &l_Std_HashMap_Raw_unitOfList___redArg___closed__1_once, _init_l_Std_HashMap_Raw_unitOfList___redArg___closed__1);
v___x_2579_ = lean_uint8_once(&l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_HashMap_Raw_instSingletonProdOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_2579_ == 0)
{
lean_dec_ref(v_l_2577_);
lean_dec_ref(v_inst_2576_);
lean_dec_ref(v_inst_2575_);
return v___x_2578_;
}
else
{
lean_object* v___f_2580_; lean_object* v___x_2581_; 
v___f_2580_ = ((lean_object*)(l_Std_HashMap_Raw_ofArray___redArg___closed__1));
v___x_2581_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_2580_, v_inst_2575_, v_inst_2576_, v___x_2578_, v_l_2577_);
return v___x_2581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_2582_){
_start:
{
lean_object* v___x_2583_; 
v___x_2583_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2582_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Std_HashMap_Raw_Internal_numBuckets___redArg(v_m_2584_);
lean_dec_ref(v_m_2584_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_2586_, lean_object* v_00_u03b2_2587_, lean_object* v_m_2588_){
_start:
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_2588_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_2590_, lean_object* v_00_u03b2_2591_, lean_object* v_m_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Std_HashMap_Raw_Internal_numBuckets(v_00_u03b1_2590_, v_00_u03b2_2591_, v_m_2592_);
lean_dec_ref(v_m_2592_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_2597_, lean_object* v___x_2598_, lean_object* v_m_2599_, lean_object* v_prec_2600_){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2601_ = ((lean_object*)(l_Std_HashMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_2602_ = lean_box(0);
v___x_2603_ = ((lean_object*)(l_Std_HashMap_Raw_keys___redArg___closed__10));
v___x_2604_ = lean_unsigned_to_nat(0u);
v___x_2605_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2603_, v___f_2597_, v_m_2599_, v___x_2602_, v___x_2604_);
v___x_2606_ = l_List_repr___redArg(v___x_2598_, v___x_2605_);
v___x_2607_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2601_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = l_Repr_addAppParen(v___x_2607_, v_prec_2600_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_2609_, lean_object* v___x_2610_, lean_object* v_m_2611_, lean_object* v_prec_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Std_HashMap_Raw_instRepr___redArg___lam__1(v___f_2609_, v___x_2610_, v_m_2611_, v_prec_2612_);
lean_dec(v_prec_2612_);
lean_dec_ref(v_m_2611_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr___redArg(lean_object* v_inst_2614_, lean_object* v_inst_2615_){
_start:
{
lean_object* v___f_2616_; lean_object* v___f_2617_; lean_object* v___x_2618_; lean_object* v___f_2619_; 
v___f_2616_ = ((lean_object*)(l_Std_HashMap_Raw_toList___redArg___closed__0));
v___f_2617_ = lean_alloc_closure((void*)(l_instReprTupleOfRepr___redArg___lam__0), 3, 1);
lean_closure_set(v___f_2617_, 0, v_inst_2615_);
v___x_2618_ = lean_alloc_closure((void*)(l_Prod_repr___boxed), 6, 4);
lean_closure_set(v___x_2618_, 0, lean_box(0));
lean_closure_set(v___x_2618_, 1, lean_box(0));
lean_closure_set(v___x_2618_, 2, v_inst_2614_);
lean_closure_set(v___x_2618_, 3, v___f_2617_);
v___f_2619_ = lean_alloc_closure((void*)(l_Std_HashMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2619_, 0, v___f_2616_);
lean_closure_set(v___f_2619_, 1, v___x_2618_);
return v___f_2619_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_Raw_instRepr(lean_object* v_00_u03b1_2620_, lean_object* v_00_u03b2_2621_, lean_object* v_inst_2622_, lean_object* v_inst_2623_){
_start:
{
lean_object* v___x_2624_; 
v___x_2624_ = l_Std_HashMap_Raw_instRepr___redArg(v_inst_2622_, v_inst_2623_);
return v___x_2624_;
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
