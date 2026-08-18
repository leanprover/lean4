// Lean compiler output
// Module: Std.Data.DHashMap.Raw
// Imports: public import Init.Data.LawfulHashable public import Std.Data.DHashMap.Internal.Defs import all Std.Data.DHashMap.Internal.Defs
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_foldRevMFrom___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Sigma_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_clearCell___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instEmptyCollection___closed__0;
static lean_once_cell_t l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instEmptyCollection___closed__1;
static lean_once_cell_t l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instEmptyCollection___closed__2;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited(lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DHashMap"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__2 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__2_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__3 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__3_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_0),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 125, 75, 48, 212, 67, 75, 250)}};
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_1),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(4, 208, 171, 151, 52, 103, 172, 57)}};
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__4_value_aux_2),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(66, 56, 12, 237, 152, 116, 148, 199)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__4 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__4_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__5 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__5_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__5_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__6 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__6_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__7 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__7_value)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__8 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__8_value;
static const lean_string_object l_Std_DHashMap_Raw_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__9 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__9_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__9_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__10 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__10_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__11 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__6_value),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__8_value),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__11_value)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__12 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__12_value;
static const lean_ctor_object l_Std_DHashMap_Raw_term___x7em___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__4_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__12_value)}};
static const lean_object* l_Std_DHashMap_Raw_term___x7em___00__closed__13 = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__13_value;
LEAN_EXPORT const lean_object* l_Std_DHashMap_Raw_term___x7em__ = (const lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__13_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_0),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_1),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value_aux_2),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Raw.Equiv"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5_value;
static lean_once_cell_t l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 77, 10, 233, 67, 27, 127, 47)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value_aux_0),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(235, 138, 4, 70, 137, 129, 138, 224)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_0),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 125, 75, 48, 212, 67, 75, 250)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_1),((lean_object*)&l_Std_DHashMap_Raw_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(4, 208, 171, 151, 52, 103, 172, 57)}};
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value_aux_2),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(43, 81, 159, 136, 76, 18, 51, 116)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__9_value)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__10_value),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__12_value)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13_value;
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0;
static lean_once_cell_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1;
static lean_once_cell_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__2;
static lean_once_cell_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__3;
static lean_once_cell_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value;
static const lean_closure_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value;
static const lean_ctor_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__0_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__1_value)}};
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value;
static const lean_ctor_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__7_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__2_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__3_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__4_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__5_value)}};
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value;
static const lean_ctor_object l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__8_value),((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__6_value)}};
static const lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9 = (const lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_toArray___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_keysArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_union___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instForInSigmaOfMonad___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)} };
static const lean_object* l_Std_DHashMap_Raw_union___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_union___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_diff___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_values___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_valuesArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0;
static lean_once_cell_t l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1;
static const lean_closure_object l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Array_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)} };
static const lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__2 = (const lean_object*)&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__2_value;
static const lean_closure_object l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__2_value)} };
static const lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__3 = (const lean_object*)&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__3_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_toList___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_Const_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_Const_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DHashMap_Raw_instRepr___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Std.DHashMap.Raw.ofList "};
static const lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__1___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_instRepr___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Std_DHashMap_Raw_instRepr___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_instRepr___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__1___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_instRepr___redArg___lam__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_keys___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_keys___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_ofList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_instForIn_x27InferInstanceMembershipOfMonad___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9_value)} };
static const lean_object* l_Std_DHashMap_Raw_ofList___redArg___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_ofList___redArg___closed__0_value;
static const lean_closure_object l_Std_DHashMap_Raw_ofList___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instForInOfForIn_x27___redArg___lam__1, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Std_DHashMap_Raw_ofList___redArg___closed__0_value)} };
static const lean_object* l_Std_DHashMap_Raw_ofList___redArg___closed__1 = (const lean_object*)&l_Std_DHashMap_Raw_ofList___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___redArg(lean_object* v_capacity_1_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___redArg___boxed(lean_object* v_capacity_13_){
_start:
{
lean_object* v_res_14_; 
v_res_14_ = l_Std_DHashMap_Raw_emptyWithCapacity___redArg(v_capacity_13_);
lean_dec(v_capacity_13_);
return v_res_14_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity(lean_object* v_00_u03b1_15_, lean_object* v_00_u03b2_16_, lean_object* v_capacity_17_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_emptyWithCapacity___boxed(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_capacity_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Std_DHashMap_Raw_emptyWithCapacity(v_00_u03b1_29_, v_00_u03b2_30_, v_capacity_31_);
lean_dec(v_capacity_31_);
return v_res_32_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0(void){
_start:
{
lean_object* v_cellCount_33_; lean_object* v___x_34_; 
v_cellCount_33_ = lean_unsigned_to_nat(16u);
v___x_34_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_33_);
return v___x_34_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1(void){
_start:
{
lean_object* v_cellCount_35_; lean_object* v___x_36_; 
v_cellCount_35_ = lean_unsigned_to_nat(16u);
v___x_36_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_37_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__1, &l_Std_DHashMap_Raw_instEmptyCollection___closed__1_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__1);
v___x_38_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0);
v___x_39_ = lean_unsigned_to_nat(0u);
v___x_40_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_40_, 0, v___x_39_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
lean_ctor_set(v___x_40_, 2, v___x_37_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instEmptyCollection(lean_object* v_00_u03b1_41_, lean_object* v_00_u03b2_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInhabited(lean_object* v_00_u03b1_44_, lean_object* v_00_u03b2_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_46_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__5));
v___x_88_ = l_String_toRawSubstring_x27(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(lean_object* v_x_112_, lean_object* v_a_113_, lean_object* v_a_114_){
_start:
{
lean_object* v___x_115_; uint8_t v___x_116_; 
v___x_115_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
lean_inc(v_x_112_);
v___x_116_ = l_Lean_Syntax_isOfKind(v_x_112_, v___x_115_);
if (v___x_116_ == 0)
{
lean_object* v___x_117_; lean_object* v___x_118_; 
lean_dec(v_x_112_);
v___x_117_ = lean_box(1);
v___x_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v_a_114_);
return v___x_118_;
}
else
{
lean_object* v_quotContext_119_; lean_object* v_currMacroScope_120_; lean_object* v_ref_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_quotContext_119_ = lean_ctor_get(v_a_113_, 1);
v_currMacroScope_120_ = lean_ctor_get(v_a_113_, 2);
v_ref_121_ = lean_ctor_get(v_a_113_, 5);
v___x_122_ = lean_unsigned_to_nat(0u);
v___x_123_ = l_Lean_Syntax_getArg(v_x_112_, v___x_122_);
v___x_124_ = lean_unsigned_to_nat(2u);
v___x_125_ = l_Lean_Syntax_getArg(v_x_112_, v___x_124_);
lean_dec(v_x_112_);
v___x_126_ = 0;
v___x_127_ = l_Lean_SourceInfo_fromRef(v_ref_121_, v___x_126_);
v___x_128_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
v___x_129_ = lean_obj_once(&l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6, &l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6_once, _init_l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__6);
v___x_130_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__8));
lean_inc(v_currMacroScope_120_);
lean_inc(v_quotContext_119_);
v___x_131_ = l_Lean_addMacroScope(v_quotContext_119_, v___x_130_, v_currMacroScope_120_);
v___x_132_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__13));
lean_inc_n(v___x_127_, 2);
v___x_133_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_133_, 0, v___x_127_);
lean_ctor_set(v___x_133_, 1, v___x_129_);
lean_ctor_set(v___x_133_, 2, v___x_131_);
lean_ctor_set(v___x_133_, 3, v___x_132_);
v___x_134_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__15));
v___x_135_ = l_Lean_Syntax_node2(v___x_127_, v___x_134_, v___x_123_, v___x_125_);
v___x_136_ = l_Lean_Syntax_node2(v___x_127_, v___x_128_, v___x_133_, v___x_135_);
v___x_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_136_);
lean_ctor_set(v___x_137_, 1, v_a_114_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___boxed(lean_object* v_x_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1(v_x_138_, v_a_139_, v_a_140_);
lean_dec_ref(v_a_139_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(lean_object* v_x_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______macroRules__Std__DHashMap__Raw__term___x7em____1___closed__4));
lean_inc(v_x_145_);
v___x_149_ = l_Lean_Syntax_isOfKind(v_x_145_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec(v_x_145_);
v___x_150_ = lean_box(0);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_a_147_);
return v___x_151_;
}
else
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v___x_152_ = lean_unsigned_to_nat(0u);
v___x_153_ = l_Lean_Syntax_getArg(v_x_145_, v___x_152_);
v___x_154_ = ((lean_object*)(l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___closed__1));
lean_inc(v___x_153_);
v___x_155_ = l_Lean_Syntax_isOfKind(v___x_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
lean_dec(v___x_153_);
lean_dec(v_x_145_);
v___x_156_ = lean_box(0);
v___x_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
lean_ctor_set(v___x_157_, 1, v_a_147_);
return v___x_157_;
}
else
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_158_ = lean_unsigned_to_nat(1u);
v___x_159_ = l_Lean_Syntax_getArg(v_x_145_, v___x_158_);
lean_dec(v_x_145_);
v___x_160_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_159_);
v___x_161_ = l_Lean_Syntax_matchesNull(v___x_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; lean_object* v___x_163_; 
lean_dec(v___x_159_);
lean_dec(v___x_153_);
v___x_162_ = lean_box(0);
v___x_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v_a_147_);
return v___x_163_;
}
else
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_ref_166_; uint8_t v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_164_ = l_Lean_Syntax_getArg(v___x_159_, v___x_152_);
v___x_165_ = l_Lean_Syntax_getArg(v___x_159_, v___x_158_);
lean_dec(v___x_159_);
v_ref_166_ = l_Lean_replaceRef(v___x_153_, v_a_146_);
lean_dec(v___x_153_);
v___x_167_ = 0;
v___x_168_ = l_Lean_SourceInfo_fromRef(v_ref_166_, v___x_167_);
lean_dec(v_ref_166_);
v___x_169_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__4));
v___x_170_ = ((lean_object*)(l_Std_DHashMap_Raw_term___x7em___00__closed__7));
lean_inc(v___x_168_);
v___x_171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_168_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = l_Lean_Syntax_node3(v___x_168_, v___x_169_, v___x_164_, v___x_171_, v___x_165_);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_a_147_);
return v___x_173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1___boxed(lean_object* v_x_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_DHashMap_Raw___aux__Std__Data__DHashMap__Raw______unexpand__Std__DHashMap__Raw__Equiv__1(v_x_174_, v_a_175_, v_a_176_);
lean_dec(v_a_175_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert___redArg(lean_object* v_inst_178_, lean_object* v_inst_179_, lean_object* v_m_180_, lean_object* v_a_181_, lean_object* v_b_182_){
_start:
{
lean_object* v___y_184_; lean_object* v_i_185_; lean_object* v___y_191_; lean_object* v___y_201_; lean_object* v_i_202_; lean_object* v_size_207_; lean_object* v_keyArray_208_; lean_object* v___x_209_; lean_object* v___x_219_; uint8_t v___x_220_; 
v_size_207_ = lean_ctor_get(v_m_180_, 0);
v_keyArray_208_ = lean_ctor_get(v_m_180_, 1);
v___x_209_ = lean_unsigned_to_nat(0u);
v___x_219_ = lean_array_get_size(v_keyArray_208_);
v___x_220_ = lean_nat_dec_lt(v___x_209_, v___x_219_);
if (v___x_220_ == 0)
{
lean_dec(v_b_182_);
lean_dec(v_a_181_);
lean_dec_ref(v_inst_179_);
lean_dec_ref(v_inst_178_);
return v_m_180_;
}
else
{
lean_object* v___x_221_; 
lean_inc(v_a_181_);
lean_inc_ref(v_inst_179_);
lean_inc_ref(v_inst_178_);
v___x_221_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_178_, v_inst_179_, v_m_180_, v_a_181_);
switch(lean_obj_tag(v___x_221_))
{
case 0:
{
lean_object* v_index_222_; lean_object* v___x_223_; 
lean_inc(v_size_207_);
lean_dec_ref(v_inst_179_);
lean_dec_ref(v_inst_178_);
v_index_222_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_index_222_);
lean_dec_ref_known(v___x_221_, 3);
v___x_223_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_180_, v_size_207_, v_index_222_, v_a_181_, v_b_182_);
lean_dec(v_index_222_);
return v___x_223_;
}
case 1:
{
lean_object* v_index_224_; lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_index_224_ = lean_ctor_get(v___x_221_, 0);
lean_inc(v_index_224_);
lean_dec_ref_known(v___x_221_, 1);
v___x_225_ = lean_unsigned_to_nat(1u);
v___x_226_ = lean_nat_add(v_size_207_, v___x_225_);
v___x_227_ = lean_nat_dec_lt(v___x_226_, v___x_219_);
if (v___x_227_ == 0)
{
lean_dec(v___x_226_);
lean_dec(v_index_224_);
goto v___jp_210_;
}
else
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_228_ = lean_unsigned_to_nat(4u);
v___x_229_ = lean_nat_mul(v___x_226_, v___x_228_);
v___x_230_ = lean_unsigned_to_nat(3u);
v___x_231_ = lean_nat_mul(v___x_219_, v___x_230_);
v___x_232_ = lean_nat_dec_le(v___x_229_, v___x_231_);
lean_dec(v___x_231_);
lean_dec(v___x_229_);
if (v___x_232_ == 0)
{
lean_dec(v___x_226_);
lean_dec(v_index_224_);
goto v___jp_210_;
}
else
{
lean_object* v___x_233_; 
lean_dec_ref(v_inst_179_);
lean_dec_ref(v_inst_178_);
v___x_233_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_180_, v___x_226_, v_index_224_, v_a_181_, v_b_182_);
lean_dec(v_index_224_);
return v___x_233_;
}
}
}
default: 
{
lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; 
v___x_234_ = lean_unsigned_to_nat(1u);
v___x_235_ = lean_nat_add(v_size_207_, v___x_234_);
v___x_236_ = lean_nat_dec_lt(v___x_235_, v___x_219_);
if (v___x_236_ == 0)
{
lean_object* v___x_237_; 
lean_dec(v___x_235_);
lean_inc_ref(v_inst_179_);
lean_inc_ref(v_inst_178_);
v___x_237_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_178_, v_inst_179_, v_m_180_);
v___y_191_ = v___x_237_;
goto v___jp_190_;
}
else
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; 
v___x_238_ = lean_unsigned_to_nat(4u);
v___x_239_ = lean_nat_mul(v___x_235_, v___x_238_);
lean_dec(v___x_235_);
v___x_240_ = lean_unsigned_to_nat(3u);
v___x_241_ = lean_nat_mul(v___x_219_, v___x_240_);
v___x_242_ = lean_nat_dec_le(v___x_239_, v___x_241_);
lean_dec(v___x_241_);
lean_dec(v___x_239_);
if (v___x_242_ == 0)
{
lean_object* v___x_243_; 
lean_inc_ref(v_inst_179_);
lean_inc_ref(v_inst_178_);
v___x_243_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_178_, v_inst_179_, v_m_180_);
v___y_191_ = v___x_243_;
goto v___jp_190_;
}
else
{
v___y_191_ = v_m_180_;
goto v___jp_190_;
}
}
}
}
}
v___jp_183_:
{
lean_object* v_size_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_size_186_ = lean_ctor_get(v___y_184_, 0);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_size_186_, v___x_187_);
v___x_189_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_184_, v___x_188_, v_i_185_, v_a_181_, v_b_182_);
lean_dec(v_i_185_);
return v___x_189_;
}
v___jp_190_:
{
lean_object* v___x_192_; 
lean_inc(v_a_181_);
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_178_, v_inst_179_, v___y_191_, v_a_181_);
switch(lean_obj_tag(v___x_192_))
{
case 0:
{
lean_object* v_index_193_; lean_object* v_size_194_; lean_object* v___x_195_; 
v_index_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_index_193_);
lean_dec_ref_known(v___x_192_, 3);
v_size_194_ = lean_ctor_get(v___y_191_, 0);
lean_inc(v_size_194_);
v___x_195_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_191_, v_size_194_, v_index_193_, v_a_181_, v_b_182_);
lean_dec(v_index_193_);
return v___x_195_;
}
case 1:
{
lean_object* v_index_196_; 
v_index_196_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_index_196_);
lean_dec_ref_known(v___x_192_, 1);
v___y_184_ = v___y_191_;
v_i_185_ = v_index_196_;
goto v___jp_183_;
}
default: 
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_191_, v___x_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_index_199_; 
v_index_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_index_199_);
lean_dec_ref_known(v___x_198_, 1);
v___y_184_ = v___y_191_;
v_i_185_ = v_index_199_;
goto v___jp_183_;
}
else
{
lean_dec(v_b_182_);
lean_dec(v_a_181_);
return v___y_191_;
}
}
}
}
v___jp_200_:
{
lean_object* v_size_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v_size_203_ = lean_ctor_get(v___y_201_, 0);
v___x_204_ = lean_unsigned_to_nat(1u);
v___x_205_ = lean_nat_add(v_size_203_, v___x_204_);
v___x_206_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_201_, v___x_205_, v_i_202_, v_a_181_, v_b_182_);
lean_dec(v_i_202_);
return v___x_206_;
}
v___jp_210_:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
lean_inc_ref(v_inst_179_);
lean_inc_ref(v_inst_178_);
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_178_, v_inst_179_, v_m_180_);
lean_inc(v_a_181_);
v___x_212_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_178_, v_inst_179_, v___x_211_, v_a_181_);
switch(lean_obj_tag(v___x_212_))
{
case 0:
{
lean_object* v_index_213_; lean_object* v_size_214_; lean_object* v___x_215_; 
v_index_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_index_213_);
lean_dec_ref_known(v___x_212_, 3);
v_size_214_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_size_214_);
v___x_215_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_211_, v_size_214_, v_index_213_, v_a_181_, v_b_182_);
lean_dec(v_index_213_);
return v___x_215_;
}
case 1:
{
lean_object* v_index_216_; 
v_index_216_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_index_216_);
lean_dec_ref_known(v___x_212_, 1);
v___y_201_ = v___x_211_;
v_i_202_ = v_index_216_;
goto v___jp_200_;
}
default: 
{
lean_object* v___x_217_; 
v___x_217_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_211_, v___x_209_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_index_218_; 
v_index_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_index_218_);
lean_dec_ref_known(v___x_217_, 1);
v___y_201_ = v___x_211_;
v_i_202_ = v_index_218_;
goto v___jp_200_;
}
else
{
lean_dec(v_b_182_);
lean_dec(v_a_181_);
return v___x_211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insert(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_m_248_, lean_object* v_a_249_, lean_object* v_b_250_){
_start:
{
lean_object* v___y_252_; lean_object* v_i_253_; lean_object* v___y_259_; lean_object* v___y_269_; lean_object* v_i_270_; lean_object* v_size_275_; lean_object* v_keyArray_276_; lean_object* v___x_277_; lean_object* v___x_287_; uint8_t v___x_288_; 
v_size_275_ = lean_ctor_get(v_m_248_, 0);
v_keyArray_276_ = lean_ctor_get(v_m_248_, 1);
v___x_277_ = lean_unsigned_to_nat(0u);
v___x_287_ = lean_array_get_size(v_keyArray_276_);
v___x_288_ = lean_nat_dec_lt(v___x_277_, v___x_287_);
if (v___x_288_ == 0)
{
lean_dec(v_b_250_);
lean_dec(v_a_249_);
lean_dec_ref(v_inst_247_);
lean_dec_ref(v_inst_246_);
return v_m_248_;
}
else
{
lean_object* v___x_289_; 
lean_inc(v_a_249_);
lean_inc_ref(v_inst_247_);
lean_inc_ref(v_inst_246_);
v___x_289_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_246_, v_inst_247_, v_m_248_, v_a_249_);
switch(lean_obj_tag(v___x_289_))
{
case 0:
{
lean_object* v_index_290_; lean_object* v___x_291_; 
lean_inc(v_size_275_);
lean_dec_ref(v_inst_247_);
lean_dec_ref(v_inst_246_);
v_index_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_index_290_);
lean_dec_ref_known(v___x_289_, 3);
v___x_291_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_248_, v_size_275_, v_index_290_, v_a_249_, v_b_250_);
lean_dec(v_index_290_);
return v___x_291_;
}
case 1:
{
lean_object* v_index_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_index_292_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_index_292_);
lean_dec_ref_known(v___x_289_, 1);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = lean_nat_add(v_size_275_, v___x_293_);
v___x_295_ = lean_nat_dec_lt(v___x_294_, v___x_287_);
if (v___x_295_ == 0)
{
lean_dec(v___x_294_);
lean_dec(v_index_292_);
goto v___jp_278_;
}
else
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; 
v___x_296_ = lean_unsigned_to_nat(4u);
v___x_297_ = lean_nat_mul(v___x_294_, v___x_296_);
v___x_298_ = lean_unsigned_to_nat(3u);
v___x_299_ = lean_nat_mul(v___x_287_, v___x_298_);
v___x_300_ = lean_nat_dec_le(v___x_297_, v___x_299_);
lean_dec(v___x_299_);
lean_dec(v___x_297_);
if (v___x_300_ == 0)
{
lean_dec(v___x_294_);
lean_dec(v_index_292_);
goto v___jp_278_;
}
else
{
lean_object* v___x_301_; 
lean_dec_ref(v_inst_247_);
lean_dec_ref(v_inst_246_);
v___x_301_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_248_, v___x_294_, v_index_292_, v_a_249_, v_b_250_);
lean_dec(v_index_292_);
return v___x_301_;
}
}
}
default: 
{
lean_object* v___x_302_; lean_object* v___x_303_; uint8_t v___x_304_; 
v___x_302_ = lean_unsigned_to_nat(1u);
v___x_303_ = lean_nat_add(v_size_275_, v___x_302_);
v___x_304_ = lean_nat_dec_lt(v___x_303_, v___x_287_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
lean_dec(v___x_303_);
lean_inc_ref(v_inst_247_);
lean_inc_ref(v_inst_246_);
v___x_305_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_246_, v_inst_247_, v_m_248_);
v___y_259_ = v___x_305_;
goto v___jp_258_;
}
else
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_306_ = lean_unsigned_to_nat(4u);
v___x_307_ = lean_nat_mul(v___x_303_, v___x_306_);
lean_dec(v___x_303_);
v___x_308_ = lean_unsigned_to_nat(3u);
v___x_309_ = lean_nat_mul(v___x_287_, v___x_308_);
v___x_310_ = lean_nat_dec_le(v___x_307_, v___x_309_);
lean_dec(v___x_309_);
lean_dec(v___x_307_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_inc_ref(v_inst_247_);
lean_inc_ref(v_inst_246_);
v___x_311_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_246_, v_inst_247_, v_m_248_);
v___y_259_ = v___x_311_;
goto v___jp_258_;
}
else
{
v___y_259_ = v_m_248_;
goto v___jp_258_;
}
}
}
}
}
v___jp_251_:
{
lean_object* v_size_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_size_254_ = lean_ctor_get(v___y_252_, 0);
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_size_254_, v___x_255_);
v___x_257_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_252_, v___x_256_, v_i_253_, v_a_249_, v_b_250_);
lean_dec(v_i_253_);
return v___x_257_;
}
v___jp_258_:
{
lean_object* v___x_260_; 
lean_inc(v_a_249_);
v___x_260_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_246_, v_inst_247_, v___y_259_, v_a_249_);
switch(lean_obj_tag(v___x_260_))
{
case 0:
{
lean_object* v_index_261_; lean_object* v_size_262_; lean_object* v___x_263_; 
v_index_261_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_index_261_);
lean_dec_ref_known(v___x_260_, 3);
v_size_262_ = lean_ctor_get(v___y_259_, 0);
lean_inc(v_size_262_);
v___x_263_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_259_, v_size_262_, v_index_261_, v_a_249_, v_b_250_);
lean_dec(v_index_261_);
return v___x_263_;
}
case 1:
{
lean_object* v_index_264_; 
v_index_264_ = lean_ctor_get(v___x_260_, 0);
lean_inc(v_index_264_);
lean_dec_ref_known(v___x_260_, 1);
v___y_252_ = v___y_259_;
v_i_253_ = v_index_264_;
goto v___jp_251_;
}
default: 
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_unsigned_to_nat(0u);
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_259_, v___x_265_);
if (lean_obj_tag(v___x_266_) == 0)
{
lean_object* v_index_267_; 
v_index_267_ = lean_ctor_get(v___x_266_, 0);
lean_inc(v_index_267_);
lean_dec_ref_known(v___x_266_, 1);
v___y_252_ = v___y_259_;
v_i_253_ = v_index_267_;
goto v___jp_251_;
}
else
{
lean_dec(v_b_250_);
lean_dec(v_a_249_);
return v___y_259_;
}
}
}
}
v___jp_268_:
{
lean_object* v_size_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_size_271_ = lean_ctor_get(v___y_269_, 0);
v___x_272_ = lean_unsigned_to_nat(1u);
v___x_273_ = lean_nat_add(v_size_271_, v___x_272_);
v___x_274_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_269_, v___x_273_, v_i_270_, v_a_249_, v_b_250_);
lean_dec(v_i_270_);
return v___x_274_;
}
v___jp_278_:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_inc_ref(v_inst_247_);
lean_inc_ref(v_inst_246_);
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_246_, v_inst_247_, v_m_248_);
lean_inc(v_a_249_);
v___x_280_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_246_, v_inst_247_, v___x_279_, v_a_249_);
switch(lean_obj_tag(v___x_280_))
{
case 0:
{
lean_object* v_index_281_; lean_object* v_size_282_; lean_object* v___x_283_; 
v_index_281_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_index_281_);
lean_dec_ref_known(v___x_280_, 3);
v_size_282_ = lean_ctor_get(v___x_279_, 0);
lean_inc(v_size_282_);
v___x_283_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_279_, v_size_282_, v_index_281_, v_a_249_, v_b_250_);
lean_dec(v_index_281_);
return v___x_283_;
}
case 1:
{
lean_object* v_index_284_; 
v_index_284_ = lean_ctor_get(v___x_280_, 0);
lean_inc(v_index_284_);
lean_dec_ref_known(v___x_280_, 1);
v___y_269_ = v___x_279_;
v_i_270_ = v_index_284_;
goto v___jp_268_;
}
default: 
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_279_, v___x_277_);
if (lean_obj_tag(v___x_285_) == 0)
{
lean_object* v_index_286_; 
v_index_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_index_286_);
lean_dec_ref_known(v___x_285_, 1);
v___y_269_ = v___x_279_;
v_i_270_ = v_index_286_;
goto v___jp_268_;
}
else
{
lean_dec(v_b_250_);
lean_dec(v_a_249_);
return v___x_279_;
}
}
}
}
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_312_; lean_object* v___x_313_; 
v___x_312_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0);
v___x_313_ = lean_array_get_size(v___x_312_);
return v___x_313_;
}
}
static uint8_t _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_obj_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = lean_nat_dec_lt(v___x_315_, v___x_314_);
return v___x_316_;
}
}
static uint8_t _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__2(void){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_obj_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_dec_lt(v___x_318_, v___x_317_);
return v___x_319_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_unsigned_to_nat(3u);
v___x_321_ = lean_obj_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__0);
v___x_322_ = lean_nat_mul(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static uint8_t _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v___x_323_ = lean_obj_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__3, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__3_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__3);
v___x_324_ = lean_unsigned_to_nat(4u);
v___x_325_ = lean_nat_dec_le(v___x_324_, v___x_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_x_328_){
_start:
{
lean_object* v_fst_329_; lean_object* v_snd_330_; lean_object* v___y_332_; lean_object* v_i_333_; lean_object* v___y_339_; lean_object* v_i_340_; lean_object* v___y_346_; lean_object* v___x_355_; lean_object* v___x_356_; uint8_t v___x_366_; 
v_fst_329_ = lean_ctor_get(v_x_328_, 0);
lean_inc(v_fst_329_);
v_snd_330_ = lean_ctor_get(v_x_328_, 1);
lean_inc(v_snd_330_);
lean_dec_ref(v_x_328_);
v___x_355_ = lean_unsigned_to_nat(0u);
v___x_356_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
v___x_366_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_366_ == 0)
{
lean_dec(v_snd_330_);
lean_dec(v_fst_329_);
lean_dec_ref(v_inst_327_);
lean_dec_ref(v_inst_326_);
return v___x_356_;
}
else
{
lean_object* v___x_367_; 
lean_inc(v_fst_329_);
lean_inc_ref(v_inst_327_);
lean_inc_ref(v_inst_326_);
v___x_367_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_326_, v_inst_327_, v___x_356_, v_fst_329_);
switch(lean_obj_tag(v___x_367_))
{
case 0:
{
lean_object* v_index_368_; lean_object* v___x_369_; 
lean_dec_ref(v_inst_327_);
lean_dec_ref(v_inst_326_);
v_index_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_index_368_);
lean_dec_ref_known(v___x_367_, 3);
v___x_369_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_356_, v___x_355_, v_index_368_, v_fst_329_, v_snd_330_);
lean_dec(v_index_368_);
return v___x_369_;
}
case 1:
{
lean_object* v_index_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v_index_370_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_index_370_);
lean_dec_ref_known(v___x_367_, 1);
v___x_371_ = lean_unsigned_to_nat(1u);
v___x_372_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__2, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__2_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__2);
if (v___x_372_ == 0)
{
lean_dec(v_index_370_);
goto v___jp_357_;
}
else
{
uint8_t v___x_373_; 
v___x_373_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__4, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__4_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__4);
if (v___x_373_ == 0)
{
lean_dec(v_index_370_);
goto v___jp_357_;
}
else
{
lean_object* v___x_374_; 
lean_dec_ref(v_inst_327_);
lean_dec_ref(v_inst_326_);
v___x_374_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_356_, v___x_371_, v_index_370_, v_fst_329_, v_snd_330_);
lean_dec(v_index_370_);
return v___x_374_;
}
}
}
default: 
{
uint8_t v___x_375_; 
v___x_375_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__2, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__2_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__2);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; 
lean_inc_ref(v_inst_327_);
lean_inc_ref(v_inst_326_);
v___x_376_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_326_, v_inst_327_, v___x_356_);
v___y_346_ = v___x_376_;
goto v___jp_345_;
}
else
{
uint8_t v___x_377_; 
v___x_377_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__4, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__4_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__4);
if (v___x_377_ == 0)
{
lean_object* v___x_378_; 
lean_inc_ref(v_inst_327_);
lean_inc_ref(v_inst_326_);
v___x_378_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_326_, v_inst_327_, v___x_356_);
v___y_346_ = v___x_378_;
goto v___jp_345_;
}
else
{
v___y_346_ = v___x_356_;
goto v___jp_345_;
}
}
}
}
}
v___jp_331_:
{
lean_object* v_size_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; 
v_size_334_ = lean_ctor_get(v___y_332_, 0);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_size_334_, v___x_335_);
v___x_337_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_332_, v___x_336_, v_i_333_, v_fst_329_, v_snd_330_);
lean_dec(v_i_333_);
return v___x_337_;
}
v___jp_338_:
{
lean_object* v_size_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_size_341_ = lean_ctor_get(v___y_339_, 0);
v___x_342_ = lean_unsigned_to_nat(1u);
v___x_343_ = lean_nat_add(v_size_341_, v___x_342_);
v___x_344_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_339_, v___x_343_, v_i_340_, v_fst_329_, v_snd_330_);
lean_dec(v_i_340_);
return v___x_344_;
}
v___jp_345_:
{
lean_object* v___x_347_; 
lean_inc(v_fst_329_);
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_326_, v_inst_327_, v___y_346_, v_fst_329_);
switch(lean_obj_tag(v___x_347_))
{
case 0:
{
lean_object* v_index_348_; lean_object* v_size_349_; lean_object* v___x_350_; 
v_index_348_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_index_348_);
lean_dec_ref_known(v___x_347_, 3);
v_size_349_ = lean_ctor_get(v___y_346_, 0);
lean_inc(v_size_349_);
v___x_350_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_346_, v_size_349_, v_index_348_, v_fst_329_, v_snd_330_);
lean_dec(v_index_348_);
return v___x_350_;
}
case 1:
{
lean_object* v_index_351_; 
v_index_351_ = lean_ctor_get(v___x_347_, 0);
lean_inc(v_index_351_);
lean_dec_ref_known(v___x_347_, 1);
v___y_339_ = v___y_346_;
v_i_340_ = v_index_351_;
goto v___jp_338_;
}
default: 
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = lean_unsigned_to_nat(0u);
v___x_353_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_346_, v___x_352_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_index_354_; 
v_index_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_index_354_);
lean_dec_ref_known(v___x_353_, 1);
v___y_339_ = v___y_346_;
v_i_340_ = v_index_354_;
goto v___jp_338_;
}
else
{
lean_dec(v_snd_330_);
lean_dec(v_fst_329_);
return v___y_346_;
}
}
}
}
v___jp_357_:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_inc_ref(v_inst_327_);
lean_inc_ref(v_inst_326_);
v___x_358_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_326_, v_inst_327_, v___x_356_);
lean_inc(v_fst_329_);
v___x_359_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_326_, v_inst_327_, v___x_358_, v_fst_329_);
switch(lean_obj_tag(v___x_359_))
{
case 0:
{
lean_object* v_index_360_; lean_object* v_size_361_; lean_object* v___x_362_; 
v_index_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_index_360_);
lean_dec_ref_known(v___x_359_, 3);
v_size_361_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_size_361_);
v___x_362_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_358_, v_size_361_, v_index_360_, v_fst_329_, v_snd_330_);
lean_dec(v_index_360_);
return v___x_362_;
}
case 1:
{
lean_object* v_index_363_; 
v_index_363_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_index_363_);
lean_dec_ref_known(v___x_359_, 1);
v___y_332_ = v___x_358_;
v_i_333_ = v_index_363_;
goto v___jp_331_;
}
default: 
{
lean_object* v___x_364_; 
v___x_364_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_358_, v___x_355_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_object* v_index_365_; 
v_index_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_index_365_);
lean_dec_ref_known(v___x_364_, 1);
v___y_332_ = v___x_358_;
v_i_333_ = v_index_365_;
goto v___jp_331_;
}
else
{
lean_dec(v_snd_330_);
lean_dec(v_fst_329_);
return v___x_358_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg(lean_object* v_inst_379_, lean_object* v_inst_380_){
_start:
{
lean_object* v___f_381_; 
v___f_381_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_381_, 0, v_inst_379_);
lean_closure_set(v___f_381_, 1, v_inst_380_);
return v___f_381_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable(lean_object* v_00_u03b1_382_, lean_object* v_00_u03b2_383_, lean_object* v_inst_384_, lean_object* v_inst_385_){
_start:
{
lean_object* v___f_386_; 
v___f_386_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0), 3, 2);
lean_closure_set(v___f_386_, 0, v_inst_384_);
lean_closure_set(v___f_386_, 1, v_inst_385_);
return v___f_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0(lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_x_389_, lean_object* v_s_390_){
_start:
{
lean_object* v_fst_391_; lean_object* v_snd_392_; lean_object* v___y_394_; lean_object* v_i_395_; lean_object* v___y_401_; lean_object* v_i_402_; lean_object* v___y_408_; lean_object* v_size_417_; lean_object* v_keyArray_418_; lean_object* v___x_419_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_fst_391_ = lean_ctor_get(v_x_389_, 0);
lean_inc(v_fst_391_);
v_snd_392_ = lean_ctor_get(v_x_389_, 1);
lean_inc(v_snd_392_);
lean_dec_ref(v_x_389_);
v_size_417_ = lean_ctor_get(v_s_390_, 0);
v_keyArray_418_ = lean_ctor_get(v_s_390_, 1);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_array_get_size(v_keyArray_418_);
v___x_430_ = lean_nat_dec_lt(v___x_419_, v___x_429_);
if (v___x_430_ == 0)
{
lean_dec(v_snd_392_);
lean_dec(v_fst_391_);
lean_dec_ref(v_inst_388_);
lean_dec_ref(v_inst_387_);
return v_s_390_;
}
else
{
lean_object* v___x_431_; 
lean_inc(v_fst_391_);
lean_inc_ref(v_inst_388_);
lean_inc_ref(v_inst_387_);
v___x_431_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_387_, v_inst_388_, v_s_390_, v_fst_391_);
switch(lean_obj_tag(v___x_431_))
{
case 0:
{
lean_object* v_index_432_; lean_object* v___x_433_; 
lean_inc(v_size_417_);
lean_dec_ref(v_inst_388_);
lean_dec_ref(v_inst_387_);
v_index_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_index_432_);
lean_dec_ref_known(v___x_431_, 3);
v___x_433_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_390_, v_size_417_, v_index_432_, v_fst_391_, v_snd_392_);
lean_dec(v_index_432_);
return v___x_433_;
}
case 1:
{
lean_object* v_index_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_index_434_ = lean_ctor_get(v___x_431_, 0);
lean_inc(v_index_434_);
lean_dec_ref_known(v___x_431_, 1);
v___x_435_ = lean_unsigned_to_nat(1u);
v___x_436_ = lean_nat_add(v_size_417_, v___x_435_);
v___x_437_ = lean_nat_dec_lt(v___x_436_, v___x_429_);
if (v___x_437_ == 0)
{
lean_dec(v___x_436_);
lean_dec(v_index_434_);
goto v___jp_420_;
}
else
{
lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_438_ = lean_unsigned_to_nat(4u);
v___x_439_ = lean_nat_mul(v___x_436_, v___x_438_);
v___x_440_ = lean_unsigned_to_nat(3u);
v___x_441_ = lean_nat_mul(v___x_429_, v___x_440_);
v___x_442_ = lean_nat_dec_le(v___x_439_, v___x_441_);
lean_dec(v___x_441_);
lean_dec(v___x_439_);
if (v___x_442_ == 0)
{
lean_dec(v___x_436_);
lean_dec(v_index_434_);
goto v___jp_420_;
}
else
{
lean_object* v___x_443_; 
lean_dec_ref(v_inst_388_);
lean_dec_ref(v_inst_387_);
v___x_443_ = l_Std_DHashMap_Raw_setEntry___redArg(v_s_390_, v___x_436_, v_index_434_, v_fst_391_, v_snd_392_);
lean_dec(v_index_434_);
return v___x_443_;
}
}
}
default: 
{
lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_444_ = lean_unsigned_to_nat(1u);
v___x_445_ = lean_nat_add(v_size_417_, v___x_444_);
v___x_446_ = lean_nat_dec_lt(v___x_445_, v___x_429_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; 
lean_dec(v___x_445_);
lean_inc_ref(v_inst_388_);
lean_inc_ref(v_inst_387_);
v___x_447_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_387_, v_inst_388_, v_s_390_);
v___y_408_ = v___x_447_;
goto v___jp_407_;
}
else
{
lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; uint8_t v___x_452_; 
v___x_448_ = lean_unsigned_to_nat(4u);
v___x_449_ = lean_nat_mul(v___x_445_, v___x_448_);
lean_dec(v___x_445_);
v___x_450_ = lean_unsigned_to_nat(3u);
v___x_451_ = lean_nat_mul(v___x_429_, v___x_450_);
v___x_452_ = lean_nat_dec_le(v___x_449_, v___x_451_);
lean_dec(v___x_451_);
lean_dec(v___x_449_);
if (v___x_452_ == 0)
{
lean_object* v___x_453_; 
lean_inc_ref(v_inst_388_);
lean_inc_ref(v_inst_387_);
v___x_453_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_387_, v_inst_388_, v_s_390_);
v___y_408_ = v___x_453_;
goto v___jp_407_;
}
else
{
v___y_408_ = v_s_390_;
goto v___jp_407_;
}
}
}
}
}
v___jp_393_:
{
lean_object* v_size_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_size_396_ = lean_ctor_get(v___y_394_, 0);
v___x_397_ = lean_unsigned_to_nat(1u);
v___x_398_ = lean_nat_add(v_size_396_, v___x_397_);
v___x_399_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_394_, v___x_398_, v_i_395_, v_fst_391_, v_snd_392_);
lean_dec(v_i_395_);
return v___x_399_;
}
v___jp_400_:
{
lean_object* v_size_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_size_403_ = lean_ctor_get(v___y_401_, 0);
v___x_404_ = lean_unsigned_to_nat(1u);
v___x_405_ = lean_nat_add(v_size_403_, v___x_404_);
v___x_406_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_401_, v___x_405_, v_i_402_, v_fst_391_, v_snd_392_);
lean_dec(v_i_402_);
return v___x_406_;
}
v___jp_407_:
{
lean_object* v___x_409_; 
lean_inc(v_fst_391_);
v___x_409_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_387_, v_inst_388_, v___y_408_, v_fst_391_);
switch(lean_obj_tag(v___x_409_))
{
case 0:
{
lean_object* v_index_410_; lean_object* v_size_411_; lean_object* v___x_412_; 
v_index_410_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_index_410_);
lean_dec_ref_known(v___x_409_, 3);
v_size_411_ = lean_ctor_get(v___y_408_, 0);
lean_inc(v_size_411_);
v___x_412_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_408_, v_size_411_, v_index_410_, v_fst_391_, v_snd_392_);
lean_dec(v_index_410_);
return v___x_412_;
}
case 1:
{
lean_object* v_index_413_; 
v_index_413_ = lean_ctor_get(v___x_409_, 0);
lean_inc(v_index_413_);
lean_dec_ref_known(v___x_409_, 1);
v___y_401_ = v___y_408_;
v_i_402_ = v_index_413_;
goto v___jp_400_;
}
default: 
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(0u);
v___x_415_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_408_, v___x_414_);
if (lean_obj_tag(v___x_415_) == 0)
{
lean_object* v_index_416_; 
v_index_416_ = lean_ctor_get(v___x_415_, 0);
lean_inc(v_index_416_);
lean_dec_ref_known(v___x_415_, 1);
v___y_401_ = v___y_408_;
v_i_402_ = v_index_416_;
goto v___jp_400_;
}
else
{
lean_dec(v_snd_392_);
lean_dec(v_fst_391_);
return v___y_408_;
}
}
}
}
v___jp_420_:
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_inc_ref(v_inst_388_);
lean_inc_ref(v_inst_387_);
v___x_421_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_387_, v_inst_388_, v_s_390_);
lean_inc(v_fst_391_);
v___x_422_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_387_, v_inst_388_, v___x_421_, v_fst_391_);
switch(lean_obj_tag(v___x_422_))
{
case 0:
{
lean_object* v_index_423_; lean_object* v_size_424_; lean_object* v___x_425_; 
v_index_423_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_index_423_);
lean_dec_ref_known(v___x_422_, 3);
v_size_424_ = lean_ctor_get(v___x_421_, 0);
lean_inc(v_size_424_);
v___x_425_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_421_, v_size_424_, v_index_423_, v_fst_391_, v_snd_392_);
lean_dec(v_index_423_);
return v___x_425_;
}
case 1:
{
lean_object* v_index_426_; 
v_index_426_ = lean_ctor_get(v___x_422_, 0);
lean_inc(v_index_426_);
lean_dec_ref_known(v___x_422_, 1);
v___y_394_ = v___x_421_;
v_i_395_ = v_index_426_;
goto v___jp_393_;
}
default: 
{
lean_object* v___x_427_; 
v___x_427_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_421_, v___x_419_);
if (lean_obj_tag(v___x_427_) == 0)
{
lean_object* v_index_428_; 
v_index_428_ = lean_ctor_get(v___x_427_, 0);
lean_inc(v_index_428_);
lean_dec_ref_known(v___x_427_, 1);
v___y_394_ = v___x_421_;
v_i_395_ = v_index_428_;
goto v___jp_393_;
}
else
{
lean_dec(v_snd_392_);
lean_dec(v_fst_391_);
return v___x_421_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg(lean_object* v_inst_454_, lean_object* v_inst_455_){
_start:
{
lean_object* v___f_456_; 
v___f_456_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_456_, 0, v_inst_454_);
lean_closure_set(v___f_456_, 1, v_inst_455_);
return v___f_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable(lean_object* v_00_u03b1_457_, lean_object* v_00_u03b2_458_, lean_object* v_inst_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v___f_461_; 
v___f_461_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instInsertSigmaOfBEqOfHashable___redArg___lam__0), 4, 2);
lean_closure_set(v___f_461_, 0, v_inst_459_);
lean_closure_set(v___f_461_, 1, v_inst_460_);
return v___f_461_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew___redArg(lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_m_464_, lean_object* v_a_465_, lean_object* v_b_466_){
_start:
{
lean_object* v___y_468_; lean_object* v_i_469_; lean_object* v___y_475_; lean_object* v___y_485_; lean_object* v_i_486_; lean_object* v_size_491_; lean_object* v_keyArray_492_; lean_object* v___x_493_; lean_object* v___x_503_; uint8_t v___x_504_; 
v_size_491_ = lean_ctor_get(v_m_464_, 0);
v_keyArray_492_ = lean_ctor_get(v_m_464_, 1);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_503_ = lean_array_get_size(v_keyArray_492_);
v___x_504_ = lean_nat_dec_lt(v___x_493_, v___x_503_);
if (v___x_504_ == 0)
{
lean_dec(v_b_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_inst_463_);
lean_dec_ref(v_inst_462_);
return v_m_464_;
}
else
{
lean_object* v___x_505_; 
lean_inc(v_a_465_);
lean_inc_ref(v_inst_463_);
lean_inc_ref(v_inst_462_);
v___x_505_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_462_, v_inst_463_, v_m_464_, v_a_465_);
switch(lean_obj_tag(v___x_505_))
{
case 0:
{
lean_dec_ref_known(v___x_505_, 3);
lean_dec(v_b_466_);
lean_dec(v_a_465_);
lean_dec_ref(v_inst_463_);
lean_dec_ref(v_inst_462_);
return v_m_464_;
}
case 1:
{
lean_object* v_index_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_index_506_ = lean_ctor_get(v___x_505_, 0);
lean_inc(v_index_506_);
lean_dec_ref_known(v___x_505_, 1);
v___x_507_ = lean_unsigned_to_nat(1u);
v___x_508_ = lean_nat_add(v_size_491_, v___x_507_);
v___x_509_ = lean_nat_dec_lt(v___x_508_, v___x_503_);
if (v___x_509_ == 0)
{
lean_dec(v___x_508_);
lean_dec(v_index_506_);
goto v___jp_494_;
}
else
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v___x_510_ = lean_unsigned_to_nat(4u);
v___x_511_ = lean_nat_mul(v___x_508_, v___x_510_);
v___x_512_ = lean_unsigned_to_nat(3u);
v___x_513_ = lean_nat_mul(v___x_503_, v___x_512_);
v___x_514_ = lean_nat_dec_le(v___x_511_, v___x_513_);
lean_dec(v___x_513_);
lean_dec(v___x_511_);
if (v___x_514_ == 0)
{
lean_dec(v___x_508_);
lean_dec(v_index_506_);
goto v___jp_494_;
}
else
{
lean_object* v___x_515_; 
lean_dec_ref(v_inst_463_);
lean_dec_ref(v_inst_462_);
v___x_515_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_464_, v___x_508_, v_index_506_, v_a_465_, v_b_466_);
lean_dec(v_index_506_);
return v___x_515_;
}
}
}
default: 
{
lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_516_ = lean_unsigned_to_nat(1u);
v___x_517_ = lean_nat_add(v_size_491_, v___x_516_);
v___x_518_ = lean_nat_dec_lt(v___x_517_, v___x_503_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
lean_dec(v___x_517_);
lean_inc_ref(v_inst_463_);
lean_inc_ref(v_inst_462_);
v___x_519_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_462_, v_inst_463_, v_m_464_);
v___y_475_ = v___x_519_;
goto v___jp_474_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_520_ = lean_unsigned_to_nat(4u);
v___x_521_ = lean_nat_mul(v___x_517_, v___x_520_);
lean_dec(v___x_517_);
v___x_522_ = lean_unsigned_to_nat(3u);
v___x_523_ = lean_nat_mul(v___x_503_, v___x_522_);
v___x_524_ = lean_nat_dec_le(v___x_521_, v___x_523_);
lean_dec(v___x_523_);
lean_dec(v___x_521_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; 
lean_inc_ref(v_inst_463_);
lean_inc_ref(v_inst_462_);
v___x_525_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_462_, v_inst_463_, v_m_464_);
v___y_475_ = v___x_525_;
goto v___jp_474_;
}
else
{
v___y_475_ = v_m_464_;
goto v___jp_474_;
}
}
}
}
}
v___jp_467_:
{
lean_object* v_size_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v_size_470_ = lean_ctor_get(v___y_468_, 0);
v___x_471_ = lean_unsigned_to_nat(1u);
v___x_472_ = lean_nat_add(v_size_470_, v___x_471_);
v___x_473_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_468_, v___x_472_, v_i_469_, v_a_465_, v_b_466_);
lean_dec(v_i_469_);
return v___x_473_;
}
v___jp_474_:
{
lean_object* v___x_476_; 
lean_inc(v_a_465_);
v___x_476_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_462_, v_inst_463_, v___y_475_, v_a_465_);
switch(lean_obj_tag(v___x_476_))
{
case 0:
{
lean_object* v_index_477_; lean_object* v_size_478_; lean_object* v___x_479_; 
v_index_477_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_index_477_);
lean_dec_ref_known(v___x_476_, 3);
v_size_478_ = lean_ctor_get(v___y_475_, 0);
lean_inc(v_size_478_);
v___x_479_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_475_, v_size_478_, v_index_477_, v_a_465_, v_b_466_);
lean_dec(v_index_477_);
return v___x_479_;
}
case 1:
{
lean_object* v_index_480_; 
v_index_480_ = lean_ctor_get(v___x_476_, 0);
lean_inc(v_index_480_);
lean_dec_ref_known(v___x_476_, 1);
v___y_468_ = v___y_475_;
v_i_469_ = v_index_480_;
goto v___jp_467_;
}
default: 
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_475_, v___x_481_);
if (lean_obj_tag(v___x_482_) == 0)
{
lean_object* v_index_483_; 
v_index_483_ = lean_ctor_get(v___x_482_, 0);
lean_inc(v_index_483_);
lean_dec_ref_known(v___x_482_, 1);
v___y_468_ = v___y_475_;
v_i_469_ = v_index_483_;
goto v___jp_467_;
}
else
{
lean_dec(v_b_466_);
lean_dec(v_a_465_);
return v___y_475_;
}
}
}
}
v___jp_484_:
{
lean_object* v_size_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v_size_487_ = lean_ctor_get(v___y_485_, 0);
v___x_488_ = lean_unsigned_to_nat(1u);
v___x_489_ = lean_nat_add(v_size_487_, v___x_488_);
v___x_490_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_485_, v___x_489_, v_i_486_, v_a_465_, v_b_466_);
lean_dec(v_i_486_);
return v___x_490_;
}
v___jp_494_:
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_inc_ref(v_inst_463_);
lean_inc_ref(v_inst_462_);
v___x_495_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_462_, v_inst_463_, v_m_464_);
lean_inc(v_a_465_);
v___x_496_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_462_, v_inst_463_, v___x_495_, v_a_465_);
switch(lean_obj_tag(v___x_496_))
{
case 0:
{
lean_object* v_index_497_; lean_object* v_size_498_; lean_object* v___x_499_; 
v_index_497_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_index_497_);
lean_dec_ref_known(v___x_496_, 3);
v_size_498_ = lean_ctor_get(v___x_495_, 0);
lean_inc(v_size_498_);
v___x_499_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_495_, v_size_498_, v_index_497_, v_a_465_, v_b_466_);
lean_dec(v_index_497_);
return v___x_499_;
}
case 1:
{
lean_object* v_index_500_; 
v_index_500_ = lean_ctor_get(v___x_496_, 0);
lean_inc(v_index_500_);
lean_dec_ref_known(v___x_496_, 1);
v___y_485_ = v___x_495_;
v_i_486_ = v_index_500_;
goto v___jp_484_;
}
default: 
{
lean_object* v___x_501_; 
v___x_501_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_495_, v___x_493_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_index_502_; 
v_index_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_index_502_);
lean_dec_ref_known(v___x_501_, 1);
v___y_485_ = v___x_495_;
v_i_486_ = v_index_502_;
goto v___jp_484_;
}
else
{
lean_dec(v_b_466_);
lean_dec(v_a_465_);
return v___x_495_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertIfNew(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_m_530_, lean_object* v_a_531_, lean_object* v_b_532_){
_start:
{
lean_object* v___y_534_; lean_object* v_i_535_; lean_object* v___y_541_; lean_object* v___y_551_; lean_object* v_i_552_; lean_object* v_size_557_; lean_object* v_keyArray_558_; lean_object* v___x_559_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_size_557_ = lean_ctor_get(v_m_530_, 0);
v_keyArray_558_ = lean_ctor_get(v_m_530_, 1);
v___x_559_ = lean_unsigned_to_nat(0u);
v___x_569_ = lean_array_get_size(v_keyArray_558_);
v___x_570_ = lean_nat_dec_lt(v___x_559_, v___x_569_);
if (v___x_570_ == 0)
{
lean_dec(v_b_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_inst_529_);
lean_dec_ref(v_inst_528_);
return v_m_530_;
}
else
{
lean_object* v___x_571_; 
lean_inc(v_a_531_);
lean_inc_ref(v_inst_529_);
lean_inc_ref(v_inst_528_);
v___x_571_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_528_, v_inst_529_, v_m_530_, v_a_531_);
switch(lean_obj_tag(v___x_571_))
{
case 0:
{
lean_dec_ref_known(v___x_571_, 3);
lean_dec(v_b_532_);
lean_dec(v_a_531_);
lean_dec_ref(v_inst_529_);
lean_dec_ref(v_inst_528_);
return v_m_530_;
}
case 1:
{
lean_object* v_index_572_; lean_object* v___x_573_; lean_object* v___x_574_; uint8_t v___x_575_; 
v_index_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc(v_index_572_);
lean_dec_ref_known(v___x_571_, 1);
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = lean_nat_add(v_size_557_, v___x_573_);
v___x_575_ = lean_nat_dec_lt(v___x_574_, v___x_569_);
if (v___x_575_ == 0)
{
lean_dec(v___x_574_);
lean_dec(v_index_572_);
goto v___jp_560_;
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_576_ = lean_unsigned_to_nat(4u);
v___x_577_ = lean_nat_mul(v___x_574_, v___x_576_);
v___x_578_ = lean_unsigned_to_nat(3u);
v___x_579_ = lean_nat_mul(v___x_569_, v___x_578_);
v___x_580_ = lean_nat_dec_le(v___x_577_, v___x_579_);
lean_dec(v___x_579_);
lean_dec(v___x_577_);
if (v___x_580_ == 0)
{
lean_dec(v___x_574_);
lean_dec(v_index_572_);
goto v___jp_560_;
}
else
{
lean_object* v___x_581_; 
lean_dec_ref(v_inst_529_);
lean_dec_ref(v_inst_528_);
v___x_581_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_530_, v___x_574_, v_index_572_, v_a_531_, v_b_532_);
lean_dec(v_index_572_);
return v___x_581_;
}
}
}
default: 
{
lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_582_ = lean_unsigned_to_nat(1u);
v___x_583_ = lean_nat_add(v_size_557_, v___x_582_);
v___x_584_ = lean_nat_dec_lt(v___x_583_, v___x_569_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; 
lean_dec(v___x_583_);
lean_inc_ref(v_inst_529_);
lean_inc_ref(v_inst_528_);
v___x_585_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_528_, v_inst_529_, v_m_530_);
v___y_541_ = v___x_585_;
goto v___jp_540_;
}
else
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_586_ = lean_unsigned_to_nat(4u);
v___x_587_ = lean_nat_mul(v___x_583_, v___x_586_);
lean_dec(v___x_583_);
v___x_588_ = lean_unsigned_to_nat(3u);
v___x_589_ = lean_nat_mul(v___x_569_, v___x_588_);
v___x_590_ = lean_nat_dec_le(v___x_587_, v___x_589_);
lean_dec(v___x_589_);
lean_dec(v___x_587_);
if (v___x_590_ == 0)
{
lean_object* v___x_591_; 
lean_inc_ref(v_inst_529_);
lean_inc_ref(v_inst_528_);
v___x_591_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_528_, v_inst_529_, v_m_530_);
v___y_541_ = v___x_591_;
goto v___jp_540_;
}
else
{
v___y_541_ = v_m_530_;
goto v___jp_540_;
}
}
}
}
}
v___jp_533_:
{
lean_object* v_size_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_size_536_ = lean_ctor_get(v___y_534_, 0);
v___x_537_ = lean_unsigned_to_nat(1u);
v___x_538_ = lean_nat_add(v_size_536_, v___x_537_);
v___x_539_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_534_, v___x_538_, v_i_535_, v_a_531_, v_b_532_);
lean_dec(v_i_535_);
return v___x_539_;
}
v___jp_540_:
{
lean_object* v___x_542_; 
lean_inc(v_a_531_);
v___x_542_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_528_, v_inst_529_, v___y_541_, v_a_531_);
switch(lean_obj_tag(v___x_542_))
{
case 0:
{
lean_object* v_index_543_; lean_object* v_size_544_; lean_object* v___x_545_; 
v_index_543_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_index_543_);
lean_dec_ref_known(v___x_542_, 3);
v_size_544_ = lean_ctor_get(v___y_541_, 0);
lean_inc(v_size_544_);
v___x_545_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_541_, v_size_544_, v_index_543_, v_a_531_, v_b_532_);
lean_dec(v_index_543_);
return v___x_545_;
}
case 1:
{
lean_object* v_index_546_; 
v_index_546_ = lean_ctor_get(v___x_542_, 0);
lean_inc(v_index_546_);
lean_dec_ref_known(v___x_542_, 1);
v___y_534_ = v___y_541_;
v_i_535_ = v_index_546_;
goto v___jp_533_;
}
default: 
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_541_, v___x_547_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_index_549_; 
v_index_549_ = lean_ctor_get(v___x_548_, 0);
lean_inc(v_index_549_);
lean_dec_ref_known(v___x_548_, 1);
v___y_534_ = v___y_541_;
v_i_535_ = v_index_549_;
goto v___jp_533_;
}
else
{
lean_dec(v_b_532_);
lean_dec(v_a_531_);
return v___y_541_;
}
}
}
}
v___jp_550_:
{
lean_object* v_size_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
v_size_553_ = lean_ctor_get(v___y_551_, 0);
v___x_554_ = lean_unsigned_to_nat(1u);
v___x_555_ = lean_nat_add(v_size_553_, v___x_554_);
v___x_556_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_551_, v___x_555_, v_i_552_, v_a_531_, v_b_532_);
lean_dec(v_i_552_);
return v___x_556_;
}
v___jp_560_:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
lean_inc_ref(v_inst_529_);
lean_inc_ref(v_inst_528_);
v___x_561_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_528_, v_inst_529_, v_m_530_);
lean_inc(v_a_531_);
v___x_562_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_528_, v_inst_529_, v___x_561_, v_a_531_);
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
v___x_565_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_561_, v_size_564_, v_index_563_, v_a_531_, v_b_532_);
lean_dec(v_index_563_);
return v___x_565_;
}
case 1:
{
lean_object* v_index_566_; 
v_index_566_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_index_566_);
lean_dec_ref_known(v___x_562_, 1);
v___y_551_ = v___x_561_;
v_i_552_ = v_index_566_;
goto v___jp_550_;
}
default: 
{
lean_object* v___x_567_; 
v___x_567_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_561_, v___x_559_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v_index_568_; 
v_index_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_index_568_);
lean_dec_ref_known(v___x_567_, 1);
v___y_551_ = v___x_561_;
v_i_552_ = v_index_568_;
goto v___jp_550_;
}
else
{
lean_dec(v_b_532_);
lean_dec(v_a_531_);
return v___x_561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert___redArg(lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_m_594_, lean_object* v_a_595_, lean_object* v_b_596_){
_start:
{
lean_object* v_size_597_; lean_object* v_keyArray_598_; lean_object* v___x_599_; lean_object* v___x_600_; uint8_t v___x_601_; 
v_size_597_ = lean_ctor_get(v_m_594_, 0);
v_keyArray_598_ = lean_ctor_get(v_m_594_, 1);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_array_get_size(v_keyArray_598_);
v___x_601_ = lean_nat_dec_lt(v___x_599_, v___x_600_);
if (v___x_601_ == 0)
{
lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_b_596_);
lean_dec(v_a_595_);
lean_dec_ref(v_inst_593_);
lean_dec_ref(v_inst_592_);
v___x_602_ = lean_box(v___x_601_);
v___x_603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_603_, 0, v___x_602_);
lean_ctor_set(v___x_603_, 1, v_m_594_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; 
lean_inc(v_a_595_);
lean_inc_ref(v_inst_593_);
lean_inc_ref(v_inst_592_);
v___x_604_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_592_, v_inst_593_, v_m_594_, v_a_595_);
switch(lean_obj_tag(v___x_604_))
{
case 0:
{
lean_object* v_index_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_inc(v_size_597_);
lean_dec_ref(v_inst_593_);
lean_dec_ref(v_inst_592_);
v_index_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_index_605_);
lean_dec_ref_known(v___x_604_, 3);
v___x_606_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_594_, v_size_597_, v_index_605_, v_a_595_, v_b_596_);
lean_dec(v_index_605_);
v___x_607_ = lean_box(v___x_601_);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v___x_606_);
return v___x_608_;
}
case 1:
{
lean_object* v_index_609_; uint8_t v___x_610_; lean_object* v___y_612_; lean_object* v_i_613_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v_index_609_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_index_609_);
lean_dec_ref_known(v___x_604_, 1);
v___x_610_ = 0;
v___x_633_ = lean_unsigned_to_nat(1u);
v___x_634_ = lean_nat_add(v_size_597_, v___x_633_);
v___x_635_ = lean_nat_dec_lt(v___x_634_, v___x_600_);
if (v___x_635_ == 0)
{
lean_dec(v___x_634_);
lean_dec(v_index_609_);
goto v___jp_620_;
}
else
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; uint8_t v___x_640_; 
v___x_636_ = lean_unsigned_to_nat(4u);
v___x_637_ = lean_nat_mul(v___x_634_, v___x_636_);
v___x_638_ = lean_unsigned_to_nat(3u);
v___x_639_ = lean_nat_mul(v___x_600_, v___x_638_);
v___x_640_ = lean_nat_dec_le(v___x_637_, v___x_639_);
lean_dec(v___x_639_);
lean_dec(v___x_637_);
if (v___x_640_ == 0)
{
lean_dec(v___x_634_);
lean_dec(v_index_609_);
goto v___jp_620_;
}
else
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec_ref(v_inst_593_);
lean_dec_ref(v_inst_592_);
v___x_641_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_594_, v___x_634_, v_index_609_, v_a_595_, v_b_596_);
lean_dec(v_index_609_);
v___x_642_ = lean_box(v___x_610_);
v___x_643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
lean_ctor_set(v___x_643_, 1, v___x_641_);
return v___x_643_;
}
}
v___jp_611_:
{
lean_object* v_size_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; 
v_size_614_ = lean_ctor_get(v___y_612_, 0);
v___x_615_ = lean_unsigned_to_nat(1u);
v___x_616_ = lean_nat_add(v_size_614_, v___x_615_);
v___x_617_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_612_, v___x_616_, v_i_613_, v_a_595_, v_b_596_);
lean_dec(v_i_613_);
v___x_618_ = lean_box(v___x_610_);
v___x_619_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v___x_617_);
return v___x_619_;
}
v___jp_620_:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_inc_ref(v_inst_593_);
lean_inc_ref(v_inst_592_);
v___x_621_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_592_, v_inst_593_, v_m_594_);
lean_inc(v_a_595_);
v___x_622_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_592_, v_inst_593_, v___x_621_, v_a_595_);
switch(lean_obj_tag(v___x_622_))
{
case 0:
{
lean_object* v_index_623_; lean_object* v_size_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v_index_623_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_index_623_);
lean_dec_ref_known(v___x_622_, 3);
v_size_624_ = lean_ctor_get(v___x_621_, 0);
lean_inc(v_size_624_);
v___x_625_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_621_, v_size_624_, v_index_623_, v_a_595_, v_b_596_);
lean_dec(v_index_623_);
v___x_626_ = lean_box(v___x_610_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_625_);
return v___x_627_;
}
case 1:
{
lean_object* v_index_628_; 
v_index_628_ = lean_ctor_get(v___x_622_, 0);
lean_inc(v_index_628_);
lean_dec_ref_known(v___x_622_, 1);
v___y_612_ = v___x_621_;
v_i_613_ = v_index_628_;
goto v___jp_611_;
}
default: 
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_621_, v___x_599_);
if (lean_obj_tag(v___x_629_) == 0)
{
lean_object* v_index_630_; 
v_index_630_ = lean_ctor_get(v___x_629_, 0);
lean_inc(v_index_630_);
lean_dec_ref_known(v___x_629_, 1);
v___y_612_ = v___x_621_;
v_i_613_ = v_index_630_;
goto v___jp_611_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v_b_596_);
lean_dec(v_a_595_);
v___x_631_ = lean_box(v___x_610_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_621_);
return v___x_632_;
}
}
}
}
}
default: 
{
uint8_t v___x_644_; lean_object* v___y_646_; lean_object* v_i_647_; lean_object* v___y_655_; lean_object* v___x_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v___x_644_ = 0;
v___x_667_ = lean_unsigned_to_nat(1u);
v___x_668_ = lean_nat_add(v_size_597_, v___x_667_);
v___x_669_ = lean_nat_dec_lt(v___x_668_, v___x_600_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; 
lean_dec(v___x_668_);
lean_inc_ref(v_inst_593_);
lean_inc_ref(v_inst_592_);
v___x_670_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_592_, v_inst_593_, v_m_594_);
v___y_655_ = v___x_670_;
goto v___jp_654_;
}
else
{
lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; uint8_t v___x_675_; 
v___x_671_ = lean_unsigned_to_nat(4u);
v___x_672_ = lean_nat_mul(v___x_668_, v___x_671_);
lean_dec(v___x_668_);
v___x_673_ = lean_unsigned_to_nat(3u);
v___x_674_ = lean_nat_mul(v___x_600_, v___x_673_);
v___x_675_ = lean_nat_dec_le(v___x_672_, v___x_674_);
lean_dec(v___x_674_);
lean_dec(v___x_672_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
lean_inc_ref(v_inst_593_);
lean_inc_ref(v_inst_592_);
v___x_676_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_592_, v_inst_593_, v_m_594_);
v___y_655_ = v___x_676_;
goto v___jp_654_;
}
else
{
v___y_655_ = v_m_594_;
goto v___jp_654_;
}
}
v___jp_645_:
{
lean_object* v_size_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v_size_648_ = lean_ctor_get(v___y_646_, 0);
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = lean_nat_add(v_size_648_, v___x_649_);
v___x_651_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_646_, v___x_650_, v_i_647_, v_a_595_, v_b_596_);
lean_dec(v_i_647_);
v___x_652_ = lean_box(v___x_644_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_652_);
lean_ctor_set(v___x_653_, 1, v___x_651_);
return v___x_653_;
}
v___jp_654_:
{
lean_object* v___x_656_; 
lean_inc(v_a_595_);
v___x_656_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_592_, v_inst_593_, v___y_655_, v_a_595_);
switch(lean_obj_tag(v___x_656_))
{
case 0:
{
lean_object* v_index_657_; lean_object* v_size_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v_index_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_index_657_);
lean_dec_ref_known(v___x_656_, 3);
v_size_658_ = lean_ctor_get(v___y_655_, 0);
lean_inc(v_size_658_);
v___x_659_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_655_, v_size_658_, v_index_657_, v_a_595_, v_b_596_);
lean_dec(v_index_657_);
v___x_660_ = lean_box(v___x_644_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v___x_659_);
return v___x_661_;
}
case 1:
{
lean_object* v_index_662_; 
v_index_662_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_index_662_);
lean_dec_ref_known(v___x_656_, 1);
v___y_646_ = v___y_655_;
v_i_647_ = v_index_662_;
goto v___jp_645_;
}
default: 
{
lean_object* v___x_663_; 
v___x_663_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_655_, v___x_599_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_index_664_; 
v_index_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_index_664_);
lean_dec_ref_known(v___x_663_, 1);
v___y_646_ = v___y_655_;
v_i_647_ = v_index_664_;
goto v___jp_645_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v_b_596_);
lean_dec(v_a_595_);
v___x_665_ = lean_box(v___x_644_);
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
lean_ctor_set(v___x_666_, 1, v___y_655_);
return v___x_666_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsert(lean_object* v_00_u03b1_677_, lean_object* v_00_u03b2_678_, lean_object* v_inst_679_, lean_object* v_inst_680_, lean_object* v_m_681_, lean_object* v_a_682_, lean_object* v_b_683_){
_start:
{
lean_object* v_size_684_; lean_object* v_keyArray_685_; lean_object* v___x_686_; lean_object* v___x_687_; uint8_t v___x_688_; 
v_size_684_ = lean_ctor_get(v_m_681_, 0);
v_keyArray_685_ = lean_ctor_get(v_m_681_, 1);
v___x_686_ = lean_unsigned_to_nat(0u);
v___x_687_ = lean_array_get_size(v_keyArray_685_);
v___x_688_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; lean_object* v___x_690_; 
lean_dec(v_b_683_);
lean_dec(v_a_682_);
lean_dec_ref(v_inst_680_);
lean_dec_ref(v_inst_679_);
v___x_689_ = lean_box(v___x_688_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v_m_681_);
return v___x_690_;
}
else
{
lean_object* v___x_691_; 
lean_inc(v_a_682_);
lean_inc_ref(v_inst_680_);
lean_inc_ref(v_inst_679_);
v___x_691_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_679_, v_inst_680_, v_m_681_, v_a_682_);
switch(lean_obj_tag(v___x_691_))
{
case 0:
{
lean_object* v_index_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
lean_inc(v_size_684_);
lean_dec_ref(v_inst_680_);
lean_dec_ref(v_inst_679_);
v_index_692_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_index_692_);
lean_dec_ref_known(v___x_691_, 3);
v___x_693_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_681_, v_size_684_, v_index_692_, v_a_682_, v_b_683_);
lean_dec(v_index_692_);
v___x_694_ = lean_box(v___x_688_);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_693_);
return v___x_695_;
}
case 1:
{
lean_object* v_index_696_; uint8_t v___x_697_; lean_object* v___y_699_; lean_object* v_i_700_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_index_696_ = lean_ctor_get(v___x_691_, 0);
lean_inc(v_index_696_);
lean_dec_ref_known(v___x_691_, 1);
v___x_697_ = 0;
v___x_720_ = lean_unsigned_to_nat(1u);
v___x_721_ = lean_nat_add(v_size_684_, v___x_720_);
v___x_722_ = lean_nat_dec_lt(v___x_721_, v___x_687_);
if (v___x_722_ == 0)
{
lean_dec(v___x_721_);
lean_dec(v_index_696_);
goto v___jp_707_;
}
else
{
lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_723_ = lean_unsigned_to_nat(4u);
v___x_724_ = lean_nat_mul(v___x_721_, v___x_723_);
v___x_725_ = lean_unsigned_to_nat(3u);
v___x_726_ = lean_nat_mul(v___x_687_, v___x_725_);
v___x_727_ = lean_nat_dec_le(v___x_724_, v___x_726_);
lean_dec(v___x_726_);
lean_dec(v___x_724_);
if (v___x_727_ == 0)
{
lean_dec(v___x_721_);
lean_dec(v_index_696_);
goto v___jp_707_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
lean_dec_ref(v_inst_680_);
lean_dec_ref(v_inst_679_);
v___x_728_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_681_, v___x_721_, v_index_696_, v_a_682_, v_b_683_);
lean_dec(v_index_696_);
v___x_729_ = lean_box(v___x_697_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
return v___x_730_;
}
}
v___jp_698_:
{
lean_object* v_size_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v_size_701_ = lean_ctor_get(v___y_699_, 0);
v___x_702_ = lean_unsigned_to_nat(1u);
v___x_703_ = lean_nat_add(v_size_701_, v___x_702_);
v___x_704_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_699_, v___x_703_, v_i_700_, v_a_682_, v_b_683_);
lean_dec(v_i_700_);
v___x_705_ = lean_box(v___x_697_);
v___x_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_706_, 0, v___x_705_);
lean_ctor_set(v___x_706_, 1, v___x_704_);
return v___x_706_;
}
v___jp_707_:
{
lean_object* v___x_708_; lean_object* v___x_709_; 
lean_inc_ref(v_inst_680_);
lean_inc_ref(v_inst_679_);
v___x_708_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_679_, v_inst_680_, v_m_681_);
lean_inc(v_a_682_);
v___x_709_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_679_, v_inst_680_, v___x_708_, v_a_682_);
switch(lean_obj_tag(v___x_709_))
{
case 0:
{
lean_object* v_index_710_; lean_object* v_size_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_index_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_index_710_);
lean_dec_ref_known(v___x_709_, 3);
v_size_711_ = lean_ctor_get(v___x_708_, 0);
lean_inc(v_size_711_);
v___x_712_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_708_, v_size_711_, v_index_710_, v_a_682_, v_b_683_);
lean_dec(v_index_710_);
v___x_713_ = lean_box(v___x_697_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v___x_712_);
return v___x_714_;
}
case 1:
{
lean_object* v_index_715_; 
v_index_715_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_index_715_);
lean_dec_ref_known(v___x_709_, 1);
v___y_699_ = v___x_708_;
v_i_700_ = v_index_715_;
goto v___jp_698_;
}
default: 
{
lean_object* v___x_716_; 
v___x_716_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_708_, v___x_686_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v_index_717_; 
v_index_717_ = lean_ctor_get(v___x_716_, 0);
lean_inc(v_index_717_);
lean_dec_ref_known(v___x_716_, 1);
v___y_699_ = v___x_708_;
v_i_700_ = v_index_717_;
goto v___jp_698_;
}
else
{
lean_object* v___x_718_; lean_object* v___x_719_; 
lean_dec(v_b_683_);
lean_dec(v_a_682_);
v___x_718_ = lean_box(v___x_697_);
v___x_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_719_, 0, v___x_718_);
lean_ctor_set(v___x_719_, 1, v___x_708_);
return v___x_719_;
}
}
}
}
}
default: 
{
uint8_t v___x_731_; lean_object* v___y_733_; lean_object* v_i_734_; lean_object* v___y_742_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_731_ = 0;
v___x_754_ = lean_unsigned_to_nat(1u);
v___x_755_ = lean_nat_add(v_size_684_, v___x_754_);
v___x_756_ = lean_nat_dec_lt(v___x_755_, v___x_687_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; 
lean_dec(v___x_755_);
lean_inc_ref(v_inst_680_);
lean_inc_ref(v_inst_679_);
v___x_757_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_679_, v_inst_680_, v_m_681_);
v___y_742_ = v___x_757_;
goto v___jp_741_;
}
else
{
lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_758_ = lean_unsigned_to_nat(4u);
v___x_759_ = lean_nat_mul(v___x_755_, v___x_758_);
lean_dec(v___x_755_);
v___x_760_ = lean_unsigned_to_nat(3u);
v___x_761_ = lean_nat_mul(v___x_687_, v___x_760_);
v___x_762_ = lean_nat_dec_le(v___x_759_, v___x_761_);
lean_dec(v___x_761_);
lean_dec(v___x_759_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
lean_inc_ref(v_inst_680_);
lean_inc_ref(v_inst_679_);
v___x_763_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_679_, v_inst_680_, v_m_681_);
v___y_742_ = v___x_763_;
goto v___jp_741_;
}
else
{
v___y_742_ = v_m_681_;
goto v___jp_741_;
}
}
v___jp_732_:
{
lean_object* v_size_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v_size_735_ = lean_ctor_get(v___y_733_, 0);
v___x_736_ = lean_unsigned_to_nat(1u);
v___x_737_ = lean_nat_add(v_size_735_, v___x_736_);
v___x_738_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_733_, v___x_737_, v_i_734_, v_a_682_, v_b_683_);
lean_dec(v_i_734_);
v___x_739_ = lean_box(v___x_731_);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
return v___x_740_;
}
v___jp_741_:
{
lean_object* v___x_743_; 
lean_inc(v_a_682_);
v___x_743_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_679_, v_inst_680_, v___y_742_, v_a_682_);
switch(lean_obj_tag(v___x_743_))
{
case 0:
{
lean_object* v_index_744_; lean_object* v_size_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v_index_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_index_744_);
lean_dec_ref_known(v___x_743_, 3);
v_size_745_ = lean_ctor_get(v___y_742_, 0);
lean_inc(v_size_745_);
v___x_746_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_742_, v_size_745_, v_index_744_, v_a_682_, v_b_683_);
lean_dec(v_index_744_);
v___x_747_ = lean_box(v___x_731_);
v___x_748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_748_, 0, v___x_747_);
lean_ctor_set(v___x_748_, 1, v___x_746_);
return v___x_748_;
}
case 1:
{
lean_object* v_index_749_; 
v_index_749_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_index_749_);
lean_dec_ref_known(v___x_743_, 1);
v___y_733_ = v___y_742_;
v_i_734_ = v_index_749_;
goto v___jp_732_;
}
default: 
{
lean_object* v___x_750_; 
v___x_750_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_742_, v___x_686_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_index_751_; 
v_index_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_index_751_);
lean_dec_ref_known(v___x_750_, 1);
v___y_733_ = v___y_742_;
v_i_734_ = v_index_751_;
goto v___jp_732_;
}
else
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec(v_b_683_);
lean_dec(v_a_682_);
v___x_752_ = lean_box(v___x_731_);
v___x_753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v___y_742_);
return v___x_753_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_764_, lean_object* v_inst_765_, lean_object* v_m_766_, lean_object* v_a_767_, lean_object* v_b_768_){
_start:
{
lean_object* v_size_769_; lean_object* v_keyArray_770_; lean_object* v___x_771_; lean_object* v___x_772_; uint8_t v___x_773_; 
v_size_769_ = lean_ctor_get(v_m_766_, 0);
v_keyArray_770_ = lean_ctor_get(v_m_766_, 1);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = lean_array_get_size(v_keyArray_770_);
v___x_773_ = lean_nat_dec_lt(v___x_771_, v___x_772_);
if (v___x_773_ == 0)
{
lean_object* v___x_774_; lean_object* v___x_775_; 
lean_dec(v_b_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_inst_765_);
lean_dec_ref(v_inst_764_);
v___x_774_ = lean_box(0);
v___x_775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v_m_766_);
return v___x_775_;
}
else
{
lean_object* v___x_776_; 
lean_inc(v_a_767_);
lean_inc_ref(v_inst_765_);
lean_inc_ref(v_inst_764_);
v___x_776_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_764_, v_inst_765_, v_m_766_, v_a_767_);
switch(lean_obj_tag(v___x_776_))
{
case 0:
{
lean_object* v_value_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
lean_dec(v_b_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_inst_765_);
lean_dec_ref(v_inst_764_);
v_value_777_ = lean_ctor_get(v___x_776_, 2);
lean_inc(v_value_777_);
lean_dec_ref_known(v___x_776_, 3);
v___x_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_778_, 0, v_value_777_);
v___x_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_778_);
lean_ctor_set(v___x_779_, 1, v_m_766_);
return v___x_779_;
}
case 1:
{
lean_object* v_index_780_; lean_object* v___x_781_; lean_object* v___y_783_; lean_object* v_i_784_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_index_780_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_index_780_);
lean_dec_ref_known(v___x_776_, 1);
v___x_781_ = lean_box(0);
v___x_801_ = lean_unsigned_to_nat(1u);
v___x_802_ = lean_nat_add(v_size_769_, v___x_801_);
v___x_803_ = lean_nat_dec_lt(v___x_802_, v___x_772_);
if (v___x_803_ == 0)
{
lean_dec(v___x_802_);
lean_dec(v_index_780_);
goto v___jp_790_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_804_ = lean_unsigned_to_nat(4u);
v___x_805_ = lean_nat_mul(v___x_802_, v___x_804_);
v___x_806_ = lean_unsigned_to_nat(3u);
v___x_807_ = lean_nat_mul(v___x_772_, v___x_806_);
v___x_808_ = lean_nat_dec_le(v___x_805_, v___x_807_);
lean_dec(v___x_807_);
lean_dec(v___x_805_);
if (v___x_808_ == 0)
{
lean_dec(v___x_802_);
lean_dec(v_index_780_);
goto v___jp_790_;
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v_inst_765_);
lean_dec_ref(v_inst_764_);
v___x_809_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_766_, v___x_802_, v_index_780_, v_a_767_, v_b_768_);
lean_dec(v_index_780_);
v___x_810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_781_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
return v___x_810_;
}
}
v___jp_782_:
{
lean_object* v_size_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_size_785_ = lean_ctor_get(v___y_783_, 0);
v___x_786_ = lean_unsigned_to_nat(1u);
v___x_787_ = lean_nat_add(v_size_785_, v___x_786_);
v___x_788_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_783_, v___x_787_, v_i_784_, v_a_767_, v_b_768_);
lean_dec(v_i_784_);
v___x_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_781_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
return v___x_789_;
}
v___jp_790_:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
lean_inc_ref(v_inst_765_);
lean_inc_ref(v_inst_764_);
v___x_791_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_764_, v_inst_765_, v_m_766_);
lean_inc(v_a_767_);
v___x_792_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_764_, v_inst_765_, v___x_791_, v_a_767_);
switch(lean_obj_tag(v___x_792_))
{
case 0:
{
lean_object* v_index_793_; lean_object* v_size_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v_index_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_index_793_);
lean_dec_ref_known(v___x_792_, 3);
v_size_794_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_size_794_);
v___x_795_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_791_, v_size_794_, v_index_793_, v_a_767_, v_b_768_);
lean_dec(v_index_793_);
v___x_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_781_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
return v___x_796_;
}
case 1:
{
lean_object* v_index_797_; 
v_index_797_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_index_797_);
lean_dec_ref_known(v___x_792_, 1);
v___y_783_ = v___x_791_;
v_i_784_ = v_index_797_;
goto v___jp_782_;
}
default: 
{
lean_object* v___x_798_; 
v___x_798_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_791_, v___x_771_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_index_799_; 
v_index_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_index_799_);
lean_dec_ref_known(v___x_798_, 1);
v___y_783_ = v___x_791_;
v_i_784_ = v_index_799_;
goto v___jp_782_;
}
else
{
lean_object* v___x_800_; 
lean_dec(v_b_768_);
lean_dec(v_a_767_);
v___x_800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_781_);
lean_ctor_set(v___x_800_, 1, v___x_791_);
return v___x_800_;
}
}
}
}
}
default: 
{
lean_object* v___x_811_; lean_object* v___y_813_; lean_object* v_i_814_; lean_object* v___y_821_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v___x_811_ = lean_box(0);
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_add(v_size_769_, v___x_831_);
v___x_833_ = lean_nat_dec_lt(v___x_832_, v___x_772_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; 
lean_dec(v___x_832_);
lean_inc_ref(v_inst_765_);
lean_inc_ref(v_inst_764_);
v___x_834_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_764_, v_inst_765_, v_m_766_);
v___y_821_ = v___x_834_;
goto v___jp_820_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_835_ = lean_unsigned_to_nat(4u);
v___x_836_ = lean_nat_mul(v___x_832_, v___x_835_);
lean_dec(v___x_832_);
v___x_837_ = lean_unsigned_to_nat(3u);
v___x_838_ = lean_nat_mul(v___x_772_, v___x_837_);
v___x_839_ = lean_nat_dec_le(v___x_836_, v___x_838_);
lean_dec(v___x_838_);
lean_dec(v___x_836_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
lean_inc_ref(v_inst_765_);
lean_inc_ref(v_inst_764_);
v___x_840_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_764_, v_inst_765_, v_m_766_);
v___y_821_ = v___x_840_;
goto v___jp_820_;
}
else
{
v___y_821_ = v_m_766_;
goto v___jp_820_;
}
}
v___jp_812_:
{
lean_object* v_size_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v_size_815_ = lean_ctor_get(v___y_813_, 0);
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = lean_nat_add(v_size_815_, v___x_816_);
v___x_818_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_813_, v___x_817_, v_i_814_, v_a_767_, v_b_768_);
lean_dec(v_i_814_);
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v___x_811_);
lean_ctor_set(v___x_819_, 1, v___x_818_);
return v___x_819_;
}
v___jp_820_:
{
lean_object* v___x_822_; 
lean_inc(v_a_767_);
v___x_822_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_764_, v_inst_765_, v___y_821_, v_a_767_);
switch(lean_obj_tag(v___x_822_))
{
case 0:
{
lean_object* v_index_823_; lean_object* v_size_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_index_823_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_index_823_);
lean_dec_ref_known(v___x_822_, 3);
v_size_824_ = lean_ctor_get(v___y_821_, 0);
lean_inc(v_size_824_);
v___x_825_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_821_, v_size_824_, v_index_823_, v_a_767_, v_b_768_);
lean_dec(v_index_823_);
v___x_826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_811_);
lean_ctor_set(v___x_826_, 1, v___x_825_);
return v___x_826_;
}
case 1:
{
lean_object* v_index_827_; 
v_index_827_ = lean_ctor_get(v___x_822_, 0);
lean_inc(v_index_827_);
lean_dec_ref_known(v___x_822_, 1);
v___y_813_ = v___y_821_;
v_i_814_ = v_index_827_;
goto v___jp_812_;
}
default: 
{
lean_object* v___x_828_; 
v___x_828_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_821_, v___x_771_);
if (lean_obj_tag(v___x_828_) == 0)
{
lean_object* v_index_829_; 
v_index_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_index_829_);
lean_dec_ref_known(v___x_828_, 1);
v___y_813_ = v___y_821_;
v_i_814_ = v_index_829_;
goto v___jp_812_;
}
else
{
lean_object* v___x_830_; 
lean_dec(v_b_768_);
lean_dec(v_a_767_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v___x_811_);
lean_ctor_set(v___x_830_, 1, v___y_821_);
return v___x_830_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_841_, lean_object* v_00_u03b2_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_m_846_, lean_object* v_a_847_, lean_object* v_b_848_){
_start:
{
lean_object* v_size_849_; lean_object* v_keyArray_850_; lean_object* v___x_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v_size_849_ = lean_ctor_get(v_m_846_, 0);
v_keyArray_850_ = lean_ctor_get(v_m_846_, 1);
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_array_get_size(v_keyArray_850_);
v___x_853_ = lean_nat_dec_lt(v___x_851_, v___x_852_);
if (v___x_853_ == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v_b_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_inst_844_);
lean_dec_ref(v_inst_843_);
v___x_854_ = lean_box(0);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v_m_846_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; 
lean_inc(v_a_847_);
lean_inc_ref(v_inst_844_);
lean_inc_ref(v_inst_843_);
v___x_856_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_843_, v_inst_844_, v_m_846_, v_a_847_);
switch(lean_obj_tag(v___x_856_))
{
case 0:
{
lean_object* v_value_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
lean_dec(v_b_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_inst_844_);
lean_dec_ref(v_inst_843_);
v_value_857_ = lean_ctor_get(v___x_856_, 2);
lean_inc(v_value_857_);
lean_dec_ref_known(v___x_856_, 3);
v___x_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_858_, 0, v_value_857_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v_m_846_);
return v___x_859_;
}
case 1:
{
lean_object* v_index_860_; lean_object* v___x_861_; lean_object* v___y_863_; lean_object* v_i_864_; lean_object* v___x_881_; lean_object* v___x_882_; uint8_t v___x_883_; 
v_index_860_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_index_860_);
lean_dec_ref_known(v___x_856_, 1);
v___x_861_ = lean_box(0);
v___x_881_ = lean_unsigned_to_nat(1u);
v___x_882_ = lean_nat_add(v_size_849_, v___x_881_);
v___x_883_ = lean_nat_dec_lt(v___x_882_, v___x_852_);
if (v___x_883_ == 0)
{
lean_dec(v___x_882_);
lean_dec(v_index_860_);
goto v___jp_870_;
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; uint8_t v___x_888_; 
v___x_884_ = lean_unsigned_to_nat(4u);
v___x_885_ = lean_nat_mul(v___x_882_, v___x_884_);
v___x_886_ = lean_unsigned_to_nat(3u);
v___x_887_ = lean_nat_mul(v___x_852_, v___x_886_);
v___x_888_ = lean_nat_dec_le(v___x_885_, v___x_887_);
lean_dec(v___x_887_);
lean_dec(v___x_885_);
if (v___x_888_ == 0)
{
lean_dec(v___x_882_);
lean_dec(v_index_860_);
goto v___jp_870_;
}
else
{
lean_object* v___x_889_; lean_object* v___x_890_; 
lean_dec_ref(v_inst_844_);
lean_dec_ref(v_inst_843_);
v___x_889_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_846_, v___x_882_, v_index_860_, v_a_847_, v_b_848_);
lean_dec(v_index_860_);
v___x_890_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_890_, 0, v___x_861_);
lean_ctor_set(v___x_890_, 1, v___x_889_);
return v___x_890_;
}
}
v___jp_862_:
{
lean_object* v_size_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_size_865_ = lean_ctor_get(v___y_863_, 0);
v___x_866_ = lean_unsigned_to_nat(1u);
v___x_867_ = lean_nat_add(v_size_865_, v___x_866_);
v___x_868_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_863_, v___x_867_, v_i_864_, v_a_847_, v_b_848_);
lean_dec(v_i_864_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_861_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
return v___x_869_;
}
v___jp_870_:
{
lean_object* v___x_871_; lean_object* v___x_872_; 
lean_inc_ref(v_inst_844_);
lean_inc_ref(v_inst_843_);
v___x_871_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_843_, v_inst_844_, v_m_846_);
lean_inc(v_a_847_);
v___x_872_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_843_, v_inst_844_, v___x_871_, v_a_847_);
switch(lean_obj_tag(v___x_872_))
{
case 0:
{
lean_object* v_index_873_; lean_object* v_size_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
v_index_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_index_873_);
lean_dec_ref_known(v___x_872_, 3);
v_size_874_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_size_874_);
v___x_875_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_871_, v_size_874_, v_index_873_, v_a_847_, v_b_848_);
lean_dec(v_index_873_);
v___x_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_861_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
return v___x_876_;
}
case 1:
{
lean_object* v_index_877_; 
v_index_877_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_index_877_);
lean_dec_ref_known(v___x_872_, 1);
v___y_863_ = v___x_871_;
v_i_864_ = v_index_877_;
goto v___jp_862_;
}
default: 
{
lean_object* v___x_878_; 
v___x_878_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_871_, v___x_851_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_index_879_; 
v_index_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_index_879_);
lean_dec_ref_known(v___x_878_, 1);
v___y_863_ = v___x_871_;
v_i_864_ = v_index_879_;
goto v___jp_862_;
}
else
{
lean_object* v___x_880_; 
lean_dec(v_b_848_);
lean_dec(v_a_847_);
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v___x_861_);
lean_ctor_set(v___x_880_, 1, v___x_871_);
return v___x_880_;
}
}
}
}
}
default: 
{
lean_object* v___x_891_; lean_object* v___y_893_; lean_object* v_i_894_; lean_object* v___y_901_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_891_ = lean_box(0);
v___x_911_ = lean_unsigned_to_nat(1u);
v___x_912_ = lean_nat_add(v_size_849_, v___x_911_);
v___x_913_ = lean_nat_dec_lt(v___x_912_, v___x_852_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; 
lean_dec(v___x_912_);
lean_inc_ref(v_inst_844_);
lean_inc_ref(v_inst_843_);
v___x_914_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_843_, v_inst_844_, v_m_846_);
v___y_901_ = v___x_914_;
goto v___jp_900_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_915_ = lean_unsigned_to_nat(4u);
v___x_916_ = lean_nat_mul(v___x_912_, v___x_915_);
lean_dec(v___x_912_);
v___x_917_ = lean_unsigned_to_nat(3u);
v___x_918_ = lean_nat_mul(v___x_852_, v___x_917_);
v___x_919_ = lean_nat_dec_le(v___x_916_, v___x_918_);
lean_dec(v___x_918_);
lean_dec(v___x_916_);
if (v___x_919_ == 0)
{
lean_object* v___x_920_; 
lean_inc_ref(v_inst_844_);
lean_inc_ref(v_inst_843_);
v___x_920_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_843_, v_inst_844_, v_m_846_);
v___y_901_ = v___x_920_;
goto v___jp_900_;
}
else
{
v___y_901_ = v_m_846_;
goto v___jp_900_;
}
}
v___jp_892_:
{
lean_object* v_size_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v_size_895_ = lean_ctor_get(v___y_893_, 0);
v___x_896_ = lean_unsigned_to_nat(1u);
v___x_897_ = lean_nat_add(v_size_895_, v___x_896_);
v___x_898_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_893_, v___x_897_, v_i_894_, v_a_847_, v_b_848_);
lean_dec(v_i_894_);
v___x_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_891_);
lean_ctor_set(v___x_899_, 1, v___x_898_);
return v___x_899_;
}
v___jp_900_:
{
lean_object* v___x_902_; 
lean_inc(v_a_847_);
v___x_902_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_843_, v_inst_844_, v___y_901_, v_a_847_);
switch(lean_obj_tag(v___x_902_))
{
case 0:
{
lean_object* v_index_903_; lean_object* v_size_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_index_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_index_903_);
lean_dec_ref_known(v___x_902_, 3);
v_size_904_ = lean_ctor_get(v___y_901_, 0);
lean_inc(v_size_904_);
v___x_905_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_901_, v_size_904_, v_index_903_, v_a_847_, v_b_848_);
lean_dec(v_index_903_);
v___x_906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_891_);
lean_ctor_set(v___x_906_, 1, v___x_905_);
return v___x_906_;
}
case 1:
{
lean_object* v_index_907_; 
v_index_907_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_index_907_);
lean_dec_ref_known(v___x_902_, 1);
v___y_893_ = v___y_901_;
v_i_894_ = v_index_907_;
goto v___jp_892_;
}
default: 
{
lean_object* v___x_908_; 
v___x_908_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_901_, v___x_851_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_index_909_; 
v_index_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_index_909_);
lean_dec_ref_known(v___x_908_, 1);
v___y_893_ = v___y_901_;
v_i_894_ = v_index_909_;
goto v___jp_892_;
}
else
{
lean_object* v___x_910_; 
lean_dec(v_b_848_);
lean_dec(v_a_847_);
v___x_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_891_);
lean_ctor_set(v___x_910_, 1, v___y_901_);
return v___x_910_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew___redArg(lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_m_923_, lean_object* v_a_924_, lean_object* v_b_925_){
_start:
{
lean_object* v_size_926_; lean_object* v_keyArray_927_; lean_object* v___x_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_size_926_ = lean_ctor_get(v_m_923_, 0);
v_keyArray_927_ = lean_ctor_get(v_m_923_, 1);
v___x_928_ = lean_unsigned_to_nat(0u);
v___x_929_ = lean_array_get_size(v_keyArray_927_);
v___x_930_ = lean_nat_dec_lt(v___x_928_, v___x_929_);
if (v___x_930_ == 0)
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_b_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_inst_921_);
v___x_931_ = lean_box(v___x_930_);
v___x_932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_931_);
lean_ctor_set(v___x_932_, 1, v_m_923_);
return v___x_932_;
}
else
{
lean_object* v___x_933_; 
lean_inc(v_a_924_);
lean_inc_ref(v_inst_922_);
lean_inc_ref(v_inst_921_);
v___x_933_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_921_, v_inst_922_, v_m_923_, v_a_924_);
switch(lean_obj_tag(v___x_933_))
{
case 0:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
lean_dec_ref_known(v___x_933_, 3);
lean_dec(v_b_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_inst_921_);
v___x_934_ = lean_box(v___x_930_);
v___x_935_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v_m_923_);
return v___x_935_;
}
case 1:
{
lean_object* v_index_936_; uint8_t v___x_937_; lean_object* v___y_939_; lean_object* v_i_940_; lean_object* v___x_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_index_936_ = lean_ctor_get(v___x_933_, 0);
lean_inc(v_index_936_);
lean_dec_ref_known(v___x_933_, 1);
v___x_937_ = 0;
v___x_960_ = lean_unsigned_to_nat(1u);
v___x_961_ = lean_nat_add(v_size_926_, v___x_960_);
v___x_962_ = lean_nat_dec_lt(v___x_961_, v___x_929_);
if (v___x_962_ == 0)
{
lean_dec(v___x_961_);
lean_dec(v_index_936_);
goto v___jp_947_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; uint8_t v___x_967_; 
v___x_963_ = lean_unsigned_to_nat(4u);
v___x_964_ = lean_nat_mul(v___x_961_, v___x_963_);
v___x_965_ = lean_unsigned_to_nat(3u);
v___x_966_ = lean_nat_mul(v___x_929_, v___x_965_);
v___x_967_ = lean_nat_dec_le(v___x_964_, v___x_966_);
lean_dec(v___x_966_);
lean_dec(v___x_964_);
if (v___x_967_ == 0)
{
lean_dec(v___x_961_);
lean_dec(v_index_936_);
goto v___jp_947_;
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec_ref(v_inst_922_);
lean_dec_ref(v_inst_921_);
v___x_968_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_923_, v___x_961_, v_index_936_, v_a_924_, v_b_925_);
lean_dec(v_index_936_);
v___x_969_ = lean_box(v___x_937_);
v___x_970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
lean_ctor_set(v___x_970_, 1, v___x_968_);
return v___x_970_;
}
}
v___jp_938_:
{
lean_object* v_size_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v_size_941_ = lean_ctor_get(v___y_939_, 0);
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_nat_add(v_size_941_, v___x_942_);
v___x_944_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_939_, v___x_943_, v_i_940_, v_a_924_, v_b_925_);
lean_dec(v_i_940_);
v___x_945_ = lean_box(v___x_937_);
v___x_946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_946_, 0, v___x_945_);
lean_ctor_set(v___x_946_, 1, v___x_944_);
return v___x_946_;
}
v___jp_947_:
{
lean_object* v___x_948_; lean_object* v___x_949_; 
lean_inc_ref(v_inst_922_);
lean_inc_ref(v_inst_921_);
v___x_948_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_921_, v_inst_922_, v_m_923_);
lean_inc(v_a_924_);
v___x_949_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_921_, v_inst_922_, v___x_948_, v_a_924_);
switch(lean_obj_tag(v___x_949_))
{
case 0:
{
lean_object* v_index_950_; lean_object* v_size_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; 
v_index_950_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_index_950_);
lean_dec_ref_known(v___x_949_, 3);
v_size_951_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_size_951_);
v___x_952_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_948_, v_size_951_, v_index_950_, v_a_924_, v_b_925_);
lean_dec(v_index_950_);
v___x_953_ = lean_box(v___x_937_);
v___x_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_954_, 0, v___x_953_);
lean_ctor_set(v___x_954_, 1, v___x_952_);
return v___x_954_;
}
case 1:
{
lean_object* v_index_955_; 
v_index_955_ = lean_ctor_get(v___x_949_, 0);
lean_inc(v_index_955_);
lean_dec_ref_known(v___x_949_, 1);
v___y_939_ = v___x_948_;
v_i_940_ = v_index_955_;
goto v___jp_938_;
}
default: 
{
lean_object* v___x_956_; 
v___x_956_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_948_, v___x_928_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_index_957_; 
v_index_957_ = lean_ctor_get(v___x_956_, 0);
lean_inc(v_index_957_);
lean_dec_ref_known(v___x_956_, 1);
v___y_939_ = v___x_948_;
v_i_940_ = v_index_957_;
goto v___jp_938_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v_b_925_);
lean_dec(v_a_924_);
v___x_958_ = lean_box(v___x_937_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_948_);
return v___x_959_;
}
}
}
}
}
default: 
{
uint8_t v___x_971_; lean_object* v___y_973_; lean_object* v_i_974_; lean_object* v___y_982_; lean_object* v___x_994_; lean_object* v___x_995_; uint8_t v___x_996_; 
v___x_971_ = 0;
v___x_994_ = lean_unsigned_to_nat(1u);
v___x_995_ = lean_nat_add(v_size_926_, v___x_994_);
v___x_996_ = lean_nat_dec_lt(v___x_995_, v___x_929_);
if (v___x_996_ == 0)
{
lean_object* v___x_997_; 
lean_dec(v___x_995_);
lean_inc_ref(v_inst_922_);
lean_inc_ref(v_inst_921_);
v___x_997_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_921_, v_inst_922_, v_m_923_);
v___y_982_ = v___x_997_;
goto v___jp_981_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_998_ = lean_unsigned_to_nat(4u);
v___x_999_ = lean_nat_mul(v___x_995_, v___x_998_);
lean_dec(v___x_995_);
v___x_1000_ = lean_unsigned_to_nat(3u);
v___x_1001_ = lean_nat_mul(v___x_929_, v___x_1000_);
v___x_1002_ = lean_nat_dec_le(v___x_999_, v___x_1001_);
lean_dec(v___x_1001_);
lean_dec(v___x_999_);
if (v___x_1002_ == 0)
{
lean_object* v___x_1003_; 
lean_inc_ref(v_inst_922_);
lean_inc_ref(v_inst_921_);
v___x_1003_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_921_, v_inst_922_, v_m_923_);
v___y_982_ = v___x_1003_;
goto v___jp_981_;
}
else
{
v___y_982_ = v_m_923_;
goto v___jp_981_;
}
}
v___jp_972_:
{
lean_object* v_size_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_size_975_ = lean_ctor_get(v___y_973_, 0);
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = lean_nat_add(v_size_975_, v___x_976_);
v___x_978_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_973_, v___x_977_, v_i_974_, v_a_924_, v_b_925_);
lean_dec(v_i_974_);
v___x_979_ = lean_box(v___x_971_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v___x_978_);
return v___x_980_;
}
v___jp_981_:
{
lean_object* v___x_983_; 
lean_inc(v_a_924_);
v___x_983_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_921_, v_inst_922_, v___y_982_, v_a_924_);
switch(lean_obj_tag(v___x_983_))
{
case 0:
{
lean_object* v_index_984_; lean_object* v_size_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_index_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_index_984_);
lean_dec_ref_known(v___x_983_, 3);
v_size_985_ = lean_ctor_get(v___y_982_, 0);
lean_inc(v_size_985_);
v___x_986_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_982_, v_size_985_, v_index_984_, v_a_924_, v_b_925_);
lean_dec(v_index_984_);
v___x_987_ = lean_box(v___x_971_);
v___x_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_988_, 0, v___x_987_);
lean_ctor_set(v___x_988_, 1, v___x_986_);
return v___x_988_;
}
case 1:
{
lean_object* v_index_989_; 
v_index_989_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_index_989_);
lean_dec_ref_known(v___x_983_, 1);
v___y_973_ = v___y_982_;
v_i_974_ = v_index_989_;
goto v___jp_972_;
}
default: 
{
lean_object* v___x_990_; 
v___x_990_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_982_, v___x_928_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_index_991_; 
v_index_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_index_991_);
lean_dec_ref_known(v___x_990_, 1);
v___y_973_ = v___y_982_;
v_i_974_ = v_index_991_;
goto v___jp_972_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec(v_b_925_);
lean_dec(v_a_924_);
v___x_992_ = lean_box(v___x_971_);
v___x_993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v___y_982_);
return v___x_993_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_containsThenInsertIfNew(lean_object* v_00_u03b1_1004_, lean_object* v_00_u03b2_1005_, lean_object* v_inst_1006_, lean_object* v_inst_1007_, lean_object* v_m_1008_, lean_object* v_a_1009_, lean_object* v_b_1010_){
_start:
{
lean_object* v_size_1011_; lean_object* v_keyArray_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; uint8_t v___x_1015_; 
v_size_1011_ = lean_ctor_get(v_m_1008_, 0);
v_keyArray_1012_ = lean_ctor_get(v_m_1008_, 1);
v___x_1013_ = lean_unsigned_to_nat(0u);
v___x_1014_ = lean_array_get_size(v_keyArray_1012_);
v___x_1015_ = lean_nat_dec_lt(v___x_1013_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
lean_dec(v_b_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_inst_1007_);
lean_dec_ref(v_inst_1006_);
v___x_1016_ = lean_box(v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v_m_1008_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; 
lean_inc(v_a_1009_);
lean_inc_ref(v_inst_1007_);
lean_inc_ref(v_inst_1006_);
v___x_1018_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1006_, v_inst_1007_, v_m_1008_, v_a_1009_);
switch(lean_obj_tag(v___x_1018_))
{
case 0:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec_ref_known(v___x_1018_, 3);
lean_dec(v_b_1010_);
lean_dec(v_a_1009_);
lean_dec_ref(v_inst_1007_);
lean_dec_ref(v_inst_1006_);
v___x_1019_ = lean_box(v___x_1015_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_m_1008_);
return v___x_1020_;
}
case 1:
{
lean_object* v_index_1021_; uint8_t v___x_1022_; lean_object* v___y_1024_; lean_object* v_i_1025_; lean_object* v___x_1045_; lean_object* v___x_1046_; uint8_t v___x_1047_; 
v_index_1021_ = lean_ctor_get(v___x_1018_, 0);
lean_inc(v_index_1021_);
lean_dec_ref_known(v___x_1018_, 1);
v___x_1022_ = 0;
v___x_1045_ = lean_unsigned_to_nat(1u);
v___x_1046_ = lean_nat_add(v_size_1011_, v___x_1045_);
v___x_1047_ = lean_nat_dec_lt(v___x_1046_, v___x_1014_);
if (v___x_1047_ == 0)
{
lean_dec(v___x_1046_);
lean_dec(v_index_1021_);
goto v___jp_1032_;
}
else
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1048_ = lean_unsigned_to_nat(4u);
v___x_1049_ = lean_nat_mul(v___x_1046_, v___x_1048_);
v___x_1050_ = lean_unsigned_to_nat(3u);
v___x_1051_ = lean_nat_mul(v___x_1014_, v___x_1050_);
v___x_1052_ = lean_nat_dec_le(v___x_1049_, v___x_1051_);
lean_dec(v___x_1051_);
lean_dec(v___x_1049_);
if (v___x_1052_ == 0)
{
lean_dec(v___x_1046_);
lean_dec(v_index_1021_);
goto v___jp_1032_;
}
else
{
lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
lean_dec_ref(v_inst_1007_);
lean_dec_ref(v_inst_1006_);
v___x_1053_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1008_, v___x_1046_, v_index_1021_, v_a_1009_, v_b_1010_);
lean_dec(v_index_1021_);
v___x_1054_ = lean_box(v___x_1022_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v___x_1053_);
return v___x_1055_;
}
}
v___jp_1023_:
{
lean_object* v_size_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v_size_1026_ = lean_ctor_get(v___y_1024_, 0);
v___x_1027_ = lean_unsigned_to_nat(1u);
v___x_1028_ = lean_nat_add(v_size_1026_, v___x_1027_);
v___x_1029_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1024_, v___x_1028_, v_i_1025_, v_a_1009_, v_b_1010_);
lean_dec(v_i_1025_);
v___x_1030_ = lean_box(v___x_1022_);
v___x_1031_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
lean_ctor_set(v___x_1031_, 1, v___x_1029_);
return v___x_1031_;
}
v___jp_1032_:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
lean_inc_ref(v_inst_1007_);
lean_inc_ref(v_inst_1006_);
v___x_1033_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1006_, v_inst_1007_, v_m_1008_);
lean_inc(v_a_1009_);
v___x_1034_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1006_, v_inst_1007_, v___x_1033_, v_a_1009_);
switch(lean_obj_tag(v___x_1034_))
{
case 0:
{
lean_object* v_index_1035_; lean_object* v_size_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_index_1035_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_index_1035_);
lean_dec_ref_known(v___x_1034_, 3);
v_size_1036_ = lean_ctor_get(v___x_1033_, 0);
lean_inc(v_size_1036_);
v___x_1037_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1033_, v_size_1036_, v_index_1035_, v_a_1009_, v_b_1010_);
lean_dec(v_index_1035_);
v___x_1038_ = lean_box(v___x_1022_);
v___x_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
lean_ctor_set(v___x_1039_, 1, v___x_1037_);
return v___x_1039_;
}
case 1:
{
lean_object* v_index_1040_; 
v_index_1040_ = lean_ctor_get(v___x_1034_, 0);
lean_inc(v_index_1040_);
lean_dec_ref_known(v___x_1034_, 1);
v___y_1024_ = v___x_1033_;
v_i_1025_ = v_index_1040_;
goto v___jp_1023_;
}
default: 
{
lean_object* v___x_1041_; 
v___x_1041_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1033_, v___x_1013_);
if (lean_obj_tag(v___x_1041_) == 0)
{
lean_object* v_index_1042_; 
v_index_1042_ = lean_ctor_get(v___x_1041_, 0);
lean_inc(v_index_1042_);
lean_dec_ref_known(v___x_1041_, 1);
v___y_1024_ = v___x_1033_;
v_i_1025_ = v_index_1042_;
goto v___jp_1023_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v_b_1010_);
lean_dec(v_a_1009_);
v___x_1043_ = lean_box(v___x_1022_);
v___x_1044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1043_);
lean_ctor_set(v___x_1044_, 1, v___x_1033_);
return v___x_1044_;
}
}
}
}
}
default: 
{
uint8_t v___x_1056_; lean_object* v___y_1058_; lean_object* v_i_1059_; lean_object* v___y_1067_; lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1056_ = 0;
v___x_1079_ = lean_unsigned_to_nat(1u);
v___x_1080_ = lean_nat_add(v_size_1011_, v___x_1079_);
v___x_1081_ = lean_nat_dec_lt(v___x_1080_, v___x_1014_);
if (v___x_1081_ == 0)
{
lean_object* v___x_1082_; 
lean_dec(v___x_1080_);
lean_inc_ref(v_inst_1007_);
lean_inc_ref(v_inst_1006_);
v___x_1082_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1006_, v_inst_1007_, v_m_1008_);
v___y_1067_ = v___x_1082_;
goto v___jp_1066_;
}
else
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; uint8_t v___x_1087_; 
v___x_1083_ = lean_unsigned_to_nat(4u);
v___x_1084_ = lean_nat_mul(v___x_1080_, v___x_1083_);
lean_dec(v___x_1080_);
v___x_1085_ = lean_unsigned_to_nat(3u);
v___x_1086_ = lean_nat_mul(v___x_1014_, v___x_1085_);
v___x_1087_ = lean_nat_dec_le(v___x_1084_, v___x_1086_);
lean_dec(v___x_1086_);
lean_dec(v___x_1084_);
if (v___x_1087_ == 0)
{
lean_object* v___x_1088_; 
lean_inc_ref(v_inst_1007_);
lean_inc_ref(v_inst_1006_);
v___x_1088_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1006_, v_inst_1007_, v_m_1008_);
v___y_1067_ = v___x_1088_;
goto v___jp_1066_;
}
else
{
v___y_1067_ = v_m_1008_;
goto v___jp_1066_;
}
}
v___jp_1057_:
{
lean_object* v_size_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v_size_1060_ = lean_ctor_get(v___y_1058_, 0);
v___x_1061_ = lean_unsigned_to_nat(1u);
v___x_1062_ = lean_nat_add(v_size_1060_, v___x_1061_);
v___x_1063_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1058_, v___x_1062_, v_i_1059_, v_a_1009_, v_b_1010_);
lean_dec(v_i_1059_);
v___x_1064_ = lean_box(v___x_1056_);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v___x_1063_);
return v___x_1065_;
}
v___jp_1066_:
{
lean_object* v___x_1068_; 
lean_inc(v_a_1009_);
v___x_1068_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1006_, v_inst_1007_, v___y_1067_, v_a_1009_);
switch(lean_obj_tag(v___x_1068_))
{
case 0:
{
lean_object* v_index_1069_; lean_object* v_size_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; 
v_index_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_index_1069_);
lean_dec_ref_known(v___x_1068_, 3);
v_size_1070_ = lean_ctor_get(v___y_1067_, 0);
lean_inc(v_size_1070_);
v___x_1071_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1067_, v_size_1070_, v_index_1069_, v_a_1009_, v_b_1010_);
lean_dec(v_index_1069_);
v___x_1072_ = lean_box(v___x_1056_);
v___x_1073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v___x_1071_);
return v___x_1073_;
}
case 1:
{
lean_object* v_index_1074_; 
v_index_1074_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_index_1074_);
lean_dec_ref_known(v___x_1068_, 1);
v___y_1058_ = v___y_1067_;
v_i_1059_ = v_index_1074_;
goto v___jp_1057_;
}
default: 
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1067_, v___x_1013_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_index_1076_; 
v_index_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_index_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v___y_1058_ = v___y_1067_;
v_i_1059_ = v_index_1076_;
goto v___jp_1057_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec(v_b_1010_);
lean_dec(v_a_1009_);
v___x_1077_ = lean_box(v___x_1056_);
v___x_1078_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v___y_1067_);
return v___x_1078_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg(lean_object* v_inst_1089_, lean_object* v_inst_1090_, lean_object* v_m_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_keyArray_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v_keyArray_1093_ = lean_ctor_get(v_m_1091_, 1);
v___x_1094_ = lean_unsigned_to_nat(0u);
v___x_1095_ = lean_array_get_size(v_keyArray_1093_);
v___x_1096_ = lean_nat_dec_lt(v___x_1094_, v___x_1095_);
if (v___x_1096_ == 0)
{
lean_object* v___x_1097_; 
lean_dec(v_a_1092_);
lean_dec_ref(v_inst_1090_);
lean_dec_ref(v_inst_1089_);
v___x_1097_ = lean_box(0);
return v___x_1097_;
}
else
{
lean_object* v___x_1098_; 
v___x_1098_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1089_, v_inst_1090_, v_m_1091_, v_a_1092_);
return v___x_1098_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___redArg___boxed(lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_m_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v_res_1103_; 
v_res_1103_ = l_Std_DHashMap_Raw_get_x3f___redArg(v_inst_1099_, v_inst_1100_, v_m_1101_, v_a_1102_);
lean_dec_ref(v_m_1101_);
return v_res_1103_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f(lean_object* v_00_u03b1_1104_, lean_object* v_00_u03b2_1105_, lean_object* v_inst_1106_, lean_object* v_inst_1107_, lean_object* v_inst_1108_, lean_object* v_m_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v_keyArray_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_keyArray_1111_ = lean_ctor_get(v_m_1109_, 1);
v___x_1112_ = lean_unsigned_to_nat(0u);
v___x_1113_ = lean_array_get_size(v_keyArray_1111_);
v___x_1114_ = lean_nat_dec_lt(v___x_1112_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_object* v___x_1115_; 
lean_dec(v_a_1110_);
lean_dec_ref(v_inst_1108_);
lean_dec_ref(v_inst_1106_);
v___x_1115_ = lean_box(0);
return v___x_1115_;
}
else
{
lean_object* v___x_1116_; 
v___x_1116_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1106_, v_inst_1108_, v_m_1109_, v_a_1110_);
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x3f___boxed(lean_object* v_00_u03b1_1117_, lean_object* v_00_u03b2_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_m_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v_res_1124_; 
v_res_1124_ = l_Std_DHashMap_Raw_get_x3f(v_00_u03b1_1117_, v_00_u03b2_1118_, v_inst_1119_, v_inst_1120_, v_inst_1121_, v_m_1122_, v_a_1123_);
lean_dec_ref(v_m_1122_);
return v_res_1124_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains___redArg(lean_object* v_inst_1125_, lean_object* v_inst_1126_, lean_object* v_m_1127_, lean_object* v_a_1128_){
_start:
{
lean_object* v_keyArray_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_keyArray_1129_ = lean_ctor_get(v_m_1127_, 1);
v___x_1130_ = lean_unsigned_to_nat(0u);
v___x_1131_ = lean_array_get_size(v_keyArray_1129_);
v___x_1132_ = lean_nat_dec_lt(v___x_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_dec(v_a_1128_);
lean_dec_ref(v_inst_1126_);
lean_dec_ref(v_inst_1125_);
return v___x_1132_;
}
else
{
uint8_t v___x_1133_; 
v___x_1133_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1125_, v_inst_1126_, v_m_1127_, v_a_1128_);
return v___x_1133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___redArg___boxed(lean_object* v_inst_1134_, lean_object* v_inst_1135_, lean_object* v_m_1136_, lean_object* v_a_1137_){
_start:
{
uint8_t v_res_1138_; lean_object* v_r_1139_; 
v_res_1138_ = l_Std_DHashMap_Raw_contains___redArg(v_inst_1134_, v_inst_1135_, v_m_1136_, v_a_1137_);
lean_dec_ref(v_m_1136_);
v_r_1139_ = lean_box(v_res_1138_);
return v_r_1139_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_contains(lean_object* v_00_u03b1_1140_, lean_object* v_00_u03b2_1141_, lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_m_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v_keyArray_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; uint8_t v___x_1149_; 
v_keyArray_1146_ = lean_ctor_get(v_m_1144_, 1);
v___x_1147_ = lean_unsigned_to_nat(0u);
v___x_1148_ = lean_array_get_size(v_keyArray_1146_);
v___x_1149_ = lean_nat_dec_lt(v___x_1147_, v___x_1148_);
if (v___x_1149_ == 0)
{
lean_dec(v_a_1145_);
lean_dec_ref(v_inst_1143_);
lean_dec_ref(v_inst_1142_);
return v___x_1149_;
}
else
{
uint8_t v___x_1150_; 
v___x_1150_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1142_, v_inst_1143_, v_m_1144_, v_a_1145_);
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_contains___boxed(lean_object* v_00_u03b1_1151_, lean_object* v_00_u03b2_1152_, lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_m_1155_, lean_object* v_a_1156_){
_start:
{
uint8_t v_res_1157_; lean_object* v_r_1158_; 
v_res_1157_ = l_Std_DHashMap_Raw_contains(v_00_u03b1_1151_, v_00_u03b2_1152_, v_inst_1153_, v_inst_1154_, v_m_1155_, v_a_1156_);
lean_dec_ref(v_m_1155_);
v_r_1158_ = lean_box(v_res_1157_);
return v_r_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(lean_object* v_00_u03b1_1159_, lean_object* v_00_u03b2_1160_, lean_object* v_inst_1161_, lean_object* v_inst_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = lean_box(0);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable___boxed(lean_object* v_00_u03b1_1164_, lean_object* v_00_u03b2_1165_, lean_object* v_inst_1166_, lean_object* v_inst_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l_Std_DHashMap_Raw_instMembershipOfBEqOfHashable(v_00_u03b1_1164_, v_00_u03b2_1165_, v_inst_1166_, v_inst_1167_);
lean_dec_ref(v_inst_1167_);
lean_dec_ref(v_inst_1166_);
return v_res_1168_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem___redArg(lean_object* v_inst_1169_, lean_object* v_inst_1170_, lean_object* v_m_1171_, lean_object* v_a_1172_){
_start:
{
lean_object* v_keyArray_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; uint8_t v___x_1176_; 
v_keyArray_1173_ = lean_ctor_get(v_m_1171_, 1);
v___x_1174_ = lean_unsigned_to_nat(0u);
v___x_1175_ = lean_array_get_size(v_keyArray_1173_);
v___x_1176_ = lean_nat_dec_lt(v___x_1174_, v___x_1175_);
if (v___x_1176_ == 0)
{
lean_dec(v_a_1172_);
lean_dec_ref(v_inst_1170_);
lean_dec_ref(v_inst_1169_);
return v___x_1176_;
}
else
{
uint8_t v___x_1177_; 
v___x_1177_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_1169_, v_inst_1170_, v_m_1171_, v_a_1172_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___redArg___boxed(lean_object* v_inst_1178_, lean_object* v_inst_1179_, lean_object* v_m_1180_, lean_object* v_a_1181_){
_start:
{
uint8_t v_res_1182_; lean_object* v_r_1183_; 
v_res_1182_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_1178_, v_inst_1179_, v_m_1180_, v_a_1181_);
lean_dec_ref(v_m_1180_);
v_r_1183_ = lean_box(v_res_1182_);
return v_r_1183_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_instDecidableMem(lean_object* v_00_u03b1_1184_, lean_object* v_00_u03b2_1185_, lean_object* v_inst_1186_, lean_object* v_inst_1187_, lean_object* v_m_1188_, lean_object* v_a_1189_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = l_Std_DHashMap_Raw_instDecidableMem___redArg(v_inst_1186_, v_inst_1187_, v_m_1188_, v_a_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instDecidableMem___boxed(lean_object* v_00_u03b1_1191_, lean_object* v_00_u03b2_1192_, lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_m_1195_, lean_object* v_a_1196_){
_start:
{
uint8_t v_res_1197_; lean_object* v_r_1198_; 
v_res_1197_ = l_Std_DHashMap_Raw_instDecidableMem(v_00_u03b1_1191_, v_00_u03b2_1192_, v_inst_1193_, v_inst_1194_, v_m_1195_, v_a_1196_);
lean_dec_ref(v_m_1195_);
v_r_1198_ = lean_box(v_res_1197_);
return v_r_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg(lean_object* v_inst_1199_, lean_object* v_inst_1200_, lean_object* v_m_1201_, lean_object* v_a_1202_){
_start:
{
lean_object* v___x_1203_; lean_object* v_val_1204_; 
v___x_1203_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1199_, v_inst_1200_, v_m_1201_, v_a_1202_);
v_val_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_val_1204_);
lean_dec(v___x_1203_);
return v_val_1204_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___redArg___boxed(lean_object* v_inst_1205_, lean_object* v_inst_1206_, lean_object* v_m_1207_, lean_object* v_a_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Std_DHashMap_Raw_get___redArg(v_inst_1205_, v_inst_1206_, v_m_1207_, v_a_1208_);
lean_dec_ref(v_m_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get(lean_object* v_00_u03b1_1210_, lean_object* v_00_u03b2_1211_, lean_object* v_inst_1212_, lean_object* v_inst_1213_, lean_object* v_inst_1214_, lean_object* v_m_1215_, lean_object* v_a_1216_, lean_object* v_h_1217_){
_start:
{
lean_object* v___x_1218_; lean_object* v_val_1219_; 
v___x_1218_ = l_Std_DHashMap_Internal_Raw_u2080_get_x3f___redArg(v_inst_1212_, v_inst_1213_, v_m_1215_, v_a_1216_);
v_val_1219_ = lean_ctor_get(v___x_1218_, 0);
lean_inc(v_val_1219_);
lean_dec(v___x_1218_);
return v_val_1219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get___boxed(lean_object* v_00_u03b1_1220_, lean_object* v_00_u03b2_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_inst_1224_, lean_object* v_m_1225_, lean_object* v_a_1226_, lean_object* v_h_1227_){
_start:
{
lean_object* v_res_1228_; 
v_res_1228_ = l_Std_DHashMap_Raw_get(v_00_u03b1_1220_, v_00_u03b2_1221_, v_inst_1222_, v_inst_1223_, v_inst_1224_, v_m_1225_, v_a_1226_, v_h_1227_);
lean_dec_ref(v_m_1225_);
return v_res_1228_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg(lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_m_1231_, lean_object* v_a_1232_, lean_object* v_fallback_1233_){
_start:
{
lean_object* v_keyArray_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; uint8_t v___x_1237_; 
v_keyArray_1234_ = lean_ctor_get(v_m_1231_, 1);
v___x_1235_ = lean_unsigned_to_nat(0u);
v___x_1236_ = lean_array_get_size(v_keyArray_1234_);
v___x_1237_ = lean_nat_dec_lt(v___x_1235_, v___x_1236_);
if (v___x_1237_ == 0)
{
lean_dec(v_a_1232_);
lean_dec_ref(v_inst_1230_);
lean_dec_ref(v_inst_1229_);
lean_inc(v_fallback_1233_);
return v_fallback_1233_;
}
else
{
lean_object* v___x_1238_; 
v___x_1238_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_1229_, v_inst_1230_, v_m_1231_, v_a_1232_, v_fallback_1233_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___redArg___boxed(lean_object* v_inst_1239_, lean_object* v_inst_1240_, lean_object* v_m_1241_, lean_object* v_a_1242_, lean_object* v_fallback_1243_){
_start:
{
lean_object* v_res_1244_; 
v_res_1244_ = l_Std_DHashMap_Raw_getD___redArg(v_inst_1239_, v_inst_1240_, v_m_1241_, v_a_1242_, v_fallback_1243_);
lean_dec(v_fallback_1243_);
lean_dec_ref(v_m_1241_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD(lean_object* v_00_u03b1_1245_, lean_object* v_00_u03b2_1246_, lean_object* v_inst_1247_, lean_object* v_inst_1248_, lean_object* v_inst_1249_, lean_object* v_m_1250_, lean_object* v_a_1251_, lean_object* v_fallback_1252_){
_start:
{
lean_object* v_keyArray_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_keyArray_1253_ = lean_ctor_get(v_m_1250_, 1);
v___x_1254_ = lean_unsigned_to_nat(0u);
v___x_1255_ = lean_array_get_size(v_keyArray_1253_);
v___x_1256_ = lean_nat_dec_lt(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_dec(v_a_1251_);
lean_dec_ref(v_inst_1248_);
lean_dec_ref(v_inst_1247_);
lean_inc(v_fallback_1252_);
return v_fallback_1252_;
}
else
{
lean_object* v___x_1257_; 
v___x_1257_ = l_Std_DHashMap_Internal_Raw_u2080_getD___redArg(v_inst_1247_, v_inst_1248_, v_m_1250_, v_a_1251_, v_fallback_1252_);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getD___boxed(lean_object* v_00_u03b1_1258_, lean_object* v_00_u03b2_1259_, lean_object* v_inst_1260_, lean_object* v_inst_1261_, lean_object* v_inst_1262_, lean_object* v_m_1263_, lean_object* v_a_1264_, lean_object* v_fallback_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Std_DHashMap_Raw_getD(v_00_u03b1_1258_, v_00_u03b2_1259_, v_inst_1260_, v_inst_1261_, v_inst_1262_, v_m_1263_, v_a_1264_, v_fallback_1265_);
lean_dec(v_fallback_1265_);
lean_dec_ref(v_m_1263_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg(lean_object* v_inst_1267_, lean_object* v_inst_1268_, lean_object* v_m_1269_, lean_object* v_a_1270_, lean_object* v_inst_1271_){
_start:
{
lean_object* v_keyArray_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; uint8_t v___x_1275_; 
v_keyArray_1272_ = lean_ctor_get(v_m_1269_, 1);
v___x_1273_ = lean_unsigned_to_nat(0u);
v___x_1274_ = lean_array_get_size(v_keyArray_1272_);
v___x_1275_ = lean_nat_dec_lt(v___x_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
lean_dec(v_a_1270_);
lean_dec_ref(v_inst_1268_);
lean_dec_ref(v_inst_1267_);
lean_inc(v_inst_1271_);
return v_inst_1271_;
}
else
{
lean_object* v___x_1276_; 
v___x_1276_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_1267_, v_inst_1268_, v_m_1269_, v_a_1270_, v_inst_1271_);
return v___x_1276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___redArg___boxed(lean_object* v_inst_1277_, lean_object* v_inst_1278_, lean_object* v_m_1279_, lean_object* v_a_1280_, lean_object* v_inst_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_Std_DHashMap_Raw_get_x21___redArg(v_inst_1277_, v_inst_1278_, v_m_1279_, v_a_1280_, v_inst_1281_);
lean_dec(v_inst_1281_);
lean_dec_ref(v_m_1279_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21(lean_object* v_00_u03b1_1283_, lean_object* v_00_u03b2_1284_, lean_object* v_inst_1285_, lean_object* v_inst_1286_, lean_object* v_inst_1287_, lean_object* v_m_1288_, lean_object* v_a_1289_, lean_object* v_inst_1290_){
_start:
{
lean_object* v_keyArray_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_keyArray_1291_ = lean_ctor_get(v_m_1288_, 1);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_array_get_size(v_keyArray_1291_);
v___x_1294_ = lean_nat_dec_lt(v___x_1292_, v___x_1293_);
if (v___x_1294_ == 0)
{
lean_dec(v_a_1289_);
lean_dec_ref(v_inst_1286_);
lean_dec_ref(v_inst_1285_);
lean_inc(v_inst_1290_);
return v_inst_1290_;
}
else
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Std_DHashMap_Internal_Raw_u2080_get_x21___redArg(v_inst_1285_, v_inst_1286_, v_m_1288_, v_a_1289_, v_inst_1290_);
return v___x_1295_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_get_x21___boxed(lean_object* v_00_u03b1_1296_, lean_object* v_00_u03b2_1297_, lean_object* v_inst_1298_, lean_object* v_inst_1299_, lean_object* v_inst_1300_, lean_object* v_m_1301_, lean_object* v_a_1302_, lean_object* v_inst_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_Std_DHashMap_Raw_get_x21(v_00_u03b1_1296_, v_00_u03b2_1297_, v_inst_1298_, v_inst_1299_, v_inst_1300_, v_m_1301_, v_a_1302_, v_inst_1303_);
lean_dec(v_inst_1303_);
lean_dec_ref(v_m_1301_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase___redArg(lean_object* v_inst_1305_, lean_object* v_inst_1306_, lean_object* v_m_1307_, lean_object* v_a_1308_){
_start:
{
lean_object* v_keyArray_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; uint8_t v___x_1312_; 
v_keyArray_1309_ = lean_ctor_get(v_m_1307_, 1);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_array_get_size(v_keyArray_1309_);
v___x_1312_ = lean_nat_dec_lt(v___x_1310_, v___x_1311_);
if (v___x_1312_ == 0)
{
lean_dec(v_a_1308_);
lean_dec_ref(v_inst_1306_);
lean_dec_ref(v_inst_1305_);
return v_m_1307_;
}
else
{
lean_object* v___x_1313_; 
v___x_1313_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1305_, v_inst_1306_, v_m_1307_, v_a_1308_);
return v___x_1313_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_erase(lean_object* v_00_u03b1_1314_, lean_object* v_00_u03b2_1315_, lean_object* v_inst_1316_, lean_object* v_inst_1317_, lean_object* v_m_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_keyArray_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; uint8_t v___x_1323_; 
v_keyArray_1320_ = lean_ctor_get(v_m_1318_, 1);
v___x_1321_ = lean_unsigned_to_nat(0u);
v___x_1322_ = lean_array_get_size(v_keyArray_1320_);
v___x_1323_ = lean_nat_dec_lt(v___x_1321_, v___x_1322_);
if (v___x_1323_ == 0)
{
lean_dec(v_a_1319_);
lean_dec_ref(v_inst_1317_);
lean_dec_ref(v_inst_1316_);
return v_m_1318_;
}
else
{
lean_object* v___x_1324_; 
v___x_1324_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_1316_, v_inst_1317_, v_m_1318_, v_a_1319_);
return v___x_1324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg(lean_object* v_inst_1325_, lean_object* v_inst_1326_, lean_object* v_m_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_keyArray_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_keyArray_1329_ = lean_ctor_get(v_m_1327_, 1);
v___x_1330_ = lean_unsigned_to_nat(0u);
v___x_1331_ = lean_array_get_size(v_keyArray_1329_);
v___x_1332_ = lean_nat_dec_lt(v___x_1330_, v___x_1331_);
if (v___x_1332_ == 0)
{
lean_object* v___x_1333_; 
lean_dec(v_a_1328_);
lean_dec_ref(v_inst_1326_);
lean_dec_ref(v_inst_1325_);
v___x_1333_ = lean_box(0);
return v___x_1333_;
}
else
{
lean_object* v___x_1334_; 
v___x_1334_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1325_, v_inst_1326_, v_m_1327_, v_a_1328_);
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___redArg___boxed(lean_object* v_inst_1335_, lean_object* v_inst_1336_, lean_object* v_m_1337_, lean_object* v_a_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Std_DHashMap_Raw_Const_get_x3f___redArg(v_inst_1335_, v_inst_1336_, v_m_1337_, v_a_1338_);
lean_dec_ref(v_m_1337_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f(lean_object* v_00_u03b1_1340_, lean_object* v_00_u03b2_1341_, lean_object* v_inst_1342_, lean_object* v_inst_1343_, lean_object* v_m_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_keyArray_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v_keyArray_1346_ = lean_ctor_get(v_m_1344_, 1);
v___x_1347_ = lean_unsigned_to_nat(0u);
v___x_1348_ = lean_array_get_size(v_keyArray_1346_);
v___x_1349_ = lean_nat_dec_lt(v___x_1347_, v___x_1348_);
if (v___x_1349_ == 0)
{
lean_object* v___x_1350_; 
lean_dec(v_a_1345_);
lean_dec_ref(v_inst_1343_);
lean_dec_ref(v_inst_1342_);
v___x_1350_ = lean_box(0);
return v___x_1350_;
}
else
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1342_, v_inst_1343_, v_m_1344_, v_a_1345_);
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x3f___boxed(lean_object* v_00_u03b1_1352_, lean_object* v_00_u03b2_1353_, lean_object* v_inst_1354_, lean_object* v_inst_1355_, lean_object* v_m_1356_, lean_object* v_a_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Std_DHashMap_Raw_Const_get_x3f(v_00_u03b1_1352_, v_00_u03b2_1353_, v_inst_1354_, v_inst_1355_, v_m_1356_, v_a_1357_);
lean_dec_ref(v_m_1356_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg(lean_object* v_inst_1359_, lean_object* v_inst_1360_, lean_object* v_m_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1363_; lean_object* v_val_1364_; 
v___x_1363_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1359_, v_inst_1360_, v_m_1361_, v_a_1362_);
v_val_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_val_1364_);
lean_dec(v___x_1363_);
return v_val_1364_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___redArg___boxed(lean_object* v_inst_1365_, lean_object* v_inst_1366_, lean_object* v_m_1367_, lean_object* v_a_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Std_DHashMap_Raw_Const_get___redArg(v_inst_1365_, v_inst_1366_, v_m_1367_, v_a_1368_);
lean_dec_ref(v_m_1367_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get(lean_object* v_00_u03b1_1370_, lean_object* v_00_u03b2_1371_, lean_object* v_inst_1372_, lean_object* v_inst_1373_, lean_object* v_m_1374_, lean_object* v_a_1375_, lean_object* v_h_1376_){
_start:
{
lean_object* v___x_1377_; lean_object* v_val_1378_; 
v___x_1377_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v_inst_1372_, v_inst_1373_, v_m_1374_, v_a_1375_);
v_val_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_val_1378_);
lean_dec(v___x_1377_);
return v_val_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get___boxed(lean_object* v_00_u03b1_1379_, lean_object* v_00_u03b2_1380_, lean_object* v_inst_1381_, lean_object* v_inst_1382_, lean_object* v_m_1383_, lean_object* v_a_1384_, lean_object* v_h_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_Std_DHashMap_Raw_Const_get(v_00_u03b1_1379_, v_00_u03b2_1380_, v_inst_1381_, v_inst_1382_, v_m_1383_, v_a_1384_, v_h_1385_);
lean_dec_ref(v_m_1383_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg(lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_m_1389_, lean_object* v_a_1390_, lean_object* v_fallback_1391_){
_start:
{
lean_object* v_keyArray_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; uint8_t v___x_1395_; 
v_keyArray_1392_ = lean_ctor_get(v_m_1389_, 1);
v___x_1393_ = lean_unsigned_to_nat(0u);
v___x_1394_ = lean_array_get_size(v_keyArray_1392_);
v___x_1395_ = lean_nat_dec_lt(v___x_1393_, v___x_1394_);
if (v___x_1395_ == 0)
{
lean_dec(v_a_1390_);
lean_dec_ref(v_inst_1388_);
lean_dec_ref(v_inst_1387_);
lean_inc(v_fallback_1391_);
return v_fallback_1391_;
}
else
{
lean_object* v___x_1396_; 
v___x_1396_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_1387_, v_inst_1388_, v_m_1389_, v_a_1390_, v_fallback_1391_);
return v___x_1396_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___redArg___boxed(lean_object* v_inst_1397_, lean_object* v_inst_1398_, lean_object* v_m_1399_, lean_object* v_a_1400_, lean_object* v_fallback_1401_){
_start:
{
lean_object* v_res_1402_; 
v_res_1402_ = l_Std_DHashMap_Raw_Const_getD___redArg(v_inst_1397_, v_inst_1398_, v_m_1399_, v_a_1400_, v_fallback_1401_);
lean_dec(v_fallback_1401_);
lean_dec_ref(v_m_1399_);
return v_res_1402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD(lean_object* v_00_u03b1_1403_, lean_object* v_00_u03b2_1404_, lean_object* v_inst_1405_, lean_object* v_inst_1406_, lean_object* v_m_1407_, lean_object* v_a_1408_, lean_object* v_fallback_1409_){
_start:
{
lean_object* v_keyArray_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; uint8_t v___x_1413_; 
v_keyArray_1410_ = lean_ctor_get(v_m_1407_, 1);
v___x_1411_ = lean_unsigned_to_nat(0u);
v___x_1412_ = lean_array_get_size(v_keyArray_1410_);
v___x_1413_ = lean_nat_dec_lt(v___x_1411_, v___x_1412_);
if (v___x_1413_ == 0)
{
lean_dec(v_a_1408_);
lean_dec_ref(v_inst_1406_);
lean_dec_ref(v_inst_1405_);
lean_inc(v_fallback_1409_);
return v_fallback_1409_;
}
else
{
lean_object* v___x_1414_; 
v___x_1414_ = l_Std_DHashMap_Internal_Raw_u2080_Const_getD___redArg(v_inst_1405_, v_inst_1406_, v_m_1407_, v_a_1408_, v_fallback_1409_);
return v___x_1414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getD___boxed(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_inst_1417_, lean_object* v_inst_1418_, lean_object* v_m_1419_, lean_object* v_a_1420_, lean_object* v_fallback_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Std_DHashMap_Raw_Const_getD(v_00_u03b1_1415_, v_00_u03b2_1416_, v_inst_1417_, v_inst_1418_, v_m_1419_, v_a_1420_, v_fallback_1421_);
lean_dec(v_fallback_1421_);
lean_dec_ref(v_m_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg(lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_inst_1425_, lean_object* v_m_1426_, lean_object* v_a_1427_){
_start:
{
lean_object* v_keyArray_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; uint8_t v___x_1431_; 
v_keyArray_1428_ = lean_ctor_get(v_m_1426_, 1);
v___x_1429_ = lean_unsigned_to_nat(0u);
v___x_1430_ = lean_array_get_size(v_keyArray_1428_);
v___x_1431_ = lean_nat_dec_lt(v___x_1429_, v___x_1430_);
if (v___x_1431_ == 0)
{
lean_dec(v_a_1427_);
lean_dec_ref(v_inst_1424_);
lean_dec_ref(v_inst_1423_);
lean_inc(v_inst_1425_);
return v_inst_1425_;
}
else
{
lean_object* v___x_1432_; 
v___x_1432_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_1423_, v_inst_1424_, v_inst_1425_, v_m_1426_, v_a_1427_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___redArg___boxed(lean_object* v_inst_1433_, lean_object* v_inst_1434_, lean_object* v_inst_1435_, lean_object* v_m_1436_, lean_object* v_a_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Std_DHashMap_Raw_Const_get_x21___redArg(v_inst_1433_, v_inst_1434_, v_inst_1435_, v_m_1436_, v_a_1437_);
lean_dec_ref(v_m_1436_);
lean_dec(v_inst_1435_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21(lean_object* v_00_u03b1_1439_, lean_object* v_00_u03b2_1440_, lean_object* v_inst_1441_, lean_object* v_inst_1442_, lean_object* v_inst_1443_, lean_object* v_m_1444_, lean_object* v_a_1445_){
_start:
{
lean_object* v_keyArray_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; uint8_t v___x_1449_; 
v_keyArray_1446_ = lean_ctor_get(v_m_1444_, 1);
v___x_1447_ = lean_unsigned_to_nat(0u);
v___x_1448_ = lean_array_get_size(v_keyArray_1446_);
v___x_1449_ = lean_nat_dec_lt(v___x_1447_, v___x_1448_);
if (v___x_1449_ == 0)
{
lean_dec(v_a_1445_);
lean_dec_ref(v_inst_1442_);
lean_dec_ref(v_inst_1441_);
lean_inc(v_inst_1443_);
return v_inst_1443_;
}
else
{
lean_object* v___x_1450_; 
v___x_1450_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_1441_, v_inst_1442_, v_inst_1443_, v_m_1444_, v_a_1445_);
return v___x_1450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_get_x21___boxed(lean_object* v_00_u03b1_1451_, lean_object* v_00_u03b2_1452_, lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_inst_1455_, lean_object* v_m_1456_, lean_object* v_a_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_Std_DHashMap_Raw_Const_get_x21(v_00_u03b1_1451_, v_00_u03b2_1452_, v_inst_1453_, v_inst_1454_, v_inst_1455_, v_m_1456_, v_a_1457_);
lean_dec_ref(v_m_1456_);
lean_dec(v_inst_1455_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f___redArg(lean_object* v_inst_1459_, lean_object* v_inst_1460_, lean_object* v_m_1461_, lean_object* v_a_1462_, lean_object* v_b_1463_){
_start:
{
lean_object* v_size_1464_; lean_object* v_keyArray_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; uint8_t v___x_1468_; 
v_size_1464_ = lean_ctor_get(v_m_1461_, 0);
v_keyArray_1465_ = lean_ctor_get(v_m_1461_, 1);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = lean_array_get_size(v_keyArray_1465_);
v___x_1468_ = lean_nat_dec_lt(v___x_1466_, v___x_1467_);
if (v___x_1468_ == 0)
{
lean_object* v___x_1469_; lean_object* v___x_1470_; 
lean_dec(v_b_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_inst_1460_);
lean_dec_ref(v_inst_1459_);
v___x_1469_ = lean_box(0);
v___x_1470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v_m_1461_);
return v___x_1470_;
}
else
{
lean_object* v___x_1471_; 
lean_inc(v_a_1462_);
lean_inc_ref(v_inst_1460_);
lean_inc_ref(v_inst_1459_);
v___x_1471_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1459_, v_inst_1460_, v_m_1461_, v_a_1462_);
switch(lean_obj_tag(v___x_1471_))
{
case 0:
{
lean_object* v_value_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
lean_dec(v_b_1463_);
lean_dec(v_a_1462_);
lean_dec_ref(v_inst_1460_);
lean_dec_ref(v_inst_1459_);
v_value_1472_ = lean_ctor_get(v___x_1471_, 2);
lean_inc(v_value_1472_);
lean_dec_ref_known(v___x_1471_, 3);
v___x_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1473_, 0, v_value_1472_);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v_m_1461_);
return v___x_1474_;
}
case 1:
{
lean_object* v_index_1475_; lean_object* v___x_1476_; lean_object* v___y_1478_; lean_object* v_i_1479_; lean_object* v___x_1496_; lean_object* v___x_1497_; uint8_t v___x_1498_; 
v_index_1475_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_index_1475_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1476_ = lean_box(0);
v___x_1496_ = lean_unsigned_to_nat(1u);
v___x_1497_ = lean_nat_add(v_size_1464_, v___x_1496_);
v___x_1498_ = lean_nat_dec_lt(v___x_1497_, v___x_1467_);
if (v___x_1498_ == 0)
{
lean_dec(v___x_1497_);
lean_dec(v_index_1475_);
goto v___jp_1485_;
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; uint8_t v___x_1503_; 
v___x_1499_ = lean_unsigned_to_nat(4u);
v___x_1500_ = lean_nat_mul(v___x_1497_, v___x_1499_);
v___x_1501_ = lean_unsigned_to_nat(3u);
v___x_1502_ = lean_nat_mul(v___x_1467_, v___x_1501_);
v___x_1503_ = lean_nat_dec_le(v___x_1500_, v___x_1502_);
lean_dec(v___x_1502_);
lean_dec(v___x_1500_);
if (v___x_1503_ == 0)
{
lean_dec(v___x_1497_);
lean_dec(v_index_1475_);
goto v___jp_1485_;
}
else
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
lean_dec_ref(v_inst_1460_);
lean_dec_ref(v_inst_1459_);
v___x_1504_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1461_, v___x_1497_, v_index_1475_, v_a_1462_, v_b_1463_);
lean_dec(v_index_1475_);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1476_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
return v___x_1505_;
}
}
v___jp_1477_:
{
lean_object* v_size_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v_size_1480_ = lean_ctor_get(v___y_1478_, 0);
v___x_1481_ = lean_unsigned_to_nat(1u);
v___x_1482_ = lean_nat_add(v_size_1480_, v___x_1481_);
v___x_1483_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1478_, v___x_1482_, v_i_1479_, v_a_1462_, v_b_1463_);
lean_dec(v_i_1479_);
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1476_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
return v___x_1484_;
}
v___jp_1485_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
lean_inc_ref(v_inst_1460_);
lean_inc_ref(v_inst_1459_);
v___x_1486_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1459_, v_inst_1460_, v_m_1461_);
lean_inc(v_a_1462_);
v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1459_, v_inst_1460_, v___x_1486_, v_a_1462_);
switch(lean_obj_tag(v___x_1487_))
{
case 0:
{
lean_object* v_index_1488_; lean_object* v_size_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; 
v_index_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_index_1488_);
lean_dec_ref_known(v___x_1487_, 3);
v_size_1489_ = lean_ctor_get(v___x_1486_, 0);
lean_inc(v_size_1489_);
v___x_1490_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1486_, v_size_1489_, v_index_1488_, v_a_1462_, v_b_1463_);
lean_dec(v_index_1488_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1476_);
lean_ctor_set(v___x_1491_, 1, v___x_1490_);
return v___x_1491_;
}
case 1:
{
lean_object* v_index_1492_; 
v_index_1492_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_index_1492_);
lean_dec_ref_known(v___x_1487_, 1);
v___y_1478_ = v___x_1486_;
v_i_1479_ = v_index_1492_;
goto v___jp_1477_;
}
default: 
{
lean_object* v___x_1493_; 
v___x_1493_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1486_, v___x_1466_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_index_1494_; 
v_index_1494_ = lean_ctor_get(v___x_1493_, 0);
lean_inc(v_index_1494_);
lean_dec_ref_known(v___x_1493_, 1);
v___y_1478_ = v___x_1486_;
v_i_1479_ = v_index_1494_;
goto v___jp_1477_;
}
else
{
lean_object* v___x_1495_; 
lean_dec(v_b_1463_);
lean_dec(v_a_1462_);
v___x_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1476_);
lean_ctor_set(v___x_1495_, 1, v___x_1486_);
return v___x_1495_;
}
}
}
}
}
default: 
{
lean_object* v___x_1506_; lean_object* v___y_1508_; lean_object* v_i_1509_; lean_object* v___y_1516_; lean_object* v___x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1506_ = lean_box(0);
v___x_1526_ = lean_unsigned_to_nat(1u);
v___x_1527_ = lean_nat_add(v_size_1464_, v___x_1526_);
v___x_1528_ = lean_nat_dec_lt(v___x_1527_, v___x_1467_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec(v___x_1527_);
lean_inc_ref(v_inst_1460_);
lean_inc_ref(v_inst_1459_);
v___x_1529_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1459_, v_inst_1460_, v_m_1461_);
v___y_1516_ = v___x_1529_;
goto v___jp_1515_;
}
else
{
lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1530_ = lean_unsigned_to_nat(4u);
v___x_1531_ = lean_nat_mul(v___x_1527_, v___x_1530_);
lean_dec(v___x_1527_);
v___x_1532_ = lean_unsigned_to_nat(3u);
v___x_1533_ = lean_nat_mul(v___x_1467_, v___x_1532_);
v___x_1534_ = lean_nat_dec_le(v___x_1531_, v___x_1533_);
lean_dec(v___x_1533_);
lean_dec(v___x_1531_);
if (v___x_1534_ == 0)
{
lean_object* v___x_1535_; 
lean_inc_ref(v_inst_1460_);
lean_inc_ref(v_inst_1459_);
v___x_1535_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1459_, v_inst_1460_, v_m_1461_);
v___y_1516_ = v___x_1535_;
goto v___jp_1515_;
}
else
{
v___y_1516_ = v_m_1461_;
goto v___jp_1515_;
}
}
v___jp_1507_:
{
lean_object* v_size_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v_size_1510_ = lean_ctor_get(v___y_1508_, 0);
v___x_1511_ = lean_unsigned_to_nat(1u);
v___x_1512_ = lean_nat_add(v_size_1510_, v___x_1511_);
v___x_1513_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1508_, v___x_1512_, v_i_1509_, v_a_1462_, v_b_1463_);
lean_dec(v_i_1509_);
v___x_1514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1506_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
return v___x_1514_;
}
v___jp_1515_:
{
lean_object* v___x_1517_; 
lean_inc(v_a_1462_);
v___x_1517_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1459_, v_inst_1460_, v___y_1516_, v_a_1462_);
switch(lean_obj_tag(v___x_1517_))
{
case 0:
{
lean_object* v_index_1518_; lean_object* v_size_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v_index_1518_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_index_1518_);
lean_dec_ref_known(v___x_1517_, 3);
v_size_1519_ = lean_ctor_get(v___y_1516_, 0);
lean_inc(v_size_1519_);
v___x_1520_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1516_, v_size_1519_, v_index_1518_, v_a_1462_, v_b_1463_);
lean_dec(v_index_1518_);
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1506_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
return v___x_1521_;
}
case 1:
{
lean_object* v_index_1522_; 
v_index_1522_ = lean_ctor_get(v___x_1517_, 0);
lean_inc(v_index_1522_);
lean_dec_ref_known(v___x_1517_, 1);
v___y_1508_ = v___y_1516_;
v_i_1509_ = v_index_1522_;
goto v___jp_1507_;
}
default: 
{
lean_object* v___x_1523_; 
v___x_1523_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1516_, v___x_1466_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_index_1524_; 
v_index_1524_ = lean_ctor_get(v___x_1523_, 0);
lean_inc(v_index_1524_);
lean_dec_ref_known(v___x_1523_, 1);
v___y_1508_ = v___y_1516_;
v_i_1509_ = v_index_1524_;
goto v___jp_1507_;
}
else
{
lean_object* v___x_1525_; 
lean_dec(v_b_1463_);
lean_dec(v_a_1462_);
v___x_1525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1506_);
lean_ctor_set(v___x_1525_, 1, v___y_1516_);
return v___x_1525_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_getThenInsertIfNew_x3f(lean_object* v_00_u03b1_1536_, lean_object* v_00_u03b2_1537_, lean_object* v_inst_1538_, lean_object* v_inst_1539_, lean_object* v_m_1540_, lean_object* v_a_1541_, lean_object* v_b_1542_){
_start:
{
lean_object* v_size_1543_; lean_object* v_keyArray_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; uint8_t v___x_1547_; 
v_size_1543_ = lean_ctor_get(v_m_1540_, 0);
v_keyArray_1544_ = lean_ctor_get(v_m_1540_, 1);
v___x_1545_ = lean_unsigned_to_nat(0u);
v___x_1546_ = lean_array_get_size(v_keyArray_1544_);
v___x_1547_ = lean_nat_dec_lt(v___x_1545_, v___x_1546_);
if (v___x_1547_ == 0)
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
lean_dec(v_b_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_inst_1539_);
lean_dec_ref(v_inst_1538_);
v___x_1548_ = lean_box(0);
v___x_1549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v_m_1540_);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; 
lean_inc(v_a_1541_);
lean_inc_ref(v_inst_1539_);
lean_inc_ref(v_inst_1538_);
v___x_1550_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1538_, v_inst_1539_, v_m_1540_, v_a_1541_);
switch(lean_obj_tag(v___x_1550_))
{
case 0:
{
lean_object* v_value_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec(v_b_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_inst_1539_);
lean_dec_ref(v_inst_1538_);
v_value_1551_ = lean_ctor_get(v___x_1550_, 2);
lean_inc(v_value_1551_);
lean_dec_ref_known(v___x_1550_, 3);
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_value_1551_);
v___x_1553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1553_, 0, v___x_1552_);
lean_ctor_set(v___x_1553_, 1, v_m_1540_);
return v___x_1553_;
}
case 1:
{
lean_object* v_index_1554_; lean_object* v___x_1555_; lean_object* v___y_1557_; lean_object* v_i_1558_; lean_object* v___x_1575_; lean_object* v___x_1576_; uint8_t v___x_1577_; 
v_index_1554_ = lean_ctor_get(v___x_1550_, 0);
lean_inc(v_index_1554_);
lean_dec_ref_known(v___x_1550_, 1);
v___x_1555_ = lean_box(0);
v___x_1575_ = lean_unsigned_to_nat(1u);
v___x_1576_ = lean_nat_add(v_size_1543_, v___x_1575_);
v___x_1577_ = lean_nat_dec_lt(v___x_1576_, v___x_1546_);
if (v___x_1577_ == 0)
{
lean_dec(v___x_1576_);
lean_dec(v_index_1554_);
goto v___jp_1564_;
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1578_ = lean_unsigned_to_nat(4u);
v___x_1579_ = lean_nat_mul(v___x_1576_, v___x_1578_);
v___x_1580_ = lean_unsigned_to_nat(3u);
v___x_1581_ = lean_nat_mul(v___x_1546_, v___x_1580_);
v___x_1582_ = lean_nat_dec_le(v___x_1579_, v___x_1581_);
lean_dec(v___x_1581_);
lean_dec(v___x_1579_);
if (v___x_1582_ == 0)
{
lean_dec(v___x_1576_);
lean_dec(v_index_1554_);
goto v___jp_1564_;
}
else
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
lean_dec_ref(v_inst_1539_);
lean_dec_ref(v_inst_1538_);
v___x_1583_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1540_, v___x_1576_, v_index_1554_, v_a_1541_, v_b_1542_);
lean_dec(v_index_1554_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v___x_1555_);
lean_ctor_set(v___x_1584_, 1, v___x_1583_);
return v___x_1584_;
}
}
v___jp_1556_:
{
lean_object* v_size_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v_size_1559_ = lean_ctor_get(v___y_1557_, 0);
v___x_1560_ = lean_unsigned_to_nat(1u);
v___x_1561_ = lean_nat_add(v_size_1559_, v___x_1560_);
v___x_1562_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1557_, v___x_1561_, v_i_1558_, v_a_1541_, v_b_1542_);
lean_dec(v_i_1558_);
v___x_1563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1563_, 0, v___x_1555_);
lean_ctor_set(v___x_1563_, 1, v___x_1562_);
return v___x_1563_;
}
v___jp_1564_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
lean_inc_ref(v_inst_1539_);
lean_inc_ref(v_inst_1538_);
v___x_1565_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1538_, v_inst_1539_, v_m_1540_);
lean_inc(v_a_1541_);
v___x_1566_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1538_, v_inst_1539_, v___x_1565_, v_a_1541_);
switch(lean_obj_tag(v___x_1566_))
{
case 0:
{
lean_object* v_index_1567_; lean_object* v_size_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v_index_1567_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_index_1567_);
lean_dec_ref_known(v___x_1566_, 3);
v_size_1568_ = lean_ctor_get(v___x_1565_, 0);
lean_inc(v_size_1568_);
v___x_1569_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_1565_, v_size_1568_, v_index_1567_, v_a_1541_, v_b_1542_);
lean_dec(v_index_1567_);
v___x_1570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1570_, 0, v___x_1555_);
lean_ctor_set(v___x_1570_, 1, v___x_1569_);
return v___x_1570_;
}
case 1:
{
lean_object* v_index_1571_; 
v_index_1571_ = lean_ctor_get(v___x_1566_, 0);
lean_inc(v_index_1571_);
lean_dec_ref_known(v___x_1566_, 1);
v___y_1557_ = v___x_1565_;
v_i_1558_ = v_index_1571_;
goto v___jp_1556_;
}
default: 
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_1565_, v___x_1545_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_index_1573_; 
v_index_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_index_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___y_1557_ = v___x_1565_;
v_i_1558_ = v_index_1573_;
goto v___jp_1556_;
}
else
{
lean_object* v___x_1574_; 
lean_dec(v_b_1542_);
lean_dec(v_a_1541_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1555_);
lean_ctor_set(v___x_1574_, 1, v___x_1565_);
return v___x_1574_;
}
}
}
}
}
default: 
{
lean_object* v___x_1585_; lean_object* v___y_1587_; lean_object* v_i_1588_; lean_object* v___y_1595_; lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1585_ = lean_box(0);
v___x_1605_ = lean_unsigned_to_nat(1u);
v___x_1606_ = lean_nat_add(v_size_1543_, v___x_1605_);
v___x_1607_ = lean_nat_dec_lt(v___x_1606_, v___x_1546_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; 
lean_dec(v___x_1606_);
lean_inc_ref(v_inst_1539_);
lean_inc_ref(v_inst_1538_);
v___x_1608_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1538_, v_inst_1539_, v_m_1540_);
v___y_1595_ = v___x_1608_;
goto v___jp_1594_;
}
else
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1609_ = lean_unsigned_to_nat(4u);
v___x_1610_ = lean_nat_mul(v___x_1606_, v___x_1609_);
lean_dec(v___x_1606_);
v___x_1611_ = lean_unsigned_to_nat(3u);
v___x_1612_ = lean_nat_mul(v___x_1546_, v___x_1611_);
v___x_1613_ = lean_nat_dec_le(v___x_1610_, v___x_1612_);
lean_dec(v___x_1612_);
lean_dec(v___x_1610_);
if (v___x_1613_ == 0)
{
lean_object* v___x_1614_; 
lean_inc_ref(v_inst_1539_);
lean_inc_ref(v_inst_1538_);
v___x_1614_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1538_, v_inst_1539_, v_m_1540_);
v___y_1595_ = v___x_1614_;
goto v___jp_1594_;
}
else
{
v___y_1595_ = v_m_1540_;
goto v___jp_1594_;
}
}
v___jp_1586_:
{
lean_object* v_size_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v_size_1589_ = lean_ctor_get(v___y_1587_, 0);
v___x_1590_ = lean_unsigned_to_nat(1u);
v___x_1591_ = lean_nat_add(v_size_1589_, v___x_1590_);
v___x_1592_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1587_, v___x_1591_, v_i_1588_, v_a_1541_, v_b_1542_);
lean_dec(v_i_1588_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1585_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
return v___x_1593_;
}
v___jp_1594_:
{
lean_object* v___x_1596_; 
lean_inc(v_a_1541_);
v___x_1596_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1538_, v_inst_1539_, v___y_1595_, v_a_1541_);
switch(lean_obj_tag(v___x_1596_))
{
case 0:
{
lean_object* v_index_1597_; lean_object* v_size_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; 
v_index_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_index_1597_);
lean_dec_ref_known(v___x_1596_, 3);
v_size_1598_ = lean_ctor_get(v___y_1595_, 0);
lean_inc(v_size_1598_);
v___x_1599_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1595_, v_size_1598_, v_index_1597_, v_a_1541_, v_b_1542_);
lean_dec(v_index_1597_);
v___x_1600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1585_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
return v___x_1600_;
}
case 1:
{
lean_object* v_index_1601_; 
v_index_1601_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_index_1601_);
lean_dec_ref_known(v___x_1596_, 1);
v___y_1587_ = v___y_1595_;
v_i_1588_ = v_index_1601_;
goto v___jp_1586_;
}
default: 
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_1595_, v___x_1545_);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v_index_1603_; 
v_index_1603_ = lean_ctor_get(v___x_1602_, 0);
lean_inc(v_index_1603_);
lean_dec_ref_known(v___x_1602_, 1);
v___y_1587_ = v___y_1595_;
v_i_1588_ = v_index_1603_;
goto v___jp_1586_;
}
else
{
lean_object* v___x_1604_; 
lean_dec(v_b_1542_);
lean_dec(v_a_1541_);
v___x_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1585_);
lean_ctor_set(v___x_1604_, 1, v___y_1595_);
return v___x_1604_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg(lean_object* v_inst_1615_, lean_object* v_inst_1616_, lean_object* v_m_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_keyArray_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; uint8_t v___x_1622_; 
v_keyArray_1619_ = lean_ctor_get(v_m_1617_, 1);
v___x_1620_ = lean_unsigned_to_nat(0u);
v___x_1621_ = lean_array_get_size(v_keyArray_1619_);
v___x_1622_ = lean_nat_dec_lt(v___x_1620_, v___x_1621_);
if (v___x_1622_ == 0)
{
lean_object* v___x_1623_; 
lean_dec(v_a_1618_);
lean_dec_ref(v_inst_1616_);
lean_dec_ref(v_inst_1615_);
v___x_1623_ = lean_box(0);
return v___x_1623_;
}
else
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1615_, v_inst_1616_, v_m_1617_, v_a_1618_);
return v___x_1624_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___redArg___boxed(lean_object* v_inst_1625_, lean_object* v_inst_1626_, lean_object* v_m_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Std_DHashMap_Raw_getKey_x3f___redArg(v_inst_1625_, v_inst_1626_, v_m_1627_, v_a_1628_);
lean_dec_ref(v_m_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f(lean_object* v_00_u03b1_1630_, lean_object* v_00_u03b2_1631_, lean_object* v_inst_1632_, lean_object* v_inst_1633_, lean_object* v_m_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_keyArray_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; uint8_t v___x_1639_; 
v_keyArray_1636_ = lean_ctor_get(v_m_1634_, 1);
v___x_1637_ = lean_unsigned_to_nat(0u);
v___x_1638_ = lean_array_get_size(v_keyArray_1636_);
v___x_1639_ = lean_nat_dec_lt(v___x_1637_, v___x_1638_);
if (v___x_1639_ == 0)
{
lean_object* v___x_1640_; 
lean_dec(v_a_1635_);
lean_dec_ref(v_inst_1633_);
lean_dec_ref(v_inst_1632_);
v___x_1640_ = lean_box(0);
return v___x_1640_;
}
else
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1632_, v_inst_1633_, v_m_1634_, v_a_1635_);
return v___x_1641_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x3f___boxed(lean_object* v_00_u03b1_1642_, lean_object* v_00_u03b2_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_m_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l_Std_DHashMap_Raw_getKey_x3f(v_00_u03b1_1642_, v_00_u03b2_1643_, v_inst_1644_, v_inst_1645_, v_m_1646_, v_a_1647_);
lean_dec_ref(v_m_1646_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg(lean_object* v_inst_1649_, lean_object* v_inst_1650_, lean_object* v_m_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v___x_1653_; lean_object* v_val_1654_; 
v___x_1653_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1649_, v_inst_1650_, v_m_1651_, v_a_1652_);
v_val_1654_ = lean_ctor_get(v___x_1653_, 0);
lean_inc(v_val_1654_);
lean_dec(v___x_1653_);
return v_val_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___redArg___boxed(lean_object* v_inst_1655_, lean_object* v_inst_1656_, lean_object* v_m_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_DHashMap_Raw_getKey___redArg(v_inst_1655_, v_inst_1656_, v_m_1657_, v_a_1658_);
lean_dec_ref(v_m_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey(lean_object* v_00_u03b1_1660_, lean_object* v_00_u03b2_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_m_1664_, lean_object* v_a_1665_, lean_object* v_h_1666_){
_start:
{
lean_object* v___x_1667_; lean_object* v_val_1668_; 
v___x_1667_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x3f___redArg(v_inst_1662_, v_inst_1663_, v_m_1664_, v_a_1665_);
v_val_1668_ = lean_ctor_get(v___x_1667_, 0);
lean_inc(v_val_1668_);
lean_dec(v___x_1667_);
return v_val_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey___boxed(lean_object* v_00_u03b1_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_inst_1671_, lean_object* v_inst_1672_, lean_object* v_m_1673_, lean_object* v_a_1674_, lean_object* v_h_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Std_DHashMap_Raw_getKey(v_00_u03b1_1669_, v_00_u03b2_1670_, v_inst_1671_, v_inst_1672_, v_m_1673_, v_a_1674_, v_h_1675_);
lean_dec_ref(v_m_1673_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg(lean_object* v_inst_1677_, lean_object* v_inst_1678_, lean_object* v_m_1679_, lean_object* v_a_1680_, lean_object* v_fallback_1681_){
_start:
{
lean_object* v_keyArray_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; uint8_t v___x_1685_; 
v_keyArray_1682_ = lean_ctor_get(v_m_1679_, 1);
v___x_1683_ = lean_unsigned_to_nat(0u);
v___x_1684_ = lean_array_get_size(v_keyArray_1682_);
v___x_1685_ = lean_nat_dec_lt(v___x_1683_, v___x_1684_);
if (v___x_1685_ == 0)
{
lean_dec(v_a_1680_);
lean_dec_ref(v_inst_1678_);
lean_dec_ref(v_inst_1677_);
lean_inc(v_fallback_1681_);
return v_fallback_1681_;
}
else
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1677_, v_inst_1678_, v_m_1679_, v_a_1680_, v_fallback_1681_);
return v___x_1686_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___redArg___boxed(lean_object* v_inst_1687_, lean_object* v_inst_1688_, lean_object* v_m_1689_, lean_object* v_a_1690_, lean_object* v_fallback_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l_Std_DHashMap_Raw_getKeyD___redArg(v_inst_1687_, v_inst_1688_, v_m_1689_, v_a_1690_, v_fallback_1691_);
lean_dec(v_fallback_1691_);
lean_dec_ref(v_m_1689_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD(lean_object* v_00_u03b1_1693_, lean_object* v_00_u03b2_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_m_1697_, lean_object* v_a_1698_, lean_object* v_fallback_1699_){
_start:
{
lean_object* v_keyArray_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; uint8_t v___x_1703_; 
v_keyArray_1700_ = lean_ctor_get(v_m_1697_, 1);
v___x_1701_ = lean_unsigned_to_nat(0u);
v___x_1702_ = lean_array_get_size(v_keyArray_1700_);
v___x_1703_ = lean_nat_dec_lt(v___x_1701_, v___x_1702_);
if (v___x_1703_ == 0)
{
lean_dec(v_a_1698_);
lean_dec_ref(v_inst_1696_);
lean_dec_ref(v_inst_1695_);
lean_inc(v_fallback_1699_);
return v_fallback_1699_;
}
else
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Std_DHashMap_Internal_Raw_u2080_getKeyD___redArg(v_inst_1695_, v_inst_1696_, v_m_1697_, v_a_1698_, v_fallback_1699_);
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKeyD___boxed(lean_object* v_00_u03b1_1705_, lean_object* v_00_u03b2_1706_, lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_m_1709_, lean_object* v_a_1710_, lean_object* v_fallback_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_Std_DHashMap_Raw_getKeyD(v_00_u03b1_1705_, v_00_u03b2_1706_, v_inst_1707_, v_inst_1708_, v_m_1709_, v_a_1710_, v_fallback_1711_);
lean_dec(v_fallback_1711_);
lean_dec_ref(v_m_1709_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg(lean_object* v_inst_1713_, lean_object* v_inst_1714_, lean_object* v_inst_1715_, lean_object* v_m_1716_, lean_object* v_a_1717_){
_start:
{
lean_object* v_keyArray_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; uint8_t v___x_1721_; 
v_keyArray_1718_ = lean_ctor_get(v_m_1716_, 1);
v___x_1719_ = lean_unsigned_to_nat(0u);
v___x_1720_ = lean_array_get_size(v_keyArray_1718_);
v___x_1721_ = lean_nat_dec_lt(v___x_1719_, v___x_1720_);
if (v___x_1721_ == 0)
{
lean_dec(v_a_1717_);
lean_dec_ref(v_inst_1714_);
lean_dec_ref(v_inst_1713_);
lean_inc(v_inst_1715_);
return v_inst_1715_;
}
else
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1713_, v_inst_1714_, v_inst_1715_, v_m_1716_, v_a_1717_);
return v___x_1722_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___redArg___boxed(lean_object* v_inst_1723_, lean_object* v_inst_1724_, lean_object* v_inst_1725_, lean_object* v_m_1726_, lean_object* v_a_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Std_DHashMap_Raw_getKey_x21___redArg(v_inst_1723_, v_inst_1724_, v_inst_1725_, v_m_1726_, v_a_1727_);
lean_dec_ref(v_m_1726_);
lean_dec(v_inst_1725_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21(lean_object* v_00_u03b1_1729_, lean_object* v_00_u03b2_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_inst_1733_, lean_object* v_m_1734_, lean_object* v_a_1735_){
_start:
{
lean_object* v_keyArray_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_keyArray_1736_ = lean_ctor_get(v_m_1734_, 1);
v___x_1737_ = lean_unsigned_to_nat(0u);
v___x_1738_ = lean_array_get_size(v_keyArray_1736_);
v___x_1739_ = lean_nat_dec_lt(v___x_1737_, v___x_1738_);
if (v___x_1739_ == 0)
{
lean_dec(v_a_1735_);
lean_dec_ref(v_inst_1732_);
lean_dec_ref(v_inst_1731_);
lean_inc(v_inst_1733_);
return v_inst_1733_;
}
else
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Std_DHashMap_Internal_Raw_u2080_getKey_x21___redArg(v_inst_1731_, v_inst_1732_, v_inst_1733_, v_m_1734_, v_a_1735_);
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getKey_x21___boxed(lean_object* v_00_u03b1_1741_, lean_object* v_00_u03b2_1742_, lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_inst_1745_, lean_object* v_m_1746_, lean_object* v_a_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Std_DHashMap_Raw_getKey_x21(v_00_u03b1_1741_, v_00_u03b2_1742_, v_inst_1743_, v_inst_1744_, v_inst_1745_, v_m_1746_, v_a_1747_);
lean_dec_ref(v_m_1746_);
lean_dec(v_inst_1745_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg(lean_object* v_inst_1749_, lean_object* v_inst_1750_, lean_object* v_m_1751_, lean_object* v_a_1752_){
_start:
{
lean_object* v_keyArray_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v_keyArray_1753_ = lean_ctor_get(v_m_1751_, 1);
v___x_1754_ = lean_unsigned_to_nat(0u);
v___x_1755_ = lean_array_get_size(v_keyArray_1753_);
v___x_1756_ = lean_nat_dec_lt(v___x_1754_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_object* v___x_1757_; 
lean_dec(v_a_1752_);
lean_dec_ref(v_inst_1750_);
lean_dec_ref(v_inst_1749_);
v___x_1757_ = lean_box(0);
return v___x_1757_;
}
else
{
lean_object* v___x_1758_; 
v___x_1758_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1749_, v_inst_1750_, v_m_1751_, v_a_1752_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___redArg___boxed(lean_object* v_inst_1759_, lean_object* v_inst_1760_, lean_object* v_m_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l_Std_DHashMap_Raw_getEntry_x3f___redArg(v_inst_1759_, v_inst_1760_, v_m_1761_, v_a_1762_);
lean_dec_ref(v_m_1761_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_inst_1766_, lean_object* v_inst_1767_, lean_object* v_m_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v_keyArray_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_keyArray_1770_ = lean_ctor_get(v_m_1768_, 1);
v___x_1771_ = lean_unsigned_to_nat(0u);
v___x_1772_ = lean_array_get_size(v_keyArray_1770_);
v___x_1773_ = lean_nat_dec_lt(v___x_1771_, v___x_1772_);
if (v___x_1773_ == 0)
{
lean_object* v___x_1774_; 
lean_dec(v_a_1769_);
lean_dec_ref(v_inst_1767_);
lean_dec_ref(v_inst_1766_);
v___x_1774_ = lean_box(0);
return v___x_1774_;
}
else
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x3f___redArg(v_inst_1766_, v_inst_1767_, v_m_1768_, v_a_1769_);
return v___x_1775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x3f___boxed(lean_object* v_00_u03b1_1776_, lean_object* v_00_u03b2_1777_, lean_object* v_inst_1778_, lean_object* v_inst_1779_, lean_object* v_m_1780_, lean_object* v_a_1781_){
_start:
{
lean_object* v_res_1782_; 
v_res_1782_ = l_Std_DHashMap_Raw_getEntry_x3f(v_00_u03b1_1776_, v_00_u03b2_1777_, v_inst_1778_, v_inst_1779_, v_m_1780_, v_a_1781_);
lean_dec_ref(v_m_1780_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg(lean_object* v_inst_1783_, lean_object* v_inst_1784_, lean_object* v_m_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1783_, v_inst_1784_, v_m_1785_, v_a_1786_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___redArg___boxed(lean_object* v_inst_1788_, lean_object* v_inst_1789_, lean_object* v_m_1790_, lean_object* v_a_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Std_DHashMap_Raw_getEntry___redArg(v_inst_1788_, v_inst_1789_, v_m_1790_, v_a_1791_);
lean_dec_ref(v_m_1790_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry(lean_object* v_00_u03b1_1793_, lean_object* v_00_u03b2_1794_, lean_object* v_inst_1795_, lean_object* v_inst_1796_, lean_object* v_m_1797_, lean_object* v_a_1798_, lean_object* v_h_1799_){
_start:
{
lean_object* v___x_1800_; 
v___x_1800_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry___redArg(v_inst_1795_, v_inst_1796_, v_m_1797_, v_a_1798_);
return v___x_1800_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry___boxed(lean_object* v_00_u03b1_1801_, lean_object* v_00_u03b2_1802_, lean_object* v_inst_1803_, lean_object* v_inst_1804_, lean_object* v_m_1805_, lean_object* v_a_1806_, lean_object* v_h_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Std_DHashMap_Raw_getEntry(v_00_u03b1_1801_, v_00_u03b2_1802_, v_inst_1803_, v_inst_1804_, v_m_1805_, v_a_1806_, v_h_1807_);
lean_dec_ref(v_m_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg(lean_object* v_inst_1809_, lean_object* v_inst_1810_, lean_object* v_m_1811_, lean_object* v_a_1812_, lean_object* v_fallback_1813_){
_start:
{
lean_object* v_keyArray_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v_keyArray_1814_ = lean_ctor_get(v_m_1811_, 1);
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_array_get_size(v_keyArray_1814_);
v___x_1817_ = lean_nat_dec_lt(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
lean_dec(v_a_1812_);
lean_dec_ref(v_inst_1810_);
lean_dec_ref(v_inst_1809_);
lean_inc_ref(v_fallback_1813_);
return v_fallback_1813_;
}
else
{
lean_object* v___x_1818_; 
v___x_1818_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1809_, v_inst_1810_, v_m_1811_, v_a_1812_, v_fallback_1813_);
return v___x_1818_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___redArg___boxed(lean_object* v_inst_1819_, lean_object* v_inst_1820_, lean_object* v_m_1821_, lean_object* v_a_1822_, lean_object* v_fallback_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Std_DHashMap_Raw_getEntryD___redArg(v_inst_1819_, v_inst_1820_, v_m_1821_, v_a_1822_, v_fallback_1823_);
lean_dec_ref(v_fallback_1823_);
lean_dec_ref(v_m_1821_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD(lean_object* v_00_u03b1_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_inst_1827_, lean_object* v_inst_1828_, lean_object* v_m_1829_, lean_object* v_a_1830_, lean_object* v_fallback_1831_){
_start:
{
lean_object* v_keyArray_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; uint8_t v___x_1835_; 
v_keyArray_1832_ = lean_ctor_get(v_m_1829_, 1);
v___x_1833_ = lean_unsigned_to_nat(0u);
v___x_1834_ = lean_array_get_size(v_keyArray_1832_);
v___x_1835_ = lean_nat_dec_lt(v___x_1833_, v___x_1834_);
if (v___x_1835_ == 0)
{
lean_dec(v_a_1830_);
lean_dec_ref(v_inst_1828_);
lean_dec_ref(v_inst_1827_);
lean_inc_ref(v_fallback_1831_);
return v_fallback_1831_;
}
else
{
lean_object* v___x_1836_; 
v___x_1836_ = l_Std_DHashMap_Internal_Raw_u2080_getEntryD___redArg(v_inst_1827_, v_inst_1828_, v_m_1829_, v_a_1830_, v_fallback_1831_);
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntryD___boxed(lean_object* v_00_u03b1_1837_, lean_object* v_00_u03b2_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_m_1841_, lean_object* v_a_1842_, lean_object* v_fallback_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Std_DHashMap_Raw_getEntryD(v_00_u03b1_1837_, v_00_u03b2_1838_, v_inst_1839_, v_inst_1840_, v_m_1841_, v_a_1842_, v_fallback_1843_);
lean_dec_ref(v_fallback_1843_);
lean_dec_ref(v_m_1841_);
return v_res_1844_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg(lean_object* v_inst_1845_, lean_object* v_inst_1846_, lean_object* v_inst_1847_, lean_object* v_m_1848_, lean_object* v_a_1849_){
_start:
{
lean_object* v_keyArray_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; uint8_t v___x_1853_; 
v_keyArray_1850_ = lean_ctor_get(v_m_1848_, 1);
v___x_1851_ = lean_unsigned_to_nat(0u);
v___x_1852_ = lean_array_get_size(v_keyArray_1850_);
v___x_1853_ = lean_nat_dec_lt(v___x_1851_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_dec(v_a_1849_);
lean_dec_ref(v_inst_1846_);
lean_dec_ref(v_inst_1845_);
lean_inc_ref(v_inst_1847_);
return v_inst_1847_;
}
else
{
lean_object* v___x_1854_; 
v___x_1854_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1845_, v_inst_1846_, v_m_1848_, v_a_1849_, v_inst_1847_);
return v___x_1854_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___redArg___boxed(lean_object* v_inst_1855_, lean_object* v_inst_1856_, lean_object* v_inst_1857_, lean_object* v_m_1858_, lean_object* v_a_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_Std_DHashMap_Raw_getEntry_x21___redArg(v_inst_1855_, v_inst_1856_, v_inst_1857_, v_m_1858_, v_a_1859_);
lean_dec_ref(v_m_1858_);
lean_dec_ref(v_inst_1857_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21(lean_object* v_00_u03b1_1861_, lean_object* v_00_u03b2_1862_, lean_object* v_inst_1863_, lean_object* v_inst_1864_, lean_object* v_inst_1865_, lean_object* v_m_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_keyArray_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v_keyArray_1868_ = lean_ctor_get(v_m_1866_, 1);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = lean_array_get_size(v_keyArray_1868_);
v___x_1871_ = lean_nat_dec_lt(v___x_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_dec(v_a_1867_);
lean_dec_ref(v_inst_1864_);
lean_dec_ref(v_inst_1863_);
lean_inc_ref(v_inst_1865_);
return v_inst_1865_;
}
else
{
lean_object* v___x_1872_; 
v___x_1872_ = l_Std_DHashMap_Internal_Raw_u2080_getEntry_x21___redArg(v_inst_1863_, v_inst_1864_, v_m_1866_, v_a_1867_, v_inst_1865_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_getEntry_x21___boxed(lean_object* v_00_u03b1_1873_, lean_object* v_00_u03b2_1874_, lean_object* v_inst_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_m_1878_, lean_object* v_a_1879_){
_start:
{
lean_object* v_res_1880_; 
v_res_1880_ = l_Std_DHashMap_Raw_getEntry_x21(v_00_u03b1_1873_, v_00_u03b2_1874_, v_inst_1875_, v_inst_1876_, v_inst_1877_, v_m_1878_, v_a_1879_);
lean_dec_ref(v_m_1878_);
lean_dec_ref(v_inst_1877_);
return v_res_1880_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty___redArg(lean_object* v_m_1881_){
_start:
{
lean_object* v_size_1882_; lean_object* v___x_1883_; uint8_t v___x_1884_; 
v_size_1882_ = lean_ctor_get(v_m_1881_, 0);
v___x_1883_ = lean_unsigned_to_nat(0u);
v___x_1884_ = lean_nat_dec_eq(v_size_1882_, v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___redArg___boxed(lean_object* v_m_1885_){
_start:
{
uint8_t v_res_1886_; lean_object* v_r_1887_; 
v_res_1886_ = l_Std_DHashMap_Raw_isEmpty___redArg(v_m_1885_);
lean_dec_ref(v_m_1885_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_isEmpty(lean_object* v_00_u03b1_1888_, lean_object* v_00_u03b2_1889_, lean_object* v_m_1890_){
_start:
{
lean_object* v_size_1891_; lean_object* v___x_1892_; uint8_t v___x_1893_; 
v_size_1891_ = lean_ctor_get(v_m_1890_, 0);
v___x_1892_ = lean_unsigned_to_nat(0u);
v___x_1893_ = lean_nat_dec_eq(v_size_1891_, v___x_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_isEmpty___boxed(lean_object* v_00_u03b1_1894_, lean_object* v_00_u03b2_1895_, lean_object* v_m_1896_){
_start:
{
uint8_t v_res_1897_; lean_object* v_r_1898_; 
v_res_1897_ = l_Std_DHashMap_Raw_isEmpty(v_00_u03b1_1894_, v_00_u03b2_1895_, v_m_1896_);
lean_dec_ref(v_m_1896_);
v_r_1898_ = lean_box(v_res_1897_);
return v_r_1898_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify___redArg(lean_object* v_inst_1899_, lean_object* v_inst_1900_, lean_object* v_m_1901_, lean_object* v_a_1902_, lean_object* v_f_1903_){
_start:
{
lean_object* v_size_1904_; lean_object* v_keyArray_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; uint8_t v___x_1908_; 
v_size_1904_ = lean_ctor_get(v_m_1901_, 0);
v_keyArray_1905_ = lean_ctor_get(v_m_1901_, 1);
v___x_1906_ = lean_unsigned_to_nat(0u);
v___x_1907_ = lean_array_get_size(v_keyArray_1905_);
v___x_1908_ = lean_nat_dec_lt(v___x_1906_, v___x_1907_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1909_; 
lean_dec(v_f_1903_);
lean_dec(v_a_1902_);
lean_dec_ref(v_m_1901_);
lean_dec_ref(v_inst_1900_);
lean_dec_ref(v_inst_1899_);
v___x_1909_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_1909_;
}
else
{
lean_object* v___x_1910_; 
lean_inc(v_a_1902_);
v___x_1910_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1899_, v_inst_1900_, v_m_1901_, v_a_1902_);
if (lean_obj_tag(v___x_1910_) == 0)
{
lean_object* v_index_1911_; lean_object* v_value_1912_; lean_object* v_v_x27_1913_; lean_object* v___x_1914_; 
lean_inc(v_size_1904_);
v_index_1911_ = lean_ctor_get(v___x_1910_, 0);
lean_inc(v_index_1911_);
v_value_1912_ = lean_ctor_get(v___x_1910_, 2);
lean_inc(v_value_1912_);
lean_dec_ref_known(v___x_1910_, 3);
v_v_x27_1913_ = lean_apply_1(v_f_1903_, v_value_1912_);
v___x_1914_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1901_, v_size_1904_, v_index_1911_, v_a_1902_, v_v_x27_1913_);
lean_dec(v_index_1911_);
return v___x_1914_;
}
else
{
lean_dec(v___x_1910_);
lean_dec(v_f_1903_);
lean_dec(v_a_1902_);
return v_m_1901_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_modify(lean_object* v_00_u03b1_1915_, lean_object* v_00_u03b2_1916_, lean_object* v_inst_1917_, lean_object* v_inst_1918_, lean_object* v_inst_1919_, lean_object* v_m_1920_, lean_object* v_a_1921_, lean_object* v_f_1922_){
_start:
{
lean_object* v_size_1923_; lean_object* v_keyArray_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v_size_1923_ = lean_ctor_get(v_m_1920_, 0);
v_keyArray_1924_ = lean_ctor_get(v_m_1920_, 1);
v___x_1925_ = lean_unsigned_to_nat(0u);
v___x_1926_ = lean_array_get_size(v_keyArray_1924_);
v___x_1927_ = lean_nat_dec_lt(v___x_1925_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; 
lean_dec(v_f_1922_);
lean_dec(v_a_1921_);
lean_dec_ref(v_m_1920_);
lean_dec_ref(v_inst_1919_);
lean_dec_ref(v_inst_1917_);
v___x_1928_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_1928_;
}
else
{
lean_object* v___x_1929_; 
lean_inc(v_a_1921_);
v___x_1929_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1917_, v_inst_1919_, v_m_1920_, v_a_1921_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_index_1930_; lean_object* v_value_1931_; lean_object* v_v_x27_1932_; lean_object* v___x_1933_; 
lean_inc(v_size_1923_);
v_index_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_index_1930_);
v_value_1931_ = lean_ctor_get(v___x_1929_, 2);
lean_inc(v_value_1931_);
lean_dec_ref_known(v___x_1929_, 3);
v_v_x27_1932_ = lean_apply_1(v_f_1922_, v_value_1931_);
v___x_1933_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1920_, v_size_1923_, v_index_1930_, v_a_1921_, v_v_x27_1932_);
lean_dec(v_index_1930_);
return v___x_1933_;
}
else
{
lean_dec(v___x_1929_);
lean_dec(v_f_1922_);
lean_dec(v_a_1921_);
return v_m_1920_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify___redArg(lean_object* v_inst_1934_, lean_object* v_inst_1935_, lean_object* v_m_1936_, lean_object* v_a_1937_, lean_object* v_f_1938_){
_start:
{
lean_object* v_size_1939_; lean_object* v_keyArray_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; uint8_t v___x_1943_; 
v_size_1939_ = lean_ctor_get(v_m_1936_, 0);
v_keyArray_1940_ = lean_ctor_get(v_m_1936_, 1);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_array_get_size(v_keyArray_1940_);
v___x_1943_ = lean_nat_dec_lt(v___x_1941_, v___x_1942_);
if (v___x_1943_ == 0)
{
lean_object* v___x_1944_; 
lean_dec(v_f_1938_);
lean_dec(v_a_1937_);
lean_dec_ref(v_m_1936_);
lean_dec_ref(v_inst_1935_);
lean_dec_ref(v_inst_1934_);
v___x_1944_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_1944_;
}
else
{
lean_object* v___x_1945_; 
lean_inc(v_a_1937_);
v___x_1945_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1934_, v_inst_1935_, v_m_1936_, v_a_1937_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_index_1946_; lean_object* v_value_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_inc(v_size_1939_);
v_index_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_index_1946_);
v_value_1947_ = lean_ctor_get(v___x_1945_, 2);
lean_inc(v_value_1947_);
lean_dec_ref_known(v___x_1945_, 3);
v___x_1948_ = lean_apply_1(v_f_1938_, v_value_1947_);
v___x_1949_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1936_, v_size_1939_, v_index_1946_, v_a_1937_, v___x_1948_);
lean_dec(v_index_1946_);
return v___x_1949_;
}
else
{
lean_dec(v___x_1945_);
lean_dec(v_f_1938_);
lean_dec(v_a_1937_);
return v_m_1936_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_modify(lean_object* v_00_u03b1_1950_, lean_object* v_inst_1951_, lean_object* v_inst_1952_, lean_object* v_inst_1953_, lean_object* v_00_u03b2_1954_, lean_object* v_m_1955_, lean_object* v_a_1956_, lean_object* v_f_1957_){
_start:
{
lean_object* v_size_1958_; lean_object* v_keyArray_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; 
v_size_1958_ = lean_ctor_get(v_m_1955_, 0);
v_keyArray_1959_ = lean_ctor_get(v_m_1955_, 1);
v___x_1960_ = lean_unsigned_to_nat(0u);
v___x_1961_ = lean_array_get_size(v_keyArray_1959_);
v___x_1962_ = lean_nat_dec_lt(v___x_1960_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
lean_dec(v_f_1957_);
lean_dec(v_a_1956_);
lean_dec_ref(v_m_1955_);
lean_dec_ref(v_inst_1953_);
lean_dec_ref(v_inst_1951_);
v___x_1963_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_1963_;
}
else
{
lean_object* v___x_1964_; 
lean_inc(v_a_1956_);
v___x_1964_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1951_, v_inst_1953_, v_m_1955_, v_a_1956_);
if (lean_obj_tag(v___x_1964_) == 0)
{
lean_object* v_index_1965_; lean_object* v_value_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_inc(v_size_1958_);
v_index_1965_ = lean_ctor_get(v___x_1964_, 0);
lean_inc(v_index_1965_);
v_value_1966_ = lean_ctor_get(v___x_1964_, 2);
lean_inc(v_value_1966_);
lean_dec_ref_known(v___x_1964_, 3);
v___x_1967_ = lean_apply_1(v_f_1957_, v_value_1966_);
v___x_1968_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1955_, v_size_1958_, v_index_1965_, v_a_1956_, v___x_1967_);
lean_dec(v_index_1965_);
return v___x_1968_;
}
else
{
lean_dec(v___x_1964_);
lean_dec(v_f_1957_);
lean_dec(v_a_1956_);
return v_m_1955_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter___redArg(lean_object* v_inst_1969_, lean_object* v_inst_1970_, lean_object* v_m_1971_, lean_object* v_a_1972_, lean_object* v_f_1973_){
_start:
{
lean_object* v_size_1974_; lean_object* v_keyArray_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; 
v_size_1974_ = lean_ctor_get(v_m_1971_, 0);
v_keyArray_1975_ = lean_ctor_get(v_m_1971_, 1);
v___x_1976_ = lean_unsigned_to_nat(0u);
v___x_1977_ = lean_array_get_size(v_keyArray_1975_);
v___x_1978_ = lean_nat_dec_lt(v___x_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_dec_ref(v_f_1973_);
lean_dec(v_a_1972_);
lean_dec_ref(v_m_1971_);
lean_dec_ref(v_inst_1970_);
lean_dec_ref(v_inst_1969_);
v___x_1979_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_1979_;
}
else
{
lean_object* v___x_1980_; 
lean_inc(v_a_1972_);
lean_inc_ref(v_inst_1970_);
lean_inc_ref(v_inst_1969_);
v___x_1980_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1969_, v_inst_1970_, v_m_1971_, v_a_1972_);
switch(lean_obj_tag(v___x_1980_))
{
case 0:
{
lean_object* v_index_1981_; lean_object* v_value_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
lean_dec_ref(v_inst_1970_);
lean_dec_ref(v_inst_1969_);
v_index_1981_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_index_1981_);
v_value_1982_ = lean_ctor_get(v___x_1980_, 2);
lean_inc(v_value_1982_);
lean_dec_ref_known(v___x_1980_, 3);
v___x_1983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1983_, 0, v_value_1982_);
v___x_1984_ = lean_apply_1(v_f_1973_, v___x_1983_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
lean_dec(v_a_1972_);
v___x_1985_ = lean_unsigned_to_nat(1u);
v___x_1986_ = lean_nat_sub(v_size_1974_, v___x_1985_);
v___x_1987_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_1971_, v___x_1986_, v_index_1981_);
lean_dec(v_index_1981_);
return v___x_1987_;
}
else
{
lean_object* v_val_1988_; lean_object* v___x_1989_; 
lean_inc(v_size_1974_);
v_val_1988_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_val_1988_);
lean_dec_ref_known(v___x_1984_, 1);
v___x_1989_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1971_, v_size_1974_, v_index_1981_, v_a_1972_, v_val_1988_);
lean_dec(v_index_1981_);
return v___x_1989_;
}
}
case 1:
{
lean_object* v_index_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v_index_1990_ = lean_ctor_get(v___x_1980_, 0);
lean_inc(v_index_1990_);
lean_dec_ref_known(v___x_1980_, 1);
v___x_1991_ = lean_box(0);
v___x_1992_ = lean_apply_1(v_f_1973_, v___x_1991_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_dec(v_index_1990_);
lean_dec(v_a_1972_);
lean_dec_ref(v_inst_1970_);
lean_dec_ref(v_inst_1969_);
return v_m_1971_;
}
else
{
lean_object* v_val_1993_; lean_object* v___y_1995_; lean_object* v_i_1996_; lean_object* v___x_2010_; lean_object* v___x_2011_; uint8_t v___x_2012_; 
v_val_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_val_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_2010_ = lean_unsigned_to_nat(1u);
v___x_2011_ = lean_nat_add(v_size_1974_, v___x_2010_);
v___x_2012_ = lean_nat_dec_lt(v___x_2011_, v___x_1977_);
if (v___x_2012_ == 0)
{
lean_dec(v___x_2011_);
lean_dec(v_index_1990_);
goto v___jp_2001_;
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; 
v___x_2013_ = lean_unsigned_to_nat(4u);
v___x_2014_ = lean_nat_mul(v___x_2011_, v___x_2013_);
v___x_2015_ = lean_unsigned_to_nat(3u);
v___x_2016_ = lean_nat_mul(v___x_1977_, v___x_2015_);
v___x_2017_ = lean_nat_dec_le(v___x_2014_, v___x_2016_);
lean_dec(v___x_2016_);
lean_dec(v___x_2014_);
if (v___x_2017_ == 0)
{
lean_dec(v___x_2011_);
lean_dec(v_index_1990_);
goto v___jp_2001_;
}
else
{
lean_object* v___x_2018_; 
lean_dec_ref(v_inst_1970_);
lean_dec_ref(v_inst_1969_);
v___x_2018_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_1971_, v___x_2011_, v_index_1990_, v_a_1972_, v_val_1993_);
lean_dec(v_index_1990_);
return v___x_2018_;
}
}
v___jp_1994_:
{
lean_object* v_size_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v_size_1997_ = lean_ctor_get(v___y_1995_, 0);
v___x_1998_ = lean_unsigned_to_nat(1u);
v___x_1999_ = lean_nat_add(v_size_1997_, v___x_1998_);
v___x_2000_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_1995_, v___x_1999_, v_i_1996_, v_a_1972_, v_val_1993_);
lean_dec(v_i_1996_);
return v___x_2000_;
}
v___jp_2001_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; 
lean_inc_ref(v_inst_1970_);
lean_inc_ref(v_inst_1969_);
v___x_2002_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1969_, v_inst_1970_, v_m_1971_);
lean_inc(v_a_1972_);
v___x_2003_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1969_, v_inst_1970_, v___x_2002_, v_a_1972_);
switch(lean_obj_tag(v___x_2003_))
{
case 0:
{
lean_object* v_index_2004_; lean_object* v_size_2005_; lean_object* v___x_2006_; 
v_index_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_index_2004_);
lean_dec_ref_known(v___x_2003_, 3);
v_size_2005_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_size_2005_);
v___x_2006_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2002_, v_size_2005_, v_index_2004_, v_a_1972_, v_val_1993_);
lean_dec(v_index_2004_);
return v___x_2006_;
}
case 1:
{
lean_object* v_index_2007_; 
v_index_2007_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_index_2007_);
lean_dec_ref_known(v___x_2003_, 1);
v___y_1995_ = v___x_2002_;
v_i_1996_ = v_index_2007_;
goto v___jp_1994_;
}
default: 
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2002_, v___x_1976_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_index_2009_; 
v_index_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_index_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v___y_1995_ = v___x_2002_;
v_i_1996_ = v_index_2009_;
goto v___jp_1994_;
}
else
{
lean_dec(v_val_1993_);
lean_dec(v_a_1972_);
return v___x_2002_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_box(0);
v___x_2020_ = lean_apply_1(v_f_1973_, v___x_2019_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_dec(v_a_1972_);
lean_dec_ref(v_inst_1970_);
lean_dec_ref(v_inst_1969_);
return v_m_1971_;
}
else
{
lean_object* v_val_2021_; lean_object* v___y_2023_; lean_object* v_i_2024_; lean_object* v___y_2030_; lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
v_val_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_val_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___x_2038_ = lean_unsigned_to_nat(1u);
v___x_2039_ = lean_nat_add(v_size_1974_, v___x_2038_);
v___x_2040_ = lean_nat_dec_lt(v___x_2039_, v___x_1977_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_dec(v___x_2039_);
lean_inc_ref(v_inst_1970_);
lean_inc_ref(v_inst_1969_);
v___x_2041_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1969_, v_inst_1970_, v_m_1971_);
v___y_2030_ = v___x_2041_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2042_ = lean_unsigned_to_nat(4u);
v___x_2043_ = lean_nat_mul(v___x_2039_, v___x_2042_);
lean_dec(v___x_2039_);
v___x_2044_ = lean_unsigned_to_nat(3u);
v___x_2045_ = lean_nat_mul(v___x_1977_, v___x_2044_);
v___x_2046_ = lean_nat_dec_le(v___x_2043_, v___x_2045_);
lean_dec(v___x_2045_);
lean_dec(v___x_2043_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; 
lean_inc_ref(v_inst_1970_);
lean_inc_ref(v_inst_1969_);
v___x_2047_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_1969_, v_inst_1970_, v_m_1971_);
v___y_2030_ = v___x_2047_;
goto v___jp_2029_;
}
else
{
v___y_2030_ = v_m_1971_;
goto v___jp_2029_;
}
}
v___jp_2022_:
{
lean_object* v_size_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_size_2025_ = lean_ctor_get(v___y_2023_, 0);
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2027_ = lean_nat_add(v_size_2025_, v___x_2026_);
v___x_2028_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2023_, v___x_2027_, v_i_2024_, v_a_1972_, v_val_2021_);
lean_dec(v_i_2024_);
return v___x_2028_;
}
v___jp_2029_:
{
lean_object* v___x_2031_; 
lean_inc(v_a_1972_);
v___x_2031_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_1969_, v_inst_1970_, v___y_2030_, v_a_1972_);
switch(lean_obj_tag(v___x_2031_))
{
case 0:
{
lean_object* v_index_2032_; lean_object* v_size_2033_; lean_object* v___x_2034_; 
v_index_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_index_2032_);
lean_dec_ref_known(v___x_2031_, 3);
v_size_2033_ = lean_ctor_get(v___y_2030_, 0);
lean_inc(v_size_2033_);
v___x_2034_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2030_, v_size_2033_, v_index_2032_, v_a_1972_, v_val_2021_);
lean_dec(v_index_2032_);
return v___x_2034_;
}
case 1:
{
lean_object* v_index_2035_; 
v_index_2035_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_index_2035_);
lean_dec_ref_known(v___x_2031_, 1);
v___y_2023_ = v___y_2030_;
v_i_2024_ = v_index_2035_;
goto v___jp_2022_;
}
default: 
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2030_, v___x_1976_);
if (lean_obj_tag(v___x_2036_) == 0)
{
lean_object* v_index_2037_; 
v_index_2037_ = lean_ctor_get(v___x_2036_, 0);
lean_inc(v_index_2037_);
lean_dec_ref_known(v___x_2036_, 1);
v___y_2023_ = v___y_2030_;
v_i_2024_ = v_index_2037_;
goto v___jp_2022_;
}
else
{
lean_dec(v_val_2021_);
lean_dec(v_a_1972_);
return v___y_2030_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_alter(lean_object* v_00_u03b1_2048_, lean_object* v_00_u03b2_2049_, lean_object* v_inst_2050_, lean_object* v_inst_2051_, lean_object* v_inst_2052_, lean_object* v_m_2053_, lean_object* v_a_2054_, lean_object* v_f_2055_){
_start:
{
lean_object* v_size_2056_; lean_object* v_keyArray_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; uint8_t v___x_2060_; 
v_size_2056_ = lean_ctor_get(v_m_2053_, 0);
v_keyArray_2057_ = lean_ctor_get(v_m_2053_, 1);
v___x_2058_ = lean_unsigned_to_nat(0u);
v___x_2059_ = lean_array_get_size(v_keyArray_2057_);
v___x_2060_ = lean_nat_dec_lt(v___x_2058_, v___x_2059_);
if (v___x_2060_ == 0)
{
lean_object* v___x_2061_; 
lean_dec_ref(v_f_2055_);
lean_dec(v_a_2054_);
lean_dec_ref(v_m_2053_);
lean_dec_ref(v_inst_2052_);
lean_dec_ref(v_inst_2050_);
v___x_2061_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_2061_;
}
else
{
lean_object* v___x_2062_; 
lean_inc(v_a_2054_);
lean_inc_ref(v_inst_2052_);
lean_inc_ref(v_inst_2050_);
v___x_2062_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2050_, v_inst_2052_, v_m_2053_, v_a_2054_);
switch(lean_obj_tag(v___x_2062_))
{
case 0:
{
lean_object* v_index_2063_; lean_object* v_value_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec_ref(v_inst_2052_);
lean_dec_ref(v_inst_2050_);
v_index_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_index_2063_);
v_value_2064_ = lean_ctor_get(v___x_2062_, 2);
lean_inc(v_value_2064_);
lean_dec_ref_known(v___x_2062_, 3);
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v_value_2064_);
v___x_2066_ = lean_apply_1(v_f_2055_, v___x_2065_);
if (lean_obj_tag(v___x_2066_) == 0)
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v_a_2054_);
v___x_2067_ = lean_unsigned_to_nat(1u);
v___x_2068_ = lean_nat_sub(v_size_2056_, v___x_2067_);
v___x_2069_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_2053_, v___x_2068_, v_index_2063_);
lean_dec(v_index_2063_);
return v___x_2069_;
}
else
{
lean_object* v_val_2070_; lean_object* v___x_2071_; 
lean_inc(v_size_2056_);
v_val_2070_ = lean_ctor_get(v___x_2066_, 0);
lean_inc(v_val_2070_);
lean_dec_ref_known(v___x_2066_, 1);
v___x_2071_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2053_, v_size_2056_, v_index_2063_, v_a_2054_, v_val_2070_);
lean_dec(v_index_2063_);
return v___x_2071_;
}
}
case 1:
{
lean_object* v_index_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; 
v_index_2072_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_index_2072_);
lean_dec_ref_known(v___x_2062_, 1);
v___x_2073_ = lean_box(0);
v___x_2074_ = lean_apply_1(v_f_2055_, v___x_2073_);
if (lean_obj_tag(v___x_2074_) == 0)
{
lean_dec(v_index_2072_);
lean_dec(v_a_2054_);
lean_dec_ref(v_inst_2052_);
lean_dec_ref(v_inst_2050_);
return v_m_2053_;
}
else
{
lean_object* v_val_2075_; lean_object* v___y_2077_; lean_object* v_i_2078_; lean_object* v___x_2092_; lean_object* v___x_2093_; uint8_t v___x_2094_; 
v_val_2075_ = lean_ctor_get(v___x_2074_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v___x_2074_, 1);
v___x_2092_ = lean_unsigned_to_nat(1u);
v___x_2093_ = lean_nat_add(v_size_2056_, v___x_2092_);
v___x_2094_ = lean_nat_dec_lt(v___x_2093_, v___x_2059_);
if (v___x_2094_ == 0)
{
lean_dec(v___x_2093_);
lean_dec(v_index_2072_);
goto v___jp_2083_;
}
else
{
lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2095_ = lean_unsigned_to_nat(4u);
v___x_2096_ = lean_nat_mul(v___x_2093_, v___x_2095_);
v___x_2097_ = lean_unsigned_to_nat(3u);
v___x_2098_ = lean_nat_mul(v___x_2059_, v___x_2097_);
v___x_2099_ = lean_nat_dec_le(v___x_2096_, v___x_2098_);
lean_dec(v___x_2098_);
lean_dec(v___x_2096_);
if (v___x_2099_ == 0)
{
lean_dec(v___x_2093_);
lean_dec(v_index_2072_);
goto v___jp_2083_;
}
else
{
lean_object* v___x_2100_; 
lean_dec_ref(v_inst_2052_);
lean_dec_ref(v_inst_2050_);
v___x_2100_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2053_, v___x_2093_, v_index_2072_, v_a_2054_, v_val_2075_);
lean_dec(v_index_2072_);
return v___x_2100_;
}
}
v___jp_2076_:
{
lean_object* v_size_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v_size_2079_ = lean_ctor_get(v___y_2077_, 0);
v___x_2080_ = lean_unsigned_to_nat(1u);
v___x_2081_ = lean_nat_add(v_size_2079_, v___x_2080_);
v___x_2082_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2077_, v___x_2081_, v_i_2078_, v_a_2054_, v_val_2075_);
lean_dec(v_i_2078_);
return v___x_2082_;
}
v___jp_2083_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_inc_ref(v_inst_2052_);
lean_inc_ref(v_inst_2050_);
v___x_2084_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2050_, v_inst_2052_, v_m_2053_);
lean_inc(v_a_2054_);
v___x_2085_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2050_, v_inst_2052_, v___x_2084_, v_a_2054_);
switch(lean_obj_tag(v___x_2085_))
{
case 0:
{
lean_object* v_index_2086_; lean_object* v_size_2087_; lean_object* v___x_2088_; 
v_index_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_index_2086_);
lean_dec_ref_known(v___x_2085_, 3);
v_size_2087_ = lean_ctor_get(v___x_2084_, 0);
lean_inc(v_size_2087_);
v___x_2088_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2084_, v_size_2087_, v_index_2086_, v_a_2054_, v_val_2075_);
lean_dec(v_index_2086_);
return v___x_2088_;
}
case 1:
{
lean_object* v_index_2089_; 
v_index_2089_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_index_2089_);
lean_dec_ref_known(v___x_2085_, 1);
v___y_2077_ = v___x_2084_;
v_i_2078_ = v_index_2089_;
goto v___jp_2076_;
}
default: 
{
lean_object* v___x_2090_; 
v___x_2090_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2084_, v___x_2058_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_index_2091_; 
v_index_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_index_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___y_2077_ = v___x_2084_;
v_i_2078_ = v_index_2091_;
goto v___jp_2076_;
}
else
{
lean_dec(v_val_2075_);
lean_dec(v_a_2054_);
return v___x_2084_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_box(0);
v___x_2102_ = lean_apply_1(v_f_2055_, v___x_2101_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_dec(v_a_2054_);
lean_dec_ref(v_inst_2052_);
lean_dec_ref(v_inst_2050_);
return v_m_2053_;
}
else
{
lean_object* v_val_2103_; lean_object* v___y_2105_; lean_object* v_i_2106_; lean_object* v___y_2112_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; 
v_val_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_val_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2120_ = lean_unsigned_to_nat(1u);
v___x_2121_ = lean_nat_add(v_size_2056_, v___x_2120_);
v___x_2122_ = lean_nat_dec_lt(v___x_2121_, v___x_2059_);
if (v___x_2122_ == 0)
{
lean_object* v___x_2123_; 
lean_dec(v___x_2121_);
lean_inc_ref(v_inst_2052_);
lean_inc_ref(v_inst_2050_);
v___x_2123_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2050_, v_inst_2052_, v_m_2053_);
v___y_2112_ = v___x_2123_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; uint8_t v___x_2128_; 
v___x_2124_ = lean_unsigned_to_nat(4u);
v___x_2125_ = lean_nat_mul(v___x_2121_, v___x_2124_);
lean_dec(v___x_2121_);
v___x_2126_ = lean_unsigned_to_nat(3u);
v___x_2127_ = lean_nat_mul(v___x_2059_, v___x_2126_);
v___x_2128_ = lean_nat_dec_le(v___x_2125_, v___x_2127_);
lean_dec(v___x_2127_);
lean_dec(v___x_2125_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; 
lean_inc_ref(v_inst_2052_);
lean_inc_ref(v_inst_2050_);
v___x_2129_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2050_, v_inst_2052_, v_m_2053_);
v___y_2112_ = v___x_2129_;
goto v___jp_2111_;
}
else
{
v___y_2112_ = v_m_2053_;
goto v___jp_2111_;
}
}
v___jp_2104_:
{
lean_object* v_size_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_size_2107_ = lean_ctor_get(v___y_2105_, 0);
v___x_2108_ = lean_unsigned_to_nat(1u);
v___x_2109_ = lean_nat_add(v_size_2107_, v___x_2108_);
v___x_2110_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2105_, v___x_2109_, v_i_2106_, v_a_2054_, v_val_2103_);
lean_dec(v_i_2106_);
return v___x_2110_;
}
v___jp_2111_:
{
lean_object* v___x_2113_; 
lean_inc(v_a_2054_);
v___x_2113_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2050_, v_inst_2052_, v___y_2112_, v_a_2054_);
switch(lean_obj_tag(v___x_2113_))
{
case 0:
{
lean_object* v_index_2114_; lean_object* v_size_2115_; lean_object* v___x_2116_; 
v_index_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_index_2114_);
lean_dec_ref_known(v___x_2113_, 3);
v_size_2115_ = lean_ctor_get(v___y_2112_, 0);
lean_inc(v_size_2115_);
v___x_2116_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2112_, v_size_2115_, v_index_2114_, v_a_2054_, v_val_2103_);
lean_dec(v_index_2114_);
return v___x_2116_;
}
case 1:
{
lean_object* v_index_2117_; 
v_index_2117_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_index_2117_);
lean_dec_ref_known(v___x_2113_, 1);
v___y_2105_ = v___y_2112_;
v_i_2106_ = v_index_2117_;
goto v___jp_2104_;
}
default: 
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2112_, v___x_2058_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_index_2119_; 
v_index_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_index_2119_);
lean_dec_ref_known(v___x_2118_, 1);
v___y_2105_ = v___y_2112_;
v_i_2106_ = v_index_2119_;
goto v___jp_2104_;
}
else
{
lean_dec(v_val_2103_);
lean_dec(v_a_2054_);
return v___y_2112_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter___redArg(lean_object* v_inst_2130_, lean_object* v_inst_2131_, lean_object* v_m_2132_, lean_object* v_a_2133_, lean_object* v_f_2134_){
_start:
{
lean_object* v_size_2135_; lean_object* v_keyArray_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v_size_2135_ = lean_ctor_get(v_m_2132_, 0);
v_keyArray_2136_ = lean_ctor_get(v_m_2132_, 1);
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_array_get_size(v_keyArray_2136_);
v___x_2139_ = lean_nat_dec_lt(v___x_2137_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
lean_dec_ref(v_f_2134_);
lean_dec(v_a_2133_);
lean_dec_ref(v_m_2132_);
lean_dec_ref(v_inst_2131_);
lean_dec_ref(v_inst_2130_);
v___x_2140_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_2140_;
}
else
{
lean_object* v___x_2141_; 
lean_inc(v_a_2133_);
lean_inc_ref(v_inst_2131_);
lean_inc_ref(v_inst_2130_);
v___x_2141_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2130_, v_inst_2131_, v_m_2132_, v_a_2133_);
switch(lean_obj_tag(v___x_2141_))
{
case 0:
{
lean_object* v_index_2142_; lean_object* v_value_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
lean_dec_ref(v_inst_2131_);
lean_dec_ref(v_inst_2130_);
v_index_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_index_2142_);
v_value_2143_ = lean_ctor_get(v___x_2141_, 2);
lean_inc(v_value_2143_);
lean_dec_ref_known(v___x_2141_, 3);
v___x_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2144_, 0, v_value_2143_);
v___x_2145_ = lean_apply_1(v_f_2134_, v___x_2144_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; 
lean_dec(v_a_2133_);
v___x_2146_ = lean_unsigned_to_nat(1u);
v___x_2147_ = lean_nat_sub(v_size_2135_, v___x_2146_);
v___x_2148_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_2132_, v___x_2147_, v_index_2142_);
lean_dec(v_index_2142_);
return v___x_2148_;
}
else
{
lean_object* v_val_2149_; lean_object* v___x_2150_; 
lean_inc(v_size_2135_);
v_val_2149_ = lean_ctor_get(v___x_2145_, 0);
lean_inc(v_val_2149_);
lean_dec_ref_known(v___x_2145_, 1);
v___x_2150_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2132_, v_size_2135_, v_index_2142_, v_a_2133_, v_val_2149_);
lean_dec(v_index_2142_);
return v___x_2150_;
}
}
case 1:
{
lean_object* v_index_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v_index_2151_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_index_2151_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2152_ = lean_box(0);
v___x_2153_ = lean_apply_1(v_f_2134_, v___x_2152_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_dec(v_index_2151_);
lean_dec(v_a_2133_);
lean_dec_ref(v_inst_2131_);
lean_dec_ref(v_inst_2130_);
return v_m_2132_;
}
else
{
lean_object* v_val_2154_; lean_object* v___y_2156_; lean_object* v_i_2157_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v_val_2154_ = lean_ctor_get(v___x_2153_, 0);
lean_inc(v_val_2154_);
lean_dec_ref_known(v___x_2153_, 1);
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_add(v_size_2135_, v___x_2171_);
v___x_2173_ = lean_nat_dec_lt(v___x_2172_, v___x_2138_);
if (v___x_2173_ == 0)
{
lean_dec(v___x_2172_);
lean_dec(v_index_2151_);
goto v___jp_2162_;
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2174_ = lean_unsigned_to_nat(4u);
v___x_2175_ = lean_nat_mul(v___x_2172_, v___x_2174_);
v___x_2176_ = lean_unsigned_to_nat(3u);
v___x_2177_ = lean_nat_mul(v___x_2138_, v___x_2176_);
v___x_2178_ = lean_nat_dec_le(v___x_2175_, v___x_2177_);
lean_dec(v___x_2177_);
lean_dec(v___x_2175_);
if (v___x_2178_ == 0)
{
lean_dec(v___x_2172_);
lean_dec(v_index_2151_);
goto v___jp_2162_;
}
else
{
lean_object* v___x_2179_; 
lean_dec_ref(v_inst_2131_);
lean_dec_ref(v_inst_2130_);
v___x_2179_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2132_, v___x_2172_, v_index_2151_, v_a_2133_, v_val_2154_);
lean_dec(v_index_2151_);
return v___x_2179_;
}
}
v___jp_2155_:
{
lean_object* v_size_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v_size_2158_ = lean_ctor_get(v___y_2156_, 0);
v___x_2159_ = lean_unsigned_to_nat(1u);
v___x_2160_ = lean_nat_add(v_size_2158_, v___x_2159_);
v___x_2161_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2156_, v___x_2160_, v_i_2157_, v_a_2133_, v_val_2154_);
lean_dec(v_i_2157_);
return v___x_2161_;
}
v___jp_2162_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_inc_ref(v_inst_2131_);
lean_inc_ref(v_inst_2130_);
v___x_2163_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2130_, v_inst_2131_, v_m_2132_);
lean_inc(v_a_2133_);
v___x_2164_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2130_, v_inst_2131_, v___x_2163_, v_a_2133_);
switch(lean_obj_tag(v___x_2164_))
{
case 0:
{
lean_object* v_index_2165_; lean_object* v_size_2166_; lean_object* v___x_2167_; 
v_index_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_index_2165_);
lean_dec_ref_known(v___x_2164_, 3);
v_size_2166_ = lean_ctor_get(v___x_2163_, 0);
lean_inc(v_size_2166_);
v___x_2167_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2163_, v_size_2166_, v_index_2165_, v_a_2133_, v_val_2154_);
lean_dec(v_index_2165_);
return v___x_2167_;
}
case 1:
{
lean_object* v_index_2168_; 
v_index_2168_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_index_2168_);
lean_dec_ref_known(v___x_2164_, 1);
v___y_2156_ = v___x_2163_;
v_i_2157_ = v_index_2168_;
goto v___jp_2155_;
}
default: 
{
lean_object* v___x_2169_; 
v___x_2169_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2163_, v___x_2137_);
if (lean_obj_tag(v___x_2169_) == 0)
{
lean_object* v_index_2170_; 
v_index_2170_ = lean_ctor_get(v___x_2169_, 0);
lean_inc(v_index_2170_);
lean_dec_ref_known(v___x_2169_, 1);
v___y_2156_ = v___x_2163_;
v_i_2157_ = v_index_2170_;
goto v___jp_2155_;
}
else
{
lean_dec(v_val_2154_);
lean_dec(v_a_2133_);
return v___x_2163_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_box(0);
v___x_2181_ = lean_apply_1(v_f_2134_, v___x_2180_);
if (lean_obj_tag(v___x_2181_) == 0)
{
lean_dec(v_a_2133_);
lean_dec_ref(v_inst_2131_);
lean_dec_ref(v_inst_2130_);
return v_m_2132_;
}
else
{
lean_object* v_val_2182_; lean_object* v___y_2184_; lean_object* v_i_2185_; lean_object* v___y_2191_; lean_object* v___x_2199_; lean_object* v___x_2200_; uint8_t v___x_2201_; 
v_val_2182_ = lean_ctor_get(v___x_2181_, 0);
lean_inc(v_val_2182_);
lean_dec_ref_known(v___x_2181_, 1);
v___x_2199_ = lean_unsigned_to_nat(1u);
v___x_2200_ = lean_nat_add(v_size_2135_, v___x_2199_);
v___x_2201_ = lean_nat_dec_lt(v___x_2200_, v___x_2138_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
lean_dec(v___x_2200_);
lean_inc_ref(v_inst_2131_);
lean_inc_ref(v_inst_2130_);
v___x_2202_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2130_, v_inst_2131_, v_m_2132_);
v___y_2191_ = v___x_2202_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; uint8_t v___x_2207_; 
v___x_2203_ = lean_unsigned_to_nat(4u);
v___x_2204_ = lean_nat_mul(v___x_2200_, v___x_2203_);
lean_dec(v___x_2200_);
v___x_2205_ = lean_unsigned_to_nat(3u);
v___x_2206_ = lean_nat_mul(v___x_2138_, v___x_2205_);
v___x_2207_ = lean_nat_dec_le(v___x_2204_, v___x_2206_);
lean_dec(v___x_2206_);
lean_dec(v___x_2204_);
if (v___x_2207_ == 0)
{
lean_object* v___x_2208_; 
lean_inc_ref(v_inst_2131_);
lean_inc_ref(v_inst_2130_);
v___x_2208_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2130_, v_inst_2131_, v_m_2132_);
v___y_2191_ = v___x_2208_;
goto v___jp_2190_;
}
else
{
v___y_2191_ = v_m_2132_;
goto v___jp_2190_;
}
}
v___jp_2183_:
{
lean_object* v_size_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v_size_2186_ = lean_ctor_get(v___y_2184_, 0);
v___x_2187_ = lean_unsigned_to_nat(1u);
v___x_2188_ = lean_nat_add(v_size_2186_, v___x_2187_);
v___x_2189_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2184_, v___x_2188_, v_i_2185_, v_a_2133_, v_val_2182_);
lean_dec(v_i_2185_);
return v___x_2189_;
}
v___jp_2190_:
{
lean_object* v___x_2192_; 
lean_inc(v_a_2133_);
v___x_2192_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2130_, v_inst_2131_, v___y_2191_, v_a_2133_);
switch(lean_obj_tag(v___x_2192_))
{
case 0:
{
lean_object* v_index_2193_; lean_object* v_size_2194_; lean_object* v___x_2195_; 
v_index_2193_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_index_2193_);
lean_dec_ref_known(v___x_2192_, 3);
v_size_2194_ = lean_ctor_get(v___y_2191_, 0);
lean_inc(v_size_2194_);
v___x_2195_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2191_, v_size_2194_, v_index_2193_, v_a_2133_, v_val_2182_);
lean_dec(v_index_2193_);
return v___x_2195_;
}
case 1:
{
lean_object* v_index_2196_; 
v_index_2196_ = lean_ctor_get(v___x_2192_, 0);
lean_inc(v_index_2196_);
lean_dec_ref_known(v___x_2192_, 1);
v___y_2184_ = v___y_2191_;
v_i_2185_ = v_index_2196_;
goto v___jp_2183_;
}
default: 
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2191_, v___x_2137_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_index_2198_; 
v_index_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_index_2198_);
lean_dec_ref_known(v___x_2197_, 1);
v___y_2184_ = v___y_2191_;
v_i_2185_ = v_index_2198_;
goto v___jp_2183_;
}
else
{
lean_dec(v_val_2182_);
lean_dec(v_a_2133_);
return v___y_2191_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_alter(lean_object* v_00_u03b1_2209_, lean_object* v_inst_2210_, lean_object* v_inst_2211_, lean_object* v_inst_2212_, lean_object* v_00_u03b2_2213_, lean_object* v_m_2214_, lean_object* v_a_2215_, lean_object* v_f_2216_){
_start:
{
lean_object* v_size_2217_; lean_object* v_keyArray_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; 
v_size_2217_ = lean_ctor_get(v_m_2214_, 0);
v_keyArray_2218_ = lean_ctor_get(v_m_2214_, 1);
v___x_2219_ = lean_unsigned_to_nat(0u);
v___x_2220_ = lean_array_get_size(v_keyArray_2218_);
v___x_2221_ = lean_nat_dec_lt(v___x_2219_, v___x_2220_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; 
lean_dec_ref(v_f_2216_);
lean_dec(v_a_2215_);
lean_dec_ref(v_m_2214_);
lean_dec_ref(v_inst_2212_);
lean_dec_ref(v_inst_2210_);
v___x_2222_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_2222_;
}
else
{
lean_object* v___x_2223_; 
lean_inc(v_a_2215_);
lean_inc_ref(v_inst_2212_);
lean_inc_ref(v_inst_2210_);
v___x_2223_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2210_, v_inst_2212_, v_m_2214_, v_a_2215_);
switch(lean_obj_tag(v___x_2223_))
{
case 0:
{
lean_object* v_index_2224_; lean_object* v_value_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec_ref(v_inst_2212_);
lean_dec_ref(v_inst_2210_);
v_index_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_index_2224_);
v_value_2225_ = lean_ctor_get(v___x_2223_, 2);
lean_inc(v_value_2225_);
lean_dec_ref_known(v___x_2223_, 3);
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v_value_2225_);
v___x_2227_ = lean_apply_1(v_f_2216_, v___x_2226_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
lean_dec(v_a_2215_);
v___x_2228_ = lean_unsigned_to_nat(1u);
v___x_2229_ = lean_nat_sub(v_size_2217_, v___x_2228_);
v___x_2230_ = l_Std_DHashMap_Raw_clearCell___redArg(v_m_2214_, v___x_2229_, v_index_2224_);
lean_dec(v_index_2224_);
return v___x_2230_;
}
else
{
lean_object* v_val_2231_; lean_object* v___x_2232_; 
lean_inc(v_size_2217_);
v_val_2231_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_val_2231_);
lean_dec_ref_known(v___x_2227_, 1);
v___x_2232_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2214_, v_size_2217_, v_index_2224_, v_a_2215_, v_val_2231_);
lean_dec(v_index_2224_);
return v___x_2232_;
}
}
case 1:
{
lean_object* v_index_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_index_2233_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_index_2233_);
lean_dec_ref_known(v___x_2223_, 1);
v___x_2234_ = lean_box(0);
v___x_2235_ = lean_apply_1(v_f_2216_, v___x_2234_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_dec(v_index_2233_);
lean_dec(v_a_2215_);
lean_dec_ref(v_inst_2212_);
lean_dec_ref(v_inst_2210_);
return v_m_2214_;
}
else
{
lean_object* v_val_2236_; lean_object* v___y_2238_; lean_object* v_i_2239_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; 
v_val_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v___x_2235_, 1);
v___x_2253_ = lean_unsigned_to_nat(1u);
v___x_2254_ = lean_nat_add(v_size_2217_, v___x_2253_);
v___x_2255_ = lean_nat_dec_lt(v___x_2254_, v___x_2220_);
if (v___x_2255_ == 0)
{
lean_dec(v___x_2254_);
lean_dec(v_index_2233_);
goto v___jp_2244_;
}
else
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; 
v___x_2256_ = lean_unsigned_to_nat(4u);
v___x_2257_ = lean_nat_mul(v___x_2254_, v___x_2256_);
v___x_2258_ = lean_unsigned_to_nat(3u);
v___x_2259_ = lean_nat_mul(v___x_2220_, v___x_2258_);
v___x_2260_ = lean_nat_dec_le(v___x_2257_, v___x_2259_);
lean_dec(v___x_2259_);
lean_dec(v___x_2257_);
if (v___x_2260_ == 0)
{
lean_dec(v___x_2254_);
lean_dec(v_index_2233_);
goto v___jp_2244_;
}
else
{
lean_object* v___x_2261_; 
lean_dec_ref(v_inst_2212_);
lean_dec_ref(v_inst_2210_);
v___x_2261_ = l_Std_DHashMap_Raw_setEntry___redArg(v_m_2214_, v___x_2254_, v_index_2233_, v_a_2215_, v_val_2236_);
lean_dec(v_index_2233_);
return v___x_2261_;
}
}
v___jp_2237_:
{
lean_object* v_size_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v_size_2240_ = lean_ctor_get(v___y_2238_, 0);
v___x_2241_ = lean_unsigned_to_nat(1u);
v___x_2242_ = lean_nat_add(v_size_2240_, v___x_2241_);
v___x_2243_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2238_, v___x_2242_, v_i_2239_, v_a_2215_, v_val_2236_);
lean_dec(v_i_2239_);
return v___x_2243_;
}
v___jp_2244_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
lean_inc_ref(v_inst_2212_);
lean_inc_ref(v_inst_2210_);
v___x_2245_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2210_, v_inst_2212_, v_m_2214_);
lean_inc(v_a_2215_);
v___x_2246_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2210_, v_inst_2212_, v___x_2245_, v_a_2215_);
switch(lean_obj_tag(v___x_2246_))
{
case 0:
{
lean_object* v_index_2247_; lean_object* v_size_2248_; lean_object* v___x_2249_; 
v_index_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_index_2247_);
lean_dec_ref_known(v___x_2246_, 3);
v_size_2248_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_size_2248_);
v___x_2249_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2245_, v_size_2248_, v_index_2247_, v_a_2215_, v_val_2236_);
lean_dec(v_index_2247_);
return v___x_2249_;
}
case 1:
{
lean_object* v_index_2250_; 
v_index_2250_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_index_2250_);
lean_dec_ref_known(v___x_2246_, 1);
v___y_2238_ = v___x_2245_;
v_i_2239_ = v_index_2250_;
goto v___jp_2237_;
}
default: 
{
lean_object* v___x_2251_; 
v___x_2251_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2245_, v___x_2219_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_index_2252_; 
v_index_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_index_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v___y_2238_ = v___x_2245_;
v_i_2239_ = v_index_2252_;
goto v___jp_2237_;
}
else
{
lean_dec(v_val_2236_);
lean_dec(v_a_2215_);
return v___x_2245_;
}
}
}
}
}
}
default: 
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = lean_box(0);
v___x_2263_ = lean_apply_1(v_f_2216_, v___x_2262_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_dec(v_a_2215_);
lean_dec_ref(v_inst_2212_);
lean_dec_ref(v_inst_2210_);
return v_m_2214_;
}
else
{
lean_object* v_val_2264_; lean_object* v___y_2266_; lean_object* v_i_2267_; lean_object* v___y_2273_; lean_object* v___x_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_val_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_val_2264_);
lean_dec_ref_known(v___x_2263_, 1);
v___x_2281_ = lean_unsigned_to_nat(1u);
v___x_2282_ = lean_nat_add(v_size_2217_, v___x_2281_);
v___x_2283_ = lean_nat_dec_lt(v___x_2282_, v___x_2220_);
if (v___x_2283_ == 0)
{
lean_object* v___x_2284_; 
lean_dec(v___x_2282_);
lean_inc_ref(v_inst_2212_);
lean_inc_ref(v_inst_2210_);
v___x_2284_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2210_, v_inst_2212_, v_m_2214_);
v___y_2273_ = v___x_2284_;
goto v___jp_2272_;
}
else
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v___x_2285_ = lean_unsigned_to_nat(4u);
v___x_2286_ = lean_nat_mul(v___x_2282_, v___x_2285_);
lean_dec(v___x_2282_);
v___x_2287_ = lean_unsigned_to_nat(3u);
v___x_2288_ = lean_nat_mul(v___x_2220_, v___x_2287_);
v___x_2289_ = lean_nat_dec_le(v___x_2286_, v___x_2288_);
lean_dec(v___x_2288_);
lean_dec(v___x_2286_);
if (v___x_2289_ == 0)
{
lean_object* v___x_2290_; 
lean_inc_ref(v_inst_2212_);
lean_inc_ref(v_inst_2210_);
v___x_2290_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2210_, v_inst_2212_, v_m_2214_);
v___y_2273_ = v___x_2290_;
goto v___jp_2272_;
}
else
{
v___y_2273_ = v_m_2214_;
goto v___jp_2272_;
}
}
v___jp_2265_:
{
lean_object* v_size_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v_size_2268_ = lean_ctor_get(v___y_2266_, 0);
v___x_2269_ = lean_unsigned_to_nat(1u);
v___x_2270_ = lean_nat_add(v_size_2268_, v___x_2269_);
v___x_2271_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2266_, v___x_2270_, v_i_2267_, v_a_2215_, v_val_2264_);
lean_dec(v_i_2267_);
return v___x_2271_;
}
v___jp_2272_:
{
lean_object* v___x_2274_; 
lean_inc(v_a_2215_);
v___x_2274_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2210_, v_inst_2212_, v___y_2273_, v_a_2215_);
switch(lean_obj_tag(v___x_2274_))
{
case 0:
{
lean_object* v_index_2275_; lean_object* v_size_2276_; lean_object* v___x_2277_; 
v_index_2275_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_index_2275_);
lean_dec_ref_known(v___x_2274_, 3);
v_size_2276_ = lean_ctor_get(v___y_2273_, 0);
lean_inc(v_size_2276_);
v___x_2277_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2273_, v_size_2276_, v_index_2275_, v_a_2215_, v_val_2264_);
lean_dec(v_index_2275_);
return v___x_2277_;
}
case 1:
{
lean_object* v_index_2278_; 
v_index_2278_ = lean_ctor_get(v___x_2274_, 0);
lean_inc(v_index_2278_);
lean_dec_ref_known(v___x_2274_, 1);
v___y_2266_ = v___y_2273_;
v_i_2267_ = v_index_2278_;
goto v___jp_2265_;
}
default: 
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2273_, v___x_2219_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_index_2280_; 
v_index_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_index_2280_);
lean_dec_ref_known(v___x_2279_, 1);
v___y_2266_ = v___y_2273_;
v_i_2267_ = v_index_2280_;
goto v___jp_2265_;
}
else
{
lean_dec(v_val_2264_);
lean_dec(v_a_2215_);
return v___y_2273_;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg(lean_object* v_inst_2291_, lean_object* v_f_2292_, lean_object* v_init_2293_, lean_object* v_b_2294_){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = lean_unsigned_to_nat(0u);
v___x_2296_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v_inst_2291_, v_f_2292_, v_b_2294_, v_init_2293_, v___x_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___redArg___boxed(lean_object* v_inst_2297_, lean_object* v_f_2298_, lean_object* v_init_2299_, lean_object* v_b_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Std_DHashMap_Raw_Internal_foldRevM___redArg(v_inst_2297_, v_f_2298_, v_init_2299_, v_b_2300_);
lean_dec_ref(v_b_2300_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM(lean_object* v_00_u03b1_2302_, lean_object* v_00_u03b2_2303_, lean_object* v_00_u03b4_2304_, lean_object* v_m_2305_, lean_object* v_inst_2306_, lean_object* v_f_2307_, lean_object* v_init_2308_, lean_object* v_b_2309_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_unsigned_to_nat(0u);
v___x_2311_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v_inst_2306_, v_f_2307_, v_b_2309_, v_init_2308_, v___x_2310_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRevM___boxed(lean_object* v_00_u03b1_2312_, lean_object* v_00_u03b2_2313_, lean_object* v_00_u03b4_2314_, lean_object* v_m_2315_, lean_object* v_inst_2316_, lean_object* v_f_2317_, lean_object* v_init_2318_, lean_object* v_b_2319_){
_start:
{
lean_object* v_res_2320_; 
v_res_2320_ = l_Std_DHashMap_Raw_Internal_foldRevM(v_00_u03b1_2312_, v_00_u03b2_2313_, v_00_u03b4_2314_, v_m_2315_, v_inst_2316_, v_f_2317_, v_init_2318_, v_b_2319_);
lean_dec_ref(v_b_2319_);
return v_res_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__0(lean_object* v_f_2321_, lean_object* v_x1_2322_, lean_object* v_x2_2323_, lean_object* v_x3_2324_){
_start:
{
lean_object* v___x_2325_; 
v___x_2325_ = lean_apply_3(v_f_2321_, v_x1_2322_, v_x2_2323_, v_x3_2324_);
return v___x_2325_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg(lean_object* v_f_2345_, lean_object* v_init_2346_, lean_object* v_b_2347_){
_start:
{
lean_object* v___f_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
v___f_2348_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2348_, 0, v_f_2345_);
v___x_2349_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2350_ = lean_unsigned_to_nat(0u);
v___x_2351_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2349_, v___f_2348_, v_b_2347_, v_init_2346_, v___x_2350_);
return v___x_2351_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___redArg___boxed(lean_object* v_f_2352_, lean_object* v_init_2353_, lean_object* v_b_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Std_DHashMap_Raw_Internal_foldRev___redArg(v_f_2352_, v_init_2353_, v_b_2354_);
lean_dec_ref(v_b_2354_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev(lean_object* v_00_u03b1_2356_, lean_object* v_00_u03b2_2357_, lean_object* v_00_u03b4_2358_, lean_object* v_f_2359_, lean_object* v_init_2360_, lean_object* v_b_2361_){
_start:
{
lean_object* v___f_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___f_2362_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2362_, 0, v_f_2359_);
v___x_2363_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2364_ = lean_unsigned_to_nat(0u);
v___x_2365_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2363_, v___f_2362_, v_b_2361_, v_init_2360_, v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_foldRev___boxed(lean_object* v_00_u03b1_2366_, lean_object* v_00_u03b2_2367_, lean_object* v_00_u03b4_2368_, lean_object* v_f_2369_, lean_object* v_init_2370_, lean_object* v_b_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Std_DHashMap_Raw_Internal_foldRev(v_00_u03b1_2366_, v_00_u03b2_2367_, v_00_u03b4_2368_, v_f_2369_, v_init_2370_, v_b_2371_);
lean_dec_ref(v_b_2371_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___redArg(lean_object* v_inst_2373_, lean_object* v_f_2374_, lean_object* v_init_2375_, lean_object* v_b_2376_){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = lean_unsigned_to_nat(0u);
v___x_2378_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v_inst_2373_, v_f_2374_, v_b_2376_, v_init_2375_, v___x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___redArg___boxed(lean_object* v_inst_2379_, lean_object* v_f_2380_, lean_object* v_init_2381_, lean_object* v_b_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Std_DHashMap_Raw_foldRevM___redArg(v_inst_2379_, v_f_2380_, v_init_2381_, v_b_2382_);
lean_dec_ref(v_b_2382_);
return v_res_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM(lean_object* v_00_u03b1_2384_, lean_object* v_00_u03b2_2385_, lean_object* v_00_u03b4_2386_, lean_object* v_m_2387_, lean_object* v_inst_2388_, lean_object* v_f_2389_, lean_object* v_init_2390_, lean_object* v_b_2391_){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v_inst_2388_, v_f_2389_, v_b_2391_, v_init_2390_, v___x_2392_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRevM___boxed(lean_object* v_00_u03b1_2394_, lean_object* v_00_u03b2_2395_, lean_object* v_00_u03b4_2396_, lean_object* v_m_2397_, lean_object* v_inst_2398_, lean_object* v_f_2399_, lean_object* v_init_2400_, lean_object* v_b_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Std_DHashMap_Raw_foldRevM(v_00_u03b1_2394_, v_00_u03b2_2395_, v_00_u03b4_2396_, v_m_2397_, v_inst_2398_, v_f_2399_, v_init_2400_, v_b_2401_);
lean_dec_ref(v_b_2401_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___redArg(lean_object* v_f_2403_, lean_object* v_init_2404_, lean_object* v_b_2405_){
_start:
{
lean_object* v___f_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___f_2406_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2406_, 0, v_f_2403_);
v___x_2407_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2408_ = lean_unsigned_to_nat(0u);
v___x_2409_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2407_, v___f_2406_, v_b_2405_, v_init_2404_, v___x_2408_);
return v___x_2409_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___redArg___boxed(lean_object* v_f_2410_, lean_object* v_init_2411_, lean_object* v_b_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Std_DHashMap_Raw_foldRev___redArg(v_f_2410_, v_init_2411_, v_b_2412_);
lean_dec_ref(v_b_2412_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev(lean_object* v_00_u03b1_2414_, lean_object* v_00_u03b2_2415_, lean_object* v_00_u03b4_2416_, lean_object* v_f_2417_, lean_object* v_init_2418_, lean_object* v_b_2419_){
_start:
{
lean_object* v___f_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; 
v___f_2420_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2420_, 0, v_f_2417_);
v___x_2421_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2422_ = lean_unsigned_to_nat(0u);
v___x_2423_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2421_, v___f_2420_, v_b_2419_, v_init_2418_, v___x_2422_);
return v___x_2423_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldRev___boxed(lean_object* v_00_u03b1_2424_, lean_object* v_00_u03b2_2425_, lean_object* v_00_u03b4_2426_, lean_object* v_f_2427_, lean_object* v_init_2428_, lean_object* v_b_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Std_DHashMap_Raw_foldRev(v_00_u03b1_2424_, v_00_u03b2_2425_, v_00_u03b4_2426_, v_f_2427_, v_init_2428_, v_b_2429_);
lean_dec_ref(v_b_2429_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0(lean_object* v_f_2431_, lean_object* v_x_2432_, lean_object* v_a_2433_, lean_object* v_v_2434_){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2435_, 0, v_a_2433_);
lean_ctor_set(v___x_2435_, 1, v_v_2434_);
v___x_2436_ = lean_apply_1(v_f_2431_, v___x_2435_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried___redArg(lean_object* v_inst_2437_, lean_object* v_f_2438_, lean_object* v_b_2439_){
_start:
{
lean_object* v___f_2440_; lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___f_2440_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2440_, 0, v_f_2438_);
v___x_2441_ = lean_box(0);
v___x_2442_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_2437_, v___f_2440_, v___x_2441_, v_b_2439_);
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forMUncurried(lean_object* v_00_u03b1_2443_, lean_object* v_m_2444_, lean_object* v_inst_2445_, lean_object* v_00_u03b2_2446_, lean_object* v_f_2447_, lean_object* v_b_2448_){
_start:
{
lean_object* v___f_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___f_2449_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forMUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2449_, 0, v_f_2447_);
v___x_2450_ = lean_box(0);
v___x_2451_ = l_Std_DHashMap_Raw_foldM___redArg(v_inst_2445_, v___f_2449_, v___x_2450_, v_b_2448_);
return v___x_2451_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0(lean_object* v_f_2452_, lean_object* v_a_2453_, lean_object* v_b_2454_, lean_object* v_d_2455_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; 
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v_a_2453_);
lean_ctor_set(v___x_2456_, 1, v_b_2454_);
v___x_2457_ = lean_apply_2(v_f_2452_, v___x_2456_, v_d_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried___redArg(lean_object* v_inst_2458_, lean_object* v_f_2459_, lean_object* v_init_2460_, lean_object* v_b_2461_){
_start:
{
lean_object* v___f_2462_; lean_object* v___x_2463_; 
v___f_2462_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2462_, 0, v_f_2459_);
v___x_2463_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_2458_, v___f_2462_, v_init_2460_, v_b_2461_);
return v___x_2463_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_forInUncurried(lean_object* v_00_u03b1_2464_, lean_object* v_00_u03b4_2465_, lean_object* v_m_2466_, lean_object* v_inst_2467_, lean_object* v_00_u03b2_2468_, lean_object* v_f_2469_, lean_object* v_init_2470_, lean_object* v_b_2471_){
_start:
{
lean_object* v___f_2472_; lean_object* v___x_2473_; 
v___f_2472_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_Const_forInUncurried___redArg___lam__0), 4, 1);
lean_closure_set(v___f_2472_, 0, v_f_2469_);
v___x_2473_ = l_Std_DHashMap_Raw_forIn___redArg(v_inst_2467_, v___f_2472_, v_init_2470_, v_b_2471_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___redArg(lean_object* v_f_2474_, lean_object* v_m_2475_){
_start:
{
lean_object* v_keyArray_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; uint8_t v___x_2479_; 
v_keyArray_2476_ = lean_ctor_get(v_m_2475_, 1);
v___x_2477_ = lean_unsigned_to_nat(0u);
v___x_2478_ = lean_array_get_size(v_keyArray_2476_);
v___x_2479_ = lean_nat_dec_lt(v___x_2477_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; 
lean_dec_ref(v_f_2474_);
v___x_2480_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2474_, v_m_2475_);
return v___x_2481_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___redArg___boxed(lean_object* v_f_2482_, lean_object* v_m_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Std_DHashMap_Raw_filterMap___redArg(v_f_2482_, v_m_2483_);
lean_dec_ref(v_m_2483_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap(lean_object* v_00_u03b1_2485_, lean_object* v_00_u03b2_2486_, lean_object* v_00_u03b3_2487_, lean_object* v_f_2488_, lean_object* v_m_2489_){
_start:
{
lean_object* v_keyArray_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; uint8_t v___x_2493_; 
v_keyArray_2490_ = lean_ctor_get(v_m_2489_, 1);
v___x_2491_ = lean_unsigned_to_nat(0u);
v___x_2492_ = lean_array_get_size(v_keyArray_2490_);
v___x_2493_ = lean_nat_dec_lt(v___x_2491_, v___x_2492_);
if (v___x_2493_ == 0)
{
lean_object* v___x_2494_; 
lean_dec_ref(v_f_2488_);
v___x_2494_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_2494_;
}
else
{
lean_object* v___x_2495_; 
v___x_2495_ = l_Std_DHashMap_Internal_Raw_u2080_filterMap___redArg(v_f_2488_, v_m_2489_);
return v___x_2495_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filterMap___boxed(lean_object* v_00_u03b1_2496_, lean_object* v_00_u03b2_2497_, lean_object* v_00_u03b3_2498_, lean_object* v_f_2499_, lean_object* v_m_2500_){
_start:
{
lean_object* v_res_2501_; 
v_res_2501_ = l_Std_DHashMap_Raw_filterMap(v_00_u03b1_2496_, v_00_u03b2_2497_, v_00_u03b3_2498_, v_f_2499_, v_m_2500_);
lean_dec_ref(v_m_2500_);
return v_res_2501_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___redArg(lean_object* v_f_2502_, lean_object* v_m_2503_){
_start:
{
lean_object* v_keyArray_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; 
v_keyArray_2504_ = lean_ctor_get(v_m_2503_, 1);
v___x_2505_ = lean_unsigned_to_nat(0u);
v___x_2506_ = lean_array_get_size(v_keyArray_2504_);
v___x_2507_ = lean_nat_dec_lt(v___x_2505_, v___x_2506_);
if (v___x_2507_ == 0)
{
lean_object* v___x_2508_; 
lean_dec(v_f_2502_);
v___x_2508_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_2508_;
}
else
{
lean_object* v___x_2509_; 
v___x_2509_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2502_, v_m_2503_);
return v___x_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___redArg___boxed(lean_object* v_f_2510_, lean_object* v_m_2511_){
_start:
{
lean_object* v_res_2512_; 
v_res_2512_ = l_Std_DHashMap_Raw_map___redArg(v_f_2510_, v_m_2511_);
lean_dec_ref(v_m_2511_);
return v_res_2512_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map(lean_object* v_00_u03b1_2513_, lean_object* v_00_u03b2_2514_, lean_object* v_00_u03b3_2515_, lean_object* v_f_2516_, lean_object* v_m_2517_){
_start:
{
lean_object* v_keyArray_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v_keyArray_2518_ = lean_ctor_get(v_m_2517_, 1);
v___x_2519_ = lean_unsigned_to_nat(0u);
v___x_2520_ = lean_array_get_size(v_keyArray_2518_);
v___x_2521_ = lean_nat_dec_lt(v___x_2519_, v___x_2520_);
if (v___x_2521_ == 0)
{
lean_object* v___x_2522_; 
lean_dec(v_f_2516_);
v___x_2522_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_2522_;
}
else
{
lean_object* v___x_2523_; 
v___x_2523_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_2516_, v_m_2517_);
return v___x_2523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_map___boxed(lean_object* v_00_u03b1_2524_, lean_object* v_00_u03b2_2525_, lean_object* v_00_u03b3_2526_, lean_object* v_f_2527_, lean_object* v_m_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_Std_DHashMap_Raw_map(v_00_u03b1_2524_, v_00_u03b2_2525_, v_00_u03b3_2526_, v_f_2527_, v_m_2528_);
lean_dec_ref(v_m_2528_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___redArg(lean_object* v_f_2530_, lean_object* v_m_2531_){
_start:
{
lean_object* v_keyArray_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; uint8_t v___x_2535_; 
v_keyArray_2532_ = lean_ctor_get(v_m_2531_, 1);
v___x_2533_ = lean_unsigned_to_nat(0u);
v___x_2534_ = lean_array_get_size(v_keyArray_2532_);
v___x_2535_ = lean_nat_dec_lt(v___x_2533_, v___x_2534_);
if (v___x_2535_ == 0)
{
lean_object* v___x_2536_; 
lean_dec_ref(v_f_2530_);
v___x_2536_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_2536_;
}
else
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2530_, v_m_2531_);
return v___x_2537_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___redArg___boxed(lean_object* v_f_2538_, lean_object* v_m_2539_){
_start:
{
lean_object* v_res_2540_; 
v_res_2540_ = l_Std_DHashMap_Raw_filter___redArg(v_f_2538_, v_m_2539_);
lean_dec_ref(v_m_2539_);
return v_res_2540_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter(lean_object* v_00_u03b1_2541_, lean_object* v_00_u03b2_2542_, lean_object* v_f_2543_, lean_object* v_m_2544_){
_start:
{
lean_object* v_keyArray_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___x_2548_; 
v_keyArray_2545_ = lean_ctor_get(v_m_2544_, 1);
v___x_2546_ = lean_unsigned_to_nat(0u);
v___x_2547_ = lean_array_get_size(v_keyArray_2545_);
v___x_2548_ = lean_nat_dec_lt(v___x_2546_, v___x_2547_);
if (v___x_2548_ == 0)
{
lean_object* v___x_2549_; 
lean_dec_ref(v_f_2543_);
v___x_2549_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
return v___x_2549_;
}
else
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v_f_2543_, v_m_2544_);
return v___x_2550_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_filter___boxed(lean_object* v_00_u03b1_2551_, lean_object* v_00_u03b2_2552_, lean_object* v_f_2553_, lean_object* v_m_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Std_DHashMap_Raw_filter(v_00_u03b1_2551_, v_00_u03b2_2552_, v_f_2553_, v_m_2554_);
lean_dec_ref(v_m_2554_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg___lam__0(lean_object* v_x1_2556_, lean_object* v_x2_2557_, lean_object* v_x3_2558_){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v_x2_2557_);
lean_ctor_set(v___x_2559_, 1, v_x3_2558_);
v___x_2560_ = lean_array_push(v_x1_2556_, v___x_2559_);
return v___x_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray___redArg(lean_object* v_m_2562_){
_start:
{
lean_object* v_size_2563_; lean_object* v___f_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; 
v_size_2563_ = lean_ctor_get(v_m_2562_, 0);
v___f_2564_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__0));
v___x_2565_ = lean_mk_empty_array_with_capacity(v_size_2563_);
v___x_2566_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2567_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2566_, v___f_2564_, v___x_2565_, v_m_2562_);
return v___x_2567_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toArray(lean_object* v_00_u03b1_2568_, lean_object* v_00_u03b2_2569_, lean_object* v_m_2570_){
_start:
{
lean_object* v_size_2571_; lean_object* v___f_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_size_2571_ = lean_ctor_get(v_m_2570_, 0);
v___f_2572_ = ((lean_object*)(l_Std_DHashMap_Raw_toArray___redArg___closed__0));
v___x_2573_ = lean_mk_empty_array_with_capacity(v_size_2571_);
v___x_2574_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2575_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2574_, v___f_2572_, v___x_2573_, v_m_2570_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg___lam__0(lean_object* v_x1_2576_, lean_object* v_x2_2577_, lean_object* v_x3_2578_){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_x2_2577_);
lean_ctor_set(v___x_2579_, 1, v_x3_2578_);
v___x_2580_ = lean_array_push(v_x1_2576_, v___x_2579_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray___redArg(lean_object* v_m_2582_){
_start:
{
lean_object* v_size_2583_; lean_object* v___f_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v_size_2583_ = lean_ctor_get(v_m_2582_, 0);
v___f_2584_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0));
v___x_2585_ = lean_mk_empty_array_with_capacity(v_size_2583_);
v___x_2586_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2587_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2586_, v___f_2584_, v___x_2585_, v_m_2582_);
return v___x_2587_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toArray(lean_object* v_00_u03b1_2588_, lean_object* v_00_u03b2_2589_, lean_object* v_m_2590_){
_start:
{
lean_object* v_size_2591_; lean_object* v___f_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v_size_2591_ = lean_ctor_get(v_m_2590_, 0);
v___f_2592_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toArray___redArg___closed__0));
v___x_2593_ = lean_mk_empty_array_with_capacity(v_size_2591_);
v___x_2594_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2595_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2594_, v___f_2592_, v___x_2593_, v_m_2590_);
return v___x_2595_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0(lean_object* v_x1_2596_, lean_object* v_x2_2597_, lean_object* v_x3_2598_){
_start:
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_array_push(v_x1_2596_, v_x2_2597_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg___lam__0___boxed(lean_object* v_x1_2600_, lean_object* v_x2_2601_, lean_object* v_x3_2602_){
_start:
{
lean_object* v_res_2603_; 
v_res_2603_ = l_Std_DHashMap_Raw_keysArray___redArg___lam__0(v_x1_2600_, v_x2_2601_, v_x3_2602_);
lean_dec(v_x3_2602_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray___redArg(lean_object* v_m_2605_){
_start:
{
lean_object* v_size_2606_; lean_object* v___f_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v_size_2606_ = lean_ctor_get(v_m_2605_, 0);
v___f_2607_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__0));
v___x_2608_ = lean_mk_empty_array_with_capacity(v_size_2606_);
v___x_2609_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2610_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2609_, v___f_2607_, v___x_2608_, v_m_2605_);
return v___x_2610_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysArray(lean_object* v_00_u03b1_2611_, lean_object* v_00_u03b2_2612_, lean_object* v_m_2613_){
_start:
{
lean_object* v_size_2614_; lean_object* v___f_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; 
v_size_2614_ = lean_ctor_get(v_m_2613_, 0);
v___f_2615_ = ((lean_object*)(l_Std_DHashMap_Raw_keysArray___redArg___closed__0));
v___x_2616_ = lean_mk_empty_array_with_capacity(v_size_2614_);
v___x_2617_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2618_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2617_, v___f_2615_, v___x_2616_, v_m_2613_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg___lam__0(lean_object* v_inst_2619_, lean_object* v_inst_2620_, lean_object* v_a_2621_, lean_object* v_b_2622_, lean_object* v_acc_2623_){
_start:
{
lean_object* v___y_2625_; lean_object* v_i_2626_; lean_object* v___y_2645_; lean_object* v_i_2646_; lean_object* v___y_2653_; lean_object* v___x_2664_; 
lean_inc(v_a_2621_);
lean_inc_ref(v_inst_2620_);
lean_inc_ref(v_inst_2619_);
v___x_2664_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2619_, v_inst_2620_, v_acc_2623_, v_a_2621_);
switch(lean_obj_tag(v___x_2664_))
{
case 0:
{
lean_object* v___x_2665_; 
lean_dec_ref_known(v___x_2664_, 3);
lean_dec(v_b_2622_);
lean_dec(v_a_2621_);
lean_dec_ref(v_inst_2620_);
lean_dec_ref(v_inst_2619_);
v___x_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2665_, 0, v_acc_2623_);
return v___x_2665_;
}
case 1:
{
lean_object* v_index_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2685_; 
v_index_2666_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2668_ = v___x_2664_;
v_isShared_2669_ = v_isSharedCheck_2685_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_index_2666_);
lean_dec(v___x_2664_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2685_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v_size_2670_; lean_object* v_keyArray_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_size_2670_ = lean_ctor_get(v_acc_2623_, 0);
v_keyArray_2671_ = lean_ctor_get(v_acc_2623_, 1);
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = lean_nat_add(v_size_2670_, v___x_2672_);
v___x_2674_ = lean_array_get_size(v_keyArray_2671_);
v___x_2675_ = lean_nat_dec_lt(v___x_2673_, v___x_2674_);
if (v___x_2675_ == 0)
{
lean_dec(v___x_2673_);
lean_del_object(v___x_2668_);
lean_dec(v_index_2666_);
goto v___jp_2632_;
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v___x_2676_ = lean_unsigned_to_nat(4u);
v___x_2677_ = lean_nat_mul(v___x_2673_, v___x_2676_);
v___x_2678_ = lean_unsigned_to_nat(3u);
v___x_2679_ = lean_nat_mul(v___x_2674_, v___x_2678_);
v___x_2680_ = lean_nat_dec_le(v___x_2677_, v___x_2679_);
lean_dec(v___x_2679_);
lean_dec(v___x_2677_);
if (v___x_2680_ == 0)
{
lean_dec(v___x_2673_);
lean_del_object(v___x_2668_);
lean_dec(v_index_2666_);
goto v___jp_2632_;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2683_; 
lean_dec_ref(v_inst_2620_);
lean_dec_ref(v_inst_2619_);
v___x_2681_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_2623_, v___x_2673_, v_index_2666_, v_a_2621_, v_b_2622_);
lean_dec(v_index_2666_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 0, v___x_2681_);
v___x_2683_ = v___x_2668_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
}
}
default: 
{
lean_object* v_size_2686_; lean_object* v_keyArray_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; uint8_t v___x_2691_; 
v_size_2686_ = lean_ctor_get(v_acc_2623_, 0);
v_keyArray_2687_ = lean_ctor_get(v_acc_2623_, 1);
v___x_2688_ = lean_unsigned_to_nat(1u);
v___x_2689_ = lean_nat_add(v_size_2686_, v___x_2688_);
v___x_2690_ = lean_array_get_size(v_keyArray_2687_);
v___x_2691_ = lean_nat_dec_lt(v___x_2689_, v___x_2690_);
if (v___x_2691_ == 0)
{
lean_object* v___x_2692_; 
lean_dec(v___x_2689_);
lean_inc_ref(v_inst_2620_);
lean_inc_ref(v_inst_2619_);
v___x_2692_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2619_, v_inst_2620_, v_acc_2623_);
v___y_2653_ = v___x_2692_;
goto v___jp_2652_;
}
else
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; uint8_t v___x_2697_; 
v___x_2693_ = lean_unsigned_to_nat(4u);
v___x_2694_ = lean_nat_mul(v___x_2689_, v___x_2693_);
lean_dec(v___x_2689_);
v___x_2695_ = lean_unsigned_to_nat(3u);
v___x_2696_ = lean_nat_mul(v___x_2690_, v___x_2695_);
v___x_2697_ = lean_nat_dec_le(v___x_2694_, v___x_2696_);
lean_dec(v___x_2696_);
lean_dec(v___x_2694_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
lean_inc_ref(v_inst_2620_);
lean_inc_ref(v_inst_2619_);
v___x_2698_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2619_, v_inst_2620_, v_acc_2623_);
v___y_2653_ = v___x_2698_;
goto v___jp_2652_;
}
else
{
v___y_2653_ = v_acc_2623_;
goto v___jp_2652_;
}
}
}
}
v___jp_2624_:
{
lean_object* v_size_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v_size_2627_ = lean_ctor_get(v___y_2625_, 0);
v___x_2628_ = lean_unsigned_to_nat(1u);
v___x_2629_ = lean_nat_add(v_size_2627_, v___x_2628_);
v___x_2630_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2625_, v___x_2629_, v_i_2626_, v_a_2621_, v_b_2622_);
lean_dec(v_i_2626_);
v___x_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
return v___x_2631_;
}
v___jp_2632_:
{
lean_object* v___x_2633_; lean_object* v___x_2634_; 
lean_inc_ref(v_inst_2620_);
lean_inc_ref(v_inst_2619_);
v___x_2633_ = l_Std_DHashMap_Internal_Raw_u2080_expand___redArg(v_inst_2619_, v_inst_2620_, v_acc_2623_);
lean_inc(v_a_2621_);
v___x_2634_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2619_, v_inst_2620_, v___x_2633_, v_a_2621_);
switch(lean_obj_tag(v___x_2634_))
{
case 0:
{
lean_object* v_index_2635_; lean_object* v_size_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; 
v_index_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_index_2635_);
lean_dec_ref_known(v___x_2634_, 3);
v_size_2636_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_size_2636_);
v___x_2637_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2633_, v_size_2636_, v_index_2635_, v_a_2621_, v_b_2622_);
lean_dec(v_index_2635_);
v___x_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2637_);
return v___x_2638_;
}
case 1:
{
lean_object* v_index_2639_; 
v_index_2639_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_index_2639_);
lean_dec_ref_known(v___x_2634_, 1);
v___y_2625_ = v___x_2633_;
v_i_2626_ = v_index_2639_;
goto v___jp_2624_;
}
default: 
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_unsigned_to_nat(0u);
v___x_2641_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2633_, v___x_2640_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_index_2642_; 
v_index_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_index_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v___y_2625_ = v___x_2633_;
v_i_2626_ = v_index_2642_;
goto v___jp_2624_;
}
else
{
lean_object* v___x_2643_; 
lean_dec(v_b_2622_);
lean_dec(v_a_2621_);
v___x_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2643_, 0, v___x_2633_);
return v___x_2643_;
}
}
}
}
v___jp_2644_:
{
lean_object* v_size_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v_size_2647_ = lean_ctor_get(v___y_2645_, 0);
v___x_2648_ = lean_unsigned_to_nat(1u);
v___x_2649_ = lean_nat_add(v_size_2647_, v___x_2648_);
v___x_2650_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2645_, v___x_2649_, v_i_2646_, v_a_2621_, v_b_2622_);
lean_dec(v_i_2646_);
v___x_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2651_, 0, v___x_2650_);
return v___x_2651_;
}
v___jp_2652_:
{
lean_object* v___x_2654_; 
lean_inc(v_a_2621_);
v___x_2654_ = l_Std_DHashMap_Internal_Raw_u2080_probe___redArg(v_inst_2619_, v_inst_2620_, v___y_2653_, v_a_2621_);
switch(lean_obj_tag(v___x_2654_))
{
case 0:
{
lean_object* v_index_2655_; lean_object* v_size_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
v_index_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_index_2655_);
lean_dec_ref_known(v___x_2654_, 3);
v_size_2656_ = lean_ctor_get(v___y_2653_, 0);
lean_inc(v_size_2656_);
v___x_2657_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2653_, v_size_2656_, v_index_2655_, v_a_2621_, v_b_2622_);
lean_dec(v_index_2655_);
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___x_2657_);
return v___x_2658_;
}
case 1:
{
lean_object* v_index_2659_; 
v_index_2659_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_index_2659_);
lean_dec_ref_known(v___x_2654_, 1);
v___y_2645_ = v___y_2653_;
v_i_2646_ = v_index_2659_;
goto v___jp_2644_;
}
default: 
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_unsigned_to_nat(0u);
v___x_2661_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2653_, v___x_2660_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_index_2662_; 
v_index_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_index_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v___y_2645_ = v___y_2653_;
v_i_2646_ = v_index_2662_;
goto v___jp_2644_;
}
else
{
lean_object* v___x_2663_; 
lean_dec(v_b_2622_);
lean_dec(v_a_2621_);
v___x_2663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2663_, 0, v___y_2653_);
return v___x_2663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union___redArg(lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_m_u2081_2703_, lean_object* v_m_u2082_2704_){
_start:
{
lean_object* v_size_2705_; lean_object* v_keyArray_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; 
v_size_2705_ = lean_ctor_get(v_m_u2081_2703_, 0);
v_keyArray_2706_ = lean_ctor_get(v_m_u2081_2703_, 1);
v___x_2707_ = lean_unsigned_to_nat(0u);
v___x_2708_ = lean_array_get_size(v_keyArray_2706_);
v___x_2709_ = lean_nat_dec_lt(v___x_2707_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_dec_ref(v_m_u2081_2703_);
lean_dec_ref(v_inst_2702_);
lean_dec_ref(v_inst_2701_);
return v_m_u2082_2704_;
}
else
{
lean_object* v_size_2710_; lean_object* v_keyArray_2711_; lean_object* v___x_2712_; uint8_t v___x_2713_; 
v_size_2710_ = lean_ctor_get(v_m_u2082_2704_, 0);
v_keyArray_2711_ = lean_ctor_get(v_m_u2082_2704_, 1);
v___x_2712_ = lean_array_get_size(v_keyArray_2711_);
v___x_2713_ = lean_nat_dec_lt(v___x_2707_, v___x_2712_);
if (v___x_2713_ == 0)
{
lean_dec_ref(v_m_u2082_2704_);
lean_dec_ref(v_inst_2702_);
lean_dec_ref(v_inst_2701_);
return v_m_u2081_2703_;
}
else
{
uint8_t v___x_2714_; 
v___x_2714_ = lean_nat_dec_le(v_size_2705_, v_size_2710_);
if (v___x_2714_ == 0)
{
lean_object* v___f_2715_; lean_object* v___x_2716_; 
v___f_2715_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2716_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2715_, v_inst_2701_, v_inst_2702_, v_m_u2081_2703_, v_m_u2082_2704_);
return v___x_2716_;
}
else
{
lean_object* v___f_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___f_2717_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2717_, 0, v_inst_2701_);
lean_closure_set(v___f_2717_, 1, v_inst_2702_);
v___x_2718_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2719_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2718_, v___f_2717_, v_m_u2082_2704_, v_m_u2081_2703_);
return v___x_2719_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_union(lean_object* v_00_u03b1_2720_, lean_object* v_00_u03b2_2721_, lean_object* v_inst_2722_, lean_object* v_inst_2723_, lean_object* v_m_u2081_2724_, lean_object* v_m_u2082_2725_){
_start:
{
lean_object* v_size_2726_; lean_object* v_keyArray_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_size_2726_ = lean_ctor_get(v_m_u2081_2724_, 0);
v_keyArray_2727_ = lean_ctor_get(v_m_u2081_2724_, 1);
v___x_2728_ = lean_unsigned_to_nat(0u);
v___x_2729_ = lean_array_get_size(v_keyArray_2727_);
v___x_2730_ = lean_nat_dec_lt(v___x_2728_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_dec_ref(v_m_u2081_2724_);
lean_dec_ref(v_inst_2723_);
lean_dec_ref(v_inst_2722_);
return v_m_u2082_2725_;
}
else
{
lean_object* v_size_2731_; lean_object* v_keyArray_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v_size_2731_ = lean_ctor_get(v_m_u2082_2725_, 0);
v_keyArray_2732_ = lean_ctor_get(v_m_u2082_2725_, 1);
v___x_2733_ = lean_array_get_size(v_keyArray_2732_);
v___x_2734_ = lean_nat_dec_lt(v___x_2728_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_dec_ref(v_m_u2082_2725_);
lean_dec_ref(v_inst_2723_);
lean_dec_ref(v_inst_2722_);
return v_m_u2081_2724_;
}
else
{
uint8_t v___x_2735_; 
v___x_2735_ = lean_nat_dec_le(v_size_2726_, v_size_2731_);
if (v___x_2735_ == 0)
{
lean_object* v___f_2736_; lean_object* v___x_2737_; 
v___f_2736_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2737_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_2736_, v_inst_2722_, v_inst_2723_, v_m_u2081_2724_, v_m_u2082_2725_);
return v___x_2737_;
}
else
{
lean_object* v___f_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v___f_2738_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union___redArg___lam__0), 5, 2);
lean_closure_set(v___f_2738_, 0, v_inst_2722_);
lean_closure_set(v___f_2738_, 1, v_inst_2723_);
v___x_2739_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2740_ = l_Std_DHashMap_Raw_forIn___redArg(v___x_2739_, v___f_2738_, v_m_u2082_2725_, v_m_u2081_2724_);
return v___x_2740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable___redArg(lean_object* v_inst_2741_, lean_object* v_inst_2742_){
_start:
{
lean_object* v___x_2743_; 
v___x_2743_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union), 6, 4);
lean_closure_set(v___x_2743_, 0, lean_box(0));
lean_closure_set(v___x_2743_, 1, lean_box(0));
lean_closure_set(v___x_2743_, 2, v_inst_2741_);
lean_closure_set(v___x_2743_, 3, v_inst_2742_);
return v___x_2743_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instUnionOfBEqOfHashable(lean_object* v_00_u03b1_2744_, lean_object* v_00_u03b2_2745_, lean_object* v_inst_2746_, lean_object* v_inst_2747_){
_start:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_union), 6, 4);
lean_closure_set(v___x_2748_, 0, lean_box(0));
lean_closure_set(v___x_2748_, 1, lean_box(0));
lean_closure_set(v___x_2748_, 2, v_inst_2746_);
lean_closure_set(v___x_2748_, 3, v_inst_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter___redArg(lean_object* v_inst_2749_, lean_object* v_inst_2750_, lean_object* v_m_u2081_2751_, lean_object* v_m_u2082_2752_){
_start:
{
lean_object* v_keyArray_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v_keyArray_2753_ = lean_ctor_get(v_m_u2081_2751_, 1);
v___x_2754_ = lean_unsigned_to_nat(0u);
v___x_2755_ = lean_array_get_size(v_keyArray_2753_);
v___x_2756_ = lean_nat_dec_lt(v___x_2754_, v___x_2755_);
if (v___x_2756_ == 0)
{
lean_dec_ref(v_m_u2081_2751_);
lean_dec_ref(v_inst_2750_);
lean_dec_ref(v_inst_2749_);
return v_m_u2082_2752_;
}
else
{
lean_object* v_keyArray_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v_keyArray_2757_ = lean_ctor_get(v_m_u2082_2752_, 1);
v___x_2758_ = lean_array_get_size(v_keyArray_2757_);
v___x_2759_ = lean_nat_dec_lt(v___x_2754_, v___x_2758_);
if (v___x_2759_ == 0)
{
lean_dec_ref(v_m_u2082_2752_);
lean_dec_ref(v_inst_2750_);
lean_dec_ref(v_inst_2749_);
return v_m_u2081_2751_;
}
else
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2749_, v_inst_2750_, v_m_u2081_2751_, v_m_u2082_2752_);
return v___x_2760_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_inter(lean_object* v_00_u03b1_2761_, lean_object* v_00_u03b2_2762_, lean_object* v_inst_2763_, lean_object* v_inst_2764_, lean_object* v_m_u2081_2765_, lean_object* v_m_u2082_2766_){
_start:
{
lean_object* v_keyArray_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___x_2770_; 
v_keyArray_2767_ = lean_ctor_get(v_m_u2081_2765_, 1);
v___x_2768_ = lean_unsigned_to_nat(0u);
v___x_2769_ = lean_array_get_size(v_keyArray_2767_);
v___x_2770_ = lean_nat_dec_lt(v___x_2768_, v___x_2769_);
if (v___x_2770_ == 0)
{
lean_dec_ref(v_m_u2081_2765_);
lean_dec_ref(v_inst_2764_);
lean_dec_ref(v_inst_2763_);
return v_m_u2082_2766_;
}
else
{
lean_object* v_keyArray_2771_; lean_object* v___x_2772_; uint8_t v___x_2773_; 
v_keyArray_2771_ = lean_ctor_get(v_m_u2082_2766_, 1);
v___x_2772_ = lean_array_get_size(v_keyArray_2771_);
v___x_2773_ = lean_nat_dec_lt(v___x_2768_, v___x_2772_);
if (v___x_2773_ == 0)
{
lean_dec_ref(v_m_u2082_2766_);
lean_dec_ref(v_inst_2764_);
lean_dec_ref(v_inst_2763_);
return v_m_u2081_2765_;
}
else
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Std_DHashMap_Internal_Raw_u2080_inter___redArg(v_inst_2763_, v_inst_2764_, v_m_u2081_2765_, v_m_u2082_2766_);
return v___x_2774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable___redArg(lean_object* v_inst_2775_, lean_object* v_inst_2776_){
_start:
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2777_, 0, lean_box(0));
lean_closure_set(v___x_2777_, 1, lean_box(0));
lean_closure_set(v___x_2777_, 2, v_inst_2775_);
lean_closure_set(v___x_2777_, 3, v_inst_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instInterOfBEqOfHashable(lean_object* v_00_u03b1_2778_, lean_object* v_00_u03b2_2779_, lean_object* v_inst_2780_, lean_object* v_inst_2781_){
_start:
{
lean_object* v___x_2782_; 
v___x_2782_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_inter), 6, 4);
lean_closure_set(v___x_2782_, 0, lean_box(0));
lean_closure_set(v___x_2782_, 1, lean_box(0));
lean_closure_set(v___x_2782_, 2, v_inst_2780_);
lean_closure_set(v___x_2782_, 3, v_inst_2781_);
return v___x_2782_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq___redArg(lean_object* v_inst_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_m_u2081_2786_, lean_object* v_m_u2082_2787_){
_start:
{
lean_object* v_keyArray_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v_keyArray_2788_ = lean_ctor_get(v_m_u2081_2786_, 1);
v___x_2789_ = lean_unsigned_to_nat(0u);
v___x_2790_ = lean_array_get_size(v_keyArray_2788_);
v___x_2791_ = lean_nat_dec_lt(v___x_2789_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_dec_ref(v_m_u2082_2787_);
lean_dec_ref(v_m_u2081_2786_);
lean_dec_ref(v_inst_2785_);
lean_dec_ref(v_inst_2784_);
lean_dec_ref(v_inst_2783_);
return v___x_2791_;
}
else
{
lean_object* v_keyArray_2792_; lean_object* v___x_2793_; uint8_t v___x_2794_; 
v_keyArray_2792_ = lean_ctor_get(v_m_u2082_2787_, 1);
v___x_2793_ = lean_array_get_size(v_keyArray_2792_);
v___x_2794_ = lean_nat_dec_lt(v___x_2789_, v___x_2793_);
if (v___x_2794_ == 0)
{
lean_dec_ref(v_m_u2082_2787_);
lean_dec_ref(v_m_u2081_2786_);
lean_dec_ref(v_inst_2785_);
lean_dec_ref(v_inst_2784_);
lean_dec_ref(v_inst_2783_);
return v___x_2794_;
}
else
{
uint8_t v___x_2795_; 
v___x_2795_ = l_Std_DHashMap_Internal_Raw_u2080_beq___redArg(v_inst_2783_, v_inst_2784_, v_inst_2785_, v_m_u2081_2786_, v_m_u2082_2787_);
return v___x_2795_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___redArg___boxed(lean_object* v_inst_2796_, lean_object* v_inst_2797_, lean_object* v_inst_2798_, lean_object* v_m_u2081_2799_, lean_object* v_m_u2082_2800_){
_start:
{
uint8_t v_res_2801_; lean_object* v_r_2802_; 
v_res_2801_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2796_, v_inst_2797_, v_inst_2798_, v_m_u2081_2799_, v_m_u2082_2800_);
v_r_2802_ = lean_box(v_res_2801_);
return v_r_2802_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_beq(lean_object* v_00_u03b1_2803_, lean_object* v_00_u03b2_2804_, lean_object* v_inst_2805_, lean_object* v_inst_2806_, lean_object* v_inst_2807_, lean_object* v_inst_2808_, lean_object* v_m_u2081_2809_, lean_object* v_m_u2082_2810_){
_start:
{
uint8_t v___x_2811_; 
v___x_2811_ = l_Std_DHashMap_Raw_beq___redArg(v_inst_2805_, v_inst_2806_, v_inst_2808_, v_m_u2081_2809_, v_m_u2082_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_beq___boxed(lean_object* v_00_u03b1_2812_, lean_object* v_00_u03b2_2813_, lean_object* v_inst_2814_, lean_object* v_inst_2815_, lean_object* v_inst_2816_, lean_object* v_inst_2817_, lean_object* v_m_u2081_2818_, lean_object* v_m_u2082_2819_){
_start:
{
uint8_t v_res_2820_; lean_object* v_r_2821_; 
v_res_2820_ = l_Std_DHashMap_Raw_beq(v_00_u03b1_2812_, v_00_u03b2_2813_, v_inst_2814_, v_inst_2815_, v_inst_2816_, v_inst_2817_, v_m_u2081_2818_, v_m_u2082_2819_);
v_r_2821_ = lean_box(v_res_2820_);
return v_r_2821_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq___redArg(lean_object* v_inst_2822_, lean_object* v_inst_2823_, lean_object* v_inst_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2825_, 0, lean_box(0));
lean_closure_set(v___x_2825_, 1, lean_box(0));
lean_closure_set(v___x_2825_, 2, v_inst_2822_);
lean_closure_set(v___x_2825_, 3, v_inst_2823_);
lean_closure_set(v___x_2825_, 4, lean_box(0));
lean_closure_set(v___x_2825_, 5, v_inst_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instBEqOfHashableOfLawfulBEq(lean_object* v_00_u03b1_2826_, lean_object* v_00_u03b2_2827_, lean_object* v_inst_2828_, lean_object* v_inst_2829_, lean_object* v_inst_2830_, lean_object* v_inst_2831_){
_start:
{
lean_object* v___x_2832_; 
v___x_2832_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_beq___boxed), 8, 6);
lean_closure_set(v___x_2832_, 0, lean_box(0));
lean_closure_set(v___x_2832_, 1, lean_box(0));
lean_closure_set(v___x_2832_, 2, v_inst_2828_);
lean_closure_set(v___x_2832_, 3, v_inst_2829_);
lean_closure_set(v___x_2832_, 4, lean_box(0));
lean_closure_set(v___x_2832_, 5, v_inst_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq___redArg(lean_object* v_inst_2833_, lean_object* v_inst_2834_, lean_object* v_inst_2835_, lean_object* v_m_u2081_2836_, lean_object* v_m_u2082_2837_){
_start:
{
lean_object* v_keyArray_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; uint8_t v___x_2841_; 
v_keyArray_2838_ = lean_ctor_get(v_m_u2081_2836_, 1);
v___x_2839_ = lean_unsigned_to_nat(0u);
v___x_2840_ = lean_array_get_size(v_keyArray_2838_);
v___x_2841_ = lean_nat_dec_lt(v___x_2839_, v___x_2840_);
if (v___x_2841_ == 0)
{
lean_dec_ref(v_m_u2082_2837_);
lean_dec_ref(v_m_u2081_2836_);
lean_dec_ref(v_inst_2835_);
lean_dec_ref(v_inst_2834_);
lean_dec_ref(v_inst_2833_);
return v___x_2841_;
}
else
{
lean_object* v_keyArray_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; 
v_keyArray_2842_ = lean_ctor_get(v_m_u2082_2837_, 1);
v___x_2843_ = lean_array_get_size(v_keyArray_2842_);
v___x_2844_ = lean_nat_dec_lt(v___x_2839_, v___x_2843_);
if (v___x_2844_ == 0)
{
lean_dec_ref(v_m_u2082_2837_);
lean_dec_ref(v_m_u2081_2836_);
lean_dec_ref(v_inst_2835_);
lean_dec_ref(v_inst_2834_);
lean_dec_ref(v_inst_2833_);
return v___x_2844_;
}
else
{
uint8_t v___x_2845_; 
v___x_2845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_beq___redArg(v_inst_2833_, v_inst_2834_, v_inst_2835_, v_m_u2081_2836_, v_m_u2082_2837_);
return v___x_2845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___redArg___boxed(lean_object* v_inst_2846_, lean_object* v_inst_2847_, lean_object* v_inst_2848_, lean_object* v_m_u2081_2849_, lean_object* v_m_u2082_2850_){
_start:
{
uint8_t v_res_2851_; lean_object* v_r_2852_; 
v_res_2851_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2846_, v_inst_2847_, v_inst_2848_, v_m_u2081_2849_, v_m_u2082_2850_);
v_r_2852_ = lean_box(v_res_2851_);
return v_r_2852_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_Const_beq(lean_object* v_00_u03b1_2853_, lean_object* v_00_u03b2_2854_, lean_object* v_inst_2855_, lean_object* v_inst_2856_, lean_object* v_inst_2857_, lean_object* v_m_u2081_2858_, lean_object* v_m_u2082_2859_){
_start:
{
uint8_t v___x_2860_; 
v___x_2860_ = l_Std_DHashMap_Raw_Const_beq___redArg(v_inst_2855_, v_inst_2856_, v_inst_2857_, v_m_u2081_2858_, v_m_u2082_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_beq___boxed(lean_object* v_00_u03b1_2861_, lean_object* v_00_u03b2_2862_, lean_object* v_inst_2863_, lean_object* v_inst_2864_, lean_object* v_inst_2865_, lean_object* v_m_u2081_2866_, lean_object* v_m_u2082_2867_){
_start:
{
uint8_t v_res_2868_; lean_object* v_r_2869_; 
v_res_2868_ = l_Std_DHashMap_Raw_Const_beq(v_00_u03b1_2861_, v_00_u03b2_2862_, v_inst_2863_, v_inst_2864_, v_inst_2865_, v_m_u2081_2866_, v_m_u2082_2867_);
v_r_2869_ = lean_box(v_res_2868_);
return v_r_2869_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Raw_diff___redArg___lam__0(lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_m_u2082_2872_, uint8_t v___x_2873_, lean_object* v_k_2874_, lean_object* v_x_2875_){
_start:
{
uint8_t v___x_2876_; 
v___x_2876_ = l_Std_DHashMap_Internal_Raw_u2080_contains___redArg(v_inst_2870_, v_inst_2871_, v_m_u2082_2872_, v_k_2874_);
if (v___x_2876_ == 0)
{
return v___x_2873_;
}
else
{
uint8_t v___x_2877_; 
v___x_2877_ = 0;
return v___x_2877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed(lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_m_u2082_2880_, lean_object* v___x_2881_, lean_object* v_k_2882_, lean_object* v_x_2883_){
_start:
{
uint8_t v___x_92__boxed_2884_; uint8_t v_res_2885_; lean_object* v_r_2886_; 
v___x_92__boxed_2884_ = lean_unbox(v___x_2881_);
v_res_2885_ = l_Std_DHashMap_Raw_diff___redArg___lam__0(v_inst_2878_, v_inst_2879_, v_m_u2082_2880_, v___x_92__boxed_2884_, v_k_2882_, v_x_2883_);
lean_dec(v_x_2883_);
lean_dec_ref(v_m_u2082_2880_);
v_r_2886_ = lean_box(v_res_2885_);
return v_r_2886_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff___redArg(lean_object* v_inst_2887_, lean_object* v_inst_2888_, lean_object* v_m_u2081_2889_, lean_object* v_m_u2082_2890_){
_start:
{
lean_object* v_size_2891_; lean_object* v_keyArray_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; uint8_t v___x_2895_; 
v_size_2891_ = lean_ctor_get(v_m_u2081_2889_, 0);
v_keyArray_2892_ = lean_ctor_get(v_m_u2081_2889_, 1);
v___x_2893_ = lean_unsigned_to_nat(0u);
v___x_2894_ = lean_array_get_size(v_keyArray_2892_);
v___x_2895_ = lean_nat_dec_lt(v___x_2893_, v___x_2894_);
if (v___x_2895_ == 0)
{
lean_dec_ref(v_m_u2081_2889_);
lean_dec_ref(v_inst_2888_);
lean_dec_ref(v_inst_2887_);
return v_m_u2082_2890_;
}
else
{
lean_object* v_size_2896_; lean_object* v_keyArray_2897_; lean_object* v___x_2898_; uint8_t v___x_2899_; 
v_size_2896_ = lean_ctor_get(v_m_u2082_2890_, 0);
v_keyArray_2897_ = lean_ctor_get(v_m_u2082_2890_, 1);
v___x_2898_ = lean_array_get_size(v_keyArray_2897_);
v___x_2899_ = lean_nat_dec_lt(v___x_2893_, v___x_2898_);
if (v___x_2899_ == 0)
{
lean_dec_ref(v_m_u2082_2890_);
lean_dec_ref(v_inst_2888_);
lean_dec_ref(v_inst_2887_);
return v_m_u2081_2889_;
}
else
{
uint8_t v___x_2900_; 
v___x_2900_ = lean_nat_dec_le(v_size_2891_, v_size_2896_);
if (v___x_2900_ == 0)
{
lean_object* v___f_2901_; lean_object* v___x_2902_; 
v___f_2901_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2902_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2901_, v_inst_2887_, v_inst_2888_, v_m_u2081_2889_, v_m_u2082_2890_);
return v___x_2902_;
}
else
{
lean_object* v___x_2903_; lean_object* v___f_2904_; lean_object* v___x_2905_; 
v___x_2903_ = lean_box(v___x_2900_);
v___f_2904_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2904_, 0, v_inst_2887_);
lean_closure_set(v___f_2904_, 1, v_inst_2888_);
lean_closure_set(v___f_2904_, 2, v_m_u2082_2890_);
lean_closure_set(v___f_2904_, 3, v___x_2903_);
v___x_2905_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2904_, v_m_u2081_2889_);
lean_dec_ref(v_m_u2081_2889_);
return v___x_2905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_diff(lean_object* v_00_u03b1_2906_, lean_object* v_00_u03b2_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_m_u2081_2910_, lean_object* v_m_u2082_2911_){
_start:
{
lean_object* v_size_2912_; lean_object* v_keyArray_2913_; lean_object* v___x_2914_; lean_object* v___x_2915_; uint8_t v___x_2916_; 
v_size_2912_ = lean_ctor_get(v_m_u2081_2910_, 0);
v_keyArray_2913_ = lean_ctor_get(v_m_u2081_2910_, 1);
v___x_2914_ = lean_unsigned_to_nat(0u);
v___x_2915_ = lean_array_get_size(v_keyArray_2913_);
v___x_2916_ = lean_nat_dec_lt(v___x_2914_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_dec_ref(v_m_u2081_2910_);
lean_dec_ref(v_inst_2909_);
lean_dec_ref(v_inst_2908_);
return v_m_u2082_2911_;
}
else
{
lean_object* v_size_2917_; lean_object* v_keyArray_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v_size_2917_ = lean_ctor_get(v_m_u2082_2911_, 0);
v_keyArray_2918_ = lean_ctor_get(v_m_u2082_2911_, 1);
v___x_2919_ = lean_array_get_size(v_keyArray_2918_);
v___x_2920_ = lean_nat_dec_lt(v___x_2914_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_dec_ref(v_m_u2082_2911_);
lean_dec_ref(v_inst_2909_);
lean_dec_ref(v_inst_2908_);
return v_m_u2081_2910_;
}
else
{
uint8_t v___x_2921_; 
v___x_2921_ = lean_nat_dec_le(v_size_2912_, v_size_2917_);
if (v___x_2921_ == 0)
{
lean_object* v___f_2922_; lean_object* v___x_2923_; 
v___f_2922_ = ((lean_object*)(l_Std_DHashMap_Raw_union___redArg___closed__0));
v___x_2923_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v___f_2922_, v_inst_2908_, v_inst_2909_, v_m_u2081_2910_, v_m_u2082_2911_);
return v___x_2923_;
}
else
{
lean_object* v___x_2924_; lean_object* v___f_2925_; lean_object* v___x_2926_; 
v___x_2924_ = lean_box(v___x_2921_);
v___f_2925_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2925_, 0, v_inst_2908_);
lean_closure_set(v___f_2925_, 1, v_inst_2909_);
lean_closure_set(v___f_2925_, 2, v_m_u2082_2911_);
lean_closure_set(v___f_2925_, 3, v___x_2924_);
v___x_2926_ = l_Std_DHashMap_Internal_Raw_u2080_filter___redArg(v___f_2925_, v_m_u2081_2910_);
lean_dec_ref(v_m_u2081_2910_);
return v___x_2926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable___redArg(lean_object* v_inst_2927_, lean_object* v_inst_2928_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2929_, 0, lean_box(0));
lean_closure_set(v___x_2929_, 1, lean_box(0));
lean_closure_set(v___x_2929_, 2, v_inst_2927_);
lean_closure_set(v___x_2929_, 3, v_inst_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instSDiffOfBEqOfHashable(lean_object* v_00_u03b1_2930_, lean_object* v_00_u03b2_2931_, lean_object* v_inst_2932_, lean_object* v_inst_2933_){
_start:
{
lean_object* v___x_2934_; 
v___x_2934_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_diff), 6, 4);
lean_closure_set(v___x_2934_, 0, lean_box(0));
lean_closure_set(v___x_2934_, 1, lean_box(0));
lean_closure_set(v___x_2934_, 2, v_inst_2932_);
lean_closure_set(v___x_2934_, 3, v_inst_2933_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0(lean_object* v_x1_2935_, lean_object* v_x2_2936_, lean_object* v_x3_2937_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2938_, 0, v_x3_2937_);
lean_ctor_set(v___x_2938_, 1, v_x1_2935_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___lam__0___boxed(lean_object* v_x1_2939_, lean_object* v_x2_2940_, lean_object* v_x3_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Std_DHashMap_Raw_values___redArg___lam__0(v_x1_2939_, v_x2_2940_, v_x3_2941_);
lean_dec(v_x2_2940_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg(lean_object* v_m_2944_){
_start:
{
lean_object* v___f_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___f_2945_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__0));
v___x_2946_ = lean_box(0);
v___x_2947_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2948_ = lean_unsigned_to_nat(0u);
v___x_2949_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2947_, v___f_2945_, v_m_2944_, v___x_2946_, v___x_2948_);
return v___x_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___redArg___boxed(lean_object* v_m_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Std_DHashMap_Raw_values___redArg(v_m_2950_);
lean_dec_ref(v_m_2950_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values(lean_object* v_00_u03b1_2952_, lean_object* v_00_u03b2_2953_, lean_object* v_m_2954_){
_start:
{
lean_object* v___f_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v___f_2955_ = ((lean_object*)(l_Std_DHashMap_Raw_values___redArg___closed__0));
v___x_2956_ = lean_box(0);
v___x_2957_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2958_ = lean_unsigned_to_nat(0u);
v___x_2959_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_2957_, v___f_2955_, v_m_2954_, v___x_2956_, v___x_2958_);
return v___x_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_values___boxed(lean_object* v_00_u03b1_2960_, lean_object* v_00_u03b2_2961_, lean_object* v_m_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Std_DHashMap_Raw_values(v_00_u03b1_2960_, v_00_u03b2_2961_, v_m_2962_);
lean_dec_ref(v_m_2962_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(lean_object* v_x1_2964_, lean_object* v_x2_2965_, lean_object* v_x3_2966_){
_start:
{
lean_object* v___x_2967_; 
v___x_2967_ = lean_array_push(v_x1_2964_, v_x3_2966_);
return v___x_2967_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg___lam__0___boxed(lean_object* v_x1_2968_, lean_object* v_x2_2969_, lean_object* v_x3_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l_Std_DHashMap_Raw_valuesArray___redArg___lam__0(v_x1_2968_, v_x2_2969_, v_x3_2970_);
lean_dec(v_x2_2969_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray___redArg(lean_object* v_m_2973_){
_start:
{
lean_object* v_size_2974_; lean_object* v___f_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v_size_2974_ = lean_ctor_get(v_m_2973_, 0);
v___f_2975_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__0));
v___x_2976_ = lean_mk_empty_array_with_capacity(v_size_2974_);
v___x_2977_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2978_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2977_, v___f_2975_, v___x_2976_, v_m_2973_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesArray(lean_object* v_00_u03b1_2979_, lean_object* v_00_u03b2_2980_, lean_object* v_m_2981_){
_start:
{
lean_object* v_size_2982_; lean_object* v___f_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; 
v_size_2982_ = lean_ctor_get(v_m_2981_, 0);
v___f_2983_ = ((lean_object*)(l_Std_DHashMap_Raw_valuesArray___redArg___closed__0));
v___x_2984_ = lean_mk_empty_array_with_capacity(v_size_2982_);
v___x_2985_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_2986_ = l_Std_DHashMap_Raw_foldM___redArg(v___x_2985_, v___f_2983_, v___x_2984_, v_m_2981_);
return v___x_2986_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany___redArg(lean_object* v_inst_2987_, lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_m_2990_, lean_object* v_l_2991_){
_start:
{
lean_object* v_keyArray_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v_keyArray_2992_ = lean_ctor_get(v_m_2990_, 1);
v___x_2993_ = lean_unsigned_to_nat(0u);
v___x_2994_ = lean_array_get_size(v_keyArray_2992_);
v___x_2995_ = lean_nat_dec_lt(v___x_2993_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_dec(v_l_2991_);
lean_dec(v_inst_2989_);
lean_dec_ref(v_inst_2988_);
lean_dec_ref(v_inst_2987_);
return v_m_2990_;
}
else
{
lean_object* v___x_2996_; 
v___x_2996_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_2989_, v_inst_2987_, v_inst_2988_, v_m_2990_, v_l_2991_);
return v___x_2996_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_insertMany(lean_object* v_00_u03b1_2997_, lean_object* v_00_u03b2_2998_, lean_object* v_inst_2999_, lean_object* v_inst_3000_, lean_object* v_00_u03c1_3001_, lean_object* v_inst_3002_, lean_object* v_m_3003_, lean_object* v_l_3004_){
_start:
{
lean_object* v_keyArray_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; uint8_t v___x_3008_; 
v_keyArray_3005_ = lean_ctor_get(v_m_3003_, 1);
v___x_3006_ = lean_unsigned_to_nat(0u);
v___x_3007_ = lean_array_get_size(v_keyArray_3005_);
v___x_3008_ = lean_nat_dec_lt(v___x_3006_, v___x_3007_);
if (v___x_3008_ == 0)
{
lean_dec(v_l_3004_);
lean_dec(v_inst_3002_);
lean_dec_ref(v_inst_3000_);
lean_dec_ref(v_inst_2999_);
return v_m_3003_;
}
else
{
lean_object* v___x_3009_; 
v___x_3009_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v_inst_3002_, v_inst_2999_, v_inst_3000_, v_m_3003_, v_l_3004_);
return v___x_3009_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries___redArg(lean_object* v_inst_3010_, lean_object* v_inst_3011_, lean_object* v_inst_3012_, lean_object* v_m_3013_, lean_object* v_l_3014_){
_start:
{
lean_object* v_keyArray_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; uint8_t v___x_3018_; 
v_keyArray_3015_ = lean_ctor_get(v_m_3013_, 1);
v___x_3016_ = lean_unsigned_to_nat(0u);
v___x_3017_ = lean_array_get_size(v_keyArray_3015_);
v___x_3018_ = lean_nat_dec_lt(v___x_3016_, v___x_3017_);
if (v___x_3018_ == 0)
{
lean_dec(v_l_3014_);
lean_dec(v_inst_3012_);
lean_dec_ref(v_inst_3011_);
lean_dec_ref(v_inst_3010_);
return v_m_3013_;
}
else
{
lean_object* v___x_3019_; 
v___x_3019_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_3012_, v_inst_3010_, v_inst_3011_, v_m_3013_, v_l_3014_);
return v___x_3019_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_eraseManyEntries(lean_object* v_00_u03b1_3020_, lean_object* v_00_u03b2_3021_, lean_object* v_inst_3022_, lean_object* v_inst_3023_, lean_object* v_00_u03c1_3024_, lean_object* v_inst_3025_, lean_object* v_m_3026_, lean_object* v_l_3027_){
_start:
{
lean_object* v_keyArray_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v_keyArray_3028_ = lean_ctor_get(v_m_3026_, 1);
v___x_3029_ = lean_unsigned_to_nat(0u);
v___x_3030_ = lean_array_get_size(v_keyArray_3028_);
v___x_3031_ = lean_nat_dec_lt(v___x_3029_, v___x_3030_);
if (v___x_3031_ == 0)
{
lean_dec(v_l_3027_);
lean_dec(v_inst_3025_);
lean_dec_ref(v_inst_3023_);
lean_dec_ref(v_inst_3022_);
return v_m_3026_;
}
else
{
lean_object* v___x_3032_; 
v___x_3032_ = l_Std_DHashMap_Internal_Raw_u2080_eraseManyEntries___redArg(v_inst_3025_, v_inst_3022_, v_inst_3023_, v_m_3026_, v_l_3027_);
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany___redArg(lean_object* v_inst_3033_, lean_object* v_inst_3034_, lean_object* v_inst_3035_, lean_object* v_m_3036_, lean_object* v_l_3037_){
_start:
{
lean_object* v_keyArray_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v_keyArray_3038_ = lean_ctor_get(v_m_3036_, 1);
v___x_3039_ = lean_unsigned_to_nat(0u);
v___x_3040_ = lean_array_get_size(v_keyArray_3038_);
v___x_3041_ = lean_nat_dec_lt(v___x_3039_, v___x_3040_);
if (v___x_3041_ == 0)
{
lean_dec(v_l_3037_);
lean_dec(v_inst_3035_);
lean_dec_ref(v_inst_3034_);
lean_dec_ref(v_inst_3033_);
return v_m_3036_;
}
else
{
lean_object* v___x_3042_; 
v___x_3042_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_3035_, v_inst_3033_, v_inst_3034_, v_m_3036_, v_l_3037_);
return v___x_3042_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertMany(lean_object* v_00_u03b1_3043_, lean_object* v_00_u03b2_3044_, lean_object* v_inst_3045_, lean_object* v_inst_3046_, lean_object* v_00_u03c1_3047_, lean_object* v_inst_3048_, lean_object* v_m_3049_, lean_object* v_l_3050_){
_start:
{
lean_object* v_keyArray_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; uint8_t v___x_3054_; 
v_keyArray_3051_ = lean_ctor_get(v_m_3049_, 1);
v___x_3052_ = lean_unsigned_to_nat(0u);
v___x_3053_ = lean_array_get_size(v_keyArray_3051_);
v___x_3054_ = lean_nat_dec_lt(v___x_3052_, v___x_3053_);
if (v___x_3054_ == 0)
{
lean_dec(v_l_3050_);
lean_dec(v_inst_3048_);
lean_dec_ref(v_inst_3046_);
lean_dec_ref(v_inst_3045_);
return v_m_3049_;
}
else
{
lean_object* v___x_3055_; 
v___x_3055_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v_inst_3048_, v_inst_3045_, v_inst_3046_, v_m_3049_, v_l_3050_);
return v___x_3055_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit___redArg(lean_object* v_inst_3056_, lean_object* v_inst_3057_, lean_object* v_inst_3058_, lean_object* v_m_3059_, lean_object* v_l_3060_){
_start:
{
lean_object* v_keyArray_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; uint8_t v___x_3064_; 
v_keyArray_3061_ = lean_ctor_get(v_m_3059_, 1);
v___x_3062_ = lean_unsigned_to_nat(0u);
v___x_3063_ = lean_array_get_size(v_keyArray_3061_);
v___x_3064_ = lean_nat_dec_lt(v___x_3062_, v___x_3063_);
if (v___x_3064_ == 0)
{
lean_dec(v_l_3060_);
lean_dec(v_inst_3058_);
lean_dec_ref(v_inst_3057_);
lean_dec_ref(v_inst_3056_);
return v_m_3059_;
}
else
{
lean_object* v___x_3065_; 
v___x_3065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_3058_, v_inst_3056_, v_inst_3057_, v_m_3059_, v_l_3060_);
return v___x_3065_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_insertManyIfNewUnit(lean_object* v_00_u03b1_3066_, lean_object* v_inst_3067_, lean_object* v_inst_3068_, lean_object* v_00_u03c1_3069_, lean_object* v_inst_3070_, lean_object* v_m_3071_, lean_object* v_l_3072_){
_start:
{
lean_object* v_keyArray_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; uint8_t v___x_3076_; 
v_keyArray_3073_ = lean_ctor_get(v_m_3071_, 1);
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = lean_array_get_size(v_keyArray_3073_);
v___x_3076_ = lean_nat_dec_lt(v___x_3074_, v___x_3075_);
if (v___x_3076_ == 0)
{
lean_dec(v_l_3072_);
lean_dec(v_inst_3070_);
lean_dec_ref(v_inst_3068_);
lean_dec_ref(v_inst_3067_);
return v_m_3071_;
}
else
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v_inst_3070_, v_inst_3067_, v_inst_3068_, v_m_3071_, v_l_3072_);
return v___x_3077_;
}
}
}
static lean_object* _init_l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_3078_; lean_object* v___x_3079_; 
v_cellCount_3078_ = lean_unsigned_to_nat(16u);
v___x_3079_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3078_);
return v___x_3079_;
}
}
static lean_object* _init_l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3080_ = lean_obj_once(&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0, &l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0_once, _init_l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__0);
v___x_3081_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__0, &l_Std_DHashMap_Raw_instEmptyCollection___closed__0_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__0);
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
lean_ctor_set(v___x_3083_, 1, v___x_3081_);
lean_ctor_set(v___x_3083_, 2, v___x_3080_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray___redArg(lean_object* v_inst_3088_, lean_object* v_inst_3089_, lean_object* v_l_3090_){
_start:
{
lean_object* v___x_3091_; uint8_t v___x_3092_; 
v___x_3091_ = lean_obj_once(&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1, &l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1);
v___x_3092_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3092_ == 0)
{
lean_dec_ref(v_l_3090_);
lean_dec_ref(v_inst_3089_);
lean_dec_ref(v_inst_3088_);
return v___x_3091_;
}
else
{
lean_object* v___f_3093_; lean_object* v___x_3094_; 
v___f_3093_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__3));
v___x_3094_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_3093_, v_inst_3088_, v_inst_3089_, v___x_3091_, v_l_3090_);
return v___x_3094_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfArray(lean_object* v_00_u03b1_3095_, lean_object* v_inst_3096_, lean_object* v_inst_3097_, lean_object* v_l_3098_){
_start:
{
lean_object* v___x_3099_; uint8_t v___x_3100_; 
v___x_3099_ = lean_obj_once(&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1, &l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1);
v___x_3100_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3100_ == 0)
{
lean_dec_ref(v_l_3098_);
lean_dec_ref(v_inst_3097_);
lean_dec_ref(v_inst_3096_);
return v___x_3099_;
}
else
{
lean_object* v___f_3101_; lean_object* v___x_3102_; 
v___f_3101_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__3));
v___x_3102_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_3101_, v_inst_3096_, v_inst_3097_, v___x_3099_, v_l_3098_);
return v___x_3102_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg(lean_object* v_m_3103_){
_start:
{
lean_object* v_keyArray_3104_; lean_object* v___x_3105_; 
v_keyArray_3104_ = lean_ctor_get(v_m_3103_, 1);
v___x_3105_ = lean_array_get_size(v_keyArray_3104_);
return v___x_3105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___redArg___boxed(lean_object* v_m_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_3106_);
lean_dec_ref(v_m_3106_);
return v_res_3107_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets(lean_object* v_00_u03b1_3108_, lean_object* v_00_u03b2_3109_, lean_object* v_m_3110_){
_start:
{
lean_object* v___x_3111_; 
v___x_3111_ = l_Std_DHashMap_Raw_Internal_numBuckets___redArg(v_m_3110_);
return v___x_3111_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Internal_numBuckets___boxed(lean_object* v_00_u03b1_3112_, lean_object* v_00_u03b2_3113_, lean_object* v_m_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Std_DHashMap_Raw_Internal_numBuckets(v_00_u03b1_3112_, v_00_u03b2_3113_, v_m_3114_);
lean_dec_ref(v_m_3114_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___lam__0(lean_object* v_x1_3116_, lean_object* v_x2_3117_, lean_object* v_x3_3118_){
_start:
{
lean_object* v___x_3119_; lean_object* v___x_3120_; 
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v_x2_3117_);
lean_ctor_set(v___x_3119_, 1, v_x3_3118_);
v___x_3120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
lean_ctor_set(v___x_3120_, 1, v_x1_3116_);
return v___x_3120_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg(lean_object* v_m_3122_){
_start:
{
lean_object* v___f_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___f_3123_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__0));
v___x_3124_ = lean_box(0);
v___x_3125_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_3126_ = lean_unsigned_to_nat(0u);
v___x_3127_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_3125_, v___f_3123_, v_m_3122_, v___x_3124_, v___x_3126_);
return v___x_3127_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___redArg___boxed(lean_object* v_m_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_Std_DHashMap_Raw_toList___redArg(v_m_3128_);
lean_dec_ref(v_m_3128_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList(lean_object* v_00_u03b1_3130_, lean_object* v_00_u03b2_3131_, lean_object* v_m_3132_){
_start:
{
lean_object* v___f_3133_; lean_object* v___x_3134_; lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; 
v___f_3133_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__0));
v___x_3134_ = lean_box(0);
v___x_3135_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_3136_ = lean_unsigned_to_nat(0u);
v___x_3137_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_3135_, v___f_3133_, v_m_3132_, v___x_3134_, v___x_3136_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_toList___boxed(lean_object* v_00_u03b1_3138_, lean_object* v_00_u03b2_3139_, lean_object* v_m_3140_){
_start:
{
lean_object* v_res_3141_; 
v_res_3141_ = l_Std_DHashMap_Raw_toList(v_00_u03b1_3138_, v_00_u03b2_3139_, v_m_3140_);
lean_dec_ref(v_m_3140_);
return v_res_3141_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___lam__0(lean_object* v_x1_3142_, lean_object* v_x2_3143_, lean_object* v_x3_3144_){
_start:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3145_, 0, v_x2_3143_);
lean_ctor_set(v___x_3145_, 1, v_x3_3144_);
v___x_3146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
lean_ctor_set(v___x_3146_, 1, v_x1_3142_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg(lean_object* v_m_3148_){
_start:
{
lean_object* v___f_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___f_3149_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toList___redArg___closed__0));
v___x_3150_ = lean_box(0);
v___x_3151_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_3151_, v___f_3149_, v_m_3148_, v___x_3150_, v___x_3152_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___redArg___boxed(lean_object* v_m_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_Std_DHashMap_Raw_Const_toList___redArg(v_m_3154_);
lean_dec_ref(v_m_3154_);
return v_res_3155_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList(lean_object* v_00_u03b1_3156_, lean_object* v_00_u03b2_3157_, lean_object* v_m_3158_){
_start:
{
lean_object* v___f_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___f_3159_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_toList___redArg___closed__0));
v___x_3160_ = lean_box(0);
v___x_3161_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_3162_ = lean_unsigned_to_nat(0u);
v___x_3163_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_3161_, v___f_3159_, v_m_3158_, v___x_3160_, v___x_3162_);
return v___x_3163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_toList___boxed(lean_object* v_00_u03b1_3164_, lean_object* v_00_u03b2_3165_, lean_object* v_m_3166_){
_start:
{
lean_object* v_res_3167_; 
v_res_3167_ = l_Std_DHashMap_Raw_Const_toList(v_00_u03b1_3164_, v_00_u03b2_3165_, v_m_3166_);
lean_dec_ref(v_m_3166_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__1(lean_object* v___f_3171_, lean_object* v___x_3172_, lean_object* v_m_3173_, lean_object* v_prec_3174_){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3175_ = ((lean_object*)(l_Std_DHashMap_Raw_instRepr___redArg___lam__1___closed__1));
v___x_3176_ = lean_box(0);
v___x_3177_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_3177_, v___f_3171_, v_m_3173_, v___x_3176_, v___x_3178_);
v___x_3180_ = l_List_repr___redArg(v___x_3172_, v___x_3179_);
v___x_3181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_3181_, 0, v___x_3175_);
lean_ctor_set(v___x_3181_, 1, v___x_3180_);
v___x_3182_ = l_Repr_addAppParen(v___x_3181_, v_prec_3174_);
return v___x_3182_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg___lam__1___boxed(lean_object* v___f_3183_, lean_object* v___x_3184_, lean_object* v_m_3185_, lean_object* v_prec_3186_){
_start:
{
lean_object* v_res_3187_; 
v_res_3187_ = l_Std_DHashMap_Raw_instRepr___redArg___lam__1(v___f_3183_, v___x_3184_, v_m_3185_, v_prec_3186_);
lean_dec(v_prec_3186_);
lean_dec_ref(v_m_3185_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr___redArg(lean_object* v_inst_3188_, lean_object* v_inst_3189_){
_start:
{
lean_object* v___f_3190_; lean_object* v___x_3191_; lean_object* v___f_3192_; 
v___f_3190_ = ((lean_object*)(l_Std_DHashMap_Raw_toList___redArg___closed__0));
v___x_3191_ = lean_alloc_closure((void*)(l_Sigma_repr___boxed), 6, 4);
lean_closure_set(v___x_3191_, 0, lean_box(0));
lean_closure_set(v___x_3191_, 1, lean_box(0));
lean_closure_set(v___x_3191_, 2, v_inst_3188_);
lean_closure_set(v___x_3191_, 3, v_inst_3189_);
v___f_3192_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instRepr___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_3192_, 0, v___f_3190_);
lean_closure_set(v___f_3192_, 1, v___x_3191_);
return v___f_3192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instRepr(lean_object* v_00_u03b1_3193_, lean_object* v_00_u03b2_3194_, lean_object* v_inst_3195_, lean_object* v_inst_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Std_DHashMap_Raw_instRepr___redArg(v_inst_3195_, v_inst_3196_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0(lean_object* v_x1_3198_, lean_object* v_x2_3199_, lean_object* v_x3_3200_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_x2_3199_);
lean_ctor_set(v___x_3201_, 1, v_x1_3198_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___lam__0___boxed(lean_object* v_x1_3202_, lean_object* v_x2_3203_, lean_object* v_x3_3204_){
_start:
{
lean_object* v_res_3205_; 
v_res_3205_ = l_Std_DHashMap_Raw_keys___redArg___lam__0(v_x1_3202_, v_x2_3203_, v_x3_3204_);
lean_dec(v_x3_3204_);
return v_res_3205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg(lean_object* v_m_3207_){
_start:
{
lean_object* v___f_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___f_3208_ = ((lean_object*)(l_Std_DHashMap_Raw_keys___redArg___closed__0));
v___x_3209_ = lean_box(0);
v___x_3210_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_3211_ = lean_unsigned_to_nat(0u);
v___x_3212_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_3210_, v___f_3208_, v_m_3207_, v___x_3209_, v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___redArg___boxed(lean_object* v_m_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Std_DHashMap_Raw_keys___redArg(v_m_3213_);
lean_dec_ref(v_m_3213_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys(lean_object* v_00_u03b1_3215_, lean_object* v_00_u03b2_3216_, lean_object* v_m_3217_){
_start:
{
lean_object* v___f_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___f_3218_ = ((lean_object*)(l_Std_DHashMap_Raw_keys___redArg___closed__0));
v___x_3219_ = lean_box(0);
v___x_3220_ = ((lean_object*)(l_Std_DHashMap_Raw_Internal_foldRev___redArg___closed__9));
v___x_3221_ = lean_unsigned_to_nat(0u);
v___x_3222_ = l_Std_DHashMap_Raw_foldRevMFrom___redArg(v___x_3220_, v___f_3218_, v_m_3217_, v___x_3219_, v___x_3221_);
return v___x_3222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keys___boxed(lean_object* v_00_u03b1_3223_, lean_object* v_00_u03b2_3224_, lean_object* v_m_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Std_DHashMap_Raw_keys(v_00_u03b1_3223_, v_00_u03b2_3224_, v_m_3225_);
lean_dec_ref(v_m_3225_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList___redArg(lean_object* v_inst_3231_, lean_object* v_inst_3232_, lean_object* v_l_3233_){
_start:
{
lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3234_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
v___x_3235_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3235_ == 0)
{
lean_dec(v_l_3233_);
lean_dec_ref(v_inst_3232_);
lean_dec_ref(v_inst_3231_);
return v___x_3234_;
}
else
{
lean_object* v___f_3236_; lean_object* v___x_3237_; 
v___f_3236_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_3237_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_3236_, v_inst_3231_, v_inst_3232_, v___x_3234_, v_l_3233_);
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofList(lean_object* v_00_u03b1_3238_, lean_object* v_00_u03b2_3239_, lean_object* v_inst_3240_, lean_object* v_inst_3241_, lean_object* v_l_3242_){
_start:
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
v___x_3244_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3244_ == 0)
{
lean_dec(v_l_3242_);
lean_dec_ref(v_inst_3241_);
lean_dec_ref(v_inst_3240_);
return v___x_3243_;
}
else
{
lean_object* v___f_3245_; lean_object* v___x_3246_; 
v___f_3245_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_3246_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_3245_, v_inst_3240_, v_inst_3241_, v___x_3243_, v_l_3242_);
return v___x_3246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray___redArg(lean_object* v_inst_3247_, lean_object* v_inst_3248_, lean_object* v_l_3249_){
_start:
{
lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
v___x_3251_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3251_ == 0)
{
lean_dec_ref(v_l_3249_);
lean_dec_ref(v_inst_3248_);
lean_dec_ref(v_inst_3247_);
return v___x_3250_;
}
else
{
lean_object* v___f_3252_; lean_object* v___x_3253_; 
v___f_3252_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__3));
v___x_3253_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_3252_, v_inst_3247_, v_inst_3248_, v___x_3250_, v_l_3249_);
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_ofArray(lean_object* v_00_u03b1_3254_, lean_object* v_00_u03b2_3255_, lean_object* v_inst_3256_, lean_object* v_inst_3257_, lean_object* v_l_3258_){
_start:
{
lean_object* v___x_3259_; uint8_t v___x_3260_; 
v___x_3259_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
v___x_3260_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3260_ == 0)
{
lean_dec_ref(v_l_3258_);
lean_dec_ref(v_inst_3257_);
lean_dec_ref(v_inst_3256_);
return v___x_3259_;
}
else
{
lean_object* v___f_3261_; lean_object* v___x_3262_; 
v___f_3261_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__3));
v___x_3262_ = l_Std_DHashMap_Internal_Raw_u2080_insertMany___redArg(v___f_3261_, v_inst_3256_, v_inst_3257_, v___x_3259_, v_l_3258_);
return v___x_3262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList___redArg(lean_object* v_inst_3263_, lean_object* v_inst_3264_, lean_object* v_l_3265_){
_start:
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
v___x_3267_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3267_ == 0)
{
lean_dec(v_l_3265_);
lean_dec_ref(v_inst_3264_);
lean_dec_ref(v_inst_3263_);
return v___x_3266_;
}
else
{
lean_object* v___f_3268_; lean_object* v___x_3269_; 
v___f_3268_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_3269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_3268_, v_inst_3263_, v_inst_3264_, v___x_3266_, v_l_3265_);
return v___x_3269_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofList(lean_object* v_00_u03b1_3270_, lean_object* v_00_u03b2_3271_, lean_object* v_inst_3272_, lean_object* v_inst_3273_, lean_object* v_l_3274_){
_start:
{
lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3275_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
v___x_3276_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3276_ == 0)
{
lean_dec(v_l_3274_);
lean_dec_ref(v_inst_3273_);
lean_dec_ref(v_inst_3272_);
return v___x_3275_;
}
else
{
lean_object* v___f_3277_; lean_object* v___x_3278_; 
v___f_3277_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_3278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_3277_, v_inst_3272_, v_inst_3273_, v___x_3275_, v_l_3274_);
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray___redArg(lean_object* v_inst_3279_, lean_object* v_inst_3280_, lean_object* v_l_3281_){
_start:
{
lean_object* v___x_3282_; uint8_t v___x_3283_; 
v___x_3282_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
v___x_3283_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3283_ == 0)
{
lean_dec_ref(v_l_3281_);
lean_dec_ref(v_inst_3280_);
lean_dec_ref(v_inst_3279_);
return v___x_3282_;
}
else
{
lean_object* v___f_3284_; lean_object* v___x_3285_; 
v___f_3284_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__3));
v___x_3285_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_3284_, v_inst_3279_, v_inst_3280_, v___x_3282_, v_l_3281_);
return v___x_3285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_ofArray(lean_object* v_00_u03b1_3286_, lean_object* v_00_u03b2_3287_, lean_object* v_inst_3288_, lean_object* v_inst_3289_, lean_object* v_l_3290_){
_start:
{
lean_object* v___x_3291_; uint8_t v___x_3292_; 
v___x_3291_ = lean_obj_once(&l_Std_DHashMap_Raw_instEmptyCollection___closed__2, &l_Std_DHashMap_Raw_instEmptyCollection___closed__2_once, _init_l_Std_DHashMap_Raw_instEmptyCollection___closed__2);
v___x_3292_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3292_ == 0)
{
lean_dec_ref(v_l_3290_);
lean_dec_ref(v_inst_3289_);
lean_dec_ref(v_inst_3288_);
return v___x_3291_;
}
else
{
lean_object* v___f_3293_; lean_object* v___x_3294_; 
v___f_3293_ = ((lean_object*)(l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__3));
v___x_3294_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___redArg(v___f_3293_, v_inst_3288_, v_inst_3289_, v___x_3291_, v_l_3290_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList___redArg(lean_object* v_inst_3295_, lean_object* v_inst_3296_, lean_object* v_l_3297_){
_start:
{
lean_object* v___x_3298_; uint8_t v___x_3299_; 
v___x_3298_ = lean_obj_once(&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1, &l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1);
v___x_3299_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3299_ == 0)
{
lean_dec(v_l_3297_);
lean_dec_ref(v_inst_3296_);
lean_dec_ref(v_inst_3295_);
return v___x_3298_;
}
else
{
lean_object* v___f_3300_; lean_object* v___x_3301_; 
v___f_3300_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_3301_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_3300_, v_inst_3295_, v_inst_3296_, v___x_3298_, v_l_3297_);
return v___x_3301_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_Const_unitOfList(lean_object* v_00_u03b1_3302_, lean_object* v_inst_3303_, lean_object* v_inst_3304_, lean_object* v_l_3305_){
_start:
{
lean_object* v___x_3306_; uint8_t v___x_3307_; 
v___x_3306_ = lean_obj_once(&l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1, &l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1_once, _init_l_Std_DHashMap_Raw_Const_unitOfArray___redArg___closed__1);
v___x_3307_ = lean_uint8_once(&l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1, &l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1_once, _init_l_Std_DHashMap_Raw_instSingletonSigmaOfBEqOfHashable___redArg___lam__0___closed__1);
if (v___x_3307_ == 0)
{
lean_dec(v_l_3305_);
lean_dec_ref(v_inst_3304_);
lean_dec_ref(v_inst_3303_);
return v___x_3306_;
}
else
{
lean_object* v___f_3308_; lean_object* v___x_3309_; 
v___f_3308_ = ((lean_object*)(l_Std_DHashMap_Raw_ofList___redArg___closed__1));
v___x_3309_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertManyIfNewUnit___redArg(v___f_3308_, v_inst_3303_, v_inst_3304_, v___x_3306_, v_l_3305_);
return v___x_3309_;
}
}
}
lean_object* runtime_initialize_Init_Data_LawfulHashable(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_LawfulHashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_LawfulHashable(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Raw(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_LawfulHashable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Raw(builtin);
}
#ifdef __cplusplus
}
#endif
