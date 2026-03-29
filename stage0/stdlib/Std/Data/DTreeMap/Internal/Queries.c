// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Queries
// Imports: public import Init.Data.Nat.Compare public import Std.Data.DTreeMap.Internal.Balanced public import Std.Data.DTreeMap.Internal.Ordered public import Init.BinderPredicates public import Init.Data.Option.BasicAux import Init.Data.Nat.Lemmas import Init.Data.Nat.Linear import Init.Omega import Init.RCases import Init.WFTactics
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DTreeMap"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__2_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Impl"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__3_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term_~m_"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__4_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 1, 106, 2, 110, 100, 218, 30)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(27, 108, 102, 221, 169, 83, 94, 148)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 90, 101, 118, 142, 120, 198, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value_aux_3),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(173, 252, 101, 70, 173, 83, 175, 204)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__7_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " ~m "};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__9 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__9_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__10 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__10_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__11 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__11_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__11_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__12 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__12_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__7_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__9_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__12_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__13 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__13_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__13_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__14 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__14_value;
LEAN_EXPORT const lean_object* l_Std_DTreeMap_Internal_Impl_term___x7em__ = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__14_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__2_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__3_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Equiv"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(0, 253, 123, 237, 128, 91, 245, 83)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_0),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(194, 1, 106, 2, 110, 100, 218, 30)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_1),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(27, 108, 102, 221, 169, 83, 94, 148)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_2),((lean_object*)&l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__3_value),LEAN_SCALAR_PTR_LITERAL(7, 90, 101, 118, 142, 120, 198, 229)}};
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value_aux_3),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(108, 66, 18, 64, 176, 254, 8, 146)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__9 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__9_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__8_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__10 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__10_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__11 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__11_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__9_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__11_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__13 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__13_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__0_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___redArg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Data.DTreeMap.Internal.Queries"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "Std.DTreeMap.Internal.Impl.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Key is not present in map"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.getEntry!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.DTreeMap.Internal.Impl.getKey!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.DTreeMap.Internal.Impl.Const.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__0_value;
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__1_value;
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__2_value;
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__3 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__3_value;
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__4 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__4_value;
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__5 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__5_value;
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__6 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__6_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__0_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__1_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__7 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__7_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__7_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__2_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__3_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__4_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__5_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__8 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__8_value;
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__8_value),((lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__6_value)}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.minEntry!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Map is empty"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.maxEntry!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.DTreeMap.Internal.Impl.minKey!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.DTreeMap.Internal.Impl.maxKey!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Std.DTreeMap.Internal.Impl.entryAtIdx!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Out-of-bounds access"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DTreeMap.Internal.Impl.keyAtIdx!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.DTreeMap.Internal.Impl.Const.minEntry!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.DTreeMap.Internal.Impl.Const.maxEntry!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "Std.DTreeMap.Internal.Impl.Const.entryAtIdx!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall(lean_object* v_00_u03b1_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5));
v___x_47_ = l_String_toRawSubstring_x27(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1(lean_object* v_x_70_, lean_object* v_a_71_, lean_object* v_a_72_){
_start:
{
lean_object* v___x_73_; uint8_t v___x_74_; 
v___x_73_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5));
lean_inc(v_x_70_);
v___x_74_ = l_Lean_Syntax_isOfKind(v_x_70_, v___x_73_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v___x_76_; 
lean_dec(v_x_70_);
v___x_75_ = lean_box(1);
v___x_76_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v_a_72_);
return v___x_76_;
}
else
{
lean_object* v_quotContext_77_; lean_object* v_currMacroScope_78_; lean_object* v_ref_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_quotContext_77_ = lean_ctor_get(v_a_71_, 1);
v_currMacroScope_78_ = lean_ctor_get(v_a_71_, 2);
v_ref_79_ = lean_ctor_get(v_a_71_, 5);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_70_, v___x_80_);
v___x_82_ = lean_unsigned_to_nat(2u);
v___x_83_ = l_Lean_Syntax_getArg(v_x_70_, v___x_82_);
lean_dec(v_x_70_);
v___x_84_ = 0;
v___x_85_ = l_Lean_SourceInfo_fromRef(v_ref_79_, v___x_84_);
v___x_86_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4));
v___x_87_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6);
v___x_88_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_78_);
lean_inc(v_quotContext_77_);
v___x_89_ = l_Lean_addMacroScope(v_quotContext_77_, v___x_88_, v_currMacroScope_78_);
v___x_90_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12));
lean_inc_n(v___x_85_, 2);
v___x_91_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_91_, 0, v___x_85_);
lean_ctor_set(v___x_91_, 1, v___x_87_);
lean_ctor_set(v___x_91_, 2, v___x_89_);
lean_ctor_set(v___x_91_, 3, v___x_90_);
v___x_92_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14));
v___x_93_ = l_Lean_Syntax_node2(v___x_85_, v___x_92_, v___x_81_, v___x_83_);
v___x_94_ = l_Lean_Syntax_node2(v___x_85_, v___x_86_, v___x_91_, v___x_93_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_a_72_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___boxed(lean_object* v_x_96_, lean_object* v_a_97_, lean_object* v_a_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1(v_x_96_, v_a_97_, v_a_98_);
lean_dec_ref(v_a_97_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(lean_object* v_x_103_, lean_object* v_a_104_, lean_object* v_a_105_){
_start:
{
lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_106_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4));
lean_inc(v_x_103_);
v___x_107_ = l_Lean_Syntax_isOfKind(v_x_103_, v___x_106_);
if (v___x_107_ == 0)
{
lean_object* v___x_108_; lean_object* v___x_109_; 
lean_dec(v_x_103_);
v___x_108_ = lean_box(0);
v___x_109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_a_105_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = l_Lean_Syntax_getArg(v_x_103_, v___x_110_);
v___x_112_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1));
lean_inc(v___x_111_);
v___x_113_ = l_Lean_Syntax_isOfKind(v___x_111_, v___x_112_);
if (v___x_113_ == 0)
{
lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v___x_111_);
lean_dec(v_x_103_);
v___x_114_ = lean_box(0);
v___x_115_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v_a_105_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_116_ = lean_unsigned_to_nat(1u);
v___x_117_ = l_Lean_Syntax_getArg(v_x_103_, v___x_116_);
lean_dec(v_x_103_);
v___x_118_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_117_);
v___x_119_ = l_Lean_Syntax_matchesNull(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v___x_117_);
lean_dec(v___x_111_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_120_);
lean_ctor_set(v___x_121_, 1, v_a_105_);
return v___x_121_;
}
else
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v_ref_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_122_ = l_Lean_Syntax_getArg(v___x_117_, v___x_110_);
v___x_123_ = l_Lean_Syntax_getArg(v___x_117_, v___x_116_);
lean_dec(v___x_117_);
v_ref_124_ = l_Lean_replaceRef(v___x_111_, v_a_104_);
lean_dec(v___x_111_);
v___x_125_ = 0;
v___x_126_ = l_Lean_SourceInfo_fromRef(v_ref_124_, v___x_125_);
lean_dec(v_ref_124_);
v___x_127_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5));
v___x_128_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8));
lean_inc(v___x_126_);
v___x_129_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_126_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v___x_130_ = l_Lean_Syntax_node3(v___x_126_, v___x_127_, v___x_122_, v___x_129_, v___x_123_);
v___x_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v_a_105_);
return v___x_131_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___boxed(lean_object* v_x_132_, lean_object* v_a_133_, lean_object* v_a_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(v_x_132_, v_a_133_, v_a_134_);
lean_dec(v_a_133_);
return v_res_135_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object* v_inst_136_, lean_object* v_k_137_, lean_object* v_t_138_){
_start:
{
if (lean_obj_tag(v_t_138_) == 0)
{
lean_object* v_k_139_; lean_object* v_l_140_; lean_object* v_r_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v_k_139_ = lean_ctor_get(v_t_138_, 1);
lean_inc(v_k_139_);
v_l_140_ = lean_ctor_get(v_t_138_, 3);
lean_inc(v_l_140_);
v_r_141_ = lean_ctor_get(v_t_138_, 4);
lean_inc(v_r_141_);
lean_dec_ref(v_t_138_);
lean_inc_ref(v_inst_136_);
lean_inc(v_k_137_);
v___x_142_ = lean_apply_2(v_inst_136_, v_k_137_, v_k_139_);
v___x_143_ = lean_unbox(v___x_142_);
switch(v___x_143_)
{
case 0:
{
lean_dec(v_r_141_);
v_t_138_ = v_l_140_;
goto _start;
}
case 1:
{
uint8_t v___x_145_; 
lean_dec(v_r_141_);
lean_dec(v_l_140_);
lean_dec(v_k_137_);
lean_dec_ref(v_inst_136_);
v___x_145_ = 1;
return v___x_145_;
}
default: 
{
lean_dec(v_l_140_);
v_t_138_ = v_r_141_;
goto _start;
}
}
}
else
{
uint8_t v___x_147_; 
lean_dec(v_k_137_);
lean_dec_ref(v_inst_136_);
v___x_147_ = 0;
return v___x_147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___redArg___boxed(lean_object* v_inst_148_, lean_object* v_k_149_, lean_object* v_t_150_){
_start:
{
uint8_t v_res_151_; lean_object* v_r_152_; 
v_res_151_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_148_, v_k_149_, v_t_150_);
v_r_152_ = lean_box(v_res_151_);
return v_r_152_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains(lean_object* v_00_u03b1_153_, lean_object* v_00_u03b2_154_, lean_object* v_inst_155_, lean_object* v_k_156_, lean_object* v_t_157_){
_start:
{
uint8_t v___x_158_; 
v___x_158_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_155_, v_k_156_, v_t_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___boxed(lean_object* v_00_u03b1_159_, lean_object* v_00_u03b2_160_, lean_object* v_inst_161_, lean_object* v_k_162_, lean_object* v_t_163_){
_start:
{
uint8_t v_res_164_; lean_object* v_r_165_; 
v_res_164_ = l_Std_DTreeMap_Internal_Impl_contains(v_00_u03b1_159_, v_00_u03b2_160_, v_inst_161_, v_k_162_, v_t_163_);
v_r_165_ = lean_box(v_res_164_);
return v_r_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_inst_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = lean_box(0);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___boxed(lean_object* v_00_u03b1_170_, lean_object* v_00_u03b2_171_, lean_object* v_inst_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(v_00_u03b1_170_, v_00_u03b2_171_, v_inst_172_);
lean_dec_ref(v_inst_172_);
return v_res_173_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(lean_object* v_inst_174_, lean_object* v_m_175_, lean_object* v_a_176_){
_start:
{
uint8_t v___x_177_; 
v___x_177_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_174_, v_a_176_, v_m_175_);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg___boxed(lean_object* v_inst_178_, lean_object* v_m_179_, lean_object* v_a_180_){
_start:
{
uint8_t v_res_181_; lean_object* v_r_182_; 
v_res_181_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(v_inst_178_, v_m_179_, v_a_180_);
v_r_182_ = lean_box(v_res_181_);
return v_r_182_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem(lean_object* v_00_u03b1_183_, lean_object* v_00_u03b2_184_, lean_object* v_inst_185_, lean_object* v_m_186_, lean_object* v_a_187_){
_start:
{
uint8_t v___x_188_; 
v___x_188_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_185_, v_a_187_, v_m_186_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___boxed(lean_object* v_00_u03b1_189_, lean_object* v_00_u03b2_190_, lean_object* v_inst_191_, lean_object* v_m_192_, lean_object* v_a_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem(v_00_u03b1_189_, v_00_u03b2_190_, v_inst_191_, v_m_192_, v_a_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_196_, lean_object* v_h__1_197_, lean_object* v_h__2_198_){
_start:
{
if (lean_obj_tag(v_t_196_) == 0)
{
lean_object* v_size_199_; lean_object* v_k_200_; lean_object* v_v_201_; lean_object* v_l_202_; lean_object* v_r_203_; lean_object* v___x_204_; 
lean_dec(v_h__1_197_);
v_size_199_ = lean_ctor_get(v_t_196_, 0);
lean_inc(v_size_199_);
v_k_200_ = lean_ctor_get(v_t_196_, 1);
lean_inc(v_k_200_);
v_v_201_ = lean_ctor_get(v_t_196_, 2);
lean_inc(v_v_201_);
v_l_202_ = lean_ctor_get(v_t_196_, 3);
lean_inc(v_l_202_);
v_r_203_ = lean_ctor_get(v_t_196_, 4);
lean_inc(v_r_203_);
lean_dec_ref(v_t_196_);
v___x_204_ = lean_apply_5(v_h__2_198_, v_size_199_, v_k_200_, v_v_201_, v_l_202_, v_r_203_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; lean_object* v___x_206_; 
lean_dec(v_h__2_198_);
v___x_205_ = lean_box(0);
v___x_206_ = lean_apply_1(v_h__1_197_, v___x_205_);
return v___x_206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_207_, lean_object* v_00_u03b2_208_, lean_object* v_motive_209_, lean_object* v_t_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_){
_start:
{
if (lean_obj_tag(v_t_210_) == 0)
{
lean_object* v_size_213_; lean_object* v_k_214_; lean_object* v_v_215_; lean_object* v_l_216_; lean_object* v_r_217_; lean_object* v___x_218_; 
lean_dec(v_h__1_211_);
v_size_213_ = lean_ctor_get(v_t_210_, 0);
lean_inc(v_size_213_);
v_k_214_ = lean_ctor_get(v_t_210_, 1);
lean_inc(v_k_214_);
v_v_215_ = lean_ctor_get(v_t_210_, 2);
lean_inc(v_v_215_);
v_l_216_ = lean_ctor_get(v_t_210_, 3);
lean_inc(v_l_216_);
v_r_217_ = lean_ctor_get(v_t_210_, 4);
lean_inc(v_r_217_);
lean_dec_ref(v_t_210_);
v___x_218_ = lean_apply_5(v_h__2_212_, v_size_213_, v_k_214_, v_v_215_, v_l_216_, v_r_217_);
return v___x_218_;
}
else
{
lean_object* v___x_219_; lean_object* v___x_220_; 
lean_dec(v_h__2_212_);
v___x_219_ = lean_box(0);
v___x_220_ = lean_apply_1(v_h__1_211_, v___x_219_);
return v___x_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t v_x_221_, lean_object* v_h__1_222_, lean_object* v_h__2_223_, lean_object* v_h__3_224_){
_start:
{
switch(v_x_221_)
{
case 0:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v_h__3_224_);
lean_dec(v_h__2_223_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_apply_1(v_h__1_222_, v___x_225_);
return v___x_226_;
}
case 1:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec(v_h__2_223_);
lean_dec(v_h__1_222_);
v___x_227_ = lean_box(0);
v___x_228_ = lean_apply_1(v_h__3_224_, v___x_227_);
return v___x_228_;
}
default: 
{
lean_object* v___x_229_; lean_object* v___x_230_; 
lean_dec(v_h__3_224_);
lean_dec(v_h__1_222_);
v___x_229_ = lean_box(0);
v___x_230_ = lean_apply_1(v_h__2_223_, v___x_229_);
return v___x_230_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* v_x_231_, lean_object* v_h__1_232_, lean_object* v_h__2_233_, lean_object* v_h__3_234_){
_start:
{
uint8_t v_x_36__boxed_235_; lean_object* v_res_236_; 
v_x_36__boxed_235_ = lean_unbox(v_x_231_);
v_res_236_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_36__boxed_235_, v_h__1_232_, v_h__2_233_, v_h__3_234_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* v_motive_237_, uint8_t v_x_238_, lean_object* v_h__1_239_, lean_object* v_h__2_240_, lean_object* v_h__3_241_){
_start:
{
switch(v_x_238_)
{
case 0:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_h__3_241_);
lean_dec(v_h__2_240_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_apply_1(v_h__1_239_, v___x_242_);
return v___x_243_;
}
case 1:
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_h__2_240_);
lean_dec(v_h__1_239_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_apply_1(v_h__3_241_, v___x_244_);
return v___x_245_;
}
default: 
{
lean_object* v___x_246_; lean_object* v___x_247_; 
lean_dec(v_h__3_241_);
lean_dec(v_h__1_239_);
v___x_246_ = lean_box(0);
v___x_247_ = lean_apply_1(v_h__2_240_, v___x_246_);
return v___x_247_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* v_motive_248_, lean_object* v_x_249_, lean_object* v_h__1_250_, lean_object* v_h__2_251_, lean_object* v_h__3_252_){
_start:
{
uint8_t v_x_51__boxed_253_; lean_object* v_res_254_; 
v_x_51__boxed_253_ = lean_unbox(v_x_249_);
v_res_254_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_248_, v_x_51__boxed_253_, v_h__1_250_, v_h__2_251_, v_h__3_252_);
return v_res_254_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(lean_object* v_t_255_){
_start:
{
if (lean_obj_tag(v_t_255_) == 0)
{
uint8_t v___x_256_; 
v___x_256_ = 0;
return v___x_256_;
}
else
{
uint8_t v___x_257_; 
v___x_257_ = 1;
return v___x_257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___redArg___boxed(lean_object* v_t_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(v_t_258_);
lean_dec(v_t_258_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty(lean_object* v_00_u03b1_261_, lean_object* v_00_u03b2_262_, lean_object* v_t_263_){
_start:
{
if (lean_obj_tag(v_t_263_) == 0)
{
uint8_t v___x_264_; 
v___x_264_ = 0;
return v___x_264_;
}
else
{
uint8_t v___x_265_; 
v___x_265_ = 1;
return v___x_265_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___boxed(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_t_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = l_Std_DTreeMap_Internal_Impl_isEmpty(v_00_u03b1_266_, v_00_u03b2_267_, v_t_268_);
lean_dec(v_t_268_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object* v_inst_271_, lean_object* v_t_272_, lean_object* v_k_273_){
_start:
{
if (lean_obj_tag(v_t_272_) == 0)
{
lean_object* v_k_274_; lean_object* v_v_275_; lean_object* v_l_276_; lean_object* v_r_277_; lean_object* v___x_278_; uint8_t v___x_279_; 
v_k_274_ = lean_ctor_get(v_t_272_, 1);
lean_inc(v_k_274_);
v_v_275_ = lean_ctor_get(v_t_272_, 2);
lean_inc(v_v_275_);
v_l_276_ = lean_ctor_get(v_t_272_, 3);
lean_inc(v_l_276_);
v_r_277_ = lean_ctor_get(v_t_272_, 4);
lean_inc(v_r_277_);
lean_dec_ref(v_t_272_);
lean_inc_ref(v_inst_271_);
lean_inc(v_k_273_);
v___x_278_ = lean_apply_2(v_inst_271_, v_k_273_, v_k_274_);
v___x_279_ = lean_unbox(v___x_278_);
switch(v___x_279_)
{
case 0:
{
lean_dec(v_r_277_);
lean_dec(v_v_275_);
v_t_272_ = v_l_276_;
goto _start;
}
case 1:
{
lean_object* v___x_281_; 
lean_dec(v_r_277_);
lean_dec(v_l_276_);
lean_dec(v_k_273_);
lean_dec_ref(v_inst_271_);
v___x_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_281_, 0, v_v_275_);
return v___x_281_;
}
default: 
{
lean_dec(v_l_276_);
lean_dec(v_v_275_);
v_t_272_ = v_r_277_;
goto _start;
}
}
}
else
{
lean_object* v___x_283_; 
lean_dec(v_k_273_);
lean_dec_ref(v_inst_271_);
v___x_283_ = lean_box(0);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f(lean_object* v_00_u03b1_284_, lean_object* v_00_u03b2_285_, lean_object* v_inst_286_, lean_object* v_inst_287_, lean_object* v_t_288_, lean_object* v_k_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_inst_286_, v_t_288_, v_k_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get___redArg(lean_object* v_inst_291_, lean_object* v_t_292_, lean_object* v_k_293_){
_start:
{
lean_object* v_k_294_; lean_object* v_v_295_; lean_object* v_l_296_; lean_object* v_r_297_; lean_object* v___x_298_; uint8_t v___x_299_; 
v_k_294_ = lean_ctor_get(v_t_292_, 1);
lean_inc(v_k_294_);
v_v_295_ = lean_ctor_get(v_t_292_, 2);
lean_inc(v_v_295_);
v_l_296_ = lean_ctor_get(v_t_292_, 3);
lean_inc(v_l_296_);
v_r_297_ = lean_ctor_get(v_t_292_, 4);
lean_inc(v_r_297_);
lean_dec(v_t_292_);
lean_inc_ref(v_inst_291_);
lean_inc(v_k_293_);
v___x_298_ = lean_apply_2(v_inst_291_, v_k_293_, v_k_294_);
v___x_299_ = lean_unbox(v___x_298_);
switch(v___x_299_)
{
case 0:
{
lean_dec(v_r_297_);
lean_dec(v_v_295_);
v_t_292_ = v_l_296_;
goto _start;
}
case 1:
{
lean_dec(v_r_297_);
lean_dec(v_l_296_);
lean_dec(v_k_293_);
lean_dec_ref(v_inst_291_);
return v_v_295_;
}
default: 
{
lean_dec(v_l_296_);
lean_dec(v_v_295_);
v_t_292_ = v_r_297_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get(lean_object* v_00_u03b1_302_, lean_object* v_00_u03b2_303_, lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_t_306_, lean_object* v_k_307_, lean_object* v_hlk_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_inst_304_, v_t_306_, v_k_307_);
return v___x_309_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_313_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_314_ = lean_unsigned_to_nat(13u);
v___x_315_ = lean_unsigned_to_nat(108u);
v___x_316_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1));
v___x_317_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_318_ = l_mkPanicMessageWithDecl(v___x_317_, v___x_316_, v___x_315_, v___x_314_, v___x_313_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object* v_inst_319_, lean_object* v_t_320_, lean_object* v_k_321_, lean_object* v_inst_322_){
_start:
{
if (lean_obj_tag(v_t_320_) == 0)
{
lean_object* v_k_323_; lean_object* v_v_324_; lean_object* v_l_325_; lean_object* v_r_326_; lean_object* v___x_327_; uint8_t v___x_328_; 
v_k_323_ = lean_ctor_get(v_t_320_, 1);
lean_inc(v_k_323_);
v_v_324_ = lean_ctor_get(v_t_320_, 2);
lean_inc(v_v_324_);
v_l_325_ = lean_ctor_get(v_t_320_, 3);
lean_inc(v_l_325_);
v_r_326_ = lean_ctor_get(v_t_320_, 4);
lean_inc(v_r_326_);
lean_dec_ref(v_t_320_);
lean_inc_ref(v_inst_319_);
lean_inc(v_k_321_);
v___x_327_ = lean_apply_2(v_inst_319_, v_k_321_, v_k_323_);
v___x_328_ = lean_unbox(v___x_327_);
switch(v___x_328_)
{
case 0:
{
lean_dec(v_r_326_);
lean_dec(v_v_324_);
v_t_320_ = v_l_325_;
goto _start;
}
case 1:
{
lean_dec(v_r_326_);
lean_dec(v_l_325_);
lean_dec(v_k_321_);
lean_dec_ref(v_inst_319_);
return v_v_324_;
}
default: 
{
lean_dec(v_l_325_);
lean_dec(v_v_324_);
v_t_320_ = v_r_326_;
goto _start;
}
}
}
else
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_k_321_);
lean_dec_ref(v_inst_319_);
v___x_331_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3);
v___x_332_ = l_panic___redArg(v_inst_322_, v___x_331_);
return v___x_332_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg___boxed(lean_object* v_inst_333_, lean_object* v_t_334_, lean_object* v_k_335_, lean_object* v_inst_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_inst_333_, v_t_334_, v_k_335_, v_inst_336_);
lean_dec(v_inst_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21(lean_object* v_00_u03b1_338_, lean_object* v_00_u03b2_339_, lean_object* v_inst_340_, lean_object* v_inst_341_, lean_object* v_t_342_, lean_object* v_k_343_, lean_object* v_inst_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_inst_340_, v_t_342_, v_k_343_, v_inst_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___boxed(lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_t_350_, lean_object* v_k_351_, lean_object* v_inst_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_DTreeMap_Internal_Impl_get_x21(v_00_u03b1_346_, v_00_u03b2_347_, v_inst_348_, v_inst_349_, v_t_350_, v_k_351_, v_inst_352_);
lean_dec(v_inst_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg(lean_object* v_inst_354_, lean_object* v_t_355_, lean_object* v_k_356_, lean_object* v_fallback_357_){
_start:
{
if (lean_obj_tag(v_t_355_) == 0)
{
lean_object* v_k_358_; lean_object* v_v_359_; lean_object* v_l_360_; lean_object* v_r_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_k_358_ = lean_ctor_get(v_t_355_, 1);
lean_inc(v_k_358_);
v_v_359_ = lean_ctor_get(v_t_355_, 2);
lean_inc(v_v_359_);
v_l_360_ = lean_ctor_get(v_t_355_, 3);
lean_inc(v_l_360_);
v_r_361_ = lean_ctor_get(v_t_355_, 4);
lean_inc(v_r_361_);
lean_dec_ref(v_t_355_);
lean_inc_ref(v_inst_354_);
lean_inc(v_k_356_);
v___x_362_ = lean_apply_2(v_inst_354_, v_k_356_, v_k_358_);
v___x_363_ = lean_unbox(v___x_362_);
switch(v___x_363_)
{
case 0:
{
lean_dec(v_r_361_);
lean_dec(v_v_359_);
v_t_355_ = v_l_360_;
goto _start;
}
case 1:
{
lean_dec(v_r_361_);
lean_dec(v_l_360_);
lean_dec(v_k_356_);
lean_dec_ref(v_inst_354_);
return v_v_359_;
}
default: 
{
lean_dec(v_l_360_);
lean_dec(v_v_359_);
v_t_355_ = v_r_361_;
goto _start;
}
}
}
else
{
lean_dec(v_k_356_);
lean_dec_ref(v_inst_354_);
lean_inc(v_fallback_357_);
return v_fallback_357_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg___boxed(lean_object* v_inst_366_, lean_object* v_t_367_, lean_object* v_k_368_, lean_object* v_fallback_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_inst_366_, v_t_367_, v_k_368_, v_fallback_369_);
lean_dec(v_fallback_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD(lean_object* v_00_u03b1_371_, lean_object* v_00_u03b2_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_t_375_, lean_object* v_k_376_, lean_object* v_fallback_377_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_inst_373_, v_t_375_, v_k_376_, v_fallback_377_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___boxed(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_t_383_, lean_object* v_k_384_, lean_object* v_fallback_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Std_DTreeMap_Internal_Impl_getD(v_00_u03b1_379_, v_00_u03b2_380_, v_inst_381_, v_inst_382_, v_t_383_, v_k_384_, v_fallback_385_);
lean_dec(v_fallback_385_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(lean_object* v_inst_387_, lean_object* v_t_388_, lean_object* v_k_389_){
_start:
{
if (lean_obj_tag(v_t_388_) == 0)
{
lean_object* v_k_390_; lean_object* v_v_391_; lean_object* v_l_392_; lean_object* v_r_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_k_390_ = lean_ctor_get(v_t_388_, 1);
lean_inc_n(v_k_390_, 2);
v_v_391_ = lean_ctor_get(v_t_388_, 2);
lean_inc(v_v_391_);
v_l_392_ = lean_ctor_get(v_t_388_, 3);
lean_inc(v_l_392_);
v_r_393_ = lean_ctor_get(v_t_388_, 4);
lean_inc(v_r_393_);
lean_dec_ref(v_t_388_);
lean_inc_ref(v_inst_387_);
lean_inc(v_k_389_);
v___x_394_ = lean_apply_2(v_inst_387_, v_k_389_, v_k_390_);
v___x_395_ = lean_unbox(v___x_394_);
switch(v___x_395_)
{
case 0:
{
lean_dec(v_r_393_);
lean_dec(v_v_391_);
lean_dec(v_k_390_);
v_t_388_ = v_l_392_;
goto _start;
}
case 1:
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v_r_393_);
lean_dec(v_l_392_);
lean_dec(v_k_389_);
lean_dec_ref(v_inst_387_);
v___x_397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_397_, 0, v_k_390_);
lean_ctor_set(v___x_397_, 1, v_v_391_);
v___x_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
return v___x_398_;
}
default: 
{
lean_dec(v_l_392_);
lean_dec(v_v_391_);
lean_dec(v_k_390_);
v_t_388_ = v_r_393_;
goto _start;
}
}
}
else
{
lean_object* v___x_400_; 
lean_dec(v_k_389_);
lean_dec_ref(v_inst_387_);
v___x_400_ = lean_box(0);
return v___x_400_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f(lean_object* v_00_u03b1_401_, lean_object* v_00_u03b2_402_, lean_object* v_inst_403_, lean_object* v_t_404_, lean_object* v_k_405_){
_start:
{
lean_object* v___x_406_; 
v___x_406_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_inst_403_, v_t_404_, v_k_405_);
return v___x_406_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry___redArg(lean_object* v_inst_407_, lean_object* v_t_408_, lean_object* v_k_409_){
_start:
{
lean_object* v_k_410_; lean_object* v_v_411_; lean_object* v_l_412_; lean_object* v_r_413_; lean_object* v___x_414_; uint8_t v___x_415_; 
v_k_410_ = lean_ctor_get(v_t_408_, 1);
lean_inc_n(v_k_410_, 2);
v_v_411_ = lean_ctor_get(v_t_408_, 2);
lean_inc(v_v_411_);
v_l_412_ = lean_ctor_get(v_t_408_, 3);
lean_inc(v_l_412_);
v_r_413_ = lean_ctor_get(v_t_408_, 4);
lean_inc(v_r_413_);
lean_dec(v_t_408_);
lean_inc_ref(v_inst_407_);
lean_inc(v_k_409_);
v___x_414_ = lean_apply_2(v_inst_407_, v_k_409_, v_k_410_);
v___x_415_ = lean_unbox(v___x_414_);
switch(v___x_415_)
{
case 0:
{
lean_dec(v_r_413_);
lean_dec(v_v_411_);
lean_dec(v_k_410_);
v_t_408_ = v_l_412_;
goto _start;
}
case 1:
{
lean_object* v___x_417_; 
lean_dec(v_r_413_);
lean_dec(v_l_412_);
lean_dec(v_k_409_);
lean_dec_ref(v_inst_407_);
v___x_417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_417_, 0, v_k_410_);
lean_ctor_set(v___x_417_, 1, v_v_411_);
return v___x_417_;
}
default: 
{
lean_dec(v_l_412_);
lean_dec(v_v_411_);
lean_dec(v_k_410_);
v_t_408_ = v_r_413_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry(lean_object* v_00_u03b1_419_, lean_object* v_00_u03b2_420_, lean_object* v_inst_421_, lean_object* v_t_422_, lean_object* v_k_423_, lean_object* v_hlk_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_inst_421_, v_t_422_, v_k_423_);
return v___x_425_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_427_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_428_ = lean_unsigned_to_nat(13u);
v___x_429_ = lean_unsigned_to_nat(147u);
v___x_430_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0));
v___x_431_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_432_ = l_mkPanicMessageWithDecl(v___x_431_, v___x_430_, v___x_429_, v___x_428_, v___x_427_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_t_435_, lean_object* v_k_436_){
_start:
{
if (lean_obj_tag(v_t_435_) == 0)
{
lean_object* v_k_437_; lean_object* v_v_438_; lean_object* v_l_439_; lean_object* v_r_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_k_437_ = lean_ctor_get(v_t_435_, 1);
lean_inc_n(v_k_437_, 2);
v_v_438_ = lean_ctor_get(v_t_435_, 2);
lean_inc(v_v_438_);
v_l_439_ = lean_ctor_get(v_t_435_, 3);
lean_inc(v_l_439_);
v_r_440_ = lean_ctor_get(v_t_435_, 4);
lean_inc(v_r_440_);
lean_dec_ref(v_t_435_);
lean_inc_ref(v_inst_433_);
lean_inc(v_k_436_);
v___x_441_ = lean_apply_2(v_inst_433_, v_k_436_, v_k_437_);
v___x_442_ = lean_unbox(v___x_441_);
switch(v___x_442_)
{
case 0:
{
lean_dec(v_r_440_);
lean_dec(v_v_438_);
lean_dec(v_k_437_);
v_t_435_ = v_l_439_;
goto _start;
}
case 1:
{
lean_object* v___x_444_; 
lean_dec(v_r_440_);
lean_dec(v_l_439_);
lean_dec(v_k_436_);
lean_dec_ref(v_inst_433_);
v___x_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_444_, 0, v_k_437_);
lean_ctor_set(v___x_444_, 1, v_v_438_);
return v___x_444_;
}
default: 
{
lean_dec(v_l_439_);
lean_dec(v_v_438_);
lean_dec(v_k_437_);
v_t_435_ = v_r_440_;
goto _start;
}
}
}
else
{
lean_object* v___x_446_; lean_object* v___x_447_; 
lean_dec(v_k_436_);
lean_dec_ref(v_inst_433_);
v___x_446_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1);
v___x_447_ = l_panic___redArg(v_inst_434_, v___x_446_);
return v___x_447_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___boxed(lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_t_450_, lean_object* v_k_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_inst_448_, v_inst_449_, v_t_450_, v_k_451_);
lean_dec_ref(v_inst_449_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21(lean_object* v_00_u03b1_453_, lean_object* v_00_u03b2_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_t_457_, lean_object* v_k_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_inst_455_, v_inst_456_, v_t_457_, v_k_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___boxed(lean_object* v_00_u03b1_460_, lean_object* v_00_u03b2_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_t_464_, lean_object* v_k_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21(v_00_u03b1_460_, v_00_u03b2_461_, v_inst_462_, v_inst_463_, v_t_464_, v_k_465_);
lean_dec_ref(v_inst_463_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(lean_object* v_inst_467_, lean_object* v_t_468_, lean_object* v_k_469_, lean_object* v_fallback_470_){
_start:
{
if (lean_obj_tag(v_t_468_) == 0)
{
lean_object* v_k_471_; lean_object* v_v_472_; lean_object* v_l_473_; lean_object* v_r_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_k_471_ = lean_ctor_get(v_t_468_, 1);
lean_inc_n(v_k_471_, 2);
v_v_472_ = lean_ctor_get(v_t_468_, 2);
lean_inc(v_v_472_);
v_l_473_ = lean_ctor_get(v_t_468_, 3);
lean_inc(v_l_473_);
v_r_474_ = lean_ctor_get(v_t_468_, 4);
lean_inc(v_r_474_);
lean_dec_ref(v_t_468_);
lean_inc_ref(v_inst_467_);
lean_inc(v_k_469_);
v___x_475_ = lean_apply_2(v_inst_467_, v_k_469_, v_k_471_);
v___x_476_ = lean_unbox(v___x_475_);
switch(v___x_476_)
{
case 0:
{
lean_dec(v_r_474_);
lean_dec(v_v_472_);
lean_dec(v_k_471_);
v_t_468_ = v_l_473_;
goto _start;
}
case 1:
{
lean_object* v___x_478_; 
lean_dec(v_r_474_);
lean_dec(v_l_473_);
lean_dec(v_k_469_);
lean_dec_ref(v_inst_467_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_k_471_);
lean_ctor_set(v___x_478_, 1, v_v_472_);
return v___x_478_;
}
default: 
{
lean_dec(v_l_473_);
lean_dec(v_v_472_);
lean_dec(v_k_471_);
v_t_468_ = v_r_474_;
goto _start;
}
}
}
else
{
lean_dec(v_k_469_);
lean_dec_ref(v_inst_467_);
lean_inc_ref(v_fallback_470_);
return v_fallback_470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg___boxed(lean_object* v_inst_480_, lean_object* v_t_481_, lean_object* v_k_482_, lean_object* v_fallback_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_480_, v_t_481_, v_k_482_, v_fallback_483_);
lean_dec_ref(v_fallback_483_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_inst_487_, lean_object* v_t_488_, lean_object* v_k_489_, lean_object* v_fallback_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_487_, v_t_488_, v_k_489_, v_fallback_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___boxed(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_inst_494_, lean_object* v_t_495_, lean_object* v_k_496_, lean_object* v_fallback_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Std_DTreeMap_Internal_Impl_getEntryD(v_00_u03b1_492_, v_00_u03b2_493_, v_inst_494_, v_t_495_, v_k_496_, v_fallback_497_);
lean_dec_ref(v_fallback_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object* v_inst_499_, lean_object* v_t_500_, lean_object* v_k_501_){
_start:
{
if (lean_obj_tag(v_t_500_) == 0)
{
lean_object* v_k_502_; lean_object* v_l_503_; lean_object* v_r_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_k_502_ = lean_ctor_get(v_t_500_, 1);
lean_inc_n(v_k_502_, 2);
v_l_503_ = lean_ctor_get(v_t_500_, 3);
lean_inc(v_l_503_);
v_r_504_ = lean_ctor_get(v_t_500_, 4);
lean_inc(v_r_504_);
lean_dec_ref(v_t_500_);
lean_inc_ref(v_inst_499_);
lean_inc(v_k_501_);
v___x_505_ = lean_apply_2(v_inst_499_, v_k_501_, v_k_502_);
v___x_506_ = lean_unbox(v___x_505_);
switch(v___x_506_)
{
case 0:
{
lean_dec(v_r_504_);
lean_dec(v_k_502_);
v_t_500_ = v_l_503_;
goto _start;
}
case 1:
{
lean_object* v___x_508_; 
lean_dec(v_r_504_);
lean_dec(v_l_503_);
lean_dec(v_k_501_);
lean_dec_ref(v_inst_499_);
v___x_508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_508_, 0, v_k_502_);
return v___x_508_;
}
default: 
{
lean_dec(v_l_503_);
lean_dec(v_k_502_);
v_t_500_ = v_r_504_;
goto _start;
}
}
}
else
{
lean_object* v___x_510_; 
lean_dec(v_k_501_);
lean_dec_ref(v_inst_499_);
v___x_510_ = lean_box(0);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f(lean_object* v_00_u03b1_511_, lean_object* v_00_u03b2_512_, lean_object* v_inst_513_, lean_object* v_t_514_, lean_object* v_k_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_inst_513_, v_t_514_, v_k_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object* v_inst_517_, lean_object* v_t_518_, lean_object* v_k_519_){
_start:
{
lean_object* v_k_520_; lean_object* v_l_521_; lean_object* v_r_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v_k_520_ = lean_ctor_get(v_t_518_, 1);
lean_inc_n(v_k_520_, 2);
v_l_521_ = lean_ctor_get(v_t_518_, 3);
lean_inc(v_l_521_);
v_r_522_ = lean_ctor_get(v_t_518_, 4);
lean_inc(v_r_522_);
lean_dec(v_t_518_);
lean_inc_ref(v_inst_517_);
lean_inc(v_k_519_);
v___x_523_ = lean_apply_2(v_inst_517_, v_k_519_, v_k_520_);
v___x_524_ = lean_unbox(v___x_523_);
switch(v___x_524_)
{
case 0:
{
lean_dec(v_r_522_);
lean_dec(v_k_520_);
v_t_518_ = v_l_521_;
goto _start;
}
case 1:
{
lean_dec(v_r_522_);
lean_dec(v_l_521_);
lean_dec(v_k_519_);
lean_dec_ref(v_inst_517_);
return v_k_520_;
}
default: 
{
lean_dec(v_l_521_);
lean_dec(v_k_520_);
v_t_518_ = v_r_522_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey(lean_object* v_00_u03b1_527_, lean_object* v_00_u03b2_528_, lean_object* v_inst_529_, lean_object* v_t_530_, lean_object* v_k_531_, lean_object* v_hlk_532_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_inst_529_, v_t_530_, v_k_531_);
return v___x_533_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_535_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_536_ = lean_unsigned_to_nat(13u);
v___x_537_ = lean_unsigned_to_nat(186u);
v___x_538_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0));
v___x_539_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_540_ = l_mkPanicMessageWithDecl(v___x_539_, v___x_538_, v___x_537_, v___x_536_, v___x_535_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object* v_inst_541_, lean_object* v_t_542_, lean_object* v_k_543_, lean_object* v_inst_544_){
_start:
{
if (lean_obj_tag(v_t_542_) == 0)
{
lean_object* v_k_545_; lean_object* v_l_546_; lean_object* v_r_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v_k_545_ = lean_ctor_get(v_t_542_, 1);
lean_inc_n(v_k_545_, 2);
v_l_546_ = lean_ctor_get(v_t_542_, 3);
lean_inc(v_l_546_);
v_r_547_ = lean_ctor_get(v_t_542_, 4);
lean_inc(v_r_547_);
lean_dec_ref(v_t_542_);
lean_inc_ref(v_inst_541_);
lean_inc(v_k_543_);
v___x_548_ = lean_apply_2(v_inst_541_, v_k_543_, v_k_545_);
v___x_549_ = lean_unbox(v___x_548_);
switch(v___x_549_)
{
case 0:
{
lean_dec(v_r_547_);
lean_dec(v_k_545_);
v_t_542_ = v_l_546_;
goto _start;
}
case 1:
{
lean_dec(v_r_547_);
lean_dec(v_l_546_);
lean_dec(v_k_543_);
lean_dec_ref(v_inst_541_);
return v_k_545_;
}
default: 
{
lean_dec(v_l_546_);
lean_dec(v_k_545_);
v_t_542_ = v_r_547_;
goto _start;
}
}
}
else
{
lean_object* v___x_552_; lean_object* v___x_553_; 
lean_dec(v_k_543_);
lean_dec_ref(v_inst_541_);
v___x_552_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1);
v___x_553_ = l_panic___redArg(v_inst_544_, v___x_552_);
return v___x_553_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___boxed(lean_object* v_inst_554_, lean_object* v_t_555_, lean_object* v_k_556_, lean_object* v_inst_557_){
_start:
{
lean_object* v_res_558_; 
v_res_558_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_inst_554_, v_t_555_, v_k_556_, v_inst_557_);
lean_dec(v_inst_557_);
return v_res_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21(lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_, lean_object* v_inst_561_, lean_object* v_t_562_, lean_object* v_k_563_, lean_object* v_inst_564_){
_start:
{
lean_object* v___x_565_; 
v___x_565_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_inst_561_, v_t_562_, v_k_563_, v_inst_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___boxed(lean_object* v_00_u03b1_566_, lean_object* v_00_u03b2_567_, lean_object* v_inst_568_, lean_object* v_t_569_, lean_object* v_k_570_, lean_object* v_inst_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_DTreeMap_Internal_Impl_getKey_x21(v_00_u03b1_566_, v_00_u03b2_567_, v_inst_568_, v_t_569_, v_k_570_, v_inst_571_);
lean_dec(v_inst_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object* v_inst_573_, lean_object* v_t_574_, lean_object* v_k_575_, lean_object* v_fallback_576_){
_start:
{
if (lean_obj_tag(v_t_574_) == 0)
{
lean_object* v_k_577_; lean_object* v_l_578_; lean_object* v_r_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_k_577_ = lean_ctor_get(v_t_574_, 1);
lean_inc_n(v_k_577_, 2);
v_l_578_ = lean_ctor_get(v_t_574_, 3);
lean_inc(v_l_578_);
v_r_579_ = lean_ctor_get(v_t_574_, 4);
lean_inc(v_r_579_);
lean_dec_ref(v_t_574_);
lean_inc_ref(v_inst_573_);
lean_inc(v_k_575_);
v___x_580_ = lean_apply_2(v_inst_573_, v_k_575_, v_k_577_);
v___x_581_ = lean_unbox(v___x_580_);
switch(v___x_581_)
{
case 0:
{
lean_dec(v_r_579_);
lean_dec(v_k_577_);
v_t_574_ = v_l_578_;
goto _start;
}
case 1:
{
lean_dec(v_r_579_);
lean_dec(v_l_578_);
lean_dec(v_k_575_);
lean_dec_ref(v_inst_573_);
return v_k_577_;
}
default: 
{
lean_dec(v_l_578_);
lean_dec(v_k_577_);
v_t_574_ = v_r_579_;
goto _start;
}
}
}
else
{
lean_dec(v_k_575_);
lean_dec_ref(v_inst_573_);
lean_inc(v_fallback_576_);
return v_fallback_576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg___boxed(lean_object* v_inst_584_, lean_object* v_t_585_, lean_object* v_k_586_, lean_object* v_fallback_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_584_, v_t_585_, v_k_586_, v_fallback_587_);
lean_dec(v_fallback_587_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD(lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_, lean_object* v_inst_591_, lean_object* v_t_592_, lean_object* v_k_593_, lean_object* v_fallback_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_591_, v_t_592_, v_k_593_, v_fallback_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___boxed(lean_object* v_00_u03b1_596_, lean_object* v_00_u03b2_597_, lean_object* v_inst_598_, lean_object* v_t_599_, lean_object* v_k_600_, lean_object* v_fallback_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Std_DTreeMap_Internal_Impl_getKeyD(v_00_u03b1_596_, v_00_u03b2_597_, v_inst_598_, v_t_599_, v_k_600_, v_fallback_601_);
lean_dec(v_fallback_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object* v_inst_603_, lean_object* v_t_604_, lean_object* v_k_605_){
_start:
{
if (lean_obj_tag(v_t_604_) == 0)
{
lean_object* v_k_606_; lean_object* v_v_607_; lean_object* v_l_608_; lean_object* v_r_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_k_606_ = lean_ctor_get(v_t_604_, 1);
lean_inc(v_k_606_);
v_v_607_ = lean_ctor_get(v_t_604_, 2);
lean_inc(v_v_607_);
v_l_608_ = lean_ctor_get(v_t_604_, 3);
lean_inc(v_l_608_);
v_r_609_ = lean_ctor_get(v_t_604_, 4);
lean_inc(v_r_609_);
lean_dec_ref(v_t_604_);
lean_inc_ref(v_inst_603_);
lean_inc(v_k_605_);
v___x_610_ = lean_apply_2(v_inst_603_, v_k_605_, v_k_606_);
v___x_611_ = lean_unbox(v___x_610_);
switch(v___x_611_)
{
case 0:
{
lean_dec(v_r_609_);
lean_dec(v_v_607_);
v_t_604_ = v_l_608_;
goto _start;
}
case 1:
{
lean_object* v___x_613_; 
lean_dec(v_r_609_);
lean_dec(v_l_608_);
lean_dec(v_k_605_);
lean_dec_ref(v_inst_603_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_v_607_);
return v___x_613_;
}
default: 
{
lean_dec(v_l_608_);
lean_dec(v_v_607_);
v_t_604_ = v_r_609_;
goto _start;
}
}
}
else
{
lean_object* v___x_615_; 
lean_dec(v_k_605_);
lean_dec_ref(v_inst_603_);
v___x_615_ = lean_box(0);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f(lean_object* v_00_u03b1_616_, lean_object* v_00_u03b4_617_, lean_object* v_inst_618_, lean_object* v_t_619_, lean_object* v_k_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_inst_618_, v_t_619_, v_k_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object* v_inst_622_, lean_object* v_t_623_, lean_object* v_k_624_){
_start:
{
lean_object* v_k_625_; lean_object* v_v_626_; lean_object* v_l_627_; lean_object* v_r_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_k_625_ = lean_ctor_get(v_t_623_, 1);
lean_inc(v_k_625_);
v_v_626_ = lean_ctor_get(v_t_623_, 2);
lean_inc(v_v_626_);
v_l_627_ = lean_ctor_get(v_t_623_, 3);
lean_inc(v_l_627_);
v_r_628_ = lean_ctor_get(v_t_623_, 4);
lean_inc(v_r_628_);
lean_dec(v_t_623_);
lean_inc_ref(v_inst_622_);
lean_inc(v_k_624_);
v___x_629_ = lean_apply_2(v_inst_622_, v_k_624_, v_k_625_);
v___x_630_ = lean_unbox(v___x_629_);
switch(v___x_630_)
{
case 0:
{
lean_dec(v_r_628_);
lean_dec(v_v_626_);
v_t_623_ = v_l_627_;
goto _start;
}
case 1:
{
lean_dec(v_r_628_);
lean_dec(v_l_627_);
lean_dec(v_k_624_);
lean_dec_ref(v_inst_622_);
return v_v_626_;
}
default: 
{
lean_dec(v_l_627_);
lean_dec(v_v_626_);
v_t_623_ = v_r_628_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get(lean_object* v_00_u03b1_633_, lean_object* v_00_u03b4_634_, lean_object* v_inst_635_, lean_object* v_t_636_, lean_object* v_k_637_, lean_object* v_hlk_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_inst_635_, v_t_636_, v_k_637_);
return v___x_639_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_641_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_642_ = lean_unsigned_to_nat(13u);
v___x_643_ = lean_unsigned_to_nat(227u);
v___x_644_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0));
v___x_645_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_646_ = l_mkPanicMessageWithDecl(v___x_645_, v___x_644_, v___x_643_, v___x_642_, v___x_641_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object* v_inst_647_, lean_object* v_inst_648_, lean_object* v_t_649_, lean_object* v_k_650_){
_start:
{
if (lean_obj_tag(v_t_649_) == 0)
{
lean_object* v_k_651_; lean_object* v_v_652_; lean_object* v_l_653_; lean_object* v_r_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v_k_651_ = lean_ctor_get(v_t_649_, 1);
lean_inc(v_k_651_);
v_v_652_ = lean_ctor_get(v_t_649_, 2);
lean_inc(v_v_652_);
v_l_653_ = lean_ctor_get(v_t_649_, 3);
lean_inc(v_l_653_);
v_r_654_ = lean_ctor_get(v_t_649_, 4);
lean_inc(v_r_654_);
lean_dec_ref(v_t_649_);
lean_inc_ref(v_inst_647_);
lean_inc(v_k_650_);
v___x_655_ = lean_apply_2(v_inst_647_, v_k_650_, v_k_651_);
v___x_656_ = lean_unbox(v___x_655_);
switch(v___x_656_)
{
case 0:
{
lean_dec(v_r_654_);
lean_dec(v_v_652_);
v_t_649_ = v_l_653_;
goto _start;
}
case 1:
{
lean_dec(v_r_654_);
lean_dec(v_l_653_);
lean_dec(v_k_650_);
lean_dec_ref(v_inst_647_);
return v_v_652_;
}
default: 
{
lean_dec(v_l_653_);
lean_dec(v_v_652_);
v_t_649_ = v_r_654_;
goto _start;
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec(v_k_650_);
lean_dec_ref(v_inst_647_);
v___x_659_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1);
v___x_660_ = l_panic___redArg(v_inst_648_, v___x_659_);
return v___x_660_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___boxed(lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_t_663_, lean_object* v_k_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_inst_661_, v_inst_662_, v_t_663_, v_k_664_);
lean_dec(v_inst_662_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b4_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_t_670_, lean_object* v_k_671_){
_start:
{
lean_object* v___x_672_; 
v___x_672_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_inst_668_, v_inst_669_, v_t_670_, v_k_671_);
return v___x_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___boxed(lean_object* v_00_u03b1_673_, lean_object* v_00_u03b4_674_, lean_object* v_inst_675_, lean_object* v_inst_676_, lean_object* v_t_677_, lean_object* v_k_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21(v_00_u03b1_673_, v_00_u03b4_674_, v_inst_675_, v_inst_676_, v_t_677_, v_k_678_);
lean_dec(v_inst_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object* v_inst_680_, lean_object* v_t_681_, lean_object* v_k_682_, lean_object* v_fallback_683_){
_start:
{
if (lean_obj_tag(v_t_681_) == 0)
{
lean_object* v_k_684_; lean_object* v_v_685_; lean_object* v_l_686_; lean_object* v_r_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_k_684_ = lean_ctor_get(v_t_681_, 1);
lean_inc(v_k_684_);
v_v_685_ = lean_ctor_get(v_t_681_, 2);
lean_inc(v_v_685_);
v_l_686_ = lean_ctor_get(v_t_681_, 3);
lean_inc(v_l_686_);
v_r_687_ = lean_ctor_get(v_t_681_, 4);
lean_inc(v_r_687_);
lean_dec_ref(v_t_681_);
lean_inc_ref(v_inst_680_);
lean_inc(v_k_682_);
v___x_688_ = lean_apply_2(v_inst_680_, v_k_682_, v_k_684_);
v___x_689_ = lean_unbox(v___x_688_);
switch(v___x_689_)
{
case 0:
{
lean_dec(v_r_687_);
lean_dec(v_v_685_);
v_t_681_ = v_l_686_;
goto _start;
}
case 1:
{
lean_dec(v_r_687_);
lean_dec(v_l_686_);
lean_dec(v_k_682_);
lean_dec_ref(v_inst_680_);
return v_v_685_;
}
default: 
{
lean_dec(v_l_686_);
lean_dec(v_v_685_);
v_t_681_ = v_r_687_;
goto _start;
}
}
}
else
{
lean_dec(v_k_682_);
lean_dec_ref(v_inst_680_);
lean_inc(v_fallback_683_);
return v_fallback_683_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg___boxed(lean_object* v_inst_692_, lean_object* v_t_693_, lean_object* v_k_694_, lean_object* v_fallback_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_692_, v_t_693_, v_k_694_, v_fallback_695_);
lean_dec(v_fallback_695_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD(lean_object* v_00_u03b1_697_, lean_object* v_00_u03b4_698_, lean_object* v_inst_699_, lean_object* v_t_700_, lean_object* v_k_701_, lean_object* v_fallback_702_){
_start:
{
lean_object* v___x_703_; 
v___x_703_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_699_, v_t_700_, v_k_701_, v_fallback_702_);
return v___x_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___boxed(lean_object* v_00_u03b1_704_, lean_object* v_00_u03b4_705_, lean_object* v_inst_706_, lean_object* v_t_707_, lean_object* v_k_708_, lean_object* v_fallback_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_Std_DTreeMap_Internal_Impl_Const_getD(v_00_u03b1_704_, v_00_u03b4_705_, v_inst_706_, v_t_707_, v_k_708_, v_fallback_709_);
lean_dec(v_fallback_709_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1(lean_object* v_f_711_, lean_object* v_k_712_, lean_object* v_v_713_, lean_object* v_toBind_714_, lean_object* v___f_715_, lean_object* v_left_716_){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = lean_apply_3(v_f_711_, v_left_716_, v_k_712_, v_v_713_);
v___x_718_ = lean_apply_4(v_toBind_714_, lean_box(0), lean_box(0), v___x_717_, v___f_715_);
return v___x_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object* v_inst_719_, lean_object* v_f_720_, lean_object* v_init_721_, lean_object* v_x_722_){
_start:
{
if (lean_obj_tag(v_x_722_) == 0)
{
lean_object* v_toBind_723_; lean_object* v_k_724_; lean_object* v_v_725_; lean_object* v_l_726_; lean_object* v_r_727_; lean_object* v___f_728_; lean_object* v___f_729_; lean_object* v___x_730_; lean_object* v___x_731_; 
v_toBind_723_ = lean_ctor_get(v_inst_719_, 1);
lean_inc_n(v_toBind_723_, 2);
v_k_724_ = lean_ctor_get(v_x_722_, 1);
lean_inc(v_k_724_);
v_v_725_ = lean_ctor_get(v_x_722_, 2);
lean_inc(v_v_725_);
v_l_726_ = lean_ctor_get(v_x_722_, 3);
lean_inc(v_l_726_);
v_r_727_ = lean_ctor_get(v_x_722_, 4);
lean_inc(v_r_727_);
lean_dec_ref(v_x_722_);
lean_inc_n(v_f_720_, 2);
lean_inc_ref(v_inst_719_);
v___f_728_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_728_, 0, v_inst_719_);
lean_closure_set(v___f_728_, 1, v_f_720_);
lean_closure_set(v___f_728_, 2, v_r_727_);
v___f_729_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_729_, 0, v_f_720_);
lean_closure_set(v___f_729_, 1, v_k_724_);
lean_closure_set(v___f_729_, 2, v_v_725_);
lean_closure_set(v___f_729_, 3, v_toBind_723_);
lean_closure_set(v___f_729_, 4, v___f_728_);
v___x_730_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_719_, v_f_720_, v_init_721_, v_l_726_);
v___x_731_ = lean_apply_4(v_toBind_723_, lean_box(0), lean_box(0), v___x_730_, v___f_729_);
return v___x_731_;
}
else
{
lean_object* v_toApplicative_732_; lean_object* v_toPure_733_; lean_object* v___x_734_; 
v_toApplicative_732_ = lean_ctor_get(v_inst_719_, 0);
lean_inc_ref(v_toApplicative_732_);
lean_dec(v_f_720_);
lean_dec_ref(v_inst_719_);
v_toPure_733_ = lean_ctor_get(v_toApplicative_732_, 1);
lean_inc(v_toPure_733_);
lean_dec_ref(v_toApplicative_732_);
v___x_734_ = lean_apply_2(v_toPure_733_, lean_box(0), v_init_721_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0(lean_object* v_inst_735_, lean_object* v_f_736_, lean_object* v_r_737_, lean_object* v_middle_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_735_, v_f_736_, v_middle_738_, v_r_737_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM(lean_object* v_00_u03b1_740_, lean_object* v_00_u03b2_741_, lean_object* v_00_u03b4_742_, lean_object* v_m_743_, lean_object* v_inst_744_, lean_object* v_f_745_, lean_object* v_init_746_, lean_object* v_x_747_){
_start:
{
lean_object* v___x_748_; 
v___x_748_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_744_, v_f_745_, v_init_746_, v_x_747_);
return v___x_748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0(lean_object* v_f_749_, lean_object* v_x1_750_, lean_object* v_x2_751_, lean_object* v_x3_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = lean_apply_3(v_f_749_, v_x1_750_, v_x2_751_, v_x3_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object* v_f_773_, lean_object* v_init_774_, lean_object* v_t_775_){
_start:
{
lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___f_776_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_776_, 0, v_f_773_);
v___x_777_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_778_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_777_, v___f_776_, v_init_774_, v_t_775_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl(lean_object* v_00_u03b1_779_, lean_object* v_00_u03b2_780_, lean_object* v_00_u03b4_781_, lean_object* v_f_782_, lean_object* v_init_783_, lean_object* v_t_784_){
_start:
{
lean_object* v___x_785_; 
v___x_785_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_782_, v_init_783_, v_t_784_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1(lean_object* v_f_786_, lean_object* v_k_787_, lean_object* v_v_788_, lean_object* v_toBind_789_, lean_object* v___f_790_, lean_object* v_right_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; 
v___x_792_ = lean_apply_3(v_f_786_, v_k_787_, v_v_788_, v_right_791_);
v___x_793_ = lean_apply_4(v_toBind_789_, lean_box(0), lean_box(0), v___x_792_, v___f_790_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object* v_inst_794_, lean_object* v_f_795_, lean_object* v_init_796_, lean_object* v_x_797_){
_start:
{
if (lean_obj_tag(v_x_797_) == 0)
{
lean_object* v_toBind_798_; lean_object* v_k_799_; lean_object* v_v_800_; lean_object* v_l_801_; lean_object* v_r_802_; lean_object* v___f_803_; lean_object* v___f_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v_toBind_798_ = lean_ctor_get(v_inst_794_, 1);
lean_inc_n(v_toBind_798_, 2);
v_k_799_ = lean_ctor_get(v_x_797_, 1);
lean_inc(v_k_799_);
v_v_800_ = lean_ctor_get(v_x_797_, 2);
lean_inc(v_v_800_);
v_l_801_ = lean_ctor_get(v_x_797_, 3);
lean_inc(v_l_801_);
v_r_802_ = lean_ctor_get(v_x_797_, 4);
lean_inc(v_r_802_);
lean_dec_ref(v_x_797_);
lean_inc_n(v_f_795_, 2);
lean_inc_ref(v_inst_794_);
v___f_803_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_803_, 0, v_inst_794_);
lean_closure_set(v___f_803_, 1, v_f_795_);
lean_closure_set(v___f_803_, 2, v_l_801_);
v___f_804_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_804_, 0, v_f_795_);
lean_closure_set(v___f_804_, 1, v_k_799_);
lean_closure_set(v___f_804_, 2, v_v_800_);
lean_closure_set(v___f_804_, 3, v_toBind_798_);
lean_closure_set(v___f_804_, 4, v___f_803_);
v___x_805_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_794_, v_f_795_, v_init_796_, v_r_802_);
v___x_806_ = lean_apply_4(v_toBind_798_, lean_box(0), lean_box(0), v___x_805_, v___f_804_);
return v___x_806_;
}
else
{
lean_object* v_toApplicative_807_; lean_object* v_toPure_808_; lean_object* v___x_809_; 
v_toApplicative_807_ = lean_ctor_get(v_inst_794_, 0);
lean_inc_ref(v_toApplicative_807_);
lean_dec(v_f_795_);
lean_dec_ref(v_inst_794_);
v_toPure_808_ = lean_ctor_get(v_toApplicative_807_, 1);
lean_inc(v_toPure_808_);
lean_dec_ref(v_toApplicative_807_);
v___x_809_ = lean_apply_2(v_toPure_808_, lean_box(0), v_init_796_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0(lean_object* v_inst_810_, lean_object* v_f_811_, lean_object* v_l_812_, lean_object* v_middle_813_){
_start:
{
lean_object* v___x_814_; 
v___x_814_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_810_, v_f_811_, v_middle_813_, v_l_812_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM(lean_object* v_00_u03b1_815_, lean_object* v_00_u03b2_816_, lean_object* v_00_u03b4_817_, lean_object* v_m_818_, lean_object* v_inst_819_, lean_object* v_f_820_, lean_object* v_init_821_, lean_object* v_x_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_819_, v_f_820_, v_init_821_, v_x_822_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr___redArg(lean_object* v_f_824_, lean_object* v_init_825_, lean_object* v_t_826_){
_start:
{
lean_object* v___f_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___f_827_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_827_, 0, v_f_824_);
v___x_828_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_829_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_828_, v___f_827_, v_init_825_, v_t_826_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr(lean_object* v_00_u03b1_830_, lean_object* v_00_u03b2_831_, lean_object* v_00_u03b4_832_, lean_object* v_f_833_, lean_object* v_init_834_, lean_object* v_t_835_){
_start:
{
lean_object* v___f_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___f_836_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_836_, 0, v_f_833_);
v___x_837_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_838_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_837_, v___f_836_, v_init_834_, v_t_835_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0(lean_object* v_f_839_, lean_object* v_x_840_, lean_object* v_k_841_, lean_object* v_v_842_){
_start:
{
lean_object* v___x_843_; 
v___x_843_ = lean_apply_2(v_f_839_, v_k_841_, v_v_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg(lean_object* v_inst_844_, lean_object* v_f_845_, lean_object* v_t_846_){
_start:
{
lean_object* v___f_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___f_847_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_847_, 0, v_f_845_);
v___x_848_ = lean_box(0);
v___x_849_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_844_, v___f_847_, v___x_848_, v_t_846_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM(lean_object* v_00_u03b1_850_, lean_object* v_00_u03b2_851_, lean_object* v_m_852_, lean_object* v_inst_853_, lean_object* v_f_854_, lean_object* v_t_855_){
_start:
{
lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___f_856_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_856_, 0, v_f_854_);
v___x_857_ = lean_box(0);
v___x_858_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_853_, v___f_856_, v___x_857_, v_t_855_);
return v___x_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0(lean_object* v_toPure_859_, lean_object* v_d_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_861_, 0, v_d_860_);
v___x_862_ = lean_apply_2(v_toPure_859_, lean_box(0), v___x_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2(lean_object* v___f_863_, lean_object* v_f_864_, lean_object* v_k_865_, lean_object* v_v_866_, lean_object* v_toBind_867_, lean_object* v___f_868_, lean_object* v_____do__lift_869_){
_start:
{
if (lean_obj_tag(v_____do__lift_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; 
lean_dec(v___f_868_);
lean_dec(v_toBind_867_);
lean_dec(v_v_866_);
lean_dec(v_k_865_);
lean_dec(v_f_864_);
v_a_870_ = lean_ctor_get(v_____do__lift_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref(v_____do__lift_869_);
v___x_871_ = lean_apply_1(v___f_863_, v_a_870_);
return v___x_871_;
}
else
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec(v___f_863_);
v_a_872_ = lean_ctor_get(v_____do__lift_869_, 0);
lean_inc(v_a_872_);
lean_dec_ref(v_____do__lift_869_);
v___x_873_ = lean_apply_3(v_f_864_, v_k_865_, v_v_866_, v_a_872_);
v___x_874_ = lean_apply_4(v_toBind_867_, lean_box(0), lean_box(0), v___x_873_, v___f_868_);
return v___x_874_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object* v_inst_875_, lean_object* v_f_876_, lean_object* v_init_877_, lean_object* v_x_878_){
_start:
{
if (lean_obj_tag(v_x_878_) == 0)
{
lean_object* v_toApplicative_879_; lean_object* v_toBind_880_; lean_object* v_toPure_881_; lean_object* v_k_882_; lean_object* v_v_883_; lean_object* v_l_884_; lean_object* v_r_885_; lean_object* v___f_886_; lean_object* v___f_887_; lean_object* v___f_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v_toApplicative_879_ = lean_ctor_get(v_inst_875_, 0);
v_toBind_880_ = lean_ctor_get(v_inst_875_, 1);
lean_inc_n(v_toBind_880_, 2);
v_toPure_881_ = lean_ctor_get(v_toApplicative_879_, 1);
v_k_882_ = lean_ctor_get(v_x_878_, 1);
lean_inc(v_k_882_);
v_v_883_ = lean_ctor_get(v_x_878_, 2);
lean_inc(v_v_883_);
v_l_884_ = lean_ctor_get(v_x_878_, 3);
lean_inc(v_l_884_);
v_r_885_ = lean_ctor_get(v_x_878_, 4);
lean_inc(v_r_885_);
lean_dec_ref(v_x_878_);
lean_inc(v_toPure_881_);
v___f_886_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0), 2, 1);
lean_closure_set(v___f_886_, 0, v_toPure_881_);
lean_inc_n(v_f_876_, 2);
lean_inc_ref(v_inst_875_);
lean_inc_ref(v___f_886_);
v___f_887_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1), 5, 4);
lean_closure_set(v___f_887_, 0, v___f_886_);
lean_closure_set(v___f_887_, 1, v_inst_875_);
lean_closure_set(v___f_887_, 2, v_f_876_);
lean_closure_set(v___f_887_, 3, v_r_885_);
v___f_888_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2), 7, 6);
lean_closure_set(v___f_888_, 0, v___f_886_);
lean_closure_set(v___f_888_, 1, v_f_876_);
lean_closure_set(v___f_888_, 2, v_k_882_);
lean_closure_set(v___f_888_, 3, v_v_883_);
lean_closure_set(v___f_888_, 4, v_toBind_880_);
lean_closure_set(v___f_888_, 5, v___f_887_);
v___x_889_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_875_, v_f_876_, v_init_877_, v_l_884_);
v___x_890_ = lean_apply_4(v_toBind_880_, lean_box(0), lean_box(0), v___x_889_, v___f_888_);
return v___x_890_;
}
else
{
lean_object* v_toApplicative_891_; lean_object* v_toPure_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v_toApplicative_891_ = lean_ctor_get(v_inst_875_, 0);
lean_inc_ref(v_toApplicative_891_);
lean_dec(v_f_876_);
lean_dec_ref(v_inst_875_);
v_toPure_892_ = lean_ctor_get(v_toApplicative_891_, 1);
lean_inc(v_toPure_892_);
lean_dec_ref(v_toApplicative_891_);
v___x_893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_893_, 0, v_init_877_);
v___x_894_ = lean_apply_2(v_toPure_892_, lean_box(0), v___x_893_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1(lean_object* v___f_895_, lean_object* v_inst_896_, lean_object* v_f_897_, lean_object* v_r_898_, lean_object* v_____do__lift_899_){
_start:
{
if (lean_obj_tag(v_____do__lift_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; 
lean_dec(v_r_898_);
lean_dec(v_f_897_);
lean_dec_ref(v_inst_896_);
v_a_900_ = lean_ctor_get(v_____do__lift_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref(v_____do__lift_899_);
v___x_901_ = lean_apply_1(v___f_895_, v_a_900_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; lean_object* v___x_903_; 
lean_dec(v___f_895_);
v_a_902_ = lean_ctor_get(v_____do__lift_899_, 0);
lean_inc(v_a_902_);
lean_dec_ref(v_____do__lift_899_);
v___x_903_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_896_, v_f_897_, v_a_902_, v_r_898_);
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep(lean_object* v_00_u03b1_904_, lean_object* v_00_u03b2_905_, lean_object* v_00_u03b4_906_, lean_object* v_m_907_, lean_object* v_inst_908_, lean_object* v_f_909_, lean_object* v_init_910_, lean_object* v_x_911_){
_start:
{
lean_object* v___x_912_; 
v___x_912_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_908_, v_f_909_, v_init_910_, v_x_911_);
return v___x_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0(lean_object* v_toPure_913_, lean_object* v_____do__lift_914_){
_start:
{
lean_object* v_a_915_; lean_object* v___x_916_; 
v_a_915_ = lean_ctor_get(v_____do__lift_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref(v_____do__lift_914_);
v___x_916_ = lean_apply_2(v_toPure_913_, lean_box(0), v_a_915_);
return v___x_916_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg(lean_object* v_inst_917_, lean_object* v_f_918_, lean_object* v_init_919_, lean_object* v_t_920_){
_start:
{
lean_object* v_toApplicative_921_; lean_object* v_toBind_922_; lean_object* v_toPure_923_; lean_object* v___x_924_; lean_object* v___f_925_; lean_object* v___x_926_; 
v_toApplicative_921_ = lean_ctor_get(v_inst_917_, 0);
v_toBind_922_ = lean_ctor_get(v_inst_917_, 1);
lean_inc(v_toBind_922_);
v_toPure_923_ = lean_ctor_get(v_toApplicative_921_, 1);
lean_inc(v_toPure_923_);
v___x_924_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_917_, v_f_918_, v_init_919_, v_t_920_);
v___f_925_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_925_, 0, v_toPure_923_);
v___x_926_ = lean_apply_4(v_toBind_922_, lean_box(0), lean_box(0), v___x_924_, v___f_925_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn(lean_object* v_00_u03b1_927_, lean_object* v_00_u03b2_928_, lean_object* v_00_u03b4_929_, lean_object* v_m_930_, lean_object* v_inst_931_, lean_object* v_f_932_, lean_object* v_init_933_, lean_object* v_t_934_){
_start:
{
lean_object* v_toApplicative_935_; lean_object* v_toBind_936_; lean_object* v_toPure_937_; lean_object* v___x_938_; lean_object* v___f_939_; lean_object* v___x_940_; 
v_toApplicative_935_ = lean_ctor_get(v_inst_931_, 0);
v_toBind_936_ = lean_ctor_get(v_inst_931_, 1);
lean_inc(v_toBind_936_);
v_toPure_937_ = lean_ctor_get(v_toApplicative_935_, 1);
lean_inc(v_toPure_937_);
v___x_938_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_931_, v_f_932_, v_init_933_, v_t_934_);
v___f_939_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_939_, 0, v_toPure_937_);
v___x_940_ = lean_apply_4(v_toBind_936_, lean_box(0), lean_box(0), v___x_938_, v___f_939_);
return v___x_940_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_941_, lean_object* v_a_942_, lean_object* v_b_943_, lean_object* v_acc_944_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_a_942_);
lean_ctor_set(v___x_945_, 1, v_b_943_);
v___x_946_ = lean_apply_2(v_f_941_, v___x_945_, v_acc_944_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_947_, lean_object* v_00_u03b2_948_, lean_object* v_m_949_, lean_object* v_init_950_, lean_object* v_f_951_){
_start:
{
lean_object* v_toApplicative_952_; lean_object* v_toBind_953_; lean_object* v_toPure_954_; lean_object* v___f_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___x_958_; 
v_toApplicative_952_ = lean_ctor_get(v_inst_947_, 0);
v_toBind_953_ = lean_ctor_get(v_inst_947_, 1);
lean_inc(v_toBind_953_);
v_toPure_954_ = lean_ctor_get(v_toApplicative_952_, 1);
lean_inc(v_toPure_954_);
v___f_955_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_955_, 0, v_f_951_);
v___x_956_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_947_, v___f_955_, v_init_950_, v_m_949_);
v___f_957_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_957_, 0, v_toPure_954_);
v___x_958_ = lean_apply_4(v_toBind_953_, lean_box(0), lean_box(0), v___x_956_, v___f_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg(lean_object* v_inst_959_){
_start:
{
lean_object* v___f_960_; 
v___f_960_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_960_, 0, v_inst_959_);
return v___f_960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad(lean_object* v_00_u03b1_961_, lean_object* v_00_u03b2_962_, lean_object* v_m_963_, lean_object* v_inst_964_){
_start:
{
lean_object* v___f_965_; 
v___f_965_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_965_, 0, v_inst_964_);
return v___f_965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(lean_object* v_p_966_, lean_object* v___x_967_, lean_object* v___x_968_, lean_object* v_a_969_, lean_object* v_b_970_, lean_object* v_acc_971_){
_start:
{
lean_object* v___x_972_; uint8_t v___x_973_; 
v___x_972_ = lean_apply_2(v_p_966_, v_a_969_, v_b_970_);
v___x_973_ = lean_unbox(v___x_972_);
if (v___x_973_ == 0)
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_967_);
return v___x_974_;
}
else
{
lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
lean_dec_ref(v___x_967_);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_972_);
v___x_976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
lean_ctor_set(v___x_976_, 1, v___x_968_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v___x_976_);
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed(lean_object* v_p_978_, lean_object* v___x_979_, lean_object* v___x_980_, lean_object* v_a_981_, lean_object* v_b_982_, lean_object* v_acc_983_){
_start:
{
lean_object* v_res_984_; 
v_res_984_ = l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(v_p_978_, v___x_979_, v___x_980_, v_a_981_, v_b_982_, v_acc_983_);
lean_dec_ref(v_acc_983_);
return v_res_984_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any___redArg(lean_object* v_t_988_, lean_object* v_p_989_){
_start:
{
lean_object* v___y_991_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___f_999_; lean_object* v___x_1000_; lean_object* v_a_1001_; 
v___x_996_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_997_ = lean_box(0);
v___x_998_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_999_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_999_, 0, v_p_989_);
lean_closure_set(v___f_999_, 1, v___x_998_);
lean_closure_set(v___f_999_, 2, v___x_997_);
v___x_1000_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_996_, v___f_999_, v___x_998_, v_t_988_);
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___y_991_ = v_a_1001_;
goto v___jp_990_;
v___jp_990_:
{
lean_object* v_fst_992_; 
v_fst_992_ = lean_ctor_get(v___y_991_, 0);
lean_inc(v_fst_992_);
lean_dec_ref(v___y_991_);
if (lean_obj_tag(v_fst_992_) == 0)
{
uint8_t v___x_993_; 
v___x_993_ = 0;
return v___x_993_;
}
else
{
lean_object* v_val_994_; uint8_t v___x_995_; 
v_val_994_ = lean_ctor_get(v_fst_992_, 0);
lean_inc(v_val_994_);
lean_dec_ref(v_fst_992_);
v___x_995_ = lean_unbox(v_val_994_);
lean_dec(v_val_994_);
return v___x_995_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___boxed(lean_object* v_t_1002_, lean_object* v_p_1003_){
_start:
{
uint8_t v_res_1004_; lean_object* v_r_1005_; 
v_res_1004_ = l_Std_DTreeMap_Internal_Impl_any___redArg(v_t_1002_, v_p_1003_);
v_r_1005_ = lean_box(v_res_1004_);
return v_r_1005_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any(lean_object* v_00_u03b1_1006_, lean_object* v_00_u03b2_1007_, lean_object* v_t_1008_, lean_object* v_p_1009_){
_start:
{
lean_object* v___y_1011_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___f_1019_; lean_object* v___x_1020_; lean_object* v_a_1021_; 
v___x_1016_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1017_ = lean_box(0);
v___x_1018_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1019_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1019_, 0, v_p_1009_);
lean_closure_set(v___f_1019_, 1, v___x_1018_);
lean_closure_set(v___f_1019_, 2, v___x_1017_);
v___x_1020_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1016_, v___f_1019_, v___x_1018_, v_t_1008_);
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___y_1011_ = v_a_1021_;
goto v___jp_1010_;
v___jp_1010_:
{
lean_object* v_fst_1012_; 
v_fst_1012_ = lean_ctor_get(v___y_1011_, 0);
lean_inc(v_fst_1012_);
lean_dec_ref(v___y_1011_);
if (lean_obj_tag(v_fst_1012_) == 0)
{
uint8_t v___x_1013_; 
v___x_1013_ = 0;
return v___x_1013_;
}
else
{
lean_object* v_val_1014_; uint8_t v___x_1015_; 
v_val_1014_ = lean_ctor_get(v_fst_1012_, 0);
lean_inc(v_val_1014_);
lean_dec_ref(v_fst_1012_);
v___x_1015_ = lean_unbox(v_val_1014_);
lean_dec(v_val_1014_);
return v___x_1015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___boxed(lean_object* v_00_u03b1_1022_, lean_object* v_00_u03b2_1023_, lean_object* v_t_1024_, lean_object* v_p_1025_){
_start:
{
uint8_t v_res_1026_; lean_object* v_r_1027_; 
v_res_1026_ = l_Std_DTreeMap_Internal_Impl_any(v_00_u03b1_1022_, v_00_u03b2_1023_, v_t_1024_, v_p_1025_);
v_r_1027_ = lean_box(v_res_1026_);
return v_r_1027_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(lean_object* v_p_1028_, lean_object* v___x_1029_, lean_object* v___x_1030_, lean_object* v_a_1031_, lean_object* v_b_1032_, lean_object* v_acc_1033_){
_start:
{
lean_object* v___x_1034_; uint8_t v___x_1035_; 
v___x_1034_ = lean_apply_2(v_p_1028_, v_a_1031_, v_b_1032_);
v___x_1035_ = lean_unbox(v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
lean_dec_ref(v___x_1030_);
v___x_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
v___x_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1037_, 0, v___x_1036_);
lean_ctor_set(v___x_1037_, 1, v___x_1029_);
v___x_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
return v___x_1038_;
}
else
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1030_);
return v___x_1039_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed(lean_object* v_p_1040_, lean_object* v___x_1041_, lean_object* v___x_1042_, lean_object* v_a_1043_, lean_object* v_b_1044_, lean_object* v_acc_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(v_p_1040_, v___x_1041_, v___x_1042_, v_a_1043_, v_b_1044_, v_acc_1045_);
lean_dec_ref(v_acc_1045_);
return v_res_1046_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all___redArg(lean_object* v_t_1047_, lean_object* v_p_1048_){
_start:
{
lean_object* v___y_1050_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___f_1058_; lean_object* v___x_1059_; lean_object* v_a_1060_; 
v___x_1055_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1056_ = lean_box(0);
v___x_1057_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1058_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1058_, 0, v_p_1048_);
lean_closure_set(v___f_1058_, 1, v___x_1056_);
lean_closure_set(v___f_1058_, 2, v___x_1057_);
v___x_1059_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1055_, v___f_1058_, v___x_1057_, v_t_1047_);
v_a_1060_ = lean_ctor_get(v___x_1059_, 0);
lean_inc(v_a_1060_);
lean_dec(v___x_1059_);
v___y_1050_ = v_a_1060_;
goto v___jp_1049_;
v___jp_1049_:
{
lean_object* v_fst_1051_; 
v_fst_1051_ = lean_ctor_get(v___y_1050_, 0);
lean_inc(v_fst_1051_);
lean_dec_ref(v___y_1050_);
if (lean_obj_tag(v_fst_1051_) == 0)
{
uint8_t v___x_1052_; 
v___x_1052_ = 1;
return v___x_1052_;
}
else
{
lean_object* v_val_1053_; uint8_t v___x_1054_; 
v_val_1053_ = lean_ctor_get(v_fst_1051_, 0);
lean_inc(v_val_1053_);
lean_dec_ref(v_fst_1051_);
v___x_1054_ = lean_unbox(v_val_1053_);
lean_dec(v_val_1053_);
return v___x_1054_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___boxed(lean_object* v_t_1061_, lean_object* v_p_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l_Std_DTreeMap_Internal_Impl_all___redArg(v_t_1061_, v_p_1062_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all(lean_object* v_00_u03b1_1065_, lean_object* v_00_u03b2_1066_, lean_object* v_t_1067_, lean_object* v_p_1068_){
_start:
{
lean_object* v___y_1070_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___f_1078_; lean_object* v___x_1079_; lean_object* v_a_1080_; 
v___x_1075_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1076_ = lean_box(0);
v___x_1077_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1078_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1078_, 0, v_p_1068_);
lean_closure_set(v___f_1078_, 1, v___x_1076_);
lean_closure_set(v___f_1078_, 2, v___x_1077_);
v___x_1079_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1075_, v___f_1078_, v___x_1077_, v_t_1067_);
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec(v___x_1079_);
v___y_1070_ = v_a_1080_;
goto v___jp_1069_;
v___jp_1069_:
{
lean_object* v_fst_1071_; 
v_fst_1071_ = lean_ctor_get(v___y_1070_, 0);
lean_inc(v_fst_1071_);
lean_dec_ref(v___y_1070_);
if (lean_obj_tag(v_fst_1071_) == 0)
{
uint8_t v___x_1072_; 
v___x_1072_ = 1;
return v___x_1072_;
}
else
{
lean_object* v_val_1073_; uint8_t v___x_1074_; 
v_val_1073_ = lean_ctor_get(v_fst_1071_, 0);
lean_inc(v_val_1073_);
lean_dec_ref(v_fst_1071_);
v___x_1074_ = lean_unbox(v_val_1073_);
lean_dec(v_val_1073_);
return v___x_1074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___boxed(lean_object* v_00_u03b1_1081_, lean_object* v_00_u03b2_1082_, lean_object* v_t_1083_, lean_object* v_p_1084_){
_start:
{
uint8_t v_res_1085_; lean_object* v_r_1086_; 
v_res_1085_ = l_Std_DTreeMap_Internal_Impl_all(v_00_u03b1_1081_, v_00_u03b2_1082_, v_t_1083_, v_p_1084_);
v_r_1086_ = lean_box(v_res_1085_);
return v_r_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(lean_object* v_x1_1087_, lean_object* v_x2_1088_, lean_object* v_x3_1089_){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_x1_1087_);
lean_ctor_set(v___x_1090_, 1, v_x3_1089_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0___boxed(lean_object* v_x1_1091_, lean_object* v_x2_1092_, lean_object* v_x3_1093_){
_start:
{
lean_object* v_res_1094_; 
v_res_1094_ = l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(v_x1_1091_, v_x2_1092_, v_x3_1093_);
lean_dec(v_x2_1092_);
return v_res_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg(lean_object* v_t_1096_){
_start:
{
lean_object* v___f_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___f_1097_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1098_ = lean_box(0);
v___x_1099_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1100_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1099_, v___f_1097_, v___x_1098_, v_t_1096_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys(lean_object* v_00_u03b1_1101_, lean_object* v_00_u03b2_1102_, lean_object* v_t_1103_){
_start:
{
lean_object* v___f_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___f_1104_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1105_ = lean_box(0);
v___x_1106_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1107_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1106_, v___f_1104_, v___x_1105_, v_t_1103_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(lean_object* v_l_1108_, lean_object* v_k_1109_, lean_object* v_x_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_array_push(v_l_1108_, v_k_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0___boxed(lean_object* v_l_1112_, lean_object* v_k_1113_, lean_object* v_x_1114_){
_start:
{
lean_object* v_res_1115_; 
v_res_1115_ = l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(v_l_1112_, v_k_1113_, v_x_1114_);
lean_dec(v_x_1114_);
return v_res_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg(lean_object* v_t_1117_){
_start:
{
lean_object* v___f_1118_; lean_object* v___y_1120_; 
v___f_1118_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1117_) == 0)
{
lean_object* v_size_1123_; 
v_size_1123_ = lean_ctor_get(v_t_1117_, 0);
lean_inc(v_size_1123_);
v___y_1120_ = v_size_1123_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_unsigned_to_nat(0u);
v___y_1120_ = v___x_1124_;
goto v___jp_1119_;
}
v___jp_1119_:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_mk_empty_array_with_capacity(v___y_1120_);
lean_dec(v___y_1120_);
v___x_1122_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1118_, v___x_1121_, v_t_1117_);
return v___x_1122_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray(lean_object* v_00_u03b1_1125_, lean_object* v_00_u03b2_1126_, lean_object* v_t_1127_){
_start:
{
lean_object* v___f_1128_; lean_object* v___y_1130_; 
v___f_1128_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1127_) == 0)
{
lean_object* v_size_1133_; 
v_size_1133_ = lean_ctor_get(v_t_1127_, 0);
lean_inc(v_size_1133_);
v___y_1130_ = v_size_1133_;
goto v___jp_1129_;
}
else
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_unsigned_to_nat(0u);
v___y_1130_ = v___x_1134_;
goto v___jp_1129_;
}
v___jp_1129_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1131_ = lean_mk_empty_array_with_capacity(v___y_1130_);
lean_dec(v___y_1130_);
v___x_1132_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1128_, v___x_1131_, v_t_1127_);
return v___x_1132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(lean_object* v_x1_1135_, lean_object* v_x2_1136_, lean_object* v_x3_1137_){
_start:
{
lean_object* v___x_1138_; 
v___x_1138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_x2_1136_);
lean_ctor_set(v___x_1138_, 1, v_x3_1137_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0___boxed(lean_object* v_x1_1139_, lean_object* v_x2_1140_, lean_object* v_x3_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(v_x1_1139_, v_x2_1140_, v_x3_1141_);
lean_dec(v_x1_1139_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg(lean_object* v_t_1144_){
_start:
{
lean_object* v___f_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; 
v___f_1145_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1146_ = lean_box(0);
v___x_1147_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1148_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1147_, v___f_1145_, v___x_1146_, v_t_1144_);
return v___x_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values(lean_object* v_00_u03b1_1149_, lean_object* v_00_u03b2_1150_, lean_object* v_t_1151_){
_start:
{
lean_object* v___f_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___f_1152_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1153_ = lean_box(0);
v___x_1154_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1155_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1154_, v___f_1152_, v___x_1153_, v_t_1151_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(lean_object* v_l_1156_, lean_object* v_x_1157_, lean_object* v_v_1158_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_array_push(v_l_1156_, v_v_1158_);
return v___x_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0___boxed(lean_object* v_l_1160_, lean_object* v_x_1161_, lean_object* v_v_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(v_l_1160_, v_x_1161_, v_v_1162_);
lean_dec(v_x_1161_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg(lean_object* v_t_1165_){
_start:
{
lean_object* v___f_1166_; lean_object* v___y_1168_; 
v___f_1166_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1165_) == 0)
{
lean_object* v_size_1171_; 
v_size_1171_ = lean_ctor_get(v_t_1165_, 0);
lean_inc(v_size_1171_);
v___y_1168_ = v_size_1171_;
goto v___jp_1167_;
}
else
{
lean_object* v___x_1172_; 
v___x_1172_ = lean_unsigned_to_nat(0u);
v___y_1168_ = v___x_1172_;
goto v___jp_1167_;
}
v___jp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_mk_empty_array_with_capacity(v___y_1168_);
lean_dec(v___y_1168_);
v___x_1170_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1166_, v___x_1169_, v_t_1165_);
return v___x_1170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray(lean_object* v_00_u03b1_1173_, lean_object* v_00_u03b2_1174_, lean_object* v_t_1175_){
_start:
{
lean_object* v___f_1176_; lean_object* v___y_1178_; 
v___f_1176_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1175_) == 0)
{
lean_object* v_size_1181_; 
v_size_1181_ = lean_ctor_get(v_t_1175_, 0);
lean_inc(v_size_1181_);
v___y_1178_ = v_size_1181_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1182_; 
v___x_1182_ = lean_unsigned_to_nat(0u);
v___y_1178_ = v___x_1182_;
goto v___jp_1177_;
}
v___jp_1177_:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
v___x_1179_ = lean_mk_empty_array_with_capacity(v___y_1178_);
lean_dec(v___y_1178_);
v___x_1180_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1176_, v___x_1179_, v_t_1175_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg___lam__0(lean_object* v_x1_1183_, lean_object* v_x2_1184_, lean_object* v_x3_1185_){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1186_, 0, v_x1_1183_);
lean_ctor_set(v___x_1186_, 1, v_x2_1184_);
v___x_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v_x3_1185_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg(lean_object* v_t_1189_){
_start:
{
lean_object* v___f_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___f_1190_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1191_ = lean_box(0);
v___x_1192_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1193_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1192_, v___f_1190_, v___x_1191_, v_t_1189_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList(lean_object* v_00_u03b1_1194_, lean_object* v_00_u03b2_1195_, lean_object* v_t_1196_){
_start:
{
lean_object* v___f_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___f_1197_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1198_ = lean_box(0);
v___x_1199_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1200_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1199_, v___f_1197_, v___x_1198_, v_t_1196_);
return v___x_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg___lam__0(lean_object* v_l_1201_, lean_object* v_k_1202_, lean_object* v_v_1203_){
_start:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v_k_1202_);
lean_ctor_set(v___x_1204_, 1, v_v_1203_);
v___x_1205_ = lean_array_push(v_l_1201_, v___x_1204_);
return v___x_1205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg(lean_object* v_t_1207_){
_start:
{
lean_object* v___f_1208_; lean_object* v___y_1210_; 
v___f_1208_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1207_) == 0)
{
lean_object* v_size_1213_; 
v_size_1213_ = lean_ctor_get(v_t_1207_, 0);
lean_inc(v_size_1213_);
v___y_1210_ = v_size_1213_;
goto v___jp_1209_;
}
else
{
lean_object* v___x_1214_; 
v___x_1214_ = lean_unsigned_to_nat(0u);
v___y_1210_ = v___x_1214_;
goto v___jp_1209_;
}
v___jp_1209_:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_mk_empty_array_with_capacity(v___y_1210_);
lean_dec(v___y_1210_);
v___x_1212_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1208_, v___x_1211_, v_t_1207_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray(lean_object* v_00_u03b1_1215_, lean_object* v_00_u03b2_1216_, lean_object* v_t_1217_){
_start:
{
lean_object* v___f_1218_; lean_object* v___y_1220_; 
v___f_1218_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1217_) == 0)
{
lean_object* v_size_1223_; 
v_size_1223_ = lean_ctor_get(v_t_1217_, 0);
lean_inc(v_size_1223_);
v___y_1220_ = v_size_1223_;
goto v___jp_1219_;
}
else
{
lean_object* v___x_1224_; 
v___x_1224_ = lean_unsigned_to_nat(0u);
v___y_1220_ = v___x_1224_;
goto v___jp_1219_;
}
v___jp_1219_:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1221_ = lean_mk_empty_array_with_capacity(v___y_1220_);
lean_dec(v___y_1220_);
v___x_1222_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1218_, v___x_1221_, v_t_1217_);
return v___x_1222_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___lam__0(lean_object* v_x1_1225_, lean_object* v_x2_1226_, lean_object* v_x3_1227_){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1228_, 0, v_x1_1225_);
lean_ctor_set(v___x_1228_, 1, v_x2_1226_);
v___x_1229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v_x3_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg(lean_object* v_t_1231_){
_start:
{
lean_object* v___f_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___f_1232_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1233_ = lean_box(0);
v___x_1234_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1235_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1234_, v___f_1232_, v___x_1233_, v_t_1231_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList(lean_object* v_00_u03b1_1236_, lean_object* v_00_u03b2_1237_, lean_object* v_t_1238_){
_start:
{
lean_object* v___f_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___f_1239_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1240_ = lean_box(0);
v___x_1241_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1242_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1241_, v___f_1239_, v___x_1240_, v_t_1238_);
return v___x_1242_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___lam__0(lean_object* v_l_1243_, lean_object* v_k_1244_, lean_object* v_v_1245_){
_start:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_k_1244_);
lean_ctor_set(v___x_1246_, 1, v_v_1245_);
v___x_1247_ = lean_array_push(v_l_1243_, v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg(lean_object* v_t_1249_){
_start:
{
lean_object* v___f_1250_; lean_object* v___y_1252_; 
v___f_1250_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1249_) == 0)
{
lean_object* v_size_1255_; 
v_size_1255_ = lean_ctor_get(v_t_1249_, 0);
lean_inc(v_size_1255_);
v___y_1252_ = v_size_1255_;
goto v___jp_1251_;
}
else
{
lean_object* v___x_1256_; 
v___x_1256_ = lean_unsigned_to_nat(0u);
v___y_1252_ = v___x_1256_;
goto v___jp_1251_;
}
v___jp_1251_:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_mk_empty_array_with_capacity(v___y_1252_);
lean_dec(v___y_1252_);
v___x_1254_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1250_, v___x_1253_, v_t_1249_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray(lean_object* v_00_u03b1_1257_, lean_object* v_00_u03b2_1258_, lean_object* v_t_1259_){
_start:
{
lean_object* v___f_1260_; lean_object* v___y_1262_; 
v___f_1260_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1259_) == 0)
{
lean_object* v_size_1265_; 
v_size_1265_ = lean_ctor_get(v_t_1259_, 0);
lean_inc(v_size_1265_);
v___y_1262_ = v_size_1265_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1266_; 
v___x_1266_ = lean_unsigned_to_nat(0u);
v___y_1262_ = v___x_1266_;
goto v___jp_1261_;
}
v___jp_1261_:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1263_ = lean_mk_empty_array_with_capacity(v___y_1262_);
lean_dec(v___y_1262_);
v___x_1264_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1260_, v___x_1263_, v_t_1259_);
return v___x_1264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object* v_x_1267_){
_start:
{
if (lean_obj_tag(v_x_1267_) == 0)
{
lean_object* v_l_1268_; 
v_l_1268_ = lean_ctor_get(v_x_1267_, 3);
if (lean_obj_tag(v_l_1268_) == 0)
{
v_x_1267_ = v_l_1268_;
goto _start;
}
else
{
lean_object* v_k_1270_; lean_object* v_v_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v_k_1270_ = lean_ctor_get(v_x_1267_, 1);
v_v_1271_ = lean_ctor_get(v_x_1267_, 2);
lean_inc(v_v_1271_);
lean_inc(v_k_1270_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_k_1270_);
lean_ctor_set(v___x_1272_, 1, v_v_1271_);
v___x_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
return v___x_1273_;
}
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_box(0);
return v___x_1274_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg___boxed(lean_object* v_x_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1275_);
lean_dec(v_x_1275_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f(lean_object* v_00_u03b1_1277_, lean_object* v_00_u03b2_1278_, lean_object* v_x_1279_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___boxed(lean_object* v_00_u03b1_1281_, lean_object* v_00_u03b2_1282_, lean_object* v_x_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f(v_00_u03b1_1281_, v_00_u03b2_1282_, v_x_1283_);
lean_dec(v_x_1283_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1285_, lean_object* v_h__1_1286_, lean_object* v_h__2_1287_, lean_object* v_h__3_1288_){
_start:
{
if (lean_obj_tag(v_x_1285_) == 0)
{
lean_object* v_l_1289_; 
lean_dec(v_h__1_1286_);
v_l_1289_ = lean_ctor_get(v_x_1285_, 3);
if (lean_obj_tag(v_l_1289_) == 0)
{
lean_object* v_size_1290_; lean_object* v_k_1291_; lean_object* v_v_1292_; lean_object* v_r_1293_; lean_object* v_size_1294_; lean_object* v_k_1295_; lean_object* v_v_1296_; lean_object* v_l_1297_; lean_object* v_r_1298_; lean_object* v___x_1299_; 
lean_inc_ref(v_l_1289_);
lean_dec(v_h__2_1287_);
v_size_1290_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_size_1290_);
v_k_1291_ = lean_ctor_get(v_x_1285_, 1);
lean_inc(v_k_1291_);
v_v_1292_ = lean_ctor_get(v_x_1285_, 2);
lean_inc(v_v_1292_);
v_r_1293_ = lean_ctor_get(v_x_1285_, 4);
lean_inc(v_r_1293_);
lean_dec_ref(v_x_1285_);
v_size_1294_ = lean_ctor_get(v_l_1289_, 0);
lean_inc(v_size_1294_);
v_k_1295_ = lean_ctor_get(v_l_1289_, 1);
lean_inc(v_k_1295_);
v_v_1296_ = lean_ctor_get(v_l_1289_, 2);
lean_inc(v_v_1296_);
v_l_1297_ = lean_ctor_get(v_l_1289_, 3);
lean_inc(v_l_1297_);
v_r_1298_ = lean_ctor_get(v_l_1289_, 4);
lean_inc(v_r_1298_);
lean_dec_ref(v_l_1289_);
v___x_1299_ = lean_apply_9(v_h__3_1288_, v_size_1290_, v_k_1291_, v_v_1292_, v_size_1294_, v_k_1295_, v_v_1296_, v_l_1297_, v_r_1298_, v_r_1293_);
return v___x_1299_;
}
else
{
lean_object* v_size_1300_; lean_object* v_k_1301_; lean_object* v_v_1302_; lean_object* v_r_1303_; lean_object* v___x_1304_; 
lean_dec(v_h__3_1288_);
v_size_1300_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_size_1300_);
v_k_1301_ = lean_ctor_get(v_x_1285_, 1);
lean_inc(v_k_1301_);
v_v_1302_ = lean_ctor_get(v_x_1285_, 2);
lean_inc(v_v_1302_);
v_r_1303_ = lean_ctor_get(v_x_1285_, 4);
lean_inc(v_r_1303_);
lean_dec_ref(v_x_1285_);
v___x_1304_ = lean_apply_4(v_h__2_1287_, v_size_1300_, v_k_1301_, v_v_1302_, v_r_1303_);
return v___x_1304_;
}
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec(v_h__3_1288_);
lean_dec(v_h__2_1287_);
v___x_1305_ = lean_box(0);
v___x_1306_ = lean_apply_1(v_h__1_1286_, v___x_1305_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1307_, lean_object* v_00_u03b2_1308_, lean_object* v_motive_1309_, lean_object* v_x_1310_, lean_object* v_h__1_1311_, lean_object* v_h__2_1312_, lean_object* v_h__3_1313_){
_start:
{
if (lean_obj_tag(v_x_1310_) == 0)
{
lean_object* v_l_1314_; 
lean_dec(v_h__1_1311_);
v_l_1314_ = lean_ctor_get(v_x_1310_, 3);
if (lean_obj_tag(v_l_1314_) == 0)
{
lean_object* v_size_1315_; lean_object* v_k_1316_; lean_object* v_v_1317_; lean_object* v_r_1318_; lean_object* v_size_1319_; lean_object* v_k_1320_; lean_object* v_v_1321_; lean_object* v_l_1322_; lean_object* v_r_1323_; lean_object* v___x_1324_; 
lean_inc_ref(v_l_1314_);
lean_dec(v_h__2_1312_);
v_size_1315_ = lean_ctor_get(v_x_1310_, 0);
lean_inc(v_size_1315_);
v_k_1316_ = lean_ctor_get(v_x_1310_, 1);
lean_inc(v_k_1316_);
v_v_1317_ = lean_ctor_get(v_x_1310_, 2);
lean_inc(v_v_1317_);
v_r_1318_ = lean_ctor_get(v_x_1310_, 4);
lean_inc(v_r_1318_);
lean_dec_ref(v_x_1310_);
v_size_1319_ = lean_ctor_get(v_l_1314_, 0);
lean_inc(v_size_1319_);
v_k_1320_ = lean_ctor_get(v_l_1314_, 1);
lean_inc(v_k_1320_);
v_v_1321_ = lean_ctor_get(v_l_1314_, 2);
lean_inc(v_v_1321_);
v_l_1322_ = lean_ctor_get(v_l_1314_, 3);
lean_inc(v_l_1322_);
v_r_1323_ = lean_ctor_get(v_l_1314_, 4);
lean_inc(v_r_1323_);
lean_dec_ref(v_l_1314_);
v___x_1324_ = lean_apply_9(v_h__3_1313_, v_size_1315_, v_k_1316_, v_v_1317_, v_size_1319_, v_k_1320_, v_v_1321_, v_l_1322_, v_r_1323_, v_r_1318_);
return v___x_1324_;
}
else
{
lean_object* v_size_1325_; lean_object* v_k_1326_; lean_object* v_v_1327_; lean_object* v_r_1328_; lean_object* v___x_1329_; 
lean_dec(v_h__3_1313_);
v_size_1325_ = lean_ctor_get(v_x_1310_, 0);
lean_inc(v_size_1325_);
v_k_1326_ = lean_ctor_get(v_x_1310_, 1);
lean_inc(v_k_1326_);
v_v_1327_ = lean_ctor_get(v_x_1310_, 2);
lean_inc(v_v_1327_);
v_r_1328_ = lean_ctor_get(v_x_1310_, 4);
lean_inc(v_r_1328_);
lean_dec_ref(v_x_1310_);
v___x_1329_ = lean_apply_4(v_h__2_1312_, v_size_1325_, v_k_1326_, v_v_1327_, v_r_1328_);
return v___x_1329_;
}
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec(v_h__3_1313_);
lean_dec(v_h__2_1312_);
v___x_1330_ = lean_box(0);
v___x_1331_ = lean_apply_1(v_h__1_1311_, v___x_1330_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg(lean_object* v_x_1332_){
_start:
{
lean_object* v_l_1333_; 
v_l_1333_ = lean_ctor_get(v_x_1332_, 3);
if (lean_obj_tag(v_l_1333_) == 0)
{
v_x_1332_ = v_l_1333_;
goto _start;
}
else
{
lean_object* v_k_1335_; lean_object* v_v_1336_; lean_object* v___x_1337_; 
v_k_1335_ = lean_ctor_get(v_x_1332_, 1);
v_v_1336_ = lean_ctor_get(v_x_1332_, 2);
lean_inc(v_v_1336_);
lean_inc(v_k_1335_);
v___x_1337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1337_, 0, v_k_1335_);
lean_ctor_set(v___x_1337_, 1, v_v_1336_);
return v___x_1337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg___boxed(lean_object* v_x_1338_){
_start:
{
lean_object* v_res_1339_; 
v_res_1339_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1338_);
lean_dec(v_x_1338_);
return v_res_1339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry(lean_object* v_00_u03b1_1340_, lean_object* v_00_u03b2_1341_, lean_object* v_x_1342_, lean_object* v_x_1343_){
_start:
{
lean_object* v___x_1344_; 
v___x_1344_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1342_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___boxed(lean_object* v_00_u03b1_1345_, lean_object* v_00_u03b2_1346_, lean_object* v_x_1347_, lean_object* v_x_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Std_DTreeMap_Internal_Impl_minEntry(v_00_u03b1_1345_, v_00_u03b2_1346_, v_x_1347_, v_x_1348_);
lean_dec(v_x_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1350_, lean_object* v_h__1_1351_, lean_object* v_h__2_1352_){
_start:
{
lean_object* v_l_1353_; 
v_l_1353_ = lean_ctor_get(v_x_1350_, 3);
if (lean_obj_tag(v_l_1353_) == 0)
{
lean_object* v_size_1354_; lean_object* v_k_1355_; lean_object* v_v_1356_; lean_object* v_r_1357_; lean_object* v_size_1358_; lean_object* v_k_1359_; lean_object* v_v_1360_; lean_object* v_l_1361_; lean_object* v_r_1362_; lean_object* v___x_1363_; 
lean_inc_ref(v_l_1353_);
lean_dec(v_h__1_1351_);
v_size_1354_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_size_1354_);
v_k_1355_ = lean_ctor_get(v_x_1350_, 1);
lean_inc(v_k_1355_);
v_v_1356_ = lean_ctor_get(v_x_1350_, 2);
lean_inc(v_v_1356_);
v_r_1357_ = lean_ctor_get(v_x_1350_, 4);
lean_inc(v_r_1357_);
lean_dec(v_x_1350_);
v_size_1358_ = lean_ctor_get(v_l_1353_, 0);
lean_inc(v_size_1358_);
v_k_1359_ = lean_ctor_get(v_l_1353_, 1);
lean_inc(v_k_1359_);
v_v_1360_ = lean_ctor_get(v_l_1353_, 2);
lean_inc(v_v_1360_);
v_l_1361_ = lean_ctor_get(v_l_1353_, 3);
lean_inc(v_l_1361_);
v_r_1362_ = lean_ctor_get(v_l_1353_, 4);
lean_inc(v_r_1362_);
lean_dec_ref(v_l_1353_);
v___x_1363_ = lean_apply_10(v_h__2_1352_, v_size_1354_, v_k_1355_, v_v_1356_, v_size_1358_, v_k_1359_, v_v_1360_, v_l_1361_, v_r_1362_, v_r_1357_, lean_box(0));
return v___x_1363_;
}
else
{
lean_object* v_size_1364_; lean_object* v_k_1365_; lean_object* v_v_1366_; lean_object* v_r_1367_; lean_object* v___x_1368_; 
lean_dec(v_h__2_1352_);
v_size_1364_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_size_1364_);
v_k_1365_ = lean_ctor_get(v_x_1350_, 1);
lean_inc(v_k_1365_);
v_v_1366_ = lean_ctor_get(v_x_1350_, 2);
lean_inc(v_v_1366_);
v_r_1367_ = lean_ctor_get(v_x_1350_, 4);
lean_inc(v_r_1367_);
lean_dec(v_x_1350_);
v___x_1368_ = lean_apply_5(v_h__1_1351_, v_size_1364_, v_k_1365_, v_v_1366_, v_r_1367_, lean_box(0));
return v___x_1368_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1369_, lean_object* v_00_u03b2_1370_, lean_object* v_motive_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v_h__1_1374_, lean_object* v_h__2_1375_){
_start:
{
lean_object* v_l_1376_; 
v_l_1376_ = lean_ctor_get(v_x_1372_, 3);
if (lean_obj_tag(v_l_1376_) == 0)
{
lean_object* v_size_1377_; lean_object* v_k_1378_; lean_object* v_v_1379_; lean_object* v_r_1380_; lean_object* v_size_1381_; lean_object* v_k_1382_; lean_object* v_v_1383_; lean_object* v_l_1384_; lean_object* v_r_1385_; lean_object* v___x_1386_; 
lean_inc_ref(v_l_1376_);
lean_dec(v_h__1_1374_);
v_size_1377_ = lean_ctor_get(v_x_1372_, 0);
lean_inc(v_size_1377_);
v_k_1378_ = lean_ctor_get(v_x_1372_, 1);
lean_inc(v_k_1378_);
v_v_1379_ = lean_ctor_get(v_x_1372_, 2);
lean_inc(v_v_1379_);
v_r_1380_ = lean_ctor_get(v_x_1372_, 4);
lean_inc(v_r_1380_);
lean_dec(v_x_1372_);
v_size_1381_ = lean_ctor_get(v_l_1376_, 0);
lean_inc(v_size_1381_);
v_k_1382_ = lean_ctor_get(v_l_1376_, 1);
lean_inc(v_k_1382_);
v_v_1383_ = lean_ctor_get(v_l_1376_, 2);
lean_inc(v_v_1383_);
v_l_1384_ = lean_ctor_get(v_l_1376_, 3);
lean_inc(v_l_1384_);
v_r_1385_ = lean_ctor_get(v_l_1376_, 4);
lean_inc(v_r_1385_);
lean_dec_ref(v_l_1376_);
v___x_1386_ = lean_apply_10(v_h__2_1375_, v_size_1377_, v_k_1378_, v_v_1379_, v_size_1381_, v_k_1382_, v_v_1383_, v_l_1384_, v_r_1385_, v_r_1380_, lean_box(0));
return v___x_1386_;
}
else
{
lean_object* v_size_1387_; lean_object* v_k_1388_; lean_object* v_v_1389_; lean_object* v_r_1390_; lean_object* v___x_1391_; 
lean_dec(v_h__2_1375_);
v_size_1387_ = lean_ctor_get(v_x_1372_, 0);
lean_inc(v_size_1387_);
v_k_1388_ = lean_ctor_get(v_x_1372_, 1);
lean_inc(v_k_1388_);
v_v_1389_ = lean_ctor_get(v_x_1372_, 2);
lean_inc(v_v_1389_);
v_r_1390_ = lean_ctor_get(v_x_1372_, 4);
lean_inc(v_r_1390_);
lean_dec(v_x_1372_);
v___x_1391_ = lean_apply_5(v_h__1_1374_, v_size_1387_, v_k_1388_, v_v_1389_, v_r_1390_, lean_box(0));
return v___x_1391_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1394_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1395_ = lean_unsigned_to_nat(13u);
v___x_1396_ = lean_unsigned_to_nat(367u);
v___x_1397_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0));
v___x_1398_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1399_ = l_mkPanicMessageWithDecl(v___x_1398_, v___x_1397_, v___x_1396_, v___x_1395_, v___x_1394_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object* v_inst_1400_, lean_object* v_x_1401_){
_start:
{
if (lean_obj_tag(v_x_1401_) == 0)
{
lean_object* v_l_1402_; 
v_l_1402_ = lean_ctor_get(v_x_1401_, 3);
if (lean_obj_tag(v_l_1402_) == 0)
{
v_x_1401_ = v_l_1402_;
goto _start;
}
else
{
lean_object* v_k_1404_; lean_object* v_v_1405_; lean_object* v___x_1406_; 
v_k_1404_ = lean_ctor_get(v_x_1401_, 1);
v_v_1405_ = lean_ctor_get(v_x_1401_, 2);
lean_inc(v_v_1405_);
lean_inc(v_k_1404_);
v___x_1406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1406_, 0, v_k_1404_);
lean_ctor_set(v___x_1406_, 1, v_v_1405_);
return v___x_1406_;
}
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1407_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2);
v___x_1408_ = l_panic___redArg(v_inst_1400_, v___x_1407_);
return v___x_1408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___boxed(lean_object* v_inst_1409_, lean_object* v_x_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1409_, v_x_1410_);
lean_dec(v_x_1410_);
lean_dec_ref(v_inst_1409_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21(lean_object* v_00_u03b1_1412_, lean_object* v_00_u03b2_1413_, lean_object* v_inst_1414_, lean_object* v_x_1415_){
_start:
{
lean_object* v___x_1416_; 
v___x_1416_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1414_, v_x_1415_);
return v___x_1416_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___boxed(lean_object* v_00_u03b1_1417_, lean_object* v_00_u03b2_1418_, lean_object* v_inst_1419_, lean_object* v_x_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21(v_00_u03b1_1417_, v_00_u03b2_1418_, v_inst_1419_, v_x_1420_);
lean_dec(v_x_1420_);
lean_dec_ref(v_inst_1419_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
if (lean_obj_tag(v_x_1422_) == 0)
{
lean_object* v_l_1424_; 
v_l_1424_ = lean_ctor_get(v_x_1422_, 3);
if (lean_obj_tag(v_l_1424_) == 0)
{
v_x_1422_ = v_l_1424_;
goto _start;
}
else
{
lean_object* v_k_1426_; lean_object* v_v_1427_; lean_object* v___x_1428_; 
v_k_1426_ = lean_ctor_get(v_x_1422_, 1);
v_v_1427_ = lean_ctor_get(v_x_1422_, 2);
lean_inc(v_v_1427_);
lean_inc(v_k_1426_);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_k_1426_);
lean_ctor_set(v___x_1428_, 1, v_v_1427_);
return v___x_1428_;
}
}
else
{
lean_inc_ref(v_x_1423_);
return v_x_1423_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg___boxed(lean_object* v_x_1429_, lean_object* v_x_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1429_, v_x_1430_);
lean_dec_ref(v_x_1430_);
lean_dec(v_x_1429_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD(lean_object* v_00_u03b1_1432_, lean_object* v_00_u03b2_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1434_, v_x_1435_);
return v___x_1436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___boxed(lean_object* v_00_u03b1_1437_, lean_object* v_00_u03b2_1438_, lean_object* v_x_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Std_DTreeMap_Internal_Impl_minEntryD(v_00_u03b1_1437_, v_00_u03b2_1438_, v_x_1439_, v_x_1440_);
lean_dec_ref(v_x_1440_);
lean_dec(v_x_1439_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v_h__1_1444_, lean_object* v_h__2_1445_, lean_object* v_h__3_1446_){
_start:
{
if (lean_obj_tag(v_x_1442_) == 0)
{
lean_object* v_l_1447_; 
lean_dec(v_h__1_1444_);
v_l_1447_ = lean_ctor_get(v_x_1442_, 3);
if (lean_obj_tag(v_l_1447_) == 0)
{
lean_object* v_size_1448_; lean_object* v_k_1449_; lean_object* v_v_1450_; lean_object* v_r_1451_; lean_object* v_size_1452_; lean_object* v_k_1453_; lean_object* v_v_1454_; lean_object* v_l_1455_; lean_object* v_r_1456_; lean_object* v___x_1457_; 
lean_inc_ref(v_l_1447_);
lean_dec(v_h__2_1445_);
v_size_1448_ = lean_ctor_get(v_x_1442_, 0);
lean_inc(v_size_1448_);
v_k_1449_ = lean_ctor_get(v_x_1442_, 1);
lean_inc(v_k_1449_);
v_v_1450_ = lean_ctor_get(v_x_1442_, 2);
lean_inc(v_v_1450_);
v_r_1451_ = lean_ctor_get(v_x_1442_, 4);
lean_inc(v_r_1451_);
lean_dec_ref(v_x_1442_);
v_size_1452_ = lean_ctor_get(v_l_1447_, 0);
lean_inc(v_size_1452_);
v_k_1453_ = lean_ctor_get(v_l_1447_, 1);
lean_inc(v_k_1453_);
v_v_1454_ = lean_ctor_get(v_l_1447_, 2);
lean_inc(v_v_1454_);
v_l_1455_ = lean_ctor_get(v_l_1447_, 3);
lean_inc(v_l_1455_);
v_r_1456_ = lean_ctor_get(v_l_1447_, 4);
lean_inc(v_r_1456_);
lean_dec_ref(v_l_1447_);
v___x_1457_ = lean_apply_10(v_h__3_1446_, v_size_1448_, v_k_1449_, v_v_1450_, v_size_1452_, v_k_1453_, v_v_1454_, v_l_1455_, v_r_1456_, v_r_1451_, v_x_1443_);
return v___x_1457_;
}
else
{
lean_object* v_size_1458_; lean_object* v_k_1459_; lean_object* v_v_1460_; lean_object* v_r_1461_; lean_object* v___x_1462_; 
lean_dec(v_h__3_1446_);
v_size_1458_ = lean_ctor_get(v_x_1442_, 0);
lean_inc(v_size_1458_);
v_k_1459_ = lean_ctor_get(v_x_1442_, 1);
lean_inc(v_k_1459_);
v_v_1460_ = lean_ctor_get(v_x_1442_, 2);
lean_inc(v_v_1460_);
v_r_1461_ = lean_ctor_get(v_x_1442_, 4);
lean_inc(v_r_1461_);
lean_dec_ref(v_x_1442_);
v___x_1462_ = lean_apply_5(v_h__2_1445_, v_size_1458_, v_k_1459_, v_v_1460_, v_r_1461_, v_x_1443_);
return v___x_1462_;
}
}
else
{
lean_object* v___x_1463_; 
lean_dec(v_h__3_1446_);
lean_dec(v_h__2_1445_);
v___x_1463_ = lean_apply_1(v_h__1_1444_, v_x_1443_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1464_, lean_object* v_00_u03b2_1465_, lean_object* v_motive_1466_, lean_object* v_x_1467_, lean_object* v_x_1468_, lean_object* v_h__1_1469_, lean_object* v_h__2_1470_, lean_object* v_h__3_1471_){
_start:
{
if (lean_obj_tag(v_x_1467_) == 0)
{
lean_object* v_l_1472_; 
lean_dec(v_h__1_1469_);
v_l_1472_ = lean_ctor_get(v_x_1467_, 3);
if (lean_obj_tag(v_l_1472_) == 0)
{
lean_object* v_size_1473_; lean_object* v_k_1474_; lean_object* v_v_1475_; lean_object* v_r_1476_; lean_object* v_size_1477_; lean_object* v_k_1478_; lean_object* v_v_1479_; lean_object* v_l_1480_; lean_object* v_r_1481_; lean_object* v___x_1482_; 
lean_inc_ref(v_l_1472_);
lean_dec(v_h__2_1470_);
v_size_1473_ = lean_ctor_get(v_x_1467_, 0);
lean_inc(v_size_1473_);
v_k_1474_ = lean_ctor_get(v_x_1467_, 1);
lean_inc(v_k_1474_);
v_v_1475_ = lean_ctor_get(v_x_1467_, 2);
lean_inc(v_v_1475_);
v_r_1476_ = lean_ctor_get(v_x_1467_, 4);
lean_inc(v_r_1476_);
lean_dec_ref(v_x_1467_);
v_size_1477_ = lean_ctor_get(v_l_1472_, 0);
lean_inc(v_size_1477_);
v_k_1478_ = lean_ctor_get(v_l_1472_, 1);
lean_inc(v_k_1478_);
v_v_1479_ = lean_ctor_get(v_l_1472_, 2);
lean_inc(v_v_1479_);
v_l_1480_ = lean_ctor_get(v_l_1472_, 3);
lean_inc(v_l_1480_);
v_r_1481_ = lean_ctor_get(v_l_1472_, 4);
lean_inc(v_r_1481_);
lean_dec_ref(v_l_1472_);
v___x_1482_ = lean_apply_10(v_h__3_1471_, v_size_1473_, v_k_1474_, v_v_1475_, v_size_1477_, v_k_1478_, v_v_1479_, v_l_1480_, v_r_1481_, v_r_1476_, v_x_1468_);
return v___x_1482_;
}
else
{
lean_object* v_size_1483_; lean_object* v_k_1484_; lean_object* v_v_1485_; lean_object* v_r_1486_; lean_object* v___x_1487_; 
lean_dec(v_h__3_1471_);
v_size_1483_ = lean_ctor_get(v_x_1467_, 0);
lean_inc(v_size_1483_);
v_k_1484_ = lean_ctor_get(v_x_1467_, 1);
lean_inc(v_k_1484_);
v_v_1485_ = lean_ctor_get(v_x_1467_, 2);
lean_inc(v_v_1485_);
v_r_1486_ = lean_ctor_get(v_x_1467_, 4);
lean_inc(v_r_1486_);
lean_dec_ref(v_x_1467_);
v___x_1487_ = lean_apply_5(v_h__2_1470_, v_size_1483_, v_k_1484_, v_v_1485_, v_r_1486_, v_x_1468_);
return v___x_1487_;
}
}
else
{
lean_object* v___x_1488_; 
lean_dec(v_h__3_1471_);
lean_dec(v_h__2_1470_);
v___x_1488_ = lean_apply_1(v_h__1_1469_, v_x_1468_);
return v___x_1488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object* v_x_1489_){
_start:
{
if (lean_obj_tag(v_x_1489_) == 0)
{
lean_object* v_r_1490_; 
v_r_1490_ = lean_ctor_get(v_x_1489_, 4);
if (lean_obj_tag(v_r_1490_) == 0)
{
v_x_1489_ = v_r_1490_;
goto _start;
}
else
{
lean_object* v_k_1492_; lean_object* v_v_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v_k_1492_ = lean_ctor_get(v_x_1489_, 1);
v_v_1493_ = lean_ctor_get(v_x_1489_, 2);
lean_inc(v_v_1493_);
lean_inc(v_k_1492_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_k_1492_);
lean_ctor_set(v___x_1494_, 1, v_v_1493_);
v___x_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
return v___x_1495_;
}
}
else
{
lean_object* v___x_1496_; 
v___x_1496_ = lean_box(0);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg___boxed(lean_object* v_x_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1497_);
lean_dec(v_x_1497_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(lean_object* v_00_u03b1_1499_, lean_object* v_00_u03b2_1500_, lean_object* v_x_1501_){
_start:
{
lean_object* v___x_1502_; 
v___x_1502_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1503_, lean_object* v_00_u03b2_1504_, lean_object* v_x_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(v_00_u03b1_1503_, v_00_u03b2_1504_, v_x_1505_);
lean_dec(v_x_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1507_, lean_object* v_h__1_1508_, lean_object* v_h__2_1509_, lean_object* v_h__3_1510_){
_start:
{
if (lean_obj_tag(v_x_1507_) == 0)
{
lean_object* v_r_1511_; 
lean_dec(v_h__1_1508_);
v_r_1511_ = lean_ctor_get(v_x_1507_, 4);
if (lean_obj_tag(v_r_1511_) == 0)
{
lean_object* v_size_1512_; lean_object* v_k_1513_; lean_object* v_v_1514_; lean_object* v_l_1515_; lean_object* v_size_1516_; lean_object* v_k_1517_; lean_object* v_v_1518_; lean_object* v_l_1519_; lean_object* v_r_1520_; lean_object* v___x_1521_; 
lean_inc_ref(v_r_1511_);
lean_dec(v_h__2_1509_);
v_size_1512_ = lean_ctor_get(v_x_1507_, 0);
lean_inc(v_size_1512_);
v_k_1513_ = lean_ctor_get(v_x_1507_, 1);
lean_inc(v_k_1513_);
v_v_1514_ = lean_ctor_get(v_x_1507_, 2);
lean_inc(v_v_1514_);
v_l_1515_ = lean_ctor_get(v_x_1507_, 3);
lean_inc(v_l_1515_);
lean_dec_ref(v_x_1507_);
v_size_1516_ = lean_ctor_get(v_r_1511_, 0);
lean_inc(v_size_1516_);
v_k_1517_ = lean_ctor_get(v_r_1511_, 1);
lean_inc(v_k_1517_);
v_v_1518_ = lean_ctor_get(v_r_1511_, 2);
lean_inc(v_v_1518_);
v_l_1519_ = lean_ctor_get(v_r_1511_, 3);
lean_inc(v_l_1519_);
v_r_1520_ = lean_ctor_get(v_r_1511_, 4);
lean_inc(v_r_1520_);
lean_dec_ref(v_r_1511_);
v___x_1521_ = lean_apply_9(v_h__3_1510_, v_size_1512_, v_k_1513_, v_v_1514_, v_l_1515_, v_size_1516_, v_k_1517_, v_v_1518_, v_l_1519_, v_r_1520_);
return v___x_1521_;
}
else
{
lean_object* v_size_1522_; lean_object* v_k_1523_; lean_object* v_v_1524_; lean_object* v_l_1525_; lean_object* v___x_1526_; 
lean_dec(v_h__3_1510_);
v_size_1522_ = lean_ctor_get(v_x_1507_, 0);
lean_inc(v_size_1522_);
v_k_1523_ = lean_ctor_get(v_x_1507_, 1);
lean_inc(v_k_1523_);
v_v_1524_ = lean_ctor_get(v_x_1507_, 2);
lean_inc(v_v_1524_);
v_l_1525_ = lean_ctor_get(v_x_1507_, 3);
lean_inc(v_l_1525_);
lean_dec_ref(v_x_1507_);
v___x_1526_ = lean_apply_4(v_h__2_1509_, v_size_1522_, v_k_1523_, v_v_1524_, v_l_1525_);
return v___x_1526_;
}
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; 
lean_dec(v_h__3_1510_);
lean_dec(v_h__2_1509_);
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_apply_1(v_h__1_1508_, v___x_1527_);
return v___x_1528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1529_, lean_object* v_00_u03b2_1530_, lean_object* v_motive_1531_, lean_object* v_x_1532_, lean_object* v_h__1_1533_, lean_object* v_h__2_1534_, lean_object* v_h__3_1535_){
_start:
{
if (lean_obj_tag(v_x_1532_) == 0)
{
lean_object* v_r_1536_; 
lean_dec(v_h__1_1533_);
v_r_1536_ = lean_ctor_get(v_x_1532_, 4);
if (lean_obj_tag(v_r_1536_) == 0)
{
lean_object* v_size_1537_; lean_object* v_k_1538_; lean_object* v_v_1539_; lean_object* v_l_1540_; lean_object* v_size_1541_; lean_object* v_k_1542_; lean_object* v_v_1543_; lean_object* v_l_1544_; lean_object* v_r_1545_; lean_object* v___x_1546_; 
lean_inc_ref(v_r_1536_);
lean_dec(v_h__2_1534_);
v_size_1537_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_size_1537_);
v_k_1538_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_k_1538_);
v_v_1539_ = lean_ctor_get(v_x_1532_, 2);
lean_inc(v_v_1539_);
v_l_1540_ = lean_ctor_get(v_x_1532_, 3);
lean_inc(v_l_1540_);
lean_dec_ref(v_x_1532_);
v_size_1541_ = lean_ctor_get(v_r_1536_, 0);
lean_inc(v_size_1541_);
v_k_1542_ = lean_ctor_get(v_r_1536_, 1);
lean_inc(v_k_1542_);
v_v_1543_ = lean_ctor_get(v_r_1536_, 2);
lean_inc(v_v_1543_);
v_l_1544_ = lean_ctor_get(v_r_1536_, 3);
lean_inc(v_l_1544_);
v_r_1545_ = lean_ctor_get(v_r_1536_, 4);
lean_inc(v_r_1545_);
lean_dec_ref(v_r_1536_);
v___x_1546_ = lean_apply_9(v_h__3_1535_, v_size_1537_, v_k_1538_, v_v_1539_, v_l_1540_, v_size_1541_, v_k_1542_, v_v_1543_, v_l_1544_, v_r_1545_);
return v___x_1546_;
}
else
{
lean_object* v_size_1547_; lean_object* v_k_1548_; lean_object* v_v_1549_; lean_object* v_l_1550_; lean_object* v___x_1551_; 
lean_dec(v_h__3_1535_);
v_size_1547_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_size_1547_);
v_k_1548_ = lean_ctor_get(v_x_1532_, 1);
lean_inc(v_k_1548_);
v_v_1549_ = lean_ctor_get(v_x_1532_, 2);
lean_inc(v_v_1549_);
v_l_1550_ = lean_ctor_get(v_x_1532_, 3);
lean_inc(v_l_1550_);
lean_dec_ref(v_x_1532_);
v___x_1551_ = lean_apply_4(v_h__2_1534_, v_size_1547_, v_k_1548_, v_v_1549_, v_l_1550_);
return v___x_1551_;
}
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
lean_dec(v_h__3_1535_);
lean_dec(v_h__2_1534_);
v___x_1552_ = lean_box(0);
v___x_1553_ = lean_apply_1(v_h__1_1533_, v___x_1552_);
return v___x_1553_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object* v_x_1554_){
_start:
{
lean_object* v_r_1555_; 
v_r_1555_ = lean_ctor_get(v_x_1554_, 4);
if (lean_obj_tag(v_r_1555_) == 0)
{
v_x_1554_ = v_r_1555_;
goto _start;
}
else
{
lean_object* v_k_1557_; lean_object* v_v_1558_; lean_object* v___x_1559_; 
v_k_1557_ = lean_ctor_get(v_x_1554_, 1);
v_v_1558_ = lean_ctor_get(v_x_1554_, 2);
lean_inc(v_v_1558_);
lean_inc(v_k_1557_);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v_k_1557_);
lean_ctor_set(v___x_1559_, 1, v_v_1558_);
return v___x_1559_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg___boxed(lean_object* v_x_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1560_);
lean_dec(v_x_1560_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry(lean_object* v_00_u03b1_1562_, lean_object* v_00_u03b2_1563_, lean_object* v_x_1564_, lean_object* v_x_1565_){
_start:
{
lean_object* v___x_1566_; 
v___x_1566_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___boxed(lean_object* v_00_u03b1_1567_, lean_object* v_00_u03b2_1568_, lean_object* v_x_1569_, lean_object* v_x_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_Std_DTreeMap_Internal_Impl_maxEntry(v_00_u03b1_1567_, v_00_u03b2_1568_, v_x_1569_, v_x_1570_);
lean_dec(v_x_1569_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1572_, lean_object* v_h__1_1573_, lean_object* v_h__2_1574_){
_start:
{
lean_object* v_r_1575_; 
v_r_1575_ = lean_ctor_get(v_x_1572_, 4);
if (lean_obj_tag(v_r_1575_) == 0)
{
lean_object* v_size_1576_; lean_object* v_k_1577_; lean_object* v_v_1578_; lean_object* v_l_1579_; lean_object* v_size_1580_; lean_object* v_k_1581_; lean_object* v_v_1582_; lean_object* v_l_1583_; lean_object* v_r_1584_; lean_object* v___x_1585_; 
lean_inc_ref(v_r_1575_);
lean_dec(v_h__1_1573_);
v_size_1576_ = lean_ctor_get(v_x_1572_, 0);
lean_inc(v_size_1576_);
v_k_1577_ = lean_ctor_get(v_x_1572_, 1);
lean_inc(v_k_1577_);
v_v_1578_ = lean_ctor_get(v_x_1572_, 2);
lean_inc(v_v_1578_);
v_l_1579_ = lean_ctor_get(v_x_1572_, 3);
lean_inc(v_l_1579_);
lean_dec(v_x_1572_);
v_size_1580_ = lean_ctor_get(v_r_1575_, 0);
lean_inc(v_size_1580_);
v_k_1581_ = lean_ctor_get(v_r_1575_, 1);
lean_inc(v_k_1581_);
v_v_1582_ = lean_ctor_get(v_r_1575_, 2);
lean_inc(v_v_1582_);
v_l_1583_ = lean_ctor_get(v_r_1575_, 3);
lean_inc(v_l_1583_);
v_r_1584_ = lean_ctor_get(v_r_1575_, 4);
lean_inc(v_r_1584_);
lean_dec_ref(v_r_1575_);
v___x_1585_ = lean_apply_10(v_h__2_1574_, v_size_1576_, v_k_1577_, v_v_1578_, v_l_1579_, v_size_1580_, v_k_1581_, v_v_1582_, v_l_1583_, v_r_1584_, lean_box(0));
return v___x_1585_;
}
else
{
lean_object* v_size_1586_; lean_object* v_k_1587_; lean_object* v_v_1588_; lean_object* v_l_1589_; lean_object* v___x_1590_; 
lean_dec(v_h__2_1574_);
v_size_1586_ = lean_ctor_get(v_x_1572_, 0);
lean_inc(v_size_1586_);
v_k_1587_ = lean_ctor_get(v_x_1572_, 1);
lean_inc(v_k_1587_);
v_v_1588_ = lean_ctor_get(v_x_1572_, 2);
lean_inc(v_v_1588_);
v_l_1589_ = lean_ctor_get(v_x_1572_, 3);
lean_inc(v_l_1589_);
lean_dec(v_x_1572_);
v___x_1590_ = lean_apply_5(v_h__1_1573_, v_size_1586_, v_k_1587_, v_v_1588_, v_l_1589_, lean_box(0));
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1591_, lean_object* v_00_u03b2_1592_, lean_object* v_motive_1593_, lean_object* v_x_1594_, lean_object* v_x_1595_, lean_object* v_h__1_1596_, lean_object* v_h__2_1597_){
_start:
{
lean_object* v_r_1598_; 
v_r_1598_ = lean_ctor_get(v_x_1594_, 4);
if (lean_obj_tag(v_r_1598_) == 0)
{
lean_object* v_size_1599_; lean_object* v_k_1600_; lean_object* v_v_1601_; lean_object* v_l_1602_; lean_object* v_size_1603_; lean_object* v_k_1604_; lean_object* v_v_1605_; lean_object* v_l_1606_; lean_object* v_r_1607_; lean_object* v___x_1608_; 
lean_inc_ref(v_r_1598_);
lean_dec(v_h__1_1596_);
v_size_1599_ = lean_ctor_get(v_x_1594_, 0);
lean_inc(v_size_1599_);
v_k_1600_ = lean_ctor_get(v_x_1594_, 1);
lean_inc(v_k_1600_);
v_v_1601_ = lean_ctor_get(v_x_1594_, 2);
lean_inc(v_v_1601_);
v_l_1602_ = lean_ctor_get(v_x_1594_, 3);
lean_inc(v_l_1602_);
lean_dec(v_x_1594_);
v_size_1603_ = lean_ctor_get(v_r_1598_, 0);
lean_inc(v_size_1603_);
v_k_1604_ = lean_ctor_get(v_r_1598_, 1);
lean_inc(v_k_1604_);
v_v_1605_ = lean_ctor_get(v_r_1598_, 2);
lean_inc(v_v_1605_);
v_l_1606_ = lean_ctor_get(v_r_1598_, 3);
lean_inc(v_l_1606_);
v_r_1607_ = lean_ctor_get(v_r_1598_, 4);
lean_inc(v_r_1607_);
lean_dec_ref(v_r_1598_);
v___x_1608_ = lean_apply_10(v_h__2_1597_, v_size_1599_, v_k_1600_, v_v_1601_, v_l_1602_, v_size_1603_, v_k_1604_, v_v_1605_, v_l_1606_, v_r_1607_, lean_box(0));
return v___x_1608_;
}
else
{
lean_object* v_size_1609_; lean_object* v_k_1610_; lean_object* v_v_1611_; lean_object* v_l_1612_; lean_object* v___x_1613_; 
lean_dec(v_h__2_1597_);
v_size_1609_ = lean_ctor_get(v_x_1594_, 0);
lean_inc(v_size_1609_);
v_k_1610_ = lean_ctor_get(v_x_1594_, 1);
lean_inc(v_k_1610_);
v_v_1611_ = lean_ctor_get(v_x_1594_, 2);
lean_inc(v_v_1611_);
v_l_1612_ = lean_ctor_get(v_x_1594_, 3);
lean_inc(v_l_1612_);
lean_dec(v_x_1594_);
v___x_1613_ = lean_apply_5(v_h__1_1596_, v_size_1609_, v_k_1610_, v_v_1611_, v_l_1612_, lean_box(0));
return v___x_1613_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1615_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1616_ = lean_unsigned_to_nat(13u);
v___x_1617_ = lean_unsigned_to_nat(390u);
v___x_1618_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0));
v___x_1619_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1620_ = l_mkPanicMessageWithDecl(v___x_1619_, v___x_1618_, v___x_1617_, v___x_1616_, v___x_1615_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object* v_inst_1621_, lean_object* v_x_1622_){
_start:
{
if (lean_obj_tag(v_x_1622_) == 0)
{
lean_object* v_r_1623_; 
v_r_1623_ = lean_ctor_get(v_x_1622_, 4);
if (lean_obj_tag(v_r_1623_) == 0)
{
v_x_1622_ = v_r_1623_;
goto _start;
}
else
{
lean_object* v_k_1625_; lean_object* v_v_1626_; lean_object* v___x_1627_; 
v_k_1625_ = lean_ctor_get(v_x_1622_, 1);
v_v_1626_ = lean_ctor_get(v_x_1622_, 2);
lean_inc(v_v_1626_);
lean_inc(v_k_1625_);
v___x_1627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1627_, 0, v_k_1625_);
lean_ctor_set(v___x_1627_, 1, v_v_1626_);
return v___x_1627_;
}
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; 
v___x_1628_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1);
v___x_1629_ = l_panic___redArg(v_inst_1621_, v___x_1628_);
return v___x_1629_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___boxed(lean_object* v_inst_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1630_, v_x_1631_);
lean_dec(v_x_1631_);
lean_dec_ref(v_inst_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21(lean_object* v_00_u03b1_1633_, lean_object* v_00_u03b2_1634_, lean_object* v_inst_1635_, lean_object* v_x_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1635_, v_x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___boxed(lean_object* v_00_u03b1_1638_, lean_object* v_00_u03b2_1639_, lean_object* v_inst_1640_, lean_object* v_x_1641_){
_start:
{
lean_object* v_res_1642_; 
v_res_1642_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21(v_00_u03b1_1638_, v_00_u03b2_1639_, v_inst_1640_, v_x_1641_);
lean_dec(v_x_1641_);
lean_dec_ref(v_inst_1640_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
if (lean_obj_tag(v_x_1643_) == 0)
{
lean_object* v_r_1645_; 
v_r_1645_ = lean_ctor_get(v_x_1643_, 4);
if (lean_obj_tag(v_r_1645_) == 0)
{
v_x_1643_ = v_r_1645_;
goto _start;
}
else
{
lean_object* v_k_1647_; lean_object* v_v_1648_; lean_object* v___x_1649_; 
v_k_1647_ = lean_ctor_get(v_x_1643_, 1);
v_v_1648_ = lean_ctor_get(v_x_1643_, 2);
lean_inc(v_v_1648_);
lean_inc(v_k_1647_);
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v_k_1647_);
lean_ctor_set(v___x_1649_, 1, v_v_1648_);
return v___x_1649_;
}
}
else
{
lean_inc_ref(v_x_1644_);
return v_x_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg___boxed(lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1650_, v_x_1651_);
lean_dec_ref(v_x_1651_);
lean_dec(v_x_1650_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD(lean_object* v_00_u03b1_1653_, lean_object* v_00_u03b2_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1655_, v_x_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___boxed(lean_object* v_00_u03b1_1658_, lean_object* v_00_u03b2_1659_, lean_object* v_x_1660_, lean_object* v_x_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_Std_DTreeMap_Internal_Impl_maxEntryD(v_00_u03b1_1658_, v_00_u03b2_1659_, v_x_1660_, v_x_1661_);
lean_dec_ref(v_x_1661_);
lean_dec(v_x_1660_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1663_, lean_object* v_x_1664_, lean_object* v_h__1_1665_, lean_object* v_h__2_1666_, lean_object* v_h__3_1667_){
_start:
{
if (lean_obj_tag(v_x_1663_) == 0)
{
lean_object* v_r_1668_; 
lean_dec(v_h__1_1665_);
v_r_1668_ = lean_ctor_get(v_x_1663_, 4);
if (lean_obj_tag(v_r_1668_) == 0)
{
lean_object* v_size_1669_; lean_object* v_k_1670_; lean_object* v_v_1671_; lean_object* v_l_1672_; lean_object* v_size_1673_; lean_object* v_k_1674_; lean_object* v_v_1675_; lean_object* v_l_1676_; lean_object* v_r_1677_; lean_object* v___x_1678_; 
lean_inc_ref(v_r_1668_);
lean_dec(v_h__2_1666_);
v_size_1669_ = lean_ctor_get(v_x_1663_, 0);
lean_inc(v_size_1669_);
v_k_1670_ = lean_ctor_get(v_x_1663_, 1);
lean_inc(v_k_1670_);
v_v_1671_ = lean_ctor_get(v_x_1663_, 2);
lean_inc(v_v_1671_);
v_l_1672_ = lean_ctor_get(v_x_1663_, 3);
lean_inc(v_l_1672_);
lean_dec_ref(v_x_1663_);
v_size_1673_ = lean_ctor_get(v_r_1668_, 0);
lean_inc(v_size_1673_);
v_k_1674_ = lean_ctor_get(v_r_1668_, 1);
lean_inc(v_k_1674_);
v_v_1675_ = lean_ctor_get(v_r_1668_, 2);
lean_inc(v_v_1675_);
v_l_1676_ = lean_ctor_get(v_r_1668_, 3);
lean_inc(v_l_1676_);
v_r_1677_ = lean_ctor_get(v_r_1668_, 4);
lean_inc(v_r_1677_);
lean_dec_ref(v_r_1668_);
v___x_1678_ = lean_apply_10(v_h__3_1667_, v_size_1669_, v_k_1670_, v_v_1671_, v_l_1672_, v_size_1673_, v_k_1674_, v_v_1675_, v_l_1676_, v_r_1677_, v_x_1664_);
return v___x_1678_;
}
else
{
lean_object* v_size_1679_; lean_object* v_k_1680_; lean_object* v_v_1681_; lean_object* v_l_1682_; lean_object* v___x_1683_; 
lean_dec(v_h__3_1667_);
v_size_1679_ = lean_ctor_get(v_x_1663_, 0);
lean_inc(v_size_1679_);
v_k_1680_ = lean_ctor_get(v_x_1663_, 1);
lean_inc(v_k_1680_);
v_v_1681_ = lean_ctor_get(v_x_1663_, 2);
lean_inc(v_v_1681_);
v_l_1682_ = lean_ctor_get(v_x_1663_, 3);
lean_inc(v_l_1682_);
lean_dec_ref(v_x_1663_);
v___x_1683_ = lean_apply_5(v_h__2_1666_, v_size_1679_, v_k_1680_, v_v_1681_, v_l_1682_, v_x_1664_);
return v___x_1683_;
}
}
else
{
lean_object* v___x_1684_; 
lean_dec(v_h__3_1667_);
lean_dec(v_h__2_1666_);
v___x_1684_ = lean_apply_1(v_h__1_1665_, v_x_1664_);
return v___x_1684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1685_, lean_object* v_00_u03b2_1686_, lean_object* v_motive_1687_, lean_object* v_x_1688_, lean_object* v_x_1689_, lean_object* v_h__1_1690_, lean_object* v_h__2_1691_, lean_object* v_h__3_1692_){
_start:
{
if (lean_obj_tag(v_x_1688_) == 0)
{
lean_object* v_r_1693_; 
lean_dec(v_h__1_1690_);
v_r_1693_ = lean_ctor_get(v_x_1688_, 4);
if (lean_obj_tag(v_r_1693_) == 0)
{
lean_object* v_size_1694_; lean_object* v_k_1695_; lean_object* v_v_1696_; lean_object* v_l_1697_; lean_object* v_size_1698_; lean_object* v_k_1699_; lean_object* v_v_1700_; lean_object* v_l_1701_; lean_object* v_r_1702_; lean_object* v___x_1703_; 
lean_inc_ref(v_r_1693_);
lean_dec(v_h__2_1691_);
v_size_1694_ = lean_ctor_get(v_x_1688_, 0);
lean_inc(v_size_1694_);
v_k_1695_ = lean_ctor_get(v_x_1688_, 1);
lean_inc(v_k_1695_);
v_v_1696_ = lean_ctor_get(v_x_1688_, 2);
lean_inc(v_v_1696_);
v_l_1697_ = lean_ctor_get(v_x_1688_, 3);
lean_inc(v_l_1697_);
lean_dec_ref(v_x_1688_);
v_size_1698_ = lean_ctor_get(v_r_1693_, 0);
lean_inc(v_size_1698_);
v_k_1699_ = lean_ctor_get(v_r_1693_, 1);
lean_inc(v_k_1699_);
v_v_1700_ = lean_ctor_get(v_r_1693_, 2);
lean_inc(v_v_1700_);
v_l_1701_ = lean_ctor_get(v_r_1693_, 3);
lean_inc(v_l_1701_);
v_r_1702_ = lean_ctor_get(v_r_1693_, 4);
lean_inc(v_r_1702_);
lean_dec_ref(v_r_1693_);
v___x_1703_ = lean_apply_10(v_h__3_1692_, v_size_1694_, v_k_1695_, v_v_1696_, v_l_1697_, v_size_1698_, v_k_1699_, v_v_1700_, v_l_1701_, v_r_1702_, v_x_1689_);
return v___x_1703_;
}
else
{
lean_object* v_size_1704_; lean_object* v_k_1705_; lean_object* v_v_1706_; lean_object* v_l_1707_; lean_object* v___x_1708_; 
lean_dec(v_h__3_1692_);
v_size_1704_ = lean_ctor_get(v_x_1688_, 0);
lean_inc(v_size_1704_);
v_k_1705_ = lean_ctor_get(v_x_1688_, 1);
lean_inc(v_k_1705_);
v_v_1706_ = lean_ctor_get(v_x_1688_, 2);
lean_inc(v_v_1706_);
v_l_1707_ = lean_ctor_get(v_x_1688_, 3);
lean_inc(v_l_1707_);
lean_dec_ref(v_x_1688_);
v___x_1708_ = lean_apply_5(v_h__2_1691_, v_size_1704_, v_k_1705_, v_v_1706_, v_l_1707_, v_x_1689_);
return v___x_1708_;
}
}
else
{
lean_object* v___x_1709_; 
lean_dec(v_h__3_1692_);
lean_dec(v_h__2_1691_);
v___x_1709_ = lean_apply_1(v_h__1_1690_, v_x_1689_);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object* v_x_1710_){
_start:
{
if (lean_obj_tag(v_x_1710_) == 0)
{
lean_object* v_l_1711_; 
v_l_1711_ = lean_ctor_get(v_x_1710_, 3);
if (lean_obj_tag(v_l_1711_) == 0)
{
v_x_1710_ = v_l_1711_;
goto _start;
}
else
{
lean_object* v_k_1713_; lean_object* v___x_1714_; 
v_k_1713_ = lean_ctor_get(v_x_1710_, 1);
lean_inc(v_k_1713_);
v___x_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1714_, 0, v_k_1713_);
return v___x_1714_;
}
}
else
{
lean_object* v___x_1715_; 
v___x_1715_ = lean_box(0);
return v___x_1715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg___boxed(lean_object* v_x_1716_){
_start:
{
lean_object* v_res_1717_; 
v_res_1717_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1716_);
lean_dec(v_x_1716_);
return v_res_1717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f(lean_object* v_00_u03b1_1718_, lean_object* v_00_u03b2_1719_, lean_object* v_x_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___boxed(lean_object* v_00_u03b1_1722_, lean_object* v_00_u03b2_1723_, lean_object* v_x_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f(v_00_u03b1_1722_, v_00_u03b2_1723_, v_x_1724_);
lean_dec(v_x_1724_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object* v_x_1726_){
_start:
{
lean_object* v_l_1727_; 
v_l_1727_ = lean_ctor_get(v_x_1726_, 3);
if (lean_obj_tag(v_l_1727_) == 0)
{
v_x_1726_ = v_l_1727_;
goto _start;
}
else
{
lean_object* v_k_1729_; 
v_k_1729_ = lean_ctor_get(v_x_1726_, 1);
lean_inc(v_k_1729_);
return v_k_1729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg___boxed(lean_object* v_x_1730_){
_start:
{
lean_object* v_res_1731_; 
v_res_1731_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1730_);
lean_dec(v_x_1730_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey(lean_object* v_00_u03b1_1732_, lean_object* v_00_u03b2_1733_, lean_object* v_x_1734_, lean_object* v_x_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1734_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___boxed(lean_object* v_00_u03b1_1737_, lean_object* v_00_u03b2_1738_, lean_object* v_x_1739_, lean_object* v_x_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Std_DTreeMap_Internal_Impl_minKey(v_00_u03b1_1737_, v_00_u03b2_1738_, v_x_1739_, v_x_1740_);
lean_dec(v_x_1739_);
return v_res_1741_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; 
v___x_1743_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1744_ = lean_unsigned_to_nat(13u);
v___x_1745_ = lean_unsigned_to_nat(413u);
v___x_1746_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0));
v___x_1747_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1748_ = l_mkPanicMessageWithDecl(v___x_1747_, v___x_1746_, v___x_1745_, v___x_1744_, v___x_1743_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object* v_inst_1749_, lean_object* v_x_1750_){
_start:
{
if (lean_obj_tag(v_x_1750_) == 0)
{
lean_object* v_l_1751_; 
v_l_1751_ = lean_ctor_get(v_x_1750_, 3);
if (lean_obj_tag(v_l_1751_) == 0)
{
v_x_1750_ = v_l_1751_;
goto _start;
}
else
{
lean_object* v_k_1753_; 
v_k_1753_ = lean_ctor_get(v_x_1750_, 1);
lean_inc(v_k_1753_);
return v_k_1753_;
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1754_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1);
v___x_1755_ = l_panic___redArg(v_inst_1749_, v___x_1754_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___boxed(lean_object* v_inst_1756_, lean_object* v_x_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1756_, v_x_1757_);
lean_dec(v_x_1757_);
lean_dec(v_inst_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21(lean_object* v_00_u03b1_1759_, lean_object* v_00_u03b2_1760_, lean_object* v_inst_1761_, lean_object* v_x_1762_){
_start:
{
lean_object* v___x_1763_; 
v___x_1763_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1761_, v_x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___boxed(lean_object* v_00_u03b1_1764_, lean_object* v_00_u03b2_1765_, lean_object* v_inst_1766_, lean_object* v_x_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Std_DTreeMap_Internal_Impl_minKey_x21(v_00_u03b1_1764_, v_00_u03b2_1765_, v_inst_1766_, v_x_1767_);
lean_dec(v_x_1767_);
lean_dec(v_inst_1766_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object* v_x_1769_, lean_object* v_x_1770_){
_start:
{
if (lean_obj_tag(v_x_1769_) == 0)
{
lean_object* v_l_1771_; 
v_l_1771_ = lean_ctor_get(v_x_1769_, 3);
if (lean_obj_tag(v_l_1771_) == 0)
{
v_x_1769_ = v_l_1771_;
goto _start;
}
else
{
lean_object* v_k_1773_; 
v_k_1773_ = lean_ctor_get(v_x_1769_, 1);
lean_inc(v_k_1773_);
return v_k_1773_;
}
}
else
{
lean_inc(v_x_1770_);
return v_x_1770_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg___boxed(lean_object* v_x_1774_, lean_object* v_x_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1774_, v_x_1775_);
lean_dec(v_x_1775_);
lean_dec(v_x_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD(lean_object* v_00_u03b1_1777_, lean_object* v_00_u03b2_1778_, lean_object* v_x_1779_, lean_object* v_x_1780_){
_start:
{
lean_object* v___x_1781_; 
v___x_1781_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1779_, v_x_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___boxed(lean_object* v_00_u03b1_1782_, lean_object* v_00_u03b2_1783_, lean_object* v_x_1784_, lean_object* v_x_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l_Std_DTreeMap_Internal_Impl_minKeyD(v_00_u03b1_1782_, v_00_u03b2_1783_, v_x_1784_, v_x_1785_);
lean_dec(v_x_1785_);
lean_dec(v_x_1784_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1787_, lean_object* v_x_1788_, lean_object* v_h__1_1789_, lean_object* v_h__2_1790_, lean_object* v_h__3_1791_){
_start:
{
if (lean_obj_tag(v_x_1787_) == 0)
{
lean_object* v_l_1792_; 
lean_dec(v_h__1_1789_);
v_l_1792_ = lean_ctor_get(v_x_1787_, 3);
if (lean_obj_tag(v_l_1792_) == 0)
{
lean_object* v_size_1793_; lean_object* v_k_1794_; lean_object* v_v_1795_; lean_object* v_r_1796_; lean_object* v_size_1797_; lean_object* v_k_1798_; lean_object* v_v_1799_; lean_object* v_l_1800_; lean_object* v_r_1801_; lean_object* v___x_1802_; 
lean_inc_ref(v_l_1792_);
lean_dec(v_h__2_1790_);
v_size_1793_ = lean_ctor_get(v_x_1787_, 0);
lean_inc(v_size_1793_);
v_k_1794_ = lean_ctor_get(v_x_1787_, 1);
lean_inc(v_k_1794_);
v_v_1795_ = lean_ctor_get(v_x_1787_, 2);
lean_inc(v_v_1795_);
v_r_1796_ = lean_ctor_get(v_x_1787_, 4);
lean_inc(v_r_1796_);
lean_dec_ref(v_x_1787_);
v_size_1797_ = lean_ctor_get(v_l_1792_, 0);
lean_inc(v_size_1797_);
v_k_1798_ = lean_ctor_get(v_l_1792_, 1);
lean_inc(v_k_1798_);
v_v_1799_ = lean_ctor_get(v_l_1792_, 2);
lean_inc(v_v_1799_);
v_l_1800_ = lean_ctor_get(v_l_1792_, 3);
lean_inc(v_l_1800_);
v_r_1801_ = lean_ctor_get(v_l_1792_, 4);
lean_inc(v_r_1801_);
lean_dec_ref(v_l_1792_);
v___x_1802_ = lean_apply_10(v_h__3_1791_, v_size_1793_, v_k_1794_, v_v_1795_, v_size_1797_, v_k_1798_, v_v_1799_, v_l_1800_, v_r_1801_, v_r_1796_, v_x_1788_);
return v___x_1802_;
}
else
{
lean_object* v_size_1803_; lean_object* v_k_1804_; lean_object* v_v_1805_; lean_object* v_r_1806_; lean_object* v___x_1807_; 
lean_dec(v_h__3_1791_);
v_size_1803_ = lean_ctor_get(v_x_1787_, 0);
lean_inc(v_size_1803_);
v_k_1804_ = lean_ctor_get(v_x_1787_, 1);
lean_inc(v_k_1804_);
v_v_1805_ = lean_ctor_get(v_x_1787_, 2);
lean_inc(v_v_1805_);
v_r_1806_ = lean_ctor_get(v_x_1787_, 4);
lean_inc(v_r_1806_);
lean_dec_ref(v_x_1787_);
v___x_1807_ = lean_apply_5(v_h__2_1790_, v_size_1803_, v_k_1804_, v_v_1805_, v_r_1806_, v_x_1788_);
return v___x_1807_;
}
}
else
{
lean_object* v___x_1808_; 
lean_dec(v_h__3_1791_);
lean_dec(v_h__2_1790_);
v___x_1808_ = lean_apply_1(v_h__1_1789_, v_x_1788_);
return v___x_1808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1809_, lean_object* v_00_u03b2_1810_, lean_object* v_motive_1811_, lean_object* v_x_1812_, lean_object* v_x_1813_, lean_object* v_h__1_1814_, lean_object* v_h__2_1815_, lean_object* v_h__3_1816_){
_start:
{
if (lean_obj_tag(v_x_1812_) == 0)
{
lean_object* v_l_1817_; 
lean_dec(v_h__1_1814_);
v_l_1817_ = lean_ctor_get(v_x_1812_, 3);
if (lean_obj_tag(v_l_1817_) == 0)
{
lean_object* v_size_1818_; lean_object* v_k_1819_; lean_object* v_v_1820_; lean_object* v_r_1821_; lean_object* v_size_1822_; lean_object* v_k_1823_; lean_object* v_v_1824_; lean_object* v_l_1825_; lean_object* v_r_1826_; lean_object* v___x_1827_; 
lean_inc_ref(v_l_1817_);
lean_dec(v_h__2_1815_);
v_size_1818_ = lean_ctor_get(v_x_1812_, 0);
lean_inc(v_size_1818_);
v_k_1819_ = lean_ctor_get(v_x_1812_, 1);
lean_inc(v_k_1819_);
v_v_1820_ = lean_ctor_get(v_x_1812_, 2);
lean_inc(v_v_1820_);
v_r_1821_ = lean_ctor_get(v_x_1812_, 4);
lean_inc(v_r_1821_);
lean_dec_ref(v_x_1812_);
v_size_1822_ = lean_ctor_get(v_l_1817_, 0);
lean_inc(v_size_1822_);
v_k_1823_ = lean_ctor_get(v_l_1817_, 1);
lean_inc(v_k_1823_);
v_v_1824_ = lean_ctor_get(v_l_1817_, 2);
lean_inc(v_v_1824_);
v_l_1825_ = lean_ctor_get(v_l_1817_, 3);
lean_inc(v_l_1825_);
v_r_1826_ = lean_ctor_get(v_l_1817_, 4);
lean_inc(v_r_1826_);
lean_dec_ref(v_l_1817_);
v___x_1827_ = lean_apply_10(v_h__3_1816_, v_size_1818_, v_k_1819_, v_v_1820_, v_size_1822_, v_k_1823_, v_v_1824_, v_l_1825_, v_r_1826_, v_r_1821_, v_x_1813_);
return v___x_1827_;
}
else
{
lean_object* v_size_1828_; lean_object* v_k_1829_; lean_object* v_v_1830_; lean_object* v_r_1831_; lean_object* v___x_1832_; 
lean_dec(v_h__3_1816_);
v_size_1828_ = lean_ctor_get(v_x_1812_, 0);
lean_inc(v_size_1828_);
v_k_1829_ = lean_ctor_get(v_x_1812_, 1);
lean_inc(v_k_1829_);
v_v_1830_ = lean_ctor_get(v_x_1812_, 2);
lean_inc(v_v_1830_);
v_r_1831_ = lean_ctor_get(v_x_1812_, 4);
lean_inc(v_r_1831_);
lean_dec_ref(v_x_1812_);
v___x_1832_ = lean_apply_5(v_h__2_1815_, v_size_1828_, v_k_1829_, v_v_1830_, v_r_1831_, v_x_1813_);
return v___x_1832_;
}
}
else
{
lean_object* v___x_1833_; 
lean_dec(v_h__3_1816_);
lean_dec(v_h__2_1815_);
v___x_1833_ = lean_apply_1(v_h__1_1814_, v_x_1813_);
return v___x_1833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object* v_x_1834_){
_start:
{
if (lean_obj_tag(v_x_1834_) == 0)
{
lean_object* v_r_1835_; 
v_r_1835_ = lean_ctor_get(v_x_1834_, 4);
if (lean_obj_tag(v_r_1835_) == 0)
{
v_x_1834_ = v_r_1835_;
goto _start;
}
else
{
lean_object* v_k_1837_; lean_object* v___x_1838_; 
v_k_1837_ = lean_ctor_get(v_x_1834_, 1);
lean_inc(v_k_1837_);
v___x_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1838_, 0, v_k_1837_);
return v___x_1838_;
}
}
else
{
lean_object* v___x_1839_; 
v___x_1839_ = lean_box(0);
return v___x_1839_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg___boxed(lean_object* v_x_1840_){
_start:
{
lean_object* v_res_1841_; 
v_res_1841_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1840_);
lean_dec(v_x_1840_);
return v_res_1841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f(lean_object* v_00_u03b1_1842_, lean_object* v_00_u03b2_1843_, lean_object* v_x_1844_){
_start:
{
lean_object* v___x_1845_; 
v___x_1845_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1844_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___boxed(lean_object* v_00_u03b1_1846_, lean_object* v_00_u03b2_1847_, lean_object* v_x_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f(v_00_u03b1_1846_, v_00_u03b2_1847_, v_x_1848_);
lean_dec(v_x_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object* v_x_1850_){
_start:
{
lean_object* v_r_1851_; 
v_r_1851_ = lean_ctor_get(v_x_1850_, 4);
if (lean_obj_tag(v_r_1851_) == 0)
{
v_x_1850_ = v_r_1851_;
goto _start;
}
else
{
lean_object* v_k_1853_; 
v_k_1853_ = lean_ctor_get(v_x_1850_, 1);
lean_inc(v_k_1853_);
return v_k_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg___boxed(lean_object* v_x_1854_){
_start:
{
lean_object* v_res_1855_; 
v_res_1855_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1854_);
lean_dec(v_x_1854_);
return v_res_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey(lean_object* v_00_u03b1_1856_, lean_object* v_00_u03b2_1857_, lean_object* v_x_1858_, lean_object* v_x_1859_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1858_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___boxed(lean_object* v_00_u03b1_1861_, lean_object* v_00_u03b2_1862_, lean_object* v_x_1863_, lean_object* v_x_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Std_DTreeMap_Internal_Impl_maxKey(v_00_u03b1_1861_, v_00_u03b2_1862_, v_x_1863_, v_x_1864_);
lean_dec(v_x_1863_);
return v_res_1865_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1867_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1868_ = lean_unsigned_to_nat(13u);
v___x_1869_ = lean_unsigned_to_nat(436u);
v___x_1870_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0));
v___x_1871_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1872_ = l_mkPanicMessageWithDecl(v___x_1871_, v___x_1870_, v___x_1869_, v___x_1868_, v___x_1867_);
return v___x_1872_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object* v_inst_1873_, lean_object* v_x_1874_){
_start:
{
if (lean_obj_tag(v_x_1874_) == 0)
{
lean_object* v_r_1875_; 
v_r_1875_ = lean_ctor_get(v_x_1874_, 4);
if (lean_obj_tag(v_r_1875_) == 0)
{
v_x_1874_ = v_r_1875_;
goto _start;
}
else
{
lean_object* v_k_1877_; 
v_k_1877_ = lean_ctor_get(v_x_1874_, 1);
lean_inc(v_k_1877_);
return v_k_1877_;
}
}
else
{
lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1878_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1);
v___x_1879_ = l_panic___redArg(v_inst_1873_, v___x_1878_);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___boxed(lean_object* v_inst_1880_, lean_object* v_x_1881_){
_start:
{
lean_object* v_res_1882_; 
v_res_1882_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1880_, v_x_1881_);
lean_dec(v_x_1881_);
lean_dec(v_inst_1880_);
return v_res_1882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21(lean_object* v_00_u03b1_1883_, lean_object* v_00_u03b2_1884_, lean_object* v_inst_1885_, lean_object* v_x_1886_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1885_, v_x_1886_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___boxed(lean_object* v_00_u03b1_1888_, lean_object* v_00_u03b2_1889_, lean_object* v_inst_1890_, lean_object* v_x_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21(v_00_u03b1_1888_, v_00_u03b2_1889_, v_inst_1890_, v_x_1891_);
lean_dec(v_x_1891_);
lean_dec(v_inst_1890_);
return v_res_1892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
if (lean_obj_tag(v_x_1893_) == 0)
{
lean_object* v_r_1895_; 
v_r_1895_ = lean_ctor_get(v_x_1893_, 4);
if (lean_obj_tag(v_r_1895_) == 0)
{
v_x_1893_ = v_r_1895_;
goto _start;
}
else
{
lean_object* v_k_1897_; 
v_k_1897_ = lean_ctor_get(v_x_1893_, 1);
lean_inc(v_k_1897_);
return v_k_1897_;
}
}
else
{
lean_inc(v_x_1894_);
return v_x_1894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg___boxed(lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1898_, v_x_1899_);
lean_dec(v_x_1899_);
lean_dec(v_x_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD(lean_object* v_00_u03b1_1901_, lean_object* v_00_u03b2_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_){
_start:
{
lean_object* v___x_1905_; 
v___x_1905_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1903_, v_x_1904_);
return v___x_1905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___boxed(lean_object* v_00_u03b1_1906_, lean_object* v_00_u03b2_1907_, lean_object* v_x_1908_, lean_object* v_x_1909_){
_start:
{
lean_object* v_res_1910_; 
v_res_1910_ = l_Std_DTreeMap_Internal_Impl_maxKeyD(v_00_u03b1_1906_, v_00_u03b2_1907_, v_x_1908_, v_x_1909_);
lean_dec(v_x_1909_);
lean_dec(v_x_1908_);
return v_res_1910_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1911_, lean_object* v_x_1912_, lean_object* v_h__1_1913_, lean_object* v_h__2_1914_, lean_object* v_h__3_1915_){
_start:
{
if (lean_obj_tag(v_x_1911_) == 0)
{
lean_object* v_r_1916_; 
lean_dec(v_h__1_1913_);
v_r_1916_ = lean_ctor_get(v_x_1911_, 4);
if (lean_obj_tag(v_r_1916_) == 0)
{
lean_object* v_size_1917_; lean_object* v_k_1918_; lean_object* v_v_1919_; lean_object* v_l_1920_; lean_object* v_size_1921_; lean_object* v_k_1922_; lean_object* v_v_1923_; lean_object* v_l_1924_; lean_object* v_r_1925_; lean_object* v___x_1926_; 
lean_inc_ref(v_r_1916_);
lean_dec(v_h__2_1914_);
v_size_1917_ = lean_ctor_get(v_x_1911_, 0);
lean_inc(v_size_1917_);
v_k_1918_ = lean_ctor_get(v_x_1911_, 1);
lean_inc(v_k_1918_);
v_v_1919_ = lean_ctor_get(v_x_1911_, 2);
lean_inc(v_v_1919_);
v_l_1920_ = lean_ctor_get(v_x_1911_, 3);
lean_inc(v_l_1920_);
lean_dec_ref(v_x_1911_);
v_size_1921_ = lean_ctor_get(v_r_1916_, 0);
lean_inc(v_size_1921_);
v_k_1922_ = lean_ctor_get(v_r_1916_, 1);
lean_inc(v_k_1922_);
v_v_1923_ = lean_ctor_get(v_r_1916_, 2);
lean_inc(v_v_1923_);
v_l_1924_ = lean_ctor_get(v_r_1916_, 3);
lean_inc(v_l_1924_);
v_r_1925_ = lean_ctor_get(v_r_1916_, 4);
lean_inc(v_r_1925_);
lean_dec_ref(v_r_1916_);
v___x_1926_ = lean_apply_10(v_h__3_1915_, v_size_1917_, v_k_1918_, v_v_1919_, v_l_1920_, v_size_1921_, v_k_1922_, v_v_1923_, v_l_1924_, v_r_1925_, v_x_1912_);
return v___x_1926_;
}
else
{
lean_object* v_size_1927_; lean_object* v_k_1928_; lean_object* v_v_1929_; lean_object* v_l_1930_; lean_object* v___x_1931_; 
lean_dec(v_h__3_1915_);
v_size_1927_ = lean_ctor_get(v_x_1911_, 0);
lean_inc(v_size_1927_);
v_k_1928_ = lean_ctor_get(v_x_1911_, 1);
lean_inc(v_k_1928_);
v_v_1929_ = lean_ctor_get(v_x_1911_, 2);
lean_inc(v_v_1929_);
v_l_1930_ = lean_ctor_get(v_x_1911_, 3);
lean_inc(v_l_1930_);
lean_dec_ref(v_x_1911_);
v___x_1931_ = lean_apply_5(v_h__2_1914_, v_size_1927_, v_k_1928_, v_v_1929_, v_l_1930_, v_x_1912_);
return v___x_1931_;
}
}
else
{
lean_object* v___x_1932_; 
lean_dec(v_h__3_1915_);
lean_dec(v_h__2_1914_);
v___x_1932_ = lean_apply_1(v_h__1_1913_, v_x_1912_);
return v___x_1932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1933_, lean_object* v_00_u03b2_1934_, lean_object* v_motive_1935_, lean_object* v_x_1936_, lean_object* v_x_1937_, lean_object* v_h__1_1938_, lean_object* v_h__2_1939_, lean_object* v_h__3_1940_){
_start:
{
if (lean_obj_tag(v_x_1936_) == 0)
{
lean_object* v_r_1941_; 
lean_dec(v_h__1_1938_);
v_r_1941_ = lean_ctor_get(v_x_1936_, 4);
if (lean_obj_tag(v_r_1941_) == 0)
{
lean_object* v_size_1942_; lean_object* v_k_1943_; lean_object* v_v_1944_; lean_object* v_l_1945_; lean_object* v_size_1946_; lean_object* v_k_1947_; lean_object* v_v_1948_; lean_object* v_l_1949_; lean_object* v_r_1950_; lean_object* v___x_1951_; 
lean_inc_ref(v_r_1941_);
lean_dec(v_h__2_1939_);
v_size_1942_ = lean_ctor_get(v_x_1936_, 0);
lean_inc(v_size_1942_);
v_k_1943_ = lean_ctor_get(v_x_1936_, 1);
lean_inc(v_k_1943_);
v_v_1944_ = lean_ctor_get(v_x_1936_, 2);
lean_inc(v_v_1944_);
v_l_1945_ = lean_ctor_get(v_x_1936_, 3);
lean_inc(v_l_1945_);
lean_dec_ref(v_x_1936_);
v_size_1946_ = lean_ctor_get(v_r_1941_, 0);
lean_inc(v_size_1946_);
v_k_1947_ = lean_ctor_get(v_r_1941_, 1);
lean_inc(v_k_1947_);
v_v_1948_ = lean_ctor_get(v_r_1941_, 2);
lean_inc(v_v_1948_);
v_l_1949_ = lean_ctor_get(v_r_1941_, 3);
lean_inc(v_l_1949_);
v_r_1950_ = lean_ctor_get(v_r_1941_, 4);
lean_inc(v_r_1950_);
lean_dec_ref(v_r_1941_);
v___x_1951_ = lean_apply_10(v_h__3_1940_, v_size_1942_, v_k_1943_, v_v_1944_, v_l_1945_, v_size_1946_, v_k_1947_, v_v_1948_, v_l_1949_, v_r_1950_, v_x_1937_);
return v___x_1951_;
}
else
{
lean_object* v_size_1952_; lean_object* v_k_1953_; lean_object* v_v_1954_; lean_object* v_l_1955_; lean_object* v___x_1956_; 
lean_dec(v_h__3_1940_);
v_size_1952_ = lean_ctor_get(v_x_1936_, 0);
lean_inc(v_size_1952_);
v_k_1953_ = lean_ctor_get(v_x_1936_, 1);
lean_inc(v_k_1953_);
v_v_1954_ = lean_ctor_get(v_x_1936_, 2);
lean_inc(v_v_1954_);
v_l_1955_ = lean_ctor_get(v_x_1936_, 3);
lean_inc(v_l_1955_);
lean_dec_ref(v_x_1936_);
v___x_1956_ = lean_apply_5(v_h__2_1939_, v_size_1952_, v_k_1953_, v_v_1954_, v_l_1955_, v_x_1937_);
return v___x_1956_;
}
}
else
{
lean_object* v___x_1957_; 
lean_dec(v_h__3_1940_);
lean_dec(v_h__2_1939_);
v___x_1957_ = lean_apply_1(v_h__1_1938_, v_x_1937_);
return v___x_1957_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object* v_x_1958_, lean_object* v_x_1959_){
_start:
{
lean_object* v_k_1960_; lean_object* v_v_1961_; lean_object* v_l_1962_; lean_object* v_r_1963_; lean_object* v___y_1965_; lean_object* v___y_1971_; 
v_k_1960_ = lean_ctor_get(v_x_1958_, 1);
v_v_1961_ = lean_ctor_get(v_x_1958_, 2);
v_l_1962_ = lean_ctor_get(v_x_1958_, 3);
v_r_1963_ = lean_ctor_get(v_x_1958_, 4);
if (lean_obj_tag(v_l_1962_) == 0)
{
lean_object* v_size_1978_; 
v_size_1978_ = lean_ctor_get(v_l_1962_, 0);
v___y_1971_ = v_size_1978_;
goto v___jp_1970_;
}
else
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_unsigned_to_nat(0u);
v___y_1971_ = v___x_1979_;
goto v___jp_1970_;
}
v___jp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1966_ = lean_nat_sub(v_x_1959_, v___y_1965_);
lean_dec(v_x_1959_);
v___x_1967_ = lean_unsigned_to_nat(1u);
v___x_1968_ = lean_nat_sub(v___x_1966_, v___x_1967_);
lean_dec(v___x_1966_);
v_x_1958_ = v_r_1963_;
v_x_1959_ = v___x_1968_;
goto _start;
}
v___jp_1970_:
{
uint8_t v___x_1972_; 
v___x_1972_ = lean_nat_dec_lt(v_x_1959_, v___y_1971_);
if (v___x_1972_ == 0)
{
uint8_t v___x_1973_; 
v___x_1973_ = lean_nat_dec_eq(v_x_1959_, v___y_1971_);
if (v___x_1973_ == 0)
{
if (lean_obj_tag(v_l_1962_) == 0)
{
lean_object* v_size_1974_; 
v_size_1974_ = lean_ctor_get(v_l_1962_, 0);
v___y_1965_ = v_size_1974_;
goto v___jp_1964_;
}
else
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_unsigned_to_nat(0u);
v___y_1965_ = v___x_1975_;
goto v___jp_1964_;
}
}
else
{
lean_object* v___x_1976_; 
lean_dec(v_x_1959_);
lean_inc(v_v_1961_);
lean_inc(v_k_1960_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v_k_1960_);
lean_ctor_set(v___x_1976_, 1, v_v_1961_);
return v___x_1976_;
}
}
else
{
v_x_1958_ = v_l_1962_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg___boxed(lean_object* v_x_1980_, lean_object* v_x_1981_){
_start:
{
lean_object* v_res_1982_; 
v_res_1982_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1980_, v_x_1981_);
lean_dec(v_x_1980_);
return v_res_1982_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx(lean_object* v_00_u03b1_1983_, lean_object* v_00_u03b2_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1985_, v_x_1987_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___boxed(lean_object* v_00_u03b1_1990_, lean_object* v_00_u03b2_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx(v_00_u03b1_1990_, v_00_u03b2_1991_, v_x_1992_, v_x_1993_, v_x_1994_, v_x_1995_);
lean_dec(v_x_1992_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object* v_x_1997_, lean_object* v_x_1998_){
_start:
{
if (lean_obj_tag(v_x_1997_) == 0)
{
lean_object* v_k_1999_; lean_object* v_v_2000_; lean_object* v_l_2001_; lean_object* v_r_2002_; lean_object* v___y_2004_; lean_object* v___y_2010_; 
v_k_1999_ = lean_ctor_get(v_x_1997_, 1);
v_v_2000_ = lean_ctor_get(v_x_1997_, 2);
v_l_2001_ = lean_ctor_get(v_x_1997_, 3);
v_r_2002_ = lean_ctor_get(v_x_1997_, 4);
if (lean_obj_tag(v_l_2001_) == 0)
{
lean_object* v_size_2018_; 
v_size_2018_ = lean_ctor_get(v_l_2001_, 0);
v___y_2010_ = v_size_2018_;
goto v___jp_2009_;
}
else
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_unsigned_to_nat(0u);
v___y_2010_ = v___x_2019_;
goto v___jp_2009_;
}
v___jp_2003_:
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2005_ = lean_nat_sub(v_x_1998_, v___y_2004_);
lean_dec(v_x_1998_);
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_sub(v___x_2005_, v___x_2006_);
lean_dec(v___x_2005_);
v_x_1997_ = v_r_2002_;
v_x_1998_ = v___x_2007_;
goto _start;
}
v___jp_2009_:
{
uint8_t v___x_2011_; 
v___x_2011_ = lean_nat_dec_lt(v_x_1998_, v___y_2010_);
if (v___x_2011_ == 0)
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_nat_dec_eq(v_x_1998_, v___y_2010_);
if (v___x_2012_ == 0)
{
if (lean_obj_tag(v_l_2001_) == 0)
{
lean_object* v_size_2013_; 
v_size_2013_ = lean_ctor_get(v_l_2001_, 0);
v___y_2004_ = v_size_2013_;
goto v___jp_2003_;
}
else
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_unsigned_to_nat(0u);
v___y_2004_ = v___x_2014_;
goto v___jp_2003_;
}
}
else
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_dec(v_x_1998_);
lean_inc(v_v_2000_);
lean_inc(v_k_1999_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v_k_1999_);
lean_ctor_set(v___x_2015_, 1, v_v_2000_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
return v___x_2016_;
}
}
else
{
v_x_1997_ = v_l_2001_;
goto _start;
}
}
}
else
{
lean_object* v___x_2020_; 
lean_dec(v_x_1998_);
v___x_2020_ = lean_box(0);
return v___x_2020_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_2021_, v_x_2022_);
lean_dec(v_x_2021_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_){
_start:
{
lean_object* v___x_2028_; 
v___x_2028_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_2026_, v_x_2027_);
return v___x_2028_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_2029_, lean_object* v_00_u03b2_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_){
_start:
{
lean_object* v_res_2033_; 
v_res_2033_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(v_00_u03b1_2029_, v_00_u03b2_2030_, v_x_2031_, v_x_2032_);
lean_dec(v_x_2031_);
return v_res_2033_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2036_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_2037_ = lean_unsigned_to_nat(16u);
v___x_2038_ = lean_unsigned_to_nat(467u);
v___x_2039_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0));
v___x_2040_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_2041_ = l_mkPanicMessageWithDecl(v___x_2040_, v___x_2039_, v___x_2038_, v___x_2037_, v___x_2036_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(lean_object* v_inst_2042_, lean_object* v_x_2043_, lean_object* v_x_2044_){
_start:
{
if (lean_obj_tag(v_x_2043_) == 0)
{
lean_object* v_k_2045_; lean_object* v_v_2046_; lean_object* v_l_2047_; lean_object* v_r_2048_; lean_object* v___y_2050_; lean_object* v___y_2056_; 
v_k_2045_ = lean_ctor_get(v_x_2043_, 1);
v_v_2046_ = lean_ctor_get(v_x_2043_, 2);
v_l_2047_ = lean_ctor_get(v_x_2043_, 3);
v_r_2048_ = lean_ctor_get(v_x_2043_, 4);
if (lean_obj_tag(v_l_2047_) == 0)
{
lean_object* v_size_2063_; 
v_size_2063_ = lean_ctor_get(v_l_2047_, 0);
v___y_2056_ = v_size_2063_;
goto v___jp_2055_;
}
else
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_unsigned_to_nat(0u);
v___y_2056_ = v___x_2064_;
goto v___jp_2055_;
}
v___jp_2049_:
{
lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v___x_2051_ = lean_nat_sub(v_x_2044_, v___y_2050_);
lean_dec(v_x_2044_);
v___x_2052_ = lean_unsigned_to_nat(1u);
v___x_2053_ = lean_nat_sub(v___x_2051_, v___x_2052_);
lean_dec(v___x_2051_);
v_x_2043_ = v_r_2048_;
v_x_2044_ = v___x_2053_;
goto _start;
}
v___jp_2055_:
{
uint8_t v___x_2057_; 
v___x_2057_ = lean_nat_dec_lt(v_x_2044_, v___y_2056_);
if (v___x_2057_ == 0)
{
uint8_t v___x_2058_; 
v___x_2058_ = lean_nat_dec_eq(v_x_2044_, v___y_2056_);
if (v___x_2058_ == 0)
{
if (lean_obj_tag(v_l_2047_) == 0)
{
lean_object* v_size_2059_; 
v_size_2059_ = lean_ctor_get(v_l_2047_, 0);
v___y_2050_ = v_size_2059_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2060_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v___y_2050_ = v___x_2060_;
goto v___jp_2049_;
}
}
else
{
lean_object* v___x_2061_; 
lean_dec(v_x_2044_);
lean_inc(v_v_2046_);
lean_inc(v_k_2045_);
v___x_2061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2061_, 0, v_k_2045_);
lean_ctor_set(v___x_2061_, 1, v_v_2046_);
return v___x_2061_;
}
}
else
{
v_x_2043_ = v_l_2047_;
goto _start;
}
}
}
else
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
lean_dec(v_x_2044_);
v___x_2065_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2);
v___x_2066_ = l_panic___redArg(v_inst_2042_, v___x_2065_);
return v___x_2066_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_2067_, lean_object* v_x_2068_, lean_object* v_x_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2067_, v_x_2068_, v_x_2069_);
lean_dec(v_x_2068_);
lean_dec_ref(v_inst_2067_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(lean_object* v_00_u03b1_2071_, lean_object* v_00_u03b2_2072_, lean_object* v_inst_2073_, lean_object* v_x_2074_, lean_object* v_x_2075_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2073_, v_x_2074_, v_x_2075_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_2077_, lean_object* v_00_u03b2_2078_, lean_object* v_inst_2079_, lean_object* v_x_2080_, lean_object* v_x_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(v_00_u03b1_2077_, v_00_u03b2_2078_, v_inst_2079_, v_x_2080_, v_x_2081_);
lean_dec(v_x_2080_);
lean_dec_ref(v_inst_2079_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_){
_start:
{
if (lean_obj_tag(v_x_2083_) == 0)
{
lean_object* v_k_2086_; lean_object* v_v_2087_; lean_object* v_l_2088_; lean_object* v_r_2089_; lean_object* v___y_2091_; lean_object* v___y_2097_; 
v_k_2086_ = lean_ctor_get(v_x_2083_, 1);
v_v_2087_ = lean_ctor_get(v_x_2083_, 2);
v_l_2088_ = lean_ctor_get(v_x_2083_, 3);
v_r_2089_ = lean_ctor_get(v_x_2083_, 4);
if (lean_obj_tag(v_l_2088_) == 0)
{
lean_object* v_size_2104_; 
v_size_2104_ = lean_ctor_get(v_l_2088_, 0);
v___y_2097_ = v_size_2104_;
goto v___jp_2096_;
}
else
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_unsigned_to_nat(0u);
v___y_2097_ = v___x_2105_;
goto v___jp_2096_;
}
v___jp_2090_:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_nat_sub(v_x_2084_, v___y_2091_);
lean_dec(v_x_2084_);
v___x_2093_ = lean_unsigned_to_nat(1u);
v___x_2094_ = lean_nat_sub(v___x_2092_, v___x_2093_);
lean_dec(v___x_2092_);
v_x_2083_ = v_r_2089_;
v_x_2084_ = v___x_2094_;
goto _start;
}
v___jp_2096_:
{
uint8_t v___x_2098_; 
v___x_2098_ = lean_nat_dec_lt(v_x_2084_, v___y_2097_);
if (v___x_2098_ == 0)
{
uint8_t v___x_2099_; 
v___x_2099_ = lean_nat_dec_eq(v_x_2084_, v___y_2097_);
if (v___x_2099_ == 0)
{
if (lean_obj_tag(v_l_2088_) == 0)
{
lean_object* v_size_2100_; 
v_size_2100_ = lean_ctor_get(v_l_2088_, 0);
v___y_2091_ = v_size_2100_;
goto v___jp_2090_;
}
else
{
lean_object* v___x_2101_; 
v___x_2101_ = lean_unsigned_to_nat(0u);
v___y_2091_ = v___x_2101_;
goto v___jp_2090_;
}
}
else
{
lean_object* v___x_2102_; 
lean_dec(v_x_2084_);
lean_inc(v_v_2087_);
lean_inc(v_k_2086_);
v___x_2102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2102_, 0, v_k_2086_);
lean_ctor_set(v___x_2102_, 1, v_v_2087_);
return v___x_2102_;
}
}
else
{
v_x_2083_ = v_l_2088_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2084_);
lean_inc_ref(v_x_2085_);
return v_x_2085_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg___boxed(lean_object* v_x_2106_, lean_object* v_x_2107_, lean_object* v_x_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2106_, v_x_2107_, v_x_2108_);
lean_dec_ref(v_x_2108_);
lean_dec(v_x_2106_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD(lean_object* v_00_u03b1_2110_, lean_object* v_00_u03b2_2111_, lean_object* v_x_2112_, lean_object* v_x_2113_, lean_object* v_x_2114_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2112_, v_x_2113_, v_x_2114_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_00_u03b2_2117_, lean_object* v_x_2118_, lean_object* v_x_2119_, lean_object* v_x_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD(v_00_u03b1_2116_, v_00_u03b2_2117_, v_x_2118_, v_x_2119_, v_x_2120_);
lean_dec_ref(v_x_2120_);
lean_dec(v_x_2118_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object* v_x_2122_, lean_object* v_x_2123_){
_start:
{
lean_object* v_k_2124_; lean_object* v_l_2125_; lean_object* v_r_2126_; lean_object* v___y_2128_; lean_object* v___y_2134_; 
v_k_2124_ = lean_ctor_get(v_x_2122_, 1);
v_l_2125_ = lean_ctor_get(v_x_2122_, 3);
v_r_2126_ = lean_ctor_get(v_x_2122_, 4);
if (lean_obj_tag(v_l_2125_) == 0)
{
lean_object* v_size_2140_; 
v_size_2140_ = lean_ctor_get(v_l_2125_, 0);
v___y_2134_ = v_size_2140_;
goto v___jp_2133_;
}
else
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_unsigned_to_nat(0u);
v___y_2134_ = v___x_2141_;
goto v___jp_2133_;
}
v___jp_2127_:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_nat_sub(v_x_2123_, v___y_2128_);
lean_dec(v_x_2123_);
v___x_2130_ = lean_unsigned_to_nat(1u);
v___x_2131_ = lean_nat_sub(v___x_2129_, v___x_2130_);
lean_dec(v___x_2129_);
v_x_2122_ = v_r_2126_;
v_x_2123_ = v___x_2131_;
goto _start;
}
v___jp_2133_:
{
uint8_t v___x_2135_; 
v___x_2135_ = lean_nat_dec_lt(v_x_2123_, v___y_2134_);
if (v___x_2135_ == 0)
{
uint8_t v___x_2136_; 
v___x_2136_ = lean_nat_dec_eq(v_x_2123_, v___y_2134_);
if (v___x_2136_ == 0)
{
if (lean_obj_tag(v_l_2125_) == 0)
{
lean_object* v_size_2137_; 
v_size_2137_ = lean_ctor_get(v_l_2125_, 0);
v___y_2128_ = v_size_2137_;
goto v___jp_2127_;
}
else
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_unsigned_to_nat(0u);
v___y_2128_ = v___x_2138_;
goto v___jp_2127_;
}
}
else
{
lean_dec(v_x_2123_);
lean_inc(v_k_2124_);
return v_k_2124_;
}
}
else
{
v_x_2122_ = v_l_2125_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg___boxed(lean_object* v_x_2142_, lean_object* v_x_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2142_, v_x_2143_);
lean_dec(v_x_2142_);
return v_res_2144_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx(lean_object* v_00_u03b1_2145_, lean_object* v_00_u03b2_2146_, lean_object* v_x_2147_, lean_object* v_x_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_){
_start:
{
lean_object* v___x_2151_; 
v___x_2151_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2147_, v_x_2149_);
return v___x_2151_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___boxed(lean_object* v_00_u03b1_2152_, lean_object* v_00_u03b2_2153_, lean_object* v_x_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx(v_00_u03b1_2152_, v_00_u03b2_2153_, v_x_2154_, v_x_2155_, v_x_2156_, v_x_2157_);
lean_dec(v_x_2154_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object* v_x_2159_, lean_object* v_x_2160_){
_start:
{
if (lean_obj_tag(v_x_2159_) == 0)
{
lean_object* v_k_2161_; lean_object* v_l_2162_; lean_object* v_r_2163_; lean_object* v___y_2165_; lean_object* v___y_2171_; 
v_k_2161_ = lean_ctor_get(v_x_2159_, 1);
v_l_2162_ = lean_ctor_get(v_x_2159_, 3);
v_r_2163_ = lean_ctor_get(v_x_2159_, 4);
if (lean_obj_tag(v_l_2162_) == 0)
{
lean_object* v_size_2178_; 
v_size_2178_ = lean_ctor_get(v_l_2162_, 0);
v___y_2171_ = v_size_2178_;
goto v___jp_2170_;
}
else
{
lean_object* v___x_2179_; 
v___x_2179_ = lean_unsigned_to_nat(0u);
v___y_2171_ = v___x_2179_;
goto v___jp_2170_;
}
v___jp_2164_:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_nat_sub(v_x_2160_, v___y_2165_);
lean_dec(v_x_2160_);
v___x_2167_ = lean_unsigned_to_nat(1u);
v___x_2168_ = lean_nat_sub(v___x_2166_, v___x_2167_);
lean_dec(v___x_2166_);
v_x_2159_ = v_r_2163_;
v_x_2160_ = v___x_2168_;
goto _start;
}
v___jp_2170_:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_nat_dec_lt(v_x_2160_, v___y_2171_);
if (v___x_2172_ == 0)
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_nat_dec_eq(v_x_2160_, v___y_2171_);
if (v___x_2173_ == 0)
{
if (lean_obj_tag(v_l_2162_) == 0)
{
lean_object* v_size_2174_; 
v_size_2174_ = lean_ctor_get(v_l_2162_, 0);
v___y_2165_ = v_size_2174_;
goto v___jp_2164_;
}
else
{
lean_object* v___x_2175_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___y_2165_ = v___x_2175_;
goto v___jp_2164_;
}
}
else
{
lean_object* v___x_2176_; 
lean_dec(v_x_2160_);
lean_inc(v_k_2161_);
v___x_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_k_2161_);
return v___x_2176_;
}
}
else
{
v_x_2159_ = v_l_2162_;
goto _start;
}
}
}
else
{
lean_object* v___x_2180_; 
lean_dec(v_x_2160_);
v___x_2180_ = lean_box(0);
return v___x_2180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg___boxed(lean_object* v_x_2181_, lean_object* v_x_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2181_, v_x_2182_);
lean_dec(v_x_2181_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(lean_object* v_00_u03b1_2184_, lean_object* v_00_u03b2_2185_, lean_object* v_x_2186_, lean_object* v_x_2187_){
_start:
{
lean_object* v___x_2188_; 
v___x_2188_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2186_, v_x_2187_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_2189_, lean_object* v_00_u03b2_2190_, lean_object* v_x_2191_, lean_object* v_x_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(v_00_u03b1_2189_, v_00_u03b2_2190_, v_x_2191_, v_x_2192_);
lean_dec(v_x_2191_);
return v_res_2193_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2195_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_2196_ = lean_unsigned_to_nat(16u);
v___x_2197_ = lean_unsigned_to_nat(503u);
v___x_2198_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0));
v___x_2199_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_2200_ = l_mkPanicMessageWithDecl(v___x_2199_, v___x_2198_, v___x_2197_, v___x_2196_, v___x_2195_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object* v_inst_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_){
_start:
{
if (lean_obj_tag(v_x_2202_) == 0)
{
lean_object* v_k_2204_; lean_object* v_l_2205_; lean_object* v_r_2206_; lean_object* v___y_2208_; lean_object* v___y_2214_; 
v_k_2204_ = lean_ctor_get(v_x_2202_, 1);
v_l_2205_ = lean_ctor_get(v_x_2202_, 3);
v_r_2206_ = lean_ctor_get(v_x_2202_, 4);
if (lean_obj_tag(v_l_2205_) == 0)
{
lean_object* v_size_2220_; 
v_size_2220_ = lean_ctor_get(v_l_2205_, 0);
v___y_2214_ = v_size_2220_;
goto v___jp_2213_;
}
else
{
lean_object* v___x_2221_; 
v___x_2221_ = lean_unsigned_to_nat(0u);
v___y_2214_ = v___x_2221_;
goto v___jp_2213_;
}
v___jp_2207_:
{
lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
v___x_2209_ = lean_nat_sub(v_x_2203_, v___y_2208_);
lean_dec(v_x_2203_);
v___x_2210_ = lean_unsigned_to_nat(1u);
v___x_2211_ = lean_nat_sub(v___x_2209_, v___x_2210_);
lean_dec(v___x_2209_);
v_x_2202_ = v_r_2206_;
v_x_2203_ = v___x_2211_;
goto _start;
}
v___jp_2213_:
{
uint8_t v___x_2215_; 
v___x_2215_ = lean_nat_dec_lt(v_x_2203_, v___y_2214_);
if (v___x_2215_ == 0)
{
uint8_t v___x_2216_; 
v___x_2216_ = lean_nat_dec_eq(v_x_2203_, v___y_2214_);
if (v___x_2216_ == 0)
{
if (lean_obj_tag(v_l_2205_) == 0)
{
lean_object* v_size_2217_; 
v_size_2217_ = lean_ctor_get(v_l_2205_, 0);
v___y_2208_ = v_size_2217_;
goto v___jp_2207_;
}
else
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_unsigned_to_nat(0u);
v___y_2208_ = v___x_2218_;
goto v___jp_2207_;
}
}
else
{
lean_dec(v_x_2203_);
lean_inc(v_k_2204_);
return v_k_2204_;
}
}
else
{
v_x_2202_ = v_l_2205_;
goto _start;
}
}
}
else
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec(v_x_2203_);
v___x_2222_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1);
v___x_2223_ = l_panic___redArg(v_inst_2201_, v___x_2222_);
return v___x_2223_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_2224_, lean_object* v_x_2225_, lean_object* v_x_2226_){
_start:
{
lean_object* v_res_2227_; 
v_res_2227_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2224_, v_x_2225_, v_x_2226_);
lean_dec(v_x_2225_);
lean_dec(v_inst_2224_);
return v_res_2227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(lean_object* v_00_u03b1_2228_, lean_object* v_00_u03b2_2229_, lean_object* v_inst_2230_, lean_object* v_x_2231_, lean_object* v_x_2232_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2230_, v_x_2231_, v_x_2232_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_2234_, lean_object* v_00_u03b2_2235_, lean_object* v_inst_2236_, lean_object* v_x_2237_, lean_object* v_x_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(v_00_u03b1_2234_, v_00_u03b2_2235_, v_inst_2236_, v_x_2237_, v_x_2238_);
lean_dec(v_x_2237_);
lean_dec(v_inst_2236_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object* v_x_2240_, lean_object* v_x_2241_, lean_object* v_x_2242_){
_start:
{
if (lean_obj_tag(v_x_2240_) == 0)
{
lean_object* v_k_2243_; lean_object* v_l_2244_; lean_object* v_r_2245_; lean_object* v___y_2247_; lean_object* v___y_2253_; 
v_k_2243_ = lean_ctor_get(v_x_2240_, 1);
v_l_2244_ = lean_ctor_get(v_x_2240_, 3);
v_r_2245_ = lean_ctor_get(v_x_2240_, 4);
if (lean_obj_tag(v_l_2244_) == 0)
{
lean_object* v_size_2259_; 
v_size_2259_ = lean_ctor_get(v_l_2244_, 0);
v___y_2253_ = v_size_2259_;
goto v___jp_2252_;
}
else
{
lean_object* v___x_2260_; 
v___x_2260_ = lean_unsigned_to_nat(0u);
v___y_2253_ = v___x_2260_;
goto v___jp_2252_;
}
v___jp_2246_:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2248_ = lean_nat_sub(v_x_2241_, v___y_2247_);
lean_dec(v_x_2241_);
v___x_2249_ = lean_unsigned_to_nat(1u);
v___x_2250_ = lean_nat_sub(v___x_2248_, v___x_2249_);
lean_dec(v___x_2248_);
v_x_2240_ = v_r_2245_;
v_x_2241_ = v___x_2250_;
goto _start;
}
v___jp_2252_:
{
uint8_t v___x_2254_; 
v___x_2254_ = lean_nat_dec_lt(v_x_2241_, v___y_2253_);
if (v___x_2254_ == 0)
{
uint8_t v___x_2255_; 
v___x_2255_ = lean_nat_dec_eq(v_x_2241_, v___y_2253_);
if (v___x_2255_ == 0)
{
if (lean_obj_tag(v_l_2244_) == 0)
{
lean_object* v_size_2256_; 
v_size_2256_ = lean_ctor_get(v_l_2244_, 0);
v___y_2247_ = v_size_2256_;
goto v___jp_2246_;
}
else
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_unsigned_to_nat(0u);
v___y_2247_ = v___x_2257_;
goto v___jp_2246_;
}
}
else
{
lean_dec(v_x_2241_);
lean_inc(v_k_2243_);
return v_k_2243_;
}
}
else
{
v_x_2240_ = v_l_2244_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2241_);
lean_inc(v_x_2242_);
return v_x_2242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg___boxed(lean_object* v_x_2261_, lean_object* v_x_2262_, lean_object* v_x_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2261_, v_x_2262_, v_x_2263_);
lean_dec(v_x_2263_);
lean_dec(v_x_2261_);
return v_res_2264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD(lean_object* v_00_u03b1_2265_, lean_object* v_00_u03b2_2266_, lean_object* v_x_2267_, lean_object* v_x_2268_, lean_object* v_x_2269_){
_start:
{
lean_object* v___x_2270_; 
v___x_2270_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2267_, v_x_2268_, v_x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___boxed(lean_object* v_00_u03b1_2271_, lean_object* v_00_u03b2_2272_, lean_object* v_x_2273_, lean_object* v_x_2274_, lean_object* v_x_2275_){
_start:
{
lean_object* v_res_2276_; 
v_res_2276_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD(v_00_u03b1_2271_, v_00_u03b2_2272_, v_x_2273_, v_x_2274_, v_x_2275_);
lean_dec(v_x_2275_);
lean_dec(v_x_2273_);
return v_res_2276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object* v_inst_2277_, lean_object* v_k_2278_, lean_object* v_best_2279_, lean_object* v_a_2280_){
_start:
{
if (lean_obj_tag(v_a_2280_) == 0)
{
lean_object* v_k_2281_; lean_object* v_v_2282_; lean_object* v_l_2283_; lean_object* v_r_2284_; lean_object* v___x_2285_; uint8_t v___x_2286_; 
v_k_2281_ = lean_ctor_get(v_a_2280_, 1);
lean_inc_n(v_k_2281_, 2);
v_v_2282_ = lean_ctor_get(v_a_2280_, 2);
lean_inc(v_v_2282_);
v_l_2283_ = lean_ctor_get(v_a_2280_, 3);
lean_inc(v_l_2283_);
v_r_2284_ = lean_ctor_get(v_a_2280_, 4);
lean_inc(v_r_2284_);
lean_dec_ref(v_a_2280_);
lean_inc_ref(v_inst_2277_);
lean_inc(v_k_2278_);
v___x_2285_ = lean_apply_2(v_inst_2277_, v_k_2278_, v_k_2281_);
v___x_2286_ = lean_unbox(v___x_2285_);
switch(v___x_2286_)
{
case 0:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec(v_r_2284_);
lean_dec(v_best_2279_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_k_2281_);
lean_ctor_set(v___x_2287_, 1, v_v_2282_);
v___x_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
v_best_2279_ = v___x_2288_;
v_a_2280_ = v_l_2283_;
goto _start;
}
case 1:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
lean_dec(v_r_2284_);
lean_dec(v_l_2283_);
lean_dec(v_best_2279_);
lean_dec(v_k_2278_);
lean_dec_ref(v_inst_2277_);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v_k_2281_);
lean_ctor_set(v___x_2290_, 1, v_v_2282_);
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
return v___x_2291_;
}
default: 
{
lean_dec(v_l_2283_);
lean_dec(v_v_2282_);
lean_dec(v_k_2281_);
v_a_2280_ = v_r_2284_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2278_);
lean_dec_ref(v_inst_2277_);
return v_best_2279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go(lean_object* v_00_u03b1_2293_, lean_object* v_00_u03b2_2294_, lean_object* v_inst_2295_, lean_object* v_k_2296_, lean_object* v_best_2297_, lean_object* v_a_2298_){
_start:
{
lean_object* v___x_2299_; 
v___x_2299_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2295_, v_k_2296_, v_best_2297_, v_a_2298_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___redArg(lean_object* v_inst_2300_, lean_object* v_k_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_box(0);
v___x_2304_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2300_, v_k_2301_, v___x_2303_, v_a_2302_);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f(lean_object* v_00_u03b1_2305_, lean_object* v_00_u03b2_2306_, lean_object* v_inst_2307_, lean_object* v_k_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2310_ = lean_box(0);
v___x_2311_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2307_, v_k_2308_, v___x_2310_, v_a_2309_);
return v___x_2311_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object* v_inst_2312_, lean_object* v_k_2313_, lean_object* v_best_2314_, lean_object* v_a_2315_){
_start:
{
if (lean_obj_tag(v_a_2315_) == 0)
{
lean_object* v_k_2316_; lean_object* v_v_2317_; lean_object* v_l_2318_; lean_object* v_r_2319_; lean_object* v___x_2320_; uint8_t v___x_2321_; 
v_k_2316_ = lean_ctor_get(v_a_2315_, 1);
lean_inc_n(v_k_2316_, 2);
v_v_2317_ = lean_ctor_get(v_a_2315_, 2);
lean_inc(v_v_2317_);
v_l_2318_ = lean_ctor_get(v_a_2315_, 3);
lean_inc(v_l_2318_);
v_r_2319_ = lean_ctor_get(v_a_2315_, 4);
lean_inc(v_r_2319_);
lean_dec_ref(v_a_2315_);
lean_inc_ref(v_inst_2312_);
lean_inc(v_k_2313_);
v___x_2320_ = lean_apply_2(v_inst_2312_, v_k_2313_, v_k_2316_);
v___x_2321_ = lean_unbox(v___x_2320_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec(v_r_2319_);
lean_dec(v_best_2314_);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v_k_2316_);
lean_ctor_set(v___x_2322_, 1, v_v_2317_);
v___x_2323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2322_);
v_best_2314_ = v___x_2323_;
v_a_2315_ = v_l_2318_;
goto _start;
}
else
{
lean_dec(v_l_2318_);
lean_dec(v_v_2317_);
lean_dec(v_k_2316_);
v_a_2315_ = v_r_2319_;
goto _start;
}
}
else
{
lean_dec(v_k_2313_);
lean_dec_ref(v_inst_2312_);
return v_best_2314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go(lean_object* v_00_u03b1_2326_, lean_object* v_00_u03b2_2327_, lean_object* v_inst_2328_, lean_object* v_k_2329_, lean_object* v_best_2330_, lean_object* v_a_2331_){
_start:
{
lean_object* v___x_2332_; 
v___x_2332_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2328_, v_k_2329_, v_best_2330_, v_a_2331_);
return v___x_2332_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___redArg(lean_object* v_inst_2333_, lean_object* v_k_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2336_ = lean_box(0);
v___x_2337_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2333_, v_k_2334_, v___x_2336_, v_a_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f(lean_object* v_00_u03b1_2338_, lean_object* v_00_u03b2_2339_, lean_object* v_inst_2340_, lean_object* v_k_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2343_ = lean_box(0);
v___x_2344_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2340_, v_k_2341_, v___x_2343_, v_a_2342_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object* v_inst_2345_, lean_object* v_k_2346_, lean_object* v_best_2347_, lean_object* v_a_2348_){
_start:
{
if (lean_obj_tag(v_a_2348_) == 0)
{
lean_object* v_k_2349_; lean_object* v_v_2350_; lean_object* v_l_2351_; lean_object* v_r_2352_; lean_object* v___x_2353_; uint8_t v___x_2354_; 
v_k_2349_ = lean_ctor_get(v_a_2348_, 1);
lean_inc_n(v_k_2349_, 2);
v_v_2350_ = lean_ctor_get(v_a_2348_, 2);
lean_inc(v_v_2350_);
v_l_2351_ = lean_ctor_get(v_a_2348_, 3);
lean_inc(v_l_2351_);
v_r_2352_ = lean_ctor_get(v_a_2348_, 4);
lean_inc(v_r_2352_);
lean_dec_ref(v_a_2348_);
lean_inc_ref(v_inst_2345_);
lean_inc(v_k_2346_);
v___x_2353_ = lean_apply_2(v_inst_2345_, v_k_2346_, v_k_2349_);
v___x_2354_ = lean_unbox(v___x_2353_);
switch(v___x_2354_)
{
case 0:
{
lean_dec(v_r_2352_);
lean_dec(v_v_2350_);
lean_dec(v_k_2349_);
v_a_2348_ = v_l_2351_;
goto _start;
}
case 1:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_dec(v_r_2352_);
lean_dec(v_l_2351_);
lean_dec(v_best_2347_);
lean_dec(v_k_2346_);
lean_dec_ref(v_inst_2345_);
v___x_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2356_, 0, v_k_2349_);
lean_ctor_set(v___x_2356_, 1, v_v_2350_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2356_);
return v___x_2357_;
}
default: 
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
lean_dec(v_l_2351_);
lean_dec(v_best_2347_);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v_k_2349_);
lean_ctor_set(v___x_2358_, 1, v_v_2350_);
v___x_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
v_best_2347_ = v___x_2359_;
v_a_2348_ = v_r_2352_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2346_);
lean_dec_ref(v_inst_2345_);
return v_best_2347_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go(lean_object* v_00_u03b1_2361_, lean_object* v_00_u03b2_2362_, lean_object* v_inst_2363_, lean_object* v_k_2364_, lean_object* v_best_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v___x_2367_; 
v___x_2367_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2363_, v_k_2364_, v_best_2365_, v_a_2366_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___redArg(lean_object* v_inst_2368_, lean_object* v_k_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = lean_box(0);
v___x_2372_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2368_, v_k_2369_, v___x_2371_, v_a_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f(lean_object* v_00_u03b1_2373_, lean_object* v_00_u03b2_2374_, lean_object* v_inst_2375_, lean_object* v_k_2376_, lean_object* v_a_2377_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2378_ = lean_box(0);
v___x_2379_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2375_, v_k_2376_, v___x_2378_, v_a_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object* v_inst_2380_, lean_object* v_k_2381_, lean_object* v_best_2382_, lean_object* v_a_2383_){
_start:
{
if (lean_obj_tag(v_a_2383_) == 0)
{
lean_object* v_k_2384_; lean_object* v_v_2385_; lean_object* v_l_2386_; lean_object* v_r_2387_; lean_object* v___x_2388_; uint8_t v___x_2389_; 
v_k_2384_ = lean_ctor_get(v_a_2383_, 1);
lean_inc_n(v_k_2384_, 2);
v_v_2385_ = lean_ctor_get(v_a_2383_, 2);
lean_inc(v_v_2385_);
v_l_2386_ = lean_ctor_get(v_a_2383_, 3);
lean_inc(v_l_2386_);
v_r_2387_ = lean_ctor_get(v_a_2383_, 4);
lean_inc(v_r_2387_);
lean_dec_ref(v_a_2383_);
lean_inc_ref(v_inst_2380_);
lean_inc(v_k_2381_);
v___x_2388_ = lean_apply_2(v_inst_2380_, v_k_2381_, v_k_2384_);
v___x_2389_ = lean_unbox(v___x_2388_);
if (v___x_2389_ == 2)
{
lean_object* v___x_2390_; lean_object* v___x_2391_; 
lean_dec(v_l_2386_);
lean_dec(v_best_2382_);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v_k_2384_);
lean_ctor_set(v___x_2390_, 1, v_v_2385_);
v___x_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2390_);
v_best_2382_ = v___x_2391_;
v_a_2383_ = v_r_2387_;
goto _start;
}
else
{
lean_dec(v_r_2387_);
lean_dec(v_v_2385_);
lean_dec(v_k_2384_);
v_a_2383_ = v_l_2386_;
goto _start;
}
}
else
{
lean_dec(v_k_2381_);
lean_dec_ref(v_inst_2380_);
return v_best_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go(lean_object* v_00_u03b1_2394_, lean_object* v_00_u03b2_2395_, lean_object* v_inst_2396_, lean_object* v_k_2397_, lean_object* v_best_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2396_, v_k_2397_, v_best_2398_, v_a_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___redArg(lean_object* v_inst_2401_, lean_object* v_k_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_box(0);
v___x_2405_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2401_, v_k_2402_, v___x_2404_, v_a_2403_);
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f(lean_object* v_00_u03b1_2406_, lean_object* v_00_u03b2_2407_, lean_object* v_inst_2408_, lean_object* v_k_2409_, lean_object* v_a_2410_){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_box(0);
v___x_2412_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2408_, v_k_2409_, v___x_2411_, v_a_2410_);
return v___x_2412_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2416_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2));
v___x_2417_ = lean_unsigned_to_nat(14u);
v___x_2418_ = lean_unsigned_to_nat(22u);
v___x_2419_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1));
v___x_2420_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0));
v___x_2421_ = l_mkPanicMessageWithDecl(v___x_2420_, v___x_2419_, v___x_2418_, v___x_2417_, v___x_2416_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(lean_object* v_inst_2422_, lean_object* v_inst_2423_, lean_object* v_k_2424_, lean_object* v_t_2425_){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_box(0);
v___x_2427_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2422_, v_k_2424_, v___x_2426_, v_t_2425_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2428_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2429_ = l_panic___redArg(v_inst_2423_, v___x_2428_);
return v___x_2429_;
}
else
{
lean_object* v_val_2430_; 
v_val_2430_ = lean_ctor_get(v___x_2427_, 0);
lean_inc(v_val_2430_);
lean_dec_ref(v___x_2427_);
return v_val_2430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___boxed(lean_object* v_inst_2431_, lean_object* v_inst_2432_, lean_object* v_k_2433_, lean_object* v_t_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(v_inst_2431_, v_inst_2432_, v_k_2433_, v_t_2434_);
lean_dec_ref(v_inst_2432_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(lean_object* v_00_u03b1_2436_, lean_object* v_00_u03b2_2437_, lean_object* v_inst_2438_, lean_object* v_inst_2439_, lean_object* v_k_2440_, lean_object* v_t_2441_){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2442_ = lean_box(0);
v___x_2443_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2438_, v_k_2440_, v___x_2442_, v_t_2441_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2445_ = l_panic___redArg(v_inst_2439_, v___x_2444_);
return v___x_2445_;
}
else
{
lean_object* v_val_2446_; 
v_val_2446_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_val_2446_);
lean_dec_ref(v___x_2443_);
return v_val_2446_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2447_, lean_object* v_00_u03b2_2448_, lean_object* v_inst_2449_, lean_object* v_inst_2450_, lean_object* v_k_2451_, lean_object* v_t_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(v_00_u03b1_2447_, v_00_u03b2_2448_, v_inst_2449_, v_inst_2450_, v_k_2451_, v_t_2452_);
lean_dec_ref(v_inst_2450_);
return v_res_2453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(lean_object* v_inst_2454_, lean_object* v_inst_2455_, lean_object* v_k_2456_, lean_object* v_t_2457_){
_start:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; 
v___x_2458_ = lean_box(0);
v___x_2459_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2454_, v_k_2456_, v___x_2458_, v_t_2457_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2461_ = l_panic___redArg(v_inst_2455_, v___x_2460_);
return v___x_2461_;
}
else
{
lean_object* v_val_2462_; 
v_val_2462_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_val_2462_);
lean_dec_ref(v___x_2459_);
return v_val_2462_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg___boxed(lean_object* v_inst_2463_, lean_object* v_inst_2464_, lean_object* v_k_2465_, lean_object* v_t_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(v_inst_2463_, v_inst_2464_, v_k_2465_, v_t_2466_);
lean_dec_ref(v_inst_2464_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(lean_object* v_00_u03b1_2468_, lean_object* v_00_u03b2_2469_, lean_object* v_inst_2470_, lean_object* v_inst_2471_, lean_object* v_k_2472_, lean_object* v_t_2473_){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = lean_box(0);
v___x_2475_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2470_, v_k_2472_, v___x_2474_, v_t_2473_);
if (lean_obj_tag(v___x_2475_) == 0)
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2477_ = l_panic___redArg(v_inst_2471_, v___x_2476_);
return v___x_2477_;
}
else
{
lean_object* v_val_2478_; 
v_val_2478_ = lean_ctor_get(v___x_2475_, 0);
lean_inc(v_val_2478_);
lean_dec_ref(v___x_2475_);
return v_val_2478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2479_, lean_object* v_00_u03b2_2480_, lean_object* v_inst_2481_, lean_object* v_inst_2482_, lean_object* v_k_2483_, lean_object* v_t_2484_){
_start:
{
lean_object* v_res_2485_; 
v_res_2485_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(v_00_u03b1_2479_, v_00_u03b2_2480_, v_inst_2481_, v_inst_2482_, v_k_2483_, v_t_2484_);
lean_dec_ref(v_inst_2482_);
return v_res_2485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(lean_object* v_inst_2486_, lean_object* v_inst_2487_, lean_object* v_k_2488_, lean_object* v_t_2489_){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; 
v___x_2490_ = lean_box(0);
v___x_2491_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2486_, v_k_2488_, v___x_2490_, v_t_2489_);
if (lean_obj_tag(v___x_2491_) == 0)
{
lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2492_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2493_ = l_panic___redArg(v_inst_2487_, v___x_2492_);
return v___x_2493_;
}
else
{
lean_object* v_val_2494_; 
v_val_2494_ = lean_ctor_get(v___x_2491_, 0);
lean_inc(v_val_2494_);
lean_dec_ref(v___x_2491_);
return v_val_2494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg___boxed(lean_object* v_inst_2495_, lean_object* v_inst_2496_, lean_object* v_k_2497_, lean_object* v_t_2498_){
_start:
{
lean_object* v_res_2499_; 
v_res_2499_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(v_inst_2495_, v_inst_2496_, v_k_2497_, v_t_2498_);
lean_dec_ref(v_inst_2496_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(lean_object* v_00_u03b1_2500_, lean_object* v_00_u03b2_2501_, lean_object* v_inst_2502_, lean_object* v_inst_2503_, lean_object* v_k_2504_, lean_object* v_t_2505_){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2506_ = lean_box(0);
v___x_2507_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2502_, v_k_2504_, v___x_2506_, v_t_2505_);
if (lean_obj_tag(v___x_2507_) == 0)
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2509_ = l_panic___redArg(v_inst_2503_, v___x_2508_);
return v___x_2509_;
}
else
{
lean_object* v_val_2510_; 
v_val_2510_ = lean_ctor_get(v___x_2507_, 0);
lean_inc(v_val_2510_);
lean_dec_ref(v___x_2507_);
return v_val_2510_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2511_, lean_object* v_00_u03b2_2512_, lean_object* v_inst_2513_, lean_object* v_inst_2514_, lean_object* v_k_2515_, lean_object* v_t_2516_){
_start:
{
lean_object* v_res_2517_; 
v_res_2517_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(v_00_u03b1_2511_, v_00_u03b2_2512_, v_inst_2513_, v_inst_2514_, v_k_2515_, v_t_2516_);
lean_dec_ref(v_inst_2514_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(lean_object* v_inst_2518_, lean_object* v_inst_2519_, lean_object* v_k_2520_, lean_object* v_t_2521_){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; 
v___x_2522_ = lean_box(0);
v___x_2523_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2518_, v_k_2520_, v___x_2522_, v_t_2521_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2525_ = l_panic___redArg(v_inst_2519_, v___x_2524_);
return v___x_2525_;
}
else
{
lean_object* v_val_2526_; 
v_val_2526_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_val_2526_);
lean_dec_ref(v___x_2523_);
return v_val_2526_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg___boxed(lean_object* v_inst_2527_, lean_object* v_inst_2528_, lean_object* v_k_2529_, lean_object* v_t_2530_){
_start:
{
lean_object* v_res_2531_; 
v_res_2531_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(v_inst_2527_, v_inst_2528_, v_k_2529_, v_t_2530_);
lean_dec_ref(v_inst_2528_);
return v_res_2531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(lean_object* v_00_u03b1_2532_, lean_object* v_00_u03b2_2533_, lean_object* v_inst_2534_, lean_object* v_inst_2535_, lean_object* v_k_2536_, lean_object* v_t_2537_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_box(0);
v___x_2539_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2534_, v_k_2536_, v___x_2538_, v_t_2537_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2541_ = l_panic___redArg(v_inst_2535_, v___x_2540_);
return v___x_2541_;
}
else
{
lean_object* v_val_2542_; 
v_val_2542_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_val_2542_);
lean_dec_ref(v___x_2539_);
return v_val_2542_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2543_, lean_object* v_00_u03b2_2544_, lean_object* v_inst_2545_, lean_object* v_inst_2546_, lean_object* v_k_2547_, lean_object* v_t_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(v_00_u03b1_2543_, v_00_u03b2_2544_, v_inst_2545_, v_inst_2546_, v_k_2547_, v_t_2548_);
lean_dec_ref(v_inst_2546_);
return v_res_2549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(lean_object* v_inst_2550_, lean_object* v_k_2551_, lean_object* v_t_2552_, lean_object* v_fallback_2553_){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = lean_box(0);
v___x_2555_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2550_, v_k_2551_, v___x_2554_, v_t_2552_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_inc_ref(v_fallback_2553_);
return v_fallback_2553_;
}
else
{
lean_object* v_val_2556_; 
v_val_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_val_2556_);
lean_dec_ref(v___x_2555_);
return v_val_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg___boxed(lean_object* v_inst_2557_, lean_object* v_k_2558_, lean_object* v_t_2559_, lean_object* v_fallback_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(v_inst_2557_, v_k_2558_, v_t_2559_, v_fallback_2560_);
lean_dec_ref(v_fallback_2560_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED(lean_object* v_00_u03b1_2562_, lean_object* v_00_u03b2_2563_, lean_object* v_inst_2564_, lean_object* v_k_2565_, lean_object* v_t_2566_, lean_object* v_fallback_2567_){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2568_ = lean_box(0);
v___x_2569_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2564_, v_k_2565_, v___x_2568_, v_t_2566_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_inc_ref(v_fallback_2567_);
return v_fallback_2567_;
}
else
{
lean_object* v_val_2570_; 
v_val_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_val_2570_);
lean_dec_ref(v___x_2569_);
return v_val_2570_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___boxed(lean_object* v_00_u03b1_2571_, lean_object* v_00_u03b2_2572_, lean_object* v_inst_2573_, lean_object* v_k_2574_, lean_object* v_t_2575_, lean_object* v_fallback_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l_Std_DTreeMap_Internal_Impl_getEntryGED(v_00_u03b1_2571_, v_00_u03b2_2572_, v_inst_2573_, v_k_2574_, v_t_2575_, v_fallback_2576_);
lean_dec_ref(v_fallback_2576_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(lean_object* v_inst_2578_, lean_object* v_k_2579_, lean_object* v_t_2580_, lean_object* v_fallback_2581_){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2582_ = lean_box(0);
v___x_2583_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2578_, v_k_2579_, v___x_2582_, v_t_2580_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_inc_ref(v_fallback_2581_);
return v_fallback_2581_;
}
else
{
lean_object* v_val_2584_; 
v_val_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_val_2584_);
lean_dec_ref(v___x_2583_);
return v_val_2584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg___boxed(lean_object* v_inst_2585_, lean_object* v_k_2586_, lean_object* v_t_2587_, lean_object* v_fallback_2588_){
_start:
{
lean_object* v_res_2589_; 
v_res_2589_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(v_inst_2585_, v_k_2586_, v_t_2587_, v_fallback_2588_);
lean_dec_ref(v_fallback_2588_);
return v_res_2589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD(lean_object* v_00_u03b1_2590_, lean_object* v_00_u03b2_2591_, lean_object* v_inst_2592_, lean_object* v_k_2593_, lean_object* v_t_2594_, lean_object* v_fallback_2595_){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2596_ = lean_box(0);
v___x_2597_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2592_, v_k_2593_, v___x_2596_, v_t_2594_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_inc_ref(v_fallback_2595_);
return v_fallback_2595_;
}
else
{
lean_object* v_val_2598_; 
v_val_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_val_2598_);
lean_dec_ref(v___x_2597_);
return v_val_2598_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___boxed(lean_object* v_00_u03b1_2599_, lean_object* v_00_u03b2_2600_, lean_object* v_inst_2601_, lean_object* v_k_2602_, lean_object* v_t_2603_, lean_object* v_fallback_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD(v_00_u03b1_2599_, v_00_u03b2_2600_, v_inst_2601_, v_k_2602_, v_t_2603_, v_fallback_2604_);
lean_dec_ref(v_fallback_2604_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(lean_object* v_inst_2606_, lean_object* v_k_2607_, lean_object* v_t_2608_, lean_object* v_fallback_2609_){
_start:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2610_ = lean_box(0);
v___x_2611_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2606_, v_k_2607_, v___x_2610_, v_t_2608_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_inc_ref(v_fallback_2609_);
return v_fallback_2609_;
}
else
{
lean_object* v_val_2612_; 
v_val_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_val_2612_);
lean_dec_ref(v___x_2611_);
return v_val_2612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg___boxed(lean_object* v_inst_2613_, lean_object* v_k_2614_, lean_object* v_t_2615_, lean_object* v_fallback_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(v_inst_2613_, v_k_2614_, v_t_2615_, v_fallback_2616_);
lean_dec_ref(v_fallback_2616_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED(lean_object* v_00_u03b1_2618_, lean_object* v_00_u03b2_2619_, lean_object* v_inst_2620_, lean_object* v_k_2621_, lean_object* v_t_2622_, lean_object* v_fallback_2623_){
_start:
{
lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2624_ = lean_box(0);
v___x_2625_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2620_, v_k_2621_, v___x_2624_, v_t_2622_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_inc_ref(v_fallback_2623_);
return v_fallback_2623_;
}
else
{
lean_object* v_val_2626_; 
v_val_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_val_2626_);
lean_dec_ref(v___x_2625_);
return v_val_2626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___boxed(lean_object* v_00_u03b1_2627_, lean_object* v_00_u03b2_2628_, lean_object* v_inst_2629_, lean_object* v_k_2630_, lean_object* v_t_2631_, lean_object* v_fallback_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l_Std_DTreeMap_Internal_Impl_getEntryLED(v_00_u03b1_2627_, v_00_u03b2_2628_, v_inst_2629_, v_k_2630_, v_t_2631_, v_fallback_2632_);
lean_dec_ref(v_fallback_2632_);
return v_res_2633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(lean_object* v_inst_2634_, lean_object* v_k_2635_, lean_object* v_t_2636_, lean_object* v_fallback_2637_){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2638_ = lean_box(0);
v___x_2639_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2634_, v_k_2635_, v___x_2638_, v_t_2636_);
if (lean_obj_tag(v___x_2639_) == 0)
{
lean_inc_ref(v_fallback_2637_);
return v_fallback_2637_;
}
else
{
lean_object* v_val_2640_; 
v_val_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_val_2640_);
lean_dec_ref(v___x_2639_);
return v_val_2640_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg___boxed(lean_object* v_inst_2641_, lean_object* v_k_2642_, lean_object* v_t_2643_, lean_object* v_fallback_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(v_inst_2641_, v_k_2642_, v_t_2643_, v_fallback_2644_);
lean_dec_ref(v_fallback_2644_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD(lean_object* v_00_u03b1_2646_, lean_object* v_00_u03b2_2647_, lean_object* v_inst_2648_, lean_object* v_k_2649_, lean_object* v_t_2650_, lean_object* v_fallback_2651_){
_start:
{
lean_object* v___x_2652_; lean_object* v___x_2653_; 
v___x_2652_ = lean_box(0);
v___x_2653_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2648_, v_k_2649_, v___x_2652_, v_t_2650_);
if (lean_obj_tag(v___x_2653_) == 0)
{
lean_inc_ref(v_fallback_2651_);
return v_fallback_2651_;
}
else
{
lean_object* v_val_2654_; 
v_val_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_val_2654_);
lean_dec_ref(v___x_2653_);
return v_val_2654_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___boxed(lean_object* v_00_u03b1_2655_, lean_object* v_00_u03b2_2656_, lean_object* v_inst_2657_, lean_object* v_k_2658_, lean_object* v_t_2659_, lean_object* v_fallback_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD(v_00_u03b1_2655_, v_00_u03b2_2656_, v_inst_2657_, v_k_2658_, v_t_2659_, v_fallback_2660_);
lean_dec_ref(v_fallback_2660_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(lean_object* v_inst_2662_, lean_object* v_k_2663_, lean_object* v_x_2664_){
_start:
{
lean_object* v_k_2665_; lean_object* v_v_2666_; lean_object* v_l_2667_; lean_object* v_r_2668_; lean_object* v___x_2669_; uint8_t v___x_2670_; 
v_k_2665_ = lean_ctor_get(v_x_2664_, 1);
lean_inc_n(v_k_2665_, 2);
v_v_2666_ = lean_ctor_get(v_x_2664_, 2);
lean_inc(v_v_2666_);
v_l_2667_ = lean_ctor_get(v_x_2664_, 3);
lean_inc(v_l_2667_);
v_r_2668_ = lean_ctor_get(v_x_2664_, 4);
lean_inc(v_r_2668_);
lean_dec(v_x_2664_);
lean_inc_ref(v_inst_2662_);
lean_inc(v_k_2663_);
v___x_2669_ = lean_apply_2(v_inst_2662_, v_k_2663_, v_k_2665_);
v___x_2670_ = lean_unbox(v___x_2669_);
switch(v___x_2670_)
{
case 0:
{
lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_dec(v_r_2668_);
v___x_2671_ = lean_box(0);
v___x_2672_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2662_, v_k_2663_, v___x_2671_, v_l_2667_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v___x_2673_; 
v___x_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2673_, 0, v_k_2665_);
lean_ctor_set(v___x_2673_, 1, v_v_2666_);
return v___x_2673_;
}
else
{
lean_object* v_val_2674_; 
lean_dec(v_v_2666_);
lean_dec(v_k_2665_);
v_val_2674_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_val_2674_);
lean_dec_ref(v___x_2672_);
return v_val_2674_;
}
}
case 1:
{
lean_object* v___x_2675_; 
lean_dec(v_r_2668_);
lean_dec(v_l_2667_);
lean_dec(v_k_2663_);
lean_dec_ref(v_inst_2662_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_k_2665_);
lean_ctor_set(v___x_2675_, 1, v_v_2666_);
return v___x_2675_;
}
default: 
{
lean_dec(v_l_2667_);
lean_dec(v_v_2666_);
lean_dec(v_k_2665_);
v_x_2664_ = v_r_2668_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE(lean_object* v_00_u03b1_2677_, lean_object* v_00_u03b2_2678_, lean_object* v_inst_2679_, lean_object* v_inst_2680_, lean_object* v_k_2681_, lean_object* v_x_2682_, lean_object* v_x_2683_, lean_object* v_x_2684_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_inst_2679_, v_k_2681_, v_x_2682_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object* v_inst_2686_, lean_object* v_k_2687_, lean_object* v_x_2688_){
_start:
{
lean_object* v_k_2689_; lean_object* v_v_2690_; lean_object* v_l_2691_; lean_object* v_r_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; uint8_t v___x_2695_; uint8_t v___x_2696_; 
v_k_2689_ = lean_ctor_get(v_x_2688_, 1);
lean_inc_n(v_k_2689_, 2);
v_v_2690_ = lean_ctor_get(v_x_2688_, 2);
lean_inc(v_v_2690_);
v_l_2691_ = lean_ctor_get(v_x_2688_, 3);
lean_inc(v_l_2691_);
v_r_2692_ = lean_ctor_get(v_x_2688_, 4);
lean_inc(v_r_2692_);
lean_dec(v_x_2688_);
lean_inc_ref(v_inst_2686_);
lean_inc(v_k_2687_);
v___x_2693_ = lean_apply_2(v_inst_2686_, v_k_2687_, v_k_2689_);
v___x_2694_ = 0;
v___x_2695_ = lean_unbox(v___x_2693_);
v___x_2696_ = l_instDecidableEqOrdering(v___x_2695_, v___x_2694_);
if (v___x_2696_ == 0)
{
lean_dec(v_l_2691_);
lean_dec(v_v_2690_);
lean_dec(v_k_2689_);
v_x_2688_ = v_r_2692_;
goto _start;
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; 
lean_dec(v_r_2692_);
v___x_2698_ = lean_box(0);
v___x_2699_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2686_, v_k_2687_, v___x_2698_, v_l_2691_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v_k_2689_);
lean_ctor_set(v___x_2700_, 1, v_v_2690_);
return v___x_2700_;
}
else
{
lean_object* v_val_2701_; 
lean_dec(v_v_2690_);
lean_dec(v_k_2689_);
v_val_2701_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_val_2701_);
lean_dec_ref(v___x_2699_);
return v_val_2701_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object* v_00_u03b1_2702_, lean_object* v_00_u03b2_2703_, lean_object* v_inst_2704_, lean_object* v_inst_2705_, lean_object* v_k_2706_, lean_object* v_x_2707_, lean_object* v_x_2708_, lean_object* v_x_2709_){
_start:
{
lean_object* v___x_2710_; 
v___x_2710_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_inst_2704_, v_k_2706_, v_x_2707_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object* v_inst_2711_, lean_object* v_k_2712_, lean_object* v_x_2713_){
_start:
{
lean_object* v_k_2714_; lean_object* v_v_2715_; lean_object* v_l_2716_; lean_object* v_r_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v_k_2714_ = lean_ctor_get(v_x_2713_, 1);
lean_inc_n(v_k_2714_, 2);
v_v_2715_ = lean_ctor_get(v_x_2713_, 2);
lean_inc(v_v_2715_);
v_l_2716_ = lean_ctor_get(v_x_2713_, 3);
lean_inc(v_l_2716_);
v_r_2717_ = lean_ctor_get(v_x_2713_, 4);
lean_inc(v_r_2717_);
lean_dec(v_x_2713_);
lean_inc_ref(v_inst_2711_);
lean_inc(v_k_2712_);
v___x_2718_ = lean_apply_2(v_inst_2711_, v_k_2712_, v_k_2714_);
v___x_2719_ = lean_unbox(v___x_2718_);
switch(v___x_2719_)
{
case 0:
{
lean_dec(v_r_2717_);
lean_dec(v_v_2715_);
lean_dec(v_k_2714_);
v_x_2713_ = v_l_2716_;
goto _start;
}
case 1:
{
lean_object* v___x_2721_; 
lean_dec(v_r_2717_);
lean_dec(v_l_2716_);
lean_dec(v_k_2712_);
lean_dec_ref(v_inst_2711_);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_k_2714_);
lean_ctor_set(v___x_2721_, 1, v_v_2715_);
return v___x_2721_;
}
default: 
{
lean_object* v___x_2722_; lean_object* v___x_2723_; 
lean_dec(v_l_2716_);
v___x_2722_ = lean_box(0);
v___x_2723_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2711_, v_k_2712_, v___x_2722_, v_r_2717_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v___x_2724_; 
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v_k_2714_);
lean_ctor_set(v___x_2724_, 1, v_v_2715_);
return v___x_2724_;
}
else
{
lean_object* v_val_2725_; 
lean_dec(v_v_2715_);
lean_dec(v_k_2714_);
v_val_2725_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_val_2725_);
lean_dec_ref(v___x_2723_);
return v_val_2725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object* v_00_u03b1_2726_, lean_object* v_00_u03b2_2727_, lean_object* v_inst_2728_, lean_object* v_inst_2729_, lean_object* v_k_2730_, lean_object* v_x_2731_, lean_object* v_x_2732_, lean_object* v_x_2733_){
_start:
{
lean_object* v___x_2734_; 
v___x_2734_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_inst_2728_, v_k_2730_, v_x_2731_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object* v_inst_2735_, lean_object* v_k_2736_, lean_object* v_x_2737_){
_start:
{
lean_object* v_k_2738_; lean_object* v_v_2739_; lean_object* v_l_2740_; lean_object* v_r_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; uint8_t v___x_2744_; uint8_t v___x_2745_; 
v_k_2738_ = lean_ctor_get(v_x_2737_, 1);
lean_inc_n(v_k_2738_, 2);
v_v_2739_ = lean_ctor_get(v_x_2737_, 2);
lean_inc(v_v_2739_);
v_l_2740_ = lean_ctor_get(v_x_2737_, 3);
lean_inc(v_l_2740_);
v_r_2741_ = lean_ctor_get(v_x_2737_, 4);
lean_inc(v_r_2741_);
lean_dec(v_x_2737_);
lean_inc_ref(v_inst_2735_);
lean_inc(v_k_2736_);
v___x_2742_ = lean_apply_2(v_inst_2735_, v_k_2736_, v_k_2738_);
v___x_2743_ = 2;
v___x_2744_ = lean_unbox(v___x_2742_);
v___x_2745_ = l_instDecidableEqOrdering(v___x_2744_, v___x_2743_);
if (v___x_2745_ == 0)
{
lean_dec(v_r_2741_);
lean_dec(v_v_2739_);
lean_dec(v_k_2738_);
v_x_2737_ = v_l_2740_;
goto _start;
}
else
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
lean_dec(v_l_2740_);
v___x_2747_ = lean_box(0);
v___x_2748_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2735_, v_k_2736_, v___x_2747_, v_r_2741_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_k_2738_);
lean_ctor_set(v___x_2749_, 1, v_v_2739_);
return v___x_2749_;
}
else
{
lean_object* v_val_2750_; 
lean_dec(v_v_2739_);
lean_dec(v_k_2738_);
v_val_2750_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_val_2750_);
lean_dec_ref(v___x_2748_);
return v_val_2750_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT(lean_object* v_00_u03b1_2751_, lean_object* v_00_u03b2_2752_, lean_object* v_inst_2753_, lean_object* v_inst_2754_, lean_object* v_k_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_, lean_object* v_x_2758_){
_start:
{
lean_object* v___x_2759_; 
v___x_2759_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_inst_2753_, v_k_2755_, v_x_2756_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object* v_inst_2760_, lean_object* v_k_2761_, lean_object* v_best_2762_, lean_object* v_a_2763_){
_start:
{
if (lean_obj_tag(v_a_2763_) == 0)
{
lean_object* v_k_2764_; lean_object* v_l_2765_; lean_object* v_r_2766_; lean_object* v___x_2767_; uint8_t v___x_2768_; 
v_k_2764_ = lean_ctor_get(v_a_2763_, 1);
lean_inc_n(v_k_2764_, 2);
v_l_2765_ = lean_ctor_get(v_a_2763_, 3);
lean_inc(v_l_2765_);
v_r_2766_ = lean_ctor_get(v_a_2763_, 4);
lean_inc(v_r_2766_);
lean_dec_ref(v_a_2763_);
lean_inc_ref(v_inst_2760_);
lean_inc(v_k_2761_);
v___x_2767_ = lean_apply_2(v_inst_2760_, v_k_2761_, v_k_2764_);
v___x_2768_ = lean_unbox(v___x_2767_);
switch(v___x_2768_)
{
case 0:
{
lean_object* v___x_2769_; 
lean_dec(v_r_2766_);
lean_dec(v_best_2762_);
v___x_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2769_, 0, v_k_2764_);
v_best_2762_ = v___x_2769_;
v_a_2763_ = v_l_2765_;
goto _start;
}
case 1:
{
lean_object* v___x_2771_; 
lean_dec(v_r_2766_);
lean_dec(v_l_2765_);
lean_dec(v_best_2762_);
lean_dec(v_k_2761_);
lean_dec_ref(v_inst_2760_);
v___x_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_k_2764_);
return v___x_2771_;
}
default: 
{
lean_dec(v_l_2765_);
lean_dec(v_k_2764_);
v_a_2763_ = v_r_2766_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2761_);
lean_dec_ref(v_inst_2760_);
return v_best_2762_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(lean_object* v_00_u03b1_2773_, lean_object* v_00_u03b2_2774_, lean_object* v_inst_2775_, lean_object* v_k_2776_, lean_object* v_best_2777_, lean_object* v_a_2778_){
_start:
{
lean_object* v___x_2779_; 
v___x_2779_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2775_, v_k_2776_, v_best_2777_, v_a_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___redArg(lean_object* v_inst_2780_, lean_object* v_k_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_box(0);
v___x_2784_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2780_, v_k_2781_, v___x_2783_, v_a_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(lean_object* v_00_u03b1_2785_, lean_object* v_00_u03b2_2786_, lean_object* v_inst_2787_, lean_object* v_k_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_box(0);
v___x_2791_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2787_, v_k_2788_, v___x_2790_, v_a_2789_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object* v_inst_2792_, lean_object* v_k_2793_, lean_object* v_best_2794_, lean_object* v_a_2795_){
_start:
{
if (lean_obj_tag(v_a_2795_) == 0)
{
lean_object* v_k_2796_; lean_object* v_l_2797_; lean_object* v_r_2798_; lean_object* v___x_2799_; uint8_t v___x_2800_; 
v_k_2796_ = lean_ctor_get(v_a_2795_, 1);
lean_inc_n(v_k_2796_, 2);
v_l_2797_ = lean_ctor_get(v_a_2795_, 3);
lean_inc(v_l_2797_);
v_r_2798_ = lean_ctor_get(v_a_2795_, 4);
lean_inc(v_r_2798_);
lean_dec_ref(v_a_2795_);
lean_inc_ref(v_inst_2792_);
lean_inc(v_k_2793_);
v___x_2799_ = lean_apply_2(v_inst_2792_, v_k_2793_, v_k_2796_);
v___x_2800_ = lean_unbox(v___x_2799_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; 
lean_dec(v_r_2798_);
lean_dec(v_best_2794_);
v___x_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2801_, 0, v_k_2796_);
v_best_2794_ = v___x_2801_;
v_a_2795_ = v_l_2797_;
goto _start;
}
else
{
lean_dec(v_l_2797_);
lean_dec(v_k_2796_);
v_a_2795_ = v_r_2798_;
goto _start;
}
}
else
{
lean_dec(v_k_2793_);
lean_dec_ref(v_inst_2792_);
return v_best_2794_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(lean_object* v_00_u03b1_2804_, lean_object* v_00_u03b2_2805_, lean_object* v_inst_2806_, lean_object* v_k_2807_, lean_object* v_best_2808_, lean_object* v_a_2809_){
_start:
{
lean_object* v___x_2810_; 
v___x_2810_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2806_, v_k_2807_, v_best_2808_, v_a_2809_);
return v___x_2810_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___redArg(lean_object* v_inst_2811_, lean_object* v_k_2812_, lean_object* v_a_2813_){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = lean_box(0);
v___x_2815_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2811_, v_k_2812_, v___x_2814_, v_a_2813_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(lean_object* v_00_u03b1_2816_, lean_object* v_00_u03b2_2817_, lean_object* v_inst_2818_, lean_object* v_k_2819_, lean_object* v_a_2820_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2821_ = lean_box(0);
v___x_2822_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2818_, v_k_2819_, v___x_2821_, v_a_2820_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object* v_inst_2823_, lean_object* v_k_2824_, lean_object* v_best_2825_, lean_object* v_a_2826_){
_start:
{
if (lean_obj_tag(v_a_2826_) == 0)
{
lean_object* v_k_2827_; lean_object* v_l_2828_; lean_object* v_r_2829_; lean_object* v___x_2830_; uint8_t v___x_2831_; 
v_k_2827_ = lean_ctor_get(v_a_2826_, 1);
lean_inc_n(v_k_2827_, 2);
v_l_2828_ = lean_ctor_get(v_a_2826_, 3);
lean_inc(v_l_2828_);
v_r_2829_ = lean_ctor_get(v_a_2826_, 4);
lean_inc(v_r_2829_);
lean_dec_ref(v_a_2826_);
lean_inc_ref(v_inst_2823_);
lean_inc(v_k_2824_);
v___x_2830_ = lean_apply_2(v_inst_2823_, v_k_2824_, v_k_2827_);
v___x_2831_ = lean_unbox(v___x_2830_);
switch(v___x_2831_)
{
case 0:
{
lean_dec(v_r_2829_);
lean_dec(v_k_2827_);
v_a_2826_ = v_l_2828_;
goto _start;
}
case 1:
{
lean_object* v___x_2833_; 
lean_dec(v_r_2829_);
lean_dec(v_l_2828_);
lean_dec(v_best_2825_);
lean_dec(v_k_2824_);
lean_dec_ref(v_inst_2823_);
v___x_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2833_, 0, v_k_2827_);
return v___x_2833_;
}
default: 
{
lean_object* v___x_2834_; 
lean_dec(v_l_2828_);
lean_dec(v_best_2825_);
v___x_2834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2834_, 0, v_k_2827_);
v_best_2825_ = v___x_2834_;
v_a_2826_ = v_r_2829_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2824_);
lean_dec_ref(v_inst_2823_);
return v_best_2825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(lean_object* v_00_u03b1_2836_, lean_object* v_00_u03b2_2837_, lean_object* v_inst_2838_, lean_object* v_k_2839_, lean_object* v_best_2840_, lean_object* v_a_2841_){
_start:
{
lean_object* v___x_2842_; 
v___x_2842_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2838_, v_k_2839_, v_best_2840_, v_a_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___redArg(lean_object* v_inst_2843_, lean_object* v_k_2844_, lean_object* v_a_2845_){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
v___x_2846_ = lean_box(0);
v___x_2847_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2843_, v_k_2844_, v___x_2846_, v_a_2845_);
return v___x_2847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(lean_object* v_00_u03b1_2848_, lean_object* v_00_u03b2_2849_, lean_object* v_inst_2850_, lean_object* v_k_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = lean_box(0);
v___x_2854_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2850_, v_k_2851_, v___x_2853_, v_a_2852_);
return v___x_2854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object* v_inst_2855_, lean_object* v_k_2856_, lean_object* v_best_2857_, lean_object* v_a_2858_){
_start:
{
if (lean_obj_tag(v_a_2858_) == 0)
{
lean_object* v_k_2859_; lean_object* v_l_2860_; lean_object* v_r_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v_k_2859_ = lean_ctor_get(v_a_2858_, 1);
lean_inc_n(v_k_2859_, 2);
v_l_2860_ = lean_ctor_get(v_a_2858_, 3);
lean_inc(v_l_2860_);
v_r_2861_ = lean_ctor_get(v_a_2858_, 4);
lean_inc(v_r_2861_);
lean_dec_ref(v_a_2858_);
lean_inc_ref(v_inst_2855_);
lean_inc(v_k_2856_);
v___x_2862_ = lean_apply_2(v_inst_2855_, v_k_2856_, v_k_2859_);
v___x_2863_ = lean_unbox(v___x_2862_);
if (v___x_2863_ == 2)
{
lean_object* v___x_2864_; 
lean_dec(v_l_2860_);
lean_dec(v_best_2857_);
v___x_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_k_2859_);
v_best_2857_ = v___x_2864_;
v_a_2858_ = v_r_2861_;
goto _start;
}
else
{
lean_dec(v_r_2861_);
lean_dec(v_k_2859_);
v_a_2858_ = v_l_2860_;
goto _start;
}
}
else
{
lean_dec(v_k_2856_);
lean_dec_ref(v_inst_2855_);
return v_best_2857_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(lean_object* v_00_u03b1_2867_, lean_object* v_00_u03b2_2868_, lean_object* v_inst_2869_, lean_object* v_k_2870_, lean_object* v_best_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v___x_2873_; 
v___x_2873_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2869_, v_k_2870_, v_best_2871_, v_a_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___redArg(lean_object* v_inst_2874_, lean_object* v_k_2875_, lean_object* v_a_2876_){
_start:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; 
v___x_2877_ = lean_box(0);
v___x_2878_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2874_, v_k_2875_, v___x_2877_, v_a_2876_);
return v___x_2878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(lean_object* v_00_u03b1_2879_, lean_object* v_00_u03b2_2880_, lean_object* v_inst_2881_, lean_object* v_k_2882_, lean_object* v_a_2883_){
_start:
{
lean_object* v___x_2884_; lean_object* v___x_2885_; 
v___x_2884_ = lean_box(0);
v___x_2885_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2881_, v_k_2882_, v___x_2884_, v_a_2883_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(lean_object* v_inst_2886_, lean_object* v_inst_2887_, lean_object* v_k_2888_, lean_object* v_t_2889_){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = lean_box(0);
v___x_2891_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2886_, v_k_2888_, v___x_2890_, v_t_2889_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; 
v___x_2892_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2893_ = l_panic___redArg(v_inst_2887_, v___x_2892_);
return v___x_2893_;
}
else
{
lean_object* v_val_2894_; 
v_val_2894_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_val_2894_);
lean_dec_ref(v___x_2891_);
return v_val_2894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg___boxed(lean_object* v_inst_2895_, lean_object* v_inst_2896_, lean_object* v_k_2897_, lean_object* v_t_2898_){
_start:
{
lean_object* v_res_2899_; 
v_res_2899_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(v_inst_2895_, v_inst_2896_, v_k_2897_, v_t_2898_);
lean_dec(v_inst_2896_);
return v_res_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object* v_00_u03b1_2900_, lean_object* v_00_u03b2_2901_, lean_object* v_inst_2902_, lean_object* v_inst_2903_, lean_object* v_k_2904_, lean_object* v_t_2905_){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = lean_box(0);
v___x_2907_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2902_, v_k_2904_, v___x_2906_, v_t_2905_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2909_ = l_panic___redArg(v_inst_2903_, v___x_2908_);
return v___x_2909_;
}
else
{
lean_object* v_val_2910_; 
v_val_2910_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_val_2910_);
lean_dec_ref(v___x_2907_);
return v_val_2910_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___boxed(lean_object* v_00_u03b1_2911_, lean_object* v_00_u03b2_2912_, lean_object* v_inst_2913_, lean_object* v_inst_2914_, lean_object* v_k_2915_, lean_object* v_t_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(v_00_u03b1_2911_, v_00_u03b2_2912_, v_inst_2913_, v_inst_2914_, v_k_2915_, v_t_2916_);
lean_dec(v_inst_2914_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(lean_object* v_inst_2918_, lean_object* v_inst_2919_, lean_object* v_k_2920_, lean_object* v_t_2921_){
_start:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_box(0);
v___x_2923_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2918_, v_k_2920_, v___x_2922_, v_t_2921_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2925_ = l_panic___redArg(v_inst_2919_, v___x_2924_);
return v___x_2925_;
}
else
{
lean_object* v_val_2926_; 
v_val_2926_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_val_2926_);
lean_dec_ref(v___x_2923_);
return v_val_2926_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg___boxed(lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_k_2929_, lean_object* v_t_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(v_inst_2927_, v_inst_2928_, v_k_2929_, v_t_2930_);
lean_dec(v_inst_2928_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object* v_00_u03b1_2932_, lean_object* v_00_u03b2_2933_, lean_object* v_inst_2934_, lean_object* v_inst_2935_, lean_object* v_k_2936_, lean_object* v_t_2937_){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_box(0);
v___x_2939_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2934_, v_k_2936_, v___x_2938_, v_t_2937_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v___x_2940_; lean_object* v___x_2941_; 
v___x_2940_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2941_ = l_panic___redArg(v_inst_2935_, v___x_2940_);
return v___x_2941_;
}
else
{
lean_object* v_val_2942_; 
v_val_2942_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_val_2942_);
lean_dec_ref(v___x_2939_);
return v_val_2942_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___boxed(lean_object* v_00_u03b1_2943_, lean_object* v_00_u03b2_2944_, lean_object* v_inst_2945_, lean_object* v_inst_2946_, lean_object* v_k_2947_, lean_object* v_t_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(v_00_u03b1_2943_, v_00_u03b2_2944_, v_inst_2945_, v_inst_2946_, v_k_2947_, v_t_2948_);
lean_dec(v_inst_2946_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(lean_object* v_inst_2950_, lean_object* v_inst_2951_, lean_object* v_k_2952_, lean_object* v_t_2953_){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_box(0);
v___x_2955_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2950_, v_k_2952_, v___x_2954_, v_t_2953_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2957_ = l_panic___redArg(v_inst_2951_, v___x_2956_);
return v___x_2957_;
}
else
{
lean_object* v_val_2958_; 
v_val_2958_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_val_2958_);
lean_dec_ref(v___x_2955_);
return v_val_2958_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg___boxed(lean_object* v_inst_2959_, lean_object* v_inst_2960_, lean_object* v_k_2961_, lean_object* v_t_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(v_inst_2959_, v_inst_2960_, v_k_2961_, v_t_2962_);
lean_dec(v_inst_2960_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object* v_00_u03b1_2964_, lean_object* v_00_u03b2_2965_, lean_object* v_inst_2966_, lean_object* v_inst_2967_, lean_object* v_k_2968_, lean_object* v_t_2969_){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_box(0);
v___x_2971_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2966_, v_k_2968_, v___x_2970_, v_t_2969_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2973_ = l_panic___redArg(v_inst_2967_, v___x_2972_);
return v___x_2973_;
}
else
{
lean_object* v_val_2974_; 
v_val_2974_ = lean_ctor_get(v___x_2971_, 0);
lean_inc(v_val_2974_);
lean_dec_ref(v___x_2971_);
return v_val_2974_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___boxed(lean_object* v_00_u03b1_2975_, lean_object* v_00_u03b2_2976_, lean_object* v_inst_2977_, lean_object* v_inst_2978_, lean_object* v_k_2979_, lean_object* v_t_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(v_00_u03b1_2975_, v_00_u03b2_2976_, v_inst_2977_, v_inst_2978_, v_k_2979_, v_t_2980_);
lean_dec(v_inst_2978_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(lean_object* v_inst_2982_, lean_object* v_inst_2983_, lean_object* v_k_2984_, lean_object* v_t_2985_){
_start:
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_box(0);
v___x_2987_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2982_, v_k_2984_, v___x_2986_, v_t_2985_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2989_ = l_panic___redArg(v_inst_2983_, v___x_2988_);
return v___x_2989_;
}
else
{
lean_object* v_val_2990_; 
v_val_2990_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_val_2990_);
lean_dec_ref(v___x_2987_);
return v_val_2990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg___boxed(lean_object* v_inst_2991_, lean_object* v_inst_2992_, lean_object* v_k_2993_, lean_object* v_t_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(v_inst_2991_, v_inst_2992_, v_k_2993_, v_t_2994_);
lean_dec(v_inst_2992_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object* v_00_u03b1_2996_, lean_object* v_00_u03b2_2997_, lean_object* v_inst_2998_, lean_object* v_inst_2999_, lean_object* v_k_3000_, lean_object* v_t_3001_){
_start:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_box(0);
v___x_3003_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2998_, v_k_3000_, v___x_3002_, v_t_3001_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3005_ = l_panic___redArg(v_inst_2999_, v___x_3004_);
return v___x_3005_;
}
else
{
lean_object* v_val_3006_; 
v_val_3006_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_val_3006_);
lean_dec_ref(v___x_3003_);
return v_val_3006_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___boxed(lean_object* v_00_u03b1_3007_, lean_object* v_00_u03b2_3008_, lean_object* v_inst_3009_, lean_object* v_inst_3010_, lean_object* v_k_3011_, lean_object* v_t_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(v_00_u03b1_3007_, v_00_u03b2_3008_, v_inst_3009_, v_inst_3010_, v_k_3011_, v_t_3012_);
lean_dec(v_inst_3010_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(lean_object* v_inst_3014_, lean_object* v_k_3015_, lean_object* v_t_3016_, lean_object* v_fallback_3017_){
_start:
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_box(0);
v___x_3019_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3014_, v_k_3015_, v___x_3018_, v_t_3016_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_inc(v_fallback_3017_);
return v_fallback_3017_;
}
else
{
lean_object* v_val_3020_; 
v_val_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_val_3020_);
lean_dec_ref(v___x_3019_);
return v_val_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg___boxed(lean_object* v_inst_3021_, lean_object* v_k_3022_, lean_object* v_t_3023_, lean_object* v_fallback_3024_){
_start:
{
lean_object* v_res_3025_; 
v_res_3025_ = l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(v_inst_3021_, v_k_3022_, v_t_3023_, v_fallback_3024_);
lean_dec(v_fallback_3024_);
return v_res_3025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED(lean_object* v_00_u03b1_3026_, lean_object* v_00_u03b2_3027_, lean_object* v_inst_3028_, lean_object* v_k_3029_, lean_object* v_t_3030_, lean_object* v_fallback_3031_){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
v___x_3032_ = lean_box(0);
v___x_3033_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3028_, v_k_3029_, v___x_3032_, v_t_3030_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_inc(v_fallback_3031_);
return v_fallback_3031_;
}
else
{
lean_object* v_val_3034_; 
v_val_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_val_3034_);
lean_dec_ref(v___x_3033_);
return v_val_3034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___boxed(lean_object* v_00_u03b1_3035_, lean_object* v_00_u03b2_3036_, lean_object* v_inst_3037_, lean_object* v_k_3038_, lean_object* v_t_3039_, lean_object* v_fallback_3040_){
_start:
{
lean_object* v_res_3041_; 
v_res_3041_ = l_Std_DTreeMap_Internal_Impl_getKeyGED(v_00_u03b1_3035_, v_00_u03b2_3036_, v_inst_3037_, v_k_3038_, v_t_3039_, v_fallback_3040_);
lean_dec(v_fallback_3040_);
return v_res_3041_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(lean_object* v_inst_3042_, lean_object* v_k_3043_, lean_object* v_t_3044_, lean_object* v_fallback_3045_){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_box(0);
v___x_3047_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3042_, v_k_3043_, v___x_3046_, v_t_3044_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_inc(v_fallback_3045_);
return v_fallback_3045_;
}
else
{
lean_object* v_val_3048_; 
v_val_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_val_3048_);
lean_dec_ref(v___x_3047_);
return v_val_3048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg___boxed(lean_object* v_inst_3049_, lean_object* v_k_3050_, lean_object* v_t_3051_, lean_object* v_fallback_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(v_inst_3049_, v_k_3050_, v_t_3051_, v_fallback_3052_);
lean_dec(v_fallback_3052_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD(lean_object* v_00_u03b1_3054_, lean_object* v_00_u03b2_3055_, lean_object* v_inst_3056_, lean_object* v_k_3057_, lean_object* v_t_3058_, lean_object* v_fallback_3059_){
_start:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3060_ = lean_box(0);
v___x_3061_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3056_, v_k_3057_, v___x_3060_, v_t_3058_);
if (lean_obj_tag(v___x_3061_) == 0)
{
lean_inc(v_fallback_3059_);
return v_fallback_3059_;
}
else
{
lean_object* v_val_3062_; 
v_val_3062_ = lean_ctor_get(v___x_3061_, 0);
lean_inc(v_val_3062_);
lean_dec_ref(v___x_3061_);
return v_val_3062_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___boxed(lean_object* v_00_u03b1_3063_, lean_object* v_00_u03b2_3064_, lean_object* v_inst_3065_, lean_object* v_k_3066_, lean_object* v_t_3067_, lean_object* v_fallback_3068_){
_start:
{
lean_object* v_res_3069_; 
v_res_3069_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD(v_00_u03b1_3063_, v_00_u03b2_3064_, v_inst_3065_, v_k_3066_, v_t_3067_, v_fallback_3068_);
lean_dec(v_fallback_3068_);
return v_res_3069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(lean_object* v_inst_3070_, lean_object* v_k_3071_, lean_object* v_t_3072_, lean_object* v_fallback_3073_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_box(0);
v___x_3075_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3070_, v_k_3071_, v___x_3074_, v_t_3072_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_inc(v_fallback_3073_);
return v_fallback_3073_;
}
else
{
lean_object* v_val_3076_; 
v_val_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_val_3076_);
lean_dec_ref(v___x_3075_);
return v_val_3076_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg___boxed(lean_object* v_inst_3077_, lean_object* v_k_3078_, lean_object* v_t_3079_, lean_object* v_fallback_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(v_inst_3077_, v_k_3078_, v_t_3079_, v_fallback_3080_);
lean_dec(v_fallback_3080_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED(lean_object* v_00_u03b1_3082_, lean_object* v_00_u03b2_3083_, lean_object* v_inst_3084_, lean_object* v_k_3085_, lean_object* v_t_3086_, lean_object* v_fallback_3087_){
_start:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_box(0);
v___x_3089_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3084_, v_k_3085_, v___x_3088_, v_t_3086_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_inc(v_fallback_3087_);
return v_fallback_3087_;
}
else
{
lean_object* v_val_3090_; 
v_val_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_val_3090_);
lean_dec_ref(v___x_3089_);
return v_val_3090_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___boxed(lean_object* v_00_u03b1_3091_, lean_object* v_00_u03b2_3092_, lean_object* v_inst_3093_, lean_object* v_k_3094_, lean_object* v_t_3095_, lean_object* v_fallback_3096_){
_start:
{
lean_object* v_res_3097_; 
v_res_3097_ = l_Std_DTreeMap_Internal_Impl_getKeyLED(v_00_u03b1_3091_, v_00_u03b2_3092_, v_inst_3093_, v_k_3094_, v_t_3095_, v_fallback_3096_);
lean_dec(v_fallback_3096_);
return v_res_3097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(lean_object* v_inst_3098_, lean_object* v_k_3099_, lean_object* v_t_3100_, lean_object* v_fallback_3101_){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_box(0);
v___x_3103_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3098_, v_k_3099_, v___x_3102_, v_t_3100_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_inc(v_fallback_3101_);
return v_fallback_3101_;
}
else
{
lean_object* v_val_3104_; 
v_val_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_val_3104_);
lean_dec_ref(v___x_3103_);
return v_val_3104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg___boxed(lean_object* v_inst_3105_, lean_object* v_k_3106_, lean_object* v_t_3107_, lean_object* v_fallback_3108_){
_start:
{
lean_object* v_res_3109_; 
v_res_3109_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(v_inst_3105_, v_k_3106_, v_t_3107_, v_fallback_3108_);
lean_dec(v_fallback_3108_);
return v_res_3109_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD(lean_object* v_00_u03b1_3110_, lean_object* v_00_u03b2_3111_, lean_object* v_inst_3112_, lean_object* v_k_3113_, lean_object* v_t_3114_, lean_object* v_fallback_3115_){
_start:
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
v___x_3116_ = lean_box(0);
v___x_3117_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3112_, v_k_3113_, v___x_3116_, v_t_3114_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_inc(v_fallback_3115_);
return v_fallback_3115_;
}
else
{
lean_object* v_val_3118_; 
v_val_3118_ = lean_ctor_get(v___x_3117_, 0);
lean_inc(v_val_3118_);
lean_dec_ref(v___x_3117_);
return v_val_3118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___boxed(lean_object* v_00_u03b1_3119_, lean_object* v_00_u03b2_3120_, lean_object* v_inst_3121_, lean_object* v_k_3122_, lean_object* v_t_3123_, lean_object* v_fallback_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD(v_00_u03b1_3119_, v_00_u03b2_3120_, v_inst_3121_, v_k_3122_, v_t_3123_, v_fallback_3124_);
lean_dec(v_fallback_3124_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object* v_inst_3126_, lean_object* v_k_3127_, lean_object* v_x_3128_){
_start:
{
lean_object* v_k_3129_; lean_object* v_l_3130_; lean_object* v_r_3131_; lean_object* v___x_3132_; uint8_t v___x_3133_; 
v_k_3129_ = lean_ctor_get(v_x_3128_, 1);
lean_inc_n(v_k_3129_, 2);
v_l_3130_ = lean_ctor_get(v_x_3128_, 3);
lean_inc(v_l_3130_);
v_r_3131_ = lean_ctor_get(v_x_3128_, 4);
lean_inc(v_r_3131_);
lean_dec(v_x_3128_);
lean_inc_ref(v_inst_3126_);
lean_inc(v_k_3127_);
v___x_3132_ = lean_apply_2(v_inst_3126_, v_k_3127_, v_k_3129_);
v___x_3133_ = lean_unbox(v___x_3132_);
switch(v___x_3133_)
{
case 0:
{
lean_object* v___x_3134_; lean_object* v___x_3135_; 
lean_dec(v_r_3131_);
v___x_3134_ = lean_box(0);
v___x_3135_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3126_, v_k_3127_, v___x_3134_, v_l_3130_);
if (lean_obj_tag(v___x_3135_) == 0)
{
return v_k_3129_;
}
else
{
lean_object* v_val_3136_; 
lean_dec(v_k_3129_);
v_val_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_val_3136_);
lean_dec_ref(v___x_3135_);
return v_val_3136_;
}
}
case 1:
{
lean_dec(v_r_3131_);
lean_dec(v_l_3130_);
lean_dec(v_k_3127_);
lean_dec_ref(v_inst_3126_);
return v_k_3129_;
}
default: 
{
lean_dec(v_l_3130_);
lean_dec(v_k_3129_);
v_x_3128_ = v_r_3131_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE(lean_object* v_00_u03b1_3138_, lean_object* v_00_u03b2_3139_, lean_object* v_inst_3140_, lean_object* v_inst_3141_, lean_object* v_k_3142_, lean_object* v_x_3143_, lean_object* v_x_3144_, lean_object* v_x_3145_){
_start:
{
lean_object* v___x_3146_; 
v___x_3146_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_inst_3140_, v_k_3142_, v_x_3143_);
return v___x_3146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object* v_inst_3147_, lean_object* v_k_3148_, lean_object* v_x_3149_){
_start:
{
lean_object* v_k_3150_; lean_object* v_l_3151_; lean_object* v_r_3152_; lean_object* v___x_3153_; uint8_t v___x_3154_; uint8_t v___x_3155_; uint8_t v___x_3156_; 
v_k_3150_ = lean_ctor_get(v_x_3149_, 1);
lean_inc_n(v_k_3150_, 2);
v_l_3151_ = lean_ctor_get(v_x_3149_, 3);
lean_inc(v_l_3151_);
v_r_3152_ = lean_ctor_get(v_x_3149_, 4);
lean_inc(v_r_3152_);
lean_dec(v_x_3149_);
lean_inc_ref(v_inst_3147_);
lean_inc(v_k_3148_);
v___x_3153_ = lean_apply_2(v_inst_3147_, v_k_3148_, v_k_3150_);
v___x_3154_ = 0;
v___x_3155_ = lean_unbox(v___x_3153_);
v___x_3156_ = l_instDecidableEqOrdering(v___x_3155_, v___x_3154_);
if (v___x_3156_ == 0)
{
lean_dec(v_l_3151_);
lean_dec(v_k_3150_);
v_x_3149_ = v_r_3152_;
goto _start;
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
lean_dec(v_r_3152_);
v___x_3158_ = lean_box(0);
v___x_3159_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3147_, v_k_3148_, v___x_3158_, v_l_3151_);
if (lean_obj_tag(v___x_3159_) == 0)
{
return v_k_3150_;
}
else
{
lean_object* v_val_3160_; 
lean_dec(v_k_3150_);
v_val_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_val_3160_);
lean_dec_ref(v___x_3159_);
return v_val_3160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT(lean_object* v_00_u03b1_3161_, lean_object* v_00_u03b2_3162_, lean_object* v_inst_3163_, lean_object* v_inst_3164_, lean_object* v_k_3165_, lean_object* v_x_3166_, lean_object* v_x_3167_, lean_object* v_x_3168_){
_start:
{
lean_object* v___x_3169_; 
v___x_3169_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_inst_3163_, v_k_3165_, v_x_3166_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object* v_inst_3170_, lean_object* v_k_3171_, lean_object* v_x_3172_){
_start:
{
lean_object* v_k_3173_; lean_object* v_l_3174_; lean_object* v_r_3175_; lean_object* v___x_3176_; uint8_t v___x_3177_; 
v_k_3173_ = lean_ctor_get(v_x_3172_, 1);
lean_inc_n(v_k_3173_, 2);
v_l_3174_ = lean_ctor_get(v_x_3172_, 3);
lean_inc(v_l_3174_);
v_r_3175_ = lean_ctor_get(v_x_3172_, 4);
lean_inc(v_r_3175_);
lean_dec(v_x_3172_);
lean_inc_ref(v_inst_3170_);
lean_inc(v_k_3171_);
v___x_3176_ = lean_apply_2(v_inst_3170_, v_k_3171_, v_k_3173_);
v___x_3177_ = lean_unbox(v___x_3176_);
switch(v___x_3177_)
{
case 0:
{
lean_dec(v_r_3175_);
lean_dec(v_k_3173_);
v_x_3172_ = v_l_3174_;
goto _start;
}
case 1:
{
lean_dec(v_r_3175_);
lean_dec(v_l_3174_);
lean_dec(v_k_3171_);
lean_dec_ref(v_inst_3170_);
return v_k_3173_;
}
default: 
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
lean_dec(v_l_3174_);
v___x_3179_ = lean_box(0);
v___x_3180_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3170_, v_k_3171_, v___x_3179_, v_r_3175_);
if (lean_obj_tag(v___x_3180_) == 0)
{
return v_k_3173_;
}
else
{
lean_object* v_val_3181_; 
lean_dec(v_k_3173_);
v_val_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_val_3181_);
lean_dec_ref(v___x_3180_);
return v_val_3181_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE(lean_object* v_00_u03b1_3182_, lean_object* v_00_u03b2_3183_, lean_object* v_inst_3184_, lean_object* v_inst_3185_, lean_object* v_k_3186_, lean_object* v_x_3187_, lean_object* v_x_3188_, lean_object* v_x_3189_){
_start:
{
lean_object* v___x_3190_; 
v___x_3190_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_inst_3184_, v_k_3186_, v_x_3187_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object* v_inst_3191_, lean_object* v_k_3192_, lean_object* v_x_3193_){
_start:
{
lean_object* v_k_3194_; lean_object* v_l_3195_; lean_object* v_r_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; uint8_t v___x_3199_; uint8_t v___x_3200_; 
v_k_3194_ = lean_ctor_get(v_x_3193_, 1);
lean_inc_n(v_k_3194_, 2);
v_l_3195_ = lean_ctor_get(v_x_3193_, 3);
lean_inc(v_l_3195_);
v_r_3196_ = lean_ctor_get(v_x_3193_, 4);
lean_inc(v_r_3196_);
lean_dec(v_x_3193_);
lean_inc_ref(v_inst_3191_);
lean_inc(v_k_3192_);
v___x_3197_ = lean_apply_2(v_inst_3191_, v_k_3192_, v_k_3194_);
v___x_3198_ = 2;
v___x_3199_ = lean_unbox(v___x_3197_);
v___x_3200_ = l_instDecidableEqOrdering(v___x_3199_, v___x_3198_);
if (v___x_3200_ == 0)
{
lean_dec(v_r_3196_);
lean_dec(v_k_3194_);
v_x_3193_ = v_l_3195_;
goto _start;
}
else
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
lean_dec(v_l_3195_);
v___x_3202_ = lean_box(0);
v___x_3203_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3191_, v_k_3192_, v___x_3202_, v_r_3196_);
if (lean_obj_tag(v___x_3203_) == 0)
{
return v_k_3194_;
}
else
{
lean_object* v_val_3204_; 
lean_dec(v_k_3194_);
v_val_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_val_3204_);
lean_dec_ref(v___x_3203_);
return v_val_3204_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT(lean_object* v_00_u03b1_3205_, lean_object* v_00_u03b2_3206_, lean_object* v_inst_3207_, lean_object* v_inst_3208_, lean_object* v_k_3209_, lean_object* v_x_3210_, lean_object* v_x_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_inst_3207_, v_k_3209_, v_x_3210_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object* v_x_3214_){
_start:
{
if (lean_obj_tag(v_x_3214_) == 0)
{
lean_object* v_l_3215_; 
v_l_3215_ = lean_ctor_get(v_x_3214_, 3);
if (lean_obj_tag(v_l_3215_) == 0)
{
v_x_3214_ = v_l_3215_;
goto _start;
}
else
{
lean_object* v_k_3217_; lean_object* v_v_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v_k_3217_ = lean_ctor_get(v_x_3214_, 1);
v_v_3218_ = lean_ctor_get(v_x_3214_, 2);
lean_inc(v_v_3218_);
lean_inc(v_k_3217_);
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_k_3217_);
lean_ctor_set(v___x_3219_, 1, v_v_3218_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v___x_3219_);
return v___x_3220_;
}
}
else
{
lean_object* v___x_3221_; 
v___x_3221_ = lean_box(0);
return v___x_3221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg___boxed(lean_object* v_x_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3222_);
lean_dec(v_x_3222_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(lean_object* v_00_u03b1_3224_, lean_object* v_00_u03b2_3225_, lean_object* v_x_3226_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_3228_, lean_object* v_00_u03b2_3229_, lean_object* v_x_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(v_00_u03b1_3228_, v_00_u03b2_3229_, v_x_3230_);
lean_dec(v_x_3230_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3232_, lean_object* v_h__1_3233_, lean_object* v_h__2_3234_, lean_object* v_h__3_3235_){
_start:
{
if (lean_obj_tag(v_x_3232_) == 0)
{
lean_object* v_l_3236_; 
lean_dec(v_h__1_3233_);
v_l_3236_ = lean_ctor_get(v_x_3232_, 3);
if (lean_obj_tag(v_l_3236_) == 0)
{
lean_object* v_size_3237_; lean_object* v_k_3238_; lean_object* v_v_3239_; lean_object* v_r_3240_; lean_object* v_size_3241_; lean_object* v_k_3242_; lean_object* v_v_3243_; lean_object* v_l_3244_; lean_object* v_r_3245_; lean_object* v___x_3246_; 
lean_inc_ref(v_l_3236_);
lean_dec(v_h__2_3234_);
v_size_3237_ = lean_ctor_get(v_x_3232_, 0);
lean_inc(v_size_3237_);
v_k_3238_ = lean_ctor_get(v_x_3232_, 1);
lean_inc(v_k_3238_);
v_v_3239_ = lean_ctor_get(v_x_3232_, 2);
lean_inc(v_v_3239_);
v_r_3240_ = lean_ctor_get(v_x_3232_, 4);
lean_inc(v_r_3240_);
lean_dec_ref(v_x_3232_);
v_size_3241_ = lean_ctor_get(v_l_3236_, 0);
lean_inc(v_size_3241_);
v_k_3242_ = lean_ctor_get(v_l_3236_, 1);
lean_inc(v_k_3242_);
v_v_3243_ = lean_ctor_get(v_l_3236_, 2);
lean_inc(v_v_3243_);
v_l_3244_ = lean_ctor_get(v_l_3236_, 3);
lean_inc(v_l_3244_);
v_r_3245_ = lean_ctor_get(v_l_3236_, 4);
lean_inc(v_r_3245_);
lean_dec_ref(v_l_3236_);
v___x_3246_ = lean_apply_9(v_h__3_3235_, v_size_3237_, v_k_3238_, v_v_3239_, v_size_3241_, v_k_3242_, v_v_3243_, v_l_3244_, v_r_3245_, v_r_3240_);
return v___x_3246_;
}
else
{
lean_object* v_size_3247_; lean_object* v_k_3248_; lean_object* v_v_3249_; lean_object* v_r_3250_; lean_object* v___x_3251_; 
lean_dec(v_h__3_3235_);
v_size_3247_ = lean_ctor_get(v_x_3232_, 0);
lean_inc(v_size_3247_);
v_k_3248_ = lean_ctor_get(v_x_3232_, 1);
lean_inc(v_k_3248_);
v_v_3249_ = lean_ctor_get(v_x_3232_, 2);
lean_inc(v_v_3249_);
v_r_3250_ = lean_ctor_get(v_x_3232_, 4);
lean_inc(v_r_3250_);
lean_dec_ref(v_x_3232_);
v___x_3251_ = lean_apply_4(v_h__2_3234_, v_size_3247_, v_k_3248_, v_v_3249_, v_r_3250_);
return v___x_3251_;
}
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
lean_dec(v_h__3_3235_);
lean_dec(v_h__2_3234_);
v___x_3252_ = lean_box(0);
v___x_3253_ = lean_apply_1(v_h__1_3233_, v___x_3252_);
return v___x_3253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3254_, lean_object* v_00_u03b2_3255_, lean_object* v_motive_3256_, lean_object* v_x_3257_, lean_object* v_h__1_3258_, lean_object* v_h__2_3259_, lean_object* v_h__3_3260_){
_start:
{
if (lean_obj_tag(v_x_3257_) == 0)
{
lean_object* v_l_3261_; 
lean_dec(v_h__1_3258_);
v_l_3261_ = lean_ctor_get(v_x_3257_, 3);
if (lean_obj_tag(v_l_3261_) == 0)
{
lean_object* v_size_3262_; lean_object* v_k_3263_; lean_object* v_v_3264_; lean_object* v_r_3265_; lean_object* v_size_3266_; lean_object* v_k_3267_; lean_object* v_v_3268_; lean_object* v_l_3269_; lean_object* v_r_3270_; lean_object* v___x_3271_; 
lean_inc_ref(v_l_3261_);
lean_dec(v_h__2_3259_);
v_size_3262_ = lean_ctor_get(v_x_3257_, 0);
lean_inc(v_size_3262_);
v_k_3263_ = lean_ctor_get(v_x_3257_, 1);
lean_inc(v_k_3263_);
v_v_3264_ = lean_ctor_get(v_x_3257_, 2);
lean_inc(v_v_3264_);
v_r_3265_ = lean_ctor_get(v_x_3257_, 4);
lean_inc(v_r_3265_);
lean_dec_ref(v_x_3257_);
v_size_3266_ = lean_ctor_get(v_l_3261_, 0);
lean_inc(v_size_3266_);
v_k_3267_ = lean_ctor_get(v_l_3261_, 1);
lean_inc(v_k_3267_);
v_v_3268_ = lean_ctor_get(v_l_3261_, 2);
lean_inc(v_v_3268_);
v_l_3269_ = lean_ctor_get(v_l_3261_, 3);
lean_inc(v_l_3269_);
v_r_3270_ = lean_ctor_get(v_l_3261_, 4);
lean_inc(v_r_3270_);
lean_dec_ref(v_l_3261_);
v___x_3271_ = lean_apply_9(v_h__3_3260_, v_size_3262_, v_k_3263_, v_v_3264_, v_size_3266_, v_k_3267_, v_v_3268_, v_l_3269_, v_r_3270_, v_r_3265_);
return v___x_3271_;
}
else
{
lean_object* v_size_3272_; lean_object* v_k_3273_; lean_object* v_v_3274_; lean_object* v_r_3275_; lean_object* v___x_3276_; 
lean_dec(v_h__3_3260_);
v_size_3272_ = lean_ctor_get(v_x_3257_, 0);
lean_inc(v_size_3272_);
v_k_3273_ = lean_ctor_get(v_x_3257_, 1);
lean_inc(v_k_3273_);
v_v_3274_ = lean_ctor_get(v_x_3257_, 2);
lean_inc(v_v_3274_);
v_r_3275_ = lean_ctor_get(v_x_3257_, 4);
lean_inc(v_r_3275_);
lean_dec_ref(v_x_3257_);
v___x_3276_ = lean_apply_4(v_h__2_3259_, v_size_3272_, v_k_3273_, v_v_3274_, v_r_3275_);
return v___x_3276_;
}
}
else
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
lean_dec(v_h__3_3260_);
lean_dec(v_h__2_3259_);
v___x_3277_ = lean_box(0);
v___x_3278_ = lean_apply_1(v_h__1_3258_, v___x_3277_);
return v___x_3278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object* v_x_3279_){
_start:
{
lean_object* v_l_3280_; 
v_l_3280_ = lean_ctor_get(v_x_3279_, 3);
if (lean_obj_tag(v_l_3280_) == 0)
{
v_x_3279_ = v_l_3280_;
goto _start;
}
else
{
lean_object* v_k_3282_; lean_object* v_v_3283_; lean_object* v___x_3284_; 
v_k_3282_ = lean_ctor_get(v_x_3279_, 1);
v_v_3283_ = lean_ctor_get(v_x_3279_, 2);
lean_inc(v_v_3283_);
lean_inc(v_k_3282_);
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v_k_3282_);
lean_ctor_set(v___x_3284_, 1, v_v_3283_);
return v___x_3284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg___boxed(lean_object* v_x_3285_){
_start:
{
lean_object* v_res_3286_; 
v_res_3286_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3285_);
lean_dec(v_x_3285_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry(lean_object* v_00_u03b1_3287_, lean_object* v_00_u03b2_3288_, lean_object* v_x_3289_, lean_object* v_x_3290_){
_start:
{
lean_object* v___x_3291_; 
v___x_3291_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3289_);
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___boxed(lean_object* v_00_u03b1_3292_, lean_object* v_00_u03b2_3293_, lean_object* v_x_3294_, lean_object* v_x_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry(v_00_u03b1_3292_, v_00_u03b2_3293_, v_x_3294_, v_x_3295_);
lean_dec(v_x_3294_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_3297_, lean_object* v_h__1_3298_, lean_object* v_h__2_3299_){
_start:
{
lean_object* v_l_3300_; 
v_l_3300_ = lean_ctor_get(v_x_3297_, 3);
if (lean_obj_tag(v_l_3300_) == 0)
{
lean_object* v_size_3301_; lean_object* v_k_3302_; lean_object* v_v_3303_; lean_object* v_r_3304_; lean_object* v_size_3305_; lean_object* v_k_3306_; lean_object* v_v_3307_; lean_object* v_l_3308_; lean_object* v_r_3309_; lean_object* v___x_3310_; 
lean_inc_ref(v_l_3300_);
lean_dec(v_h__1_3298_);
v_size_3301_ = lean_ctor_get(v_x_3297_, 0);
lean_inc(v_size_3301_);
v_k_3302_ = lean_ctor_get(v_x_3297_, 1);
lean_inc(v_k_3302_);
v_v_3303_ = lean_ctor_get(v_x_3297_, 2);
lean_inc(v_v_3303_);
v_r_3304_ = lean_ctor_get(v_x_3297_, 4);
lean_inc(v_r_3304_);
lean_dec(v_x_3297_);
v_size_3305_ = lean_ctor_get(v_l_3300_, 0);
lean_inc(v_size_3305_);
v_k_3306_ = lean_ctor_get(v_l_3300_, 1);
lean_inc(v_k_3306_);
v_v_3307_ = lean_ctor_get(v_l_3300_, 2);
lean_inc(v_v_3307_);
v_l_3308_ = lean_ctor_get(v_l_3300_, 3);
lean_inc(v_l_3308_);
v_r_3309_ = lean_ctor_get(v_l_3300_, 4);
lean_inc(v_r_3309_);
lean_dec_ref(v_l_3300_);
v___x_3310_ = lean_apply_10(v_h__2_3299_, v_size_3301_, v_k_3302_, v_v_3303_, v_size_3305_, v_k_3306_, v_v_3307_, v_l_3308_, v_r_3309_, v_r_3304_, lean_box(0));
return v___x_3310_;
}
else
{
lean_object* v_size_3311_; lean_object* v_k_3312_; lean_object* v_v_3313_; lean_object* v_r_3314_; lean_object* v___x_3315_; 
lean_dec(v_h__2_3299_);
v_size_3311_ = lean_ctor_get(v_x_3297_, 0);
lean_inc(v_size_3311_);
v_k_3312_ = lean_ctor_get(v_x_3297_, 1);
lean_inc(v_k_3312_);
v_v_3313_ = lean_ctor_get(v_x_3297_, 2);
lean_inc(v_v_3313_);
v_r_3314_ = lean_ctor_get(v_x_3297_, 4);
lean_inc(v_r_3314_);
lean_dec(v_x_3297_);
v___x_3315_ = lean_apply_5(v_h__1_3298_, v_size_3311_, v_k_3312_, v_v_3313_, v_r_3314_, lean_box(0));
return v___x_3315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_3316_, lean_object* v_00_u03b2_3317_, lean_object* v_motive_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_, lean_object* v_h__1_3321_, lean_object* v_h__2_3322_){
_start:
{
lean_object* v_l_3323_; 
v_l_3323_ = lean_ctor_get(v_x_3319_, 3);
if (lean_obj_tag(v_l_3323_) == 0)
{
lean_object* v_size_3324_; lean_object* v_k_3325_; lean_object* v_v_3326_; lean_object* v_r_3327_; lean_object* v_size_3328_; lean_object* v_k_3329_; lean_object* v_v_3330_; lean_object* v_l_3331_; lean_object* v_r_3332_; lean_object* v___x_3333_; 
lean_inc_ref(v_l_3323_);
lean_dec(v_h__1_3321_);
v_size_3324_ = lean_ctor_get(v_x_3319_, 0);
lean_inc(v_size_3324_);
v_k_3325_ = lean_ctor_get(v_x_3319_, 1);
lean_inc(v_k_3325_);
v_v_3326_ = lean_ctor_get(v_x_3319_, 2);
lean_inc(v_v_3326_);
v_r_3327_ = lean_ctor_get(v_x_3319_, 4);
lean_inc(v_r_3327_);
lean_dec(v_x_3319_);
v_size_3328_ = lean_ctor_get(v_l_3323_, 0);
lean_inc(v_size_3328_);
v_k_3329_ = lean_ctor_get(v_l_3323_, 1);
lean_inc(v_k_3329_);
v_v_3330_ = lean_ctor_get(v_l_3323_, 2);
lean_inc(v_v_3330_);
v_l_3331_ = lean_ctor_get(v_l_3323_, 3);
lean_inc(v_l_3331_);
v_r_3332_ = lean_ctor_get(v_l_3323_, 4);
lean_inc(v_r_3332_);
lean_dec_ref(v_l_3323_);
v___x_3333_ = lean_apply_10(v_h__2_3322_, v_size_3324_, v_k_3325_, v_v_3326_, v_size_3328_, v_k_3329_, v_v_3330_, v_l_3331_, v_r_3332_, v_r_3327_, lean_box(0));
return v___x_3333_;
}
else
{
lean_object* v_size_3334_; lean_object* v_k_3335_; lean_object* v_v_3336_; lean_object* v_r_3337_; lean_object* v___x_3338_; 
lean_dec(v_h__2_3322_);
v_size_3334_ = lean_ctor_get(v_x_3319_, 0);
lean_inc(v_size_3334_);
v_k_3335_ = lean_ctor_get(v_x_3319_, 1);
lean_inc(v_k_3335_);
v_v_3336_ = lean_ctor_get(v_x_3319_, 2);
lean_inc(v_v_3336_);
v_r_3337_ = lean_ctor_get(v_x_3319_, 4);
lean_inc(v_r_3337_);
lean_dec(v_x_3319_);
v___x_3338_ = lean_apply_5(v_h__1_3321_, v_size_3334_, v_k_3335_, v_v_3336_, v_r_3337_, lean_box(0));
return v___x_3338_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v___x_3340_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3341_ = lean_unsigned_to_nat(13u);
v___x_3342_ = lean_unsigned_to_nat(816u);
v___x_3343_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0));
v___x_3344_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3345_ = l_mkPanicMessageWithDecl(v___x_3344_, v___x_3343_, v___x_3342_, v___x_3341_, v___x_3340_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object* v_inst_3346_, lean_object* v_x_3347_){
_start:
{
if (lean_obj_tag(v_x_3347_) == 0)
{
lean_object* v_l_3348_; 
v_l_3348_ = lean_ctor_get(v_x_3347_, 3);
if (lean_obj_tag(v_l_3348_) == 0)
{
v_x_3347_ = v_l_3348_;
goto _start;
}
else
{
lean_object* v_k_3350_; lean_object* v_v_3351_; lean_object* v___x_3352_; 
v_k_3350_ = lean_ctor_get(v_x_3347_, 1);
v_v_3351_ = lean_ctor_get(v_x_3347_, 2);
lean_inc(v_v_3351_);
lean_inc(v_k_3350_);
v___x_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3352_, 0, v_k_3350_);
lean_ctor_set(v___x_3352_, 1, v_v_3351_);
return v___x_3352_;
}
}
else
{
lean_object* v___x_3353_; lean_object* v___x_3354_; 
v___x_3353_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1);
v___x_3354_ = l_panic___redArg(v_inst_3346_, v___x_3353_);
return v___x_3354_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_3355_, lean_object* v_x_3356_){
_start:
{
lean_object* v_res_3357_; 
v_res_3357_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3355_, v_x_3356_);
lean_dec(v_x_3356_);
lean_dec_ref(v_inst_3355_);
return v_res_3357_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(lean_object* v_00_u03b1_3358_, lean_object* v_00_u03b2_3359_, lean_object* v_inst_3360_, lean_object* v_x_3361_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3360_, v_x_3361_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_3363_, lean_object* v_00_u03b2_3364_, lean_object* v_inst_3365_, lean_object* v_x_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(v_00_u03b1_3363_, v_00_u03b2_3364_, v_inst_3365_, v_x_3366_);
lean_dec(v_x_3366_);
lean_dec_ref(v_inst_3365_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object* v_x_3368_, lean_object* v_x_3369_){
_start:
{
if (lean_obj_tag(v_x_3368_) == 0)
{
lean_object* v_l_3370_; 
v_l_3370_ = lean_ctor_get(v_x_3368_, 3);
if (lean_obj_tag(v_l_3370_) == 0)
{
v_x_3368_ = v_l_3370_;
goto _start;
}
else
{
lean_object* v_k_3372_; lean_object* v_v_3373_; lean_object* v___x_3374_; 
v_k_3372_ = lean_ctor_get(v_x_3368_, 1);
v_v_3373_ = lean_ctor_get(v_x_3368_, 2);
lean_inc(v_v_3373_);
lean_inc(v_k_3372_);
v___x_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3374_, 0, v_k_3372_);
lean_ctor_set(v___x_3374_, 1, v_v_3373_);
return v___x_3374_;
}
}
else
{
lean_inc_ref(v_x_3369_);
return v_x_3369_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg___boxed(lean_object* v_x_3375_, lean_object* v_x_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3375_, v_x_3376_);
lean_dec_ref(v_x_3376_);
lean_dec(v_x_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD(lean_object* v_00_u03b1_3378_, lean_object* v_00_u03b2_3379_, lean_object* v_x_3380_, lean_object* v_x_3381_){
_start:
{
lean_object* v___x_3382_; 
v___x_3382_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3380_, v_x_3381_);
return v___x_3382_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___boxed(lean_object* v_00_u03b1_3383_, lean_object* v_00_u03b2_3384_, lean_object* v_x_3385_, lean_object* v_x_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD(v_00_u03b1_3383_, v_00_u03b2_3384_, v_x_3385_, v_x_3386_);
lean_dec_ref(v_x_3386_);
lean_dec(v_x_3385_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_3388_, lean_object* v_x_3389_, lean_object* v_h__1_3390_, lean_object* v_h__2_3391_, lean_object* v_h__3_3392_){
_start:
{
if (lean_obj_tag(v_x_3388_) == 0)
{
lean_object* v_l_3393_; 
lean_dec(v_h__1_3390_);
v_l_3393_ = lean_ctor_get(v_x_3388_, 3);
if (lean_obj_tag(v_l_3393_) == 0)
{
lean_object* v_size_3394_; lean_object* v_k_3395_; lean_object* v_v_3396_; lean_object* v_r_3397_; lean_object* v_size_3398_; lean_object* v_k_3399_; lean_object* v_v_3400_; lean_object* v_l_3401_; lean_object* v_r_3402_; lean_object* v___x_3403_; 
lean_inc_ref(v_l_3393_);
lean_dec(v_h__2_3391_);
v_size_3394_ = lean_ctor_get(v_x_3388_, 0);
lean_inc(v_size_3394_);
v_k_3395_ = lean_ctor_get(v_x_3388_, 1);
lean_inc(v_k_3395_);
v_v_3396_ = lean_ctor_get(v_x_3388_, 2);
lean_inc(v_v_3396_);
v_r_3397_ = lean_ctor_get(v_x_3388_, 4);
lean_inc(v_r_3397_);
lean_dec_ref(v_x_3388_);
v_size_3398_ = lean_ctor_get(v_l_3393_, 0);
lean_inc(v_size_3398_);
v_k_3399_ = lean_ctor_get(v_l_3393_, 1);
lean_inc(v_k_3399_);
v_v_3400_ = lean_ctor_get(v_l_3393_, 2);
lean_inc(v_v_3400_);
v_l_3401_ = lean_ctor_get(v_l_3393_, 3);
lean_inc(v_l_3401_);
v_r_3402_ = lean_ctor_get(v_l_3393_, 4);
lean_inc(v_r_3402_);
lean_dec_ref(v_l_3393_);
v___x_3403_ = lean_apply_10(v_h__3_3392_, v_size_3394_, v_k_3395_, v_v_3396_, v_size_3398_, v_k_3399_, v_v_3400_, v_l_3401_, v_r_3402_, v_r_3397_, v_x_3389_);
return v___x_3403_;
}
else
{
lean_object* v_size_3404_; lean_object* v_k_3405_; lean_object* v_v_3406_; lean_object* v_r_3407_; lean_object* v___x_3408_; 
lean_dec(v_h__3_3392_);
v_size_3404_ = lean_ctor_get(v_x_3388_, 0);
lean_inc(v_size_3404_);
v_k_3405_ = lean_ctor_get(v_x_3388_, 1);
lean_inc(v_k_3405_);
v_v_3406_ = lean_ctor_get(v_x_3388_, 2);
lean_inc(v_v_3406_);
v_r_3407_ = lean_ctor_get(v_x_3388_, 4);
lean_inc(v_r_3407_);
lean_dec_ref(v_x_3388_);
v___x_3408_ = lean_apply_5(v_h__2_3391_, v_size_3404_, v_k_3405_, v_v_3406_, v_r_3407_, v_x_3389_);
return v___x_3408_;
}
}
else
{
lean_object* v___x_3409_; 
lean_dec(v_h__3_3392_);
lean_dec(v_h__2_3391_);
v___x_3409_ = lean_apply_1(v_h__1_3390_, v_x_3389_);
return v___x_3409_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_3410_, lean_object* v_00_u03b2_3411_, lean_object* v_motive_3412_, lean_object* v_x_3413_, lean_object* v_x_3414_, lean_object* v_h__1_3415_, lean_object* v_h__2_3416_, lean_object* v_h__3_3417_){
_start:
{
if (lean_obj_tag(v_x_3413_) == 0)
{
lean_object* v_l_3418_; 
lean_dec(v_h__1_3415_);
v_l_3418_ = lean_ctor_get(v_x_3413_, 3);
if (lean_obj_tag(v_l_3418_) == 0)
{
lean_object* v_size_3419_; lean_object* v_k_3420_; lean_object* v_v_3421_; lean_object* v_r_3422_; lean_object* v_size_3423_; lean_object* v_k_3424_; lean_object* v_v_3425_; lean_object* v_l_3426_; lean_object* v_r_3427_; lean_object* v___x_3428_; 
lean_inc_ref(v_l_3418_);
lean_dec(v_h__2_3416_);
v_size_3419_ = lean_ctor_get(v_x_3413_, 0);
lean_inc(v_size_3419_);
v_k_3420_ = lean_ctor_get(v_x_3413_, 1);
lean_inc(v_k_3420_);
v_v_3421_ = lean_ctor_get(v_x_3413_, 2);
lean_inc(v_v_3421_);
v_r_3422_ = lean_ctor_get(v_x_3413_, 4);
lean_inc(v_r_3422_);
lean_dec_ref(v_x_3413_);
v_size_3423_ = lean_ctor_get(v_l_3418_, 0);
lean_inc(v_size_3423_);
v_k_3424_ = lean_ctor_get(v_l_3418_, 1);
lean_inc(v_k_3424_);
v_v_3425_ = lean_ctor_get(v_l_3418_, 2);
lean_inc(v_v_3425_);
v_l_3426_ = lean_ctor_get(v_l_3418_, 3);
lean_inc(v_l_3426_);
v_r_3427_ = lean_ctor_get(v_l_3418_, 4);
lean_inc(v_r_3427_);
lean_dec_ref(v_l_3418_);
v___x_3428_ = lean_apply_10(v_h__3_3417_, v_size_3419_, v_k_3420_, v_v_3421_, v_size_3423_, v_k_3424_, v_v_3425_, v_l_3426_, v_r_3427_, v_r_3422_, v_x_3414_);
return v___x_3428_;
}
else
{
lean_object* v_size_3429_; lean_object* v_k_3430_; lean_object* v_v_3431_; lean_object* v_r_3432_; lean_object* v___x_3433_; 
lean_dec(v_h__3_3417_);
v_size_3429_ = lean_ctor_get(v_x_3413_, 0);
lean_inc(v_size_3429_);
v_k_3430_ = lean_ctor_get(v_x_3413_, 1);
lean_inc(v_k_3430_);
v_v_3431_ = lean_ctor_get(v_x_3413_, 2);
lean_inc(v_v_3431_);
v_r_3432_ = lean_ctor_get(v_x_3413_, 4);
lean_inc(v_r_3432_);
lean_dec_ref(v_x_3413_);
v___x_3433_ = lean_apply_5(v_h__2_3416_, v_size_3429_, v_k_3430_, v_v_3431_, v_r_3432_, v_x_3414_);
return v___x_3433_;
}
}
else
{
lean_object* v___x_3434_; 
lean_dec(v_h__3_3417_);
lean_dec(v_h__2_3416_);
v___x_3434_ = lean_apply_1(v_h__1_3415_, v_x_3414_);
return v___x_3434_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object* v_x_3435_){
_start:
{
if (lean_obj_tag(v_x_3435_) == 0)
{
lean_object* v_r_3436_; 
v_r_3436_ = lean_ctor_get(v_x_3435_, 4);
if (lean_obj_tag(v_r_3436_) == 0)
{
v_x_3435_ = v_r_3436_;
goto _start;
}
else
{
lean_object* v_k_3438_; lean_object* v_v_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; 
v_k_3438_ = lean_ctor_get(v_x_3435_, 1);
v_v_3439_ = lean_ctor_get(v_x_3435_, 2);
lean_inc(v_v_3439_);
lean_inc(v_k_3438_);
v___x_3440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3440_, 0, v_k_3438_);
lean_ctor_set(v___x_3440_, 1, v_v_3439_);
v___x_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3441_, 0, v___x_3440_);
return v___x_3441_;
}
}
else
{
lean_object* v___x_3442_; 
v___x_3442_ = lean_box(0);
return v___x_3442_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg___boxed(lean_object* v_x_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3443_);
lean_dec(v_x_3443_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(lean_object* v_00_u03b1_3445_, lean_object* v_00_u03b2_3446_, lean_object* v_x_3447_){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3447_);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_3449_, lean_object* v_00_u03b2_3450_, lean_object* v_x_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(v_00_u03b1_3449_, v_00_u03b2_3450_, v_x_3451_);
lean_dec(v_x_3451_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3453_, lean_object* v_h__1_3454_, lean_object* v_h__2_3455_, lean_object* v_h__3_3456_){
_start:
{
if (lean_obj_tag(v_x_3453_) == 0)
{
lean_object* v_r_3457_; 
lean_dec(v_h__1_3454_);
v_r_3457_ = lean_ctor_get(v_x_3453_, 4);
if (lean_obj_tag(v_r_3457_) == 0)
{
lean_object* v_size_3458_; lean_object* v_k_3459_; lean_object* v_v_3460_; lean_object* v_l_3461_; lean_object* v_size_3462_; lean_object* v_k_3463_; lean_object* v_v_3464_; lean_object* v_l_3465_; lean_object* v_r_3466_; lean_object* v___x_3467_; 
lean_inc_ref(v_r_3457_);
lean_dec(v_h__2_3455_);
v_size_3458_ = lean_ctor_get(v_x_3453_, 0);
lean_inc(v_size_3458_);
v_k_3459_ = lean_ctor_get(v_x_3453_, 1);
lean_inc(v_k_3459_);
v_v_3460_ = lean_ctor_get(v_x_3453_, 2);
lean_inc(v_v_3460_);
v_l_3461_ = lean_ctor_get(v_x_3453_, 3);
lean_inc(v_l_3461_);
lean_dec_ref(v_x_3453_);
v_size_3462_ = lean_ctor_get(v_r_3457_, 0);
lean_inc(v_size_3462_);
v_k_3463_ = lean_ctor_get(v_r_3457_, 1);
lean_inc(v_k_3463_);
v_v_3464_ = lean_ctor_get(v_r_3457_, 2);
lean_inc(v_v_3464_);
v_l_3465_ = lean_ctor_get(v_r_3457_, 3);
lean_inc(v_l_3465_);
v_r_3466_ = lean_ctor_get(v_r_3457_, 4);
lean_inc(v_r_3466_);
lean_dec_ref(v_r_3457_);
v___x_3467_ = lean_apply_9(v_h__3_3456_, v_size_3458_, v_k_3459_, v_v_3460_, v_l_3461_, v_size_3462_, v_k_3463_, v_v_3464_, v_l_3465_, v_r_3466_);
return v___x_3467_;
}
else
{
lean_object* v_size_3468_; lean_object* v_k_3469_; lean_object* v_v_3470_; lean_object* v_l_3471_; lean_object* v___x_3472_; 
lean_dec(v_h__3_3456_);
v_size_3468_ = lean_ctor_get(v_x_3453_, 0);
lean_inc(v_size_3468_);
v_k_3469_ = lean_ctor_get(v_x_3453_, 1);
lean_inc(v_k_3469_);
v_v_3470_ = lean_ctor_get(v_x_3453_, 2);
lean_inc(v_v_3470_);
v_l_3471_ = lean_ctor_get(v_x_3453_, 3);
lean_inc(v_l_3471_);
lean_dec_ref(v_x_3453_);
v___x_3472_ = lean_apply_4(v_h__2_3455_, v_size_3468_, v_k_3469_, v_v_3470_, v_l_3471_);
return v___x_3472_;
}
}
else
{
lean_object* v___x_3473_; lean_object* v___x_3474_; 
lean_dec(v_h__3_3456_);
lean_dec(v_h__2_3455_);
v___x_3473_ = lean_box(0);
v___x_3474_ = lean_apply_1(v_h__1_3454_, v___x_3473_);
return v___x_3474_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3475_, lean_object* v_00_u03b2_3476_, lean_object* v_motive_3477_, lean_object* v_x_3478_, lean_object* v_h__1_3479_, lean_object* v_h__2_3480_, lean_object* v_h__3_3481_){
_start:
{
if (lean_obj_tag(v_x_3478_) == 0)
{
lean_object* v_r_3482_; 
lean_dec(v_h__1_3479_);
v_r_3482_ = lean_ctor_get(v_x_3478_, 4);
if (lean_obj_tag(v_r_3482_) == 0)
{
lean_object* v_size_3483_; lean_object* v_k_3484_; lean_object* v_v_3485_; lean_object* v_l_3486_; lean_object* v_size_3487_; lean_object* v_k_3488_; lean_object* v_v_3489_; lean_object* v_l_3490_; lean_object* v_r_3491_; lean_object* v___x_3492_; 
lean_inc_ref(v_r_3482_);
lean_dec(v_h__2_3480_);
v_size_3483_ = lean_ctor_get(v_x_3478_, 0);
lean_inc(v_size_3483_);
v_k_3484_ = lean_ctor_get(v_x_3478_, 1);
lean_inc(v_k_3484_);
v_v_3485_ = lean_ctor_get(v_x_3478_, 2);
lean_inc(v_v_3485_);
v_l_3486_ = lean_ctor_get(v_x_3478_, 3);
lean_inc(v_l_3486_);
lean_dec_ref(v_x_3478_);
v_size_3487_ = lean_ctor_get(v_r_3482_, 0);
lean_inc(v_size_3487_);
v_k_3488_ = lean_ctor_get(v_r_3482_, 1);
lean_inc(v_k_3488_);
v_v_3489_ = lean_ctor_get(v_r_3482_, 2);
lean_inc(v_v_3489_);
v_l_3490_ = lean_ctor_get(v_r_3482_, 3);
lean_inc(v_l_3490_);
v_r_3491_ = lean_ctor_get(v_r_3482_, 4);
lean_inc(v_r_3491_);
lean_dec_ref(v_r_3482_);
v___x_3492_ = lean_apply_9(v_h__3_3481_, v_size_3483_, v_k_3484_, v_v_3485_, v_l_3486_, v_size_3487_, v_k_3488_, v_v_3489_, v_l_3490_, v_r_3491_);
return v___x_3492_;
}
else
{
lean_object* v_size_3493_; lean_object* v_k_3494_; lean_object* v_v_3495_; lean_object* v_l_3496_; lean_object* v___x_3497_; 
lean_dec(v_h__3_3481_);
v_size_3493_ = lean_ctor_get(v_x_3478_, 0);
lean_inc(v_size_3493_);
v_k_3494_ = lean_ctor_get(v_x_3478_, 1);
lean_inc(v_k_3494_);
v_v_3495_ = lean_ctor_get(v_x_3478_, 2);
lean_inc(v_v_3495_);
v_l_3496_ = lean_ctor_get(v_x_3478_, 3);
lean_inc(v_l_3496_);
lean_dec_ref(v_x_3478_);
v___x_3497_ = lean_apply_4(v_h__2_3480_, v_size_3493_, v_k_3494_, v_v_3495_, v_l_3496_);
return v___x_3497_;
}
}
else
{
lean_object* v___x_3498_; lean_object* v___x_3499_; 
lean_dec(v_h__3_3481_);
lean_dec(v_h__2_3480_);
v___x_3498_ = lean_box(0);
v___x_3499_ = lean_apply_1(v_h__1_3479_, v___x_3498_);
return v___x_3499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object* v_x_3500_){
_start:
{
lean_object* v_r_3501_; 
v_r_3501_ = lean_ctor_get(v_x_3500_, 4);
if (lean_obj_tag(v_r_3501_) == 0)
{
v_x_3500_ = v_r_3501_;
goto _start;
}
else
{
lean_object* v_k_3503_; lean_object* v_v_3504_; lean_object* v___x_3505_; 
v_k_3503_ = lean_ctor_get(v_x_3500_, 1);
v_v_3504_ = lean_ctor_get(v_x_3500_, 2);
lean_inc(v_v_3504_);
lean_inc(v_k_3503_);
v___x_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3505_, 0, v_k_3503_);
lean_ctor_set(v___x_3505_, 1, v_v_3504_);
return v___x_3505_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg___boxed(lean_object* v_x_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3506_);
lean_dec(v_x_3506_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry(lean_object* v_00_u03b1_3508_, lean_object* v_00_u03b2_3509_, lean_object* v_x_3510_, lean_object* v_x_3511_){
_start:
{
lean_object* v___x_3512_; 
v___x_3512_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3510_);
return v___x_3512_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___boxed(lean_object* v_00_u03b1_3513_, lean_object* v_00_u03b2_3514_, lean_object* v_x_3515_, lean_object* v_x_3516_){
_start:
{
lean_object* v_res_3517_; 
v_res_3517_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry(v_00_u03b1_3513_, v_00_u03b2_3514_, v_x_3515_, v_x_3516_);
lean_dec(v_x_3515_);
return v_res_3517_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_3518_, lean_object* v_h__1_3519_, lean_object* v_h__2_3520_){
_start:
{
lean_object* v_r_3521_; 
v_r_3521_ = lean_ctor_get(v_x_3518_, 4);
if (lean_obj_tag(v_r_3521_) == 0)
{
lean_object* v_size_3522_; lean_object* v_k_3523_; lean_object* v_v_3524_; lean_object* v_l_3525_; lean_object* v_size_3526_; lean_object* v_k_3527_; lean_object* v_v_3528_; lean_object* v_l_3529_; lean_object* v_r_3530_; lean_object* v___x_3531_; 
lean_inc_ref(v_r_3521_);
lean_dec(v_h__1_3519_);
v_size_3522_ = lean_ctor_get(v_x_3518_, 0);
lean_inc(v_size_3522_);
v_k_3523_ = lean_ctor_get(v_x_3518_, 1);
lean_inc(v_k_3523_);
v_v_3524_ = lean_ctor_get(v_x_3518_, 2);
lean_inc(v_v_3524_);
v_l_3525_ = lean_ctor_get(v_x_3518_, 3);
lean_inc(v_l_3525_);
lean_dec(v_x_3518_);
v_size_3526_ = lean_ctor_get(v_r_3521_, 0);
lean_inc(v_size_3526_);
v_k_3527_ = lean_ctor_get(v_r_3521_, 1);
lean_inc(v_k_3527_);
v_v_3528_ = lean_ctor_get(v_r_3521_, 2);
lean_inc(v_v_3528_);
v_l_3529_ = lean_ctor_get(v_r_3521_, 3);
lean_inc(v_l_3529_);
v_r_3530_ = lean_ctor_get(v_r_3521_, 4);
lean_inc(v_r_3530_);
lean_dec_ref(v_r_3521_);
v___x_3531_ = lean_apply_10(v_h__2_3520_, v_size_3522_, v_k_3523_, v_v_3524_, v_l_3525_, v_size_3526_, v_k_3527_, v_v_3528_, v_l_3529_, v_r_3530_, lean_box(0));
return v___x_3531_;
}
else
{
lean_object* v_size_3532_; lean_object* v_k_3533_; lean_object* v_v_3534_; lean_object* v_l_3535_; lean_object* v___x_3536_; 
lean_dec(v_h__2_3520_);
v_size_3532_ = lean_ctor_get(v_x_3518_, 0);
lean_inc(v_size_3532_);
v_k_3533_ = lean_ctor_get(v_x_3518_, 1);
lean_inc(v_k_3533_);
v_v_3534_ = lean_ctor_get(v_x_3518_, 2);
lean_inc(v_v_3534_);
v_l_3535_ = lean_ctor_get(v_x_3518_, 3);
lean_inc(v_l_3535_);
lean_dec(v_x_3518_);
v___x_3536_ = lean_apply_5(v_h__1_3519_, v_size_3532_, v_k_3533_, v_v_3534_, v_l_3535_, lean_box(0));
return v___x_3536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_3537_, lean_object* v_00_u03b2_3538_, lean_object* v_motive_3539_, lean_object* v_x_3540_, lean_object* v_x_3541_, lean_object* v_h__1_3542_, lean_object* v_h__2_3543_){
_start:
{
lean_object* v_r_3544_; 
v_r_3544_ = lean_ctor_get(v_x_3540_, 4);
if (lean_obj_tag(v_r_3544_) == 0)
{
lean_object* v_size_3545_; lean_object* v_k_3546_; lean_object* v_v_3547_; lean_object* v_l_3548_; lean_object* v_size_3549_; lean_object* v_k_3550_; lean_object* v_v_3551_; lean_object* v_l_3552_; lean_object* v_r_3553_; lean_object* v___x_3554_; 
lean_inc_ref(v_r_3544_);
lean_dec(v_h__1_3542_);
v_size_3545_ = lean_ctor_get(v_x_3540_, 0);
lean_inc(v_size_3545_);
v_k_3546_ = lean_ctor_get(v_x_3540_, 1);
lean_inc(v_k_3546_);
v_v_3547_ = lean_ctor_get(v_x_3540_, 2);
lean_inc(v_v_3547_);
v_l_3548_ = lean_ctor_get(v_x_3540_, 3);
lean_inc(v_l_3548_);
lean_dec(v_x_3540_);
v_size_3549_ = lean_ctor_get(v_r_3544_, 0);
lean_inc(v_size_3549_);
v_k_3550_ = lean_ctor_get(v_r_3544_, 1);
lean_inc(v_k_3550_);
v_v_3551_ = lean_ctor_get(v_r_3544_, 2);
lean_inc(v_v_3551_);
v_l_3552_ = lean_ctor_get(v_r_3544_, 3);
lean_inc(v_l_3552_);
v_r_3553_ = lean_ctor_get(v_r_3544_, 4);
lean_inc(v_r_3553_);
lean_dec_ref(v_r_3544_);
v___x_3554_ = lean_apply_10(v_h__2_3543_, v_size_3545_, v_k_3546_, v_v_3547_, v_l_3548_, v_size_3549_, v_k_3550_, v_v_3551_, v_l_3552_, v_r_3553_, lean_box(0));
return v___x_3554_;
}
else
{
lean_object* v_size_3555_; lean_object* v_k_3556_; lean_object* v_v_3557_; lean_object* v_l_3558_; lean_object* v___x_3559_; 
lean_dec(v_h__2_3543_);
v_size_3555_ = lean_ctor_get(v_x_3540_, 0);
lean_inc(v_size_3555_);
v_k_3556_ = lean_ctor_get(v_x_3540_, 1);
lean_inc(v_k_3556_);
v_v_3557_ = lean_ctor_get(v_x_3540_, 2);
lean_inc(v_v_3557_);
v_l_3558_ = lean_ctor_get(v_x_3540_, 3);
lean_inc(v_l_3558_);
lean_dec(v_x_3540_);
v___x_3559_ = lean_apply_5(v_h__1_3542_, v_size_3555_, v_k_3556_, v_v_3557_, v_l_3558_, lean_box(0));
return v___x_3559_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3561_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3562_ = lean_unsigned_to_nat(13u);
v___x_3563_ = lean_unsigned_to_nat(839u);
v___x_3564_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0));
v___x_3565_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3566_ = l_mkPanicMessageWithDecl(v___x_3565_, v___x_3564_, v___x_3563_, v___x_3562_, v___x_3561_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object* v_inst_3567_, lean_object* v_x_3568_){
_start:
{
if (lean_obj_tag(v_x_3568_) == 0)
{
lean_object* v_r_3569_; 
v_r_3569_ = lean_ctor_get(v_x_3568_, 4);
if (lean_obj_tag(v_r_3569_) == 0)
{
v_x_3568_ = v_r_3569_;
goto _start;
}
else
{
lean_object* v_k_3571_; lean_object* v_v_3572_; lean_object* v___x_3573_; 
v_k_3571_ = lean_ctor_get(v_x_3568_, 1);
v_v_3572_ = lean_ctor_get(v_x_3568_, 2);
lean_inc(v_v_3572_);
lean_inc(v_k_3571_);
v___x_3573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3573_, 0, v_k_3571_);
lean_ctor_set(v___x_3573_, 1, v_v_3572_);
return v___x_3573_;
}
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1);
v___x_3575_ = l_panic___redArg(v_inst_3567_, v___x_3574_);
return v___x_3575_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_3576_, lean_object* v_x_3577_){
_start:
{
lean_object* v_res_3578_; 
v_res_3578_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3576_, v_x_3577_);
lean_dec(v_x_3577_);
lean_dec_ref(v_inst_3576_);
return v_res_3578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(lean_object* v_00_u03b1_3579_, lean_object* v_00_u03b2_3580_, lean_object* v_inst_3581_, lean_object* v_x_3582_){
_start:
{
lean_object* v___x_3583_; 
v___x_3583_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3581_, v_x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_3584_, lean_object* v_00_u03b2_3585_, lean_object* v_inst_3586_, lean_object* v_x_3587_){
_start:
{
lean_object* v_res_3588_; 
v_res_3588_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(v_00_u03b1_3584_, v_00_u03b2_3585_, v_inst_3586_, v_x_3587_);
lean_dec(v_x_3587_);
lean_dec_ref(v_inst_3586_);
return v_res_3588_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object* v_x_3589_, lean_object* v_x_3590_){
_start:
{
if (lean_obj_tag(v_x_3589_) == 0)
{
lean_object* v_r_3591_; 
v_r_3591_ = lean_ctor_get(v_x_3589_, 4);
if (lean_obj_tag(v_r_3591_) == 0)
{
v_x_3589_ = v_r_3591_;
goto _start;
}
else
{
lean_object* v_k_3593_; lean_object* v_v_3594_; lean_object* v___x_3595_; 
v_k_3593_ = lean_ctor_get(v_x_3589_, 1);
v_v_3594_ = lean_ctor_get(v_x_3589_, 2);
lean_inc(v_v_3594_);
lean_inc(v_k_3593_);
v___x_3595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3595_, 0, v_k_3593_);
lean_ctor_set(v___x_3595_, 1, v_v_3594_);
return v___x_3595_;
}
}
else
{
lean_inc_ref(v_x_3590_);
return v_x_3590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg___boxed(lean_object* v_x_3596_, lean_object* v_x_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3596_, v_x_3597_);
lean_dec_ref(v_x_3597_);
lean_dec(v_x_3596_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(lean_object* v_00_u03b1_3599_, lean_object* v_00_u03b2_3600_, lean_object* v_x_3601_, lean_object* v_x_3602_){
_start:
{
lean_object* v___x_3603_; 
v___x_3603_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3601_, v_x_3602_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___boxed(lean_object* v_00_u03b1_3604_, lean_object* v_00_u03b2_3605_, lean_object* v_x_3606_, lean_object* v_x_3607_){
_start:
{
lean_object* v_res_3608_; 
v_res_3608_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(v_00_u03b1_3604_, v_00_u03b2_3605_, v_x_3606_, v_x_3607_);
lean_dec_ref(v_x_3607_);
lean_dec(v_x_3606_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_3609_, lean_object* v_x_3610_, lean_object* v_h__1_3611_, lean_object* v_h__2_3612_, lean_object* v_h__3_3613_){
_start:
{
if (lean_obj_tag(v_x_3609_) == 0)
{
lean_object* v_r_3614_; 
lean_dec(v_h__1_3611_);
v_r_3614_ = lean_ctor_get(v_x_3609_, 4);
if (lean_obj_tag(v_r_3614_) == 0)
{
lean_object* v_size_3615_; lean_object* v_k_3616_; lean_object* v_v_3617_; lean_object* v_l_3618_; lean_object* v_size_3619_; lean_object* v_k_3620_; lean_object* v_v_3621_; lean_object* v_l_3622_; lean_object* v_r_3623_; lean_object* v___x_3624_; 
lean_inc_ref(v_r_3614_);
lean_dec(v_h__2_3612_);
v_size_3615_ = lean_ctor_get(v_x_3609_, 0);
lean_inc(v_size_3615_);
v_k_3616_ = lean_ctor_get(v_x_3609_, 1);
lean_inc(v_k_3616_);
v_v_3617_ = lean_ctor_get(v_x_3609_, 2);
lean_inc(v_v_3617_);
v_l_3618_ = lean_ctor_get(v_x_3609_, 3);
lean_inc(v_l_3618_);
lean_dec_ref(v_x_3609_);
v_size_3619_ = lean_ctor_get(v_r_3614_, 0);
lean_inc(v_size_3619_);
v_k_3620_ = lean_ctor_get(v_r_3614_, 1);
lean_inc(v_k_3620_);
v_v_3621_ = lean_ctor_get(v_r_3614_, 2);
lean_inc(v_v_3621_);
v_l_3622_ = lean_ctor_get(v_r_3614_, 3);
lean_inc(v_l_3622_);
v_r_3623_ = lean_ctor_get(v_r_3614_, 4);
lean_inc(v_r_3623_);
lean_dec_ref(v_r_3614_);
v___x_3624_ = lean_apply_10(v_h__3_3613_, v_size_3615_, v_k_3616_, v_v_3617_, v_l_3618_, v_size_3619_, v_k_3620_, v_v_3621_, v_l_3622_, v_r_3623_, v_x_3610_);
return v___x_3624_;
}
else
{
lean_object* v_size_3625_; lean_object* v_k_3626_; lean_object* v_v_3627_; lean_object* v_l_3628_; lean_object* v___x_3629_; 
lean_dec(v_h__3_3613_);
v_size_3625_ = lean_ctor_get(v_x_3609_, 0);
lean_inc(v_size_3625_);
v_k_3626_ = lean_ctor_get(v_x_3609_, 1);
lean_inc(v_k_3626_);
v_v_3627_ = lean_ctor_get(v_x_3609_, 2);
lean_inc(v_v_3627_);
v_l_3628_ = lean_ctor_get(v_x_3609_, 3);
lean_inc(v_l_3628_);
lean_dec_ref(v_x_3609_);
v___x_3629_ = lean_apply_5(v_h__2_3612_, v_size_3625_, v_k_3626_, v_v_3627_, v_l_3628_, v_x_3610_);
return v___x_3629_;
}
}
else
{
lean_object* v___x_3630_; 
lean_dec(v_h__3_3613_);
lean_dec(v_h__2_3612_);
v___x_3630_ = lean_apply_1(v_h__1_3611_, v_x_3610_);
return v___x_3630_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_3631_, lean_object* v_00_u03b2_3632_, lean_object* v_motive_3633_, lean_object* v_x_3634_, lean_object* v_x_3635_, lean_object* v_h__1_3636_, lean_object* v_h__2_3637_, lean_object* v_h__3_3638_){
_start:
{
if (lean_obj_tag(v_x_3634_) == 0)
{
lean_object* v_r_3639_; 
lean_dec(v_h__1_3636_);
v_r_3639_ = lean_ctor_get(v_x_3634_, 4);
if (lean_obj_tag(v_r_3639_) == 0)
{
lean_object* v_size_3640_; lean_object* v_k_3641_; lean_object* v_v_3642_; lean_object* v_l_3643_; lean_object* v_size_3644_; lean_object* v_k_3645_; lean_object* v_v_3646_; lean_object* v_l_3647_; lean_object* v_r_3648_; lean_object* v___x_3649_; 
lean_inc_ref(v_r_3639_);
lean_dec(v_h__2_3637_);
v_size_3640_ = lean_ctor_get(v_x_3634_, 0);
lean_inc(v_size_3640_);
v_k_3641_ = lean_ctor_get(v_x_3634_, 1);
lean_inc(v_k_3641_);
v_v_3642_ = lean_ctor_get(v_x_3634_, 2);
lean_inc(v_v_3642_);
v_l_3643_ = lean_ctor_get(v_x_3634_, 3);
lean_inc(v_l_3643_);
lean_dec_ref(v_x_3634_);
v_size_3644_ = lean_ctor_get(v_r_3639_, 0);
lean_inc(v_size_3644_);
v_k_3645_ = lean_ctor_get(v_r_3639_, 1);
lean_inc(v_k_3645_);
v_v_3646_ = lean_ctor_get(v_r_3639_, 2);
lean_inc(v_v_3646_);
v_l_3647_ = lean_ctor_get(v_r_3639_, 3);
lean_inc(v_l_3647_);
v_r_3648_ = lean_ctor_get(v_r_3639_, 4);
lean_inc(v_r_3648_);
lean_dec_ref(v_r_3639_);
v___x_3649_ = lean_apply_10(v_h__3_3638_, v_size_3640_, v_k_3641_, v_v_3642_, v_l_3643_, v_size_3644_, v_k_3645_, v_v_3646_, v_l_3647_, v_r_3648_, v_x_3635_);
return v___x_3649_;
}
else
{
lean_object* v_size_3650_; lean_object* v_k_3651_; lean_object* v_v_3652_; lean_object* v_l_3653_; lean_object* v___x_3654_; 
lean_dec(v_h__3_3638_);
v_size_3650_ = lean_ctor_get(v_x_3634_, 0);
lean_inc(v_size_3650_);
v_k_3651_ = lean_ctor_get(v_x_3634_, 1);
lean_inc(v_k_3651_);
v_v_3652_ = lean_ctor_get(v_x_3634_, 2);
lean_inc(v_v_3652_);
v_l_3653_ = lean_ctor_get(v_x_3634_, 3);
lean_inc(v_l_3653_);
lean_dec_ref(v_x_3634_);
v___x_3654_ = lean_apply_5(v_h__2_3637_, v_size_3650_, v_k_3651_, v_v_3652_, v_l_3653_, v_x_3635_);
return v___x_3654_;
}
}
else
{
lean_object* v___x_3655_; 
lean_dec(v_h__3_3638_);
lean_dec(v_h__2_3637_);
v___x_3655_ = lean_apply_1(v_h__1_3636_, v_x_3635_);
return v___x_3655_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object* v_x_3656_, lean_object* v_x_3657_){
_start:
{
lean_object* v_k_3658_; lean_object* v_v_3659_; lean_object* v_l_3660_; lean_object* v_r_3661_; lean_object* v___y_3663_; lean_object* v___y_3669_; 
v_k_3658_ = lean_ctor_get(v_x_3656_, 1);
v_v_3659_ = lean_ctor_get(v_x_3656_, 2);
v_l_3660_ = lean_ctor_get(v_x_3656_, 3);
v_r_3661_ = lean_ctor_get(v_x_3656_, 4);
if (lean_obj_tag(v_l_3660_) == 0)
{
lean_object* v_size_3676_; 
v_size_3676_ = lean_ctor_get(v_l_3660_, 0);
v___y_3669_ = v_size_3676_;
goto v___jp_3668_;
}
else
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_unsigned_to_nat(0u);
v___y_3669_ = v___x_3677_;
goto v___jp_3668_;
}
v___jp_3662_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = lean_nat_sub(v_x_3657_, v___y_3663_);
lean_dec(v_x_3657_);
v___x_3665_ = lean_unsigned_to_nat(1u);
v___x_3666_ = lean_nat_sub(v___x_3664_, v___x_3665_);
lean_dec(v___x_3664_);
v_x_3656_ = v_r_3661_;
v_x_3657_ = v___x_3666_;
goto _start;
}
v___jp_3668_:
{
uint8_t v___x_3670_; 
v___x_3670_ = lean_nat_dec_lt(v_x_3657_, v___y_3669_);
if (v___x_3670_ == 0)
{
uint8_t v___x_3671_; 
v___x_3671_ = lean_nat_dec_eq(v_x_3657_, v___y_3669_);
if (v___x_3671_ == 0)
{
if (lean_obj_tag(v_l_3660_) == 0)
{
lean_object* v_size_3672_; 
v_size_3672_ = lean_ctor_get(v_l_3660_, 0);
v___y_3663_ = v_size_3672_;
goto v___jp_3662_;
}
else
{
lean_object* v___x_3673_; 
v___x_3673_ = lean_unsigned_to_nat(0u);
v___y_3663_ = v___x_3673_;
goto v___jp_3662_;
}
}
else
{
lean_object* v___x_3674_; 
lean_dec(v_x_3657_);
lean_inc(v_v_3659_);
lean_inc(v_k_3658_);
v___x_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3674_, 0, v_k_3658_);
lean_ctor_set(v___x_3674_, 1, v_v_3659_);
return v___x_3674_;
}
}
else
{
v_x_3656_ = v_l_3660_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg___boxed(lean_object* v_x_3678_, lean_object* v_x_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3678_, v_x_3679_);
lean_dec(v_x_3678_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_object* v_00_u03b1_3681_, lean_object* v_00_u03b2_3682_, lean_object* v_x_3683_, lean_object* v_x_3684_, lean_object* v_x_3685_, lean_object* v_x_3686_){
_start:
{
lean_object* v___x_3687_; 
v___x_3687_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3683_, v_x_3685_);
return v___x_3687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_3688_, lean_object* v_00_u03b2_3689_, lean_object* v_x_3690_, lean_object* v_x_3691_, lean_object* v_x_3692_, lean_object* v_x_3693_){
_start:
{
lean_object* v_res_3694_; 
v_res_3694_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(v_00_u03b1_3688_, v_00_u03b2_3689_, v_x_3690_, v_x_3691_, v_x_3692_, v_x_3693_);
lean_dec(v_x_3690_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object* v_x_3695_, lean_object* v_x_3696_){
_start:
{
if (lean_obj_tag(v_x_3695_) == 0)
{
lean_object* v_k_3697_; lean_object* v_v_3698_; lean_object* v_l_3699_; lean_object* v_r_3700_; lean_object* v___y_3702_; lean_object* v___y_3708_; 
v_k_3697_ = lean_ctor_get(v_x_3695_, 1);
v_v_3698_ = lean_ctor_get(v_x_3695_, 2);
v_l_3699_ = lean_ctor_get(v_x_3695_, 3);
v_r_3700_ = lean_ctor_get(v_x_3695_, 4);
if (lean_obj_tag(v_l_3699_) == 0)
{
lean_object* v_size_3716_; 
v_size_3716_ = lean_ctor_get(v_l_3699_, 0);
v___y_3708_ = v_size_3716_;
goto v___jp_3707_;
}
else
{
lean_object* v___x_3717_; 
v___x_3717_ = lean_unsigned_to_nat(0u);
v___y_3708_ = v___x_3717_;
goto v___jp_3707_;
}
v___jp_3701_:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; 
v___x_3703_ = lean_nat_sub(v_x_3696_, v___y_3702_);
lean_dec(v_x_3696_);
v___x_3704_ = lean_unsigned_to_nat(1u);
v___x_3705_ = lean_nat_sub(v___x_3703_, v___x_3704_);
lean_dec(v___x_3703_);
v_x_3695_ = v_r_3700_;
v_x_3696_ = v___x_3705_;
goto _start;
}
v___jp_3707_:
{
uint8_t v___x_3709_; 
v___x_3709_ = lean_nat_dec_lt(v_x_3696_, v___y_3708_);
if (v___x_3709_ == 0)
{
uint8_t v___x_3710_; 
v___x_3710_ = lean_nat_dec_eq(v_x_3696_, v___y_3708_);
if (v___x_3710_ == 0)
{
if (lean_obj_tag(v_l_3699_) == 0)
{
lean_object* v_size_3711_; 
v_size_3711_ = lean_ctor_get(v_l_3699_, 0);
v___y_3702_ = v_size_3711_;
goto v___jp_3701_;
}
else
{
lean_object* v___x_3712_; 
v___x_3712_ = lean_unsigned_to_nat(0u);
v___y_3702_ = v___x_3712_;
goto v___jp_3701_;
}
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3714_; 
lean_dec(v_x_3696_);
lean_inc(v_v_3698_);
lean_inc(v_k_3697_);
v___x_3713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3713_, 0, v_k_3697_);
lean_ctor_set(v___x_3713_, 1, v_v_3698_);
v___x_3714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3714_, 0, v___x_3713_);
return v___x_3714_;
}
}
else
{
v_x_3695_ = v_l_3699_;
goto _start;
}
}
}
else
{
lean_object* v___x_3718_; 
lean_dec(v_x_3696_);
v___x_3718_ = lean_box(0);
return v___x_3718_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_3719_, lean_object* v_x_3720_){
_start:
{
lean_object* v_res_3721_; 
v_res_3721_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3719_, v_x_3720_);
lean_dec(v_x_3719_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_3722_, lean_object* v_00_u03b2_3723_, lean_object* v_x_3724_, lean_object* v_x_3725_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3724_, v_x_3725_);
return v___x_3726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_3727_, lean_object* v_00_u03b2_3728_, lean_object* v_x_3729_, lean_object* v_x_3730_){
_start:
{
lean_object* v_res_3731_; 
v_res_3731_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(v_00_u03b1_3727_, v_00_u03b2_3728_, v_x_3729_, v_x_3730_);
lean_dec(v_x_3729_);
return v_res_3731_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3733_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_3734_ = lean_unsigned_to_nat(16u);
v___x_3735_ = lean_unsigned_to_nat(870u);
v___x_3736_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0));
v___x_3737_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3738_ = l_mkPanicMessageWithDecl(v___x_3737_, v___x_3736_, v___x_3735_, v___x_3734_, v___x_3733_);
return v___x_3738_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object* v_inst_3739_, lean_object* v_x_3740_, lean_object* v_x_3741_){
_start:
{
if (lean_obj_tag(v_x_3740_) == 0)
{
lean_object* v_k_3742_; lean_object* v_v_3743_; lean_object* v_l_3744_; lean_object* v_r_3745_; lean_object* v___y_3747_; lean_object* v___y_3753_; 
v_k_3742_ = lean_ctor_get(v_x_3740_, 1);
v_v_3743_ = lean_ctor_get(v_x_3740_, 2);
v_l_3744_ = lean_ctor_get(v_x_3740_, 3);
v_r_3745_ = lean_ctor_get(v_x_3740_, 4);
if (lean_obj_tag(v_l_3744_) == 0)
{
lean_object* v_size_3760_; 
v_size_3760_ = lean_ctor_get(v_l_3744_, 0);
v___y_3753_ = v_size_3760_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3761_; 
v___x_3761_ = lean_unsigned_to_nat(0u);
v___y_3753_ = v___x_3761_;
goto v___jp_3752_;
}
v___jp_3746_:
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3748_ = lean_nat_sub(v_x_3741_, v___y_3747_);
lean_dec(v_x_3741_);
v___x_3749_ = lean_unsigned_to_nat(1u);
v___x_3750_ = lean_nat_sub(v___x_3748_, v___x_3749_);
lean_dec(v___x_3748_);
v_x_3740_ = v_r_3745_;
v_x_3741_ = v___x_3750_;
goto _start;
}
v___jp_3752_:
{
uint8_t v___x_3754_; 
v___x_3754_ = lean_nat_dec_lt(v_x_3741_, v___y_3753_);
if (v___x_3754_ == 0)
{
uint8_t v___x_3755_; 
v___x_3755_ = lean_nat_dec_eq(v_x_3741_, v___y_3753_);
if (v___x_3755_ == 0)
{
if (lean_obj_tag(v_l_3744_) == 0)
{
lean_object* v_size_3756_; 
v_size_3756_ = lean_ctor_get(v_l_3744_, 0);
v___y_3747_ = v_size_3756_;
goto v___jp_3746_;
}
else
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_unsigned_to_nat(0u);
v___y_3747_ = v___x_3757_;
goto v___jp_3746_;
}
}
else
{
lean_object* v___x_3758_; 
lean_dec(v_x_3741_);
lean_inc(v_v_3743_);
lean_inc(v_k_3742_);
v___x_3758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3758_, 0, v_k_3742_);
lean_ctor_set(v___x_3758_, 1, v_v_3743_);
return v___x_3758_;
}
}
else
{
v_x_3740_ = v_l_3744_;
goto _start;
}
}
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_dec(v_x_3741_);
v___x_3762_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1);
v___x_3763_ = l_panic___redArg(v_inst_3739_, v___x_3762_);
return v___x_3763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_3764_, lean_object* v_x_3765_, lean_object* v_x_3766_){
_start:
{
lean_object* v_res_3767_; 
v_res_3767_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3764_, v_x_3765_, v_x_3766_);
lean_dec(v_x_3765_);
lean_dec_ref(v_inst_3764_);
return v_res_3767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(lean_object* v_00_u03b1_3768_, lean_object* v_00_u03b2_3769_, lean_object* v_inst_3770_, lean_object* v_x_3771_, lean_object* v_x_3772_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3770_, v_x_3771_, v_x_3772_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_3774_, lean_object* v_00_u03b2_3775_, lean_object* v_inst_3776_, lean_object* v_x_3777_, lean_object* v_x_3778_){
_start:
{
lean_object* v_res_3779_; 
v_res_3779_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(v_00_u03b1_3774_, v_00_u03b2_3775_, v_inst_3776_, v_x_3777_, v_x_3778_);
lean_dec(v_x_3777_);
lean_dec_ref(v_inst_3776_);
return v_res_3779_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object* v_x_3780_, lean_object* v_x_3781_, lean_object* v_x_3782_){
_start:
{
if (lean_obj_tag(v_x_3780_) == 0)
{
lean_object* v_k_3783_; lean_object* v_v_3784_; lean_object* v_l_3785_; lean_object* v_r_3786_; lean_object* v___y_3788_; lean_object* v___y_3794_; 
v_k_3783_ = lean_ctor_get(v_x_3780_, 1);
v_v_3784_ = lean_ctor_get(v_x_3780_, 2);
v_l_3785_ = lean_ctor_get(v_x_3780_, 3);
v_r_3786_ = lean_ctor_get(v_x_3780_, 4);
if (lean_obj_tag(v_l_3785_) == 0)
{
lean_object* v_size_3801_; 
v_size_3801_ = lean_ctor_get(v_l_3785_, 0);
v___y_3794_ = v_size_3801_;
goto v___jp_3793_;
}
else
{
lean_object* v___x_3802_; 
v___x_3802_ = lean_unsigned_to_nat(0u);
v___y_3794_ = v___x_3802_;
goto v___jp_3793_;
}
v___jp_3787_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3789_ = lean_nat_sub(v_x_3781_, v___y_3788_);
lean_dec(v_x_3781_);
v___x_3790_ = lean_unsigned_to_nat(1u);
v___x_3791_ = lean_nat_sub(v___x_3789_, v___x_3790_);
lean_dec(v___x_3789_);
v_x_3780_ = v_r_3786_;
v_x_3781_ = v___x_3791_;
goto _start;
}
v___jp_3793_:
{
uint8_t v___x_3795_; 
v___x_3795_ = lean_nat_dec_lt(v_x_3781_, v___y_3794_);
if (v___x_3795_ == 0)
{
uint8_t v___x_3796_; 
v___x_3796_ = lean_nat_dec_eq(v_x_3781_, v___y_3794_);
if (v___x_3796_ == 0)
{
if (lean_obj_tag(v_l_3785_) == 0)
{
lean_object* v_size_3797_; 
v_size_3797_ = lean_ctor_get(v_l_3785_, 0);
v___y_3788_ = v_size_3797_;
goto v___jp_3787_;
}
else
{
lean_object* v___x_3798_; 
v___x_3798_ = lean_unsigned_to_nat(0u);
v___y_3788_ = v___x_3798_;
goto v___jp_3787_;
}
}
else
{
lean_object* v___x_3799_; 
lean_dec(v_x_3781_);
lean_inc(v_v_3784_);
lean_inc(v_k_3783_);
v___x_3799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3799_, 0, v_k_3783_);
lean_ctor_set(v___x_3799_, 1, v_v_3784_);
return v___x_3799_;
}
}
else
{
v_x_3780_ = v_l_3785_;
goto _start;
}
}
}
else
{
lean_dec(v_x_3781_);
lean_inc_ref(v_x_3782_);
return v_x_3782_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg___boxed(lean_object* v_x_3803_, lean_object* v_x_3804_, lean_object* v_x_3805_){
_start:
{
lean_object* v_res_3806_; 
v_res_3806_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3803_, v_x_3804_, v_x_3805_);
lean_dec_ref(v_x_3805_);
lean_dec(v_x_3803_);
return v_res_3806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(lean_object* v_00_u03b1_3807_, lean_object* v_00_u03b2_3808_, lean_object* v_x_3809_, lean_object* v_x_3810_, lean_object* v_x_3811_){
_start:
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3809_, v_x_3810_, v_x_3811_);
return v___x_3812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_3813_, lean_object* v_00_u03b2_3814_, lean_object* v_x_3815_, lean_object* v_x_3816_, lean_object* v_x_3817_){
_start:
{
lean_object* v_res_3818_; 
v_res_3818_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(v_00_u03b1_3813_, v_00_u03b2_3814_, v_x_3815_, v_x_3816_, v_x_3817_);
lean_dec_ref(v_x_3817_);
lean_dec(v_x_3815_);
return v_res_3818_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object* v_inst_3819_, lean_object* v_k_3820_, lean_object* v_best_3821_, lean_object* v_a_3822_){
_start:
{
if (lean_obj_tag(v_a_3822_) == 0)
{
lean_object* v_k_3823_; lean_object* v_v_3824_; lean_object* v_l_3825_; lean_object* v_r_3826_; lean_object* v___x_3827_; uint8_t v___x_3828_; 
v_k_3823_ = lean_ctor_get(v_a_3822_, 1);
lean_inc_n(v_k_3823_, 2);
v_v_3824_ = lean_ctor_get(v_a_3822_, 2);
lean_inc(v_v_3824_);
v_l_3825_ = lean_ctor_get(v_a_3822_, 3);
lean_inc(v_l_3825_);
v_r_3826_ = lean_ctor_get(v_a_3822_, 4);
lean_inc(v_r_3826_);
lean_dec_ref(v_a_3822_);
lean_inc_ref(v_inst_3819_);
lean_inc(v_k_3820_);
v___x_3827_ = lean_apply_2(v_inst_3819_, v_k_3820_, v_k_3823_);
v___x_3828_ = lean_unbox(v___x_3827_);
switch(v___x_3828_)
{
case 0:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_dec(v_r_3826_);
lean_dec(v_best_3821_);
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v_k_3823_);
lean_ctor_set(v___x_3829_, 1, v_v_3824_);
v___x_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
v_best_3821_ = v___x_3830_;
v_a_3822_ = v_l_3825_;
goto _start;
}
case 1:
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
lean_dec(v_r_3826_);
lean_dec(v_l_3825_);
lean_dec(v_best_3821_);
lean_dec(v_k_3820_);
lean_dec_ref(v_inst_3819_);
v___x_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3832_, 0, v_k_3823_);
lean_ctor_set(v___x_3832_, 1, v_v_3824_);
v___x_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
return v___x_3833_;
}
default: 
{
lean_dec(v_l_3825_);
lean_dec(v_v_3824_);
lean_dec(v_k_3823_);
v_a_3822_ = v_r_3826_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3820_);
lean_dec_ref(v_inst_3819_);
return v_best_3821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(lean_object* v_00_u03b1_3835_, lean_object* v_00_u03b2_3836_, lean_object* v_inst_3837_, lean_object* v_k_3838_, lean_object* v_best_3839_, lean_object* v_a_3840_){
_start:
{
lean_object* v___x_3841_; 
v___x_3841_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3837_, v_k_3838_, v_best_3839_, v_a_3840_);
return v___x_3841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___redArg(lean_object* v_inst_3842_, lean_object* v_k_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
v___x_3845_ = lean_box(0);
v___x_3846_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3842_, v_k_3843_, v___x_3845_, v_a_3844_);
return v___x_3846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(lean_object* v_00_u03b1_3847_, lean_object* v_00_u03b2_3848_, lean_object* v_inst_3849_, lean_object* v_k_3850_, lean_object* v_a_3851_){
_start:
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_box(0);
v___x_3853_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3849_, v_k_3850_, v___x_3852_, v_a_3851_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object* v_inst_3854_, lean_object* v_k_3855_, lean_object* v_best_3856_, lean_object* v_a_3857_){
_start:
{
if (lean_obj_tag(v_a_3857_) == 0)
{
lean_object* v_k_3858_; lean_object* v_v_3859_; lean_object* v_l_3860_; lean_object* v_r_3861_; lean_object* v___x_3862_; uint8_t v___x_3863_; 
v_k_3858_ = lean_ctor_get(v_a_3857_, 1);
lean_inc_n(v_k_3858_, 2);
v_v_3859_ = lean_ctor_get(v_a_3857_, 2);
lean_inc(v_v_3859_);
v_l_3860_ = lean_ctor_get(v_a_3857_, 3);
lean_inc(v_l_3860_);
v_r_3861_ = lean_ctor_get(v_a_3857_, 4);
lean_inc(v_r_3861_);
lean_dec_ref(v_a_3857_);
lean_inc_ref(v_inst_3854_);
lean_inc(v_k_3855_);
v___x_3862_ = lean_apply_2(v_inst_3854_, v_k_3855_, v_k_3858_);
v___x_3863_ = lean_unbox(v___x_3862_);
if (v___x_3863_ == 0)
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
lean_dec(v_r_3861_);
lean_dec(v_best_3856_);
v___x_3864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3864_, 0, v_k_3858_);
lean_ctor_set(v___x_3864_, 1, v_v_3859_);
v___x_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
v_best_3856_ = v___x_3865_;
v_a_3857_ = v_l_3860_;
goto _start;
}
else
{
lean_dec(v_l_3860_);
lean_dec(v_v_3859_);
lean_dec(v_k_3858_);
v_a_3857_ = v_r_3861_;
goto _start;
}
}
else
{
lean_dec(v_k_3855_);
lean_dec_ref(v_inst_3854_);
return v_best_3856_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(lean_object* v_00_u03b1_3868_, lean_object* v_00_u03b2_3869_, lean_object* v_inst_3870_, lean_object* v_k_3871_, lean_object* v_best_3872_, lean_object* v_a_3873_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3870_, v_k_3871_, v_best_3872_, v_a_3873_);
return v___x_3874_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___redArg(lean_object* v_inst_3875_, lean_object* v_k_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = lean_box(0);
v___x_3879_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3875_, v_k_3876_, v___x_3878_, v_a_3877_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(lean_object* v_00_u03b1_3880_, lean_object* v_00_u03b2_3881_, lean_object* v_inst_3882_, lean_object* v_k_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v___x_3885_; lean_object* v___x_3886_; 
v___x_3885_ = lean_box(0);
v___x_3886_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3882_, v_k_3883_, v___x_3885_, v_a_3884_);
return v___x_3886_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object* v_inst_3887_, lean_object* v_k_3888_, lean_object* v_best_3889_, lean_object* v_a_3890_){
_start:
{
if (lean_obj_tag(v_a_3890_) == 0)
{
lean_object* v_k_3891_; lean_object* v_v_3892_; lean_object* v_l_3893_; lean_object* v_r_3894_; lean_object* v___x_3895_; uint8_t v___x_3896_; 
v_k_3891_ = lean_ctor_get(v_a_3890_, 1);
lean_inc_n(v_k_3891_, 2);
v_v_3892_ = lean_ctor_get(v_a_3890_, 2);
lean_inc(v_v_3892_);
v_l_3893_ = lean_ctor_get(v_a_3890_, 3);
lean_inc(v_l_3893_);
v_r_3894_ = lean_ctor_get(v_a_3890_, 4);
lean_inc(v_r_3894_);
lean_dec_ref(v_a_3890_);
lean_inc_ref(v_inst_3887_);
lean_inc(v_k_3888_);
v___x_3895_ = lean_apply_2(v_inst_3887_, v_k_3888_, v_k_3891_);
v___x_3896_ = lean_unbox(v___x_3895_);
switch(v___x_3896_)
{
case 0:
{
lean_dec(v_r_3894_);
lean_dec(v_v_3892_);
lean_dec(v_k_3891_);
v_a_3890_ = v_l_3893_;
goto _start;
}
case 1:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
lean_dec(v_r_3894_);
lean_dec(v_l_3893_);
lean_dec(v_best_3889_);
lean_dec(v_k_3888_);
lean_dec_ref(v_inst_3887_);
v___x_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3898_, 0, v_k_3891_);
lean_ctor_set(v___x_3898_, 1, v_v_3892_);
v___x_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
return v___x_3899_;
}
default: 
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
lean_dec(v_l_3893_);
lean_dec(v_best_3889_);
v___x_3900_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3900_, 0, v_k_3891_);
lean_ctor_set(v___x_3900_, 1, v_v_3892_);
v___x_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
v_best_3889_ = v___x_3901_;
v_a_3890_ = v_r_3894_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3888_);
lean_dec_ref(v_inst_3887_);
return v_best_3889_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(lean_object* v_00_u03b1_3903_, lean_object* v_00_u03b2_3904_, lean_object* v_inst_3905_, lean_object* v_k_3906_, lean_object* v_best_3907_, lean_object* v_a_3908_){
_start:
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3905_, v_k_3906_, v_best_3907_, v_a_3908_);
return v___x_3909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___redArg(lean_object* v_inst_3910_, lean_object* v_k_3911_, lean_object* v_a_3912_){
_start:
{
lean_object* v___x_3913_; lean_object* v___x_3914_; 
v___x_3913_ = lean_box(0);
v___x_3914_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3910_, v_k_3911_, v___x_3913_, v_a_3912_);
return v___x_3914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(lean_object* v_00_u03b1_3915_, lean_object* v_00_u03b2_3916_, lean_object* v_inst_3917_, lean_object* v_k_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = lean_box(0);
v___x_3921_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3917_, v_k_3918_, v___x_3920_, v_a_3919_);
return v___x_3921_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object* v_inst_3922_, lean_object* v_k_3923_, lean_object* v_best_3924_, lean_object* v_a_3925_){
_start:
{
if (lean_obj_tag(v_a_3925_) == 0)
{
lean_object* v_k_3926_; lean_object* v_v_3927_; lean_object* v_l_3928_; lean_object* v_r_3929_; lean_object* v___x_3930_; uint8_t v___x_3931_; 
v_k_3926_ = lean_ctor_get(v_a_3925_, 1);
lean_inc_n(v_k_3926_, 2);
v_v_3927_ = lean_ctor_get(v_a_3925_, 2);
lean_inc(v_v_3927_);
v_l_3928_ = lean_ctor_get(v_a_3925_, 3);
lean_inc(v_l_3928_);
v_r_3929_ = lean_ctor_get(v_a_3925_, 4);
lean_inc(v_r_3929_);
lean_dec_ref(v_a_3925_);
lean_inc_ref(v_inst_3922_);
lean_inc(v_k_3923_);
v___x_3930_ = lean_apply_2(v_inst_3922_, v_k_3923_, v_k_3926_);
v___x_3931_ = lean_unbox(v___x_3930_);
if (v___x_3931_ == 2)
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
lean_dec(v_l_3928_);
lean_dec(v_best_3924_);
v___x_3932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3932_, 0, v_k_3926_);
lean_ctor_set(v___x_3932_, 1, v_v_3927_);
v___x_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
v_best_3924_ = v___x_3933_;
v_a_3925_ = v_r_3929_;
goto _start;
}
else
{
lean_dec(v_r_3929_);
lean_dec(v_v_3927_);
lean_dec(v_k_3926_);
v_a_3925_ = v_l_3928_;
goto _start;
}
}
else
{
lean_dec(v_k_3923_);
lean_dec_ref(v_inst_3922_);
return v_best_3924_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(lean_object* v_00_u03b1_3936_, lean_object* v_00_u03b2_3937_, lean_object* v_inst_3938_, lean_object* v_k_3939_, lean_object* v_best_3940_, lean_object* v_a_3941_){
_start:
{
lean_object* v___x_3942_; 
v___x_3942_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3938_, v_k_3939_, v_best_3940_, v_a_3941_);
return v___x_3942_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___redArg(lean_object* v_inst_3943_, lean_object* v_k_3944_, lean_object* v_a_3945_){
_start:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3946_ = lean_box(0);
v___x_3947_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3943_, v_k_3944_, v___x_3946_, v_a_3945_);
return v___x_3947_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(lean_object* v_00_u03b1_3948_, lean_object* v_00_u03b2_3949_, lean_object* v_inst_3950_, lean_object* v_k_3951_, lean_object* v_a_3952_){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = lean_box(0);
v___x_3954_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3950_, v_k_3951_, v___x_3953_, v_a_3952_);
return v___x_3954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(lean_object* v_inst_3955_, lean_object* v_inst_3956_, lean_object* v_k_3957_, lean_object* v_t_3958_){
_start:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3959_ = lean_box(0);
v___x_3960_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3955_, v_k_3957_, v___x_3959_, v_t_3958_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3962_ = l_panic___redArg(v_inst_3956_, v___x_3961_);
return v___x_3962_;
}
else
{
lean_object* v_val_3963_; 
v_val_3963_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_val_3963_);
lean_dec_ref(v___x_3960_);
return v_val_3963_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg___boxed(lean_object* v_inst_3964_, lean_object* v_inst_3965_, lean_object* v_k_3966_, lean_object* v_t_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(v_inst_3964_, v_inst_3965_, v_k_3966_, v_t_3967_);
lean_dec_ref(v_inst_3965_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object* v_00_u03b1_3969_, lean_object* v_00_u03b2_3970_, lean_object* v_inst_3971_, lean_object* v_inst_3972_, lean_object* v_k_3973_, lean_object* v_t_3974_){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; 
v___x_3975_ = lean_box(0);
v___x_3976_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3971_, v_k_3973_, v___x_3975_, v_t_3974_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3978_ = l_panic___redArg(v_inst_3972_, v___x_3977_);
return v___x_3978_;
}
else
{
lean_object* v_val_3979_; 
v_val_3979_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_val_3979_);
lean_dec_ref(v___x_3976_);
return v_val_3979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_3980_, lean_object* v_00_u03b2_3981_, lean_object* v_inst_3982_, lean_object* v_inst_3983_, lean_object* v_k_3984_, lean_object* v_t_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(v_00_u03b1_3980_, v_00_u03b2_3981_, v_inst_3982_, v_inst_3983_, v_k_3984_, v_t_3985_);
lean_dec_ref(v_inst_3983_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(lean_object* v_inst_3987_, lean_object* v_inst_3988_, lean_object* v_k_3989_, lean_object* v_t_3990_){
_start:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3991_ = lean_box(0);
v___x_3992_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3987_, v_k_3989_, v___x_3991_, v_t_3990_);
if (lean_obj_tag(v___x_3992_) == 0)
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3993_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3994_ = l_panic___redArg(v_inst_3988_, v___x_3993_);
return v___x_3994_;
}
else
{
lean_object* v_val_3995_; 
v_val_3995_ = lean_ctor_get(v___x_3992_, 0);
lean_inc(v_val_3995_);
lean_dec_ref(v___x_3992_);
return v_val_3995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg___boxed(lean_object* v_inst_3996_, lean_object* v_inst_3997_, lean_object* v_k_3998_, lean_object* v_t_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(v_inst_3996_, v_inst_3997_, v_k_3998_, v_t_3999_);
lean_dec_ref(v_inst_3997_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object* v_00_u03b1_4001_, lean_object* v_00_u03b2_4002_, lean_object* v_inst_4003_, lean_object* v_inst_4004_, lean_object* v_k_4005_, lean_object* v_t_4006_){
_start:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4007_ = lean_box(0);
v___x_4008_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4003_, v_k_4005_, v___x_4007_, v_t_4006_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v___x_4009_; lean_object* v___x_4010_; 
v___x_4009_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4010_ = l_panic___redArg(v_inst_4004_, v___x_4009_);
return v___x_4010_;
}
else
{
lean_object* v_val_4011_; 
v_val_4011_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_val_4011_);
lean_dec_ref(v___x_4008_);
return v_val_4011_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_4012_, lean_object* v_00_u03b2_4013_, lean_object* v_inst_4014_, lean_object* v_inst_4015_, lean_object* v_k_4016_, lean_object* v_t_4017_){
_start:
{
lean_object* v_res_4018_; 
v_res_4018_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(v_00_u03b1_4012_, v_00_u03b2_4013_, v_inst_4014_, v_inst_4015_, v_k_4016_, v_t_4017_);
lean_dec_ref(v_inst_4015_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(lean_object* v_inst_4019_, lean_object* v_inst_4020_, lean_object* v_k_4021_, lean_object* v_t_4022_){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4023_ = lean_box(0);
v___x_4024_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4019_, v_k_4021_, v___x_4023_, v_t_4022_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4026_ = l_panic___redArg(v_inst_4020_, v___x_4025_);
return v___x_4026_;
}
else
{
lean_object* v_val_4027_; 
v_val_4027_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_val_4027_);
lean_dec_ref(v___x_4024_);
return v_val_4027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg___boxed(lean_object* v_inst_4028_, lean_object* v_inst_4029_, lean_object* v_k_4030_, lean_object* v_t_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(v_inst_4028_, v_inst_4029_, v_k_4030_, v_t_4031_);
lean_dec_ref(v_inst_4029_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object* v_00_u03b1_4033_, lean_object* v_00_u03b2_4034_, lean_object* v_inst_4035_, lean_object* v_inst_4036_, lean_object* v_k_4037_, lean_object* v_t_4038_){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; 
v___x_4039_ = lean_box(0);
v___x_4040_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4035_, v_k_4037_, v___x_4039_, v_t_4038_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v___x_4041_; lean_object* v___x_4042_; 
v___x_4041_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4042_ = l_panic___redArg(v_inst_4036_, v___x_4041_);
return v___x_4042_;
}
else
{
lean_object* v_val_4043_; 
v_val_4043_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_val_4043_);
lean_dec_ref(v___x_4040_);
return v_val_4043_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_4044_, lean_object* v_00_u03b2_4045_, lean_object* v_inst_4046_, lean_object* v_inst_4047_, lean_object* v_k_4048_, lean_object* v_t_4049_){
_start:
{
lean_object* v_res_4050_; 
v_res_4050_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(v_00_u03b1_4044_, v_00_u03b2_4045_, v_inst_4046_, v_inst_4047_, v_k_4048_, v_t_4049_);
lean_dec_ref(v_inst_4047_);
return v_res_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(lean_object* v_inst_4051_, lean_object* v_inst_4052_, lean_object* v_k_4053_, lean_object* v_t_4054_){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = lean_box(0);
v___x_4056_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4051_, v_k_4053_, v___x_4055_, v_t_4054_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4057_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4058_ = l_panic___redArg(v_inst_4052_, v___x_4057_);
return v___x_4058_;
}
else
{
lean_object* v_val_4059_; 
v_val_4059_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_val_4059_);
lean_dec_ref(v___x_4056_);
return v_val_4059_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg___boxed(lean_object* v_inst_4060_, lean_object* v_inst_4061_, lean_object* v_k_4062_, lean_object* v_t_4063_){
_start:
{
lean_object* v_res_4064_; 
v_res_4064_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(v_inst_4060_, v_inst_4061_, v_k_4062_, v_t_4063_);
lean_dec_ref(v_inst_4061_);
return v_res_4064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object* v_00_u03b1_4065_, lean_object* v_00_u03b2_4066_, lean_object* v_inst_4067_, lean_object* v_inst_4068_, lean_object* v_k_4069_, lean_object* v_t_4070_){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = lean_box(0);
v___x_4072_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4067_, v_k_4069_, v___x_4071_, v_t_4070_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4074_ = l_panic___redArg(v_inst_4068_, v___x_4073_);
return v___x_4074_;
}
else
{
lean_object* v_val_4075_; 
v_val_4075_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_val_4075_);
lean_dec_ref(v___x_4072_);
return v_val_4075_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_4076_, lean_object* v_00_u03b2_4077_, lean_object* v_inst_4078_, lean_object* v_inst_4079_, lean_object* v_k_4080_, lean_object* v_t_4081_){
_start:
{
lean_object* v_res_4082_; 
v_res_4082_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(v_00_u03b1_4076_, v_00_u03b2_4077_, v_inst_4078_, v_inst_4079_, v_k_4080_, v_t_4081_);
lean_dec_ref(v_inst_4079_);
return v_res_4082_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(lean_object* v_inst_4083_, lean_object* v_k_4084_, lean_object* v_t_4085_, lean_object* v_fallback_4086_){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = lean_box(0);
v___x_4088_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4083_, v_k_4084_, v___x_4087_, v_t_4085_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_inc_ref(v_fallback_4086_);
return v_fallback_4086_;
}
else
{
lean_object* v_val_4089_; 
v_val_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_val_4089_);
lean_dec_ref(v___x_4088_);
return v_val_4089_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg___boxed(lean_object* v_inst_4090_, lean_object* v_k_4091_, lean_object* v_t_4092_, lean_object* v_fallback_4093_){
_start:
{
lean_object* v_res_4094_; 
v_res_4094_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(v_inst_4090_, v_k_4091_, v_t_4092_, v_fallback_4093_);
lean_dec_ref(v_fallback_4093_);
return v_res_4094_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(lean_object* v_00_u03b1_4095_, lean_object* v_00_u03b2_4096_, lean_object* v_inst_4097_, lean_object* v_k_4098_, lean_object* v_t_4099_, lean_object* v_fallback_4100_){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
v___x_4101_ = lean_box(0);
v___x_4102_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4097_, v_k_4098_, v___x_4101_, v_t_4099_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_inc_ref(v_fallback_4100_);
return v_fallback_4100_;
}
else
{
lean_object* v_val_4103_; 
v_val_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_val_4103_);
lean_dec_ref(v___x_4102_);
return v_val_4103_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___boxed(lean_object* v_00_u03b1_4104_, lean_object* v_00_u03b2_4105_, lean_object* v_inst_4106_, lean_object* v_k_4107_, lean_object* v_t_4108_, lean_object* v_fallback_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(v_00_u03b1_4104_, v_00_u03b2_4105_, v_inst_4106_, v_k_4107_, v_t_4108_, v_fallback_4109_);
lean_dec_ref(v_fallback_4109_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(lean_object* v_inst_4111_, lean_object* v_k_4112_, lean_object* v_t_4113_, lean_object* v_fallback_4114_){
_start:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4115_ = lean_box(0);
v___x_4116_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4111_, v_k_4112_, v___x_4115_, v_t_4113_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_inc_ref(v_fallback_4114_);
return v_fallback_4114_;
}
else
{
lean_object* v_val_4117_; 
v_val_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_val_4117_);
lean_dec_ref(v___x_4116_);
return v_val_4117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg___boxed(lean_object* v_inst_4118_, lean_object* v_k_4119_, lean_object* v_t_4120_, lean_object* v_fallback_4121_){
_start:
{
lean_object* v_res_4122_; 
v_res_4122_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(v_inst_4118_, v_k_4119_, v_t_4120_, v_fallback_4121_);
lean_dec_ref(v_fallback_4121_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(lean_object* v_00_u03b1_4123_, lean_object* v_00_u03b2_4124_, lean_object* v_inst_4125_, lean_object* v_k_4126_, lean_object* v_t_4127_, lean_object* v_fallback_4128_){
_start:
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4129_ = lean_box(0);
v___x_4130_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4125_, v_k_4126_, v___x_4129_, v_t_4127_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_inc_ref(v_fallback_4128_);
return v_fallback_4128_;
}
else
{
lean_object* v_val_4131_; 
v_val_4131_ = lean_ctor_get(v___x_4130_, 0);
lean_inc(v_val_4131_);
lean_dec_ref(v___x_4130_);
return v_val_4131_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_4132_, lean_object* v_00_u03b2_4133_, lean_object* v_inst_4134_, lean_object* v_k_4135_, lean_object* v_t_4136_, lean_object* v_fallback_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(v_00_u03b1_4132_, v_00_u03b2_4133_, v_inst_4134_, v_k_4135_, v_t_4136_, v_fallback_4137_);
lean_dec_ref(v_fallback_4137_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(lean_object* v_inst_4139_, lean_object* v_k_4140_, lean_object* v_t_4141_, lean_object* v_fallback_4142_){
_start:
{
lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4143_ = lean_box(0);
v___x_4144_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4139_, v_k_4140_, v___x_4143_, v_t_4141_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_inc_ref(v_fallback_4142_);
return v_fallback_4142_;
}
else
{
lean_object* v_val_4145_; 
v_val_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_val_4145_);
lean_dec_ref(v___x_4144_);
return v_val_4145_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg___boxed(lean_object* v_inst_4146_, lean_object* v_k_4147_, lean_object* v_t_4148_, lean_object* v_fallback_4149_){
_start:
{
lean_object* v_res_4150_; 
v_res_4150_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(v_inst_4146_, v_k_4147_, v_t_4148_, v_fallback_4149_);
lean_dec_ref(v_fallback_4149_);
return v_res_4150_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(lean_object* v_00_u03b1_4151_, lean_object* v_00_u03b2_4152_, lean_object* v_inst_4153_, lean_object* v_k_4154_, lean_object* v_t_4155_, lean_object* v_fallback_4156_){
_start:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4157_ = lean_box(0);
v___x_4158_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4153_, v_k_4154_, v___x_4157_, v_t_4155_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_inc_ref(v_fallback_4156_);
return v_fallback_4156_;
}
else
{
lean_object* v_val_4159_; 
v_val_4159_ = lean_ctor_get(v___x_4158_, 0);
lean_inc(v_val_4159_);
lean_dec_ref(v___x_4158_);
return v_val_4159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___boxed(lean_object* v_00_u03b1_4160_, lean_object* v_00_u03b2_4161_, lean_object* v_inst_4162_, lean_object* v_k_4163_, lean_object* v_t_4164_, lean_object* v_fallback_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(v_00_u03b1_4160_, v_00_u03b2_4161_, v_inst_4162_, v_k_4163_, v_t_4164_, v_fallback_4165_);
lean_dec_ref(v_fallback_4165_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(lean_object* v_inst_4167_, lean_object* v_k_4168_, lean_object* v_t_4169_, lean_object* v_fallback_4170_){
_start:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4171_ = lean_box(0);
v___x_4172_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4167_, v_k_4168_, v___x_4171_, v_t_4169_);
if (lean_obj_tag(v___x_4172_) == 0)
{
lean_inc_ref(v_fallback_4170_);
return v_fallback_4170_;
}
else
{
lean_object* v_val_4173_; 
v_val_4173_ = lean_ctor_get(v___x_4172_, 0);
lean_inc(v_val_4173_);
lean_dec_ref(v___x_4172_);
return v_val_4173_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg___boxed(lean_object* v_inst_4174_, lean_object* v_k_4175_, lean_object* v_t_4176_, lean_object* v_fallback_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(v_inst_4174_, v_k_4175_, v_t_4176_, v_fallback_4177_);
lean_dec_ref(v_fallback_4177_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(lean_object* v_00_u03b1_4179_, lean_object* v_00_u03b2_4180_, lean_object* v_inst_4181_, lean_object* v_k_4182_, lean_object* v_t_4183_, lean_object* v_fallback_4184_){
_start:
{
lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4185_ = lean_box(0);
v___x_4186_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4181_, v_k_4182_, v___x_4185_, v_t_4183_);
if (lean_obj_tag(v___x_4186_) == 0)
{
lean_inc_ref(v_fallback_4184_);
return v_fallback_4184_;
}
else
{
lean_object* v_val_4187_; 
v_val_4187_ = lean_ctor_get(v___x_4186_, 0);
lean_inc(v_val_4187_);
lean_dec_ref(v___x_4186_);
return v_val_4187_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_4188_, lean_object* v_00_u03b2_4189_, lean_object* v_inst_4190_, lean_object* v_k_4191_, lean_object* v_t_4192_, lean_object* v_fallback_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(v_00_u03b1_4188_, v_00_u03b2_4189_, v_inst_4190_, v_k_4191_, v_t_4192_, v_fallback_4193_);
lean_dec_ref(v_fallback_4193_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object* v_inst_4195_, lean_object* v_k_4196_, lean_object* v_x_4197_){
_start:
{
lean_object* v_k_4198_; lean_object* v_v_4199_; lean_object* v_l_4200_; lean_object* v_r_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; 
v_k_4198_ = lean_ctor_get(v_x_4197_, 1);
lean_inc_n(v_k_4198_, 2);
v_v_4199_ = lean_ctor_get(v_x_4197_, 2);
lean_inc(v_v_4199_);
v_l_4200_ = lean_ctor_get(v_x_4197_, 3);
lean_inc(v_l_4200_);
v_r_4201_ = lean_ctor_get(v_x_4197_, 4);
lean_inc(v_r_4201_);
lean_dec(v_x_4197_);
lean_inc_ref(v_inst_4195_);
lean_inc(v_k_4196_);
v___x_4202_ = lean_apply_2(v_inst_4195_, v_k_4196_, v_k_4198_);
v___x_4203_ = lean_unbox(v___x_4202_);
switch(v___x_4203_)
{
case 0:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_dec(v_r_4201_);
v___x_4204_ = lean_box(0);
v___x_4205_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4195_, v_k_4196_, v___x_4204_, v_l_4200_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v___x_4206_; 
v___x_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4206_, 0, v_k_4198_);
lean_ctor_set(v___x_4206_, 1, v_v_4199_);
return v___x_4206_;
}
else
{
lean_object* v_val_4207_; 
lean_dec(v_v_4199_);
lean_dec(v_k_4198_);
v_val_4207_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_val_4207_);
lean_dec_ref(v___x_4205_);
return v_val_4207_;
}
}
case 1:
{
lean_object* v___x_4208_; 
lean_dec(v_r_4201_);
lean_dec(v_l_4200_);
lean_dec(v_k_4196_);
lean_dec_ref(v_inst_4195_);
v___x_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4208_, 0, v_k_4198_);
lean_ctor_set(v___x_4208_, 1, v_v_4199_);
return v___x_4208_;
}
default: 
{
lean_dec(v_l_4200_);
lean_dec(v_v_4199_);
lean_dec(v_k_4198_);
v_x_4197_ = v_r_4201_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(lean_object* v_00_u03b1_4210_, lean_object* v_00_u03b2_4211_, lean_object* v_inst_4212_, lean_object* v_inst_4213_, lean_object* v_k_4214_, lean_object* v_x_4215_, lean_object* v_x_4216_, lean_object* v_x_4217_){
_start:
{
lean_object* v___x_4218_; 
v___x_4218_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_inst_4212_, v_k_4214_, v_x_4215_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object* v_inst_4219_, lean_object* v_k_4220_, lean_object* v_x_4221_){
_start:
{
lean_object* v_k_4222_; lean_object* v_v_4223_; lean_object* v_l_4224_; lean_object* v_r_4225_; lean_object* v___x_4226_; uint8_t v___x_4227_; uint8_t v___x_4228_; uint8_t v___x_4229_; 
v_k_4222_ = lean_ctor_get(v_x_4221_, 1);
lean_inc_n(v_k_4222_, 2);
v_v_4223_ = lean_ctor_get(v_x_4221_, 2);
lean_inc(v_v_4223_);
v_l_4224_ = lean_ctor_get(v_x_4221_, 3);
lean_inc(v_l_4224_);
v_r_4225_ = lean_ctor_get(v_x_4221_, 4);
lean_inc(v_r_4225_);
lean_dec(v_x_4221_);
lean_inc_ref(v_inst_4219_);
lean_inc(v_k_4220_);
v___x_4226_ = lean_apply_2(v_inst_4219_, v_k_4220_, v_k_4222_);
v___x_4227_ = 0;
v___x_4228_ = lean_unbox(v___x_4226_);
v___x_4229_ = l_instDecidableEqOrdering(v___x_4228_, v___x_4227_);
if (v___x_4229_ == 0)
{
lean_dec(v_l_4224_);
lean_dec(v_v_4223_);
lean_dec(v_k_4222_);
v_x_4221_ = v_r_4225_;
goto _start;
}
else
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
lean_dec(v_r_4225_);
v___x_4231_ = lean_box(0);
v___x_4232_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4219_, v_k_4220_, v___x_4231_, v_l_4224_);
if (lean_obj_tag(v___x_4232_) == 0)
{
lean_object* v___x_4233_; 
v___x_4233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4233_, 0, v_k_4222_);
lean_ctor_set(v___x_4233_, 1, v_v_4223_);
return v___x_4233_;
}
else
{
lean_object* v_val_4234_; 
lean_dec(v_v_4223_);
lean_dec(v_k_4222_);
v_val_4234_ = lean_ctor_get(v___x_4232_, 0);
lean_inc(v_val_4234_);
lean_dec_ref(v___x_4232_);
return v_val_4234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(lean_object* v_00_u03b1_4235_, lean_object* v_00_u03b2_4236_, lean_object* v_inst_4237_, lean_object* v_inst_4238_, lean_object* v_k_4239_, lean_object* v_x_4240_, lean_object* v_x_4241_, lean_object* v_x_4242_){
_start:
{
lean_object* v___x_4243_; 
v___x_4243_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_inst_4237_, v_k_4239_, v_x_4240_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object* v_inst_4244_, lean_object* v_k_4245_, lean_object* v_x_4246_){
_start:
{
lean_object* v_k_4247_; lean_object* v_v_4248_; lean_object* v_l_4249_; lean_object* v_r_4250_; lean_object* v___x_4251_; uint8_t v___x_4252_; 
v_k_4247_ = lean_ctor_get(v_x_4246_, 1);
lean_inc_n(v_k_4247_, 2);
v_v_4248_ = lean_ctor_get(v_x_4246_, 2);
lean_inc(v_v_4248_);
v_l_4249_ = lean_ctor_get(v_x_4246_, 3);
lean_inc(v_l_4249_);
v_r_4250_ = lean_ctor_get(v_x_4246_, 4);
lean_inc(v_r_4250_);
lean_dec(v_x_4246_);
lean_inc_ref(v_inst_4244_);
lean_inc(v_k_4245_);
v___x_4251_ = lean_apply_2(v_inst_4244_, v_k_4245_, v_k_4247_);
v___x_4252_ = lean_unbox(v___x_4251_);
switch(v___x_4252_)
{
case 0:
{
lean_dec(v_r_4250_);
lean_dec(v_v_4248_);
lean_dec(v_k_4247_);
v_x_4246_ = v_l_4249_;
goto _start;
}
case 1:
{
lean_object* v___x_4254_; 
lean_dec(v_r_4250_);
lean_dec(v_l_4249_);
lean_dec(v_k_4245_);
lean_dec_ref(v_inst_4244_);
v___x_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4254_, 0, v_k_4247_);
lean_ctor_set(v___x_4254_, 1, v_v_4248_);
return v___x_4254_;
}
default: 
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
lean_dec(v_l_4249_);
v___x_4255_ = lean_box(0);
v___x_4256_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4244_, v_k_4245_, v___x_4255_, v_r_4250_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v___x_4257_; 
v___x_4257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4257_, 0, v_k_4247_);
lean_ctor_set(v___x_4257_, 1, v_v_4248_);
return v___x_4257_;
}
else
{
lean_object* v_val_4258_; 
lean_dec(v_v_4248_);
lean_dec(v_k_4247_);
v_val_4258_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_val_4258_);
lean_dec_ref(v___x_4256_);
return v_val_4258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(lean_object* v_00_u03b1_4259_, lean_object* v_00_u03b2_4260_, lean_object* v_inst_4261_, lean_object* v_inst_4262_, lean_object* v_k_4263_, lean_object* v_x_4264_, lean_object* v_x_4265_, lean_object* v_x_4266_){
_start:
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_inst_4261_, v_k_4263_, v_x_4264_);
return v___x_4267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object* v_inst_4268_, lean_object* v_k_4269_, lean_object* v_x_4270_){
_start:
{
lean_object* v_k_4271_; lean_object* v_v_4272_; lean_object* v_l_4273_; lean_object* v_r_4274_; lean_object* v___x_4275_; uint8_t v___x_4276_; uint8_t v___x_4277_; uint8_t v___x_4278_; 
v_k_4271_ = lean_ctor_get(v_x_4270_, 1);
lean_inc_n(v_k_4271_, 2);
v_v_4272_ = lean_ctor_get(v_x_4270_, 2);
lean_inc(v_v_4272_);
v_l_4273_ = lean_ctor_get(v_x_4270_, 3);
lean_inc(v_l_4273_);
v_r_4274_ = lean_ctor_get(v_x_4270_, 4);
lean_inc(v_r_4274_);
lean_dec(v_x_4270_);
lean_inc_ref(v_inst_4268_);
lean_inc(v_k_4269_);
v___x_4275_ = lean_apply_2(v_inst_4268_, v_k_4269_, v_k_4271_);
v___x_4276_ = 2;
v___x_4277_ = lean_unbox(v___x_4275_);
v___x_4278_ = l_instDecidableEqOrdering(v___x_4277_, v___x_4276_);
if (v___x_4278_ == 0)
{
lean_dec(v_r_4274_);
lean_dec(v_v_4272_);
lean_dec(v_k_4271_);
v_x_4270_ = v_l_4273_;
goto _start;
}
else
{
lean_object* v___x_4280_; lean_object* v___x_4281_; 
lean_dec(v_l_4273_);
v___x_4280_ = lean_box(0);
v___x_4281_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4268_, v_k_4269_, v___x_4280_, v_r_4274_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v___x_4282_; 
v___x_4282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4282_, 0, v_k_4271_);
lean_ctor_set(v___x_4282_, 1, v_v_4272_);
return v___x_4282_;
}
else
{
lean_object* v_val_4283_; 
lean_dec(v_v_4272_);
lean_dec(v_k_4271_);
v_val_4283_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_val_4283_);
lean_dec_ref(v___x_4281_);
return v_val_4283_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(lean_object* v_00_u03b1_4284_, lean_object* v_00_u03b2_4285_, lean_object* v_inst_4286_, lean_object* v_inst_4287_, lean_object* v_k_4288_, lean_object* v_x_4289_, lean_object* v_x_4290_, lean_object* v_x_4291_){
_start:
{
lean_object* v___x_4292_; 
v___x_4292_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_inst_4286_, v_k_4288_, v_x_4289_);
return v___x_4292_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Compare(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Balanced(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Ordered(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Queries(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Balanced(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Ordered(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DTreeMap_Internal_Queries(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Compare(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Internal_Balanced(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Internal_Ordered(uint8_t builtin);
lean_object* initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DTreeMap_Internal_Queries(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Compare(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Balanced(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Internal_Ordered(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderPredicates(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DTreeMap_Internal_Queries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DTreeMap_Internal_Queries(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DTreeMap_Internal_Queries(builtin);
}
#ifdef __cplusplus
}
#endif
