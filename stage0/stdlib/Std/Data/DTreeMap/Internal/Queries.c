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
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqOrdering(uint8_t, uint8_t);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v_a_71_);
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
lean_inc(v_quotContext_77_);
v_currMacroScope_78_ = lean_ctor_get(v_a_71_, 2);
lean_inc(v_currMacroScope_78_);
v_ref_79_ = lean_ctor_get(v_a_71_, 5);
lean_inc(v_ref_79_);
lean_dec_ref(v_a_71_);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = l_Lean_Syntax_getArg(v_x_70_, v___x_80_);
v___x_82_ = lean_unsigned_to_nat(2u);
v___x_83_ = l_Lean_Syntax_getArg(v_x_70_, v___x_82_);
lean_dec(v_x_70_);
v___x_84_ = 0;
v___x_85_ = l_Lean_SourceInfo_fromRef(v_ref_79_, v___x_84_);
lean_dec(v_ref_79_);
v___x_86_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4));
v___x_87_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6);
v___x_88_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7));
v___x_89_ = l_Lean_addMacroScope(v_quotContext_77_, v___x_88_, v_currMacroScope_78_);
v___x_90_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12));
lean_inc(v___x_85_);
v___x_91_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_91_, 0, v___x_85_);
lean_ctor_set(v___x_91_, 1, v___x_87_);
lean_ctor_set(v___x_91_, 2, v___x_89_);
lean_ctor_set(v___x_91_, 3, v___x_90_);
v___x_92_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14));
lean_inc(v___x_85_);
v___x_93_ = l_Lean_Syntax_node2(v___x_85_, v___x_92_, v___x_81_, v___x_83_);
v___x_94_ = l_Lean_Syntax_node2(v___x_85_, v___x_86_, v___x_91_, v___x_93_);
v___x_95_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set(v___x_95_, 1, v_a_72_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(lean_object* v_x_99_, lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_102_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4));
lean_inc(v_x_99_);
v___x_103_ = l_Lean_Syntax_isOfKind(v_x_99_, v___x_102_);
if (v___x_103_ == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; 
lean_dec(v_x_99_);
v___x_104_ = lean_box(0);
v___x_105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_104_);
lean_ctor_set(v___x_105_, 1, v_a_101_);
return v___x_105_;
}
else
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = l_Lean_Syntax_getArg(v_x_99_, v___x_106_);
v___x_108_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1));
lean_inc(v___x_107_);
v___x_109_ = l_Lean_Syntax_isOfKind(v___x_107_, v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; 
lean_dec(v___x_107_);
lean_dec(v_x_99_);
v___x_110_ = lean_box(0);
v___x_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_110_);
lean_ctor_set(v___x_111_, 1, v_a_101_);
return v___x_111_;
}
else
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = l_Lean_Syntax_getArg(v_x_99_, v___x_112_);
lean_dec(v_x_99_);
v___x_114_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_113_);
v___x_115_ = l_Lean_Syntax_matchesNull(v___x_113_, v___x_114_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_dec(v___x_113_);
lean_dec(v___x_107_);
v___x_116_ = lean_box(0);
v___x_117_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v_a_101_);
return v___x_117_;
}
else
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v_ref_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_118_ = l_Lean_Syntax_getArg(v___x_113_, v___x_106_);
v___x_119_ = l_Lean_Syntax_getArg(v___x_113_, v___x_112_);
lean_dec(v___x_113_);
v_ref_120_ = l_Lean_replaceRef(v___x_107_, v_a_100_);
lean_dec(v___x_107_);
v___x_121_ = 0;
v___x_122_ = l_Lean_SourceInfo_fromRef(v_ref_120_, v___x_121_);
lean_dec(v_ref_120_);
v___x_123_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5));
v___x_124_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8));
lean_inc(v___x_122_);
v___x_125_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_122_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
v___x_126_ = l_Lean_Syntax_node3(v___x_122_, v___x_123_, v___x_118_, v___x_125_, v___x_119_);
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v_a_101_);
return v___x_127_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___boxed(lean_object* v_x_128_, lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(v_x_128_, v_a_129_, v_a_130_);
lean_dec(v_a_129_);
return v_res_131_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object* v_inst_132_, lean_object* v_k_133_, lean_object* v_t_134_){
_start:
{
if (lean_obj_tag(v_t_134_) == 0)
{
lean_object* v_k_135_; lean_object* v_l_136_; lean_object* v_r_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v_k_135_ = lean_ctor_get(v_t_134_, 1);
lean_inc(v_k_135_);
v_l_136_ = lean_ctor_get(v_t_134_, 3);
lean_inc(v_l_136_);
v_r_137_ = lean_ctor_get(v_t_134_, 4);
lean_inc(v_r_137_);
lean_dec_ref(v_t_134_);
lean_inc_ref(v_inst_132_);
lean_inc(v_k_133_);
v___x_138_ = lean_apply_2(v_inst_132_, v_k_133_, v_k_135_);
v___x_139_ = lean_unbox(v___x_138_);
switch(v___x_139_)
{
case 0:
{
lean_dec(v_r_137_);
v_t_134_ = v_l_136_;
goto _start;
}
case 1:
{
uint8_t v___x_141_; 
lean_dec(v_r_137_);
lean_dec(v_l_136_);
lean_dec(v_k_133_);
lean_dec_ref(v_inst_132_);
v___x_141_ = 1;
return v___x_141_;
}
default: 
{
lean_dec(v_l_136_);
v_t_134_ = v_r_137_;
goto _start;
}
}
}
else
{
uint8_t v___x_143_; 
lean_dec(v_k_133_);
lean_dec_ref(v_inst_132_);
v___x_143_ = 0;
return v___x_143_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___redArg___boxed(lean_object* v_inst_144_, lean_object* v_k_145_, lean_object* v_t_146_){
_start:
{
uint8_t v_res_147_; lean_object* v_r_148_; 
v_res_147_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_144_, v_k_145_, v_t_146_);
v_r_148_ = lean_box(v_res_147_);
return v_r_148_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains(lean_object* v_00_u03b1_149_, lean_object* v_00_u03b2_150_, lean_object* v_inst_151_, lean_object* v_k_152_, lean_object* v_t_153_){
_start:
{
uint8_t v___x_154_; 
v___x_154_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_151_, v_k_152_, v_t_153_);
return v___x_154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___boxed(lean_object* v_00_u03b1_155_, lean_object* v_00_u03b2_156_, lean_object* v_inst_157_, lean_object* v_k_158_, lean_object* v_t_159_){
_start:
{
uint8_t v_res_160_; lean_object* v_r_161_; 
v_res_160_ = l_Std_DTreeMap_Internal_Impl_contains(v_00_u03b1_155_, v_00_u03b2_156_, v_inst_157_, v_k_158_, v_t_159_);
v_r_161_ = lean_box(v_res_160_);
return v_r_161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(lean_object* v_00_u03b1_162_, lean_object* v_00_u03b2_163_, lean_object* v_inst_164_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = lean_box(0);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___boxed(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_inst_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(v_00_u03b1_166_, v_00_u03b2_167_, v_inst_168_);
lean_dec_ref(v_inst_168_);
return v_res_169_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(lean_object* v_inst_170_, lean_object* v_m_171_, lean_object* v_a_172_){
_start:
{
uint8_t v___x_173_; 
v___x_173_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_170_, v_a_172_, v_m_171_);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg___boxed(lean_object* v_inst_174_, lean_object* v_m_175_, lean_object* v_a_176_){
_start:
{
uint8_t v_res_177_; lean_object* v_r_178_; 
v_res_177_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(v_inst_174_, v_m_175_, v_a_176_);
v_r_178_ = lean_box(v_res_177_);
return v_r_178_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_inst_181_, lean_object* v_m_182_, lean_object* v_a_183_){
_start:
{
uint8_t v___x_184_; 
v___x_184_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_181_, v_a_183_, v_m_182_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___boxed(lean_object* v_00_u03b1_185_, lean_object* v_00_u03b2_186_, lean_object* v_inst_187_, lean_object* v_m_188_, lean_object* v_a_189_){
_start:
{
uint8_t v_res_190_; lean_object* v_r_191_; 
v_res_190_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem(v_00_u03b1_185_, v_00_u03b2_186_, v_inst_187_, v_m_188_, v_a_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_192_, lean_object* v_h__1_193_, lean_object* v_h__2_194_){
_start:
{
if (lean_obj_tag(v_t_192_) == 0)
{
lean_object* v_size_195_; lean_object* v_k_196_; lean_object* v_v_197_; lean_object* v_l_198_; lean_object* v_r_199_; lean_object* v___x_200_; 
lean_dec(v_h__1_193_);
v_size_195_ = lean_ctor_get(v_t_192_, 0);
lean_inc(v_size_195_);
v_k_196_ = lean_ctor_get(v_t_192_, 1);
lean_inc(v_k_196_);
v_v_197_ = lean_ctor_get(v_t_192_, 2);
lean_inc(v_v_197_);
v_l_198_ = lean_ctor_get(v_t_192_, 3);
lean_inc(v_l_198_);
v_r_199_ = lean_ctor_get(v_t_192_, 4);
lean_inc(v_r_199_);
lean_dec_ref(v_t_192_);
v___x_200_ = lean_apply_5(v_h__2_194_, v_size_195_, v_k_196_, v_v_197_, v_l_198_, v_r_199_);
return v___x_200_;
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v_h__2_194_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_apply_1(v_h__1_193_, v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_motive_205_, lean_object* v_t_206_, lean_object* v_h__1_207_, lean_object* v_h__2_208_){
_start:
{
if (lean_obj_tag(v_t_206_) == 0)
{
lean_object* v_size_209_; lean_object* v_k_210_; lean_object* v_v_211_; lean_object* v_l_212_; lean_object* v_r_213_; lean_object* v___x_214_; 
lean_dec(v_h__1_207_);
v_size_209_ = lean_ctor_get(v_t_206_, 0);
lean_inc(v_size_209_);
v_k_210_ = lean_ctor_get(v_t_206_, 1);
lean_inc(v_k_210_);
v_v_211_ = lean_ctor_get(v_t_206_, 2);
lean_inc(v_v_211_);
v_l_212_ = lean_ctor_get(v_t_206_, 3);
lean_inc(v_l_212_);
v_r_213_ = lean_ctor_get(v_t_206_, 4);
lean_inc(v_r_213_);
lean_dec_ref(v_t_206_);
v___x_214_ = lean_apply_5(v_h__2_208_, v_size_209_, v_k_210_, v_v_211_, v_l_212_, v_r_213_);
return v___x_214_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; 
lean_dec(v_h__2_208_);
v___x_215_ = lean_box(0);
v___x_216_ = lean_apply_1(v_h__1_207_, v___x_215_);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t v_x_217_, lean_object* v_h__1_218_, lean_object* v_h__2_219_, lean_object* v_h__3_220_){
_start:
{
switch(v_x_217_)
{
case 0:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
lean_dec(v_h__3_220_);
lean_dec(v_h__2_219_);
v___x_221_ = lean_box(0);
v___x_222_ = lean_apply_1(v_h__1_218_, v___x_221_);
return v___x_222_;
}
case 1:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v_h__2_219_);
lean_dec(v_h__1_218_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_apply_1(v_h__3_220_, v___x_223_);
return v___x_224_;
}
default: 
{
lean_object* v___x_225_; lean_object* v___x_226_; 
lean_dec(v_h__3_220_);
lean_dec(v_h__1_218_);
v___x_225_ = lean_box(0);
v___x_226_ = lean_apply_1(v_h__2_219_, v___x_225_);
return v___x_226_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* v_x_227_, lean_object* v_h__1_228_, lean_object* v_h__2_229_, lean_object* v_h__3_230_){
_start:
{
uint8_t v_x_36__boxed_231_; lean_object* v_res_232_; 
v_x_36__boxed_231_ = lean_unbox(v_x_227_);
v_res_232_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_36__boxed_231_, v_h__1_228_, v_h__2_229_, v_h__3_230_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* v_motive_233_, uint8_t v_x_234_, lean_object* v_h__1_235_, lean_object* v_h__2_236_, lean_object* v_h__3_237_){
_start:
{
switch(v_x_234_)
{
case 0:
{
lean_object* v___x_238_; lean_object* v___x_239_; 
lean_dec(v_h__3_237_);
lean_dec(v_h__2_236_);
v___x_238_ = lean_box(0);
v___x_239_ = lean_apply_1(v_h__1_235_, v___x_238_);
return v___x_239_;
}
case 1:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_h__2_236_);
lean_dec(v_h__1_235_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_apply_1(v_h__3_237_, v___x_240_);
return v___x_241_;
}
default: 
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_h__3_237_);
lean_dec(v_h__1_235_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_apply_1(v_h__2_236_, v___x_242_);
return v___x_243_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* v_motive_244_, lean_object* v_x_245_, lean_object* v_h__1_246_, lean_object* v_h__2_247_, lean_object* v_h__3_248_){
_start:
{
uint8_t v_x_51__boxed_249_; lean_object* v_res_250_; 
v_x_51__boxed_249_ = lean_unbox(v_x_245_);
v_res_250_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_244_, v_x_51__boxed_249_, v_h__1_246_, v_h__2_247_, v_h__3_248_);
return v_res_250_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(lean_object* v_t_251_){
_start:
{
if (lean_obj_tag(v_t_251_) == 0)
{
uint8_t v___x_252_; 
v___x_252_ = 0;
return v___x_252_;
}
else
{
uint8_t v___x_253_; 
v___x_253_ = 1;
return v___x_253_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___redArg___boxed(lean_object* v_t_254_){
_start:
{
uint8_t v_res_255_; lean_object* v_r_256_; 
v_res_255_ = l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(v_t_254_);
lean_dec(v_t_254_);
v_r_256_ = lean_box(v_res_255_);
return v_r_256_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty(lean_object* v_00_u03b1_257_, lean_object* v_00_u03b2_258_, lean_object* v_t_259_){
_start:
{
if (lean_obj_tag(v_t_259_) == 0)
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
else
{
uint8_t v___x_261_; 
v___x_261_ = 1;
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___boxed(lean_object* v_00_u03b1_262_, lean_object* v_00_u03b2_263_, lean_object* v_t_264_){
_start:
{
uint8_t v_res_265_; lean_object* v_r_266_; 
v_res_265_ = l_Std_DTreeMap_Internal_Impl_isEmpty(v_00_u03b1_262_, v_00_u03b2_263_, v_t_264_);
lean_dec(v_t_264_);
v_r_266_ = lean_box(v_res_265_);
return v_r_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object* v_inst_267_, lean_object* v_t_268_, lean_object* v_k_269_){
_start:
{
if (lean_obj_tag(v_t_268_) == 0)
{
lean_object* v_k_270_; lean_object* v_v_271_; lean_object* v_l_272_; lean_object* v_r_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_k_270_ = lean_ctor_get(v_t_268_, 1);
lean_inc(v_k_270_);
v_v_271_ = lean_ctor_get(v_t_268_, 2);
lean_inc(v_v_271_);
v_l_272_ = lean_ctor_get(v_t_268_, 3);
lean_inc(v_l_272_);
v_r_273_ = lean_ctor_get(v_t_268_, 4);
lean_inc(v_r_273_);
lean_dec_ref(v_t_268_);
lean_inc_ref(v_inst_267_);
lean_inc(v_k_269_);
v___x_274_ = lean_apply_2(v_inst_267_, v_k_269_, v_k_270_);
v___x_275_ = lean_unbox(v___x_274_);
switch(v___x_275_)
{
case 0:
{
lean_dec(v_r_273_);
lean_dec(v_v_271_);
v_t_268_ = v_l_272_;
goto _start;
}
case 1:
{
lean_object* v___x_277_; 
lean_dec(v_r_273_);
lean_dec(v_l_272_);
lean_dec(v_k_269_);
lean_dec_ref(v_inst_267_);
v___x_277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_277_, 0, v_v_271_);
return v___x_277_;
}
default: 
{
lean_dec(v_l_272_);
lean_dec(v_v_271_);
v_t_268_ = v_r_273_;
goto _start;
}
}
}
else
{
lean_object* v___x_279_; 
lean_dec(v_k_269_);
lean_dec_ref(v_inst_267_);
v___x_279_ = lean_box(0);
return v___x_279_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f(lean_object* v_00_u03b1_280_, lean_object* v_00_u03b2_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_t_284_, lean_object* v_k_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_inst_282_, v_t_284_, v_k_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get___redArg(lean_object* v_inst_287_, lean_object* v_t_288_, lean_object* v_k_289_){
_start:
{
lean_object* v_k_290_; lean_object* v_v_291_; lean_object* v_l_292_; lean_object* v_r_293_; lean_object* v___x_294_; uint8_t v___x_295_; 
v_k_290_ = lean_ctor_get(v_t_288_, 1);
lean_inc(v_k_290_);
v_v_291_ = lean_ctor_get(v_t_288_, 2);
lean_inc(v_v_291_);
v_l_292_ = lean_ctor_get(v_t_288_, 3);
lean_inc(v_l_292_);
v_r_293_ = lean_ctor_get(v_t_288_, 4);
lean_inc(v_r_293_);
lean_dec(v_t_288_);
lean_inc_ref(v_inst_287_);
lean_inc(v_k_289_);
v___x_294_ = lean_apply_2(v_inst_287_, v_k_289_, v_k_290_);
v___x_295_ = lean_unbox(v___x_294_);
switch(v___x_295_)
{
case 0:
{
lean_dec(v_r_293_);
lean_dec(v_v_291_);
v_t_288_ = v_l_292_;
goto _start;
}
case 1:
{
lean_dec(v_r_293_);
lean_dec(v_l_292_);
lean_dec(v_k_289_);
lean_dec_ref(v_inst_287_);
return v_v_291_;
}
default: 
{
lean_dec(v_l_292_);
lean_dec(v_v_291_);
v_t_288_ = v_r_293_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get(lean_object* v_00_u03b1_298_, lean_object* v_00_u03b2_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_t_302_, lean_object* v_k_303_, lean_object* v_hlk_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_inst_300_, v_t_302_, v_k_303_);
return v___x_305_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_309_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_310_ = lean_unsigned_to_nat(13u);
v___x_311_ = lean_unsigned_to_nat(108u);
v___x_312_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1));
v___x_313_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_314_ = l_mkPanicMessageWithDecl(v___x_313_, v___x_312_, v___x_311_, v___x_310_, v___x_309_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object* v_inst_315_, lean_object* v_t_316_, lean_object* v_k_317_, lean_object* v_inst_318_){
_start:
{
if (lean_obj_tag(v_t_316_) == 0)
{
lean_object* v_k_319_; lean_object* v_v_320_; lean_object* v_l_321_; lean_object* v_r_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v_k_319_ = lean_ctor_get(v_t_316_, 1);
lean_inc(v_k_319_);
v_v_320_ = lean_ctor_get(v_t_316_, 2);
lean_inc(v_v_320_);
v_l_321_ = lean_ctor_get(v_t_316_, 3);
lean_inc(v_l_321_);
v_r_322_ = lean_ctor_get(v_t_316_, 4);
lean_inc(v_r_322_);
lean_dec_ref(v_t_316_);
lean_inc_ref(v_inst_315_);
lean_inc(v_k_317_);
v___x_323_ = lean_apply_2(v_inst_315_, v_k_317_, v_k_319_);
v___x_324_ = lean_unbox(v___x_323_);
switch(v___x_324_)
{
case 0:
{
lean_dec(v_r_322_);
lean_dec(v_v_320_);
v_t_316_ = v_l_321_;
goto _start;
}
case 1:
{
lean_dec(v_r_322_);
lean_dec(v_l_321_);
lean_dec(v_inst_318_);
lean_dec(v_k_317_);
lean_dec_ref(v_inst_315_);
return v_v_320_;
}
default: 
{
lean_dec(v_l_321_);
lean_dec(v_v_320_);
v_t_316_ = v_r_322_;
goto _start;
}
}
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_k_317_);
lean_dec_ref(v_inst_315_);
v___x_327_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3);
v___x_328_ = l_panic___redArg(v_inst_318_, v___x_327_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_t_333_, lean_object* v_k_334_, lean_object* v_inst_335_){
_start:
{
lean_object* v___x_336_; 
v___x_336_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_inst_331_, v_t_333_, v_k_334_, v_inst_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg(lean_object* v_inst_337_, lean_object* v_t_338_, lean_object* v_k_339_, lean_object* v_fallback_340_){
_start:
{
if (lean_obj_tag(v_t_338_) == 0)
{
lean_object* v_k_341_; lean_object* v_v_342_; lean_object* v_l_343_; lean_object* v_r_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v_k_341_ = lean_ctor_get(v_t_338_, 1);
lean_inc(v_k_341_);
v_v_342_ = lean_ctor_get(v_t_338_, 2);
lean_inc(v_v_342_);
v_l_343_ = lean_ctor_get(v_t_338_, 3);
lean_inc(v_l_343_);
v_r_344_ = lean_ctor_get(v_t_338_, 4);
lean_inc(v_r_344_);
lean_dec_ref(v_t_338_);
lean_inc_ref(v_inst_337_);
lean_inc(v_k_339_);
v___x_345_ = lean_apply_2(v_inst_337_, v_k_339_, v_k_341_);
v___x_346_ = lean_unbox(v___x_345_);
switch(v___x_346_)
{
case 0:
{
lean_dec(v_r_344_);
lean_dec(v_v_342_);
v_t_338_ = v_l_343_;
goto _start;
}
case 1:
{
lean_dec(v_r_344_);
lean_dec(v_l_343_);
lean_dec(v_k_339_);
lean_dec_ref(v_inst_337_);
return v_v_342_;
}
default: 
{
lean_dec(v_l_343_);
lean_dec(v_v_342_);
v_t_338_ = v_r_344_;
goto _start;
}
}
}
else
{
lean_dec(v_k_339_);
lean_dec_ref(v_inst_337_);
lean_inc(v_fallback_340_);
return v_fallback_340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg___boxed(lean_object* v_inst_349_, lean_object* v_t_350_, lean_object* v_k_351_, lean_object* v_fallback_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_inst_349_, v_t_350_, v_k_351_, v_fallback_352_);
lean_dec(v_fallback_352_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD(lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_t_358_, lean_object* v_k_359_, lean_object* v_fallback_360_){
_start:
{
lean_object* v___x_361_; 
v___x_361_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_inst_356_, v_t_358_, v_k_359_, v_fallback_360_);
return v___x_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___boxed(lean_object* v_00_u03b1_362_, lean_object* v_00_u03b2_363_, lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_t_366_, lean_object* v_k_367_, lean_object* v_fallback_368_){
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_DTreeMap_Internal_Impl_getD(v_00_u03b1_362_, v_00_u03b2_363_, v_inst_364_, v_inst_365_, v_t_366_, v_k_367_, v_fallback_368_);
lean_dec(v_fallback_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(lean_object* v_inst_370_, lean_object* v_t_371_, lean_object* v_k_372_){
_start:
{
if (lean_obj_tag(v_t_371_) == 0)
{
lean_object* v_k_373_; lean_object* v_v_374_; lean_object* v_l_375_; lean_object* v_r_376_; lean_object* v___x_377_; uint8_t v___x_378_; 
v_k_373_ = lean_ctor_get(v_t_371_, 1);
lean_inc(v_k_373_);
v_v_374_ = lean_ctor_get(v_t_371_, 2);
lean_inc(v_v_374_);
v_l_375_ = lean_ctor_get(v_t_371_, 3);
lean_inc(v_l_375_);
v_r_376_ = lean_ctor_get(v_t_371_, 4);
lean_inc(v_r_376_);
lean_dec_ref(v_t_371_);
lean_inc_ref(v_inst_370_);
lean_inc(v_k_373_);
lean_inc(v_k_372_);
v___x_377_ = lean_apply_2(v_inst_370_, v_k_372_, v_k_373_);
v___x_378_ = lean_unbox(v___x_377_);
switch(v___x_378_)
{
case 0:
{
lean_dec(v_r_376_);
lean_dec(v_v_374_);
lean_dec(v_k_373_);
v_t_371_ = v_l_375_;
goto _start;
}
case 1:
{
lean_object* v___x_380_; lean_object* v___x_381_; 
lean_dec(v_r_376_);
lean_dec(v_l_375_);
lean_dec(v_k_372_);
lean_dec_ref(v_inst_370_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v_k_373_);
lean_ctor_set(v___x_380_, 1, v_v_374_);
v___x_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
return v___x_381_;
}
default: 
{
lean_dec(v_l_375_);
lean_dec(v_v_374_);
lean_dec(v_k_373_);
v_t_371_ = v_r_376_;
goto _start;
}
}
}
else
{
lean_object* v___x_383_; 
lean_dec(v_k_372_);
lean_dec_ref(v_inst_370_);
v___x_383_ = lean_box(0);
return v___x_383_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f(lean_object* v_00_u03b1_384_, lean_object* v_00_u03b2_385_, lean_object* v_inst_386_, lean_object* v_t_387_, lean_object* v_k_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_inst_386_, v_t_387_, v_k_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry___redArg(lean_object* v_inst_390_, lean_object* v_t_391_, lean_object* v_k_392_){
_start:
{
lean_object* v_k_393_; lean_object* v_v_394_; lean_object* v_l_395_; lean_object* v_r_396_; lean_object* v___x_397_; uint8_t v___x_398_; 
v_k_393_ = lean_ctor_get(v_t_391_, 1);
lean_inc(v_k_393_);
v_v_394_ = lean_ctor_get(v_t_391_, 2);
lean_inc(v_v_394_);
v_l_395_ = lean_ctor_get(v_t_391_, 3);
lean_inc(v_l_395_);
v_r_396_ = lean_ctor_get(v_t_391_, 4);
lean_inc(v_r_396_);
lean_dec(v_t_391_);
lean_inc_ref(v_inst_390_);
lean_inc(v_k_393_);
lean_inc(v_k_392_);
v___x_397_ = lean_apply_2(v_inst_390_, v_k_392_, v_k_393_);
v___x_398_ = lean_unbox(v___x_397_);
switch(v___x_398_)
{
case 0:
{
lean_dec(v_r_396_);
lean_dec(v_v_394_);
lean_dec(v_k_393_);
v_t_391_ = v_l_395_;
goto _start;
}
case 1:
{
lean_object* v___x_400_; 
lean_dec(v_r_396_);
lean_dec(v_l_395_);
lean_dec(v_k_392_);
lean_dec_ref(v_inst_390_);
v___x_400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_400_, 0, v_k_393_);
lean_ctor_set(v___x_400_, 1, v_v_394_);
return v___x_400_;
}
default: 
{
lean_dec(v_l_395_);
lean_dec(v_v_394_);
lean_dec(v_k_393_);
v_t_391_ = v_r_396_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry(lean_object* v_00_u03b1_402_, lean_object* v_00_u03b2_403_, lean_object* v_inst_404_, lean_object* v_t_405_, lean_object* v_k_406_, lean_object* v_hlk_407_){
_start:
{
lean_object* v___x_408_; 
v___x_408_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_inst_404_, v_t_405_, v_k_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_410_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_411_ = lean_unsigned_to_nat(13u);
v___x_412_ = lean_unsigned_to_nat(147u);
v___x_413_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0));
v___x_414_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_415_ = l_mkPanicMessageWithDecl(v___x_414_, v___x_413_, v___x_412_, v___x_411_, v___x_410_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_t_418_, lean_object* v_k_419_){
_start:
{
if (lean_obj_tag(v_t_418_) == 0)
{
lean_object* v_k_420_; lean_object* v_v_421_; lean_object* v_l_422_; lean_object* v_r_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v_k_420_ = lean_ctor_get(v_t_418_, 1);
lean_inc(v_k_420_);
v_v_421_ = lean_ctor_get(v_t_418_, 2);
lean_inc(v_v_421_);
v_l_422_ = lean_ctor_get(v_t_418_, 3);
lean_inc(v_l_422_);
v_r_423_ = lean_ctor_get(v_t_418_, 4);
lean_inc(v_r_423_);
lean_dec_ref(v_t_418_);
lean_inc_ref(v_inst_416_);
lean_inc(v_k_420_);
lean_inc(v_k_419_);
v___x_424_ = lean_apply_2(v_inst_416_, v_k_419_, v_k_420_);
v___x_425_ = lean_unbox(v___x_424_);
switch(v___x_425_)
{
case 0:
{
lean_dec(v_r_423_);
lean_dec(v_v_421_);
lean_dec(v_k_420_);
v_t_418_ = v_l_422_;
goto _start;
}
case 1:
{
lean_object* v___x_427_; 
lean_dec(v_r_423_);
lean_dec(v_l_422_);
lean_dec(v_k_419_);
lean_dec_ref(v_inst_417_);
lean_dec_ref(v_inst_416_);
v___x_427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_427_, 0, v_k_420_);
lean_ctor_set(v___x_427_, 1, v_v_421_);
return v___x_427_;
}
default: 
{
lean_dec(v_l_422_);
lean_dec(v_v_421_);
lean_dec(v_k_420_);
v_t_418_ = v_r_423_;
goto _start;
}
}
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_k_419_);
lean_dec_ref(v_inst_416_);
v___x_429_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1);
v___x_430_ = l_panic___redArg(v_inst_417_, v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21(lean_object* v_00_u03b1_431_, lean_object* v_00_u03b2_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_t_435_, lean_object* v_k_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_inst_433_, v_inst_434_, v_t_435_, v_k_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(lean_object* v_inst_438_, lean_object* v_t_439_, lean_object* v_k_440_, lean_object* v_fallback_441_){
_start:
{
if (lean_obj_tag(v_t_439_) == 0)
{
lean_object* v_k_442_; lean_object* v_v_443_; lean_object* v_l_444_; lean_object* v_r_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_k_442_ = lean_ctor_get(v_t_439_, 1);
lean_inc(v_k_442_);
v_v_443_ = lean_ctor_get(v_t_439_, 2);
lean_inc(v_v_443_);
v_l_444_ = lean_ctor_get(v_t_439_, 3);
lean_inc(v_l_444_);
v_r_445_ = lean_ctor_get(v_t_439_, 4);
lean_inc(v_r_445_);
lean_dec_ref(v_t_439_);
lean_inc_ref(v_inst_438_);
lean_inc(v_k_442_);
lean_inc(v_k_440_);
v___x_446_ = lean_apply_2(v_inst_438_, v_k_440_, v_k_442_);
v___x_447_ = lean_unbox(v___x_446_);
switch(v___x_447_)
{
case 0:
{
lean_dec(v_r_445_);
lean_dec(v_v_443_);
lean_dec(v_k_442_);
v_t_439_ = v_l_444_;
goto _start;
}
case 1:
{
lean_object* v___x_449_; 
lean_dec(v_r_445_);
lean_dec(v_l_444_);
lean_dec(v_k_440_);
lean_dec_ref(v_inst_438_);
v___x_449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_449_, 0, v_k_442_);
lean_ctor_set(v___x_449_, 1, v_v_443_);
return v___x_449_;
}
default: 
{
lean_dec(v_l_444_);
lean_dec(v_v_443_);
lean_dec(v_k_442_);
v_t_439_ = v_r_445_;
goto _start;
}
}
}
else
{
lean_dec(v_k_440_);
lean_dec_ref(v_inst_438_);
lean_inc_ref(v_fallback_441_);
return v_fallback_441_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg___boxed(lean_object* v_inst_451_, lean_object* v_t_452_, lean_object* v_k_453_, lean_object* v_fallback_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_451_, v_t_452_, v_k_453_, v_fallback_454_);
lean_dec_ref(v_fallback_454_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD(lean_object* v_00_u03b1_456_, lean_object* v_00_u03b2_457_, lean_object* v_inst_458_, lean_object* v_t_459_, lean_object* v_k_460_, lean_object* v_fallback_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_458_, v_t_459_, v_k_460_, v_fallback_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___boxed(lean_object* v_00_u03b1_463_, lean_object* v_00_u03b2_464_, lean_object* v_inst_465_, lean_object* v_t_466_, lean_object* v_k_467_, lean_object* v_fallback_468_){
_start:
{
lean_object* v_res_469_; 
v_res_469_ = l_Std_DTreeMap_Internal_Impl_getEntryD(v_00_u03b1_463_, v_00_u03b2_464_, v_inst_465_, v_t_466_, v_k_467_, v_fallback_468_);
lean_dec_ref(v_fallback_468_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object* v_inst_470_, lean_object* v_t_471_, lean_object* v_k_472_){
_start:
{
if (lean_obj_tag(v_t_471_) == 0)
{
lean_object* v_k_473_; lean_object* v_l_474_; lean_object* v_r_475_; lean_object* v___x_476_; uint8_t v___x_477_; 
v_k_473_ = lean_ctor_get(v_t_471_, 1);
lean_inc(v_k_473_);
v_l_474_ = lean_ctor_get(v_t_471_, 3);
lean_inc(v_l_474_);
v_r_475_ = lean_ctor_get(v_t_471_, 4);
lean_inc(v_r_475_);
lean_dec_ref(v_t_471_);
lean_inc_ref(v_inst_470_);
lean_inc(v_k_473_);
lean_inc(v_k_472_);
v___x_476_ = lean_apply_2(v_inst_470_, v_k_472_, v_k_473_);
v___x_477_ = lean_unbox(v___x_476_);
switch(v___x_477_)
{
case 0:
{
lean_dec(v_r_475_);
lean_dec(v_k_473_);
v_t_471_ = v_l_474_;
goto _start;
}
case 1:
{
lean_object* v___x_479_; 
lean_dec(v_r_475_);
lean_dec(v_l_474_);
lean_dec(v_k_472_);
lean_dec_ref(v_inst_470_);
v___x_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_479_, 0, v_k_473_);
return v___x_479_;
}
default: 
{
lean_dec(v_l_474_);
lean_dec(v_k_473_);
v_t_471_ = v_r_475_;
goto _start;
}
}
}
else
{
lean_object* v___x_481_; 
lean_dec(v_k_472_);
lean_dec_ref(v_inst_470_);
v___x_481_ = lean_box(0);
return v___x_481_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f(lean_object* v_00_u03b1_482_, lean_object* v_00_u03b2_483_, lean_object* v_inst_484_, lean_object* v_t_485_, lean_object* v_k_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_inst_484_, v_t_485_, v_k_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object* v_inst_488_, lean_object* v_t_489_, lean_object* v_k_490_){
_start:
{
lean_object* v_k_491_; lean_object* v_l_492_; lean_object* v_r_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_k_491_ = lean_ctor_get(v_t_489_, 1);
lean_inc(v_k_491_);
v_l_492_ = lean_ctor_get(v_t_489_, 3);
lean_inc(v_l_492_);
v_r_493_ = lean_ctor_get(v_t_489_, 4);
lean_inc(v_r_493_);
lean_dec(v_t_489_);
lean_inc_ref(v_inst_488_);
lean_inc(v_k_491_);
lean_inc(v_k_490_);
v___x_494_ = lean_apply_2(v_inst_488_, v_k_490_, v_k_491_);
v___x_495_ = lean_unbox(v___x_494_);
switch(v___x_495_)
{
case 0:
{
lean_dec(v_r_493_);
lean_dec(v_k_491_);
v_t_489_ = v_l_492_;
goto _start;
}
case 1:
{
lean_dec(v_r_493_);
lean_dec(v_l_492_);
lean_dec(v_k_490_);
lean_dec_ref(v_inst_488_);
return v_k_491_;
}
default: 
{
lean_dec(v_l_492_);
lean_dec(v_k_491_);
v_t_489_ = v_r_493_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey(lean_object* v_00_u03b1_498_, lean_object* v_00_u03b2_499_, lean_object* v_inst_500_, lean_object* v_t_501_, lean_object* v_k_502_, lean_object* v_hlk_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_inst_500_, v_t_501_, v_k_502_);
return v___x_504_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_506_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_507_ = lean_unsigned_to_nat(13u);
v___x_508_ = lean_unsigned_to_nat(186u);
v___x_509_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0));
v___x_510_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_511_ = l_mkPanicMessageWithDecl(v___x_510_, v___x_509_, v___x_508_, v___x_507_, v___x_506_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object* v_inst_512_, lean_object* v_t_513_, lean_object* v_k_514_, lean_object* v_inst_515_){
_start:
{
if (lean_obj_tag(v_t_513_) == 0)
{
lean_object* v_k_516_; lean_object* v_l_517_; lean_object* v_r_518_; lean_object* v___x_519_; uint8_t v___x_520_; 
v_k_516_ = lean_ctor_get(v_t_513_, 1);
lean_inc(v_k_516_);
v_l_517_ = lean_ctor_get(v_t_513_, 3);
lean_inc(v_l_517_);
v_r_518_ = lean_ctor_get(v_t_513_, 4);
lean_inc(v_r_518_);
lean_dec_ref(v_t_513_);
lean_inc_ref(v_inst_512_);
lean_inc(v_k_516_);
lean_inc(v_k_514_);
v___x_519_ = lean_apply_2(v_inst_512_, v_k_514_, v_k_516_);
v___x_520_ = lean_unbox(v___x_519_);
switch(v___x_520_)
{
case 0:
{
lean_dec(v_r_518_);
lean_dec(v_k_516_);
v_t_513_ = v_l_517_;
goto _start;
}
case 1:
{
lean_dec(v_r_518_);
lean_dec(v_l_517_);
lean_dec(v_inst_515_);
lean_dec(v_k_514_);
lean_dec_ref(v_inst_512_);
return v_k_516_;
}
default: 
{
lean_dec(v_l_517_);
lean_dec(v_k_516_);
v_t_513_ = v_r_518_;
goto _start;
}
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; 
lean_dec(v_k_514_);
lean_dec_ref(v_inst_512_);
v___x_523_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1);
v___x_524_ = l_panic___redArg(v_inst_515_, v___x_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21(lean_object* v_00_u03b1_525_, lean_object* v_00_u03b2_526_, lean_object* v_inst_527_, lean_object* v_t_528_, lean_object* v_k_529_, lean_object* v_inst_530_){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_inst_527_, v_t_528_, v_k_529_, v_inst_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object* v_inst_532_, lean_object* v_t_533_, lean_object* v_k_534_, lean_object* v_fallback_535_){
_start:
{
if (lean_obj_tag(v_t_533_) == 0)
{
lean_object* v_k_536_; lean_object* v_l_537_; lean_object* v_r_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v_k_536_ = lean_ctor_get(v_t_533_, 1);
lean_inc(v_k_536_);
v_l_537_ = lean_ctor_get(v_t_533_, 3);
lean_inc(v_l_537_);
v_r_538_ = lean_ctor_get(v_t_533_, 4);
lean_inc(v_r_538_);
lean_dec_ref(v_t_533_);
lean_inc_ref(v_inst_532_);
lean_inc(v_k_536_);
lean_inc(v_k_534_);
v___x_539_ = lean_apply_2(v_inst_532_, v_k_534_, v_k_536_);
v___x_540_ = lean_unbox(v___x_539_);
switch(v___x_540_)
{
case 0:
{
lean_dec(v_r_538_);
lean_dec(v_k_536_);
v_t_533_ = v_l_537_;
goto _start;
}
case 1:
{
lean_dec(v_r_538_);
lean_dec(v_l_537_);
lean_dec(v_k_534_);
lean_dec_ref(v_inst_532_);
return v_k_536_;
}
default: 
{
lean_dec(v_l_537_);
lean_dec(v_k_536_);
v_t_533_ = v_r_538_;
goto _start;
}
}
}
else
{
lean_dec(v_k_534_);
lean_dec_ref(v_inst_532_);
lean_inc(v_fallback_535_);
return v_fallback_535_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg___boxed(lean_object* v_inst_543_, lean_object* v_t_544_, lean_object* v_k_545_, lean_object* v_fallback_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_543_, v_t_544_, v_k_545_, v_fallback_546_);
lean_dec(v_fallback_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, lean_object* v_inst_550_, lean_object* v_t_551_, lean_object* v_k_552_, lean_object* v_fallback_553_){
_start:
{
lean_object* v___x_554_; 
v___x_554_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_550_, v_t_551_, v_k_552_, v_fallback_553_);
return v___x_554_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___boxed(lean_object* v_00_u03b1_555_, lean_object* v_00_u03b2_556_, lean_object* v_inst_557_, lean_object* v_t_558_, lean_object* v_k_559_, lean_object* v_fallback_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_Std_DTreeMap_Internal_Impl_getKeyD(v_00_u03b1_555_, v_00_u03b2_556_, v_inst_557_, v_t_558_, v_k_559_, v_fallback_560_);
lean_dec(v_fallback_560_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object* v_inst_562_, lean_object* v_t_563_, lean_object* v_k_564_){
_start:
{
if (lean_obj_tag(v_t_563_) == 0)
{
lean_object* v_k_565_; lean_object* v_v_566_; lean_object* v_l_567_; lean_object* v_r_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_k_565_ = lean_ctor_get(v_t_563_, 1);
lean_inc(v_k_565_);
v_v_566_ = lean_ctor_get(v_t_563_, 2);
lean_inc(v_v_566_);
v_l_567_ = lean_ctor_get(v_t_563_, 3);
lean_inc(v_l_567_);
v_r_568_ = lean_ctor_get(v_t_563_, 4);
lean_inc(v_r_568_);
lean_dec_ref(v_t_563_);
lean_inc_ref(v_inst_562_);
lean_inc(v_k_564_);
v___x_569_ = lean_apply_2(v_inst_562_, v_k_564_, v_k_565_);
v___x_570_ = lean_unbox(v___x_569_);
switch(v___x_570_)
{
case 0:
{
lean_dec(v_r_568_);
lean_dec(v_v_566_);
v_t_563_ = v_l_567_;
goto _start;
}
case 1:
{
lean_object* v___x_572_; 
lean_dec(v_r_568_);
lean_dec(v_l_567_);
lean_dec(v_k_564_);
lean_dec_ref(v_inst_562_);
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v_v_566_);
return v___x_572_;
}
default: 
{
lean_dec(v_l_567_);
lean_dec(v_v_566_);
v_t_563_ = v_r_568_;
goto _start;
}
}
}
else
{
lean_object* v___x_574_; 
lean_dec(v_k_564_);
lean_dec_ref(v_inst_562_);
v___x_574_ = lean_box(0);
return v___x_574_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f(lean_object* v_00_u03b1_575_, lean_object* v_00_u03b4_576_, lean_object* v_inst_577_, lean_object* v_t_578_, lean_object* v_k_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_inst_577_, v_t_578_, v_k_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object* v_inst_581_, lean_object* v_t_582_, lean_object* v_k_583_){
_start:
{
lean_object* v_k_584_; lean_object* v_v_585_; lean_object* v_l_586_; lean_object* v_r_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_k_584_ = lean_ctor_get(v_t_582_, 1);
lean_inc(v_k_584_);
v_v_585_ = lean_ctor_get(v_t_582_, 2);
lean_inc(v_v_585_);
v_l_586_ = lean_ctor_get(v_t_582_, 3);
lean_inc(v_l_586_);
v_r_587_ = lean_ctor_get(v_t_582_, 4);
lean_inc(v_r_587_);
lean_dec(v_t_582_);
lean_inc_ref(v_inst_581_);
lean_inc(v_k_583_);
v___x_588_ = lean_apply_2(v_inst_581_, v_k_583_, v_k_584_);
v___x_589_ = lean_unbox(v___x_588_);
switch(v___x_589_)
{
case 0:
{
lean_dec(v_r_587_);
lean_dec(v_v_585_);
v_t_582_ = v_l_586_;
goto _start;
}
case 1:
{
lean_dec(v_r_587_);
lean_dec(v_l_586_);
lean_dec(v_k_583_);
lean_dec_ref(v_inst_581_);
return v_v_585_;
}
default: 
{
lean_dec(v_l_586_);
lean_dec(v_v_585_);
v_t_582_ = v_r_587_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get(lean_object* v_00_u03b1_592_, lean_object* v_00_u03b4_593_, lean_object* v_inst_594_, lean_object* v_t_595_, lean_object* v_k_596_, lean_object* v_hlk_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_inst_594_, v_t_595_, v_k_596_);
return v___x_598_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_600_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_601_ = lean_unsigned_to_nat(13u);
v___x_602_ = lean_unsigned_to_nat(227u);
v___x_603_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0));
v___x_604_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_605_ = l_mkPanicMessageWithDecl(v___x_604_, v___x_603_, v___x_602_, v___x_601_, v___x_600_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object* v_inst_606_, lean_object* v_inst_607_, lean_object* v_t_608_, lean_object* v_k_609_){
_start:
{
if (lean_obj_tag(v_t_608_) == 0)
{
lean_object* v_k_610_; lean_object* v_v_611_; lean_object* v_l_612_; lean_object* v_r_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_k_610_ = lean_ctor_get(v_t_608_, 1);
lean_inc(v_k_610_);
v_v_611_ = lean_ctor_get(v_t_608_, 2);
lean_inc(v_v_611_);
v_l_612_ = lean_ctor_get(v_t_608_, 3);
lean_inc(v_l_612_);
v_r_613_ = lean_ctor_get(v_t_608_, 4);
lean_inc(v_r_613_);
lean_dec_ref(v_t_608_);
lean_inc_ref(v_inst_606_);
lean_inc(v_k_609_);
v___x_614_ = lean_apply_2(v_inst_606_, v_k_609_, v_k_610_);
v___x_615_ = lean_unbox(v___x_614_);
switch(v___x_615_)
{
case 0:
{
lean_dec(v_r_613_);
lean_dec(v_v_611_);
v_t_608_ = v_l_612_;
goto _start;
}
case 1:
{
lean_dec(v_r_613_);
lean_dec(v_l_612_);
lean_dec(v_k_609_);
lean_dec(v_inst_607_);
lean_dec_ref(v_inst_606_);
return v_v_611_;
}
default: 
{
lean_dec(v_l_612_);
lean_dec(v_v_611_);
v_t_608_ = v_r_613_;
goto _start;
}
}
}
else
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_k_609_);
lean_dec_ref(v_inst_606_);
v___x_618_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1);
v___x_619_ = l_panic___redArg(v_inst_607_, v___x_618_);
return v___x_619_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21(lean_object* v_00_u03b1_620_, lean_object* v_00_u03b4_621_, lean_object* v_inst_622_, lean_object* v_inst_623_, lean_object* v_t_624_, lean_object* v_k_625_){
_start:
{
lean_object* v___x_626_; 
v___x_626_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_inst_622_, v_inst_623_, v_t_624_, v_k_625_);
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object* v_inst_627_, lean_object* v_t_628_, lean_object* v_k_629_, lean_object* v_fallback_630_){
_start:
{
if (lean_obj_tag(v_t_628_) == 0)
{
lean_object* v_k_631_; lean_object* v_v_632_; lean_object* v_l_633_; lean_object* v_r_634_; lean_object* v___x_635_; uint8_t v___x_636_; 
v_k_631_ = lean_ctor_get(v_t_628_, 1);
lean_inc(v_k_631_);
v_v_632_ = lean_ctor_get(v_t_628_, 2);
lean_inc(v_v_632_);
v_l_633_ = lean_ctor_get(v_t_628_, 3);
lean_inc(v_l_633_);
v_r_634_ = lean_ctor_get(v_t_628_, 4);
lean_inc(v_r_634_);
lean_dec_ref(v_t_628_);
lean_inc_ref(v_inst_627_);
lean_inc(v_k_629_);
v___x_635_ = lean_apply_2(v_inst_627_, v_k_629_, v_k_631_);
v___x_636_ = lean_unbox(v___x_635_);
switch(v___x_636_)
{
case 0:
{
lean_dec(v_r_634_);
lean_dec(v_v_632_);
v_t_628_ = v_l_633_;
goto _start;
}
case 1:
{
lean_dec(v_r_634_);
lean_dec(v_l_633_);
lean_dec(v_k_629_);
lean_dec_ref(v_inst_627_);
return v_v_632_;
}
default: 
{
lean_dec(v_l_633_);
lean_dec(v_v_632_);
v_t_628_ = v_r_634_;
goto _start;
}
}
}
else
{
lean_dec(v_k_629_);
lean_dec_ref(v_inst_627_);
lean_inc(v_fallback_630_);
return v_fallback_630_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg___boxed(lean_object* v_inst_639_, lean_object* v_t_640_, lean_object* v_k_641_, lean_object* v_fallback_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_639_, v_t_640_, v_k_641_, v_fallback_642_);
lean_dec(v_fallback_642_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD(lean_object* v_00_u03b1_644_, lean_object* v_00_u03b4_645_, lean_object* v_inst_646_, lean_object* v_t_647_, lean_object* v_k_648_, lean_object* v_fallback_649_){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_646_, v_t_647_, v_k_648_, v_fallback_649_);
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___boxed(lean_object* v_00_u03b1_651_, lean_object* v_00_u03b4_652_, lean_object* v_inst_653_, lean_object* v_t_654_, lean_object* v_k_655_, lean_object* v_fallback_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Std_DTreeMap_Internal_Impl_Const_getD(v_00_u03b1_651_, v_00_u03b4_652_, v_inst_653_, v_t_654_, v_k_655_, v_fallback_656_);
lean_dec(v_fallback_656_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1(lean_object* v_f_658_, lean_object* v_k_659_, lean_object* v_v_660_, lean_object* v_toBind_661_, lean_object* v___f_662_, lean_object* v_left_663_){
_start:
{
lean_object* v___x_664_; lean_object* v___x_665_; 
v___x_664_ = lean_apply_3(v_f_658_, v_left_663_, v_k_659_, v_v_660_);
v___x_665_ = lean_apply_4(v_toBind_661_, lean_box(0), lean_box(0), v___x_664_, v___f_662_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object* v_inst_666_, lean_object* v_f_667_, lean_object* v_init_668_, lean_object* v_x_669_){
_start:
{
if (lean_obj_tag(v_x_669_) == 0)
{
lean_object* v_toBind_670_; lean_object* v_k_671_; lean_object* v_v_672_; lean_object* v_l_673_; lean_object* v_r_674_; lean_object* v___f_675_; lean_object* v___f_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v_toBind_670_ = lean_ctor_get(v_inst_666_, 1);
lean_inc(v_toBind_670_);
v_k_671_ = lean_ctor_get(v_x_669_, 1);
lean_inc(v_k_671_);
v_v_672_ = lean_ctor_get(v_x_669_, 2);
lean_inc(v_v_672_);
v_l_673_ = lean_ctor_get(v_x_669_, 3);
lean_inc(v_l_673_);
v_r_674_ = lean_ctor_get(v_x_669_, 4);
lean_inc(v_r_674_);
lean_dec_ref(v_x_669_);
lean_inc(v_f_667_);
lean_inc_ref(v_inst_666_);
v___f_675_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_675_, 0, v_inst_666_);
lean_closure_set(v___f_675_, 1, v_f_667_);
lean_closure_set(v___f_675_, 2, v_r_674_);
lean_inc(v_toBind_670_);
lean_inc(v_f_667_);
v___f_676_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_676_, 0, v_f_667_);
lean_closure_set(v___f_676_, 1, v_k_671_);
lean_closure_set(v___f_676_, 2, v_v_672_);
lean_closure_set(v___f_676_, 3, v_toBind_670_);
lean_closure_set(v___f_676_, 4, v___f_675_);
v___x_677_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_666_, v_f_667_, v_init_668_, v_l_673_);
v___x_678_ = lean_apply_4(v_toBind_670_, lean_box(0), lean_box(0), v___x_677_, v___f_676_);
return v___x_678_;
}
else
{
lean_object* v_toApplicative_679_; lean_object* v_toPure_680_; lean_object* v___x_681_; 
v_toApplicative_679_ = lean_ctor_get(v_inst_666_, 0);
lean_inc_ref(v_toApplicative_679_);
lean_dec(v_f_667_);
lean_dec_ref(v_inst_666_);
v_toPure_680_ = lean_ctor_get(v_toApplicative_679_, 1);
lean_inc(v_toPure_680_);
lean_dec_ref(v_toApplicative_679_);
v___x_681_ = lean_apply_2(v_toPure_680_, lean_box(0), v_init_668_);
return v___x_681_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0(lean_object* v_inst_682_, lean_object* v_f_683_, lean_object* v_r_684_, lean_object* v_middle_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_682_, v_f_683_, v_middle_685_, v_r_684_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM(lean_object* v_00_u03b1_687_, lean_object* v_00_u03b2_688_, lean_object* v_00_u03b4_689_, lean_object* v_m_690_, lean_object* v_inst_691_, lean_object* v_f_692_, lean_object* v_init_693_, lean_object* v_x_694_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_691_, v_f_692_, v_init_693_, v_x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0(lean_object* v_f_696_, lean_object* v_x1_697_, lean_object* v_x2_698_, lean_object* v_x3_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = lean_apply_3(v_f_696_, v_x1_697_, v_x2_698_, v_x3_699_);
return v___x_700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object* v_f_720_, lean_object* v_init_721_, lean_object* v_t_722_){
_start:
{
lean_object* v___f_723_; lean_object* v___x_724_; lean_object* v___x_725_; 
v___f_723_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_723_, 0, v_f_720_);
v___x_724_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_725_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_724_, v___f_723_, v_init_721_, v_t_722_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl(lean_object* v_00_u03b1_726_, lean_object* v_00_u03b2_727_, lean_object* v_00_u03b4_728_, lean_object* v_f_729_, lean_object* v_init_730_, lean_object* v_t_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_729_, v_init_730_, v_t_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1(lean_object* v_f_733_, lean_object* v_k_734_, lean_object* v_v_735_, lean_object* v_toBind_736_, lean_object* v___f_737_, lean_object* v_right_738_){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = lean_apply_3(v_f_733_, v_k_734_, v_v_735_, v_right_738_);
v___x_740_ = lean_apply_4(v_toBind_736_, lean_box(0), lean_box(0), v___x_739_, v___f_737_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object* v_inst_741_, lean_object* v_f_742_, lean_object* v_init_743_, lean_object* v_x_744_){
_start:
{
if (lean_obj_tag(v_x_744_) == 0)
{
lean_object* v_toBind_745_; lean_object* v_k_746_; lean_object* v_v_747_; lean_object* v_l_748_; lean_object* v_r_749_; lean_object* v___f_750_; lean_object* v___f_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_toBind_745_ = lean_ctor_get(v_inst_741_, 1);
lean_inc(v_toBind_745_);
v_k_746_ = lean_ctor_get(v_x_744_, 1);
lean_inc(v_k_746_);
v_v_747_ = lean_ctor_get(v_x_744_, 2);
lean_inc(v_v_747_);
v_l_748_ = lean_ctor_get(v_x_744_, 3);
lean_inc(v_l_748_);
v_r_749_ = lean_ctor_get(v_x_744_, 4);
lean_inc(v_r_749_);
lean_dec_ref(v_x_744_);
lean_inc(v_f_742_);
lean_inc_ref(v_inst_741_);
v___f_750_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_750_, 0, v_inst_741_);
lean_closure_set(v___f_750_, 1, v_f_742_);
lean_closure_set(v___f_750_, 2, v_l_748_);
lean_inc(v_toBind_745_);
lean_inc(v_f_742_);
v___f_751_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_751_, 0, v_f_742_);
lean_closure_set(v___f_751_, 1, v_k_746_);
lean_closure_set(v___f_751_, 2, v_v_747_);
lean_closure_set(v___f_751_, 3, v_toBind_745_);
lean_closure_set(v___f_751_, 4, v___f_750_);
v___x_752_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_741_, v_f_742_, v_init_743_, v_r_749_);
v___x_753_ = lean_apply_4(v_toBind_745_, lean_box(0), lean_box(0), v___x_752_, v___f_751_);
return v___x_753_;
}
else
{
lean_object* v_toApplicative_754_; lean_object* v_toPure_755_; lean_object* v___x_756_; 
v_toApplicative_754_ = lean_ctor_get(v_inst_741_, 0);
lean_inc_ref(v_toApplicative_754_);
lean_dec(v_f_742_);
lean_dec_ref(v_inst_741_);
v_toPure_755_ = lean_ctor_get(v_toApplicative_754_, 1);
lean_inc(v_toPure_755_);
lean_dec_ref(v_toApplicative_754_);
v___x_756_ = lean_apply_2(v_toPure_755_, lean_box(0), v_init_743_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0(lean_object* v_inst_757_, lean_object* v_f_758_, lean_object* v_l_759_, lean_object* v_middle_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_757_, v_f_758_, v_middle_760_, v_l_759_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_00_u03b4_764_, lean_object* v_m_765_, lean_object* v_inst_766_, lean_object* v_f_767_, lean_object* v_init_768_, lean_object* v_x_769_){
_start:
{
lean_object* v___x_770_; 
v___x_770_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_766_, v_f_767_, v_init_768_, v_x_769_);
return v___x_770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr___redArg(lean_object* v_f_771_, lean_object* v_init_772_, lean_object* v_t_773_){
_start:
{
lean_object* v___f_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___f_774_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_774_, 0, v_f_771_);
v___x_775_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_776_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_775_, v___f_774_, v_init_772_, v_t_773_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr(lean_object* v_00_u03b1_777_, lean_object* v_00_u03b2_778_, lean_object* v_00_u03b4_779_, lean_object* v_f_780_, lean_object* v_init_781_, lean_object* v_t_782_){
_start:
{
lean_object* v___f_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___f_783_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_783_, 0, v_f_780_);
v___x_784_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_785_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_784_, v___f_783_, v_init_781_, v_t_782_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0(lean_object* v_f_786_, lean_object* v_x_787_, lean_object* v_k_788_, lean_object* v_v_789_){
_start:
{
lean_object* v___x_790_; 
v___x_790_ = lean_apply_2(v_f_786_, v_k_788_, v_v_789_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg(lean_object* v_inst_791_, lean_object* v_f_792_, lean_object* v_t_793_){
_start:
{
lean_object* v___f_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___f_794_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_794_, 0, v_f_792_);
v___x_795_ = lean_box(0);
v___x_796_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_791_, v___f_794_, v___x_795_, v_t_793_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM(lean_object* v_00_u03b1_797_, lean_object* v_00_u03b2_798_, lean_object* v_m_799_, lean_object* v_inst_800_, lean_object* v_f_801_, lean_object* v_t_802_){
_start:
{
lean_object* v___f_803_; lean_object* v___x_804_; lean_object* v___x_805_; 
v___f_803_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_803_, 0, v_f_801_);
v___x_804_ = lean_box(0);
v___x_805_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_800_, v___f_803_, v___x_804_, v_t_802_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0(lean_object* v_toPure_806_, lean_object* v_d_807_){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_808_, 0, v_d_807_);
v___x_809_ = lean_apply_2(v_toPure_806_, lean_box(0), v___x_808_);
return v___x_809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2(lean_object* v___f_810_, lean_object* v_f_811_, lean_object* v_k_812_, lean_object* v_v_813_, lean_object* v_toBind_814_, lean_object* v___f_815_, lean_object* v_____do__lift_816_){
_start:
{
if (lean_obj_tag(v_____do__lift_816_) == 0)
{
lean_object* v_a_817_; lean_object* v___x_818_; 
lean_dec(v___f_815_);
lean_dec(v_toBind_814_);
lean_dec(v_v_813_);
lean_dec(v_k_812_);
lean_dec(v_f_811_);
v_a_817_ = lean_ctor_get(v_____do__lift_816_, 0);
lean_inc(v_a_817_);
lean_dec_ref(v_____do__lift_816_);
v___x_818_ = lean_apply_1(v___f_810_, v_a_817_);
return v___x_818_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec(v___f_810_);
v_a_819_ = lean_ctor_get(v_____do__lift_816_, 0);
lean_inc(v_a_819_);
lean_dec_ref(v_____do__lift_816_);
v___x_820_ = lean_apply_3(v_f_811_, v_k_812_, v_v_813_, v_a_819_);
v___x_821_ = lean_apply_4(v_toBind_814_, lean_box(0), lean_box(0), v___x_820_, v___f_815_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object* v_inst_822_, lean_object* v_f_823_, lean_object* v_init_824_, lean_object* v_x_825_){
_start:
{
if (lean_obj_tag(v_x_825_) == 0)
{
lean_object* v_toApplicative_826_; lean_object* v_toBind_827_; lean_object* v_toPure_828_; lean_object* v_k_829_; lean_object* v_v_830_; lean_object* v_l_831_; lean_object* v_r_832_; lean_object* v___f_833_; lean_object* v___f_834_; lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v_toApplicative_826_ = lean_ctor_get(v_inst_822_, 0);
v_toBind_827_ = lean_ctor_get(v_inst_822_, 1);
lean_inc(v_toBind_827_);
v_toPure_828_ = lean_ctor_get(v_toApplicative_826_, 1);
v_k_829_ = lean_ctor_get(v_x_825_, 1);
lean_inc(v_k_829_);
v_v_830_ = lean_ctor_get(v_x_825_, 2);
lean_inc(v_v_830_);
v_l_831_ = lean_ctor_get(v_x_825_, 3);
lean_inc(v_l_831_);
v_r_832_ = lean_ctor_get(v_x_825_, 4);
lean_inc(v_r_832_);
lean_dec_ref(v_x_825_);
lean_inc(v_toPure_828_);
v___f_833_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0), 2, 1);
lean_closure_set(v___f_833_, 0, v_toPure_828_);
lean_inc(v_f_823_);
lean_inc_ref(v_inst_822_);
lean_inc_ref(v___f_833_);
v___f_834_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1), 5, 4);
lean_closure_set(v___f_834_, 0, v___f_833_);
lean_closure_set(v___f_834_, 1, v_inst_822_);
lean_closure_set(v___f_834_, 2, v_f_823_);
lean_closure_set(v___f_834_, 3, v_r_832_);
lean_inc(v_toBind_827_);
lean_inc(v_f_823_);
v___f_835_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2), 7, 6);
lean_closure_set(v___f_835_, 0, v___f_833_);
lean_closure_set(v___f_835_, 1, v_f_823_);
lean_closure_set(v___f_835_, 2, v_k_829_);
lean_closure_set(v___f_835_, 3, v_v_830_);
lean_closure_set(v___f_835_, 4, v_toBind_827_);
lean_closure_set(v___f_835_, 5, v___f_834_);
v___x_836_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_822_, v_f_823_, v_init_824_, v_l_831_);
v___x_837_ = lean_apply_4(v_toBind_827_, lean_box(0), lean_box(0), v___x_836_, v___f_835_);
return v___x_837_;
}
else
{
lean_object* v_toApplicative_838_; lean_object* v_toPure_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_toApplicative_838_ = lean_ctor_get(v_inst_822_, 0);
lean_inc_ref(v_toApplicative_838_);
lean_dec(v_f_823_);
lean_dec_ref(v_inst_822_);
v_toPure_839_ = lean_ctor_get(v_toApplicative_838_, 1);
lean_inc(v_toPure_839_);
lean_dec_ref(v_toApplicative_838_);
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v_init_824_);
v___x_841_ = lean_apply_2(v_toPure_839_, lean_box(0), v___x_840_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1(lean_object* v___f_842_, lean_object* v_inst_843_, lean_object* v_f_844_, lean_object* v_r_845_, lean_object* v_____do__lift_846_){
_start:
{
if (lean_obj_tag(v_____do__lift_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___x_848_; 
lean_dec(v_r_845_);
lean_dec(v_f_844_);
lean_dec_ref(v_inst_843_);
v_a_847_ = lean_ctor_get(v_____do__lift_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref(v_____do__lift_846_);
v___x_848_ = lean_apply_1(v___f_842_, v_a_847_);
return v___x_848_;
}
else
{
lean_object* v_a_849_; lean_object* v___x_850_; 
lean_dec(v___f_842_);
v_a_849_ = lean_ctor_get(v_____do__lift_846_, 0);
lean_inc(v_a_849_);
lean_dec_ref(v_____do__lift_846_);
v___x_850_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_843_, v_f_844_, v_a_849_, v_r_845_);
return v___x_850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep(lean_object* v_00_u03b1_851_, lean_object* v_00_u03b2_852_, lean_object* v_00_u03b4_853_, lean_object* v_m_854_, lean_object* v_inst_855_, lean_object* v_f_856_, lean_object* v_init_857_, lean_object* v_x_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_855_, v_f_856_, v_init_857_, v_x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0(lean_object* v_toPure_860_, lean_object* v_____do__lift_861_){
_start:
{
lean_object* v_a_862_; lean_object* v___x_863_; 
v_a_862_ = lean_ctor_get(v_____do__lift_861_, 0);
lean_inc(v_a_862_);
lean_dec_ref(v_____do__lift_861_);
v___x_863_ = lean_apply_2(v_toPure_860_, lean_box(0), v_a_862_);
return v___x_863_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg(lean_object* v_inst_864_, lean_object* v_f_865_, lean_object* v_init_866_, lean_object* v_t_867_){
_start:
{
lean_object* v_toApplicative_868_; lean_object* v_toBind_869_; lean_object* v_toPure_870_; lean_object* v___x_871_; lean_object* v___f_872_; lean_object* v___x_873_; 
v_toApplicative_868_ = lean_ctor_get(v_inst_864_, 0);
v_toBind_869_ = lean_ctor_get(v_inst_864_, 1);
lean_inc(v_toBind_869_);
v_toPure_870_ = lean_ctor_get(v_toApplicative_868_, 1);
lean_inc(v_toPure_870_);
v___x_871_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_864_, v_f_865_, v_init_866_, v_t_867_);
v___f_872_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_872_, 0, v_toPure_870_);
v___x_873_ = lean_apply_4(v_toBind_869_, lean_box(0), lean_box(0), v___x_871_, v___f_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn(lean_object* v_00_u03b1_874_, lean_object* v_00_u03b2_875_, lean_object* v_00_u03b4_876_, lean_object* v_m_877_, lean_object* v_inst_878_, lean_object* v_f_879_, lean_object* v_init_880_, lean_object* v_t_881_){
_start:
{
lean_object* v_toApplicative_882_; lean_object* v_toBind_883_; lean_object* v_toPure_884_; lean_object* v___x_885_; lean_object* v___f_886_; lean_object* v___x_887_; 
v_toApplicative_882_ = lean_ctor_get(v_inst_878_, 0);
v_toBind_883_ = lean_ctor_get(v_inst_878_, 1);
lean_inc(v_toBind_883_);
v_toPure_884_ = lean_ctor_get(v_toApplicative_882_, 1);
lean_inc(v_toPure_884_);
v___x_885_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_878_, v_f_879_, v_init_880_, v_t_881_);
v___f_886_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_886_, 0, v_toPure_884_);
v___x_887_ = lean_apply_4(v_toBind_883_, lean_box(0), lean_box(0), v___x_885_, v___f_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_888_, lean_object* v_a_889_, lean_object* v_b_890_, lean_object* v_acc_891_){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_892_, 0, v_a_889_);
lean_ctor_set(v___x_892_, 1, v_b_890_);
v___x_893_ = lean_apply_2(v_f_888_, v___x_892_, v_acc_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_894_, lean_object* v_00_u03b2_895_, lean_object* v_m_896_, lean_object* v_init_897_, lean_object* v_f_898_){
_start:
{
lean_object* v_toApplicative_899_; lean_object* v_toBind_900_; lean_object* v_toPure_901_; lean_object* v___f_902_; lean_object* v___x_903_; lean_object* v___f_904_; lean_object* v___x_905_; 
v_toApplicative_899_ = lean_ctor_get(v_inst_894_, 0);
v_toBind_900_ = lean_ctor_get(v_inst_894_, 1);
lean_inc(v_toBind_900_);
v_toPure_901_ = lean_ctor_get(v_toApplicative_899_, 1);
lean_inc(v_toPure_901_);
v___f_902_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_902_, 0, v_f_898_);
v___x_903_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_894_, v___f_902_, v_init_897_, v_m_896_);
v___f_904_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_904_, 0, v_toPure_901_);
v___x_905_ = lean_apply_4(v_toBind_900_, lean_box(0), lean_box(0), v___x_903_, v___f_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg(lean_object* v_inst_906_){
_start:
{
lean_object* v___f_907_; 
v___f_907_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_907_, 0, v_inst_906_);
return v___f_907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad(lean_object* v_00_u03b1_908_, lean_object* v_00_u03b2_909_, lean_object* v_m_910_, lean_object* v_inst_911_){
_start:
{
lean_object* v___f_912_; 
v___f_912_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_912_, 0, v_inst_911_);
return v___f_912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(lean_object* v_p_913_, lean_object* v___x_914_, lean_object* v___x_915_, lean_object* v_a_916_, lean_object* v_b_917_, lean_object* v_acc_918_){
_start:
{
lean_object* v___x_919_; uint8_t v___x_920_; 
v___x_919_ = lean_apply_2(v_p_913_, v_a_916_, v_b_917_);
v___x_920_ = lean_unbox(v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
v___x_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_914_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec_ref(v___x_914_);
v___x_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_919_);
v___x_923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v___x_915_);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed(lean_object* v_p_925_, lean_object* v___x_926_, lean_object* v___x_927_, lean_object* v_a_928_, lean_object* v_b_929_, lean_object* v_acc_930_){
_start:
{
lean_object* v_res_931_; 
v_res_931_ = l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(v_p_925_, v___x_926_, v___x_927_, v_a_928_, v_b_929_, v_acc_930_);
lean_dec_ref(v_acc_930_);
return v_res_931_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any___redArg(lean_object* v_t_935_, lean_object* v_p_936_){
_start:
{
lean_object* v___y_938_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___f_946_; lean_object* v___x_947_; lean_object* v_a_948_; 
v___x_943_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_944_ = lean_box(0);
v___x_945_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_946_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_946_, 0, v_p_936_);
lean_closure_set(v___f_946_, 1, v___x_945_);
lean_closure_set(v___f_946_, 2, v___x_944_);
v___x_947_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_943_, v___f_946_, v___x_945_, v_t_935_);
v_a_948_ = lean_ctor_get(v___x_947_, 0);
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___y_938_ = v_a_948_;
goto v___jp_937_;
v___jp_937_:
{
lean_object* v_fst_939_; 
v_fst_939_ = lean_ctor_get(v___y_938_, 0);
lean_inc(v_fst_939_);
lean_dec_ref(v___y_938_);
if (lean_obj_tag(v_fst_939_) == 0)
{
uint8_t v___x_940_; 
v___x_940_ = 0;
return v___x_940_;
}
else
{
lean_object* v_val_941_; uint8_t v___x_942_; 
v_val_941_ = lean_ctor_get(v_fst_939_, 0);
lean_inc(v_val_941_);
lean_dec_ref(v_fst_939_);
v___x_942_ = lean_unbox(v_val_941_);
lean_dec(v_val_941_);
return v___x_942_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___boxed(lean_object* v_t_949_, lean_object* v_p_950_){
_start:
{
uint8_t v_res_951_; lean_object* v_r_952_; 
v_res_951_ = l_Std_DTreeMap_Internal_Impl_any___redArg(v_t_949_, v_p_950_);
v_r_952_ = lean_box(v_res_951_);
return v_r_952_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any(lean_object* v_00_u03b1_953_, lean_object* v_00_u03b2_954_, lean_object* v_t_955_, lean_object* v_p_956_){
_start:
{
lean_object* v___y_958_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___f_966_; lean_object* v___x_967_; lean_object* v_a_968_; 
v___x_963_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_964_ = lean_box(0);
v___x_965_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_966_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_966_, 0, v_p_956_);
lean_closure_set(v___f_966_, 1, v___x_965_);
lean_closure_set(v___f_966_, 2, v___x_964_);
v___x_967_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_963_, v___f_966_, v___x_965_, v_t_955_);
v_a_968_ = lean_ctor_get(v___x_967_, 0);
lean_inc(v_a_968_);
lean_dec(v___x_967_);
v___y_958_ = v_a_968_;
goto v___jp_957_;
v___jp_957_:
{
lean_object* v_fst_959_; 
v_fst_959_ = lean_ctor_get(v___y_958_, 0);
lean_inc(v_fst_959_);
lean_dec_ref(v___y_958_);
if (lean_obj_tag(v_fst_959_) == 0)
{
uint8_t v___x_960_; 
v___x_960_ = 0;
return v___x_960_;
}
else
{
lean_object* v_val_961_; uint8_t v___x_962_; 
v_val_961_ = lean_ctor_get(v_fst_959_, 0);
lean_inc(v_val_961_);
lean_dec_ref(v_fst_959_);
v___x_962_ = lean_unbox(v_val_961_);
lean_dec(v_val_961_);
return v___x_962_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___boxed(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_t_971_, lean_object* v_p_972_){
_start:
{
uint8_t v_res_973_; lean_object* v_r_974_; 
v_res_973_ = l_Std_DTreeMap_Internal_Impl_any(v_00_u03b1_969_, v_00_u03b2_970_, v_t_971_, v_p_972_);
v_r_974_ = lean_box(v_res_973_);
return v_r_974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(lean_object* v_p_975_, lean_object* v___x_976_, lean_object* v___x_977_, lean_object* v_a_978_, lean_object* v_b_979_, lean_object* v_acc_980_){
_start:
{
lean_object* v___x_981_; uint8_t v___x_982_; 
v___x_981_ = lean_apply_2(v_p_975_, v_a_978_, v_b_979_);
v___x_982_ = lean_unbox(v___x_981_);
if (v___x_982_ == 0)
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec_ref(v___x_977_);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_981_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_976_);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
else
{
lean_object* v___x_986_; 
v___x_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_977_);
return v___x_986_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed(lean_object* v_p_987_, lean_object* v___x_988_, lean_object* v___x_989_, lean_object* v_a_990_, lean_object* v_b_991_, lean_object* v_acc_992_){
_start:
{
lean_object* v_res_993_; 
v_res_993_ = l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(v_p_987_, v___x_988_, v___x_989_, v_a_990_, v_b_991_, v_acc_992_);
lean_dec_ref(v_acc_992_);
return v_res_993_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all___redArg(lean_object* v_t_994_, lean_object* v_p_995_){
_start:
{
lean_object* v___y_997_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___f_1005_; lean_object* v___x_1006_; lean_object* v_a_1007_; 
v___x_1002_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1003_ = lean_box(0);
v___x_1004_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1005_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1005_, 0, v_p_995_);
lean_closure_set(v___f_1005_, 1, v___x_1003_);
lean_closure_set(v___f_1005_, 2, v___x_1004_);
v___x_1006_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1002_, v___f_1005_, v___x_1004_, v_t_994_);
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___y_997_ = v_a_1007_;
goto v___jp_996_;
v___jp_996_:
{
lean_object* v_fst_998_; 
v_fst_998_ = lean_ctor_get(v___y_997_, 0);
lean_inc(v_fst_998_);
lean_dec_ref(v___y_997_);
if (lean_obj_tag(v_fst_998_) == 0)
{
uint8_t v___x_999_; 
v___x_999_ = 1;
return v___x_999_;
}
else
{
lean_object* v_val_1000_; uint8_t v___x_1001_; 
v_val_1000_ = lean_ctor_get(v_fst_998_, 0);
lean_inc(v_val_1000_);
lean_dec_ref(v_fst_998_);
v___x_1001_ = lean_unbox(v_val_1000_);
lean_dec(v_val_1000_);
return v___x_1001_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___boxed(lean_object* v_t_1008_, lean_object* v_p_1009_){
_start:
{
uint8_t v_res_1010_; lean_object* v_r_1011_; 
v_res_1010_ = l_Std_DTreeMap_Internal_Impl_all___redArg(v_t_1008_, v_p_1009_);
v_r_1011_ = lean_box(v_res_1010_);
return v_r_1011_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all(lean_object* v_00_u03b1_1012_, lean_object* v_00_u03b2_1013_, lean_object* v_t_1014_, lean_object* v_p_1015_){
_start:
{
lean_object* v___y_1017_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___f_1025_; lean_object* v___x_1026_; lean_object* v_a_1027_; 
v___x_1022_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1023_ = lean_box(0);
v___x_1024_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1025_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1025_, 0, v_p_1015_);
lean_closure_set(v___f_1025_, 1, v___x_1023_);
lean_closure_set(v___f_1025_, 2, v___x_1024_);
v___x_1026_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1022_, v___f_1025_, v___x_1024_, v_t_1014_);
v_a_1027_ = lean_ctor_get(v___x_1026_, 0);
lean_inc(v_a_1027_);
lean_dec(v___x_1026_);
v___y_1017_ = v_a_1027_;
goto v___jp_1016_;
v___jp_1016_:
{
lean_object* v_fst_1018_; 
v_fst_1018_ = lean_ctor_get(v___y_1017_, 0);
lean_inc(v_fst_1018_);
lean_dec_ref(v___y_1017_);
if (lean_obj_tag(v_fst_1018_) == 0)
{
uint8_t v___x_1019_; 
v___x_1019_ = 1;
return v___x_1019_;
}
else
{
lean_object* v_val_1020_; uint8_t v___x_1021_; 
v_val_1020_ = lean_ctor_get(v_fst_1018_, 0);
lean_inc(v_val_1020_);
lean_dec_ref(v_fst_1018_);
v___x_1021_ = lean_unbox(v_val_1020_);
lean_dec(v_val_1020_);
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___boxed(lean_object* v_00_u03b1_1028_, lean_object* v_00_u03b2_1029_, lean_object* v_t_1030_, lean_object* v_p_1031_){
_start:
{
uint8_t v_res_1032_; lean_object* v_r_1033_; 
v_res_1032_ = l_Std_DTreeMap_Internal_Impl_all(v_00_u03b1_1028_, v_00_u03b2_1029_, v_t_1030_, v_p_1031_);
v_r_1033_ = lean_box(v_res_1032_);
return v_r_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(lean_object* v_x1_1034_, lean_object* v_x2_1035_, lean_object* v_x3_1036_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1037_, 0, v_x1_1034_);
lean_ctor_set(v___x_1037_, 1, v_x3_1036_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0___boxed(lean_object* v_x1_1038_, lean_object* v_x2_1039_, lean_object* v_x3_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(v_x1_1038_, v_x2_1039_, v_x3_1040_);
lean_dec(v_x2_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg(lean_object* v_t_1043_){
_start:
{
lean_object* v___f_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___f_1044_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1045_ = lean_box(0);
v___x_1046_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1047_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1046_, v___f_1044_, v___x_1045_, v_t_1043_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys(lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_t_1050_){
_start:
{
lean_object* v___f_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___f_1051_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1052_ = lean_box(0);
v___x_1053_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1054_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1053_, v___f_1051_, v___x_1052_, v_t_1050_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(lean_object* v_l_1055_, lean_object* v_k_1056_, lean_object* v_x_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = lean_array_push(v_l_1055_, v_k_1056_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0___boxed(lean_object* v_l_1059_, lean_object* v_k_1060_, lean_object* v_x_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(v_l_1059_, v_k_1060_, v_x_1061_);
lean_dec(v_x_1061_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg(lean_object* v_t_1064_){
_start:
{
lean_object* v___f_1065_; lean_object* v___y_1067_; 
v___f_1065_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1064_) == 0)
{
lean_object* v_size_1070_; 
v_size_1070_ = lean_ctor_get(v_t_1064_, 0);
lean_inc(v_size_1070_);
v___y_1067_ = v_size_1070_;
goto v___jp_1066_;
}
else
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_unsigned_to_nat(0u);
v___y_1067_ = v___x_1071_;
goto v___jp_1066_;
}
v___jp_1066_:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = lean_mk_empty_array_with_capacity(v___y_1067_);
lean_dec(v___y_1067_);
v___x_1069_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1065_, v___x_1068_, v_t_1064_);
return v___x_1069_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray(lean_object* v_00_u03b1_1072_, lean_object* v_00_u03b2_1073_, lean_object* v_t_1074_){
_start:
{
lean_object* v___f_1075_; lean_object* v___y_1077_; 
v___f_1075_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1074_) == 0)
{
lean_object* v_size_1080_; 
v_size_1080_ = lean_ctor_get(v_t_1074_, 0);
lean_inc(v_size_1080_);
v___y_1077_ = v_size_1080_;
goto v___jp_1076_;
}
else
{
lean_object* v___x_1081_; 
v___x_1081_ = lean_unsigned_to_nat(0u);
v___y_1077_ = v___x_1081_;
goto v___jp_1076_;
}
v___jp_1076_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1078_ = lean_mk_empty_array_with_capacity(v___y_1077_);
lean_dec(v___y_1077_);
v___x_1079_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1075_, v___x_1078_, v_t_1074_);
return v___x_1079_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(lean_object* v_x1_1082_, lean_object* v_x2_1083_, lean_object* v_x3_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_x2_1083_);
lean_ctor_set(v___x_1085_, 1, v_x3_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0___boxed(lean_object* v_x1_1086_, lean_object* v_x2_1087_, lean_object* v_x3_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(v_x1_1086_, v_x2_1087_, v_x3_1088_);
lean_dec(v_x1_1086_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg(lean_object* v_t_1091_){
_start:
{
lean_object* v___f_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___f_1092_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1093_ = lean_box(0);
v___x_1094_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1095_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1094_, v___f_1092_, v___x_1093_, v_t_1091_);
return v___x_1095_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values(lean_object* v_00_u03b1_1096_, lean_object* v_00_u03b2_1097_, lean_object* v_t_1098_){
_start:
{
lean_object* v___f_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___f_1099_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1100_ = lean_box(0);
v___x_1101_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1102_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1101_, v___f_1099_, v___x_1100_, v_t_1098_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(lean_object* v_l_1103_, lean_object* v_x_1104_, lean_object* v_v_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_array_push(v_l_1103_, v_v_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0___boxed(lean_object* v_l_1107_, lean_object* v_x_1108_, lean_object* v_v_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(v_l_1107_, v_x_1108_, v_v_1109_);
lean_dec(v_x_1108_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg(lean_object* v_t_1112_){
_start:
{
lean_object* v___f_1113_; lean_object* v___y_1115_; 
v___f_1113_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1112_) == 0)
{
lean_object* v_size_1118_; 
v_size_1118_ = lean_ctor_get(v_t_1112_, 0);
lean_inc(v_size_1118_);
v___y_1115_ = v_size_1118_;
goto v___jp_1114_;
}
else
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_unsigned_to_nat(0u);
v___y_1115_ = v___x_1119_;
goto v___jp_1114_;
}
v___jp_1114_:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = lean_mk_empty_array_with_capacity(v___y_1115_);
lean_dec(v___y_1115_);
v___x_1117_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1113_, v___x_1116_, v_t_1112_);
return v___x_1117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray(lean_object* v_00_u03b1_1120_, lean_object* v_00_u03b2_1121_, lean_object* v_t_1122_){
_start:
{
lean_object* v___f_1123_; lean_object* v___y_1125_; 
v___f_1123_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1122_) == 0)
{
lean_object* v_size_1128_; 
v_size_1128_ = lean_ctor_get(v_t_1122_, 0);
lean_inc(v_size_1128_);
v___y_1125_ = v_size_1128_;
goto v___jp_1124_;
}
else
{
lean_object* v___x_1129_; 
v___x_1129_ = lean_unsigned_to_nat(0u);
v___y_1125_ = v___x_1129_;
goto v___jp_1124_;
}
v___jp_1124_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1126_ = lean_mk_empty_array_with_capacity(v___y_1125_);
lean_dec(v___y_1125_);
v___x_1127_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1123_, v___x_1126_, v_t_1122_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg___lam__0(lean_object* v_x1_1130_, lean_object* v_x2_1131_, lean_object* v_x3_1132_){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v_x1_1130_);
lean_ctor_set(v___x_1133_, 1, v_x2_1131_);
v___x_1134_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
lean_ctor_set(v___x_1134_, 1, v_x3_1132_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg(lean_object* v_t_1136_){
_start:
{
lean_object* v___f_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___f_1137_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1138_ = lean_box(0);
v___x_1139_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1140_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1139_, v___f_1137_, v___x_1138_, v_t_1136_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList(lean_object* v_00_u03b1_1141_, lean_object* v_00_u03b2_1142_, lean_object* v_t_1143_){
_start:
{
lean_object* v___f_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___f_1144_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1145_ = lean_box(0);
v___x_1146_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1147_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1146_, v___f_1144_, v___x_1145_, v_t_1143_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg___lam__0(lean_object* v_l_1148_, lean_object* v_k_1149_, lean_object* v_v_1150_){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v_k_1149_);
lean_ctor_set(v___x_1151_, 1, v_v_1150_);
v___x_1152_ = lean_array_push(v_l_1148_, v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg(lean_object* v_t_1154_){
_start:
{
lean_object* v___f_1155_; lean_object* v___y_1157_; 
v___f_1155_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1154_) == 0)
{
lean_object* v_size_1160_; 
v_size_1160_ = lean_ctor_get(v_t_1154_, 0);
lean_inc(v_size_1160_);
v___y_1157_ = v_size_1160_;
goto v___jp_1156_;
}
else
{
lean_object* v___x_1161_; 
v___x_1161_ = lean_unsigned_to_nat(0u);
v___y_1157_ = v___x_1161_;
goto v___jp_1156_;
}
v___jp_1156_:
{
lean_object* v___x_1158_; lean_object* v___x_1159_; 
v___x_1158_ = lean_mk_empty_array_with_capacity(v___y_1157_);
lean_dec(v___y_1157_);
v___x_1159_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1155_, v___x_1158_, v_t_1154_);
return v___x_1159_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray(lean_object* v_00_u03b1_1162_, lean_object* v_00_u03b2_1163_, lean_object* v_t_1164_){
_start:
{
lean_object* v___f_1165_; lean_object* v___y_1167_; 
v___f_1165_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1164_) == 0)
{
lean_object* v_size_1170_; 
v_size_1170_ = lean_ctor_get(v_t_1164_, 0);
lean_inc(v_size_1170_);
v___y_1167_ = v_size_1170_;
goto v___jp_1166_;
}
else
{
lean_object* v___x_1171_; 
v___x_1171_ = lean_unsigned_to_nat(0u);
v___y_1167_ = v___x_1171_;
goto v___jp_1166_;
}
v___jp_1166_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_mk_empty_array_with_capacity(v___y_1167_);
lean_dec(v___y_1167_);
v___x_1169_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1165_, v___x_1168_, v_t_1164_);
return v___x_1169_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___lam__0(lean_object* v_x1_1172_, lean_object* v_x2_1173_, lean_object* v_x3_1174_){
_start:
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___x_1175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1175_, 0, v_x1_1172_);
lean_ctor_set(v___x_1175_, 1, v_x2_1173_);
v___x_1176_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1176_, 0, v___x_1175_);
lean_ctor_set(v___x_1176_, 1, v_x3_1174_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg(lean_object* v_t_1178_){
_start:
{
lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___f_1179_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1180_ = lean_box(0);
v___x_1181_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1182_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1181_, v___f_1179_, v___x_1180_, v_t_1178_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList(lean_object* v_00_u03b1_1183_, lean_object* v_00_u03b2_1184_, lean_object* v_t_1185_){
_start:
{
lean_object* v___f_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___f_1186_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1187_ = lean_box(0);
v___x_1188_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1188_, v___f_1186_, v___x_1187_, v_t_1185_);
return v___x_1189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___lam__0(lean_object* v_l_1190_, lean_object* v_k_1191_, lean_object* v_v_1192_){
_start:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v_k_1191_);
lean_ctor_set(v___x_1193_, 1, v_v_1192_);
v___x_1194_ = lean_array_push(v_l_1190_, v___x_1193_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg(lean_object* v_t_1196_){
_start:
{
lean_object* v___f_1197_; lean_object* v___y_1199_; 
v___f_1197_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1196_) == 0)
{
lean_object* v_size_1202_; 
v_size_1202_ = lean_ctor_get(v_t_1196_, 0);
lean_inc(v_size_1202_);
v___y_1199_ = v_size_1202_;
goto v___jp_1198_;
}
else
{
lean_object* v___x_1203_; 
v___x_1203_ = lean_unsigned_to_nat(0u);
v___y_1199_ = v___x_1203_;
goto v___jp_1198_;
}
v___jp_1198_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = lean_mk_empty_array_with_capacity(v___y_1199_);
lean_dec(v___y_1199_);
v___x_1201_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1197_, v___x_1200_, v_t_1196_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray(lean_object* v_00_u03b1_1204_, lean_object* v_00_u03b2_1205_, lean_object* v_t_1206_){
_start:
{
lean_object* v___f_1207_; lean_object* v___y_1209_; 
v___f_1207_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1206_) == 0)
{
lean_object* v_size_1212_; 
v_size_1212_ = lean_ctor_get(v_t_1206_, 0);
lean_inc(v_size_1212_);
v___y_1209_ = v_size_1212_;
goto v___jp_1208_;
}
else
{
lean_object* v___x_1213_; 
v___x_1213_ = lean_unsigned_to_nat(0u);
v___y_1209_ = v___x_1213_;
goto v___jp_1208_;
}
v___jp_1208_:
{
lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1210_ = lean_mk_empty_array_with_capacity(v___y_1209_);
lean_dec(v___y_1209_);
v___x_1211_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1207_, v___x_1210_, v_t_1206_);
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object* v_x_1214_){
_start:
{
if (lean_obj_tag(v_x_1214_) == 0)
{
lean_object* v_l_1215_; 
v_l_1215_ = lean_ctor_get(v_x_1214_, 3);
if (lean_obj_tag(v_l_1215_) == 0)
{
v_x_1214_ = v_l_1215_;
goto _start;
}
else
{
lean_object* v_k_1217_; lean_object* v_v_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; 
v_k_1217_ = lean_ctor_get(v_x_1214_, 1);
v_v_1218_ = lean_ctor_get(v_x_1214_, 2);
lean_inc(v_v_1218_);
lean_inc(v_k_1217_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v_k_1217_);
lean_ctor_set(v___x_1219_, 1, v_v_1218_);
v___x_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1219_);
return v___x_1220_;
}
}
else
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_box(0);
return v___x_1221_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg___boxed(lean_object* v_x_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1222_);
lean_dec(v_x_1222_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f(lean_object* v_00_u03b1_1224_, lean_object* v_00_u03b2_1225_, lean_object* v_x_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___boxed(lean_object* v_00_u03b1_1228_, lean_object* v_00_u03b2_1229_, lean_object* v_x_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f(v_00_u03b1_1228_, v_00_u03b2_1229_, v_x_1230_);
lean_dec(v_x_1230_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1232_, lean_object* v_h__1_1233_, lean_object* v_h__2_1234_, lean_object* v_h__3_1235_){
_start:
{
if (lean_obj_tag(v_x_1232_) == 0)
{
lean_object* v_l_1236_; 
lean_dec(v_h__1_1233_);
v_l_1236_ = lean_ctor_get(v_x_1232_, 3);
if (lean_obj_tag(v_l_1236_) == 0)
{
lean_object* v_size_1237_; lean_object* v_k_1238_; lean_object* v_v_1239_; lean_object* v_r_1240_; lean_object* v_size_1241_; lean_object* v_k_1242_; lean_object* v_v_1243_; lean_object* v_l_1244_; lean_object* v_r_1245_; lean_object* v___x_1246_; 
lean_inc_ref(v_l_1236_);
lean_dec(v_h__2_1234_);
v_size_1237_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_size_1237_);
v_k_1238_ = lean_ctor_get(v_x_1232_, 1);
lean_inc(v_k_1238_);
v_v_1239_ = lean_ctor_get(v_x_1232_, 2);
lean_inc(v_v_1239_);
v_r_1240_ = lean_ctor_get(v_x_1232_, 4);
lean_inc(v_r_1240_);
lean_dec_ref(v_x_1232_);
v_size_1241_ = lean_ctor_get(v_l_1236_, 0);
lean_inc(v_size_1241_);
v_k_1242_ = lean_ctor_get(v_l_1236_, 1);
lean_inc(v_k_1242_);
v_v_1243_ = lean_ctor_get(v_l_1236_, 2);
lean_inc(v_v_1243_);
v_l_1244_ = lean_ctor_get(v_l_1236_, 3);
lean_inc(v_l_1244_);
v_r_1245_ = lean_ctor_get(v_l_1236_, 4);
lean_inc(v_r_1245_);
lean_dec_ref(v_l_1236_);
v___x_1246_ = lean_apply_9(v_h__3_1235_, v_size_1237_, v_k_1238_, v_v_1239_, v_size_1241_, v_k_1242_, v_v_1243_, v_l_1244_, v_r_1245_, v_r_1240_);
return v___x_1246_;
}
else
{
lean_object* v_size_1247_; lean_object* v_k_1248_; lean_object* v_v_1249_; lean_object* v_r_1250_; lean_object* v___x_1251_; 
lean_dec(v_h__3_1235_);
v_size_1247_ = lean_ctor_get(v_x_1232_, 0);
lean_inc(v_size_1247_);
v_k_1248_ = lean_ctor_get(v_x_1232_, 1);
lean_inc(v_k_1248_);
v_v_1249_ = lean_ctor_get(v_x_1232_, 2);
lean_inc(v_v_1249_);
v_r_1250_ = lean_ctor_get(v_x_1232_, 4);
lean_inc(v_r_1250_);
lean_dec_ref(v_x_1232_);
v___x_1251_ = lean_apply_4(v_h__2_1234_, v_size_1247_, v_k_1248_, v_v_1249_, v_r_1250_);
return v___x_1251_;
}
}
else
{
lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_dec(v_h__3_1235_);
lean_dec(v_h__2_1234_);
v___x_1252_ = lean_box(0);
v___x_1253_ = lean_apply_1(v_h__1_1233_, v___x_1252_);
return v___x_1253_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1254_, lean_object* v_00_u03b2_1255_, lean_object* v_motive_1256_, lean_object* v_x_1257_, lean_object* v_h__1_1258_, lean_object* v_h__2_1259_, lean_object* v_h__3_1260_){
_start:
{
if (lean_obj_tag(v_x_1257_) == 0)
{
lean_object* v_l_1261_; 
lean_dec(v_h__1_1258_);
v_l_1261_ = lean_ctor_get(v_x_1257_, 3);
if (lean_obj_tag(v_l_1261_) == 0)
{
lean_object* v_size_1262_; lean_object* v_k_1263_; lean_object* v_v_1264_; lean_object* v_r_1265_; lean_object* v_size_1266_; lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v_l_1269_; lean_object* v_r_1270_; lean_object* v___x_1271_; 
lean_inc_ref(v_l_1261_);
lean_dec(v_h__2_1259_);
v_size_1262_ = lean_ctor_get(v_x_1257_, 0);
lean_inc(v_size_1262_);
v_k_1263_ = lean_ctor_get(v_x_1257_, 1);
lean_inc(v_k_1263_);
v_v_1264_ = lean_ctor_get(v_x_1257_, 2);
lean_inc(v_v_1264_);
v_r_1265_ = lean_ctor_get(v_x_1257_, 4);
lean_inc(v_r_1265_);
lean_dec_ref(v_x_1257_);
v_size_1266_ = lean_ctor_get(v_l_1261_, 0);
lean_inc(v_size_1266_);
v_k_1267_ = lean_ctor_get(v_l_1261_, 1);
lean_inc(v_k_1267_);
v_v_1268_ = lean_ctor_get(v_l_1261_, 2);
lean_inc(v_v_1268_);
v_l_1269_ = lean_ctor_get(v_l_1261_, 3);
lean_inc(v_l_1269_);
v_r_1270_ = lean_ctor_get(v_l_1261_, 4);
lean_inc(v_r_1270_);
lean_dec_ref(v_l_1261_);
v___x_1271_ = lean_apply_9(v_h__3_1260_, v_size_1262_, v_k_1263_, v_v_1264_, v_size_1266_, v_k_1267_, v_v_1268_, v_l_1269_, v_r_1270_, v_r_1265_);
return v___x_1271_;
}
else
{
lean_object* v_size_1272_; lean_object* v_k_1273_; lean_object* v_v_1274_; lean_object* v_r_1275_; lean_object* v___x_1276_; 
lean_dec(v_h__3_1260_);
v_size_1272_ = lean_ctor_get(v_x_1257_, 0);
lean_inc(v_size_1272_);
v_k_1273_ = lean_ctor_get(v_x_1257_, 1);
lean_inc(v_k_1273_);
v_v_1274_ = lean_ctor_get(v_x_1257_, 2);
lean_inc(v_v_1274_);
v_r_1275_ = lean_ctor_get(v_x_1257_, 4);
lean_inc(v_r_1275_);
lean_dec_ref(v_x_1257_);
v___x_1276_ = lean_apply_4(v_h__2_1259_, v_size_1272_, v_k_1273_, v_v_1274_, v_r_1275_);
return v___x_1276_;
}
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_dec(v_h__3_1260_);
lean_dec(v_h__2_1259_);
v___x_1277_ = lean_box(0);
v___x_1278_ = lean_apply_1(v_h__1_1258_, v___x_1277_);
return v___x_1278_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg(lean_object* v_x_1279_){
_start:
{
lean_object* v_l_1280_; 
v_l_1280_ = lean_ctor_get(v_x_1279_, 3);
if (lean_obj_tag(v_l_1280_) == 0)
{
v_x_1279_ = v_l_1280_;
goto _start;
}
else
{
lean_object* v_k_1282_; lean_object* v_v_1283_; lean_object* v___x_1284_; 
v_k_1282_ = lean_ctor_get(v_x_1279_, 1);
v_v_1283_ = lean_ctor_get(v_x_1279_, 2);
lean_inc(v_v_1283_);
lean_inc(v_k_1282_);
v___x_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1284_, 0, v_k_1282_);
lean_ctor_set(v___x_1284_, 1, v_v_1283_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg___boxed(lean_object* v_x_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1285_);
lean_dec(v_x_1285_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry(lean_object* v_00_u03b1_1287_, lean_object* v_00_u03b2_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_){
_start:
{
lean_object* v___x_1291_; 
v___x_1291_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1289_);
return v___x_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___boxed(lean_object* v_00_u03b1_1292_, lean_object* v_00_u03b2_1293_, lean_object* v_x_1294_, lean_object* v_x_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_Std_DTreeMap_Internal_Impl_minEntry(v_00_u03b1_1292_, v_00_u03b2_1293_, v_x_1294_, v_x_1295_);
lean_dec(v_x_1294_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1297_, lean_object* v_h__1_1298_, lean_object* v_h__2_1299_){
_start:
{
lean_object* v_l_1300_; 
v_l_1300_ = lean_ctor_get(v_x_1297_, 3);
if (lean_obj_tag(v_l_1300_) == 0)
{
lean_object* v_size_1301_; lean_object* v_k_1302_; lean_object* v_v_1303_; lean_object* v_r_1304_; lean_object* v_size_1305_; lean_object* v_k_1306_; lean_object* v_v_1307_; lean_object* v_l_1308_; lean_object* v_r_1309_; lean_object* v___x_1310_; 
lean_inc_ref(v_l_1300_);
lean_dec(v_h__1_1298_);
v_size_1301_ = lean_ctor_get(v_x_1297_, 0);
lean_inc(v_size_1301_);
v_k_1302_ = lean_ctor_get(v_x_1297_, 1);
lean_inc(v_k_1302_);
v_v_1303_ = lean_ctor_get(v_x_1297_, 2);
lean_inc(v_v_1303_);
v_r_1304_ = lean_ctor_get(v_x_1297_, 4);
lean_inc(v_r_1304_);
lean_dec(v_x_1297_);
v_size_1305_ = lean_ctor_get(v_l_1300_, 0);
lean_inc(v_size_1305_);
v_k_1306_ = lean_ctor_get(v_l_1300_, 1);
lean_inc(v_k_1306_);
v_v_1307_ = lean_ctor_get(v_l_1300_, 2);
lean_inc(v_v_1307_);
v_l_1308_ = lean_ctor_get(v_l_1300_, 3);
lean_inc(v_l_1308_);
v_r_1309_ = lean_ctor_get(v_l_1300_, 4);
lean_inc(v_r_1309_);
lean_dec_ref(v_l_1300_);
v___x_1310_ = lean_apply_10(v_h__2_1299_, v_size_1301_, v_k_1302_, v_v_1303_, v_size_1305_, v_k_1306_, v_v_1307_, v_l_1308_, v_r_1309_, v_r_1304_, lean_box(0));
return v___x_1310_;
}
else
{
lean_object* v_size_1311_; lean_object* v_k_1312_; lean_object* v_v_1313_; lean_object* v_r_1314_; lean_object* v___x_1315_; 
lean_dec(v_h__2_1299_);
v_size_1311_ = lean_ctor_get(v_x_1297_, 0);
lean_inc(v_size_1311_);
v_k_1312_ = lean_ctor_get(v_x_1297_, 1);
lean_inc(v_k_1312_);
v_v_1313_ = lean_ctor_get(v_x_1297_, 2);
lean_inc(v_v_1313_);
v_r_1314_ = lean_ctor_get(v_x_1297_, 4);
lean_inc(v_r_1314_);
lean_dec(v_x_1297_);
v___x_1315_ = lean_apply_5(v_h__1_1298_, v_size_1311_, v_k_1312_, v_v_1313_, v_r_1314_, lean_box(0));
return v___x_1315_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1316_, lean_object* v_00_u03b2_1317_, lean_object* v_motive_1318_, lean_object* v_x_1319_, lean_object* v_x_1320_, lean_object* v_h__1_1321_, lean_object* v_h__2_1322_){
_start:
{
lean_object* v_l_1323_; 
v_l_1323_ = lean_ctor_get(v_x_1319_, 3);
if (lean_obj_tag(v_l_1323_) == 0)
{
lean_object* v_size_1324_; lean_object* v_k_1325_; lean_object* v_v_1326_; lean_object* v_r_1327_; lean_object* v_size_1328_; lean_object* v_k_1329_; lean_object* v_v_1330_; lean_object* v_l_1331_; lean_object* v_r_1332_; lean_object* v___x_1333_; 
lean_inc_ref(v_l_1323_);
lean_dec(v_h__1_1321_);
v_size_1324_ = lean_ctor_get(v_x_1319_, 0);
lean_inc(v_size_1324_);
v_k_1325_ = lean_ctor_get(v_x_1319_, 1);
lean_inc(v_k_1325_);
v_v_1326_ = lean_ctor_get(v_x_1319_, 2);
lean_inc(v_v_1326_);
v_r_1327_ = lean_ctor_get(v_x_1319_, 4);
lean_inc(v_r_1327_);
lean_dec(v_x_1319_);
v_size_1328_ = lean_ctor_get(v_l_1323_, 0);
lean_inc(v_size_1328_);
v_k_1329_ = lean_ctor_get(v_l_1323_, 1);
lean_inc(v_k_1329_);
v_v_1330_ = lean_ctor_get(v_l_1323_, 2);
lean_inc(v_v_1330_);
v_l_1331_ = lean_ctor_get(v_l_1323_, 3);
lean_inc(v_l_1331_);
v_r_1332_ = lean_ctor_get(v_l_1323_, 4);
lean_inc(v_r_1332_);
lean_dec_ref(v_l_1323_);
v___x_1333_ = lean_apply_10(v_h__2_1322_, v_size_1324_, v_k_1325_, v_v_1326_, v_size_1328_, v_k_1329_, v_v_1330_, v_l_1331_, v_r_1332_, v_r_1327_, lean_box(0));
return v___x_1333_;
}
else
{
lean_object* v_size_1334_; lean_object* v_k_1335_; lean_object* v_v_1336_; lean_object* v_r_1337_; lean_object* v___x_1338_; 
lean_dec(v_h__2_1322_);
v_size_1334_ = lean_ctor_get(v_x_1319_, 0);
lean_inc(v_size_1334_);
v_k_1335_ = lean_ctor_get(v_x_1319_, 1);
lean_inc(v_k_1335_);
v_v_1336_ = lean_ctor_get(v_x_1319_, 2);
lean_inc(v_v_1336_);
v_r_1337_ = lean_ctor_get(v_x_1319_, 4);
lean_inc(v_r_1337_);
lean_dec(v_x_1319_);
v___x_1338_ = lean_apply_5(v_h__1_1321_, v_size_1334_, v_k_1335_, v_v_1336_, v_r_1337_, lean_box(0));
return v___x_1338_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1341_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1342_ = lean_unsigned_to_nat(13u);
v___x_1343_ = lean_unsigned_to_nat(367u);
v___x_1344_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0));
v___x_1345_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1346_ = l_mkPanicMessageWithDecl(v___x_1345_, v___x_1344_, v___x_1343_, v___x_1342_, v___x_1341_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object* v_inst_1347_, lean_object* v_x_1348_){
_start:
{
if (lean_obj_tag(v_x_1348_) == 0)
{
lean_object* v_l_1349_; 
v_l_1349_ = lean_ctor_get(v_x_1348_, 3);
if (lean_obj_tag(v_l_1349_) == 0)
{
v_x_1348_ = v_l_1349_;
goto _start;
}
else
{
lean_object* v_k_1351_; lean_object* v_v_1352_; lean_object* v___x_1353_; 
lean_dec_ref(v_inst_1347_);
v_k_1351_ = lean_ctor_get(v_x_1348_, 1);
v_v_1352_ = lean_ctor_get(v_x_1348_, 2);
lean_inc(v_v_1352_);
lean_inc(v_k_1351_);
v___x_1353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_k_1351_);
lean_ctor_set(v___x_1353_, 1, v_v_1352_);
return v___x_1353_;
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1354_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2);
v___x_1355_ = l_panic___redArg(v_inst_1347_, v___x_1354_);
return v___x_1355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___boxed(lean_object* v_inst_1356_, lean_object* v_x_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1356_, v_x_1357_);
lean_dec(v_x_1357_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21(lean_object* v_00_u03b1_1359_, lean_object* v_00_u03b2_1360_, lean_object* v_inst_1361_, lean_object* v_x_1362_){
_start:
{
lean_object* v___x_1363_; 
v___x_1363_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1361_, v_x_1362_);
return v___x_1363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___boxed(lean_object* v_00_u03b1_1364_, lean_object* v_00_u03b2_1365_, lean_object* v_inst_1366_, lean_object* v_x_1367_){
_start:
{
lean_object* v_res_1368_; 
v_res_1368_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21(v_00_u03b1_1364_, v_00_u03b2_1365_, v_inst_1366_, v_x_1367_);
lean_dec(v_x_1367_);
return v_res_1368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object* v_x_1369_, lean_object* v_x_1370_){
_start:
{
if (lean_obj_tag(v_x_1369_) == 0)
{
lean_object* v_l_1371_; 
v_l_1371_ = lean_ctor_get(v_x_1369_, 3);
if (lean_obj_tag(v_l_1371_) == 0)
{
v_x_1369_ = v_l_1371_;
goto _start;
}
else
{
lean_object* v_k_1373_; lean_object* v_v_1374_; lean_object* v___x_1375_; 
v_k_1373_ = lean_ctor_get(v_x_1369_, 1);
v_v_1374_ = lean_ctor_get(v_x_1369_, 2);
lean_inc(v_v_1374_);
lean_inc(v_k_1373_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v_k_1373_);
lean_ctor_set(v___x_1375_, 1, v_v_1374_);
return v___x_1375_;
}
}
else
{
lean_inc_ref(v_x_1370_);
return v_x_1370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg___boxed(lean_object* v_x_1376_, lean_object* v_x_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1376_, v_x_1377_);
lean_dec_ref(v_x_1377_);
lean_dec(v_x_1376_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD(lean_object* v_00_u03b1_1379_, lean_object* v_00_u03b2_1380_, lean_object* v_x_1381_, lean_object* v_x_1382_){
_start:
{
lean_object* v___x_1383_; 
v___x_1383_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1381_, v_x_1382_);
return v___x_1383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___boxed(lean_object* v_00_u03b1_1384_, lean_object* v_00_u03b2_1385_, lean_object* v_x_1386_, lean_object* v_x_1387_){
_start:
{
lean_object* v_res_1388_; 
v_res_1388_ = l_Std_DTreeMap_Internal_Impl_minEntryD(v_00_u03b1_1384_, v_00_u03b2_1385_, v_x_1386_, v_x_1387_);
lean_dec_ref(v_x_1387_);
lean_dec(v_x_1386_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1389_, lean_object* v_x_1390_, lean_object* v_h__1_1391_, lean_object* v_h__2_1392_, lean_object* v_h__3_1393_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
lean_object* v_l_1394_; 
lean_dec(v_h__1_1391_);
v_l_1394_ = lean_ctor_get(v_x_1389_, 3);
if (lean_obj_tag(v_l_1394_) == 0)
{
lean_object* v_size_1395_; lean_object* v_k_1396_; lean_object* v_v_1397_; lean_object* v_r_1398_; lean_object* v_size_1399_; lean_object* v_k_1400_; lean_object* v_v_1401_; lean_object* v_l_1402_; lean_object* v_r_1403_; lean_object* v___x_1404_; 
lean_inc_ref(v_l_1394_);
lean_dec(v_h__2_1392_);
v_size_1395_ = lean_ctor_get(v_x_1389_, 0);
lean_inc(v_size_1395_);
v_k_1396_ = lean_ctor_get(v_x_1389_, 1);
lean_inc(v_k_1396_);
v_v_1397_ = lean_ctor_get(v_x_1389_, 2);
lean_inc(v_v_1397_);
v_r_1398_ = lean_ctor_get(v_x_1389_, 4);
lean_inc(v_r_1398_);
lean_dec_ref(v_x_1389_);
v_size_1399_ = lean_ctor_get(v_l_1394_, 0);
lean_inc(v_size_1399_);
v_k_1400_ = lean_ctor_get(v_l_1394_, 1);
lean_inc(v_k_1400_);
v_v_1401_ = lean_ctor_get(v_l_1394_, 2);
lean_inc(v_v_1401_);
v_l_1402_ = lean_ctor_get(v_l_1394_, 3);
lean_inc(v_l_1402_);
v_r_1403_ = lean_ctor_get(v_l_1394_, 4);
lean_inc(v_r_1403_);
lean_dec_ref(v_l_1394_);
v___x_1404_ = lean_apply_10(v_h__3_1393_, v_size_1395_, v_k_1396_, v_v_1397_, v_size_1399_, v_k_1400_, v_v_1401_, v_l_1402_, v_r_1403_, v_r_1398_, v_x_1390_);
return v___x_1404_;
}
else
{
lean_object* v_size_1405_; lean_object* v_k_1406_; lean_object* v_v_1407_; lean_object* v_r_1408_; lean_object* v___x_1409_; 
lean_dec(v_h__3_1393_);
v_size_1405_ = lean_ctor_get(v_x_1389_, 0);
lean_inc(v_size_1405_);
v_k_1406_ = lean_ctor_get(v_x_1389_, 1);
lean_inc(v_k_1406_);
v_v_1407_ = lean_ctor_get(v_x_1389_, 2);
lean_inc(v_v_1407_);
v_r_1408_ = lean_ctor_get(v_x_1389_, 4);
lean_inc(v_r_1408_);
lean_dec_ref(v_x_1389_);
v___x_1409_ = lean_apply_5(v_h__2_1392_, v_size_1405_, v_k_1406_, v_v_1407_, v_r_1408_, v_x_1390_);
return v___x_1409_;
}
}
else
{
lean_object* v___x_1410_; 
lean_dec(v_h__3_1393_);
lean_dec(v_h__2_1392_);
v___x_1410_ = lean_apply_1(v_h__1_1391_, v_x_1390_);
return v___x_1410_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1411_, lean_object* v_00_u03b2_1412_, lean_object* v_motive_1413_, lean_object* v_x_1414_, lean_object* v_x_1415_, lean_object* v_h__1_1416_, lean_object* v_h__2_1417_, lean_object* v_h__3_1418_){
_start:
{
if (lean_obj_tag(v_x_1414_) == 0)
{
lean_object* v_l_1419_; 
lean_dec(v_h__1_1416_);
v_l_1419_ = lean_ctor_get(v_x_1414_, 3);
if (lean_obj_tag(v_l_1419_) == 0)
{
lean_object* v_size_1420_; lean_object* v_k_1421_; lean_object* v_v_1422_; lean_object* v_r_1423_; lean_object* v_size_1424_; lean_object* v_k_1425_; lean_object* v_v_1426_; lean_object* v_l_1427_; lean_object* v_r_1428_; lean_object* v___x_1429_; 
lean_inc_ref(v_l_1419_);
lean_dec(v_h__2_1417_);
v_size_1420_ = lean_ctor_get(v_x_1414_, 0);
lean_inc(v_size_1420_);
v_k_1421_ = lean_ctor_get(v_x_1414_, 1);
lean_inc(v_k_1421_);
v_v_1422_ = lean_ctor_get(v_x_1414_, 2);
lean_inc(v_v_1422_);
v_r_1423_ = lean_ctor_get(v_x_1414_, 4);
lean_inc(v_r_1423_);
lean_dec_ref(v_x_1414_);
v_size_1424_ = lean_ctor_get(v_l_1419_, 0);
lean_inc(v_size_1424_);
v_k_1425_ = lean_ctor_get(v_l_1419_, 1);
lean_inc(v_k_1425_);
v_v_1426_ = lean_ctor_get(v_l_1419_, 2);
lean_inc(v_v_1426_);
v_l_1427_ = lean_ctor_get(v_l_1419_, 3);
lean_inc(v_l_1427_);
v_r_1428_ = lean_ctor_get(v_l_1419_, 4);
lean_inc(v_r_1428_);
lean_dec_ref(v_l_1419_);
v___x_1429_ = lean_apply_10(v_h__3_1418_, v_size_1420_, v_k_1421_, v_v_1422_, v_size_1424_, v_k_1425_, v_v_1426_, v_l_1427_, v_r_1428_, v_r_1423_, v_x_1415_);
return v___x_1429_;
}
else
{
lean_object* v_size_1430_; lean_object* v_k_1431_; lean_object* v_v_1432_; lean_object* v_r_1433_; lean_object* v___x_1434_; 
lean_dec(v_h__3_1418_);
v_size_1430_ = lean_ctor_get(v_x_1414_, 0);
lean_inc(v_size_1430_);
v_k_1431_ = lean_ctor_get(v_x_1414_, 1);
lean_inc(v_k_1431_);
v_v_1432_ = lean_ctor_get(v_x_1414_, 2);
lean_inc(v_v_1432_);
v_r_1433_ = lean_ctor_get(v_x_1414_, 4);
lean_inc(v_r_1433_);
lean_dec_ref(v_x_1414_);
v___x_1434_ = lean_apply_5(v_h__2_1417_, v_size_1430_, v_k_1431_, v_v_1432_, v_r_1433_, v_x_1415_);
return v___x_1434_;
}
}
else
{
lean_object* v___x_1435_; 
lean_dec(v_h__3_1418_);
lean_dec(v_h__2_1417_);
v___x_1435_ = lean_apply_1(v_h__1_1416_, v_x_1415_);
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object* v_x_1436_){
_start:
{
if (lean_obj_tag(v_x_1436_) == 0)
{
lean_object* v_r_1437_; 
v_r_1437_ = lean_ctor_get(v_x_1436_, 4);
if (lean_obj_tag(v_r_1437_) == 0)
{
v_x_1436_ = v_r_1437_;
goto _start;
}
else
{
lean_object* v_k_1439_; lean_object* v_v_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v_k_1439_ = lean_ctor_get(v_x_1436_, 1);
v_v_1440_ = lean_ctor_get(v_x_1436_, 2);
lean_inc(v_v_1440_);
lean_inc(v_k_1439_);
v___x_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1441_, 0, v_k_1439_);
lean_ctor_set(v___x_1441_, 1, v_v_1440_);
v___x_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
}
else
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_box(0);
return v___x_1443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg___boxed(lean_object* v_x_1444_){
_start:
{
lean_object* v_res_1445_; 
v_res_1445_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1444_);
lean_dec(v_x_1444_);
return v_res_1445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(lean_object* v_00_u03b1_1446_, lean_object* v_00_u03b2_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1450_, lean_object* v_00_u03b2_1451_, lean_object* v_x_1452_){
_start:
{
lean_object* v_res_1453_; 
v_res_1453_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(v_00_u03b1_1450_, v_00_u03b2_1451_, v_x_1452_);
lean_dec(v_x_1452_);
return v_res_1453_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1454_, lean_object* v_h__1_1455_, lean_object* v_h__2_1456_, lean_object* v_h__3_1457_){
_start:
{
if (lean_obj_tag(v_x_1454_) == 0)
{
lean_object* v_r_1458_; 
lean_dec(v_h__1_1455_);
v_r_1458_ = lean_ctor_get(v_x_1454_, 4);
if (lean_obj_tag(v_r_1458_) == 0)
{
lean_object* v_size_1459_; lean_object* v_k_1460_; lean_object* v_v_1461_; lean_object* v_l_1462_; lean_object* v_size_1463_; lean_object* v_k_1464_; lean_object* v_v_1465_; lean_object* v_l_1466_; lean_object* v_r_1467_; lean_object* v___x_1468_; 
lean_inc_ref(v_r_1458_);
lean_dec(v_h__2_1456_);
v_size_1459_ = lean_ctor_get(v_x_1454_, 0);
lean_inc(v_size_1459_);
v_k_1460_ = lean_ctor_get(v_x_1454_, 1);
lean_inc(v_k_1460_);
v_v_1461_ = lean_ctor_get(v_x_1454_, 2);
lean_inc(v_v_1461_);
v_l_1462_ = lean_ctor_get(v_x_1454_, 3);
lean_inc(v_l_1462_);
lean_dec_ref(v_x_1454_);
v_size_1463_ = lean_ctor_get(v_r_1458_, 0);
lean_inc(v_size_1463_);
v_k_1464_ = lean_ctor_get(v_r_1458_, 1);
lean_inc(v_k_1464_);
v_v_1465_ = lean_ctor_get(v_r_1458_, 2);
lean_inc(v_v_1465_);
v_l_1466_ = lean_ctor_get(v_r_1458_, 3);
lean_inc(v_l_1466_);
v_r_1467_ = lean_ctor_get(v_r_1458_, 4);
lean_inc(v_r_1467_);
lean_dec_ref(v_r_1458_);
v___x_1468_ = lean_apply_9(v_h__3_1457_, v_size_1459_, v_k_1460_, v_v_1461_, v_l_1462_, v_size_1463_, v_k_1464_, v_v_1465_, v_l_1466_, v_r_1467_);
return v___x_1468_;
}
else
{
lean_object* v_size_1469_; lean_object* v_k_1470_; lean_object* v_v_1471_; lean_object* v_l_1472_; lean_object* v___x_1473_; 
lean_dec(v_h__3_1457_);
v_size_1469_ = lean_ctor_get(v_x_1454_, 0);
lean_inc(v_size_1469_);
v_k_1470_ = lean_ctor_get(v_x_1454_, 1);
lean_inc(v_k_1470_);
v_v_1471_ = lean_ctor_get(v_x_1454_, 2);
lean_inc(v_v_1471_);
v_l_1472_ = lean_ctor_get(v_x_1454_, 3);
lean_inc(v_l_1472_);
lean_dec_ref(v_x_1454_);
v___x_1473_ = lean_apply_4(v_h__2_1456_, v_size_1469_, v_k_1470_, v_v_1471_, v_l_1472_);
return v___x_1473_;
}
}
else
{
lean_object* v___x_1474_; lean_object* v___x_1475_; 
lean_dec(v_h__3_1457_);
lean_dec(v_h__2_1456_);
v___x_1474_ = lean_box(0);
v___x_1475_ = lean_apply_1(v_h__1_1455_, v___x_1474_);
return v___x_1475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1476_, lean_object* v_00_u03b2_1477_, lean_object* v_motive_1478_, lean_object* v_x_1479_, lean_object* v_h__1_1480_, lean_object* v_h__2_1481_, lean_object* v_h__3_1482_){
_start:
{
if (lean_obj_tag(v_x_1479_) == 0)
{
lean_object* v_r_1483_; 
lean_dec(v_h__1_1480_);
v_r_1483_ = lean_ctor_get(v_x_1479_, 4);
if (lean_obj_tag(v_r_1483_) == 0)
{
lean_object* v_size_1484_; lean_object* v_k_1485_; lean_object* v_v_1486_; lean_object* v_l_1487_; lean_object* v_size_1488_; lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v_l_1491_; lean_object* v_r_1492_; lean_object* v___x_1493_; 
lean_inc_ref(v_r_1483_);
lean_dec(v_h__2_1481_);
v_size_1484_ = lean_ctor_get(v_x_1479_, 0);
lean_inc(v_size_1484_);
v_k_1485_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_k_1485_);
v_v_1486_ = lean_ctor_get(v_x_1479_, 2);
lean_inc(v_v_1486_);
v_l_1487_ = lean_ctor_get(v_x_1479_, 3);
lean_inc(v_l_1487_);
lean_dec_ref(v_x_1479_);
v_size_1488_ = lean_ctor_get(v_r_1483_, 0);
lean_inc(v_size_1488_);
v_k_1489_ = lean_ctor_get(v_r_1483_, 1);
lean_inc(v_k_1489_);
v_v_1490_ = lean_ctor_get(v_r_1483_, 2);
lean_inc(v_v_1490_);
v_l_1491_ = lean_ctor_get(v_r_1483_, 3);
lean_inc(v_l_1491_);
v_r_1492_ = lean_ctor_get(v_r_1483_, 4);
lean_inc(v_r_1492_);
lean_dec_ref(v_r_1483_);
v___x_1493_ = lean_apply_9(v_h__3_1482_, v_size_1484_, v_k_1485_, v_v_1486_, v_l_1487_, v_size_1488_, v_k_1489_, v_v_1490_, v_l_1491_, v_r_1492_);
return v___x_1493_;
}
else
{
lean_object* v_size_1494_; lean_object* v_k_1495_; lean_object* v_v_1496_; lean_object* v_l_1497_; lean_object* v___x_1498_; 
lean_dec(v_h__3_1482_);
v_size_1494_ = lean_ctor_get(v_x_1479_, 0);
lean_inc(v_size_1494_);
v_k_1495_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_k_1495_);
v_v_1496_ = lean_ctor_get(v_x_1479_, 2);
lean_inc(v_v_1496_);
v_l_1497_ = lean_ctor_get(v_x_1479_, 3);
lean_inc(v_l_1497_);
lean_dec_ref(v_x_1479_);
v___x_1498_ = lean_apply_4(v_h__2_1481_, v_size_1494_, v_k_1495_, v_v_1496_, v_l_1497_);
return v___x_1498_;
}
}
else
{
lean_object* v___x_1499_; lean_object* v___x_1500_; 
lean_dec(v_h__3_1482_);
lean_dec(v_h__2_1481_);
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_apply_1(v_h__1_1480_, v___x_1499_);
return v___x_1500_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object* v_x_1501_){
_start:
{
lean_object* v_r_1502_; 
v_r_1502_ = lean_ctor_get(v_x_1501_, 4);
if (lean_obj_tag(v_r_1502_) == 0)
{
v_x_1501_ = v_r_1502_;
goto _start;
}
else
{
lean_object* v_k_1504_; lean_object* v_v_1505_; lean_object* v___x_1506_; 
v_k_1504_ = lean_ctor_get(v_x_1501_, 1);
v_v_1505_ = lean_ctor_get(v_x_1501_, 2);
lean_inc(v_v_1505_);
lean_inc(v_k_1504_);
v___x_1506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1506_, 0, v_k_1504_);
lean_ctor_set(v___x_1506_, 1, v_v_1505_);
return v___x_1506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg___boxed(lean_object* v_x_1507_){
_start:
{
lean_object* v_res_1508_; 
v_res_1508_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1507_);
lean_dec(v_x_1507_);
return v_res_1508_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry(lean_object* v_00_u03b1_1509_, lean_object* v_00_u03b2_1510_, lean_object* v_x_1511_, lean_object* v_x_1512_){
_start:
{
lean_object* v___x_1513_; 
v___x_1513_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1511_);
return v___x_1513_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___boxed(lean_object* v_00_u03b1_1514_, lean_object* v_00_u03b2_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Std_DTreeMap_Internal_Impl_maxEntry(v_00_u03b1_1514_, v_00_u03b2_1515_, v_x_1516_, v_x_1517_);
lean_dec(v_x_1516_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1519_, lean_object* v_h__1_1520_, lean_object* v_h__2_1521_){
_start:
{
lean_object* v_r_1522_; 
v_r_1522_ = lean_ctor_get(v_x_1519_, 4);
if (lean_obj_tag(v_r_1522_) == 0)
{
lean_object* v_size_1523_; lean_object* v_k_1524_; lean_object* v_v_1525_; lean_object* v_l_1526_; lean_object* v_size_1527_; lean_object* v_k_1528_; lean_object* v_v_1529_; lean_object* v_l_1530_; lean_object* v_r_1531_; lean_object* v___x_1532_; 
lean_inc_ref(v_r_1522_);
lean_dec(v_h__1_1520_);
v_size_1523_ = lean_ctor_get(v_x_1519_, 0);
lean_inc(v_size_1523_);
v_k_1524_ = lean_ctor_get(v_x_1519_, 1);
lean_inc(v_k_1524_);
v_v_1525_ = lean_ctor_get(v_x_1519_, 2);
lean_inc(v_v_1525_);
v_l_1526_ = lean_ctor_get(v_x_1519_, 3);
lean_inc(v_l_1526_);
lean_dec(v_x_1519_);
v_size_1527_ = lean_ctor_get(v_r_1522_, 0);
lean_inc(v_size_1527_);
v_k_1528_ = lean_ctor_get(v_r_1522_, 1);
lean_inc(v_k_1528_);
v_v_1529_ = lean_ctor_get(v_r_1522_, 2);
lean_inc(v_v_1529_);
v_l_1530_ = lean_ctor_get(v_r_1522_, 3);
lean_inc(v_l_1530_);
v_r_1531_ = lean_ctor_get(v_r_1522_, 4);
lean_inc(v_r_1531_);
lean_dec_ref(v_r_1522_);
v___x_1532_ = lean_apply_10(v_h__2_1521_, v_size_1523_, v_k_1524_, v_v_1525_, v_l_1526_, v_size_1527_, v_k_1528_, v_v_1529_, v_l_1530_, v_r_1531_, lean_box(0));
return v___x_1532_;
}
else
{
lean_object* v_size_1533_; lean_object* v_k_1534_; lean_object* v_v_1535_; lean_object* v_l_1536_; lean_object* v___x_1537_; 
lean_dec(v_h__2_1521_);
v_size_1533_ = lean_ctor_get(v_x_1519_, 0);
lean_inc(v_size_1533_);
v_k_1534_ = lean_ctor_get(v_x_1519_, 1);
lean_inc(v_k_1534_);
v_v_1535_ = lean_ctor_get(v_x_1519_, 2);
lean_inc(v_v_1535_);
v_l_1536_ = lean_ctor_get(v_x_1519_, 3);
lean_inc(v_l_1536_);
lean_dec(v_x_1519_);
v___x_1537_ = lean_apply_5(v_h__1_1520_, v_size_1533_, v_k_1534_, v_v_1535_, v_l_1536_, lean_box(0));
return v___x_1537_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1538_, lean_object* v_00_u03b2_1539_, lean_object* v_motive_1540_, lean_object* v_x_1541_, lean_object* v_x_1542_, lean_object* v_h__1_1543_, lean_object* v_h__2_1544_){
_start:
{
lean_object* v_r_1545_; 
v_r_1545_ = lean_ctor_get(v_x_1541_, 4);
if (lean_obj_tag(v_r_1545_) == 0)
{
lean_object* v_size_1546_; lean_object* v_k_1547_; lean_object* v_v_1548_; lean_object* v_l_1549_; lean_object* v_size_1550_; lean_object* v_k_1551_; lean_object* v_v_1552_; lean_object* v_l_1553_; lean_object* v_r_1554_; lean_object* v___x_1555_; 
lean_inc_ref(v_r_1545_);
lean_dec(v_h__1_1543_);
v_size_1546_ = lean_ctor_get(v_x_1541_, 0);
lean_inc(v_size_1546_);
v_k_1547_ = lean_ctor_get(v_x_1541_, 1);
lean_inc(v_k_1547_);
v_v_1548_ = lean_ctor_get(v_x_1541_, 2);
lean_inc(v_v_1548_);
v_l_1549_ = lean_ctor_get(v_x_1541_, 3);
lean_inc(v_l_1549_);
lean_dec(v_x_1541_);
v_size_1550_ = lean_ctor_get(v_r_1545_, 0);
lean_inc(v_size_1550_);
v_k_1551_ = lean_ctor_get(v_r_1545_, 1);
lean_inc(v_k_1551_);
v_v_1552_ = lean_ctor_get(v_r_1545_, 2);
lean_inc(v_v_1552_);
v_l_1553_ = lean_ctor_get(v_r_1545_, 3);
lean_inc(v_l_1553_);
v_r_1554_ = lean_ctor_get(v_r_1545_, 4);
lean_inc(v_r_1554_);
lean_dec_ref(v_r_1545_);
v___x_1555_ = lean_apply_10(v_h__2_1544_, v_size_1546_, v_k_1547_, v_v_1548_, v_l_1549_, v_size_1550_, v_k_1551_, v_v_1552_, v_l_1553_, v_r_1554_, lean_box(0));
return v___x_1555_;
}
else
{
lean_object* v_size_1556_; lean_object* v_k_1557_; lean_object* v_v_1558_; lean_object* v_l_1559_; lean_object* v___x_1560_; 
lean_dec(v_h__2_1544_);
v_size_1556_ = lean_ctor_get(v_x_1541_, 0);
lean_inc(v_size_1556_);
v_k_1557_ = lean_ctor_get(v_x_1541_, 1);
lean_inc(v_k_1557_);
v_v_1558_ = lean_ctor_get(v_x_1541_, 2);
lean_inc(v_v_1558_);
v_l_1559_ = lean_ctor_get(v_x_1541_, 3);
lean_inc(v_l_1559_);
lean_dec(v_x_1541_);
v___x_1560_ = lean_apply_5(v_h__1_1543_, v_size_1556_, v_k_1557_, v_v_1558_, v_l_1559_, lean_box(0));
return v___x_1560_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1562_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1563_ = lean_unsigned_to_nat(13u);
v___x_1564_ = lean_unsigned_to_nat(390u);
v___x_1565_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0));
v___x_1566_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1567_ = l_mkPanicMessageWithDecl(v___x_1566_, v___x_1565_, v___x_1564_, v___x_1563_, v___x_1562_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object* v_inst_1568_, lean_object* v_x_1569_){
_start:
{
if (lean_obj_tag(v_x_1569_) == 0)
{
lean_object* v_r_1570_; 
v_r_1570_ = lean_ctor_get(v_x_1569_, 4);
if (lean_obj_tag(v_r_1570_) == 0)
{
v_x_1569_ = v_r_1570_;
goto _start;
}
else
{
lean_object* v_k_1572_; lean_object* v_v_1573_; lean_object* v___x_1574_; 
lean_dec_ref(v_inst_1568_);
v_k_1572_ = lean_ctor_get(v_x_1569_, 1);
v_v_1573_ = lean_ctor_get(v_x_1569_, 2);
lean_inc(v_v_1573_);
lean_inc(v_k_1572_);
v___x_1574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1574_, 0, v_k_1572_);
lean_ctor_set(v___x_1574_, 1, v_v_1573_);
return v___x_1574_;
}
}
else
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1);
v___x_1576_ = l_panic___redArg(v_inst_1568_, v___x_1575_);
return v___x_1576_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___boxed(lean_object* v_inst_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1577_, v_x_1578_);
lean_dec(v_x_1578_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21(lean_object* v_00_u03b1_1580_, lean_object* v_00_u03b2_1581_, lean_object* v_inst_1582_, lean_object* v_x_1583_){
_start:
{
lean_object* v___x_1584_; 
v___x_1584_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1582_, v_x_1583_);
return v___x_1584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___boxed(lean_object* v_00_u03b1_1585_, lean_object* v_00_u03b2_1586_, lean_object* v_inst_1587_, lean_object* v_x_1588_){
_start:
{
lean_object* v_res_1589_; 
v_res_1589_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21(v_00_u03b1_1585_, v_00_u03b2_1586_, v_inst_1587_, v_x_1588_);
lean_dec(v_x_1588_);
return v_res_1589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(lean_object* v_x_1590_, lean_object* v_x_1591_){
_start:
{
if (lean_obj_tag(v_x_1590_) == 0)
{
lean_object* v_r_1592_; 
v_r_1592_ = lean_ctor_get(v_x_1590_, 4);
if (lean_obj_tag(v_r_1592_) == 0)
{
v_x_1590_ = v_r_1592_;
goto _start;
}
else
{
lean_object* v_k_1594_; lean_object* v_v_1595_; lean_object* v___x_1596_; 
v_k_1594_ = lean_ctor_get(v_x_1590_, 1);
v_v_1595_ = lean_ctor_get(v_x_1590_, 2);
lean_inc(v_v_1595_);
lean_inc(v_k_1594_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_k_1594_);
lean_ctor_set(v___x_1596_, 1, v_v_1595_);
return v___x_1596_;
}
}
else
{
lean_inc_ref(v_x_1591_);
return v_x_1591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg___boxed(lean_object* v_x_1597_, lean_object* v_x_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1597_, v_x_1598_);
lean_dec_ref(v_x_1598_);
lean_dec(v_x_1597_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD(lean_object* v_00_u03b1_1600_, lean_object* v_00_u03b2_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_){
_start:
{
lean_object* v___x_1604_; 
v___x_1604_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1602_, v_x_1603_);
return v___x_1604_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___boxed(lean_object* v_00_u03b1_1605_, lean_object* v_00_u03b2_1606_, lean_object* v_x_1607_, lean_object* v_x_1608_){
_start:
{
lean_object* v_res_1609_; 
v_res_1609_ = l_Std_DTreeMap_Internal_Impl_maxEntryD(v_00_u03b1_1605_, v_00_u03b2_1606_, v_x_1607_, v_x_1608_);
lean_dec_ref(v_x_1608_);
lean_dec(v_x_1607_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1610_, lean_object* v_x_1611_, lean_object* v_h__1_1612_, lean_object* v_h__2_1613_, lean_object* v_h__3_1614_){
_start:
{
if (lean_obj_tag(v_x_1610_) == 0)
{
lean_object* v_r_1615_; 
lean_dec(v_h__1_1612_);
v_r_1615_ = lean_ctor_get(v_x_1610_, 4);
if (lean_obj_tag(v_r_1615_) == 0)
{
lean_object* v_size_1616_; lean_object* v_k_1617_; lean_object* v_v_1618_; lean_object* v_l_1619_; lean_object* v_size_1620_; lean_object* v_k_1621_; lean_object* v_v_1622_; lean_object* v_l_1623_; lean_object* v_r_1624_; lean_object* v___x_1625_; 
lean_inc_ref(v_r_1615_);
lean_dec(v_h__2_1613_);
v_size_1616_ = lean_ctor_get(v_x_1610_, 0);
lean_inc(v_size_1616_);
v_k_1617_ = lean_ctor_get(v_x_1610_, 1);
lean_inc(v_k_1617_);
v_v_1618_ = lean_ctor_get(v_x_1610_, 2);
lean_inc(v_v_1618_);
v_l_1619_ = lean_ctor_get(v_x_1610_, 3);
lean_inc(v_l_1619_);
lean_dec_ref(v_x_1610_);
v_size_1620_ = lean_ctor_get(v_r_1615_, 0);
lean_inc(v_size_1620_);
v_k_1621_ = lean_ctor_get(v_r_1615_, 1);
lean_inc(v_k_1621_);
v_v_1622_ = lean_ctor_get(v_r_1615_, 2);
lean_inc(v_v_1622_);
v_l_1623_ = lean_ctor_get(v_r_1615_, 3);
lean_inc(v_l_1623_);
v_r_1624_ = lean_ctor_get(v_r_1615_, 4);
lean_inc(v_r_1624_);
lean_dec_ref(v_r_1615_);
v___x_1625_ = lean_apply_10(v_h__3_1614_, v_size_1616_, v_k_1617_, v_v_1618_, v_l_1619_, v_size_1620_, v_k_1621_, v_v_1622_, v_l_1623_, v_r_1624_, v_x_1611_);
return v___x_1625_;
}
else
{
lean_object* v_size_1626_; lean_object* v_k_1627_; lean_object* v_v_1628_; lean_object* v_l_1629_; lean_object* v___x_1630_; 
lean_dec(v_h__3_1614_);
v_size_1626_ = lean_ctor_get(v_x_1610_, 0);
lean_inc(v_size_1626_);
v_k_1627_ = lean_ctor_get(v_x_1610_, 1);
lean_inc(v_k_1627_);
v_v_1628_ = lean_ctor_get(v_x_1610_, 2);
lean_inc(v_v_1628_);
v_l_1629_ = lean_ctor_get(v_x_1610_, 3);
lean_inc(v_l_1629_);
lean_dec_ref(v_x_1610_);
v___x_1630_ = lean_apply_5(v_h__2_1613_, v_size_1626_, v_k_1627_, v_v_1628_, v_l_1629_, v_x_1611_);
return v___x_1630_;
}
}
else
{
lean_object* v___x_1631_; 
lean_dec(v_h__3_1614_);
lean_dec(v_h__2_1613_);
v___x_1631_ = lean_apply_1(v_h__1_1612_, v_x_1611_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1632_, lean_object* v_00_u03b2_1633_, lean_object* v_motive_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_, lean_object* v_h__1_1637_, lean_object* v_h__2_1638_, lean_object* v_h__3_1639_){
_start:
{
if (lean_obj_tag(v_x_1635_) == 0)
{
lean_object* v_r_1640_; 
lean_dec(v_h__1_1637_);
v_r_1640_ = lean_ctor_get(v_x_1635_, 4);
if (lean_obj_tag(v_r_1640_) == 0)
{
lean_object* v_size_1641_; lean_object* v_k_1642_; lean_object* v_v_1643_; lean_object* v_l_1644_; lean_object* v_size_1645_; lean_object* v_k_1646_; lean_object* v_v_1647_; lean_object* v_l_1648_; lean_object* v_r_1649_; lean_object* v___x_1650_; 
lean_inc_ref(v_r_1640_);
lean_dec(v_h__2_1638_);
v_size_1641_ = lean_ctor_get(v_x_1635_, 0);
lean_inc(v_size_1641_);
v_k_1642_ = lean_ctor_get(v_x_1635_, 1);
lean_inc(v_k_1642_);
v_v_1643_ = lean_ctor_get(v_x_1635_, 2);
lean_inc(v_v_1643_);
v_l_1644_ = lean_ctor_get(v_x_1635_, 3);
lean_inc(v_l_1644_);
lean_dec_ref(v_x_1635_);
v_size_1645_ = lean_ctor_get(v_r_1640_, 0);
lean_inc(v_size_1645_);
v_k_1646_ = lean_ctor_get(v_r_1640_, 1);
lean_inc(v_k_1646_);
v_v_1647_ = lean_ctor_get(v_r_1640_, 2);
lean_inc(v_v_1647_);
v_l_1648_ = lean_ctor_get(v_r_1640_, 3);
lean_inc(v_l_1648_);
v_r_1649_ = lean_ctor_get(v_r_1640_, 4);
lean_inc(v_r_1649_);
lean_dec_ref(v_r_1640_);
v___x_1650_ = lean_apply_10(v_h__3_1639_, v_size_1641_, v_k_1642_, v_v_1643_, v_l_1644_, v_size_1645_, v_k_1646_, v_v_1647_, v_l_1648_, v_r_1649_, v_x_1636_);
return v___x_1650_;
}
else
{
lean_object* v_size_1651_; lean_object* v_k_1652_; lean_object* v_v_1653_; lean_object* v_l_1654_; lean_object* v___x_1655_; 
lean_dec(v_h__3_1639_);
v_size_1651_ = lean_ctor_get(v_x_1635_, 0);
lean_inc(v_size_1651_);
v_k_1652_ = lean_ctor_get(v_x_1635_, 1);
lean_inc(v_k_1652_);
v_v_1653_ = lean_ctor_get(v_x_1635_, 2);
lean_inc(v_v_1653_);
v_l_1654_ = lean_ctor_get(v_x_1635_, 3);
lean_inc(v_l_1654_);
lean_dec_ref(v_x_1635_);
v___x_1655_ = lean_apply_5(v_h__2_1638_, v_size_1651_, v_k_1652_, v_v_1653_, v_l_1654_, v_x_1636_);
return v___x_1655_;
}
}
else
{
lean_object* v___x_1656_; 
lean_dec(v_h__3_1639_);
lean_dec(v_h__2_1638_);
v___x_1656_ = lean_apply_1(v_h__1_1637_, v_x_1636_);
return v___x_1656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object* v_x_1657_){
_start:
{
if (lean_obj_tag(v_x_1657_) == 0)
{
lean_object* v_l_1658_; 
v_l_1658_ = lean_ctor_get(v_x_1657_, 3);
if (lean_obj_tag(v_l_1658_) == 0)
{
v_x_1657_ = v_l_1658_;
goto _start;
}
else
{
lean_object* v_k_1660_; lean_object* v___x_1661_; 
v_k_1660_ = lean_ctor_get(v_x_1657_, 1);
lean_inc(v_k_1660_);
v___x_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1661_, 0, v_k_1660_);
return v___x_1661_;
}
}
else
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_box(0);
return v___x_1662_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg___boxed(lean_object* v_x_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1663_);
lean_dec(v_x_1663_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f(lean_object* v_00_u03b1_1665_, lean_object* v_00_u03b2_1666_, lean_object* v_x_1667_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1667_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___boxed(lean_object* v_00_u03b1_1669_, lean_object* v_00_u03b2_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v_res_1672_; 
v_res_1672_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f(v_00_u03b1_1669_, v_00_u03b2_1670_, v_x_1671_);
lean_dec(v_x_1671_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object* v_x_1673_){
_start:
{
lean_object* v_l_1674_; 
v_l_1674_ = lean_ctor_get(v_x_1673_, 3);
if (lean_obj_tag(v_l_1674_) == 0)
{
v_x_1673_ = v_l_1674_;
goto _start;
}
else
{
lean_object* v_k_1676_; 
v_k_1676_ = lean_ctor_get(v_x_1673_, 1);
lean_inc(v_k_1676_);
return v_k_1676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg___boxed(lean_object* v_x_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1677_);
lean_dec(v_x_1677_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey(lean_object* v_00_u03b1_1679_, lean_object* v_00_u03b2_1680_, lean_object* v_x_1681_, lean_object* v_x_1682_){
_start:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1681_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___boxed(lean_object* v_00_u03b1_1684_, lean_object* v_00_u03b2_1685_, lean_object* v_x_1686_, lean_object* v_x_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Std_DTreeMap_Internal_Impl_minKey(v_00_u03b1_1684_, v_00_u03b2_1685_, v_x_1686_, v_x_1687_);
lean_dec(v_x_1686_);
return v_res_1688_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1690_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1691_ = lean_unsigned_to_nat(13u);
v___x_1692_ = lean_unsigned_to_nat(413u);
v___x_1693_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0));
v___x_1694_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1695_ = l_mkPanicMessageWithDecl(v___x_1694_, v___x_1693_, v___x_1692_, v___x_1691_, v___x_1690_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object* v_inst_1696_, lean_object* v_x_1697_){
_start:
{
if (lean_obj_tag(v_x_1697_) == 0)
{
lean_object* v_l_1698_; 
v_l_1698_ = lean_ctor_get(v_x_1697_, 3);
if (lean_obj_tag(v_l_1698_) == 0)
{
v_x_1697_ = v_l_1698_;
goto _start;
}
else
{
lean_object* v_k_1700_; 
lean_dec(v_inst_1696_);
v_k_1700_ = lean_ctor_get(v_x_1697_, 1);
lean_inc(v_k_1700_);
return v_k_1700_;
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; 
v___x_1701_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1);
v___x_1702_ = l_panic___redArg(v_inst_1696_, v___x_1701_);
return v___x_1702_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___boxed(lean_object* v_inst_1703_, lean_object* v_x_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1703_, v_x_1704_);
lean_dec(v_x_1704_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21(lean_object* v_00_u03b1_1706_, lean_object* v_00_u03b2_1707_, lean_object* v_inst_1708_, lean_object* v_x_1709_){
_start:
{
lean_object* v___x_1710_; 
v___x_1710_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1708_, v_x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___boxed(lean_object* v_00_u03b1_1711_, lean_object* v_00_u03b2_1712_, lean_object* v_inst_1713_, lean_object* v_x_1714_){
_start:
{
lean_object* v_res_1715_; 
v_res_1715_ = l_Std_DTreeMap_Internal_Impl_minKey_x21(v_00_u03b1_1711_, v_00_u03b2_1712_, v_inst_1713_, v_x_1714_);
lean_dec(v_x_1714_);
return v_res_1715_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object* v_x_1716_, lean_object* v_x_1717_){
_start:
{
if (lean_obj_tag(v_x_1716_) == 0)
{
lean_object* v_l_1718_; 
v_l_1718_ = lean_ctor_get(v_x_1716_, 3);
if (lean_obj_tag(v_l_1718_) == 0)
{
v_x_1716_ = v_l_1718_;
goto _start;
}
else
{
lean_object* v_k_1720_; 
v_k_1720_ = lean_ctor_get(v_x_1716_, 1);
lean_inc(v_k_1720_);
return v_k_1720_;
}
}
else
{
lean_inc(v_x_1717_);
return v_x_1717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg___boxed(lean_object* v_x_1721_, lean_object* v_x_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1721_, v_x_1722_);
lean_dec(v_x_1722_);
lean_dec(v_x_1721_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD(lean_object* v_00_u03b1_1724_, lean_object* v_00_u03b2_1725_, lean_object* v_x_1726_, lean_object* v_x_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1726_, v_x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___boxed(lean_object* v_00_u03b1_1729_, lean_object* v_00_u03b2_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Std_DTreeMap_Internal_Impl_minKeyD(v_00_u03b1_1729_, v_00_u03b2_1730_, v_x_1731_, v_x_1732_);
lean_dec(v_x_1732_);
lean_dec(v_x_1731_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1734_, lean_object* v_x_1735_, lean_object* v_h__1_1736_, lean_object* v_h__2_1737_, lean_object* v_h__3_1738_){
_start:
{
if (lean_obj_tag(v_x_1734_) == 0)
{
lean_object* v_l_1739_; 
lean_dec(v_h__1_1736_);
v_l_1739_ = lean_ctor_get(v_x_1734_, 3);
if (lean_obj_tag(v_l_1739_) == 0)
{
lean_object* v_size_1740_; lean_object* v_k_1741_; lean_object* v_v_1742_; lean_object* v_r_1743_; lean_object* v_size_1744_; lean_object* v_k_1745_; lean_object* v_v_1746_; lean_object* v_l_1747_; lean_object* v_r_1748_; lean_object* v___x_1749_; 
lean_inc_ref(v_l_1739_);
lean_dec(v_h__2_1737_);
v_size_1740_ = lean_ctor_get(v_x_1734_, 0);
lean_inc(v_size_1740_);
v_k_1741_ = lean_ctor_get(v_x_1734_, 1);
lean_inc(v_k_1741_);
v_v_1742_ = lean_ctor_get(v_x_1734_, 2);
lean_inc(v_v_1742_);
v_r_1743_ = lean_ctor_get(v_x_1734_, 4);
lean_inc(v_r_1743_);
lean_dec_ref(v_x_1734_);
v_size_1744_ = lean_ctor_get(v_l_1739_, 0);
lean_inc(v_size_1744_);
v_k_1745_ = lean_ctor_get(v_l_1739_, 1);
lean_inc(v_k_1745_);
v_v_1746_ = lean_ctor_get(v_l_1739_, 2);
lean_inc(v_v_1746_);
v_l_1747_ = lean_ctor_get(v_l_1739_, 3);
lean_inc(v_l_1747_);
v_r_1748_ = lean_ctor_get(v_l_1739_, 4);
lean_inc(v_r_1748_);
lean_dec_ref(v_l_1739_);
v___x_1749_ = lean_apply_10(v_h__3_1738_, v_size_1740_, v_k_1741_, v_v_1742_, v_size_1744_, v_k_1745_, v_v_1746_, v_l_1747_, v_r_1748_, v_r_1743_, v_x_1735_);
return v___x_1749_;
}
else
{
lean_object* v_size_1750_; lean_object* v_k_1751_; lean_object* v_v_1752_; lean_object* v_r_1753_; lean_object* v___x_1754_; 
lean_dec(v_h__3_1738_);
v_size_1750_ = lean_ctor_get(v_x_1734_, 0);
lean_inc(v_size_1750_);
v_k_1751_ = lean_ctor_get(v_x_1734_, 1);
lean_inc(v_k_1751_);
v_v_1752_ = lean_ctor_get(v_x_1734_, 2);
lean_inc(v_v_1752_);
v_r_1753_ = lean_ctor_get(v_x_1734_, 4);
lean_inc(v_r_1753_);
lean_dec_ref(v_x_1734_);
v___x_1754_ = lean_apply_5(v_h__2_1737_, v_size_1750_, v_k_1751_, v_v_1752_, v_r_1753_, v_x_1735_);
return v___x_1754_;
}
}
else
{
lean_object* v___x_1755_; 
lean_dec(v_h__3_1738_);
lean_dec(v_h__2_1737_);
v___x_1755_ = lean_apply_1(v_h__1_1736_, v_x_1735_);
return v___x_1755_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1756_, lean_object* v_00_u03b2_1757_, lean_object* v_motive_1758_, lean_object* v_x_1759_, lean_object* v_x_1760_, lean_object* v_h__1_1761_, lean_object* v_h__2_1762_, lean_object* v_h__3_1763_){
_start:
{
if (lean_obj_tag(v_x_1759_) == 0)
{
lean_object* v_l_1764_; 
lean_dec(v_h__1_1761_);
v_l_1764_ = lean_ctor_get(v_x_1759_, 3);
if (lean_obj_tag(v_l_1764_) == 0)
{
lean_object* v_size_1765_; lean_object* v_k_1766_; lean_object* v_v_1767_; lean_object* v_r_1768_; lean_object* v_size_1769_; lean_object* v_k_1770_; lean_object* v_v_1771_; lean_object* v_l_1772_; lean_object* v_r_1773_; lean_object* v___x_1774_; 
lean_inc_ref(v_l_1764_);
lean_dec(v_h__2_1762_);
v_size_1765_ = lean_ctor_get(v_x_1759_, 0);
lean_inc(v_size_1765_);
v_k_1766_ = lean_ctor_get(v_x_1759_, 1);
lean_inc(v_k_1766_);
v_v_1767_ = lean_ctor_get(v_x_1759_, 2);
lean_inc(v_v_1767_);
v_r_1768_ = lean_ctor_get(v_x_1759_, 4);
lean_inc(v_r_1768_);
lean_dec_ref(v_x_1759_);
v_size_1769_ = lean_ctor_get(v_l_1764_, 0);
lean_inc(v_size_1769_);
v_k_1770_ = lean_ctor_get(v_l_1764_, 1);
lean_inc(v_k_1770_);
v_v_1771_ = lean_ctor_get(v_l_1764_, 2);
lean_inc(v_v_1771_);
v_l_1772_ = lean_ctor_get(v_l_1764_, 3);
lean_inc(v_l_1772_);
v_r_1773_ = lean_ctor_get(v_l_1764_, 4);
lean_inc(v_r_1773_);
lean_dec_ref(v_l_1764_);
v___x_1774_ = lean_apply_10(v_h__3_1763_, v_size_1765_, v_k_1766_, v_v_1767_, v_size_1769_, v_k_1770_, v_v_1771_, v_l_1772_, v_r_1773_, v_r_1768_, v_x_1760_);
return v___x_1774_;
}
else
{
lean_object* v_size_1775_; lean_object* v_k_1776_; lean_object* v_v_1777_; lean_object* v_r_1778_; lean_object* v___x_1779_; 
lean_dec(v_h__3_1763_);
v_size_1775_ = lean_ctor_get(v_x_1759_, 0);
lean_inc(v_size_1775_);
v_k_1776_ = lean_ctor_get(v_x_1759_, 1);
lean_inc(v_k_1776_);
v_v_1777_ = lean_ctor_get(v_x_1759_, 2);
lean_inc(v_v_1777_);
v_r_1778_ = lean_ctor_get(v_x_1759_, 4);
lean_inc(v_r_1778_);
lean_dec_ref(v_x_1759_);
v___x_1779_ = lean_apply_5(v_h__2_1762_, v_size_1775_, v_k_1776_, v_v_1777_, v_r_1778_, v_x_1760_);
return v___x_1779_;
}
}
else
{
lean_object* v___x_1780_; 
lean_dec(v_h__3_1763_);
lean_dec(v_h__2_1762_);
v___x_1780_ = lean_apply_1(v_h__1_1761_, v_x_1760_);
return v___x_1780_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object* v_x_1781_){
_start:
{
if (lean_obj_tag(v_x_1781_) == 0)
{
lean_object* v_r_1782_; 
v_r_1782_ = lean_ctor_get(v_x_1781_, 4);
if (lean_obj_tag(v_r_1782_) == 0)
{
v_x_1781_ = v_r_1782_;
goto _start;
}
else
{
lean_object* v_k_1784_; lean_object* v___x_1785_; 
v_k_1784_ = lean_ctor_get(v_x_1781_, 1);
lean_inc(v_k_1784_);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v_k_1784_);
return v___x_1785_;
}
}
else
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_box(0);
return v___x_1786_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg___boxed(lean_object* v_x_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1787_);
lean_dec(v_x_1787_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f(lean_object* v_00_u03b1_1789_, lean_object* v_00_u03b2_1790_, lean_object* v_x_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___boxed(lean_object* v_00_u03b1_1793_, lean_object* v_00_u03b2_1794_, lean_object* v_x_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f(v_00_u03b1_1793_, v_00_u03b2_1794_, v_x_1795_);
lean_dec(v_x_1795_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object* v_x_1797_){
_start:
{
lean_object* v_r_1798_; 
v_r_1798_ = lean_ctor_get(v_x_1797_, 4);
if (lean_obj_tag(v_r_1798_) == 0)
{
v_x_1797_ = v_r_1798_;
goto _start;
}
else
{
lean_object* v_k_1800_; 
v_k_1800_ = lean_ctor_get(v_x_1797_, 1);
lean_inc(v_k_1800_);
return v_k_1800_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg___boxed(lean_object* v_x_1801_){
_start:
{
lean_object* v_res_1802_; 
v_res_1802_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1801_);
lean_dec(v_x_1801_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey(lean_object* v_00_u03b1_1803_, lean_object* v_00_u03b2_1804_, lean_object* v_x_1805_, lean_object* v_x_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1805_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___boxed(lean_object* v_00_u03b1_1808_, lean_object* v_00_u03b2_1809_, lean_object* v_x_1810_, lean_object* v_x_1811_){
_start:
{
lean_object* v_res_1812_; 
v_res_1812_ = l_Std_DTreeMap_Internal_Impl_maxKey(v_00_u03b1_1808_, v_00_u03b2_1809_, v_x_1810_, v_x_1811_);
lean_dec(v_x_1810_);
return v_res_1812_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1814_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1815_ = lean_unsigned_to_nat(13u);
v___x_1816_ = lean_unsigned_to_nat(436u);
v___x_1817_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0));
v___x_1818_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1819_ = l_mkPanicMessageWithDecl(v___x_1818_, v___x_1817_, v___x_1816_, v___x_1815_, v___x_1814_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object* v_inst_1820_, lean_object* v_x_1821_){
_start:
{
if (lean_obj_tag(v_x_1821_) == 0)
{
lean_object* v_r_1822_; 
v_r_1822_ = lean_ctor_get(v_x_1821_, 4);
if (lean_obj_tag(v_r_1822_) == 0)
{
v_x_1821_ = v_r_1822_;
goto _start;
}
else
{
lean_object* v_k_1824_; 
lean_dec(v_inst_1820_);
v_k_1824_ = lean_ctor_get(v_x_1821_, 1);
lean_inc(v_k_1824_);
return v_k_1824_;
}
}
else
{
lean_object* v___x_1825_; lean_object* v___x_1826_; 
v___x_1825_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1);
v___x_1826_ = l_panic___redArg(v_inst_1820_, v___x_1825_);
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___boxed(lean_object* v_inst_1827_, lean_object* v_x_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1827_, v_x_1828_);
lean_dec(v_x_1828_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21(lean_object* v_00_u03b1_1830_, lean_object* v_00_u03b2_1831_, lean_object* v_inst_1832_, lean_object* v_x_1833_){
_start:
{
lean_object* v___x_1834_; 
v___x_1834_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1832_, v_x_1833_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___boxed(lean_object* v_00_u03b1_1835_, lean_object* v_00_u03b2_1836_, lean_object* v_inst_1837_, lean_object* v_x_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21(v_00_u03b1_1835_, v_00_u03b2_1836_, v_inst_1837_, v_x_1838_);
lean_dec(v_x_1838_);
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object* v_x_1840_, lean_object* v_x_1841_){
_start:
{
if (lean_obj_tag(v_x_1840_) == 0)
{
lean_object* v_r_1842_; 
v_r_1842_ = lean_ctor_get(v_x_1840_, 4);
if (lean_obj_tag(v_r_1842_) == 0)
{
v_x_1840_ = v_r_1842_;
goto _start;
}
else
{
lean_object* v_k_1844_; 
v_k_1844_ = lean_ctor_get(v_x_1840_, 1);
lean_inc(v_k_1844_);
return v_k_1844_;
}
}
else
{
lean_inc(v_x_1841_);
return v_x_1841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg___boxed(lean_object* v_x_1845_, lean_object* v_x_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1845_, v_x_1846_);
lean_dec(v_x_1846_);
lean_dec(v_x_1845_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD(lean_object* v_00_u03b1_1848_, lean_object* v_00_u03b2_1849_, lean_object* v_x_1850_, lean_object* v_x_1851_){
_start:
{
lean_object* v___x_1852_; 
v___x_1852_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1850_, v_x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___boxed(lean_object* v_00_u03b1_1853_, lean_object* v_00_u03b2_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Std_DTreeMap_Internal_Impl_maxKeyD(v_00_u03b1_1853_, v_00_u03b2_1854_, v_x_1855_, v_x_1856_);
lean_dec(v_x_1856_);
lean_dec(v_x_1855_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1858_, lean_object* v_x_1859_, lean_object* v_h__1_1860_, lean_object* v_h__2_1861_, lean_object* v_h__3_1862_){
_start:
{
if (lean_obj_tag(v_x_1858_) == 0)
{
lean_object* v_r_1863_; 
lean_dec(v_h__1_1860_);
v_r_1863_ = lean_ctor_get(v_x_1858_, 4);
if (lean_obj_tag(v_r_1863_) == 0)
{
lean_object* v_size_1864_; lean_object* v_k_1865_; lean_object* v_v_1866_; lean_object* v_l_1867_; lean_object* v_size_1868_; lean_object* v_k_1869_; lean_object* v_v_1870_; lean_object* v_l_1871_; lean_object* v_r_1872_; lean_object* v___x_1873_; 
lean_inc_ref(v_r_1863_);
lean_dec(v_h__2_1861_);
v_size_1864_ = lean_ctor_get(v_x_1858_, 0);
lean_inc(v_size_1864_);
v_k_1865_ = lean_ctor_get(v_x_1858_, 1);
lean_inc(v_k_1865_);
v_v_1866_ = lean_ctor_get(v_x_1858_, 2);
lean_inc(v_v_1866_);
v_l_1867_ = lean_ctor_get(v_x_1858_, 3);
lean_inc(v_l_1867_);
lean_dec_ref(v_x_1858_);
v_size_1868_ = lean_ctor_get(v_r_1863_, 0);
lean_inc(v_size_1868_);
v_k_1869_ = lean_ctor_get(v_r_1863_, 1);
lean_inc(v_k_1869_);
v_v_1870_ = lean_ctor_get(v_r_1863_, 2);
lean_inc(v_v_1870_);
v_l_1871_ = lean_ctor_get(v_r_1863_, 3);
lean_inc(v_l_1871_);
v_r_1872_ = lean_ctor_get(v_r_1863_, 4);
lean_inc(v_r_1872_);
lean_dec_ref(v_r_1863_);
v___x_1873_ = lean_apply_10(v_h__3_1862_, v_size_1864_, v_k_1865_, v_v_1866_, v_l_1867_, v_size_1868_, v_k_1869_, v_v_1870_, v_l_1871_, v_r_1872_, v_x_1859_);
return v___x_1873_;
}
else
{
lean_object* v_size_1874_; lean_object* v_k_1875_; lean_object* v_v_1876_; lean_object* v_l_1877_; lean_object* v___x_1878_; 
lean_dec(v_h__3_1862_);
v_size_1874_ = lean_ctor_get(v_x_1858_, 0);
lean_inc(v_size_1874_);
v_k_1875_ = lean_ctor_get(v_x_1858_, 1);
lean_inc(v_k_1875_);
v_v_1876_ = lean_ctor_get(v_x_1858_, 2);
lean_inc(v_v_1876_);
v_l_1877_ = lean_ctor_get(v_x_1858_, 3);
lean_inc(v_l_1877_);
lean_dec_ref(v_x_1858_);
v___x_1878_ = lean_apply_5(v_h__2_1861_, v_size_1874_, v_k_1875_, v_v_1876_, v_l_1877_, v_x_1859_);
return v___x_1878_;
}
}
else
{
lean_object* v___x_1879_; 
lean_dec(v_h__3_1862_);
lean_dec(v_h__2_1861_);
v___x_1879_ = lean_apply_1(v_h__1_1860_, v_x_1859_);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1880_, lean_object* v_00_u03b2_1881_, lean_object* v_motive_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v_h__1_1885_, lean_object* v_h__2_1886_, lean_object* v_h__3_1887_){
_start:
{
if (lean_obj_tag(v_x_1883_) == 0)
{
lean_object* v_r_1888_; 
lean_dec(v_h__1_1885_);
v_r_1888_ = lean_ctor_get(v_x_1883_, 4);
if (lean_obj_tag(v_r_1888_) == 0)
{
lean_object* v_size_1889_; lean_object* v_k_1890_; lean_object* v_v_1891_; lean_object* v_l_1892_; lean_object* v_size_1893_; lean_object* v_k_1894_; lean_object* v_v_1895_; lean_object* v_l_1896_; lean_object* v_r_1897_; lean_object* v___x_1898_; 
lean_inc_ref(v_r_1888_);
lean_dec(v_h__2_1886_);
v_size_1889_ = lean_ctor_get(v_x_1883_, 0);
lean_inc(v_size_1889_);
v_k_1890_ = lean_ctor_get(v_x_1883_, 1);
lean_inc(v_k_1890_);
v_v_1891_ = lean_ctor_get(v_x_1883_, 2);
lean_inc(v_v_1891_);
v_l_1892_ = lean_ctor_get(v_x_1883_, 3);
lean_inc(v_l_1892_);
lean_dec_ref(v_x_1883_);
v_size_1893_ = lean_ctor_get(v_r_1888_, 0);
lean_inc(v_size_1893_);
v_k_1894_ = lean_ctor_get(v_r_1888_, 1);
lean_inc(v_k_1894_);
v_v_1895_ = lean_ctor_get(v_r_1888_, 2);
lean_inc(v_v_1895_);
v_l_1896_ = lean_ctor_get(v_r_1888_, 3);
lean_inc(v_l_1896_);
v_r_1897_ = lean_ctor_get(v_r_1888_, 4);
lean_inc(v_r_1897_);
lean_dec_ref(v_r_1888_);
v___x_1898_ = lean_apply_10(v_h__3_1887_, v_size_1889_, v_k_1890_, v_v_1891_, v_l_1892_, v_size_1893_, v_k_1894_, v_v_1895_, v_l_1896_, v_r_1897_, v_x_1884_);
return v___x_1898_;
}
else
{
lean_object* v_size_1899_; lean_object* v_k_1900_; lean_object* v_v_1901_; lean_object* v_l_1902_; lean_object* v___x_1903_; 
lean_dec(v_h__3_1887_);
v_size_1899_ = lean_ctor_get(v_x_1883_, 0);
lean_inc(v_size_1899_);
v_k_1900_ = lean_ctor_get(v_x_1883_, 1);
lean_inc(v_k_1900_);
v_v_1901_ = lean_ctor_get(v_x_1883_, 2);
lean_inc(v_v_1901_);
v_l_1902_ = lean_ctor_get(v_x_1883_, 3);
lean_inc(v_l_1902_);
lean_dec_ref(v_x_1883_);
v___x_1903_ = lean_apply_5(v_h__2_1886_, v_size_1899_, v_k_1900_, v_v_1901_, v_l_1902_, v_x_1884_);
return v___x_1903_;
}
}
else
{
lean_object* v___x_1904_; 
lean_dec(v_h__3_1887_);
lean_dec(v_h__2_1886_);
v___x_1904_ = lean_apply_1(v_h__1_1885_, v_x_1884_);
return v___x_1904_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object* v_x_1905_, lean_object* v_x_1906_){
_start:
{
lean_object* v_k_1907_; lean_object* v_v_1908_; lean_object* v_l_1909_; lean_object* v_r_1910_; lean_object* v___y_1912_; lean_object* v___y_1918_; 
v_k_1907_ = lean_ctor_get(v_x_1905_, 1);
v_v_1908_ = lean_ctor_get(v_x_1905_, 2);
v_l_1909_ = lean_ctor_get(v_x_1905_, 3);
v_r_1910_ = lean_ctor_get(v_x_1905_, 4);
if (lean_obj_tag(v_l_1909_) == 0)
{
lean_object* v_size_1925_; 
v_size_1925_ = lean_ctor_get(v_l_1909_, 0);
v___y_1918_ = v_size_1925_;
goto v___jp_1917_;
}
else
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_unsigned_to_nat(0u);
v___y_1918_ = v___x_1926_;
goto v___jp_1917_;
}
v___jp_1911_:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_nat_sub(v_x_1906_, v___y_1912_);
lean_dec(v_x_1906_);
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_sub(v___x_1913_, v___x_1914_);
lean_dec(v___x_1913_);
v_x_1905_ = v_r_1910_;
v_x_1906_ = v___x_1915_;
goto _start;
}
v___jp_1917_:
{
uint8_t v___x_1919_; 
v___x_1919_ = lean_nat_dec_lt(v_x_1906_, v___y_1918_);
if (v___x_1919_ == 0)
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_nat_dec_eq(v_x_1906_, v___y_1918_);
if (v___x_1920_ == 0)
{
if (lean_obj_tag(v_l_1909_) == 0)
{
lean_object* v_size_1921_; 
v_size_1921_ = lean_ctor_get(v_l_1909_, 0);
v___y_1912_ = v_size_1921_;
goto v___jp_1911_;
}
else
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_unsigned_to_nat(0u);
v___y_1912_ = v___x_1922_;
goto v___jp_1911_;
}
}
else
{
lean_object* v___x_1923_; 
lean_dec(v_x_1906_);
lean_inc(v_v_1908_);
lean_inc(v_k_1907_);
v___x_1923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1923_, 0, v_k_1907_);
lean_ctor_set(v___x_1923_, 1, v_v_1908_);
return v___x_1923_;
}
}
else
{
v_x_1905_ = v_l_1909_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg___boxed(lean_object* v_x_1927_, lean_object* v_x_1928_){
_start:
{
lean_object* v_res_1929_; 
v_res_1929_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1927_, v_x_1928_);
lean_dec(v_x_1927_);
return v_res_1929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx(lean_object* v_00_u03b1_1930_, lean_object* v_00_u03b2_1931_, lean_object* v_x_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_, lean_object* v_x_1935_){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1932_, v_x_1934_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___boxed(lean_object* v_00_u03b1_1937_, lean_object* v_00_u03b2_1938_, lean_object* v_x_1939_, lean_object* v_x_1940_, lean_object* v_x_1941_, lean_object* v_x_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx(v_00_u03b1_1937_, v_00_u03b2_1938_, v_x_1939_, v_x_1940_, v_x_1941_, v_x_1942_);
lean_dec(v_x_1939_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object* v_x_1944_, lean_object* v_x_1945_){
_start:
{
if (lean_obj_tag(v_x_1944_) == 0)
{
lean_object* v_k_1946_; lean_object* v_v_1947_; lean_object* v_l_1948_; lean_object* v_r_1949_; lean_object* v___y_1951_; lean_object* v___y_1957_; 
v_k_1946_ = lean_ctor_get(v_x_1944_, 1);
v_v_1947_ = lean_ctor_get(v_x_1944_, 2);
v_l_1948_ = lean_ctor_get(v_x_1944_, 3);
v_r_1949_ = lean_ctor_get(v_x_1944_, 4);
if (lean_obj_tag(v_l_1948_) == 0)
{
lean_object* v_size_1965_; 
v_size_1965_ = lean_ctor_get(v_l_1948_, 0);
v___y_1957_ = v_size_1965_;
goto v___jp_1956_;
}
else
{
lean_object* v___x_1966_; 
v___x_1966_ = lean_unsigned_to_nat(0u);
v___y_1957_ = v___x_1966_;
goto v___jp_1956_;
}
v___jp_1950_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
v___x_1952_ = lean_nat_sub(v_x_1945_, v___y_1951_);
lean_dec(v_x_1945_);
v___x_1953_ = lean_unsigned_to_nat(1u);
v___x_1954_ = lean_nat_sub(v___x_1952_, v___x_1953_);
lean_dec(v___x_1952_);
v_x_1944_ = v_r_1949_;
v_x_1945_ = v___x_1954_;
goto _start;
}
v___jp_1956_:
{
uint8_t v___x_1958_; 
v___x_1958_ = lean_nat_dec_lt(v_x_1945_, v___y_1957_);
if (v___x_1958_ == 0)
{
uint8_t v___x_1959_; 
v___x_1959_ = lean_nat_dec_eq(v_x_1945_, v___y_1957_);
if (v___x_1959_ == 0)
{
if (lean_obj_tag(v_l_1948_) == 0)
{
lean_object* v_size_1960_; 
v_size_1960_ = lean_ctor_get(v_l_1948_, 0);
v___y_1951_ = v_size_1960_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_unsigned_to_nat(0u);
v___y_1951_ = v___x_1961_;
goto v___jp_1950_;
}
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec(v_x_1945_);
lean_inc(v_v_1947_);
lean_inc(v_k_1946_);
v___x_1962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1962_, 0, v_k_1946_);
lean_ctor_set(v___x_1962_, 1, v_v_1947_);
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v___x_1962_);
return v___x_1963_;
}
}
else
{
v_x_1944_ = v_l_1948_;
goto _start;
}
}
}
else
{
lean_object* v___x_1967_; 
lean_dec(v_x_1945_);
v___x_1967_ = lean_box(0);
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_1968_, lean_object* v_x_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_1968_, v_x_1969_);
lean_dec(v_x_1968_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(lean_object* v_00_u03b1_1971_, lean_object* v_00_u03b2_1972_, lean_object* v_x_1973_, lean_object* v_x_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_1973_, v_x_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1976_, lean_object* v_00_u03b2_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(v_00_u03b1_1976_, v_00_u03b2_1977_, v_x_1978_, v_x_1979_);
lean_dec(v_x_1978_);
return v_res_1980_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1983_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_1984_ = lean_unsigned_to_nat(16u);
v___x_1985_ = lean_unsigned_to_nat(467u);
v___x_1986_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0));
v___x_1987_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1988_ = l_mkPanicMessageWithDecl(v___x_1987_, v___x_1986_, v___x_1985_, v___x_1984_, v___x_1983_);
return v___x_1988_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(lean_object* v_inst_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_){
_start:
{
if (lean_obj_tag(v_x_1990_) == 0)
{
lean_object* v_k_1992_; lean_object* v_v_1993_; lean_object* v_l_1994_; lean_object* v_r_1995_; lean_object* v___y_1997_; lean_object* v___y_2003_; 
v_k_1992_ = lean_ctor_get(v_x_1990_, 1);
v_v_1993_ = lean_ctor_get(v_x_1990_, 2);
v_l_1994_ = lean_ctor_get(v_x_1990_, 3);
v_r_1995_ = lean_ctor_get(v_x_1990_, 4);
if (lean_obj_tag(v_l_1994_) == 0)
{
lean_object* v_size_2010_; 
v_size_2010_ = lean_ctor_get(v_l_1994_, 0);
v___y_2003_ = v_size_2010_;
goto v___jp_2002_;
}
else
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_unsigned_to_nat(0u);
v___y_2003_ = v___x_2011_;
goto v___jp_2002_;
}
v___jp_1996_:
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1998_ = lean_nat_sub(v_x_1991_, v___y_1997_);
lean_dec(v_x_1991_);
v___x_1999_ = lean_unsigned_to_nat(1u);
v___x_2000_ = lean_nat_sub(v___x_1998_, v___x_1999_);
lean_dec(v___x_1998_);
v_x_1990_ = v_r_1995_;
v_x_1991_ = v___x_2000_;
goto _start;
}
v___jp_2002_:
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_nat_dec_lt(v_x_1991_, v___y_2003_);
if (v___x_2004_ == 0)
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_nat_dec_eq(v_x_1991_, v___y_2003_);
if (v___x_2005_ == 0)
{
if (lean_obj_tag(v_l_1994_) == 0)
{
lean_object* v_size_2006_; 
v_size_2006_ = lean_ctor_get(v_l_1994_, 0);
v___y_1997_ = v_size_2006_;
goto v___jp_1996_;
}
else
{
lean_object* v___x_2007_; 
v___x_2007_ = lean_unsigned_to_nat(0u);
v___y_1997_ = v___x_2007_;
goto v___jp_1996_;
}
}
else
{
lean_object* v___x_2008_; 
lean_dec(v_x_1991_);
lean_dec_ref(v_inst_1989_);
lean_inc(v_v_1993_);
lean_inc(v_k_1992_);
v___x_2008_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2008_, 0, v_k_1992_);
lean_ctor_set(v___x_2008_, 1, v_v_1993_);
return v___x_2008_;
}
}
else
{
v_x_1990_ = v_l_1994_;
goto _start;
}
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_x_1991_);
v___x_2012_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2);
v___x_2013_ = l_panic___redArg(v_inst_1989_, v___x_2012_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2014_, v_x_2015_, v_x_2016_);
lean_dec(v_x_2015_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(lean_object* v_00_u03b1_2018_, lean_object* v_00_u03b2_2019_, lean_object* v_inst_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_){
_start:
{
lean_object* v___x_2023_; 
v___x_2023_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2020_, v_x_2021_, v_x_2022_);
return v___x_2023_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_2024_, lean_object* v_00_u03b2_2025_, lean_object* v_inst_2026_, lean_object* v_x_2027_, lean_object* v_x_2028_){
_start:
{
lean_object* v_res_2029_; 
v_res_2029_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(v_00_u03b1_2024_, v_00_u03b2_2025_, v_inst_2026_, v_x_2027_, v_x_2028_);
lean_dec(v_x_2027_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object* v_x_2030_, lean_object* v_x_2031_, lean_object* v_x_2032_){
_start:
{
if (lean_obj_tag(v_x_2030_) == 0)
{
lean_object* v_k_2033_; lean_object* v_v_2034_; lean_object* v_l_2035_; lean_object* v_r_2036_; lean_object* v___y_2038_; lean_object* v___y_2044_; 
v_k_2033_ = lean_ctor_get(v_x_2030_, 1);
v_v_2034_ = lean_ctor_get(v_x_2030_, 2);
v_l_2035_ = lean_ctor_get(v_x_2030_, 3);
v_r_2036_ = lean_ctor_get(v_x_2030_, 4);
if (lean_obj_tag(v_l_2035_) == 0)
{
lean_object* v_size_2051_; 
v_size_2051_ = lean_ctor_get(v_l_2035_, 0);
v___y_2044_ = v_size_2051_;
goto v___jp_2043_;
}
else
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_unsigned_to_nat(0u);
v___y_2044_ = v___x_2052_;
goto v___jp_2043_;
}
v___jp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2039_ = lean_nat_sub(v_x_2031_, v___y_2038_);
lean_dec(v_x_2031_);
v___x_2040_ = lean_unsigned_to_nat(1u);
v___x_2041_ = lean_nat_sub(v___x_2039_, v___x_2040_);
lean_dec(v___x_2039_);
v_x_2030_ = v_r_2036_;
v_x_2031_ = v___x_2041_;
goto _start;
}
v___jp_2043_:
{
uint8_t v___x_2045_; 
v___x_2045_ = lean_nat_dec_lt(v_x_2031_, v___y_2044_);
if (v___x_2045_ == 0)
{
uint8_t v___x_2046_; 
v___x_2046_ = lean_nat_dec_eq(v_x_2031_, v___y_2044_);
if (v___x_2046_ == 0)
{
if (lean_obj_tag(v_l_2035_) == 0)
{
lean_object* v_size_2047_; 
v_size_2047_ = lean_ctor_get(v_l_2035_, 0);
v___y_2038_ = v_size_2047_;
goto v___jp_2037_;
}
else
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_unsigned_to_nat(0u);
v___y_2038_ = v___x_2048_;
goto v___jp_2037_;
}
}
else
{
lean_object* v___x_2049_; 
lean_dec(v_x_2031_);
lean_inc(v_v_2034_);
lean_inc(v_k_2033_);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v_k_2033_);
lean_ctor_set(v___x_2049_, 1, v_v_2034_);
return v___x_2049_;
}
}
else
{
v_x_2030_ = v_l_2035_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2031_);
lean_inc_ref(v_x_2032_);
return v_x_2032_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg___boxed(lean_object* v_x_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2053_, v_x_2054_, v_x_2055_);
lean_dec_ref(v_x_2055_);
lean_dec(v_x_2053_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD(lean_object* v_00_u03b1_2057_, lean_object* v_00_u03b2_2058_, lean_object* v_x_2059_, lean_object* v_x_2060_, lean_object* v_x_2061_){
_start:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2059_, v_x_2060_, v_x_2061_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___boxed(lean_object* v_00_u03b1_2063_, lean_object* v_00_u03b2_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_, lean_object* v_x_2067_){
_start:
{
lean_object* v_res_2068_; 
v_res_2068_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD(v_00_u03b1_2063_, v_00_u03b2_2064_, v_x_2065_, v_x_2066_, v_x_2067_);
lean_dec_ref(v_x_2067_);
lean_dec(v_x_2065_);
return v_res_2068_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object* v_x_2069_, lean_object* v_x_2070_){
_start:
{
lean_object* v_k_2071_; lean_object* v_l_2072_; lean_object* v_r_2073_; lean_object* v___y_2075_; lean_object* v___y_2081_; 
v_k_2071_ = lean_ctor_get(v_x_2069_, 1);
v_l_2072_ = lean_ctor_get(v_x_2069_, 3);
v_r_2073_ = lean_ctor_get(v_x_2069_, 4);
if (lean_obj_tag(v_l_2072_) == 0)
{
lean_object* v_size_2087_; 
v_size_2087_ = lean_ctor_get(v_l_2072_, 0);
v___y_2081_ = v_size_2087_;
goto v___jp_2080_;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_unsigned_to_nat(0u);
v___y_2081_ = v___x_2088_;
goto v___jp_2080_;
}
v___jp_2074_:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = lean_nat_sub(v_x_2070_, v___y_2075_);
lean_dec(v_x_2070_);
v___x_2077_ = lean_unsigned_to_nat(1u);
v___x_2078_ = lean_nat_sub(v___x_2076_, v___x_2077_);
lean_dec(v___x_2076_);
v_x_2069_ = v_r_2073_;
v_x_2070_ = v___x_2078_;
goto _start;
}
v___jp_2080_:
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_nat_dec_lt(v_x_2070_, v___y_2081_);
if (v___x_2082_ == 0)
{
uint8_t v___x_2083_; 
v___x_2083_ = lean_nat_dec_eq(v_x_2070_, v___y_2081_);
if (v___x_2083_ == 0)
{
if (lean_obj_tag(v_l_2072_) == 0)
{
lean_object* v_size_2084_; 
v_size_2084_ = lean_ctor_get(v_l_2072_, 0);
v___y_2075_ = v_size_2084_;
goto v___jp_2074_;
}
else
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_unsigned_to_nat(0u);
v___y_2075_ = v___x_2085_;
goto v___jp_2074_;
}
}
else
{
lean_dec(v_x_2070_);
lean_inc(v_k_2071_);
return v_k_2071_;
}
}
else
{
v_x_2069_ = v_l_2072_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg___boxed(lean_object* v_x_2089_, lean_object* v_x_2090_){
_start:
{
lean_object* v_res_2091_; 
v_res_2091_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2089_, v_x_2090_);
lean_dec(v_x_2089_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx(lean_object* v_00_u03b1_2092_, lean_object* v_00_u03b2_2093_, lean_object* v_x_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2094_, v_x_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___boxed(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx(v_00_u03b1_2099_, v_00_u03b2_2100_, v_x_2101_, v_x_2102_, v_x_2103_, v_x_2104_);
lean_dec(v_x_2101_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object* v_x_2106_, lean_object* v_x_2107_){
_start:
{
if (lean_obj_tag(v_x_2106_) == 0)
{
lean_object* v_k_2108_; lean_object* v_l_2109_; lean_object* v_r_2110_; lean_object* v___y_2112_; lean_object* v___y_2118_; 
v_k_2108_ = lean_ctor_get(v_x_2106_, 1);
v_l_2109_ = lean_ctor_get(v_x_2106_, 3);
v_r_2110_ = lean_ctor_get(v_x_2106_, 4);
if (lean_obj_tag(v_l_2109_) == 0)
{
lean_object* v_size_2125_; 
v_size_2125_ = lean_ctor_get(v_l_2109_, 0);
v___y_2118_ = v_size_2125_;
goto v___jp_2117_;
}
else
{
lean_object* v___x_2126_; 
v___x_2126_ = lean_unsigned_to_nat(0u);
v___y_2118_ = v___x_2126_;
goto v___jp_2117_;
}
v___jp_2111_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2113_ = lean_nat_sub(v_x_2107_, v___y_2112_);
lean_dec(v_x_2107_);
v___x_2114_ = lean_unsigned_to_nat(1u);
v___x_2115_ = lean_nat_sub(v___x_2113_, v___x_2114_);
lean_dec(v___x_2113_);
v_x_2106_ = v_r_2110_;
v_x_2107_ = v___x_2115_;
goto _start;
}
v___jp_2117_:
{
uint8_t v___x_2119_; 
v___x_2119_ = lean_nat_dec_lt(v_x_2107_, v___y_2118_);
if (v___x_2119_ == 0)
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_nat_dec_eq(v_x_2107_, v___y_2118_);
if (v___x_2120_ == 0)
{
if (lean_obj_tag(v_l_2109_) == 0)
{
lean_object* v_size_2121_; 
v_size_2121_ = lean_ctor_get(v_l_2109_, 0);
v___y_2112_ = v_size_2121_;
goto v___jp_2111_;
}
else
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_unsigned_to_nat(0u);
v___y_2112_ = v___x_2122_;
goto v___jp_2111_;
}
}
else
{
lean_object* v___x_2123_; 
lean_dec(v_x_2107_);
lean_inc(v_k_2108_);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v_k_2108_);
return v___x_2123_;
}
}
else
{
v_x_2106_ = v_l_2109_;
goto _start;
}
}
}
else
{
lean_object* v___x_2127_; 
lean_dec(v_x_2107_);
v___x_2127_ = lean_box(0);
return v___x_2127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg___boxed(lean_object* v_x_2128_, lean_object* v_x_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2128_, v_x_2129_);
lean_dec(v_x_2128_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(lean_object* v_00_u03b1_2131_, lean_object* v_00_u03b2_2132_, lean_object* v_x_2133_, lean_object* v_x_2134_){
_start:
{
lean_object* v___x_2135_; 
v___x_2135_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2133_, v_x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_2136_, lean_object* v_00_u03b2_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(v_00_u03b1_2136_, v_00_u03b2_2137_, v_x_2138_, v_x_2139_);
lean_dec(v_x_2138_);
return v_res_2140_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2142_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_2143_ = lean_unsigned_to_nat(16u);
v___x_2144_ = lean_unsigned_to_nat(503u);
v___x_2145_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0));
v___x_2146_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_2147_ = l_mkPanicMessageWithDecl(v___x_2146_, v___x_2145_, v___x_2144_, v___x_2143_, v___x_2142_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object* v_inst_2148_, lean_object* v_x_2149_, lean_object* v_x_2150_){
_start:
{
if (lean_obj_tag(v_x_2149_) == 0)
{
lean_object* v_k_2151_; lean_object* v_l_2152_; lean_object* v_r_2153_; lean_object* v___y_2155_; lean_object* v___y_2161_; 
v_k_2151_ = lean_ctor_get(v_x_2149_, 1);
v_l_2152_ = lean_ctor_get(v_x_2149_, 3);
v_r_2153_ = lean_ctor_get(v_x_2149_, 4);
if (lean_obj_tag(v_l_2152_) == 0)
{
lean_object* v_size_2167_; 
v_size_2167_ = lean_ctor_get(v_l_2152_, 0);
v___y_2161_ = v_size_2167_;
goto v___jp_2160_;
}
else
{
lean_object* v___x_2168_; 
v___x_2168_ = lean_unsigned_to_nat(0u);
v___y_2161_ = v___x_2168_;
goto v___jp_2160_;
}
v___jp_2154_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2156_ = lean_nat_sub(v_x_2150_, v___y_2155_);
lean_dec(v_x_2150_);
v___x_2157_ = lean_unsigned_to_nat(1u);
v___x_2158_ = lean_nat_sub(v___x_2156_, v___x_2157_);
lean_dec(v___x_2156_);
v_x_2149_ = v_r_2153_;
v_x_2150_ = v___x_2158_;
goto _start;
}
v___jp_2160_:
{
uint8_t v___x_2162_; 
v___x_2162_ = lean_nat_dec_lt(v_x_2150_, v___y_2161_);
if (v___x_2162_ == 0)
{
uint8_t v___x_2163_; 
v___x_2163_ = lean_nat_dec_eq(v_x_2150_, v___y_2161_);
if (v___x_2163_ == 0)
{
if (lean_obj_tag(v_l_2152_) == 0)
{
lean_object* v_size_2164_; 
v_size_2164_ = lean_ctor_get(v_l_2152_, 0);
v___y_2155_ = v_size_2164_;
goto v___jp_2154_;
}
else
{
lean_object* v___x_2165_; 
v___x_2165_ = lean_unsigned_to_nat(0u);
v___y_2155_ = v___x_2165_;
goto v___jp_2154_;
}
}
else
{
lean_dec(v_x_2150_);
lean_dec(v_inst_2148_);
lean_inc(v_k_2151_);
return v_k_2151_;
}
}
else
{
v_x_2149_ = v_l_2152_;
goto _start;
}
}
}
else
{
lean_object* v___x_2169_; lean_object* v___x_2170_; 
lean_dec(v_x_2150_);
v___x_2169_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1);
v___x_2170_ = l_panic___redArg(v_inst_2148_, v___x_2169_);
return v___x_2170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2171_, v_x_2172_, v_x_2173_);
lean_dec(v_x_2172_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(lean_object* v_00_u03b1_2175_, lean_object* v_00_u03b2_2176_, lean_object* v_inst_2177_, lean_object* v_x_2178_, lean_object* v_x_2179_){
_start:
{
lean_object* v___x_2180_; 
v___x_2180_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2177_, v_x_2178_, v_x_2179_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_2181_, lean_object* v_00_u03b2_2182_, lean_object* v_inst_2183_, lean_object* v_x_2184_, lean_object* v_x_2185_){
_start:
{
lean_object* v_res_2186_; 
v_res_2186_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(v_00_u03b1_2181_, v_00_u03b2_2182_, v_inst_2183_, v_x_2184_, v_x_2185_);
lean_dec(v_x_2184_);
return v_res_2186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object* v_x_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
if (lean_obj_tag(v_x_2187_) == 0)
{
lean_object* v_k_2190_; lean_object* v_l_2191_; lean_object* v_r_2192_; lean_object* v___y_2194_; lean_object* v___y_2200_; 
v_k_2190_ = lean_ctor_get(v_x_2187_, 1);
v_l_2191_ = lean_ctor_get(v_x_2187_, 3);
v_r_2192_ = lean_ctor_get(v_x_2187_, 4);
if (lean_obj_tag(v_l_2191_) == 0)
{
lean_object* v_size_2206_; 
v_size_2206_ = lean_ctor_get(v_l_2191_, 0);
v___y_2200_ = v_size_2206_;
goto v___jp_2199_;
}
else
{
lean_object* v___x_2207_; 
v___x_2207_ = lean_unsigned_to_nat(0u);
v___y_2200_ = v___x_2207_;
goto v___jp_2199_;
}
v___jp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2195_ = lean_nat_sub(v_x_2188_, v___y_2194_);
lean_dec(v_x_2188_);
v___x_2196_ = lean_unsigned_to_nat(1u);
v___x_2197_ = lean_nat_sub(v___x_2195_, v___x_2196_);
lean_dec(v___x_2195_);
v_x_2187_ = v_r_2192_;
v_x_2188_ = v___x_2197_;
goto _start;
}
v___jp_2199_:
{
uint8_t v___x_2201_; 
v___x_2201_ = lean_nat_dec_lt(v_x_2188_, v___y_2200_);
if (v___x_2201_ == 0)
{
uint8_t v___x_2202_; 
v___x_2202_ = lean_nat_dec_eq(v_x_2188_, v___y_2200_);
if (v___x_2202_ == 0)
{
if (lean_obj_tag(v_l_2191_) == 0)
{
lean_object* v_size_2203_; 
v_size_2203_ = lean_ctor_get(v_l_2191_, 0);
v___y_2194_ = v_size_2203_;
goto v___jp_2193_;
}
else
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___y_2194_ = v___x_2204_;
goto v___jp_2193_;
}
}
else
{
lean_dec(v_x_2188_);
lean_inc(v_k_2190_);
return v_k_2190_;
}
}
else
{
v_x_2187_ = v_l_2191_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2188_);
lean_inc(v_x_2189_);
return v_x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg___boxed(lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2208_, v_x_2209_, v_x_2210_);
lean_dec(v_x_2210_);
lean_dec(v_x_2208_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD(lean_object* v_00_u03b1_2212_, lean_object* v_00_u03b2_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_, lean_object* v_x_2216_){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2214_, v_x_2215_, v_x_2216_);
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___boxed(lean_object* v_00_u03b1_2218_, lean_object* v_00_u03b2_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_, lean_object* v_x_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD(v_00_u03b1_2218_, v_00_u03b2_2219_, v_x_2220_, v_x_2221_, v_x_2222_);
lean_dec(v_x_2222_);
lean_dec(v_x_2220_);
return v_res_2223_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object* v_inst_2224_, lean_object* v_k_2225_, lean_object* v_best_2226_, lean_object* v_a_2227_){
_start:
{
if (lean_obj_tag(v_a_2227_) == 0)
{
lean_object* v_k_2228_; lean_object* v_v_2229_; lean_object* v_l_2230_; lean_object* v_r_2231_; lean_object* v___x_2232_; uint8_t v___x_2233_; 
v_k_2228_ = lean_ctor_get(v_a_2227_, 1);
lean_inc(v_k_2228_);
v_v_2229_ = lean_ctor_get(v_a_2227_, 2);
lean_inc(v_v_2229_);
v_l_2230_ = lean_ctor_get(v_a_2227_, 3);
lean_inc(v_l_2230_);
v_r_2231_ = lean_ctor_get(v_a_2227_, 4);
lean_inc(v_r_2231_);
lean_dec_ref(v_a_2227_);
lean_inc_ref(v_inst_2224_);
lean_inc(v_k_2228_);
lean_inc(v_k_2225_);
v___x_2232_ = lean_apply_2(v_inst_2224_, v_k_2225_, v_k_2228_);
v___x_2233_ = lean_unbox(v___x_2232_);
switch(v___x_2233_)
{
case 0:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; 
lean_dec(v_r_2231_);
lean_dec(v_best_2226_);
v___x_2234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2234_, 0, v_k_2228_);
lean_ctor_set(v___x_2234_, 1, v_v_2229_);
v___x_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
v_best_2226_ = v___x_2235_;
v_a_2227_ = v_l_2230_;
goto _start;
}
case 1:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
lean_dec(v_r_2231_);
lean_dec(v_l_2230_);
lean_dec(v_best_2226_);
lean_dec(v_k_2225_);
lean_dec_ref(v_inst_2224_);
v___x_2237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2237_, 0, v_k_2228_);
lean_ctor_set(v___x_2237_, 1, v_v_2229_);
v___x_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
return v___x_2238_;
}
default: 
{
lean_dec(v_l_2230_);
lean_dec(v_v_2229_);
lean_dec(v_k_2228_);
v_a_2227_ = v_r_2231_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2225_);
lean_dec_ref(v_inst_2224_);
return v_best_2226_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go(lean_object* v_00_u03b1_2240_, lean_object* v_00_u03b2_2241_, lean_object* v_inst_2242_, lean_object* v_k_2243_, lean_object* v_best_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2242_, v_k_2243_, v_best_2244_, v_a_2245_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___redArg(lean_object* v_inst_2247_, lean_object* v_k_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = lean_box(0);
v___x_2251_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2247_, v_k_2248_, v___x_2250_, v_a_2249_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f(lean_object* v_00_u03b1_2252_, lean_object* v_00_u03b2_2253_, lean_object* v_inst_2254_, lean_object* v_k_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_box(0);
v___x_2258_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2254_, v_k_2255_, v___x_2257_, v_a_2256_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object* v_inst_2259_, lean_object* v_k_2260_, lean_object* v_best_2261_, lean_object* v_a_2262_){
_start:
{
if (lean_obj_tag(v_a_2262_) == 0)
{
lean_object* v_k_2263_; lean_object* v_v_2264_; lean_object* v_l_2265_; lean_object* v_r_2266_; lean_object* v___x_2267_; uint8_t v___x_2268_; 
v_k_2263_ = lean_ctor_get(v_a_2262_, 1);
lean_inc(v_k_2263_);
v_v_2264_ = lean_ctor_get(v_a_2262_, 2);
lean_inc(v_v_2264_);
v_l_2265_ = lean_ctor_get(v_a_2262_, 3);
lean_inc(v_l_2265_);
v_r_2266_ = lean_ctor_get(v_a_2262_, 4);
lean_inc(v_r_2266_);
lean_dec_ref(v_a_2262_);
lean_inc_ref(v_inst_2259_);
lean_inc(v_k_2263_);
lean_inc(v_k_2260_);
v___x_2267_ = lean_apply_2(v_inst_2259_, v_k_2260_, v_k_2263_);
v___x_2268_ = lean_unbox(v___x_2267_);
if (v___x_2268_ == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
lean_dec(v_r_2266_);
lean_dec(v_best_2261_);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v_k_2263_);
lean_ctor_set(v___x_2269_, 1, v_v_2264_);
v___x_2270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2269_);
v_best_2261_ = v___x_2270_;
v_a_2262_ = v_l_2265_;
goto _start;
}
else
{
lean_dec(v_l_2265_);
lean_dec(v_v_2264_);
lean_dec(v_k_2263_);
v_a_2262_ = v_r_2266_;
goto _start;
}
}
else
{
lean_dec(v_k_2260_);
lean_dec_ref(v_inst_2259_);
return v_best_2261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go(lean_object* v_00_u03b1_2273_, lean_object* v_00_u03b2_2274_, lean_object* v_inst_2275_, lean_object* v_k_2276_, lean_object* v_best_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2275_, v_k_2276_, v_best_2277_, v_a_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___redArg(lean_object* v_inst_2280_, lean_object* v_k_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = lean_box(0);
v___x_2284_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2280_, v_k_2281_, v___x_2283_, v_a_2282_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f(lean_object* v_00_u03b1_2285_, lean_object* v_00_u03b2_2286_, lean_object* v_inst_2287_, lean_object* v_k_2288_, lean_object* v_a_2289_){
_start:
{
lean_object* v___x_2290_; lean_object* v___x_2291_; 
v___x_2290_ = lean_box(0);
v___x_2291_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2287_, v_k_2288_, v___x_2290_, v_a_2289_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object* v_inst_2292_, lean_object* v_k_2293_, lean_object* v_best_2294_, lean_object* v_a_2295_){
_start:
{
if (lean_obj_tag(v_a_2295_) == 0)
{
lean_object* v_k_2296_; lean_object* v_v_2297_; lean_object* v_l_2298_; lean_object* v_r_2299_; lean_object* v___x_2300_; uint8_t v___x_2301_; 
v_k_2296_ = lean_ctor_get(v_a_2295_, 1);
lean_inc(v_k_2296_);
v_v_2297_ = lean_ctor_get(v_a_2295_, 2);
lean_inc(v_v_2297_);
v_l_2298_ = lean_ctor_get(v_a_2295_, 3);
lean_inc(v_l_2298_);
v_r_2299_ = lean_ctor_get(v_a_2295_, 4);
lean_inc(v_r_2299_);
lean_dec_ref(v_a_2295_);
lean_inc_ref(v_inst_2292_);
lean_inc(v_k_2296_);
lean_inc(v_k_2293_);
v___x_2300_ = lean_apply_2(v_inst_2292_, v_k_2293_, v_k_2296_);
v___x_2301_ = lean_unbox(v___x_2300_);
switch(v___x_2301_)
{
case 0:
{
lean_dec(v_r_2299_);
lean_dec(v_v_2297_);
lean_dec(v_k_2296_);
v_a_2295_ = v_l_2298_;
goto _start;
}
case 1:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
lean_dec(v_r_2299_);
lean_dec(v_l_2298_);
lean_dec(v_best_2294_);
lean_dec(v_k_2293_);
lean_dec_ref(v_inst_2292_);
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v_k_2296_);
lean_ctor_set(v___x_2303_, 1, v_v_2297_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
return v___x_2304_;
}
default: 
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec(v_l_2298_);
lean_dec(v_best_2294_);
v___x_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2305_, 0, v_k_2296_);
lean_ctor_set(v___x_2305_, 1, v_v_2297_);
v___x_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
v_best_2294_ = v___x_2306_;
v_a_2295_ = v_r_2299_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2293_);
lean_dec_ref(v_inst_2292_);
return v_best_2294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go(lean_object* v_00_u03b1_2308_, lean_object* v_00_u03b2_2309_, lean_object* v_inst_2310_, lean_object* v_k_2311_, lean_object* v_best_2312_, lean_object* v_a_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2310_, v_k_2311_, v_best_2312_, v_a_2313_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___redArg(lean_object* v_inst_2315_, lean_object* v_k_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_box(0);
v___x_2319_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2315_, v_k_2316_, v___x_2318_, v_a_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f(lean_object* v_00_u03b1_2320_, lean_object* v_00_u03b2_2321_, lean_object* v_inst_2322_, lean_object* v_k_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2325_ = lean_box(0);
v___x_2326_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2322_, v_k_2323_, v___x_2325_, v_a_2324_);
return v___x_2326_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object* v_inst_2327_, lean_object* v_k_2328_, lean_object* v_best_2329_, lean_object* v_a_2330_){
_start:
{
if (lean_obj_tag(v_a_2330_) == 0)
{
lean_object* v_k_2331_; lean_object* v_v_2332_; lean_object* v_l_2333_; lean_object* v_r_2334_; lean_object* v___x_2335_; uint8_t v___x_2336_; 
v_k_2331_ = lean_ctor_get(v_a_2330_, 1);
lean_inc(v_k_2331_);
v_v_2332_ = lean_ctor_get(v_a_2330_, 2);
lean_inc(v_v_2332_);
v_l_2333_ = lean_ctor_get(v_a_2330_, 3);
lean_inc(v_l_2333_);
v_r_2334_ = lean_ctor_get(v_a_2330_, 4);
lean_inc(v_r_2334_);
lean_dec_ref(v_a_2330_);
lean_inc_ref(v_inst_2327_);
lean_inc(v_k_2331_);
lean_inc(v_k_2328_);
v___x_2335_ = lean_apply_2(v_inst_2327_, v_k_2328_, v_k_2331_);
v___x_2336_ = lean_unbox(v___x_2335_);
if (v___x_2336_ == 2)
{
lean_object* v___x_2337_; lean_object* v___x_2338_; 
lean_dec(v_l_2333_);
lean_dec(v_best_2329_);
v___x_2337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2337_, 0, v_k_2331_);
lean_ctor_set(v___x_2337_, 1, v_v_2332_);
v___x_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2337_);
v_best_2329_ = v___x_2338_;
v_a_2330_ = v_r_2334_;
goto _start;
}
else
{
lean_dec(v_r_2334_);
lean_dec(v_v_2332_);
lean_dec(v_k_2331_);
v_a_2330_ = v_l_2333_;
goto _start;
}
}
else
{
lean_dec(v_k_2328_);
lean_dec_ref(v_inst_2327_);
return v_best_2329_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go(lean_object* v_00_u03b1_2341_, lean_object* v_00_u03b2_2342_, lean_object* v_inst_2343_, lean_object* v_k_2344_, lean_object* v_best_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2343_, v_k_2344_, v_best_2345_, v_a_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___redArg(lean_object* v_inst_2348_, lean_object* v_k_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = lean_box(0);
v___x_2352_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2348_, v_k_2349_, v___x_2351_, v_a_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f(lean_object* v_00_u03b1_2353_, lean_object* v_00_u03b2_2354_, lean_object* v_inst_2355_, lean_object* v_k_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = lean_box(0);
v___x_2359_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2355_, v_k_2356_, v___x_2358_, v_a_2357_);
return v___x_2359_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2363_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2));
v___x_2364_ = lean_unsigned_to_nat(14u);
v___x_2365_ = lean_unsigned_to_nat(22u);
v___x_2366_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1));
v___x_2367_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0));
v___x_2368_ = l_mkPanicMessageWithDecl(v___x_2367_, v___x_2366_, v___x_2365_, v___x_2364_, v___x_2363_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(lean_object* v_inst_2369_, lean_object* v_inst_2370_, lean_object* v_k_2371_, lean_object* v_t_2372_){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = lean_box(0);
v___x_2374_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2369_, v_k_2371_, v___x_2373_, v_t_2372_);
if (lean_obj_tag(v___x_2374_) == 0)
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2376_ = l_panic___redArg(v_inst_2370_, v___x_2375_);
return v___x_2376_;
}
else
{
lean_object* v_val_2377_; 
lean_dec_ref(v_inst_2370_);
v_val_2377_ = lean_ctor_get(v___x_2374_, 0);
lean_inc(v_val_2377_);
lean_dec_ref(v___x_2374_);
return v_val_2377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(lean_object* v_00_u03b1_2378_, lean_object* v_00_u03b2_2379_, lean_object* v_inst_2380_, lean_object* v_inst_2381_, lean_object* v_k_2382_, lean_object* v_t_2383_){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = lean_box(0);
v___x_2385_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2380_, v_k_2382_, v___x_2384_, v_t_2383_);
if (lean_obj_tag(v___x_2385_) == 0)
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2387_ = l_panic___redArg(v_inst_2381_, v___x_2386_);
return v___x_2387_;
}
else
{
lean_object* v_val_2388_; 
lean_dec_ref(v_inst_2381_);
v_val_2388_ = lean_ctor_get(v___x_2385_, 0);
lean_inc(v_val_2388_);
lean_dec_ref(v___x_2385_);
return v_val_2388_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(lean_object* v_inst_2389_, lean_object* v_inst_2390_, lean_object* v_k_2391_, lean_object* v_t_2392_){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = lean_box(0);
v___x_2394_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2389_, v_k_2391_, v___x_2393_, v_t_2392_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2396_ = l_panic___redArg(v_inst_2390_, v___x_2395_);
return v___x_2396_;
}
else
{
lean_object* v_val_2397_; 
lean_dec_ref(v_inst_2390_);
v_val_2397_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_val_2397_);
lean_dec_ref(v___x_2394_);
return v_val_2397_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(lean_object* v_00_u03b1_2398_, lean_object* v_00_u03b2_2399_, lean_object* v_inst_2400_, lean_object* v_inst_2401_, lean_object* v_k_2402_, lean_object* v_t_2403_){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2404_ = lean_box(0);
v___x_2405_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2400_, v_k_2402_, v___x_2404_, v_t_2403_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2406_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2407_ = l_panic___redArg(v_inst_2401_, v___x_2406_);
return v___x_2407_;
}
else
{
lean_object* v_val_2408_; 
lean_dec_ref(v_inst_2401_);
v_val_2408_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_val_2408_);
lean_dec_ref(v___x_2405_);
return v_val_2408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(lean_object* v_inst_2409_, lean_object* v_inst_2410_, lean_object* v_k_2411_, lean_object* v_t_2412_){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = lean_box(0);
v___x_2414_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2409_, v_k_2411_, v___x_2413_, v_t_2412_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2415_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2416_ = l_panic___redArg(v_inst_2410_, v___x_2415_);
return v___x_2416_;
}
else
{
lean_object* v_val_2417_; 
lean_dec_ref(v_inst_2410_);
v_val_2417_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_val_2417_);
lean_dec_ref(v___x_2414_);
return v_val_2417_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(lean_object* v_00_u03b1_2418_, lean_object* v_00_u03b2_2419_, lean_object* v_inst_2420_, lean_object* v_inst_2421_, lean_object* v_k_2422_, lean_object* v_t_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2424_ = lean_box(0);
v___x_2425_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2420_, v_k_2422_, v___x_2424_, v_t_2423_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2426_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2427_ = l_panic___redArg(v_inst_2421_, v___x_2426_);
return v___x_2427_;
}
else
{
lean_object* v_val_2428_; 
lean_dec_ref(v_inst_2421_);
v_val_2428_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_val_2428_);
lean_dec_ref(v___x_2425_);
return v_val_2428_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_k_2431_, lean_object* v_t_2432_){
_start:
{
lean_object* v___x_2433_; lean_object* v___x_2434_; 
v___x_2433_ = lean_box(0);
v___x_2434_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2429_, v_k_2431_, v___x_2433_, v_t_2432_);
if (lean_obj_tag(v___x_2434_) == 0)
{
lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2435_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2436_ = l_panic___redArg(v_inst_2430_, v___x_2435_);
return v___x_2436_;
}
else
{
lean_object* v_val_2437_; 
lean_dec_ref(v_inst_2430_);
v_val_2437_ = lean_ctor_get(v___x_2434_, 0);
lean_inc(v_val_2437_);
lean_dec_ref(v___x_2434_);
return v_val_2437_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(lean_object* v_00_u03b1_2438_, lean_object* v_00_u03b2_2439_, lean_object* v_inst_2440_, lean_object* v_inst_2441_, lean_object* v_k_2442_, lean_object* v_t_2443_){
_start:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2444_ = lean_box(0);
v___x_2445_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2440_, v_k_2442_, v___x_2444_, v_t_2443_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2447_ = l_panic___redArg(v_inst_2441_, v___x_2446_);
return v___x_2447_;
}
else
{
lean_object* v_val_2448_; 
lean_dec_ref(v_inst_2441_);
v_val_2448_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_val_2448_);
lean_dec_ref(v___x_2445_);
return v_val_2448_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(lean_object* v_inst_2449_, lean_object* v_k_2450_, lean_object* v_t_2451_, lean_object* v_fallback_2452_){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_box(0);
v___x_2454_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2449_, v_k_2450_, v___x_2453_, v_t_2451_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_inc_ref(v_fallback_2452_);
return v_fallback_2452_;
}
else
{
lean_object* v_val_2455_; 
v_val_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_val_2455_);
lean_dec_ref(v___x_2454_);
return v_val_2455_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg___boxed(lean_object* v_inst_2456_, lean_object* v_k_2457_, lean_object* v_t_2458_, lean_object* v_fallback_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(v_inst_2456_, v_k_2457_, v_t_2458_, v_fallback_2459_);
lean_dec_ref(v_fallback_2459_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED(lean_object* v_00_u03b1_2461_, lean_object* v_00_u03b2_2462_, lean_object* v_inst_2463_, lean_object* v_k_2464_, lean_object* v_t_2465_, lean_object* v_fallback_2466_){
_start:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
v___x_2467_ = lean_box(0);
v___x_2468_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2463_, v_k_2464_, v___x_2467_, v_t_2465_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_inc_ref(v_fallback_2466_);
return v_fallback_2466_;
}
else
{
lean_object* v_val_2469_; 
v_val_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_val_2469_);
lean_dec_ref(v___x_2468_);
return v_val_2469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___boxed(lean_object* v_00_u03b1_2470_, lean_object* v_00_u03b2_2471_, lean_object* v_inst_2472_, lean_object* v_k_2473_, lean_object* v_t_2474_, lean_object* v_fallback_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Std_DTreeMap_Internal_Impl_getEntryGED(v_00_u03b1_2470_, v_00_u03b2_2471_, v_inst_2472_, v_k_2473_, v_t_2474_, v_fallback_2475_);
lean_dec_ref(v_fallback_2475_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(lean_object* v_inst_2477_, lean_object* v_k_2478_, lean_object* v_t_2479_, lean_object* v_fallback_2480_){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2481_ = lean_box(0);
v___x_2482_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2477_, v_k_2478_, v___x_2481_, v_t_2479_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_inc_ref(v_fallback_2480_);
return v_fallback_2480_;
}
else
{
lean_object* v_val_2483_; 
v_val_2483_ = lean_ctor_get(v___x_2482_, 0);
lean_inc(v_val_2483_);
lean_dec_ref(v___x_2482_);
return v_val_2483_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg___boxed(lean_object* v_inst_2484_, lean_object* v_k_2485_, lean_object* v_t_2486_, lean_object* v_fallback_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(v_inst_2484_, v_k_2485_, v_t_2486_, v_fallback_2487_);
lean_dec_ref(v_fallback_2487_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD(lean_object* v_00_u03b1_2489_, lean_object* v_00_u03b2_2490_, lean_object* v_inst_2491_, lean_object* v_k_2492_, lean_object* v_t_2493_, lean_object* v_fallback_2494_){
_start:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2495_ = lean_box(0);
v___x_2496_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2491_, v_k_2492_, v___x_2495_, v_t_2493_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_inc_ref(v_fallback_2494_);
return v_fallback_2494_;
}
else
{
lean_object* v_val_2497_; 
v_val_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_val_2497_);
lean_dec_ref(v___x_2496_);
return v_val_2497_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___boxed(lean_object* v_00_u03b1_2498_, lean_object* v_00_u03b2_2499_, lean_object* v_inst_2500_, lean_object* v_k_2501_, lean_object* v_t_2502_, lean_object* v_fallback_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD(v_00_u03b1_2498_, v_00_u03b2_2499_, v_inst_2500_, v_k_2501_, v_t_2502_, v_fallback_2503_);
lean_dec_ref(v_fallback_2503_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(lean_object* v_inst_2505_, lean_object* v_k_2506_, lean_object* v_t_2507_, lean_object* v_fallback_2508_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; 
v___x_2509_ = lean_box(0);
v___x_2510_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2505_, v_k_2506_, v___x_2509_, v_t_2507_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_inc_ref(v_fallback_2508_);
return v_fallback_2508_;
}
else
{
lean_object* v_val_2511_; 
v_val_2511_ = lean_ctor_get(v___x_2510_, 0);
lean_inc(v_val_2511_);
lean_dec_ref(v___x_2510_);
return v_val_2511_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg___boxed(lean_object* v_inst_2512_, lean_object* v_k_2513_, lean_object* v_t_2514_, lean_object* v_fallback_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(v_inst_2512_, v_k_2513_, v_t_2514_, v_fallback_2515_);
lean_dec_ref(v_fallback_2515_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED(lean_object* v_00_u03b1_2517_, lean_object* v_00_u03b2_2518_, lean_object* v_inst_2519_, lean_object* v_k_2520_, lean_object* v_t_2521_, lean_object* v_fallback_2522_){
_start:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_box(0);
v___x_2524_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2519_, v_k_2520_, v___x_2523_, v_t_2521_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_inc_ref(v_fallback_2522_);
return v_fallback_2522_;
}
else
{
lean_object* v_val_2525_; 
v_val_2525_ = lean_ctor_get(v___x_2524_, 0);
lean_inc(v_val_2525_);
lean_dec_ref(v___x_2524_);
return v_val_2525_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___boxed(lean_object* v_00_u03b1_2526_, lean_object* v_00_u03b2_2527_, lean_object* v_inst_2528_, lean_object* v_k_2529_, lean_object* v_t_2530_, lean_object* v_fallback_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Std_DTreeMap_Internal_Impl_getEntryLED(v_00_u03b1_2526_, v_00_u03b2_2527_, v_inst_2528_, v_k_2529_, v_t_2530_, v_fallback_2531_);
lean_dec_ref(v_fallback_2531_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(lean_object* v_inst_2533_, lean_object* v_k_2534_, lean_object* v_t_2535_, lean_object* v_fallback_2536_){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_box(0);
v___x_2538_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2533_, v_k_2534_, v___x_2537_, v_t_2535_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_inc_ref(v_fallback_2536_);
return v_fallback_2536_;
}
else
{
lean_object* v_val_2539_; 
v_val_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_val_2539_);
lean_dec_ref(v___x_2538_);
return v_val_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg___boxed(lean_object* v_inst_2540_, lean_object* v_k_2541_, lean_object* v_t_2542_, lean_object* v_fallback_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(v_inst_2540_, v_k_2541_, v_t_2542_, v_fallback_2543_);
lean_dec_ref(v_fallback_2543_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD(lean_object* v_00_u03b1_2545_, lean_object* v_00_u03b2_2546_, lean_object* v_inst_2547_, lean_object* v_k_2548_, lean_object* v_t_2549_, lean_object* v_fallback_2550_){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_box(0);
v___x_2552_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2547_, v_k_2548_, v___x_2551_, v_t_2549_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_inc_ref(v_fallback_2550_);
return v_fallback_2550_;
}
else
{
lean_object* v_val_2553_; 
v_val_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_val_2553_);
lean_dec_ref(v___x_2552_);
return v_val_2553_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___boxed(lean_object* v_00_u03b1_2554_, lean_object* v_00_u03b2_2555_, lean_object* v_inst_2556_, lean_object* v_k_2557_, lean_object* v_t_2558_, lean_object* v_fallback_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD(v_00_u03b1_2554_, v_00_u03b2_2555_, v_inst_2556_, v_k_2557_, v_t_2558_, v_fallback_2559_);
lean_dec_ref(v_fallback_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(lean_object* v_inst_2561_, lean_object* v_k_2562_, lean_object* v_x_2563_){
_start:
{
lean_object* v_k_2564_; lean_object* v_v_2565_; lean_object* v_l_2566_; lean_object* v_r_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; 
v_k_2564_ = lean_ctor_get(v_x_2563_, 1);
lean_inc(v_k_2564_);
v_v_2565_ = lean_ctor_get(v_x_2563_, 2);
lean_inc(v_v_2565_);
v_l_2566_ = lean_ctor_get(v_x_2563_, 3);
lean_inc(v_l_2566_);
v_r_2567_ = lean_ctor_get(v_x_2563_, 4);
lean_inc(v_r_2567_);
lean_dec(v_x_2563_);
lean_inc_ref(v_inst_2561_);
lean_inc(v_k_2564_);
lean_inc(v_k_2562_);
v___x_2568_ = lean_apply_2(v_inst_2561_, v_k_2562_, v_k_2564_);
v___x_2569_ = lean_unbox(v___x_2568_);
switch(v___x_2569_)
{
case 0:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; 
lean_dec(v_r_2567_);
v___x_2570_ = lean_box(0);
v___x_2571_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2561_, v_k_2562_, v___x_2570_, v_l_2566_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v___x_2572_; 
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v_k_2564_);
lean_ctor_set(v___x_2572_, 1, v_v_2565_);
return v___x_2572_;
}
else
{
lean_object* v_val_2573_; 
lean_dec(v_v_2565_);
lean_dec(v_k_2564_);
v_val_2573_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_val_2573_);
lean_dec_ref(v___x_2571_);
return v_val_2573_;
}
}
case 1:
{
lean_object* v___x_2574_; 
lean_dec(v_r_2567_);
lean_dec(v_l_2566_);
lean_dec(v_k_2562_);
lean_dec_ref(v_inst_2561_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v_k_2564_);
lean_ctor_set(v___x_2574_, 1, v_v_2565_);
return v___x_2574_;
}
default: 
{
lean_dec(v_l_2566_);
lean_dec(v_v_2565_);
lean_dec(v_k_2564_);
v_x_2563_ = v_r_2567_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE(lean_object* v_00_u03b1_2576_, lean_object* v_00_u03b2_2577_, lean_object* v_inst_2578_, lean_object* v_inst_2579_, lean_object* v_k_2580_, lean_object* v_x_2581_, lean_object* v_x_2582_, lean_object* v_x_2583_){
_start:
{
lean_object* v___x_2584_; 
v___x_2584_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_inst_2578_, v_k_2580_, v_x_2581_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object* v_inst_2585_, lean_object* v_k_2586_, lean_object* v_x_2587_){
_start:
{
lean_object* v_k_2588_; lean_object* v_v_2589_; lean_object* v_l_2590_; lean_object* v_r_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; uint8_t v___x_2594_; uint8_t v___x_2595_; 
v_k_2588_ = lean_ctor_get(v_x_2587_, 1);
lean_inc(v_k_2588_);
v_v_2589_ = lean_ctor_get(v_x_2587_, 2);
lean_inc(v_v_2589_);
v_l_2590_ = lean_ctor_get(v_x_2587_, 3);
lean_inc(v_l_2590_);
v_r_2591_ = lean_ctor_get(v_x_2587_, 4);
lean_inc(v_r_2591_);
lean_dec(v_x_2587_);
lean_inc_ref(v_inst_2585_);
lean_inc(v_k_2588_);
lean_inc(v_k_2586_);
v___x_2592_ = lean_apply_2(v_inst_2585_, v_k_2586_, v_k_2588_);
v___x_2593_ = 0;
v___x_2594_ = lean_unbox(v___x_2592_);
v___x_2595_ = l_instDecidableEqOrdering(v___x_2594_, v___x_2593_);
if (v___x_2595_ == 0)
{
lean_dec(v_l_2590_);
lean_dec(v_v_2589_);
lean_dec(v_k_2588_);
v_x_2587_ = v_r_2591_;
goto _start;
}
else
{
lean_object* v___x_2597_; lean_object* v___x_2598_; 
lean_dec(v_r_2591_);
v___x_2597_ = lean_box(0);
v___x_2598_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2585_, v_k_2586_, v___x_2597_, v_l_2590_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2599_, 0, v_k_2588_);
lean_ctor_set(v___x_2599_, 1, v_v_2589_);
return v___x_2599_;
}
else
{
lean_object* v_val_2600_; 
lean_dec(v_v_2589_);
lean_dec(v_k_2588_);
v_val_2600_ = lean_ctor_get(v___x_2598_, 0);
lean_inc(v_val_2600_);
lean_dec_ref(v___x_2598_);
return v_val_2600_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object* v_00_u03b1_2601_, lean_object* v_00_u03b2_2602_, lean_object* v_inst_2603_, lean_object* v_inst_2604_, lean_object* v_k_2605_, lean_object* v_x_2606_, lean_object* v_x_2607_, lean_object* v_x_2608_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_inst_2603_, v_k_2605_, v_x_2606_);
return v___x_2609_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object* v_inst_2610_, lean_object* v_k_2611_, lean_object* v_x_2612_){
_start:
{
lean_object* v_k_2613_; lean_object* v_v_2614_; lean_object* v_l_2615_; lean_object* v_r_2616_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v_k_2613_ = lean_ctor_get(v_x_2612_, 1);
lean_inc(v_k_2613_);
v_v_2614_ = lean_ctor_get(v_x_2612_, 2);
lean_inc(v_v_2614_);
v_l_2615_ = lean_ctor_get(v_x_2612_, 3);
lean_inc(v_l_2615_);
v_r_2616_ = lean_ctor_get(v_x_2612_, 4);
lean_inc(v_r_2616_);
lean_dec(v_x_2612_);
lean_inc_ref(v_inst_2610_);
lean_inc(v_k_2613_);
lean_inc(v_k_2611_);
v___x_2617_ = lean_apply_2(v_inst_2610_, v_k_2611_, v_k_2613_);
v___x_2618_ = lean_unbox(v___x_2617_);
switch(v___x_2618_)
{
case 0:
{
lean_dec(v_r_2616_);
lean_dec(v_v_2614_);
lean_dec(v_k_2613_);
v_x_2612_ = v_l_2615_;
goto _start;
}
case 1:
{
lean_object* v___x_2620_; 
lean_dec(v_r_2616_);
lean_dec(v_l_2615_);
lean_dec(v_k_2611_);
lean_dec_ref(v_inst_2610_);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v_k_2613_);
lean_ctor_set(v___x_2620_, 1, v_v_2614_);
return v___x_2620_;
}
default: 
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
lean_dec(v_l_2615_);
v___x_2621_ = lean_box(0);
v___x_2622_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2610_, v_k_2611_, v___x_2621_, v_r_2616_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v___x_2623_; 
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v_k_2613_);
lean_ctor_set(v___x_2623_, 1, v_v_2614_);
return v___x_2623_;
}
else
{
lean_object* v_val_2624_; 
lean_dec(v_v_2614_);
lean_dec(v_k_2613_);
v_val_2624_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_val_2624_);
lean_dec_ref(v___x_2622_);
return v_val_2624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object* v_00_u03b1_2625_, lean_object* v_00_u03b2_2626_, lean_object* v_inst_2627_, lean_object* v_inst_2628_, lean_object* v_k_2629_, lean_object* v_x_2630_, lean_object* v_x_2631_, lean_object* v_x_2632_){
_start:
{
lean_object* v___x_2633_; 
v___x_2633_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_inst_2627_, v_k_2629_, v_x_2630_);
return v___x_2633_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object* v_inst_2634_, lean_object* v_k_2635_, lean_object* v_x_2636_){
_start:
{
lean_object* v_k_2637_; lean_object* v_v_2638_; lean_object* v_l_2639_; lean_object* v_r_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; uint8_t v___x_2643_; uint8_t v___x_2644_; 
v_k_2637_ = lean_ctor_get(v_x_2636_, 1);
lean_inc(v_k_2637_);
v_v_2638_ = lean_ctor_get(v_x_2636_, 2);
lean_inc(v_v_2638_);
v_l_2639_ = lean_ctor_get(v_x_2636_, 3);
lean_inc(v_l_2639_);
v_r_2640_ = lean_ctor_get(v_x_2636_, 4);
lean_inc(v_r_2640_);
lean_dec(v_x_2636_);
lean_inc_ref(v_inst_2634_);
lean_inc(v_k_2637_);
lean_inc(v_k_2635_);
v___x_2641_ = lean_apply_2(v_inst_2634_, v_k_2635_, v_k_2637_);
v___x_2642_ = 2;
v___x_2643_ = lean_unbox(v___x_2641_);
v___x_2644_ = l_instDecidableEqOrdering(v___x_2643_, v___x_2642_);
if (v___x_2644_ == 0)
{
lean_dec(v_r_2640_);
lean_dec(v_v_2638_);
lean_dec(v_k_2637_);
v_x_2636_ = v_l_2639_;
goto _start;
}
else
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
lean_dec(v_l_2639_);
v___x_2646_ = lean_box(0);
v___x_2647_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2634_, v_k_2635_, v___x_2646_, v_r_2640_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2648_, 0, v_k_2637_);
lean_ctor_set(v___x_2648_, 1, v_v_2638_);
return v___x_2648_;
}
else
{
lean_object* v_val_2649_; 
lean_dec(v_v_2638_);
lean_dec(v_k_2637_);
v_val_2649_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_val_2649_);
lean_dec_ref(v___x_2647_);
return v_val_2649_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT(lean_object* v_00_u03b1_2650_, lean_object* v_00_u03b2_2651_, lean_object* v_inst_2652_, lean_object* v_inst_2653_, lean_object* v_k_2654_, lean_object* v_x_2655_, lean_object* v_x_2656_, lean_object* v_x_2657_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_inst_2652_, v_k_2654_, v_x_2655_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object* v_inst_2659_, lean_object* v_k_2660_, lean_object* v_best_2661_, lean_object* v_a_2662_){
_start:
{
if (lean_obj_tag(v_a_2662_) == 0)
{
lean_object* v_k_2663_; lean_object* v_l_2664_; lean_object* v_r_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v_k_2663_ = lean_ctor_get(v_a_2662_, 1);
lean_inc(v_k_2663_);
v_l_2664_ = lean_ctor_get(v_a_2662_, 3);
lean_inc(v_l_2664_);
v_r_2665_ = lean_ctor_get(v_a_2662_, 4);
lean_inc(v_r_2665_);
lean_dec_ref(v_a_2662_);
lean_inc_ref(v_inst_2659_);
lean_inc(v_k_2663_);
lean_inc(v_k_2660_);
v___x_2666_ = lean_apply_2(v_inst_2659_, v_k_2660_, v_k_2663_);
v___x_2667_ = lean_unbox(v___x_2666_);
switch(v___x_2667_)
{
case 0:
{
lean_object* v___x_2668_; 
lean_dec(v_r_2665_);
lean_dec(v_best_2661_);
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_k_2663_);
v_best_2661_ = v___x_2668_;
v_a_2662_ = v_l_2664_;
goto _start;
}
case 1:
{
lean_object* v___x_2670_; 
lean_dec(v_r_2665_);
lean_dec(v_l_2664_);
lean_dec(v_best_2661_);
lean_dec(v_k_2660_);
lean_dec_ref(v_inst_2659_);
v___x_2670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2670_, 0, v_k_2663_);
return v___x_2670_;
}
default: 
{
lean_dec(v_l_2664_);
lean_dec(v_k_2663_);
v_a_2662_ = v_r_2665_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2660_);
lean_dec_ref(v_inst_2659_);
return v_best_2661_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(lean_object* v_00_u03b1_2672_, lean_object* v_00_u03b2_2673_, lean_object* v_inst_2674_, lean_object* v_k_2675_, lean_object* v_best_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v___x_2678_; 
v___x_2678_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2674_, v_k_2675_, v_best_2676_, v_a_2677_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___redArg(lean_object* v_inst_2679_, lean_object* v_k_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2682_ = lean_box(0);
v___x_2683_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2679_, v_k_2680_, v___x_2682_, v_a_2681_);
return v___x_2683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(lean_object* v_00_u03b1_2684_, lean_object* v_00_u03b2_2685_, lean_object* v_inst_2686_, lean_object* v_k_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2689_ = lean_box(0);
v___x_2690_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2686_, v_k_2687_, v___x_2689_, v_a_2688_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object* v_inst_2691_, lean_object* v_k_2692_, lean_object* v_best_2693_, lean_object* v_a_2694_){
_start:
{
if (lean_obj_tag(v_a_2694_) == 0)
{
lean_object* v_k_2695_; lean_object* v_l_2696_; lean_object* v_r_2697_; lean_object* v___x_2698_; uint8_t v___x_2699_; 
v_k_2695_ = lean_ctor_get(v_a_2694_, 1);
lean_inc(v_k_2695_);
v_l_2696_ = lean_ctor_get(v_a_2694_, 3);
lean_inc(v_l_2696_);
v_r_2697_ = lean_ctor_get(v_a_2694_, 4);
lean_inc(v_r_2697_);
lean_dec_ref(v_a_2694_);
lean_inc_ref(v_inst_2691_);
lean_inc(v_k_2695_);
lean_inc(v_k_2692_);
v___x_2698_ = lean_apply_2(v_inst_2691_, v_k_2692_, v_k_2695_);
v___x_2699_ = lean_unbox(v___x_2698_);
if (v___x_2699_ == 0)
{
lean_object* v___x_2700_; 
lean_dec(v_r_2697_);
lean_dec(v_best_2693_);
v___x_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2700_, 0, v_k_2695_);
v_best_2693_ = v___x_2700_;
v_a_2694_ = v_l_2696_;
goto _start;
}
else
{
lean_dec(v_l_2696_);
lean_dec(v_k_2695_);
v_a_2694_ = v_r_2697_;
goto _start;
}
}
else
{
lean_dec(v_k_2692_);
lean_dec_ref(v_inst_2691_);
return v_best_2693_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(lean_object* v_00_u03b1_2703_, lean_object* v_00_u03b2_2704_, lean_object* v_inst_2705_, lean_object* v_k_2706_, lean_object* v_best_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v___x_2709_; 
v___x_2709_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2705_, v_k_2706_, v_best_2707_, v_a_2708_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___redArg(lean_object* v_inst_2710_, lean_object* v_k_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = lean_box(0);
v___x_2714_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2710_, v_k_2711_, v___x_2713_, v_a_2712_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(lean_object* v_00_u03b1_2715_, lean_object* v_00_u03b2_2716_, lean_object* v_inst_2717_, lean_object* v_k_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2720_ = lean_box(0);
v___x_2721_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2717_, v_k_2718_, v___x_2720_, v_a_2719_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object* v_inst_2722_, lean_object* v_k_2723_, lean_object* v_best_2724_, lean_object* v_a_2725_){
_start:
{
if (lean_obj_tag(v_a_2725_) == 0)
{
lean_object* v_k_2726_; lean_object* v_l_2727_; lean_object* v_r_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_k_2726_ = lean_ctor_get(v_a_2725_, 1);
lean_inc(v_k_2726_);
v_l_2727_ = lean_ctor_get(v_a_2725_, 3);
lean_inc(v_l_2727_);
v_r_2728_ = lean_ctor_get(v_a_2725_, 4);
lean_inc(v_r_2728_);
lean_dec_ref(v_a_2725_);
lean_inc_ref(v_inst_2722_);
lean_inc(v_k_2726_);
lean_inc(v_k_2723_);
v___x_2729_ = lean_apply_2(v_inst_2722_, v_k_2723_, v_k_2726_);
v___x_2730_ = lean_unbox(v___x_2729_);
switch(v___x_2730_)
{
case 0:
{
lean_dec(v_r_2728_);
lean_dec(v_k_2726_);
v_a_2725_ = v_l_2727_;
goto _start;
}
case 1:
{
lean_object* v___x_2732_; 
lean_dec(v_r_2728_);
lean_dec(v_l_2727_);
lean_dec(v_best_2724_);
lean_dec(v_k_2723_);
lean_dec_ref(v_inst_2722_);
v___x_2732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2732_, 0, v_k_2726_);
return v___x_2732_;
}
default: 
{
lean_object* v___x_2733_; 
lean_dec(v_l_2727_);
lean_dec(v_best_2724_);
v___x_2733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2733_, 0, v_k_2726_);
v_best_2724_ = v___x_2733_;
v_a_2725_ = v_r_2728_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2723_);
lean_dec_ref(v_inst_2722_);
return v_best_2724_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(lean_object* v_00_u03b1_2735_, lean_object* v_00_u03b2_2736_, lean_object* v_inst_2737_, lean_object* v_k_2738_, lean_object* v_best_2739_, lean_object* v_a_2740_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2737_, v_k_2738_, v_best_2739_, v_a_2740_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___redArg(lean_object* v_inst_2742_, lean_object* v_k_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = lean_box(0);
v___x_2746_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2742_, v_k_2743_, v___x_2745_, v_a_2744_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(lean_object* v_00_u03b1_2747_, lean_object* v_00_u03b2_2748_, lean_object* v_inst_2749_, lean_object* v_k_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = lean_box(0);
v___x_2753_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2749_, v_k_2750_, v___x_2752_, v_a_2751_);
return v___x_2753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object* v_inst_2754_, lean_object* v_k_2755_, lean_object* v_best_2756_, lean_object* v_a_2757_){
_start:
{
if (lean_obj_tag(v_a_2757_) == 0)
{
lean_object* v_k_2758_; lean_object* v_l_2759_; lean_object* v_r_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v_k_2758_ = lean_ctor_get(v_a_2757_, 1);
lean_inc(v_k_2758_);
v_l_2759_ = lean_ctor_get(v_a_2757_, 3);
lean_inc(v_l_2759_);
v_r_2760_ = lean_ctor_get(v_a_2757_, 4);
lean_inc(v_r_2760_);
lean_dec_ref(v_a_2757_);
lean_inc_ref(v_inst_2754_);
lean_inc(v_k_2758_);
lean_inc(v_k_2755_);
v___x_2761_ = lean_apply_2(v_inst_2754_, v_k_2755_, v_k_2758_);
v___x_2762_ = lean_unbox(v___x_2761_);
if (v___x_2762_ == 2)
{
lean_object* v___x_2763_; 
lean_dec(v_l_2759_);
lean_dec(v_best_2756_);
v___x_2763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2763_, 0, v_k_2758_);
v_best_2756_ = v___x_2763_;
v_a_2757_ = v_r_2760_;
goto _start;
}
else
{
lean_dec(v_r_2760_);
lean_dec(v_k_2758_);
v_a_2757_ = v_l_2759_;
goto _start;
}
}
else
{
lean_dec(v_k_2755_);
lean_dec_ref(v_inst_2754_);
return v_best_2756_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(lean_object* v_00_u03b1_2766_, lean_object* v_00_u03b2_2767_, lean_object* v_inst_2768_, lean_object* v_k_2769_, lean_object* v_best_2770_, lean_object* v_a_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2768_, v_k_2769_, v_best_2770_, v_a_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___redArg(lean_object* v_inst_2773_, lean_object* v_k_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_box(0);
v___x_2777_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2773_, v_k_2774_, v___x_2776_, v_a_2775_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(lean_object* v_00_u03b1_2778_, lean_object* v_00_u03b2_2779_, lean_object* v_inst_2780_, lean_object* v_k_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_box(0);
v___x_2784_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2780_, v_k_2781_, v___x_2783_, v_a_2782_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(lean_object* v_inst_2785_, lean_object* v_inst_2786_, lean_object* v_k_2787_, lean_object* v_t_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_box(0);
v___x_2790_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2785_, v_k_2787_, v___x_2789_, v_t_2788_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2792_ = l_panic___redArg(v_inst_2786_, v___x_2791_);
return v___x_2792_;
}
else
{
lean_object* v_val_2793_; 
lean_dec(v_inst_2786_);
v_val_2793_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_val_2793_);
lean_dec_ref(v___x_2790_);
return v_val_2793_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object* v_00_u03b1_2794_, lean_object* v_00_u03b2_2795_, lean_object* v_inst_2796_, lean_object* v_inst_2797_, lean_object* v_k_2798_, lean_object* v_t_2799_){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = lean_box(0);
v___x_2801_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2796_, v_k_2798_, v___x_2800_, v_t_2799_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2803_ = l_panic___redArg(v_inst_2797_, v___x_2802_);
return v___x_2803_;
}
else
{
lean_object* v_val_2804_; 
lean_dec(v_inst_2797_);
v_val_2804_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_val_2804_);
lean_dec_ref(v___x_2801_);
return v_val_2804_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(lean_object* v_inst_2805_, lean_object* v_inst_2806_, lean_object* v_k_2807_, lean_object* v_t_2808_){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = lean_box(0);
v___x_2810_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2805_, v_k_2807_, v___x_2809_, v_t_2808_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2812_ = l_panic___redArg(v_inst_2806_, v___x_2811_);
return v___x_2812_;
}
else
{
lean_object* v_val_2813_; 
lean_dec(v_inst_2806_);
v_val_2813_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_val_2813_);
lean_dec_ref(v___x_2810_);
return v_val_2813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object* v_00_u03b1_2814_, lean_object* v_00_u03b2_2815_, lean_object* v_inst_2816_, lean_object* v_inst_2817_, lean_object* v_k_2818_, lean_object* v_t_2819_){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_box(0);
v___x_2821_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2816_, v_k_2818_, v___x_2820_, v_t_2819_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2823_ = l_panic___redArg(v_inst_2817_, v___x_2822_);
return v___x_2823_;
}
else
{
lean_object* v_val_2824_; 
lean_dec(v_inst_2817_);
v_val_2824_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_val_2824_);
lean_dec_ref(v___x_2821_);
return v_val_2824_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(lean_object* v_inst_2825_, lean_object* v_inst_2826_, lean_object* v_k_2827_, lean_object* v_t_2828_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_box(0);
v___x_2830_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2825_, v_k_2827_, v___x_2829_, v_t_2828_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2832_ = l_panic___redArg(v_inst_2826_, v___x_2831_);
return v___x_2832_;
}
else
{
lean_object* v_val_2833_; 
lean_dec(v_inst_2826_);
v_val_2833_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_val_2833_);
lean_dec_ref(v___x_2830_);
return v_val_2833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object* v_00_u03b1_2834_, lean_object* v_00_u03b2_2835_, lean_object* v_inst_2836_, lean_object* v_inst_2837_, lean_object* v_k_2838_, lean_object* v_t_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_box(0);
v___x_2841_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2836_, v_k_2838_, v___x_2840_, v_t_2839_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v___x_2842_; lean_object* v___x_2843_; 
v___x_2842_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2843_ = l_panic___redArg(v_inst_2837_, v___x_2842_);
return v___x_2843_;
}
else
{
lean_object* v_val_2844_; 
lean_dec(v_inst_2837_);
v_val_2844_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_val_2844_);
lean_dec_ref(v___x_2841_);
return v_val_2844_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(lean_object* v_inst_2845_, lean_object* v_inst_2846_, lean_object* v_k_2847_, lean_object* v_t_2848_){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; 
v___x_2849_ = lean_box(0);
v___x_2850_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2845_, v_k_2847_, v___x_2849_, v_t_2848_);
if (lean_obj_tag(v___x_2850_) == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; 
v___x_2851_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2852_ = l_panic___redArg(v_inst_2846_, v___x_2851_);
return v___x_2852_;
}
else
{
lean_object* v_val_2853_; 
lean_dec(v_inst_2846_);
v_val_2853_ = lean_ctor_get(v___x_2850_, 0);
lean_inc(v_val_2853_);
lean_dec_ref(v___x_2850_);
return v_val_2853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object* v_00_u03b1_2854_, lean_object* v_00_u03b2_2855_, lean_object* v_inst_2856_, lean_object* v_inst_2857_, lean_object* v_k_2858_, lean_object* v_t_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_box(0);
v___x_2861_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2856_, v_k_2858_, v___x_2860_, v_t_2859_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2863_ = l_panic___redArg(v_inst_2857_, v___x_2862_);
return v___x_2863_;
}
else
{
lean_object* v_val_2864_; 
lean_dec(v_inst_2857_);
v_val_2864_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_val_2864_);
lean_dec_ref(v___x_2861_);
return v_val_2864_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(lean_object* v_inst_2865_, lean_object* v_k_2866_, lean_object* v_t_2867_, lean_object* v_fallback_2868_){
_start:
{
lean_object* v___x_2869_; lean_object* v___x_2870_; 
v___x_2869_ = lean_box(0);
v___x_2870_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2865_, v_k_2866_, v___x_2869_, v_t_2867_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_inc(v_fallback_2868_);
return v_fallback_2868_;
}
else
{
lean_object* v_val_2871_; 
v_val_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_val_2871_);
lean_dec_ref(v___x_2870_);
return v_val_2871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg___boxed(lean_object* v_inst_2872_, lean_object* v_k_2873_, lean_object* v_t_2874_, lean_object* v_fallback_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(v_inst_2872_, v_k_2873_, v_t_2874_, v_fallback_2875_);
lean_dec(v_fallback_2875_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED(lean_object* v_00_u03b1_2877_, lean_object* v_00_u03b2_2878_, lean_object* v_inst_2879_, lean_object* v_k_2880_, lean_object* v_t_2881_, lean_object* v_fallback_2882_){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_box(0);
v___x_2884_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2879_, v_k_2880_, v___x_2883_, v_t_2881_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_inc(v_fallback_2882_);
return v_fallback_2882_;
}
else
{
lean_object* v_val_2885_; 
v_val_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_val_2885_);
lean_dec_ref(v___x_2884_);
return v_val_2885_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___boxed(lean_object* v_00_u03b1_2886_, lean_object* v_00_u03b2_2887_, lean_object* v_inst_2888_, lean_object* v_k_2889_, lean_object* v_t_2890_, lean_object* v_fallback_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Std_DTreeMap_Internal_Impl_getKeyGED(v_00_u03b1_2886_, v_00_u03b2_2887_, v_inst_2888_, v_k_2889_, v_t_2890_, v_fallback_2891_);
lean_dec(v_fallback_2891_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(lean_object* v_inst_2893_, lean_object* v_k_2894_, lean_object* v_t_2895_, lean_object* v_fallback_2896_){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = lean_box(0);
v___x_2898_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2893_, v_k_2894_, v___x_2897_, v_t_2895_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_inc(v_fallback_2896_);
return v_fallback_2896_;
}
else
{
lean_object* v_val_2899_; 
v_val_2899_ = lean_ctor_get(v___x_2898_, 0);
lean_inc(v_val_2899_);
lean_dec_ref(v___x_2898_);
return v_val_2899_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg___boxed(lean_object* v_inst_2900_, lean_object* v_k_2901_, lean_object* v_t_2902_, lean_object* v_fallback_2903_){
_start:
{
lean_object* v_res_2904_; 
v_res_2904_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(v_inst_2900_, v_k_2901_, v_t_2902_, v_fallback_2903_);
lean_dec(v_fallback_2903_);
return v_res_2904_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD(lean_object* v_00_u03b1_2905_, lean_object* v_00_u03b2_2906_, lean_object* v_inst_2907_, lean_object* v_k_2908_, lean_object* v_t_2909_, lean_object* v_fallback_2910_){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_box(0);
v___x_2912_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2907_, v_k_2908_, v___x_2911_, v_t_2909_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_inc(v_fallback_2910_);
return v_fallback_2910_;
}
else
{
lean_object* v_val_2913_; 
v_val_2913_ = lean_ctor_get(v___x_2912_, 0);
lean_inc(v_val_2913_);
lean_dec_ref(v___x_2912_);
return v_val_2913_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___boxed(lean_object* v_00_u03b1_2914_, lean_object* v_00_u03b2_2915_, lean_object* v_inst_2916_, lean_object* v_k_2917_, lean_object* v_t_2918_, lean_object* v_fallback_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD(v_00_u03b1_2914_, v_00_u03b2_2915_, v_inst_2916_, v_k_2917_, v_t_2918_, v_fallback_2919_);
lean_dec(v_fallback_2919_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(lean_object* v_inst_2921_, lean_object* v_k_2922_, lean_object* v_t_2923_, lean_object* v_fallback_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = lean_box(0);
v___x_2926_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2921_, v_k_2922_, v___x_2925_, v_t_2923_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_inc(v_fallback_2924_);
return v_fallback_2924_;
}
else
{
lean_object* v_val_2927_; 
v_val_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_val_2927_);
lean_dec_ref(v___x_2926_);
return v_val_2927_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg___boxed(lean_object* v_inst_2928_, lean_object* v_k_2929_, lean_object* v_t_2930_, lean_object* v_fallback_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(v_inst_2928_, v_k_2929_, v_t_2930_, v_fallback_2931_);
lean_dec(v_fallback_2931_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED(lean_object* v_00_u03b1_2933_, lean_object* v_00_u03b2_2934_, lean_object* v_inst_2935_, lean_object* v_k_2936_, lean_object* v_t_2937_, lean_object* v_fallback_2938_){
_start:
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_box(0);
v___x_2940_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2935_, v_k_2936_, v___x_2939_, v_t_2937_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_inc(v_fallback_2938_);
return v_fallback_2938_;
}
else
{
lean_object* v_val_2941_; 
v_val_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_val_2941_);
lean_dec_ref(v___x_2940_);
return v_val_2941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___boxed(lean_object* v_00_u03b1_2942_, lean_object* v_00_u03b2_2943_, lean_object* v_inst_2944_, lean_object* v_k_2945_, lean_object* v_t_2946_, lean_object* v_fallback_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Std_DTreeMap_Internal_Impl_getKeyLED(v_00_u03b1_2942_, v_00_u03b2_2943_, v_inst_2944_, v_k_2945_, v_t_2946_, v_fallback_2947_);
lean_dec(v_fallback_2947_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(lean_object* v_inst_2949_, lean_object* v_k_2950_, lean_object* v_t_2951_, lean_object* v_fallback_2952_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_box(0);
v___x_2954_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2949_, v_k_2950_, v___x_2953_, v_t_2951_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_inc(v_fallback_2952_);
return v_fallback_2952_;
}
else
{
lean_object* v_val_2955_; 
v_val_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_val_2955_);
lean_dec_ref(v___x_2954_);
return v_val_2955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg___boxed(lean_object* v_inst_2956_, lean_object* v_k_2957_, lean_object* v_t_2958_, lean_object* v_fallback_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(v_inst_2956_, v_k_2957_, v_t_2958_, v_fallback_2959_);
lean_dec(v_fallback_2959_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD(lean_object* v_00_u03b1_2961_, lean_object* v_00_u03b2_2962_, lean_object* v_inst_2963_, lean_object* v_k_2964_, lean_object* v_t_2965_, lean_object* v_fallback_2966_){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = lean_box(0);
v___x_2968_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2963_, v_k_2964_, v___x_2967_, v_t_2965_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_inc(v_fallback_2966_);
return v_fallback_2966_;
}
else
{
lean_object* v_val_2969_; 
v_val_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_val_2969_);
lean_dec_ref(v___x_2968_);
return v_val_2969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___boxed(lean_object* v_00_u03b1_2970_, lean_object* v_00_u03b2_2971_, lean_object* v_inst_2972_, lean_object* v_k_2973_, lean_object* v_t_2974_, lean_object* v_fallback_2975_){
_start:
{
lean_object* v_res_2976_; 
v_res_2976_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD(v_00_u03b1_2970_, v_00_u03b2_2971_, v_inst_2972_, v_k_2973_, v_t_2974_, v_fallback_2975_);
lean_dec(v_fallback_2975_);
return v_res_2976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object* v_inst_2977_, lean_object* v_k_2978_, lean_object* v_x_2979_){
_start:
{
lean_object* v_k_2980_; lean_object* v_l_2981_; lean_object* v_r_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v_k_2980_ = lean_ctor_get(v_x_2979_, 1);
lean_inc(v_k_2980_);
v_l_2981_ = lean_ctor_get(v_x_2979_, 3);
lean_inc(v_l_2981_);
v_r_2982_ = lean_ctor_get(v_x_2979_, 4);
lean_inc(v_r_2982_);
lean_dec(v_x_2979_);
lean_inc_ref(v_inst_2977_);
lean_inc(v_k_2980_);
lean_inc(v_k_2978_);
v___x_2983_ = lean_apply_2(v_inst_2977_, v_k_2978_, v_k_2980_);
v___x_2984_ = lean_unbox(v___x_2983_);
switch(v___x_2984_)
{
case 0:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
lean_dec(v_r_2982_);
v___x_2985_ = lean_box(0);
v___x_2986_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2977_, v_k_2978_, v___x_2985_, v_l_2981_);
if (lean_obj_tag(v___x_2986_) == 0)
{
return v_k_2980_;
}
else
{
lean_object* v_val_2987_; 
lean_dec(v_k_2980_);
v_val_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_val_2987_);
lean_dec_ref(v___x_2986_);
return v_val_2987_;
}
}
case 1:
{
lean_dec(v_r_2982_);
lean_dec(v_l_2981_);
lean_dec(v_k_2978_);
lean_dec_ref(v_inst_2977_);
return v_k_2980_;
}
default: 
{
lean_dec(v_l_2981_);
lean_dec(v_k_2980_);
v_x_2979_ = v_r_2982_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE(lean_object* v_00_u03b1_2989_, lean_object* v_00_u03b2_2990_, lean_object* v_inst_2991_, lean_object* v_inst_2992_, lean_object* v_k_2993_, lean_object* v_x_2994_, lean_object* v_x_2995_, lean_object* v_x_2996_){
_start:
{
lean_object* v___x_2997_; 
v___x_2997_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_inst_2991_, v_k_2993_, v_x_2994_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object* v_inst_2998_, lean_object* v_k_2999_, lean_object* v_x_3000_){
_start:
{
lean_object* v_k_3001_; lean_object* v_l_3002_; lean_object* v_r_3003_; lean_object* v___x_3004_; uint8_t v___x_3005_; uint8_t v___x_3006_; uint8_t v___x_3007_; 
v_k_3001_ = lean_ctor_get(v_x_3000_, 1);
lean_inc(v_k_3001_);
v_l_3002_ = lean_ctor_get(v_x_3000_, 3);
lean_inc(v_l_3002_);
v_r_3003_ = lean_ctor_get(v_x_3000_, 4);
lean_inc(v_r_3003_);
lean_dec(v_x_3000_);
lean_inc_ref(v_inst_2998_);
lean_inc(v_k_3001_);
lean_inc(v_k_2999_);
v___x_3004_ = lean_apply_2(v_inst_2998_, v_k_2999_, v_k_3001_);
v___x_3005_ = 0;
v___x_3006_ = lean_unbox(v___x_3004_);
v___x_3007_ = l_instDecidableEqOrdering(v___x_3006_, v___x_3005_);
if (v___x_3007_ == 0)
{
lean_dec(v_l_3002_);
lean_dec(v_k_3001_);
v_x_3000_ = v_r_3003_;
goto _start;
}
else
{
lean_object* v___x_3009_; lean_object* v___x_3010_; 
lean_dec(v_r_3003_);
v___x_3009_ = lean_box(0);
v___x_3010_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2998_, v_k_2999_, v___x_3009_, v_l_3002_);
if (lean_obj_tag(v___x_3010_) == 0)
{
return v_k_3001_;
}
else
{
lean_object* v_val_3011_; 
lean_dec(v_k_3001_);
v_val_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_val_3011_);
lean_dec_ref(v___x_3010_);
return v_val_3011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT(lean_object* v_00_u03b1_3012_, lean_object* v_00_u03b2_3013_, lean_object* v_inst_3014_, lean_object* v_inst_3015_, lean_object* v_k_3016_, lean_object* v_x_3017_, lean_object* v_x_3018_, lean_object* v_x_3019_){
_start:
{
lean_object* v___x_3020_; 
v___x_3020_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_inst_3014_, v_k_3016_, v_x_3017_);
return v___x_3020_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object* v_inst_3021_, lean_object* v_k_3022_, lean_object* v_x_3023_){
_start:
{
lean_object* v_k_3024_; lean_object* v_l_3025_; lean_object* v_r_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v_k_3024_ = lean_ctor_get(v_x_3023_, 1);
lean_inc(v_k_3024_);
v_l_3025_ = lean_ctor_get(v_x_3023_, 3);
lean_inc(v_l_3025_);
v_r_3026_ = lean_ctor_get(v_x_3023_, 4);
lean_inc(v_r_3026_);
lean_dec(v_x_3023_);
lean_inc_ref(v_inst_3021_);
lean_inc(v_k_3024_);
lean_inc(v_k_3022_);
v___x_3027_ = lean_apply_2(v_inst_3021_, v_k_3022_, v_k_3024_);
v___x_3028_ = lean_unbox(v___x_3027_);
switch(v___x_3028_)
{
case 0:
{
lean_dec(v_r_3026_);
lean_dec(v_k_3024_);
v_x_3023_ = v_l_3025_;
goto _start;
}
case 1:
{
lean_dec(v_r_3026_);
lean_dec(v_l_3025_);
lean_dec(v_k_3022_);
lean_dec_ref(v_inst_3021_);
return v_k_3024_;
}
default: 
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_dec(v_l_3025_);
v___x_3030_ = lean_box(0);
v___x_3031_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3021_, v_k_3022_, v___x_3030_, v_r_3026_);
if (lean_obj_tag(v___x_3031_) == 0)
{
return v_k_3024_;
}
else
{
lean_object* v_val_3032_; 
lean_dec(v_k_3024_);
v_val_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_val_3032_);
lean_dec_ref(v___x_3031_);
return v_val_3032_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE(lean_object* v_00_u03b1_3033_, lean_object* v_00_u03b2_3034_, lean_object* v_inst_3035_, lean_object* v_inst_3036_, lean_object* v_k_3037_, lean_object* v_x_3038_, lean_object* v_x_3039_, lean_object* v_x_3040_){
_start:
{
lean_object* v___x_3041_; 
v___x_3041_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_inst_3035_, v_k_3037_, v_x_3038_);
return v___x_3041_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object* v_inst_3042_, lean_object* v_k_3043_, lean_object* v_x_3044_){
_start:
{
lean_object* v_k_3045_; lean_object* v_l_3046_; lean_object* v_r_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; uint8_t v___x_3050_; uint8_t v___x_3051_; 
v_k_3045_ = lean_ctor_get(v_x_3044_, 1);
lean_inc(v_k_3045_);
v_l_3046_ = lean_ctor_get(v_x_3044_, 3);
lean_inc(v_l_3046_);
v_r_3047_ = lean_ctor_get(v_x_3044_, 4);
lean_inc(v_r_3047_);
lean_dec(v_x_3044_);
lean_inc_ref(v_inst_3042_);
lean_inc(v_k_3045_);
lean_inc(v_k_3043_);
v___x_3048_ = lean_apply_2(v_inst_3042_, v_k_3043_, v_k_3045_);
v___x_3049_ = 2;
v___x_3050_ = lean_unbox(v___x_3048_);
v___x_3051_ = l_instDecidableEqOrdering(v___x_3050_, v___x_3049_);
if (v___x_3051_ == 0)
{
lean_dec(v_r_3047_);
lean_dec(v_k_3045_);
v_x_3044_ = v_l_3046_;
goto _start;
}
else
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
lean_dec(v_l_3046_);
v___x_3053_ = lean_box(0);
v___x_3054_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3042_, v_k_3043_, v___x_3053_, v_r_3047_);
if (lean_obj_tag(v___x_3054_) == 0)
{
return v_k_3045_;
}
else
{
lean_object* v_val_3055_; 
lean_dec(v_k_3045_);
v_val_3055_ = lean_ctor_get(v___x_3054_, 0);
lean_inc(v_val_3055_);
lean_dec_ref(v___x_3054_);
return v_val_3055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT(lean_object* v_00_u03b1_3056_, lean_object* v_00_u03b2_3057_, lean_object* v_inst_3058_, lean_object* v_inst_3059_, lean_object* v_k_3060_, lean_object* v_x_3061_, lean_object* v_x_3062_, lean_object* v_x_3063_){
_start:
{
lean_object* v___x_3064_; 
v___x_3064_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_inst_3058_, v_k_3060_, v_x_3061_);
return v___x_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object* v_x_3065_){
_start:
{
if (lean_obj_tag(v_x_3065_) == 0)
{
lean_object* v_l_3066_; 
v_l_3066_ = lean_ctor_get(v_x_3065_, 3);
if (lean_obj_tag(v_l_3066_) == 0)
{
v_x_3065_ = v_l_3066_;
goto _start;
}
else
{
lean_object* v_k_3068_; lean_object* v_v_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_k_3068_ = lean_ctor_get(v_x_3065_, 1);
v_v_3069_ = lean_ctor_get(v_x_3065_, 2);
lean_inc(v_v_3069_);
lean_inc(v_k_3068_);
v___x_3070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3070_, 0, v_k_3068_);
lean_ctor_set(v___x_3070_, 1, v_v_3069_);
v___x_3071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
return v___x_3071_;
}
}
else
{
lean_object* v___x_3072_; 
v___x_3072_ = lean_box(0);
return v___x_3072_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg___boxed(lean_object* v_x_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3073_);
lean_dec(v_x_3073_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(lean_object* v_00_u03b1_3075_, lean_object* v_00_u03b2_3076_, lean_object* v_x_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3077_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_3079_, lean_object* v_00_u03b2_3080_, lean_object* v_x_3081_){
_start:
{
lean_object* v_res_3082_; 
v_res_3082_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(v_00_u03b1_3079_, v_00_u03b2_3080_, v_x_3081_);
lean_dec(v_x_3081_);
return v_res_3082_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3083_, lean_object* v_h__1_3084_, lean_object* v_h__2_3085_, lean_object* v_h__3_3086_){
_start:
{
if (lean_obj_tag(v_x_3083_) == 0)
{
lean_object* v_l_3087_; 
lean_dec(v_h__1_3084_);
v_l_3087_ = lean_ctor_get(v_x_3083_, 3);
if (lean_obj_tag(v_l_3087_) == 0)
{
lean_object* v_size_3088_; lean_object* v_k_3089_; lean_object* v_v_3090_; lean_object* v_r_3091_; lean_object* v_size_3092_; lean_object* v_k_3093_; lean_object* v_v_3094_; lean_object* v_l_3095_; lean_object* v_r_3096_; lean_object* v___x_3097_; 
lean_inc_ref(v_l_3087_);
lean_dec(v_h__2_3085_);
v_size_3088_ = lean_ctor_get(v_x_3083_, 0);
lean_inc(v_size_3088_);
v_k_3089_ = lean_ctor_get(v_x_3083_, 1);
lean_inc(v_k_3089_);
v_v_3090_ = lean_ctor_get(v_x_3083_, 2);
lean_inc(v_v_3090_);
v_r_3091_ = lean_ctor_get(v_x_3083_, 4);
lean_inc(v_r_3091_);
lean_dec_ref(v_x_3083_);
v_size_3092_ = lean_ctor_get(v_l_3087_, 0);
lean_inc(v_size_3092_);
v_k_3093_ = lean_ctor_get(v_l_3087_, 1);
lean_inc(v_k_3093_);
v_v_3094_ = lean_ctor_get(v_l_3087_, 2);
lean_inc(v_v_3094_);
v_l_3095_ = lean_ctor_get(v_l_3087_, 3);
lean_inc(v_l_3095_);
v_r_3096_ = lean_ctor_get(v_l_3087_, 4);
lean_inc(v_r_3096_);
lean_dec_ref(v_l_3087_);
v___x_3097_ = lean_apply_9(v_h__3_3086_, v_size_3088_, v_k_3089_, v_v_3090_, v_size_3092_, v_k_3093_, v_v_3094_, v_l_3095_, v_r_3096_, v_r_3091_);
return v___x_3097_;
}
else
{
lean_object* v_size_3098_; lean_object* v_k_3099_; lean_object* v_v_3100_; lean_object* v_r_3101_; lean_object* v___x_3102_; 
lean_dec(v_h__3_3086_);
v_size_3098_ = lean_ctor_get(v_x_3083_, 0);
lean_inc(v_size_3098_);
v_k_3099_ = lean_ctor_get(v_x_3083_, 1);
lean_inc(v_k_3099_);
v_v_3100_ = lean_ctor_get(v_x_3083_, 2);
lean_inc(v_v_3100_);
v_r_3101_ = lean_ctor_get(v_x_3083_, 4);
lean_inc(v_r_3101_);
lean_dec_ref(v_x_3083_);
v___x_3102_ = lean_apply_4(v_h__2_3085_, v_size_3098_, v_k_3099_, v_v_3100_, v_r_3101_);
return v___x_3102_;
}
}
else
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
lean_dec(v_h__3_3086_);
lean_dec(v_h__2_3085_);
v___x_3103_ = lean_box(0);
v___x_3104_ = lean_apply_1(v_h__1_3084_, v___x_3103_);
return v___x_3104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3105_, lean_object* v_00_u03b2_3106_, lean_object* v_motive_3107_, lean_object* v_x_3108_, lean_object* v_h__1_3109_, lean_object* v_h__2_3110_, lean_object* v_h__3_3111_){
_start:
{
if (lean_obj_tag(v_x_3108_) == 0)
{
lean_object* v_l_3112_; 
lean_dec(v_h__1_3109_);
v_l_3112_ = lean_ctor_get(v_x_3108_, 3);
if (lean_obj_tag(v_l_3112_) == 0)
{
lean_object* v_size_3113_; lean_object* v_k_3114_; lean_object* v_v_3115_; lean_object* v_r_3116_; lean_object* v_size_3117_; lean_object* v_k_3118_; lean_object* v_v_3119_; lean_object* v_l_3120_; lean_object* v_r_3121_; lean_object* v___x_3122_; 
lean_inc_ref(v_l_3112_);
lean_dec(v_h__2_3110_);
v_size_3113_ = lean_ctor_get(v_x_3108_, 0);
lean_inc(v_size_3113_);
v_k_3114_ = lean_ctor_get(v_x_3108_, 1);
lean_inc(v_k_3114_);
v_v_3115_ = lean_ctor_get(v_x_3108_, 2);
lean_inc(v_v_3115_);
v_r_3116_ = lean_ctor_get(v_x_3108_, 4);
lean_inc(v_r_3116_);
lean_dec_ref(v_x_3108_);
v_size_3117_ = lean_ctor_get(v_l_3112_, 0);
lean_inc(v_size_3117_);
v_k_3118_ = lean_ctor_get(v_l_3112_, 1);
lean_inc(v_k_3118_);
v_v_3119_ = lean_ctor_get(v_l_3112_, 2);
lean_inc(v_v_3119_);
v_l_3120_ = lean_ctor_get(v_l_3112_, 3);
lean_inc(v_l_3120_);
v_r_3121_ = lean_ctor_get(v_l_3112_, 4);
lean_inc(v_r_3121_);
lean_dec_ref(v_l_3112_);
v___x_3122_ = lean_apply_9(v_h__3_3111_, v_size_3113_, v_k_3114_, v_v_3115_, v_size_3117_, v_k_3118_, v_v_3119_, v_l_3120_, v_r_3121_, v_r_3116_);
return v___x_3122_;
}
else
{
lean_object* v_size_3123_; lean_object* v_k_3124_; lean_object* v_v_3125_; lean_object* v_r_3126_; lean_object* v___x_3127_; 
lean_dec(v_h__3_3111_);
v_size_3123_ = lean_ctor_get(v_x_3108_, 0);
lean_inc(v_size_3123_);
v_k_3124_ = lean_ctor_get(v_x_3108_, 1);
lean_inc(v_k_3124_);
v_v_3125_ = lean_ctor_get(v_x_3108_, 2);
lean_inc(v_v_3125_);
v_r_3126_ = lean_ctor_get(v_x_3108_, 4);
lean_inc(v_r_3126_);
lean_dec_ref(v_x_3108_);
v___x_3127_ = lean_apply_4(v_h__2_3110_, v_size_3123_, v_k_3124_, v_v_3125_, v_r_3126_);
return v___x_3127_;
}
}
else
{
lean_object* v___x_3128_; lean_object* v___x_3129_; 
lean_dec(v_h__3_3111_);
lean_dec(v_h__2_3110_);
v___x_3128_ = lean_box(0);
v___x_3129_ = lean_apply_1(v_h__1_3109_, v___x_3128_);
return v___x_3129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object* v_x_3130_){
_start:
{
lean_object* v_l_3131_; 
v_l_3131_ = lean_ctor_get(v_x_3130_, 3);
if (lean_obj_tag(v_l_3131_) == 0)
{
v_x_3130_ = v_l_3131_;
goto _start;
}
else
{
lean_object* v_k_3133_; lean_object* v_v_3134_; lean_object* v___x_3135_; 
v_k_3133_ = lean_ctor_get(v_x_3130_, 1);
v_v_3134_ = lean_ctor_get(v_x_3130_, 2);
lean_inc(v_v_3134_);
lean_inc(v_k_3133_);
v___x_3135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3135_, 0, v_k_3133_);
lean_ctor_set(v___x_3135_, 1, v_v_3134_);
return v___x_3135_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg___boxed(lean_object* v_x_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3136_);
lean_dec(v_x_3136_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry(lean_object* v_00_u03b1_3138_, lean_object* v_00_u03b2_3139_, lean_object* v_x_3140_, lean_object* v_x_3141_){
_start:
{
lean_object* v___x_3142_; 
v___x_3142_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3140_);
return v___x_3142_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___boxed(lean_object* v_00_u03b1_3143_, lean_object* v_00_u03b2_3144_, lean_object* v_x_3145_, lean_object* v_x_3146_){
_start:
{
lean_object* v_res_3147_; 
v_res_3147_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry(v_00_u03b1_3143_, v_00_u03b2_3144_, v_x_3145_, v_x_3146_);
lean_dec(v_x_3145_);
return v_res_3147_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_3148_, lean_object* v_h__1_3149_, lean_object* v_h__2_3150_){
_start:
{
lean_object* v_l_3151_; 
v_l_3151_ = lean_ctor_get(v_x_3148_, 3);
if (lean_obj_tag(v_l_3151_) == 0)
{
lean_object* v_size_3152_; lean_object* v_k_3153_; lean_object* v_v_3154_; lean_object* v_r_3155_; lean_object* v_size_3156_; lean_object* v_k_3157_; lean_object* v_v_3158_; lean_object* v_l_3159_; lean_object* v_r_3160_; lean_object* v___x_3161_; 
lean_inc_ref(v_l_3151_);
lean_dec(v_h__1_3149_);
v_size_3152_ = lean_ctor_get(v_x_3148_, 0);
lean_inc(v_size_3152_);
v_k_3153_ = lean_ctor_get(v_x_3148_, 1);
lean_inc(v_k_3153_);
v_v_3154_ = lean_ctor_get(v_x_3148_, 2);
lean_inc(v_v_3154_);
v_r_3155_ = lean_ctor_get(v_x_3148_, 4);
lean_inc(v_r_3155_);
lean_dec(v_x_3148_);
v_size_3156_ = lean_ctor_get(v_l_3151_, 0);
lean_inc(v_size_3156_);
v_k_3157_ = lean_ctor_get(v_l_3151_, 1);
lean_inc(v_k_3157_);
v_v_3158_ = lean_ctor_get(v_l_3151_, 2);
lean_inc(v_v_3158_);
v_l_3159_ = lean_ctor_get(v_l_3151_, 3);
lean_inc(v_l_3159_);
v_r_3160_ = lean_ctor_get(v_l_3151_, 4);
lean_inc(v_r_3160_);
lean_dec_ref(v_l_3151_);
v___x_3161_ = lean_apply_10(v_h__2_3150_, v_size_3152_, v_k_3153_, v_v_3154_, v_size_3156_, v_k_3157_, v_v_3158_, v_l_3159_, v_r_3160_, v_r_3155_, lean_box(0));
return v___x_3161_;
}
else
{
lean_object* v_size_3162_; lean_object* v_k_3163_; lean_object* v_v_3164_; lean_object* v_r_3165_; lean_object* v___x_3166_; 
lean_dec(v_h__2_3150_);
v_size_3162_ = lean_ctor_get(v_x_3148_, 0);
lean_inc(v_size_3162_);
v_k_3163_ = lean_ctor_get(v_x_3148_, 1);
lean_inc(v_k_3163_);
v_v_3164_ = lean_ctor_get(v_x_3148_, 2);
lean_inc(v_v_3164_);
v_r_3165_ = lean_ctor_get(v_x_3148_, 4);
lean_inc(v_r_3165_);
lean_dec(v_x_3148_);
v___x_3166_ = lean_apply_5(v_h__1_3149_, v_size_3162_, v_k_3163_, v_v_3164_, v_r_3165_, lean_box(0));
return v___x_3166_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_3167_, lean_object* v_00_u03b2_3168_, lean_object* v_motive_3169_, lean_object* v_x_3170_, lean_object* v_x_3171_, lean_object* v_h__1_3172_, lean_object* v_h__2_3173_){
_start:
{
lean_object* v_l_3174_; 
v_l_3174_ = lean_ctor_get(v_x_3170_, 3);
if (lean_obj_tag(v_l_3174_) == 0)
{
lean_object* v_size_3175_; lean_object* v_k_3176_; lean_object* v_v_3177_; lean_object* v_r_3178_; lean_object* v_size_3179_; lean_object* v_k_3180_; lean_object* v_v_3181_; lean_object* v_l_3182_; lean_object* v_r_3183_; lean_object* v___x_3184_; 
lean_inc_ref(v_l_3174_);
lean_dec(v_h__1_3172_);
v_size_3175_ = lean_ctor_get(v_x_3170_, 0);
lean_inc(v_size_3175_);
v_k_3176_ = lean_ctor_get(v_x_3170_, 1);
lean_inc(v_k_3176_);
v_v_3177_ = lean_ctor_get(v_x_3170_, 2);
lean_inc(v_v_3177_);
v_r_3178_ = lean_ctor_get(v_x_3170_, 4);
lean_inc(v_r_3178_);
lean_dec(v_x_3170_);
v_size_3179_ = lean_ctor_get(v_l_3174_, 0);
lean_inc(v_size_3179_);
v_k_3180_ = lean_ctor_get(v_l_3174_, 1);
lean_inc(v_k_3180_);
v_v_3181_ = lean_ctor_get(v_l_3174_, 2);
lean_inc(v_v_3181_);
v_l_3182_ = lean_ctor_get(v_l_3174_, 3);
lean_inc(v_l_3182_);
v_r_3183_ = lean_ctor_get(v_l_3174_, 4);
lean_inc(v_r_3183_);
lean_dec_ref(v_l_3174_);
v___x_3184_ = lean_apply_10(v_h__2_3173_, v_size_3175_, v_k_3176_, v_v_3177_, v_size_3179_, v_k_3180_, v_v_3181_, v_l_3182_, v_r_3183_, v_r_3178_, lean_box(0));
return v___x_3184_;
}
else
{
lean_object* v_size_3185_; lean_object* v_k_3186_; lean_object* v_v_3187_; lean_object* v_r_3188_; lean_object* v___x_3189_; 
lean_dec(v_h__2_3173_);
v_size_3185_ = lean_ctor_get(v_x_3170_, 0);
lean_inc(v_size_3185_);
v_k_3186_ = lean_ctor_get(v_x_3170_, 1);
lean_inc(v_k_3186_);
v_v_3187_ = lean_ctor_get(v_x_3170_, 2);
lean_inc(v_v_3187_);
v_r_3188_ = lean_ctor_get(v_x_3170_, 4);
lean_inc(v_r_3188_);
lean_dec(v_x_3170_);
v___x_3189_ = lean_apply_5(v_h__1_3172_, v_size_3185_, v_k_3186_, v_v_3187_, v_r_3188_, lean_box(0));
return v___x_3189_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3191_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3192_ = lean_unsigned_to_nat(13u);
v___x_3193_ = lean_unsigned_to_nat(816u);
v___x_3194_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0));
v___x_3195_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3196_ = l_mkPanicMessageWithDecl(v___x_3195_, v___x_3194_, v___x_3193_, v___x_3192_, v___x_3191_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object* v_inst_3197_, lean_object* v_x_3198_){
_start:
{
if (lean_obj_tag(v_x_3198_) == 0)
{
lean_object* v_l_3199_; 
v_l_3199_ = lean_ctor_get(v_x_3198_, 3);
if (lean_obj_tag(v_l_3199_) == 0)
{
v_x_3198_ = v_l_3199_;
goto _start;
}
else
{
lean_object* v_k_3201_; lean_object* v_v_3202_; lean_object* v___x_3203_; 
lean_dec_ref(v_inst_3197_);
v_k_3201_ = lean_ctor_get(v_x_3198_, 1);
v_v_3202_ = lean_ctor_get(v_x_3198_, 2);
lean_inc(v_v_3202_);
lean_inc(v_k_3201_);
v___x_3203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3203_, 0, v_k_3201_);
lean_ctor_set(v___x_3203_, 1, v_v_3202_);
return v___x_3203_;
}
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
v___x_3204_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1);
v___x_3205_ = l_panic___redArg(v_inst_3197_, v___x_3204_);
return v___x_3205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_3206_, lean_object* v_x_3207_){
_start:
{
lean_object* v_res_3208_; 
v_res_3208_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3206_, v_x_3207_);
lean_dec(v_x_3207_);
return v_res_3208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(lean_object* v_00_u03b1_3209_, lean_object* v_00_u03b2_3210_, lean_object* v_inst_3211_, lean_object* v_x_3212_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3211_, v_x_3212_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_3214_, lean_object* v_00_u03b2_3215_, lean_object* v_inst_3216_, lean_object* v_x_3217_){
_start:
{
lean_object* v_res_3218_; 
v_res_3218_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(v_00_u03b1_3214_, v_00_u03b2_3215_, v_inst_3216_, v_x_3217_);
lean_dec(v_x_3217_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object* v_x_3219_, lean_object* v_x_3220_){
_start:
{
if (lean_obj_tag(v_x_3219_) == 0)
{
lean_object* v_l_3221_; 
v_l_3221_ = lean_ctor_get(v_x_3219_, 3);
if (lean_obj_tag(v_l_3221_) == 0)
{
v_x_3219_ = v_l_3221_;
goto _start;
}
else
{
lean_object* v_k_3223_; lean_object* v_v_3224_; lean_object* v___x_3225_; 
v_k_3223_ = lean_ctor_get(v_x_3219_, 1);
v_v_3224_ = lean_ctor_get(v_x_3219_, 2);
lean_inc(v_v_3224_);
lean_inc(v_k_3223_);
v___x_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3225_, 0, v_k_3223_);
lean_ctor_set(v___x_3225_, 1, v_v_3224_);
return v___x_3225_;
}
}
else
{
lean_inc_ref(v_x_3220_);
return v_x_3220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg___boxed(lean_object* v_x_3226_, lean_object* v_x_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3226_, v_x_3227_);
lean_dec_ref(v_x_3227_);
lean_dec(v_x_3226_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD(lean_object* v_00_u03b1_3229_, lean_object* v_00_u03b2_3230_, lean_object* v_x_3231_, lean_object* v_x_3232_){
_start:
{
lean_object* v___x_3233_; 
v___x_3233_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3231_, v_x_3232_);
return v___x_3233_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___boxed(lean_object* v_00_u03b1_3234_, lean_object* v_00_u03b2_3235_, lean_object* v_x_3236_, lean_object* v_x_3237_){
_start:
{
lean_object* v_res_3238_; 
v_res_3238_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD(v_00_u03b1_3234_, v_00_u03b2_3235_, v_x_3236_, v_x_3237_);
lean_dec_ref(v_x_3237_);
lean_dec(v_x_3236_);
return v_res_3238_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_3239_, lean_object* v_x_3240_, lean_object* v_h__1_3241_, lean_object* v_h__2_3242_, lean_object* v_h__3_3243_){
_start:
{
if (lean_obj_tag(v_x_3239_) == 0)
{
lean_object* v_l_3244_; 
lean_dec(v_h__1_3241_);
v_l_3244_ = lean_ctor_get(v_x_3239_, 3);
if (lean_obj_tag(v_l_3244_) == 0)
{
lean_object* v_size_3245_; lean_object* v_k_3246_; lean_object* v_v_3247_; lean_object* v_r_3248_; lean_object* v_size_3249_; lean_object* v_k_3250_; lean_object* v_v_3251_; lean_object* v_l_3252_; lean_object* v_r_3253_; lean_object* v___x_3254_; 
lean_inc_ref(v_l_3244_);
lean_dec(v_h__2_3242_);
v_size_3245_ = lean_ctor_get(v_x_3239_, 0);
lean_inc(v_size_3245_);
v_k_3246_ = lean_ctor_get(v_x_3239_, 1);
lean_inc(v_k_3246_);
v_v_3247_ = lean_ctor_get(v_x_3239_, 2);
lean_inc(v_v_3247_);
v_r_3248_ = lean_ctor_get(v_x_3239_, 4);
lean_inc(v_r_3248_);
lean_dec_ref(v_x_3239_);
v_size_3249_ = lean_ctor_get(v_l_3244_, 0);
lean_inc(v_size_3249_);
v_k_3250_ = lean_ctor_get(v_l_3244_, 1);
lean_inc(v_k_3250_);
v_v_3251_ = lean_ctor_get(v_l_3244_, 2);
lean_inc(v_v_3251_);
v_l_3252_ = lean_ctor_get(v_l_3244_, 3);
lean_inc(v_l_3252_);
v_r_3253_ = lean_ctor_get(v_l_3244_, 4);
lean_inc(v_r_3253_);
lean_dec_ref(v_l_3244_);
v___x_3254_ = lean_apply_10(v_h__3_3243_, v_size_3245_, v_k_3246_, v_v_3247_, v_size_3249_, v_k_3250_, v_v_3251_, v_l_3252_, v_r_3253_, v_r_3248_, v_x_3240_);
return v___x_3254_;
}
else
{
lean_object* v_size_3255_; lean_object* v_k_3256_; lean_object* v_v_3257_; lean_object* v_r_3258_; lean_object* v___x_3259_; 
lean_dec(v_h__3_3243_);
v_size_3255_ = lean_ctor_get(v_x_3239_, 0);
lean_inc(v_size_3255_);
v_k_3256_ = lean_ctor_get(v_x_3239_, 1);
lean_inc(v_k_3256_);
v_v_3257_ = lean_ctor_get(v_x_3239_, 2);
lean_inc(v_v_3257_);
v_r_3258_ = lean_ctor_get(v_x_3239_, 4);
lean_inc(v_r_3258_);
lean_dec_ref(v_x_3239_);
v___x_3259_ = lean_apply_5(v_h__2_3242_, v_size_3255_, v_k_3256_, v_v_3257_, v_r_3258_, v_x_3240_);
return v___x_3259_;
}
}
else
{
lean_object* v___x_3260_; 
lean_dec(v_h__3_3243_);
lean_dec(v_h__2_3242_);
v___x_3260_ = lean_apply_1(v_h__1_3241_, v_x_3240_);
return v___x_3260_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_3261_, lean_object* v_00_u03b2_3262_, lean_object* v_motive_3263_, lean_object* v_x_3264_, lean_object* v_x_3265_, lean_object* v_h__1_3266_, lean_object* v_h__2_3267_, lean_object* v_h__3_3268_){
_start:
{
if (lean_obj_tag(v_x_3264_) == 0)
{
lean_object* v_l_3269_; 
lean_dec(v_h__1_3266_);
v_l_3269_ = lean_ctor_get(v_x_3264_, 3);
if (lean_obj_tag(v_l_3269_) == 0)
{
lean_object* v_size_3270_; lean_object* v_k_3271_; lean_object* v_v_3272_; lean_object* v_r_3273_; lean_object* v_size_3274_; lean_object* v_k_3275_; lean_object* v_v_3276_; lean_object* v_l_3277_; lean_object* v_r_3278_; lean_object* v___x_3279_; 
lean_inc_ref(v_l_3269_);
lean_dec(v_h__2_3267_);
v_size_3270_ = lean_ctor_get(v_x_3264_, 0);
lean_inc(v_size_3270_);
v_k_3271_ = lean_ctor_get(v_x_3264_, 1);
lean_inc(v_k_3271_);
v_v_3272_ = lean_ctor_get(v_x_3264_, 2);
lean_inc(v_v_3272_);
v_r_3273_ = lean_ctor_get(v_x_3264_, 4);
lean_inc(v_r_3273_);
lean_dec_ref(v_x_3264_);
v_size_3274_ = lean_ctor_get(v_l_3269_, 0);
lean_inc(v_size_3274_);
v_k_3275_ = lean_ctor_get(v_l_3269_, 1);
lean_inc(v_k_3275_);
v_v_3276_ = lean_ctor_get(v_l_3269_, 2);
lean_inc(v_v_3276_);
v_l_3277_ = lean_ctor_get(v_l_3269_, 3);
lean_inc(v_l_3277_);
v_r_3278_ = lean_ctor_get(v_l_3269_, 4);
lean_inc(v_r_3278_);
lean_dec_ref(v_l_3269_);
v___x_3279_ = lean_apply_10(v_h__3_3268_, v_size_3270_, v_k_3271_, v_v_3272_, v_size_3274_, v_k_3275_, v_v_3276_, v_l_3277_, v_r_3278_, v_r_3273_, v_x_3265_);
return v___x_3279_;
}
else
{
lean_object* v_size_3280_; lean_object* v_k_3281_; lean_object* v_v_3282_; lean_object* v_r_3283_; lean_object* v___x_3284_; 
lean_dec(v_h__3_3268_);
v_size_3280_ = lean_ctor_get(v_x_3264_, 0);
lean_inc(v_size_3280_);
v_k_3281_ = lean_ctor_get(v_x_3264_, 1);
lean_inc(v_k_3281_);
v_v_3282_ = lean_ctor_get(v_x_3264_, 2);
lean_inc(v_v_3282_);
v_r_3283_ = lean_ctor_get(v_x_3264_, 4);
lean_inc(v_r_3283_);
lean_dec_ref(v_x_3264_);
v___x_3284_ = lean_apply_5(v_h__2_3267_, v_size_3280_, v_k_3281_, v_v_3282_, v_r_3283_, v_x_3265_);
return v___x_3284_;
}
}
else
{
lean_object* v___x_3285_; 
lean_dec(v_h__3_3268_);
lean_dec(v_h__2_3267_);
v___x_3285_ = lean_apply_1(v_h__1_3266_, v_x_3265_);
return v___x_3285_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object* v_x_3286_){
_start:
{
if (lean_obj_tag(v_x_3286_) == 0)
{
lean_object* v_r_3287_; 
v_r_3287_ = lean_ctor_get(v_x_3286_, 4);
if (lean_obj_tag(v_r_3287_) == 0)
{
v_x_3286_ = v_r_3287_;
goto _start;
}
else
{
lean_object* v_k_3289_; lean_object* v_v_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; 
v_k_3289_ = lean_ctor_get(v_x_3286_, 1);
v_v_3290_ = lean_ctor_get(v_x_3286_, 2);
lean_inc(v_v_3290_);
lean_inc(v_k_3289_);
v___x_3291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3291_, 0, v_k_3289_);
lean_ctor_set(v___x_3291_, 1, v_v_3290_);
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
return v___x_3292_;
}
}
else
{
lean_object* v___x_3293_; 
v___x_3293_ = lean_box(0);
return v___x_3293_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg___boxed(lean_object* v_x_3294_){
_start:
{
lean_object* v_res_3295_; 
v_res_3295_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3294_);
lean_dec(v_x_3294_);
return v_res_3295_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(lean_object* v_00_u03b1_3296_, lean_object* v_00_u03b2_3297_, lean_object* v_x_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_3300_, lean_object* v_00_u03b2_3301_, lean_object* v_x_3302_){
_start:
{
lean_object* v_res_3303_; 
v_res_3303_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(v_00_u03b1_3300_, v_00_u03b2_3301_, v_x_3302_);
lean_dec(v_x_3302_);
return v_res_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3304_, lean_object* v_h__1_3305_, lean_object* v_h__2_3306_, lean_object* v_h__3_3307_){
_start:
{
if (lean_obj_tag(v_x_3304_) == 0)
{
lean_object* v_r_3308_; 
lean_dec(v_h__1_3305_);
v_r_3308_ = lean_ctor_get(v_x_3304_, 4);
if (lean_obj_tag(v_r_3308_) == 0)
{
lean_object* v_size_3309_; lean_object* v_k_3310_; lean_object* v_v_3311_; lean_object* v_l_3312_; lean_object* v_size_3313_; lean_object* v_k_3314_; lean_object* v_v_3315_; lean_object* v_l_3316_; lean_object* v_r_3317_; lean_object* v___x_3318_; 
lean_inc_ref(v_r_3308_);
lean_dec(v_h__2_3306_);
v_size_3309_ = lean_ctor_get(v_x_3304_, 0);
lean_inc(v_size_3309_);
v_k_3310_ = lean_ctor_get(v_x_3304_, 1);
lean_inc(v_k_3310_);
v_v_3311_ = lean_ctor_get(v_x_3304_, 2);
lean_inc(v_v_3311_);
v_l_3312_ = lean_ctor_get(v_x_3304_, 3);
lean_inc(v_l_3312_);
lean_dec_ref(v_x_3304_);
v_size_3313_ = lean_ctor_get(v_r_3308_, 0);
lean_inc(v_size_3313_);
v_k_3314_ = lean_ctor_get(v_r_3308_, 1);
lean_inc(v_k_3314_);
v_v_3315_ = lean_ctor_get(v_r_3308_, 2);
lean_inc(v_v_3315_);
v_l_3316_ = lean_ctor_get(v_r_3308_, 3);
lean_inc(v_l_3316_);
v_r_3317_ = lean_ctor_get(v_r_3308_, 4);
lean_inc(v_r_3317_);
lean_dec_ref(v_r_3308_);
v___x_3318_ = lean_apply_9(v_h__3_3307_, v_size_3309_, v_k_3310_, v_v_3311_, v_l_3312_, v_size_3313_, v_k_3314_, v_v_3315_, v_l_3316_, v_r_3317_);
return v___x_3318_;
}
else
{
lean_object* v_size_3319_; lean_object* v_k_3320_; lean_object* v_v_3321_; lean_object* v_l_3322_; lean_object* v___x_3323_; 
lean_dec(v_h__3_3307_);
v_size_3319_ = lean_ctor_get(v_x_3304_, 0);
lean_inc(v_size_3319_);
v_k_3320_ = lean_ctor_get(v_x_3304_, 1);
lean_inc(v_k_3320_);
v_v_3321_ = lean_ctor_get(v_x_3304_, 2);
lean_inc(v_v_3321_);
v_l_3322_ = lean_ctor_get(v_x_3304_, 3);
lean_inc(v_l_3322_);
lean_dec_ref(v_x_3304_);
v___x_3323_ = lean_apply_4(v_h__2_3306_, v_size_3319_, v_k_3320_, v_v_3321_, v_l_3322_);
return v___x_3323_;
}
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; 
lean_dec(v_h__3_3307_);
lean_dec(v_h__2_3306_);
v___x_3324_ = lean_box(0);
v___x_3325_ = lean_apply_1(v_h__1_3305_, v___x_3324_);
return v___x_3325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3326_, lean_object* v_00_u03b2_3327_, lean_object* v_motive_3328_, lean_object* v_x_3329_, lean_object* v_h__1_3330_, lean_object* v_h__2_3331_, lean_object* v_h__3_3332_){
_start:
{
if (lean_obj_tag(v_x_3329_) == 0)
{
lean_object* v_r_3333_; 
lean_dec(v_h__1_3330_);
v_r_3333_ = lean_ctor_get(v_x_3329_, 4);
if (lean_obj_tag(v_r_3333_) == 0)
{
lean_object* v_size_3334_; lean_object* v_k_3335_; lean_object* v_v_3336_; lean_object* v_l_3337_; lean_object* v_size_3338_; lean_object* v_k_3339_; lean_object* v_v_3340_; lean_object* v_l_3341_; lean_object* v_r_3342_; lean_object* v___x_3343_; 
lean_inc_ref(v_r_3333_);
lean_dec(v_h__2_3331_);
v_size_3334_ = lean_ctor_get(v_x_3329_, 0);
lean_inc(v_size_3334_);
v_k_3335_ = lean_ctor_get(v_x_3329_, 1);
lean_inc(v_k_3335_);
v_v_3336_ = lean_ctor_get(v_x_3329_, 2);
lean_inc(v_v_3336_);
v_l_3337_ = lean_ctor_get(v_x_3329_, 3);
lean_inc(v_l_3337_);
lean_dec_ref(v_x_3329_);
v_size_3338_ = lean_ctor_get(v_r_3333_, 0);
lean_inc(v_size_3338_);
v_k_3339_ = lean_ctor_get(v_r_3333_, 1);
lean_inc(v_k_3339_);
v_v_3340_ = lean_ctor_get(v_r_3333_, 2);
lean_inc(v_v_3340_);
v_l_3341_ = lean_ctor_get(v_r_3333_, 3);
lean_inc(v_l_3341_);
v_r_3342_ = lean_ctor_get(v_r_3333_, 4);
lean_inc(v_r_3342_);
lean_dec_ref(v_r_3333_);
v___x_3343_ = lean_apply_9(v_h__3_3332_, v_size_3334_, v_k_3335_, v_v_3336_, v_l_3337_, v_size_3338_, v_k_3339_, v_v_3340_, v_l_3341_, v_r_3342_);
return v___x_3343_;
}
else
{
lean_object* v_size_3344_; lean_object* v_k_3345_; lean_object* v_v_3346_; lean_object* v_l_3347_; lean_object* v___x_3348_; 
lean_dec(v_h__3_3332_);
v_size_3344_ = lean_ctor_get(v_x_3329_, 0);
lean_inc(v_size_3344_);
v_k_3345_ = lean_ctor_get(v_x_3329_, 1);
lean_inc(v_k_3345_);
v_v_3346_ = lean_ctor_get(v_x_3329_, 2);
lean_inc(v_v_3346_);
v_l_3347_ = lean_ctor_get(v_x_3329_, 3);
lean_inc(v_l_3347_);
lean_dec_ref(v_x_3329_);
v___x_3348_ = lean_apply_4(v_h__2_3331_, v_size_3344_, v_k_3345_, v_v_3346_, v_l_3347_);
return v___x_3348_;
}
}
else
{
lean_object* v___x_3349_; lean_object* v___x_3350_; 
lean_dec(v_h__3_3332_);
lean_dec(v_h__2_3331_);
v___x_3349_ = lean_box(0);
v___x_3350_ = lean_apply_1(v_h__1_3330_, v___x_3349_);
return v___x_3350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object* v_x_3351_){
_start:
{
lean_object* v_r_3352_; 
v_r_3352_ = lean_ctor_get(v_x_3351_, 4);
if (lean_obj_tag(v_r_3352_) == 0)
{
v_x_3351_ = v_r_3352_;
goto _start;
}
else
{
lean_object* v_k_3354_; lean_object* v_v_3355_; lean_object* v___x_3356_; 
v_k_3354_ = lean_ctor_get(v_x_3351_, 1);
v_v_3355_ = lean_ctor_get(v_x_3351_, 2);
lean_inc(v_v_3355_);
lean_inc(v_k_3354_);
v___x_3356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3356_, 0, v_k_3354_);
lean_ctor_set(v___x_3356_, 1, v_v_3355_);
return v___x_3356_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg___boxed(lean_object* v_x_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3357_);
lean_dec(v_x_3357_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry(lean_object* v_00_u03b1_3359_, lean_object* v_00_u03b2_3360_, lean_object* v_x_3361_, lean_object* v_x_3362_){
_start:
{
lean_object* v___x_3363_; 
v___x_3363_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3361_);
return v___x_3363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___boxed(lean_object* v_00_u03b1_3364_, lean_object* v_00_u03b2_3365_, lean_object* v_x_3366_, lean_object* v_x_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry(v_00_u03b1_3364_, v_00_u03b2_3365_, v_x_3366_, v_x_3367_);
lean_dec(v_x_3366_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_3369_, lean_object* v_h__1_3370_, lean_object* v_h__2_3371_){
_start:
{
lean_object* v_r_3372_; 
v_r_3372_ = lean_ctor_get(v_x_3369_, 4);
if (lean_obj_tag(v_r_3372_) == 0)
{
lean_object* v_size_3373_; lean_object* v_k_3374_; lean_object* v_v_3375_; lean_object* v_l_3376_; lean_object* v_size_3377_; lean_object* v_k_3378_; lean_object* v_v_3379_; lean_object* v_l_3380_; lean_object* v_r_3381_; lean_object* v___x_3382_; 
lean_inc_ref(v_r_3372_);
lean_dec(v_h__1_3370_);
v_size_3373_ = lean_ctor_get(v_x_3369_, 0);
lean_inc(v_size_3373_);
v_k_3374_ = lean_ctor_get(v_x_3369_, 1);
lean_inc(v_k_3374_);
v_v_3375_ = lean_ctor_get(v_x_3369_, 2);
lean_inc(v_v_3375_);
v_l_3376_ = lean_ctor_get(v_x_3369_, 3);
lean_inc(v_l_3376_);
lean_dec(v_x_3369_);
v_size_3377_ = lean_ctor_get(v_r_3372_, 0);
lean_inc(v_size_3377_);
v_k_3378_ = lean_ctor_get(v_r_3372_, 1);
lean_inc(v_k_3378_);
v_v_3379_ = lean_ctor_get(v_r_3372_, 2);
lean_inc(v_v_3379_);
v_l_3380_ = lean_ctor_get(v_r_3372_, 3);
lean_inc(v_l_3380_);
v_r_3381_ = lean_ctor_get(v_r_3372_, 4);
lean_inc(v_r_3381_);
lean_dec_ref(v_r_3372_);
v___x_3382_ = lean_apply_10(v_h__2_3371_, v_size_3373_, v_k_3374_, v_v_3375_, v_l_3376_, v_size_3377_, v_k_3378_, v_v_3379_, v_l_3380_, v_r_3381_, lean_box(0));
return v___x_3382_;
}
else
{
lean_object* v_size_3383_; lean_object* v_k_3384_; lean_object* v_v_3385_; lean_object* v_l_3386_; lean_object* v___x_3387_; 
lean_dec(v_h__2_3371_);
v_size_3383_ = lean_ctor_get(v_x_3369_, 0);
lean_inc(v_size_3383_);
v_k_3384_ = lean_ctor_get(v_x_3369_, 1);
lean_inc(v_k_3384_);
v_v_3385_ = lean_ctor_get(v_x_3369_, 2);
lean_inc(v_v_3385_);
v_l_3386_ = lean_ctor_get(v_x_3369_, 3);
lean_inc(v_l_3386_);
lean_dec(v_x_3369_);
v___x_3387_ = lean_apply_5(v_h__1_3370_, v_size_3383_, v_k_3384_, v_v_3385_, v_l_3386_, lean_box(0));
return v___x_3387_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_3388_, lean_object* v_00_u03b2_3389_, lean_object* v_motive_3390_, lean_object* v_x_3391_, lean_object* v_x_3392_, lean_object* v_h__1_3393_, lean_object* v_h__2_3394_){
_start:
{
lean_object* v_r_3395_; 
v_r_3395_ = lean_ctor_get(v_x_3391_, 4);
if (lean_obj_tag(v_r_3395_) == 0)
{
lean_object* v_size_3396_; lean_object* v_k_3397_; lean_object* v_v_3398_; lean_object* v_l_3399_; lean_object* v_size_3400_; lean_object* v_k_3401_; lean_object* v_v_3402_; lean_object* v_l_3403_; lean_object* v_r_3404_; lean_object* v___x_3405_; 
lean_inc_ref(v_r_3395_);
lean_dec(v_h__1_3393_);
v_size_3396_ = lean_ctor_get(v_x_3391_, 0);
lean_inc(v_size_3396_);
v_k_3397_ = lean_ctor_get(v_x_3391_, 1);
lean_inc(v_k_3397_);
v_v_3398_ = lean_ctor_get(v_x_3391_, 2);
lean_inc(v_v_3398_);
v_l_3399_ = lean_ctor_get(v_x_3391_, 3);
lean_inc(v_l_3399_);
lean_dec(v_x_3391_);
v_size_3400_ = lean_ctor_get(v_r_3395_, 0);
lean_inc(v_size_3400_);
v_k_3401_ = lean_ctor_get(v_r_3395_, 1);
lean_inc(v_k_3401_);
v_v_3402_ = lean_ctor_get(v_r_3395_, 2);
lean_inc(v_v_3402_);
v_l_3403_ = lean_ctor_get(v_r_3395_, 3);
lean_inc(v_l_3403_);
v_r_3404_ = lean_ctor_get(v_r_3395_, 4);
lean_inc(v_r_3404_);
lean_dec_ref(v_r_3395_);
v___x_3405_ = lean_apply_10(v_h__2_3394_, v_size_3396_, v_k_3397_, v_v_3398_, v_l_3399_, v_size_3400_, v_k_3401_, v_v_3402_, v_l_3403_, v_r_3404_, lean_box(0));
return v___x_3405_;
}
else
{
lean_object* v_size_3406_; lean_object* v_k_3407_; lean_object* v_v_3408_; lean_object* v_l_3409_; lean_object* v___x_3410_; 
lean_dec(v_h__2_3394_);
v_size_3406_ = lean_ctor_get(v_x_3391_, 0);
lean_inc(v_size_3406_);
v_k_3407_ = lean_ctor_get(v_x_3391_, 1);
lean_inc(v_k_3407_);
v_v_3408_ = lean_ctor_get(v_x_3391_, 2);
lean_inc(v_v_3408_);
v_l_3409_ = lean_ctor_get(v_x_3391_, 3);
lean_inc(v_l_3409_);
lean_dec(v_x_3391_);
v___x_3410_ = lean_apply_5(v_h__1_3393_, v_size_3406_, v_k_3407_, v_v_3408_, v_l_3409_, lean_box(0));
return v___x_3410_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3412_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3413_ = lean_unsigned_to_nat(13u);
v___x_3414_ = lean_unsigned_to_nat(839u);
v___x_3415_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0));
v___x_3416_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3417_ = l_mkPanicMessageWithDecl(v___x_3416_, v___x_3415_, v___x_3414_, v___x_3413_, v___x_3412_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object* v_inst_3418_, lean_object* v_x_3419_){
_start:
{
if (lean_obj_tag(v_x_3419_) == 0)
{
lean_object* v_r_3420_; 
v_r_3420_ = lean_ctor_get(v_x_3419_, 4);
if (lean_obj_tag(v_r_3420_) == 0)
{
v_x_3419_ = v_r_3420_;
goto _start;
}
else
{
lean_object* v_k_3422_; lean_object* v_v_3423_; lean_object* v___x_3424_; 
lean_dec_ref(v_inst_3418_);
v_k_3422_ = lean_ctor_get(v_x_3419_, 1);
v_v_3423_ = lean_ctor_get(v_x_3419_, 2);
lean_inc(v_v_3423_);
lean_inc(v_k_3422_);
v___x_3424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3424_, 0, v_k_3422_);
lean_ctor_set(v___x_3424_, 1, v_v_3423_);
return v___x_3424_;
}
}
else
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1);
v___x_3426_ = l_panic___redArg(v_inst_3418_, v___x_3425_);
return v___x_3426_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_3427_, lean_object* v_x_3428_){
_start:
{
lean_object* v_res_3429_; 
v_res_3429_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3427_, v_x_3428_);
lean_dec(v_x_3428_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(lean_object* v_00_u03b1_3430_, lean_object* v_00_u03b2_3431_, lean_object* v_inst_3432_, lean_object* v_x_3433_){
_start:
{
lean_object* v___x_3434_; 
v___x_3434_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3432_, v_x_3433_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_3435_, lean_object* v_00_u03b2_3436_, lean_object* v_inst_3437_, lean_object* v_x_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(v_00_u03b1_3435_, v_00_u03b2_3436_, v_inst_3437_, v_x_3438_);
lean_dec(v_x_3438_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object* v_x_3440_, lean_object* v_x_3441_){
_start:
{
if (lean_obj_tag(v_x_3440_) == 0)
{
lean_object* v_r_3442_; 
v_r_3442_ = lean_ctor_get(v_x_3440_, 4);
if (lean_obj_tag(v_r_3442_) == 0)
{
v_x_3440_ = v_r_3442_;
goto _start;
}
else
{
lean_object* v_k_3444_; lean_object* v_v_3445_; lean_object* v___x_3446_; 
v_k_3444_ = lean_ctor_get(v_x_3440_, 1);
v_v_3445_ = lean_ctor_get(v_x_3440_, 2);
lean_inc(v_v_3445_);
lean_inc(v_k_3444_);
v___x_3446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3446_, 0, v_k_3444_);
lean_ctor_set(v___x_3446_, 1, v_v_3445_);
return v___x_3446_;
}
}
else
{
lean_inc_ref(v_x_3441_);
return v_x_3441_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg___boxed(lean_object* v_x_3447_, lean_object* v_x_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3447_, v_x_3448_);
lean_dec_ref(v_x_3448_);
lean_dec(v_x_3447_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(lean_object* v_00_u03b1_3450_, lean_object* v_00_u03b2_3451_, lean_object* v_x_3452_, lean_object* v_x_3453_){
_start:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3452_, v_x_3453_);
return v___x_3454_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___boxed(lean_object* v_00_u03b1_3455_, lean_object* v_00_u03b2_3456_, lean_object* v_x_3457_, lean_object* v_x_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(v_00_u03b1_3455_, v_00_u03b2_3456_, v_x_3457_, v_x_3458_);
lean_dec_ref(v_x_3458_);
lean_dec(v_x_3457_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_3460_, lean_object* v_x_3461_, lean_object* v_h__1_3462_, lean_object* v_h__2_3463_, lean_object* v_h__3_3464_){
_start:
{
if (lean_obj_tag(v_x_3460_) == 0)
{
lean_object* v_r_3465_; 
lean_dec(v_h__1_3462_);
v_r_3465_ = lean_ctor_get(v_x_3460_, 4);
if (lean_obj_tag(v_r_3465_) == 0)
{
lean_object* v_size_3466_; lean_object* v_k_3467_; lean_object* v_v_3468_; lean_object* v_l_3469_; lean_object* v_size_3470_; lean_object* v_k_3471_; lean_object* v_v_3472_; lean_object* v_l_3473_; lean_object* v_r_3474_; lean_object* v___x_3475_; 
lean_inc_ref(v_r_3465_);
lean_dec(v_h__2_3463_);
v_size_3466_ = lean_ctor_get(v_x_3460_, 0);
lean_inc(v_size_3466_);
v_k_3467_ = lean_ctor_get(v_x_3460_, 1);
lean_inc(v_k_3467_);
v_v_3468_ = lean_ctor_get(v_x_3460_, 2);
lean_inc(v_v_3468_);
v_l_3469_ = lean_ctor_get(v_x_3460_, 3);
lean_inc(v_l_3469_);
lean_dec_ref(v_x_3460_);
v_size_3470_ = lean_ctor_get(v_r_3465_, 0);
lean_inc(v_size_3470_);
v_k_3471_ = lean_ctor_get(v_r_3465_, 1);
lean_inc(v_k_3471_);
v_v_3472_ = lean_ctor_get(v_r_3465_, 2);
lean_inc(v_v_3472_);
v_l_3473_ = lean_ctor_get(v_r_3465_, 3);
lean_inc(v_l_3473_);
v_r_3474_ = lean_ctor_get(v_r_3465_, 4);
lean_inc(v_r_3474_);
lean_dec_ref(v_r_3465_);
v___x_3475_ = lean_apply_10(v_h__3_3464_, v_size_3466_, v_k_3467_, v_v_3468_, v_l_3469_, v_size_3470_, v_k_3471_, v_v_3472_, v_l_3473_, v_r_3474_, v_x_3461_);
return v___x_3475_;
}
else
{
lean_object* v_size_3476_; lean_object* v_k_3477_; lean_object* v_v_3478_; lean_object* v_l_3479_; lean_object* v___x_3480_; 
lean_dec(v_h__3_3464_);
v_size_3476_ = lean_ctor_get(v_x_3460_, 0);
lean_inc(v_size_3476_);
v_k_3477_ = lean_ctor_get(v_x_3460_, 1);
lean_inc(v_k_3477_);
v_v_3478_ = lean_ctor_get(v_x_3460_, 2);
lean_inc(v_v_3478_);
v_l_3479_ = lean_ctor_get(v_x_3460_, 3);
lean_inc(v_l_3479_);
lean_dec_ref(v_x_3460_);
v___x_3480_ = lean_apply_5(v_h__2_3463_, v_size_3476_, v_k_3477_, v_v_3478_, v_l_3479_, v_x_3461_);
return v___x_3480_;
}
}
else
{
lean_object* v___x_3481_; 
lean_dec(v_h__3_3464_);
lean_dec(v_h__2_3463_);
v___x_3481_ = lean_apply_1(v_h__1_3462_, v_x_3461_);
return v___x_3481_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_3482_, lean_object* v_00_u03b2_3483_, lean_object* v_motive_3484_, lean_object* v_x_3485_, lean_object* v_x_3486_, lean_object* v_h__1_3487_, lean_object* v_h__2_3488_, lean_object* v_h__3_3489_){
_start:
{
if (lean_obj_tag(v_x_3485_) == 0)
{
lean_object* v_r_3490_; 
lean_dec(v_h__1_3487_);
v_r_3490_ = lean_ctor_get(v_x_3485_, 4);
if (lean_obj_tag(v_r_3490_) == 0)
{
lean_object* v_size_3491_; lean_object* v_k_3492_; lean_object* v_v_3493_; lean_object* v_l_3494_; lean_object* v_size_3495_; lean_object* v_k_3496_; lean_object* v_v_3497_; lean_object* v_l_3498_; lean_object* v_r_3499_; lean_object* v___x_3500_; 
lean_inc_ref(v_r_3490_);
lean_dec(v_h__2_3488_);
v_size_3491_ = lean_ctor_get(v_x_3485_, 0);
lean_inc(v_size_3491_);
v_k_3492_ = lean_ctor_get(v_x_3485_, 1);
lean_inc(v_k_3492_);
v_v_3493_ = lean_ctor_get(v_x_3485_, 2);
lean_inc(v_v_3493_);
v_l_3494_ = lean_ctor_get(v_x_3485_, 3);
lean_inc(v_l_3494_);
lean_dec_ref(v_x_3485_);
v_size_3495_ = lean_ctor_get(v_r_3490_, 0);
lean_inc(v_size_3495_);
v_k_3496_ = lean_ctor_get(v_r_3490_, 1);
lean_inc(v_k_3496_);
v_v_3497_ = lean_ctor_get(v_r_3490_, 2);
lean_inc(v_v_3497_);
v_l_3498_ = lean_ctor_get(v_r_3490_, 3);
lean_inc(v_l_3498_);
v_r_3499_ = lean_ctor_get(v_r_3490_, 4);
lean_inc(v_r_3499_);
lean_dec_ref(v_r_3490_);
v___x_3500_ = lean_apply_10(v_h__3_3489_, v_size_3491_, v_k_3492_, v_v_3493_, v_l_3494_, v_size_3495_, v_k_3496_, v_v_3497_, v_l_3498_, v_r_3499_, v_x_3486_);
return v___x_3500_;
}
else
{
lean_object* v_size_3501_; lean_object* v_k_3502_; lean_object* v_v_3503_; lean_object* v_l_3504_; lean_object* v___x_3505_; 
lean_dec(v_h__3_3489_);
v_size_3501_ = lean_ctor_get(v_x_3485_, 0);
lean_inc(v_size_3501_);
v_k_3502_ = lean_ctor_get(v_x_3485_, 1);
lean_inc(v_k_3502_);
v_v_3503_ = lean_ctor_get(v_x_3485_, 2);
lean_inc(v_v_3503_);
v_l_3504_ = lean_ctor_get(v_x_3485_, 3);
lean_inc(v_l_3504_);
lean_dec_ref(v_x_3485_);
v___x_3505_ = lean_apply_5(v_h__2_3488_, v_size_3501_, v_k_3502_, v_v_3503_, v_l_3504_, v_x_3486_);
return v___x_3505_;
}
}
else
{
lean_object* v___x_3506_; 
lean_dec(v_h__3_3489_);
lean_dec(v_h__2_3488_);
v___x_3506_ = lean_apply_1(v_h__1_3487_, v_x_3486_);
return v___x_3506_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object* v_x_3507_, lean_object* v_x_3508_){
_start:
{
lean_object* v_k_3509_; lean_object* v_v_3510_; lean_object* v_l_3511_; lean_object* v_r_3512_; lean_object* v___y_3514_; lean_object* v___y_3520_; 
v_k_3509_ = lean_ctor_get(v_x_3507_, 1);
v_v_3510_ = lean_ctor_get(v_x_3507_, 2);
v_l_3511_ = lean_ctor_get(v_x_3507_, 3);
v_r_3512_ = lean_ctor_get(v_x_3507_, 4);
if (lean_obj_tag(v_l_3511_) == 0)
{
lean_object* v_size_3527_; 
v_size_3527_ = lean_ctor_get(v_l_3511_, 0);
v___y_3520_ = v_size_3527_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3528_; 
v___x_3528_ = lean_unsigned_to_nat(0u);
v___y_3520_ = v___x_3528_;
goto v___jp_3519_;
}
v___jp_3513_:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_nat_sub(v_x_3508_, v___y_3514_);
lean_dec(v_x_3508_);
v___x_3516_ = lean_unsigned_to_nat(1u);
v___x_3517_ = lean_nat_sub(v___x_3515_, v___x_3516_);
lean_dec(v___x_3515_);
v_x_3507_ = v_r_3512_;
v_x_3508_ = v___x_3517_;
goto _start;
}
v___jp_3519_:
{
uint8_t v___x_3521_; 
v___x_3521_ = lean_nat_dec_lt(v_x_3508_, v___y_3520_);
if (v___x_3521_ == 0)
{
uint8_t v___x_3522_; 
v___x_3522_ = lean_nat_dec_eq(v_x_3508_, v___y_3520_);
if (v___x_3522_ == 0)
{
if (lean_obj_tag(v_l_3511_) == 0)
{
lean_object* v_size_3523_; 
v_size_3523_ = lean_ctor_get(v_l_3511_, 0);
v___y_3514_ = v_size_3523_;
goto v___jp_3513_;
}
else
{
lean_object* v___x_3524_; 
v___x_3524_ = lean_unsigned_to_nat(0u);
v___y_3514_ = v___x_3524_;
goto v___jp_3513_;
}
}
else
{
lean_object* v___x_3525_; 
lean_dec(v_x_3508_);
lean_inc(v_v_3510_);
lean_inc(v_k_3509_);
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v_k_3509_);
lean_ctor_set(v___x_3525_, 1, v_v_3510_);
return v___x_3525_;
}
}
else
{
v_x_3507_ = v_l_3511_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg___boxed(lean_object* v_x_3529_, lean_object* v_x_3530_){
_start:
{
lean_object* v_res_3531_; 
v_res_3531_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3529_, v_x_3530_);
lean_dec(v_x_3529_);
return v_res_3531_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_object* v_00_u03b1_3532_, lean_object* v_00_u03b2_3533_, lean_object* v_x_3534_, lean_object* v_x_3535_, lean_object* v_x_3536_, lean_object* v_x_3537_){
_start:
{
lean_object* v___x_3538_; 
v___x_3538_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3534_, v_x_3536_);
return v___x_3538_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_3539_, lean_object* v_00_u03b2_3540_, lean_object* v_x_3541_, lean_object* v_x_3542_, lean_object* v_x_3543_, lean_object* v_x_3544_){
_start:
{
lean_object* v_res_3545_; 
v_res_3545_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(v_00_u03b1_3539_, v_00_u03b2_3540_, v_x_3541_, v_x_3542_, v_x_3543_, v_x_3544_);
lean_dec(v_x_3541_);
return v_res_3545_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object* v_x_3546_, lean_object* v_x_3547_){
_start:
{
if (lean_obj_tag(v_x_3546_) == 0)
{
lean_object* v_k_3548_; lean_object* v_v_3549_; lean_object* v_l_3550_; lean_object* v_r_3551_; lean_object* v___y_3553_; lean_object* v___y_3559_; 
v_k_3548_ = lean_ctor_get(v_x_3546_, 1);
v_v_3549_ = lean_ctor_get(v_x_3546_, 2);
v_l_3550_ = lean_ctor_get(v_x_3546_, 3);
v_r_3551_ = lean_ctor_get(v_x_3546_, 4);
if (lean_obj_tag(v_l_3550_) == 0)
{
lean_object* v_size_3567_; 
v_size_3567_ = lean_ctor_get(v_l_3550_, 0);
v___y_3559_ = v_size_3567_;
goto v___jp_3558_;
}
else
{
lean_object* v___x_3568_; 
v___x_3568_ = lean_unsigned_to_nat(0u);
v___y_3559_ = v___x_3568_;
goto v___jp_3558_;
}
v___jp_3552_:
{
lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = lean_nat_sub(v_x_3547_, v___y_3553_);
lean_dec(v_x_3547_);
v___x_3555_ = lean_unsigned_to_nat(1u);
v___x_3556_ = lean_nat_sub(v___x_3554_, v___x_3555_);
lean_dec(v___x_3554_);
v_x_3546_ = v_r_3551_;
v_x_3547_ = v___x_3556_;
goto _start;
}
v___jp_3558_:
{
uint8_t v___x_3560_; 
v___x_3560_ = lean_nat_dec_lt(v_x_3547_, v___y_3559_);
if (v___x_3560_ == 0)
{
uint8_t v___x_3561_; 
v___x_3561_ = lean_nat_dec_eq(v_x_3547_, v___y_3559_);
if (v___x_3561_ == 0)
{
if (lean_obj_tag(v_l_3550_) == 0)
{
lean_object* v_size_3562_; 
v_size_3562_ = lean_ctor_get(v_l_3550_, 0);
v___y_3553_ = v_size_3562_;
goto v___jp_3552_;
}
else
{
lean_object* v___x_3563_; 
v___x_3563_ = lean_unsigned_to_nat(0u);
v___y_3553_ = v___x_3563_;
goto v___jp_3552_;
}
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
lean_dec(v_x_3547_);
lean_inc(v_v_3549_);
lean_inc(v_k_3548_);
v___x_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3564_, 0, v_k_3548_);
lean_ctor_set(v___x_3564_, 1, v_v_3549_);
v___x_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___x_3564_);
return v___x_3565_;
}
}
else
{
v_x_3546_ = v_l_3550_;
goto _start;
}
}
}
else
{
lean_object* v___x_3569_; 
lean_dec(v_x_3547_);
v___x_3569_ = lean_box(0);
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_3570_, lean_object* v_x_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3570_, v_x_3571_);
lean_dec(v_x_3570_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_3573_, lean_object* v_00_u03b2_3574_, lean_object* v_x_3575_, lean_object* v_x_3576_){
_start:
{
lean_object* v___x_3577_; 
v___x_3577_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3575_, v_x_3576_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_3578_, lean_object* v_00_u03b2_3579_, lean_object* v_x_3580_, lean_object* v_x_3581_){
_start:
{
lean_object* v_res_3582_; 
v_res_3582_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(v_00_u03b1_3578_, v_00_u03b2_3579_, v_x_3580_, v_x_3581_);
lean_dec(v_x_3580_);
return v_res_3582_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3584_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_3585_ = lean_unsigned_to_nat(16u);
v___x_3586_ = lean_unsigned_to_nat(870u);
v___x_3587_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0));
v___x_3588_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3589_ = l_mkPanicMessageWithDecl(v___x_3588_, v___x_3587_, v___x_3586_, v___x_3585_, v___x_3584_);
return v___x_3589_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object* v_inst_3590_, lean_object* v_x_3591_, lean_object* v_x_3592_){
_start:
{
if (lean_obj_tag(v_x_3591_) == 0)
{
lean_object* v_k_3593_; lean_object* v_v_3594_; lean_object* v_l_3595_; lean_object* v_r_3596_; lean_object* v___y_3598_; lean_object* v___y_3604_; 
v_k_3593_ = lean_ctor_get(v_x_3591_, 1);
v_v_3594_ = lean_ctor_get(v_x_3591_, 2);
v_l_3595_ = lean_ctor_get(v_x_3591_, 3);
v_r_3596_ = lean_ctor_get(v_x_3591_, 4);
if (lean_obj_tag(v_l_3595_) == 0)
{
lean_object* v_size_3611_; 
v_size_3611_ = lean_ctor_get(v_l_3595_, 0);
v___y_3604_ = v_size_3611_;
goto v___jp_3603_;
}
else
{
lean_object* v___x_3612_; 
v___x_3612_ = lean_unsigned_to_nat(0u);
v___y_3604_ = v___x_3612_;
goto v___jp_3603_;
}
v___jp_3597_:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3599_ = lean_nat_sub(v_x_3592_, v___y_3598_);
lean_dec(v_x_3592_);
v___x_3600_ = lean_unsigned_to_nat(1u);
v___x_3601_ = lean_nat_sub(v___x_3599_, v___x_3600_);
lean_dec(v___x_3599_);
v_x_3591_ = v_r_3596_;
v_x_3592_ = v___x_3601_;
goto _start;
}
v___jp_3603_:
{
uint8_t v___x_3605_; 
v___x_3605_ = lean_nat_dec_lt(v_x_3592_, v___y_3604_);
if (v___x_3605_ == 0)
{
uint8_t v___x_3606_; 
v___x_3606_ = lean_nat_dec_eq(v_x_3592_, v___y_3604_);
if (v___x_3606_ == 0)
{
if (lean_obj_tag(v_l_3595_) == 0)
{
lean_object* v_size_3607_; 
v_size_3607_ = lean_ctor_get(v_l_3595_, 0);
v___y_3598_ = v_size_3607_;
goto v___jp_3597_;
}
else
{
lean_object* v___x_3608_; 
v___x_3608_ = lean_unsigned_to_nat(0u);
v___y_3598_ = v___x_3608_;
goto v___jp_3597_;
}
}
else
{
lean_object* v___x_3609_; 
lean_dec(v_x_3592_);
lean_dec_ref(v_inst_3590_);
lean_inc(v_v_3594_);
lean_inc(v_k_3593_);
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v_k_3593_);
lean_ctor_set(v___x_3609_, 1, v_v_3594_);
return v___x_3609_;
}
}
else
{
v_x_3591_ = v_l_3595_;
goto _start;
}
}
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3614_; 
lean_dec(v_x_3592_);
v___x_3613_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1);
v___x_3614_ = l_panic___redArg(v_inst_3590_, v___x_3613_);
return v___x_3614_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_3615_, lean_object* v_x_3616_, lean_object* v_x_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3615_, v_x_3616_, v_x_3617_);
lean_dec(v_x_3616_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(lean_object* v_00_u03b1_3619_, lean_object* v_00_u03b2_3620_, lean_object* v_inst_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3621_, v_x_3622_, v_x_3623_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_3625_, lean_object* v_00_u03b2_3626_, lean_object* v_inst_3627_, lean_object* v_x_3628_, lean_object* v_x_3629_){
_start:
{
lean_object* v_res_3630_; 
v_res_3630_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(v_00_u03b1_3625_, v_00_u03b2_3626_, v_inst_3627_, v_x_3628_, v_x_3629_);
lean_dec(v_x_3628_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object* v_x_3631_, lean_object* v_x_3632_, lean_object* v_x_3633_){
_start:
{
if (lean_obj_tag(v_x_3631_) == 0)
{
lean_object* v_k_3634_; lean_object* v_v_3635_; lean_object* v_l_3636_; lean_object* v_r_3637_; lean_object* v___y_3639_; lean_object* v___y_3645_; 
v_k_3634_ = lean_ctor_get(v_x_3631_, 1);
v_v_3635_ = lean_ctor_get(v_x_3631_, 2);
v_l_3636_ = lean_ctor_get(v_x_3631_, 3);
v_r_3637_ = lean_ctor_get(v_x_3631_, 4);
if (lean_obj_tag(v_l_3636_) == 0)
{
lean_object* v_size_3652_; 
v_size_3652_ = lean_ctor_get(v_l_3636_, 0);
v___y_3645_ = v_size_3652_;
goto v___jp_3644_;
}
else
{
lean_object* v___x_3653_; 
v___x_3653_ = lean_unsigned_to_nat(0u);
v___y_3645_ = v___x_3653_;
goto v___jp_3644_;
}
v___jp_3638_:
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3640_ = lean_nat_sub(v_x_3632_, v___y_3639_);
lean_dec(v_x_3632_);
v___x_3641_ = lean_unsigned_to_nat(1u);
v___x_3642_ = lean_nat_sub(v___x_3640_, v___x_3641_);
lean_dec(v___x_3640_);
v_x_3631_ = v_r_3637_;
v_x_3632_ = v___x_3642_;
goto _start;
}
v___jp_3644_:
{
uint8_t v___x_3646_; 
v___x_3646_ = lean_nat_dec_lt(v_x_3632_, v___y_3645_);
if (v___x_3646_ == 0)
{
uint8_t v___x_3647_; 
v___x_3647_ = lean_nat_dec_eq(v_x_3632_, v___y_3645_);
if (v___x_3647_ == 0)
{
if (lean_obj_tag(v_l_3636_) == 0)
{
lean_object* v_size_3648_; 
v_size_3648_ = lean_ctor_get(v_l_3636_, 0);
v___y_3639_ = v_size_3648_;
goto v___jp_3638_;
}
else
{
lean_object* v___x_3649_; 
v___x_3649_ = lean_unsigned_to_nat(0u);
v___y_3639_ = v___x_3649_;
goto v___jp_3638_;
}
}
else
{
lean_object* v___x_3650_; 
lean_dec(v_x_3632_);
lean_inc(v_v_3635_);
lean_inc(v_k_3634_);
v___x_3650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3650_, 0, v_k_3634_);
lean_ctor_set(v___x_3650_, 1, v_v_3635_);
return v___x_3650_;
}
}
else
{
v_x_3631_ = v_l_3636_;
goto _start;
}
}
}
else
{
lean_dec(v_x_3632_);
lean_inc_ref(v_x_3633_);
return v_x_3633_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg___boxed(lean_object* v_x_3654_, lean_object* v_x_3655_, lean_object* v_x_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3654_, v_x_3655_, v_x_3656_);
lean_dec_ref(v_x_3656_);
lean_dec(v_x_3654_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(lean_object* v_00_u03b1_3658_, lean_object* v_00_u03b2_3659_, lean_object* v_x_3660_, lean_object* v_x_3661_, lean_object* v_x_3662_){
_start:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3660_, v_x_3661_, v_x_3662_);
return v___x_3663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_3664_, lean_object* v_00_u03b2_3665_, lean_object* v_x_3666_, lean_object* v_x_3667_, lean_object* v_x_3668_){
_start:
{
lean_object* v_res_3669_; 
v_res_3669_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(v_00_u03b1_3664_, v_00_u03b2_3665_, v_x_3666_, v_x_3667_, v_x_3668_);
lean_dec_ref(v_x_3668_);
lean_dec(v_x_3666_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object* v_inst_3670_, lean_object* v_k_3671_, lean_object* v_best_3672_, lean_object* v_a_3673_){
_start:
{
if (lean_obj_tag(v_a_3673_) == 0)
{
lean_object* v_k_3674_; lean_object* v_v_3675_; lean_object* v_l_3676_; lean_object* v_r_3677_; lean_object* v___x_3678_; uint8_t v___x_3679_; 
v_k_3674_ = lean_ctor_get(v_a_3673_, 1);
lean_inc(v_k_3674_);
v_v_3675_ = lean_ctor_get(v_a_3673_, 2);
lean_inc(v_v_3675_);
v_l_3676_ = lean_ctor_get(v_a_3673_, 3);
lean_inc(v_l_3676_);
v_r_3677_ = lean_ctor_get(v_a_3673_, 4);
lean_inc(v_r_3677_);
lean_dec_ref(v_a_3673_);
lean_inc_ref(v_inst_3670_);
lean_inc(v_k_3674_);
lean_inc(v_k_3671_);
v___x_3678_ = lean_apply_2(v_inst_3670_, v_k_3671_, v_k_3674_);
v___x_3679_ = lean_unbox(v___x_3678_);
switch(v___x_3679_)
{
case 0:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; 
lean_dec(v_r_3677_);
lean_dec(v_best_3672_);
v___x_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3680_, 0, v_k_3674_);
lean_ctor_set(v___x_3680_, 1, v_v_3675_);
v___x_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3680_);
v_best_3672_ = v___x_3681_;
v_a_3673_ = v_l_3676_;
goto _start;
}
case 1:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
lean_dec(v_r_3677_);
lean_dec(v_l_3676_);
lean_dec(v_best_3672_);
lean_dec(v_k_3671_);
lean_dec_ref(v_inst_3670_);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v_k_3674_);
lean_ctor_set(v___x_3683_, 1, v_v_3675_);
v___x_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3683_);
return v___x_3684_;
}
default: 
{
lean_dec(v_l_3676_);
lean_dec(v_v_3675_);
lean_dec(v_k_3674_);
v_a_3673_ = v_r_3677_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3671_);
lean_dec_ref(v_inst_3670_);
return v_best_3672_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(lean_object* v_00_u03b1_3686_, lean_object* v_00_u03b2_3687_, lean_object* v_inst_3688_, lean_object* v_k_3689_, lean_object* v_best_3690_, lean_object* v_a_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3688_, v_k_3689_, v_best_3690_, v_a_3691_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___redArg(lean_object* v_inst_3693_, lean_object* v_k_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3696_ = lean_box(0);
v___x_3697_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3693_, v_k_3694_, v___x_3696_, v_a_3695_);
return v___x_3697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(lean_object* v_00_u03b1_3698_, lean_object* v_00_u03b2_3699_, lean_object* v_inst_3700_, lean_object* v_k_3701_, lean_object* v_a_3702_){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = lean_box(0);
v___x_3704_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3700_, v_k_3701_, v___x_3703_, v_a_3702_);
return v___x_3704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object* v_inst_3705_, lean_object* v_k_3706_, lean_object* v_best_3707_, lean_object* v_a_3708_){
_start:
{
if (lean_obj_tag(v_a_3708_) == 0)
{
lean_object* v_k_3709_; lean_object* v_v_3710_; lean_object* v_l_3711_; lean_object* v_r_3712_; lean_object* v___x_3713_; uint8_t v___x_3714_; 
v_k_3709_ = lean_ctor_get(v_a_3708_, 1);
lean_inc(v_k_3709_);
v_v_3710_ = lean_ctor_get(v_a_3708_, 2);
lean_inc(v_v_3710_);
v_l_3711_ = lean_ctor_get(v_a_3708_, 3);
lean_inc(v_l_3711_);
v_r_3712_ = lean_ctor_get(v_a_3708_, 4);
lean_inc(v_r_3712_);
lean_dec_ref(v_a_3708_);
lean_inc_ref(v_inst_3705_);
lean_inc(v_k_3709_);
lean_inc(v_k_3706_);
v___x_3713_ = lean_apply_2(v_inst_3705_, v_k_3706_, v_k_3709_);
v___x_3714_ = lean_unbox(v___x_3713_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
lean_dec(v_r_3712_);
lean_dec(v_best_3707_);
v___x_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3715_, 0, v_k_3709_);
lean_ctor_set(v___x_3715_, 1, v_v_3710_);
v___x_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
v_best_3707_ = v___x_3716_;
v_a_3708_ = v_l_3711_;
goto _start;
}
else
{
lean_dec(v_l_3711_);
lean_dec(v_v_3710_);
lean_dec(v_k_3709_);
v_a_3708_ = v_r_3712_;
goto _start;
}
}
else
{
lean_dec(v_k_3706_);
lean_dec_ref(v_inst_3705_);
return v_best_3707_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(lean_object* v_00_u03b1_3719_, lean_object* v_00_u03b2_3720_, lean_object* v_inst_3721_, lean_object* v_k_3722_, lean_object* v_best_3723_, lean_object* v_a_3724_){
_start:
{
lean_object* v___x_3725_; 
v___x_3725_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3721_, v_k_3722_, v_best_3723_, v_a_3724_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___redArg(lean_object* v_inst_3726_, lean_object* v_k_3727_, lean_object* v_a_3728_){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3729_ = lean_box(0);
v___x_3730_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3726_, v_k_3727_, v___x_3729_, v_a_3728_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(lean_object* v_00_u03b1_3731_, lean_object* v_00_u03b2_3732_, lean_object* v_inst_3733_, lean_object* v_k_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = lean_box(0);
v___x_3737_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3733_, v_k_3734_, v___x_3736_, v_a_3735_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object* v_inst_3738_, lean_object* v_k_3739_, lean_object* v_best_3740_, lean_object* v_a_3741_){
_start:
{
if (lean_obj_tag(v_a_3741_) == 0)
{
lean_object* v_k_3742_; lean_object* v_v_3743_; lean_object* v_l_3744_; lean_object* v_r_3745_; lean_object* v___x_3746_; uint8_t v___x_3747_; 
v_k_3742_ = lean_ctor_get(v_a_3741_, 1);
lean_inc(v_k_3742_);
v_v_3743_ = lean_ctor_get(v_a_3741_, 2);
lean_inc(v_v_3743_);
v_l_3744_ = lean_ctor_get(v_a_3741_, 3);
lean_inc(v_l_3744_);
v_r_3745_ = lean_ctor_get(v_a_3741_, 4);
lean_inc(v_r_3745_);
lean_dec_ref(v_a_3741_);
lean_inc_ref(v_inst_3738_);
lean_inc(v_k_3742_);
lean_inc(v_k_3739_);
v___x_3746_ = lean_apply_2(v_inst_3738_, v_k_3739_, v_k_3742_);
v___x_3747_ = lean_unbox(v___x_3746_);
switch(v___x_3747_)
{
case 0:
{
lean_dec(v_r_3745_);
lean_dec(v_v_3743_);
lean_dec(v_k_3742_);
v_a_3741_ = v_l_3744_;
goto _start;
}
case 1:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_dec(v_r_3745_);
lean_dec(v_l_3744_);
lean_dec(v_best_3740_);
lean_dec(v_k_3739_);
lean_dec_ref(v_inst_3738_);
v___x_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3749_, 0, v_k_3742_);
lean_ctor_set(v___x_3749_, 1, v_v_3743_);
v___x_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
return v___x_3750_;
}
default: 
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_dec(v_l_3744_);
lean_dec(v_best_3740_);
v___x_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3751_, 0, v_k_3742_);
lean_ctor_set(v___x_3751_, 1, v_v_3743_);
v___x_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
v_best_3740_ = v___x_3752_;
v_a_3741_ = v_r_3745_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3739_);
lean_dec_ref(v_inst_3738_);
return v_best_3740_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(lean_object* v_00_u03b1_3754_, lean_object* v_00_u03b2_3755_, lean_object* v_inst_3756_, lean_object* v_k_3757_, lean_object* v_best_3758_, lean_object* v_a_3759_){
_start:
{
lean_object* v___x_3760_; 
v___x_3760_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3756_, v_k_3757_, v_best_3758_, v_a_3759_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___redArg(lean_object* v_inst_3761_, lean_object* v_k_3762_, lean_object* v_a_3763_){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = lean_box(0);
v___x_3765_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3761_, v_k_3762_, v___x_3764_, v_a_3763_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(lean_object* v_00_u03b1_3766_, lean_object* v_00_u03b2_3767_, lean_object* v_inst_3768_, lean_object* v_k_3769_, lean_object* v_a_3770_){
_start:
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
v___x_3771_ = lean_box(0);
v___x_3772_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3768_, v_k_3769_, v___x_3771_, v_a_3770_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object* v_inst_3773_, lean_object* v_k_3774_, lean_object* v_best_3775_, lean_object* v_a_3776_){
_start:
{
if (lean_obj_tag(v_a_3776_) == 0)
{
lean_object* v_k_3777_; lean_object* v_v_3778_; lean_object* v_l_3779_; lean_object* v_r_3780_; lean_object* v___x_3781_; uint8_t v___x_3782_; 
v_k_3777_ = lean_ctor_get(v_a_3776_, 1);
lean_inc(v_k_3777_);
v_v_3778_ = lean_ctor_get(v_a_3776_, 2);
lean_inc(v_v_3778_);
v_l_3779_ = lean_ctor_get(v_a_3776_, 3);
lean_inc(v_l_3779_);
v_r_3780_ = lean_ctor_get(v_a_3776_, 4);
lean_inc(v_r_3780_);
lean_dec_ref(v_a_3776_);
lean_inc_ref(v_inst_3773_);
lean_inc(v_k_3777_);
lean_inc(v_k_3774_);
v___x_3781_ = lean_apply_2(v_inst_3773_, v_k_3774_, v_k_3777_);
v___x_3782_ = lean_unbox(v___x_3781_);
if (v___x_3782_ == 2)
{
lean_object* v___x_3783_; lean_object* v___x_3784_; 
lean_dec(v_l_3779_);
lean_dec(v_best_3775_);
v___x_3783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3783_, 0, v_k_3777_);
lean_ctor_set(v___x_3783_, 1, v_v_3778_);
v___x_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3783_);
v_best_3775_ = v___x_3784_;
v_a_3776_ = v_r_3780_;
goto _start;
}
else
{
lean_dec(v_r_3780_);
lean_dec(v_v_3778_);
lean_dec(v_k_3777_);
v_a_3776_ = v_l_3779_;
goto _start;
}
}
else
{
lean_dec(v_k_3774_);
lean_dec_ref(v_inst_3773_);
return v_best_3775_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(lean_object* v_00_u03b1_3787_, lean_object* v_00_u03b2_3788_, lean_object* v_inst_3789_, lean_object* v_k_3790_, lean_object* v_best_3791_, lean_object* v_a_3792_){
_start:
{
lean_object* v___x_3793_; 
v___x_3793_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3789_, v_k_3790_, v_best_3791_, v_a_3792_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___redArg(lean_object* v_inst_3794_, lean_object* v_k_3795_, lean_object* v_a_3796_){
_start:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = lean_box(0);
v___x_3798_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3794_, v_k_3795_, v___x_3797_, v_a_3796_);
return v___x_3798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(lean_object* v_00_u03b1_3799_, lean_object* v_00_u03b2_3800_, lean_object* v_inst_3801_, lean_object* v_k_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; 
v___x_3804_ = lean_box(0);
v___x_3805_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3801_, v_k_3802_, v___x_3804_, v_a_3803_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(lean_object* v_inst_3806_, lean_object* v_inst_3807_, lean_object* v_k_3808_, lean_object* v_t_3809_){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
v___x_3810_ = lean_box(0);
v___x_3811_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3806_, v_k_3808_, v___x_3810_, v_t_3809_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
v___x_3812_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3813_ = l_panic___redArg(v_inst_3807_, v___x_3812_);
return v___x_3813_;
}
else
{
lean_object* v_val_3814_; 
lean_dec_ref(v_inst_3807_);
v_val_3814_ = lean_ctor_get(v___x_3811_, 0);
lean_inc(v_val_3814_);
lean_dec_ref(v___x_3811_);
return v_val_3814_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object* v_00_u03b1_3815_, lean_object* v_00_u03b2_3816_, lean_object* v_inst_3817_, lean_object* v_inst_3818_, lean_object* v_k_3819_, lean_object* v_t_3820_){
_start:
{
lean_object* v___x_3821_; lean_object* v___x_3822_; 
v___x_3821_ = lean_box(0);
v___x_3822_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3817_, v_k_3819_, v___x_3821_, v_t_3820_);
if (lean_obj_tag(v___x_3822_) == 0)
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3824_ = l_panic___redArg(v_inst_3818_, v___x_3823_);
return v___x_3824_;
}
else
{
lean_object* v_val_3825_; 
lean_dec_ref(v_inst_3818_);
v_val_3825_ = lean_ctor_get(v___x_3822_, 0);
lean_inc(v_val_3825_);
lean_dec_ref(v___x_3822_);
return v_val_3825_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(lean_object* v_inst_3826_, lean_object* v_inst_3827_, lean_object* v_k_3828_, lean_object* v_t_3829_){
_start:
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
v___x_3830_ = lean_box(0);
v___x_3831_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3826_, v_k_3828_, v___x_3830_, v_t_3829_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3832_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3833_ = l_panic___redArg(v_inst_3827_, v___x_3832_);
return v___x_3833_;
}
else
{
lean_object* v_val_3834_; 
lean_dec_ref(v_inst_3827_);
v_val_3834_ = lean_ctor_get(v___x_3831_, 0);
lean_inc(v_val_3834_);
lean_dec_ref(v___x_3831_);
return v_val_3834_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object* v_00_u03b1_3835_, lean_object* v_00_u03b2_3836_, lean_object* v_inst_3837_, lean_object* v_inst_3838_, lean_object* v_k_3839_, lean_object* v_t_3840_){
_start:
{
lean_object* v___x_3841_; lean_object* v___x_3842_; 
v___x_3841_ = lean_box(0);
v___x_3842_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3837_, v_k_3839_, v___x_3841_, v_t_3840_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3844_ = l_panic___redArg(v_inst_3838_, v___x_3843_);
return v___x_3844_;
}
else
{
lean_object* v_val_3845_; 
lean_dec_ref(v_inst_3838_);
v_val_3845_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_val_3845_);
lean_dec_ref(v___x_3842_);
return v_val_3845_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(lean_object* v_inst_3846_, lean_object* v_inst_3847_, lean_object* v_k_3848_, lean_object* v_t_3849_){
_start:
{
lean_object* v___x_3850_; lean_object* v___x_3851_; 
v___x_3850_ = lean_box(0);
v___x_3851_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3846_, v_k_3848_, v___x_3850_, v_t_3849_);
if (lean_obj_tag(v___x_3851_) == 0)
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3853_ = l_panic___redArg(v_inst_3847_, v___x_3852_);
return v___x_3853_;
}
else
{
lean_object* v_val_3854_; 
lean_dec_ref(v_inst_3847_);
v_val_3854_ = lean_ctor_get(v___x_3851_, 0);
lean_inc(v_val_3854_);
lean_dec_ref(v___x_3851_);
return v_val_3854_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object* v_00_u03b1_3855_, lean_object* v_00_u03b2_3856_, lean_object* v_inst_3857_, lean_object* v_inst_3858_, lean_object* v_k_3859_, lean_object* v_t_3860_){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_box(0);
v___x_3862_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3857_, v_k_3859_, v___x_3861_, v_t_3860_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3863_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3864_ = l_panic___redArg(v_inst_3858_, v___x_3863_);
return v___x_3864_;
}
else
{
lean_object* v_val_3865_; 
lean_dec_ref(v_inst_3858_);
v_val_3865_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_val_3865_);
lean_dec_ref(v___x_3862_);
return v_val_3865_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(lean_object* v_inst_3866_, lean_object* v_inst_3867_, lean_object* v_k_3868_, lean_object* v_t_3869_){
_start:
{
lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3870_ = lean_box(0);
v___x_3871_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3866_, v_k_3868_, v___x_3870_, v_t_3869_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
v___x_3872_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3873_ = l_panic___redArg(v_inst_3867_, v___x_3872_);
return v___x_3873_;
}
else
{
lean_object* v_val_3874_; 
lean_dec_ref(v_inst_3867_);
v_val_3874_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_val_3874_);
lean_dec_ref(v___x_3871_);
return v_val_3874_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object* v_00_u03b1_3875_, lean_object* v_00_u03b2_3876_, lean_object* v_inst_3877_, lean_object* v_inst_3878_, lean_object* v_k_3879_, lean_object* v_t_3880_){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = lean_box(0);
v___x_3882_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3877_, v_k_3879_, v___x_3881_, v_t_3880_);
if (lean_obj_tag(v___x_3882_) == 0)
{
lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3883_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3884_ = l_panic___redArg(v_inst_3878_, v___x_3883_);
return v___x_3884_;
}
else
{
lean_object* v_val_3885_; 
lean_dec_ref(v_inst_3878_);
v_val_3885_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_val_3885_);
lean_dec_ref(v___x_3882_);
return v_val_3885_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(lean_object* v_inst_3886_, lean_object* v_k_3887_, lean_object* v_t_3888_, lean_object* v_fallback_3889_){
_start:
{
lean_object* v___x_3890_; lean_object* v___x_3891_; 
v___x_3890_ = lean_box(0);
v___x_3891_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3886_, v_k_3887_, v___x_3890_, v_t_3888_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_inc_ref(v_fallback_3889_);
return v_fallback_3889_;
}
else
{
lean_object* v_val_3892_; 
v_val_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_val_3892_);
lean_dec_ref(v___x_3891_);
return v_val_3892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg___boxed(lean_object* v_inst_3893_, lean_object* v_k_3894_, lean_object* v_t_3895_, lean_object* v_fallback_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(v_inst_3893_, v_k_3894_, v_t_3895_, v_fallback_3896_);
lean_dec_ref(v_fallback_3896_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(lean_object* v_00_u03b1_3898_, lean_object* v_00_u03b2_3899_, lean_object* v_inst_3900_, lean_object* v_k_3901_, lean_object* v_t_3902_, lean_object* v_fallback_3903_){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_box(0);
v___x_3905_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3900_, v_k_3901_, v___x_3904_, v_t_3902_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_inc_ref(v_fallback_3903_);
return v_fallback_3903_;
}
else
{
lean_object* v_val_3906_; 
v_val_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_val_3906_);
lean_dec_ref(v___x_3905_);
return v_val_3906_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___boxed(lean_object* v_00_u03b1_3907_, lean_object* v_00_u03b2_3908_, lean_object* v_inst_3909_, lean_object* v_k_3910_, lean_object* v_t_3911_, lean_object* v_fallback_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(v_00_u03b1_3907_, v_00_u03b2_3908_, v_inst_3909_, v_k_3910_, v_t_3911_, v_fallback_3912_);
lean_dec_ref(v_fallback_3912_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(lean_object* v_inst_3914_, lean_object* v_k_3915_, lean_object* v_t_3916_, lean_object* v_fallback_3917_){
_start:
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
v___x_3918_ = lean_box(0);
v___x_3919_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3914_, v_k_3915_, v___x_3918_, v_t_3916_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_inc_ref(v_fallback_3917_);
return v_fallback_3917_;
}
else
{
lean_object* v_val_3920_; 
v_val_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_val_3920_);
lean_dec_ref(v___x_3919_);
return v_val_3920_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg___boxed(lean_object* v_inst_3921_, lean_object* v_k_3922_, lean_object* v_t_3923_, lean_object* v_fallback_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(v_inst_3921_, v_k_3922_, v_t_3923_, v_fallback_3924_);
lean_dec_ref(v_fallback_3924_);
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(lean_object* v_00_u03b1_3926_, lean_object* v_00_u03b2_3927_, lean_object* v_inst_3928_, lean_object* v_k_3929_, lean_object* v_t_3930_, lean_object* v_fallback_3931_){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3932_ = lean_box(0);
v___x_3933_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3928_, v_k_3929_, v___x_3932_, v_t_3930_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_inc_ref(v_fallback_3931_);
return v_fallback_3931_;
}
else
{
lean_object* v_val_3934_; 
v_val_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_val_3934_);
lean_dec_ref(v___x_3933_);
return v_val_3934_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_3935_, lean_object* v_00_u03b2_3936_, lean_object* v_inst_3937_, lean_object* v_k_3938_, lean_object* v_t_3939_, lean_object* v_fallback_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(v_00_u03b1_3935_, v_00_u03b2_3936_, v_inst_3937_, v_k_3938_, v_t_3939_, v_fallback_3940_);
lean_dec_ref(v_fallback_3940_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(lean_object* v_inst_3942_, lean_object* v_k_3943_, lean_object* v_t_3944_, lean_object* v_fallback_3945_){
_start:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3946_ = lean_box(0);
v___x_3947_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3942_, v_k_3943_, v___x_3946_, v_t_3944_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_inc_ref(v_fallback_3945_);
return v_fallback_3945_;
}
else
{
lean_object* v_val_3948_; 
v_val_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_val_3948_);
lean_dec_ref(v___x_3947_);
return v_val_3948_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg___boxed(lean_object* v_inst_3949_, lean_object* v_k_3950_, lean_object* v_t_3951_, lean_object* v_fallback_3952_){
_start:
{
lean_object* v_res_3953_; 
v_res_3953_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(v_inst_3949_, v_k_3950_, v_t_3951_, v_fallback_3952_);
lean_dec_ref(v_fallback_3952_);
return v_res_3953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(lean_object* v_00_u03b1_3954_, lean_object* v_00_u03b2_3955_, lean_object* v_inst_3956_, lean_object* v_k_3957_, lean_object* v_t_3958_, lean_object* v_fallback_3959_){
_start:
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = lean_box(0);
v___x_3961_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3956_, v_k_3957_, v___x_3960_, v_t_3958_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_inc_ref(v_fallback_3959_);
return v_fallback_3959_;
}
else
{
lean_object* v_val_3962_; 
v_val_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_val_3962_);
lean_dec_ref(v___x_3961_);
return v_val_3962_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___boxed(lean_object* v_00_u03b1_3963_, lean_object* v_00_u03b2_3964_, lean_object* v_inst_3965_, lean_object* v_k_3966_, lean_object* v_t_3967_, lean_object* v_fallback_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(v_00_u03b1_3963_, v_00_u03b2_3964_, v_inst_3965_, v_k_3966_, v_t_3967_, v_fallback_3968_);
lean_dec_ref(v_fallback_3968_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(lean_object* v_inst_3970_, lean_object* v_k_3971_, lean_object* v_t_3972_, lean_object* v_fallback_3973_){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = lean_box(0);
v___x_3975_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3970_, v_k_3971_, v___x_3974_, v_t_3972_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_inc_ref(v_fallback_3973_);
return v_fallback_3973_;
}
else
{
lean_object* v_val_3976_; 
v_val_3976_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_val_3976_);
lean_dec_ref(v___x_3975_);
return v_val_3976_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg___boxed(lean_object* v_inst_3977_, lean_object* v_k_3978_, lean_object* v_t_3979_, lean_object* v_fallback_3980_){
_start:
{
lean_object* v_res_3981_; 
v_res_3981_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(v_inst_3977_, v_k_3978_, v_t_3979_, v_fallback_3980_);
lean_dec_ref(v_fallback_3980_);
return v_res_3981_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(lean_object* v_00_u03b1_3982_, lean_object* v_00_u03b2_3983_, lean_object* v_inst_3984_, lean_object* v_k_3985_, lean_object* v_t_3986_, lean_object* v_fallback_3987_){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_box(0);
v___x_3989_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3984_, v_k_3985_, v___x_3988_, v_t_3986_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_inc_ref(v_fallback_3987_);
return v_fallback_3987_;
}
else
{
lean_object* v_val_3990_; 
v_val_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_val_3990_);
lean_dec_ref(v___x_3989_);
return v_val_3990_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_3991_, lean_object* v_00_u03b2_3992_, lean_object* v_inst_3993_, lean_object* v_k_3994_, lean_object* v_t_3995_, lean_object* v_fallback_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(v_00_u03b1_3991_, v_00_u03b2_3992_, v_inst_3993_, v_k_3994_, v_t_3995_, v_fallback_3996_);
lean_dec_ref(v_fallback_3996_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object* v_inst_3998_, lean_object* v_k_3999_, lean_object* v_x_4000_){
_start:
{
lean_object* v_k_4001_; lean_object* v_v_4002_; lean_object* v_l_4003_; lean_object* v_r_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; 
v_k_4001_ = lean_ctor_get(v_x_4000_, 1);
lean_inc(v_k_4001_);
v_v_4002_ = lean_ctor_get(v_x_4000_, 2);
lean_inc(v_v_4002_);
v_l_4003_ = lean_ctor_get(v_x_4000_, 3);
lean_inc(v_l_4003_);
v_r_4004_ = lean_ctor_get(v_x_4000_, 4);
lean_inc(v_r_4004_);
lean_dec(v_x_4000_);
lean_inc_ref(v_inst_3998_);
lean_inc(v_k_4001_);
lean_inc(v_k_3999_);
v___x_4005_ = lean_apply_2(v_inst_3998_, v_k_3999_, v_k_4001_);
v___x_4006_ = lean_unbox(v___x_4005_);
switch(v___x_4006_)
{
case 0:
{
lean_object* v___x_4007_; lean_object* v___x_4008_; 
lean_dec(v_r_4004_);
v___x_4007_ = lean_box(0);
v___x_4008_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3998_, v_k_3999_, v___x_4007_, v_l_4003_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v___x_4009_; 
v___x_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4009_, 0, v_k_4001_);
lean_ctor_set(v___x_4009_, 1, v_v_4002_);
return v___x_4009_;
}
else
{
lean_object* v_val_4010_; 
lean_dec(v_v_4002_);
lean_dec(v_k_4001_);
v_val_4010_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_val_4010_);
lean_dec_ref(v___x_4008_);
return v_val_4010_;
}
}
case 1:
{
lean_object* v___x_4011_; 
lean_dec(v_r_4004_);
lean_dec(v_l_4003_);
lean_dec(v_k_3999_);
lean_dec_ref(v_inst_3998_);
v___x_4011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4011_, 0, v_k_4001_);
lean_ctor_set(v___x_4011_, 1, v_v_4002_);
return v___x_4011_;
}
default: 
{
lean_dec(v_l_4003_);
lean_dec(v_v_4002_);
lean_dec(v_k_4001_);
v_x_4000_ = v_r_4004_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(lean_object* v_00_u03b1_4013_, lean_object* v_00_u03b2_4014_, lean_object* v_inst_4015_, lean_object* v_inst_4016_, lean_object* v_k_4017_, lean_object* v_x_4018_, lean_object* v_x_4019_, lean_object* v_x_4020_){
_start:
{
lean_object* v___x_4021_; 
v___x_4021_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_inst_4015_, v_k_4017_, v_x_4018_);
return v___x_4021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object* v_inst_4022_, lean_object* v_k_4023_, lean_object* v_x_4024_){
_start:
{
lean_object* v_k_4025_; lean_object* v_v_4026_; lean_object* v_l_4027_; lean_object* v_r_4028_; lean_object* v___x_4029_; uint8_t v___x_4030_; uint8_t v___x_4031_; uint8_t v___x_4032_; 
v_k_4025_ = lean_ctor_get(v_x_4024_, 1);
lean_inc(v_k_4025_);
v_v_4026_ = lean_ctor_get(v_x_4024_, 2);
lean_inc(v_v_4026_);
v_l_4027_ = lean_ctor_get(v_x_4024_, 3);
lean_inc(v_l_4027_);
v_r_4028_ = lean_ctor_get(v_x_4024_, 4);
lean_inc(v_r_4028_);
lean_dec(v_x_4024_);
lean_inc_ref(v_inst_4022_);
lean_inc(v_k_4025_);
lean_inc(v_k_4023_);
v___x_4029_ = lean_apply_2(v_inst_4022_, v_k_4023_, v_k_4025_);
v___x_4030_ = 0;
v___x_4031_ = lean_unbox(v___x_4029_);
v___x_4032_ = l_instDecidableEqOrdering(v___x_4031_, v___x_4030_);
if (v___x_4032_ == 0)
{
lean_dec(v_l_4027_);
lean_dec(v_v_4026_);
lean_dec(v_k_4025_);
v_x_4024_ = v_r_4028_;
goto _start;
}
else
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
lean_dec(v_r_4028_);
v___x_4034_ = lean_box(0);
v___x_4035_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4022_, v_k_4023_, v___x_4034_, v_l_4027_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v___x_4036_; 
v___x_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4036_, 0, v_k_4025_);
lean_ctor_set(v___x_4036_, 1, v_v_4026_);
return v___x_4036_;
}
else
{
lean_object* v_val_4037_; 
lean_dec(v_v_4026_);
lean_dec(v_k_4025_);
v_val_4037_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_val_4037_);
lean_dec_ref(v___x_4035_);
return v_val_4037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(lean_object* v_00_u03b1_4038_, lean_object* v_00_u03b2_4039_, lean_object* v_inst_4040_, lean_object* v_inst_4041_, lean_object* v_k_4042_, lean_object* v_x_4043_, lean_object* v_x_4044_, lean_object* v_x_4045_){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_inst_4040_, v_k_4042_, v_x_4043_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object* v_inst_4047_, lean_object* v_k_4048_, lean_object* v_x_4049_){
_start:
{
lean_object* v_k_4050_; lean_object* v_v_4051_; lean_object* v_l_4052_; lean_object* v_r_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; 
v_k_4050_ = lean_ctor_get(v_x_4049_, 1);
lean_inc(v_k_4050_);
v_v_4051_ = lean_ctor_get(v_x_4049_, 2);
lean_inc(v_v_4051_);
v_l_4052_ = lean_ctor_get(v_x_4049_, 3);
lean_inc(v_l_4052_);
v_r_4053_ = lean_ctor_get(v_x_4049_, 4);
lean_inc(v_r_4053_);
lean_dec(v_x_4049_);
lean_inc_ref(v_inst_4047_);
lean_inc(v_k_4050_);
lean_inc(v_k_4048_);
v___x_4054_ = lean_apply_2(v_inst_4047_, v_k_4048_, v_k_4050_);
v___x_4055_ = lean_unbox(v___x_4054_);
switch(v___x_4055_)
{
case 0:
{
lean_dec(v_r_4053_);
lean_dec(v_v_4051_);
lean_dec(v_k_4050_);
v_x_4049_ = v_l_4052_;
goto _start;
}
case 1:
{
lean_object* v___x_4057_; 
lean_dec(v_r_4053_);
lean_dec(v_l_4052_);
lean_dec(v_k_4048_);
lean_dec_ref(v_inst_4047_);
v___x_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4057_, 0, v_k_4050_);
lean_ctor_set(v___x_4057_, 1, v_v_4051_);
return v___x_4057_;
}
default: 
{
lean_object* v___x_4058_; lean_object* v___x_4059_; 
lean_dec(v_l_4052_);
v___x_4058_ = lean_box(0);
v___x_4059_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4047_, v_k_4048_, v___x_4058_, v_r_4053_);
if (lean_obj_tag(v___x_4059_) == 0)
{
lean_object* v___x_4060_; 
v___x_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4060_, 0, v_k_4050_);
lean_ctor_set(v___x_4060_, 1, v_v_4051_);
return v___x_4060_;
}
else
{
lean_object* v_val_4061_; 
lean_dec(v_v_4051_);
lean_dec(v_k_4050_);
v_val_4061_ = lean_ctor_get(v___x_4059_, 0);
lean_inc(v_val_4061_);
lean_dec_ref(v___x_4059_);
return v_val_4061_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(lean_object* v_00_u03b1_4062_, lean_object* v_00_u03b2_4063_, lean_object* v_inst_4064_, lean_object* v_inst_4065_, lean_object* v_k_4066_, lean_object* v_x_4067_, lean_object* v_x_4068_, lean_object* v_x_4069_){
_start:
{
lean_object* v___x_4070_; 
v___x_4070_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_inst_4064_, v_k_4066_, v_x_4067_);
return v___x_4070_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object* v_inst_4071_, lean_object* v_k_4072_, lean_object* v_x_4073_){
_start:
{
lean_object* v_k_4074_; lean_object* v_v_4075_; lean_object* v_l_4076_; lean_object* v_r_4077_; lean_object* v___x_4078_; uint8_t v___x_4079_; uint8_t v___x_4080_; uint8_t v___x_4081_; 
v_k_4074_ = lean_ctor_get(v_x_4073_, 1);
lean_inc(v_k_4074_);
v_v_4075_ = lean_ctor_get(v_x_4073_, 2);
lean_inc(v_v_4075_);
v_l_4076_ = lean_ctor_get(v_x_4073_, 3);
lean_inc(v_l_4076_);
v_r_4077_ = lean_ctor_get(v_x_4073_, 4);
lean_inc(v_r_4077_);
lean_dec(v_x_4073_);
lean_inc_ref(v_inst_4071_);
lean_inc(v_k_4074_);
lean_inc(v_k_4072_);
v___x_4078_ = lean_apply_2(v_inst_4071_, v_k_4072_, v_k_4074_);
v___x_4079_ = 2;
v___x_4080_ = lean_unbox(v___x_4078_);
v___x_4081_ = l_instDecidableEqOrdering(v___x_4080_, v___x_4079_);
if (v___x_4081_ == 0)
{
lean_dec(v_r_4077_);
lean_dec(v_v_4075_);
lean_dec(v_k_4074_);
v_x_4073_ = v_l_4076_;
goto _start;
}
else
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
lean_dec(v_l_4076_);
v___x_4083_ = lean_box(0);
v___x_4084_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4071_, v_k_4072_, v___x_4083_, v_r_4077_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v___x_4085_; 
v___x_4085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4085_, 0, v_k_4074_);
lean_ctor_set(v___x_4085_, 1, v_v_4075_);
return v___x_4085_;
}
else
{
lean_object* v_val_4086_; 
lean_dec(v_v_4075_);
lean_dec(v_k_4074_);
v_val_4086_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_val_4086_);
lean_dec_ref(v___x_4084_);
return v_val_4086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(lean_object* v_00_u03b1_4087_, lean_object* v_00_u03b2_4088_, lean_object* v_inst_4089_, lean_object* v_inst_4090_, lean_object* v_k_4091_, lean_object* v_x_4092_, lean_object* v_x_4093_, lean_object* v_x_4094_){
_start:
{
lean_object* v___x_4095_; 
v___x_4095_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_inst_4089_, v_k_4091_, v_x_4092_);
return v___x_4095_;
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
