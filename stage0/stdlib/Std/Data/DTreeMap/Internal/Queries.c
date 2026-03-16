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
lean_object* v___x_209_; 
v___x_209_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(v_t_206_, v_h__1_207_, v_h__2_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t v_x_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_, lean_object* v_h__3_213_){
_start:
{
switch(v_x_210_)
{
case 0:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_h__3_213_);
lean_dec(v_h__2_212_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_apply_1(v_h__1_211_, v___x_214_);
return v___x_215_;
}
case 1:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
lean_dec(v_h__2_212_);
lean_dec(v_h__1_211_);
v___x_216_ = lean_box(0);
v___x_217_ = lean_apply_1(v_h__3_213_, v___x_216_);
return v___x_217_;
}
default: 
{
lean_object* v___x_218_; lean_object* v___x_219_; 
lean_dec(v_h__3_213_);
lean_dec(v_h__1_211_);
v___x_218_ = lean_box(0);
v___x_219_ = lean_apply_1(v_h__2_212_, v___x_218_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_, lean_object* v_h__3_223_){
_start:
{
uint8_t v_x_30__boxed_224_; lean_object* v_res_225_; 
v_x_30__boxed_224_ = lean_unbox(v_x_220_);
v_res_225_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_30__boxed_224_, v_h__1_221_, v_h__2_222_, v_h__3_223_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* v_motive_226_, uint8_t v_x_227_, lean_object* v_h__1_228_, lean_object* v_h__2_229_, lean_object* v_h__3_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_227_, v_h__1_228_, v_h__2_229_, v_h__3_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* v_motive_232_, lean_object* v_x_233_, lean_object* v_h__1_234_, lean_object* v_h__2_235_, lean_object* v_h__3_236_){
_start:
{
uint8_t v_x_45__boxed_237_; lean_object* v_res_238_; 
v_x_45__boxed_237_ = lean_unbox(v_x_233_);
v_res_238_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_232_, v_x_45__boxed_237_, v_h__1_234_, v_h__2_235_, v_h__3_236_);
return v_res_238_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(lean_object* v_t_239_){
_start:
{
if (lean_obj_tag(v_t_239_) == 0)
{
uint8_t v___x_240_; 
v___x_240_ = 0;
return v___x_240_;
}
else
{
uint8_t v___x_241_; 
v___x_241_ = 1;
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___redArg___boxed(lean_object* v_t_242_){
_start:
{
uint8_t v_res_243_; lean_object* v_r_244_; 
v_res_243_ = l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(v_t_242_);
lean_dec(v_t_242_);
v_r_244_ = lean_box(v_res_243_);
return v_r_244_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty(lean_object* v_00_u03b1_245_, lean_object* v_00_u03b2_246_, lean_object* v_t_247_){
_start:
{
if (lean_obj_tag(v_t_247_) == 0)
{
uint8_t v___x_248_; 
v___x_248_ = 0;
return v___x_248_;
}
else
{
uint8_t v___x_249_; 
v___x_249_ = 1;
return v___x_249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___boxed(lean_object* v_00_u03b1_250_, lean_object* v_00_u03b2_251_, lean_object* v_t_252_){
_start:
{
uint8_t v_res_253_; lean_object* v_r_254_; 
v_res_253_ = l_Std_DTreeMap_Internal_Impl_isEmpty(v_00_u03b1_250_, v_00_u03b2_251_, v_t_252_);
lean_dec(v_t_252_);
v_r_254_ = lean_box(v_res_253_);
return v_r_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object* v_inst_255_, lean_object* v_t_256_, lean_object* v_k_257_){
_start:
{
if (lean_obj_tag(v_t_256_) == 0)
{
lean_object* v_k_258_; lean_object* v_v_259_; lean_object* v_l_260_; lean_object* v_r_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v_k_258_ = lean_ctor_get(v_t_256_, 1);
lean_inc(v_k_258_);
v_v_259_ = lean_ctor_get(v_t_256_, 2);
lean_inc(v_v_259_);
v_l_260_ = lean_ctor_get(v_t_256_, 3);
lean_inc(v_l_260_);
v_r_261_ = lean_ctor_get(v_t_256_, 4);
lean_inc(v_r_261_);
lean_dec_ref(v_t_256_);
lean_inc_ref(v_inst_255_);
lean_inc(v_k_257_);
v___x_262_ = lean_apply_2(v_inst_255_, v_k_257_, v_k_258_);
v___x_263_ = lean_unbox(v___x_262_);
switch(v___x_263_)
{
case 0:
{
lean_dec(v_r_261_);
lean_dec(v_v_259_);
v_t_256_ = v_l_260_;
goto _start;
}
case 1:
{
lean_object* v___x_265_; 
lean_dec(v_r_261_);
lean_dec(v_l_260_);
lean_dec(v_k_257_);
lean_dec_ref(v_inst_255_);
v___x_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_265_, 0, v_v_259_);
return v___x_265_;
}
default: 
{
lean_dec(v_l_260_);
lean_dec(v_v_259_);
v_t_256_ = v_r_261_;
goto _start;
}
}
}
else
{
lean_object* v___x_267_; 
lean_dec(v_k_257_);
lean_dec_ref(v_inst_255_);
v___x_267_ = lean_box(0);
return v___x_267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f(lean_object* v_00_u03b1_268_, lean_object* v_00_u03b2_269_, lean_object* v_inst_270_, lean_object* v_inst_271_, lean_object* v_t_272_, lean_object* v_k_273_){
_start:
{
lean_object* v___x_274_; 
v___x_274_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_inst_270_, v_t_272_, v_k_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get___redArg(lean_object* v_inst_275_, lean_object* v_t_276_, lean_object* v_k_277_){
_start:
{
lean_object* v_k_278_; lean_object* v_v_279_; lean_object* v_l_280_; lean_object* v_r_281_; lean_object* v___x_282_; uint8_t v___x_283_; 
v_k_278_ = lean_ctor_get(v_t_276_, 1);
lean_inc(v_k_278_);
v_v_279_ = lean_ctor_get(v_t_276_, 2);
lean_inc(v_v_279_);
v_l_280_ = lean_ctor_get(v_t_276_, 3);
lean_inc(v_l_280_);
v_r_281_ = lean_ctor_get(v_t_276_, 4);
lean_inc(v_r_281_);
lean_dec(v_t_276_);
lean_inc_ref(v_inst_275_);
lean_inc(v_k_277_);
v___x_282_ = lean_apply_2(v_inst_275_, v_k_277_, v_k_278_);
v___x_283_ = lean_unbox(v___x_282_);
switch(v___x_283_)
{
case 0:
{
lean_dec(v_r_281_);
lean_dec(v_v_279_);
v_t_276_ = v_l_280_;
goto _start;
}
case 1:
{
lean_dec(v_r_281_);
lean_dec(v_l_280_);
lean_dec(v_k_277_);
lean_dec_ref(v_inst_275_);
return v_v_279_;
}
default: 
{
lean_dec(v_l_280_);
lean_dec(v_v_279_);
v_t_276_ = v_r_281_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get(lean_object* v_00_u03b1_286_, lean_object* v_00_u03b2_287_, lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_t_290_, lean_object* v_k_291_, lean_object* v_hlk_292_){
_start:
{
lean_object* v___x_293_; 
v___x_293_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_inst_288_, v_t_290_, v_k_291_);
return v___x_293_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_297_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_298_ = lean_unsigned_to_nat(13u);
v___x_299_ = lean_unsigned_to_nat(108u);
v___x_300_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1));
v___x_301_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_302_ = l_mkPanicMessageWithDecl(v___x_301_, v___x_300_, v___x_299_, v___x_298_, v___x_297_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object* v_inst_303_, lean_object* v_t_304_, lean_object* v_k_305_, lean_object* v_inst_306_){
_start:
{
if (lean_obj_tag(v_t_304_) == 0)
{
lean_object* v_k_307_; lean_object* v_v_308_; lean_object* v_l_309_; lean_object* v_r_310_; lean_object* v___x_311_; uint8_t v___x_312_; 
v_k_307_ = lean_ctor_get(v_t_304_, 1);
lean_inc(v_k_307_);
v_v_308_ = lean_ctor_get(v_t_304_, 2);
lean_inc(v_v_308_);
v_l_309_ = lean_ctor_get(v_t_304_, 3);
lean_inc(v_l_309_);
v_r_310_ = lean_ctor_get(v_t_304_, 4);
lean_inc(v_r_310_);
lean_dec_ref(v_t_304_);
lean_inc_ref(v_inst_303_);
lean_inc(v_k_305_);
v___x_311_ = lean_apply_2(v_inst_303_, v_k_305_, v_k_307_);
v___x_312_ = lean_unbox(v___x_311_);
switch(v___x_312_)
{
case 0:
{
lean_dec(v_r_310_);
lean_dec(v_v_308_);
v_t_304_ = v_l_309_;
goto _start;
}
case 1:
{
lean_dec(v_r_310_);
lean_dec(v_l_309_);
lean_dec(v_inst_306_);
lean_dec(v_k_305_);
lean_dec_ref(v_inst_303_);
return v_v_308_;
}
default: 
{
lean_dec(v_l_309_);
lean_dec(v_v_308_);
v_t_304_ = v_r_310_;
goto _start;
}
}
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; 
lean_dec(v_k_305_);
lean_dec_ref(v_inst_303_);
v___x_315_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3);
v___x_316_ = l_panic___redArg(v_inst_306_, v___x_315_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21(lean_object* v_00_u03b1_317_, lean_object* v_00_u03b2_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_t_321_, lean_object* v_k_322_, lean_object* v_inst_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_inst_319_, v_t_321_, v_k_322_, v_inst_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg(lean_object* v_inst_325_, lean_object* v_t_326_, lean_object* v_k_327_, lean_object* v_fallback_328_){
_start:
{
if (lean_obj_tag(v_t_326_) == 0)
{
lean_object* v_k_329_; lean_object* v_v_330_; lean_object* v_l_331_; lean_object* v_r_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v_k_329_ = lean_ctor_get(v_t_326_, 1);
lean_inc(v_k_329_);
v_v_330_ = lean_ctor_get(v_t_326_, 2);
lean_inc(v_v_330_);
v_l_331_ = lean_ctor_get(v_t_326_, 3);
lean_inc(v_l_331_);
v_r_332_ = lean_ctor_get(v_t_326_, 4);
lean_inc(v_r_332_);
lean_dec_ref(v_t_326_);
lean_inc_ref(v_inst_325_);
lean_inc(v_k_327_);
v___x_333_ = lean_apply_2(v_inst_325_, v_k_327_, v_k_329_);
v___x_334_ = lean_unbox(v___x_333_);
switch(v___x_334_)
{
case 0:
{
lean_dec(v_r_332_);
lean_dec(v_v_330_);
v_t_326_ = v_l_331_;
goto _start;
}
case 1:
{
lean_dec(v_r_332_);
lean_dec(v_l_331_);
lean_dec(v_k_327_);
lean_dec_ref(v_inst_325_);
return v_v_330_;
}
default: 
{
lean_dec(v_l_331_);
lean_dec(v_v_330_);
v_t_326_ = v_r_332_;
goto _start;
}
}
}
else
{
lean_dec(v_k_327_);
lean_dec_ref(v_inst_325_);
lean_inc(v_fallback_328_);
return v_fallback_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg___boxed(lean_object* v_inst_337_, lean_object* v_t_338_, lean_object* v_k_339_, lean_object* v_fallback_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_inst_337_, v_t_338_, v_k_339_, v_fallback_340_);
lean_dec(v_fallback_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD(lean_object* v_00_u03b1_342_, lean_object* v_00_u03b2_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v_t_346_, lean_object* v_k_347_, lean_object* v_fallback_348_){
_start:
{
lean_object* v___x_349_; 
v___x_349_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_inst_344_, v_t_346_, v_k_347_, v_fallback_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___boxed(lean_object* v_00_u03b1_350_, lean_object* v_00_u03b2_351_, lean_object* v_inst_352_, lean_object* v_inst_353_, lean_object* v_t_354_, lean_object* v_k_355_, lean_object* v_fallback_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_DTreeMap_Internal_Impl_getD(v_00_u03b1_350_, v_00_u03b2_351_, v_inst_352_, v_inst_353_, v_t_354_, v_k_355_, v_fallback_356_);
lean_dec(v_fallback_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(lean_object* v_inst_358_, lean_object* v_t_359_, lean_object* v_k_360_){
_start:
{
if (lean_obj_tag(v_t_359_) == 0)
{
lean_object* v_k_361_; lean_object* v_v_362_; lean_object* v_l_363_; lean_object* v_r_364_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_k_361_ = lean_ctor_get(v_t_359_, 1);
lean_inc(v_k_361_);
v_v_362_ = lean_ctor_get(v_t_359_, 2);
lean_inc(v_v_362_);
v_l_363_ = lean_ctor_get(v_t_359_, 3);
lean_inc(v_l_363_);
v_r_364_ = lean_ctor_get(v_t_359_, 4);
lean_inc(v_r_364_);
lean_dec_ref(v_t_359_);
lean_inc_ref(v_inst_358_);
lean_inc(v_k_361_);
lean_inc(v_k_360_);
v___x_365_ = lean_apply_2(v_inst_358_, v_k_360_, v_k_361_);
v___x_366_ = lean_unbox(v___x_365_);
switch(v___x_366_)
{
case 0:
{
lean_dec(v_r_364_);
lean_dec(v_v_362_);
lean_dec(v_k_361_);
v_t_359_ = v_l_363_;
goto _start;
}
case 1:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
lean_dec(v_r_364_);
lean_dec(v_l_363_);
lean_dec(v_k_360_);
lean_dec_ref(v_inst_358_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v_k_361_);
lean_ctor_set(v___x_368_, 1, v_v_362_);
v___x_369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
return v___x_369_;
}
default: 
{
lean_dec(v_l_363_);
lean_dec(v_v_362_);
lean_dec(v_k_361_);
v_t_359_ = v_r_364_;
goto _start;
}
}
}
else
{
lean_object* v___x_371_; 
lean_dec(v_k_360_);
lean_dec_ref(v_inst_358_);
v___x_371_ = lean_box(0);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_inst_374_, lean_object* v_t_375_, lean_object* v_k_376_){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_inst_374_, v_t_375_, v_k_376_);
return v___x_377_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry___redArg(lean_object* v_inst_378_, lean_object* v_t_379_, lean_object* v_k_380_){
_start:
{
lean_object* v_k_381_; lean_object* v_v_382_; lean_object* v_l_383_; lean_object* v_r_384_; lean_object* v___x_385_; uint8_t v___x_386_; 
v_k_381_ = lean_ctor_get(v_t_379_, 1);
lean_inc(v_k_381_);
v_v_382_ = lean_ctor_get(v_t_379_, 2);
lean_inc(v_v_382_);
v_l_383_ = lean_ctor_get(v_t_379_, 3);
lean_inc(v_l_383_);
v_r_384_ = lean_ctor_get(v_t_379_, 4);
lean_inc(v_r_384_);
lean_dec(v_t_379_);
lean_inc_ref(v_inst_378_);
lean_inc(v_k_381_);
lean_inc(v_k_380_);
v___x_385_ = lean_apply_2(v_inst_378_, v_k_380_, v_k_381_);
v___x_386_ = lean_unbox(v___x_385_);
switch(v___x_386_)
{
case 0:
{
lean_dec(v_r_384_);
lean_dec(v_v_382_);
lean_dec(v_k_381_);
v_t_379_ = v_l_383_;
goto _start;
}
case 1:
{
lean_object* v___x_388_; 
lean_dec(v_r_384_);
lean_dec(v_l_383_);
lean_dec(v_k_380_);
lean_dec_ref(v_inst_378_);
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_k_381_);
lean_ctor_set(v___x_388_, 1, v_v_382_);
return v___x_388_;
}
default: 
{
lean_dec(v_l_383_);
lean_dec(v_v_382_);
lean_dec(v_k_381_);
v_t_379_ = v_r_384_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry(lean_object* v_00_u03b1_390_, lean_object* v_00_u03b2_391_, lean_object* v_inst_392_, lean_object* v_t_393_, lean_object* v_k_394_, lean_object* v_hlk_395_){
_start:
{
lean_object* v___x_396_; 
v___x_396_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_inst_392_, v_t_393_, v_k_394_);
return v___x_396_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_398_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_399_ = lean_unsigned_to_nat(13u);
v___x_400_ = lean_unsigned_to_nat(147u);
v___x_401_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0));
v___x_402_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_403_ = l_mkPanicMessageWithDecl(v___x_402_, v___x_401_, v___x_400_, v___x_399_, v___x_398_);
return v___x_403_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_t_406_, lean_object* v_k_407_){
_start:
{
if (lean_obj_tag(v_t_406_) == 0)
{
lean_object* v_k_408_; lean_object* v_v_409_; lean_object* v_l_410_; lean_object* v_r_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
v_k_408_ = lean_ctor_get(v_t_406_, 1);
lean_inc(v_k_408_);
v_v_409_ = lean_ctor_get(v_t_406_, 2);
lean_inc(v_v_409_);
v_l_410_ = lean_ctor_get(v_t_406_, 3);
lean_inc(v_l_410_);
v_r_411_ = lean_ctor_get(v_t_406_, 4);
lean_inc(v_r_411_);
lean_dec_ref(v_t_406_);
lean_inc_ref(v_inst_404_);
lean_inc(v_k_408_);
lean_inc(v_k_407_);
v___x_412_ = lean_apply_2(v_inst_404_, v_k_407_, v_k_408_);
v___x_413_ = lean_unbox(v___x_412_);
switch(v___x_413_)
{
case 0:
{
lean_dec(v_r_411_);
lean_dec(v_v_409_);
lean_dec(v_k_408_);
v_t_406_ = v_l_410_;
goto _start;
}
case 1:
{
lean_object* v___x_415_; 
lean_dec(v_r_411_);
lean_dec(v_l_410_);
lean_dec(v_k_407_);
lean_dec_ref(v_inst_405_);
lean_dec_ref(v_inst_404_);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v_k_408_);
lean_ctor_set(v___x_415_, 1, v_v_409_);
return v___x_415_;
}
default: 
{
lean_dec(v_l_410_);
lean_dec(v_v_409_);
lean_dec(v_k_408_);
v_t_406_ = v_r_411_;
goto _start;
}
}
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec(v_k_407_);
lean_dec_ref(v_inst_404_);
v___x_417_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1);
v___x_418_ = l_panic___redArg(v_inst_405_, v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21(lean_object* v_00_u03b1_419_, lean_object* v_00_u03b2_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_t_423_, lean_object* v_k_424_){
_start:
{
lean_object* v___x_425_; 
v___x_425_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_inst_421_, v_inst_422_, v_t_423_, v_k_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(lean_object* v_inst_426_, lean_object* v_t_427_, lean_object* v_k_428_, lean_object* v_fallback_429_){
_start:
{
if (lean_obj_tag(v_t_427_) == 0)
{
lean_object* v_k_430_; lean_object* v_v_431_; lean_object* v_l_432_; lean_object* v_r_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_k_430_ = lean_ctor_get(v_t_427_, 1);
lean_inc(v_k_430_);
v_v_431_ = lean_ctor_get(v_t_427_, 2);
lean_inc(v_v_431_);
v_l_432_ = lean_ctor_get(v_t_427_, 3);
lean_inc(v_l_432_);
v_r_433_ = lean_ctor_get(v_t_427_, 4);
lean_inc(v_r_433_);
lean_dec_ref(v_t_427_);
lean_inc_ref(v_inst_426_);
lean_inc(v_k_430_);
lean_inc(v_k_428_);
v___x_434_ = lean_apply_2(v_inst_426_, v_k_428_, v_k_430_);
v___x_435_ = lean_unbox(v___x_434_);
switch(v___x_435_)
{
case 0:
{
lean_dec(v_r_433_);
lean_dec(v_v_431_);
lean_dec(v_k_430_);
v_t_427_ = v_l_432_;
goto _start;
}
case 1:
{
lean_object* v___x_437_; 
lean_dec(v_r_433_);
lean_dec(v_l_432_);
lean_dec(v_k_428_);
lean_dec_ref(v_inst_426_);
v___x_437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_437_, 0, v_k_430_);
lean_ctor_set(v___x_437_, 1, v_v_431_);
return v___x_437_;
}
default: 
{
lean_dec(v_l_432_);
lean_dec(v_v_431_);
lean_dec(v_k_430_);
v_t_427_ = v_r_433_;
goto _start;
}
}
}
else
{
lean_dec(v_k_428_);
lean_dec_ref(v_inst_426_);
lean_inc_ref(v_fallback_429_);
return v_fallback_429_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg___boxed(lean_object* v_inst_439_, lean_object* v_t_440_, lean_object* v_k_441_, lean_object* v_fallback_442_){
_start:
{
lean_object* v_res_443_; 
v_res_443_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_439_, v_t_440_, v_k_441_, v_fallback_442_);
lean_dec_ref(v_fallback_442_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD(lean_object* v_00_u03b1_444_, lean_object* v_00_u03b2_445_, lean_object* v_inst_446_, lean_object* v_t_447_, lean_object* v_k_448_, lean_object* v_fallback_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_446_, v_t_447_, v_k_448_, v_fallback_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___boxed(lean_object* v_00_u03b1_451_, lean_object* v_00_u03b2_452_, lean_object* v_inst_453_, lean_object* v_t_454_, lean_object* v_k_455_, lean_object* v_fallback_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_DTreeMap_Internal_Impl_getEntryD(v_00_u03b1_451_, v_00_u03b2_452_, v_inst_453_, v_t_454_, v_k_455_, v_fallback_456_);
lean_dec_ref(v_fallback_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object* v_inst_458_, lean_object* v_t_459_, lean_object* v_k_460_){
_start:
{
if (lean_obj_tag(v_t_459_) == 0)
{
lean_object* v_k_461_; lean_object* v_l_462_; lean_object* v_r_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v_k_461_ = lean_ctor_get(v_t_459_, 1);
lean_inc(v_k_461_);
v_l_462_ = lean_ctor_get(v_t_459_, 3);
lean_inc(v_l_462_);
v_r_463_ = lean_ctor_get(v_t_459_, 4);
lean_inc(v_r_463_);
lean_dec_ref(v_t_459_);
lean_inc_ref(v_inst_458_);
lean_inc(v_k_461_);
lean_inc(v_k_460_);
v___x_464_ = lean_apply_2(v_inst_458_, v_k_460_, v_k_461_);
v___x_465_ = lean_unbox(v___x_464_);
switch(v___x_465_)
{
case 0:
{
lean_dec(v_r_463_);
lean_dec(v_k_461_);
v_t_459_ = v_l_462_;
goto _start;
}
case 1:
{
lean_object* v___x_467_; 
lean_dec(v_r_463_);
lean_dec(v_l_462_);
lean_dec(v_k_460_);
lean_dec_ref(v_inst_458_);
v___x_467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_467_, 0, v_k_461_);
return v___x_467_;
}
default: 
{
lean_dec(v_l_462_);
lean_dec(v_k_461_);
v_t_459_ = v_r_463_;
goto _start;
}
}
}
else
{
lean_object* v___x_469_; 
lean_dec(v_k_460_);
lean_dec_ref(v_inst_458_);
v___x_469_ = lean_box(0);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f(lean_object* v_00_u03b1_470_, lean_object* v_00_u03b2_471_, lean_object* v_inst_472_, lean_object* v_t_473_, lean_object* v_k_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_inst_472_, v_t_473_, v_k_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object* v_inst_476_, lean_object* v_t_477_, lean_object* v_k_478_){
_start:
{
lean_object* v_k_479_; lean_object* v_l_480_; lean_object* v_r_481_; lean_object* v___x_482_; uint8_t v___x_483_; 
v_k_479_ = lean_ctor_get(v_t_477_, 1);
lean_inc(v_k_479_);
v_l_480_ = lean_ctor_get(v_t_477_, 3);
lean_inc(v_l_480_);
v_r_481_ = lean_ctor_get(v_t_477_, 4);
lean_inc(v_r_481_);
lean_dec(v_t_477_);
lean_inc_ref(v_inst_476_);
lean_inc(v_k_479_);
lean_inc(v_k_478_);
v___x_482_ = lean_apply_2(v_inst_476_, v_k_478_, v_k_479_);
v___x_483_ = lean_unbox(v___x_482_);
switch(v___x_483_)
{
case 0:
{
lean_dec(v_r_481_);
lean_dec(v_k_479_);
v_t_477_ = v_l_480_;
goto _start;
}
case 1:
{
lean_dec(v_r_481_);
lean_dec(v_l_480_);
lean_dec(v_k_478_);
lean_dec_ref(v_inst_476_);
return v_k_479_;
}
default: 
{
lean_dec(v_l_480_);
lean_dec(v_k_479_);
v_t_477_ = v_r_481_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey(lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_inst_488_, lean_object* v_t_489_, lean_object* v_k_490_, lean_object* v_hlk_491_){
_start:
{
lean_object* v___x_492_; 
v___x_492_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_inst_488_, v_t_489_, v_k_490_);
return v___x_492_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_494_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_495_ = lean_unsigned_to_nat(13u);
v___x_496_ = lean_unsigned_to_nat(186u);
v___x_497_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0));
v___x_498_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_499_ = l_mkPanicMessageWithDecl(v___x_498_, v___x_497_, v___x_496_, v___x_495_, v___x_494_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object* v_inst_500_, lean_object* v_t_501_, lean_object* v_k_502_, lean_object* v_inst_503_){
_start:
{
if (lean_obj_tag(v_t_501_) == 0)
{
lean_object* v_k_504_; lean_object* v_l_505_; lean_object* v_r_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
v_k_504_ = lean_ctor_get(v_t_501_, 1);
lean_inc(v_k_504_);
v_l_505_ = lean_ctor_get(v_t_501_, 3);
lean_inc(v_l_505_);
v_r_506_ = lean_ctor_get(v_t_501_, 4);
lean_inc(v_r_506_);
lean_dec_ref(v_t_501_);
lean_inc_ref(v_inst_500_);
lean_inc(v_k_504_);
lean_inc(v_k_502_);
v___x_507_ = lean_apply_2(v_inst_500_, v_k_502_, v_k_504_);
v___x_508_ = lean_unbox(v___x_507_);
switch(v___x_508_)
{
case 0:
{
lean_dec(v_r_506_);
lean_dec(v_k_504_);
v_t_501_ = v_l_505_;
goto _start;
}
case 1:
{
lean_dec(v_r_506_);
lean_dec(v_l_505_);
lean_dec(v_inst_503_);
lean_dec(v_k_502_);
lean_dec_ref(v_inst_500_);
return v_k_504_;
}
default: 
{
lean_dec(v_l_505_);
lean_dec(v_k_504_);
v_t_501_ = v_r_506_;
goto _start;
}
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec(v_k_502_);
lean_dec_ref(v_inst_500_);
v___x_511_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1);
v___x_512_ = l_panic___redArg(v_inst_503_, v___x_511_);
return v___x_512_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21(lean_object* v_00_u03b1_513_, lean_object* v_00_u03b2_514_, lean_object* v_inst_515_, lean_object* v_t_516_, lean_object* v_k_517_, lean_object* v_inst_518_){
_start:
{
lean_object* v___x_519_; 
v___x_519_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_inst_515_, v_t_516_, v_k_517_, v_inst_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object* v_inst_520_, lean_object* v_t_521_, lean_object* v_k_522_, lean_object* v_fallback_523_){
_start:
{
if (lean_obj_tag(v_t_521_) == 0)
{
lean_object* v_k_524_; lean_object* v_l_525_; lean_object* v_r_526_; lean_object* v___x_527_; uint8_t v___x_528_; 
v_k_524_ = lean_ctor_get(v_t_521_, 1);
lean_inc(v_k_524_);
v_l_525_ = lean_ctor_get(v_t_521_, 3);
lean_inc(v_l_525_);
v_r_526_ = lean_ctor_get(v_t_521_, 4);
lean_inc(v_r_526_);
lean_dec_ref(v_t_521_);
lean_inc_ref(v_inst_520_);
lean_inc(v_k_524_);
lean_inc(v_k_522_);
v___x_527_ = lean_apply_2(v_inst_520_, v_k_522_, v_k_524_);
v___x_528_ = lean_unbox(v___x_527_);
switch(v___x_528_)
{
case 0:
{
lean_dec(v_r_526_);
lean_dec(v_k_524_);
v_t_521_ = v_l_525_;
goto _start;
}
case 1:
{
lean_dec(v_r_526_);
lean_dec(v_l_525_);
lean_dec(v_k_522_);
lean_dec_ref(v_inst_520_);
return v_k_524_;
}
default: 
{
lean_dec(v_l_525_);
lean_dec(v_k_524_);
v_t_521_ = v_r_526_;
goto _start;
}
}
}
else
{
lean_dec(v_k_522_);
lean_dec_ref(v_inst_520_);
lean_inc(v_fallback_523_);
return v_fallback_523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg___boxed(lean_object* v_inst_531_, lean_object* v_t_532_, lean_object* v_k_533_, lean_object* v_fallback_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_531_, v_t_532_, v_k_533_, v_fallback_534_);
lean_dec(v_fallback_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_inst_538_, lean_object* v_t_539_, lean_object* v_k_540_, lean_object* v_fallback_541_){
_start:
{
lean_object* v___x_542_; 
v___x_542_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_538_, v_t_539_, v_k_540_, v_fallback_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___boxed(lean_object* v_00_u03b1_543_, lean_object* v_00_u03b2_544_, lean_object* v_inst_545_, lean_object* v_t_546_, lean_object* v_k_547_, lean_object* v_fallback_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_DTreeMap_Internal_Impl_getKeyD(v_00_u03b1_543_, v_00_u03b2_544_, v_inst_545_, v_t_546_, v_k_547_, v_fallback_548_);
lean_dec(v_fallback_548_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object* v_inst_550_, lean_object* v_t_551_, lean_object* v_k_552_){
_start:
{
if (lean_obj_tag(v_t_551_) == 0)
{
lean_object* v_k_553_; lean_object* v_v_554_; lean_object* v_l_555_; lean_object* v_r_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_k_553_ = lean_ctor_get(v_t_551_, 1);
lean_inc(v_k_553_);
v_v_554_ = lean_ctor_get(v_t_551_, 2);
lean_inc(v_v_554_);
v_l_555_ = lean_ctor_get(v_t_551_, 3);
lean_inc(v_l_555_);
v_r_556_ = lean_ctor_get(v_t_551_, 4);
lean_inc(v_r_556_);
lean_dec_ref(v_t_551_);
lean_inc_ref(v_inst_550_);
lean_inc(v_k_552_);
v___x_557_ = lean_apply_2(v_inst_550_, v_k_552_, v_k_553_);
v___x_558_ = lean_unbox(v___x_557_);
switch(v___x_558_)
{
case 0:
{
lean_dec(v_r_556_);
lean_dec(v_v_554_);
v_t_551_ = v_l_555_;
goto _start;
}
case 1:
{
lean_object* v___x_560_; 
lean_dec(v_r_556_);
lean_dec(v_l_555_);
lean_dec(v_k_552_);
lean_dec_ref(v_inst_550_);
v___x_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_560_, 0, v_v_554_);
return v___x_560_;
}
default: 
{
lean_dec(v_l_555_);
lean_dec(v_v_554_);
v_t_551_ = v_r_556_;
goto _start;
}
}
}
else
{
lean_object* v___x_562_; 
lean_dec(v_k_552_);
lean_dec_ref(v_inst_550_);
v___x_562_ = lean_box(0);
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f(lean_object* v_00_u03b1_563_, lean_object* v_00_u03b4_564_, lean_object* v_inst_565_, lean_object* v_t_566_, lean_object* v_k_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_inst_565_, v_t_566_, v_k_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object* v_inst_569_, lean_object* v_t_570_, lean_object* v_k_571_){
_start:
{
lean_object* v_k_572_; lean_object* v_v_573_; lean_object* v_l_574_; lean_object* v_r_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v_k_572_ = lean_ctor_get(v_t_570_, 1);
lean_inc(v_k_572_);
v_v_573_ = lean_ctor_get(v_t_570_, 2);
lean_inc(v_v_573_);
v_l_574_ = lean_ctor_get(v_t_570_, 3);
lean_inc(v_l_574_);
v_r_575_ = lean_ctor_get(v_t_570_, 4);
lean_inc(v_r_575_);
lean_dec(v_t_570_);
lean_inc_ref(v_inst_569_);
lean_inc(v_k_571_);
v___x_576_ = lean_apply_2(v_inst_569_, v_k_571_, v_k_572_);
v___x_577_ = lean_unbox(v___x_576_);
switch(v___x_577_)
{
case 0:
{
lean_dec(v_r_575_);
lean_dec(v_v_573_);
v_t_570_ = v_l_574_;
goto _start;
}
case 1:
{
lean_dec(v_r_575_);
lean_dec(v_l_574_);
lean_dec(v_k_571_);
lean_dec_ref(v_inst_569_);
return v_v_573_;
}
default: 
{
lean_dec(v_l_574_);
lean_dec(v_v_573_);
v_t_570_ = v_r_575_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get(lean_object* v_00_u03b1_580_, lean_object* v_00_u03b4_581_, lean_object* v_inst_582_, lean_object* v_t_583_, lean_object* v_k_584_, lean_object* v_hlk_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_inst_582_, v_t_583_, v_k_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; 
v___x_588_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_589_ = lean_unsigned_to_nat(13u);
v___x_590_ = lean_unsigned_to_nat(227u);
v___x_591_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0));
v___x_592_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_593_ = l_mkPanicMessageWithDecl(v___x_592_, v___x_591_, v___x_590_, v___x_589_, v___x_588_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object* v_inst_594_, lean_object* v_inst_595_, lean_object* v_t_596_, lean_object* v_k_597_){
_start:
{
if (lean_obj_tag(v_t_596_) == 0)
{
lean_object* v_k_598_; lean_object* v_v_599_; lean_object* v_l_600_; lean_object* v_r_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v_k_598_ = lean_ctor_get(v_t_596_, 1);
lean_inc(v_k_598_);
v_v_599_ = lean_ctor_get(v_t_596_, 2);
lean_inc(v_v_599_);
v_l_600_ = lean_ctor_get(v_t_596_, 3);
lean_inc(v_l_600_);
v_r_601_ = lean_ctor_get(v_t_596_, 4);
lean_inc(v_r_601_);
lean_dec_ref(v_t_596_);
lean_inc_ref(v_inst_594_);
lean_inc(v_k_597_);
v___x_602_ = lean_apply_2(v_inst_594_, v_k_597_, v_k_598_);
v___x_603_ = lean_unbox(v___x_602_);
switch(v___x_603_)
{
case 0:
{
lean_dec(v_r_601_);
lean_dec(v_v_599_);
v_t_596_ = v_l_600_;
goto _start;
}
case 1:
{
lean_dec(v_r_601_);
lean_dec(v_l_600_);
lean_dec(v_k_597_);
lean_dec(v_inst_595_);
lean_dec_ref(v_inst_594_);
return v_v_599_;
}
default: 
{
lean_dec(v_l_600_);
lean_dec(v_v_599_);
v_t_596_ = v_r_601_;
goto _start;
}
}
}
else
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec(v_k_597_);
lean_dec_ref(v_inst_594_);
v___x_606_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1);
v___x_607_ = l_panic___redArg(v_inst_595_, v___x_606_);
return v___x_607_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21(lean_object* v_00_u03b1_608_, lean_object* v_00_u03b4_609_, lean_object* v_inst_610_, lean_object* v_inst_611_, lean_object* v_t_612_, lean_object* v_k_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_inst_610_, v_inst_611_, v_t_612_, v_k_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object* v_inst_615_, lean_object* v_t_616_, lean_object* v_k_617_, lean_object* v_fallback_618_){
_start:
{
if (lean_obj_tag(v_t_616_) == 0)
{
lean_object* v_k_619_; lean_object* v_v_620_; lean_object* v_l_621_; lean_object* v_r_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v_k_619_ = lean_ctor_get(v_t_616_, 1);
lean_inc(v_k_619_);
v_v_620_ = lean_ctor_get(v_t_616_, 2);
lean_inc(v_v_620_);
v_l_621_ = lean_ctor_get(v_t_616_, 3);
lean_inc(v_l_621_);
v_r_622_ = lean_ctor_get(v_t_616_, 4);
lean_inc(v_r_622_);
lean_dec_ref(v_t_616_);
lean_inc_ref(v_inst_615_);
lean_inc(v_k_617_);
v___x_623_ = lean_apply_2(v_inst_615_, v_k_617_, v_k_619_);
v___x_624_ = lean_unbox(v___x_623_);
switch(v___x_624_)
{
case 0:
{
lean_dec(v_r_622_);
lean_dec(v_v_620_);
v_t_616_ = v_l_621_;
goto _start;
}
case 1:
{
lean_dec(v_r_622_);
lean_dec(v_l_621_);
lean_dec(v_k_617_);
lean_dec_ref(v_inst_615_);
return v_v_620_;
}
default: 
{
lean_dec(v_l_621_);
lean_dec(v_v_620_);
v_t_616_ = v_r_622_;
goto _start;
}
}
}
else
{
lean_dec(v_k_617_);
lean_dec_ref(v_inst_615_);
lean_inc(v_fallback_618_);
return v_fallback_618_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg___boxed(lean_object* v_inst_627_, lean_object* v_t_628_, lean_object* v_k_629_, lean_object* v_fallback_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_627_, v_t_628_, v_k_629_, v_fallback_630_);
lean_dec(v_fallback_630_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD(lean_object* v_00_u03b1_632_, lean_object* v_00_u03b4_633_, lean_object* v_inst_634_, lean_object* v_t_635_, lean_object* v_k_636_, lean_object* v_fallback_637_){
_start:
{
lean_object* v___x_638_; 
v___x_638_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_634_, v_t_635_, v_k_636_, v_fallback_637_);
return v___x_638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___boxed(lean_object* v_00_u03b1_639_, lean_object* v_00_u03b4_640_, lean_object* v_inst_641_, lean_object* v_t_642_, lean_object* v_k_643_, lean_object* v_fallback_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Std_DTreeMap_Internal_Impl_Const_getD(v_00_u03b1_639_, v_00_u03b4_640_, v_inst_641_, v_t_642_, v_k_643_, v_fallback_644_);
lean_dec(v_fallback_644_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1(lean_object* v_f_646_, lean_object* v_k_647_, lean_object* v_v_648_, lean_object* v_toBind_649_, lean_object* v___f_650_, lean_object* v_left_651_){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = lean_apply_3(v_f_646_, v_left_651_, v_k_647_, v_v_648_);
v___x_653_ = lean_apply_4(v_toBind_649_, lean_box(0), lean_box(0), v___x_652_, v___f_650_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object* v_inst_654_, lean_object* v_f_655_, lean_object* v_init_656_, lean_object* v_x_657_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v_toBind_658_; lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v_l_661_; lean_object* v_r_662_; lean_object* v___f_663_; lean_object* v___f_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v_toBind_658_ = lean_ctor_get(v_inst_654_, 1);
lean_inc(v_toBind_658_);
v_k_659_ = lean_ctor_get(v_x_657_, 1);
lean_inc(v_k_659_);
v_v_660_ = lean_ctor_get(v_x_657_, 2);
lean_inc(v_v_660_);
v_l_661_ = lean_ctor_get(v_x_657_, 3);
lean_inc(v_l_661_);
v_r_662_ = lean_ctor_get(v_x_657_, 4);
lean_inc(v_r_662_);
lean_dec_ref(v_x_657_);
lean_inc(v_f_655_);
lean_inc_ref(v_inst_654_);
v___f_663_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_663_, 0, v_inst_654_);
lean_closure_set(v___f_663_, 1, v_f_655_);
lean_closure_set(v___f_663_, 2, v_r_662_);
lean_inc(v_toBind_658_);
lean_inc(v_f_655_);
v___f_664_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_664_, 0, v_f_655_);
lean_closure_set(v___f_664_, 1, v_k_659_);
lean_closure_set(v___f_664_, 2, v_v_660_);
lean_closure_set(v___f_664_, 3, v_toBind_658_);
lean_closure_set(v___f_664_, 4, v___f_663_);
v___x_665_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_654_, v_f_655_, v_init_656_, v_l_661_);
v___x_666_ = lean_apply_4(v_toBind_658_, lean_box(0), lean_box(0), v___x_665_, v___f_664_);
return v___x_666_;
}
else
{
lean_object* v_toApplicative_667_; lean_object* v_toPure_668_; lean_object* v___x_669_; 
v_toApplicative_667_ = lean_ctor_get(v_inst_654_, 0);
lean_inc_ref(v_toApplicative_667_);
lean_dec(v_f_655_);
lean_dec_ref(v_inst_654_);
v_toPure_668_ = lean_ctor_get(v_toApplicative_667_, 1);
lean_inc(v_toPure_668_);
lean_dec_ref(v_toApplicative_667_);
v___x_669_ = lean_apply_2(v_toPure_668_, lean_box(0), v_init_656_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0(lean_object* v_inst_670_, lean_object* v_f_671_, lean_object* v_r_672_, lean_object* v_middle_673_){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_670_, v_f_671_, v_middle_673_, v_r_672_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM(lean_object* v_00_u03b1_675_, lean_object* v_00_u03b2_676_, lean_object* v_00_u03b4_677_, lean_object* v_m_678_, lean_object* v_inst_679_, lean_object* v_f_680_, lean_object* v_init_681_, lean_object* v_x_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_679_, v_f_680_, v_init_681_, v_x_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0(lean_object* v_f_684_, lean_object* v_x1_685_, lean_object* v_x2_686_, lean_object* v_x3_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_apply_3(v_f_684_, v_x1_685_, v_x2_686_, v_x3_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object* v_f_708_, lean_object* v_init_709_, lean_object* v_t_710_){
_start:
{
lean_object* v___f_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___f_711_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_711_, 0, v_f_708_);
v___x_712_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_713_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_712_, v___f_711_, v_init_709_, v_t_710_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl(lean_object* v_00_u03b1_714_, lean_object* v_00_u03b2_715_, lean_object* v_00_u03b4_716_, lean_object* v_f_717_, lean_object* v_init_718_, lean_object* v_t_719_){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_717_, v_init_718_, v_t_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1(lean_object* v_f_721_, lean_object* v_k_722_, lean_object* v_v_723_, lean_object* v_toBind_724_, lean_object* v___f_725_, lean_object* v_right_726_){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; 
v___x_727_ = lean_apply_3(v_f_721_, v_k_722_, v_v_723_, v_right_726_);
v___x_728_ = lean_apply_4(v_toBind_724_, lean_box(0), lean_box(0), v___x_727_, v___f_725_);
return v___x_728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object* v_inst_729_, lean_object* v_f_730_, lean_object* v_init_731_, lean_object* v_x_732_){
_start:
{
if (lean_obj_tag(v_x_732_) == 0)
{
lean_object* v_toBind_733_; lean_object* v_k_734_; lean_object* v_v_735_; lean_object* v_l_736_; lean_object* v_r_737_; lean_object* v___f_738_; lean_object* v___f_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v_toBind_733_ = lean_ctor_get(v_inst_729_, 1);
lean_inc(v_toBind_733_);
v_k_734_ = lean_ctor_get(v_x_732_, 1);
lean_inc(v_k_734_);
v_v_735_ = lean_ctor_get(v_x_732_, 2);
lean_inc(v_v_735_);
v_l_736_ = lean_ctor_get(v_x_732_, 3);
lean_inc(v_l_736_);
v_r_737_ = lean_ctor_get(v_x_732_, 4);
lean_inc(v_r_737_);
lean_dec_ref(v_x_732_);
lean_inc(v_f_730_);
lean_inc_ref(v_inst_729_);
v___f_738_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_738_, 0, v_inst_729_);
lean_closure_set(v___f_738_, 1, v_f_730_);
lean_closure_set(v___f_738_, 2, v_l_736_);
lean_inc(v_toBind_733_);
lean_inc(v_f_730_);
v___f_739_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_739_, 0, v_f_730_);
lean_closure_set(v___f_739_, 1, v_k_734_);
lean_closure_set(v___f_739_, 2, v_v_735_);
lean_closure_set(v___f_739_, 3, v_toBind_733_);
lean_closure_set(v___f_739_, 4, v___f_738_);
v___x_740_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_729_, v_f_730_, v_init_731_, v_r_737_);
v___x_741_ = lean_apply_4(v_toBind_733_, lean_box(0), lean_box(0), v___x_740_, v___f_739_);
return v___x_741_;
}
else
{
lean_object* v_toApplicative_742_; lean_object* v_toPure_743_; lean_object* v___x_744_; 
v_toApplicative_742_ = lean_ctor_get(v_inst_729_, 0);
lean_inc_ref(v_toApplicative_742_);
lean_dec(v_f_730_);
lean_dec_ref(v_inst_729_);
v_toPure_743_ = lean_ctor_get(v_toApplicative_742_, 1);
lean_inc(v_toPure_743_);
lean_dec_ref(v_toApplicative_742_);
v___x_744_ = lean_apply_2(v_toPure_743_, lean_box(0), v_init_731_);
return v___x_744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0(lean_object* v_inst_745_, lean_object* v_f_746_, lean_object* v_l_747_, lean_object* v_middle_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_745_, v_f_746_, v_middle_748_, v_l_747_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM(lean_object* v_00_u03b1_750_, lean_object* v_00_u03b2_751_, lean_object* v_00_u03b4_752_, lean_object* v_m_753_, lean_object* v_inst_754_, lean_object* v_f_755_, lean_object* v_init_756_, lean_object* v_x_757_){
_start:
{
lean_object* v___x_758_; 
v___x_758_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_754_, v_f_755_, v_init_756_, v_x_757_);
return v___x_758_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr___redArg(lean_object* v_f_759_, lean_object* v_init_760_, lean_object* v_t_761_){
_start:
{
lean_object* v___f_762_; lean_object* v___x_763_; lean_object* v___x_764_; 
v___f_762_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_762_, 0, v_f_759_);
v___x_763_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_764_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_763_, v___f_762_, v_init_760_, v_t_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr(lean_object* v_00_u03b1_765_, lean_object* v_00_u03b2_766_, lean_object* v_00_u03b4_767_, lean_object* v_f_768_, lean_object* v_init_769_, lean_object* v_t_770_){
_start:
{
lean_object* v___f_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___f_771_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_771_, 0, v_f_768_);
v___x_772_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_773_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_772_, v___f_771_, v_init_769_, v_t_770_);
return v___x_773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0(lean_object* v_f_774_, lean_object* v_x_775_, lean_object* v_k_776_, lean_object* v_v_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = lean_apply_2(v_f_774_, v_k_776_, v_v_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg(lean_object* v_inst_779_, lean_object* v_f_780_, lean_object* v_t_781_){
_start:
{
lean_object* v___f_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___f_782_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_782_, 0, v_f_780_);
v___x_783_ = lean_box(0);
v___x_784_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_779_, v___f_782_, v___x_783_, v_t_781_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM(lean_object* v_00_u03b1_785_, lean_object* v_00_u03b2_786_, lean_object* v_m_787_, lean_object* v_inst_788_, lean_object* v_f_789_, lean_object* v_t_790_){
_start:
{
lean_object* v___f_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
v___f_791_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_791_, 0, v_f_789_);
v___x_792_ = lean_box(0);
v___x_793_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_788_, v___f_791_, v___x_792_, v_t_790_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0(lean_object* v_toPure_794_, lean_object* v_d_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; 
v___x_796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_796_, 0, v_d_795_);
v___x_797_ = lean_apply_2(v_toPure_794_, lean_box(0), v___x_796_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2(lean_object* v___f_798_, lean_object* v_f_799_, lean_object* v_k_800_, lean_object* v_v_801_, lean_object* v_toBind_802_, lean_object* v___f_803_, lean_object* v_____do__lift_804_){
_start:
{
if (lean_obj_tag(v_____do__lift_804_) == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; 
lean_dec(v___f_803_);
lean_dec(v_toBind_802_);
lean_dec(v_v_801_);
lean_dec(v_k_800_);
lean_dec(v_f_799_);
v_a_805_ = lean_ctor_get(v_____do__lift_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref(v_____do__lift_804_);
v___x_806_ = lean_apply_1(v___f_798_, v_a_805_);
return v___x_806_;
}
else
{
lean_object* v_a_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v___f_798_);
v_a_807_ = lean_ctor_get(v_____do__lift_804_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v_____do__lift_804_);
v___x_808_ = lean_apply_3(v_f_799_, v_k_800_, v_v_801_, v_a_807_);
v___x_809_ = lean_apply_4(v_toBind_802_, lean_box(0), lean_box(0), v___x_808_, v___f_803_);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object* v_inst_810_, lean_object* v_f_811_, lean_object* v_init_812_, lean_object* v_x_813_){
_start:
{
if (lean_obj_tag(v_x_813_) == 0)
{
lean_object* v_toApplicative_814_; lean_object* v_toBind_815_; lean_object* v_toPure_816_; lean_object* v_k_817_; lean_object* v_v_818_; lean_object* v_l_819_; lean_object* v_r_820_; lean_object* v___f_821_; lean_object* v___f_822_; lean_object* v___f_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_toApplicative_814_ = lean_ctor_get(v_inst_810_, 0);
v_toBind_815_ = lean_ctor_get(v_inst_810_, 1);
lean_inc(v_toBind_815_);
v_toPure_816_ = lean_ctor_get(v_toApplicative_814_, 1);
v_k_817_ = lean_ctor_get(v_x_813_, 1);
lean_inc(v_k_817_);
v_v_818_ = lean_ctor_get(v_x_813_, 2);
lean_inc(v_v_818_);
v_l_819_ = lean_ctor_get(v_x_813_, 3);
lean_inc(v_l_819_);
v_r_820_ = lean_ctor_get(v_x_813_, 4);
lean_inc(v_r_820_);
lean_dec_ref(v_x_813_);
lean_inc(v_toPure_816_);
v___f_821_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0), 2, 1);
lean_closure_set(v___f_821_, 0, v_toPure_816_);
lean_inc(v_f_811_);
lean_inc_ref(v_inst_810_);
lean_inc_ref(v___f_821_);
v___f_822_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1), 5, 4);
lean_closure_set(v___f_822_, 0, v___f_821_);
lean_closure_set(v___f_822_, 1, v_inst_810_);
lean_closure_set(v___f_822_, 2, v_f_811_);
lean_closure_set(v___f_822_, 3, v_r_820_);
lean_inc(v_toBind_815_);
lean_inc(v_f_811_);
v___f_823_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2), 7, 6);
lean_closure_set(v___f_823_, 0, v___f_821_);
lean_closure_set(v___f_823_, 1, v_f_811_);
lean_closure_set(v___f_823_, 2, v_k_817_);
lean_closure_set(v___f_823_, 3, v_v_818_);
lean_closure_set(v___f_823_, 4, v_toBind_815_);
lean_closure_set(v___f_823_, 5, v___f_822_);
v___x_824_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_810_, v_f_811_, v_init_812_, v_l_819_);
v___x_825_ = lean_apply_4(v_toBind_815_, lean_box(0), lean_box(0), v___x_824_, v___f_823_);
return v___x_825_;
}
else
{
lean_object* v_toApplicative_826_; lean_object* v_toPure_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v_toApplicative_826_ = lean_ctor_get(v_inst_810_, 0);
lean_inc_ref(v_toApplicative_826_);
lean_dec(v_f_811_);
lean_dec_ref(v_inst_810_);
v_toPure_827_ = lean_ctor_get(v_toApplicative_826_, 1);
lean_inc(v_toPure_827_);
lean_dec_ref(v_toApplicative_826_);
v___x_828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_828_, 0, v_init_812_);
v___x_829_ = lean_apply_2(v_toPure_827_, lean_box(0), v___x_828_);
return v___x_829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1(lean_object* v___f_830_, lean_object* v_inst_831_, lean_object* v_f_832_, lean_object* v_r_833_, lean_object* v_____do__lift_834_){
_start:
{
if (lean_obj_tag(v_____do__lift_834_) == 0)
{
lean_object* v_a_835_; lean_object* v___x_836_; 
lean_dec(v_r_833_);
lean_dec(v_f_832_);
lean_dec_ref(v_inst_831_);
v_a_835_ = lean_ctor_get(v_____do__lift_834_, 0);
lean_inc(v_a_835_);
lean_dec_ref(v_____do__lift_834_);
v___x_836_ = lean_apply_1(v___f_830_, v_a_835_);
return v___x_836_;
}
else
{
lean_object* v_a_837_; lean_object* v___x_838_; 
lean_dec(v___f_830_);
v_a_837_ = lean_ctor_get(v_____do__lift_834_, 0);
lean_inc(v_a_837_);
lean_dec_ref(v_____do__lift_834_);
v___x_838_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_831_, v_f_832_, v_a_837_, v_r_833_);
return v___x_838_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep(lean_object* v_00_u03b1_839_, lean_object* v_00_u03b2_840_, lean_object* v_00_u03b4_841_, lean_object* v_m_842_, lean_object* v_inst_843_, lean_object* v_f_844_, lean_object* v_init_845_, lean_object* v_x_846_){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_843_, v_f_844_, v_init_845_, v_x_846_);
return v___x_847_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0(lean_object* v_toPure_848_, lean_object* v_____do__lift_849_){
_start:
{
lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_850_ = lean_ctor_get(v_____do__lift_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref(v_____do__lift_849_);
v___x_851_ = lean_apply_2(v_toPure_848_, lean_box(0), v_a_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg(lean_object* v_inst_852_, lean_object* v_f_853_, lean_object* v_init_854_, lean_object* v_t_855_){
_start:
{
lean_object* v_toApplicative_856_; lean_object* v_toBind_857_; lean_object* v_toPure_858_; lean_object* v___x_859_; lean_object* v___f_860_; lean_object* v___x_861_; 
v_toApplicative_856_ = lean_ctor_get(v_inst_852_, 0);
v_toBind_857_ = lean_ctor_get(v_inst_852_, 1);
lean_inc(v_toBind_857_);
v_toPure_858_ = lean_ctor_get(v_toApplicative_856_, 1);
lean_inc(v_toPure_858_);
v___x_859_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_852_, v_f_853_, v_init_854_, v_t_855_);
v___f_860_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_860_, 0, v_toPure_858_);
v___x_861_ = lean_apply_4(v_toBind_857_, lean_box(0), lean_box(0), v___x_859_, v___f_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn(lean_object* v_00_u03b1_862_, lean_object* v_00_u03b2_863_, lean_object* v_00_u03b4_864_, lean_object* v_m_865_, lean_object* v_inst_866_, lean_object* v_f_867_, lean_object* v_init_868_, lean_object* v_t_869_){
_start:
{
lean_object* v_toApplicative_870_; lean_object* v_toBind_871_; lean_object* v_toPure_872_; lean_object* v___x_873_; lean_object* v___f_874_; lean_object* v___x_875_; 
v_toApplicative_870_ = lean_ctor_get(v_inst_866_, 0);
v_toBind_871_ = lean_ctor_get(v_inst_866_, 1);
lean_inc(v_toBind_871_);
v_toPure_872_ = lean_ctor_get(v_toApplicative_870_, 1);
lean_inc(v_toPure_872_);
v___x_873_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_866_, v_f_867_, v_init_868_, v_t_869_);
v___f_874_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_874_, 0, v_toPure_872_);
v___x_875_ = lean_apply_4(v_toBind_871_, lean_box(0), lean_box(0), v___x_873_, v___f_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_876_, lean_object* v_a_877_, lean_object* v_b_878_, lean_object* v_acc_879_){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_880_, 0, v_a_877_);
lean_ctor_set(v___x_880_, 1, v_b_878_);
v___x_881_ = lean_apply_2(v_f_876_, v___x_880_, v_acc_879_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_882_, lean_object* v_00_u03b2_883_, lean_object* v_m_884_, lean_object* v_init_885_, lean_object* v_f_886_){
_start:
{
lean_object* v_toApplicative_887_; lean_object* v_toBind_888_; lean_object* v_toPure_889_; lean_object* v___f_890_; lean_object* v___x_891_; lean_object* v___f_892_; lean_object* v___x_893_; 
v_toApplicative_887_ = lean_ctor_get(v_inst_882_, 0);
v_toBind_888_ = lean_ctor_get(v_inst_882_, 1);
lean_inc(v_toBind_888_);
v_toPure_889_ = lean_ctor_get(v_toApplicative_887_, 1);
lean_inc(v_toPure_889_);
v___f_890_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_890_, 0, v_f_886_);
v___x_891_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_882_, v___f_890_, v_init_885_, v_m_884_);
v___f_892_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_892_, 0, v_toPure_889_);
v___x_893_ = lean_apply_4(v_toBind_888_, lean_box(0), lean_box(0), v___x_891_, v___f_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg(lean_object* v_inst_894_){
_start:
{
lean_object* v___f_895_; 
v___f_895_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_895_, 0, v_inst_894_);
return v___f_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad(lean_object* v_00_u03b1_896_, lean_object* v_00_u03b2_897_, lean_object* v_m_898_, lean_object* v_inst_899_){
_start:
{
lean_object* v___f_900_; 
v___f_900_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_900_, 0, v_inst_899_);
return v___f_900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(lean_object* v_p_901_, lean_object* v___x_902_, lean_object* v___x_903_, lean_object* v_a_904_, lean_object* v_b_905_, lean_object* v_acc_906_){
_start:
{
lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_907_ = lean_apply_2(v_p_901_, v_a_904_, v_b_905_);
v___x_908_ = lean_unbox(v___x_907_);
if (v___x_908_ == 0)
{
lean_object* v___x_909_; 
v___x_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_902_);
return v___x_909_;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref(v___x_902_);
v___x_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_907_);
v___x_911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v___x_903_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed(lean_object* v_p_913_, lean_object* v___x_914_, lean_object* v___x_915_, lean_object* v_a_916_, lean_object* v_b_917_, lean_object* v_acc_918_){
_start:
{
lean_object* v_res_919_; 
v_res_919_ = l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(v_p_913_, v___x_914_, v___x_915_, v_a_916_, v_b_917_, v_acc_918_);
lean_dec_ref(v_acc_918_);
return v_res_919_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any___redArg(lean_object* v_t_923_, lean_object* v_p_924_){
_start:
{
lean_object* v___y_926_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___f_934_; lean_object* v___x_935_; lean_object* v_a_936_; 
v___x_931_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_932_ = lean_box(0);
v___x_933_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_934_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_934_, 0, v_p_924_);
lean_closure_set(v___f_934_, 1, v___x_933_);
lean_closure_set(v___f_934_, 2, v___x_932_);
v___x_935_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_931_, v___f_934_, v___x_933_, v_t_923_);
v_a_936_ = lean_ctor_get(v___x_935_, 0);
lean_inc(v_a_936_);
lean_dec(v___x_935_);
v___y_926_ = v_a_936_;
goto v___jp_925_;
v___jp_925_:
{
lean_object* v_fst_927_; 
v_fst_927_ = lean_ctor_get(v___y_926_, 0);
lean_inc(v_fst_927_);
lean_dec_ref(v___y_926_);
if (lean_obj_tag(v_fst_927_) == 0)
{
uint8_t v___x_928_; 
v___x_928_ = 0;
return v___x_928_;
}
else
{
lean_object* v_val_929_; uint8_t v___x_930_; 
v_val_929_ = lean_ctor_get(v_fst_927_, 0);
lean_inc(v_val_929_);
lean_dec_ref(v_fst_927_);
v___x_930_ = lean_unbox(v_val_929_);
lean_dec(v_val_929_);
return v___x_930_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___boxed(lean_object* v_t_937_, lean_object* v_p_938_){
_start:
{
uint8_t v_res_939_; lean_object* v_r_940_; 
v_res_939_ = l_Std_DTreeMap_Internal_Impl_any___redArg(v_t_937_, v_p_938_);
v_r_940_ = lean_box(v_res_939_);
return v_r_940_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any(lean_object* v_00_u03b1_941_, lean_object* v_00_u03b2_942_, lean_object* v_t_943_, lean_object* v_p_944_){
_start:
{
lean_object* v___y_946_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___f_954_; lean_object* v___x_955_; lean_object* v_a_956_; 
v___x_951_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_952_ = lean_box(0);
v___x_953_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_954_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_954_, 0, v_p_944_);
lean_closure_set(v___f_954_, 1, v___x_953_);
lean_closure_set(v___f_954_, 2, v___x_952_);
v___x_955_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_951_, v___f_954_, v___x_953_, v_t_943_);
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___y_946_ = v_a_956_;
goto v___jp_945_;
v___jp_945_:
{
lean_object* v_fst_947_; 
v_fst_947_ = lean_ctor_get(v___y_946_, 0);
lean_inc(v_fst_947_);
lean_dec_ref(v___y_946_);
if (lean_obj_tag(v_fst_947_) == 0)
{
uint8_t v___x_948_; 
v___x_948_ = 0;
return v___x_948_;
}
else
{
lean_object* v_val_949_; uint8_t v___x_950_; 
v_val_949_ = lean_ctor_get(v_fst_947_, 0);
lean_inc(v_val_949_);
lean_dec_ref(v_fst_947_);
v___x_950_ = lean_unbox(v_val_949_);
lean_dec(v_val_949_);
return v___x_950_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___boxed(lean_object* v_00_u03b1_957_, lean_object* v_00_u03b2_958_, lean_object* v_t_959_, lean_object* v_p_960_){
_start:
{
uint8_t v_res_961_; lean_object* v_r_962_; 
v_res_961_ = l_Std_DTreeMap_Internal_Impl_any(v_00_u03b1_957_, v_00_u03b2_958_, v_t_959_, v_p_960_);
v_r_962_ = lean_box(v_res_961_);
return v_r_962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(lean_object* v_p_963_, lean_object* v___x_964_, lean_object* v___x_965_, lean_object* v_a_966_, lean_object* v_b_967_, lean_object* v_acc_968_){
_start:
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = lean_apply_2(v_p_963_, v_a_966_, v_b_967_);
v___x_970_ = lean_unbox(v___x_969_);
if (v___x_970_ == 0)
{
lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec_ref(v___x_965_);
v___x_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_971_, 0, v___x_969_);
v___x_972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_964_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_974_, 0, v___x_965_);
return v___x_974_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed(lean_object* v_p_975_, lean_object* v___x_976_, lean_object* v___x_977_, lean_object* v_a_978_, lean_object* v_b_979_, lean_object* v_acc_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(v_p_975_, v___x_976_, v___x_977_, v_a_978_, v_b_979_, v_acc_980_);
lean_dec_ref(v_acc_980_);
return v_res_981_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all___redArg(lean_object* v_t_982_, lean_object* v_p_983_){
_start:
{
lean_object* v___y_985_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___f_993_; lean_object* v___x_994_; lean_object* v_a_995_; 
v___x_990_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_991_ = lean_box(0);
v___x_992_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_993_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_993_, 0, v_p_983_);
lean_closure_set(v___f_993_, 1, v___x_991_);
lean_closure_set(v___f_993_, 2, v___x_992_);
v___x_994_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_990_, v___f_993_, v___x_992_, v_t_982_);
v_a_995_ = lean_ctor_get(v___x_994_, 0);
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___y_985_ = v_a_995_;
goto v___jp_984_;
v___jp_984_:
{
lean_object* v_fst_986_; 
v_fst_986_ = lean_ctor_get(v___y_985_, 0);
lean_inc(v_fst_986_);
lean_dec_ref(v___y_985_);
if (lean_obj_tag(v_fst_986_) == 0)
{
uint8_t v___x_987_; 
v___x_987_ = 1;
return v___x_987_;
}
else
{
lean_object* v_val_988_; uint8_t v___x_989_; 
v_val_988_ = lean_ctor_get(v_fst_986_, 0);
lean_inc(v_val_988_);
lean_dec_ref(v_fst_986_);
v___x_989_ = lean_unbox(v_val_988_);
lean_dec(v_val_988_);
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___boxed(lean_object* v_t_996_, lean_object* v_p_997_){
_start:
{
uint8_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l_Std_DTreeMap_Internal_Impl_all___redArg(v_t_996_, v_p_997_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all(lean_object* v_00_u03b1_1000_, lean_object* v_00_u03b2_1001_, lean_object* v_t_1002_, lean_object* v_p_1003_){
_start:
{
lean_object* v___y_1005_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v_a_1015_; 
v___x_1010_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1011_ = lean_box(0);
v___x_1012_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1013_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1013_, 0, v_p_1003_);
lean_closure_set(v___f_1013_, 1, v___x_1011_);
lean_closure_set(v___f_1013_, 2, v___x_1012_);
v___x_1014_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1010_, v___f_1013_, v___x_1012_, v_t_1002_);
v_a_1015_ = lean_ctor_get(v___x_1014_, 0);
lean_inc(v_a_1015_);
lean_dec(v___x_1014_);
v___y_1005_ = v_a_1015_;
goto v___jp_1004_;
v___jp_1004_:
{
lean_object* v_fst_1006_; 
v_fst_1006_ = lean_ctor_get(v___y_1005_, 0);
lean_inc(v_fst_1006_);
lean_dec_ref(v___y_1005_);
if (lean_obj_tag(v_fst_1006_) == 0)
{
uint8_t v___x_1007_; 
v___x_1007_ = 1;
return v___x_1007_;
}
else
{
lean_object* v_val_1008_; uint8_t v___x_1009_; 
v_val_1008_ = lean_ctor_get(v_fst_1006_, 0);
lean_inc(v_val_1008_);
lean_dec_ref(v_fst_1006_);
v___x_1009_ = lean_unbox(v_val_1008_);
lean_dec(v_val_1008_);
return v___x_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___boxed(lean_object* v_00_u03b1_1016_, lean_object* v_00_u03b2_1017_, lean_object* v_t_1018_, lean_object* v_p_1019_){
_start:
{
uint8_t v_res_1020_; lean_object* v_r_1021_; 
v_res_1020_ = l_Std_DTreeMap_Internal_Impl_all(v_00_u03b1_1016_, v_00_u03b2_1017_, v_t_1018_, v_p_1019_);
v_r_1021_ = lean_box(v_res_1020_);
return v_r_1021_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(lean_object* v_x1_1022_, lean_object* v_x2_1023_, lean_object* v_x3_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1025_, 0, v_x1_1022_);
lean_ctor_set(v___x_1025_, 1, v_x3_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0___boxed(lean_object* v_x1_1026_, lean_object* v_x2_1027_, lean_object* v_x3_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(v_x1_1026_, v_x2_1027_, v_x3_1028_);
lean_dec(v_x2_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg(lean_object* v_t_1031_){
_start:
{
lean_object* v___f_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___f_1032_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1033_ = lean_box(0);
v___x_1034_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1035_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1034_, v___f_1032_, v___x_1033_, v_t_1031_);
return v___x_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys(lean_object* v_00_u03b1_1036_, lean_object* v_00_u03b2_1037_, lean_object* v_t_1038_){
_start:
{
lean_object* v___f_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___f_1039_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1040_ = lean_box(0);
v___x_1041_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1041_, v___f_1039_, v___x_1040_, v_t_1038_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(lean_object* v_l_1043_, lean_object* v_k_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v___x_1046_; 
v___x_1046_ = lean_array_push(v_l_1043_, v_k_1044_);
return v___x_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0___boxed(lean_object* v_l_1047_, lean_object* v_k_1048_, lean_object* v_x_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(v_l_1047_, v_k_1048_, v_x_1049_);
lean_dec(v_x_1049_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg(lean_object* v_t_1052_){
_start:
{
lean_object* v___f_1053_; lean_object* v___y_1055_; 
v___f_1053_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1052_) == 0)
{
lean_object* v_size_1058_; 
v_size_1058_ = lean_ctor_get(v_t_1052_, 0);
lean_inc(v_size_1058_);
v___y_1055_ = v_size_1058_;
goto v___jp_1054_;
}
else
{
lean_object* v___x_1059_; 
v___x_1059_ = lean_unsigned_to_nat(0u);
v___y_1055_ = v___x_1059_;
goto v___jp_1054_;
}
v___jp_1054_:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = lean_mk_empty_array_with_capacity(v___y_1055_);
lean_dec(v___y_1055_);
v___x_1057_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1053_, v___x_1056_, v_t_1052_);
return v___x_1057_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray(lean_object* v_00_u03b1_1060_, lean_object* v_00_u03b2_1061_, lean_object* v_t_1062_){
_start:
{
lean_object* v___f_1063_; lean_object* v___y_1065_; 
v___f_1063_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1062_) == 0)
{
lean_object* v_size_1068_; 
v_size_1068_ = lean_ctor_get(v_t_1062_, 0);
lean_inc(v_size_1068_);
v___y_1065_ = v_size_1068_;
goto v___jp_1064_;
}
else
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_unsigned_to_nat(0u);
v___y_1065_ = v___x_1069_;
goto v___jp_1064_;
}
v___jp_1064_:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = lean_mk_empty_array_with_capacity(v___y_1065_);
lean_dec(v___y_1065_);
v___x_1067_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1063_, v___x_1066_, v_t_1062_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(lean_object* v_x1_1070_, lean_object* v_x2_1071_, lean_object* v_x3_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_x2_1071_);
lean_ctor_set(v___x_1073_, 1, v_x3_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0___boxed(lean_object* v_x1_1074_, lean_object* v_x2_1075_, lean_object* v_x3_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(v_x1_1074_, v_x2_1075_, v_x3_1076_);
lean_dec(v_x1_1074_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg(lean_object* v_t_1079_){
_start:
{
lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___f_1080_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1081_ = lean_box(0);
v___x_1082_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1083_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1082_, v___f_1080_, v___x_1081_, v_t_1079_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values(lean_object* v_00_u03b1_1084_, lean_object* v_00_u03b2_1085_, lean_object* v_t_1086_){
_start:
{
lean_object* v___f_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___f_1087_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1088_ = lean_box(0);
v___x_1089_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1090_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1089_, v___f_1087_, v___x_1088_, v_t_1086_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(lean_object* v_l_1091_, lean_object* v_x_1092_, lean_object* v_v_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_array_push(v_l_1091_, v_v_1093_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0___boxed(lean_object* v_l_1095_, lean_object* v_x_1096_, lean_object* v_v_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(v_l_1095_, v_x_1096_, v_v_1097_);
lean_dec(v_x_1096_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg(lean_object* v_t_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___y_1103_; 
v___f_1101_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1100_) == 0)
{
lean_object* v_size_1106_; 
v_size_1106_ = lean_ctor_get(v_t_1100_, 0);
lean_inc(v_size_1106_);
v___y_1103_ = v_size_1106_;
goto v___jp_1102_;
}
else
{
lean_object* v___x_1107_; 
v___x_1107_ = lean_unsigned_to_nat(0u);
v___y_1103_ = v___x_1107_;
goto v___jp_1102_;
}
v___jp_1102_:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1104_ = lean_mk_empty_array_with_capacity(v___y_1103_);
lean_dec(v___y_1103_);
v___x_1105_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1101_, v___x_1104_, v_t_1100_);
return v___x_1105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray(lean_object* v_00_u03b1_1108_, lean_object* v_00_u03b2_1109_, lean_object* v_t_1110_){
_start:
{
lean_object* v___f_1111_; lean_object* v___y_1113_; 
v___f_1111_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1110_) == 0)
{
lean_object* v_size_1116_; 
v_size_1116_ = lean_ctor_get(v_t_1110_, 0);
lean_inc(v_size_1116_);
v___y_1113_ = v_size_1116_;
goto v___jp_1112_;
}
else
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_unsigned_to_nat(0u);
v___y_1113_ = v___x_1117_;
goto v___jp_1112_;
}
v___jp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_mk_empty_array_with_capacity(v___y_1113_);
lean_dec(v___y_1113_);
v___x_1115_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1111_, v___x_1114_, v_t_1110_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg___lam__0(lean_object* v_x1_1118_, lean_object* v_x2_1119_, lean_object* v_x3_1120_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_x1_1118_);
lean_ctor_set(v___x_1121_, 1, v_x2_1119_);
v___x_1122_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1122_, 0, v___x_1121_);
lean_ctor_set(v___x_1122_, 1, v_x3_1120_);
return v___x_1122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg(lean_object* v_t_1124_){
_start:
{
lean_object* v___f_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___f_1125_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1126_ = lean_box(0);
v___x_1127_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1128_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1127_, v___f_1125_, v___x_1126_, v_t_1124_);
return v___x_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList(lean_object* v_00_u03b1_1129_, lean_object* v_00_u03b2_1130_, lean_object* v_t_1131_){
_start:
{
lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___f_1132_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1133_ = lean_box(0);
v___x_1134_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1135_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1134_, v___f_1132_, v___x_1133_, v_t_1131_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg___lam__0(lean_object* v_l_1136_, lean_object* v_k_1137_, lean_object* v_v_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_k_1137_);
lean_ctor_set(v___x_1139_, 1, v_v_1138_);
v___x_1140_ = lean_array_push(v_l_1136_, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg(lean_object* v_t_1142_){
_start:
{
lean_object* v___f_1143_; lean_object* v___y_1145_; 
v___f_1143_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1142_) == 0)
{
lean_object* v_size_1148_; 
v_size_1148_ = lean_ctor_get(v_t_1142_, 0);
lean_inc(v_size_1148_);
v___y_1145_ = v_size_1148_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1149_; 
v___x_1149_ = lean_unsigned_to_nat(0u);
v___y_1145_ = v___x_1149_;
goto v___jp_1144_;
}
v___jp_1144_:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = lean_mk_empty_array_with_capacity(v___y_1145_);
lean_dec(v___y_1145_);
v___x_1147_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1143_, v___x_1146_, v_t_1142_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray(lean_object* v_00_u03b1_1150_, lean_object* v_00_u03b2_1151_, lean_object* v_t_1152_){
_start:
{
lean_object* v___f_1153_; lean_object* v___y_1155_; 
v___f_1153_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1152_) == 0)
{
lean_object* v_size_1158_; 
v_size_1158_ = lean_ctor_get(v_t_1152_, 0);
lean_inc(v_size_1158_);
v___y_1155_ = v_size_1158_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1159_; 
v___x_1159_ = lean_unsigned_to_nat(0u);
v___y_1155_ = v___x_1159_;
goto v___jp_1154_;
}
v___jp_1154_:
{
lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1156_ = lean_mk_empty_array_with_capacity(v___y_1155_);
lean_dec(v___y_1155_);
v___x_1157_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1153_, v___x_1156_, v_t_1152_);
return v___x_1157_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___lam__0(lean_object* v_x1_1160_, lean_object* v_x2_1161_, lean_object* v_x3_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; 
v___x_1163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1163_, 0, v_x1_1160_);
lean_ctor_set(v___x_1163_, 1, v_x2_1161_);
v___x_1164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1164_, 0, v___x_1163_);
lean_ctor_set(v___x_1164_, 1, v_x3_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg(lean_object* v_t_1166_){
_start:
{
lean_object* v___f_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___f_1167_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1168_ = lean_box(0);
v___x_1169_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1170_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1169_, v___f_1167_, v___x_1168_, v_t_1166_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList(lean_object* v_00_u03b1_1171_, lean_object* v_00_u03b2_1172_, lean_object* v_t_1173_){
_start:
{
lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___f_1174_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1175_ = lean_box(0);
v___x_1176_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1177_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1176_, v___f_1174_, v___x_1175_, v_t_1173_);
return v___x_1177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___lam__0(lean_object* v_l_1178_, lean_object* v_k_1179_, lean_object* v_v_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1181_, 0, v_k_1179_);
lean_ctor_set(v___x_1181_, 1, v_v_1180_);
v___x_1182_ = lean_array_push(v_l_1178_, v___x_1181_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg(lean_object* v_t_1184_){
_start:
{
lean_object* v___f_1185_; lean_object* v___y_1187_; 
v___f_1185_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1184_) == 0)
{
lean_object* v_size_1190_; 
v_size_1190_ = lean_ctor_get(v_t_1184_, 0);
lean_inc(v_size_1190_);
v___y_1187_ = v_size_1190_;
goto v___jp_1186_;
}
else
{
lean_object* v___x_1191_; 
v___x_1191_ = lean_unsigned_to_nat(0u);
v___y_1187_ = v___x_1191_;
goto v___jp_1186_;
}
v___jp_1186_:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; 
v___x_1188_ = lean_mk_empty_array_with_capacity(v___y_1187_);
lean_dec(v___y_1187_);
v___x_1189_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1185_, v___x_1188_, v_t_1184_);
return v___x_1189_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray(lean_object* v_00_u03b1_1192_, lean_object* v_00_u03b2_1193_, lean_object* v_t_1194_){
_start:
{
lean_object* v___f_1195_; lean_object* v___y_1197_; 
v___f_1195_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1194_) == 0)
{
lean_object* v_size_1200_; 
v_size_1200_ = lean_ctor_get(v_t_1194_, 0);
lean_inc(v_size_1200_);
v___y_1197_ = v_size_1200_;
goto v___jp_1196_;
}
else
{
lean_object* v___x_1201_; 
v___x_1201_ = lean_unsigned_to_nat(0u);
v___y_1197_ = v___x_1201_;
goto v___jp_1196_;
}
v___jp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1198_ = lean_mk_empty_array_with_capacity(v___y_1197_);
lean_dec(v___y_1197_);
v___x_1199_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1195_, v___x_1198_, v_t_1194_);
return v___x_1199_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object* v_x_1202_){
_start:
{
if (lean_obj_tag(v_x_1202_) == 0)
{
lean_object* v_l_1203_; 
v_l_1203_ = lean_ctor_get(v_x_1202_, 3);
if (lean_obj_tag(v_l_1203_) == 0)
{
v_x_1202_ = v_l_1203_;
goto _start;
}
else
{
lean_object* v_k_1205_; lean_object* v_v_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v_k_1205_ = lean_ctor_get(v_x_1202_, 1);
v_v_1206_ = lean_ctor_get(v_x_1202_, 2);
lean_inc(v_v_1206_);
lean_inc(v_k_1205_);
v___x_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1207_, 0, v_k_1205_);
lean_ctor_set(v___x_1207_, 1, v_v_1206_);
v___x_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
return v___x_1208_;
}
}
else
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_box(0);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg___boxed(lean_object* v_x_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1210_);
lean_dec(v_x_1210_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f(lean_object* v_00_u03b1_1212_, lean_object* v_00_u03b2_1213_, lean_object* v_x_1214_){
_start:
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1214_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___boxed(lean_object* v_00_u03b1_1216_, lean_object* v_00_u03b2_1217_, lean_object* v_x_1218_){
_start:
{
lean_object* v_res_1219_; 
v_res_1219_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f(v_00_u03b1_1216_, v_00_u03b2_1217_, v_x_1218_);
lean_dec(v_x_1218_);
return v_res_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1220_, lean_object* v_h__1_1221_, lean_object* v_h__2_1222_, lean_object* v_h__3_1223_){
_start:
{
if (lean_obj_tag(v_x_1220_) == 0)
{
lean_object* v_l_1224_; 
lean_dec(v_h__1_1221_);
v_l_1224_ = lean_ctor_get(v_x_1220_, 3);
if (lean_obj_tag(v_l_1224_) == 0)
{
lean_object* v_size_1225_; lean_object* v_k_1226_; lean_object* v_v_1227_; lean_object* v_r_1228_; lean_object* v_size_1229_; lean_object* v_k_1230_; lean_object* v_v_1231_; lean_object* v_l_1232_; lean_object* v_r_1233_; lean_object* v___x_1234_; 
lean_inc_ref(v_l_1224_);
lean_dec(v_h__2_1222_);
v_size_1225_ = lean_ctor_get(v_x_1220_, 0);
lean_inc(v_size_1225_);
v_k_1226_ = lean_ctor_get(v_x_1220_, 1);
lean_inc(v_k_1226_);
v_v_1227_ = lean_ctor_get(v_x_1220_, 2);
lean_inc(v_v_1227_);
v_r_1228_ = lean_ctor_get(v_x_1220_, 4);
lean_inc(v_r_1228_);
lean_dec_ref(v_x_1220_);
v_size_1229_ = lean_ctor_get(v_l_1224_, 0);
lean_inc(v_size_1229_);
v_k_1230_ = lean_ctor_get(v_l_1224_, 1);
lean_inc(v_k_1230_);
v_v_1231_ = lean_ctor_get(v_l_1224_, 2);
lean_inc(v_v_1231_);
v_l_1232_ = lean_ctor_get(v_l_1224_, 3);
lean_inc(v_l_1232_);
v_r_1233_ = lean_ctor_get(v_l_1224_, 4);
lean_inc(v_r_1233_);
lean_dec_ref(v_l_1224_);
v___x_1234_ = lean_apply_9(v_h__3_1223_, v_size_1225_, v_k_1226_, v_v_1227_, v_size_1229_, v_k_1230_, v_v_1231_, v_l_1232_, v_r_1233_, v_r_1228_);
return v___x_1234_;
}
else
{
lean_object* v_size_1235_; lean_object* v_k_1236_; lean_object* v_v_1237_; lean_object* v_r_1238_; lean_object* v___x_1239_; 
lean_dec(v_h__3_1223_);
v_size_1235_ = lean_ctor_get(v_x_1220_, 0);
lean_inc(v_size_1235_);
v_k_1236_ = lean_ctor_get(v_x_1220_, 1);
lean_inc(v_k_1236_);
v_v_1237_ = lean_ctor_get(v_x_1220_, 2);
lean_inc(v_v_1237_);
v_r_1238_ = lean_ctor_get(v_x_1220_, 4);
lean_inc(v_r_1238_);
lean_dec_ref(v_x_1220_);
v___x_1239_ = lean_apply_4(v_h__2_1222_, v_size_1235_, v_k_1236_, v_v_1237_, v_r_1238_);
return v___x_1239_;
}
}
else
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
lean_dec(v_h__3_1223_);
lean_dec(v_h__2_1222_);
v___x_1240_ = lean_box(0);
v___x_1241_ = lean_apply_1(v_h__1_1221_, v___x_1240_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1242_, lean_object* v_00_u03b2_1243_, lean_object* v_motive_1244_, lean_object* v_x_1245_, lean_object* v_h__1_1246_, lean_object* v_h__2_1247_, lean_object* v_h__3_1248_){
_start:
{
if (lean_obj_tag(v_x_1245_) == 0)
{
lean_object* v_l_1249_; 
lean_dec(v_h__1_1246_);
v_l_1249_ = lean_ctor_get(v_x_1245_, 3);
if (lean_obj_tag(v_l_1249_) == 0)
{
lean_object* v_size_1250_; lean_object* v_k_1251_; lean_object* v_v_1252_; lean_object* v_r_1253_; lean_object* v_size_1254_; lean_object* v_k_1255_; lean_object* v_v_1256_; lean_object* v_l_1257_; lean_object* v_r_1258_; lean_object* v___x_1259_; 
lean_inc_ref(v_l_1249_);
lean_dec(v_h__2_1247_);
v_size_1250_ = lean_ctor_get(v_x_1245_, 0);
lean_inc(v_size_1250_);
v_k_1251_ = lean_ctor_get(v_x_1245_, 1);
lean_inc(v_k_1251_);
v_v_1252_ = lean_ctor_get(v_x_1245_, 2);
lean_inc(v_v_1252_);
v_r_1253_ = lean_ctor_get(v_x_1245_, 4);
lean_inc(v_r_1253_);
lean_dec_ref(v_x_1245_);
v_size_1254_ = lean_ctor_get(v_l_1249_, 0);
lean_inc(v_size_1254_);
v_k_1255_ = lean_ctor_get(v_l_1249_, 1);
lean_inc(v_k_1255_);
v_v_1256_ = lean_ctor_get(v_l_1249_, 2);
lean_inc(v_v_1256_);
v_l_1257_ = lean_ctor_get(v_l_1249_, 3);
lean_inc(v_l_1257_);
v_r_1258_ = lean_ctor_get(v_l_1249_, 4);
lean_inc(v_r_1258_);
lean_dec_ref(v_l_1249_);
v___x_1259_ = lean_apply_9(v_h__3_1248_, v_size_1250_, v_k_1251_, v_v_1252_, v_size_1254_, v_k_1255_, v_v_1256_, v_l_1257_, v_r_1258_, v_r_1253_);
return v___x_1259_;
}
else
{
lean_object* v_size_1260_; lean_object* v_k_1261_; lean_object* v_v_1262_; lean_object* v_r_1263_; lean_object* v___x_1264_; 
lean_dec(v_h__3_1248_);
v_size_1260_ = lean_ctor_get(v_x_1245_, 0);
lean_inc(v_size_1260_);
v_k_1261_ = lean_ctor_get(v_x_1245_, 1);
lean_inc(v_k_1261_);
v_v_1262_ = lean_ctor_get(v_x_1245_, 2);
lean_inc(v_v_1262_);
v_r_1263_ = lean_ctor_get(v_x_1245_, 4);
lean_inc(v_r_1263_);
lean_dec_ref(v_x_1245_);
v___x_1264_ = lean_apply_4(v_h__2_1247_, v_size_1260_, v_k_1261_, v_v_1262_, v_r_1263_);
return v___x_1264_;
}
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_dec(v_h__3_1248_);
lean_dec(v_h__2_1247_);
v___x_1265_ = lean_box(0);
v___x_1266_ = lean_apply_1(v_h__1_1246_, v___x_1265_);
return v___x_1266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg(lean_object* v_x_1267_){
_start:
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
lean_object* v_k_1270_; lean_object* v_v_1271_; lean_object* v___x_1272_; 
v_k_1270_ = lean_ctor_get(v_x_1267_, 1);
v_v_1271_ = lean_ctor_get(v_x_1267_, 2);
lean_inc(v_v_1271_);
lean_inc(v_k_1270_);
v___x_1272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_k_1270_);
lean_ctor_set(v___x_1272_, 1, v_v_1271_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg___boxed(lean_object* v_x_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1273_);
lean_dec(v_x_1273_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry(lean_object* v_00_u03b1_1275_, lean_object* v_00_u03b2_1276_, lean_object* v_x_1277_, lean_object* v_x_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1277_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___boxed(lean_object* v_00_u03b1_1280_, lean_object* v_00_u03b2_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_DTreeMap_Internal_Impl_minEntry(v_00_u03b1_1280_, v_00_u03b2_1281_, v_x_1282_, v_x_1283_);
lean_dec(v_x_1282_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1285_, lean_object* v_h__1_1286_, lean_object* v_h__2_1287_){
_start:
{
lean_object* v_l_1288_; 
v_l_1288_ = lean_ctor_get(v_x_1285_, 3);
if (lean_obj_tag(v_l_1288_) == 0)
{
lean_object* v_size_1289_; lean_object* v_k_1290_; lean_object* v_v_1291_; lean_object* v_r_1292_; lean_object* v_size_1293_; lean_object* v_k_1294_; lean_object* v_v_1295_; lean_object* v_l_1296_; lean_object* v_r_1297_; lean_object* v___x_1298_; 
lean_inc_ref(v_l_1288_);
lean_dec(v_h__1_1286_);
v_size_1289_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_size_1289_);
v_k_1290_ = lean_ctor_get(v_x_1285_, 1);
lean_inc(v_k_1290_);
v_v_1291_ = lean_ctor_get(v_x_1285_, 2);
lean_inc(v_v_1291_);
v_r_1292_ = lean_ctor_get(v_x_1285_, 4);
lean_inc(v_r_1292_);
lean_dec(v_x_1285_);
v_size_1293_ = lean_ctor_get(v_l_1288_, 0);
lean_inc(v_size_1293_);
v_k_1294_ = lean_ctor_get(v_l_1288_, 1);
lean_inc(v_k_1294_);
v_v_1295_ = lean_ctor_get(v_l_1288_, 2);
lean_inc(v_v_1295_);
v_l_1296_ = lean_ctor_get(v_l_1288_, 3);
lean_inc(v_l_1296_);
v_r_1297_ = lean_ctor_get(v_l_1288_, 4);
lean_inc(v_r_1297_);
lean_dec_ref(v_l_1288_);
v___x_1298_ = lean_apply_10(v_h__2_1287_, v_size_1289_, v_k_1290_, v_v_1291_, v_size_1293_, v_k_1294_, v_v_1295_, v_l_1296_, v_r_1297_, v_r_1292_, lean_box(0));
return v___x_1298_;
}
else
{
lean_object* v_size_1299_; lean_object* v_k_1300_; lean_object* v_v_1301_; lean_object* v_r_1302_; lean_object* v___x_1303_; 
lean_dec(v_h__2_1287_);
v_size_1299_ = lean_ctor_get(v_x_1285_, 0);
lean_inc(v_size_1299_);
v_k_1300_ = lean_ctor_get(v_x_1285_, 1);
lean_inc(v_k_1300_);
v_v_1301_ = lean_ctor_get(v_x_1285_, 2);
lean_inc(v_v_1301_);
v_r_1302_ = lean_ctor_get(v_x_1285_, 4);
lean_inc(v_r_1302_);
lean_dec(v_x_1285_);
v___x_1303_ = lean_apply_5(v_h__1_1286_, v_size_1299_, v_k_1300_, v_v_1301_, v_r_1302_, lean_box(0));
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_motive_1306_, lean_object* v_x_1307_, lean_object* v_x_1308_, lean_object* v_h__1_1309_, lean_object* v_h__2_1310_){
_start:
{
lean_object* v_l_1311_; 
v_l_1311_ = lean_ctor_get(v_x_1307_, 3);
if (lean_obj_tag(v_l_1311_) == 0)
{
lean_object* v_size_1312_; lean_object* v_k_1313_; lean_object* v_v_1314_; lean_object* v_r_1315_; lean_object* v_size_1316_; lean_object* v_k_1317_; lean_object* v_v_1318_; lean_object* v_l_1319_; lean_object* v_r_1320_; lean_object* v___x_1321_; 
lean_inc_ref(v_l_1311_);
lean_dec(v_h__1_1309_);
v_size_1312_ = lean_ctor_get(v_x_1307_, 0);
lean_inc(v_size_1312_);
v_k_1313_ = lean_ctor_get(v_x_1307_, 1);
lean_inc(v_k_1313_);
v_v_1314_ = lean_ctor_get(v_x_1307_, 2);
lean_inc(v_v_1314_);
v_r_1315_ = lean_ctor_get(v_x_1307_, 4);
lean_inc(v_r_1315_);
lean_dec(v_x_1307_);
v_size_1316_ = lean_ctor_get(v_l_1311_, 0);
lean_inc(v_size_1316_);
v_k_1317_ = lean_ctor_get(v_l_1311_, 1);
lean_inc(v_k_1317_);
v_v_1318_ = lean_ctor_get(v_l_1311_, 2);
lean_inc(v_v_1318_);
v_l_1319_ = lean_ctor_get(v_l_1311_, 3);
lean_inc(v_l_1319_);
v_r_1320_ = lean_ctor_get(v_l_1311_, 4);
lean_inc(v_r_1320_);
lean_dec_ref(v_l_1311_);
v___x_1321_ = lean_apply_10(v_h__2_1310_, v_size_1312_, v_k_1313_, v_v_1314_, v_size_1316_, v_k_1317_, v_v_1318_, v_l_1319_, v_r_1320_, v_r_1315_, lean_box(0));
return v___x_1321_;
}
else
{
lean_object* v_size_1322_; lean_object* v_k_1323_; lean_object* v_v_1324_; lean_object* v_r_1325_; lean_object* v___x_1326_; 
lean_dec(v_h__2_1310_);
v_size_1322_ = lean_ctor_get(v_x_1307_, 0);
lean_inc(v_size_1322_);
v_k_1323_ = lean_ctor_get(v_x_1307_, 1);
lean_inc(v_k_1323_);
v_v_1324_ = lean_ctor_get(v_x_1307_, 2);
lean_inc(v_v_1324_);
v_r_1325_ = lean_ctor_get(v_x_1307_, 4);
lean_inc(v_r_1325_);
lean_dec(v_x_1307_);
v___x_1326_ = lean_apply_5(v_h__1_1309_, v_size_1322_, v_k_1323_, v_v_1324_, v_r_1325_, lean_box(0));
return v___x_1326_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v___x_1329_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1330_ = lean_unsigned_to_nat(13u);
v___x_1331_ = lean_unsigned_to_nat(367u);
v___x_1332_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0));
v___x_1333_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1334_ = l_mkPanicMessageWithDecl(v___x_1333_, v___x_1332_, v___x_1331_, v___x_1330_, v___x_1329_);
return v___x_1334_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object* v_inst_1335_, lean_object* v_x_1336_){
_start:
{
if (lean_obj_tag(v_x_1336_) == 0)
{
lean_object* v_l_1337_; 
v_l_1337_ = lean_ctor_get(v_x_1336_, 3);
if (lean_obj_tag(v_l_1337_) == 0)
{
v_x_1336_ = v_l_1337_;
goto _start;
}
else
{
lean_object* v_k_1339_; lean_object* v_v_1340_; lean_object* v___x_1341_; 
lean_dec_ref(v_inst_1335_);
v_k_1339_ = lean_ctor_get(v_x_1336_, 1);
v_v_1340_ = lean_ctor_get(v_x_1336_, 2);
lean_inc(v_v_1340_);
lean_inc(v_k_1339_);
v___x_1341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1341_, 0, v_k_1339_);
lean_ctor_set(v___x_1341_, 1, v_v_1340_);
return v___x_1341_;
}
}
else
{
lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1342_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2);
v___x_1343_ = l_panic___redArg(v_inst_1335_, v___x_1342_);
return v___x_1343_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___boxed(lean_object* v_inst_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1344_, v_x_1345_);
lean_dec(v_x_1345_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21(lean_object* v_00_u03b1_1347_, lean_object* v_00_u03b2_1348_, lean_object* v_inst_1349_, lean_object* v_x_1350_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1349_, v_x_1350_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___boxed(lean_object* v_00_u03b1_1352_, lean_object* v_00_u03b2_1353_, lean_object* v_inst_1354_, lean_object* v_x_1355_){
_start:
{
lean_object* v_res_1356_; 
v_res_1356_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21(v_00_u03b1_1352_, v_00_u03b2_1353_, v_inst_1354_, v_x_1355_);
lean_dec(v_x_1355_);
return v_res_1356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object* v_x_1357_, lean_object* v_x_1358_){
_start:
{
if (lean_obj_tag(v_x_1357_) == 0)
{
lean_object* v_l_1359_; 
v_l_1359_ = lean_ctor_get(v_x_1357_, 3);
if (lean_obj_tag(v_l_1359_) == 0)
{
v_x_1357_ = v_l_1359_;
goto _start;
}
else
{
lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v___x_1363_; 
v_k_1361_ = lean_ctor_get(v_x_1357_, 1);
v_v_1362_ = lean_ctor_get(v_x_1357_, 2);
lean_inc(v_v_1362_);
lean_inc(v_k_1361_);
v___x_1363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1363_, 0, v_k_1361_);
lean_ctor_set(v___x_1363_, 1, v_v_1362_);
return v___x_1363_;
}
}
else
{
lean_inc_ref(v_x_1358_);
return v_x_1358_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg___boxed(lean_object* v_x_1364_, lean_object* v_x_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1364_, v_x_1365_);
lean_dec_ref(v_x_1365_);
lean_dec(v_x_1364_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD(lean_object* v_00_u03b1_1367_, lean_object* v_00_u03b2_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_){
_start:
{
lean_object* v___x_1371_; 
v___x_1371_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1369_, v_x_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___boxed(lean_object* v_00_u03b1_1372_, lean_object* v_00_u03b2_1373_, lean_object* v_x_1374_, lean_object* v_x_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Std_DTreeMap_Internal_Impl_minEntryD(v_00_u03b1_1372_, v_00_u03b2_1373_, v_x_1374_, v_x_1375_);
lean_dec_ref(v_x_1375_);
lean_dec(v_x_1374_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1377_, lean_object* v_x_1378_, lean_object* v_h__1_1379_, lean_object* v_h__2_1380_, lean_object* v_h__3_1381_){
_start:
{
if (lean_obj_tag(v_x_1377_) == 0)
{
lean_object* v_l_1382_; 
lean_dec(v_h__1_1379_);
v_l_1382_ = lean_ctor_get(v_x_1377_, 3);
if (lean_obj_tag(v_l_1382_) == 0)
{
lean_object* v_size_1383_; lean_object* v_k_1384_; lean_object* v_v_1385_; lean_object* v_r_1386_; lean_object* v_size_1387_; lean_object* v_k_1388_; lean_object* v_v_1389_; lean_object* v_l_1390_; lean_object* v_r_1391_; lean_object* v___x_1392_; 
lean_inc_ref(v_l_1382_);
lean_dec(v_h__2_1380_);
v_size_1383_ = lean_ctor_get(v_x_1377_, 0);
lean_inc(v_size_1383_);
v_k_1384_ = lean_ctor_get(v_x_1377_, 1);
lean_inc(v_k_1384_);
v_v_1385_ = lean_ctor_get(v_x_1377_, 2);
lean_inc(v_v_1385_);
v_r_1386_ = lean_ctor_get(v_x_1377_, 4);
lean_inc(v_r_1386_);
lean_dec_ref(v_x_1377_);
v_size_1387_ = lean_ctor_get(v_l_1382_, 0);
lean_inc(v_size_1387_);
v_k_1388_ = lean_ctor_get(v_l_1382_, 1);
lean_inc(v_k_1388_);
v_v_1389_ = lean_ctor_get(v_l_1382_, 2);
lean_inc(v_v_1389_);
v_l_1390_ = lean_ctor_get(v_l_1382_, 3);
lean_inc(v_l_1390_);
v_r_1391_ = lean_ctor_get(v_l_1382_, 4);
lean_inc(v_r_1391_);
lean_dec_ref(v_l_1382_);
v___x_1392_ = lean_apply_10(v_h__3_1381_, v_size_1383_, v_k_1384_, v_v_1385_, v_size_1387_, v_k_1388_, v_v_1389_, v_l_1390_, v_r_1391_, v_r_1386_, v_x_1378_);
return v___x_1392_;
}
else
{
lean_object* v_size_1393_; lean_object* v_k_1394_; lean_object* v_v_1395_; lean_object* v_r_1396_; lean_object* v___x_1397_; 
lean_dec(v_h__3_1381_);
v_size_1393_ = lean_ctor_get(v_x_1377_, 0);
lean_inc(v_size_1393_);
v_k_1394_ = lean_ctor_get(v_x_1377_, 1);
lean_inc(v_k_1394_);
v_v_1395_ = lean_ctor_get(v_x_1377_, 2);
lean_inc(v_v_1395_);
v_r_1396_ = lean_ctor_get(v_x_1377_, 4);
lean_inc(v_r_1396_);
lean_dec_ref(v_x_1377_);
v___x_1397_ = lean_apply_5(v_h__2_1380_, v_size_1393_, v_k_1394_, v_v_1395_, v_r_1396_, v_x_1378_);
return v___x_1397_;
}
}
else
{
lean_object* v___x_1398_; 
lean_dec(v_h__3_1381_);
lean_dec(v_h__2_1380_);
v___x_1398_ = lean_apply_1(v_h__1_1379_, v_x_1378_);
return v___x_1398_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1399_, lean_object* v_00_u03b2_1400_, lean_object* v_motive_1401_, lean_object* v_x_1402_, lean_object* v_x_1403_, lean_object* v_h__1_1404_, lean_object* v_h__2_1405_, lean_object* v_h__3_1406_){
_start:
{
if (lean_obj_tag(v_x_1402_) == 0)
{
lean_object* v_l_1407_; 
lean_dec(v_h__1_1404_);
v_l_1407_ = lean_ctor_get(v_x_1402_, 3);
if (lean_obj_tag(v_l_1407_) == 0)
{
lean_object* v_size_1408_; lean_object* v_k_1409_; lean_object* v_v_1410_; lean_object* v_r_1411_; lean_object* v_size_1412_; lean_object* v_k_1413_; lean_object* v_v_1414_; lean_object* v_l_1415_; lean_object* v_r_1416_; lean_object* v___x_1417_; 
lean_inc_ref(v_l_1407_);
lean_dec(v_h__2_1405_);
v_size_1408_ = lean_ctor_get(v_x_1402_, 0);
lean_inc(v_size_1408_);
v_k_1409_ = lean_ctor_get(v_x_1402_, 1);
lean_inc(v_k_1409_);
v_v_1410_ = lean_ctor_get(v_x_1402_, 2);
lean_inc(v_v_1410_);
v_r_1411_ = lean_ctor_get(v_x_1402_, 4);
lean_inc(v_r_1411_);
lean_dec_ref(v_x_1402_);
v_size_1412_ = lean_ctor_get(v_l_1407_, 0);
lean_inc(v_size_1412_);
v_k_1413_ = lean_ctor_get(v_l_1407_, 1);
lean_inc(v_k_1413_);
v_v_1414_ = lean_ctor_get(v_l_1407_, 2);
lean_inc(v_v_1414_);
v_l_1415_ = lean_ctor_get(v_l_1407_, 3);
lean_inc(v_l_1415_);
v_r_1416_ = lean_ctor_get(v_l_1407_, 4);
lean_inc(v_r_1416_);
lean_dec_ref(v_l_1407_);
v___x_1417_ = lean_apply_10(v_h__3_1406_, v_size_1408_, v_k_1409_, v_v_1410_, v_size_1412_, v_k_1413_, v_v_1414_, v_l_1415_, v_r_1416_, v_r_1411_, v_x_1403_);
return v___x_1417_;
}
else
{
lean_object* v_size_1418_; lean_object* v_k_1419_; lean_object* v_v_1420_; lean_object* v_r_1421_; lean_object* v___x_1422_; 
lean_dec(v_h__3_1406_);
v_size_1418_ = lean_ctor_get(v_x_1402_, 0);
lean_inc(v_size_1418_);
v_k_1419_ = lean_ctor_get(v_x_1402_, 1);
lean_inc(v_k_1419_);
v_v_1420_ = lean_ctor_get(v_x_1402_, 2);
lean_inc(v_v_1420_);
v_r_1421_ = lean_ctor_get(v_x_1402_, 4);
lean_inc(v_r_1421_);
lean_dec_ref(v_x_1402_);
v___x_1422_ = lean_apply_5(v_h__2_1405_, v_size_1418_, v_k_1419_, v_v_1420_, v_r_1421_, v_x_1403_);
return v___x_1422_;
}
}
else
{
lean_object* v___x_1423_; 
lean_dec(v_h__3_1406_);
lean_dec(v_h__2_1405_);
v___x_1423_ = lean_apply_1(v_h__1_1404_, v_x_1403_);
return v___x_1423_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object* v_x_1424_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
lean_object* v_r_1425_; 
v_r_1425_ = lean_ctor_get(v_x_1424_, 4);
if (lean_obj_tag(v_r_1425_) == 0)
{
v_x_1424_ = v_r_1425_;
goto _start;
}
else
{
lean_object* v_k_1427_; lean_object* v_v_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v_k_1427_ = lean_ctor_get(v_x_1424_, 1);
v_v_1428_ = lean_ctor_get(v_x_1424_, 2);
lean_inc(v_v_1428_);
lean_inc(v_k_1427_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v_k_1427_);
lean_ctor_set(v___x_1429_, 1, v_v_1428_);
v___x_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
return v___x_1430_;
}
}
else
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_box(0);
return v___x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg___boxed(lean_object* v_x_1432_){
_start:
{
lean_object* v_res_1433_; 
v_res_1433_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1432_);
lean_dec(v_x_1432_);
return v_res_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(lean_object* v_00_u03b1_1434_, lean_object* v_00_u03b2_1435_, lean_object* v_x_1436_){
_start:
{
lean_object* v___x_1437_; 
v___x_1437_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1436_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1438_, lean_object* v_00_u03b2_1439_, lean_object* v_x_1440_){
_start:
{
lean_object* v_res_1441_; 
v_res_1441_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(v_00_u03b1_1438_, v_00_u03b2_1439_, v_x_1440_);
lean_dec(v_x_1440_);
return v_res_1441_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1442_, lean_object* v_h__1_1443_, lean_object* v_h__2_1444_, lean_object* v_h__3_1445_){
_start:
{
if (lean_obj_tag(v_x_1442_) == 0)
{
lean_object* v_r_1446_; 
lean_dec(v_h__1_1443_);
v_r_1446_ = lean_ctor_get(v_x_1442_, 4);
if (lean_obj_tag(v_r_1446_) == 0)
{
lean_object* v_size_1447_; lean_object* v_k_1448_; lean_object* v_v_1449_; lean_object* v_l_1450_; lean_object* v_size_1451_; lean_object* v_k_1452_; lean_object* v_v_1453_; lean_object* v_l_1454_; lean_object* v_r_1455_; lean_object* v___x_1456_; 
lean_inc_ref(v_r_1446_);
lean_dec(v_h__2_1444_);
v_size_1447_ = lean_ctor_get(v_x_1442_, 0);
lean_inc(v_size_1447_);
v_k_1448_ = lean_ctor_get(v_x_1442_, 1);
lean_inc(v_k_1448_);
v_v_1449_ = lean_ctor_get(v_x_1442_, 2);
lean_inc(v_v_1449_);
v_l_1450_ = lean_ctor_get(v_x_1442_, 3);
lean_inc(v_l_1450_);
lean_dec_ref(v_x_1442_);
v_size_1451_ = lean_ctor_get(v_r_1446_, 0);
lean_inc(v_size_1451_);
v_k_1452_ = lean_ctor_get(v_r_1446_, 1);
lean_inc(v_k_1452_);
v_v_1453_ = lean_ctor_get(v_r_1446_, 2);
lean_inc(v_v_1453_);
v_l_1454_ = lean_ctor_get(v_r_1446_, 3);
lean_inc(v_l_1454_);
v_r_1455_ = lean_ctor_get(v_r_1446_, 4);
lean_inc(v_r_1455_);
lean_dec_ref(v_r_1446_);
v___x_1456_ = lean_apply_9(v_h__3_1445_, v_size_1447_, v_k_1448_, v_v_1449_, v_l_1450_, v_size_1451_, v_k_1452_, v_v_1453_, v_l_1454_, v_r_1455_);
return v___x_1456_;
}
else
{
lean_object* v_size_1457_; lean_object* v_k_1458_; lean_object* v_v_1459_; lean_object* v_l_1460_; lean_object* v___x_1461_; 
lean_dec(v_h__3_1445_);
v_size_1457_ = lean_ctor_get(v_x_1442_, 0);
lean_inc(v_size_1457_);
v_k_1458_ = lean_ctor_get(v_x_1442_, 1);
lean_inc(v_k_1458_);
v_v_1459_ = lean_ctor_get(v_x_1442_, 2);
lean_inc(v_v_1459_);
v_l_1460_ = lean_ctor_get(v_x_1442_, 3);
lean_inc(v_l_1460_);
lean_dec_ref(v_x_1442_);
v___x_1461_ = lean_apply_4(v_h__2_1444_, v_size_1457_, v_k_1458_, v_v_1459_, v_l_1460_);
return v___x_1461_;
}
}
else
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
lean_dec(v_h__3_1445_);
lean_dec(v_h__2_1444_);
v___x_1462_ = lean_box(0);
v___x_1463_ = lean_apply_1(v_h__1_1443_, v___x_1462_);
return v___x_1463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1464_, lean_object* v_00_u03b2_1465_, lean_object* v_motive_1466_, lean_object* v_x_1467_, lean_object* v_h__1_1468_, lean_object* v_h__2_1469_, lean_object* v_h__3_1470_){
_start:
{
if (lean_obj_tag(v_x_1467_) == 0)
{
lean_object* v_r_1471_; 
lean_dec(v_h__1_1468_);
v_r_1471_ = lean_ctor_get(v_x_1467_, 4);
if (lean_obj_tag(v_r_1471_) == 0)
{
lean_object* v_size_1472_; lean_object* v_k_1473_; lean_object* v_v_1474_; lean_object* v_l_1475_; lean_object* v_size_1476_; lean_object* v_k_1477_; lean_object* v_v_1478_; lean_object* v_l_1479_; lean_object* v_r_1480_; lean_object* v___x_1481_; 
lean_inc_ref(v_r_1471_);
lean_dec(v_h__2_1469_);
v_size_1472_ = lean_ctor_get(v_x_1467_, 0);
lean_inc(v_size_1472_);
v_k_1473_ = lean_ctor_get(v_x_1467_, 1);
lean_inc(v_k_1473_);
v_v_1474_ = lean_ctor_get(v_x_1467_, 2);
lean_inc(v_v_1474_);
v_l_1475_ = lean_ctor_get(v_x_1467_, 3);
lean_inc(v_l_1475_);
lean_dec_ref(v_x_1467_);
v_size_1476_ = lean_ctor_get(v_r_1471_, 0);
lean_inc(v_size_1476_);
v_k_1477_ = lean_ctor_get(v_r_1471_, 1);
lean_inc(v_k_1477_);
v_v_1478_ = lean_ctor_get(v_r_1471_, 2);
lean_inc(v_v_1478_);
v_l_1479_ = lean_ctor_get(v_r_1471_, 3);
lean_inc(v_l_1479_);
v_r_1480_ = lean_ctor_get(v_r_1471_, 4);
lean_inc(v_r_1480_);
lean_dec_ref(v_r_1471_);
v___x_1481_ = lean_apply_9(v_h__3_1470_, v_size_1472_, v_k_1473_, v_v_1474_, v_l_1475_, v_size_1476_, v_k_1477_, v_v_1478_, v_l_1479_, v_r_1480_);
return v___x_1481_;
}
else
{
lean_object* v_size_1482_; lean_object* v_k_1483_; lean_object* v_v_1484_; lean_object* v_l_1485_; lean_object* v___x_1486_; 
lean_dec(v_h__3_1470_);
v_size_1482_ = lean_ctor_get(v_x_1467_, 0);
lean_inc(v_size_1482_);
v_k_1483_ = lean_ctor_get(v_x_1467_, 1);
lean_inc(v_k_1483_);
v_v_1484_ = lean_ctor_get(v_x_1467_, 2);
lean_inc(v_v_1484_);
v_l_1485_ = lean_ctor_get(v_x_1467_, 3);
lean_inc(v_l_1485_);
lean_dec_ref(v_x_1467_);
v___x_1486_ = lean_apply_4(v_h__2_1469_, v_size_1482_, v_k_1483_, v_v_1484_, v_l_1485_);
return v___x_1486_;
}
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; 
lean_dec(v_h__3_1470_);
lean_dec(v_h__2_1469_);
v___x_1487_ = lean_box(0);
v___x_1488_ = lean_apply_1(v_h__1_1468_, v___x_1487_);
return v___x_1488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object* v_x_1489_){
_start:
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
lean_object* v_k_1492_; lean_object* v_v_1493_; lean_object* v___x_1494_; 
v_k_1492_ = lean_ctor_get(v_x_1489_, 1);
v_v_1493_ = lean_ctor_get(v_x_1489_, 2);
lean_inc(v_v_1493_);
lean_inc(v_k_1492_);
v___x_1494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1494_, 0, v_k_1492_);
lean_ctor_set(v___x_1494_, 1, v_v_1493_);
return v___x_1494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg___boxed(lean_object* v_x_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1495_);
lean_dec(v_x_1495_);
return v_res_1496_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry(lean_object* v_00_u03b1_1497_, lean_object* v_00_u03b2_1498_, lean_object* v_x_1499_, lean_object* v_x_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1499_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___boxed(lean_object* v_00_u03b1_1502_, lean_object* v_00_u03b2_1503_, lean_object* v_x_1504_, lean_object* v_x_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_DTreeMap_Internal_Impl_maxEntry(v_00_u03b1_1502_, v_00_u03b2_1503_, v_x_1504_, v_x_1505_);
lean_dec(v_x_1504_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1507_, lean_object* v_h__1_1508_, lean_object* v_h__2_1509_){
_start:
{
lean_object* v_r_1510_; 
v_r_1510_ = lean_ctor_get(v_x_1507_, 4);
if (lean_obj_tag(v_r_1510_) == 0)
{
lean_object* v_size_1511_; lean_object* v_k_1512_; lean_object* v_v_1513_; lean_object* v_l_1514_; lean_object* v_size_1515_; lean_object* v_k_1516_; lean_object* v_v_1517_; lean_object* v_l_1518_; lean_object* v_r_1519_; lean_object* v___x_1520_; 
lean_inc_ref(v_r_1510_);
lean_dec(v_h__1_1508_);
v_size_1511_ = lean_ctor_get(v_x_1507_, 0);
lean_inc(v_size_1511_);
v_k_1512_ = lean_ctor_get(v_x_1507_, 1);
lean_inc(v_k_1512_);
v_v_1513_ = lean_ctor_get(v_x_1507_, 2);
lean_inc(v_v_1513_);
v_l_1514_ = lean_ctor_get(v_x_1507_, 3);
lean_inc(v_l_1514_);
lean_dec(v_x_1507_);
v_size_1515_ = lean_ctor_get(v_r_1510_, 0);
lean_inc(v_size_1515_);
v_k_1516_ = lean_ctor_get(v_r_1510_, 1);
lean_inc(v_k_1516_);
v_v_1517_ = lean_ctor_get(v_r_1510_, 2);
lean_inc(v_v_1517_);
v_l_1518_ = lean_ctor_get(v_r_1510_, 3);
lean_inc(v_l_1518_);
v_r_1519_ = lean_ctor_get(v_r_1510_, 4);
lean_inc(v_r_1519_);
lean_dec_ref(v_r_1510_);
v___x_1520_ = lean_apply_10(v_h__2_1509_, v_size_1511_, v_k_1512_, v_v_1513_, v_l_1514_, v_size_1515_, v_k_1516_, v_v_1517_, v_l_1518_, v_r_1519_, lean_box(0));
return v___x_1520_;
}
else
{
lean_object* v_size_1521_; lean_object* v_k_1522_; lean_object* v_v_1523_; lean_object* v_l_1524_; lean_object* v___x_1525_; 
lean_dec(v_h__2_1509_);
v_size_1521_ = lean_ctor_get(v_x_1507_, 0);
lean_inc(v_size_1521_);
v_k_1522_ = lean_ctor_get(v_x_1507_, 1);
lean_inc(v_k_1522_);
v_v_1523_ = lean_ctor_get(v_x_1507_, 2);
lean_inc(v_v_1523_);
v_l_1524_ = lean_ctor_get(v_x_1507_, 3);
lean_inc(v_l_1524_);
lean_dec(v_x_1507_);
v___x_1525_ = lean_apply_5(v_h__1_1508_, v_size_1521_, v_k_1522_, v_v_1523_, v_l_1524_, lean_box(0));
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1526_, lean_object* v_00_u03b2_1527_, lean_object* v_motive_1528_, lean_object* v_x_1529_, lean_object* v_x_1530_, lean_object* v_h__1_1531_, lean_object* v_h__2_1532_){
_start:
{
lean_object* v_r_1533_; 
v_r_1533_ = lean_ctor_get(v_x_1529_, 4);
if (lean_obj_tag(v_r_1533_) == 0)
{
lean_object* v_size_1534_; lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v_l_1537_; lean_object* v_size_1538_; lean_object* v_k_1539_; lean_object* v_v_1540_; lean_object* v_l_1541_; lean_object* v_r_1542_; lean_object* v___x_1543_; 
lean_inc_ref(v_r_1533_);
lean_dec(v_h__1_1531_);
v_size_1534_ = lean_ctor_get(v_x_1529_, 0);
lean_inc(v_size_1534_);
v_k_1535_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_k_1535_);
v_v_1536_ = lean_ctor_get(v_x_1529_, 2);
lean_inc(v_v_1536_);
v_l_1537_ = lean_ctor_get(v_x_1529_, 3);
lean_inc(v_l_1537_);
lean_dec(v_x_1529_);
v_size_1538_ = lean_ctor_get(v_r_1533_, 0);
lean_inc(v_size_1538_);
v_k_1539_ = lean_ctor_get(v_r_1533_, 1);
lean_inc(v_k_1539_);
v_v_1540_ = lean_ctor_get(v_r_1533_, 2);
lean_inc(v_v_1540_);
v_l_1541_ = lean_ctor_get(v_r_1533_, 3);
lean_inc(v_l_1541_);
v_r_1542_ = lean_ctor_get(v_r_1533_, 4);
lean_inc(v_r_1542_);
lean_dec_ref(v_r_1533_);
v___x_1543_ = lean_apply_10(v_h__2_1532_, v_size_1534_, v_k_1535_, v_v_1536_, v_l_1537_, v_size_1538_, v_k_1539_, v_v_1540_, v_l_1541_, v_r_1542_, lean_box(0));
return v___x_1543_;
}
else
{
lean_object* v_size_1544_; lean_object* v_k_1545_; lean_object* v_v_1546_; lean_object* v_l_1547_; lean_object* v___x_1548_; 
lean_dec(v_h__2_1532_);
v_size_1544_ = lean_ctor_get(v_x_1529_, 0);
lean_inc(v_size_1544_);
v_k_1545_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_k_1545_);
v_v_1546_ = lean_ctor_get(v_x_1529_, 2);
lean_inc(v_v_1546_);
v_l_1547_ = lean_ctor_get(v_x_1529_, 3);
lean_inc(v_l_1547_);
lean_dec(v_x_1529_);
v___x_1548_ = lean_apply_5(v_h__1_1531_, v_size_1544_, v_k_1545_, v_v_1546_, v_l_1547_, lean_box(0));
return v___x_1548_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1550_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1551_ = lean_unsigned_to_nat(13u);
v___x_1552_ = lean_unsigned_to_nat(390u);
v___x_1553_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0));
v___x_1554_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1555_ = l_mkPanicMessageWithDecl(v___x_1554_, v___x_1553_, v___x_1552_, v___x_1551_, v___x_1550_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object* v_inst_1556_, lean_object* v_x_1557_){
_start:
{
if (lean_obj_tag(v_x_1557_) == 0)
{
lean_object* v_r_1558_; 
v_r_1558_ = lean_ctor_get(v_x_1557_, 4);
if (lean_obj_tag(v_r_1558_) == 0)
{
v_x_1557_ = v_r_1558_;
goto _start;
}
else
{
lean_object* v_k_1560_; lean_object* v_v_1561_; lean_object* v___x_1562_; 
lean_dec_ref(v_inst_1556_);
v_k_1560_ = lean_ctor_get(v_x_1557_, 1);
v_v_1561_ = lean_ctor_get(v_x_1557_, 2);
lean_inc(v_v_1561_);
lean_inc(v_k_1560_);
v___x_1562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1562_, 0, v_k_1560_);
lean_ctor_set(v___x_1562_, 1, v_v_1561_);
return v___x_1562_;
}
}
else
{
lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1563_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1);
v___x_1564_ = l_panic___redArg(v_inst_1556_, v___x_1563_);
return v___x_1564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___boxed(lean_object* v_inst_1565_, lean_object* v_x_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1565_, v_x_1566_);
lean_dec(v_x_1566_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21(lean_object* v_00_u03b1_1568_, lean_object* v_00_u03b2_1569_, lean_object* v_inst_1570_, lean_object* v_x_1571_){
_start:
{
lean_object* v___x_1572_; 
v___x_1572_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1570_, v_x_1571_);
return v___x_1572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___boxed(lean_object* v_00_u03b1_1573_, lean_object* v_00_u03b2_1574_, lean_object* v_inst_1575_, lean_object* v_x_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21(v_00_u03b1_1573_, v_00_u03b2_1574_, v_inst_1575_, v_x_1576_);
lean_dec(v_x_1576_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(lean_object* v_x_1578_, lean_object* v_x_1579_){
_start:
{
if (lean_obj_tag(v_x_1578_) == 0)
{
lean_object* v_r_1580_; 
v_r_1580_ = lean_ctor_get(v_x_1578_, 4);
if (lean_obj_tag(v_r_1580_) == 0)
{
v_x_1578_ = v_r_1580_;
goto _start;
}
else
{
lean_object* v_k_1582_; lean_object* v_v_1583_; lean_object* v___x_1584_; 
v_k_1582_ = lean_ctor_get(v_x_1578_, 1);
v_v_1583_ = lean_ctor_get(v_x_1578_, 2);
lean_inc(v_v_1583_);
lean_inc(v_k_1582_);
v___x_1584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1584_, 0, v_k_1582_);
lean_ctor_set(v___x_1584_, 1, v_v_1583_);
return v___x_1584_;
}
}
else
{
lean_inc_ref(v_x_1579_);
return v_x_1579_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg___boxed(lean_object* v_x_1585_, lean_object* v_x_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1585_, v_x_1586_);
lean_dec_ref(v_x_1586_);
lean_dec(v_x_1585_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD(lean_object* v_00_u03b1_1588_, lean_object* v_00_u03b2_1589_, lean_object* v_x_1590_, lean_object* v_x_1591_){
_start:
{
lean_object* v___x_1592_; 
v___x_1592_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1590_, v_x_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___boxed(lean_object* v_00_u03b1_1593_, lean_object* v_00_u03b2_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Std_DTreeMap_Internal_Impl_maxEntryD(v_00_u03b1_1593_, v_00_u03b2_1594_, v_x_1595_, v_x_1596_);
lean_dec_ref(v_x_1596_);
lean_dec(v_x_1595_);
return v_res_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1598_, lean_object* v_x_1599_, lean_object* v_h__1_1600_, lean_object* v_h__2_1601_, lean_object* v_h__3_1602_){
_start:
{
if (lean_obj_tag(v_x_1598_) == 0)
{
lean_object* v_r_1603_; 
lean_dec(v_h__1_1600_);
v_r_1603_ = lean_ctor_get(v_x_1598_, 4);
if (lean_obj_tag(v_r_1603_) == 0)
{
lean_object* v_size_1604_; lean_object* v_k_1605_; lean_object* v_v_1606_; lean_object* v_l_1607_; lean_object* v_size_1608_; lean_object* v_k_1609_; lean_object* v_v_1610_; lean_object* v_l_1611_; lean_object* v_r_1612_; lean_object* v___x_1613_; 
lean_inc_ref(v_r_1603_);
lean_dec(v_h__2_1601_);
v_size_1604_ = lean_ctor_get(v_x_1598_, 0);
lean_inc(v_size_1604_);
v_k_1605_ = lean_ctor_get(v_x_1598_, 1);
lean_inc(v_k_1605_);
v_v_1606_ = lean_ctor_get(v_x_1598_, 2);
lean_inc(v_v_1606_);
v_l_1607_ = lean_ctor_get(v_x_1598_, 3);
lean_inc(v_l_1607_);
lean_dec_ref(v_x_1598_);
v_size_1608_ = lean_ctor_get(v_r_1603_, 0);
lean_inc(v_size_1608_);
v_k_1609_ = lean_ctor_get(v_r_1603_, 1);
lean_inc(v_k_1609_);
v_v_1610_ = lean_ctor_get(v_r_1603_, 2);
lean_inc(v_v_1610_);
v_l_1611_ = lean_ctor_get(v_r_1603_, 3);
lean_inc(v_l_1611_);
v_r_1612_ = lean_ctor_get(v_r_1603_, 4);
lean_inc(v_r_1612_);
lean_dec_ref(v_r_1603_);
v___x_1613_ = lean_apply_10(v_h__3_1602_, v_size_1604_, v_k_1605_, v_v_1606_, v_l_1607_, v_size_1608_, v_k_1609_, v_v_1610_, v_l_1611_, v_r_1612_, v_x_1599_);
return v___x_1613_;
}
else
{
lean_object* v_size_1614_; lean_object* v_k_1615_; lean_object* v_v_1616_; lean_object* v_l_1617_; lean_object* v___x_1618_; 
lean_dec(v_h__3_1602_);
v_size_1614_ = lean_ctor_get(v_x_1598_, 0);
lean_inc(v_size_1614_);
v_k_1615_ = lean_ctor_get(v_x_1598_, 1);
lean_inc(v_k_1615_);
v_v_1616_ = lean_ctor_get(v_x_1598_, 2);
lean_inc(v_v_1616_);
v_l_1617_ = lean_ctor_get(v_x_1598_, 3);
lean_inc(v_l_1617_);
lean_dec_ref(v_x_1598_);
v___x_1618_ = lean_apply_5(v_h__2_1601_, v_size_1614_, v_k_1615_, v_v_1616_, v_l_1617_, v_x_1599_);
return v___x_1618_;
}
}
else
{
lean_object* v___x_1619_; 
lean_dec(v_h__3_1602_);
lean_dec(v_h__2_1601_);
v___x_1619_ = lean_apply_1(v_h__1_1600_, v_x_1599_);
return v___x_1619_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1620_, lean_object* v_00_u03b2_1621_, lean_object* v_motive_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v_h__1_1625_, lean_object* v_h__2_1626_, lean_object* v_h__3_1627_){
_start:
{
if (lean_obj_tag(v_x_1623_) == 0)
{
lean_object* v_r_1628_; 
lean_dec(v_h__1_1625_);
v_r_1628_ = lean_ctor_get(v_x_1623_, 4);
if (lean_obj_tag(v_r_1628_) == 0)
{
lean_object* v_size_1629_; lean_object* v_k_1630_; lean_object* v_v_1631_; lean_object* v_l_1632_; lean_object* v_size_1633_; lean_object* v_k_1634_; lean_object* v_v_1635_; lean_object* v_l_1636_; lean_object* v_r_1637_; lean_object* v___x_1638_; 
lean_inc_ref(v_r_1628_);
lean_dec(v_h__2_1626_);
v_size_1629_ = lean_ctor_get(v_x_1623_, 0);
lean_inc(v_size_1629_);
v_k_1630_ = lean_ctor_get(v_x_1623_, 1);
lean_inc(v_k_1630_);
v_v_1631_ = lean_ctor_get(v_x_1623_, 2);
lean_inc(v_v_1631_);
v_l_1632_ = lean_ctor_get(v_x_1623_, 3);
lean_inc(v_l_1632_);
lean_dec_ref(v_x_1623_);
v_size_1633_ = lean_ctor_get(v_r_1628_, 0);
lean_inc(v_size_1633_);
v_k_1634_ = lean_ctor_get(v_r_1628_, 1);
lean_inc(v_k_1634_);
v_v_1635_ = lean_ctor_get(v_r_1628_, 2);
lean_inc(v_v_1635_);
v_l_1636_ = lean_ctor_get(v_r_1628_, 3);
lean_inc(v_l_1636_);
v_r_1637_ = lean_ctor_get(v_r_1628_, 4);
lean_inc(v_r_1637_);
lean_dec_ref(v_r_1628_);
v___x_1638_ = lean_apply_10(v_h__3_1627_, v_size_1629_, v_k_1630_, v_v_1631_, v_l_1632_, v_size_1633_, v_k_1634_, v_v_1635_, v_l_1636_, v_r_1637_, v_x_1624_);
return v___x_1638_;
}
else
{
lean_object* v_size_1639_; lean_object* v_k_1640_; lean_object* v_v_1641_; lean_object* v_l_1642_; lean_object* v___x_1643_; 
lean_dec(v_h__3_1627_);
v_size_1639_ = lean_ctor_get(v_x_1623_, 0);
lean_inc(v_size_1639_);
v_k_1640_ = lean_ctor_get(v_x_1623_, 1);
lean_inc(v_k_1640_);
v_v_1641_ = lean_ctor_get(v_x_1623_, 2);
lean_inc(v_v_1641_);
v_l_1642_ = lean_ctor_get(v_x_1623_, 3);
lean_inc(v_l_1642_);
lean_dec_ref(v_x_1623_);
v___x_1643_ = lean_apply_5(v_h__2_1626_, v_size_1639_, v_k_1640_, v_v_1641_, v_l_1642_, v_x_1624_);
return v___x_1643_;
}
}
else
{
lean_object* v___x_1644_; 
lean_dec(v_h__3_1627_);
lean_dec(v_h__2_1626_);
v___x_1644_ = lean_apply_1(v_h__1_1625_, v_x_1624_);
return v___x_1644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object* v_x_1645_){
_start:
{
if (lean_obj_tag(v_x_1645_) == 0)
{
lean_object* v_l_1646_; 
v_l_1646_ = lean_ctor_get(v_x_1645_, 3);
if (lean_obj_tag(v_l_1646_) == 0)
{
v_x_1645_ = v_l_1646_;
goto _start;
}
else
{
lean_object* v_k_1648_; lean_object* v___x_1649_; 
v_k_1648_ = lean_ctor_get(v_x_1645_, 1);
lean_inc(v_k_1648_);
v___x_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1649_, 0, v_k_1648_);
return v___x_1649_;
}
}
else
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_box(0);
return v___x_1650_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg___boxed(lean_object* v_x_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1651_);
lean_dec(v_x_1651_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f(lean_object* v_00_u03b1_1653_, lean_object* v_00_u03b2_1654_, lean_object* v_x_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___boxed(lean_object* v_00_u03b1_1657_, lean_object* v_00_u03b2_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f(v_00_u03b1_1657_, v_00_u03b2_1658_, v_x_1659_);
lean_dec(v_x_1659_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object* v_x_1661_){
_start:
{
lean_object* v_l_1662_; 
v_l_1662_ = lean_ctor_get(v_x_1661_, 3);
if (lean_obj_tag(v_l_1662_) == 0)
{
v_x_1661_ = v_l_1662_;
goto _start;
}
else
{
lean_object* v_k_1664_; 
v_k_1664_ = lean_ctor_get(v_x_1661_, 1);
lean_inc(v_k_1664_);
return v_k_1664_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg___boxed(lean_object* v_x_1665_){
_start:
{
lean_object* v_res_1666_; 
v_res_1666_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1665_);
lean_dec(v_x_1665_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey(lean_object* v_00_u03b1_1667_, lean_object* v_00_u03b2_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_){
_start:
{
lean_object* v___x_1671_; 
v___x_1671_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1669_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___boxed(lean_object* v_00_u03b1_1672_, lean_object* v_00_u03b2_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l_Std_DTreeMap_Internal_Impl_minKey(v_00_u03b1_1672_, v_00_u03b2_1673_, v_x_1674_, v_x_1675_);
lean_dec(v_x_1674_);
return v_res_1676_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1678_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1679_ = lean_unsigned_to_nat(13u);
v___x_1680_ = lean_unsigned_to_nat(413u);
v___x_1681_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0));
v___x_1682_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1683_ = l_mkPanicMessageWithDecl(v___x_1682_, v___x_1681_, v___x_1680_, v___x_1679_, v___x_1678_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object* v_inst_1684_, lean_object* v_x_1685_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 0)
{
lean_object* v_l_1686_; 
v_l_1686_ = lean_ctor_get(v_x_1685_, 3);
if (lean_obj_tag(v_l_1686_) == 0)
{
v_x_1685_ = v_l_1686_;
goto _start;
}
else
{
lean_object* v_k_1688_; 
lean_dec(v_inst_1684_);
v_k_1688_ = lean_ctor_get(v_x_1685_, 1);
lean_inc(v_k_1688_);
return v_k_1688_;
}
}
else
{
lean_object* v___x_1689_; lean_object* v___x_1690_; 
v___x_1689_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1);
v___x_1690_ = l_panic___redArg(v_inst_1684_, v___x_1689_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___boxed(lean_object* v_inst_1691_, lean_object* v_x_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1691_, v_x_1692_);
lean_dec(v_x_1692_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21(lean_object* v_00_u03b1_1694_, lean_object* v_00_u03b2_1695_, lean_object* v_inst_1696_, lean_object* v_x_1697_){
_start:
{
lean_object* v___x_1698_; 
v___x_1698_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1696_, v_x_1697_);
return v___x_1698_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___boxed(lean_object* v_00_u03b1_1699_, lean_object* v_00_u03b2_1700_, lean_object* v_inst_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v_res_1703_; 
v_res_1703_ = l_Std_DTreeMap_Internal_Impl_minKey_x21(v_00_u03b1_1699_, v_00_u03b2_1700_, v_inst_1701_, v_x_1702_);
lean_dec(v_x_1702_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
if (lean_obj_tag(v_x_1704_) == 0)
{
lean_object* v_l_1706_; 
v_l_1706_ = lean_ctor_get(v_x_1704_, 3);
if (lean_obj_tag(v_l_1706_) == 0)
{
v_x_1704_ = v_l_1706_;
goto _start;
}
else
{
lean_object* v_k_1708_; 
v_k_1708_ = lean_ctor_get(v_x_1704_, 1);
lean_inc(v_k_1708_);
return v_k_1708_;
}
}
else
{
lean_inc(v_x_1705_);
return v_x_1705_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg___boxed(lean_object* v_x_1709_, lean_object* v_x_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1709_, v_x_1710_);
lean_dec(v_x_1710_);
lean_dec(v_x_1709_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD(lean_object* v_00_u03b1_1712_, lean_object* v_00_u03b2_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1714_, v_x_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___boxed(lean_object* v_00_u03b1_1717_, lean_object* v_00_u03b2_1718_, lean_object* v_x_1719_, lean_object* v_x_1720_){
_start:
{
lean_object* v_res_1721_; 
v_res_1721_ = l_Std_DTreeMap_Internal_Impl_minKeyD(v_00_u03b1_1717_, v_00_u03b2_1718_, v_x_1719_, v_x_1720_);
lean_dec(v_x_1720_);
lean_dec(v_x_1719_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1722_, lean_object* v_x_1723_, lean_object* v_h__1_1724_, lean_object* v_h__2_1725_, lean_object* v_h__3_1726_){
_start:
{
if (lean_obj_tag(v_x_1722_) == 0)
{
lean_object* v_l_1727_; 
lean_dec(v_h__1_1724_);
v_l_1727_ = lean_ctor_get(v_x_1722_, 3);
if (lean_obj_tag(v_l_1727_) == 0)
{
lean_object* v_size_1728_; lean_object* v_k_1729_; lean_object* v_v_1730_; lean_object* v_r_1731_; lean_object* v_size_1732_; lean_object* v_k_1733_; lean_object* v_v_1734_; lean_object* v_l_1735_; lean_object* v_r_1736_; lean_object* v___x_1737_; 
lean_inc_ref(v_l_1727_);
lean_dec(v_h__2_1725_);
v_size_1728_ = lean_ctor_get(v_x_1722_, 0);
lean_inc(v_size_1728_);
v_k_1729_ = lean_ctor_get(v_x_1722_, 1);
lean_inc(v_k_1729_);
v_v_1730_ = lean_ctor_get(v_x_1722_, 2);
lean_inc(v_v_1730_);
v_r_1731_ = lean_ctor_get(v_x_1722_, 4);
lean_inc(v_r_1731_);
lean_dec_ref(v_x_1722_);
v_size_1732_ = lean_ctor_get(v_l_1727_, 0);
lean_inc(v_size_1732_);
v_k_1733_ = lean_ctor_get(v_l_1727_, 1);
lean_inc(v_k_1733_);
v_v_1734_ = lean_ctor_get(v_l_1727_, 2);
lean_inc(v_v_1734_);
v_l_1735_ = lean_ctor_get(v_l_1727_, 3);
lean_inc(v_l_1735_);
v_r_1736_ = lean_ctor_get(v_l_1727_, 4);
lean_inc(v_r_1736_);
lean_dec_ref(v_l_1727_);
v___x_1737_ = lean_apply_10(v_h__3_1726_, v_size_1728_, v_k_1729_, v_v_1730_, v_size_1732_, v_k_1733_, v_v_1734_, v_l_1735_, v_r_1736_, v_r_1731_, v_x_1723_);
return v___x_1737_;
}
else
{
lean_object* v_size_1738_; lean_object* v_k_1739_; lean_object* v_v_1740_; lean_object* v_r_1741_; lean_object* v___x_1742_; 
lean_dec(v_h__3_1726_);
v_size_1738_ = lean_ctor_get(v_x_1722_, 0);
lean_inc(v_size_1738_);
v_k_1739_ = lean_ctor_get(v_x_1722_, 1);
lean_inc(v_k_1739_);
v_v_1740_ = lean_ctor_get(v_x_1722_, 2);
lean_inc(v_v_1740_);
v_r_1741_ = lean_ctor_get(v_x_1722_, 4);
lean_inc(v_r_1741_);
lean_dec_ref(v_x_1722_);
v___x_1742_ = lean_apply_5(v_h__2_1725_, v_size_1738_, v_k_1739_, v_v_1740_, v_r_1741_, v_x_1723_);
return v___x_1742_;
}
}
else
{
lean_object* v___x_1743_; 
lean_dec(v_h__3_1726_);
lean_dec(v_h__2_1725_);
v___x_1743_ = lean_apply_1(v_h__1_1724_, v_x_1723_);
return v___x_1743_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1744_, lean_object* v_00_u03b2_1745_, lean_object* v_motive_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_, lean_object* v_h__1_1749_, lean_object* v_h__2_1750_, lean_object* v_h__3_1751_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
lean_object* v_l_1752_; 
lean_dec(v_h__1_1749_);
v_l_1752_ = lean_ctor_get(v_x_1747_, 3);
if (lean_obj_tag(v_l_1752_) == 0)
{
lean_object* v_size_1753_; lean_object* v_k_1754_; lean_object* v_v_1755_; lean_object* v_r_1756_; lean_object* v_size_1757_; lean_object* v_k_1758_; lean_object* v_v_1759_; lean_object* v_l_1760_; lean_object* v_r_1761_; lean_object* v___x_1762_; 
lean_inc_ref(v_l_1752_);
lean_dec(v_h__2_1750_);
v_size_1753_ = lean_ctor_get(v_x_1747_, 0);
lean_inc(v_size_1753_);
v_k_1754_ = lean_ctor_get(v_x_1747_, 1);
lean_inc(v_k_1754_);
v_v_1755_ = lean_ctor_get(v_x_1747_, 2);
lean_inc(v_v_1755_);
v_r_1756_ = lean_ctor_get(v_x_1747_, 4);
lean_inc(v_r_1756_);
lean_dec_ref(v_x_1747_);
v_size_1757_ = lean_ctor_get(v_l_1752_, 0);
lean_inc(v_size_1757_);
v_k_1758_ = lean_ctor_get(v_l_1752_, 1);
lean_inc(v_k_1758_);
v_v_1759_ = lean_ctor_get(v_l_1752_, 2);
lean_inc(v_v_1759_);
v_l_1760_ = lean_ctor_get(v_l_1752_, 3);
lean_inc(v_l_1760_);
v_r_1761_ = lean_ctor_get(v_l_1752_, 4);
lean_inc(v_r_1761_);
lean_dec_ref(v_l_1752_);
v___x_1762_ = lean_apply_10(v_h__3_1751_, v_size_1753_, v_k_1754_, v_v_1755_, v_size_1757_, v_k_1758_, v_v_1759_, v_l_1760_, v_r_1761_, v_r_1756_, v_x_1748_);
return v___x_1762_;
}
else
{
lean_object* v_size_1763_; lean_object* v_k_1764_; lean_object* v_v_1765_; lean_object* v_r_1766_; lean_object* v___x_1767_; 
lean_dec(v_h__3_1751_);
v_size_1763_ = lean_ctor_get(v_x_1747_, 0);
lean_inc(v_size_1763_);
v_k_1764_ = lean_ctor_get(v_x_1747_, 1);
lean_inc(v_k_1764_);
v_v_1765_ = lean_ctor_get(v_x_1747_, 2);
lean_inc(v_v_1765_);
v_r_1766_ = lean_ctor_get(v_x_1747_, 4);
lean_inc(v_r_1766_);
lean_dec_ref(v_x_1747_);
v___x_1767_ = lean_apply_5(v_h__2_1750_, v_size_1763_, v_k_1764_, v_v_1765_, v_r_1766_, v_x_1748_);
return v___x_1767_;
}
}
else
{
lean_object* v___x_1768_; 
lean_dec(v_h__3_1751_);
lean_dec(v_h__2_1750_);
v___x_1768_ = lean_apply_1(v_h__1_1749_, v_x_1748_);
return v___x_1768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object* v_x_1769_){
_start:
{
if (lean_obj_tag(v_x_1769_) == 0)
{
lean_object* v_r_1770_; 
v_r_1770_ = lean_ctor_get(v_x_1769_, 4);
if (lean_obj_tag(v_r_1770_) == 0)
{
v_x_1769_ = v_r_1770_;
goto _start;
}
else
{
lean_object* v_k_1772_; lean_object* v___x_1773_; 
v_k_1772_ = lean_ctor_get(v_x_1769_, 1);
lean_inc(v_k_1772_);
v___x_1773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1773_, 0, v_k_1772_);
return v___x_1773_;
}
}
else
{
lean_object* v___x_1774_; 
v___x_1774_ = lean_box(0);
return v___x_1774_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg___boxed(lean_object* v_x_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1775_);
lean_dec(v_x_1775_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f(lean_object* v_00_u03b1_1777_, lean_object* v_00_u03b2_1778_, lean_object* v_x_1779_){
_start:
{
lean_object* v___x_1780_; 
v___x_1780_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1779_);
return v___x_1780_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___boxed(lean_object* v_00_u03b1_1781_, lean_object* v_00_u03b2_1782_, lean_object* v_x_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f(v_00_u03b1_1781_, v_00_u03b2_1782_, v_x_1783_);
lean_dec(v_x_1783_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object* v_x_1785_){
_start:
{
lean_object* v_r_1786_; 
v_r_1786_ = lean_ctor_get(v_x_1785_, 4);
if (lean_obj_tag(v_r_1786_) == 0)
{
v_x_1785_ = v_r_1786_;
goto _start;
}
else
{
lean_object* v_k_1788_; 
v_k_1788_ = lean_ctor_get(v_x_1785_, 1);
lean_inc(v_k_1788_);
return v_k_1788_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg___boxed(lean_object* v_x_1789_){
_start:
{
lean_object* v_res_1790_; 
v_res_1790_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1789_);
lean_dec(v_x_1789_);
return v_res_1790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey(lean_object* v_00_u03b1_1791_, lean_object* v_00_u03b2_1792_, lean_object* v_x_1793_, lean_object* v_x_1794_){
_start:
{
lean_object* v___x_1795_; 
v___x_1795_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1793_);
return v___x_1795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___boxed(lean_object* v_00_u03b1_1796_, lean_object* v_00_u03b2_1797_, lean_object* v_x_1798_, lean_object* v_x_1799_){
_start:
{
lean_object* v_res_1800_; 
v_res_1800_ = l_Std_DTreeMap_Internal_Impl_maxKey(v_00_u03b1_1796_, v_00_u03b2_1797_, v_x_1798_, v_x_1799_);
lean_dec(v_x_1798_);
return v_res_1800_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1802_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1803_ = lean_unsigned_to_nat(13u);
v___x_1804_ = lean_unsigned_to_nat(436u);
v___x_1805_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0));
v___x_1806_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1807_ = l_mkPanicMessageWithDecl(v___x_1806_, v___x_1805_, v___x_1804_, v___x_1803_, v___x_1802_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object* v_inst_1808_, lean_object* v_x_1809_){
_start:
{
if (lean_obj_tag(v_x_1809_) == 0)
{
lean_object* v_r_1810_; 
v_r_1810_ = lean_ctor_get(v_x_1809_, 4);
if (lean_obj_tag(v_r_1810_) == 0)
{
v_x_1809_ = v_r_1810_;
goto _start;
}
else
{
lean_object* v_k_1812_; 
lean_dec(v_inst_1808_);
v_k_1812_ = lean_ctor_get(v_x_1809_, 1);
lean_inc(v_k_1812_);
return v_k_1812_;
}
}
else
{
lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1813_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1);
v___x_1814_ = l_panic___redArg(v_inst_1808_, v___x_1813_);
return v___x_1814_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___boxed(lean_object* v_inst_1815_, lean_object* v_x_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1815_, v_x_1816_);
lean_dec(v_x_1816_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21(lean_object* v_00_u03b1_1818_, lean_object* v_00_u03b2_1819_, lean_object* v_inst_1820_, lean_object* v_x_1821_){
_start:
{
lean_object* v___x_1822_; 
v___x_1822_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1820_, v_x_1821_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___boxed(lean_object* v_00_u03b1_1823_, lean_object* v_00_u03b2_1824_, lean_object* v_inst_1825_, lean_object* v_x_1826_){
_start:
{
lean_object* v_res_1827_; 
v_res_1827_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21(v_00_u03b1_1823_, v_00_u03b2_1824_, v_inst_1825_, v_x_1826_);
lean_dec(v_x_1826_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object* v_x_1828_, lean_object* v_x_1829_){
_start:
{
if (lean_obj_tag(v_x_1828_) == 0)
{
lean_object* v_r_1830_; 
v_r_1830_ = lean_ctor_get(v_x_1828_, 4);
if (lean_obj_tag(v_r_1830_) == 0)
{
v_x_1828_ = v_r_1830_;
goto _start;
}
else
{
lean_object* v_k_1832_; 
v_k_1832_ = lean_ctor_get(v_x_1828_, 1);
lean_inc(v_k_1832_);
return v_k_1832_;
}
}
else
{
lean_inc(v_x_1829_);
return v_x_1829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg___boxed(lean_object* v_x_1833_, lean_object* v_x_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1833_, v_x_1834_);
lean_dec(v_x_1834_);
lean_dec(v_x_1833_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD(lean_object* v_00_u03b1_1836_, lean_object* v_00_u03b2_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1838_, v_x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___boxed(lean_object* v_00_u03b1_1841_, lean_object* v_00_u03b2_1842_, lean_object* v_x_1843_, lean_object* v_x_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Std_DTreeMap_Internal_Impl_maxKeyD(v_00_u03b1_1841_, v_00_u03b2_1842_, v_x_1843_, v_x_1844_);
lean_dec(v_x_1844_);
lean_dec(v_x_1843_);
return v_res_1845_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1846_, lean_object* v_x_1847_, lean_object* v_h__1_1848_, lean_object* v_h__2_1849_, lean_object* v_h__3_1850_){
_start:
{
if (lean_obj_tag(v_x_1846_) == 0)
{
lean_object* v_r_1851_; 
lean_dec(v_h__1_1848_);
v_r_1851_ = lean_ctor_get(v_x_1846_, 4);
if (lean_obj_tag(v_r_1851_) == 0)
{
lean_object* v_size_1852_; lean_object* v_k_1853_; lean_object* v_v_1854_; lean_object* v_l_1855_; lean_object* v_size_1856_; lean_object* v_k_1857_; lean_object* v_v_1858_; lean_object* v_l_1859_; lean_object* v_r_1860_; lean_object* v___x_1861_; 
lean_inc_ref(v_r_1851_);
lean_dec(v_h__2_1849_);
v_size_1852_ = lean_ctor_get(v_x_1846_, 0);
lean_inc(v_size_1852_);
v_k_1853_ = lean_ctor_get(v_x_1846_, 1);
lean_inc(v_k_1853_);
v_v_1854_ = lean_ctor_get(v_x_1846_, 2);
lean_inc(v_v_1854_);
v_l_1855_ = lean_ctor_get(v_x_1846_, 3);
lean_inc(v_l_1855_);
lean_dec_ref(v_x_1846_);
v_size_1856_ = lean_ctor_get(v_r_1851_, 0);
lean_inc(v_size_1856_);
v_k_1857_ = lean_ctor_get(v_r_1851_, 1);
lean_inc(v_k_1857_);
v_v_1858_ = lean_ctor_get(v_r_1851_, 2);
lean_inc(v_v_1858_);
v_l_1859_ = lean_ctor_get(v_r_1851_, 3);
lean_inc(v_l_1859_);
v_r_1860_ = lean_ctor_get(v_r_1851_, 4);
lean_inc(v_r_1860_);
lean_dec_ref(v_r_1851_);
v___x_1861_ = lean_apply_10(v_h__3_1850_, v_size_1852_, v_k_1853_, v_v_1854_, v_l_1855_, v_size_1856_, v_k_1857_, v_v_1858_, v_l_1859_, v_r_1860_, v_x_1847_);
return v___x_1861_;
}
else
{
lean_object* v_size_1862_; lean_object* v_k_1863_; lean_object* v_v_1864_; lean_object* v_l_1865_; lean_object* v___x_1866_; 
lean_dec(v_h__3_1850_);
v_size_1862_ = lean_ctor_get(v_x_1846_, 0);
lean_inc(v_size_1862_);
v_k_1863_ = lean_ctor_get(v_x_1846_, 1);
lean_inc(v_k_1863_);
v_v_1864_ = lean_ctor_get(v_x_1846_, 2);
lean_inc(v_v_1864_);
v_l_1865_ = lean_ctor_get(v_x_1846_, 3);
lean_inc(v_l_1865_);
lean_dec_ref(v_x_1846_);
v___x_1866_ = lean_apply_5(v_h__2_1849_, v_size_1862_, v_k_1863_, v_v_1864_, v_l_1865_, v_x_1847_);
return v___x_1866_;
}
}
else
{
lean_object* v___x_1867_; 
lean_dec(v_h__3_1850_);
lean_dec(v_h__2_1849_);
v___x_1867_ = lean_apply_1(v_h__1_1848_, v_x_1847_);
return v___x_1867_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1868_, lean_object* v_00_u03b2_1869_, lean_object* v_motive_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_, lean_object* v_h__1_1873_, lean_object* v_h__2_1874_, lean_object* v_h__3_1875_){
_start:
{
if (lean_obj_tag(v_x_1871_) == 0)
{
lean_object* v_r_1876_; 
lean_dec(v_h__1_1873_);
v_r_1876_ = lean_ctor_get(v_x_1871_, 4);
if (lean_obj_tag(v_r_1876_) == 0)
{
lean_object* v_size_1877_; lean_object* v_k_1878_; lean_object* v_v_1879_; lean_object* v_l_1880_; lean_object* v_size_1881_; lean_object* v_k_1882_; lean_object* v_v_1883_; lean_object* v_l_1884_; lean_object* v_r_1885_; lean_object* v___x_1886_; 
lean_inc_ref(v_r_1876_);
lean_dec(v_h__2_1874_);
v_size_1877_ = lean_ctor_get(v_x_1871_, 0);
lean_inc(v_size_1877_);
v_k_1878_ = lean_ctor_get(v_x_1871_, 1);
lean_inc(v_k_1878_);
v_v_1879_ = lean_ctor_get(v_x_1871_, 2);
lean_inc(v_v_1879_);
v_l_1880_ = lean_ctor_get(v_x_1871_, 3);
lean_inc(v_l_1880_);
lean_dec_ref(v_x_1871_);
v_size_1881_ = lean_ctor_get(v_r_1876_, 0);
lean_inc(v_size_1881_);
v_k_1882_ = lean_ctor_get(v_r_1876_, 1);
lean_inc(v_k_1882_);
v_v_1883_ = lean_ctor_get(v_r_1876_, 2);
lean_inc(v_v_1883_);
v_l_1884_ = lean_ctor_get(v_r_1876_, 3);
lean_inc(v_l_1884_);
v_r_1885_ = lean_ctor_get(v_r_1876_, 4);
lean_inc(v_r_1885_);
lean_dec_ref(v_r_1876_);
v___x_1886_ = lean_apply_10(v_h__3_1875_, v_size_1877_, v_k_1878_, v_v_1879_, v_l_1880_, v_size_1881_, v_k_1882_, v_v_1883_, v_l_1884_, v_r_1885_, v_x_1872_);
return v___x_1886_;
}
else
{
lean_object* v_size_1887_; lean_object* v_k_1888_; lean_object* v_v_1889_; lean_object* v_l_1890_; lean_object* v___x_1891_; 
lean_dec(v_h__3_1875_);
v_size_1887_ = lean_ctor_get(v_x_1871_, 0);
lean_inc(v_size_1887_);
v_k_1888_ = lean_ctor_get(v_x_1871_, 1);
lean_inc(v_k_1888_);
v_v_1889_ = lean_ctor_get(v_x_1871_, 2);
lean_inc(v_v_1889_);
v_l_1890_ = lean_ctor_get(v_x_1871_, 3);
lean_inc(v_l_1890_);
lean_dec_ref(v_x_1871_);
v___x_1891_ = lean_apply_5(v_h__2_1874_, v_size_1887_, v_k_1888_, v_v_1889_, v_l_1890_, v_x_1872_);
return v___x_1891_;
}
}
else
{
lean_object* v___x_1892_; 
lean_dec(v_h__3_1875_);
lean_dec(v_h__2_1874_);
v___x_1892_ = lean_apply_1(v_h__1_1873_, v_x_1872_);
return v___x_1892_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object* v_x_1893_, lean_object* v_x_1894_){
_start:
{
lean_object* v_k_1895_; lean_object* v_v_1896_; lean_object* v_l_1897_; lean_object* v_r_1898_; lean_object* v___y_1900_; lean_object* v___y_1906_; 
v_k_1895_ = lean_ctor_get(v_x_1893_, 1);
v_v_1896_ = lean_ctor_get(v_x_1893_, 2);
v_l_1897_ = lean_ctor_get(v_x_1893_, 3);
v_r_1898_ = lean_ctor_get(v_x_1893_, 4);
if (lean_obj_tag(v_l_1897_) == 0)
{
lean_object* v_size_1913_; 
v_size_1913_ = lean_ctor_get(v_l_1897_, 0);
v___y_1906_ = v_size_1913_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_1914_; 
v___x_1914_ = lean_unsigned_to_nat(0u);
v___y_1906_ = v___x_1914_;
goto v___jp_1905_;
}
v___jp_1899_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = lean_nat_sub(v_x_1894_, v___y_1900_);
lean_dec(v_x_1894_);
v___x_1902_ = lean_unsigned_to_nat(1u);
v___x_1903_ = lean_nat_sub(v___x_1901_, v___x_1902_);
lean_dec(v___x_1901_);
v_x_1893_ = v_r_1898_;
v_x_1894_ = v___x_1903_;
goto _start;
}
v___jp_1905_:
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_nat_dec_lt(v_x_1894_, v___y_1906_);
if (v___x_1907_ == 0)
{
uint8_t v___x_1908_; 
v___x_1908_ = lean_nat_dec_eq(v_x_1894_, v___y_1906_);
if (v___x_1908_ == 0)
{
if (lean_obj_tag(v_l_1897_) == 0)
{
lean_object* v_size_1909_; 
v_size_1909_ = lean_ctor_get(v_l_1897_, 0);
v___y_1900_ = v_size_1909_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1910_; 
v___x_1910_ = lean_unsigned_to_nat(0u);
v___y_1900_ = v___x_1910_;
goto v___jp_1899_;
}
}
else
{
lean_object* v___x_1911_; 
lean_dec(v_x_1894_);
lean_inc(v_v_1896_);
lean_inc(v_k_1895_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v_k_1895_);
lean_ctor_set(v___x_1911_, 1, v_v_1896_);
return v___x_1911_;
}
}
else
{
v_x_1893_ = v_l_1897_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg___boxed(lean_object* v_x_1915_, lean_object* v_x_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1915_, v_x_1916_);
lean_dec(v_x_1915_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx(lean_object* v_00_u03b1_1918_, lean_object* v_00_u03b2_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_, lean_object* v_x_1923_){
_start:
{
lean_object* v___x_1924_; 
v___x_1924_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1920_, v_x_1922_);
return v___x_1924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___boxed(lean_object* v_00_u03b1_1925_, lean_object* v_00_u03b2_1926_, lean_object* v_x_1927_, lean_object* v_x_1928_, lean_object* v_x_1929_, lean_object* v_x_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx(v_00_u03b1_1925_, v_00_u03b2_1926_, v_x_1927_, v_x_1928_, v_x_1929_, v_x_1930_);
lean_dec(v_x_1927_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object* v_x_1932_, lean_object* v_x_1933_){
_start:
{
if (lean_obj_tag(v_x_1932_) == 0)
{
lean_object* v_k_1934_; lean_object* v_v_1935_; lean_object* v_l_1936_; lean_object* v_r_1937_; lean_object* v___y_1939_; lean_object* v___y_1945_; 
v_k_1934_ = lean_ctor_get(v_x_1932_, 1);
v_v_1935_ = lean_ctor_get(v_x_1932_, 2);
v_l_1936_ = lean_ctor_get(v_x_1932_, 3);
v_r_1937_ = lean_ctor_get(v_x_1932_, 4);
if (lean_obj_tag(v_l_1936_) == 0)
{
lean_object* v_size_1953_; 
v_size_1953_ = lean_ctor_get(v_l_1936_, 0);
v___y_1945_ = v_size_1953_;
goto v___jp_1944_;
}
else
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_unsigned_to_nat(0u);
v___y_1945_ = v___x_1954_;
goto v___jp_1944_;
}
v___jp_1938_:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_nat_sub(v_x_1933_, v___y_1939_);
lean_dec(v_x_1933_);
v___x_1941_ = lean_unsigned_to_nat(1u);
v___x_1942_ = lean_nat_sub(v___x_1940_, v___x_1941_);
lean_dec(v___x_1940_);
v_x_1932_ = v_r_1937_;
v_x_1933_ = v___x_1942_;
goto _start;
}
v___jp_1944_:
{
uint8_t v___x_1946_; 
v___x_1946_ = lean_nat_dec_lt(v_x_1933_, v___y_1945_);
if (v___x_1946_ == 0)
{
uint8_t v___x_1947_; 
v___x_1947_ = lean_nat_dec_eq(v_x_1933_, v___y_1945_);
if (v___x_1947_ == 0)
{
if (lean_obj_tag(v_l_1936_) == 0)
{
lean_object* v_size_1948_; 
v_size_1948_ = lean_ctor_get(v_l_1936_, 0);
v___y_1939_ = v_size_1948_;
goto v___jp_1938_;
}
else
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_unsigned_to_nat(0u);
v___y_1939_ = v___x_1949_;
goto v___jp_1938_;
}
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v_x_1933_);
lean_inc(v_v_1935_);
lean_inc(v_k_1934_);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v_k_1934_);
lean_ctor_set(v___x_1950_, 1, v_v_1935_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
return v___x_1951_;
}
}
else
{
v_x_1932_ = v_l_1936_;
goto _start;
}
}
}
else
{
lean_object* v___x_1955_; 
lean_dec(v_x_1933_);
v___x_1955_ = lean_box(0);
return v___x_1955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_1956_, lean_object* v_x_1957_){
_start:
{
lean_object* v_res_1958_; 
v_res_1958_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_1956_, v_x_1957_);
lean_dec(v_x_1956_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(lean_object* v_00_u03b1_1959_, lean_object* v_00_u03b2_1960_, lean_object* v_x_1961_, lean_object* v_x_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_1961_, v_x_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_1964_, lean_object* v_00_u03b2_1965_, lean_object* v_x_1966_, lean_object* v_x_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(v_00_u03b1_1964_, v_00_u03b2_1965_, v_x_1966_, v_x_1967_);
lean_dec(v_x_1966_);
return v_res_1968_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1971_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_1972_ = lean_unsigned_to_nat(16u);
v___x_1973_ = lean_unsigned_to_nat(467u);
v___x_1974_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0));
v___x_1975_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1976_ = l_mkPanicMessageWithDecl(v___x_1975_, v___x_1974_, v___x_1973_, v___x_1972_, v___x_1971_);
return v___x_1976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(lean_object* v_inst_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_){
_start:
{
if (lean_obj_tag(v_x_1978_) == 0)
{
lean_object* v_k_1980_; lean_object* v_v_1981_; lean_object* v_l_1982_; lean_object* v_r_1983_; lean_object* v___y_1985_; lean_object* v___y_1991_; 
v_k_1980_ = lean_ctor_get(v_x_1978_, 1);
v_v_1981_ = lean_ctor_get(v_x_1978_, 2);
v_l_1982_ = lean_ctor_get(v_x_1978_, 3);
v_r_1983_ = lean_ctor_get(v_x_1978_, 4);
if (lean_obj_tag(v_l_1982_) == 0)
{
lean_object* v_size_1998_; 
v_size_1998_ = lean_ctor_get(v_l_1982_, 0);
v___y_1991_ = v_size_1998_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_unsigned_to_nat(0u);
v___y_1991_ = v___x_1999_;
goto v___jp_1990_;
}
v___jp_1984_:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1986_ = lean_nat_sub(v_x_1979_, v___y_1985_);
lean_dec(v_x_1979_);
v___x_1987_ = lean_unsigned_to_nat(1u);
v___x_1988_ = lean_nat_sub(v___x_1986_, v___x_1987_);
lean_dec(v___x_1986_);
v_x_1978_ = v_r_1983_;
v_x_1979_ = v___x_1988_;
goto _start;
}
v___jp_1990_:
{
uint8_t v___x_1992_; 
v___x_1992_ = lean_nat_dec_lt(v_x_1979_, v___y_1991_);
if (v___x_1992_ == 0)
{
uint8_t v___x_1993_; 
v___x_1993_ = lean_nat_dec_eq(v_x_1979_, v___y_1991_);
if (v___x_1993_ == 0)
{
if (lean_obj_tag(v_l_1982_) == 0)
{
lean_object* v_size_1994_; 
v_size_1994_ = lean_ctor_get(v_l_1982_, 0);
v___y_1985_ = v_size_1994_;
goto v___jp_1984_;
}
else
{
lean_object* v___x_1995_; 
v___x_1995_ = lean_unsigned_to_nat(0u);
v___y_1985_ = v___x_1995_;
goto v___jp_1984_;
}
}
else
{
lean_object* v___x_1996_; 
lean_dec(v_x_1979_);
lean_dec_ref(v_inst_1977_);
lean_inc(v_v_1981_);
lean_inc(v_k_1980_);
v___x_1996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1996_, 0, v_k_1980_);
lean_ctor_set(v___x_1996_, 1, v_v_1981_);
return v___x_1996_;
}
}
else
{
v_x_1978_ = v_l_1982_;
goto _start;
}
}
}
else
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec(v_x_1979_);
v___x_2000_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2);
v___x_2001_ = l_panic___redArg(v_inst_1977_, v___x_2000_);
return v___x_2001_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_2002_, lean_object* v_x_2003_, lean_object* v_x_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2002_, v_x_2003_, v_x_2004_);
lean_dec(v_x_2003_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(lean_object* v_00_u03b1_2006_, lean_object* v_00_u03b2_2007_, lean_object* v_inst_2008_, lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2008_, v_x_2009_, v_x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_inst_2014_, lean_object* v_x_2015_, lean_object* v_x_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(v_00_u03b1_2012_, v_00_u03b2_2013_, v_inst_2014_, v_x_2015_, v_x_2016_);
lean_dec(v_x_2015_);
return v_res_2017_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_){
_start:
{
if (lean_obj_tag(v_x_2018_) == 0)
{
lean_object* v_k_2021_; lean_object* v_v_2022_; lean_object* v_l_2023_; lean_object* v_r_2024_; lean_object* v___y_2026_; lean_object* v___y_2032_; 
v_k_2021_ = lean_ctor_get(v_x_2018_, 1);
v_v_2022_ = lean_ctor_get(v_x_2018_, 2);
v_l_2023_ = lean_ctor_get(v_x_2018_, 3);
v_r_2024_ = lean_ctor_get(v_x_2018_, 4);
if (lean_obj_tag(v_l_2023_) == 0)
{
lean_object* v_size_2039_; 
v_size_2039_ = lean_ctor_get(v_l_2023_, 0);
v___y_2032_ = v_size_2039_;
goto v___jp_2031_;
}
else
{
lean_object* v___x_2040_; 
v___x_2040_ = lean_unsigned_to_nat(0u);
v___y_2032_ = v___x_2040_;
goto v___jp_2031_;
}
v___jp_2025_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2027_ = lean_nat_sub(v_x_2019_, v___y_2026_);
lean_dec(v_x_2019_);
v___x_2028_ = lean_unsigned_to_nat(1u);
v___x_2029_ = lean_nat_sub(v___x_2027_, v___x_2028_);
lean_dec(v___x_2027_);
v_x_2018_ = v_r_2024_;
v_x_2019_ = v___x_2029_;
goto _start;
}
v___jp_2031_:
{
uint8_t v___x_2033_; 
v___x_2033_ = lean_nat_dec_lt(v_x_2019_, v___y_2032_);
if (v___x_2033_ == 0)
{
uint8_t v___x_2034_; 
v___x_2034_ = lean_nat_dec_eq(v_x_2019_, v___y_2032_);
if (v___x_2034_ == 0)
{
if (lean_obj_tag(v_l_2023_) == 0)
{
lean_object* v_size_2035_; 
v_size_2035_ = lean_ctor_get(v_l_2023_, 0);
v___y_2026_ = v_size_2035_;
goto v___jp_2025_;
}
else
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_unsigned_to_nat(0u);
v___y_2026_ = v___x_2036_;
goto v___jp_2025_;
}
}
else
{
lean_object* v___x_2037_; 
lean_dec(v_x_2019_);
lean_inc(v_v_2022_);
lean_inc(v_k_2021_);
v___x_2037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2037_, 0, v_k_2021_);
lean_ctor_set(v___x_2037_, 1, v_v_2022_);
return v___x_2037_;
}
}
else
{
v_x_2018_ = v_l_2023_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2019_);
lean_inc_ref(v_x_2020_);
return v_x_2020_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg___boxed(lean_object* v_x_2041_, lean_object* v_x_2042_, lean_object* v_x_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2041_, v_x_2042_, v_x_2043_);
lean_dec_ref(v_x_2043_);
lean_dec(v_x_2041_);
return v_res_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD(lean_object* v_00_u03b1_2045_, lean_object* v_00_u03b2_2046_, lean_object* v_x_2047_, lean_object* v_x_2048_, lean_object* v_x_2049_){
_start:
{
lean_object* v___x_2050_; 
v___x_2050_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2047_, v_x_2048_, v_x_2049_);
return v___x_2050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___boxed(lean_object* v_00_u03b1_2051_, lean_object* v_00_u03b2_2052_, lean_object* v_x_2053_, lean_object* v_x_2054_, lean_object* v_x_2055_){
_start:
{
lean_object* v_res_2056_; 
v_res_2056_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD(v_00_u03b1_2051_, v_00_u03b2_2052_, v_x_2053_, v_x_2054_, v_x_2055_);
lean_dec_ref(v_x_2055_);
lean_dec(v_x_2053_);
return v_res_2056_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v_k_2059_; lean_object* v_l_2060_; lean_object* v_r_2061_; lean_object* v___y_2063_; lean_object* v___y_2069_; 
v_k_2059_ = lean_ctor_get(v_x_2057_, 1);
v_l_2060_ = lean_ctor_get(v_x_2057_, 3);
v_r_2061_ = lean_ctor_get(v_x_2057_, 4);
if (lean_obj_tag(v_l_2060_) == 0)
{
lean_object* v_size_2075_; 
v_size_2075_ = lean_ctor_get(v_l_2060_, 0);
v___y_2069_ = v_size_2075_;
goto v___jp_2068_;
}
else
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_unsigned_to_nat(0u);
v___y_2069_ = v___x_2076_;
goto v___jp_2068_;
}
v___jp_2062_:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_nat_sub(v_x_2058_, v___y_2063_);
lean_dec(v_x_2058_);
v___x_2065_ = lean_unsigned_to_nat(1u);
v___x_2066_ = lean_nat_sub(v___x_2064_, v___x_2065_);
lean_dec(v___x_2064_);
v_x_2057_ = v_r_2061_;
v_x_2058_ = v___x_2066_;
goto _start;
}
v___jp_2068_:
{
uint8_t v___x_2070_; 
v___x_2070_ = lean_nat_dec_lt(v_x_2058_, v___y_2069_);
if (v___x_2070_ == 0)
{
uint8_t v___x_2071_; 
v___x_2071_ = lean_nat_dec_eq(v_x_2058_, v___y_2069_);
if (v___x_2071_ == 0)
{
if (lean_obj_tag(v_l_2060_) == 0)
{
lean_object* v_size_2072_; 
v_size_2072_ = lean_ctor_get(v_l_2060_, 0);
v___y_2063_ = v_size_2072_;
goto v___jp_2062_;
}
else
{
lean_object* v___x_2073_; 
v___x_2073_ = lean_unsigned_to_nat(0u);
v___y_2063_ = v___x_2073_;
goto v___jp_2062_;
}
}
else
{
lean_dec(v_x_2058_);
lean_inc(v_k_2059_);
return v_k_2059_;
}
}
else
{
v_x_2057_ = v_l_2060_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg___boxed(lean_object* v_x_2077_, lean_object* v_x_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2077_, v_x_2078_);
lean_dec(v_x_2077_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx(lean_object* v_00_u03b1_2080_, lean_object* v_00_u03b2_2081_, lean_object* v_x_2082_, lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v_x_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2082_, v_x_2084_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___boxed(lean_object* v_00_u03b1_2087_, lean_object* v_00_u03b2_2088_, lean_object* v_x_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_, lean_object* v_x_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx(v_00_u03b1_2087_, v_00_u03b2_2088_, v_x_2089_, v_x_2090_, v_x_2091_, v_x_2092_);
lean_dec(v_x_2089_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object* v_x_2094_, lean_object* v_x_2095_){
_start:
{
if (lean_obj_tag(v_x_2094_) == 0)
{
lean_object* v_k_2096_; lean_object* v_l_2097_; lean_object* v_r_2098_; lean_object* v___y_2100_; lean_object* v___y_2106_; 
v_k_2096_ = lean_ctor_get(v_x_2094_, 1);
v_l_2097_ = lean_ctor_get(v_x_2094_, 3);
v_r_2098_ = lean_ctor_get(v_x_2094_, 4);
if (lean_obj_tag(v_l_2097_) == 0)
{
lean_object* v_size_2113_; 
v_size_2113_ = lean_ctor_get(v_l_2097_, 0);
v___y_2106_ = v_size_2113_;
goto v___jp_2105_;
}
else
{
lean_object* v___x_2114_; 
v___x_2114_ = lean_unsigned_to_nat(0u);
v___y_2106_ = v___x_2114_;
goto v___jp_2105_;
}
v___jp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2101_ = lean_nat_sub(v_x_2095_, v___y_2100_);
lean_dec(v_x_2095_);
v___x_2102_ = lean_unsigned_to_nat(1u);
v___x_2103_ = lean_nat_sub(v___x_2101_, v___x_2102_);
lean_dec(v___x_2101_);
v_x_2094_ = v_r_2098_;
v_x_2095_ = v___x_2103_;
goto _start;
}
v___jp_2105_:
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_nat_dec_lt(v_x_2095_, v___y_2106_);
if (v___x_2107_ == 0)
{
uint8_t v___x_2108_; 
v___x_2108_ = lean_nat_dec_eq(v_x_2095_, v___y_2106_);
if (v___x_2108_ == 0)
{
if (lean_obj_tag(v_l_2097_) == 0)
{
lean_object* v_size_2109_; 
v_size_2109_ = lean_ctor_get(v_l_2097_, 0);
v___y_2100_ = v_size_2109_;
goto v___jp_2099_;
}
else
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_unsigned_to_nat(0u);
v___y_2100_ = v___x_2110_;
goto v___jp_2099_;
}
}
else
{
lean_object* v___x_2111_; 
lean_dec(v_x_2095_);
lean_inc(v_k_2096_);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v_k_2096_);
return v___x_2111_;
}
}
else
{
v_x_2094_ = v_l_2097_;
goto _start;
}
}
}
else
{
lean_object* v___x_2115_; 
lean_dec(v_x_2095_);
v___x_2115_ = lean_box(0);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg___boxed(lean_object* v_x_2116_, lean_object* v_x_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2116_, v_x_2117_);
lean_dec(v_x_2116_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(lean_object* v_00_u03b1_2119_, lean_object* v_00_u03b2_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2121_, v_x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_2124_, lean_object* v_00_u03b2_2125_, lean_object* v_x_2126_, lean_object* v_x_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(v_00_u03b1_2124_, v_00_u03b2_2125_, v_x_2126_, v_x_2127_);
lean_dec(v_x_2126_);
return v_res_2128_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2130_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_2131_ = lean_unsigned_to_nat(16u);
v___x_2132_ = lean_unsigned_to_nat(503u);
v___x_2133_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0));
v___x_2134_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_2135_ = l_mkPanicMessageWithDecl(v___x_2134_, v___x_2133_, v___x_2132_, v___x_2131_, v___x_2130_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object* v_inst_2136_, lean_object* v_x_2137_, lean_object* v_x_2138_){
_start:
{
if (lean_obj_tag(v_x_2137_) == 0)
{
lean_object* v_k_2139_; lean_object* v_l_2140_; lean_object* v_r_2141_; lean_object* v___y_2143_; lean_object* v___y_2149_; 
v_k_2139_ = lean_ctor_get(v_x_2137_, 1);
v_l_2140_ = lean_ctor_get(v_x_2137_, 3);
v_r_2141_ = lean_ctor_get(v_x_2137_, 4);
if (lean_obj_tag(v_l_2140_) == 0)
{
lean_object* v_size_2155_; 
v_size_2155_ = lean_ctor_get(v_l_2140_, 0);
v___y_2149_ = v_size_2155_;
goto v___jp_2148_;
}
else
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_unsigned_to_nat(0u);
v___y_2149_ = v___x_2156_;
goto v___jp_2148_;
}
v___jp_2142_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = lean_nat_sub(v_x_2138_, v___y_2143_);
lean_dec(v_x_2138_);
v___x_2145_ = lean_unsigned_to_nat(1u);
v___x_2146_ = lean_nat_sub(v___x_2144_, v___x_2145_);
lean_dec(v___x_2144_);
v_x_2137_ = v_r_2141_;
v_x_2138_ = v___x_2146_;
goto _start;
}
v___jp_2148_:
{
uint8_t v___x_2150_; 
v___x_2150_ = lean_nat_dec_lt(v_x_2138_, v___y_2149_);
if (v___x_2150_ == 0)
{
uint8_t v___x_2151_; 
v___x_2151_ = lean_nat_dec_eq(v_x_2138_, v___y_2149_);
if (v___x_2151_ == 0)
{
if (lean_obj_tag(v_l_2140_) == 0)
{
lean_object* v_size_2152_; 
v_size_2152_ = lean_ctor_get(v_l_2140_, 0);
v___y_2143_ = v_size_2152_;
goto v___jp_2142_;
}
else
{
lean_object* v___x_2153_; 
v___x_2153_ = lean_unsigned_to_nat(0u);
v___y_2143_ = v___x_2153_;
goto v___jp_2142_;
}
}
else
{
lean_dec(v_x_2138_);
lean_dec(v_inst_2136_);
lean_inc(v_k_2139_);
return v_k_2139_;
}
}
else
{
v_x_2137_ = v_l_2140_;
goto _start;
}
}
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec(v_x_2138_);
v___x_2157_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1);
v___x_2158_ = l_panic___redArg(v_inst_2136_, v___x_2157_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_2159_, lean_object* v_x_2160_, lean_object* v_x_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2159_, v_x_2160_, v_x_2161_);
lean_dec(v_x_2160_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(lean_object* v_00_u03b1_2163_, lean_object* v_00_u03b2_2164_, lean_object* v_inst_2165_, lean_object* v_x_2166_, lean_object* v_x_2167_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2165_, v_x_2166_, v_x_2167_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_2169_, lean_object* v_00_u03b2_2170_, lean_object* v_inst_2171_, lean_object* v_x_2172_, lean_object* v_x_2173_){
_start:
{
lean_object* v_res_2174_; 
v_res_2174_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(v_00_u03b1_2169_, v_00_u03b2_2170_, v_inst_2171_, v_x_2172_, v_x_2173_);
lean_dec(v_x_2172_);
return v_res_2174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object* v_x_2175_, lean_object* v_x_2176_, lean_object* v_x_2177_){
_start:
{
if (lean_obj_tag(v_x_2175_) == 0)
{
lean_object* v_k_2178_; lean_object* v_l_2179_; lean_object* v_r_2180_; lean_object* v___y_2182_; lean_object* v___y_2188_; 
v_k_2178_ = lean_ctor_get(v_x_2175_, 1);
v_l_2179_ = lean_ctor_get(v_x_2175_, 3);
v_r_2180_ = lean_ctor_get(v_x_2175_, 4);
if (lean_obj_tag(v_l_2179_) == 0)
{
lean_object* v_size_2194_; 
v_size_2194_ = lean_ctor_get(v_l_2179_, 0);
v___y_2188_ = v_size_2194_;
goto v___jp_2187_;
}
else
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_unsigned_to_nat(0u);
v___y_2188_ = v___x_2195_;
goto v___jp_2187_;
}
v___jp_2181_:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = lean_nat_sub(v_x_2176_, v___y_2182_);
lean_dec(v_x_2176_);
v___x_2184_ = lean_unsigned_to_nat(1u);
v___x_2185_ = lean_nat_sub(v___x_2183_, v___x_2184_);
lean_dec(v___x_2183_);
v_x_2175_ = v_r_2180_;
v_x_2176_ = v___x_2185_;
goto _start;
}
v___jp_2187_:
{
uint8_t v___x_2189_; 
v___x_2189_ = lean_nat_dec_lt(v_x_2176_, v___y_2188_);
if (v___x_2189_ == 0)
{
uint8_t v___x_2190_; 
v___x_2190_ = lean_nat_dec_eq(v_x_2176_, v___y_2188_);
if (v___x_2190_ == 0)
{
if (lean_obj_tag(v_l_2179_) == 0)
{
lean_object* v_size_2191_; 
v_size_2191_ = lean_ctor_get(v_l_2179_, 0);
v___y_2182_ = v_size_2191_;
goto v___jp_2181_;
}
else
{
lean_object* v___x_2192_; 
v___x_2192_ = lean_unsigned_to_nat(0u);
v___y_2182_ = v___x_2192_;
goto v___jp_2181_;
}
}
else
{
lean_dec(v_x_2176_);
lean_inc(v_k_2178_);
return v_k_2178_;
}
}
else
{
v_x_2175_ = v_l_2179_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2176_);
lean_inc(v_x_2177_);
return v_x_2177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg___boxed(lean_object* v_x_2196_, lean_object* v_x_2197_, lean_object* v_x_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2196_, v_x_2197_, v_x_2198_);
lean_dec(v_x_2198_);
lean_dec(v_x_2196_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD(lean_object* v_00_u03b1_2200_, lean_object* v_00_u03b2_2201_, lean_object* v_x_2202_, lean_object* v_x_2203_, lean_object* v_x_2204_){
_start:
{
lean_object* v___x_2205_; 
v___x_2205_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2202_, v_x_2203_, v_x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___boxed(lean_object* v_00_u03b1_2206_, lean_object* v_00_u03b2_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_, lean_object* v_x_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD(v_00_u03b1_2206_, v_00_u03b2_2207_, v_x_2208_, v_x_2209_, v_x_2210_);
lean_dec(v_x_2210_);
lean_dec(v_x_2208_);
return v_res_2211_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object* v_inst_2212_, lean_object* v_k_2213_, lean_object* v_best_2214_, lean_object* v_a_2215_){
_start:
{
if (lean_obj_tag(v_a_2215_) == 0)
{
lean_object* v_k_2216_; lean_object* v_v_2217_; lean_object* v_l_2218_; lean_object* v_r_2219_; lean_object* v___x_2220_; uint8_t v___x_2221_; 
v_k_2216_ = lean_ctor_get(v_a_2215_, 1);
lean_inc(v_k_2216_);
v_v_2217_ = lean_ctor_get(v_a_2215_, 2);
lean_inc(v_v_2217_);
v_l_2218_ = lean_ctor_get(v_a_2215_, 3);
lean_inc(v_l_2218_);
v_r_2219_ = lean_ctor_get(v_a_2215_, 4);
lean_inc(v_r_2219_);
lean_dec_ref(v_a_2215_);
lean_inc_ref(v_inst_2212_);
lean_inc(v_k_2216_);
lean_inc(v_k_2213_);
v___x_2220_ = lean_apply_2(v_inst_2212_, v_k_2213_, v_k_2216_);
v___x_2221_ = lean_unbox(v___x_2220_);
switch(v___x_2221_)
{
case 0:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; 
lean_dec(v_r_2219_);
lean_dec(v_best_2214_);
v___x_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2222_, 0, v_k_2216_);
lean_ctor_set(v___x_2222_, 1, v_v_2217_);
v___x_2223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
v_best_2214_ = v___x_2223_;
v_a_2215_ = v_l_2218_;
goto _start;
}
case 1:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
lean_dec(v_r_2219_);
lean_dec(v_l_2218_);
lean_dec(v_best_2214_);
lean_dec(v_k_2213_);
lean_dec_ref(v_inst_2212_);
v___x_2225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2225_, 0, v_k_2216_);
lean_ctor_set(v___x_2225_, 1, v_v_2217_);
v___x_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2226_, 0, v___x_2225_);
return v___x_2226_;
}
default: 
{
lean_dec(v_l_2218_);
lean_dec(v_v_2217_);
lean_dec(v_k_2216_);
v_a_2215_ = v_r_2219_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2213_);
lean_dec_ref(v_inst_2212_);
return v_best_2214_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go(lean_object* v_00_u03b1_2228_, lean_object* v_00_u03b2_2229_, lean_object* v_inst_2230_, lean_object* v_k_2231_, lean_object* v_best_2232_, lean_object* v_a_2233_){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2230_, v_k_2231_, v_best_2232_, v_a_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___redArg(lean_object* v_inst_2235_, lean_object* v_k_2236_, lean_object* v_a_2237_){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = lean_box(0);
v___x_2239_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2235_, v_k_2236_, v___x_2238_, v_a_2237_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f(lean_object* v_00_u03b1_2240_, lean_object* v_00_u03b2_2241_, lean_object* v_inst_2242_, lean_object* v_k_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; 
v___x_2245_ = lean_box(0);
v___x_2246_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2242_, v_k_2243_, v___x_2245_, v_a_2244_);
return v___x_2246_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object* v_inst_2247_, lean_object* v_k_2248_, lean_object* v_best_2249_, lean_object* v_a_2250_){
_start:
{
if (lean_obj_tag(v_a_2250_) == 0)
{
lean_object* v_k_2251_; lean_object* v_v_2252_; lean_object* v_l_2253_; lean_object* v_r_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; 
v_k_2251_ = lean_ctor_get(v_a_2250_, 1);
lean_inc(v_k_2251_);
v_v_2252_ = lean_ctor_get(v_a_2250_, 2);
lean_inc(v_v_2252_);
v_l_2253_ = lean_ctor_get(v_a_2250_, 3);
lean_inc(v_l_2253_);
v_r_2254_ = lean_ctor_get(v_a_2250_, 4);
lean_inc(v_r_2254_);
lean_dec_ref(v_a_2250_);
lean_inc_ref(v_inst_2247_);
lean_inc(v_k_2251_);
lean_inc(v_k_2248_);
v___x_2255_ = lean_apply_2(v_inst_2247_, v_k_2248_, v_k_2251_);
v___x_2256_ = lean_unbox(v___x_2255_);
if (v___x_2256_ == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
lean_dec(v_r_2254_);
lean_dec(v_best_2249_);
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v_k_2251_);
lean_ctor_set(v___x_2257_, 1, v_v_2252_);
v___x_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2258_, 0, v___x_2257_);
v_best_2249_ = v___x_2258_;
v_a_2250_ = v_l_2253_;
goto _start;
}
else
{
lean_dec(v_l_2253_);
lean_dec(v_v_2252_);
lean_dec(v_k_2251_);
v_a_2250_ = v_r_2254_;
goto _start;
}
}
else
{
lean_dec(v_k_2248_);
lean_dec_ref(v_inst_2247_);
return v_best_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go(lean_object* v_00_u03b1_2261_, lean_object* v_00_u03b2_2262_, lean_object* v_inst_2263_, lean_object* v_k_2264_, lean_object* v_best_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2263_, v_k_2264_, v_best_2265_, v_a_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___redArg(lean_object* v_inst_2268_, lean_object* v_k_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = lean_box(0);
v___x_2272_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2268_, v_k_2269_, v___x_2271_, v_a_2270_);
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f(lean_object* v_00_u03b1_2273_, lean_object* v_00_u03b2_2274_, lean_object* v_inst_2275_, lean_object* v_k_2276_, lean_object* v_a_2277_){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_box(0);
v___x_2279_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2275_, v_k_2276_, v___x_2278_, v_a_2277_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object* v_inst_2280_, lean_object* v_k_2281_, lean_object* v_best_2282_, lean_object* v_a_2283_){
_start:
{
if (lean_obj_tag(v_a_2283_) == 0)
{
lean_object* v_k_2284_; lean_object* v_v_2285_; lean_object* v_l_2286_; lean_object* v_r_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; 
v_k_2284_ = lean_ctor_get(v_a_2283_, 1);
lean_inc(v_k_2284_);
v_v_2285_ = lean_ctor_get(v_a_2283_, 2);
lean_inc(v_v_2285_);
v_l_2286_ = lean_ctor_get(v_a_2283_, 3);
lean_inc(v_l_2286_);
v_r_2287_ = lean_ctor_get(v_a_2283_, 4);
lean_inc(v_r_2287_);
lean_dec_ref(v_a_2283_);
lean_inc_ref(v_inst_2280_);
lean_inc(v_k_2284_);
lean_inc(v_k_2281_);
v___x_2288_ = lean_apply_2(v_inst_2280_, v_k_2281_, v_k_2284_);
v___x_2289_ = lean_unbox(v___x_2288_);
switch(v___x_2289_)
{
case 0:
{
lean_dec(v_r_2287_);
lean_dec(v_v_2285_);
lean_dec(v_k_2284_);
v_a_2283_ = v_l_2286_;
goto _start;
}
case 1:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec(v_r_2287_);
lean_dec(v_l_2286_);
lean_dec(v_best_2282_);
lean_dec(v_k_2281_);
lean_dec_ref(v_inst_2280_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v_k_2284_);
lean_ctor_set(v___x_2291_, 1, v_v_2285_);
v___x_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
return v___x_2292_;
}
default: 
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
lean_dec(v_l_2286_);
lean_dec(v_best_2282_);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v_k_2284_);
lean_ctor_set(v___x_2293_, 1, v_v_2285_);
v___x_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
v_best_2282_ = v___x_2294_;
v_a_2283_ = v_r_2287_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2281_);
lean_dec_ref(v_inst_2280_);
return v_best_2282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go(lean_object* v_00_u03b1_2296_, lean_object* v_00_u03b2_2297_, lean_object* v_inst_2298_, lean_object* v_k_2299_, lean_object* v_best_2300_, lean_object* v_a_2301_){
_start:
{
lean_object* v___x_2302_; 
v___x_2302_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2298_, v_k_2299_, v_best_2300_, v_a_2301_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___redArg(lean_object* v_inst_2303_, lean_object* v_k_2304_, lean_object* v_a_2305_){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2306_ = lean_box(0);
v___x_2307_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2303_, v_k_2304_, v___x_2306_, v_a_2305_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f(lean_object* v_00_u03b1_2308_, lean_object* v_00_u03b2_2309_, lean_object* v_inst_2310_, lean_object* v_k_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_box(0);
v___x_2314_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2310_, v_k_2311_, v___x_2313_, v_a_2312_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object* v_inst_2315_, lean_object* v_k_2316_, lean_object* v_best_2317_, lean_object* v_a_2318_){
_start:
{
if (lean_obj_tag(v_a_2318_) == 0)
{
lean_object* v_k_2319_; lean_object* v_v_2320_; lean_object* v_l_2321_; lean_object* v_r_2322_; lean_object* v___x_2323_; uint8_t v___x_2324_; 
v_k_2319_ = lean_ctor_get(v_a_2318_, 1);
lean_inc(v_k_2319_);
v_v_2320_ = lean_ctor_get(v_a_2318_, 2);
lean_inc(v_v_2320_);
v_l_2321_ = lean_ctor_get(v_a_2318_, 3);
lean_inc(v_l_2321_);
v_r_2322_ = lean_ctor_get(v_a_2318_, 4);
lean_inc(v_r_2322_);
lean_dec_ref(v_a_2318_);
lean_inc_ref(v_inst_2315_);
lean_inc(v_k_2319_);
lean_inc(v_k_2316_);
v___x_2323_ = lean_apply_2(v_inst_2315_, v_k_2316_, v_k_2319_);
v___x_2324_ = lean_unbox(v___x_2323_);
if (v___x_2324_ == 2)
{
lean_object* v___x_2325_; lean_object* v___x_2326_; 
lean_dec(v_l_2321_);
lean_dec(v_best_2317_);
v___x_2325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2325_, 0, v_k_2319_);
lean_ctor_set(v___x_2325_, 1, v_v_2320_);
v___x_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2325_);
v_best_2317_ = v___x_2326_;
v_a_2318_ = v_r_2322_;
goto _start;
}
else
{
lean_dec(v_r_2322_);
lean_dec(v_v_2320_);
lean_dec(v_k_2319_);
v_a_2318_ = v_l_2321_;
goto _start;
}
}
else
{
lean_dec(v_k_2316_);
lean_dec_ref(v_inst_2315_);
return v_best_2317_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go(lean_object* v_00_u03b1_2329_, lean_object* v_00_u03b2_2330_, lean_object* v_inst_2331_, lean_object* v_k_2332_, lean_object* v_best_2333_, lean_object* v_a_2334_){
_start:
{
lean_object* v___x_2335_; 
v___x_2335_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2331_, v_k_2332_, v_best_2333_, v_a_2334_);
return v___x_2335_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___redArg(lean_object* v_inst_2336_, lean_object* v_k_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2339_ = lean_box(0);
v___x_2340_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2336_, v_k_2337_, v___x_2339_, v_a_2338_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f(lean_object* v_00_u03b1_2341_, lean_object* v_00_u03b2_2342_, lean_object* v_inst_2343_, lean_object* v_k_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2346_ = lean_box(0);
v___x_2347_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2343_, v_k_2344_, v___x_2346_, v_a_2345_);
return v___x_2347_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2351_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2));
v___x_2352_ = lean_unsigned_to_nat(14u);
v___x_2353_ = lean_unsigned_to_nat(22u);
v___x_2354_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1));
v___x_2355_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0));
v___x_2356_ = l_mkPanicMessageWithDecl(v___x_2355_, v___x_2354_, v___x_2353_, v___x_2352_, v___x_2351_);
return v___x_2356_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(lean_object* v_inst_2357_, lean_object* v_inst_2358_, lean_object* v_k_2359_, lean_object* v_t_2360_){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_box(0);
v___x_2362_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2357_, v_k_2359_, v___x_2361_, v_t_2360_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v___x_2363_; lean_object* v___x_2364_; 
v___x_2363_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2364_ = l_panic___redArg(v_inst_2358_, v___x_2363_);
return v___x_2364_;
}
else
{
lean_object* v_val_2365_; 
lean_dec_ref(v_inst_2358_);
v_val_2365_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_val_2365_);
lean_dec_ref(v___x_2362_);
return v_val_2365_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(lean_object* v_00_u03b1_2366_, lean_object* v_00_u03b2_2367_, lean_object* v_inst_2368_, lean_object* v_inst_2369_, lean_object* v_k_2370_, lean_object* v_t_2371_){
_start:
{
lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2372_ = lean_box(0);
v___x_2373_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2368_, v_k_2370_, v___x_2372_, v_t_2371_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2375_ = l_panic___redArg(v_inst_2369_, v___x_2374_);
return v___x_2375_;
}
else
{
lean_object* v_val_2376_; 
lean_dec_ref(v_inst_2369_);
v_val_2376_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_val_2376_);
lean_dec_ref(v___x_2373_);
return v_val_2376_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(lean_object* v_inst_2377_, lean_object* v_inst_2378_, lean_object* v_k_2379_, lean_object* v_t_2380_){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = lean_box(0);
v___x_2382_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2377_, v_k_2379_, v___x_2381_, v_t_2380_);
if (lean_obj_tag(v___x_2382_) == 0)
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2384_ = l_panic___redArg(v_inst_2378_, v___x_2383_);
return v___x_2384_;
}
else
{
lean_object* v_val_2385_; 
lean_dec_ref(v_inst_2378_);
v_val_2385_ = lean_ctor_get(v___x_2382_, 0);
lean_inc(v_val_2385_);
lean_dec_ref(v___x_2382_);
return v_val_2385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(lean_object* v_00_u03b1_2386_, lean_object* v_00_u03b2_2387_, lean_object* v_inst_2388_, lean_object* v_inst_2389_, lean_object* v_k_2390_, lean_object* v_t_2391_){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = lean_box(0);
v___x_2393_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2388_, v_k_2390_, v___x_2392_, v_t_2391_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2395_ = l_panic___redArg(v_inst_2389_, v___x_2394_);
return v___x_2395_;
}
else
{
lean_object* v_val_2396_; 
lean_dec_ref(v_inst_2389_);
v_val_2396_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_val_2396_);
lean_dec_ref(v___x_2393_);
return v_val_2396_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(lean_object* v_inst_2397_, lean_object* v_inst_2398_, lean_object* v_k_2399_, lean_object* v_t_2400_){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = lean_box(0);
v___x_2402_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2397_, v_k_2399_, v___x_2401_, v_t_2400_);
if (lean_obj_tag(v___x_2402_) == 0)
{
lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2403_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2404_ = l_panic___redArg(v_inst_2398_, v___x_2403_);
return v___x_2404_;
}
else
{
lean_object* v_val_2405_; 
lean_dec_ref(v_inst_2398_);
v_val_2405_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_val_2405_);
lean_dec_ref(v___x_2402_);
return v_val_2405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(lean_object* v_00_u03b1_2406_, lean_object* v_00_u03b2_2407_, lean_object* v_inst_2408_, lean_object* v_inst_2409_, lean_object* v_k_2410_, lean_object* v_t_2411_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_box(0);
v___x_2413_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2408_, v_k_2410_, v___x_2412_, v_t_2411_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2414_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2415_ = l_panic___redArg(v_inst_2409_, v___x_2414_);
return v___x_2415_;
}
else
{
lean_object* v_val_2416_; 
lean_dec_ref(v_inst_2409_);
v_val_2416_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_val_2416_);
lean_dec_ref(v___x_2413_);
return v_val_2416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(lean_object* v_inst_2417_, lean_object* v_inst_2418_, lean_object* v_k_2419_, lean_object* v_t_2420_){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = lean_box(0);
v___x_2422_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2417_, v_k_2419_, v___x_2421_, v_t_2420_);
if (lean_obj_tag(v___x_2422_) == 0)
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2424_ = l_panic___redArg(v_inst_2418_, v___x_2423_);
return v___x_2424_;
}
else
{
lean_object* v_val_2425_; 
lean_dec_ref(v_inst_2418_);
v_val_2425_ = lean_ctor_get(v___x_2422_, 0);
lean_inc(v_val_2425_);
lean_dec_ref(v___x_2422_);
return v_val_2425_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(lean_object* v_00_u03b1_2426_, lean_object* v_00_u03b2_2427_, lean_object* v_inst_2428_, lean_object* v_inst_2429_, lean_object* v_k_2430_, lean_object* v_t_2431_){
_start:
{
lean_object* v___x_2432_; lean_object* v___x_2433_; 
v___x_2432_ = lean_box(0);
v___x_2433_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2428_, v_k_2430_, v___x_2432_, v_t_2431_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2435_ = l_panic___redArg(v_inst_2429_, v___x_2434_);
return v___x_2435_;
}
else
{
lean_object* v_val_2436_; 
lean_dec_ref(v_inst_2429_);
v_val_2436_ = lean_ctor_get(v___x_2433_, 0);
lean_inc(v_val_2436_);
lean_dec_ref(v___x_2433_);
return v_val_2436_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(lean_object* v_inst_2437_, lean_object* v_k_2438_, lean_object* v_t_2439_, lean_object* v_fallback_2440_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_box(0);
v___x_2442_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2437_, v_k_2438_, v___x_2441_, v_t_2439_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_inc_ref(v_fallback_2440_);
return v_fallback_2440_;
}
else
{
lean_object* v_val_2443_; 
v_val_2443_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_val_2443_);
lean_dec_ref(v___x_2442_);
return v_val_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg___boxed(lean_object* v_inst_2444_, lean_object* v_k_2445_, lean_object* v_t_2446_, lean_object* v_fallback_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(v_inst_2444_, v_k_2445_, v_t_2446_, v_fallback_2447_);
lean_dec_ref(v_fallback_2447_);
return v_res_2448_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED(lean_object* v_00_u03b1_2449_, lean_object* v_00_u03b2_2450_, lean_object* v_inst_2451_, lean_object* v_k_2452_, lean_object* v_t_2453_, lean_object* v_fallback_2454_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = lean_box(0);
v___x_2456_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2451_, v_k_2452_, v___x_2455_, v_t_2453_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_inc_ref(v_fallback_2454_);
return v_fallback_2454_;
}
else
{
lean_object* v_val_2457_; 
v_val_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_val_2457_);
lean_dec_ref(v___x_2456_);
return v_val_2457_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___boxed(lean_object* v_00_u03b1_2458_, lean_object* v_00_u03b2_2459_, lean_object* v_inst_2460_, lean_object* v_k_2461_, lean_object* v_t_2462_, lean_object* v_fallback_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Std_DTreeMap_Internal_Impl_getEntryGED(v_00_u03b1_2458_, v_00_u03b2_2459_, v_inst_2460_, v_k_2461_, v_t_2462_, v_fallback_2463_);
lean_dec_ref(v_fallback_2463_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(lean_object* v_inst_2465_, lean_object* v_k_2466_, lean_object* v_t_2467_, lean_object* v_fallback_2468_){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; 
v___x_2469_ = lean_box(0);
v___x_2470_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2465_, v_k_2466_, v___x_2469_, v_t_2467_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_inc_ref(v_fallback_2468_);
return v_fallback_2468_;
}
else
{
lean_object* v_val_2471_; 
v_val_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_val_2471_);
lean_dec_ref(v___x_2470_);
return v_val_2471_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg___boxed(lean_object* v_inst_2472_, lean_object* v_k_2473_, lean_object* v_t_2474_, lean_object* v_fallback_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(v_inst_2472_, v_k_2473_, v_t_2474_, v_fallback_2475_);
lean_dec_ref(v_fallback_2475_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD(lean_object* v_00_u03b1_2477_, lean_object* v_00_u03b2_2478_, lean_object* v_inst_2479_, lean_object* v_k_2480_, lean_object* v_t_2481_, lean_object* v_fallback_2482_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; 
v___x_2483_ = lean_box(0);
v___x_2484_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2479_, v_k_2480_, v___x_2483_, v_t_2481_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_inc_ref(v_fallback_2482_);
return v_fallback_2482_;
}
else
{
lean_object* v_val_2485_; 
v_val_2485_ = lean_ctor_get(v___x_2484_, 0);
lean_inc(v_val_2485_);
lean_dec_ref(v___x_2484_);
return v_val_2485_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___boxed(lean_object* v_00_u03b1_2486_, lean_object* v_00_u03b2_2487_, lean_object* v_inst_2488_, lean_object* v_k_2489_, lean_object* v_t_2490_, lean_object* v_fallback_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD(v_00_u03b1_2486_, v_00_u03b2_2487_, v_inst_2488_, v_k_2489_, v_t_2490_, v_fallback_2491_);
lean_dec_ref(v_fallback_2491_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(lean_object* v_inst_2493_, lean_object* v_k_2494_, lean_object* v_t_2495_, lean_object* v_fallback_2496_){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2497_ = lean_box(0);
v___x_2498_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2493_, v_k_2494_, v___x_2497_, v_t_2495_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_inc_ref(v_fallback_2496_);
return v_fallback_2496_;
}
else
{
lean_object* v_val_2499_; 
v_val_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_val_2499_);
lean_dec_ref(v___x_2498_);
return v_val_2499_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg___boxed(lean_object* v_inst_2500_, lean_object* v_k_2501_, lean_object* v_t_2502_, lean_object* v_fallback_2503_){
_start:
{
lean_object* v_res_2504_; 
v_res_2504_ = l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(v_inst_2500_, v_k_2501_, v_t_2502_, v_fallback_2503_);
lean_dec_ref(v_fallback_2503_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED(lean_object* v_00_u03b1_2505_, lean_object* v_00_u03b2_2506_, lean_object* v_inst_2507_, lean_object* v_k_2508_, lean_object* v_t_2509_, lean_object* v_fallback_2510_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = lean_box(0);
v___x_2512_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2507_, v_k_2508_, v___x_2511_, v_t_2509_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_inc_ref(v_fallback_2510_);
return v_fallback_2510_;
}
else
{
lean_object* v_val_2513_; 
v_val_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_val_2513_);
lean_dec_ref(v___x_2512_);
return v_val_2513_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___boxed(lean_object* v_00_u03b1_2514_, lean_object* v_00_u03b2_2515_, lean_object* v_inst_2516_, lean_object* v_k_2517_, lean_object* v_t_2518_, lean_object* v_fallback_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Std_DTreeMap_Internal_Impl_getEntryLED(v_00_u03b1_2514_, v_00_u03b2_2515_, v_inst_2516_, v_k_2517_, v_t_2518_, v_fallback_2519_);
lean_dec_ref(v_fallback_2519_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(lean_object* v_inst_2521_, lean_object* v_k_2522_, lean_object* v_t_2523_, lean_object* v_fallback_2524_){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = lean_box(0);
v___x_2526_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2521_, v_k_2522_, v___x_2525_, v_t_2523_);
if (lean_obj_tag(v___x_2526_) == 0)
{
lean_inc_ref(v_fallback_2524_);
return v_fallback_2524_;
}
else
{
lean_object* v_val_2527_; 
v_val_2527_ = lean_ctor_get(v___x_2526_, 0);
lean_inc(v_val_2527_);
lean_dec_ref(v___x_2526_);
return v_val_2527_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg___boxed(lean_object* v_inst_2528_, lean_object* v_k_2529_, lean_object* v_t_2530_, lean_object* v_fallback_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(v_inst_2528_, v_k_2529_, v_t_2530_, v_fallback_2531_);
lean_dec_ref(v_fallback_2531_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD(lean_object* v_00_u03b1_2533_, lean_object* v_00_u03b2_2534_, lean_object* v_inst_2535_, lean_object* v_k_2536_, lean_object* v_t_2537_, lean_object* v_fallback_2538_){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_box(0);
v___x_2540_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2535_, v_k_2536_, v___x_2539_, v_t_2537_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_inc_ref(v_fallback_2538_);
return v_fallback_2538_;
}
else
{
lean_object* v_val_2541_; 
v_val_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_val_2541_);
lean_dec_ref(v___x_2540_);
return v_val_2541_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___boxed(lean_object* v_00_u03b1_2542_, lean_object* v_00_u03b2_2543_, lean_object* v_inst_2544_, lean_object* v_k_2545_, lean_object* v_t_2546_, lean_object* v_fallback_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD(v_00_u03b1_2542_, v_00_u03b2_2543_, v_inst_2544_, v_k_2545_, v_t_2546_, v_fallback_2547_);
lean_dec_ref(v_fallback_2547_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(lean_object* v_inst_2549_, lean_object* v_k_2550_, lean_object* v_x_2551_){
_start:
{
lean_object* v_k_2552_; lean_object* v_v_2553_; lean_object* v_l_2554_; lean_object* v_r_2555_; lean_object* v___x_2556_; uint8_t v___x_2557_; 
v_k_2552_ = lean_ctor_get(v_x_2551_, 1);
lean_inc(v_k_2552_);
v_v_2553_ = lean_ctor_get(v_x_2551_, 2);
lean_inc(v_v_2553_);
v_l_2554_ = lean_ctor_get(v_x_2551_, 3);
lean_inc(v_l_2554_);
v_r_2555_ = lean_ctor_get(v_x_2551_, 4);
lean_inc(v_r_2555_);
lean_dec(v_x_2551_);
lean_inc_ref(v_inst_2549_);
lean_inc(v_k_2552_);
lean_inc(v_k_2550_);
v___x_2556_ = lean_apply_2(v_inst_2549_, v_k_2550_, v_k_2552_);
v___x_2557_ = lean_unbox(v___x_2556_);
switch(v___x_2557_)
{
case 0:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_dec(v_r_2555_);
v___x_2558_ = lean_box(0);
v___x_2559_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2549_, v_k_2550_, v___x_2558_, v_l_2554_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2560_; 
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_k_2552_);
lean_ctor_set(v___x_2560_, 1, v_v_2553_);
return v___x_2560_;
}
else
{
lean_object* v_val_2561_; 
lean_dec(v_v_2553_);
lean_dec(v_k_2552_);
v_val_2561_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_val_2561_);
lean_dec_ref(v___x_2559_);
return v_val_2561_;
}
}
case 1:
{
lean_object* v___x_2562_; 
lean_dec(v_r_2555_);
lean_dec(v_l_2554_);
lean_dec(v_k_2550_);
lean_dec_ref(v_inst_2549_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v_k_2552_);
lean_ctor_set(v___x_2562_, 1, v_v_2553_);
return v___x_2562_;
}
default: 
{
lean_dec(v_l_2554_);
lean_dec(v_v_2553_);
lean_dec(v_k_2552_);
v_x_2551_ = v_r_2555_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE(lean_object* v_00_u03b1_2564_, lean_object* v_00_u03b2_2565_, lean_object* v_inst_2566_, lean_object* v_inst_2567_, lean_object* v_k_2568_, lean_object* v_x_2569_, lean_object* v_x_2570_, lean_object* v_x_2571_){
_start:
{
lean_object* v___x_2572_; 
v___x_2572_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_inst_2566_, v_k_2568_, v_x_2569_);
return v___x_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object* v_inst_2573_, lean_object* v_k_2574_, lean_object* v_x_2575_){
_start:
{
lean_object* v_k_2576_; lean_object* v_v_2577_; lean_object* v_l_2578_; lean_object* v_r_2579_; lean_object* v___x_2580_; uint8_t v___x_2581_; uint8_t v___x_2582_; uint8_t v___x_2583_; 
v_k_2576_ = lean_ctor_get(v_x_2575_, 1);
lean_inc(v_k_2576_);
v_v_2577_ = lean_ctor_get(v_x_2575_, 2);
lean_inc(v_v_2577_);
v_l_2578_ = lean_ctor_get(v_x_2575_, 3);
lean_inc(v_l_2578_);
v_r_2579_ = lean_ctor_get(v_x_2575_, 4);
lean_inc(v_r_2579_);
lean_dec(v_x_2575_);
lean_inc_ref(v_inst_2573_);
lean_inc(v_k_2576_);
lean_inc(v_k_2574_);
v___x_2580_ = lean_apply_2(v_inst_2573_, v_k_2574_, v_k_2576_);
v___x_2581_ = 0;
v___x_2582_ = lean_unbox(v___x_2580_);
v___x_2583_ = l_instDecidableEqOrdering(v___x_2582_, v___x_2581_);
if (v___x_2583_ == 0)
{
lean_dec(v_l_2578_);
lean_dec(v_v_2577_);
lean_dec(v_k_2576_);
v_x_2575_ = v_r_2579_;
goto _start;
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; 
lean_dec(v_r_2579_);
v___x_2585_ = lean_box(0);
v___x_2586_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2573_, v_k_2574_, v___x_2585_, v_l_2578_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v_k_2576_);
lean_ctor_set(v___x_2587_, 1, v_v_2577_);
return v___x_2587_;
}
else
{
lean_object* v_val_2588_; 
lean_dec(v_v_2577_);
lean_dec(v_k_2576_);
v_val_2588_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_val_2588_);
lean_dec_ref(v___x_2586_);
return v_val_2588_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object* v_00_u03b1_2589_, lean_object* v_00_u03b2_2590_, lean_object* v_inst_2591_, lean_object* v_inst_2592_, lean_object* v_k_2593_, lean_object* v_x_2594_, lean_object* v_x_2595_, lean_object* v_x_2596_){
_start:
{
lean_object* v___x_2597_; 
v___x_2597_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_inst_2591_, v_k_2593_, v_x_2594_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object* v_inst_2598_, lean_object* v_k_2599_, lean_object* v_x_2600_){
_start:
{
lean_object* v_k_2601_; lean_object* v_v_2602_; lean_object* v_l_2603_; lean_object* v_r_2604_; lean_object* v___x_2605_; uint8_t v___x_2606_; 
v_k_2601_ = lean_ctor_get(v_x_2600_, 1);
lean_inc(v_k_2601_);
v_v_2602_ = lean_ctor_get(v_x_2600_, 2);
lean_inc(v_v_2602_);
v_l_2603_ = lean_ctor_get(v_x_2600_, 3);
lean_inc(v_l_2603_);
v_r_2604_ = lean_ctor_get(v_x_2600_, 4);
lean_inc(v_r_2604_);
lean_dec(v_x_2600_);
lean_inc_ref(v_inst_2598_);
lean_inc(v_k_2601_);
lean_inc(v_k_2599_);
v___x_2605_ = lean_apply_2(v_inst_2598_, v_k_2599_, v_k_2601_);
v___x_2606_ = lean_unbox(v___x_2605_);
switch(v___x_2606_)
{
case 0:
{
lean_dec(v_r_2604_);
lean_dec(v_v_2602_);
lean_dec(v_k_2601_);
v_x_2600_ = v_l_2603_;
goto _start;
}
case 1:
{
lean_object* v___x_2608_; 
lean_dec(v_r_2604_);
lean_dec(v_l_2603_);
lean_dec(v_k_2599_);
lean_dec_ref(v_inst_2598_);
v___x_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2608_, 0, v_k_2601_);
lean_ctor_set(v___x_2608_, 1, v_v_2602_);
return v___x_2608_;
}
default: 
{
lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec(v_l_2603_);
v___x_2609_ = lean_box(0);
v___x_2610_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2598_, v_k_2599_, v___x_2609_, v_r_2604_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v_k_2601_);
lean_ctor_set(v___x_2611_, 1, v_v_2602_);
return v___x_2611_;
}
else
{
lean_object* v_val_2612_; 
lean_dec(v_v_2602_);
lean_dec(v_k_2601_);
v_val_2612_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_val_2612_);
lean_dec_ref(v___x_2610_);
return v_val_2612_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object* v_00_u03b1_2613_, lean_object* v_00_u03b2_2614_, lean_object* v_inst_2615_, lean_object* v_inst_2616_, lean_object* v_k_2617_, lean_object* v_x_2618_, lean_object* v_x_2619_, lean_object* v_x_2620_){
_start:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_inst_2615_, v_k_2617_, v_x_2618_);
return v___x_2621_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object* v_inst_2622_, lean_object* v_k_2623_, lean_object* v_x_2624_){
_start:
{
lean_object* v_k_2625_; lean_object* v_v_2626_; lean_object* v_l_2627_; lean_object* v_r_2628_; lean_object* v___x_2629_; uint8_t v___x_2630_; uint8_t v___x_2631_; uint8_t v___x_2632_; 
v_k_2625_ = lean_ctor_get(v_x_2624_, 1);
lean_inc(v_k_2625_);
v_v_2626_ = lean_ctor_get(v_x_2624_, 2);
lean_inc(v_v_2626_);
v_l_2627_ = lean_ctor_get(v_x_2624_, 3);
lean_inc(v_l_2627_);
v_r_2628_ = lean_ctor_get(v_x_2624_, 4);
lean_inc(v_r_2628_);
lean_dec(v_x_2624_);
lean_inc_ref(v_inst_2622_);
lean_inc(v_k_2625_);
lean_inc(v_k_2623_);
v___x_2629_ = lean_apply_2(v_inst_2622_, v_k_2623_, v_k_2625_);
v___x_2630_ = 2;
v___x_2631_ = lean_unbox(v___x_2629_);
v___x_2632_ = l_instDecidableEqOrdering(v___x_2631_, v___x_2630_);
if (v___x_2632_ == 0)
{
lean_dec(v_r_2628_);
lean_dec(v_v_2626_);
lean_dec(v_k_2625_);
v_x_2624_ = v_l_2627_;
goto _start;
}
else
{
lean_object* v___x_2634_; lean_object* v___x_2635_; 
lean_dec(v_l_2627_);
v___x_2634_ = lean_box(0);
v___x_2635_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2622_, v_k_2623_, v___x_2634_, v_r_2628_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v___x_2636_; 
v___x_2636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2636_, 0, v_k_2625_);
lean_ctor_set(v___x_2636_, 1, v_v_2626_);
return v___x_2636_;
}
else
{
lean_object* v_val_2637_; 
lean_dec(v_v_2626_);
lean_dec(v_k_2625_);
v_val_2637_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_val_2637_);
lean_dec_ref(v___x_2635_);
return v_val_2637_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT(lean_object* v_00_u03b1_2638_, lean_object* v_00_u03b2_2639_, lean_object* v_inst_2640_, lean_object* v_inst_2641_, lean_object* v_k_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_, lean_object* v_x_2645_){
_start:
{
lean_object* v___x_2646_; 
v___x_2646_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_inst_2640_, v_k_2642_, v_x_2643_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object* v_inst_2647_, lean_object* v_k_2648_, lean_object* v_best_2649_, lean_object* v_a_2650_){
_start:
{
if (lean_obj_tag(v_a_2650_) == 0)
{
lean_object* v_k_2651_; lean_object* v_l_2652_; lean_object* v_r_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v_k_2651_ = lean_ctor_get(v_a_2650_, 1);
lean_inc(v_k_2651_);
v_l_2652_ = lean_ctor_get(v_a_2650_, 3);
lean_inc(v_l_2652_);
v_r_2653_ = lean_ctor_get(v_a_2650_, 4);
lean_inc(v_r_2653_);
lean_dec_ref(v_a_2650_);
lean_inc_ref(v_inst_2647_);
lean_inc(v_k_2651_);
lean_inc(v_k_2648_);
v___x_2654_ = lean_apply_2(v_inst_2647_, v_k_2648_, v_k_2651_);
v___x_2655_ = lean_unbox(v___x_2654_);
switch(v___x_2655_)
{
case 0:
{
lean_object* v___x_2656_; 
lean_dec(v_r_2653_);
lean_dec(v_best_2649_);
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v_k_2651_);
v_best_2649_ = v___x_2656_;
v_a_2650_ = v_l_2652_;
goto _start;
}
case 1:
{
lean_object* v___x_2658_; 
lean_dec(v_r_2653_);
lean_dec(v_l_2652_);
lean_dec(v_best_2649_);
lean_dec(v_k_2648_);
lean_dec_ref(v_inst_2647_);
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v_k_2651_);
return v___x_2658_;
}
default: 
{
lean_dec(v_l_2652_);
lean_dec(v_k_2651_);
v_a_2650_ = v_r_2653_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2648_);
lean_dec_ref(v_inst_2647_);
return v_best_2649_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(lean_object* v_00_u03b1_2660_, lean_object* v_00_u03b2_2661_, lean_object* v_inst_2662_, lean_object* v_k_2663_, lean_object* v_best_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2662_, v_k_2663_, v_best_2664_, v_a_2665_);
return v___x_2666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___redArg(lean_object* v_inst_2667_, lean_object* v_k_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2670_ = lean_box(0);
v___x_2671_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2667_, v_k_2668_, v___x_2670_, v_a_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(lean_object* v_00_u03b1_2672_, lean_object* v_00_u03b2_2673_, lean_object* v_inst_2674_, lean_object* v_k_2675_, lean_object* v_a_2676_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; 
v___x_2677_ = lean_box(0);
v___x_2678_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2674_, v_k_2675_, v___x_2677_, v_a_2676_);
return v___x_2678_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object* v_inst_2679_, lean_object* v_k_2680_, lean_object* v_best_2681_, lean_object* v_a_2682_){
_start:
{
if (lean_obj_tag(v_a_2682_) == 0)
{
lean_object* v_k_2683_; lean_object* v_l_2684_; lean_object* v_r_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v_k_2683_ = lean_ctor_get(v_a_2682_, 1);
lean_inc(v_k_2683_);
v_l_2684_ = lean_ctor_get(v_a_2682_, 3);
lean_inc(v_l_2684_);
v_r_2685_ = lean_ctor_get(v_a_2682_, 4);
lean_inc(v_r_2685_);
lean_dec_ref(v_a_2682_);
lean_inc_ref(v_inst_2679_);
lean_inc(v_k_2683_);
lean_inc(v_k_2680_);
v___x_2686_ = lean_apply_2(v_inst_2679_, v_k_2680_, v_k_2683_);
v___x_2687_ = lean_unbox(v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; 
lean_dec(v_r_2685_);
lean_dec(v_best_2681_);
v___x_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2688_, 0, v_k_2683_);
v_best_2681_ = v___x_2688_;
v_a_2682_ = v_l_2684_;
goto _start;
}
else
{
lean_dec(v_l_2684_);
lean_dec(v_k_2683_);
v_a_2682_ = v_r_2685_;
goto _start;
}
}
else
{
lean_dec(v_k_2680_);
lean_dec_ref(v_inst_2679_);
return v_best_2681_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(lean_object* v_00_u03b1_2691_, lean_object* v_00_u03b2_2692_, lean_object* v_inst_2693_, lean_object* v_k_2694_, lean_object* v_best_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2693_, v_k_2694_, v_best_2695_, v_a_2696_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___redArg(lean_object* v_inst_2698_, lean_object* v_k_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2701_ = lean_box(0);
v___x_2702_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2698_, v_k_2699_, v___x_2701_, v_a_2700_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(lean_object* v_00_u03b1_2703_, lean_object* v_00_u03b2_2704_, lean_object* v_inst_2705_, lean_object* v_k_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2708_ = lean_box(0);
v___x_2709_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2705_, v_k_2706_, v___x_2708_, v_a_2707_);
return v___x_2709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object* v_inst_2710_, lean_object* v_k_2711_, lean_object* v_best_2712_, lean_object* v_a_2713_){
_start:
{
if (lean_obj_tag(v_a_2713_) == 0)
{
lean_object* v_k_2714_; lean_object* v_l_2715_; lean_object* v_r_2716_; lean_object* v___x_2717_; uint8_t v___x_2718_; 
v_k_2714_ = lean_ctor_get(v_a_2713_, 1);
lean_inc(v_k_2714_);
v_l_2715_ = lean_ctor_get(v_a_2713_, 3);
lean_inc(v_l_2715_);
v_r_2716_ = lean_ctor_get(v_a_2713_, 4);
lean_inc(v_r_2716_);
lean_dec_ref(v_a_2713_);
lean_inc_ref(v_inst_2710_);
lean_inc(v_k_2714_);
lean_inc(v_k_2711_);
v___x_2717_ = lean_apply_2(v_inst_2710_, v_k_2711_, v_k_2714_);
v___x_2718_ = lean_unbox(v___x_2717_);
switch(v___x_2718_)
{
case 0:
{
lean_dec(v_r_2716_);
lean_dec(v_k_2714_);
v_a_2713_ = v_l_2715_;
goto _start;
}
case 1:
{
lean_object* v___x_2720_; 
lean_dec(v_r_2716_);
lean_dec(v_l_2715_);
lean_dec(v_best_2712_);
lean_dec(v_k_2711_);
lean_dec_ref(v_inst_2710_);
v___x_2720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_k_2714_);
return v___x_2720_;
}
default: 
{
lean_object* v___x_2721_; 
lean_dec(v_l_2715_);
lean_dec(v_best_2712_);
v___x_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_k_2714_);
v_best_2712_ = v___x_2721_;
v_a_2713_ = v_r_2716_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2711_);
lean_dec_ref(v_inst_2710_);
return v_best_2712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(lean_object* v_00_u03b1_2723_, lean_object* v_00_u03b2_2724_, lean_object* v_inst_2725_, lean_object* v_k_2726_, lean_object* v_best_2727_, lean_object* v_a_2728_){
_start:
{
lean_object* v___x_2729_; 
v___x_2729_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2725_, v_k_2726_, v_best_2727_, v_a_2728_);
return v___x_2729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___redArg(lean_object* v_inst_2730_, lean_object* v_k_2731_, lean_object* v_a_2732_){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2733_ = lean_box(0);
v___x_2734_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2730_, v_k_2731_, v___x_2733_, v_a_2732_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(lean_object* v_00_u03b1_2735_, lean_object* v_00_u03b2_2736_, lean_object* v_inst_2737_, lean_object* v_k_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = lean_box(0);
v___x_2741_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2737_, v_k_2738_, v___x_2740_, v_a_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object* v_inst_2742_, lean_object* v_k_2743_, lean_object* v_best_2744_, lean_object* v_a_2745_){
_start:
{
if (lean_obj_tag(v_a_2745_) == 0)
{
lean_object* v_k_2746_; lean_object* v_l_2747_; lean_object* v_r_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v_k_2746_ = lean_ctor_get(v_a_2745_, 1);
lean_inc(v_k_2746_);
v_l_2747_ = lean_ctor_get(v_a_2745_, 3);
lean_inc(v_l_2747_);
v_r_2748_ = lean_ctor_get(v_a_2745_, 4);
lean_inc(v_r_2748_);
lean_dec_ref(v_a_2745_);
lean_inc_ref(v_inst_2742_);
lean_inc(v_k_2746_);
lean_inc(v_k_2743_);
v___x_2749_ = lean_apply_2(v_inst_2742_, v_k_2743_, v_k_2746_);
v___x_2750_ = lean_unbox(v___x_2749_);
if (v___x_2750_ == 2)
{
lean_object* v___x_2751_; 
lean_dec(v_l_2747_);
lean_dec(v_best_2744_);
v___x_2751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2751_, 0, v_k_2746_);
v_best_2744_ = v___x_2751_;
v_a_2745_ = v_r_2748_;
goto _start;
}
else
{
lean_dec(v_r_2748_);
lean_dec(v_k_2746_);
v_a_2745_ = v_l_2747_;
goto _start;
}
}
else
{
lean_dec(v_k_2743_);
lean_dec_ref(v_inst_2742_);
return v_best_2744_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(lean_object* v_00_u03b1_2754_, lean_object* v_00_u03b2_2755_, lean_object* v_inst_2756_, lean_object* v_k_2757_, lean_object* v_best_2758_, lean_object* v_a_2759_){
_start:
{
lean_object* v___x_2760_; 
v___x_2760_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2756_, v_k_2757_, v_best_2758_, v_a_2759_);
return v___x_2760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___redArg(lean_object* v_inst_2761_, lean_object* v_k_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = lean_box(0);
v___x_2765_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2761_, v_k_2762_, v___x_2764_, v_a_2763_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(lean_object* v_00_u03b1_2766_, lean_object* v_00_u03b2_2767_, lean_object* v_inst_2768_, lean_object* v_k_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_box(0);
v___x_2772_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2768_, v_k_2769_, v___x_2771_, v_a_2770_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(lean_object* v_inst_2773_, lean_object* v_inst_2774_, lean_object* v_k_2775_, lean_object* v_t_2776_){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = lean_box(0);
v___x_2778_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2773_, v_k_2775_, v___x_2777_, v_t_2776_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2780_ = l_panic___redArg(v_inst_2774_, v___x_2779_);
return v___x_2780_;
}
else
{
lean_object* v_val_2781_; 
lean_dec(v_inst_2774_);
v_val_2781_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_val_2781_);
lean_dec_ref(v___x_2778_);
return v_val_2781_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object* v_00_u03b1_2782_, lean_object* v_00_u03b2_2783_, lean_object* v_inst_2784_, lean_object* v_inst_2785_, lean_object* v_k_2786_, lean_object* v_t_2787_){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_box(0);
v___x_2789_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2784_, v_k_2786_, v___x_2788_, v_t_2787_);
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2791_ = l_panic___redArg(v_inst_2785_, v___x_2790_);
return v___x_2791_;
}
else
{
lean_object* v_val_2792_; 
lean_dec(v_inst_2785_);
v_val_2792_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_val_2792_);
lean_dec_ref(v___x_2789_);
return v_val_2792_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(lean_object* v_inst_2793_, lean_object* v_inst_2794_, lean_object* v_k_2795_, lean_object* v_t_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_box(0);
v___x_2798_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2793_, v_k_2795_, v___x_2797_, v_t_2796_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2800_ = l_panic___redArg(v_inst_2794_, v___x_2799_);
return v___x_2800_;
}
else
{
lean_object* v_val_2801_; 
lean_dec(v_inst_2794_);
v_val_2801_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_val_2801_);
lean_dec_ref(v___x_2798_);
return v_val_2801_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object* v_00_u03b1_2802_, lean_object* v_00_u03b2_2803_, lean_object* v_inst_2804_, lean_object* v_inst_2805_, lean_object* v_k_2806_, lean_object* v_t_2807_){
_start:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = lean_box(0);
v___x_2809_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2804_, v_k_2806_, v___x_2808_, v_t_2807_);
if (lean_obj_tag(v___x_2809_) == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2811_ = l_panic___redArg(v_inst_2805_, v___x_2810_);
return v___x_2811_;
}
else
{
lean_object* v_val_2812_; 
lean_dec(v_inst_2805_);
v_val_2812_ = lean_ctor_get(v___x_2809_, 0);
lean_inc(v_val_2812_);
lean_dec_ref(v___x_2809_);
return v_val_2812_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(lean_object* v_inst_2813_, lean_object* v_inst_2814_, lean_object* v_k_2815_, lean_object* v_t_2816_){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2817_ = lean_box(0);
v___x_2818_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2813_, v_k_2815_, v___x_2817_, v_t_2816_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2819_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2820_ = l_panic___redArg(v_inst_2814_, v___x_2819_);
return v___x_2820_;
}
else
{
lean_object* v_val_2821_; 
lean_dec(v_inst_2814_);
v_val_2821_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_val_2821_);
lean_dec_ref(v___x_2818_);
return v_val_2821_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object* v_00_u03b1_2822_, lean_object* v_00_u03b2_2823_, lean_object* v_inst_2824_, lean_object* v_inst_2825_, lean_object* v_k_2826_, lean_object* v_t_2827_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_box(0);
v___x_2829_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2824_, v_k_2826_, v___x_2828_, v_t_2827_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2831_ = l_panic___redArg(v_inst_2825_, v___x_2830_);
return v___x_2831_;
}
else
{
lean_object* v_val_2832_; 
lean_dec(v_inst_2825_);
v_val_2832_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_val_2832_);
lean_dec_ref(v___x_2829_);
return v_val_2832_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(lean_object* v_inst_2833_, lean_object* v_inst_2834_, lean_object* v_k_2835_, lean_object* v_t_2836_){
_start:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2837_ = lean_box(0);
v___x_2838_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2833_, v_k_2835_, v___x_2837_, v_t_2836_);
if (lean_obj_tag(v___x_2838_) == 0)
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2840_ = l_panic___redArg(v_inst_2834_, v___x_2839_);
return v___x_2840_;
}
else
{
lean_object* v_val_2841_; 
lean_dec(v_inst_2834_);
v_val_2841_ = lean_ctor_get(v___x_2838_, 0);
lean_inc(v_val_2841_);
lean_dec_ref(v___x_2838_);
return v_val_2841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object* v_00_u03b1_2842_, lean_object* v_00_u03b2_2843_, lean_object* v_inst_2844_, lean_object* v_inst_2845_, lean_object* v_k_2846_, lean_object* v_t_2847_){
_start:
{
lean_object* v___x_2848_; lean_object* v___x_2849_; 
v___x_2848_ = lean_box(0);
v___x_2849_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2844_, v_k_2846_, v___x_2848_, v_t_2847_);
if (lean_obj_tag(v___x_2849_) == 0)
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2851_ = l_panic___redArg(v_inst_2845_, v___x_2850_);
return v___x_2851_;
}
else
{
lean_object* v_val_2852_; 
lean_dec(v_inst_2845_);
v_val_2852_ = lean_ctor_get(v___x_2849_, 0);
lean_inc(v_val_2852_);
lean_dec_ref(v___x_2849_);
return v_val_2852_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(lean_object* v_inst_2853_, lean_object* v_k_2854_, lean_object* v_t_2855_, lean_object* v_fallback_2856_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = lean_box(0);
v___x_2858_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2853_, v_k_2854_, v___x_2857_, v_t_2855_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_inc(v_fallback_2856_);
return v_fallback_2856_;
}
else
{
lean_object* v_val_2859_; 
v_val_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_val_2859_);
lean_dec_ref(v___x_2858_);
return v_val_2859_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg___boxed(lean_object* v_inst_2860_, lean_object* v_k_2861_, lean_object* v_t_2862_, lean_object* v_fallback_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(v_inst_2860_, v_k_2861_, v_t_2862_, v_fallback_2863_);
lean_dec(v_fallback_2863_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED(lean_object* v_00_u03b1_2865_, lean_object* v_00_u03b2_2866_, lean_object* v_inst_2867_, lean_object* v_k_2868_, lean_object* v_t_2869_, lean_object* v_fallback_2870_){
_start:
{
lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2871_ = lean_box(0);
v___x_2872_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2867_, v_k_2868_, v___x_2871_, v_t_2869_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_inc(v_fallback_2870_);
return v_fallback_2870_;
}
else
{
lean_object* v_val_2873_; 
v_val_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_val_2873_);
lean_dec_ref(v___x_2872_);
return v_val_2873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___boxed(lean_object* v_00_u03b1_2874_, lean_object* v_00_u03b2_2875_, lean_object* v_inst_2876_, lean_object* v_k_2877_, lean_object* v_t_2878_, lean_object* v_fallback_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_Std_DTreeMap_Internal_Impl_getKeyGED(v_00_u03b1_2874_, v_00_u03b2_2875_, v_inst_2876_, v_k_2877_, v_t_2878_, v_fallback_2879_);
lean_dec(v_fallback_2879_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(lean_object* v_inst_2881_, lean_object* v_k_2882_, lean_object* v_t_2883_, lean_object* v_fallback_2884_){
_start:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; 
v___x_2885_ = lean_box(0);
v___x_2886_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2881_, v_k_2882_, v___x_2885_, v_t_2883_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_inc(v_fallback_2884_);
return v_fallback_2884_;
}
else
{
lean_object* v_val_2887_; 
v_val_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_val_2887_);
lean_dec_ref(v___x_2886_);
return v_val_2887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg___boxed(lean_object* v_inst_2888_, lean_object* v_k_2889_, lean_object* v_t_2890_, lean_object* v_fallback_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(v_inst_2888_, v_k_2889_, v_t_2890_, v_fallback_2891_);
lean_dec(v_fallback_2891_);
return v_res_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD(lean_object* v_00_u03b1_2893_, lean_object* v_00_u03b2_2894_, lean_object* v_inst_2895_, lean_object* v_k_2896_, lean_object* v_t_2897_, lean_object* v_fallback_2898_){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; 
v___x_2899_ = lean_box(0);
v___x_2900_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2895_, v_k_2896_, v___x_2899_, v_t_2897_);
if (lean_obj_tag(v___x_2900_) == 0)
{
lean_inc(v_fallback_2898_);
return v_fallback_2898_;
}
else
{
lean_object* v_val_2901_; 
v_val_2901_ = lean_ctor_get(v___x_2900_, 0);
lean_inc(v_val_2901_);
lean_dec_ref(v___x_2900_);
return v_val_2901_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___boxed(lean_object* v_00_u03b1_2902_, lean_object* v_00_u03b2_2903_, lean_object* v_inst_2904_, lean_object* v_k_2905_, lean_object* v_t_2906_, lean_object* v_fallback_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD(v_00_u03b1_2902_, v_00_u03b2_2903_, v_inst_2904_, v_k_2905_, v_t_2906_, v_fallback_2907_);
lean_dec(v_fallback_2907_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(lean_object* v_inst_2909_, lean_object* v_k_2910_, lean_object* v_t_2911_, lean_object* v_fallback_2912_){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = lean_box(0);
v___x_2914_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2909_, v_k_2910_, v___x_2913_, v_t_2911_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_inc(v_fallback_2912_);
return v_fallback_2912_;
}
else
{
lean_object* v_val_2915_; 
v_val_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_val_2915_);
lean_dec_ref(v___x_2914_);
return v_val_2915_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg___boxed(lean_object* v_inst_2916_, lean_object* v_k_2917_, lean_object* v_t_2918_, lean_object* v_fallback_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(v_inst_2916_, v_k_2917_, v_t_2918_, v_fallback_2919_);
lean_dec(v_fallback_2919_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED(lean_object* v_00_u03b1_2921_, lean_object* v_00_u03b2_2922_, lean_object* v_inst_2923_, lean_object* v_k_2924_, lean_object* v_t_2925_, lean_object* v_fallback_2926_){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = lean_box(0);
v___x_2928_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2923_, v_k_2924_, v___x_2927_, v_t_2925_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_inc(v_fallback_2926_);
return v_fallback_2926_;
}
else
{
lean_object* v_val_2929_; 
v_val_2929_ = lean_ctor_get(v___x_2928_, 0);
lean_inc(v_val_2929_);
lean_dec_ref(v___x_2928_);
return v_val_2929_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___boxed(lean_object* v_00_u03b1_2930_, lean_object* v_00_u03b2_2931_, lean_object* v_inst_2932_, lean_object* v_k_2933_, lean_object* v_t_2934_, lean_object* v_fallback_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l_Std_DTreeMap_Internal_Impl_getKeyLED(v_00_u03b1_2930_, v_00_u03b2_2931_, v_inst_2932_, v_k_2933_, v_t_2934_, v_fallback_2935_);
lean_dec(v_fallback_2935_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(lean_object* v_inst_2937_, lean_object* v_k_2938_, lean_object* v_t_2939_, lean_object* v_fallback_2940_){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = lean_box(0);
v___x_2942_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2937_, v_k_2938_, v___x_2941_, v_t_2939_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_inc(v_fallback_2940_);
return v_fallback_2940_;
}
else
{
lean_object* v_val_2943_; 
v_val_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_val_2943_);
lean_dec_ref(v___x_2942_);
return v_val_2943_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg___boxed(lean_object* v_inst_2944_, lean_object* v_k_2945_, lean_object* v_t_2946_, lean_object* v_fallback_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(v_inst_2944_, v_k_2945_, v_t_2946_, v_fallback_2947_);
lean_dec(v_fallback_2947_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD(lean_object* v_00_u03b1_2949_, lean_object* v_00_u03b2_2950_, lean_object* v_inst_2951_, lean_object* v_k_2952_, lean_object* v_t_2953_, lean_object* v_fallback_2954_){
_start:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_box(0);
v___x_2956_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2951_, v_k_2952_, v___x_2955_, v_t_2953_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_inc(v_fallback_2954_);
return v_fallback_2954_;
}
else
{
lean_object* v_val_2957_; 
v_val_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_val_2957_);
lean_dec_ref(v___x_2956_);
return v_val_2957_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___boxed(lean_object* v_00_u03b1_2958_, lean_object* v_00_u03b2_2959_, lean_object* v_inst_2960_, lean_object* v_k_2961_, lean_object* v_t_2962_, lean_object* v_fallback_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD(v_00_u03b1_2958_, v_00_u03b2_2959_, v_inst_2960_, v_k_2961_, v_t_2962_, v_fallback_2963_);
lean_dec(v_fallback_2963_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object* v_inst_2965_, lean_object* v_k_2966_, lean_object* v_x_2967_){
_start:
{
lean_object* v_k_2968_; lean_object* v_l_2969_; lean_object* v_r_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_k_2968_ = lean_ctor_get(v_x_2967_, 1);
lean_inc(v_k_2968_);
v_l_2969_ = lean_ctor_get(v_x_2967_, 3);
lean_inc(v_l_2969_);
v_r_2970_ = lean_ctor_get(v_x_2967_, 4);
lean_inc(v_r_2970_);
lean_dec(v_x_2967_);
lean_inc_ref(v_inst_2965_);
lean_inc(v_k_2968_);
lean_inc(v_k_2966_);
v___x_2971_ = lean_apply_2(v_inst_2965_, v_k_2966_, v_k_2968_);
v___x_2972_ = lean_unbox(v___x_2971_);
switch(v___x_2972_)
{
case 0:
{
lean_object* v___x_2973_; lean_object* v___x_2974_; 
lean_dec(v_r_2970_);
v___x_2973_ = lean_box(0);
v___x_2974_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2965_, v_k_2966_, v___x_2973_, v_l_2969_);
if (lean_obj_tag(v___x_2974_) == 0)
{
return v_k_2968_;
}
else
{
lean_object* v_val_2975_; 
lean_dec(v_k_2968_);
v_val_2975_ = lean_ctor_get(v___x_2974_, 0);
lean_inc(v_val_2975_);
lean_dec_ref(v___x_2974_);
return v_val_2975_;
}
}
case 1:
{
lean_dec(v_r_2970_);
lean_dec(v_l_2969_);
lean_dec(v_k_2966_);
lean_dec_ref(v_inst_2965_);
return v_k_2968_;
}
default: 
{
lean_dec(v_l_2969_);
lean_dec(v_k_2968_);
v_x_2967_ = v_r_2970_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE(lean_object* v_00_u03b1_2977_, lean_object* v_00_u03b2_2978_, lean_object* v_inst_2979_, lean_object* v_inst_2980_, lean_object* v_k_2981_, lean_object* v_x_2982_, lean_object* v_x_2983_, lean_object* v_x_2984_){
_start:
{
lean_object* v___x_2985_; 
v___x_2985_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_inst_2979_, v_k_2981_, v_x_2982_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object* v_inst_2986_, lean_object* v_k_2987_, lean_object* v_x_2988_){
_start:
{
lean_object* v_k_2989_; lean_object* v_l_2990_; lean_object* v_r_2991_; lean_object* v___x_2992_; uint8_t v___x_2993_; uint8_t v___x_2994_; uint8_t v___x_2995_; 
v_k_2989_ = lean_ctor_get(v_x_2988_, 1);
lean_inc(v_k_2989_);
v_l_2990_ = lean_ctor_get(v_x_2988_, 3);
lean_inc(v_l_2990_);
v_r_2991_ = lean_ctor_get(v_x_2988_, 4);
lean_inc(v_r_2991_);
lean_dec(v_x_2988_);
lean_inc_ref(v_inst_2986_);
lean_inc(v_k_2989_);
lean_inc(v_k_2987_);
v___x_2992_ = lean_apply_2(v_inst_2986_, v_k_2987_, v_k_2989_);
v___x_2993_ = 0;
v___x_2994_ = lean_unbox(v___x_2992_);
v___x_2995_ = l_instDecidableEqOrdering(v___x_2994_, v___x_2993_);
if (v___x_2995_ == 0)
{
lean_dec(v_l_2990_);
lean_dec(v_k_2989_);
v_x_2988_ = v_r_2991_;
goto _start;
}
else
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
lean_dec(v_r_2991_);
v___x_2997_ = lean_box(0);
v___x_2998_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2986_, v_k_2987_, v___x_2997_, v_l_2990_);
if (lean_obj_tag(v___x_2998_) == 0)
{
return v_k_2989_;
}
else
{
lean_object* v_val_2999_; 
lean_dec(v_k_2989_);
v_val_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_val_2999_);
lean_dec_ref(v___x_2998_);
return v_val_2999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT(lean_object* v_00_u03b1_3000_, lean_object* v_00_u03b2_3001_, lean_object* v_inst_3002_, lean_object* v_inst_3003_, lean_object* v_k_3004_, lean_object* v_x_3005_, lean_object* v_x_3006_, lean_object* v_x_3007_){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_inst_3002_, v_k_3004_, v_x_3005_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object* v_inst_3009_, lean_object* v_k_3010_, lean_object* v_x_3011_){
_start:
{
lean_object* v_k_3012_; lean_object* v_l_3013_; lean_object* v_r_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v_k_3012_ = lean_ctor_get(v_x_3011_, 1);
lean_inc(v_k_3012_);
v_l_3013_ = lean_ctor_get(v_x_3011_, 3);
lean_inc(v_l_3013_);
v_r_3014_ = lean_ctor_get(v_x_3011_, 4);
lean_inc(v_r_3014_);
lean_dec(v_x_3011_);
lean_inc_ref(v_inst_3009_);
lean_inc(v_k_3012_);
lean_inc(v_k_3010_);
v___x_3015_ = lean_apply_2(v_inst_3009_, v_k_3010_, v_k_3012_);
v___x_3016_ = lean_unbox(v___x_3015_);
switch(v___x_3016_)
{
case 0:
{
lean_dec(v_r_3014_);
lean_dec(v_k_3012_);
v_x_3011_ = v_l_3013_;
goto _start;
}
case 1:
{
lean_dec(v_r_3014_);
lean_dec(v_l_3013_);
lean_dec(v_k_3010_);
lean_dec_ref(v_inst_3009_);
return v_k_3012_;
}
default: 
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
lean_dec(v_l_3013_);
v___x_3018_ = lean_box(0);
v___x_3019_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3009_, v_k_3010_, v___x_3018_, v_r_3014_);
if (lean_obj_tag(v___x_3019_) == 0)
{
return v_k_3012_;
}
else
{
lean_object* v_val_3020_; 
lean_dec(v_k_3012_);
v_val_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_val_3020_);
lean_dec_ref(v___x_3019_);
return v_val_3020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE(lean_object* v_00_u03b1_3021_, lean_object* v_00_u03b2_3022_, lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_k_3025_, lean_object* v_x_3026_, lean_object* v_x_3027_, lean_object* v_x_3028_){
_start:
{
lean_object* v___x_3029_; 
v___x_3029_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_inst_3023_, v_k_3025_, v_x_3026_);
return v___x_3029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object* v_inst_3030_, lean_object* v_k_3031_, lean_object* v_x_3032_){
_start:
{
lean_object* v_k_3033_; lean_object* v_l_3034_; lean_object* v_r_3035_; lean_object* v___x_3036_; uint8_t v___x_3037_; uint8_t v___x_3038_; uint8_t v___x_3039_; 
v_k_3033_ = lean_ctor_get(v_x_3032_, 1);
lean_inc(v_k_3033_);
v_l_3034_ = lean_ctor_get(v_x_3032_, 3);
lean_inc(v_l_3034_);
v_r_3035_ = lean_ctor_get(v_x_3032_, 4);
lean_inc(v_r_3035_);
lean_dec(v_x_3032_);
lean_inc_ref(v_inst_3030_);
lean_inc(v_k_3033_);
lean_inc(v_k_3031_);
v___x_3036_ = lean_apply_2(v_inst_3030_, v_k_3031_, v_k_3033_);
v___x_3037_ = 2;
v___x_3038_ = lean_unbox(v___x_3036_);
v___x_3039_ = l_instDecidableEqOrdering(v___x_3038_, v___x_3037_);
if (v___x_3039_ == 0)
{
lean_dec(v_r_3035_);
lean_dec(v_k_3033_);
v_x_3032_ = v_l_3034_;
goto _start;
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
lean_dec(v_l_3034_);
v___x_3041_ = lean_box(0);
v___x_3042_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3030_, v_k_3031_, v___x_3041_, v_r_3035_);
if (lean_obj_tag(v___x_3042_) == 0)
{
return v_k_3033_;
}
else
{
lean_object* v_val_3043_; 
lean_dec(v_k_3033_);
v_val_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_val_3043_);
lean_dec_ref(v___x_3042_);
return v_val_3043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT(lean_object* v_00_u03b1_3044_, lean_object* v_00_u03b2_3045_, lean_object* v_inst_3046_, lean_object* v_inst_3047_, lean_object* v_k_3048_, lean_object* v_x_3049_, lean_object* v_x_3050_, lean_object* v_x_3051_){
_start:
{
lean_object* v___x_3052_; 
v___x_3052_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_inst_3046_, v_k_3048_, v_x_3049_);
return v___x_3052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object* v_x_3053_){
_start:
{
if (lean_obj_tag(v_x_3053_) == 0)
{
lean_object* v_l_3054_; 
v_l_3054_ = lean_ctor_get(v_x_3053_, 3);
if (lean_obj_tag(v_l_3054_) == 0)
{
v_x_3053_ = v_l_3054_;
goto _start;
}
else
{
lean_object* v_k_3056_; lean_object* v_v_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v_k_3056_ = lean_ctor_get(v_x_3053_, 1);
v_v_3057_ = lean_ctor_get(v_x_3053_, 2);
lean_inc(v_v_3057_);
lean_inc(v_k_3056_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v_k_3056_);
lean_ctor_set(v___x_3058_, 1, v_v_3057_);
v___x_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
return v___x_3059_;
}
}
else
{
lean_object* v___x_3060_; 
v___x_3060_ = lean_box(0);
return v___x_3060_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg___boxed(lean_object* v_x_3061_){
_start:
{
lean_object* v_res_3062_; 
v_res_3062_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3061_);
lean_dec(v_x_3061_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(lean_object* v_00_u03b1_3063_, lean_object* v_00_u03b2_3064_, lean_object* v_x_3065_){
_start:
{
lean_object* v___x_3066_; 
v___x_3066_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3065_);
return v___x_3066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_3067_, lean_object* v_00_u03b2_3068_, lean_object* v_x_3069_){
_start:
{
lean_object* v_res_3070_; 
v_res_3070_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(v_00_u03b1_3067_, v_00_u03b2_3068_, v_x_3069_);
lean_dec(v_x_3069_);
return v_res_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3071_, lean_object* v_h__1_3072_, lean_object* v_h__2_3073_, lean_object* v_h__3_3074_){
_start:
{
if (lean_obj_tag(v_x_3071_) == 0)
{
lean_object* v_l_3075_; 
lean_dec(v_h__1_3072_);
v_l_3075_ = lean_ctor_get(v_x_3071_, 3);
if (lean_obj_tag(v_l_3075_) == 0)
{
lean_object* v_size_3076_; lean_object* v_k_3077_; lean_object* v_v_3078_; lean_object* v_r_3079_; lean_object* v_size_3080_; lean_object* v_k_3081_; lean_object* v_v_3082_; lean_object* v_l_3083_; lean_object* v_r_3084_; lean_object* v___x_3085_; 
lean_inc_ref(v_l_3075_);
lean_dec(v_h__2_3073_);
v_size_3076_ = lean_ctor_get(v_x_3071_, 0);
lean_inc(v_size_3076_);
v_k_3077_ = lean_ctor_get(v_x_3071_, 1);
lean_inc(v_k_3077_);
v_v_3078_ = lean_ctor_get(v_x_3071_, 2);
lean_inc(v_v_3078_);
v_r_3079_ = lean_ctor_get(v_x_3071_, 4);
lean_inc(v_r_3079_);
lean_dec_ref(v_x_3071_);
v_size_3080_ = lean_ctor_get(v_l_3075_, 0);
lean_inc(v_size_3080_);
v_k_3081_ = lean_ctor_get(v_l_3075_, 1);
lean_inc(v_k_3081_);
v_v_3082_ = lean_ctor_get(v_l_3075_, 2);
lean_inc(v_v_3082_);
v_l_3083_ = lean_ctor_get(v_l_3075_, 3);
lean_inc(v_l_3083_);
v_r_3084_ = lean_ctor_get(v_l_3075_, 4);
lean_inc(v_r_3084_);
lean_dec_ref(v_l_3075_);
v___x_3085_ = lean_apply_9(v_h__3_3074_, v_size_3076_, v_k_3077_, v_v_3078_, v_size_3080_, v_k_3081_, v_v_3082_, v_l_3083_, v_r_3084_, v_r_3079_);
return v___x_3085_;
}
else
{
lean_object* v_size_3086_; lean_object* v_k_3087_; lean_object* v_v_3088_; lean_object* v_r_3089_; lean_object* v___x_3090_; 
lean_dec(v_h__3_3074_);
v_size_3086_ = lean_ctor_get(v_x_3071_, 0);
lean_inc(v_size_3086_);
v_k_3087_ = lean_ctor_get(v_x_3071_, 1);
lean_inc(v_k_3087_);
v_v_3088_ = lean_ctor_get(v_x_3071_, 2);
lean_inc(v_v_3088_);
v_r_3089_ = lean_ctor_get(v_x_3071_, 4);
lean_inc(v_r_3089_);
lean_dec_ref(v_x_3071_);
v___x_3090_ = lean_apply_4(v_h__2_3073_, v_size_3086_, v_k_3087_, v_v_3088_, v_r_3089_);
return v___x_3090_;
}
}
else
{
lean_object* v___x_3091_; lean_object* v___x_3092_; 
lean_dec(v_h__3_3074_);
lean_dec(v_h__2_3073_);
v___x_3091_ = lean_box(0);
v___x_3092_ = lean_apply_1(v_h__1_3072_, v___x_3091_);
return v___x_3092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3093_, lean_object* v_00_u03b2_3094_, lean_object* v_motive_3095_, lean_object* v_x_3096_, lean_object* v_h__1_3097_, lean_object* v_h__2_3098_, lean_object* v_h__3_3099_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 0)
{
lean_object* v_l_3100_; 
lean_dec(v_h__1_3097_);
v_l_3100_ = lean_ctor_get(v_x_3096_, 3);
if (lean_obj_tag(v_l_3100_) == 0)
{
lean_object* v_size_3101_; lean_object* v_k_3102_; lean_object* v_v_3103_; lean_object* v_r_3104_; lean_object* v_size_3105_; lean_object* v_k_3106_; lean_object* v_v_3107_; lean_object* v_l_3108_; lean_object* v_r_3109_; lean_object* v___x_3110_; 
lean_inc_ref(v_l_3100_);
lean_dec(v_h__2_3098_);
v_size_3101_ = lean_ctor_get(v_x_3096_, 0);
lean_inc(v_size_3101_);
v_k_3102_ = lean_ctor_get(v_x_3096_, 1);
lean_inc(v_k_3102_);
v_v_3103_ = lean_ctor_get(v_x_3096_, 2);
lean_inc(v_v_3103_);
v_r_3104_ = lean_ctor_get(v_x_3096_, 4);
lean_inc(v_r_3104_);
lean_dec_ref(v_x_3096_);
v_size_3105_ = lean_ctor_get(v_l_3100_, 0);
lean_inc(v_size_3105_);
v_k_3106_ = lean_ctor_get(v_l_3100_, 1);
lean_inc(v_k_3106_);
v_v_3107_ = lean_ctor_get(v_l_3100_, 2);
lean_inc(v_v_3107_);
v_l_3108_ = lean_ctor_get(v_l_3100_, 3);
lean_inc(v_l_3108_);
v_r_3109_ = lean_ctor_get(v_l_3100_, 4);
lean_inc(v_r_3109_);
lean_dec_ref(v_l_3100_);
v___x_3110_ = lean_apply_9(v_h__3_3099_, v_size_3101_, v_k_3102_, v_v_3103_, v_size_3105_, v_k_3106_, v_v_3107_, v_l_3108_, v_r_3109_, v_r_3104_);
return v___x_3110_;
}
else
{
lean_object* v_size_3111_; lean_object* v_k_3112_; lean_object* v_v_3113_; lean_object* v_r_3114_; lean_object* v___x_3115_; 
lean_dec(v_h__3_3099_);
v_size_3111_ = lean_ctor_get(v_x_3096_, 0);
lean_inc(v_size_3111_);
v_k_3112_ = lean_ctor_get(v_x_3096_, 1);
lean_inc(v_k_3112_);
v_v_3113_ = lean_ctor_get(v_x_3096_, 2);
lean_inc(v_v_3113_);
v_r_3114_ = lean_ctor_get(v_x_3096_, 4);
lean_inc(v_r_3114_);
lean_dec_ref(v_x_3096_);
v___x_3115_ = lean_apply_4(v_h__2_3098_, v_size_3111_, v_k_3112_, v_v_3113_, v_r_3114_);
return v___x_3115_;
}
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec(v_h__3_3099_);
lean_dec(v_h__2_3098_);
v___x_3116_ = lean_box(0);
v___x_3117_ = lean_apply_1(v_h__1_3097_, v___x_3116_);
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object* v_x_3118_){
_start:
{
lean_object* v_l_3119_; 
v_l_3119_ = lean_ctor_get(v_x_3118_, 3);
if (lean_obj_tag(v_l_3119_) == 0)
{
v_x_3118_ = v_l_3119_;
goto _start;
}
else
{
lean_object* v_k_3121_; lean_object* v_v_3122_; lean_object* v___x_3123_; 
v_k_3121_ = lean_ctor_get(v_x_3118_, 1);
v_v_3122_ = lean_ctor_get(v_x_3118_, 2);
lean_inc(v_v_3122_);
lean_inc(v_k_3121_);
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v_k_3121_);
lean_ctor_set(v___x_3123_, 1, v_v_3122_);
return v___x_3123_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg___boxed(lean_object* v_x_3124_){
_start:
{
lean_object* v_res_3125_; 
v_res_3125_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3124_);
lean_dec(v_x_3124_);
return v_res_3125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry(lean_object* v_00_u03b1_3126_, lean_object* v_00_u03b2_3127_, lean_object* v_x_3128_, lean_object* v_x_3129_){
_start:
{
lean_object* v___x_3130_; 
v___x_3130_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3128_);
return v___x_3130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___boxed(lean_object* v_00_u03b1_3131_, lean_object* v_00_u03b2_3132_, lean_object* v_x_3133_, lean_object* v_x_3134_){
_start:
{
lean_object* v_res_3135_; 
v_res_3135_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry(v_00_u03b1_3131_, v_00_u03b2_3132_, v_x_3133_, v_x_3134_);
lean_dec(v_x_3133_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_3136_, lean_object* v_h__1_3137_, lean_object* v_h__2_3138_){
_start:
{
lean_object* v_l_3139_; 
v_l_3139_ = lean_ctor_get(v_x_3136_, 3);
if (lean_obj_tag(v_l_3139_) == 0)
{
lean_object* v_size_3140_; lean_object* v_k_3141_; lean_object* v_v_3142_; lean_object* v_r_3143_; lean_object* v_size_3144_; lean_object* v_k_3145_; lean_object* v_v_3146_; lean_object* v_l_3147_; lean_object* v_r_3148_; lean_object* v___x_3149_; 
lean_inc_ref(v_l_3139_);
lean_dec(v_h__1_3137_);
v_size_3140_ = lean_ctor_get(v_x_3136_, 0);
lean_inc(v_size_3140_);
v_k_3141_ = lean_ctor_get(v_x_3136_, 1);
lean_inc(v_k_3141_);
v_v_3142_ = lean_ctor_get(v_x_3136_, 2);
lean_inc(v_v_3142_);
v_r_3143_ = lean_ctor_get(v_x_3136_, 4);
lean_inc(v_r_3143_);
lean_dec(v_x_3136_);
v_size_3144_ = lean_ctor_get(v_l_3139_, 0);
lean_inc(v_size_3144_);
v_k_3145_ = lean_ctor_get(v_l_3139_, 1);
lean_inc(v_k_3145_);
v_v_3146_ = lean_ctor_get(v_l_3139_, 2);
lean_inc(v_v_3146_);
v_l_3147_ = lean_ctor_get(v_l_3139_, 3);
lean_inc(v_l_3147_);
v_r_3148_ = lean_ctor_get(v_l_3139_, 4);
lean_inc(v_r_3148_);
lean_dec_ref(v_l_3139_);
v___x_3149_ = lean_apply_10(v_h__2_3138_, v_size_3140_, v_k_3141_, v_v_3142_, v_size_3144_, v_k_3145_, v_v_3146_, v_l_3147_, v_r_3148_, v_r_3143_, lean_box(0));
return v___x_3149_;
}
else
{
lean_object* v_size_3150_; lean_object* v_k_3151_; lean_object* v_v_3152_; lean_object* v_r_3153_; lean_object* v___x_3154_; 
lean_dec(v_h__2_3138_);
v_size_3150_ = lean_ctor_get(v_x_3136_, 0);
lean_inc(v_size_3150_);
v_k_3151_ = lean_ctor_get(v_x_3136_, 1);
lean_inc(v_k_3151_);
v_v_3152_ = lean_ctor_get(v_x_3136_, 2);
lean_inc(v_v_3152_);
v_r_3153_ = lean_ctor_get(v_x_3136_, 4);
lean_inc(v_r_3153_);
lean_dec(v_x_3136_);
v___x_3154_ = lean_apply_5(v_h__1_3137_, v_size_3150_, v_k_3151_, v_v_3152_, v_r_3153_, lean_box(0));
return v___x_3154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_3155_, lean_object* v_00_u03b2_3156_, lean_object* v_motive_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_, lean_object* v_h__1_3160_, lean_object* v_h__2_3161_){
_start:
{
lean_object* v_l_3162_; 
v_l_3162_ = lean_ctor_get(v_x_3158_, 3);
if (lean_obj_tag(v_l_3162_) == 0)
{
lean_object* v_size_3163_; lean_object* v_k_3164_; lean_object* v_v_3165_; lean_object* v_r_3166_; lean_object* v_size_3167_; lean_object* v_k_3168_; lean_object* v_v_3169_; lean_object* v_l_3170_; lean_object* v_r_3171_; lean_object* v___x_3172_; 
lean_inc_ref(v_l_3162_);
lean_dec(v_h__1_3160_);
v_size_3163_ = lean_ctor_get(v_x_3158_, 0);
lean_inc(v_size_3163_);
v_k_3164_ = lean_ctor_get(v_x_3158_, 1);
lean_inc(v_k_3164_);
v_v_3165_ = lean_ctor_get(v_x_3158_, 2);
lean_inc(v_v_3165_);
v_r_3166_ = lean_ctor_get(v_x_3158_, 4);
lean_inc(v_r_3166_);
lean_dec(v_x_3158_);
v_size_3167_ = lean_ctor_get(v_l_3162_, 0);
lean_inc(v_size_3167_);
v_k_3168_ = lean_ctor_get(v_l_3162_, 1);
lean_inc(v_k_3168_);
v_v_3169_ = lean_ctor_get(v_l_3162_, 2);
lean_inc(v_v_3169_);
v_l_3170_ = lean_ctor_get(v_l_3162_, 3);
lean_inc(v_l_3170_);
v_r_3171_ = lean_ctor_get(v_l_3162_, 4);
lean_inc(v_r_3171_);
lean_dec_ref(v_l_3162_);
v___x_3172_ = lean_apply_10(v_h__2_3161_, v_size_3163_, v_k_3164_, v_v_3165_, v_size_3167_, v_k_3168_, v_v_3169_, v_l_3170_, v_r_3171_, v_r_3166_, lean_box(0));
return v___x_3172_;
}
else
{
lean_object* v_size_3173_; lean_object* v_k_3174_; lean_object* v_v_3175_; lean_object* v_r_3176_; lean_object* v___x_3177_; 
lean_dec(v_h__2_3161_);
v_size_3173_ = lean_ctor_get(v_x_3158_, 0);
lean_inc(v_size_3173_);
v_k_3174_ = lean_ctor_get(v_x_3158_, 1);
lean_inc(v_k_3174_);
v_v_3175_ = lean_ctor_get(v_x_3158_, 2);
lean_inc(v_v_3175_);
v_r_3176_ = lean_ctor_get(v_x_3158_, 4);
lean_inc(v_r_3176_);
lean_dec(v_x_3158_);
v___x_3177_ = lean_apply_5(v_h__1_3160_, v_size_3173_, v_k_3174_, v_v_3175_, v_r_3176_, lean_box(0));
return v___x_3177_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3179_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3180_ = lean_unsigned_to_nat(13u);
v___x_3181_ = lean_unsigned_to_nat(816u);
v___x_3182_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0));
v___x_3183_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3184_ = l_mkPanicMessageWithDecl(v___x_3183_, v___x_3182_, v___x_3181_, v___x_3180_, v___x_3179_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object* v_inst_3185_, lean_object* v_x_3186_){
_start:
{
if (lean_obj_tag(v_x_3186_) == 0)
{
lean_object* v_l_3187_; 
v_l_3187_ = lean_ctor_get(v_x_3186_, 3);
if (lean_obj_tag(v_l_3187_) == 0)
{
v_x_3186_ = v_l_3187_;
goto _start;
}
else
{
lean_object* v_k_3189_; lean_object* v_v_3190_; lean_object* v___x_3191_; 
lean_dec_ref(v_inst_3185_);
v_k_3189_ = lean_ctor_get(v_x_3186_, 1);
v_v_3190_ = lean_ctor_get(v_x_3186_, 2);
lean_inc(v_v_3190_);
lean_inc(v_k_3189_);
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v_k_3189_);
lean_ctor_set(v___x_3191_, 1, v_v_3190_);
return v___x_3191_;
}
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3192_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1);
v___x_3193_ = l_panic___redArg(v_inst_3185_, v___x_3192_);
return v___x_3193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_3194_, lean_object* v_x_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3194_, v_x_3195_);
lean_dec(v_x_3195_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(lean_object* v_00_u03b1_3197_, lean_object* v_00_u03b2_3198_, lean_object* v_inst_3199_, lean_object* v_x_3200_){
_start:
{
lean_object* v___x_3201_; 
v___x_3201_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3199_, v_x_3200_);
return v___x_3201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_3202_, lean_object* v_00_u03b2_3203_, lean_object* v_inst_3204_, lean_object* v_x_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(v_00_u03b1_3202_, v_00_u03b2_3203_, v_inst_3204_, v_x_3205_);
lean_dec(v_x_3205_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object* v_x_3207_, lean_object* v_x_3208_){
_start:
{
if (lean_obj_tag(v_x_3207_) == 0)
{
lean_object* v_l_3209_; 
v_l_3209_ = lean_ctor_get(v_x_3207_, 3);
if (lean_obj_tag(v_l_3209_) == 0)
{
v_x_3207_ = v_l_3209_;
goto _start;
}
else
{
lean_object* v_k_3211_; lean_object* v_v_3212_; lean_object* v___x_3213_; 
v_k_3211_ = lean_ctor_get(v_x_3207_, 1);
v_v_3212_ = lean_ctor_get(v_x_3207_, 2);
lean_inc(v_v_3212_);
lean_inc(v_k_3211_);
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v_k_3211_);
lean_ctor_set(v___x_3213_, 1, v_v_3212_);
return v___x_3213_;
}
}
else
{
lean_inc_ref(v_x_3208_);
return v_x_3208_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg___boxed(lean_object* v_x_3214_, lean_object* v_x_3215_){
_start:
{
lean_object* v_res_3216_; 
v_res_3216_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3214_, v_x_3215_);
lean_dec_ref(v_x_3215_);
lean_dec(v_x_3214_);
return v_res_3216_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD(lean_object* v_00_u03b1_3217_, lean_object* v_00_u03b2_3218_, lean_object* v_x_3219_, lean_object* v_x_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3219_, v_x_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___boxed(lean_object* v_00_u03b1_3222_, lean_object* v_00_u03b2_3223_, lean_object* v_x_3224_, lean_object* v_x_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD(v_00_u03b1_3222_, v_00_u03b2_3223_, v_x_3224_, v_x_3225_);
lean_dec_ref(v_x_3225_);
lean_dec(v_x_3224_);
return v_res_3226_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_3227_, lean_object* v_x_3228_, lean_object* v_h__1_3229_, lean_object* v_h__2_3230_, lean_object* v_h__3_3231_){
_start:
{
if (lean_obj_tag(v_x_3227_) == 0)
{
lean_object* v_l_3232_; 
lean_dec(v_h__1_3229_);
v_l_3232_ = lean_ctor_get(v_x_3227_, 3);
if (lean_obj_tag(v_l_3232_) == 0)
{
lean_object* v_size_3233_; lean_object* v_k_3234_; lean_object* v_v_3235_; lean_object* v_r_3236_; lean_object* v_size_3237_; lean_object* v_k_3238_; lean_object* v_v_3239_; lean_object* v_l_3240_; lean_object* v_r_3241_; lean_object* v___x_3242_; 
lean_inc_ref(v_l_3232_);
lean_dec(v_h__2_3230_);
v_size_3233_ = lean_ctor_get(v_x_3227_, 0);
lean_inc(v_size_3233_);
v_k_3234_ = lean_ctor_get(v_x_3227_, 1);
lean_inc(v_k_3234_);
v_v_3235_ = lean_ctor_get(v_x_3227_, 2);
lean_inc(v_v_3235_);
v_r_3236_ = lean_ctor_get(v_x_3227_, 4);
lean_inc(v_r_3236_);
lean_dec_ref(v_x_3227_);
v_size_3237_ = lean_ctor_get(v_l_3232_, 0);
lean_inc(v_size_3237_);
v_k_3238_ = lean_ctor_get(v_l_3232_, 1);
lean_inc(v_k_3238_);
v_v_3239_ = lean_ctor_get(v_l_3232_, 2);
lean_inc(v_v_3239_);
v_l_3240_ = lean_ctor_get(v_l_3232_, 3);
lean_inc(v_l_3240_);
v_r_3241_ = lean_ctor_get(v_l_3232_, 4);
lean_inc(v_r_3241_);
lean_dec_ref(v_l_3232_);
v___x_3242_ = lean_apply_10(v_h__3_3231_, v_size_3233_, v_k_3234_, v_v_3235_, v_size_3237_, v_k_3238_, v_v_3239_, v_l_3240_, v_r_3241_, v_r_3236_, v_x_3228_);
return v___x_3242_;
}
else
{
lean_object* v_size_3243_; lean_object* v_k_3244_; lean_object* v_v_3245_; lean_object* v_r_3246_; lean_object* v___x_3247_; 
lean_dec(v_h__3_3231_);
v_size_3243_ = lean_ctor_get(v_x_3227_, 0);
lean_inc(v_size_3243_);
v_k_3244_ = lean_ctor_get(v_x_3227_, 1);
lean_inc(v_k_3244_);
v_v_3245_ = lean_ctor_get(v_x_3227_, 2);
lean_inc(v_v_3245_);
v_r_3246_ = lean_ctor_get(v_x_3227_, 4);
lean_inc(v_r_3246_);
lean_dec_ref(v_x_3227_);
v___x_3247_ = lean_apply_5(v_h__2_3230_, v_size_3243_, v_k_3244_, v_v_3245_, v_r_3246_, v_x_3228_);
return v___x_3247_;
}
}
else
{
lean_object* v___x_3248_; 
lean_dec(v_h__3_3231_);
lean_dec(v_h__2_3230_);
v___x_3248_ = lean_apply_1(v_h__1_3229_, v_x_3228_);
return v___x_3248_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_3249_, lean_object* v_00_u03b2_3250_, lean_object* v_motive_3251_, lean_object* v_x_3252_, lean_object* v_x_3253_, lean_object* v_h__1_3254_, lean_object* v_h__2_3255_, lean_object* v_h__3_3256_){
_start:
{
if (lean_obj_tag(v_x_3252_) == 0)
{
lean_object* v_l_3257_; 
lean_dec(v_h__1_3254_);
v_l_3257_ = lean_ctor_get(v_x_3252_, 3);
if (lean_obj_tag(v_l_3257_) == 0)
{
lean_object* v_size_3258_; lean_object* v_k_3259_; lean_object* v_v_3260_; lean_object* v_r_3261_; lean_object* v_size_3262_; lean_object* v_k_3263_; lean_object* v_v_3264_; lean_object* v_l_3265_; lean_object* v_r_3266_; lean_object* v___x_3267_; 
lean_inc_ref(v_l_3257_);
lean_dec(v_h__2_3255_);
v_size_3258_ = lean_ctor_get(v_x_3252_, 0);
lean_inc(v_size_3258_);
v_k_3259_ = lean_ctor_get(v_x_3252_, 1);
lean_inc(v_k_3259_);
v_v_3260_ = lean_ctor_get(v_x_3252_, 2);
lean_inc(v_v_3260_);
v_r_3261_ = lean_ctor_get(v_x_3252_, 4);
lean_inc(v_r_3261_);
lean_dec_ref(v_x_3252_);
v_size_3262_ = lean_ctor_get(v_l_3257_, 0);
lean_inc(v_size_3262_);
v_k_3263_ = lean_ctor_get(v_l_3257_, 1);
lean_inc(v_k_3263_);
v_v_3264_ = lean_ctor_get(v_l_3257_, 2);
lean_inc(v_v_3264_);
v_l_3265_ = lean_ctor_get(v_l_3257_, 3);
lean_inc(v_l_3265_);
v_r_3266_ = lean_ctor_get(v_l_3257_, 4);
lean_inc(v_r_3266_);
lean_dec_ref(v_l_3257_);
v___x_3267_ = lean_apply_10(v_h__3_3256_, v_size_3258_, v_k_3259_, v_v_3260_, v_size_3262_, v_k_3263_, v_v_3264_, v_l_3265_, v_r_3266_, v_r_3261_, v_x_3253_);
return v___x_3267_;
}
else
{
lean_object* v_size_3268_; lean_object* v_k_3269_; lean_object* v_v_3270_; lean_object* v_r_3271_; lean_object* v___x_3272_; 
lean_dec(v_h__3_3256_);
v_size_3268_ = lean_ctor_get(v_x_3252_, 0);
lean_inc(v_size_3268_);
v_k_3269_ = lean_ctor_get(v_x_3252_, 1);
lean_inc(v_k_3269_);
v_v_3270_ = lean_ctor_get(v_x_3252_, 2);
lean_inc(v_v_3270_);
v_r_3271_ = lean_ctor_get(v_x_3252_, 4);
lean_inc(v_r_3271_);
lean_dec_ref(v_x_3252_);
v___x_3272_ = lean_apply_5(v_h__2_3255_, v_size_3268_, v_k_3269_, v_v_3270_, v_r_3271_, v_x_3253_);
return v___x_3272_;
}
}
else
{
lean_object* v___x_3273_; 
lean_dec(v_h__3_3256_);
lean_dec(v_h__2_3255_);
v___x_3273_ = lean_apply_1(v_h__1_3254_, v_x_3253_);
return v___x_3273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object* v_x_3274_){
_start:
{
if (lean_obj_tag(v_x_3274_) == 0)
{
lean_object* v_r_3275_; 
v_r_3275_ = lean_ctor_get(v_x_3274_, 4);
if (lean_obj_tag(v_r_3275_) == 0)
{
v_x_3274_ = v_r_3275_;
goto _start;
}
else
{
lean_object* v_k_3277_; lean_object* v_v_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; 
v_k_3277_ = lean_ctor_get(v_x_3274_, 1);
v_v_3278_ = lean_ctor_get(v_x_3274_, 2);
lean_inc(v_v_3278_);
lean_inc(v_k_3277_);
v___x_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3279_, 0, v_k_3277_);
lean_ctor_set(v___x_3279_, 1, v_v_3278_);
v___x_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
return v___x_3280_;
}
}
else
{
lean_object* v___x_3281_; 
v___x_3281_ = lean_box(0);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg___boxed(lean_object* v_x_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3282_);
lean_dec(v_x_3282_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(lean_object* v_00_u03b1_3284_, lean_object* v_00_u03b2_3285_, lean_object* v_x_3286_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3286_);
return v___x_3287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_3288_, lean_object* v_00_u03b2_3289_, lean_object* v_x_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(v_00_u03b1_3288_, v_00_u03b2_3289_, v_x_3290_);
lean_dec(v_x_3290_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3292_, lean_object* v_h__1_3293_, lean_object* v_h__2_3294_, lean_object* v_h__3_3295_){
_start:
{
if (lean_obj_tag(v_x_3292_) == 0)
{
lean_object* v_r_3296_; 
lean_dec(v_h__1_3293_);
v_r_3296_ = lean_ctor_get(v_x_3292_, 4);
if (lean_obj_tag(v_r_3296_) == 0)
{
lean_object* v_size_3297_; lean_object* v_k_3298_; lean_object* v_v_3299_; lean_object* v_l_3300_; lean_object* v_size_3301_; lean_object* v_k_3302_; lean_object* v_v_3303_; lean_object* v_l_3304_; lean_object* v_r_3305_; lean_object* v___x_3306_; 
lean_inc_ref(v_r_3296_);
lean_dec(v_h__2_3294_);
v_size_3297_ = lean_ctor_get(v_x_3292_, 0);
lean_inc(v_size_3297_);
v_k_3298_ = lean_ctor_get(v_x_3292_, 1);
lean_inc(v_k_3298_);
v_v_3299_ = lean_ctor_get(v_x_3292_, 2);
lean_inc(v_v_3299_);
v_l_3300_ = lean_ctor_get(v_x_3292_, 3);
lean_inc(v_l_3300_);
lean_dec_ref(v_x_3292_);
v_size_3301_ = lean_ctor_get(v_r_3296_, 0);
lean_inc(v_size_3301_);
v_k_3302_ = lean_ctor_get(v_r_3296_, 1);
lean_inc(v_k_3302_);
v_v_3303_ = lean_ctor_get(v_r_3296_, 2);
lean_inc(v_v_3303_);
v_l_3304_ = lean_ctor_get(v_r_3296_, 3);
lean_inc(v_l_3304_);
v_r_3305_ = lean_ctor_get(v_r_3296_, 4);
lean_inc(v_r_3305_);
lean_dec_ref(v_r_3296_);
v___x_3306_ = lean_apply_9(v_h__3_3295_, v_size_3297_, v_k_3298_, v_v_3299_, v_l_3300_, v_size_3301_, v_k_3302_, v_v_3303_, v_l_3304_, v_r_3305_);
return v___x_3306_;
}
else
{
lean_object* v_size_3307_; lean_object* v_k_3308_; lean_object* v_v_3309_; lean_object* v_l_3310_; lean_object* v___x_3311_; 
lean_dec(v_h__3_3295_);
v_size_3307_ = lean_ctor_get(v_x_3292_, 0);
lean_inc(v_size_3307_);
v_k_3308_ = lean_ctor_get(v_x_3292_, 1);
lean_inc(v_k_3308_);
v_v_3309_ = lean_ctor_get(v_x_3292_, 2);
lean_inc(v_v_3309_);
v_l_3310_ = lean_ctor_get(v_x_3292_, 3);
lean_inc(v_l_3310_);
lean_dec_ref(v_x_3292_);
v___x_3311_ = lean_apply_4(v_h__2_3294_, v_size_3307_, v_k_3308_, v_v_3309_, v_l_3310_);
return v___x_3311_;
}
}
else
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
lean_dec(v_h__3_3295_);
lean_dec(v_h__2_3294_);
v___x_3312_ = lean_box(0);
v___x_3313_ = lean_apply_1(v_h__1_3293_, v___x_3312_);
return v___x_3313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3314_, lean_object* v_00_u03b2_3315_, lean_object* v_motive_3316_, lean_object* v_x_3317_, lean_object* v_h__1_3318_, lean_object* v_h__2_3319_, lean_object* v_h__3_3320_){
_start:
{
if (lean_obj_tag(v_x_3317_) == 0)
{
lean_object* v_r_3321_; 
lean_dec(v_h__1_3318_);
v_r_3321_ = lean_ctor_get(v_x_3317_, 4);
if (lean_obj_tag(v_r_3321_) == 0)
{
lean_object* v_size_3322_; lean_object* v_k_3323_; lean_object* v_v_3324_; lean_object* v_l_3325_; lean_object* v_size_3326_; lean_object* v_k_3327_; lean_object* v_v_3328_; lean_object* v_l_3329_; lean_object* v_r_3330_; lean_object* v___x_3331_; 
lean_inc_ref(v_r_3321_);
lean_dec(v_h__2_3319_);
v_size_3322_ = lean_ctor_get(v_x_3317_, 0);
lean_inc(v_size_3322_);
v_k_3323_ = lean_ctor_get(v_x_3317_, 1);
lean_inc(v_k_3323_);
v_v_3324_ = lean_ctor_get(v_x_3317_, 2);
lean_inc(v_v_3324_);
v_l_3325_ = lean_ctor_get(v_x_3317_, 3);
lean_inc(v_l_3325_);
lean_dec_ref(v_x_3317_);
v_size_3326_ = lean_ctor_get(v_r_3321_, 0);
lean_inc(v_size_3326_);
v_k_3327_ = lean_ctor_get(v_r_3321_, 1);
lean_inc(v_k_3327_);
v_v_3328_ = lean_ctor_get(v_r_3321_, 2);
lean_inc(v_v_3328_);
v_l_3329_ = lean_ctor_get(v_r_3321_, 3);
lean_inc(v_l_3329_);
v_r_3330_ = lean_ctor_get(v_r_3321_, 4);
lean_inc(v_r_3330_);
lean_dec_ref(v_r_3321_);
v___x_3331_ = lean_apply_9(v_h__3_3320_, v_size_3322_, v_k_3323_, v_v_3324_, v_l_3325_, v_size_3326_, v_k_3327_, v_v_3328_, v_l_3329_, v_r_3330_);
return v___x_3331_;
}
else
{
lean_object* v_size_3332_; lean_object* v_k_3333_; lean_object* v_v_3334_; lean_object* v_l_3335_; lean_object* v___x_3336_; 
lean_dec(v_h__3_3320_);
v_size_3332_ = lean_ctor_get(v_x_3317_, 0);
lean_inc(v_size_3332_);
v_k_3333_ = lean_ctor_get(v_x_3317_, 1);
lean_inc(v_k_3333_);
v_v_3334_ = lean_ctor_get(v_x_3317_, 2);
lean_inc(v_v_3334_);
v_l_3335_ = lean_ctor_get(v_x_3317_, 3);
lean_inc(v_l_3335_);
lean_dec_ref(v_x_3317_);
v___x_3336_ = lean_apply_4(v_h__2_3319_, v_size_3332_, v_k_3333_, v_v_3334_, v_l_3335_);
return v___x_3336_;
}
}
else
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
lean_dec(v_h__3_3320_);
lean_dec(v_h__2_3319_);
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_apply_1(v_h__1_3318_, v___x_3337_);
return v___x_3338_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object* v_x_3339_){
_start:
{
lean_object* v_r_3340_; 
v_r_3340_ = lean_ctor_get(v_x_3339_, 4);
if (lean_obj_tag(v_r_3340_) == 0)
{
v_x_3339_ = v_r_3340_;
goto _start;
}
else
{
lean_object* v_k_3342_; lean_object* v_v_3343_; lean_object* v___x_3344_; 
v_k_3342_ = lean_ctor_get(v_x_3339_, 1);
v_v_3343_ = lean_ctor_get(v_x_3339_, 2);
lean_inc(v_v_3343_);
lean_inc(v_k_3342_);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v_k_3342_);
lean_ctor_set(v___x_3344_, 1, v_v_3343_);
return v___x_3344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg___boxed(lean_object* v_x_3345_){
_start:
{
lean_object* v_res_3346_; 
v_res_3346_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3345_);
lean_dec(v_x_3345_);
return v_res_3346_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry(lean_object* v_00_u03b1_3347_, lean_object* v_00_u03b2_3348_, lean_object* v_x_3349_, lean_object* v_x_3350_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3349_);
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___boxed(lean_object* v_00_u03b1_3352_, lean_object* v_00_u03b2_3353_, lean_object* v_x_3354_, lean_object* v_x_3355_){
_start:
{
lean_object* v_res_3356_; 
v_res_3356_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry(v_00_u03b1_3352_, v_00_u03b2_3353_, v_x_3354_, v_x_3355_);
lean_dec(v_x_3354_);
return v_res_3356_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_3357_, lean_object* v_h__1_3358_, lean_object* v_h__2_3359_){
_start:
{
lean_object* v_r_3360_; 
v_r_3360_ = lean_ctor_get(v_x_3357_, 4);
if (lean_obj_tag(v_r_3360_) == 0)
{
lean_object* v_size_3361_; lean_object* v_k_3362_; lean_object* v_v_3363_; lean_object* v_l_3364_; lean_object* v_size_3365_; lean_object* v_k_3366_; lean_object* v_v_3367_; lean_object* v_l_3368_; lean_object* v_r_3369_; lean_object* v___x_3370_; 
lean_inc_ref(v_r_3360_);
lean_dec(v_h__1_3358_);
v_size_3361_ = lean_ctor_get(v_x_3357_, 0);
lean_inc(v_size_3361_);
v_k_3362_ = lean_ctor_get(v_x_3357_, 1);
lean_inc(v_k_3362_);
v_v_3363_ = lean_ctor_get(v_x_3357_, 2);
lean_inc(v_v_3363_);
v_l_3364_ = lean_ctor_get(v_x_3357_, 3);
lean_inc(v_l_3364_);
lean_dec(v_x_3357_);
v_size_3365_ = lean_ctor_get(v_r_3360_, 0);
lean_inc(v_size_3365_);
v_k_3366_ = lean_ctor_get(v_r_3360_, 1);
lean_inc(v_k_3366_);
v_v_3367_ = lean_ctor_get(v_r_3360_, 2);
lean_inc(v_v_3367_);
v_l_3368_ = lean_ctor_get(v_r_3360_, 3);
lean_inc(v_l_3368_);
v_r_3369_ = lean_ctor_get(v_r_3360_, 4);
lean_inc(v_r_3369_);
lean_dec_ref(v_r_3360_);
v___x_3370_ = lean_apply_10(v_h__2_3359_, v_size_3361_, v_k_3362_, v_v_3363_, v_l_3364_, v_size_3365_, v_k_3366_, v_v_3367_, v_l_3368_, v_r_3369_, lean_box(0));
return v___x_3370_;
}
else
{
lean_object* v_size_3371_; lean_object* v_k_3372_; lean_object* v_v_3373_; lean_object* v_l_3374_; lean_object* v___x_3375_; 
lean_dec(v_h__2_3359_);
v_size_3371_ = lean_ctor_get(v_x_3357_, 0);
lean_inc(v_size_3371_);
v_k_3372_ = lean_ctor_get(v_x_3357_, 1);
lean_inc(v_k_3372_);
v_v_3373_ = lean_ctor_get(v_x_3357_, 2);
lean_inc(v_v_3373_);
v_l_3374_ = lean_ctor_get(v_x_3357_, 3);
lean_inc(v_l_3374_);
lean_dec(v_x_3357_);
v___x_3375_ = lean_apply_5(v_h__1_3358_, v_size_3371_, v_k_3372_, v_v_3373_, v_l_3374_, lean_box(0));
return v___x_3375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_3376_, lean_object* v_00_u03b2_3377_, lean_object* v_motive_3378_, lean_object* v_x_3379_, lean_object* v_x_3380_, lean_object* v_h__1_3381_, lean_object* v_h__2_3382_){
_start:
{
lean_object* v_r_3383_; 
v_r_3383_ = lean_ctor_get(v_x_3379_, 4);
if (lean_obj_tag(v_r_3383_) == 0)
{
lean_object* v_size_3384_; lean_object* v_k_3385_; lean_object* v_v_3386_; lean_object* v_l_3387_; lean_object* v_size_3388_; lean_object* v_k_3389_; lean_object* v_v_3390_; lean_object* v_l_3391_; lean_object* v_r_3392_; lean_object* v___x_3393_; 
lean_inc_ref(v_r_3383_);
lean_dec(v_h__1_3381_);
v_size_3384_ = lean_ctor_get(v_x_3379_, 0);
lean_inc(v_size_3384_);
v_k_3385_ = lean_ctor_get(v_x_3379_, 1);
lean_inc(v_k_3385_);
v_v_3386_ = lean_ctor_get(v_x_3379_, 2);
lean_inc(v_v_3386_);
v_l_3387_ = lean_ctor_get(v_x_3379_, 3);
lean_inc(v_l_3387_);
lean_dec(v_x_3379_);
v_size_3388_ = lean_ctor_get(v_r_3383_, 0);
lean_inc(v_size_3388_);
v_k_3389_ = lean_ctor_get(v_r_3383_, 1);
lean_inc(v_k_3389_);
v_v_3390_ = lean_ctor_get(v_r_3383_, 2);
lean_inc(v_v_3390_);
v_l_3391_ = lean_ctor_get(v_r_3383_, 3);
lean_inc(v_l_3391_);
v_r_3392_ = lean_ctor_get(v_r_3383_, 4);
lean_inc(v_r_3392_);
lean_dec_ref(v_r_3383_);
v___x_3393_ = lean_apply_10(v_h__2_3382_, v_size_3384_, v_k_3385_, v_v_3386_, v_l_3387_, v_size_3388_, v_k_3389_, v_v_3390_, v_l_3391_, v_r_3392_, lean_box(0));
return v___x_3393_;
}
else
{
lean_object* v_size_3394_; lean_object* v_k_3395_; lean_object* v_v_3396_; lean_object* v_l_3397_; lean_object* v___x_3398_; 
lean_dec(v_h__2_3382_);
v_size_3394_ = lean_ctor_get(v_x_3379_, 0);
lean_inc(v_size_3394_);
v_k_3395_ = lean_ctor_get(v_x_3379_, 1);
lean_inc(v_k_3395_);
v_v_3396_ = lean_ctor_get(v_x_3379_, 2);
lean_inc(v_v_3396_);
v_l_3397_ = lean_ctor_get(v_x_3379_, 3);
lean_inc(v_l_3397_);
lean_dec(v_x_3379_);
v___x_3398_ = lean_apply_5(v_h__1_3381_, v_size_3394_, v_k_3395_, v_v_3396_, v_l_3397_, lean_box(0));
return v___x_3398_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3400_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3401_ = lean_unsigned_to_nat(13u);
v___x_3402_ = lean_unsigned_to_nat(839u);
v___x_3403_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0));
v___x_3404_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3405_ = l_mkPanicMessageWithDecl(v___x_3404_, v___x_3403_, v___x_3402_, v___x_3401_, v___x_3400_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object* v_inst_3406_, lean_object* v_x_3407_){
_start:
{
if (lean_obj_tag(v_x_3407_) == 0)
{
lean_object* v_r_3408_; 
v_r_3408_ = lean_ctor_get(v_x_3407_, 4);
if (lean_obj_tag(v_r_3408_) == 0)
{
v_x_3407_ = v_r_3408_;
goto _start;
}
else
{
lean_object* v_k_3410_; lean_object* v_v_3411_; lean_object* v___x_3412_; 
lean_dec_ref(v_inst_3406_);
v_k_3410_ = lean_ctor_get(v_x_3407_, 1);
v_v_3411_ = lean_ctor_get(v_x_3407_, 2);
lean_inc(v_v_3411_);
lean_inc(v_k_3410_);
v___x_3412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3412_, 0, v_k_3410_);
lean_ctor_set(v___x_3412_, 1, v_v_3411_);
return v___x_3412_;
}
}
else
{
lean_object* v___x_3413_; lean_object* v___x_3414_; 
v___x_3413_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1);
v___x_3414_ = l_panic___redArg(v_inst_3406_, v___x_3413_);
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_3415_, lean_object* v_x_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3415_, v_x_3416_);
lean_dec(v_x_3416_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(lean_object* v_00_u03b1_3418_, lean_object* v_00_u03b2_3419_, lean_object* v_inst_3420_, lean_object* v_x_3421_){
_start:
{
lean_object* v___x_3422_; 
v___x_3422_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3420_, v_x_3421_);
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_3423_, lean_object* v_00_u03b2_3424_, lean_object* v_inst_3425_, lean_object* v_x_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(v_00_u03b1_3423_, v_00_u03b2_3424_, v_inst_3425_, v_x_3426_);
lean_dec(v_x_3426_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object* v_x_3428_, lean_object* v_x_3429_){
_start:
{
if (lean_obj_tag(v_x_3428_) == 0)
{
lean_object* v_r_3430_; 
v_r_3430_ = lean_ctor_get(v_x_3428_, 4);
if (lean_obj_tag(v_r_3430_) == 0)
{
v_x_3428_ = v_r_3430_;
goto _start;
}
else
{
lean_object* v_k_3432_; lean_object* v_v_3433_; lean_object* v___x_3434_; 
v_k_3432_ = lean_ctor_get(v_x_3428_, 1);
v_v_3433_ = lean_ctor_get(v_x_3428_, 2);
lean_inc(v_v_3433_);
lean_inc(v_k_3432_);
v___x_3434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3434_, 0, v_k_3432_);
lean_ctor_set(v___x_3434_, 1, v_v_3433_);
return v___x_3434_;
}
}
else
{
lean_inc_ref(v_x_3429_);
return v_x_3429_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg___boxed(lean_object* v_x_3435_, lean_object* v_x_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3435_, v_x_3436_);
lean_dec_ref(v_x_3436_);
lean_dec(v_x_3435_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(lean_object* v_00_u03b1_3438_, lean_object* v_00_u03b2_3439_, lean_object* v_x_3440_, lean_object* v_x_3441_){
_start:
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3440_, v_x_3441_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___boxed(lean_object* v_00_u03b1_3443_, lean_object* v_00_u03b2_3444_, lean_object* v_x_3445_, lean_object* v_x_3446_){
_start:
{
lean_object* v_res_3447_; 
v_res_3447_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(v_00_u03b1_3443_, v_00_u03b2_3444_, v_x_3445_, v_x_3446_);
lean_dec_ref(v_x_3446_);
lean_dec(v_x_3445_);
return v_res_3447_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_3448_, lean_object* v_x_3449_, lean_object* v_h__1_3450_, lean_object* v_h__2_3451_, lean_object* v_h__3_3452_){
_start:
{
if (lean_obj_tag(v_x_3448_) == 0)
{
lean_object* v_r_3453_; 
lean_dec(v_h__1_3450_);
v_r_3453_ = lean_ctor_get(v_x_3448_, 4);
if (lean_obj_tag(v_r_3453_) == 0)
{
lean_object* v_size_3454_; lean_object* v_k_3455_; lean_object* v_v_3456_; lean_object* v_l_3457_; lean_object* v_size_3458_; lean_object* v_k_3459_; lean_object* v_v_3460_; lean_object* v_l_3461_; lean_object* v_r_3462_; lean_object* v___x_3463_; 
lean_inc_ref(v_r_3453_);
lean_dec(v_h__2_3451_);
v_size_3454_ = lean_ctor_get(v_x_3448_, 0);
lean_inc(v_size_3454_);
v_k_3455_ = lean_ctor_get(v_x_3448_, 1);
lean_inc(v_k_3455_);
v_v_3456_ = lean_ctor_get(v_x_3448_, 2);
lean_inc(v_v_3456_);
v_l_3457_ = lean_ctor_get(v_x_3448_, 3);
lean_inc(v_l_3457_);
lean_dec_ref(v_x_3448_);
v_size_3458_ = lean_ctor_get(v_r_3453_, 0);
lean_inc(v_size_3458_);
v_k_3459_ = lean_ctor_get(v_r_3453_, 1);
lean_inc(v_k_3459_);
v_v_3460_ = lean_ctor_get(v_r_3453_, 2);
lean_inc(v_v_3460_);
v_l_3461_ = lean_ctor_get(v_r_3453_, 3);
lean_inc(v_l_3461_);
v_r_3462_ = lean_ctor_get(v_r_3453_, 4);
lean_inc(v_r_3462_);
lean_dec_ref(v_r_3453_);
v___x_3463_ = lean_apply_10(v_h__3_3452_, v_size_3454_, v_k_3455_, v_v_3456_, v_l_3457_, v_size_3458_, v_k_3459_, v_v_3460_, v_l_3461_, v_r_3462_, v_x_3449_);
return v___x_3463_;
}
else
{
lean_object* v_size_3464_; lean_object* v_k_3465_; lean_object* v_v_3466_; lean_object* v_l_3467_; lean_object* v___x_3468_; 
lean_dec(v_h__3_3452_);
v_size_3464_ = lean_ctor_get(v_x_3448_, 0);
lean_inc(v_size_3464_);
v_k_3465_ = lean_ctor_get(v_x_3448_, 1);
lean_inc(v_k_3465_);
v_v_3466_ = lean_ctor_get(v_x_3448_, 2);
lean_inc(v_v_3466_);
v_l_3467_ = lean_ctor_get(v_x_3448_, 3);
lean_inc(v_l_3467_);
lean_dec_ref(v_x_3448_);
v___x_3468_ = lean_apply_5(v_h__2_3451_, v_size_3464_, v_k_3465_, v_v_3466_, v_l_3467_, v_x_3449_);
return v___x_3468_;
}
}
else
{
lean_object* v___x_3469_; 
lean_dec(v_h__3_3452_);
lean_dec(v_h__2_3451_);
v___x_3469_ = lean_apply_1(v_h__1_3450_, v_x_3449_);
return v___x_3469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_3470_, lean_object* v_00_u03b2_3471_, lean_object* v_motive_3472_, lean_object* v_x_3473_, lean_object* v_x_3474_, lean_object* v_h__1_3475_, lean_object* v_h__2_3476_, lean_object* v_h__3_3477_){
_start:
{
if (lean_obj_tag(v_x_3473_) == 0)
{
lean_object* v_r_3478_; 
lean_dec(v_h__1_3475_);
v_r_3478_ = lean_ctor_get(v_x_3473_, 4);
if (lean_obj_tag(v_r_3478_) == 0)
{
lean_object* v_size_3479_; lean_object* v_k_3480_; lean_object* v_v_3481_; lean_object* v_l_3482_; lean_object* v_size_3483_; lean_object* v_k_3484_; lean_object* v_v_3485_; lean_object* v_l_3486_; lean_object* v_r_3487_; lean_object* v___x_3488_; 
lean_inc_ref(v_r_3478_);
lean_dec(v_h__2_3476_);
v_size_3479_ = lean_ctor_get(v_x_3473_, 0);
lean_inc(v_size_3479_);
v_k_3480_ = lean_ctor_get(v_x_3473_, 1);
lean_inc(v_k_3480_);
v_v_3481_ = lean_ctor_get(v_x_3473_, 2);
lean_inc(v_v_3481_);
v_l_3482_ = lean_ctor_get(v_x_3473_, 3);
lean_inc(v_l_3482_);
lean_dec_ref(v_x_3473_);
v_size_3483_ = lean_ctor_get(v_r_3478_, 0);
lean_inc(v_size_3483_);
v_k_3484_ = lean_ctor_get(v_r_3478_, 1);
lean_inc(v_k_3484_);
v_v_3485_ = lean_ctor_get(v_r_3478_, 2);
lean_inc(v_v_3485_);
v_l_3486_ = lean_ctor_get(v_r_3478_, 3);
lean_inc(v_l_3486_);
v_r_3487_ = lean_ctor_get(v_r_3478_, 4);
lean_inc(v_r_3487_);
lean_dec_ref(v_r_3478_);
v___x_3488_ = lean_apply_10(v_h__3_3477_, v_size_3479_, v_k_3480_, v_v_3481_, v_l_3482_, v_size_3483_, v_k_3484_, v_v_3485_, v_l_3486_, v_r_3487_, v_x_3474_);
return v___x_3488_;
}
else
{
lean_object* v_size_3489_; lean_object* v_k_3490_; lean_object* v_v_3491_; lean_object* v_l_3492_; lean_object* v___x_3493_; 
lean_dec(v_h__3_3477_);
v_size_3489_ = lean_ctor_get(v_x_3473_, 0);
lean_inc(v_size_3489_);
v_k_3490_ = lean_ctor_get(v_x_3473_, 1);
lean_inc(v_k_3490_);
v_v_3491_ = lean_ctor_get(v_x_3473_, 2);
lean_inc(v_v_3491_);
v_l_3492_ = lean_ctor_get(v_x_3473_, 3);
lean_inc(v_l_3492_);
lean_dec_ref(v_x_3473_);
v___x_3493_ = lean_apply_5(v_h__2_3476_, v_size_3489_, v_k_3490_, v_v_3491_, v_l_3492_, v_x_3474_);
return v___x_3493_;
}
}
else
{
lean_object* v___x_3494_; 
lean_dec(v_h__3_3477_);
lean_dec(v_h__2_3476_);
v___x_3494_ = lean_apply_1(v_h__1_3475_, v_x_3474_);
return v___x_3494_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object* v_x_3495_, lean_object* v_x_3496_){
_start:
{
lean_object* v_k_3497_; lean_object* v_v_3498_; lean_object* v_l_3499_; lean_object* v_r_3500_; lean_object* v___y_3502_; lean_object* v___y_3508_; 
v_k_3497_ = lean_ctor_get(v_x_3495_, 1);
v_v_3498_ = lean_ctor_get(v_x_3495_, 2);
v_l_3499_ = lean_ctor_get(v_x_3495_, 3);
v_r_3500_ = lean_ctor_get(v_x_3495_, 4);
if (lean_obj_tag(v_l_3499_) == 0)
{
lean_object* v_size_3515_; 
v_size_3515_ = lean_ctor_get(v_l_3499_, 0);
v___y_3508_ = v_size_3515_;
goto v___jp_3507_;
}
else
{
lean_object* v___x_3516_; 
v___x_3516_ = lean_unsigned_to_nat(0u);
v___y_3508_ = v___x_3516_;
goto v___jp_3507_;
}
v___jp_3501_:
{
lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = lean_nat_sub(v_x_3496_, v___y_3502_);
lean_dec(v_x_3496_);
v___x_3504_ = lean_unsigned_to_nat(1u);
v___x_3505_ = lean_nat_sub(v___x_3503_, v___x_3504_);
lean_dec(v___x_3503_);
v_x_3495_ = v_r_3500_;
v_x_3496_ = v___x_3505_;
goto _start;
}
v___jp_3507_:
{
uint8_t v___x_3509_; 
v___x_3509_ = lean_nat_dec_lt(v_x_3496_, v___y_3508_);
if (v___x_3509_ == 0)
{
uint8_t v___x_3510_; 
v___x_3510_ = lean_nat_dec_eq(v_x_3496_, v___y_3508_);
if (v___x_3510_ == 0)
{
if (lean_obj_tag(v_l_3499_) == 0)
{
lean_object* v_size_3511_; 
v_size_3511_ = lean_ctor_get(v_l_3499_, 0);
v___y_3502_ = v_size_3511_;
goto v___jp_3501_;
}
else
{
lean_object* v___x_3512_; 
v___x_3512_ = lean_unsigned_to_nat(0u);
v___y_3502_ = v___x_3512_;
goto v___jp_3501_;
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v_x_3496_);
lean_inc(v_v_3498_);
lean_inc(v_k_3497_);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v_k_3497_);
lean_ctor_set(v___x_3513_, 1, v_v_3498_);
return v___x_3513_;
}
}
else
{
v_x_3495_ = v_l_3499_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg___boxed(lean_object* v_x_3517_, lean_object* v_x_3518_){
_start:
{
lean_object* v_res_3519_; 
v_res_3519_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3517_, v_x_3518_);
lean_dec(v_x_3517_);
return v_res_3519_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_object* v_00_u03b1_3520_, lean_object* v_00_u03b2_3521_, lean_object* v_x_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_, lean_object* v_x_3525_){
_start:
{
lean_object* v___x_3526_; 
v___x_3526_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3522_, v_x_3524_);
return v___x_3526_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_3527_, lean_object* v_00_u03b2_3528_, lean_object* v_x_3529_, lean_object* v_x_3530_, lean_object* v_x_3531_, lean_object* v_x_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(v_00_u03b1_3527_, v_00_u03b2_3528_, v_x_3529_, v_x_3530_, v_x_3531_, v_x_3532_);
lean_dec(v_x_3529_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object* v_x_3534_, lean_object* v_x_3535_){
_start:
{
if (lean_obj_tag(v_x_3534_) == 0)
{
lean_object* v_k_3536_; lean_object* v_v_3537_; lean_object* v_l_3538_; lean_object* v_r_3539_; lean_object* v___y_3541_; lean_object* v___y_3547_; 
v_k_3536_ = lean_ctor_get(v_x_3534_, 1);
v_v_3537_ = lean_ctor_get(v_x_3534_, 2);
v_l_3538_ = lean_ctor_get(v_x_3534_, 3);
v_r_3539_ = lean_ctor_get(v_x_3534_, 4);
if (lean_obj_tag(v_l_3538_) == 0)
{
lean_object* v_size_3555_; 
v_size_3555_ = lean_ctor_get(v_l_3538_, 0);
v___y_3547_ = v_size_3555_;
goto v___jp_3546_;
}
else
{
lean_object* v___x_3556_; 
v___x_3556_ = lean_unsigned_to_nat(0u);
v___y_3547_ = v___x_3556_;
goto v___jp_3546_;
}
v___jp_3540_:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3542_ = lean_nat_sub(v_x_3535_, v___y_3541_);
lean_dec(v_x_3535_);
v___x_3543_ = lean_unsigned_to_nat(1u);
v___x_3544_ = lean_nat_sub(v___x_3542_, v___x_3543_);
lean_dec(v___x_3542_);
v_x_3534_ = v_r_3539_;
v_x_3535_ = v___x_3544_;
goto _start;
}
v___jp_3546_:
{
uint8_t v___x_3548_; 
v___x_3548_ = lean_nat_dec_lt(v_x_3535_, v___y_3547_);
if (v___x_3548_ == 0)
{
uint8_t v___x_3549_; 
v___x_3549_ = lean_nat_dec_eq(v_x_3535_, v___y_3547_);
if (v___x_3549_ == 0)
{
if (lean_obj_tag(v_l_3538_) == 0)
{
lean_object* v_size_3550_; 
v_size_3550_ = lean_ctor_get(v_l_3538_, 0);
v___y_3541_ = v_size_3550_;
goto v___jp_3540_;
}
else
{
lean_object* v___x_3551_; 
v___x_3551_ = lean_unsigned_to_nat(0u);
v___y_3541_ = v___x_3551_;
goto v___jp_3540_;
}
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
lean_dec(v_x_3535_);
lean_inc(v_v_3537_);
lean_inc(v_k_3536_);
v___x_3552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3552_, 0, v_k_3536_);
lean_ctor_set(v___x_3552_, 1, v_v_3537_);
v___x_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3553_, 0, v___x_3552_);
return v___x_3553_;
}
}
else
{
v_x_3534_ = v_l_3538_;
goto _start;
}
}
}
else
{
lean_object* v___x_3557_; 
lean_dec(v_x_3535_);
v___x_3557_ = lean_box(0);
return v___x_3557_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_3558_, lean_object* v_x_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3558_, v_x_3559_);
lean_dec(v_x_3558_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_3561_, lean_object* v_00_u03b2_3562_, lean_object* v_x_3563_, lean_object* v_x_3564_){
_start:
{
lean_object* v___x_3565_; 
v___x_3565_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3563_, v_x_3564_);
return v___x_3565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_3566_, lean_object* v_00_u03b2_3567_, lean_object* v_x_3568_, lean_object* v_x_3569_){
_start:
{
lean_object* v_res_3570_; 
v_res_3570_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(v_00_u03b1_3566_, v_00_u03b2_3567_, v_x_3568_, v_x_3569_);
lean_dec(v_x_3568_);
return v_res_3570_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3572_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_3573_ = lean_unsigned_to_nat(16u);
v___x_3574_ = lean_unsigned_to_nat(870u);
v___x_3575_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0));
v___x_3576_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3577_ = l_mkPanicMessageWithDecl(v___x_3576_, v___x_3575_, v___x_3574_, v___x_3573_, v___x_3572_);
return v___x_3577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object* v_inst_3578_, lean_object* v_x_3579_, lean_object* v_x_3580_){
_start:
{
if (lean_obj_tag(v_x_3579_) == 0)
{
lean_object* v_k_3581_; lean_object* v_v_3582_; lean_object* v_l_3583_; lean_object* v_r_3584_; lean_object* v___y_3586_; lean_object* v___y_3592_; 
v_k_3581_ = lean_ctor_get(v_x_3579_, 1);
v_v_3582_ = lean_ctor_get(v_x_3579_, 2);
v_l_3583_ = lean_ctor_get(v_x_3579_, 3);
v_r_3584_ = lean_ctor_get(v_x_3579_, 4);
if (lean_obj_tag(v_l_3583_) == 0)
{
lean_object* v_size_3599_; 
v_size_3599_ = lean_ctor_get(v_l_3583_, 0);
v___y_3592_ = v_size_3599_;
goto v___jp_3591_;
}
else
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_unsigned_to_nat(0u);
v___y_3592_ = v___x_3600_;
goto v___jp_3591_;
}
v___jp_3585_:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3587_ = lean_nat_sub(v_x_3580_, v___y_3586_);
lean_dec(v_x_3580_);
v___x_3588_ = lean_unsigned_to_nat(1u);
v___x_3589_ = lean_nat_sub(v___x_3587_, v___x_3588_);
lean_dec(v___x_3587_);
v_x_3579_ = v_r_3584_;
v_x_3580_ = v___x_3589_;
goto _start;
}
v___jp_3591_:
{
uint8_t v___x_3593_; 
v___x_3593_ = lean_nat_dec_lt(v_x_3580_, v___y_3592_);
if (v___x_3593_ == 0)
{
uint8_t v___x_3594_; 
v___x_3594_ = lean_nat_dec_eq(v_x_3580_, v___y_3592_);
if (v___x_3594_ == 0)
{
if (lean_obj_tag(v_l_3583_) == 0)
{
lean_object* v_size_3595_; 
v_size_3595_ = lean_ctor_get(v_l_3583_, 0);
v___y_3586_ = v_size_3595_;
goto v___jp_3585_;
}
else
{
lean_object* v___x_3596_; 
v___x_3596_ = lean_unsigned_to_nat(0u);
v___y_3586_ = v___x_3596_;
goto v___jp_3585_;
}
}
else
{
lean_object* v___x_3597_; 
lean_dec(v_x_3580_);
lean_dec_ref(v_inst_3578_);
lean_inc(v_v_3582_);
lean_inc(v_k_3581_);
v___x_3597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3597_, 0, v_k_3581_);
lean_ctor_set(v___x_3597_, 1, v_v_3582_);
return v___x_3597_;
}
}
else
{
v_x_3579_ = v_l_3583_;
goto _start;
}
}
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
lean_dec(v_x_3580_);
v___x_3601_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1);
v___x_3602_ = l_panic___redArg(v_inst_3578_, v___x_3601_);
return v___x_3602_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_3603_, lean_object* v_x_3604_, lean_object* v_x_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3603_, v_x_3604_, v_x_3605_);
lean_dec(v_x_3604_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(lean_object* v_00_u03b1_3607_, lean_object* v_00_u03b2_3608_, lean_object* v_inst_3609_, lean_object* v_x_3610_, lean_object* v_x_3611_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3609_, v_x_3610_, v_x_3611_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_3613_, lean_object* v_00_u03b2_3614_, lean_object* v_inst_3615_, lean_object* v_x_3616_, lean_object* v_x_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(v_00_u03b1_3613_, v_00_u03b2_3614_, v_inst_3615_, v_x_3616_, v_x_3617_);
lean_dec(v_x_3616_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object* v_x_3619_, lean_object* v_x_3620_, lean_object* v_x_3621_){
_start:
{
if (lean_obj_tag(v_x_3619_) == 0)
{
lean_object* v_k_3622_; lean_object* v_v_3623_; lean_object* v_l_3624_; lean_object* v_r_3625_; lean_object* v___y_3627_; lean_object* v___y_3633_; 
v_k_3622_ = lean_ctor_get(v_x_3619_, 1);
v_v_3623_ = lean_ctor_get(v_x_3619_, 2);
v_l_3624_ = lean_ctor_get(v_x_3619_, 3);
v_r_3625_ = lean_ctor_get(v_x_3619_, 4);
if (lean_obj_tag(v_l_3624_) == 0)
{
lean_object* v_size_3640_; 
v_size_3640_ = lean_ctor_get(v_l_3624_, 0);
v___y_3633_ = v_size_3640_;
goto v___jp_3632_;
}
else
{
lean_object* v___x_3641_; 
v___x_3641_ = lean_unsigned_to_nat(0u);
v___y_3633_ = v___x_3641_;
goto v___jp_3632_;
}
v___jp_3626_:
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3628_ = lean_nat_sub(v_x_3620_, v___y_3627_);
lean_dec(v_x_3620_);
v___x_3629_ = lean_unsigned_to_nat(1u);
v___x_3630_ = lean_nat_sub(v___x_3628_, v___x_3629_);
lean_dec(v___x_3628_);
v_x_3619_ = v_r_3625_;
v_x_3620_ = v___x_3630_;
goto _start;
}
v___jp_3632_:
{
uint8_t v___x_3634_; 
v___x_3634_ = lean_nat_dec_lt(v_x_3620_, v___y_3633_);
if (v___x_3634_ == 0)
{
uint8_t v___x_3635_; 
v___x_3635_ = lean_nat_dec_eq(v_x_3620_, v___y_3633_);
if (v___x_3635_ == 0)
{
if (lean_obj_tag(v_l_3624_) == 0)
{
lean_object* v_size_3636_; 
v_size_3636_ = lean_ctor_get(v_l_3624_, 0);
v___y_3627_ = v_size_3636_;
goto v___jp_3626_;
}
else
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_unsigned_to_nat(0u);
v___y_3627_ = v___x_3637_;
goto v___jp_3626_;
}
}
else
{
lean_object* v___x_3638_; 
lean_dec(v_x_3620_);
lean_inc(v_v_3623_);
lean_inc(v_k_3622_);
v___x_3638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3638_, 0, v_k_3622_);
lean_ctor_set(v___x_3638_, 1, v_v_3623_);
return v___x_3638_;
}
}
else
{
v_x_3619_ = v_l_3624_;
goto _start;
}
}
}
else
{
lean_dec(v_x_3620_);
lean_inc_ref(v_x_3621_);
return v_x_3621_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg___boxed(lean_object* v_x_3642_, lean_object* v_x_3643_, lean_object* v_x_3644_){
_start:
{
lean_object* v_res_3645_; 
v_res_3645_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3642_, v_x_3643_, v_x_3644_);
lean_dec_ref(v_x_3644_);
lean_dec(v_x_3642_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(lean_object* v_00_u03b1_3646_, lean_object* v_00_u03b2_3647_, lean_object* v_x_3648_, lean_object* v_x_3649_, lean_object* v_x_3650_){
_start:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3648_, v_x_3649_, v_x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_3652_, lean_object* v_00_u03b2_3653_, lean_object* v_x_3654_, lean_object* v_x_3655_, lean_object* v_x_3656_){
_start:
{
lean_object* v_res_3657_; 
v_res_3657_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(v_00_u03b1_3652_, v_00_u03b2_3653_, v_x_3654_, v_x_3655_, v_x_3656_);
lean_dec_ref(v_x_3656_);
lean_dec(v_x_3654_);
return v_res_3657_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object* v_inst_3658_, lean_object* v_k_3659_, lean_object* v_best_3660_, lean_object* v_a_3661_){
_start:
{
if (lean_obj_tag(v_a_3661_) == 0)
{
lean_object* v_k_3662_; lean_object* v_v_3663_; lean_object* v_l_3664_; lean_object* v_r_3665_; lean_object* v___x_3666_; uint8_t v___x_3667_; 
v_k_3662_ = lean_ctor_get(v_a_3661_, 1);
lean_inc(v_k_3662_);
v_v_3663_ = lean_ctor_get(v_a_3661_, 2);
lean_inc(v_v_3663_);
v_l_3664_ = lean_ctor_get(v_a_3661_, 3);
lean_inc(v_l_3664_);
v_r_3665_ = lean_ctor_get(v_a_3661_, 4);
lean_inc(v_r_3665_);
lean_dec_ref(v_a_3661_);
lean_inc_ref(v_inst_3658_);
lean_inc(v_k_3662_);
lean_inc(v_k_3659_);
v___x_3666_ = lean_apply_2(v_inst_3658_, v_k_3659_, v_k_3662_);
v___x_3667_ = lean_unbox(v___x_3666_);
switch(v___x_3667_)
{
case 0:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
lean_dec(v_r_3665_);
lean_dec(v_best_3660_);
v___x_3668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3668_, 0, v_k_3662_);
lean_ctor_set(v___x_3668_, 1, v_v_3663_);
v___x_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
v_best_3660_ = v___x_3669_;
v_a_3661_ = v_l_3664_;
goto _start;
}
case 1:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_dec(v_r_3665_);
lean_dec(v_l_3664_);
lean_dec(v_best_3660_);
lean_dec(v_k_3659_);
lean_dec_ref(v_inst_3658_);
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v_k_3662_);
lean_ctor_set(v___x_3671_, 1, v_v_3663_);
v___x_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3671_);
return v___x_3672_;
}
default: 
{
lean_dec(v_l_3664_);
lean_dec(v_v_3663_);
lean_dec(v_k_3662_);
v_a_3661_ = v_r_3665_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3659_);
lean_dec_ref(v_inst_3658_);
return v_best_3660_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(lean_object* v_00_u03b1_3674_, lean_object* v_00_u03b2_3675_, lean_object* v_inst_3676_, lean_object* v_k_3677_, lean_object* v_best_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v___x_3680_; 
v___x_3680_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3676_, v_k_3677_, v_best_3678_, v_a_3679_);
return v___x_3680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___redArg(lean_object* v_inst_3681_, lean_object* v_k_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_box(0);
v___x_3685_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3681_, v_k_3682_, v___x_3684_, v_a_3683_);
return v___x_3685_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(lean_object* v_00_u03b1_3686_, lean_object* v_00_u03b2_3687_, lean_object* v_inst_3688_, lean_object* v_k_3689_, lean_object* v_a_3690_){
_start:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3691_ = lean_box(0);
v___x_3692_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3688_, v_k_3689_, v___x_3691_, v_a_3690_);
return v___x_3692_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object* v_inst_3693_, lean_object* v_k_3694_, lean_object* v_best_3695_, lean_object* v_a_3696_){
_start:
{
if (lean_obj_tag(v_a_3696_) == 0)
{
lean_object* v_k_3697_; lean_object* v_v_3698_; lean_object* v_l_3699_; lean_object* v_r_3700_; lean_object* v___x_3701_; uint8_t v___x_3702_; 
v_k_3697_ = lean_ctor_get(v_a_3696_, 1);
lean_inc(v_k_3697_);
v_v_3698_ = lean_ctor_get(v_a_3696_, 2);
lean_inc(v_v_3698_);
v_l_3699_ = lean_ctor_get(v_a_3696_, 3);
lean_inc(v_l_3699_);
v_r_3700_ = lean_ctor_get(v_a_3696_, 4);
lean_inc(v_r_3700_);
lean_dec_ref(v_a_3696_);
lean_inc_ref(v_inst_3693_);
lean_inc(v_k_3697_);
lean_inc(v_k_3694_);
v___x_3701_ = lean_apply_2(v_inst_3693_, v_k_3694_, v_k_3697_);
v___x_3702_ = lean_unbox(v___x_3701_);
if (v___x_3702_ == 0)
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
lean_dec(v_r_3700_);
lean_dec(v_best_3695_);
v___x_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3703_, 0, v_k_3697_);
lean_ctor_set(v___x_3703_, 1, v_v_3698_);
v___x_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
v_best_3695_ = v___x_3704_;
v_a_3696_ = v_l_3699_;
goto _start;
}
else
{
lean_dec(v_l_3699_);
lean_dec(v_v_3698_);
lean_dec(v_k_3697_);
v_a_3696_ = v_r_3700_;
goto _start;
}
}
else
{
lean_dec(v_k_3694_);
lean_dec_ref(v_inst_3693_);
return v_best_3695_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(lean_object* v_00_u03b1_3707_, lean_object* v_00_u03b2_3708_, lean_object* v_inst_3709_, lean_object* v_k_3710_, lean_object* v_best_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3709_, v_k_3710_, v_best_3711_, v_a_3712_);
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___redArg(lean_object* v_inst_3714_, lean_object* v_k_3715_, lean_object* v_a_3716_){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = lean_box(0);
v___x_3718_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3714_, v_k_3715_, v___x_3717_, v_a_3716_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(lean_object* v_00_u03b1_3719_, lean_object* v_00_u03b2_3720_, lean_object* v_inst_3721_, lean_object* v_k_3722_, lean_object* v_a_3723_){
_start:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = lean_box(0);
v___x_3725_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3721_, v_k_3722_, v___x_3724_, v_a_3723_);
return v___x_3725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object* v_inst_3726_, lean_object* v_k_3727_, lean_object* v_best_3728_, lean_object* v_a_3729_){
_start:
{
if (lean_obj_tag(v_a_3729_) == 0)
{
lean_object* v_k_3730_; lean_object* v_v_3731_; lean_object* v_l_3732_; lean_object* v_r_3733_; lean_object* v___x_3734_; uint8_t v___x_3735_; 
v_k_3730_ = lean_ctor_get(v_a_3729_, 1);
lean_inc(v_k_3730_);
v_v_3731_ = lean_ctor_get(v_a_3729_, 2);
lean_inc(v_v_3731_);
v_l_3732_ = lean_ctor_get(v_a_3729_, 3);
lean_inc(v_l_3732_);
v_r_3733_ = lean_ctor_get(v_a_3729_, 4);
lean_inc(v_r_3733_);
lean_dec_ref(v_a_3729_);
lean_inc_ref(v_inst_3726_);
lean_inc(v_k_3730_);
lean_inc(v_k_3727_);
v___x_3734_ = lean_apply_2(v_inst_3726_, v_k_3727_, v_k_3730_);
v___x_3735_ = lean_unbox(v___x_3734_);
switch(v___x_3735_)
{
case 0:
{
lean_dec(v_r_3733_);
lean_dec(v_v_3731_);
lean_dec(v_k_3730_);
v_a_3729_ = v_l_3732_;
goto _start;
}
case 1:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
lean_dec(v_r_3733_);
lean_dec(v_l_3732_);
lean_dec(v_best_3728_);
lean_dec(v_k_3727_);
lean_dec_ref(v_inst_3726_);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v_k_3730_);
lean_ctor_set(v___x_3737_, 1, v_v_3731_);
v___x_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
return v___x_3738_;
}
default: 
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_dec(v_l_3732_);
lean_dec(v_best_3728_);
v___x_3739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3739_, 0, v_k_3730_);
lean_ctor_set(v___x_3739_, 1, v_v_3731_);
v___x_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
v_best_3728_ = v___x_3740_;
v_a_3729_ = v_r_3733_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3727_);
lean_dec_ref(v_inst_3726_);
return v_best_3728_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(lean_object* v_00_u03b1_3742_, lean_object* v_00_u03b2_3743_, lean_object* v_inst_3744_, lean_object* v_k_3745_, lean_object* v_best_3746_, lean_object* v_a_3747_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3744_, v_k_3745_, v_best_3746_, v_a_3747_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___redArg(lean_object* v_inst_3749_, lean_object* v_k_3750_, lean_object* v_a_3751_){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = lean_box(0);
v___x_3753_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3749_, v_k_3750_, v___x_3752_, v_a_3751_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(lean_object* v_00_u03b1_3754_, lean_object* v_00_u03b2_3755_, lean_object* v_inst_3756_, lean_object* v_k_3757_, lean_object* v_a_3758_){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = lean_box(0);
v___x_3760_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3756_, v_k_3757_, v___x_3759_, v_a_3758_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object* v_inst_3761_, lean_object* v_k_3762_, lean_object* v_best_3763_, lean_object* v_a_3764_){
_start:
{
if (lean_obj_tag(v_a_3764_) == 0)
{
lean_object* v_k_3765_; lean_object* v_v_3766_; lean_object* v_l_3767_; lean_object* v_r_3768_; lean_object* v___x_3769_; uint8_t v___x_3770_; 
v_k_3765_ = lean_ctor_get(v_a_3764_, 1);
lean_inc(v_k_3765_);
v_v_3766_ = lean_ctor_get(v_a_3764_, 2);
lean_inc(v_v_3766_);
v_l_3767_ = lean_ctor_get(v_a_3764_, 3);
lean_inc(v_l_3767_);
v_r_3768_ = lean_ctor_get(v_a_3764_, 4);
lean_inc(v_r_3768_);
lean_dec_ref(v_a_3764_);
lean_inc_ref(v_inst_3761_);
lean_inc(v_k_3765_);
lean_inc(v_k_3762_);
v___x_3769_ = lean_apply_2(v_inst_3761_, v_k_3762_, v_k_3765_);
v___x_3770_ = lean_unbox(v___x_3769_);
if (v___x_3770_ == 2)
{
lean_object* v___x_3771_; lean_object* v___x_3772_; 
lean_dec(v_l_3767_);
lean_dec(v_best_3763_);
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v_k_3765_);
lean_ctor_set(v___x_3771_, 1, v_v_3766_);
v___x_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
v_best_3763_ = v___x_3772_;
v_a_3764_ = v_r_3768_;
goto _start;
}
else
{
lean_dec(v_r_3768_);
lean_dec(v_v_3766_);
lean_dec(v_k_3765_);
v_a_3764_ = v_l_3767_;
goto _start;
}
}
else
{
lean_dec(v_k_3762_);
lean_dec_ref(v_inst_3761_);
return v_best_3763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(lean_object* v_00_u03b1_3775_, lean_object* v_00_u03b2_3776_, lean_object* v_inst_3777_, lean_object* v_k_3778_, lean_object* v_best_3779_, lean_object* v_a_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3777_, v_k_3778_, v_best_3779_, v_a_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___redArg(lean_object* v_inst_3782_, lean_object* v_k_3783_, lean_object* v_a_3784_){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = lean_box(0);
v___x_3786_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3782_, v_k_3783_, v___x_3785_, v_a_3784_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(lean_object* v_00_u03b1_3787_, lean_object* v_00_u03b2_3788_, lean_object* v_inst_3789_, lean_object* v_k_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = lean_box(0);
v___x_3793_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3789_, v_k_3790_, v___x_3792_, v_a_3791_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(lean_object* v_inst_3794_, lean_object* v_inst_3795_, lean_object* v_k_3796_, lean_object* v_t_3797_){
_start:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_box(0);
v___x_3799_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3794_, v_k_3796_, v___x_3798_, v_t_3797_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
v___x_3800_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3801_ = l_panic___redArg(v_inst_3795_, v___x_3800_);
return v___x_3801_;
}
else
{
lean_object* v_val_3802_; 
lean_dec_ref(v_inst_3795_);
v_val_3802_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_val_3802_);
lean_dec_ref(v___x_3799_);
return v_val_3802_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object* v_00_u03b1_3803_, lean_object* v_00_u03b2_3804_, lean_object* v_inst_3805_, lean_object* v_inst_3806_, lean_object* v_k_3807_, lean_object* v_t_3808_){
_start:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; 
v___x_3809_ = lean_box(0);
v___x_3810_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3805_, v_k_3807_, v___x_3809_, v_t_3808_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3811_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3812_ = l_panic___redArg(v_inst_3806_, v___x_3811_);
return v___x_3812_;
}
else
{
lean_object* v_val_3813_; 
lean_dec_ref(v_inst_3806_);
v_val_3813_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_val_3813_);
lean_dec_ref(v___x_3810_);
return v_val_3813_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(lean_object* v_inst_3814_, lean_object* v_inst_3815_, lean_object* v_k_3816_, lean_object* v_t_3817_){
_start:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
v___x_3818_ = lean_box(0);
v___x_3819_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3814_, v_k_3816_, v___x_3818_, v_t_3817_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3821_ = l_panic___redArg(v_inst_3815_, v___x_3820_);
return v___x_3821_;
}
else
{
lean_object* v_val_3822_; 
lean_dec_ref(v_inst_3815_);
v_val_3822_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_val_3822_);
lean_dec_ref(v___x_3819_);
return v_val_3822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object* v_00_u03b1_3823_, lean_object* v_00_u03b2_3824_, lean_object* v_inst_3825_, lean_object* v_inst_3826_, lean_object* v_k_3827_, lean_object* v_t_3828_){
_start:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3829_ = lean_box(0);
v___x_3830_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3825_, v_k_3827_, v___x_3829_, v_t_3828_);
if (lean_obj_tag(v___x_3830_) == 0)
{
lean_object* v___x_3831_; lean_object* v___x_3832_; 
v___x_3831_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3832_ = l_panic___redArg(v_inst_3826_, v___x_3831_);
return v___x_3832_;
}
else
{
lean_object* v_val_3833_; 
lean_dec_ref(v_inst_3826_);
v_val_3833_ = lean_ctor_get(v___x_3830_, 0);
lean_inc(v_val_3833_);
lean_dec_ref(v___x_3830_);
return v_val_3833_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(lean_object* v_inst_3834_, lean_object* v_inst_3835_, lean_object* v_k_3836_, lean_object* v_t_3837_){
_start:
{
lean_object* v___x_3838_; lean_object* v___x_3839_; 
v___x_3838_ = lean_box(0);
v___x_3839_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3834_, v_k_3836_, v___x_3838_, v_t_3837_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
v___x_3840_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3841_ = l_panic___redArg(v_inst_3835_, v___x_3840_);
return v___x_3841_;
}
else
{
lean_object* v_val_3842_; 
lean_dec_ref(v_inst_3835_);
v_val_3842_ = lean_ctor_get(v___x_3839_, 0);
lean_inc(v_val_3842_);
lean_dec_ref(v___x_3839_);
return v_val_3842_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object* v_00_u03b1_3843_, lean_object* v_00_u03b2_3844_, lean_object* v_inst_3845_, lean_object* v_inst_3846_, lean_object* v_k_3847_, lean_object* v_t_3848_){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3849_ = lean_box(0);
v___x_3850_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3845_, v_k_3847_, v___x_3849_, v_t_3848_);
if (lean_obj_tag(v___x_3850_) == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3852_ = l_panic___redArg(v_inst_3846_, v___x_3851_);
return v___x_3852_;
}
else
{
lean_object* v_val_3853_; 
lean_dec_ref(v_inst_3846_);
v_val_3853_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_val_3853_);
lean_dec_ref(v___x_3850_);
return v_val_3853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(lean_object* v_inst_3854_, lean_object* v_inst_3855_, lean_object* v_k_3856_, lean_object* v_t_3857_){
_start:
{
lean_object* v___x_3858_; lean_object* v___x_3859_; 
v___x_3858_ = lean_box(0);
v___x_3859_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3854_, v_k_3856_, v___x_3858_, v_t_3857_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3861_ = l_panic___redArg(v_inst_3855_, v___x_3860_);
return v___x_3861_;
}
else
{
lean_object* v_val_3862_; 
lean_dec_ref(v_inst_3855_);
v_val_3862_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_val_3862_);
lean_dec_ref(v___x_3859_);
return v_val_3862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object* v_00_u03b1_3863_, lean_object* v_00_u03b2_3864_, lean_object* v_inst_3865_, lean_object* v_inst_3866_, lean_object* v_k_3867_, lean_object* v_t_3868_){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = lean_box(0);
v___x_3870_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3865_, v_k_3867_, v___x_3869_, v_t_3868_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3871_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3872_ = l_panic___redArg(v_inst_3866_, v___x_3871_);
return v___x_3872_;
}
else
{
lean_object* v_val_3873_; 
lean_dec_ref(v_inst_3866_);
v_val_3873_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_val_3873_);
lean_dec_ref(v___x_3870_);
return v_val_3873_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(lean_object* v_inst_3874_, lean_object* v_k_3875_, lean_object* v_t_3876_, lean_object* v_fallback_3877_){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = lean_box(0);
v___x_3879_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3874_, v_k_3875_, v___x_3878_, v_t_3876_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_inc_ref(v_fallback_3877_);
return v_fallback_3877_;
}
else
{
lean_object* v_val_3880_; 
v_val_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_val_3880_);
lean_dec_ref(v___x_3879_);
return v_val_3880_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg___boxed(lean_object* v_inst_3881_, lean_object* v_k_3882_, lean_object* v_t_3883_, lean_object* v_fallback_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(v_inst_3881_, v_k_3882_, v_t_3883_, v_fallback_3884_);
lean_dec_ref(v_fallback_3884_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(lean_object* v_00_u03b1_3886_, lean_object* v_00_u03b2_3887_, lean_object* v_inst_3888_, lean_object* v_k_3889_, lean_object* v_t_3890_, lean_object* v_fallback_3891_){
_start:
{
lean_object* v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = lean_box(0);
v___x_3893_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3888_, v_k_3889_, v___x_3892_, v_t_3890_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_inc_ref(v_fallback_3891_);
return v_fallback_3891_;
}
else
{
lean_object* v_val_3894_; 
v_val_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_val_3894_);
lean_dec_ref(v___x_3893_);
return v_val_3894_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___boxed(lean_object* v_00_u03b1_3895_, lean_object* v_00_u03b2_3896_, lean_object* v_inst_3897_, lean_object* v_k_3898_, lean_object* v_t_3899_, lean_object* v_fallback_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(v_00_u03b1_3895_, v_00_u03b2_3896_, v_inst_3897_, v_k_3898_, v_t_3899_, v_fallback_3900_);
lean_dec_ref(v_fallback_3900_);
return v_res_3901_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(lean_object* v_inst_3902_, lean_object* v_k_3903_, lean_object* v_t_3904_, lean_object* v_fallback_3905_){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = lean_box(0);
v___x_3907_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3902_, v_k_3903_, v___x_3906_, v_t_3904_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_inc_ref(v_fallback_3905_);
return v_fallback_3905_;
}
else
{
lean_object* v_val_3908_; 
v_val_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_val_3908_);
lean_dec_ref(v___x_3907_);
return v_val_3908_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg___boxed(lean_object* v_inst_3909_, lean_object* v_k_3910_, lean_object* v_t_3911_, lean_object* v_fallback_3912_){
_start:
{
lean_object* v_res_3913_; 
v_res_3913_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(v_inst_3909_, v_k_3910_, v_t_3911_, v_fallback_3912_);
lean_dec_ref(v_fallback_3912_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(lean_object* v_00_u03b1_3914_, lean_object* v_00_u03b2_3915_, lean_object* v_inst_3916_, lean_object* v_k_3917_, lean_object* v_t_3918_, lean_object* v_fallback_3919_){
_start:
{
lean_object* v___x_3920_; lean_object* v___x_3921_; 
v___x_3920_ = lean_box(0);
v___x_3921_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3916_, v_k_3917_, v___x_3920_, v_t_3918_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_inc_ref(v_fallback_3919_);
return v_fallback_3919_;
}
else
{
lean_object* v_val_3922_; 
v_val_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_val_3922_);
lean_dec_ref(v___x_3921_);
return v_val_3922_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_3923_, lean_object* v_00_u03b2_3924_, lean_object* v_inst_3925_, lean_object* v_k_3926_, lean_object* v_t_3927_, lean_object* v_fallback_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(v_00_u03b1_3923_, v_00_u03b2_3924_, v_inst_3925_, v_k_3926_, v_t_3927_, v_fallback_3928_);
lean_dec_ref(v_fallback_3928_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(lean_object* v_inst_3930_, lean_object* v_k_3931_, lean_object* v_t_3932_, lean_object* v_fallback_3933_){
_start:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = lean_box(0);
v___x_3935_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3930_, v_k_3931_, v___x_3934_, v_t_3932_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_inc_ref(v_fallback_3933_);
return v_fallback_3933_;
}
else
{
lean_object* v_val_3936_; 
v_val_3936_ = lean_ctor_get(v___x_3935_, 0);
lean_inc(v_val_3936_);
lean_dec_ref(v___x_3935_);
return v_val_3936_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg___boxed(lean_object* v_inst_3937_, lean_object* v_k_3938_, lean_object* v_t_3939_, lean_object* v_fallback_3940_){
_start:
{
lean_object* v_res_3941_; 
v_res_3941_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(v_inst_3937_, v_k_3938_, v_t_3939_, v_fallback_3940_);
lean_dec_ref(v_fallback_3940_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(lean_object* v_00_u03b1_3942_, lean_object* v_00_u03b2_3943_, lean_object* v_inst_3944_, lean_object* v_k_3945_, lean_object* v_t_3946_, lean_object* v_fallback_3947_){
_start:
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3948_ = lean_box(0);
v___x_3949_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3944_, v_k_3945_, v___x_3948_, v_t_3946_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_inc_ref(v_fallback_3947_);
return v_fallback_3947_;
}
else
{
lean_object* v_val_3950_; 
v_val_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_val_3950_);
lean_dec_ref(v___x_3949_);
return v_val_3950_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___boxed(lean_object* v_00_u03b1_3951_, lean_object* v_00_u03b2_3952_, lean_object* v_inst_3953_, lean_object* v_k_3954_, lean_object* v_t_3955_, lean_object* v_fallback_3956_){
_start:
{
lean_object* v_res_3957_; 
v_res_3957_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(v_00_u03b1_3951_, v_00_u03b2_3952_, v_inst_3953_, v_k_3954_, v_t_3955_, v_fallback_3956_);
lean_dec_ref(v_fallback_3956_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(lean_object* v_inst_3958_, lean_object* v_k_3959_, lean_object* v_t_3960_, lean_object* v_fallback_3961_){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_box(0);
v___x_3963_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3958_, v_k_3959_, v___x_3962_, v_t_3960_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_inc_ref(v_fallback_3961_);
return v_fallback_3961_;
}
else
{
lean_object* v_val_3964_; 
v_val_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_val_3964_);
lean_dec_ref(v___x_3963_);
return v_val_3964_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg___boxed(lean_object* v_inst_3965_, lean_object* v_k_3966_, lean_object* v_t_3967_, lean_object* v_fallback_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(v_inst_3965_, v_k_3966_, v_t_3967_, v_fallback_3968_);
lean_dec_ref(v_fallback_3968_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(lean_object* v_00_u03b1_3970_, lean_object* v_00_u03b2_3971_, lean_object* v_inst_3972_, lean_object* v_k_3973_, lean_object* v_t_3974_, lean_object* v_fallback_3975_){
_start:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = lean_box(0);
v___x_3977_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3972_, v_k_3973_, v___x_3976_, v_t_3974_);
if (lean_obj_tag(v___x_3977_) == 0)
{
lean_inc_ref(v_fallback_3975_);
return v_fallback_3975_;
}
else
{
lean_object* v_val_3978_; 
v_val_3978_ = lean_ctor_get(v___x_3977_, 0);
lean_inc(v_val_3978_);
lean_dec_ref(v___x_3977_);
return v_val_3978_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_3979_, lean_object* v_00_u03b2_3980_, lean_object* v_inst_3981_, lean_object* v_k_3982_, lean_object* v_t_3983_, lean_object* v_fallback_3984_){
_start:
{
lean_object* v_res_3985_; 
v_res_3985_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(v_00_u03b1_3979_, v_00_u03b2_3980_, v_inst_3981_, v_k_3982_, v_t_3983_, v_fallback_3984_);
lean_dec_ref(v_fallback_3984_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object* v_inst_3986_, lean_object* v_k_3987_, lean_object* v_x_3988_){
_start:
{
lean_object* v_k_3989_; lean_object* v_v_3990_; lean_object* v_l_3991_; lean_object* v_r_3992_; lean_object* v___x_3993_; uint8_t v___x_3994_; 
v_k_3989_ = lean_ctor_get(v_x_3988_, 1);
lean_inc(v_k_3989_);
v_v_3990_ = lean_ctor_get(v_x_3988_, 2);
lean_inc(v_v_3990_);
v_l_3991_ = lean_ctor_get(v_x_3988_, 3);
lean_inc(v_l_3991_);
v_r_3992_ = lean_ctor_get(v_x_3988_, 4);
lean_inc(v_r_3992_);
lean_dec(v_x_3988_);
lean_inc_ref(v_inst_3986_);
lean_inc(v_k_3989_);
lean_inc(v_k_3987_);
v___x_3993_ = lean_apply_2(v_inst_3986_, v_k_3987_, v_k_3989_);
v___x_3994_ = lean_unbox(v___x_3993_);
switch(v___x_3994_)
{
case 0:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
lean_dec(v_r_3992_);
v___x_3995_ = lean_box(0);
v___x_3996_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3986_, v_k_3987_, v___x_3995_, v_l_3991_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v___x_3997_; 
v___x_3997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3997_, 0, v_k_3989_);
lean_ctor_set(v___x_3997_, 1, v_v_3990_);
return v___x_3997_;
}
else
{
lean_object* v_val_3998_; 
lean_dec(v_v_3990_);
lean_dec(v_k_3989_);
v_val_3998_ = lean_ctor_get(v___x_3996_, 0);
lean_inc(v_val_3998_);
lean_dec_ref(v___x_3996_);
return v_val_3998_;
}
}
case 1:
{
lean_object* v___x_3999_; 
lean_dec(v_r_3992_);
lean_dec(v_l_3991_);
lean_dec(v_k_3987_);
lean_dec_ref(v_inst_3986_);
v___x_3999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3999_, 0, v_k_3989_);
lean_ctor_set(v___x_3999_, 1, v_v_3990_);
return v___x_3999_;
}
default: 
{
lean_dec(v_l_3991_);
lean_dec(v_v_3990_);
lean_dec(v_k_3989_);
v_x_3988_ = v_r_3992_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(lean_object* v_00_u03b1_4001_, lean_object* v_00_u03b2_4002_, lean_object* v_inst_4003_, lean_object* v_inst_4004_, lean_object* v_k_4005_, lean_object* v_x_4006_, lean_object* v_x_4007_, lean_object* v_x_4008_){
_start:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_inst_4003_, v_k_4005_, v_x_4006_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object* v_inst_4010_, lean_object* v_k_4011_, lean_object* v_x_4012_){
_start:
{
lean_object* v_k_4013_; lean_object* v_v_4014_; lean_object* v_l_4015_; lean_object* v_r_4016_; lean_object* v___x_4017_; uint8_t v___x_4018_; uint8_t v___x_4019_; uint8_t v___x_4020_; 
v_k_4013_ = lean_ctor_get(v_x_4012_, 1);
lean_inc(v_k_4013_);
v_v_4014_ = lean_ctor_get(v_x_4012_, 2);
lean_inc(v_v_4014_);
v_l_4015_ = lean_ctor_get(v_x_4012_, 3);
lean_inc(v_l_4015_);
v_r_4016_ = lean_ctor_get(v_x_4012_, 4);
lean_inc(v_r_4016_);
lean_dec(v_x_4012_);
lean_inc_ref(v_inst_4010_);
lean_inc(v_k_4013_);
lean_inc(v_k_4011_);
v___x_4017_ = lean_apply_2(v_inst_4010_, v_k_4011_, v_k_4013_);
v___x_4018_ = 0;
v___x_4019_ = lean_unbox(v___x_4017_);
v___x_4020_ = l_instDecidableEqOrdering(v___x_4019_, v___x_4018_);
if (v___x_4020_ == 0)
{
lean_dec(v_l_4015_);
lean_dec(v_v_4014_);
lean_dec(v_k_4013_);
v_x_4012_ = v_r_4016_;
goto _start;
}
else
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
lean_dec(v_r_4016_);
v___x_4022_ = lean_box(0);
v___x_4023_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4010_, v_k_4011_, v___x_4022_, v_l_4015_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v___x_4024_; 
v___x_4024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4024_, 0, v_k_4013_);
lean_ctor_set(v___x_4024_, 1, v_v_4014_);
return v___x_4024_;
}
else
{
lean_object* v_val_4025_; 
lean_dec(v_v_4014_);
lean_dec(v_k_4013_);
v_val_4025_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_val_4025_);
lean_dec_ref(v___x_4023_);
return v_val_4025_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(lean_object* v_00_u03b1_4026_, lean_object* v_00_u03b2_4027_, lean_object* v_inst_4028_, lean_object* v_inst_4029_, lean_object* v_k_4030_, lean_object* v_x_4031_, lean_object* v_x_4032_, lean_object* v_x_4033_){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_inst_4028_, v_k_4030_, v_x_4031_);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object* v_inst_4035_, lean_object* v_k_4036_, lean_object* v_x_4037_){
_start:
{
lean_object* v_k_4038_; lean_object* v_v_4039_; lean_object* v_l_4040_; lean_object* v_r_4041_; lean_object* v___x_4042_; uint8_t v___x_4043_; 
v_k_4038_ = lean_ctor_get(v_x_4037_, 1);
lean_inc(v_k_4038_);
v_v_4039_ = lean_ctor_get(v_x_4037_, 2);
lean_inc(v_v_4039_);
v_l_4040_ = lean_ctor_get(v_x_4037_, 3);
lean_inc(v_l_4040_);
v_r_4041_ = lean_ctor_get(v_x_4037_, 4);
lean_inc(v_r_4041_);
lean_dec(v_x_4037_);
lean_inc_ref(v_inst_4035_);
lean_inc(v_k_4038_);
lean_inc(v_k_4036_);
v___x_4042_ = lean_apply_2(v_inst_4035_, v_k_4036_, v_k_4038_);
v___x_4043_ = lean_unbox(v___x_4042_);
switch(v___x_4043_)
{
case 0:
{
lean_dec(v_r_4041_);
lean_dec(v_v_4039_);
lean_dec(v_k_4038_);
v_x_4037_ = v_l_4040_;
goto _start;
}
case 1:
{
lean_object* v___x_4045_; 
lean_dec(v_r_4041_);
lean_dec(v_l_4040_);
lean_dec(v_k_4036_);
lean_dec_ref(v_inst_4035_);
v___x_4045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4045_, 0, v_k_4038_);
lean_ctor_set(v___x_4045_, 1, v_v_4039_);
return v___x_4045_;
}
default: 
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
lean_dec(v_l_4040_);
v___x_4046_ = lean_box(0);
v___x_4047_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4035_, v_k_4036_, v___x_4046_, v_r_4041_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v___x_4048_; 
v___x_4048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4048_, 0, v_k_4038_);
lean_ctor_set(v___x_4048_, 1, v_v_4039_);
return v___x_4048_;
}
else
{
lean_object* v_val_4049_; 
lean_dec(v_v_4039_);
lean_dec(v_k_4038_);
v_val_4049_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_val_4049_);
lean_dec_ref(v___x_4047_);
return v_val_4049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(lean_object* v_00_u03b1_4050_, lean_object* v_00_u03b2_4051_, lean_object* v_inst_4052_, lean_object* v_inst_4053_, lean_object* v_k_4054_, lean_object* v_x_4055_, lean_object* v_x_4056_, lean_object* v_x_4057_){
_start:
{
lean_object* v___x_4058_; 
v___x_4058_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_inst_4052_, v_k_4054_, v_x_4055_);
return v___x_4058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object* v_inst_4059_, lean_object* v_k_4060_, lean_object* v_x_4061_){
_start:
{
lean_object* v_k_4062_; lean_object* v_v_4063_; lean_object* v_l_4064_; lean_object* v_r_4065_; lean_object* v___x_4066_; uint8_t v___x_4067_; uint8_t v___x_4068_; uint8_t v___x_4069_; 
v_k_4062_ = lean_ctor_get(v_x_4061_, 1);
lean_inc(v_k_4062_);
v_v_4063_ = lean_ctor_get(v_x_4061_, 2);
lean_inc(v_v_4063_);
v_l_4064_ = lean_ctor_get(v_x_4061_, 3);
lean_inc(v_l_4064_);
v_r_4065_ = lean_ctor_get(v_x_4061_, 4);
lean_inc(v_r_4065_);
lean_dec(v_x_4061_);
lean_inc_ref(v_inst_4059_);
lean_inc(v_k_4062_);
lean_inc(v_k_4060_);
v___x_4066_ = lean_apply_2(v_inst_4059_, v_k_4060_, v_k_4062_);
v___x_4067_ = 2;
v___x_4068_ = lean_unbox(v___x_4066_);
v___x_4069_ = l_instDecidableEqOrdering(v___x_4068_, v___x_4067_);
if (v___x_4069_ == 0)
{
lean_dec(v_r_4065_);
lean_dec(v_v_4063_);
lean_dec(v_k_4062_);
v_x_4061_ = v_l_4064_;
goto _start;
}
else
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
lean_dec(v_l_4064_);
v___x_4071_ = lean_box(0);
v___x_4072_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4059_, v_k_4060_, v___x_4071_, v_r_4065_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v___x_4073_; 
v___x_4073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4073_, 0, v_k_4062_);
lean_ctor_set(v___x_4073_, 1, v_v_4063_);
return v___x_4073_;
}
else
{
lean_object* v_val_4074_; 
lean_dec(v_v_4063_);
lean_dec(v_k_4062_);
v_val_4074_ = lean_ctor_get(v___x_4072_, 0);
lean_inc(v_val_4074_);
lean_dec_ref(v___x_4072_);
return v_val_4074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(lean_object* v_00_u03b1_4075_, lean_object* v_00_u03b2_4076_, lean_object* v_inst_4077_, lean_object* v_inst_4078_, lean_object* v_k_4079_, lean_object* v_x_4080_, lean_object* v_x_4081_, lean_object* v_x_4082_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_inst_4077_, v_k_4079_, v_x_4080_);
return v___x_4083_;
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
