// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Queries
// Imports: public import Init.Data.Nat.Compare public import Std.Data.DTreeMap.Internal.Balanced public import Std.Data.DTreeMap.Internal.Ordered public import Init.BinderPredicates public import Init.Data.Option.BasicAux import Init.Data.Nat.Lemmas import Init.Data.Nat.Internal.Linear import Init.Omega import Init.RCases import Init.WFTactics
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
lean_object* l_Ordering_ctorIdx(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0;
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
lean_dec_ref_known(v_t_138_, 5);
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
lean_dec_ref_known(v_t_196_, 5);
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
lean_dec_ref_known(v_t_210_, 5);
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
uint8_t v_x_33__boxed_235_; lean_object* v_res_236_; 
v_x_33__boxed_235_ = lean_unbox(v_x_231_);
v_res_236_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_33__boxed_235_, v_h__1_232_, v_h__2_233_, v_h__3_234_);
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
uint8_t v_x_48__boxed_253_; lean_object* v_res_254_; 
v_x_48__boxed_253_ = lean_unbox(v_x_249_);
v_res_254_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_248_, v_x_48__boxed_253_, v_h__1_250_, v_h__2_251_, v_h__3_252_);
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
lean_dec_ref_known(v_t_272_, 5);
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
lean_dec_ref_known(v_t_320_, 5);
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
lean_dec_ref_known(v_t_355_, 5);
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
lean_dec_ref_known(v_t_388_, 5);
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
lean_dec_ref_known(v_t_435_, 5);
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
lean_dec_ref_known(v_t_468_, 5);
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
lean_dec_ref_known(v_t_500_, 5);
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
lean_dec_ref_known(v_t_542_, 5);
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
lean_dec_ref_known(v_t_574_, 5);
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
lean_dec_ref_known(v_t_604_, 5);
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
lean_dec_ref_known(v_t_649_, 5);
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
lean_dec_ref_known(v_t_681_, 5);
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
lean_dec_ref_known(v_x_722_, 5);
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
lean_dec_ref_known(v_x_797_, 5);
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
lean_dec_ref_known(v_____do__lift_869_, 1);
v___x_871_ = lean_apply_1(v___f_863_, v_a_870_);
return v___x_871_;
}
else
{
lean_object* v_a_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
lean_dec(v___f_863_);
v_a_872_ = lean_ctor_get(v_____do__lift_869_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v_____do__lift_869_, 1);
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
lean_dec_ref_known(v_x_878_, 5);
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
lean_dec_ref_known(v_____do__lift_899_, 1);
v___x_901_ = lean_apply_1(v___f_895_, v_a_900_);
return v___x_901_;
}
else
{
lean_object* v_a_902_; lean_object* v___x_903_; 
lean_dec(v___f_895_);
v_a_902_ = lean_ctor_get(v_____do__lift_899_, 0);
lean_inc(v_a_902_);
lean_dec_ref_known(v_____do__lift_899_, 1);
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
lean_dec_ref_known(v_fst_992_, 1);
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
lean_dec_ref_known(v_fst_1012_, 1);
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
lean_dec_ref_known(v_fst_1051_, 1);
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
lean_dec_ref_known(v_fst_1071_, 1);
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
lean_dec_ref_known(v_x_1285_, 5);
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
lean_dec_ref_known(v_l_1289_, 5);
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
lean_dec_ref_known(v_x_1285_, 5);
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
lean_dec_ref_known(v_x_1310_, 5);
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
lean_dec_ref_known(v_l_1314_, 5);
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
lean_dec_ref_known(v_x_1310_, 5);
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
lean_dec_ref_known(v_l_1353_, 5);
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
lean_dec_ref_known(v_l_1376_, 5);
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
lean_dec_ref_known(v_x_1442_, 5);
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
lean_dec_ref_known(v_l_1447_, 5);
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
lean_dec_ref_known(v_x_1442_, 5);
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
lean_dec_ref_known(v_x_1467_, 5);
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
lean_dec_ref_known(v_l_1472_, 5);
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
lean_dec_ref_known(v_x_1467_, 5);
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
lean_dec_ref_known(v_x_1507_, 5);
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
lean_dec_ref_known(v_r_1511_, 5);
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
lean_dec_ref_known(v_x_1507_, 5);
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
lean_dec_ref_known(v_x_1532_, 5);
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
lean_dec_ref_known(v_r_1536_, 5);
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
lean_dec_ref_known(v_x_1532_, 5);
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
lean_dec_ref_known(v_r_1575_, 5);
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
lean_dec_ref_known(v_r_1598_, 5);
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
lean_dec_ref_known(v_x_1663_, 5);
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
lean_dec_ref_known(v_r_1668_, 5);
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
lean_dec_ref_known(v_x_1663_, 5);
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
lean_dec_ref_known(v_x_1688_, 5);
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
lean_dec_ref_known(v_r_1693_, 5);
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
lean_dec_ref_known(v_x_1688_, 5);
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
lean_dec_ref_known(v_x_1787_, 5);
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
lean_dec_ref_known(v_l_1792_, 5);
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
lean_dec_ref_known(v_x_1787_, 5);
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
lean_dec_ref_known(v_x_1812_, 5);
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
lean_dec_ref_known(v_l_1817_, 5);
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
lean_dec_ref_known(v_x_1812_, 5);
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
lean_dec_ref_known(v_x_1911_, 5);
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
lean_dec_ref_known(v_r_1916_, 5);
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
lean_dec_ref_known(v_x_1911_, 5);
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
lean_dec_ref_known(v_x_1936_, 5);
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
lean_dec_ref_known(v_r_1941_, 5);
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
lean_dec_ref_known(v_x_1936_, 5);
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
lean_dec_ref_known(v_a_2280_, 5);
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
lean_dec_ref_known(v_a_2315_, 5);
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
lean_dec_ref_known(v_a_2348_, 5);
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
lean_dec_ref_known(v_a_2383_, 5);
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
lean_dec_ref_known(v___x_2427_, 1);
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
lean_dec_ref_known(v___x_2443_, 1);
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
lean_dec_ref_known(v___x_2459_, 1);
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
lean_dec_ref_known(v___x_2475_, 1);
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
lean_dec_ref_known(v___x_2491_, 1);
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
lean_dec_ref_known(v___x_2507_, 1);
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
lean_dec_ref_known(v___x_2523_, 1);
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
lean_dec_ref_known(v___x_2539_, 1);
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
lean_dec_ref_known(v___x_2555_, 1);
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
lean_dec_ref_known(v___x_2569_, 1);
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
lean_dec_ref_known(v___x_2583_, 1);
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
lean_dec_ref_known(v___x_2597_, 1);
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
lean_dec_ref_known(v___x_2611_, 1);
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
lean_dec_ref_known(v___x_2625_, 1);
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
lean_dec_ref_known(v___x_2639_, 1);
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
lean_dec_ref_known(v___x_2653_, 1);
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
lean_dec_ref_known(v___x_2672_, 1);
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
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0(void){
_start:
{
uint8_t v___x_2686_; lean_object* v___x_2687_; 
v___x_2686_ = 0;
v___x_2687_ = l_Ordering_ctorIdx(v___x_2686_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object* v_inst_2688_, lean_object* v_k_2689_, lean_object* v_x_2690_){
_start:
{
lean_object* v_k_2691_; lean_object* v_v_2692_; lean_object* v_l_2693_; lean_object* v_r_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; uint8_t v___x_2699_; 
v_k_2691_ = lean_ctor_get(v_x_2690_, 1);
lean_inc_n(v_k_2691_, 2);
v_v_2692_ = lean_ctor_get(v_x_2690_, 2);
lean_inc(v_v_2692_);
v_l_2693_ = lean_ctor_get(v_x_2690_, 3);
lean_inc(v_l_2693_);
v_r_2694_ = lean_ctor_get(v_x_2690_, 4);
lean_inc(v_r_2694_);
lean_dec(v_x_2690_);
lean_inc_ref(v_inst_2688_);
lean_inc(v_k_2689_);
v___x_2695_ = lean_apply_2(v_inst_2688_, v_k_2689_, v_k_2691_);
v___x_2696_ = lean_unbox(v___x_2695_);
v___x_2697_ = l_Ordering_ctorIdx(v___x_2696_);
v___x_2698_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0);
v___x_2699_ = lean_nat_dec_eq(v___x_2697_, v___x_2698_);
lean_dec(v___x_2697_);
if (v___x_2699_ == 0)
{
lean_dec(v_l_2693_);
lean_dec(v_v_2692_);
lean_dec(v_k_2691_);
v_x_2690_ = v_r_2694_;
goto _start;
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2702_; 
lean_dec(v_r_2694_);
v___x_2701_ = lean_box(0);
v___x_2702_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2688_, v_k_2689_, v___x_2701_, v_l_2693_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v_k_2691_);
lean_ctor_set(v___x_2703_, 1, v_v_2692_);
return v___x_2703_;
}
else
{
lean_object* v_val_2704_; 
lean_dec(v_v_2692_);
lean_dec(v_k_2691_);
v_val_2704_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_val_2704_);
lean_dec_ref_known(v___x_2702_, 1);
return v_val_2704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object* v_00_u03b1_2705_, lean_object* v_00_u03b2_2706_, lean_object* v_inst_2707_, lean_object* v_inst_2708_, lean_object* v_k_2709_, lean_object* v_x_2710_, lean_object* v_x_2711_, lean_object* v_x_2712_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_inst_2707_, v_k_2709_, v_x_2710_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object* v_inst_2714_, lean_object* v_k_2715_, lean_object* v_x_2716_){
_start:
{
lean_object* v_k_2717_; lean_object* v_v_2718_; lean_object* v_l_2719_; lean_object* v_r_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v_k_2717_ = lean_ctor_get(v_x_2716_, 1);
lean_inc_n(v_k_2717_, 2);
v_v_2718_ = lean_ctor_get(v_x_2716_, 2);
lean_inc(v_v_2718_);
v_l_2719_ = lean_ctor_get(v_x_2716_, 3);
lean_inc(v_l_2719_);
v_r_2720_ = lean_ctor_get(v_x_2716_, 4);
lean_inc(v_r_2720_);
lean_dec(v_x_2716_);
lean_inc_ref(v_inst_2714_);
lean_inc(v_k_2715_);
v___x_2721_ = lean_apply_2(v_inst_2714_, v_k_2715_, v_k_2717_);
v___x_2722_ = lean_unbox(v___x_2721_);
switch(v___x_2722_)
{
case 0:
{
lean_dec(v_r_2720_);
lean_dec(v_v_2718_);
lean_dec(v_k_2717_);
v_x_2716_ = v_l_2719_;
goto _start;
}
case 1:
{
lean_object* v___x_2724_; 
lean_dec(v_r_2720_);
lean_dec(v_l_2719_);
lean_dec(v_k_2715_);
lean_dec_ref(v_inst_2714_);
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v_k_2717_);
lean_ctor_set(v___x_2724_, 1, v_v_2718_);
return v___x_2724_;
}
default: 
{
lean_object* v___x_2725_; lean_object* v___x_2726_; 
lean_dec(v_l_2719_);
v___x_2725_ = lean_box(0);
v___x_2726_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2714_, v_k_2715_, v___x_2725_, v_r_2720_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2727_, 0, v_k_2717_);
lean_ctor_set(v___x_2727_, 1, v_v_2718_);
return v___x_2727_;
}
else
{
lean_object* v_val_2728_; 
lean_dec(v_v_2718_);
lean_dec(v_k_2717_);
v_val_2728_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_val_2728_);
lean_dec_ref_known(v___x_2726_, 1);
return v_val_2728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object* v_00_u03b1_2729_, lean_object* v_00_u03b2_2730_, lean_object* v_inst_2731_, lean_object* v_inst_2732_, lean_object* v_k_2733_, lean_object* v_x_2734_, lean_object* v_x_2735_, lean_object* v_x_2736_){
_start:
{
lean_object* v___x_2737_; 
v___x_2737_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_inst_2731_, v_k_2733_, v_x_2734_);
return v___x_2737_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0(void){
_start:
{
uint8_t v___x_2738_; lean_object* v___x_2739_; 
v___x_2738_ = 2;
v___x_2739_ = l_Ordering_ctorIdx(v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object* v_inst_2740_, lean_object* v_k_2741_, lean_object* v_x_2742_){
_start:
{
lean_object* v_k_2743_; lean_object* v_v_2744_; lean_object* v_l_2745_; lean_object* v_r_2746_; lean_object* v___x_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v_k_2743_ = lean_ctor_get(v_x_2742_, 1);
lean_inc_n(v_k_2743_, 2);
v_v_2744_ = lean_ctor_get(v_x_2742_, 2);
lean_inc(v_v_2744_);
v_l_2745_ = lean_ctor_get(v_x_2742_, 3);
lean_inc(v_l_2745_);
v_r_2746_ = lean_ctor_get(v_x_2742_, 4);
lean_inc(v_r_2746_);
lean_dec(v_x_2742_);
lean_inc_ref(v_inst_2740_);
lean_inc(v_k_2741_);
v___x_2747_ = lean_apply_2(v_inst_2740_, v_k_2741_, v_k_2743_);
v___x_2748_ = lean_unbox(v___x_2747_);
v___x_2749_ = l_Ordering_ctorIdx(v___x_2748_);
v___x_2750_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0);
v___x_2751_ = lean_nat_dec_eq(v___x_2749_, v___x_2750_);
lean_dec(v___x_2749_);
if (v___x_2751_ == 0)
{
lean_dec(v_r_2746_);
lean_dec(v_v_2744_);
lean_dec(v_k_2743_);
v_x_2742_ = v_l_2745_;
goto _start;
}
else
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
lean_dec(v_l_2745_);
v___x_2753_ = lean_box(0);
v___x_2754_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2740_, v_k_2741_, v___x_2753_, v_r_2746_);
if (lean_obj_tag(v___x_2754_) == 0)
{
lean_object* v___x_2755_; 
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_k_2743_);
lean_ctor_set(v___x_2755_, 1, v_v_2744_);
return v___x_2755_;
}
else
{
lean_object* v_val_2756_; 
lean_dec(v_v_2744_);
lean_dec(v_k_2743_);
v_val_2756_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_val_2756_);
lean_dec_ref_known(v___x_2754_, 1);
return v_val_2756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT(lean_object* v_00_u03b1_2757_, lean_object* v_00_u03b2_2758_, lean_object* v_inst_2759_, lean_object* v_inst_2760_, lean_object* v_k_2761_, lean_object* v_x_2762_, lean_object* v_x_2763_, lean_object* v_x_2764_){
_start:
{
lean_object* v___x_2765_; 
v___x_2765_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_inst_2759_, v_k_2761_, v_x_2762_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object* v_inst_2766_, lean_object* v_k_2767_, lean_object* v_best_2768_, lean_object* v_a_2769_){
_start:
{
if (lean_obj_tag(v_a_2769_) == 0)
{
lean_object* v_k_2770_; lean_object* v_l_2771_; lean_object* v_r_2772_; lean_object* v___x_2773_; uint8_t v___x_2774_; 
v_k_2770_ = lean_ctor_get(v_a_2769_, 1);
lean_inc_n(v_k_2770_, 2);
v_l_2771_ = lean_ctor_get(v_a_2769_, 3);
lean_inc(v_l_2771_);
v_r_2772_ = lean_ctor_get(v_a_2769_, 4);
lean_inc(v_r_2772_);
lean_dec_ref_known(v_a_2769_, 5);
lean_inc_ref(v_inst_2766_);
lean_inc(v_k_2767_);
v___x_2773_ = lean_apply_2(v_inst_2766_, v_k_2767_, v_k_2770_);
v___x_2774_ = lean_unbox(v___x_2773_);
switch(v___x_2774_)
{
case 0:
{
lean_object* v___x_2775_; 
lean_dec(v_r_2772_);
lean_dec(v_best_2768_);
v___x_2775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2775_, 0, v_k_2770_);
v_best_2768_ = v___x_2775_;
v_a_2769_ = v_l_2771_;
goto _start;
}
case 1:
{
lean_object* v___x_2777_; 
lean_dec(v_r_2772_);
lean_dec(v_l_2771_);
lean_dec(v_best_2768_);
lean_dec(v_k_2767_);
lean_dec_ref(v_inst_2766_);
v___x_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2777_, 0, v_k_2770_);
return v___x_2777_;
}
default: 
{
lean_dec(v_l_2771_);
lean_dec(v_k_2770_);
v_a_2769_ = v_r_2772_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2767_);
lean_dec_ref(v_inst_2766_);
return v_best_2768_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(lean_object* v_00_u03b1_2779_, lean_object* v_00_u03b2_2780_, lean_object* v_inst_2781_, lean_object* v_k_2782_, lean_object* v_best_2783_, lean_object* v_a_2784_){
_start:
{
lean_object* v___x_2785_; 
v___x_2785_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2781_, v_k_2782_, v_best_2783_, v_a_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___redArg(lean_object* v_inst_2786_, lean_object* v_k_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = lean_box(0);
v___x_2790_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2786_, v_k_2787_, v___x_2789_, v_a_2788_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(lean_object* v_00_u03b1_2791_, lean_object* v_00_u03b2_2792_, lean_object* v_inst_2793_, lean_object* v_k_2794_, lean_object* v_a_2795_){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_box(0);
v___x_2797_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2793_, v_k_2794_, v___x_2796_, v_a_2795_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object* v_inst_2798_, lean_object* v_k_2799_, lean_object* v_best_2800_, lean_object* v_a_2801_){
_start:
{
if (lean_obj_tag(v_a_2801_) == 0)
{
lean_object* v_k_2802_; lean_object* v_l_2803_; lean_object* v_r_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; 
v_k_2802_ = lean_ctor_get(v_a_2801_, 1);
lean_inc_n(v_k_2802_, 2);
v_l_2803_ = lean_ctor_get(v_a_2801_, 3);
lean_inc(v_l_2803_);
v_r_2804_ = lean_ctor_get(v_a_2801_, 4);
lean_inc(v_r_2804_);
lean_dec_ref_known(v_a_2801_, 5);
lean_inc_ref(v_inst_2798_);
lean_inc(v_k_2799_);
v___x_2805_ = lean_apply_2(v_inst_2798_, v_k_2799_, v_k_2802_);
v___x_2806_ = lean_unbox(v___x_2805_);
if (v___x_2806_ == 0)
{
lean_object* v___x_2807_; 
lean_dec(v_r_2804_);
lean_dec(v_best_2800_);
v___x_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2807_, 0, v_k_2802_);
v_best_2800_ = v___x_2807_;
v_a_2801_ = v_l_2803_;
goto _start;
}
else
{
lean_dec(v_l_2803_);
lean_dec(v_k_2802_);
v_a_2801_ = v_r_2804_;
goto _start;
}
}
else
{
lean_dec(v_k_2799_);
lean_dec_ref(v_inst_2798_);
return v_best_2800_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(lean_object* v_00_u03b1_2810_, lean_object* v_00_u03b2_2811_, lean_object* v_inst_2812_, lean_object* v_k_2813_, lean_object* v_best_2814_, lean_object* v_a_2815_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2812_, v_k_2813_, v_best_2814_, v_a_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___redArg(lean_object* v_inst_2817_, lean_object* v_k_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = lean_box(0);
v___x_2821_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2817_, v_k_2818_, v___x_2820_, v_a_2819_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(lean_object* v_00_u03b1_2822_, lean_object* v_00_u03b2_2823_, lean_object* v_inst_2824_, lean_object* v_k_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = lean_box(0);
v___x_2828_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2824_, v_k_2825_, v___x_2827_, v_a_2826_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object* v_inst_2829_, lean_object* v_k_2830_, lean_object* v_best_2831_, lean_object* v_a_2832_){
_start:
{
if (lean_obj_tag(v_a_2832_) == 0)
{
lean_object* v_k_2833_; lean_object* v_l_2834_; lean_object* v_r_2835_; lean_object* v___x_2836_; uint8_t v___x_2837_; 
v_k_2833_ = lean_ctor_get(v_a_2832_, 1);
lean_inc_n(v_k_2833_, 2);
v_l_2834_ = lean_ctor_get(v_a_2832_, 3);
lean_inc(v_l_2834_);
v_r_2835_ = lean_ctor_get(v_a_2832_, 4);
lean_inc(v_r_2835_);
lean_dec_ref_known(v_a_2832_, 5);
lean_inc_ref(v_inst_2829_);
lean_inc(v_k_2830_);
v___x_2836_ = lean_apply_2(v_inst_2829_, v_k_2830_, v_k_2833_);
v___x_2837_ = lean_unbox(v___x_2836_);
switch(v___x_2837_)
{
case 0:
{
lean_dec(v_r_2835_);
lean_dec(v_k_2833_);
v_a_2832_ = v_l_2834_;
goto _start;
}
case 1:
{
lean_object* v___x_2839_; 
lean_dec(v_r_2835_);
lean_dec(v_l_2834_);
lean_dec(v_best_2831_);
lean_dec(v_k_2830_);
lean_dec_ref(v_inst_2829_);
v___x_2839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2839_, 0, v_k_2833_);
return v___x_2839_;
}
default: 
{
lean_object* v___x_2840_; 
lean_dec(v_l_2834_);
lean_dec(v_best_2831_);
v___x_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2840_, 0, v_k_2833_);
v_best_2831_ = v___x_2840_;
v_a_2832_ = v_r_2835_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2830_);
lean_dec_ref(v_inst_2829_);
return v_best_2831_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(lean_object* v_00_u03b1_2842_, lean_object* v_00_u03b2_2843_, lean_object* v_inst_2844_, lean_object* v_k_2845_, lean_object* v_best_2846_, lean_object* v_a_2847_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2844_, v_k_2845_, v_best_2846_, v_a_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___redArg(lean_object* v_inst_2849_, lean_object* v_k_2850_, lean_object* v_a_2851_){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; 
v___x_2852_ = lean_box(0);
v___x_2853_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2849_, v_k_2850_, v___x_2852_, v_a_2851_);
return v___x_2853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(lean_object* v_00_u03b1_2854_, lean_object* v_00_u03b2_2855_, lean_object* v_inst_2856_, lean_object* v_k_2857_, lean_object* v_a_2858_){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = lean_box(0);
v___x_2860_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2856_, v_k_2857_, v___x_2859_, v_a_2858_);
return v___x_2860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object* v_inst_2861_, lean_object* v_k_2862_, lean_object* v_best_2863_, lean_object* v_a_2864_){
_start:
{
if (lean_obj_tag(v_a_2864_) == 0)
{
lean_object* v_k_2865_; lean_object* v_l_2866_; lean_object* v_r_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v_k_2865_ = lean_ctor_get(v_a_2864_, 1);
lean_inc_n(v_k_2865_, 2);
v_l_2866_ = lean_ctor_get(v_a_2864_, 3);
lean_inc(v_l_2866_);
v_r_2867_ = lean_ctor_get(v_a_2864_, 4);
lean_inc(v_r_2867_);
lean_dec_ref_known(v_a_2864_, 5);
lean_inc_ref(v_inst_2861_);
lean_inc(v_k_2862_);
v___x_2868_ = lean_apply_2(v_inst_2861_, v_k_2862_, v_k_2865_);
v___x_2869_ = lean_unbox(v___x_2868_);
if (v___x_2869_ == 2)
{
lean_object* v___x_2870_; 
lean_dec(v_l_2866_);
lean_dec(v_best_2863_);
v___x_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2870_, 0, v_k_2865_);
v_best_2863_ = v___x_2870_;
v_a_2864_ = v_r_2867_;
goto _start;
}
else
{
lean_dec(v_r_2867_);
lean_dec(v_k_2865_);
v_a_2864_ = v_l_2866_;
goto _start;
}
}
else
{
lean_dec(v_k_2862_);
lean_dec_ref(v_inst_2861_);
return v_best_2863_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(lean_object* v_00_u03b1_2873_, lean_object* v_00_u03b2_2874_, lean_object* v_inst_2875_, lean_object* v_k_2876_, lean_object* v_best_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v___x_2879_; 
v___x_2879_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2875_, v_k_2876_, v_best_2877_, v_a_2878_);
return v___x_2879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___redArg(lean_object* v_inst_2880_, lean_object* v_k_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_box(0);
v___x_2884_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2880_, v_k_2881_, v___x_2883_, v_a_2882_);
return v___x_2884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(lean_object* v_00_u03b1_2885_, lean_object* v_00_u03b2_2886_, lean_object* v_inst_2887_, lean_object* v_k_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2890_ = lean_box(0);
v___x_2891_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2887_, v_k_2888_, v___x_2890_, v_a_2889_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_k_2894_, lean_object* v_t_2895_){
_start:
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_box(0);
v___x_2897_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2892_, v_k_2894_, v___x_2896_, v_t_2895_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2899_ = l_panic___redArg(v_inst_2893_, v___x_2898_);
return v___x_2899_;
}
else
{
lean_object* v_val_2900_; 
v_val_2900_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_val_2900_);
lean_dec_ref_known(v___x_2897_, 1);
return v_val_2900_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg___boxed(lean_object* v_inst_2901_, lean_object* v_inst_2902_, lean_object* v_k_2903_, lean_object* v_t_2904_){
_start:
{
lean_object* v_res_2905_; 
v_res_2905_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(v_inst_2901_, v_inst_2902_, v_k_2903_, v_t_2904_);
lean_dec(v_inst_2902_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object* v_00_u03b1_2906_, lean_object* v_00_u03b2_2907_, lean_object* v_inst_2908_, lean_object* v_inst_2909_, lean_object* v_k_2910_, lean_object* v_t_2911_){
_start:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_box(0);
v___x_2913_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2908_, v_k_2910_, v___x_2912_, v_t_2911_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2915_ = l_panic___redArg(v_inst_2909_, v___x_2914_);
return v___x_2915_;
}
else
{
lean_object* v_val_2916_; 
v_val_2916_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_val_2916_);
lean_dec_ref_known(v___x_2913_, 1);
return v_val_2916_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___boxed(lean_object* v_00_u03b1_2917_, lean_object* v_00_u03b2_2918_, lean_object* v_inst_2919_, lean_object* v_inst_2920_, lean_object* v_k_2921_, lean_object* v_t_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(v_00_u03b1_2917_, v_00_u03b2_2918_, v_inst_2919_, v_inst_2920_, v_k_2921_, v_t_2922_);
lean_dec(v_inst_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_k_2926_, lean_object* v_t_2927_){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = lean_box(0);
v___x_2929_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2924_, v_k_2926_, v___x_2928_, v_t_2927_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2931_ = l_panic___redArg(v_inst_2925_, v___x_2930_);
return v___x_2931_;
}
else
{
lean_object* v_val_2932_; 
v_val_2932_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_val_2932_);
lean_dec_ref_known(v___x_2929_, 1);
return v_val_2932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg___boxed(lean_object* v_inst_2933_, lean_object* v_inst_2934_, lean_object* v_k_2935_, lean_object* v_t_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(v_inst_2933_, v_inst_2934_, v_k_2935_, v_t_2936_);
lean_dec(v_inst_2934_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object* v_00_u03b1_2938_, lean_object* v_00_u03b2_2939_, lean_object* v_inst_2940_, lean_object* v_inst_2941_, lean_object* v_k_2942_, lean_object* v_t_2943_){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = lean_box(0);
v___x_2945_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2940_, v_k_2942_, v___x_2944_, v_t_2943_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2947_ = l_panic___redArg(v_inst_2941_, v___x_2946_);
return v___x_2947_;
}
else
{
lean_object* v_val_2948_; 
v_val_2948_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_val_2948_);
lean_dec_ref_known(v___x_2945_, 1);
return v_val_2948_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___boxed(lean_object* v_00_u03b1_2949_, lean_object* v_00_u03b2_2950_, lean_object* v_inst_2951_, lean_object* v_inst_2952_, lean_object* v_k_2953_, lean_object* v_t_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(v_00_u03b1_2949_, v_00_u03b2_2950_, v_inst_2951_, v_inst_2952_, v_k_2953_, v_t_2954_);
lean_dec(v_inst_2952_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_k_2958_, lean_object* v_t_2959_){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; 
v___x_2960_ = lean_box(0);
v___x_2961_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2956_, v_k_2958_, v___x_2960_, v_t_2959_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2963_ = l_panic___redArg(v_inst_2957_, v___x_2962_);
return v___x_2963_;
}
else
{
lean_object* v_val_2964_; 
v_val_2964_ = lean_ctor_get(v___x_2961_, 0);
lean_inc(v_val_2964_);
lean_dec_ref_known(v___x_2961_, 1);
return v_val_2964_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg___boxed(lean_object* v_inst_2965_, lean_object* v_inst_2966_, lean_object* v_k_2967_, lean_object* v_t_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(v_inst_2965_, v_inst_2966_, v_k_2967_, v_t_2968_);
lean_dec(v_inst_2966_);
return v_res_2969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object* v_00_u03b1_2970_, lean_object* v_00_u03b2_2971_, lean_object* v_inst_2972_, lean_object* v_inst_2973_, lean_object* v_k_2974_, lean_object* v_t_2975_){
_start:
{
lean_object* v___x_2976_; lean_object* v___x_2977_; 
v___x_2976_ = lean_box(0);
v___x_2977_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2972_, v_k_2974_, v___x_2976_, v_t_2975_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2978_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2979_ = l_panic___redArg(v_inst_2973_, v___x_2978_);
return v___x_2979_;
}
else
{
lean_object* v_val_2980_; 
v_val_2980_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_val_2980_);
lean_dec_ref_known(v___x_2977_, 1);
return v_val_2980_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___boxed(lean_object* v_00_u03b1_2981_, lean_object* v_00_u03b2_2982_, lean_object* v_inst_2983_, lean_object* v_inst_2984_, lean_object* v_k_2985_, lean_object* v_t_2986_){
_start:
{
lean_object* v_res_2987_; 
v_res_2987_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(v_00_u03b1_2981_, v_00_u03b2_2982_, v_inst_2983_, v_inst_2984_, v_k_2985_, v_t_2986_);
lean_dec(v_inst_2984_);
return v_res_2987_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_k_2990_, lean_object* v_t_2991_){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; 
v___x_2992_ = lean_box(0);
v___x_2993_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2988_, v_k_2990_, v___x_2992_, v_t_2991_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2995_ = l_panic___redArg(v_inst_2989_, v___x_2994_);
return v___x_2995_;
}
else
{
lean_object* v_val_2996_; 
v_val_2996_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_val_2996_);
lean_dec_ref_known(v___x_2993_, 1);
return v_val_2996_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg___boxed(lean_object* v_inst_2997_, lean_object* v_inst_2998_, lean_object* v_k_2999_, lean_object* v_t_3000_){
_start:
{
lean_object* v_res_3001_; 
v_res_3001_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(v_inst_2997_, v_inst_2998_, v_k_2999_, v_t_3000_);
lean_dec(v_inst_2998_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object* v_00_u03b1_3002_, lean_object* v_00_u03b2_3003_, lean_object* v_inst_3004_, lean_object* v_inst_3005_, lean_object* v_k_3006_, lean_object* v_t_3007_){
_start:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; 
v___x_3008_ = lean_box(0);
v___x_3009_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3004_, v_k_3006_, v___x_3008_, v_t_3007_);
if (lean_obj_tag(v___x_3009_) == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3010_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3011_ = l_panic___redArg(v_inst_3005_, v___x_3010_);
return v___x_3011_;
}
else
{
lean_object* v_val_3012_; 
v_val_3012_ = lean_ctor_get(v___x_3009_, 0);
lean_inc(v_val_3012_);
lean_dec_ref_known(v___x_3009_, 1);
return v_val_3012_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___boxed(lean_object* v_00_u03b1_3013_, lean_object* v_00_u03b2_3014_, lean_object* v_inst_3015_, lean_object* v_inst_3016_, lean_object* v_k_3017_, lean_object* v_t_3018_){
_start:
{
lean_object* v_res_3019_; 
v_res_3019_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(v_00_u03b1_3013_, v_00_u03b2_3014_, v_inst_3015_, v_inst_3016_, v_k_3017_, v_t_3018_);
lean_dec(v_inst_3016_);
return v_res_3019_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(lean_object* v_inst_3020_, lean_object* v_k_3021_, lean_object* v_t_3022_, lean_object* v_fallback_3023_){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3024_ = lean_box(0);
v___x_3025_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3020_, v_k_3021_, v___x_3024_, v_t_3022_);
if (lean_obj_tag(v___x_3025_) == 0)
{
lean_inc(v_fallback_3023_);
return v_fallback_3023_;
}
else
{
lean_object* v_val_3026_; 
v_val_3026_ = lean_ctor_get(v___x_3025_, 0);
lean_inc(v_val_3026_);
lean_dec_ref_known(v___x_3025_, 1);
return v_val_3026_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg___boxed(lean_object* v_inst_3027_, lean_object* v_k_3028_, lean_object* v_t_3029_, lean_object* v_fallback_3030_){
_start:
{
lean_object* v_res_3031_; 
v_res_3031_ = l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(v_inst_3027_, v_k_3028_, v_t_3029_, v_fallback_3030_);
lean_dec(v_fallback_3030_);
return v_res_3031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED(lean_object* v_00_u03b1_3032_, lean_object* v_00_u03b2_3033_, lean_object* v_inst_3034_, lean_object* v_k_3035_, lean_object* v_t_3036_, lean_object* v_fallback_3037_){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
v___x_3038_ = lean_box(0);
v___x_3039_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3034_, v_k_3035_, v___x_3038_, v_t_3036_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_inc(v_fallback_3037_);
return v_fallback_3037_;
}
else
{
lean_object* v_val_3040_; 
v_val_3040_ = lean_ctor_get(v___x_3039_, 0);
lean_inc(v_val_3040_);
lean_dec_ref_known(v___x_3039_, 1);
return v_val_3040_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___boxed(lean_object* v_00_u03b1_3041_, lean_object* v_00_u03b2_3042_, lean_object* v_inst_3043_, lean_object* v_k_3044_, lean_object* v_t_3045_, lean_object* v_fallback_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Std_DTreeMap_Internal_Impl_getKeyGED(v_00_u03b1_3041_, v_00_u03b2_3042_, v_inst_3043_, v_k_3044_, v_t_3045_, v_fallback_3046_);
lean_dec(v_fallback_3046_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(lean_object* v_inst_3048_, lean_object* v_k_3049_, lean_object* v_t_3050_, lean_object* v_fallback_3051_){
_start:
{
lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3052_ = lean_box(0);
v___x_3053_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3048_, v_k_3049_, v___x_3052_, v_t_3050_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_inc(v_fallback_3051_);
return v_fallback_3051_;
}
else
{
lean_object* v_val_3054_; 
v_val_3054_ = lean_ctor_get(v___x_3053_, 0);
lean_inc(v_val_3054_);
lean_dec_ref_known(v___x_3053_, 1);
return v_val_3054_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg___boxed(lean_object* v_inst_3055_, lean_object* v_k_3056_, lean_object* v_t_3057_, lean_object* v_fallback_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(v_inst_3055_, v_k_3056_, v_t_3057_, v_fallback_3058_);
lean_dec(v_fallback_3058_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD(lean_object* v_00_u03b1_3060_, lean_object* v_00_u03b2_3061_, lean_object* v_inst_3062_, lean_object* v_k_3063_, lean_object* v_t_3064_, lean_object* v_fallback_3065_){
_start:
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_box(0);
v___x_3067_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3062_, v_k_3063_, v___x_3066_, v_t_3064_);
if (lean_obj_tag(v___x_3067_) == 0)
{
lean_inc(v_fallback_3065_);
return v_fallback_3065_;
}
else
{
lean_object* v_val_3068_; 
v_val_3068_ = lean_ctor_get(v___x_3067_, 0);
lean_inc(v_val_3068_);
lean_dec_ref_known(v___x_3067_, 1);
return v_val_3068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___boxed(lean_object* v_00_u03b1_3069_, lean_object* v_00_u03b2_3070_, lean_object* v_inst_3071_, lean_object* v_k_3072_, lean_object* v_t_3073_, lean_object* v_fallback_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD(v_00_u03b1_3069_, v_00_u03b2_3070_, v_inst_3071_, v_k_3072_, v_t_3073_, v_fallback_3074_);
lean_dec(v_fallback_3074_);
return v_res_3075_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(lean_object* v_inst_3076_, lean_object* v_k_3077_, lean_object* v_t_3078_, lean_object* v_fallback_3079_){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = lean_box(0);
v___x_3081_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3076_, v_k_3077_, v___x_3080_, v_t_3078_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_inc(v_fallback_3079_);
return v_fallback_3079_;
}
else
{
lean_object* v_val_3082_; 
v_val_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_val_3082_);
lean_dec_ref_known(v___x_3081_, 1);
return v_val_3082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg___boxed(lean_object* v_inst_3083_, lean_object* v_k_3084_, lean_object* v_t_3085_, lean_object* v_fallback_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(v_inst_3083_, v_k_3084_, v_t_3085_, v_fallback_3086_);
lean_dec(v_fallback_3086_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED(lean_object* v_00_u03b1_3088_, lean_object* v_00_u03b2_3089_, lean_object* v_inst_3090_, lean_object* v_k_3091_, lean_object* v_t_3092_, lean_object* v_fallback_3093_){
_start:
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3094_ = lean_box(0);
v___x_3095_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3090_, v_k_3091_, v___x_3094_, v_t_3092_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_inc(v_fallback_3093_);
return v_fallback_3093_;
}
else
{
lean_object* v_val_3096_; 
v_val_3096_ = lean_ctor_get(v___x_3095_, 0);
lean_inc(v_val_3096_);
lean_dec_ref_known(v___x_3095_, 1);
return v_val_3096_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___boxed(lean_object* v_00_u03b1_3097_, lean_object* v_00_u03b2_3098_, lean_object* v_inst_3099_, lean_object* v_k_3100_, lean_object* v_t_3101_, lean_object* v_fallback_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Std_DTreeMap_Internal_Impl_getKeyLED(v_00_u03b1_3097_, v_00_u03b2_3098_, v_inst_3099_, v_k_3100_, v_t_3101_, v_fallback_3102_);
lean_dec(v_fallback_3102_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(lean_object* v_inst_3104_, lean_object* v_k_3105_, lean_object* v_t_3106_, lean_object* v_fallback_3107_){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3108_ = lean_box(0);
v___x_3109_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3104_, v_k_3105_, v___x_3108_, v_t_3106_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_inc(v_fallback_3107_);
return v_fallback_3107_;
}
else
{
lean_object* v_val_3110_; 
v_val_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_val_3110_);
lean_dec_ref_known(v___x_3109_, 1);
return v_val_3110_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg___boxed(lean_object* v_inst_3111_, lean_object* v_k_3112_, lean_object* v_t_3113_, lean_object* v_fallback_3114_){
_start:
{
lean_object* v_res_3115_; 
v_res_3115_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(v_inst_3111_, v_k_3112_, v_t_3113_, v_fallback_3114_);
lean_dec(v_fallback_3114_);
return v_res_3115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD(lean_object* v_00_u03b1_3116_, lean_object* v_00_u03b2_3117_, lean_object* v_inst_3118_, lean_object* v_k_3119_, lean_object* v_t_3120_, lean_object* v_fallback_3121_){
_start:
{
lean_object* v___x_3122_; lean_object* v___x_3123_; 
v___x_3122_ = lean_box(0);
v___x_3123_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3118_, v_k_3119_, v___x_3122_, v_t_3120_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_inc(v_fallback_3121_);
return v_fallback_3121_;
}
else
{
lean_object* v_val_3124_; 
v_val_3124_ = lean_ctor_get(v___x_3123_, 0);
lean_inc(v_val_3124_);
lean_dec_ref_known(v___x_3123_, 1);
return v_val_3124_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___boxed(lean_object* v_00_u03b1_3125_, lean_object* v_00_u03b2_3126_, lean_object* v_inst_3127_, lean_object* v_k_3128_, lean_object* v_t_3129_, lean_object* v_fallback_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD(v_00_u03b1_3125_, v_00_u03b2_3126_, v_inst_3127_, v_k_3128_, v_t_3129_, v_fallback_3130_);
lean_dec(v_fallback_3130_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object* v_inst_3132_, lean_object* v_k_3133_, lean_object* v_x_3134_){
_start:
{
lean_object* v_k_3135_; lean_object* v_l_3136_; lean_object* v_r_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v_k_3135_ = lean_ctor_get(v_x_3134_, 1);
lean_inc_n(v_k_3135_, 2);
v_l_3136_ = lean_ctor_get(v_x_3134_, 3);
lean_inc(v_l_3136_);
v_r_3137_ = lean_ctor_get(v_x_3134_, 4);
lean_inc(v_r_3137_);
lean_dec(v_x_3134_);
lean_inc_ref(v_inst_3132_);
lean_inc(v_k_3133_);
v___x_3138_ = lean_apply_2(v_inst_3132_, v_k_3133_, v_k_3135_);
v___x_3139_ = lean_unbox(v___x_3138_);
switch(v___x_3139_)
{
case 0:
{
lean_object* v___x_3140_; lean_object* v___x_3141_; 
lean_dec(v_r_3137_);
v___x_3140_ = lean_box(0);
v___x_3141_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3132_, v_k_3133_, v___x_3140_, v_l_3136_);
if (lean_obj_tag(v___x_3141_) == 0)
{
return v_k_3135_;
}
else
{
lean_object* v_val_3142_; 
lean_dec(v_k_3135_);
v_val_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc(v_val_3142_);
lean_dec_ref_known(v___x_3141_, 1);
return v_val_3142_;
}
}
case 1:
{
lean_dec(v_r_3137_);
lean_dec(v_l_3136_);
lean_dec(v_k_3133_);
lean_dec_ref(v_inst_3132_);
return v_k_3135_;
}
default: 
{
lean_dec(v_l_3136_);
lean_dec(v_k_3135_);
v_x_3134_ = v_r_3137_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE(lean_object* v_00_u03b1_3144_, lean_object* v_00_u03b2_3145_, lean_object* v_inst_3146_, lean_object* v_inst_3147_, lean_object* v_k_3148_, lean_object* v_x_3149_, lean_object* v_x_3150_, lean_object* v_x_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_inst_3146_, v_k_3148_, v_x_3149_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object* v_inst_3153_, lean_object* v_k_3154_, lean_object* v_x_3155_){
_start:
{
lean_object* v_k_3156_; lean_object* v_l_3157_; lean_object* v_r_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; lean_object* v___x_3161_; lean_object* v___x_3162_; uint8_t v___x_3163_; 
v_k_3156_ = lean_ctor_get(v_x_3155_, 1);
lean_inc_n(v_k_3156_, 2);
v_l_3157_ = lean_ctor_get(v_x_3155_, 3);
lean_inc(v_l_3157_);
v_r_3158_ = lean_ctor_get(v_x_3155_, 4);
lean_inc(v_r_3158_);
lean_dec(v_x_3155_);
lean_inc_ref(v_inst_3153_);
lean_inc(v_k_3154_);
v___x_3159_ = lean_apply_2(v_inst_3153_, v_k_3154_, v_k_3156_);
v___x_3160_ = lean_unbox(v___x_3159_);
v___x_3161_ = l_Ordering_ctorIdx(v___x_3160_);
v___x_3162_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0);
v___x_3163_ = lean_nat_dec_eq(v___x_3161_, v___x_3162_);
lean_dec(v___x_3161_);
if (v___x_3163_ == 0)
{
lean_dec(v_l_3157_);
lean_dec(v_k_3156_);
v_x_3155_ = v_r_3158_;
goto _start;
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
lean_dec(v_r_3158_);
v___x_3165_ = lean_box(0);
v___x_3166_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3153_, v_k_3154_, v___x_3165_, v_l_3157_);
if (lean_obj_tag(v___x_3166_) == 0)
{
return v_k_3156_;
}
else
{
lean_object* v_val_3167_; 
lean_dec(v_k_3156_);
v_val_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_val_3167_);
lean_dec_ref_known(v___x_3166_, 1);
return v_val_3167_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT(lean_object* v_00_u03b1_3168_, lean_object* v_00_u03b2_3169_, lean_object* v_inst_3170_, lean_object* v_inst_3171_, lean_object* v_k_3172_, lean_object* v_x_3173_, lean_object* v_x_3174_, lean_object* v_x_3175_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_inst_3170_, v_k_3172_, v_x_3173_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object* v_inst_3177_, lean_object* v_k_3178_, lean_object* v_x_3179_){
_start:
{
lean_object* v_k_3180_; lean_object* v_l_3181_; lean_object* v_r_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v_k_3180_ = lean_ctor_get(v_x_3179_, 1);
lean_inc_n(v_k_3180_, 2);
v_l_3181_ = lean_ctor_get(v_x_3179_, 3);
lean_inc(v_l_3181_);
v_r_3182_ = lean_ctor_get(v_x_3179_, 4);
lean_inc(v_r_3182_);
lean_dec(v_x_3179_);
lean_inc_ref(v_inst_3177_);
lean_inc(v_k_3178_);
v___x_3183_ = lean_apply_2(v_inst_3177_, v_k_3178_, v_k_3180_);
v___x_3184_ = lean_unbox(v___x_3183_);
switch(v___x_3184_)
{
case 0:
{
lean_dec(v_r_3182_);
lean_dec(v_k_3180_);
v_x_3179_ = v_l_3181_;
goto _start;
}
case 1:
{
lean_dec(v_r_3182_);
lean_dec(v_l_3181_);
lean_dec(v_k_3178_);
lean_dec_ref(v_inst_3177_);
return v_k_3180_;
}
default: 
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
lean_dec(v_l_3181_);
v___x_3186_ = lean_box(0);
v___x_3187_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3177_, v_k_3178_, v___x_3186_, v_r_3182_);
if (lean_obj_tag(v___x_3187_) == 0)
{
return v_k_3180_;
}
else
{
lean_object* v_val_3188_; 
lean_dec(v_k_3180_);
v_val_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc(v_val_3188_);
lean_dec_ref_known(v___x_3187_, 1);
return v_val_3188_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE(lean_object* v_00_u03b1_3189_, lean_object* v_00_u03b2_3190_, lean_object* v_inst_3191_, lean_object* v_inst_3192_, lean_object* v_k_3193_, lean_object* v_x_3194_, lean_object* v_x_3195_, lean_object* v_x_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_inst_3191_, v_k_3193_, v_x_3194_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object* v_inst_3198_, lean_object* v_k_3199_, lean_object* v_x_3200_){
_start:
{
lean_object* v_k_3201_; lean_object* v_l_3202_; lean_object* v_r_3203_; lean_object* v___x_3204_; uint8_t v___x_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; 
v_k_3201_ = lean_ctor_get(v_x_3200_, 1);
lean_inc_n(v_k_3201_, 2);
v_l_3202_ = lean_ctor_get(v_x_3200_, 3);
lean_inc(v_l_3202_);
v_r_3203_ = lean_ctor_get(v_x_3200_, 4);
lean_inc(v_r_3203_);
lean_dec(v_x_3200_);
lean_inc_ref(v_inst_3198_);
lean_inc(v_k_3199_);
v___x_3204_ = lean_apply_2(v_inst_3198_, v_k_3199_, v_k_3201_);
v___x_3205_ = lean_unbox(v___x_3204_);
v___x_3206_ = l_Ordering_ctorIdx(v___x_3205_);
v___x_3207_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0);
v___x_3208_ = lean_nat_dec_eq(v___x_3206_, v___x_3207_);
lean_dec(v___x_3206_);
if (v___x_3208_ == 0)
{
lean_dec(v_r_3203_);
lean_dec(v_k_3201_);
v_x_3200_ = v_l_3202_;
goto _start;
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec(v_l_3202_);
v___x_3210_ = lean_box(0);
v___x_3211_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3198_, v_k_3199_, v___x_3210_, v_r_3203_);
if (lean_obj_tag(v___x_3211_) == 0)
{
return v_k_3201_;
}
else
{
lean_object* v_val_3212_; 
lean_dec(v_k_3201_);
v_val_3212_ = lean_ctor_get(v___x_3211_, 0);
lean_inc(v_val_3212_);
lean_dec_ref_known(v___x_3211_, 1);
return v_val_3212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT(lean_object* v_00_u03b1_3213_, lean_object* v_00_u03b2_3214_, lean_object* v_inst_3215_, lean_object* v_inst_3216_, lean_object* v_k_3217_, lean_object* v_x_3218_, lean_object* v_x_3219_, lean_object* v_x_3220_){
_start:
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_inst_3215_, v_k_3217_, v_x_3218_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object* v_x_3222_){
_start:
{
if (lean_obj_tag(v_x_3222_) == 0)
{
lean_object* v_l_3223_; 
v_l_3223_ = lean_ctor_get(v_x_3222_, 3);
if (lean_obj_tag(v_l_3223_) == 0)
{
v_x_3222_ = v_l_3223_;
goto _start;
}
else
{
lean_object* v_k_3225_; lean_object* v_v_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v_k_3225_ = lean_ctor_get(v_x_3222_, 1);
v_v_3226_ = lean_ctor_get(v_x_3222_, 2);
lean_inc(v_v_3226_);
lean_inc(v_k_3225_);
v___x_3227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3227_, 0, v_k_3225_);
lean_ctor_set(v___x_3227_, 1, v_v_3226_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
return v___x_3228_;
}
}
else
{
lean_object* v___x_3229_; 
v___x_3229_ = lean_box(0);
return v___x_3229_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg___boxed(lean_object* v_x_3230_){
_start:
{
lean_object* v_res_3231_; 
v_res_3231_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3230_);
lean_dec(v_x_3230_);
return v_res_3231_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(lean_object* v_00_u03b1_3232_, lean_object* v_00_u03b2_3233_, lean_object* v_x_3234_){
_start:
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3234_);
return v___x_3235_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_3236_, lean_object* v_00_u03b2_3237_, lean_object* v_x_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(v_00_u03b1_3236_, v_00_u03b2_3237_, v_x_3238_);
lean_dec(v_x_3238_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3240_, lean_object* v_h__1_3241_, lean_object* v_h__2_3242_, lean_object* v_h__3_3243_){
_start:
{
if (lean_obj_tag(v_x_3240_) == 0)
{
lean_object* v_l_3244_; 
lean_dec(v_h__1_3241_);
v_l_3244_ = lean_ctor_get(v_x_3240_, 3);
if (lean_obj_tag(v_l_3244_) == 0)
{
lean_object* v_size_3245_; lean_object* v_k_3246_; lean_object* v_v_3247_; lean_object* v_r_3248_; lean_object* v_size_3249_; lean_object* v_k_3250_; lean_object* v_v_3251_; lean_object* v_l_3252_; lean_object* v_r_3253_; lean_object* v___x_3254_; 
lean_inc_ref(v_l_3244_);
lean_dec(v_h__2_3242_);
v_size_3245_ = lean_ctor_get(v_x_3240_, 0);
lean_inc(v_size_3245_);
v_k_3246_ = lean_ctor_get(v_x_3240_, 1);
lean_inc(v_k_3246_);
v_v_3247_ = lean_ctor_get(v_x_3240_, 2);
lean_inc(v_v_3247_);
v_r_3248_ = lean_ctor_get(v_x_3240_, 4);
lean_inc(v_r_3248_);
lean_dec_ref_known(v_x_3240_, 5);
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
lean_dec_ref_known(v_l_3244_, 5);
v___x_3254_ = lean_apply_9(v_h__3_3243_, v_size_3245_, v_k_3246_, v_v_3247_, v_size_3249_, v_k_3250_, v_v_3251_, v_l_3252_, v_r_3253_, v_r_3248_);
return v___x_3254_;
}
else
{
lean_object* v_size_3255_; lean_object* v_k_3256_; lean_object* v_v_3257_; lean_object* v_r_3258_; lean_object* v___x_3259_; 
lean_dec(v_h__3_3243_);
v_size_3255_ = lean_ctor_get(v_x_3240_, 0);
lean_inc(v_size_3255_);
v_k_3256_ = lean_ctor_get(v_x_3240_, 1);
lean_inc(v_k_3256_);
v_v_3257_ = lean_ctor_get(v_x_3240_, 2);
lean_inc(v_v_3257_);
v_r_3258_ = lean_ctor_get(v_x_3240_, 4);
lean_inc(v_r_3258_);
lean_dec_ref_known(v_x_3240_, 5);
v___x_3259_ = lean_apply_4(v_h__2_3242_, v_size_3255_, v_k_3256_, v_v_3257_, v_r_3258_);
return v___x_3259_;
}
}
else
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec(v_h__3_3243_);
lean_dec(v_h__2_3242_);
v___x_3260_ = lean_box(0);
v___x_3261_ = lean_apply_1(v_h__1_3241_, v___x_3260_);
return v___x_3261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3262_, lean_object* v_00_u03b2_3263_, lean_object* v_motive_3264_, lean_object* v_x_3265_, lean_object* v_h__1_3266_, lean_object* v_h__2_3267_, lean_object* v_h__3_3268_){
_start:
{
if (lean_obj_tag(v_x_3265_) == 0)
{
lean_object* v_l_3269_; 
lean_dec(v_h__1_3266_);
v_l_3269_ = lean_ctor_get(v_x_3265_, 3);
if (lean_obj_tag(v_l_3269_) == 0)
{
lean_object* v_size_3270_; lean_object* v_k_3271_; lean_object* v_v_3272_; lean_object* v_r_3273_; lean_object* v_size_3274_; lean_object* v_k_3275_; lean_object* v_v_3276_; lean_object* v_l_3277_; lean_object* v_r_3278_; lean_object* v___x_3279_; 
lean_inc_ref(v_l_3269_);
lean_dec(v_h__2_3267_);
v_size_3270_ = lean_ctor_get(v_x_3265_, 0);
lean_inc(v_size_3270_);
v_k_3271_ = lean_ctor_get(v_x_3265_, 1);
lean_inc(v_k_3271_);
v_v_3272_ = lean_ctor_get(v_x_3265_, 2);
lean_inc(v_v_3272_);
v_r_3273_ = lean_ctor_get(v_x_3265_, 4);
lean_inc(v_r_3273_);
lean_dec_ref_known(v_x_3265_, 5);
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
lean_dec_ref_known(v_l_3269_, 5);
v___x_3279_ = lean_apply_9(v_h__3_3268_, v_size_3270_, v_k_3271_, v_v_3272_, v_size_3274_, v_k_3275_, v_v_3276_, v_l_3277_, v_r_3278_, v_r_3273_);
return v___x_3279_;
}
else
{
lean_object* v_size_3280_; lean_object* v_k_3281_; lean_object* v_v_3282_; lean_object* v_r_3283_; lean_object* v___x_3284_; 
lean_dec(v_h__3_3268_);
v_size_3280_ = lean_ctor_get(v_x_3265_, 0);
lean_inc(v_size_3280_);
v_k_3281_ = lean_ctor_get(v_x_3265_, 1);
lean_inc(v_k_3281_);
v_v_3282_ = lean_ctor_get(v_x_3265_, 2);
lean_inc(v_v_3282_);
v_r_3283_ = lean_ctor_get(v_x_3265_, 4);
lean_inc(v_r_3283_);
lean_dec_ref_known(v_x_3265_, 5);
v___x_3284_ = lean_apply_4(v_h__2_3267_, v_size_3280_, v_k_3281_, v_v_3282_, v_r_3283_);
return v___x_3284_;
}
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3286_; 
lean_dec(v_h__3_3268_);
lean_dec(v_h__2_3267_);
v___x_3285_ = lean_box(0);
v___x_3286_ = lean_apply_1(v_h__1_3266_, v___x_3285_);
return v___x_3286_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object* v_x_3287_){
_start:
{
lean_object* v_l_3288_; 
v_l_3288_ = lean_ctor_get(v_x_3287_, 3);
if (lean_obj_tag(v_l_3288_) == 0)
{
v_x_3287_ = v_l_3288_;
goto _start;
}
else
{
lean_object* v_k_3290_; lean_object* v_v_3291_; lean_object* v___x_3292_; 
v_k_3290_ = lean_ctor_get(v_x_3287_, 1);
v_v_3291_ = lean_ctor_get(v_x_3287_, 2);
lean_inc(v_v_3291_);
lean_inc(v_k_3290_);
v___x_3292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3292_, 0, v_k_3290_);
lean_ctor_set(v___x_3292_, 1, v_v_3291_);
return v___x_3292_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg___boxed(lean_object* v_x_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3293_);
lean_dec(v_x_3293_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry(lean_object* v_00_u03b1_3295_, lean_object* v_00_u03b2_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3297_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___boxed(lean_object* v_00_u03b1_3300_, lean_object* v_00_u03b2_3301_, lean_object* v_x_3302_, lean_object* v_x_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry(v_00_u03b1_3300_, v_00_u03b2_3301_, v_x_3302_, v_x_3303_);
lean_dec(v_x_3302_);
return v_res_3304_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_3305_, lean_object* v_h__1_3306_, lean_object* v_h__2_3307_){
_start:
{
lean_object* v_l_3308_; 
v_l_3308_ = lean_ctor_get(v_x_3305_, 3);
if (lean_obj_tag(v_l_3308_) == 0)
{
lean_object* v_size_3309_; lean_object* v_k_3310_; lean_object* v_v_3311_; lean_object* v_r_3312_; lean_object* v_size_3313_; lean_object* v_k_3314_; lean_object* v_v_3315_; lean_object* v_l_3316_; lean_object* v_r_3317_; lean_object* v___x_3318_; 
lean_inc_ref(v_l_3308_);
lean_dec(v_h__1_3306_);
v_size_3309_ = lean_ctor_get(v_x_3305_, 0);
lean_inc(v_size_3309_);
v_k_3310_ = lean_ctor_get(v_x_3305_, 1);
lean_inc(v_k_3310_);
v_v_3311_ = lean_ctor_get(v_x_3305_, 2);
lean_inc(v_v_3311_);
v_r_3312_ = lean_ctor_get(v_x_3305_, 4);
lean_inc(v_r_3312_);
lean_dec(v_x_3305_);
v_size_3313_ = lean_ctor_get(v_l_3308_, 0);
lean_inc(v_size_3313_);
v_k_3314_ = lean_ctor_get(v_l_3308_, 1);
lean_inc(v_k_3314_);
v_v_3315_ = lean_ctor_get(v_l_3308_, 2);
lean_inc(v_v_3315_);
v_l_3316_ = lean_ctor_get(v_l_3308_, 3);
lean_inc(v_l_3316_);
v_r_3317_ = lean_ctor_get(v_l_3308_, 4);
lean_inc(v_r_3317_);
lean_dec_ref_known(v_l_3308_, 5);
v___x_3318_ = lean_apply_10(v_h__2_3307_, v_size_3309_, v_k_3310_, v_v_3311_, v_size_3313_, v_k_3314_, v_v_3315_, v_l_3316_, v_r_3317_, v_r_3312_, lean_box(0));
return v___x_3318_;
}
else
{
lean_object* v_size_3319_; lean_object* v_k_3320_; lean_object* v_v_3321_; lean_object* v_r_3322_; lean_object* v___x_3323_; 
lean_dec(v_h__2_3307_);
v_size_3319_ = lean_ctor_get(v_x_3305_, 0);
lean_inc(v_size_3319_);
v_k_3320_ = lean_ctor_get(v_x_3305_, 1);
lean_inc(v_k_3320_);
v_v_3321_ = lean_ctor_get(v_x_3305_, 2);
lean_inc(v_v_3321_);
v_r_3322_ = lean_ctor_get(v_x_3305_, 4);
lean_inc(v_r_3322_);
lean_dec(v_x_3305_);
v___x_3323_ = lean_apply_5(v_h__1_3306_, v_size_3319_, v_k_3320_, v_v_3321_, v_r_3322_, lean_box(0));
return v___x_3323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_3324_, lean_object* v_00_u03b2_3325_, lean_object* v_motive_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_, lean_object* v_h__1_3329_, lean_object* v_h__2_3330_){
_start:
{
lean_object* v_l_3331_; 
v_l_3331_ = lean_ctor_get(v_x_3327_, 3);
if (lean_obj_tag(v_l_3331_) == 0)
{
lean_object* v_size_3332_; lean_object* v_k_3333_; lean_object* v_v_3334_; lean_object* v_r_3335_; lean_object* v_size_3336_; lean_object* v_k_3337_; lean_object* v_v_3338_; lean_object* v_l_3339_; lean_object* v_r_3340_; lean_object* v___x_3341_; 
lean_inc_ref(v_l_3331_);
lean_dec(v_h__1_3329_);
v_size_3332_ = lean_ctor_get(v_x_3327_, 0);
lean_inc(v_size_3332_);
v_k_3333_ = lean_ctor_get(v_x_3327_, 1);
lean_inc(v_k_3333_);
v_v_3334_ = lean_ctor_get(v_x_3327_, 2);
lean_inc(v_v_3334_);
v_r_3335_ = lean_ctor_get(v_x_3327_, 4);
lean_inc(v_r_3335_);
lean_dec(v_x_3327_);
v_size_3336_ = lean_ctor_get(v_l_3331_, 0);
lean_inc(v_size_3336_);
v_k_3337_ = lean_ctor_get(v_l_3331_, 1);
lean_inc(v_k_3337_);
v_v_3338_ = lean_ctor_get(v_l_3331_, 2);
lean_inc(v_v_3338_);
v_l_3339_ = lean_ctor_get(v_l_3331_, 3);
lean_inc(v_l_3339_);
v_r_3340_ = lean_ctor_get(v_l_3331_, 4);
lean_inc(v_r_3340_);
lean_dec_ref_known(v_l_3331_, 5);
v___x_3341_ = lean_apply_10(v_h__2_3330_, v_size_3332_, v_k_3333_, v_v_3334_, v_size_3336_, v_k_3337_, v_v_3338_, v_l_3339_, v_r_3340_, v_r_3335_, lean_box(0));
return v___x_3341_;
}
else
{
lean_object* v_size_3342_; lean_object* v_k_3343_; lean_object* v_v_3344_; lean_object* v_r_3345_; lean_object* v___x_3346_; 
lean_dec(v_h__2_3330_);
v_size_3342_ = lean_ctor_get(v_x_3327_, 0);
lean_inc(v_size_3342_);
v_k_3343_ = lean_ctor_get(v_x_3327_, 1);
lean_inc(v_k_3343_);
v_v_3344_ = lean_ctor_get(v_x_3327_, 2);
lean_inc(v_v_3344_);
v_r_3345_ = lean_ctor_get(v_x_3327_, 4);
lean_inc(v_r_3345_);
lean_dec(v_x_3327_);
v___x_3346_ = lean_apply_5(v_h__1_3329_, v_size_3342_, v_k_3343_, v_v_3344_, v_r_3345_, lean_box(0));
return v___x_3346_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3348_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3349_ = lean_unsigned_to_nat(13u);
v___x_3350_ = lean_unsigned_to_nat(816u);
v___x_3351_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0));
v___x_3352_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3353_ = l_mkPanicMessageWithDecl(v___x_3352_, v___x_3351_, v___x_3350_, v___x_3349_, v___x_3348_);
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object* v_inst_3354_, lean_object* v_x_3355_){
_start:
{
if (lean_obj_tag(v_x_3355_) == 0)
{
lean_object* v_l_3356_; 
v_l_3356_ = lean_ctor_get(v_x_3355_, 3);
if (lean_obj_tag(v_l_3356_) == 0)
{
v_x_3355_ = v_l_3356_;
goto _start;
}
else
{
lean_object* v_k_3358_; lean_object* v_v_3359_; lean_object* v___x_3360_; 
v_k_3358_ = lean_ctor_get(v_x_3355_, 1);
v_v_3359_ = lean_ctor_get(v_x_3355_, 2);
lean_inc(v_v_3359_);
lean_inc(v_k_3358_);
v___x_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3360_, 0, v_k_3358_);
lean_ctor_set(v___x_3360_, 1, v_v_3359_);
return v___x_3360_;
}
}
else
{
lean_object* v___x_3361_; lean_object* v___x_3362_; 
v___x_3361_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1);
v___x_3362_ = l_panic___redArg(v_inst_3354_, v___x_3361_);
return v___x_3362_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_3363_, lean_object* v_x_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3363_, v_x_3364_);
lean_dec(v_x_3364_);
lean_dec_ref(v_inst_3363_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(lean_object* v_00_u03b1_3366_, lean_object* v_00_u03b2_3367_, lean_object* v_inst_3368_, lean_object* v_x_3369_){
_start:
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3368_, v_x_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_3371_, lean_object* v_00_u03b2_3372_, lean_object* v_inst_3373_, lean_object* v_x_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(v_00_u03b1_3371_, v_00_u03b2_3372_, v_inst_3373_, v_x_3374_);
lean_dec(v_x_3374_);
lean_dec_ref(v_inst_3373_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object* v_x_3376_, lean_object* v_x_3377_){
_start:
{
if (lean_obj_tag(v_x_3376_) == 0)
{
lean_object* v_l_3378_; 
v_l_3378_ = lean_ctor_get(v_x_3376_, 3);
if (lean_obj_tag(v_l_3378_) == 0)
{
v_x_3376_ = v_l_3378_;
goto _start;
}
else
{
lean_object* v_k_3380_; lean_object* v_v_3381_; lean_object* v___x_3382_; 
v_k_3380_ = lean_ctor_get(v_x_3376_, 1);
v_v_3381_ = lean_ctor_get(v_x_3376_, 2);
lean_inc(v_v_3381_);
lean_inc(v_k_3380_);
v___x_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3382_, 0, v_k_3380_);
lean_ctor_set(v___x_3382_, 1, v_v_3381_);
return v___x_3382_;
}
}
else
{
lean_inc_ref(v_x_3377_);
return v_x_3377_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg___boxed(lean_object* v_x_3383_, lean_object* v_x_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3383_, v_x_3384_);
lean_dec_ref(v_x_3384_);
lean_dec(v_x_3383_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD(lean_object* v_00_u03b1_3386_, lean_object* v_00_u03b2_3387_, lean_object* v_x_3388_, lean_object* v_x_3389_){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3388_, v_x_3389_);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___boxed(lean_object* v_00_u03b1_3391_, lean_object* v_00_u03b2_3392_, lean_object* v_x_3393_, lean_object* v_x_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD(v_00_u03b1_3391_, v_00_u03b2_3392_, v_x_3393_, v_x_3394_);
lean_dec_ref(v_x_3394_);
lean_dec(v_x_3393_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_3396_, lean_object* v_x_3397_, lean_object* v_h__1_3398_, lean_object* v_h__2_3399_, lean_object* v_h__3_3400_){
_start:
{
if (lean_obj_tag(v_x_3396_) == 0)
{
lean_object* v_l_3401_; 
lean_dec(v_h__1_3398_);
v_l_3401_ = lean_ctor_get(v_x_3396_, 3);
if (lean_obj_tag(v_l_3401_) == 0)
{
lean_object* v_size_3402_; lean_object* v_k_3403_; lean_object* v_v_3404_; lean_object* v_r_3405_; lean_object* v_size_3406_; lean_object* v_k_3407_; lean_object* v_v_3408_; lean_object* v_l_3409_; lean_object* v_r_3410_; lean_object* v___x_3411_; 
lean_inc_ref(v_l_3401_);
lean_dec(v_h__2_3399_);
v_size_3402_ = lean_ctor_get(v_x_3396_, 0);
lean_inc(v_size_3402_);
v_k_3403_ = lean_ctor_get(v_x_3396_, 1);
lean_inc(v_k_3403_);
v_v_3404_ = lean_ctor_get(v_x_3396_, 2);
lean_inc(v_v_3404_);
v_r_3405_ = lean_ctor_get(v_x_3396_, 4);
lean_inc(v_r_3405_);
lean_dec_ref_known(v_x_3396_, 5);
v_size_3406_ = lean_ctor_get(v_l_3401_, 0);
lean_inc(v_size_3406_);
v_k_3407_ = lean_ctor_get(v_l_3401_, 1);
lean_inc(v_k_3407_);
v_v_3408_ = lean_ctor_get(v_l_3401_, 2);
lean_inc(v_v_3408_);
v_l_3409_ = lean_ctor_get(v_l_3401_, 3);
lean_inc(v_l_3409_);
v_r_3410_ = lean_ctor_get(v_l_3401_, 4);
lean_inc(v_r_3410_);
lean_dec_ref_known(v_l_3401_, 5);
v___x_3411_ = lean_apply_10(v_h__3_3400_, v_size_3402_, v_k_3403_, v_v_3404_, v_size_3406_, v_k_3407_, v_v_3408_, v_l_3409_, v_r_3410_, v_r_3405_, v_x_3397_);
return v___x_3411_;
}
else
{
lean_object* v_size_3412_; lean_object* v_k_3413_; lean_object* v_v_3414_; lean_object* v_r_3415_; lean_object* v___x_3416_; 
lean_dec(v_h__3_3400_);
v_size_3412_ = lean_ctor_get(v_x_3396_, 0);
lean_inc(v_size_3412_);
v_k_3413_ = lean_ctor_get(v_x_3396_, 1);
lean_inc(v_k_3413_);
v_v_3414_ = lean_ctor_get(v_x_3396_, 2);
lean_inc(v_v_3414_);
v_r_3415_ = lean_ctor_get(v_x_3396_, 4);
lean_inc(v_r_3415_);
lean_dec_ref_known(v_x_3396_, 5);
v___x_3416_ = lean_apply_5(v_h__2_3399_, v_size_3412_, v_k_3413_, v_v_3414_, v_r_3415_, v_x_3397_);
return v___x_3416_;
}
}
else
{
lean_object* v___x_3417_; 
lean_dec(v_h__3_3400_);
lean_dec(v_h__2_3399_);
v___x_3417_ = lean_apply_1(v_h__1_3398_, v_x_3397_);
return v___x_3417_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_3418_, lean_object* v_00_u03b2_3419_, lean_object* v_motive_3420_, lean_object* v_x_3421_, lean_object* v_x_3422_, lean_object* v_h__1_3423_, lean_object* v_h__2_3424_, lean_object* v_h__3_3425_){
_start:
{
if (lean_obj_tag(v_x_3421_) == 0)
{
lean_object* v_l_3426_; 
lean_dec(v_h__1_3423_);
v_l_3426_ = lean_ctor_get(v_x_3421_, 3);
if (lean_obj_tag(v_l_3426_) == 0)
{
lean_object* v_size_3427_; lean_object* v_k_3428_; lean_object* v_v_3429_; lean_object* v_r_3430_; lean_object* v_size_3431_; lean_object* v_k_3432_; lean_object* v_v_3433_; lean_object* v_l_3434_; lean_object* v_r_3435_; lean_object* v___x_3436_; 
lean_inc_ref(v_l_3426_);
lean_dec(v_h__2_3424_);
v_size_3427_ = lean_ctor_get(v_x_3421_, 0);
lean_inc(v_size_3427_);
v_k_3428_ = lean_ctor_get(v_x_3421_, 1);
lean_inc(v_k_3428_);
v_v_3429_ = lean_ctor_get(v_x_3421_, 2);
lean_inc(v_v_3429_);
v_r_3430_ = lean_ctor_get(v_x_3421_, 4);
lean_inc(v_r_3430_);
lean_dec_ref_known(v_x_3421_, 5);
v_size_3431_ = lean_ctor_get(v_l_3426_, 0);
lean_inc(v_size_3431_);
v_k_3432_ = lean_ctor_get(v_l_3426_, 1);
lean_inc(v_k_3432_);
v_v_3433_ = lean_ctor_get(v_l_3426_, 2);
lean_inc(v_v_3433_);
v_l_3434_ = lean_ctor_get(v_l_3426_, 3);
lean_inc(v_l_3434_);
v_r_3435_ = lean_ctor_get(v_l_3426_, 4);
lean_inc(v_r_3435_);
lean_dec_ref_known(v_l_3426_, 5);
v___x_3436_ = lean_apply_10(v_h__3_3425_, v_size_3427_, v_k_3428_, v_v_3429_, v_size_3431_, v_k_3432_, v_v_3433_, v_l_3434_, v_r_3435_, v_r_3430_, v_x_3422_);
return v___x_3436_;
}
else
{
lean_object* v_size_3437_; lean_object* v_k_3438_; lean_object* v_v_3439_; lean_object* v_r_3440_; lean_object* v___x_3441_; 
lean_dec(v_h__3_3425_);
v_size_3437_ = lean_ctor_get(v_x_3421_, 0);
lean_inc(v_size_3437_);
v_k_3438_ = lean_ctor_get(v_x_3421_, 1);
lean_inc(v_k_3438_);
v_v_3439_ = lean_ctor_get(v_x_3421_, 2);
lean_inc(v_v_3439_);
v_r_3440_ = lean_ctor_get(v_x_3421_, 4);
lean_inc(v_r_3440_);
lean_dec_ref_known(v_x_3421_, 5);
v___x_3441_ = lean_apply_5(v_h__2_3424_, v_size_3437_, v_k_3438_, v_v_3439_, v_r_3440_, v_x_3422_);
return v___x_3441_;
}
}
else
{
lean_object* v___x_3442_; 
lean_dec(v_h__3_3425_);
lean_dec(v_h__2_3424_);
v___x_3442_ = lean_apply_1(v_h__1_3423_, v_x_3422_);
return v___x_3442_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object* v_x_3443_){
_start:
{
if (lean_obj_tag(v_x_3443_) == 0)
{
lean_object* v_r_3444_; 
v_r_3444_ = lean_ctor_get(v_x_3443_, 4);
if (lean_obj_tag(v_r_3444_) == 0)
{
v_x_3443_ = v_r_3444_;
goto _start;
}
else
{
lean_object* v_k_3446_; lean_object* v_v_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v_k_3446_ = lean_ctor_get(v_x_3443_, 1);
v_v_3447_ = lean_ctor_get(v_x_3443_, 2);
lean_inc(v_v_3447_);
lean_inc(v_k_3446_);
v___x_3448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3448_, 0, v_k_3446_);
lean_ctor_set(v___x_3448_, 1, v_v_3447_);
v___x_3449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3448_);
return v___x_3449_;
}
}
else
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_box(0);
return v___x_3450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg___boxed(lean_object* v_x_3451_){
_start:
{
lean_object* v_res_3452_; 
v_res_3452_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3451_);
lean_dec(v_x_3451_);
return v_res_3452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(lean_object* v_00_u03b1_3453_, lean_object* v_00_u03b2_3454_, lean_object* v_x_3455_){
_start:
{
lean_object* v___x_3456_; 
v___x_3456_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3455_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_3457_, lean_object* v_00_u03b2_3458_, lean_object* v_x_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(v_00_u03b1_3457_, v_00_u03b2_3458_, v_x_3459_);
lean_dec(v_x_3459_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3461_, lean_object* v_h__1_3462_, lean_object* v_h__2_3463_, lean_object* v_h__3_3464_){
_start:
{
if (lean_obj_tag(v_x_3461_) == 0)
{
lean_object* v_r_3465_; 
lean_dec(v_h__1_3462_);
v_r_3465_ = lean_ctor_get(v_x_3461_, 4);
if (lean_obj_tag(v_r_3465_) == 0)
{
lean_object* v_size_3466_; lean_object* v_k_3467_; lean_object* v_v_3468_; lean_object* v_l_3469_; lean_object* v_size_3470_; lean_object* v_k_3471_; lean_object* v_v_3472_; lean_object* v_l_3473_; lean_object* v_r_3474_; lean_object* v___x_3475_; 
lean_inc_ref(v_r_3465_);
lean_dec(v_h__2_3463_);
v_size_3466_ = lean_ctor_get(v_x_3461_, 0);
lean_inc(v_size_3466_);
v_k_3467_ = lean_ctor_get(v_x_3461_, 1);
lean_inc(v_k_3467_);
v_v_3468_ = lean_ctor_get(v_x_3461_, 2);
lean_inc(v_v_3468_);
v_l_3469_ = lean_ctor_get(v_x_3461_, 3);
lean_inc(v_l_3469_);
lean_dec_ref_known(v_x_3461_, 5);
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
lean_dec_ref_known(v_r_3465_, 5);
v___x_3475_ = lean_apply_9(v_h__3_3464_, v_size_3466_, v_k_3467_, v_v_3468_, v_l_3469_, v_size_3470_, v_k_3471_, v_v_3472_, v_l_3473_, v_r_3474_);
return v___x_3475_;
}
else
{
lean_object* v_size_3476_; lean_object* v_k_3477_; lean_object* v_v_3478_; lean_object* v_l_3479_; lean_object* v___x_3480_; 
lean_dec(v_h__3_3464_);
v_size_3476_ = lean_ctor_get(v_x_3461_, 0);
lean_inc(v_size_3476_);
v_k_3477_ = lean_ctor_get(v_x_3461_, 1);
lean_inc(v_k_3477_);
v_v_3478_ = lean_ctor_get(v_x_3461_, 2);
lean_inc(v_v_3478_);
v_l_3479_ = lean_ctor_get(v_x_3461_, 3);
lean_inc(v_l_3479_);
lean_dec_ref_known(v_x_3461_, 5);
v___x_3480_ = lean_apply_4(v_h__2_3463_, v_size_3476_, v_k_3477_, v_v_3478_, v_l_3479_);
return v___x_3480_;
}
}
else
{
lean_object* v___x_3481_; lean_object* v___x_3482_; 
lean_dec(v_h__3_3464_);
lean_dec(v_h__2_3463_);
v___x_3481_ = lean_box(0);
v___x_3482_ = lean_apply_1(v_h__1_3462_, v___x_3481_);
return v___x_3482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3483_, lean_object* v_00_u03b2_3484_, lean_object* v_motive_3485_, lean_object* v_x_3486_, lean_object* v_h__1_3487_, lean_object* v_h__2_3488_, lean_object* v_h__3_3489_){
_start:
{
if (lean_obj_tag(v_x_3486_) == 0)
{
lean_object* v_r_3490_; 
lean_dec(v_h__1_3487_);
v_r_3490_ = lean_ctor_get(v_x_3486_, 4);
if (lean_obj_tag(v_r_3490_) == 0)
{
lean_object* v_size_3491_; lean_object* v_k_3492_; lean_object* v_v_3493_; lean_object* v_l_3494_; lean_object* v_size_3495_; lean_object* v_k_3496_; lean_object* v_v_3497_; lean_object* v_l_3498_; lean_object* v_r_3499_; lean_object* v___x_3500_; 
lean_inc_ref(v_r_3490_);
lean_dec(v_h__2_3488_);
v_size_3491_ = lean_ctor_get(v_x_3486_, 0);
lean_inc(v_size_3491_);
v_k_3492_ = lean_ctor_get(v_x_3486_, 1);
lean_inc(v_k_3492_);
v_v_3493_ = lean_ctor_get(v_x_3486_, 2);
lean_inc(v_v_3493_);
v_l_3494_ = lean_ctor_get(v_x_3486_, 3);
lean_inc(v_l_3494_);
lean_dec_ref_known(v_x_3486_, 5);
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
lean_dec_ref_known(v_r_3490_, 5);
v___x_3500_ = lean_apply_9(v_h__3_3489_, v_size_3491_, v_k_3492_, v_v_3493_, v_l_3494_, v_size_3495_, v_k_3496_, v_v_3497_, v_l_3498_, v_r_3499_);
return v___x_3500_;
}
else
{
lean_object* v_size_3501_; lean_object* v_k_3502_; lean_object* v_v_3503_; lean_object* v_l_3504_; lean_object* v___x_3505_; 
lean_dec(v_h__3_3489_);
v_size_3501_ = lean_ctor_get(v_x_3486_, 0);
lean_inc(v_size_3501_);
v_k_3502_ = lean_ctor_get(v_x_3486_, 1);
lean_inc(v_k_3502_);
v_v_3503_ = lean_ctor_get(v_x_3486_, 2);
lean_inc(v_v_3503_);
v_l_3504_ = lean_ctor_get(v_x_3486_, 3);
lean_inc(v_l_3504_);
lean_dec_ref_known(v_x_3486_, 5);
v___x_3505_ = lean_apply_4(v_h__2_3488_, v_size_3501_, v_k_3502_, v_v_3503_, v_l_3504_);
return v___x_3505_;
}
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_dec(v_h__3_3489_);
lean_dec(v_h__2_3488_);
v___x_3506_ = lean_box(0);
v___x_3507_ = lean_apply_1(v_h__1_3487_, v___x_3506_);
return v___x_3507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object* v_x_3508_){
_start:
{
lean_object* v_r_3509_; 
v_r_3509_ = lean_ctor_get(v_x_3508_, 4);
if (lean_obj_tag(v_r_3509_) == 0)
{
v_x_3508_ = v_r_3509_;
goto _start;
}
else
{
lean_object* v_k_3511_; lean_object* v_v_3512_; lean_object* v___x_3513_; 
v_k_3511_ = lean_ctor_get(v_x_3508_, 1);
v_v_3512_ = lean_ctor_get(v_x_3508_, 2);
lean_inc(v_v_3512_);
lean_inc(v_k_3511_);
v___x_3513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3513_, 0, v_k_3511_);
lean_ctor_set(v___x_3513_, 1, v_v_3512_);
return v___x_3513_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg___boxed(lean_object* v_x_3514_){
_start:
{
lean_object* v_res_3515_; 
v_res_3515_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3514_);
lean_dec(v_x_3514_);
return v_res_3515_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry(lean_object* v_00_u03b1_3516_, lean_object* v_00_u03b2_3517_, lean_object* v_x_3518_, lean_object* v_x_3519_){
_start:
{
lean_object* v___x_3520_; 
v___x_3520_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3518_);
return v___x_3520_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___boxed(lean_object* v_00_u03b1_3521_, lean_object* v_00_u03b2_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry(v_00_u03b1_3521_, v_00_u03b2_3522_, v_x_3523_, v_x_3524_);
lean_dec(v_x_3523_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_3526_, lean_object* v_h__1_3527_, lean_object* v_h__2_3528_){
_start:
{
lean_object* v_r_3529_; 
v_r_3529_ = lean_ctor_get(v_x_3526_, 4);
if (lean_obj_tag(v_r_3529_) == 0)
{
lean_object* v_size_3530_; lean_object* v_k_3531_; lean_object* v_v_3532_; lean_object* v_l_3533_; lean_object* v_size_3534_; lean_object* v_k_3535_; lean_object* v_v_3536_; lean_object* v_l_3537_; lean_object* v_r_3538_; lean_object* v___x_3539_; 
lean_inc_ref(v_r_3529_);
lean_dec(v_h__1_3527_);
v_size_3530_ = lean_ctor_get(v_x_3526_, 0);
lean_inc(v_size_3530_);
v_k_3531_ = lean_ctor_get(v_x_3526_, 1);
lean_inc(v_k_3531_);
v_v_3532_ = lean_ctor_get(v_x_3526_, 2);
lean_inc(v_v_3532_);
v_l_3533_ = lean_ctor_get(v_x_3526_, 3);
lean_inc(v_l_3533_);
lean_dec(v_x_3526_);
v_size_3534_ = lean_ctor_get(v_r_3529_, 0);
lean_inc(v_size_3534_);
v_k_3535_ = lean_ctor_get(v_r_3529_, 1);
lean_inc(v_k_3535_);
v_v_3536_ = lean_ctor_get(v_r_3529_, 2);
lean_inc(v_v_3536_);
v_l_3537_ = lean_ctor_get(v_r_3529_, 3);
lean_inc(v_l_3537_);
v_r_3538_ = lean_ctor_get(v_r_3529_, 4);
lean_inc(v_r_3538_);
lean_dec_ref_known(v_r_3529_, 5);
v___x_3539_ = lean_apply_10(v_h__2_3528_, v_size_3530_, v_k_3531_, v_v_3532_, v_l_3533_, v_size_3534_, v_k_3535_, v_v_3536_, v_l_3537_, v_r_3538_, lean_box(0));
return v___x_3539_;
}
else
{
lean_object* v_size_3540_; lean_object* v_k_3541_; lean_object* v_v_3542_; lean_object* v_l_3543_; lean_object* v___x_3544_; 
lean_dec(v_h__2_3528_);
v_size_3540_ = lean_ctor_get(v_x_3526_, 0);
lean_inc(v_size_3540_);
v_k_3541_ = lean_ctor_get(v_x_3526_, 1);
lean_inc(v_k_3541_);
v_v_3542_ = lean_ctor_get(v_x_3526_, 2);
lean_inc(v_v_3542_);
v_l_3543_ = lean_ctor_get(v_x_3526_, 3);
lean_inc(v_l_3543_);
lean_dec(v_x_3526_);
v___x_3544_ = lean_apply_5(v_h__1_3527_, v_size_3540_, v_k_3541_, v_v_3542_, v_l_3543_, lean_box(0));
return v___x_3544_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_3545_, lean_object* v_00_u03b2_3546_, lean_object* v_motive_3547_, lean_object* v_x_3548_, lean_object* v_x_3549_, lean_object* v_h__1_3550_, lean_object* v_h__2_3551_){
_start:
{
lean_object* v_r_3552_; 
v_r_3552_ = lean_ctor_get(v_x_3548_, 4);
if (lean_obj_tag(v_r_3552_) == 0)
{
lean_object* v_size_3553_; lean_object* v_k_3554_; lean_object* v_v_3555_; lean_object* v_l_3556_; lean_object* v_size_3557_; lean_object* v_k_3558_; lean_object* v_v_3559_; lean_object* v_l_3560_; lean_object* v_r_3561_; lean_object* v___x_3562_; 
lean_inc_ref(v_r_3552_);
lean_dec(v_h__1_3550_);
v_size_3553_ = lean_ctor_get(v_x_3548_, 0);
lean_inc(v_size_3553_);
v_k_3554_ = lean_ctor_get(v_x_3548_, 1);
lean_inc(v_k_3554_);
v_v_3555_ = lean_ctor_get(v_x_3548_, 2);
lean_inc(v_v_3555_);
v_l_3556_ = lean_ctor_get(v_x_3548_, 3);
lean_inc(v_l_3556_);
lean_dec(v_x_3548_);
v_size_3557_ = lean_ctor_get(v_r_3552_, 0);
lean_inc(v_size_3557_);
v_k_3558_ = lean_ctor_get(v_r_3552_, 1);
lean_inc(v_k_3558_);
v_v_3559_ = lean_ctor_get(v_r_3552_, 2);
lean_inc(v_v_3559_);
v_l_3560_ = lean_ctor_get(v_r_3552_, 3);
lean_inc(v_l_3560_);
v_r_3561_ = lean_ctor_get(v_r_3552_, 4);
lean_inc(v_r_3561_);
lean_dec_ref_known(v_r_3552_, 5);
v___x_3562_ = lean_apply_10(v_h__2_3551_, v_size_3553_, v_k_3554_, v_v_3555_, v_l_3556_, v_size_3557_, v_k_3558_, v_v_3559_, v_l_3560_, v_r_3561_, lean_box(0));
return v___x_3562_;
}
else
{
lean_object* v_size_3563_; lean_object* v_k_3564_; lean_object* v_v_3565_; lean_object* v_l_3566_; lean_object* v___x_3567_; 
lean_dec(v_h__2_3551_);
v_size_3563_ = lean_ctor_get(v_x_3548_, 0);
lean_inc(v_size_3563_);
v_k_3564_ = lean_ctor_get(v_x_3548_, 1);
lean_inc(v_k_3564_);
v_v_3565_ = lean_ctor_get(v_x_3548_, 2);
lean_inc(v_v_3565_);
v_l_3566_ = lean_ctor_get(v_x_3548_, 3);
lean_inc(v_l_3566_);
lean_dec(v_x_3548_);
v___x_3567_ = lean_apply_5(v_h__1_3550_, v_size_3563_, v_k_3564_, v_v_3565_, v_l_3566_, lean_box(0));
return v___x_3567_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3569_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3570_ = lean_unsigned_to_nat(13u);
v___x_3571_ = lean_unsigned_to_nat(839u);
v___x_3572_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0));
v___x_3573_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3574_ = l_mkPanicMessageWithDecl(v___x_3573_, v___x_3572_, v___x_3571_, v___x_3570_, v___x_3569_);
return v___x_3574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object* v_inst_3575_, lean_object* v_x_3576_){
_start:
{
if (lean_obj_tag(v_x_3576_) == 0)
{
lean_object* v_r_3577_; 
v_r_3577_ = lean_ctor_get(v_x_3576_, 4);
if (lean_obj_tag(v_r_3577_) == 0)
{
v_x_3576_ = v_r_3577_;
goto _start;
}
else
{
lean_object* v_k_3579_; lean_object* v_v_3580_; lean_object* v___x_3581_; 
v_k_3579_ = lean_ctor_get(v_x_3576_, 1);
v_v_3580_ = lean_ctor_get(v_x_3576_, 2);
lean_inc(v_v_3580_);
lean_inc(v_k_3579_);
v___x_3581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3581_, 0, v_k_3579_);
lean_ctor_set(v___x_3581_, 1, v_v_3580_);
return v___x_3581_;
}
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3582_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1);
v___x_3583_ = l_panic___redArg(v_inst_3575_, v___x_3582_);
return v___x_3583_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_3584_, lean_object* v_x_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3584_, v_x_3585_);
lean_dec(v_x_3585_);
lean_dec_ref(v_inst_3584_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(lean_object* v_00_u03b1_3587_, lean_object* v_00_u03b2_3588_, lean_object* v_inst_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v___x_3591_; 
v___x_3591_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3589_, v_x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_3592_, lean_object* v_00_u03b2_3593_, lean_object* v_inst_3594_, lean_object* v_x_3595_){
_start:
{
lean_object* v_res_3596_; 
v_res_3596_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(v_00_u03b1_3592_, v_00_u03b2_3593_, v_inst_3594_, v_x_3595_);
lean_dec(v_x_3595_);
lean_dec_ref(v_inst_3594_);
return v_res_3596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object* v_x_3597_, lean_object* v_x_3598_){
_start:
{
if (lean_obj_tag(v_x_3597_) == 0)
{
lean_object* v_r_3599_; 
v_r_3599_ = lean_ctor_get(v_x_3597_, 4);
if (lean_obj_tag(v_r_3599_) == 0)
{
v_x_3597_ = v_r_3599_;
goto _start;
}
else
{
lean_object* v_k_3601_; lean_object* v_v_3602_; lean_object* v___x_3603_; 
v_k_3601_ = lean_ctor_get(v_x_3597_, 1);
v_v_3602_ = lean_ctor_get(v_x_3597_, 2);
lean_inc(v_v_3602_);
lean_inc(v_k_3601_);
v___x_3603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3603_, 0, v_k_3601_);
lean_ctor_set(v___x_3603_, 1, v_v_3602_);
return v___x_3603_;
}
}
else
{
lean_inc_ref(v_x_3598_);
return v_x_3598_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg___boxed(lean_object* v_x_3604_, lean_object* v_x_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3604_, v_x_3605_);
lean_dec_ref(v_x_3605_);
lean_dec(v_x_3604_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(lean_object* v_00_u03b1_3607_, lean_object* v_00_u03b2_3608_, lean_object* v_x_3609_, lean_object* v_x_3610_){
_start:
{
lean_object* v___x_3611_; 
v___x_3611_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3609_, v_x_3610_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___boxed(lean_object* v_00_u03b1_3612_, lean_object* v_00_u03b2_3613_, lean_object* v_x_3614_, lean_object* v_x_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(v_00_u03b1_3612_, v_00_u03b2_3613_, v_x_3614_, v_x_3615_);
lean_dec_ref(v_x_3615_);
lean_dec(v_x_3614_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_3617_, lean_object* v_x_3618_, lean_object* v_h__1_3619_, lean_object* v_h__2_3620_, lean_object* v_h__3_3621_){
_start:
{
if (lean_obj_tag(v_x_3617_) == 0)
{
lean_object* v_r_3622_; 
lean_dec(v_h__1_3619_);
v_r_3622_ = lean_ctor_get(v_x_3617_, 4);
if (lean_obj_tag(v_r_3622_) == 0)
{
lean_object* v_size_3623_; lean_object* v_k_3624_; lean_object* v_v_3625_; lean_object* v_l_3626_; lean_object* v_size_3627_; lean_object* v_k_3628_; lean_object* v_v_3629_; lean_object* v_l_3630_; lean_object* v_r_3631_; lean_object* v___x_3632_; 
lean_inc_ref(v_r_3622_);
lean_dec(v_h__2_3620_);
v_size_3623_ = lean_ctor_get(v_x_3617_, 0);
lean_inc(v_size_3623_);
v_k_3624_ = lean_ctor_get(v_x_3617_, 1);
lean_inc(v_k_3624_);
v_v_3625_ = lean_ctor_get(v_x_3617_, 2);
lean_inc(v_v_3625_);
v_l_3626_ = lean_ctor_get(v_x_3617_, 3);
lean_inc(v_l_3626_);
lean_dec_ref_known(v_x_3617_, 5);
v_size_3627_ = lean_ctor_get(v_r_3622_, 0);
lean_inc(v_size_3627_);
v_k_3628_ = lean_ctor_get(v_r_3622_, 1);
lean_inc(v_k_3628_);
v_v_3629_ = lean_ctor_get(v_r_3622_, 2);
lean_inc(v_v_3629_);
v_l_3630_ = lean_ctor_get(v_r_3622_, 3);
lean_inc(v_l_3630_);
v_r_3631_ = lean_ctor_get(v_r_3622_, 4);
lean_inc(v_r_3631_);
lean_dec_ref_known(v_r_3622_, 5);
v___x_3632_ = lean_apply_10(v_h__3_3621_, v_size_3623_, v_k_3624_, v_v_3625_, v_l_3626_, v_size_3627_, v_k_3628_, v_v_3629_, v_l_3630_, v_r_3631_, v_x_3618_);
return v___x_3632_;
}
else
{
lean_object* v_size_3633_; lean_object* v_k_3634_; lean_object* v_v_3635_; lean_object* v_l_3636_; lean_object* v___x_3637_; 
lean_dec(v_h__3_3621_);
v_size_3633_ = lean_ctor_get(v_x_3617_, 0);
lean_inc(v_size_3633_);
v_k_3634_ = lean_ctor_get(v_x_3617_, 1);
lean_inc(v_k_3634_);
v_v_3635_ = lean_ctor_get(v_x_3617_, 2);
lean_inc(v_v_3635_);
v_l_3636_ = lean_ctor_get(v_x_3617_, 3);
lean_inc(v_l_3636_);
lean_dec_ref_known(v_x_3617_, 5);
v___x_3637_ = lean_apply_5(v_h__2_3620_, v_size_3633_, v_k_3634_, v_v_3635_, v_l_3636_, v_x_3618_);
return v___x_3637_;
}
}
else
{
lean_object* v___x_3638_; 
lean_dec(v_h__3_3621_);
lean_dec(v_h__2_3620_);
v___x_3638_ = lean_apply_1(v_h__1_3619_, v_x_3618_);
return v___x_3638_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_3639_, lean_object* v_00_u03b2_3640_, lean_object* v_motive_3641_, lean_object* v_x_3642_, lean_object* v_x_3643_, lean_object* v_h__1_3644_, lean_object* v_h__2_3645_, lean_object* v_h__3_3646_){
_start:
{
if (lean_obj_tag(v_x_3642_) == 0)
{
lean_object* v_r_3647_; 
lean_dec(v_h__1_3644_);
v_r_3647_ = lean_ctor_get(v_x_3642_, 4);
if (lean_obj_tag(v_r_3647_) == 0)
{
lean_object* v_size_3648_; lean_object* v_k_3649_; lean_object* v_v_3650_; lean_object* v_l_3651_; lean_object* v_size_3652_; lean_object* v_k_3653_; lean_object* v_v_3654_; lean_object* v_l_3655_; lean_object* v_r_3656_; lean_object* v___x_3657_; 
lean_inc_ref(v_r_3647_);
lean_dec(v_h__2_3645_);
v_size_3648_ = lean_ctor_get(v_x_3642_, 0);
lean_inc(v_size_3648_);
v_k_3649_ = lean_ctor_get(v_x_3642_, 1);
lean_inc(v_k_3649_);
v_v_3650_ = lean_ctor_get(v_x_3642_, 2);
lean_inc(v_v_3650_);
v_l_3651_ = lean_ctor_get(v_x_3642_, 3);
lean_inc(v_l_3651_);
lean_dec_ref_known(v_x_3642_, 5);
v_size_3652_ = lean_ctor_get(v_r_3647_, 0);
lean_inc(v_size_3652_);
v_k_3653_ = lean_ctor_get(v_r_3647_, 1);
lean_inc(v_k_3653_);
v_v_3654_ = lean_ctor_get(v_r_3647_, 2);
lean_inc(v_v_3654_);
v_l_3655_ = lean_ctor_get(v_r_3647_, 3);
lean_inc(v_l_3655_);
v_r_3656_ = lean_ctor_get(v_r_3647_, 4);
lean_inc(v_r_3656_);
lean_dec_ref_known(v_r_3647_, 5);
v___x_3657_ = lean_apply_10(v_h__3_3646_, v_size_3648_, v_k_3649_, v_v_3650_, v_l_3651_, v_size_3652_, v_k_3653_, v_v_3654_, v_l_3655_, v_r_3656_, v_x_3643_);
return v___x_3657_;
}
else
{
lean_object* v_size_3658_; lean_object* v_k_3659_; lean_object* v_v_3660_; lean_object* v_l_3661_; lean_object* v___x_3662_; 
lean_dec(v_h__3_3646_);
v_size_3658_ = lean_ctor_get(v_x_3642_, 0);
lean_inc(v_size_3658_);
v_k_3659_ = lean_ctor_get(v_x_3642_, 1);
lean_inc(v_k_3659_);
v_v_3660_ = lean_ctor_get(v_x_3642_, 2);
lean_inc(v_v_3660_);
v_l_3661_ = lean_ctor_get(v_x_3642_, 3);
lean_inc(v_l_3661_);
lean_dec_ref_known(v_x_3642_, 5);
v___x_3662_ = lean_apply_5(v_h__2_3645_, v_size_3658_, v_k_3659_, v_v_3660_, v_l_3661_, v_x_3643_);
return v___x_3662_;
}
}
else
{
lean_object* v___x_3663_; 
lean_dec(v_h__3_3646_);
lean_dec(v_h__2_3645_);
v___x_3663_ = lean_apply_1(v_h__1_3644_, v_x_3643_);
return v___x_3663_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object* v_x_3664_, lean_object* v_x_3665_){
_start:
{
lean_object* v_k_3666_; lean_object* v_v_3667_; lean_object* v_l_3668_; lean_object* v_r_3669_; lean_object* v___y_3671_; lean_object* v___y_3677_; 
v_k_3666_ = lean_ctor_get(v_x_3664_, 1);
v_v_3667_ = lean_ctor_get(v_x_3664_, 2);
v_l_3668_ = lean_ctor_get(v_x_3664_, 3);
v_r_3669_ = lean_ctor_get(v_x_3664_, 4);
if (lean_obj_tag(v_l_3668_) == 0)
{
lean_object* v_size_3684_; 
v_size_3684_ = lean_ctor_get(v_l_3668_, 0);
v___y_3677_ = v_size_3684_;
goto v___jp_3676_;
}
else
{
lean_object* v___x_3685_; 
v___x_3685_ = lean_unsigned_to_nat(0u);
v___y_3677_ = v___x_3685_;
goto v___jp_3676_;
}
v___jp_3670_:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; 
v___x_3672_ = lean_nat_sub(v_x_3665_, v___y_3671_);
lean_dec(v_x_3665_);
v___x_3673_ = lean_unsigned_to_nat(1u);
v___x_3674_ = lean_nat_sub(v___x_3672_, v___x_3673_);
lean_dec(v___x_3672_);
v_x_3664_ = v_r_3669_;
v_x_3665_ = v___x_3674_;
goto _start;
}
v___jp_3676_:
{
uint8_t v___x_3678_; 
v___x_3678_ = lean_nat_dec_lt(v_x_3665_, v___y_3677_);
if (v___x_3678_ == 0)
{
uint8_t v___x_3679_; 
v___x_3679_ = lean_nat_dec_eq(v_x_3665_, v___y_3677_);
if (v___x_3679_ == 0)
{
if (lean_obj_tag(v_l_3668_) == 0)
{
lean_object* v_size_3680_; 
v_size_3680_ = lean_ctor_get(v_l_3668_, 0);
v___y_3671_ = v_size_3680_;
goto v___jp_3670_;
}
else
{
lean_object* v___x_3681_; 
v___x_3681_ = lean_unsigned_to_nat(0u);
v___y_3671_ = v___x_3681_;
goto v___jp_3670_;
}
}
else
{
lean_object* v___x_3682_; 
lean_dec(v_x_3665_);
lean_inc(v_v_3667_);
lean_inc(v_k_3666_);
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v_k_3666_);
lean_ctor_set(v___x_3682_, 1, v_v_3667_);
return v___x_3682_;
}
}
else
{
v_x_3664_ = v_l_3668_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg___boxed(lean_object* v_x_3686_, lean_object* v_x_3687_){
_start:
{
lean_object* v_res_3688_; 
v_res_3688_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3686_, v_x_3687_);
lean_dec(v_x_3686_);
return v_res_3688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_object* v_00_u03b1_3689_, lean_object* v_00_u03b2_3690_, lean_object* v_x_3691_, lean_object* v_x_3692_, lean_object* v_x_3693_, lean_object* v_x_3694_){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3691_, v_x_3693_);
return v___x_3695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_3696_, lean_object* v_00_u03b2_3697_, lean_object* v_x_3698_, lean_object* v_x_3699_, lean_object* v_x_3700_, lean_object* v_x_3701_){
_start:
{
lean_object* v_res_3702_; 
v_res_3702_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(v_00_u03b1_3696_, v_00_u03b2_3697_, v_x_3698_, v_x_3699_, v_x_3700_, v_x_3701_);
lean_dec(v_x_3698_);
return v_res_3702_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object* v_x_3703_, lean_object* v_x_3704_){
_start:
{
if (lean_obj_tag(v_x_3703_) == 0)
{
lean_object* v_k_3705_; lean_object* v_v_3706_; lean_object* v_l_3707_; lean_object* v_r_3708_; lean_object* v___y_3710_; lean_object* v___y_3716_; 
v_k_3705_ = lean_ctor_get(v_x_3703_, 1);
v_v_3706_ = lean_ctor_get(v_x_3703_, 2);
v_l_3707_ = lean_ctor_get(v_x_3703_, 3);
v_r_3708_ = lean_ctor_get(v_x_3703_, 4);
if (lean_obj_tag(v_l_3707_) == 0)
{
lean_object* v_size_3724_; 
v_size_3724_ = lean_ctor_get(v_l_3707_, 0);
v___y_3716_ = v_size_3724_;
goto v___jp_3715_;
}
else
{
lean_object* v___x_3725_; 
v___x_3725_ = lean_unsigned_to_nat(0u);
v___y_3716_ = v___x_3725_;
goto v___jp_3715_;
}
v___jp_3709_:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3711_ = lean_nat_sub(v_x_3704_, v___y_3710_);
lean_dec(v_x_3704_);
v___x_3712_ = lean_unsigned_to_nat(1u);
v___x_3713_ = lean_nat_sub(v___x_3711_, v___x_3712_);
lean_dec(v___x_3711_);
v_x_3703_ = v_r_3708_;
v_x_3704_ = v___x_3713_;
goto _start;
}
v___jp_3715_:
{
uint8_t v___x_3717_; 
v___x_3717_ = lean_nat_dec_lt(v_x_3704_, v___y_3716_);
if (v___x_3717_ == 0)
{
uint8_t v___x_3718_; 
v___x_3718_ = lean_nat_dec_eq(v_x_3704_, v___y_3716_);
if (v___x_3718_ == 0)
{
if (lean_obj_tag(v_l_3707_) == 0)
{
lean_object* v_size_3719_; 
v_size_3719_ = lean_ctor_get(v_l_3707_, 0);
v___y_3710_ = v_size_3719_;
goto v___jp_3709_;
}
else
{
lean_object* v___x_3720_; 
v___x_3720_ = lean_unsigned_to_nat(0u);
v___y_3710_ = v___x_3720_;
goto v___jp_3709_;
}
}
else
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
lean_dec(v_x_3704_);
lean_inc(v_v_3706_);
lean_inc(v_k_3705_);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v_k_3705_);
lean_ctor_set(v___x_3721_, 1, v_v_3706_);
v___x_3722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
return v___x_3722_;
}
}
else
{
v_x_3703_ = v_l_3707_;
goto _start;
}
}
}
else
{
lean_object* v___x_3726_; 
lean_dec(v_x_3704_);
v___x_3726_ = lean_box(0);
return v___x_3726_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_3727_, lean_object* v_x_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3727_, v_x_3728_);
lean_dec(v_x_3727_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_3730_, lean_object* v_00_u03b2_3731_, lean_object* v_x_3732_, lean_object* v_x_3733_){
_start:
{
lean_object* v___x_3734_; 
v___x_3734_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3732_, v_x_3733_);
return v___x_3734_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_3735_, lean_object* v_00_u03b2_3736_, lean_object* v_x_3737_, lean_object* v_x_3738_){
_start:
{
lean_object* v_res_3739_; 
v_res_3739_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(v_00_u03b1_3735_, v_00_u03b2_3736_, v_x_3737_, v_x_3738_);
lean_dec(v_x_3737_);
return v_res_3739_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
v___x_3741_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_3742_ = lean_unsigned_to_nat(16u);
v___x_3743_ = lean_unsigned_to_nat(870u);
v___x_3744_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0));
v___x_3745_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3746_ = l_mkPanicMessageWithDecl(v___x_3745_, v___x_3744_, v___x_3743_, v___x_3742_, v___x_3741_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object* v_inst_3747_, lean_object* v_x_3748_, lean_object* v_x_3749_){
_start:
{
if (lean_obj_tag(v_x_3748_) == 0)
{
lean_object* v_k_3750_; lean_object* v_v_3751_; lean_object* v_l_3752_; lean_object* v_r_3753_; lean_object* v___y_3755_; lean_object* v___y_3761_; 
v_k_3750_ = lean_ctor_get(v_x_3748_, 1);
v_v_3751_ = lean_ctor_get(v_x_3748_, 2);
v_l_3752_ = lean_ctor_get(v_x_3748_, 3);
v_r_3753_ = lean_ctor_get(v_x_3748_, 4);
if (lean_obj_tag(v_l_3752_) == 0)
{
lean_object* v_size_3768_; 
v_size_3768_ = lean_ctor_get(v_l_3752_, 0);
v___y_3761_ = v_size_3768_;
goto v___jp_3760_;
}
else
{
lean_object* v___x_3769_; 
v___x_3769_ = lean_unsigned_to_nat(0u);
v___y_3761_ = v___x_3769_;
goto v___jp_3760_;
}
v___jp_3754_:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3756_ = lean_nat_sub(v_x_3749_, v___y_3755_);
lean_dec(v_x_3749_);
v___x_3757_ = lean_unsigned_to_nat(1u);
v___x_3758_ = lean_nat_sub(v___x_3756_, v___x_3757_);
lean_dec(v___x_3756_);
v_x_3748_ = v_r_3753_;
v_x_3749_ = v___x_3758_;
goto _start;
}
v___jp_3760_:
{
uint8_t v___x_3762_; 
v___x_3762_ = lean_nat_dec_lt(v_x_3749_, v___y_3761_);
if (v___x_3762_ == 0)
{
uint8_t v___x_3763_; 
v___x_3763_ = lean_nat_dec_eq(v_x_3749_, v___y_3761_);
if (v___x_3763_ == 0)
{
if (lean_obj_tag(v_l_3752_) == 0)
{
lean_object* v_size_3764_; 
v_size_3764_ = lean_ctor_get(v_l_3752_, 0);
v___y_3755_ = v_size_3764_;
goto v___jp_3754_;
}
else
{
lean_object* v___x_3765_; 
v___x_3765_ = lean_unsigned_to_nat(0u);
v___y_3755_ = v___x_3765_;
goto v___jp_3754_;
}
}
else
{
lean_object* v___x_3766_; 
lean_dec(v_x_3749_);
lean_inc(v_v_3751_);
lean_inc(v_k_3750_);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v_k_3750_);
lean_ctor_set(v___x_3766_, 1, v_v_3751_);
return v___x_3766_;
}
}
else
{
v_x_3748_ = v_l_3752_;
goto _start;
}
}
}
else
{
lean_object* v___x_3770_; lean_object* v___x_3771_; 
lean_dec(v_x_3749_);
v___x_3770_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1);
v___x_3771_ = l_panic___redArg(v_inst_3747_, v___x_3770_);
return v___x_3771_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_3772_, lean_object* v_x_3773_, lean_object* v_x_3774_){
_start:
{
lean_object* v_res_3775_; 
v_res_3775_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3772_, v_x_3773_, v_x_3774_);
lean_dec(v_x_3773_);
lean_dec_ref(v_inst_3772_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(lean_object* v_00_u03b1_3776_, lean_object* v_00_u03b2_3777_, lean_object* v_inst_3778_, lean_object* v_x_3779_, lean_object* v_x_3780_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3778_, v_x_3779_, v_x_3780_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_3782_, lean_object* v_00_u03b2_3783_, lean_object* v_inst_3784_, lean_object* v_x_3785_, lean_object* v_x_3786_){
_start:
{
lean_object* v_res_3787_; 
v_res_3787_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(v_00_u03b1_3782_, v_00_u03b2_3783_, v_inst_3784_, v_x_3785_, v_x_3786_);
lean_dec(v_x_3785_);
lean_dec_ref(v_inst_3784_);
return v_res_3787_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object* v_x_3788_, lean_object* v_x_3789_, lean_object* v_x_3790_){
_start:
{
if (lean_obj_tag(v_x_3788_) == 0)
{
lean_object* v_k_3791_; lean_object* v_v_3792_; lean_object* v_l_3793_; lean_object* v_r_3794_; lean_object* v___y_3796_; lean_object* v___y_3802_; 
v_k_3791_ = lean_ctor_get(v_x_3788_, 1);
v_v_3792_ = lean_ctor_get(v_x_3788_, 2);
v_l_3793_ = lean_ctor_get(v_x_3788_, 3);
v_r_3794_ = lean_ctor_get(v_x_3788_, 4);
if (lean_obj_tag(v_l_3793_) == 0)
{
lean_object* v_size_3809_; 
v_size_3809_ = lean_ctor_get(v_l_3793_, 0);
v___y_3802_ = v_size_3809_;
goto v___jp_3801_;
}
else
{
lean_object* v___x_3810_; 
v___x_3810_ = lean_unsigned_to_nat(0u);
v___y_3802_ = v___x_3810_;
goto v___jp_3801_;
}
v___jp_3795_:
{
lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3797_ = lean_nat_sub(v_x_3789_, v___y_3796_);
lean_dec(v_x_3789_);
v___x_3798_ = lean_unsigned_to_nat(1u);
v___x_3799_ = lean_nat_sub(v___x_3797_, v___x_3798_);
lean_dec(v___x_3797_);
v_x_3788_ = v_r_3794_;
v_x_3789_ = v___x_3799_;
goto _start;
}
v___jp_3801_:
{
uint8_t v___x_3803_; 
v___x_3803_ = lean_nat_dec_lt(v_x_3789_, v___y_3802_);
if (v___x_3803_ == 0)
{
uint8_t v___x_3804_; 
v___x_3804_ = lean_nat_dec_eq(v_x_3789_, v___y_3802_);
if (v___x_3804_ == 0)
{
if (lean_obj_tag(v_l_3793_) == 0)
{
lean_object* v_size_3805_; 
v_size_3805_ = lean_ctor_get(v_l_3793_, 0);
v___y_3796_ = v_size_3805_;
goto v___jp_3795_;
}
else
{
lean_object* v___x_3806_; 
v___x_3806_ = lean_unsigned_to_nat(0u);
v___y_3796_ = v___x_3806_;
goto v___jp_3795_;
}
}
else
{
lean_object* v___x_3807_; 
lean_dec(v_x_3789_);
lean_inc(v_v_3792_);
lean_inc(v_k_3791_);
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v_k_3791_);
lean_ctor_set(v___x_3807_, 1, v_v_3792_);
return v___x_3807_;
}
}
else
{
v_x_3788_ = v_l_3793_;
goto _start;
}
}
}
else
{
lean_dec(v_x_3789_);
lean_inc_ref(v_x_3790_);
return v_x_3790_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg___boxed(lean_object* v_x_3811_, lean_object* v_x_3812_, lean_object* v_x_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3811_, v_x_3812_, v_x_3813_);
lean_dec_ref(v_x_3813_);
lean_dec(v_x_3811_);
return v_res_3814_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(lean_object* v_00_u03b1_3815_, lean_object* v_00_u03b2_3816_, lean_object* v_x_3817_, lean_object* v_x_3818_, lean_object* v_x_3819_){
_start:
{
lean_object* v___x_3820_; 
v___x_3820_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3817_, v_x_3818_, v_x_3819_);
return v___x_3820_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_3821_, lean_object* v_00_u03b2_3822_, lean_object* v_x_3823_, lean_object* v_x_3824_, lean_object* v_x_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(v_00_u03b1_3821_, v_00_u03b2_3822_, v_x_3823_, v_x_3824_, v_x_3825_);
lean_dec_ref(v_x_3825_);
lean_dec(v_x_3823_);
return v_res_3826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object* v_inst_3827_, lean_object* v_k_3828_, lean_object* v_best_3829_, lean_object* v_a_3830_){
_start:
{
if (lean_obj_tag(v_a_3830_) == 0)
{
lean_object* v_k_3831_; lean_object* v_v_3832_; lean_object* v_l_3833_; lean_object* v_r_3834_; lean_object* v___x_3835_; uint8_t v___x_3836_; 
v_k_3831_ = lean_ctor_get(v_a_3830_, 1);
lean_inc_n(v_k_3831_, 2);
v_v_3832_ = lean_ctor_get(v_a_3830_, 2);
lean_inc(v_v_3832_);
v_l_3833_ = lean_ctor_get(v_a_3830_, 3);
lean_inc(v_l_3833_);
v_r_3834_ = lean_ctor_get(v_a_3830_, 4);
lean_inc(v_r_3834_);
lean_dec_ref_known(v_a_3830_, 5);
lean_inc_ref(v_inst_3827_);
lean_inc(v_k_3828_);
v___x_3835_ = lean_apply_2(v_inst_3827_, v_k_3828_, v_k_3831_);
v___x_3836_ = lean_unbox(v___x_3835_);
switch(v___x_3836_)
{
case 0:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; 
lean_dec(v_r_3834_);
lean_dec(v_best_3829_);
v___x_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3837_, 0, v_k_3831_);
lean_ctor_set(v___x_3837_, 1, v_v_3832_);
v___x_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3838_, 0, v___x_3837_);
v_best_3829_ = v___x_3838_;
v_a_3830_ = v_l_3833_;
goto _start;
}
case 1:
{
lean_object* v___x_3840_; lean_object* v___x_3841_; 
lean_dec(v_r_3834_);
lean_dec(v_l_3833_);
lean_dec(v_best_3829_);
lean_dec(v_k_3828_);
lean_dec_ref(v_inst_3827_);
v___x_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3840_, 0, v_k_3831_);
lean_ctor_set(v___x_3840_, 1, v_v_3832_);
v___x_3841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3840_);
return v___x_3841_;
}
default: 
{
lean_dec(v_l_3833_);
lean_dec(v_v_3832_);
lean_dec(v_k_3831_);
v_a_3830_ = v_r_3834_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3828_);
lean_dec_ref(v_inst_3827_);
return v_best_3829_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(lean_object* v_00_u03b1_3843_, lean_object* v_00_u03b2_3844_, lean_object* v_inst_3845_, lean_object* v_k_3846_, lean_object* v_best_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v___x_3849_; 
v___x_3849_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3845_, v_k_3846_, v_best_3847_, v_a_3848_);
return v___x_3849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___redArg(lean_object* v_inst_3850_, lean_object* v_k_3851_, lean_object* v_a_3852_){
_start:
{
lean_object* v___x_3853_; lean_object* v___x_3854_; 
v___x_3853_ = lean_box(0);
v___x_3854_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3850_, v_k_3851_, v___x_3853_, v_a_3852_);
return v___x_3854_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(lean_object* v_00_u03b1_3855_, lean_object* v_00_u03b2_3856_, lean_object* v_inst_3857_, lean_object* v_k_3858_, lean_object* v_a_3859_){
_start:
{
lean_object* v___x_3860_; lean_object* v___x_3861_; 
v___x_3860_ = lean_box(0);
v___x_3861_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3857_, v_k_3858_, v___x_3860_, v_a_3859_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object* v_inst_3862_, lean_object* v_k_3863_, lean_object* v_best_3864_, lean_object* v_a_3865_){
_start:
{
if (lean_obj_tag(v_a_3865_) == 0)
{
lean_object* v_k_3866_; lean_object* v_v_3867_; lean_object* v_l_3868_; lean_object* v_r_3869_; lean_object* v___x_3870_; uint8_t v___x_3871_; 
v_k_3866_ = lean_ctor_get(v_a_3865_, 1);
lean_inc_n(v_k_3866_, 2);
v_v_3867_ = lean_ctor_get(v_a_3865_, 2);
lean_inc(v_v_3867_);
v_l_3868_ = lean_ctor_get(v_a_3865_, 3);
lean_inc(v_l_3868_);
v_r_3869_ = lean_ctor_get(v_a_3865_, 4);
lean_inc(v_r_3869_);
lean_dec_ref_known(v_a_3865_, 5);
lean_inc_ref(v_inst_3862_);
lean_inc(v_k_3863_);
v___x_3870_ = lean_apply_2(v_inst_3862_, v_k_3863_, v_k_3866_);
v___x_3871_ = lean_unbox(v___x_3870_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; lean_object* v___x_3873_; 
lean_dec(v_r_3869_);
lean_dec(v_best_3864_);
v___x_3872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3872_, 0, v_k_3866_);
lean_ctor_set(v___x_3872_, 1, v_v_3867_);
v___x_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3872_);
v_best_3864_ = v___x_3873_;
v_a_3865_ = v_l_3868_;
goto _start;
}
else
{
lean_dec(v_l_3868_);
lean_dec(v_v_3867_);
lean_dec(v_k_3866_);
v_a_3865_ = v_r_3869_;
goto _start;
}
}
else
{
lean_dec(v_k_3863_);
lean_dec_ref(v_inst_3862_);
return v_best_3864_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(lean_object* v_00_u03b1_3876_, lean_object* v_00_u03b2_3877_, lean_object* v_inst_3878_, lean_object* v_k_3879_, lean_object* v_best_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v___x_3882_; 
v___x_3882_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3878_, v_k_3879_, v_best_3880_, v_a_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___redArg(lean_object* v_inst_3883_, lean_object* v_k_3884_, lean_object* v_a_3885_){
_start:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; 
v___x_3886_ = lean_box(0);
v___x_3887_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3883_, v_k_3884_, v___x_3886_, v_a_3885_);
return v___x_3887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(lean_object* v_00_u03b1_3888_, lean_object* v_00_u03b2_3889_, lean_object* v_inst_3890_, lean_object* v_k_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3893_ = lean_box(0);
v___x_3894_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3890_, v_k_3891_, v___x_3893_, v_a_3892_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object* v_inst_3895_, lean_object* v_k_3896_, lean_object* v_best_3897_, lean_object* v_a_3898_){
_start:
{
if (lean_obj_tag(v_a_3898_) == 0)
{
lean_object* v_k_3899_; lean_object* v_v_3900_; lean_object* v_l_3901_; lean_object* v_r_3902_; lean_object* v___x_3903_; uint8_t v___x_3904_; 
v_k_3899_ = lean_ctor_get(v_a_3898_, 1);
lean_inc_n(v_k_3899_, 2);
v_v_3900_ = lean_ctor_get(v_a_3898_, 2);
lean_inc(v_v_3900_);
v_l_3901_ = lean_ctor_get(v_a_3898_, 3);
lean_inc(v_l_3901_);
v_r_3902_ = lean_ctor_get(v_a_3898_, 4);
lean_inc(v_r_3902_);
lean_dec_ref_known(v_a_3898_, 5);
lean_inc_ref(v_inst_3895_);
lean_inc(v_k_3896_);
v___x_3903_ = lean_apply_2(v_inst_3895_, v_k_3896_, v_k_3899_);
v___x_3904_ = lean_unbox(v___x_3903_);
switch(v___x_3904_)
{
case 0:
{
lean_dec(v_r_3902_);
lean_dec(v_v_3900_);
lean_dec(v_k_3899_);
v_a_3898_ = v_l_3901_;
goto _start;
}
case 1:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
lean_dec(v_r_3902_);
lean_dec(v_l_3901_);
lean_dec(v_best_3897_);
lean_dec(v_k_3896_);
lean_dec_ref(v_inst_3895_);
v___x_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3906_, 0, v_k_3899_);
lean_ctor_set(v___x_3906_, 1, v_v_3900_);
v___x_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
return v___x_3907_;
}
default: 
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec(v_l_3901_);
lean_dec(v_best_3897_);
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v_k_3899_);
lean_ctor_set(v___x_3908_, 1, v_v_3900_);
v___x_3909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
v_best_3897_ = v___x_3909_;
v_a_3898_ = v_r_3902_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3896_);
lean_dec_ref(v_inst_3895_);
return v_best_3897_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(lean_object* v_00_u03b1_3911_, lean_object* v_00_u03b2_3912_, lean_object* v_inst_3913_, lean_object* v_k_3914_, lean_object* v_best_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v___x_3917_; 
v___x_3917_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3913_, v_k_3914_, v_best_3915_, v_a_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___redArg(lean_object* v_inst_3918_, lean_object* v_k_3919_, lean_object* v_a_3920_){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3921_ = lean_box(0);
v___x_3922_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3918_, v_k_3919_, v___x_3921_, v_a_3920_);
return v___x_3922_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(lean_object* v_00_u03b1_3923_, lean_object* v_00_u03b2_3924_, lean_object* v_inst_3925_, lean_object* v_k_3926_, lean_object* v_a_3927_){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = lean_box(0);
v___x_3929_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3925_, v_k_3926_, v___x_3928_, v_a_3927_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object* v_inst_3930_, lean_object* v_k_3931_, lean_object* v_best_3932_, lean_object* v_a_3933_){
_start:
{
if (lean_obj_tag(v_a_3933_) == 0)
{
lean_object* v_k_3934_; lean_object* v_v_3935_; lean_object* v_l_3936_; lean_object* v_r_3937_; lean_object* v___x_3938_; uint8_t v___x_3939_; 
v_k_3934_ = lean_ctor_get(v_a_3933_, 1);
lean_inc_n(v_k_3934_, 2);
v_v_3935_ = lean_ctor_get(v_a_3933_, 2);
lean_inc(v_v_3935_);
v_l_3936_ = lean_ctor_get(v_a_3933_, 3);
lean_inc(v_l_3936_);
v_r_3937_ = lean_ctor_get(v_a_3933_, 4);
lean_inc(v_r_3937_);
lean_dec_ref_known(v_a_3933_, 5);
lean_inc_ref(v_inst_3930_);
lean_inc(v_k_3931_);
v___x_3938_ = lean_apply_2(v_inst_3930_, v_k_3931_, v_k_3934_);
v___x_3939_ = lean_unbox(v___x_3938_);
if (v___x_3939_ == 2)
{
lean_object* v___x_3940_; lean_object* v___x_3941_; 
lean_dec(v_l_3936_);
lean_dec(v_best_3932_);
v___x_3940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3940_, 0, v_k_3934_);
lean_ctor_set(v___x_3940_, 1, v_v_3935_);
v___x_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3940_);
v_best_3932_ = v___x_3941_;
v_a_3933_ = v_r_3937_;
goto _start;
}
else
{
lean_dec(v_r_3937_);
lean_dec(v_v_3935_);
lean_dec(v_k_3934_);
v_a_3933_ = v_l_3936_;
goto _start;
}
}
else
{
lean_dec(v_k_3931_);
lean_dec_ref(v_inst_3930_);
return v_best_3932_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(lean_object* v_00_u03b1_3944_, lean_object* v_00_u03b2_3945_, lean_object* v_inst_3946_, lean_object* v_k_3947_, lean_object* v_best_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v___x_3950_; 
v___x_3950_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3946_, v_k_3947_, v_best_3948_, v_a_3949_);
return v___x_3950_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___redArg(lean_object* v_inst_3951_, lean_object* v_k_3952_, lean_object* v_a_3953_){
_start:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3954_ = lean_box(0);
v___x_3955_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3951_, v_k_3952_, v___x_3954_, v_a_3953_);
return v___x_3955_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(lean_object* v_00_u03b1_3956_, lean_object* v_00_u03b2_3957_, lean_object* v_inst_3958_, lean_object* v_k_3959_, lean_object* v_a_3960_){
_start:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_box(0);
v___x_3962_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3958_, v_k_3959_, v___x_3961_, v_a_3960_);
return v___x_3962_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(lean_object* v_inst_3963_, lean_object* v_inst_3964_, lean_object* v_k_3965_, lean_object* v_t_3966_){
_start:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; 
v___x_3967_ = lean_box(0);
v___x_3968_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3963_, v_k_3965_, v___x_3967_, v_t_3966_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3970_ = l_panic___redArg(v_inst_3964_, v___x_3969_);
return v___x_3970_;
}
else
{
lean_object* v_val_3971_; 
v_val_3971_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_val_3971_);
lean_dec_ref_known(v___x_3968_, 1);
return v_val_3971_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg___boxed(lean_object* v_inst_3972_, lean_object* v_inst_3973_, lean_object* v_k_3974_, lean_object* v_t_3975_){
_start:
{
lean_object* v_res_3976_; 
v_res_3976_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(v_inst_3972_, v_inst_3973_, v_k_3974_, v_t_3975_);
lean_dec_ref(v_inst_3973_);
return v_res_3976_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object* v_00_u03b1_3977_, lean_object* v_00_u03b2_3978_, lean_object* v_inst_3979_, lean_object* v_inst_3980_, lean_object* v_k_3981_, lean_object* v_t_3982_){
_start:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3983_ = lean_box(0);
v___x_3984_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3979_, v_k_3981_, v___x_3983_, v_t_3982_);
if (lean_obj_tag(v___x_3984_) == 0)
{
lean_object* v___x_3985_; lean_object* v___x_3986_; 
v___x_3985_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3986_ = l_panic___redArg(v_inst_3980_, v___x_3985_);
return v___x_3986_;
}
else
{
lean_object* v_val_3987_; 
v_val_3987_ = lean_ctor_get(v___x_3984_, 0);
lean_inc(v_val_3987_);
lean_dec_ref_known(v___x_3984_, 1);
return v_val_3987_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_3988_, lean_object* v_00_u03b2_3989_, lean_object* v_inst_3990_, lean_object* v_inst_3991_, lean_object* v_k_3992_, lean_object* v_t_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(v_00_u03b1_3988_, v_00_u03b2_3989_, v_inst_3990_, v_inst_3991_, v_k_3992_, v_t_3993_);
lean_dec_ref(v_inst_3991_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(lean_object* v_inst_3995_, lean_object* v_inst_3996_, lean_object* v_k_3997_, lean_object* v_t_3998_){
_start:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = lean_box(0);
v___x_4000_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3995_, v_k_3997_, v___x_3999_, v_t_3998_);
if (lean_obj_tag(v___x_4000_) == 0)
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4002_ = l_panic___redArg(v_inst_3996_, v___x_4001_);
return v___x_4002_;
}
else
{
lean_object* v_val_4003_; 
v_val_4003_ = lean_ctor_get(v___x_4000_, 0);
lean_inc(v_val_4003_);
lean_dec_ref_known(v___x_4000_, 1);
return v_val_4003_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg___boxed(lean_object* v_inst_4004_, lean_object* v_inst_4005_, lean_object* v_k_4006_, lean_object* v_t_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(v_inst_4004_, v_inst_4005_, v_k_4006_, v_t_4007_);
lean_dec_ref(v_inst_4005_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object* v_00_u03b1_4009_, lean_object* v_00_u03b2_4010_, lean_object* v_inst_4011_, lean_object* v_inst_4012_, lean_object* v_k_4013_, lean_object* v_t_4014_){
_start:
{
lean_object* v___x_4015_; lean_object* v___x_4016_; 
v___x_4015_ = lean_box(0);
v___x_4016_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4011_, v_k_4013_, v___x_4015_, v_t_4014_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4017_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4018_ = l_panic___redArg(v_inst_4012_, v___x_4017_);
return v___x_4018_;
}
else
{
lean_object* v_val_4019_; 
v_val_4019_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_val_4019_);
lean_dec_ref_known(v___x_4016_, 1);
return v_val_4019_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_4020_, lean_object* v_00_u03b2_4021_, lean_object* v_inst_4022_, lean_object* v_inst_4023_, lean_object* v_k_4024_, lean_object* v_t_4025_){
_start:
{
lean_object* v_res_4026_; 
v_res_4026_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(v_00_u03b1_4020_, v_00_u03b2_4021_, v_inst_4022_, v_inst_4023_, v_k_4024_, v_t_4025_);
lean_dec_ref(v_inst_4023_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(lean_object* v_inst_4027_, lean_object* v_inst_4028_, lean_object* v_k_4029_, lean_object* v_t_4030_){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = lean_box(0);
v___x_4032_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4027_, v_k_4029_, v___x_4031_, v_t_4030_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4033_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4034_ = l_panic___redArg(v_inst_4028_, v___x_4033_);
return v___x_4034_;
}
else
{
lean_object* v_val_4035_; 
v_val_4035_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_val_4035_);
lean_dec_ref_known(v___x_4032_, 1);
return v_val_4035_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg___boxed(lean_object* v_inst_4036_, lean_object* v_inst_4037_, lean_object* v_k_4038_, lean_object* v_t_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(v_inst_4036_, v_inst_4037_, v_k_4038_, v_t_4039_);
lean_dec_ref(v_inst_4037_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object* v_00_u03b1_4041_, lean_object* v_00_u03b2_4042_, lean_object* v_inst_4043_, lean_object* v_inst_4044_, lean_object* v_k_4045_, lean_object* v_t_4046_){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = lean_box(0);
v___x_4048_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4043_, v_k_4045_, v___x_4047_, v_t_4046_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4050_ = l_panic___redArg(v_inst_4044_, v___x_4049_);
return v___x_4050_;
}
else
{
lean_object* v_val_4051_; 
v_val_4051_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_val_4051_);
lean_dec_ref_known(v___x_4048_, 1);
return v_val_4051_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_4052_, lean_object* v_00_u03b2_4053_, lean_object* v_inst_4054_, lean_object* v_inst_4055_, lean_object* v_k_4056_, lean_object* v_t_4057_){
_start:
{
lean_object* v_res_4058_; 
v_res_4058_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(v_00_u03b1_4052_, v_00_u03b2_4053_, v_inst_4054_, v_inst_4055_, v_k_4056_, v_t_4057_);
lean_dec_ref(v_inst_4055_);
return v_res_4058_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(lean_object* v_inst_4059_, lean_object* v_inst_4060_, lean_object* v_k_4061_, lean_object* v_t_4062_){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4063_ = lean_box(0);
v___x_4064_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4059_, v_k_4061_, v___x_4063_, v_t_4062_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4066_ = l_panic___redArg(v_inst_4060_, v___x_4065_);
return v___x_4066_;
}
else
{
lean_object* v_val_4067_; 
v_val_4067_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_val_4067_);
lean_dec_ref_known(v___x_4064_, 1);
return v_val_4067_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg___boxed(lean_object* v_inst_4068_, lean_object* v_inst_4069_, lean_object* v_k_4070_, lean_object* v_t_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(v_inst_4068_, v_inst_4069_, v_k_4070_, v_t_4071_);
lean_dec_ref(v_inst_4069_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object* v_00_u03b1_4073_, lean_object* v_00_u03b2_4074_, lean_object* v_inst_4075_, lean_object* v_inst_4076_, lean_object* v_k_4077_, lean_object* v_t_4078_){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = lean_box(0);
v___x_4080_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4075_, v_k_4077_, v___x_4079_, v_t_4078_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4082_ = l_panic___redArg(v_inst_4076_, v___x_4081_);
return v___x_4082_;
}
else
{
lean_object* v_val_4083_; 
v_val_4083_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_val_4083_);
lean_dec_ref_known(v___x_4080_, 1);
return v_val_4083_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_4084_, lean_object* v_00_u03b2_4085_, lean_object* v_inst_4086_, lean_object* v_inst_4087_, lean_object* v_k_4088_, lean_object* v_t_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(v_00_u03b1_4084_, v_00_u03b2_4085_, v_inst_4086_, v_inst_4087_, v_k_4088_, v_t_4089_);
lean_dec_ref(v_inst_4087_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(lean_object* v_inst_4091_, lean_object* v_k_4092_, lean_object* v_t_4093_, lean_object* v_fallback_4094_){
_start:
{
lean_object* v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = lean_box(0);
v___x_4096_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4091_, v_k_4092_, v___x_4095_, v_t_4093_);
if (lean_obj_tag(v___x_4096_) == 0)
{
lean_inc_ref(v_fallback_4094_);
return v_fallback_4094_;
}
else
{
lean_object* v_val_4097_; 
v_val_4097_ = lean_ctor_get(v___x_4096_, 0);
lean_inc(v_val_4097_);
lean_dec_ref_known(v___x_4096_, 1);
return v_val_4097_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg___boxed(lean_object* v_inst_4098_, lean_object* v_k_4099_, lean_object* v_t_4100_, lean_object* v_fallback_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(v_inst_4098_, v_k_4099_, v_t_4100_, v_fallback_4101_);
lean_dec_ref(v_fallback_4101_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(lean_object* v_00_u03b1_4103_, lean_object* v_00_u03b2_4104_, lean_object* v_inst_4105_, lean_object* v_k_4106_, lean_object* v_t_4107_, lean_object* v_fallback_4108_){
_start:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; 
v___x_4109_ = lean_box(0);
v___x_4110_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4105_, v_k_4106_, v___x_4109_, v_t_4107_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_inc_ref(v_fallback_4108_);
return v_fallback_4108_;
}
else
{
lean_object* v_val_4111_; 
v_val_4111_ = lean_ctor_get(v___x_4110_, 0);
lean_inc(v_val_4111_);
lean_dec_ref_known(v___x_4110_, 1);
return v_val_4111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___boxed(lean_object* v_00_u03b1_4112_, lean_object* v_00_u03b2_4113_, lean_object* v_inst_4114_, lean_object* v_k_4115_, lean_object* v_t_4116_, lean_object* v_fallback_4117_){
_start:
{
lean_object* v_res_4118_; 
v_res_4118_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(v_00_u03b1_4112_, v_00_u03b2_4113_, v_inst_4114_, v_k_4115_, v_t_4116_, v_fallback_4117_);
lean_dec_ref(v_fallback_4117_);
return v_res_4118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(lean_object* v_inst_4119_, lean_object* v_k_4120_, lean_object* v_t_4121_, lean_object* v_fallback_4122_){
_start:
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = lean_box(0);
v___x_4124_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4119_, v_k_4120_, v___x_4123_, v_t_4121_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_inc_ref(v_fallback_4122_);
return v_fallback_4122_;
}
else
{
lean_object* v_val_4125_; 
v_val_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc(v_val_4125_);
lean_dec_ref_known(v___x_4124_, 1);
return v_val_4125_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg___boxed(lean_object* v_inst_4126_, lean_object* v_k_4127_, lean_object* v_t_4128_, lean_object* v_fallback_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(v_inst_4126_, v_k_4127_, v_t_4128_, v_fallback_4129_);
lean_dec_ref(v_fallback_4129_);
return v_res_4130_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(lean_object* v_00_u03b1_4131_, lean_object* v_00_u03b2_4132_, lean_object* v_inst_4133_, lean_object* v_k_4134_, lean_object* v_t_4135_, lean_object* v_fallback_4136_){
_start:
{
lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4137_ = lean_box(0);
v___x_4138_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4133_, v_k_4134_, v___x_4137_, v_t_4135_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_inc_ref(v_fallback_4136_);
return v_fallback_4136_;
}
else
{
lean_object* v_val_4139_; 
v_val_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_val_4139_);
lean_dec_ref_known(v___x_4138_, 1);
return v_val_4139_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_4140_, lean_object* v_00_u03b2_4141_, lean_object* v_inst_4142_, lean_object* v_k_4143_, lean_object* v_t_4144_, lean_object* v_fallback_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(v_00_u03b1_4140_, v_00_u03b2_4141_, v_inst_4142_, v_k_4143_, v_t_4144_, v_fallback_4145_);
lean_dec_ref(v_fallback_4145_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(lean_object* v_inst_4147_, lean_object* v_k_4148_, lean_object* v_t_4149_, lean_object* v_fallback_4150_){
_start:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4151_ = lean_box(0);
v___x_4152_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4147_, v_k_4148_, v___x_4151_, v_t_4149_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_inc_ref(v_fallback_4150_);
return v_fallback_4150_;
}
else
{
lean_object* v_val_4153_; 
v_val_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_val_4153_);
lean_dec_ref_known(v___x_4152_, 1);
return v_val_4153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg___boxed(lean_object* v_inst_4154_, lean_object* v_k_4155_, lean_object* v_t_4156_, lean_object* v_fallback_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(v_inst_4154_, v_k_4155_, v_t_4156_, v_fallback_4157_);
lean_dec_ref(v_fallback_4157_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(lean_object* v_00_u03b1_4159_, lean_object* v_00_u03b2_4160_, lean_object* v_inst_4161_, lean_object* v_k_4162_, lean_object* v_t_4163_, lean_object* v_fallback_4164_){
_start:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; 
v___x_4165_ = lean_box(0);
v___x_4166_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4161_, v_k_4162_, v___x_4165_, v_t_4163_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_inc_ref(v_fallback_4164_);
return v_fallback_4164_;
}
else
{
lean_object* v_val_4167_; 
v_val_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc(v_val_4167_);
lean_dec_ref_known(v___x_4166_, 1);
return v_val_4167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___boxed(lean_object* v_00_u03b1_4168_, lean_object* v_00_u03b2_4169_, lean_object* v_inst_4170_, lean_object* v_k_4171_, lean_object* v_t_4172_, lean_object* v_fallback_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(v_00_u03b1_4168_, v_00_u03b2_4169_, v_inst_4170_, v_k_4171_, v_t_4172_, v_fallback_4173_);
lean_dec_ref(v_fallback_4173_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(lean_object* v_inst_4175_, lean_object* v_k_4176_, lean_object* v_t_4177_, lean_object* v_fallback_4178_){
_start:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4179_ = lean_box(0);
v___x_4180_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4175_, v_k_4176_, v___x_4179_, v_t_4177_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_inc_ref(v_fallback_4178_);
return v_fallback_4178_;
}
else
{
lean_object* v_val_4181_; 
v_val_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc(v_val_4181_);
lean_dec_ref_known(v___x_4180_, 1);
return v_val_4181_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg___boxed(lean_object* v_inst_4182_, lean_object* v_k_4183_, lean_object* v_t_4184_, lean_object* v_fallback_4185_){
_start:
{
lean_object* v_res_4186_; 
v_res_4186_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(v_inst_4182_, v_k_4183_, v_t_4184_, v_fallback_4185_);
lean_dec_ref(v_fallback_4185_);
return v_res_4186_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(lean_object* v_00_u03b1_4187_, lean_object* v_00_u03b2_4188_, lean_object* v_inst_4189_, lean_object* v_k_4190_, lean_object* v_t_4191_, lean_object* v_fallback_4192_){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = lean_box(0);
v___x_4194_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4189_, v_k_4190_, v___x_4193_, v_t_4191_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_inc_ref(v_fallback_4192_);
return v_fallback_4192_;
}
else
{
lean_object* v_val_4195_; 
v_val_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_val_4195_);
lean_dec_ref_known(v___x_4194_, 1);
return v_val_4195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_4196_, lean_object* v_00_u03b2_4197_, lean_object* v_inst_4198_, lean_object* v_k_4199_, lean_object* v_t_4200_, lean_object* v_fallback_4201_){
_start:
{
lean_object* v_res_4202_; 
v_res_4202_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(v_00_u03b1_4196_, v_00_u03b2_4197_, v_inst_4198_, v_k_4199_, v_t_4200_, v_fallback_4201_);
lean_dec_ref(v_fallback_4201_);
return v_res_4202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object* v_inst_4203_, lean_object* v_k_4204_, lean_object* v_x_4205_){
_start:
{
lean_object* v_k_4206_; lean_object* v_v_4207_; lean_object* v_l_4208_; lean_object* v_r_4209_; lean_object* v___x_4210_; uint8_t v___x_4211_; 
v_k_4206_ = lean_ctor_get(v_x_4205_, 1);
lean_inc_n(v_k_4206_, 2);
v_v_4207_ = lean_ctor_get(v_x_4205_, 2);
lean_inc(v_v_4207_);
v_l_4208_ = lean_ctor_get(v_x_4205_, 3);
lean_inc(v_l_4208_);
v_r_4209_ = lean_ctor_get(v_x_4205_, 4);
lean_inc(v_r_4209_);
lean_dec(v_x_4205_);
lean_inc_ref(v_inst_4203_);
lean_inc(v_k_4204_);
v___x_4210_ = lean_apply_2(v_inst_4203_, v_k_4204_, v_k_4206_);
v___x_4211_ = lean_unbox(v___x_4210_);
switch(v___x_4211_)
{
case 0:
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
lean_dec(v_r_4209_);
v___x_4212_ = lean_box(0);
v___x_4213_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4203_, v_k_4204_, v___x_4212_, v_l_4208_);
if (lean_obj_tag(v___x_4213_) == 0)
{
lean_object* v___x_4214_; 
v___x_4214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4214_, 0, v_k_4206_);
lean_ctor_set(v___x_4214_, 1, v_v_4207_);
return v___x_4214_;
}
else
{
lean_object* v_val_4215_; 
lean_dec(v_v_4207_);
lean_dec(v_k_4206_);
v_val_4215_ = lean_ctor_get(v___x_4213_, 0);
lean_inc(v_val_4215_);
lean_dec_ref_known(v___x_4213_, 1);
return v_val_4215_;
}
}
case 1:
{
lean_object* v___x_4216_; 
lean_dec(v_r_4209_);
lean_dec(v_l_4208_);
lean_dec(v_k_4204_);
lean_dec_ref(v_inst_4203_);
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v_k_4206_);
lean_ctor_set(v___x_4216_, 1, v_v_4207_);
return v___x_4216_;
}
default: 
{
lean_dec(v_l_4208_);
lean_dec(v_v_4207_);
lean_dec(v_k_4206_);
v_x_4205_ = v_r_4209_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(lean_object* v_00_u03b1_4218_, lean_object* v_00_u03b2_4219_, lean_object* v_inst_4220_, lean_object* v_inst_4221_, lean_object* v_k_4222_, lean_object* v_x_4223_, lean_object* v_x_4224_, lean_object* v_x_4225_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_inst_4220_, v_k_4222_, v_x_4223_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object* v_inst_4227_, lean_object* v_k_4228_, lean_object* v_x_4229_){
_start:
{
lean_object* v_k_4230_; lean_object* v_v_4231_; lean_object* v_l_4232_; lean_object* v_r_4233_; lean_object* v___x_4234_; uint8_t v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; uint8_t v___x_4238_; 
v_k_4230_ = lean_ctor_get(v_x_4229_, 1);
lean_inc_n(v_k_4230_, 2);
v_v_4231_ = lean_ctor_get(v_x_4229_, 2);
lean_inc(v_v_4231_);
v_l_4232_ = lean_ctor_get(v_x_4229_, 3);
lean_inc(v_l_4232_);
v_r_4233_ = lean_ctor_get(v_x_4229_, 4);
lean_inc(v_r_4233_);
lean_dec(v_x_4229_);
lean_inc_ref(v_inst_4227_);
lean_inc(v_k_4228_);
v___x_4234_ = lean_apply_2(v_inst_4227_, v_k_4228_, v_k_4230_);
v___x_4235_ = lean_unbox(v___x_4234_);
v___x_4236_ = l_Ordering_ctorIdx(v___x_4235_);
v___x_4237_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0);
v___x_4238_ = lean_nat_dec_eq(v___x_4236_, v___x_4237_);
lean_dec(v___x_4236_);
if (v___x_4238_ == 0)
{
lean_dec(v_l_4232_);
lean_dec(v_v_4231_);
lean_dec(v_k_4230_);
v_x_4229_ = v_r_4233_;
goto _start;
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
lean_dec(v_r_4233_);
v___x_4240_ = lean_box(0);
v___x_4241_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4227_, v_k_4228_, v___x_4240_, v_l_4232_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v___x_4242_; 
v___x_4242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4242_, 0, v_k_4230_);
lean_ctor_set(v___x_4242_, 1, v_v_4231_);
return v___x_4242_;
}
else
{
lean_object* v_val_4243_; 
lean_dec(v_v_4231_);
lean_dec(v_k_4230_);
v_val_4243_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_val_4243_);
lean_dec_ref_known(v___x_4241_, 1);
return v_val_4243_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(lean_object* v_00_u03b1_4244_, lean_object* v_00_u03b2_4245_, lean_object* v_inst_4246_, lean_object* v_inst_4247_, lean_object* v_k_4248_, lean_object* v_x_4249_, lean_object* v_x_4250_, lean_object* v_x_4251_){
_start:
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_inst_4246_, v_k_4248_, v_x_4249_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object* v_inst_4253_, lean_object* v_k_4254_, lean_object* v_x_4255_){
_start:
{
lean_object* v_k_4256_; lean_object* v_v_4257_; lean_object* v_l_4258_; lean_object* v_r_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; 
v_k_4256_ = lean_ctor_get(v_x_4255_, 1);
lean_inc_n(v_k_4256_, 2);
v_v_4257_ = lean_ctor_get(v_x_4255_, 2);
lean_inc(v_v_4257_);
v_l_4258_ = lean_ctor_get(v_x_4255_, 3);
lean_inc(v_l_4258_);
v_r_4259_ = lean_ctor_get(v_x_4255_, 4);
lean_inc(v_r_4259_);
lean_dec(v_x_4255_);
lean_inc_ref(v_inst_4253_);
lean_inc(v_k_4254_);
v___x_4260_ = lean_apply_2(v_inst_4253_, v_k_4254_, v_k_4256_);
v___x_4261_ = lean_unbox(v___x_4260_);
switch(v___x_4261_)
{
case 0:
{
lean_dec(v_r_4259_);
lean_dec(v_v_4257_);
lean_dec(v_k_4256_);
v_x_4255_ = v_l_4258_;
goto _start;
}
case 1:
{
lean_object* v___x_4263_; 
lean_dec(v_r_4259_);
lean_dec(v_l_4258_);
lean_dec(v_k_4254_);
lean_dec_ref(v_inst_4253_);
v___x_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4263_, 0, v_k_4256_);
lean_ctor_set(v___x_4263_, 1, v_v_4257_);
return v___x_4263_;
}
default: 
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
lean_dec(v_l_4258_);
v___x_4264_ = lean_box(0);
v___x_4265_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4253_, v_k_4254_, v___x_4264_, v_r_4259_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v___x_4266_; 
v___x_4266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4266_, 0, v_k_4256_);
lean_ctor_set(v___x_4266_, 1, v_v_4257_);
return v___x_4266_;
}
else
{
lean_object* v_val_4267_; 
lean_dec(v_v_4257_);
lean_dec(v_k_4256_);
v_val_4267_ = lean_ctor_get(v___x_4265_, 0);
lean_inc(v_val_4267_);
lean_dec_ref_known(v___x_4265_, 1);
return v_val_4267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(lean_object* v_00_u03b1_4268_, lean_object* v_00_u03b2_4269_, lean_object* v_inst_4270_, lean_object* v_inst_4271_, lean_object* v_k_4272_, lean_object* v_x_4273_, lean_object* v_x_4274_, lean_object* v_x_4275_){
_start:
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_inst_4270_, v_k_4272_, v_x_4273_);
return v___x_4276_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object* v_inst_4277_, lean_object* v_k_4278_, lean_object* v_x_4279_){
_start:
{
lean_object* v_k_4280_; lean_object* v_v_4281_; lean_object* v_l_4282_; lean_object* v_r_4283_; lean_object* v___x_4284_; uint8_t v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; uint8_t v___x_4288_; 
v_k_4280_ = lean_ctor_get(v_x_4279_, 1);
lean_inc_n(v_k_4280_, 2);
v_v_4281_ = lean_ctor_get(v_x_4279_, 2);
lean_inc(v_v_4281_);
v_l_4282_ = lean_ctor_get(v_x_4279_, 3);
lean_inc(v_l_4282_);
v_r_4283_ = lean_ctor_get(v_x_4279_, 4);
lean_inc(v_r_4283_);
lean_dec(v_x_4279_);
lean_inc_ref(v_inst_4277_);
lean_inc(v_k_4278_);
v___x_4284_ = lean_apply_2(v_inst_4277_, v_k_4278_, v_k_4280_);
v___x_4285_ = lean_unbox(v___x_4284_);
v___x_4286_ = l_Ordering_ctorIdx(v___x_4285_);
v___x_4287_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0);
v___x_4288_ = lean_nat_dec_eq(v___x_4286_, v___x_4287_);
lean_dec(v___x_4286_);
if (v___x_4288_ == 0)
{
lean_dec(v_r_4283_);
lean_dec(v_v_4281_);
lean_dec(v_k_4280_);
v_x_4279_ = v_l_4282_;
goto _start;
}
else
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
lean_dec(v_l_4282_);
v___x_4290_ = lean_box(0);
v___x_4291_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4277_, v_k_4278_, v___x_4290_, v_r_4283_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v___x_4292_; 
v___x_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4292_, 0, v_k_4280_);
lean_ctor_set(v___x_4292_, 1, v_v_4281_);
return v___x_4292_;
}
else
{
lean_object* v_val_4293_; 
lean_dec(v_v_4281_);
lean_dec(v_k_4280_);
v_val_4293_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_val_4293_);
lean_dec_ref_known(v___x_4291_, 1);
return v_val_4293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(lean_object* v_00_u03b1_4294_, lean_object* v_00_u03b2_4295_, lean_object* v_inst_4296_, lean_object* v_inst_4297_, lean_object* v_k_4298_, lean_object* v_x_4299_, lean_object* v_x_4300_, lean_object* v_x_4301_){
_start:
{
lean_object* v___x_4302_; 
v___x_4302_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_inst_4296_, v_k_4298_, v_x_4299_);
return v___x_4302_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Compare(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Balanced(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Ordered(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderPredicates(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_BasicAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DTreeMap_Internal_Queries(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = runtime_initialize_Init_Data_Nat_Internal_Linear(builtin);
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
lean_object* initialize_Init_Data_Nat_Internal_Linear(uint8_t builtin);
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
res = initialize_Init_Data_Nat_Internal_Linear(builtin);
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
