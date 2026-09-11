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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___redArg();
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall___redArg___boxed(lean_object* v___dummy_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_DTreeMap_Internal_Impl_instCoeTypeForall___redArg();
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall(lean_object* v_00_u03b1_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_box(0);
return v___x_6_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5));
v___x_51_ = l_String_toRawSubstring_x27(v___x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1(lean_object* v_x_74_, lean_object* v_a_75_, lean_object* v_a_76_){
_start:
{
lean_object* v___x_77_; uint8_t v___x_78_; 
v___x_77_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5));
lean_inc(v_x_74_);
v___x_78_ = l_Lean_Syntax_isOfKind(v_x_74_, v___x_77_);
if (v___x_78_ == 0)
{
lean_object* v___x_79_; lean_object* v___x_80_; 
lean_dec(v_x_74_);
v___x_79_ = lean_box(1);
v___x_80_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v_a_76_);
return v___x_80_;
}
else
{
lean_object* v_quotContext_81_; lean_object* v_currMacroScope_82_; lean_object* v_ref_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_quotContext_81_ = lean_ctor_get(v_a_75_, 1);
v_currMacroScope_82_ = lean_ctor_get(v_a_75_, 2);
v_ref_83_ = lean_ctor_get(v_a_75_, 5);
v___x_84_ = lean_unsigned_to_nat(0u);
v___x_85_ = l_Lean_Syntax_getArg(v_x_74_, v___x_84_);
v___x_86_ = lean_unsigned_to_nat(2u);
v___x_87_ = l_Lean_Syntax_getArg(v_x_74_, v___x_86_);
lean_dec(v_x_74_);
v___x_88_ = 0;
v___x_89_ = l_Lean_SourceInfo_fromRef(v_ref_83_, v___x_88_);
v___x_90_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4));
v___x_91_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6);
v___x_92_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_82_);
lean_inc(v_quotContext_81_);
v___x_93_ = l_Lean_addMacroScope(v_quotContext_81_, v___x_92_, v_currMacroScope_82_);
v___x_94_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12));
lean_inc_n(v___x_89_, 2);
v___x_95_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_95_, 0, v___x_89_);
lean_ctor_set(v___x_95_, 1, v___x_91_);
lean_ctor_set(v___x_95_, 2, v___x_93_);
lean_ctor_set(v___x_95_, 3, v___x_94_);
v___x_96_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14));
v___x_97_ = l_Lean_Syntax_node2(v___x_89_, v___x_96_, v___x_85_, v___x_87_);
v___x_98_ = l_Lean_Syntax_node2(v___x_89_, v___x_90_, v___x_95_, v___x_97_);
v___x_99_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v_a_76_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___boxed(lean_object* v_x_100_, lean_object* v_a_101_, lean_object* v_a_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1(v_x_100_, v_a_101_, v_a_102_);
lean_dec_ref(v_a_101_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(lean_object* v_x_107_, lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_110_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4));
lean_inc(v_x_107_);
v___x_111_ = l_Lean_Syntax_isOfKind(v_x_107_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_x_107_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_a_109_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = l_Lean_Syntax_getArg(v_x_107_, v___x_114_);
v___x_116_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1));
lean_inc(v___x_115_);
v___x_117_ = l_Lean_Syntax_isOfKind(v___x_115_, v___x_116_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; lean_object* v___x_119_; 
lean_dec(v___x_115_);
lean_dec(v_x_107_);
v___x_118_ = lean_box(0);
v___x_119_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_109_);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = l_Lean_Syntax_getArg(v_x_107_, v___x_120_);
lean_dec(v_x_107_);
v___x_122_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_121_);
v___x_123_ = l_Lean_Syntax_matchesNull(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___x_125_; 
lean_dec(v___x_121_);
lean_dec(v___x_115_);
v___x_124_ = lean_box(0);
v___x_125_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v_a_109_);
return v___x_125_;
}
else
{
lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v_ref_128_; uint8_t v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_126_ = l_Lean_Syntax_getArg(v___x_121_, v___x_114_);
v___x_127_ = l_Lean_Syntax_getArg(v___x_121_, v___x_120_);
lean_dec(v___x_121_);
v_ref_128_ = l_Lean_replaceRef(v___x_115_, v_a_108_);
lean_dec(v___x_115_);
v___x_129_ = 0;
v___x_130_ = l_Lean_SourceInfo_fromRef(v_ref_128_, v___x_129_);
lean_dec(v_ref_128_);
v___x_131_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5));
v___x_132_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8));
lean_inc(v___x_130_);
v___x_133_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_130_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = l_Lean_Syntax_node3(v___x_130_, v___x_131_, v___x_126_, v___x_133_, v___x_127_);
v___x_135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_a_109_);
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___boxed(lean_object* v_x_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(v_x_136_, v_a_137_, v_a_138_);
lean_dec(v_a_137_);
return v_res_139_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object* v_inst_140_, lean_object* v_k_141_, lean_object* v_t_142_){
_start:
{
if (lean_obj_tag(v_t_142_) == 0)
{
lean_object* v_k_143_; lean_object* v_l_144_; lean_object* v_r_145_; lean_object* v___x_146_; uint8_t v___x_147_; 
v_k_143_ = lean_ctor_get(v_t_142_, 1);
lean_inc(v_k_143_);
v_l_144_ = lean_ctor_get(v_t_142_, 3);
lean_inc(v_l_144_);
v_r_145_ = lean_ctor_get(v_t_142_, 4);
lean_inc(v_r_145_);
lean_dec_ref_known(v_t_142_, 5);
lean_inc_ref(v_inst_140_);
lean_inc(v_k_141_);
v___x_146_ = lean_apply_2(v_inst_140_, v_k_141_, v_k_143_);
v___x_147_ = lean_unbox(v___x_146_);
switch(v___x_147_)
{
case 0:
{
lean_dec(v_r_145_);
v_t_142_ = v_l_144_;
goto _start;
}
case 1:
{
uint8_t v___x_149_; 
lean_dec(v_r_145_);
lean_dec(v_l_144_);
lean_dec(v_k_141_);
lean_dec_ref(v_inst_140_);
v___x_149_ = 1;
return v___x_149_;
}
default: 
{
lean_dec(v_l_144_);
v_t_142_ = v_r_145_;
goto _start;
}
}
}
else
{
uint8_t v___x_151_; 
lean_dec(v_k_141_);
lean_dec_ref(v_inst_140_);
v___x_151_ = 0;
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___redArg___boxed(lean_object* v_inst_152_, lean_object* v_k_153_, lean_object* v_t_154_){
_start:
{
uint8_t v_res_155_; lean_object* v_r_156_; 
v_res_155_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_152_, v_k_153_, v_t_154_);
v_r_156_ = lean_box(v_res_155_);
return v_r_156_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_inst_159_, lean_object* v_k_160_, lean_object* v_t_161_){
_start:
{
uint8_t v___x_162_; 
v___x_162_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_159_, v_k_160_, v_t_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___boxed(lean_object* v_00_u03b1_163_, lean_object* v_00_u03b2_164_, lean_object* v_inst_165_, lean_object* v_k_166_, lean_object* v_t_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = l_Std_DTreeMap_Internal_Impl_contains(v_00_u03b1_163_, v_00_u03b2_164_, v_inst_165_, v_k_166_, v_t_167_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___redArg(){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lean_box(0);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___redArg___boxed(lean_object* v___dummy_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___redArg();
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(lean_object* v_00_u03b1_174_, lean_object* v_00_u03b2_175_, lean_object* v_inst_176_){
_start:
{
lean_object* v___x_177_; 
v___x_177_ = lean_box(0);
return v___x_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___boxed(lean_object* v_00_u03b1_178_, lean_object* v_00_u03b2_179_, lean_object* v_inst_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(v_00_u03b1_178_, v_00_u03b2_179_, v_inst_180_);
lean_dec_ref(v_inst_180_);
return v_res_181_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(lean_object* v_inst_182_, lean_object* v_m_183_, lean_object* v_a_184_){
_start:
{
uint8_t v___x_185_; 
v___x_185_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_182_, v_a_184_, v_m_183_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg___boxed(lean_object* v_inst_186_, lean_object* v_m_187_, lean_object* v_a_188_){
_start:
{
uint8_t v_res_189_; lean_object* v_r_190_; 
v_res_189_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(v_inst_186_, v_m_187_, v_a_188_);
v_r_190_ = lean_box(v_res_189_);
return v_r_190_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem(lean_object* v_00_u03b1_191_, lean_object* v_00_u03b2_192_, lean_object* v_inst_193_, lean_object* v_m_194_, lean_object* v_a_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_193_, v_a_195_, v_m_194_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___boxed(lean_object* v_00_u03b1_197_, lean_object* v_00_u03b2_198_, lean_object* v_inst_199_, lean_object* v_m_200_, lean_object* v_a_201_){
_start:
{
uint8_t v_res_202_; lean_object* v_r_203_; 
v_res_202_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem(v_00_u03b1_197_, v_00_u03b2_198_, v_inst_199_, v_m_200_, v_a_201_);
v_r_203_ = lean_box(v_res_202_);
return v_r_203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter___redArg(lean_object* v_t_204_, lean_object* v_h__1_205_, lean_object* v_h__2_206_){
_start:
{
if (lean_obj_tag(v_t_204_) == 0)
{
lean_object* v_size_207_; lean_object* v_k_208_; lean_object* v_v_209_; lean_object* v_l_210_; lean_object* v_r_211_; lean_object* v___x_212_; 
lean_dec(v_h__1_205_);
v_size_207_ = lean_ctor_get(v_t_204_, 0);
lean_inc(v_size_207_);
v_k_208_ = lean_ctor_get(v_t_204_, 1);
lean_inc(v_k_208_);
v_v_209_ = lean_ctor_get(v_t_204_, 2);
lean_inc(v_v_209_);
v_l_210_ = lean_ctor_get(v_t_204_, 3);
lean_inc(v_l_210_);
v_r_211_ = lean_ctor_get(v_t_204_, 4);
lean_inc(v_r_211_);
lean_dec_ref_known(v_t_204_, 5);
v___x_212_ = lean_apply_5(v_h__2_206_, v_size_207_, v_k_208_, v_v_209_, v_l_210_, v_r_211_);
return v___x_212_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; 
lean_dec(v_h__2_206_);
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_1(v_h__1_205_, v___x_213_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__3_splitter(lean_object* v_00_u03b1_215_, lean_object* v_00_u03b2_216_, lean_object* v_motive_217_, lean_object* v_t_218_, lean_object* v_h__1_219_, lean_object* v_h__2_220_){
_start:
{
if (lean_obj_tag(v_t_218_) == 0)
{
lean_object* v_size_221_; lean_object* v_k_222_; lean_object* v_v_223_; lean_object* v_l_224_; lean_object* v_r_225_; lean_object* v___x_226_; 
lean_dec(v_h__1_219_);
v_size_221_ = lean_ctor_get(v_t_218_, 0);
lean_inc(v_size_221_);
v_k_222_ = lean_ctor_get(v_t_218_, 1);
lean_inc(v_k_222_);
v_v_223_ = lean_ctor_get(v_t_218_, 2);
lean_inc(v_v_223_);
v_l_224_ = lean_ctor_get(v_t_218_, 3);
lean_inc(v_l_224_);
v_r_225_ = lean_ctor_get(v_t_218_, 4);
lean_inc(v_r_225_);
lean_dec_ref_known(v_t_218_, 5);
v___x_226_ = lean_apply_5(v_h__2_220_, v_size_221_, v_k_222_, v_v_223_, v_l_224_, v_r_225_);
return v___x_226_;
}
else
{
lean_object* v___x_227_; lean_object* v___x_228_; 
lean_dec(v_h__2_220_);
v___x_227_ = lean_box(0);
v___x_228_ = lean_apply_1(v_h__1_219_, v___x_227_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t v_x_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_, lean_object* v_h__3_232_){
_start:
{
switch(v_x_229_)
{
case 0:
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_h__3_232_);
lean_dec(v_h__2_231_);
v___x_233_ = lean_box(0);
v___x_234_ = lean_apply_1(v_h__1_230_, v___x_233_);
return v___x_234_;
}
case 1:
{
lean_object* v___x_235_; lean_object* v___x_236_; 
lean_dec(v_h__2_231_);
lean_dec(v_h__1_230_);
v___x_235_ = lean_box(0);
v___x_236_ = lean_apply_1(v_h__3_232_, v___x_235_);
return v___x_236_;
}
default: 
{
lean_object* v___x_237_; lean_object* v___x_238_; 
lean_dec(v_h__3_232_);
lean_dec(v_h__1_230_);
v___x_237_ = lean_box(0);
v___x_238_ = lean_apply_1(v_h__2_231_, v___x_237_);
return v___x_238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* v_x_239_, lean_object* v_h__1_240_, lean_object* v_h__2_241_, lean_object* v_h__3_242_){
_start:
{
uint8_t v_x_33__boxed_243_; lean_object* v_res_244_; 
v_x_33__boxed_243_ = lean_unbox(v_x_239_);
v_res_244_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_33__boxed_243_, v_h__1_240_, v_h__2_241_, v_h__3_242_);
return v_res_244_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* v_motive_245_, uint8_t v_x_246_, lean_object* v_h__1_247_, lean_object* v_h__2_248_, lean_object* v_h__3_249_){
_start:
{
switch(v_x_246_)
{
case 0:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
lean_dec(v_h__3_249_);
lean_dec(v_h__2_248_);
v___x_250_ = lean_box(0);
v___x_251_ = lean_apply_1(v_h__1_247_, v___x_250_);
return v___x_251_;
}
case 1:
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec(v_h__2_248_);
lean_dec(v_h__1_247_);
v___x_252_ = lean_box(0);
v___x_253_ = lean_apply_1(v_h__3_249_, v___x_252_);
return v___x_253_;
}
default: 
{
lean_object* v___x_254_; lean_object* v___x_255_; 
lean_dec(v_h__3_249_);
lean_dec(v_h__1_247_);
v___x_254_ = lean_box(0);
v___x_255_ = lean_apply_1(v_h__2_248_, v___x_254_);
return v___x_255_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* v_motive_256_, lean_object* v_x_257_, lean_object* v_h__1_258_, lean_object* v_h__2_259_, lean_object* v_h__3_260_){
_start:
{
uint8_t v_x_48__boxed_261_; lean_object* v_res_262_; 
v_x_48__boxed_261_ = lean_unbox(v_x_257_);
v_res_262_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_256_, v_x_48__boxed_261_, v_h__1_258_, v_h__2_259_, v_h__3_260_);
return v_res_262_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(lean_object* v_t_263_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___redArg___boxed(lean_object* v_t_266_){
_start:
{
uint8_t v_res_267_; lean_object* v_r_268_; 
v_res_267_ = l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(v_t_266_);
lean_dec(v_t_266_);
v_r_268_ = lean_box(v_res_267_);
return v_r_268_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty(lean_object* v_00_u03b1_269_, lean_object* v_00_u03b2_270_, lean_object* v_t_271_){
_start:
{
if (lean_obj_tag(v_t_271_) == 0)
{
uint8_t v___x_272_; 
v___x_272_ = 0;
return v___x_272_;
}
else
{
uint8_t v___x_273_; 
v___x_273_ = 1;
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___boxed(lean_object* v_00_u03b1_274_, lean_object* v_00_u03b2_275_, lean_object* v_t_276_){
_start:
{
uint8_t v_res_277_; lean_object* v_r_278_; 
v_res_277_ = l_Std_DTreeMap_Internal_Impl_isEmpty(v_00_u03b1_274_, v_00_u03b2_275_, v_t_276_);
lean_dec(v_t_276_);
v_r_278_ = lean_box(v_res_277_);
return v_r_278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object* v_inst_279_, lean_object* v_t_280_, lean_object* v_k_281_){
_start:
{
if (lean_obj_tag(v_t_280_) == 0)
{
lean_object* v_k_282_; lean_object* v_v_283_; lean_object* v_l_284_; lean_object* v_r_285_; lean_object* v___x_286_; uint8_t v___x_287_; 
v_k_282_ = lean_ctor_get(v_t_280_, 1);
lean_inc(v_k_282_);
v_v_283_ = lean_ctor_get(v_t_280_, 2);
lean_inc(v_v_283_);
v_l_284_ = lean_ctor_get(v_t_280_, 3);
lean_inc(v_l_284_);
v_r_285_ = lean_ctor_get(v_t_280_, 4);
lean_inc(v_r_285_);
lean_dec_ref_known(v_t_280_, 5);
lean_inc_ref(v_inst_279_);
lean_inc(v_k_281_);
v___x_286_ = lean_apply_2(v_inst_279_, v_k_281_, v_k_282_);
v___x_287_ = lean_unbox(v___x_286_);
switch(v___x_287_)
{
case 0:
{
lean_dec(v_r_285_);
lean_dec(v_v_283_);
v_t_280_ = v_l_284_;
goto _start;
}
case 1:
{
lean_object* v___x_289_; 
lean_dec(v_r_285_);
lean_dec(v_l_284_);
lean_dec(v_k_281_);
lean_dec_ref(v_inst_279_);
v___x_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_289_, 0, v_v_283_);
return v___x_289_;
}
default: 
{
lean_dec(v_l_284_);
lean_dec(v_v_283_);
v_t_280_ = v_r_285_;
goto _start;
}
}
}
else
{
lean_object* v___x_291_; 
lean_dec(v_k_281_);
lean_dec_ref(v_inst_279_);
v___x_291_ = lean_box(0);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f(lean_object* v_00_u03b1_292_, lean_object* v_00_u03b2_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_t_296_, lean_object* v_k_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_inst_294_, v_t_296_, v_k_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get___redArg(lean_object* v_inst_299_, lean_object* v_t_300_, lean_object* v_k_301_){
_start:
{
lean_object* v_k_302_; lean_object* v_v_303_; lean_object* v_l_304_; lean_object* v_r_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v_k_302_ = lean_ctor_get(v_t_300_, 1);
lean_inc(v_k_302_);
v_v_303_ = lean_ctor_get(v_t_300_, 2);
lean_inc(v_v_303_);
v_l_304_ = lean_ctor_get(v_t_300_, 3);
lean_inc(v_l_304_);
v_r_305_ = lean_ctor_get(v_t_300_, 4);
lean_inc(v_r_305_);
lean_dec(v_t_300_);
lean_inc_ref(v_inst_299_);
lean_inc(v_k_301_);
v___x_306_ = lean_apply_2(v_inst_299_, v_k_301_, v_k_302_);
v___x_307_ = lean_unbox(v___x_306_);
switch(v___x_307_)
{
case 0:
{
lean_dec(v_r_305_);
lean_dec(v_v_303_);
v_t_300_ = v_l_304_;
goto _start;
}
case 1:
{
lean_dec(v_r_305_);
lean_dec(v_l_304_);
lean_dec(v_k_301_);
lean_dec_ref(v_inst_299_);
return v_v_303_;
}
default: 
{
lean_dec(v_l_304_);
lean_dec(v_v_303_);
v_t_300_ = v_r_305_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get(lean_object* v_00_u03b1_310_, lean_object* v_00_u03b2_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_t_314_, lean_object* v_k_315_, lean_object* v_hlk_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_inst_312_, v_t_314_, v_k_315_);
return v___x_317_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_321_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_322_ = lean_unsigned_to_nat(13u);
v___x_323_ = lean_unsigned_to_nat(108u);
v___x_324_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1));
v___x_325_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_326_ = l_mkPanicMessageWithDecl(v___x_325_, v___x_324_, v___x_323_, v___x_322_, v___x_321_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object* v_inst_327_, lean_object* v_t_328_, lean_object* v_k_329_, lean_object* v_inst_330_){
_start:
{
if (lean_obj_tag(v_t_328_) == 0)
{
lean_object* v_k_331_; lean_object* v_v_332_; lean_object* v_l_333_; lean_object* v_r_334_; lean_object* v___x_335_; uint8_t v___x_336_; 
v_k_331_ = lean_ctor_get(v_t_328_, 1);
lean_inc(v_k_331_);
v_v_332_ = lean_ctor_get(v_t_328_, 2);
lean_inc(v_v_332_);
v_l_333_ = lean_ctor_get(v_t_328_, 3);
lean_inc(v_l_333_);
v_r_334_ = lean_ctor_get(v_t_328_, 4);
lean_inc(v_r_334_);
lean_dec_ref_known(v_t_328_, 5);
lean_inc_ref(v_inst_327_);
lean_inc(v_k_329_);
v___x_335_ = lean_apply_2(v_inst_327_, v_k_329_, v_k_331_);
v___x_336_ = lean_unbox(v___x_335_);
switch(v___x_336_)
{
case 0:
{
lean_dec(v_r_334_);
lean_dec(v_v_332_);
v_t_328_ = v_l_333_;
goto _start;
}
case 1:
{
lean_dec(v_r_334_);
lean_dec(v_l_333_);
lean_dec(v_k_329_);
lean_dec_ref(v_inst_327_);
return v_v_332_;
}
default: 
{
lean_dec(v_l_333_);
lean_dec(v_v_332_);
v_t_328_ = v_r_334_;
goto _start;
}
}
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec(v_k_329_);
lean_dec_ref(v_inst_327_);
v___x_339_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3);
v___x_340_ = l_panic___redArg(v_inst_330_, v___x_339_);
return v___x_340_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg___boxed(lean_object* v_inst_341_, lean_object* v_t_342_, lean_object* v_k_343_, lean_object* v_inst_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_inst_341_, v_t_342_, v_k_343_, v_inst_344_);
lean_dec(v_inst_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21(lean_object* v_00_u03b1_346_, lean_object* v_00_u03b2_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_t_350_, lean_object* v_k_351_, lean_object* v_inst_352_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_inst_348_, v_t_350_, v_k_351_, v_inst_352_);
return v___x_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___boxed(lean_object* v_00_u03b1_354_, lean_object* v_00_u03b2_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_t_358_, lean_object* v_k_359_, lean_object* v_inst_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_DTreeMap_Internal_Impl_get_x21(v_00_u03b1_354_, v_00_u03b2_355_, v_inst_356_, v_inst_357_, v_t_358_, v_k_359_, v_inst_360_);
lean_dec(v_inst_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg(lean_object* v_inst_362_, lean_object* v_t_363_, lean_object* v_k_364_, lean_object* v_fallback_365_){
_start:
{
if (lean_obj_tag(v_t_363_) == 0)
{
lean_object* v_k_366_; lean_object* v_v_367_; lean_object* v_l_368_; lean_object* v_r_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_k_366_ = lean_ctor_get(v_t_363_, 1);
lean_inc(v_k_366_);
v_v_367_ = lean_ctor_get(v_t_363_, 2);
lean_inc(v_v_367_);
v_l_368_ = lean_ctor_get(v_t_363_, 3);
lean_inc(v_l_368_);
v_r_369_ = lean_ctor_get(v_t_363_, 4);
lean_inc(v_r_369_);
lean_dec_ref_known(v_t_363_, 5);
lean_inc_ref(v_inst_362_);
lean_inc(v_k_364_);
v___x_370_ = lean_apply_2(v_inst_362_, v_k_364_, v_k_366_);
v___x_371_ = lean_unbox(v___x_370_);
switch(v___x_371_)
{
case 0:
{
lean_dec(v_r_369_);
lean_dec(v_v_367_);
v_t_363_ = v_l_368_;
goto _start;
}
case 1:
{
lean_dec(v_r_369_);
lean_dec(v_l_368_);
lean_dec(v_k_364_);
lean_dec_ref(v_inst_362_);
return v_v_367_;
}
default: 
{
lean_dec(v_l_368_);
lean_dec(v_v_367_);
v_t_363_ = v_r_369_;
goto _start;
}
}
}
else
{
lean_dec(v_k_364_);
lean_dec_ref(v_inst_362_);
lean_inc(v_fallback_365_);
return v_fallback_365_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg___boxed(lean_object* v_inst_374_, lean_object* v_t_375_, lean_object* v_k_376_, lean_object* v_fallback_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_inst_374_, v_t_375_, v_k_376_, v_fallback_377_);
lean_dec(v_fallback_377_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_inst_381_, lean_object* v_inst_382_, lean_object* v_t_383_, lean_object* v_k_384_, lean_object* v_fallback_385_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_inst_381_, v_t_383_, v_k_384_, v_fallback_385_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___boxed(lean_object* v_00_u03b1_387_, lean_object* v_00_u03b2_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_t_391_, lean_object* v_k_392_, lean_object* v_fallback_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Std_DTreeMap_Internal_Impl_getD(v_00_u03b1_387_, v_00_u03b2_388_, v_inst_389_, v_inst_390_, v_t_391_, v_k_392_, v_fallback_393_);
lean_dec(v_fallback_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(lean_object* v_inst_395_, lean_object* v_t_396_, lean_object* v_k_397_){
_start:
{
if (lean_obj_tag(v_t_396_) == 0)
{
lean_object* v_k_398_; lean_object* v_v_399_; lean_object* v_l_400_; lean_object* v_r_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v_k_398_ = lean_ctor_get(v_t_396_, 1);
lean_inc_n(v_k_398_, 2);
v_v_399_ = lean_ctor_get(v_t_396_, 2);
lean_inc(v_v_399_);
v_l_400_ = lean_ctor_get(v_t_396_, 3);
lean_inc(v_l_400_);
v_r_401_ = lean_ctor_get(v_t_396_, 4);
lean_inc(v_r_401_);
lean_dec_ref_known(v_t_396_, 5);
lean_inc_ref(v_inst_395_);
lean_inc(v_k_397_);
v___x_402_ = lean_apply_2(v_inst_395_, v_k_397_, v_k_398_);
v___x_403_ = lean_unbox(v___x_402_);
switch(v___x_403_)
{
case 0:
{
lean_dec(v_r_401_);
lean_dec(v_v_399_);
lean_dec(v_k_398_);
v_t_396_ = v_l_400_;
goto _start;
}
case 1:
{
lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v_r_401_);
lean_dec(v_l_400_);
lean_dec(v_k_397_);
lean_dec_ref(v_inst_395_);
v___x_405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_405_, 0, v_k_398_);
lean_ctor_set(v___x_405_, 1, v_v_399_);
v___x_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_406_, 0, v___x_405_);
return v___x_406_;
}
default: 
{
lean_dec(v_l_400_);
lean_dec(v_v_399_);
lean_dec(v_k_398_);
v_t_396_ = v_r_401_;
goto _start;
}
}
}
else
{
lean_object* v___x_408_; 
lean_dec(v_k_397_);
lean_dec_ref(v_inst_395_);
v___x_408_ = lean_box(0);
return v___x_408_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f(lean_object* v_00_u03b1_409_, lean_object* v_00_u03b2_410_, lean_object* v_inst_411_, lean_object* v_t_412_, lean_object* v_k_413_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_inst_411_, v_t_412_, v_k_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry___redArg(lean_object* v_inst_415_, lean_object* v_t_416_, lean_object* v_k_417_){
_start:
{
lean_object* v_k_418_; lean_object* v_v_419_; lean_object* v_l_420_; lean_object* v_r_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_k_418_ = lean_ctor_get(v_t_416_, 1);
lean_inc_n(v_k_418_, 2);
v_v_419_ = lean_ctor_get(v_t_416_, 2);
lean_inc(v_v_419_);
v_l_420_ = lean_ctor_get(v_t_416_, 3);
lean_inc(v_l_420_);
v_r_421_ = lean_ctor_get(v_t_416_, 4);
lean_inc(v_r_421_);
lean_dec(v_t_416_);
lean_inc_ref(v_inst_415_);
lean_inc(v_k_417_);
v___x_422_ = lean_apply_2(v_inst_415_, v_k_417_, v_k_418_);
v___x_423_ = lean_unbox(v___x_422_);
switch(v___x_423_)
{
case 0:
{
lean_dec(v_r_421_);
lean_dec(v_v_419_);
lean_dec(v_k_418_);
v_t_416_ = v_l_420_;
goto _start;
}
case 1:
{
lean_object* v___x_425_; 
lean_dec(v_r_421_);
lean_dec(v_l_420_);
lean_dec(v_k_417_);
lean_dec_ref(v_inst_415_);
v___x_425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_425_, 0, v_k_418_);
lean_ctor_set(v___x_425_, 1, v_v_419_);
return v___x_425_;
}
default: 
{
lean_dec(v_l_420_);
lean_dec(v_v_419_);
lean_dec(v_k_418_);
v_t_416_ = v_r_421_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry(lean_object* v_00_u03b1_427_, lean_object* v_00_u03b2_428_, lean_object* v_inst_429_, lean_object* v_t_430_, lean_object* v_k_431_, lean_object* v_hlk_432_){
_start:
{
lean_object* v___x_433_; 
v___x_433_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_inst_429_, v_t_430_, v_k_431_);
return v___x_433_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_435_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_436_ = lean_unsigned_to_nat(13u);
v___x_437_ = lean_unsigned_to_nat(147u);
v___x_438_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0));
v___x_439_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_440_ = l_mkPanicMessageWithDecl(v___x_439_, v___x_438_, v___x_437_, v___x_436_, v___x_435_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_t_443_, lean_object* v_k_444_){
_start:
{
if (lean_obj_tag(v_t_443_) == 0)
{
lean_object* v_k_445_; lean_object* v_v_446_; lean_object* v_l_447_; lean_object* v_r_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_k_445_ = lean_ctor_get(v_t_443_, 1);
lean_inc_n(v_k_445_, 2);
v_v_446_ = lean_ctor_get(v_t_443_, 2);
lean_inc(v_v_446_);
v_l_447_ = lean_ctor_get(v_t_443_, 3);
lean_inc(v_l_447_);
v_r_448_ = lean_ctor_get(v_t_443_, 4);
lean_inc(v_r_448_);
lean_dec_ref_known(v_t_443_, 5);
lean_inc_ref(v_inst_441_);
lean_inc(v_k_444_);
v___x_449_ = lean_apply_2(v_inst_441_, v_k_444_, v_k_445_);
v___x_450_ = lean_unbox(v___x_449_);
switch(v___x_450_)
{
case 0:
{
lean_dec(v_r_448_);
lean_dec(v_v_446_);
lean_dec(v_k_445_);
v_t_443_ = v_l_447_;
goto _start;
}
case 1:
{
lean_object* v___x_452_; 
lean_dec(v_r_448_);
lean_dec(v_l_447_);
lean_dec(v_k_444_);
lean_dec_ref(v_inst_441_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v_k_445_);
lean_ctor_set(v___x_452_, 1, v_v_446_);
return v___x_452_;
}
default: 
{
lean_dec(v_l_447_);
lean_dec(v_v_446_);
lean_dec(v_k_445_);
v_t_443_ = v_r_448_;
goto _start;
}
}
}
else
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v_k_444_);
lean_dec_ref(v_inst_441_);
v___x_454_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1);
v___x_455_ = l_panic___redArg(v_inst_442_, v___x_454_);
return v___x_455_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___boxed(lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_t_458_, lean_object* v_k_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_inst_456_, v_inst_457_, v_t_458_, v_k_459_);
lean_dec_ref(v_inst_457_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21(lean_object* v_00_u03b1_461_, lean_object* v_00_u03b2_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_t_465_, lean_object* v_k_466_){
_start:
{
lean_object* v___x_467_; 
v___x_467_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_inst_463_, v_inst_464_, v_t_465_, v_k_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___boxed(lean_object* v_00_u03b1_468_, lean_object* v_00_u03b2_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_t_472_, lean_object* v_k_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21(v_00_u03b1_468_, v_00_u03b2_469_, v_inst_470_, v_inst_471_, v_t_472_, v_k_473_);
lean_dec_ref(v_inst_471_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(lean_object* v_inst_475_, lean_object* v_t_476_, lean_object* v_k_477_, lean_object* v_fallback_478_){
_start:
{
if (lean_obj_tag(v_t_476_) == 0)
{
lean_object* v_k_479_; lean_object* v_v_480_; lean_object* v_l_481_; lean_object* v_r_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v_k_479_ = lean_ctor_get(v_t_476_, 1);
lean_inc_n(v_k_479_, 2);
v_v_480_ = lean_ctor_get(v_t_476_, 2);
lean_inc(v_v_480_);
v_l_481_ = lean_ctor_get(v_t_476_, 3);
lean_inc(v_l_481_);
v_r_482_ = lean_ctor_get(v_t_476_, 4);
lean_inc(v_r_482_);
lean_dec_ref_known(v_t_476_, 5);
lean_inc_ref(v_inst_475_);
lean_inc(v_k_477_);
v___x_483_ = lean_apply_2(v_inst_475_, v_k_477_, v_k_479_);
v___x_484_ = lean_unbox(v___x_483_);
switch(v___x_484_)
{
case 0:
{
lean_dec(v_r_482_);
lean_dec(v_v_480_);
lean_dec(v_k_479_);
v_t_476_ = v_l_481_;
goto _start;
}
case 1:
{
lean_object* v___x_486_; 
lean_dec(v_r_482_);
lean_dec(v_l_481_);
lean_dec(v_k_477_);
lean_dec_ref(v_inst_475_);
v___x_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_486_, 0, v_k_479_);
lean_ctor_set(v___x_486_, 1, v_v_480_);
return v___x_486_;
}
default: 
{
lean_dec(v_l_481_);
lean_dec(v_v_480_);
lean_dec(v_k_479_);
v_t_476_ = v_r_482_;
goto _start;
}
}
}
else
{
lean_dec(v_k_477_);
lean_dec_ref(v_inst_475_);
lean_inc_ref(v_fallback_478_);
return v_fallback_478_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg___boxed(lean_object* v_inst_488_, lean_object* v_t_489_, lean_object* v_k_490_, lean_object* v_fallback_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_488_, v_t_489_, v_k_490_, v_fallback_491_);
lean_dec_ref(v_fallback_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b2_494_, lean_object* v_inst_495_, lean_object* v_t_496_, lean_object* v_k_497_, lean_object* v_fallback_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_495_, v_t_496_, v_k_497_, v_fallback_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___boxed(lean_object* v_00_u03b1_500_, lean_object* v_00_u03b2_501_, lean_object* v_inst_502_, lean_object* v_t_503_, lean_object* v_k_504_, lean_object* v_fallback_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l_Std_DTreeMap_Internal_Impl_getEntryD(v_00_u03b1_500_, v_00_u03b2_501_, v_inst_502_, v_t_503_, v_k_504_, v_fallback_505_);
lean_dec_ref(v_fallback_505_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object* v_inst_507_, lean_object* v_t_508_, lean_object* v_k_509_){
_start:
{
if (lean_obj_tag(v_t_508_) == 0)
{
lean_object* v_k_510_; lean_object* v_l_511_; lean_object* v_r_512_; lean_object* v___x_513_; uint8_t v___x_514_; 
v_k_510_ = lean_ctor_get(v_t_508_, 1);
lean_inc_n(v_k_510_, 2);
v_l_511_ = lean_ctor_get(v_t_508_, 3);
lean_inc(v_l_511_);
v_r_512_ = lean_ctor_get(v_t_508_, 4);
lean_inc(v_r_512_);
lean_dec_ref_known(v_t_508_, 5);
lean_inc_ref(v_inst_507_);
lean_inc(v_k_509_);
v___x_513_ = lean_apply_2(v_inst_507_, v_k_509_, v_k_510_);
v___x_514_ = lean_unbox(v___x_513_);
switch(v___x_514_)
{
case 0:
{
lean_dec(v_r_512_);
lean_dec(v_k_510_);
v_t_508_ = v_l_511_;
goto _start;
}
case 1:
{
lean_object* v___x_516_; 
lean_dec(v_r_512_);
lean_dec(v_l_511_);
lean_dec(v_k_509_);
lean_dec_ref(v_inst_507_);
v___x_516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_516_, 0, v_k_510_);
return v___x_516_;
}
default: 
{
lean_dec(v_l_511_);
lean_dec(v_k_510_);
v_t_508_ = v_r_512_;
goto _start;
}
}
}
else
{
lean_object* v___x_518_; 
lean_dec(v_k_509_);
lean_dec_ref(v_inst_507_);
v___x_518_ = lean_box(0);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f(lean_object* v_00_u03b1_519_, lean_object* v_00_u03b2_520_, lean_object* v_inst_521_, lean_object* v_t_522_, lean_object* v_k_523_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_inst_521_, v_t_522_, v_k_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object* v_inst_525_, lean_object* v_t_526_, lean_object* v_k_527_){
_start:
{
lean_object* v_k_528_; lean_object* v_l_529_; lean_object* v_r_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_k_528_ = lean_ctor_get(v_t_526_, 1);
lean_inc_n(v_k_528_, 2);
v_l_529_ = lean_ctor_get(v_t_526_, 3);
lean_inc(v_l_529_);
v_r_530_ = lean_ctor_get(v_t_526_, 4);
lean_inc(v_r_530_);
lean_dec(v_t_526_);
lean_inc_ref(v_inst_525_);
lean_inc(v_k_527_);
v___x_531_ = lean_apply_2(v_inst_525_, v_k_527_, v_k_528_);
v___x_532_ = lean_unbox(v___x_531_);
switch(v___x_532_)
{
case 0:
{
lean_dec(v_r_530_);
lean_dec(v_k_528_);
v_t_526_ = v_l_529_;
goto _start;
}
case 1:
{
lean_dec(v_r_530_);
lean_dec(v_l_529_);
lean_dec(v_k_527_);
lean_dec_ref(v_inst_525_);
return v_k_528_;
}
default: 
{
lean_dec(v_l_529_);
lean_dec(v_k_528_);
v_t_526_ = v_r_530_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey(lean_object* v_00_u03b1_535_, lean_object* v_00_u03b2_536_, lean_object* v_inst_537_, lean_object* v_t_538_, lean_object* v_k_539_, lean_object* v_hlk_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_inst_537_, v_t_538_, v_k_539_);
return v___x_541_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_543_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_544_ = lean_unsigned_to_nat(13u);
v___x_545_ = lean_unsigned_to_nat(186u);
v___x_546_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0));
v___x_547_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_548_ = l_mkPanicMessageWithDecl(v___x_547_, v___x_546_, v___x_545_, v___x_544_, v___x_543_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object* v_inst_549_, lean_object* v_t_550_, lean_object* v_k_551_, lean_object* v_inst_552_){
_start:
{
if (lean_obj_tag(v_t_550_) == 0)
{
lean_object* v_k_553_; lean_object* v_l_554_; lean_object* v_r_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v_k_553_ = lean_ctor_get(v_t_550_, 1);
lean_inc_n(v_k_553_, 2);
v_l_554_ = lean_ctor_get(v_t_550_, 3);
lean_inc(v_l_554_);
v_r_555_ = lean_ctor_get(v_t_550_, 4);
lean_inc(v_r_555_);
lean_dec_ref_known(v_t_550_, 5);
lean_inc_ref(v_inst_549_);
lean_inc(v_k_551_);
v___x_556_ = lean_apply_2(v_inst_549_, v_k_551_, v_k_553_);
v___x_557_ = lean_unbox(v___x_556_);
switch(v___x_557_)
{
case 0:
{
lean_dec(v_r_555_);
lean_dec(v_k_553_);
v_t_550_ = v_l_554_;
goto _start;
}
case 1:
{
lean_dec(v_r_555_);
lean_dec(v_l_554_);
lean_dec(v_k_551_);
lean_dec_ref(v_inst_549_);
return v_k_553_;
}
default: 
{
lean_dec(v_l_554_);
lean_dec(v_k_553_);
v_t_550_ = v_r_555_;
goto _start;
}
}
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; 
lean_dec(v_k_551_);
lean_dec_ref(v_inst_549_);
v___x_560_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1);
v___x_561_ = l_panic___redArg(v_inst_552_, v___x_560_);
return v___x_561_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___boxed(lean_object* v_inst_562_, lean_object* v_t_563_, lean_object* v_k_564_, lean_object* v_inst_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_inst_562_, v_t_563_, v_k_564_, v_inst_565_);
lean_dec(v_inst_565_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21(lean_object* v_00_u03b1_567_, lean_object* v_00_u03b2_568_, lean_object* v_inst_569_, lean_object* v_t_570_, lean_object* v_k_571_, lean_object* v_inst_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_inst_569_, v_t_570_, v_k_571_, v_inst_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___boxed(lean_object* v_00_u03b1_574_, lean_object* v_00_u03b2_575_, lean_object* v_inst_576_, lean_object* v_t_577_, lean_object* v_k_578_, lean_object* v_inst_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l_Std_DTreeMap_Internal_Impl_getKey_x21(v_00_u03b1_574_, v_00_u03b2_575_, v_inst_576_, v_t_577_, v_k_578_, v_inst_579_);
lean_dec(v_inst_579_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object* v_inst_581_, lean_object* v_t_582_, lean_object* v_k_583_, lean_object* v_fallback_584_){
_start:
{
if (lean_obj_tag(v_t_582_) == 0)
{
lean_object* v_k_585_; lean_object* v_l_586_; lean_object* v_r_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_k_585_ = lean_ctor_get(v_t_582_, 1);
lean_inc_n(v_k_585_, 2);
v_l_586_ = lean_ctor_get(v_t_582_, 3);
lean_inc(v_l_586_);
v_r_587_ = lean_ctor_get(v_t_582_, 4);
lean_inc(v_r_587_);
lean_dec_ref_known(v_t_582_, 5);
lean_inc_ref(v_inst_581_);
lean_inc(v_k_583_);
v___x_588_ = lean_apply_2(v_inst_581_, v_k_583_, v_k_585_);
v___x_589_ = lean_unbox(v___x_588_);
switch(v___x_589_)
{
case 0:
{
lean_dec(v_r_587_);
lean_dec(v_k_585_);
v_t_582_ = v_l_586_;
goto _start;
}
case 1:
{
lean_dec(v_r_587_);
lean_dec(v_l_586_);
lean_dec(v_k_583_);
lean_dec_ref(v_inst_581_);
return v_k_585_;
}
default: 
{
lean_dec(v_l_586_);
lean_dec(v_k_585_);
v_t_582_ = v_r_587_;
goto _start;
}
}
}
else
{
lean_dec(v_k_583_);
lean_dec_ref(v_inst_581_);
lean_inc(v_fallback_584_);
return v_fallback_584_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg___boxed(lean_object* v_inst_592_, lean_object* v_t_593_, lean_object* v_k_594_, lean_object* v_fallback_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_592_, v_t_593_, v_k_594_, v_fallback_595_);
lean_dec(v_fallback_595_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD(lean_object* v_00_u03b1_597_, lean_object* v_00_u03b2_598_, lean_object* v_inst_599_, lean_object* v_t_600_, lean_object* v_k_601_, lean_object* v_fallback_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_599_, v_t_600_, v_k_601_, v_fallback_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___boxed(lean_object* v_00_u03b1_604_, lean_object* v_00_u03b2_605_, lean_object* v_inst_606_, lean_object* v_t_607_, lean_object* v_k_608_, lean_object* v_fallback_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Std_DTreeMap_Internal_Impl_getKeyD(v_00_u03b1_604_, v_00_u03b2_605_, v_inst_606_, v_t_607_, v_k_608_, v_fallback_609_);
lean_dec(v_fallback_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object* v_inst_611_, lean_object* v_t_612_, lean_object* v_k_613_){
_start:
{
if (lean_obj_tag(v_t_612_) == 0)
{
lean_object* v_k_614_; lean_object* v_v_615_; lean_object* v_l_616_; lean_object* v_r_617_; lean_object* v___x_618_; uint8_t v___x_619_; 
v_k_614_ = lean_ctor_get(v_t_612_, 1);
lean_inc(v_k_614_);
v_v_615_ = lean_ctor_get(v_t_612_, 2);
lean_inc(v_v_615_);
v_l_616_ = lean_ctor_get(v_t_612_, 3);
lean_inc(v_l_616_);
v_r_617_ = lean_ctor_get(v_t_612_, 4);
lean_inc(v_r_617_);
lean_dec_ref_known(v_t_612_, 5);
lean_inc_ref(v_inst_611_);
lean_inc(v_k_613_);
v___x_618_ = lean_apply_2(v_inst_611_, v_k_613_, v_k_614_);
v___x_619_ = lean_unbox(v___x_618_);
switch(v___x_619_)
{
case 0:
{
lean_dec(v_r_617_);
lean_dec(v_v_615_);
v_t_612_ = v_l_616_;
goto _start;
}
case 1:
{
lean_object* v___x_621_; 
lean_dec(v_r_617_);
lean_dec(v_l_616_);
lean_dec(v_k_613_);
lean_dec_ref(v_inst_611_);
v___x_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_621_, 0, v_v_615_);
return v___x_621_;
}
default: 
{
lean_dec(v_l_616_);
lean_dec(v_v_615_);
v_t_612_ = v_r_617_;
goto _start;
}
}
}
else
{
lean_object* v___x_623_; 
lean_dec(v_k_613_);
lean_dec_ref(v_inst_611_);
v___x_623_ = lean_box(0);
return v___x_623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f(lean_object* v_00_u03b1_624_, lean_object* v_00_u03b4_625_, lean_object* v_inst_626_, lean_object* v_t_627_, lean_object* v_k_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_inst_626_, v_t_627_, v_k_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object* v_inst_630_, lean_object* v_t_631_, lean_object* v_k_632_){
_start:
{
lean_object* v_k_633_; lean_object* v_v_634_; lean_object* v_l_635_; lean_object* v_r_636_; lean_object* v___x_637_; uint8_t v___x_638_; 
v_k_633_ = lean_ctor_get(v_t_631_, 1);
lean_inc(v_k_633_);
v_v_634_ = lean_ctor_get(v_t_631_, 2);
lean_inc(v_v_634_);
v_l_635_ = lean_ctor_get(v_t_631_, 3);
lean_inc(v_l_635_);
v_r_636_ = lean_ctor_get(v_t_631_, 4);
lean_inc(v_r_636_);
lean_dec(v_t_631_);
lean_inc_ref(v_inst_630_);
lean_inc(v_k_632_);
v___x_637_ = lean_apply_2(v_inst_630_, v_k_632_, v_k_633_);
v___x_638_ = lean_unbox(v___x_637_);
switch(v___x_638_)
{
case 0:
{
lean_dec(v_r_636_);
lean_dec(v_v_634_);
v_t_631_ = v_l_635_;
goto _start;
}
case 1:
{
lean_dec(v_r_636_);
lean_dec(v_l_635_);
lean_dec(v_k_632_);
lean_dec_ref(v_inst_630_);
return v_v_634_;
}
default: 
{
lean_dec(v_l_635_);
lean_dec(v_v_634_);
v_t_631_ = v_r_636_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get(lean_object* v_00_u03b1_641_, lean_object* v_00_u03b4_642_, lean_object* v_inst_643_, lean_object* v_t_644_, lean_object* v_k_645_, lean_object* v_hlk_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_inst_643_, v_t_644_, v_k_645_);
return v___x_647_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_649_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_650_ = lean_unsigned_to_nat(13u);
v___x_651_ = lean_unsigned_to_nat(227u);
v___x_652_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0));
v___x_653_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_654_ = l_mkPanicMessageWithDecl(v___x_653_, v___x_652_, v___x_651_, v___x_650_, v___x_649_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object* v_inst_655_, lean_object* v_inst_656_, lean_object* v_t_657_, lean_object* v_k_658_){
_start:
{
if (lean_obj_tag(v_t_657_) == 0)
{
lean_object* v_k_659_; lean_object* v_v_660_; lean_object* v_l_661_; lean_object* v_r_662_; lean_object* v___x_663_; uint8_t v___x_664_; 
v_k_659_ = lean_ctor_get(v_t_657_, 1);
lean_inc(v_k_659_);
v_v_660_ = lean_ctor_get(v_t_657_, 2);
lean_inc(v_v_660_);
v_l_661_ = lean_ctor_get(v_t_657_, 3);
lean_inc(v_l_661_);
v_r_662_ = lean_ctor_get(v_t_657_, 4);
lean_inc(v_r_662_);
lean_dec_ref_known(v_t_657_, 5);
lean_inc_ref(v_inst_655_);
lean_inc(v_k_658_);
v___x_663_ = lean_apply_2(v_inst_655_, v_k_658_, v_k_659_);
v___x_664_ = lean_unbox(v___x_663_);
switch(v___x_664_)
{
case 0:
{
lean_dec(v_r_662_);
lean_dec(v_v_660_);
v_t_657_ = v_l_661_;
goto _start;
}
case 1:
{
lean_dec(v_r_662_);
lean_dec(v_l_661_);
lean_dec(v_k_658_);
lean_dec_ref(v_inst_655_);
return v_v_660_;
}
default: 
{
lean_dec(v_l_661_);
lean_dec(v_v_660_);
v_t_657_ = v_r_662_;
goto _start;
}
}
}
else
{
lean_object* v___x_667_; lean_object* v___x_668_; 
lean_dec(v_k_658_);
lean_dec_ref(v_inst_655_);
v___x_667_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1);
v___x_668_ = l_panic___redArg(v_inst_656_, v___x_667_);
return v___x_668_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___boxed(lean_object* v_inst_669_, lean_object* v_inst_670_, lean_object* v_t_671_, lean_object* v_k_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_inst_669_, v_inst_670_, v_t_671_, v_k_672_);
lean_dec(v_inst_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21(lean_object* v_00_u03b1_674_, lean_object* v_00_u03b4_675_, lean_object* v_inst_676_, lean_object* v_inst_677_, lean_object* v_t_678_, lean_object* v_k_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_inst_676_, v_inst_677_, v_t_678_, v_k_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___boxed(lean_object* v_00_u03b1_681_, lean_object* v_00_u03b4_682_, lean_object* v_inst_683_, lean_object* v_inst_684_, lean_object* v_t_685_, lean_object* v_k_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21(v_00_u03b1_681_, v_00_u03b4_682_, v_inst_683_, v_inst_684_, v_t_685_, v_k_686_);
lean_dec(v_inst_684_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object* v_inst_688_, lean_object* v_t_689_, lean_object* v_k_690_, lean_object* v_fallback_691_){
_start:
{
if (lean_obj_tag(v_t_689_) == 0)
{
lean_object* v_k_692_; lean_object* v_v_693_; lean_object* v_l_694_; lean_object* v_r_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v_k_692_ = lean_ctor_get(v_t_689_, 1);
lean_inc(v_k_692_);
v_v_693_ = lean_ctor_get(v_t_689_, 2);
lean_inc(v_v_693_);
v_l_694_ = lean_ctor_get(v_t_689_, 3);
lean_inc(v_l_694_);
v_r_695_ = lean_ctor_get(v_t_689_, 4);
lean_inc(v_r_695_);
lean_dec_ref_known(v_t_689_, 5);
lean_inc_ref(v_inst_688_);
lean_inc(v_k_690_);
v___x_696_ = lean_apply_2(v_inst_688_, v_k_690_, v_k_692_);
v___x_697_ = lean_unbox(v___x_696_);
switch(v___x_697_)
{
case 0:
{
lean_dec(v_r_695_);
lean_dec(v_v_693_);
v_t_689_ = v_l_694_;
goto _start;
}
case 1:
{
lean_dec(v_r_695_);
lean_dec(v_l_694_);
lean_dec(v_k_690_);
lean_dec_ref(v_inst_688_);
return v_v_693_;
}
default: 
{
lean_dec(v_l_694_);
lean_dec(v_v_693_);
v_t_689_ = v_r_695_;
goto _start;
}
}
}
else
{
lean_dec(v_k_690_);
lean_dec_ref(v_inst_688_);
lean_inc(v_fallback_691_);
return v_fallback_691_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg___boxed(lean_object* v_inst_700_, lean_object* v_t_701_, lean_object* v_k_702_, lean_object* v_fallback_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_700_, v_t_701_, v_k_702_, v_fallback_703_);
lean_dec(v_fallback_703_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD(lean_object* v_00_u03b1_705_, lean_object* v_00_u03b4_706_, lean_object* v_inst_707_, lean_object* v_t_708_, lean_object* v_k_709_, lean_object* v_fallback_710_){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_707_, v_t_708_, v_k_709_, v_fallback_710_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___boxed(lean_object* v_00_u03b1_712_, lean_object* v_00_u03b4_713_, lean_object* v_inst_714_, lean_object* v_t_715_, lean_object* v_k_716_, lean_object* v_fallback_717_){
_start:
{
lean_object* v_res_718_; 
v_res_718_ = l_Std_DTreeMap_Internal_Impl_Const_getD(v_00_u03b1_712_, v_00_u03b4_713_, v_inst_714_, v_t_715_, v_k_716_, v_fallback_717_);
lean_dec(v_fallback_717_);
return v_res_718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1(lean_object* v_f_719_, lean_object* v_k_720_, lean_object* v_v_721_, lean_object* v_toBind_722_, lean_object* v___f_723_, lean_object* v_left_724_){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; 
v___x_725_ = lean_apply_3(v_f_719_, v_left_724_, v_k_720_, v_v_721_);
v___x_726_ = lean_apply_4(v_toBind_722_, lean_box(0), lean_box(0), v___x_725_, v___f_723_);
return v___x_726_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object* v_inst_727_, lean_object* v_f_728_, lean_object* v_init_729_, lean_object* v_x_730_){
_start:
{
if (lean_obj_tag(v_x_730_) == 0)
{
lean_object* v_toBind_731_; lean_object* v_k_732_; lean_object* v_v_733_; lean_object* v_l_734_; lean_object* v_r_735_; lean_object* v___f_736_; lean_object* v___f_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v_toBind_731_ = lean_ctor_get(v_inst_727_, 1);
lean_inc_n(v_toBind_731_, 2);
v_k_732_ = lean_ctor_get(v_x_730_, 1);
lean_inc(v_k_732_);
v_v_733_ = lean_ctor_get(v_x_730_, 2);
lean_inc(v_v_733_);
v_l_734_ = lean_ctor_get(v_x_730_, 3);
lean_inc(v_l_734_);
v_r_735_ = lean_ctor_get(v_x_730_, 4);
lean_inc(v_r_735_);
lean_dec_ref_known(v_x_730_, 5);
lean_inc_n(v_f_728_, 2);
lean_inc_ref(v_inst_727_);
v___f_736_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_736_, 0, v_inst_727_);
lean_closure_set(v___f_736_, 1, v_f_728_);
lean_closure_set(v___f_736_, 2, v_r_735_);
v___f_737_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_737_, 0, v_f_728_);
lean_closure_set(v___f_737_, 1, v_k_732_);
lean_closure_set(v___f_737_, 2, v_v_733_);
lean_closure_set(v___f_737_, 3, v_toBind_731_);
lean_closure_set(v___f_737_, 4, v___f_736_);
v___x_738_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_727_, v_f_728_, v_init_729_, v_l_734_);
v___x_739_ = lean_apply_4(v_toBind_731_, lean_box(0), lean_box(0), v___x_738_, v___f_737_);
return v___x_739_;
}
else
{
lean_object* v_toApplicative_740_; lean_object* v_toPure_741_; lean_object* v___x_742_; 
v_toApplicative_740_ = lean_ctor_get(v_inst_727_, 0);
lean_inc_ref(v_toApplicative_740_);
lean_dec(v_f_728_);
lean_dec_ref(v_inst_727_);
v_toPure_741_ = lean_ctor_get(v_toApplicative_740_, 1);
lean_inc(v_toPure_741_);
lean_dec_ref(v_toApplicative_740_);
v___x_742_ = lean_apply_2(v_toPure_741_, lean_box(0), v_init_729_);
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0(lean_object* v_inst_743_, lean_object* v_f_744_, lean_object* v_r_745_, lean_object* v_middle_746_){
_start:
{
lean_object* v___x_747_; 
v___x_747_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_743_, v_f_744_, v_middle_746_, v_r_745_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM(lean_object* v_00_u03b1_748_, lean_object* v_00_u03b2_749_, lean_object* v_00_u03b4_750_, lean_object* v_m_751_, lean_object* v_inst_752_, lean_object* v_f_753_, lean_object* v_init_754_, lean_object* v_x_755_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_752_, v_f_753_, v_init_754_, v_x_755_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0(lean_object* v_f_757_, lean_object* v_x1_758_, lean_object* v_x2_759_, lean_object* v_x3_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = lean_apply_3(v_f_757_, v_x1_758_, v_x2_759_, v_x3_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object* v_f_781_, lean_object* v_init_782_, lean_object* v_t_783_){
_start:
{
lean_object* v___f_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___f_784_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_784_, 0, v_f_781_);
v___x_785_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_786_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_785_, v___f_784_, v_init_782_, v_t_783_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl(lean_object* v_00_u03b1_787_, lean_object* v_00_u03b2_788_, lean_object* v_00_u03b4_789_, lean_object* v_f_790_, lean_object* v_init_791_, lean_object* v_t_792_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_790_, v_init_791_, v_t_792_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1(lean_object* v_f_794_, lean_object* v_k_795_, lean_object* v_v_796_, lean_object* v_toBind_797_, lean_object* v___f_798_, lean_object* v_right_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = lean_apply_3(v_f_794_, v_k_795_, v_v_796_, v_right_799_);
v___x_801_ = lean_apply_4(v_toBind_797_, lean_box(0), lean_box(0), v___x_800_, v___f_798_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object* v_inst_802_, lean_object* v_f_803_, lean_object* v_init_804_, lean_object* v_x_805_){
_start:
{
if (lean_obj_tag(v_x_805_) == 0)
{
lean_object* v_toBind_806_; lean_object* v_k_807_; lean_object* v_v_808_; lean_object* v_l_809_; lean_object* v_r_810_; lean_object* v___f_811_; lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v_toBind_806_ = lean_ctor_get(v_inst_802_, 1);
lean_inc_n(v_toBind_806_, 2);
v_k_807_ = lean_ctor_get(v_x_805_, 1);
lean_inc(v_k_807_);
v_v_808_ = lean_ctor_get(v_x_805_, 2);
lean_inc(v_v_808_);
v_l_809_ = lean_ctor_get(v_x_805_, 3);
lean_inc(v_l_809_);
v_r_810_ = lean_ctor_get(v_x_805_, 4);
lean_inc(v_r_810_);
lean_dec_ref_known(v_x_805_, 5);
lean_inc_n(v_f_803_, 2);
lean_inc_ref(v_inst_802_);
v___f_811_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_811_, 0, v_inst_802_);
lean_closure_set(v___f_811_, 1, v_f_803_);
lean_closure_set(v___f_811_, 2, v_l_809_);
v___f_812_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_812_, 0, v_f_803_);
lean_closure_set(v___f_812_, 1, v_k_807_);
lean_closure_set(v___f_812_, 2, v_v_808_);
lean_closure_set(v___f_812_, 3, v_toBind_806_);
lean_closure_set(v___f_812_, 4, v___f_811_);
v___x_813_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_802_, v_f_803_, v_init_804_, v_r_810_);
v___x_814_ = lean_apply_4(v_toBind_806_, lean_box(0), lean_box(0), v___x_813_, v___f_812_);
return v___x_814_;
}
else
{
lean_object* v_toApplicative_815_; lean_object* v_toPure_816_; lean_object* v___x_817_; 
v_toApplicative_815_ = lean_ctor_get(v_inst_802_, 0);
lean_inc_ref(v_toApplicative_815_);
lean_dec(v_f_803_);
lean_dec_ref(v_inst_802_);
v_toPure_816_ = lean_ctor_get(v_toApplicative_815_, 1);
lean_inc(v_toPure_816_);
lean_dec_ref(v_toApplicative_815_);
v___x_817_ = lean_apply_2(v_toPure_816_, lean_box(0), v_init_804_);
return v___x_817_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0(lean_object* v_inst_818_, lean_object* v_f_819_, lean_object* v_l_820_, lean_object* v_middle_821_){
_start:
{
lean_object* v___x_822_; 
v___x_822_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_818_, v_f_819_, v_middle_821_, v_l_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_00_u03b4_825_, lean_object* v_m_826_, lean_object* v_inst_827_, lean_object* v_f_828_, lean_object* v_init_829_, lean_object* v_x_830_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_827_, v_f_828_, v_init_829_, v_x_830_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr___redArg(lean_object* v_f_832_, lean_object* v_init_833_, lean_object* v_t_834_){
_start:
{
lean_object* v___f_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___f_835_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_835_, 0, v_f_832_);
v___x_836_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_837_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_836_, v___f_835_, v_init_833_, v_t_834_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr(lean_object* v_00_u03b1_838_, lean_object* v_00_u03b2_839_, lean_object* v_00_u03b4_840_, lean_object* v_f_841_, lean_object* v_init_842_, lean_object* v_t_843_){
_start:
{
lean_object* v___f_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___f_844_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_844_, 0, v_f_841_);
v___x_845_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_846_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_845_, v___f_844_, v_init_842_, v_t_843_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0(lean_object* v_f_847_, lean_object* v_x_848_, lean_object* v_k_849_, lean_object* v_v_850_){
_start:
{
lean_object* v___x_851_; 
v___x_851_ = lean_apply_2(v_f_847_, v_k_849_, v_v_850_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg(lean_object* v_inst_852_, lean_object* v_f_853_, lean_object* v_t_854_){
_start:
{
lean_object* v___f_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___f_855_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_855_, 0, v_f_853_);
v___x_856_ = lean_box(0);
v___x_857_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_852_, v___f_855_, v___x_856_, v_t_854_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM(lean_object* v_00_u03b1_858_, lean_object* v_00_u03b2_859_, lean_object* v_m_860_, lean_object* v_inst_861_, lean_object* v_f_862_, lean_object* v_t_863_){
_start:
{
lean_object* v___f_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___f_864_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_864_, 0, v_f_862_);
v___x_865_ = lean_box(0);
v___x_866_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_861_, v___f_864_, v___x_865_, v_t_863_);
return v___x_866_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0(lean_object* v_toPure_867_, lean_object* v_d_868_){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_869_, 0, v_d_868_);
v___x_870_ = lean_apply_2(v_toPure_867_, lean_box(0), v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2(lean_object* v___f_871_, lean_object* v_f_872_, lean_object* v_k_873_, lean_object* v_v_874_, lean_object* v_toBind_875_, lean_object* v___f_876_, lean_object* v_____do__lift_877_){
_start:
{
if (lean_obj_tag(v_____do__lift_877_) == 0)
{
lean_object* v_a_878_; lean_object* v___x_879_; 
lean_dec(v___f_876_);
lean_dec(v_toBind_875_);
lean_dec(v_v_874_);
lean_dec(v_k_873_);
lean_dec(v_f_872_);
v_a_878_ = lean_ctor_get(v_____do__lift_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v_____do__lift_877_, 1);
v___x_879_ = lean_apply_1(v___f_871_, v_a_878_);
return v___x_879_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v___x_882_; 
lean_dec(v___f_871_);
v_a_880_ = lean_ctor_get(v_____do__lift_877_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v_____do__lift_877_, 1);
v___x_881_ = lean_apply_3(v_f_872_, v_k_873_, v_v_874_, v_a_880_);
v___x_882_ = lean_apply_4(v_toBind_875_, lean_box(0), lean_box(0), v___x_881_, v___f_876_);
return v___x_882_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object* v_inst_883_, lean_object* v_f_884_, lean_object* v_init_885_, lean_object* v_x_886_){
_start:
{
if (lean_obj_tag(v_x_886_) == 0)
{
lean_object* v_toApplicative_887_; lean_object* v_toBind_888_; lean_object* v_toPure_889_; lean_object* v_k_890_; lean_object* v_v_891_; lean_object* v_l_892_; lean_object* v_r_893_; lean_object* v___f_894_; lean_object* v___f_895_; lean_object* v___f_896_; lean_object* v___x_897_; lean_object* v___x_898_; 
v_toApplicative_887_ = lean_ctor_get(v_inst_883_, 0);
v_toBind_888_ = lean_ctor_get(v_inst_883_, 1);
lean_inc_n(v_toBind_888_, 2);
v_toPure_889_ = lean_ctor_get(v_toApplicative_887_, 1);
v_k_890_ = lean_ctor_get(v_x_886_, 1);
lean_inc(v_k_890_);
v_v_891_ = lean_ctor_get(v_x_886_, 2);
lean_inc(v_v_891_);
v_l_892_ = lean_ctor_get(v_x_886_, 3);
lean_inc(v_l_892_);
v_r_893_ = lean_ctor_get(v_x_886_, 4);
lean_inc(v_r_893_);
lean_dec_ref_known(v_x_886_, 5);
lean_inc(v_toPure_889_);
v___f_894_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0), 2, 1);
lean_closure_set(v___f_894_, 0, v_toPure_889_);
lean_inc_n(v_f_884_, 2);
lean_inc_ref(v_inst_883_);
lean_inc_ref(v___f_894_);
v___f_895_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1), 5, 4);
lean_closure_set(v___f_895_, 0, v___f_894_);
lean_closure_set(v___f_895_, 1, v_inst_883_);
lean_closure_set(v___f_895_, 2, v_f_884_);
lean_closure_set(v___f_895_, 3, v_r_893_);
v___f_896_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2), 7, 6);
lean_closure_set(v___f_896_, 0, v___f_894_);
lean_closure_set(v___f_896_, 1, v_f_884_);
lean_closure_set(v___f_896_, 2, v_k_890_);
lean_closure_set(v___f_896_, 3, v_v_891_);
lean_closure_set(v___f_896_, 4, v_toBind_888_);
lean_closure_set(v___f_896_, 5, v___f_895_);
v___x_897_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_883_, v_f_884_, v_init_885_, v_l_892_);
v___x_898_ = lean_apply_4(v_toBind_888_, lean_box(0), lean_box(0), v___x_897_, v___f_896_);
return v___x_898_;
}
else
{
lean_object* v_toApplicative_899_; lean_object* v_toPure_900_; lean_object* v___x_901_; lean_object* v___x_902_; 
v_toApplicative_899_ = lean_ctor_get(v_inst_883_, 0);
lean_inc_ref(v_toApplicative_899_);
lean_dec(v_f_884_);
lean_dec_ref(v_inst_883_);
v_toPure_900_ = lean_ctor_get(v_toApplicative_899_, 1);
lean_inc(v_toPure_900_);
lean_dec_ref(v_toApplicative_899_);
v___x_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_901_, 0, v_init_885_);
v___x_902_ = lean_apply_2(v_toPure_900_, lean_box(0), v___x_901_);
return v___x_902_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1(lean_object* v___f_903_, lean_object* v_inst_904_, lean_object* v_f_905_, lean_object* v_r_906_, lean_object* v_____do__lift_907_){
_start:
{
if (lean_obj_tag(v_____do__lift_907_) == 0)
{
lean_object* v_a_908_; lean_object* v___x_909_; 
lean_dec(v_r_906_);
lean_dec(v_f_905_);
lean_dec_ref(v_inst_904_);
v_a_908_ = lean_ctor_get(v_____do__lift_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v_____do__lift_907_, 1);
v___x_909_ = lean_apply_1(v___f_903_, v_a_908_);
return v___x_909_;
}
else
{
lean_object* v_a_910_; lean_object* v___x_911_; 
lean_dec(v___f_903_);
v_a_910_ = lean_ctor_get(v_____do__lift_907_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v_____do__lift_907_, 1);
v___x_911_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_904_, v_f_905_, v_a_910_, v_r_906_);
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep(lean_object* v_00_u03b1_912_, lean_object* v_00_u03b2_913_, lean_object* v_00_u03b4_914_, lean_object* v_m_915_, lean_object* v_inst_916_, lean_object* v_f_917_, lean_object* v_init_918_, lean_object* v_x_919_){
_start:
{
lean_object* v___x_920_; 
v___x_920_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_916_, v_f_917_, v_init_918_, v_x_919_);
return v___x_920_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0(lean_object* v_toPure_921_, lean_object* v_____do__lift_922_){
_start:
{
lean_object* v_a_923_; lean_object* v___x_924_; 
v_a_923_ = lean_ctor_get(v_____do__lift_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref(v_____do__lift_922_);
v___x_924_ = lean_apply_2(v_toPure_921_, lean_box(0), v_a_923_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg(lean_object* v_inst_925_, lean_object* v_f_926_, lean_object* v_init_927_, lean_object* v_t_928_){
_start:
{
lean_object* v_toApplicative_929_; lean_object* v_toBind_930_; lean_object* v_toPure_931_; lean_object* v___x_932_; lean_object* v___f_933_; lean_object* v___x_934_; 
v_toApplicative_929_ = lean_ctor_get(v_inst_925_, 0);
v_toBind_930_ = lean_ctor_get(v_inst_925_, 1);
lean_inc(v_toBind_930_);
v_toPure_931_ = lean_ctor_get(v_toApplicative_929_, 1);
lean_inc(v_toPure_931_);
v___x_932_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_925_, v_f_926_, v_init_927_, v_t_928_);
v___f_933_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_933_, 0, v_toPure_931_);
v___x_934_ = lean_apply_4(v_toBind_930_, lean_box(0), lean_box(0), v___x_932_, v___f_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn(lean_object* v_00_u03b1_935_, lean_object* v_00_u03b2_936_, lean_object* v_00_u03b4_937_, lean_object* v_m_938_, lean_object* v_inst_939_, lean_object* v_f_940_, lean_object* v_init_941_, lean_object* v_t_942_){
_start:
{
lean_object* v_toApplicative_943_; lean_object* v_toBind_944_; lean_object* v_toPure_945_; lean_object* v___x_946_; lean_object* v___f_947_; lean_object* v___x_948_; 
v_toApplicative_943_ = lean_ctor_get(v_inst_939_, 0);
v_toBind_944_ = lean_ctor_get(v_inst_939_, 1);
lean_inc(v_toBind_944_);
v_toPure_945_ = lean_ctor_get(v_toApplicative_943_, 1);
lean_inc(v_toPure_945_);
v___x_946_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_939_, v_f_940_, v_init_941_, v_t_942_);
v___f_947_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_947_, 0, v_toPure_945_);
v___x_948_ = lean_apply_4(v_toBind_944_, lean_box(0), lean_box(0), v___x_946_, v___f_947_);
return v___x_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_949_, lean_object* v_a_950_, lean_object* v_b_951_, lean_object* v_acc_952_){
_start:
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_a_950_);
lean_ctor_set(v___x_953_, 1, v_b_951_);
v___x_954_ = lean_apply_2(v_f_949_, v___x_953_, v_acc_952_);
return v___x_954_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_955_, lean_object* v_00_u03b2_956_, lean_object* v_m_957_, lean_object* v_init_958_, lean_object* v_f_959_){
_start:
{
lean_object* v_toApplicative_960_; lean_object* v_toBind_961_; lean_object* v_toPure_962_; lean_object* v___f_963_; lean_object* v___x_964_; lean_object* v___f_965_; lean_object* v___x_966_; 
v_toApplicative_960_ = lean_ctor_get(v_inst_955_, 0);
v_toBind_961_ = lean_ctor_get(v_inst_955_, 1);
lean_inc(v_toBind_961_);
v_toPure_962_ = lean_ctor_get(v_toApplicative_960_, 1);
lean_inc(v_toPure_962_);
v___f_963_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_963_, 0, v_f_959_);
v___x_964_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_955_, v___f_963_, v_init_958_, v_m_957_);
v___f_965_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_965_, 0, v_toPure_962_);
v___x_966_ = lean_apply_4(v_toBind_961_, lean_box(0), lean_box(0), v___x_964_, v___f_965_);
return v___x_966_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg(lean_object* v_inst_967_){
_start:
{
lean_object* v___f_968_; 
v___f_968_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_968_, 0, v_inst_967_);
return v___f_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad(lean_object* v_00_u03b1_969_, lean_object* v_00_u03b2_970_, lean_object* v_m_971_, lean_object* v_inst_972_){
_start:
{
lean_object* v___f_973_; 
v___f_973_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_973_, 0, v_inst_972_);
return v___f_973_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(lean_object* v_p_974_, lean_object* v___x_975_, lean_object* v___x_976_, lean_object* v_a_977_, lean_object* v_b_978_, lean_object* v_acc_979_){
_start:
{
lean_object* v___x_980_; uint8_t v___x_981_; 
v___x_980_ = lean_apply_2(v_p_974_, v_a_977_, v_b_978_);
v___x_981_ = lean_unbox(v___x_980_);
if (v___x_981_ == 0)
{
lean_object* v___x_982_; 
v___x_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_975_);
return v___x_982_;
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
lean_dec_ref(v___x_975_);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_980_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v___x_976_);
v___x_985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed(lean_object* v_p_986_, lean_object* v___x_987_, lean_object* v___x_988_, lean_object* v_a_989_, lean_object* v_b_990_, lean_object* v_acc_991_){
_start:
{
lean_object* v_res_992_; 
v_res_992_ = l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(v_p_986_, v___x_987_, v___x_988_, v_a_989_, v_b_990_, v_acc_991_);
lean_dec_ref(v_acc_991_);
return v_res_992_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any___redArg(lean_object* v_t_996_, lean_object* v_p_997_){
_start:
{
lean_object* v___y_999_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___f_1007_; lean_object* v___x_1008_; lean_object* v_a_1009_; 
v___x_1004_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1005_ = lean_box(0);
v___x_1006_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1007_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1007_, 0, v_p_997_);
lean_closure_set(v___f_1007_, 1, v___x_1006_);
lean_closure_set(v___f_1007_, 2, v___x_1005_);
v___x_1008_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1004_, v___f_1007_, v___x_1006_, v_t_996_);
v_a_1009_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_a_1009_);
lean_dec(v___x_1008_);
v___y_999_ = v_a_1009_;
goto v___jp_998_;
v___jp_998_:
{
lean_object* v_fst_1000_; 
v_fst_1000_ = lean_ctor_get(v___y_999_, 0);
lean_inc(v_fst_1000_);
lean_dec_ref(v___y_999_);
if (lean_obj_tag(v_fst_1000_) == 0)
{
uint8_t v___x_1001_; 
v___x_1001_ = 0;
return v___x_1001_;
}
else
{
lean_object* v_val_1002_; uint8_t v___x_1003_; 
v_val_1002_ = lean_ctor_get(v_fst_1000_, 0);
lean_inc(v_val_1002_);
lean_dec_ref_known(v_fst_1000_, 1);
v___x_1003_ = lean_unbox(v_val_1002_);
lean_dec(v_val_1002_);
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___boxed(lean_object* v_t_1010_, lean_object* v_p_1011_){
_start:
{
uint8_t v_res_1012_; lean_object* v_r_1013_; 
v_res_1012_ = l_Std_DTreeMap_Internal_Impl_any___redArg(v_t_1010_, v_p_1011_);
v_r_1013_ = lean_box(v_res_1012_);
return v_r_1013_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any(lean_object* v_00_u03b1_1014_, lean_object* v_00_u03b2_1015_, lean_object* v_t_1016_, lean_object* v_p_1017_){
_start:
{
lean_object* v___y_1019_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___f_1027_; lean_object* v___x_1028_; lean_object* v_a_1029_; 
v___x_1024_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1025_ = lean_box(0);
v___x_1026_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1027_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1027_, 0, v_p_1017_);
lean_closure_set(v___f_1027_, 1, v___x_1026_);
lean_closure_set(v___f_1027_, 2, v___x_1025_);
v___x_1028_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1024_, v___f_1027_, v___x_1026_, v_t_1016_);
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec(v___x_1028_);
v___y_1019_ = v_a_1029_;
goto v___jp_1018_;
v___jp_1018_:
{
lean_object* v_fst_1020_; 
v_fst_1020_ = lean_ctor_get(v___y_1019_, 0);
lean_inc(v_fst_1020_);
lean_dec_ref(v___y_1019_);
if (lean_obj_tag(v_fst_1020_) == 0)
{
uint8_t v___x_1021_; 
v___x_1021_ = 0;
return v___x_1021_;
}
else
{
lean_object* v_val_1022_; uint8_t v___x_1023_; 
v_val_1022_ = lean_ctor_get(v_fst_1020_, 0);
lean_inc(v_val_1022_);
lean_dec_ref_known(v_fst_1020_, 1);
v___x_1023_ = lean_unbox(v_val_1022_);
lean_dec(v_val_1022_);
return v___x_1023_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___boxed(lean_object* v_00_u03b1_1030_, lean_object* v_00_u03b2_1031_, lean_object* v_t_1032_, lean_object* v_p_1033_){
_start:
{
uint8_t v_res_1034_; lean_object* v_r_1035_; 
v_res_1034_ = l_Std_DTreeMap_Internal_Impl_any(v_00_u03b1_1030_, v_00_u03b2_1031_, v_t_1032_, v_p_1033_);
v_r_1035_ = lean_box(v_res_1034_);
return v_r_1035_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(lean_object* v_p_1036_, lean_object* v___x_1037_, lean_object* v___x_1038_, lean_object* v_a_1039_, lean_object* v_b_1040_, lean_object* v_acc_1041_){
_start:
{
lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1042_ = lean_apply_2(v_p_1036_, v_a_1039_, v_b_1040_);
v___x_1043_ = lean_unbox(v___x_1042_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec_ref(v___x_1038_);
v___x_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
v___x_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v___x_1037_);
v___x_1046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1046_, 0, v___x_1045_);
return v___x_1046_;
}
else
{
lean_object* v___x_1047_; 
v___x_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1038_);
return v___x_1047_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed(lean_object* v_p_1048_, lean_object* v___x_1049_, lean_object* v___x_1050_, lean_object* v_a_1051_, lean_object* v_b_1052_, lean_object* v_acc_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(v_p_1048_, v___x_1049_, v___x_1050_, v_a_1051_, v_b_1052_, v_acc_1053_);
lean_dec_ref(v_acc_1053_);
return v_res_1054_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all___redArg(lean_object* v_t_1055_, lean_object* v_p_1056_){
_start:
{
lean_object* v___y_1058_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___f_1066_; lean_object* v___x_1067_; lean_object* v_a_1068_; 
v___x_1063_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1064_ = lean_box(0);
v___x_1065_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1066_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1066_, 0, v_p_1056_);
lean_closure_set(v___f_1066_, 1, v___x_1064_);
lean_closure_set(v___f_1066_, 2, v___x_1065_);
v___x_1067_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1063_, v___f_1066_, v___x_1065_, v_t_1055_);
v_a_1068_ = lean_ctor_get(v___x_1067_, 0);
lean_inc(v_a_1068_);
lean_dec(v___x_1067_);
v___y_1058_ = v_a_1068_;
goto v___jp_1057_;
v___jp_1057_:
{
lean_object* v_fst_1059_; 
v_fst_1059_ = lean_ctor_get(v___y_1058_, 0);
lean_inc(v_fst_1059_);
lean_dec_ref(v___y_1058_);
if (lean_obj_tag(v_fst_1059_) == 0)
{
uint8_t v___x_1060_; 
v___x_1060_ = 1;
return v___x_1060_;
}
else
{
lean_object* v_val_1061_; uint8_t v___x_1062_; 
v_val_1061_ = lean_ctor_get(v_fst_1059_, 0);
lean_inc(v_val_1061_);
lean_dec_ref_known(v_fst_1059_, 1);
v___x_1062_ = lean_unbox(v_val_1061_);
lean_dec(v_val_1061_);
return v___x_1062_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___boxed(lean_object* v_t_1069_, lean_object* v_p_1070_){
_start:
{
uint8_t v_res_1071_; lean_object* v_r_1072_; 
v_res_1071_ = l_Std_DTreeMap_Internal_Impl_all___redArg(v_t_1069_, v_p_1070_);
v_r_1072_ = lean_box(v_res_1071_);
return v_r_1072_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all(lean_object* v_00_u03b1_1073_, lean_object* v_00_u03b2_1074_, lean_object* v_t_1075_, lean_object* v_p_1076_){
_start:
{
lean_object* v___y_1078_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___f_1086_; lean_object* v___x_1087_; lean_object* v_a_1088_; 
v___x_1083_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1084_ = lean_box(0);
v___x_1085_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1086_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1086_, 0, v_p_1076_);
lean_closure_set(v___f_1086_, 1, v___x_1084_);
lean_closure_set(v___f_1086_, 2, v___x_1085_);
v___x_1087_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1083_, v___f_1086_, v___x_1085_, v_t_1075_);
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec(v___x_1087_);
v___y_1078_ = v_a_1088_;
goto v___jp_1077_;
v___jp_1077_:
{
lean_object* v_fst_1079_; 
v_fst_1079_ = lean_ctor_get(v___y_1078_, 0);
lean_inc(v_fst_1079_);
lean_dec_ref(v___y_1078_);
if (lean_obj_tag(v_fst_1079_) == 0)
{
uint8_t v___x_1080_; 
v___x_1080_ = 1;
return v___x_1080_;
}
else
{
lean_object* v_val_1081_; uint8_t v___x_1082_; 
v_val_1081_ = lean_ctor_get(v_fst_1079_, 0);
lean_inc(v_val_1081_);
lean_dec_ref_known(v_fst_1079_, 1);
v___x_1082_ = lean_unbox(v_val_1081_);
lean_dec(v_val_1081_);
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___boxed(lean_object* v_00_u03b1_1089_, lean_object* v_00_u03b2_1090_, lean_object* v_t_1091_, lean_object* v_p_1092_){
_start:
{
uint8_t v_res_1093_; lean_object* v_r_1094_; 
v_res_1093_ = l_Std_DTreeMap_Internal_Impl_all(v_00_u03b1_1089_, v_00_u03b2_1090_, v_t_1091_, v_p_1092_);
v_r_1094_ = lean_box(v_res_1093_);
return v_r_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(lean_object* v_x1_1095_, lean_object* v_x2_1096_, lean_object* v_x3_1097_){
_start:
{
lean_object* v___x_1098_; 
v___x_1098_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1098_, 0, v_x1_1095_);
lean_ctor_set(v___x_1098_, 1, v_x3_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0___boxed(lean_object* v_x1_1099_, lean_object* v_x2_1100_, lean_object* v_x3_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(v_x1_1099_, v_x2_1100_, v_x3_1101_);
lean_dec(v_x2_1100_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg(lean_object* v_t_1104_){
_start:
{
lean_object* v___f_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___f_1105_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1106_ = lean_box(0);
v___x_1107_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1108_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1107_, v___f_1105_, v___x_1106_, v_t_1104_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys(lean_object* v_00_u03b1_1109_, lean_object* v_00_u03b2_1110_, lean_object* v_t_1111_){
_start:
{
lean_object* v___f_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___f_1112_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1113_ = lean_box(0);
v___x_1114_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1115_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1114_, v___f_1112_, v___x_1113_, v_t_1111_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(lean_object* v_l_1116_, lean_object* v_k_1117_, lean_object* v_x_1118_){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_array_push(v_l_1116_, v_k_1117_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0___boxed(lean_object* v_l_1120_, lean_object* v_k_1121_, lean_object* v_x_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(v_l_1120_, v_k_1121_, v_x_1122_);
lean_dec(v_x_1122_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg(lean_object* v_t_1125_){
_start:
{
lean_object* v___f_1126_; lean_object* v___y_1128_; 
v___f_1126_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1125_) == 0)
{
lean_object* v_size_1131_; 
v_size_1131_ = lean_ctor_get(v_t_1125_, 0);
lean_inc(v_size_1131_);
v___y_1128_ = v_size_1131_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___y_1128_ = v___x_1132_;
goto v___jp_1127_;
}
v___jp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_mk_empty_array_with_capacity(v___y_1128_);
lean_dec(v___y_1128_);
v___x_1130_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1126_, v___x_1129_, v_t_1125_);
return v___x_1130_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray(lean_object* v_00_u03b1_1133_, lean_object* v_00_u03b2_1134_, lean_object* v_t_1135_){
_start:
{
lean_object* v___f_1136_; lean_object* v___y_1138_; 
v___f_1136_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1135_) == 0)
{
lean_object* v_size_1141_; 
v_size_1141_ = lean_ctor_get(v_t_1135_, 0);
lean_inc(v_size_1141_);
v___y_1138_ = v_size_1141_;
goto v___jp_1137_;
}
else
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_unsigned_to_nat(0u);
v___y_1138_ = v___x_1142_;
goto v___jp_1137_;
}
v___jp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1139_ = lean_mk_empty_array_with_capacity(v___y_1138_);
lean_dec(v___y_1138_);
v___x_1140_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1136_, v___x_1139_, v_t_1135_);
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(lean_object* v_x1_1143_, lean_object* v_x2_1144_, lean_object* v_x3_1145_){
_start:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1146_, 0, v_x2_1144_);
lean_ctor_set(v___x_1146_, 1, v_x3_1145_);
return v___x_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0___boxed(lean_object* v_x1_1147_, lean_object* v_x2_1148_, lean_object* v_x3_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(v_x1_1147_, v_x2_1148_, v_x3_1149_);
lean_dec(v_x1_1147_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg(lean_object* v_t_1152_){
_start:
{
lean_object* v___f_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___f_1153_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1154_ = lean_box(0);
v___x_1155_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1156_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1155_, v___f_1153_, v___x_1154_, v_t_1152_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values(lean_object* v_00_u03b1_1157_, lean_object* v_00_u03b2_1158_, lean_object* v_t_1159_){
_start:
{
lean_object* v___f_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___f_1160_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1161_ = lean_box(0);
v___x_1162_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1163_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1162_, v___f_1160_, v___x_1161_, v_t_1159_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(lean_object* v_l_1164_, lean_object* v_x_1165_, lean_object* v_v_1166_){
_start:
{
lean_object* v___x_1167_; 
v___x_1167_ = lean_array_push(v_l_1164_, v_v_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0___boxed(lean_object* v_l_1168_, lean_object* v_x_1169_, lean_object* v_v_1170_){
_start:
{
lean_object* v_res_1171_; 
v_res_1171_ = l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(v_l_1168_, v_x_1169_, v_v_1170_);
lean_dec(v_x_1169_);
return v_res_1171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg(lean_object* v_t_1173_){
_start:
{
lean_object* v___f_1174_; lean_object* v___y_1176_; 
v___f_1174_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1173_) == 0)
{
lean_object* v_size_1179_; 
v_size_1179_ = lean_ctor_get(v_t_1173_, 0);
lean_inc(v_size_1179_);
v___y_1176_ = v_size_1179_;
goto v___jp_1175_;
}
else
{
lean_object* v___x_1180_; 
v___x_1180_ = lean_unsigned_to_nat(0u);
v___y_1176_ = v___x_1180_;
goto v___jp_1175_;
}
v___jp_1175_:
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1177_ = lean_mk_empty_array_with_capacity(v___y_1176_);
lean_dec(v___y_1176_);
v___x_1178_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1174_, v___x_1177_, v_t_1173_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray(lean_object* v_00_u03b1_1181_, lean_object* v_00_u03b2_1182_, lean_object* v_t_1183_){
_start:
{
lean_object* v___f_1184_; lean_object* v___y_1186_; 
v___f_1184_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1183_) == 0)
{
lean_object* v_size_1189_; 
v_size_1189_ = lean_ctor_get(v_t_1183_, 0);
lean_inc(v_size_1189_);
v___y_1186_ = v_size_1189_;
goto v___jp_1185_;
}
else
{
lean_object* v___x_1190_; 
v___x_1190_ = lean_unsigned_to_nat(0u);
v___y_1186_ = v___x_1190_;
goto v___jp_1185_;
}
v___jp_1185_:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_mk_empty_array_with_capacity(v___y_1186_);
lean_dec(v___y_1186_);
v___x_1188_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1184_, v___x_1187_, v_t_1183_);
return v___x_1188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg___lam__0(lean_object* v_x1_1191_, lean_object* v_x2_1192_, lean_object* v_x3_1193_){
_start:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v_x1_1191_);
lean_ctor_set(v___x_1194_, 1, v_x2_1192_);
v___x_1195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1195_, 0, v___x_1194_);
lean_ctor_set(v___x_1195_, 1, v_x3_1193_);
return v___x_1195_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg(lean_object* v_t_1197_){
_start:
{
lean_object* v___f_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___f_1198_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1199_ = lean_box(0);
v___x_1200_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1201_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1200_, v___f_1198_, v___x_1199_, v_t_1197_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList(lean_object* v_00_u03b1_1202_, lean_object* v_00_u03b2_1203_, lean_object* v_t_1204_){
_start:
{
lean_object* v___f_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___f_1205_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1206_ = lean_box(0);
v___x_1207_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1208_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1207_, v___f_1205_, v___x_1206_, v_t_1204_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg___lam__0(lean_object* v_l_1209_, lean_object* v_k_1210_, lean_object* v_v_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1212_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1212_, 0, v_k_1210_);
lean_ctor_set(v___x_1212_, 1, v_v_1211_);
v___x_1213_ = lean_array_push(v_l_1209_, v___x_1212_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg(lean_object* v_t_1215_){
_start:
{
lean_object* v___f_1216_; lean_object* v___y_1218_; 
v___f_1216_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1215_) == 0)
{
lean_object* v_size_1221_; 
v_size_1221_ = lean_ctor_get(v_t_1215_, 0);
lean_inc(v_size_1221_);
v___y_1218_ = v_size_1221_;
goto v___jp_1217_;
}
else
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_unsigned_to_nat(0u);
v___y_1218_ = v___x_1222_;
goto v___jp_1217_;
}
v___jp_1217_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; 
v___x_1219_ = lean_mk_empty_array_with_capacity(v___y_1218_);
lean_dec(v___y_1218_);
v___x_1220_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1216_, v___x_1219_, v_t_1215_);
return v___x_1220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray(lean_object* v_00_u03b1_1223_, lean_object* v_00_u03b2_1224_, lean_object* v_t_1225_){
_start:
{
lean_object* v___f_1226_; lean_object* v___y_1228_; 
v___f_1226_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1225_) == 0)
{
lean_object* v_size_1231_; 
v_size_1231_ = lean_ctor_get(v_t_1225_, 0);
lean_inc(v_size_1231_);
v___y_1228_ = v_size_1231_;
goto v___jp_1227_;
}
else
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_unsigned_to_nat(0u);
v___y_1228_ = v___x_1232_;
goto v___jp_1227_;
}
v___jp_1227_:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_mk_empty_array_with_capacity(v___y_1228_);
lean_dec(v___y_1228_);
v___x_1230_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1226_, v___x_1229_, v_t_1225_);
return v___x_1230_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___lam__0(lean_object* v_x1_1233_, lean_object* v_x2_1234_, lean_object* v_x3_1235_){
_start:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1236_, 0, v_x1_1233_);
lean_ctor_set(v___x_1236_, 1, v_x2_1234_);
v___x_1237_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v_x3_1235_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg(lean_object* v_t_1239_){
_start:
{
lean_object* v___f_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___f_1240_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1241_ = lean_box(0);
v___x_1242_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1243_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1242_, v___f_1240_, v___x_1241_, v_t_1239_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList(lean_object* v_00_u03b1_1244_, lean_object* v_00_u03b2_1245_, lean_object* v_t_1246_){
_start:
{
lean_object* v___f_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___f_1247_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1248_ = lean_box(0);
v___x_1249_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1250_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1249_, v___f_1247_, v___x_1248_, v_t_1246_);
return v___x_1250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___lam__0(lean_object* v_l_1251_, lean_object* v_k_1252_, lean_object* v_v_1253_){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; 
v___x_1254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_k_1252_);
lean_ctor_set(v___x_1254_, 1, v_v_1253_);
v___x_1255_ = lean_array_push(v_l_1251_, v___x_1254_);
return v___x_1255_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg(lean_object* v_t_1257_){
_start:
{
lean_object* v___f_1258_; lean_object* v___y_1260_; 
v___f_1258_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1257_) == 0)
{
lean_object* v_size_1263_; 
v_size_1263_ = lean_ctor_get(v_t_1257_, 0);
lean_inc(v_size_1263_);
v___y_1260_ = v_size_1263_;
goto v___jp_1259_;
}
else
{
lean_object* v___x_1264_; 
v___x_1264_ = lean_unsigned_to_nat(0u);
v___y_1260_ = v___x_1264_;
goto v___jp_1259_;
}
v___jp_1259_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_mk_empty_array_with_capacity(v___y_1260_);
lean_dec(v___y_1260_);
v___x_1262_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1258_, v___x_1261_, v_t_1257_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray(lean_object* v_00_u03b1_1265_, lean_object* v_00_u03b2_1266_, lean_object* v_t_1267_){
_start:
{
lean_object* v___f_1268_; lean_object* v___y_1270_; 
v___f_1268_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1267_) == 0)
{
lean_object* v_size_1273_; 
v_size_1273_ = lean_ctor_get(v_t_1267_, 0);
lean_inc(v_size_1273_);
v___y_1270_ = v_size_1273_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1274_; 
v___x_1274_ = lean_unsigned_to_nat(0u);
v___y_1270_ = v___x_1274_;
goto v___jp_1269_;
}
v___jp_1269_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_mk_empty_array_with_capacity(v___y_1270_);
lean_dec(v___y_1270_);
v___x_1272_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1268_, v___x_1271_, v_t_1267_);
return v___x_1272_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object* v_x_1275_){
_start:
{
if (lean_obj_tag(v_x_1275_) == 0)
{
lean_object* v_l_1276_; 
v_l_1276_ = lean_ctor_get(v_x_1275_, 3);
if (lean_obj_tag(v_l_1276_) == 0)
{
v_x_1275_ = v_l_1276_;
goto _start;
}
else
{
lean_object* v_k_1278_; lean_object* v_v_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; 
v_k_1278_ = lean_ctor_get(v_x_1275_, 1);
v_v_1279_ = lean_ctor_get(v_x_1275_, 2);
lean_inc(v_v_1279_);
lean_inc(v_k_1278_);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v_k_1278_);
lean_ctor_set(v___x_1280_, 1, v_v_1279_);
v___x_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
return v___x_1281_;
}
}
else
{
lean_object* v___x_1282_; 
v___x_1282_ = lean_box(0);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg___boxed(lean_object* v_x_1283_){
_start:
{
lean_object* v_res_1284_; 
v_res_1284_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1283_);
lean_dec(v_x_1283_);
return v_res_1284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f(lean_object* v_00_u03b1_1285_, lean_object* v_00_u03b2_1286_, lean_object* v_x_1287_){
_start:
{
lean_object* v___x_1288_; 
v___x_1288_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1287_);
return v___x_1288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___boxed(lean_object* v_00_u03b1_1289_, lean_object* v_00_u03b2_1290_, lean_object* v_x_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f(v_00_u03b1_1289_, v_00_u03b2_1290_, v_x_1291_);
lean_dec(v_x_1291_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1293_, lean_object* v_h__1_1294_, lean_object* v_h__2_1295_, lean_object* v_h__3_1296_){
_start:
{
if (lean_obj_tag(v_x_1293_) == 0)
{
lean_object* v_l_1297_; 
lean_dec(v_h__1_1294_);
v_l_1297_ = lean_ctor_get(v_x_1293_, 3);
if (lean_obj_tag(v_l_1297_) == 0)
{
lean_object* v_size_1298_; lean_object* v_k_1299_; lean_object* v_v_1300_; lean_object* v_r_1301_; lean_object* v_size_1302_; lean_object* v_k_1303_; lean_object* v_v_1304_; lean_object* v_l_1305_; lean_object* v_r_1306_; lean_object* v___x_1307_; 
lean_inc_ref(v_l_1297_);
lean_dec(v_h__2_1295_);
v_size_1298_ = lean_ctor_get(v_x_1293_, 0);
lean_inc(v_size_1298_);
v_k_1299_ = lean_ctor_get(v_x_1293_, 1);
lean_inc(v_k_1299_);
v_v_1300_ = lean_ctor_get(v_x_1293_, 2);
lean_inc(v_v_1300_);
v_r_1301_ = lean_ctor_get(v_x_1293_, 4);
lean_inc(v_r_1301_);
lean_dec_ref_known(v_x_1293_, 5);
v_size_1302_ = lean_ctor_get(v_l_1297_, 0);
lean_inc(v_size_1302_);
v_k_1303_ = lean_ctor_get(v_l_1297_, 1);
lean_inc(v_k_1303_);
v_v_1304_ = lean_ctor_get(v_l_1297_, 2);
lean_inc(v_v_1304_);
v_l_1305_ = lean_ctor_get(v_l_1297_, 3);
lean_inc(v_l_1305_);
v_r_1306_ = lean_ctor_get(v_l_1297_, 4);
lean_inc(v_r_1306_);
lean_dec_ref_known(v_l_1297_, 5);
v___x_1307_ = lean_apply_9(v_h__3_1296_, v_size_1298_, v_k_1299_, v_v_1300_, v_size_1302_, v_k_1303_, v_v_1304_, v_l_1305_, v_r_1306_, v_r_1301_);
return v___x_1307_;
}
else
{
lean_object* v_size_1308_; lean_object* v_k_1309_; lean_object* v_v_1310_; lean_object* v_r_1311_; lean_object* v___x_1312_; 
lean_dec(v_h__3_1296_);
v_size_1308_ = lean_ctor_get(v_x_1293_, 0);
lean_inc(v_size_1308_);
v_k_1309_ = lean_ctor_get(v_x_1293_, 1);
lean_inc(v_k_1309_);
v_v_1310_ = lean_ctor_get(v_x_1293_, 2);
lean_inc(v_v_1310_);
v_r_1311_ = lean_ctor_get(v_x_1293_, 4);
lean_inc(v_r_1311_);
lean_dec_ref_known(v_x_1293_, 5);
v___x_1312_ = lean_apply_4(v_h__2_1295_, v_size_1308_, v_k_1309_, v_v_1310_, v_r_1311_);
return v___x_1312_;
}
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
lean_dec(v_h__3_1296_);
lean_dec(v_h__2_1295_);
v___x_1313_ = lean_box(0);
v___x_1314_ = lean_apply_1(v_h__1_1294_, v___x_1313_);
return v___x_1314_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1315_, lean_object* v_00_u03b2_1316_, lean_object* v_motive_1317_, lean_object* v_x_1318_, lean_object* v_h__1_1319_, lean_object* v_h__2_1320_, lean_object* v_h__3_1321_){
_start:
{
if (lean_obj_tag(v_x_1318_) == 0)
{
lean_object* v_l_1322_; 
lean_dec(v_h__1_1319_);
v_l_1322_ = lean_ctor_get(v_x_1318_, 3);
if (lean_obj_tag(v_l_1322_) == 0)
{
lean_object* v_size_1323_; lean_object* v_k_1324_; lean_object* v_v_1325_; lean_object* v_r_1326_; lean_object* v_size_1327_; lean_object* v_k_1328_; lean_object* v_v_1329_; lean_object* v_l_1330_; lean_object* v_r_1331_; lean_object* v___x_1332_; 
lean_inc_ref(v_l_1322_);
lean_dec(v_h__2_1320_);
v_size_1323_ = lean_ctor_get(v_x_1318_, 0);
lean_inc(v_size_1323_);
v_k_1324_ = lean_ctor_get(v_x_1318_, 1);
lean_inc(v_k_1324_);
v_v_1325_ = lean_ctor_get(v_x_1318_, 2);
lean_inc(v_v_1325_);
v_r_1326_ = lean_ctor_get(v_x_1318_, 4);
lean_inc(v_r_1326_);
lean_dec_ref_known(v_x_1318_, 5);
v_size_1327_ = lean_ctor_get(v_l_1322_, 0);
lean_inc(v_size_1327_);
v_k_1328_ = lean_ctor_get(v_l_1322_, 1);
lean_inc(v_k_1328_);
v_v_1329_ = lean_ctor_get(v_l_1322_, 2);
lean_inc(v_v_1329_);
v_l_1330_ = lean_ctor_get(v_l_1322_, 3);
lean_inc(v_l_1330_);
v_r_1331_ = lean_ctor_get(v_l_1322_, 4);
lean_inc(v_r_1331_);
lean_dec_ref_known(v_l_1322_, 5);
v___x_1332_ = lean_apply_9(v_h__3_1321_, v_size_1323_, v_k_1324_, v_v_1325_, v_size_1327_, v_k_1328_, v_v_1329_, v_l_1330_, v_r_1331_, v_r_1326_);
return v___x_1332_;
}
else
{
lean_object* v_size_1333_; lean_object* v_k_1334_; lean_object* v_v_1335_; lean_object* v_r_1336_; lean_object* v___x_1337_; 
lean_dec(v_h__3_1321_);
v_size_1333_ = lean_ctor_get(v_x_1318_, 0);
lean_inc(v_size_1333_);
v_k_1334_ = lean_ctor_get(v_x_1318_, 1);
lean_inc(v_k_1334_);
v_v_1335_ = lean_ctor_get(v_x_1318_, 2);
lean_inc(v_v_1335_);
v_r_1336_ = lean_ctor_get(v_x_1318_, 4);
lean_inc(v_r_1336_);
lean_dec_ref_known(v_x_1318_, 5);
v___x_1337_ = lean_apply_4(v_h__2_1320_, v_size_1333_, v_k_1334_, v_v_1335_, v_r_1336_);
return v___x_1337_;
}
}
else
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
lean_dec(v_h__3_1321_);
lean_dec(v_h__2_1320_);
v___x_1338_ = lean_box(0);
v___x_1339_ = lean_apply_1(v_h__1_1319_, v___x_1338_);
return v___x_1339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg(lean_object* v_x_1340_){
_start:
{
lean_object* v_l_1341_; 
v_l_1341_ = lean_ctor_get(v_x_1340_, 3);
if (lean_obj_tag(v_l_1341_) == 0)
{
v_x_1340_ = v_l_1341_;
goto _start;
}
else
{
lean_object* v_k_1343_; lean_object* v_v_1344_; lean_object* v___x_1345_; 
v_k_1343_ = lean_ctor_get(v_x_1340_, 1);
v_v_1344_ = lean_ctor_get(v_x_1340_, 2);
lean_inc(v_v_1344_);
lean_inc(v_k_1343_);
v___x_1345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1345_, 0, v_k_1343_);
lean_ctor_set(v___x_1345_, 1, v_v_1344_);
return v___x_1345_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg___boxed(lean_object* v_x_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1346_);
lean_dec(v_x_1346_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry(lean_object* v_00_u03b1_1348_, lean_object* v_00_u03b2_1349_, lean_object* v_x_1350_, lean_object* v_x_1351_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1350_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___boxed(lean_object* v_00_u03b1_1353_, lean_object* v_00_u03b2_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l_Std_DTreeMap_Internal_Impl_minEntry(v_00_u03b1_1353_, v_00_u03b2_1354_, v_x_1355_, v_x_1356_);
lean_dec(v_x_1355_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1358_, lean_object* v_h__1_1359_, lean_object* v_h__2_1360_){
_start:
{
lean_object* v_l_1361_; 
v_l_1361_ = lean_ctor_get(v_x_1358_, 3);
if (lean_obj_tag(v_l_1361_) == 0)
{
lean_object* v_size_1362_; lean_object* v_k_1363_; lean_object* v_v_1364_; lean_object* v_r_1365_; lean_object* v_size_1366_; lean_object* v_k_1367_; lean_object* v_v_1368_; lean_object* v_l_1369_; lean_object* v_r_1370_; lean_object* v___x_1371_; 
lean_inc_ref(v_l_1361_);
lean_dec(v_h__1_1359_);
v_size_1362_ = lean_ctor_get(v_x_1358_, 0);
lean_inc(v_size_1362_);
v_k_1363_ = lean_ctor_get(v_x_1358_, 1);
lean_inc(v_k_1363_);
v_v_1364_ = lean_ctor_get(v_x_1358_, 2);
lean_inc(v_v_1364_);
v_r_1365_ = lean_ctor_get(v_x_1358_, 4);
lean_inc(v_r_1365_);
lean_dec(v_x_1358_);
v_size_1366_ = lean_ctor_get(v_l_1361_, 0);
lean_inc(v_size_1366_);
v_k_1367_ = lean_ctor_get(v_l_1361_, 1);
lean_inc(v_k_1367_);
v_v_1368_ = lean_ctor_get(v_l_1361_, 2);
lean_inc(v_v_1368_);
v_l_1369_ = lean_ctor_get(v_l_1361_, 3);
lean_inc(v_l_1369_);
v_r_1370_ = lean_ctor_get(v_l_1361_, 4);
lean_inc(v_r_1370_);
lean_dec_ref_known(v_l_1361_, 5);
v___x_1371_ = lean_apply_10(v_h__2_1360_, v_size_1362_, v_k_1363_, v_v_1364_, v_size_1366_, v_k_1367_, v_v_1368_, v_l_1369_, v_r_1370_, v_r_1365_, lean_box(0));
return v___x_1371_;
}
else
{
lean_object* v_size_1372_; lean_object* v_k_1373_; lean_object* v_v_1374_; lean_object* v_r_1375_; lean_object* v___x_1376_; 
lean_dec(v_h__2_1360_);
v_size_1372_ = lean_ctor_get(v_x_1358_, 0);
lean_inc(v_size_1372_);
v_k_1373_ = lean_ctor_get(v_x_1358_, 1);
lean_inc(v_k_1373_);
v_v_1374_ = lean_ctor_get(v_x_1358_, 2);
lean_inc(v_v_1374_);
v_r_1375_ = lean_ctor_get(v_x_1358_, 4);
lean_inc(v_r_1375_);
lean_dec(v_x_1358_);
v___x_1376_ = lean_apply_5(v_h__1_1359_, v_size_1372_, v_k_1373_, v_v_1374_, v_r_1375_, lean_box(0));
return v___x_1376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1377_, lean_object* v_00_u03b2_1378_, lean_object* v_motive_1379_, lean_object* v_x_1380_, lean_object* v_x_1381_, lean_object* v_h__1_1382_, lean_object* v_h__2_1383_){
_start:
{
lean_object* v_l_1384_; 
v_l_1384_ = lean_ctor_get(v_x_1380_, 3);
if (lean_obj_tag(v_l_1384_) == 0)
{
lean_object* v_size_1385_; lean_object* v_k_1386_; lean_object* v_v_1387_; lean_object* v_r_1388_; lean_object* v_size_1389_; lean_object* v_k_1390_; lean_object* v_v_1391_; lean_object* v_l_1392_; lean_object* v_r_1393_; lean_object* v___x_1394_; 
lean_inc_ref(v_l_1384_);
lean_dec(v_h__1_1382_);
v_size_1385_ = lean_ctor_get(v_x_1380_, 0);
lean_inc(v_size_1385_);
v_k_1386_ = lean_ctor_get(v_x_1380_, 1);
lean_inc(v_k_1386_);
v_v_1387_ = lean_ctor_get(v_x_1380_, 2);
lean_inc(v_v_1387_);
v_r_1388_ = lean_ctor_get(v_x_1380_, 4);
lean_inc(v_r_1388_);
lean_dec(v_x_1380_);
v_size_1389_ = lean_ctor_get(v_l_1384_, 0);
lean_inc(v_size_1389_);
v_k_1390_ = lean_ctor_get(v_l_1384_, 1);
lean_inc(v_k_1390_);
v_v_1391_ = lean_ctor_get(v_l_1384_, 2);
lean_inc(v_v_1391_);
v_l_1392_ = lean_ctor_get(v_l_1384_, 3);
lean_inc(v_l_1392_);
v_r_1393_ = lean_ctor_get(v_l_1384_, 4);
lean_inc(v_r_1393_);
lean_dec_ref_known(v_l_1384_, 5);
v___x_1394_ = lean_apply_10(v_h__2_1383_, v_size_1385_, v_k_1386_, v_v_1387_, v_size_1389_, v_k_1390_, v_v_1391_, v_l_1392_, v_r_1393_, v_r_1388_, lean_box(0));
return v___x_1394_;
}
else
{
lean_object* v_size_1395_; lean_object* v_k_1396_; lean_object* v_v_1397_; lean_object* v_r_1398_; lean_object* v___x_1399_; 
lean_dec(v_h__2_1383_);
v_size_1395_ = lean_ctor_get(v_x_1380_, 0);
lean_inc(v_size_1395_);
v_k_1396_ = lean_ctor_get(v_x_1380_, 1);
lean_inc(v_k_1396_);
v_v_1397_ = lean_ctor_get(v_x_1380_, 2);
lean_inc(v_v_1397_);
v_r_1398_ = lean_ctor_get(v_x_1380_, 4);
lean_inc(v_r_1398_);
lean_dec(v_x_1380_);
v___x_1399_ = lean_apply_5(v_h__1_1382_, v_size_1395_, v_k_1396_, v_v_1397_, v_r_1398_, lean_box(0));
return v___x_1399_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; 
v___x_1402_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1403_ = lean_unsigned_to_nat(13u);
v___x_1404_ = lean_unsigned_to_nat(367u);
v___x_1405_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0));
v___x_1406_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1407_ = l_mkPanicMessageWithDecl(v___x_1406_, v___x_1405_, v___x_1404_, v___x_1403_, v___x_1402_);
return v___x_1407_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object* v_inst_1408_, lean_object* v_x_1409_){
_start:
{
if (lean_obj_tag(v_x_1409_) == 0)
{
lean_object* v_l_1410_; 
v_l_1410_ = lean_ctor_get(v_x_1409_, 3);
if (lean_obj_tag(v_l_1410_) == 0)
{
v_x_1409_ = v_l_1410_;
goto _start;
}
else
{
lean_object* v_k_1412_; lean_object* v_v_1413_; lean_object* v___x_1414_; 
v_k_1412_ = lean_ctor_get(v_x_1409_, 1);
v_v_1413_ = lean_ctor_get(v_x_1409_, 2);
lean_inc(v_v_1413_);
lean_inc(v_k_1412_);
v___x_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1414_, 0, v_k_1412_);
lean_ctor_set(v___x_1414_, 1, v_v_1413_);
return v___x_1414_;
}
}
else
{
lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1415_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2);
v___x_1416_ = l_panic___redArg(v_inst_1408_, v___x_1415_);
return v___x_1416_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___boxed(lean_object* v_inst_1417_, lean_object* v_x_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1417_, v_x_1418_);
lean_dec(v_x_1418_);
lean_dec_ref(v_inst_1417_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21(lean_object* v_00_u03b1_1420_, lean_object* v_00_u03b2_1421_, lean_object* v_inst_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1422_, v_x_1423_);
return v___x_1424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___boxed(lean_object* v_00_u03b1_1425_, lean_object* v_00_u03b2_1426_, lean_object* v_inst_1427_, lean_object* v_x_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21(v_00_u03b1_1425_, v_00_u03b2_1426_, v_inst_1427_, v_x_1428_);
lean_dec(v_x_1428_);
lean_dec_ref(v_inst_1427_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object* v_x_1430_, lean_object* v_x_1431_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
lean_object* v_l_1432_; 
v_l_1432_ = lean_ctor_get(v_x_1430_, 3);
if (lean_obj_tag(v_l_1432_) == 0)
{
v_x_1430_ = v_l_1432_;
goto _start;
}
else
{
lean_object* v_k_1434_; lean_object* v_v_1435_; lean_object* v___x_1436_; 
v_k_1434_ = lean_ctor_get(v_x_1430_, 1);
v_v_1435_ = lean_ctor_get(v_x_1430_, 2);
lean_inc(v_v_1435_);
lean_inc(v_k_1434_);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_k_1434_);
lean_ctor_set(v___x_1436_, 1, v_v_1435_);
return v___x_1436_;
}
}
else
{
lean_inc_ref(v_x_1431_);
return v_x_1431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg___boxed(lean_object* v_x_1437_, lean_object* v_x_1438_){
_start:
{
lean_object* v_res_1439_; 
v_res_1439_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1437_, v_x_1438_);
lean_dec_ref(v_x_1438_);
lean_dec(v_x_1437_);
return v_res_1439_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD(lean_object* v_00_u03b1_1440_, lean_object* v_00_u03b2_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1442_, v_x_1443_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___boxed(lean_object* v_00_u03b1_1445_, lean_object* v_00_u03b2_1446_, lean_object* v_x_1447_, lean_object* v_x_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_Std_DTreeMap_Internal_Impl_minEntryD(v_00_u03b1_1445_, v_00_u03b2_1446_, v_x_1447_, v_x_1448_);
lean_dec_ref(v_x_1448_);
lean_dec(v_x_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1450_, lean_object* v_x_1451_, lean_object* v_h__1_1452_, lean_object* v_h__2_1453_, lean_object* v_h__3_1454_){
_start:
{
if (lean_obj_tag(v_x_1450_) == 0)
{
lean_object* v_l_1455_; 
lean_dec(v_h__1_1452_);
v_l_1455_ = lean_ctor_get(v_x_1450_, 3);
if (lean_obj_tag(v_l_1455_) == 0)
{
lean_object* v_size_1456_; lean_object* v_k_1457_; lean_object* v_v_1458_; lean_object* v_r_1459_; lean_object* v_size_1460_; lean_object* v_k_1461_; lean_object* v_v_1462_; lean_object* v_l_1463_; lean_object* v_r_1464_; lean_object* v___x_1465_; 
lean_inc_ref(v_l_1455_);
lean_dec(v_h__2_1453_);
v_size_1456_ = lean_ctor_get(v_x_1450_, 0);
lean_inc(v_size_1456_);
v_k_1457_ = lean_ctor_get(v_x_1450_, 1);
lean_inc(v_k_1457_);
v_v_1458_ = lean_ctor_get(v_x_1450_, 2);
lean_inc(v_v_1458_);
v_r_1459_ = lean_ctor_get(v_x_1450_, 4);
lean_inc(v_r_1459_);
lean_dec_ref_known(v_x_1450_, 5);
v_size_1460_ = lean_ctor_get(v_l_1455_, 0);
lean_inc(v_size_1460_);
v_k_1461_ = lean_ctor_get(v_l_1455_, 1);
lean_inc(v_k_1461_);
v_v_1462_ = lean_ctor_get(v_l_1455_, 2);
lean_inc(v_v_1462_);
v_l_1463_ = lean_ctor_get(v_l_1455_, 3);
lean_inc(v_l_1463_);
v_r_1464_ = lean_ctor_get(v_l_1455_, 4);
lean_inc(v_r_1464_);
lean_dec_ref_known(v_l_1455_, 5);
v___x_1465_ = lean_apply_10(v_h__3_1454_, v_size_1456_, v_k_1457_, v_v_1458_, v_size_1460_, v_k_1461_, v_v_1462_, v_l_1463_, v_r_1464_, v_r_1459_, v_x_1451_);
return v___x_1465_;
}
else
{
lean_object* v_size_1466_; lean_object* v_k_1467_; lean_object* v_v_1468_; lean_object* v_r_1469_; lean_object* v___x_1470_; 
lean_dec(v_h__3_1454_);
v_size_1466_ = lean_ctor_get(v_x_1450_, 0);
lean_inc(v_size_1466_);
v_k_1467_ = lean_ctor_get(v_x_1450_, 1);
lean_inc(v_k_1467_);
v_v_1468_ = lean_ctor_get(v_x_1450_, 2);
lean_inc(v_v_1468_);
v_r_1469_ = lean_ctor_get(v_x_1450_, 4);
lean_inc(v_r_1469_);
lean_dec_ref_known(v_x_1450_, 5);
v___x_1470_ = lean_apply_5(v_h__2_1453_, v_size_1466_, v_k_1467_, v_v_1468_, v_r_1469_, v_x_1451_);
return v___x_1470_;
}
}
else
{
lean_object* v___x_1471_; 
lean_dec(v_h__3_1454_);
lean_dec(v_h__2_1453_);
v___x_1471_ = lean_apply_1(v_h__1_1452_, v_x_1451_);
return v___x_1471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1472_, lean_object* v_00_u03b2_1473_, lean_object* v_motive_1474_, lean_object* v_x_1475_, lean_object* v_x_1476_, lean_object* v_h__1_1477_, lean_object* v_h__2_1478_, lean_object* v_h__3_1479_){
_start:
{
if (lean_obj_tag(v_x_1475_) == 0)
{
lean_object* v_l_1480_; 
lean_dec(v_h__1_1477_);
v_l_1480_ = lean_ctor_get(v_x_1475_, 3);
if (lean_obj_tag(v_l_1480_) == 0)
{
lean_object* v_size_1481_; lean_object* v_k_1482_; lean_object* v_v_1483_; lean_object* v_r_1484_; lean_object* v_size_1485_; lean_object* v_k_1486_; lean_object* v_v_1487_; lean_object* v_l_1488_; lean_object* v_r_1489_; lean_object* v___x_1490_; 
lean_inc_ref(v_l_1480_);
lean_dec(v_h__2_1478_);
v_size_1481_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_size_1481_);
v_k_1482_ = lean_ctor_get(v_x_1475_, 1);
lean_inc(v_k_1482_);
v_v_1483_ = lean_ctor_get(v_x_1475_, 2);
lean_inc(v_v_1483_);
v_r_1484_ = lean_ctor_get(v_x_1475_, 4);
lean_inc(v_r_1484_);
lean_dec_ref_known(v_x_1475_, 5);
v_size_1485_ = lean_ctor_get(v_l_1480_, 0);
lean_inc(v_size_1485_);
v_k_1486_ = lean_ctor_get(v_l_1480_, 1);
lean_inc(v_k_1486_);
v_v_1487_ = lean_ctor_get(v_l_1480_, 2);
lean_inc(v_v_1487_);
v_l_1488_ = lean_ctor_get(v_l_1480_, 3);
lean_inc(v_l_1488_);
v_r_1489_ = lean_ctor_get(v_l_1480_, 4);
lean_inc(v_r_1489_);
lean_dec_ref_known(v_l_1480_, 5);
v___x_1490_ = lean_apply_10(v_h__3_1479_, v_size_1481_, v_k_1482_, v_v_1483_, v_size_1485_, v_k_1486_, v_v_1487_, v_l_1488_, v_r_1489_, v_r_1484_, v_x_1476_);
return v___x_1490_;
}
else
{
lean_object* v_size_1491_; lean_object* v_k_1492_; lean_object* v_v_1493_; lean_object* v_r_1494_; lean_object* v___x_1495_; 
lean_dec(v_h__3_1479_);
v_size_1491_ = lean_ctor_get(v_x_1475_, 0);
lean_inc(v_size_1491_);
v_k_1492_ = lean_ctor_get(v_x_1475_, 1);
lean_inc(v_k_1492_);
v_v_1493_ = lean_ctor_get(v_x_1475_, 2);
lean_inc(v_v_1493_);
v_r_1494_ = lean_ctor_get(v_x_1475_, 4);
lean_inc(v_r_1494_);
lean_dec_ref_known(v_x_1475_, 5);
v___x_1495_ = lean_apply_5(v_h__2_1478_, v_size_1491_, v_k_1492_, v_v_1493_, v_r_1494_, v_x_1476_);
return v___x_1495_;
}
}
else
{
lean_object* v___x_1496_; 
lean_dec(v_h__3_1479_);
lean_dec(v_h__2_1478_);
v___x_1496_ = lean_apply_1(v_h__1_1477_, v_x_1476_);
return v___x_1496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object* v_x_1497_){
_start:
{
if (lean_obj_tag(v_x_1497_) == 0)
{
lean_object* v_r_1498_; 
v_r_1498_ = lean_ctor_get(v_x_1497_, 4);
if (lean_obj_tag(v_r_1498_) == 0)
{
v_x_1497_ = v_r_1498_;
goto _start;
}
else
{
lean_object* v_k_1500_; lean_object* v_v_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; 
v_k_1500_ = lean_ctor_get(v_x_1497_, 1);
v_v_1501_ = lean_ctor_get(v_x_1497_, 2);
lean_inc(v_v_1501_);
lean_inc(v_k_1500_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v_k_1500_);
lean_ctor_set(v___x_1502_, 1, v_v_1501_);
v___x_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1502_);
return v___x_1503_;
}
}
else
{
lean_object* v___x_1504_; 
v___x_1504_ = lean_box(0);
return v___x_1504_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg___boxed(lean_object* v_x_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1505_);
lean_dec(v_x_1505_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(lean_object* v_00_u03b1_1507_, lean_object* v_00_u03b2_1508_, lean_object* v_x_1509_){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1511_, lean_object* v_00_u03b2_1512_, lean_object* v_x_1513_){
_start:
{
lean_object* v_res_1514_; 
v_res_1514_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(v_00_u03b1_1511_, v_00_u03b2_1512_, v_x_1513_);
lean_dec(v_x_1513_);
return v_res_1514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1515_, lean_object* v_h__1_1516_, lean_object* v_h__2_1517_, lean_object* v_h__3_1518_){
_start:
{
if (lean_obj_tag(v_x_1515_) == 0)
{
lean_object* v_r_1519_; 
lean_dec(v_h__1_1516_);
v_r_1519_ = lean_ctor_get(v_x_1515_, 4);
if (lean_obj_tag(v_r_1519_) == 0)
{
lean_object* v_size_1520_; lean_object* v_k_1521_; lean_object* v_v_1522_; lean_object* v_l_1523_; lean_object* v_size_1524_; lean_object* v_k_1525_; lean_object* v_v_1526_; lean_object* v_l_1527_; lean_object* v_r_1528_; lean_object* v___x_1529_; 
lean_inc_ref(v_r_1519_);
lean_dec(v_h__2_1517_);
v_size_1520_ = lean_ctor_get(v_x_1515_, 0);
lean_inc(v_size_1520_);
v_k_1521_ = lean_ctor_get(v_x_1515_, 1);
lean_inc(v_k_1521_);
v_v_1522_ = lean_ctor_get(v_x_1515_, 2);
lean_inc(v_v_1522_);
v_l_1523_ = lean_ctor_get(v_x_1515_, 3);
lean_inc(v_l_1523_);
lean_dec_ref_known(v_x_1515_, 5);
v_size_1524_ = lean_ctor_get(v_r_1519_, 0);
lean_inc(v_size_1524_);
v_k_1525_ = lean_ctor_get(v_r_1519_, 1);
lean_inc(v_k_1525_);
v_v_1526_ = lean_ctor_get(v_r_1519_, 2);
lean_inc(v_v_1526_);
v_l_1527_ = lean_ctor_get(v_r_1519_, 3);
lean_inc(v_l_1527_);
v_r_1528_ = lean_ctor_get(v_r_1519_, 4);
lean_inc(v_r_1528_);
lean_dec_ref_known(v_r_1519_, 5);
v___x_1529_ = lean_apply_9(v_h__3_1518_, v_size_1520_, v_k_1521_, v_v_1522_, v_l_1523_, v_size_1524_, v_k_1525_, v_v_1526_, v_l_1527_, v_r_1528_);
return v___x_1529_;
}
else
{
lean_object* v_size_1530_; lean_object* v_k_1531_; lean_object* v_v_1532_; lean_object* v_l_1533_; lean_object* v___x_1534_; 
lean_dec(v_h__3_1518_);
v_size_1530_ = lean_ctor_get(v_x_1515_, 0);
lean_inc(v_size_1530_);
v_k_1531_ = lean_ctor_get(v_x_1515_, 1);
lean_inc(v_k_1531_);
v_v_1532_ = lean_ctor_get(v_x_1515_, 2);
lean_inc(v_v_1532_);
v_l_1533_ = lean_ctor_get(v_x_1515_, 3);
lean_inc(v_l_1533_);
lean_dec_ref_known(v_x_1515_, 5);
v___x_1534_ = lean_apply_4(v_h__2_1517_, v_size_1530_, v_k_1531_, v_v_1532_, v_l_1533_);
return v___x_1534_;
}
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_h__3_1518_);
lean_dec(v_h__2_1517_);
v___x_1535_ = lean_box(0);
v___x_1536_ = lean_apply_1(v_h__1_1516_, v___x_1535_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1537_, lean_object* v_00_u03b2_1538_, lean_object* v_motive_1539_, lean_object* v_x_1540_, lean_object* v_h__1_1541_, lean_object* v_h__2_1542_, lean_object* v_h__3_1543_){
_start:
{
if (lean_obj_tag(v_x_1540_) == 0)
{
lean_object* v_r_1544_; 
lean_dec(v_h__1_1541_);
v_r_1544_ = lean_ctor_get(v_x_1540_, 4);
if (lean_obj_tag(v_r_1544_) == 0)
{
lean_object* v_size_1545_; lean_object* v_k_1546_; lean_object* v_v_1547_; lean_object* v_l_1548_; lean_object* v_size_1549_; lean_object* v_k_1550_; lean_object* v_v_1551_; lean_object* v_l_1552_; lean_object* v_r_1553_; lean_object* v___x_1554_; 
lean_inc_ref(v_r_1544_);
lean_dec(v_h__2_1542_);
v_size_1545_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_size_1545_);
v_k_1546_ = lean_ctor_get(v_x_1540_, 1);
lean_inc(v_k_1546_);
v_v_1547_ = lean_ctor_get(v_x_1540_, 2);
lean_inc(v_v_1547_);
v_l_1548_ = lean_ctor_get(v_x_1540_, 3);
lean_inc(v_l_1548_);
lean_dec_ref_known(v_x_1540_, 5);
v_size_1549_ = lean_ctor_get(v_r_1544_, 0);
lean_inc(v_size_1549_);
v_k_1550_ = lean_ctor_get(v_r_1544_, 1);
lean_inc(v_k_1550_);
v_v_1551_ = lean_ctor_get(v_r_1544_, 2);
lean_inc(v_v_1551_);
v_l_1552_ = lean_ctor_get(v_r_1544_, 3);
lean_inc(v_l_1552_);
v_r_1553_ = lean_ctor_get(v_r_1544_, 4);
lean_inc(v_r_1553_);
lean_dec_ref_known(v_r_1544_, 5);
v___x_1554_ = lean_apply_9(v_h__3_1543_, v_size_1545_, v_k_1546_, v_v_1547_, v_l_1548_, v_size_1549_, v_k_1550_, v_v_1551_, v_l_1552_, v_r_1553_);
return v___x_1554_;
}
else
{
lean_object* v_size_1555_; lean_object* v_k_1556_; lean_object* v_v_1557_; lean_object* v_l_1558_; lean_object* v___x_1559_; 
lean_dec(v_h__3_1543_);
v_size_1555_ = lean_ctor_get(v_x_1540_, 0);
lean_inc(v_size_1555_);
v_k_1556_ = lean_ctor_get(v_x_1540_, 1);
lean_inc(v_k_1556_);
v_v_1557_ = lean_ctor_get(v_x_1540_, 2);
lean_inc(v_v_1557_);
v_l_1558_ = lean_ctor_get(v_x_1540_, 3);
lean_inc(v_l_1558_);
lean_dec_ref_known(v_x_1540_, 5);
v___x_1559_ = lean_apply_4(v_h__2_1542_, v_size_1555_, v_k_1556_, v_v_1557_, v_l_1558_);
return v___x_1559_;
}
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_h__3_1543_);
lean_dec(v_h__2_1542_);
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_apply_1(v_h__1_1541_, v___x_1560_);
return v___x_1561_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object* v_x_1562_){
_start:
{
lean_object* v_r_1563_; 
v_r_1563_ = lean_ctor_get(v_x_1562_, 4);
if (lean_obj_tag(v_r_1563_) == 0)
{
v_x_1562_ = v_r_1563_;
goto _start;
}
else
{
lean_object* v_k_1565_; lean_object* v_v_1566_; lean_object* v___x_1567_; 
v_k_1565_ = lean_ctor_get(v_x_1562_, 1);
v_v_1566_ = lean_ctor_get(v_x_1562_, 2);
lean_inc(v_v_1566_);
lean_inc(v_k_1565_);
v___x_1567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1567_, 0, v_k_1565_);
lean_ctor_set(v___x_1567_, 1, v_v_1566_);
return v___x_1567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg___boxed(lean_object* v_x_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1568_);
lean_dec(v_x_1568_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry(lean_object* v_00_u03b1_1570_, lean_object* v_00_u03b2_1571_, lean_object* v_x_1572_, lean_object* v_x_1573_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1572_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___boxed(lean_object* v_00_u03b1_1575_, lean_object* v_00_u03b2_1576_, lean_object* v_x_1577_, lean_object* v_x_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Std_DTreeMap_Internal_Impl_maxEntry(v_00_u03b1_1575_, v_00_u03b2_1576_, v_x_1577_, v_x_1578_);
lean_dec(v_x_1577_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1580_, lean_object* v_h__1_1581_, lean_object* v_h__2_1582_){
_start:
{
lean_object* v_r_1583_; 
v_r_1583_ = lean_ctor_get(v_x_1580_, 4);
if (lean_obj_tag(v_r_1583_) == 0)
{
lean_object* v_size_1584_; lean_object* v_k_1585_; lean_object* v_v_1586_; lean_object* v_l_1587_; lean_object* v_size_1588_; lean_object* v_k_1589_; lean_object* v_v_1590_; lean_object* v_l_1591_; lean_object* v_r_1592_; lean_object* v___x_1593_; 
lean_inc_ref(v_r_1583_);
lean_dec(v_h__1_1581_);
v_size_1584_ = lean_ctor_get(v_x_1580_, 0);
lean_inc(v_size_1584_);
v_k_1585_ = lean_ctor_get(v_x_1580_, 1);
lean_inc(v_k_1585_);
v_v_1586_ = lean_ctor_get(v_x_1580_, 2);
lean_inc(v_v_1586_);
v_l_1587_ = lean_ctor_get(v_x_1580_, 3);
lean_inc(v_l_1587_);
lean_dec(v_x_1580_);
v_size_1588_ = lean_ctor_get(v_r_1583_, 0);
lean_inc(v_size_1588_);
v_k_1589_ = lean_ctor_get(v_r_1583_, 1);
lean_inc(v_k_1589_);
v_v_1590_ = lean_ctor_get(v_r_1583_, 2);
lean_inc(v_v_1590_);
v_l_1591_ = lean_ctor_get(v_r_1583_, 3);
lean_inc(v_l_1591_);
v_r_1592_ = lean_ctor_get(v_r_1583_, 4);
lean_inc(v_r_1592_);
lean_dec_ref_known(v_r_1583_, 5);
v___x_1593_ = lean_apply_10(v_h__2_1582_, v_size_1584_, v_k_1585_, v_v_1586_, v_l_1587_, v_size_1588_, v_k_1589_, v_v_1590_, v_l_1591_, v_r_1592_, lean_box(0));
return v___x_1593_;
}
else
{
lean_object* v_size_1594_; lean_object* v_k_1595_; lean_object* v_v_1596_; lean_object* v_l_1597_; lean_object* v___x_1598_; 
lean_dec(v_h__2_1582_);
v_size_1594_ = lean_ctor_get(v_x_1580_, 0);
lean_inc(v_size_1594_);
v_k_1595_ = lean_ctor_get(v_x_1580_, 1);
lean_inc(v_k_1595_);
v_v_1596_ = lean_ctor_get(v_x_1580_, 2);
lean_inc(v_v_1596_);
v_l_1597_ = lean_ctor_get(v_x_1580_, 3);
lean_inc(v_l_1597_);
lean_dec(v_x_1580_);
v___x_1598_ = lean_apply_5(v_h__1_1581_, v_size_1594_, v_k_1595_, v_v_1596_, v_l_1597_, lean_box(0));
return v___x_1598_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1599_, lean_object* v_00_u03b2_1600_, lean_object* v_motive_1601_, lean_object* v_x_1602_, lean_object* v_x_1603_, lean_object* v_h__1_1604_, lean_object* v_h__2_1605_){
_start:
{
lean_object* v_r_1606_; 
v_r_1606_ = lean_ctor_get(v_x_1602_, 4);
if (lean_obj_tag(v_r_1606_) == 0)
{
lean_object* v_size_1607_; lean_object* v_k_1608_; lean_object* v_v_1609_; lean_object* v_l_1610_; lean_object* v_size_1611_; lean_object* v_k_1612_; lean_object* v_v_1613_; lean_object* v_l_1614_; lean_object* v_r_1615_; lean_object* v___x_1616_; 
lean_inc_ref(v_r_1606_);
lean_dec(v_h__1_1604_);
v_size_1607_ = lean_ctor_get(v_x_1602_, 0);
lean_inc(v_size_1607_);
v_k_1608_ = lean_ctor_get(v_x_1602_, 1);
lean_inc(v_k_1608_);
v_v_1609_ = lean_ctor_get(v_x_1602_, 2);
lean_inc(v_v_1609_);
v_l_1610_ = lean_ctor_get(v_x_1602_, 3);
lean_inc(v_l_1610_);
lean_dec(v_x_1602_);
v_size_1611_ = lean_ctor_get(v_r_1606_, 0);
lean_inc(v_size_1611_);
v_k_1612_ = lean_ctor_get(v_r_1606_, 1);
lean_inc(v_k_1612_);
v_v_1613_ = lean_ctor_get(v_r_1606_, 2);
lean_inc(v_v_1613_);
v_l_1614_ = lean_ctor_get(v_r_1606_, 3);
lean_inc(v_l_1614_);
v_r_1615_ = lean_ctor_get(v_r_1606_, 4);
lean_inc(v_r_1615_);
lean_dec_ref_known(v_r_1606_, 5);
v___x_1616_ = lean_apply_10(v_h__2_1605_, v_size_1607_, v_k_1608_, v_v_1609_, v_l_1610_, v_size_1611_, v_k_1612_, v_v_1613_, v_l_1614_, v_r_1615_, lean_box(0));
return v___x_1616_;
}
else
{
lean_object* v_size_1617_; lean_object* v_k_1618_; lean_object* v_v_1619_; lean_object* v_l_1620_; lean_object* v___x_1621_; 
lean_dec(v_h__2_1605_);
v_size_1617_ = lean_ctor_get(v_x_1602_, 0);
lean_inc(v_size_1617_);
v_k_1618_ = lean_ctor_get(v_x_1602_, 1);
lean_inc(v_k_1618_);
v_v_1619_ = lean_ctor_get(v_x_1602_, 2);
lean_inc(v_v_1619_);
v_l_1620_ = lean_ctor_get(v_x_1602_, 3);
lean_inc(v_l_1620_);
lean_dec(v_x_1602_);
v___x_1621_ = lean_apply_5(v_h__1_1604_, v_size_1617_, v_k_1618_, v_v_1619_, v_l_1620_, lean_box(0));
return v___x_1621_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1623_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1624_ = lean_unsigned_to_nat(13u);
v___x_1625_ = lean_unsigned_to_nat(390u);
v___x_1626_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0));
v___x_1627_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1628_ = l_mkPanicMessageWithDecl(v___x_1627_, v___x_1626_, v___x_1625_, v___x_1624_, v___x_1623_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object* v_inst_1629_, lean_object* v_x_1630_){
_start:
{
if (lean_obj_tag(v_x_1630_) == 0)
{
lean_object* v_r_1631_; 
v_r_1631_ = lean_ctor_get(v_x_1630_, 4);
if (lean_obj_tag(v_r_1631_) == 0)
{
v_x_1630_ = v_r_1631_;
goto _start;
}
else
{
lean_object* v_k_1633_; lean_object* v_v_1634_; lean_object* v___x_1635_; 
v_k_1633_ = lean_ctor_get(v_x_1630_, 1);
v_v_1634_ = lean_ctor_get(v_x_1630_, 2);
lean_inc(v_v_1634_);
lean_inc(v_k_1633_);
v___x_1635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1635_, 0, v_k_1633_);
lean_ctor_set(v___x_1635_, 1, v_v_1634_);
return v___x_1635_;
}
}
else
{
lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1636_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1);
v___x_1637_ = l_panic___redArg(v_inst_1629_, v___x_1636_);
return v___x_1637_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___boxed(lean_object* v_inst_1638_, lean_object* v_x_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1638_, v_x_1639_);
lean_dec(v_x_1639_);
lean_dec_ref(v_inst_1638_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21(lean_object* v_00_u03b1_1641_, lean_object* v_00_u03b2_1642_, lean_object* v_inst_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1643_, v_x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___boxed(lean_object* v_00_u03b1_1646_, lean_object* v_00_u03b2_1647_, lean_object* v_inst_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21(v_00_u03b1_1646_, v_00_u03b2_1647_, v_inst_1648_, v_x_1649_);
lean_dec(v_x_1649_);
lean_dec_ref(v_inst_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(lean_object* v_x_1651_, lean_object* v_x_1652_){
_start:
{
if (lean_obj_tag(v_x_1651_) == 0)
{
lean_object* v_r_1653_; 
v_r_1653_ = lean_ctor_get(v_x_1651_, 4);
if (lean_obj_tag(v_r_1653_) == 0)
{
v_x_1651_ = v_r_1653_;
goto _start;
}
else
{
lean_object* v_k_1655_; lean_object* v_v_1656_; lean_object* v___x_1657_; 
v_k_1655_ = lean_ctor_get(v_x_1651_, 1);
v_v_1656_ = lean_ctor_get(v_x_1651_, 2);
lean_inc(v_v_1656_);
lean_inc(v_k_1655_);
v___x_1657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1657_, 0, v_k_1655_);
lean_ctor_set(v___x_1657_, 1, v_v_1656_);
return v___x_1657_;
}
}
else
{
lean_inc_ref(v_x_1652_);
return v_x_1652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg___boxed(lean_object* v_x_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1658_, v_x_1659_);
lean_dec_ref(v_x_1659_);
lean_dec(v_x_1658_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD(lean_object* v_00_u03b1_1661_, lean_object* v_00_u03b2_1662_, lean_object* v_x_1663_, lean_object* v_x_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1663_, v_x_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___boxed(lean_object* v_00_u03b1_1666_, lean_object* v_00_u03b2_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v_res_1670_; 
v_res_1670_ = l_Std_DTreeMap_Internal_Impl_maxEntryD(v_00_u03b1_1666_, v_00_u03b2_1667_, v_x_1668_, v_x_1669_);
lean_dec_ref(v_x_1669_);
lean_dec(v_x_1668_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v_h__1_1673_, lean_object* v_h__2_1674_, lean_object* v_h__3_1675_){
_start:
{
if (lean_obj_tag(v_x_1671_) == 0)
{
lean_object* v_r_1676_; 
lean_dec(v_h__1_1673_);
v_r_1676_ = lean_ctor_get(v_x_1671_, 4);
if (lean_obj_tag(v_r_1676_) == 0)
{
lean_object* v_size_1677_; lean_object* v_k_1678_; lean_object* v_v_1679_; lean_object* v_l_1680_; lean_object* v_size_1681_; lean_object* v_k_1682_; lean_object* v_v_1683_; lean_object* v_l_1684_; lean_object* v_r_1685_; lean_object* v___x_1686_; 
lean_inc_ref(v_r_1676_);
lean_dec(v_h__2_1674_);
v_size_1677_ = lean_ctor_get(v_x_1671_, 0);
lean_inc(v_size_1677_);
v_k_1678_ = lean_ctor_get(v_x_1671_, 1);
lean_inc(v_k_1678_);
v_v_1679_ = lean_ctor_get(v_x_1671_, 2);
lean_inc(v_v_1679_);
v_l_1680_ = lean_ctor_get(v_x_1671_, 3);
lean_inc(v_l_1680_);
lean_dec_ref_known(v_x_1671_, 5);
v_size_1681_ = lean_ctor_get(v_r_1676_, 0);
lean_inc(v_size_1681_);
v_k_1682_ = lean_ctor_get(v_r_1676_, 1);
lean_inc(v_k_1682_);
v_v_1683_ = lean_ctor_get(v_r_1676_, 2);
lean_inc(v_v_1683_);
v_l_1684_ = lean_ctor_get(v_r_1676_, 3);
lean_inc(v_l_1684_);
v_r_1685_ = lean_ctor_get(v_r_1676_, 4);
lean_inc(v_r_1685_);
lean_dec_ref_known(v_r_1676_, 5);
v___x_1686_ = lean_apply_10(v_h__3_1675_, v_size_1677_, v_k_1678_, v_v_1679_, v_l_1680_, v_size_1681_, v_k_1682_, v_v_1683_, v_l_1684_, v_r_1685_, v_x_1672_);
return v___x_1686_;
}
else
{
lean_object* v_size_1687_; lean_object* v_k_1688_; lean_object* v_v_1689_; lean_object* v_l_1690_; lean_object* v___x_1691_; 
lean_dec(v_h__3_1675_);
v_size_1687_ = lean_ctor_get(v_x_1671_, 0);
lean_inc(v_size_1687_);
v_k_1688_ = lean_ctor_get(v_x_1671_, 1);
lean_inc(v_k_1688_);
v_v_1689_ = lean_ctor_get(v_x_1671_, 2);
lean_inc(v_v_1689_);
v_l_1690_ = lean_ctor_get(v_x_1671_, 3);
lean_inc(v_l_1690_);
lean_dec_ref_known(v_x_1671_, 5);
v___x_1691_ = lean_apply_5(v_h__2_1674_, v_size_1687_, v_k_1688_, v_v_1689_, v_l_1690_, v_x_1672_);
return v___x_1691_;
}
}
else
{
lean_object* v___x_1692_; 
lean_dec(v_h__3_1675_);
lean_dec(v_h__2_1674_);
v___x_1692_ = lean_apply_1(v_h__1_1673_, v_x_1672_);
return v___x_1692_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1693_, lean_object* v_00_u03b2_1694_, lean_object* v_motive_1695_, lean_object* v_x_1696_, lean_object* v_x_1697_, lean_object* v_h__1_1698_, lean_object* v_h__2_1699_, lean_object* v_h__3_1700_){
_start:
{
if (lean_obj_tag(v_x_1696_) == 0)
{
lean_object* v_r_1701_; 
lean_dec(v_h__1_1698_);
v_r_1701_ = lean_ctor_get(v_x_1696_, 4);
if (lean_obj_tag(v_r_1701_) == 0)
{
lean_object* v_size_1702_; lean_object* v_k_1703_; lean_object* v_v_1704_; lean_object* v_l_1705_; lean_object* v_size_1706_; lean_object* v_k_1707_; lean_object* v_v_1708_; lean_object* v_l_1709_; lean_object* v_r_1710_; lean_object* v___x_1711_; 
lean_inc_ref(v_r_1701_);
lean_dec(v_h__2_1699_);
v_size_1702_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_size_1702_);
v_k_1703_ = lean_ctor_get(v_x_1696_, 1);
lean_inc(v_k_1703_);
v_v_1704_ = lean_ctor_get(v_x_1696_, 2);
lean_inc(v_v_1704_);
v_l_1705_ = lean_ctor_get(v_x_1696_, 3);
lean_inc(v_l_1705_);
lean_dec_ref_known(v_x_1696_, 5);
v_size_1706_ = lean_ctor_get(v_r_1701_, 0);
lean_inc(v_size_1706_);
v_k_1707_ = lean_ctor_get(v_r_1701_, 1);
lean_inc(v_k_1707_);
v_v_1708_ = lean_ctor_get(v_r_1701_, 2);
lean_inc(v_v_1708_);
v_l_1709_ = lean_ctor_get(v_r_1701_, 3);
lean_inc(v_l_1709_);
v_r_1710_ = lean_ctor_get(v_r_1701_, 4);
lean_inc(v_r_1710_);
lean_dec_ref_known(v_r_1701_, 5);
v___x_1711_ = lean_apply_10(v_h__3_1700_, v_size_1702_, v_k_1703_, v_v_1704_, v_l_1705_, v_size_1706_, v_k_1707_, v_v_1708_, v_l_1709_, v_r_1710_, v_x_1697_);
return v___x_1711_;
}
else
{
lean_object* v_size_1712_; lean_object* v_k_1713_; lean_object* v_v_1714_; lean_object* v_l_1715_; lean_object* v___x_1716_; 
lean_dec(v_h__3_1700_);
v_size_1712_ = lean_ctor_get(v_x_1696_, 0);
lean_inc(v_size_1712_);
v_k_1713_ = lean_ctor_get(v_x_1696_, 1);
lean_inc(v_k_1713_);
v_v_1714_ = lean_ctor_get(v_x_1696_, 2);
lean_inc(v_v_1714_);
v_l_1715_ = lean_ctor_get(v_x_1696_, 3);
lean_inc(v_l_1715_);
lean_dec_ref_known(v_x_1696_, 5);
v___x_1716_ = lean_apply_5(v_h__2_1699_, v_size_1712_, v_k_1713_, v_v_1714_, v_l_1715_, v_x_1697_);
return v___x_1716_;
}
}
else
{
lean_object* v___x_1717_; 
lean_dec(v_h__3_1700_);
lean_dec(v_h__2_1699_);
v___x_1717_ = lean_apply_1(v_h__1_1698_, v_x_1697_);
return v___x_1717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object* v_x_1718_){
_start:
{
if (lean_obj_tag(v_x_1718_) == 0)
{
lean_object* v_l_1719_; 
v_l_1719_ = lean_ctor_get(v_x_1718_, 3);
if (lean_obj_tag(v_l_1719_) == 0)
{
v_x_1718_ = v_l_1719_;
goto _start;
}
else
{
lean_object* v_k_1721_; lean_object* v___x_1722_; 
v_k_1721_ = lean_ctor_get(v_x_1718_, 1);
lean_inc(v_k_1721_);
v___x_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1722_, 0, v_k_1721_);
return v___x_1722_;
}
}
else
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_box(0);
return v___x_1723_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg___boxed(lean_object* v_x_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1724_);
lean_dec(v_x_1724_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f(lean_object* v_00_u03b1_1726_, lean_object* v_00_u03b2_1727_, lean_object* v_x_1728_){
_start:
{
lean_object* v___x_1729_; 
v___x_1729_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1728_);
return v___x_1729_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___boxed(lean_object* v_00_u03b1_1730_, lean_object* v_00_u03b2_1731_, lean_object* v_x_1732_){
_start:
{
lean_object* v_res_1733_; 
v_res_1733_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f(v_00_u03b1_1730_, v_00_u03b2_1731_, v_x_1732_);
lean_dec(v_x_1732_);
return v_res_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object* v_x_1734_){
_start:
{
lean_object* v_l_1735_; 
v_l_1735_ = lean_ctor_get(v_x_1734_, 3);
if (lean_obj_tag(v_l_1735_) == 0)
{
v_x_1734_ = v_l_1735_;
goto _start;
}
else
{
lean_object* v_k_1737_; 
v_k_1737_ = lean_ctor_get(v_x_1734_, 1);
lean_inc(v_k_1737_);
return v_k_1737_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg___boxed(lean_object* v_x_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1738_);
lean_dec(v_x_1738_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey(lean_object* v_00_u03b1_1740_, lean_object* v_00_u03b2_1741_, lean_object* v_x_1742_, lean_object* v_x_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___boxed(lean_object* v_00_u03b1_1745_, lean_object* v_00_u03b2_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l_Std_DTreeMap_Internal_Impl_minKey(v_00_u03b1_1745_, v_00_u03b2_1746_, v_x_1747_, v_x_1748_);
lean_dec(v_x_1747_);
return v_res_1749_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1751_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1752_ = lean_unsigned_to_nat(13u);
v___x_1753_ = lean_unsigned_to_nat(413u);
v___x_1754_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0));
v___x_1755_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1756_ = l_mkPanicMessageWithDecl(v___x_1755_, v___x_1754_, v___x_1753_, v___x_1752_, v___x_1751_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object* v_inst_1757_, lean_object* v_x_1758_){
_start:
{
if (lean_obj_tag(v_x_1758_) == 0)
{
lean_object* v_l_1759_; 
v_l_1759_ = lean_ctor_get(v_x_1758_, 3);
if (lean_obj_tag(v_l_1759_) == 0)
{
v_x_1758_ = v_l_1759_;
goto _start;
}
else
{
lean_object* v_k_1761_; 
v_k_1761_ = lean_ctor_get(v_x_1758_, 1);
lean_inc(v_k_1761_);
return v_k_1761_;
}
}
else
{
lean_object* v___x_1762_; lean_object* v___x_1763_; 
v___x_1762_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1);
v___x_1763_ = l_panic___redArg(v_inst_1757_, v___x_1762_);
return v___x_1763_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___boxed(lean_object* v_inst_1764_, lean_object* v_x_1765_){
_start:
{
lean_object* v_res_1766_; 
v_res_1766_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1764_, v_x_1765_);
lean_dec(v_x_1765_);
lean_dec(v_inst_1764_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21(lean_object* v_00_u03b1_1767_, lean_object* v_00_u03b2_1768_, lean_object* v_inst_1769_, lean_object* v_x_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1769_, v_x_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___boxed(lean_object* v_00_u03b1_1772_, lean_object* v_00_u03b2_1773_, lean_object* v_inst_1774_, lean_object* v_x_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Std_DTreeMap_Internal_Impl_minKey_x21(v_00_u03b1_1772_, v_00_u03b2_1773_, v_inst_1774_, v_x_1775_);
lean_dec(v_x_1775_);
lean_dec(v_inst_1774_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object* v_x_1777_, lean_object* v_x_1778_){
_start:
{
if (lean_obj_tag(v_x_1777_) == 0)
{
lean_object* v_l_1779_; 
v_l_1779_ = lean_ctor_get(v_x_1777_, 3);
if (lean_obj_tag(v_l_1779_) == 0)
{
v_x_1777_ = v_l_1779_;
goto _start;
}
else
{
lean_object* v_k_1781_; 
v_k_1781_ = lean_ctor_get(v_x_1777_, 1);
lean_inc(v_k_1781_);
return v_k_1781_;
}
}
else
{
lean_inc(v_x_1778_);
return v_x_1778_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg___boxed(lean_object* v_x_1782_, lean_object* v_x_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1782_, v_x_1783_);
lean_dec(v_x_1783_);
lean_dec(v_x_1782_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD(lean_object* v_00_u03b1_1785_, lean_object* v_00_u03b2_1786_, lean_object* v_x_1787_, lean_object* v_x_1788_){
_start:
{
lean_object* v___x_1789_; 
v___x_1789_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1787_, v_x_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___boxed(lean_object* v_00_u03b1_1790_, lean_object* v_00_u03b2_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_Std_DTreeMap_Internal_Impl_minKeyD(v_00_u03b1_1790_, v_00_u03b2_1791_, v_x_1792_, v_x_1793_);
lean_dec(v_x_1793_);
lean_dec(v_x_1792_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1795_, lean_object* v_x_1796_, lean_object* v_h__1_1797_, lean_object* v_h__2_1798_, lean_object* v_h__3_1799_){
_start:
{
if (lean_obj_tag(v_x_1795_) == 0)
{
lean_object* v_l_1800_; 
lean_dec(v_h__1_1797_);
v_l_1800_ = lean_ctor_get(v_x_1795_, 3);
if (lean_obj_tag(v_l_1800_) == 0)
{
lean_object* v_size_1801_; lean_object* v_k_1802_; lean_object* v_v_1803_; lean_object* v_r_1804_; lean_object* v_size_1805_; lean_object* v_k_1806_; lean_object* v_v_1807_; lean_object* v_l_1808_; lean_object* v_r_1809_; lean_object* v___x_1810_; 
lean_inc_ref(v_l_1800_);
lean_dec(v_h__2_1798_);
v_size_1801_ = lean_ctor_get(v_x_1795_, 0);
lean_inc(v_size_1801_);
v_k_1802_ = lean_ctor_get(v_x_1795_, 1);
lean_inc(v_k_1802_);
v_v_1803_ = lean_ctor_get(v_x_1795_, 2);
lean_inc(v_v_1803_);
v_r_1804_ = lean_ctor_get(v_x_1795_, 4);
lean_inc(v_r_1804_);
lean_dec_ref_known(v_x_1795_, 5);
v_size_1805_ = lean_ctor_get(v_l_1800_, 0);
lean_inc(v_size_1805_);
v_k_1806_ = lean_ctor_get(v_l_1800_, 1);
lean_inc(v_k_1806_);
v_v_1807_ = lean_ctor_get(v_l_1800_, 2);
lean_inc(v_v_1807_);
v_l_1808_ = lean_ctor_get(v_l_1800_, 3);
lean_inc(v_l_1808_);
v_r_1809_ = lean_ctor_get(v_l_1800_, 4);
lean_inc(v_r_1809_);
lean_dec_ref_known(v_l_1800_, 5);
v___x_1810_ = lean_apply_10(v_h__3_1799_, v_size_1801_, v_k_1802_, v_v_1803_, v_size_1805_, v_k_1806_, v_v_1807_, v_l_1808_, v_r_1809_, v_r_1804_, v_x_1796_);
return v___x_1810_;
}
else
{
lean_object* v_size_1811_; lean_object* v_k_1812_; lean_object* v_v_1813_; lean_object* v_r_1814_; lean_object* v___x_1815_; 
lean_dec(v_h__3_1799_);
v_size_1811_ = lean_ctor_get(v_x_1795_, 0);
lean_inc(v_size_1811_);
v_k_1812_ = lean_ctor_get(v_x_1795_, 1);
lean_inc(v_k_1812_);
v_v_1813_ = lean_ctor_get(v_x_1795_, 2);
lean_inc(v_v_1813_);
v_r_1814_ = lean_ctor_get(v_x_1795_, 4);
lean_inc(v_r_1814_);
lean_dec_ref_known(v_x_1795_, 5);
v___x_1815_ = lean_apply_5(v_h__2_1798_, v_size_1811_, v_k_1812_, v_v_1813_, v_r_1814_, v_x_1796_);
return v___x_1815_;
}
}
else
{
lean_object* v___x_1816_; 
lean_dec(v_h__3_1799_);
lean_dec(v_h__2_1798_);
v___x_1816_ = lean_apply_1(v_h__1_1797_, v_x_1796_);
return v___x_1816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1817_, lean_object* v_00_u03b2_1818_, lean_object* v_motive_1819_, lean_object* v_x_1820_, lean_object* v_x_1821_, lean_object* v_h__1_1822_, lean_object* v_h__2_1823_, lean_object* v_h__3_1824_){
_start:
{
if (lean_obj_tag(v_x_1820_) == 0)
{
lean_object* v_l_1825_; 
lean_dec(v_h__1_1822_);
v_l_1825_ = lean_ctor_get(v_x_1820_, 3);
if (lean_obj_tag(v_l_1825_) == 0)
{
lean_object* v_size_1826_; lean_object* v_k_1827_; lean_object* v_v_1828_; lean_object* v_r_1829_; lean_object* v_size_1830_; lean_object* v_k_1831_; lean_object* v_v_1832_; lean_object* v_l_1833_; lean_object* v_r_1834_; lean_object* v___x_1835_; 
lean_inc_ref(v_l_1825_);
lean_dec(v_h__2_1823_);
v_size_1826_ = lean_ctor_get(v_x_1820_, 0);
lean_inc(v_size_1826_);
v_k_1827_ = lean_ctor_get(v_x_1820_, 1);
lean_inc(v_k_1827_);
v_v_1828_ = lean_ctor_get(v_x_1820_, 2);
lean_inc(v_v_1828_);
v_r_1829_ = lean_ctor_get(v_x_1820_, 4);
lean_inc(v_r_1829_);
lean_dec_ref_known(v_x_1820_, 5);
v_size_1830_ = lean_ctor_get(v_l_1825_, 0);
lean_inc(v_size_1830_);
v_k_1831_ = lean_ctor_get(v_l_1825_, 1);
lean_inc(v_k_1831_);
v_v_1832_ = lean_ctor_get(v_l_1825_, 2);
lean_inc(v_v_1832_);
v_l_1833_ = lean_ctor_get(v_l_1825_, 3);
lean_inc(v_l_1833_);
v_r_1834_ = lean_ctor_get(v_l_1825_, 4);
lean_inc(v_r_1834_);
lean_dec_ref_known(v_l_1825_, 5);
v___x_1835_ = lean_apply_10(v_h__3_1824_, v_size_1826_, v_k_1827_, v_v_1828_, v_size_1830_, v_k_1831_, v_v_1832_, v_l_1833_, v_r_1834_, v_r_1829_, v_x_1821_);
return v___x_1835_;
}
else
{
lean_object* v_size_1836_; lean_object* v_k_1837_; lean_object* v_v_1838_; lean_object* v_r_1839_; lean_object* v___x_1840_; 
lean_dec(v_h__3_1824_);
v_size_1836_ = lean_ctor_get(v_x_1820_, 0);
lean_inc(v_size_1836_);
v_k_1837_ = lean_ctor_get(v_x_1820_, 1);
lean_inc(v_k_1837_);
v_v_1838_ = lean_ctor_get(v_x_1820_, 2);
lean_inc(v_v_1838_);
v_r_1839_ = lean_ctor_get(v_x_1820_, 4);
lean_inc(v_r_1839_);
lean_dec_ref_known(v_x_1820_, 5);
v___x_1840_ = lean_apply_5(v_h__2_1823_, v_size_1836_, v_k_1837_, v_v_1838_, v_r_1839_, v_x_1821_);
return v___x_1840_;
}
}
else
{
lean_object* v___x_1841_; 
lean_dec(v_h__3_1824_);
lean_dec(v_h__2_1823_);
v___x_1841_ = lean_apply_1(v_h__1_1822_, v_x_1821_);
return v___x_1841_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object* v_x_1842_){
_start:
{
if (lean_obj_tag(v_x_1842_) == 0)
{
lean_object* v_r_1843_; 
v_r_1843_ = lean_ctor_get(v_x_1842_, 4);
if (lean_obj_tag(v_r_1843_) == 0)
{
v_x_1842_ = v_r_1843_;
goto _start;
}
else
{
lean_object* v_k_1845_; lean_object* v___x_1846_; 
v_k_1845_ = lean_ctor_get(v_x_1842_, 1);
lean_inc(v_k_1845_);
v___x_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1846_, 0, v_k_1845_);
return v___x_1846_;
}
}
else
{
lean_object* v___x_1847_; 
v___x_1847_ = lean_box(0);
return v___x_1847_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg___boxed(lean_object* v_x_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1848_);
lean_dec(v_x_1848_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f(lean_object* v_00_u03b1_1850_, lean_object* v_00_u03b2_1851_, lean_object* v_x_1852_){
_start:
{
lean_object* v___x_1853_; 
v___x_1853_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1852_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___boxed(lean_object* v_00_u03b1_1854_, lean_object* v_00_u03b2_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f(v_00_u03b1_1854_, v_00_u03b2_1855_, v_x_1856_);
lean_dec(v_x_1856_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object* v_x_1858_){
_start:
{
lean_object* v_r_1859_; 
v_r_1859_ = lean_ctor_get(v_x_1858_, 4);
if (lean_obj_tag(v_r_1859_) == 0)
{
v_x_1858_ = v_r_1859_;
goto _start;
}
else
{
lean_object* v_k_1861_; 
v_k_1861_ = lean_ctor_get(v_x_1858_, 1);
lean_inc(v_k_1861_);
return v_k_1861_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg___boxed(lean_object* v_x_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1862_);
lean_dec(v_x_1862_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey(lean_object* v_00_u03b1_1864_, lean_object* v_00_u03b2_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1866_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___boxed(lean_object* v_00_u03b1_1869_, lean_object* v_00_u03b2_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Std_DTreeMap_Internal_Impl_maxKey(v_00_u03b1_1869_, v_00_u03b2_1870_, v_x_1871_, v_x_1872_);
lean_dec(v_x_1871_);
return v_res_1873_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1875_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1876_ = lean_unsigned_to_nat(13u);
v___x_1877_ = lean_unsigned_to_nat(436u);
v___x_1878_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0));
v___x_1879_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1880_ = l_mkPanicMessageWithDecl(v___x_1879_, v___x_1878_, v___x_1877_, v___x_1876_, v___x_1875_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object* v_inst_1881_, lean_object* v_x_1882_){
_start:
{
if (lean_obj_tag(v_x_1882_) == 0)
{
lean_object* v_r_1883_; 
v_r_1883_ = lean_ctor_get(v_x_1882_, 4);
if (lean_obj_tag(v_r_1883_) == 0)
{
v_x_1882_ = v_r_1883_;
goto _start;
}
else
{
lean_object* v_k_1885_; 
v_k_1885_ = lean_ctor_get(v_x_1882_, 1);
lean_inc(v_k_1885_);
return v_k_1885_;
}
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1);
v___x_1887_ = l_panic___redArg(v_inst_1881_, v___x_1886_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___boxed(lean_object* v_inst_1888_, lean_object* v_x_1889_){
_start:
{
lean_object* v_res_1890_; 
v_res_1890_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1888_, v_x_1889_);
lean_dec(v_x_1889_);
lean_dec(v_inst_1888_);
return v_res_1890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21(lean_object* v_00_u03b1_1891_, lean_object* v_00_u03b2_1892_, lean_object* v_inst_1893_, lean_object* v_x_1894_){
_start:
{
lean_object* v___x_1895_; 
v___x_1895_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1893_, v_x_1894_);
return v___x_1895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___boxed(lean_object* v_00_u03b1_1896_, lean_object* v_00_u03b2_1897_, lean_object* v_inst_1898_, lean_object* v_x_1899_){
_start:
{
lean_object* v_res_1900_; 
v_res_1900_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21(v_00_u03b1_1896_, v_00_u03b2_1897_, v_inst_1898_, v_x_1899_);
lean_dec(v_x_1899_);
lean_dec(v_inst_1898_);
return v_res_1900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object* v_x_1901_, lean_object* v_x_1902_){
_start:
{
if (lean_obj_tag(v_x_1901_) == 0)
{
lean_object* v_r_1903_; 
v_r_1903_ = lean_ctor_get(v_x_1901_, 4);
if (lean_obj_tag(v_r_1903_) == 0)
{
v_x_1901_ = v_r_1903_;
goto _start;
}
else
{
lean_object* v_k_1905_; 
v_k_1905_ = lean_ctor_get(v_x_1901_, 1);
lean_inc(v_k_1905_);
return v_k_1905_;
}
}
else
{
lean_inc(v_x_1902_);
return v_x_1902_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg___boxed(lean_object* v_x_1906_, lean_object* v_x_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1906_, v_x_1907_);
lean_dec(v_x_1907_);
lean_dec(v_x_1906_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD(lean_object* v_00_u03b1_1909_, lean_object* v_00_u03b2_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1911_, v_x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___boxed(lean_object* v_00_u03b1_1914_, lean_object* v_00_u03b2_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_Std_DTreeMap_Internal_Impl_maxKeyD(v_00_u03b1_1914_, v_00_u03b2_1915_, v_x_1916_, v_x_1917_);
lean_dec(v_x_1917_);
lean_dec(v_x_1916_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v_h__1_1921_, lean_object* v_h__2_1922_, lean_object* v_h__3_1923_){
_start:
{
if (lean_obj_tag(v_x_1919_) == 0)
{
lean_object* v_r_1924_; 
lean_dec(v_h__1_1921_);
v_r_1924_ = lean_ctor_get(v_x_1919_, 4);
if (lean_obj_tag(v_r_1924_) == 0)
{
lean_object* v_size_1925_; lean_object* v_k_1926_; lean_object* v_v_1927_; lean_object* v_l_1928_; lean_object* v_size_1929_; lean_object* v_k_1930_; lean_object* v_v_1931_; lean_object* v_l_1932_; lean_object* v_r_1933_; lean_object* v___x_1934_; 
lean_inc_ref(v_r_1924_);
lean_dec(v_h__2_1922_);
v_size_1925_ = lean_ctor_get(v_x_1919_, 0);
lean_inc(v_size_1925_);
v_k_1926_ = lean_ctor_get(v_x_1919_, 1);
lean_inc(v_k_1926_);
v_v_1927_ = lean_ctor_get(v_x_1919_, 2);
lean_inc(v_v_1927_);
v_l_1928_ = lean_ctor_get(v_x_1919_, 3);
lean_inc(v_l_1928_);
lean_dec_ref_known(v_x_1919_, 5);
v_size_1929_ = lean_ctor_get(v_r_1924_, 0);
lean_inc(v_size_1929_);
v_k_1930_ = lean_ctor_get(v_r_1924_, 1);
lean_inc(v_k_1930_);
v_v_1931_ = lean_ctor_get(v_r_1924_, 2);
lean_inc(v_v_1931_);
v_l_1932_ = lean_ctor_get(v_r_1924_, 3);
lean_inc(v_l_1932_);
v_r_1933_ = lean_ctor_get(v_r_1924_, 4);
lean_inc(v_r_1933_);
lean_dec_ref_known(v_r_1924_, 5);
v___x_1934_ = lean_apply_10(v_h__3_1923_, v_size_1925_, v_k_1926_, v_v_1927_, v_l_1928_, v_size_1929_, v_k_1930_, v_v_1931_, v_l_1932_, v_r_1933_, v_x_1920_);
return v___x_1934_;
}
else
{
lean_object* v_size_1935_; lean_object* v_k_1936_; lean_object* v_v_1937_; lean_object* v_l_1938_; lean_object* v___x_1939_; 
lean_dec(v_h__3_1923_);
v_size_1935_ = lean_ctor_get(v_x_1919_, 0);
lean_inc(v_size_1935_);
v_k_1936_ = lean_ctor_get(v_x_1919_, 1);
lean_inc(v_k_1936_);
v_v_1937_ = lean_ctor_get(v_x_1919_, 2);
lean_inc(v_v_1937_);
v_l_1938_ = lean_ctor_get(v_x_1919_, 3);
lean_inc(v_l_1938_);
lean_dec_ref_known(v_x_1919_, 5);
v___x_1939_ = lean_apply_5(v_h__2_1922_, v_size_1935_, v_k_1936_, v_v_1937_, v_l_1938_, v_x_1920_);
return v___x_1939_;
}
}
else
{
lean_object* v___x_1940_; 
lean_dec(v_h__3_1923_);
lean_dec(v_h__2_1922_);
v___x_1940_ = lean_apply_1(v_h__1_1921_, v_x_1920_);
return v___x_1940_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1941_, lean_object* v_00_u03b2_1942_, lean_object* v_motive_1943_, lean_object* v_x_1944_, lean_object* v_x_1945_, lean_object* v_h__1_1946_, lean_object* v_h__2_1947_, lean_object* v_h__3_1948_){
_start:
{
if (lean_obj_tag(v_x_1944_) == 0)
{
lean_object* v_r_1949_; 
lean_dec(v_h__1_1946_);
v_r_1949_ = lean_ctor_get(v_x_1944_, 4);
if (lean_obj_tag(v_r_1949_) == 0)
{
lean_object* v_size_1950_; lean_object* v_k_1951_; lean_object* v_v_1952_; lean_object* v_l_1953_; lean_object* v_size_1954_; lean_object* v_k_1955_; lean_object* v_v_1956_; lean_object* v_l_1957_; lean_object* v_r_1958_; lean_object* v___x_1959_; 
lean_inc_ref(v_r_1949_);
lean_dec(v_h__2_1947_);
v_size_1950_ = lean_ctor_get(v_x_1944_, 0);
lean_inc(v_size_1950_);
v_k_1951_ = lean_ctor_get(v_x_1944_, 1);
lean_inc(v_k_1951_);
v_v_1952_ = lean_ctor_get(v_x_1944_, 2);
lean_inc(v_v_1952_);
v_l_1953_ = lean_ctor_get(v_x_1944_, 3);
lean_inc(v_l_1953_);
lean_dec_ref_known(v_x_1944_, 5);
v_size_1954_ = lean_ctor_get(v_r_1949_, 0);
lean_inc(v_size_1954_);
v_k_1955_ = lean_ctor_get(v_r_1949_, 1);
lean_inc(v_k_1955_);
v_v_1956_ = lean_ctor_get(v_r_1949_, 2);
lean_inc(v_v_1956_);
v_l_1957_ = lean_ctor_get(v_r_1949_, 3);
lean_inc(v_l_1957_);
v_r_1958_ = lean_ctor_get(v_r_1949_, 4);
lean_inc(v_r_1958_);
lean_dec_ref_known(v_r_1949_, 5);
v___x_1959_ = lean_apply_10(v_h__3_1948_, v_size_1950_, v_k_1951_, v_v_1952_, v_l_1953_, v_size_1954_, v_k_1955_, v_v_1956_, v_l_1957_, v_r_1958_, v_x_1945_);
return v___x_1959_;
}
else
{
lean_object* v_size_1960_; lean_object* v_k_1961_; lean_object* v_v_1962_; lean_object* v_l_1963_; lean_object* v___x_1964_; 
lean_dec(v_h__3_1948_);
v_size_1960_ = lean_ctor_get(v_x_1944_, 0);
lean_inc(v_size_1960_);
v_k_1961_ = lean_ctor_get(v_x_1944_, 1);
lean_inc(v_k_1961_);
v_v_1962_ = lean_ctor_get(v_x_1944_, 2);
lean_inc(v_v_1962_);
v_l_1963_ = lean_ctor_get(v_x_1944_, 3);
lean_inc(v_l_1963_);
lean_dec_ref_known(v_x_1944_, 5);
v___x_1964_ = lean_apply_5(v_h__2_1947_, v_size_1960_, v_k_1961_, v_v_1962_, v_l_1963_, v_x_1945_);
return v___x_1964_;
}
}
else
{
lean_object* v___x_1965_; 
lean_dec(v_h__3_1948_);
lean_dec(v_h__2_1947_);
v___x_1965_ = lean_apply_1(v_h__1_1946_, v_x_1945_);
return v___x_1965_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object* v_x_1966_, lean_object* v_x_1967_){
_start:
{
lean_object* v_k_1968_; lean_object* v_v_1969_; lean_object* v_l_1970_; lean_object* v_r_1971_; lean_object* v___y_1973_; lean_object* v___y_1979_; 
v_k_1968_ = lean_ctor_get(v_x_1966_, 1);
v_v_1969_ = lean_ctor_get(v_x_1966_, 2);
v_l_1970_ = lean_ctor_get(v_x_1966_, 3);
v_r_1971_ = lean_ctor_get(v_x_1966_, 4);
if (lean_obj_tag(v_l_1970_) == 0)
{
lean_object* v_size_1986_; 
v_size_1986_ = lean_ctor_get(v_l_1970_, 0);
v___y_1979_ = v_size_1986_;
goto v___jp_1978_;
}
else
{
lean_object* v___x_1987_; 
v___x_1987_ = lean_unsigned_to_nat(0u);
v___y_1979_ = v___x_1987_;
goto v___jp_1978_;
}
v___jp_1972_:
{
lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = lean_nat_sub(v_x_1967_, v___y_1973_);
lean_dec(v_x_1967_);
v___x_1975_ = lean_unsigned_to_nat(1u);
v___x_1976_ = lean_nat_sub(v___x_1974_, v___x_1975_);
lean_dec(v___x_1974_);
v_x_1966_ = v_r_1971_;
v_x_1967_ = v___x_1976_;
goto _start;
}
v___jp_1978_:
{
uint8_t v___x_1980_; 
v___x_1980_ = lean_nat_dec_lt(v_x_1967_, v___y_1979_);
if (v___x_1980_ == 0)
{
uint8_t v___x_1981_; 
v___x_1981_ = lean_nat_dec_eq(v_x_1967_, v___y_1979_);
if (v___x_1981_ == 0)
{
if (lean_obj_tag(v_l_1970_) == 0)
{
lean_object* v_size_1982_; 
v_size_1982_ = lean_ctor_get(v_l_1970_, 0);
v___y_1973_ = v_size_1982_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_unsigned_to_nat(0u);
v___y_1973_ = v___x_1983_;
goto v___jp_1972_;
}
}
else
{
lean_object* v___x_1984_; 
lean_dec(v_x_1967_);
lean_inc(v_v_1969_);
lean_inc(v_k_1968_);
v___x_1984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1984_, 0, v_k_1968_);
lean_ctor_set(v___x_1984_, 1, v_v_1969_);
return v___x_1984_;
}
}
else
{
v_x_1966_ = v_l_1970_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg___boxed(lean_object* v_x_1988_, lean_object* v_x_1989_){
_start:
{
lean_object* v_res_1990_; 
v_res_1990_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1988_, v_x_1989_);
lean_dec(v_x_1988_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx(lean_object* v_00_u03b1_1991_, lean_object* v_00_u03b2_1992_, lean_object* v_x_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1993_, v_x_1995_);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___boxed(lean_object* v_00_u03b1_1998_, lean_object* v_00_u03b2_1999_, lean_object* v_x_2000_, lean_object* v_x_2001_, lean_object* v_x_2002_, lean_object* v_x_2003_){
_start:
{
lean_object* v_res_2004_; 
v_res_2004_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx(v_00_u03b1_1998_, v_00_u03b2_1999_, v_x_2000_, v_x_2001_, v_x_2002_, v_x_2003_);
lean_dec(v_x_2000_);
return v_res_2004_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object* v_x_2005_, lean_object* v_x_2006_){
_start:
{
if (lean_obj_tag(v_x_2005_) == 0)
{
lean_object* v_k_2007_; lean_object* v_v_2008_; lean_object* v_l_2009_; lean_object* v_r_2010_; lean_object* v___y_2012_; lean_object* v___y_2018_; 
v_k_2007_ = lean_ctor_get(v_x_2005_, 1);
v_v_2008_ = lean_ctor_get(v_x_2005_, 2);
v_l_2009_ = lean_ctor_get(v_x_2005_, 3);
v_r_2010_ = lean_ctor_get(v_x_2005_, 4);
if (lean_obj_tag(v_l_2009_) == 0)
{
lean_object* v_size_2026_; 
v_size_2026_ = lean_ctor_get(v_l_2009_, 0);
v___y_2018_ = v_size_2026_;
goto v___jp_2017_;
}
else
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_unsigned_to_nat(0u);
v___y_2018_ = v___x_2027_;
goto v___jp_2017_;
}
v___jp_2011_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; 
v___x_2013_ = lean_nat_sub(v_x_2006_, v___y_2012_);
lean_dec(v_x_2006_);
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = lean_nat_sub(v___x_2013_, v___x_2014_);
lean_dec(v___x_2013_);
v_x_2005_ = v_r_2010_;
v_x_2006_ = v___x_2015_;
goto _start;
}
v___jp_2017_:
{
uint8_t v___x_2019_; 
v___x_2019_ = lean_nat_dec_lt(v_x_2006_, v___y_2018_);
if (v___x_2019_ == 0)
{
uint8_t v___x_2020_; 
v___x_2020_ = lean_nat_dec_eq(v_x_2006_, v___y_2018_);
if (v___x_2020_ == 0)
{
if (lean_obj_tag(v_l_2009_) == 0)
{
lean_object* v_size_2021_; 
v_size_2021_ = lean_ctor_get(v_l_2009_, 0);
v___y_2012_ = v_size_2021_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_unsigned_to_nat(0u);
v___y_2012_ = v___x_2022_;
goto v___jp_2011_;
}
}
else
{
lean_object* v___x_2023_; lean_object* v___x_2024_; 
lean_dec(v_x_2006_);
lean_inc(v_v_2008_);
lean_inc(v_k_2007_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v_k_2007_);
lean_ctor_set(v___x_2023_, 1, v_v_2008_);
v___x_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
return v___x_2024_;
}
}
else
{
v_x_2005_ = v_l_2009_;
goto _start;
}
}
}
else
{
lean_object* v___x_2028_; 
lean_dec(v_x_2006_);
v___x_2028_ = lean_box(0);
return v___x_2028_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_2029_, lean_object* v_x_2030_){
_start:
{
lean_object* v_res_2031_; 
v_res_2031_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_2029_, v_x_2030_);
lean_dec(v_x_2029_);
return v_res_2031_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(lean_object* v_00_u03b1_2032_, lean_object* v_00_u03b2_2033_, lean_object* v_x_2034_, lean_object* v_x_2035_){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_2034_, v_x_2035_);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_2037_, lean_object* v_00_u03b2_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(v_00_u03b1_2037_, v_00_u03b2_2038_, v_x_2039_, v_x_2040_);
lean_dec(v_x_2039_);
return v_res_2041_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2044_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_2045_ = lean_unsigned_to_nat(16u);
v___x_2046_ = lean_unsigned_to_nat(467u);
v___x_2047_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0));
v___x_2048_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_2049_ = l_mkPanicMessageWithDecl(v___x_2048_, v___x_2047_, v___x_2046_, v___x_2045_, v___x_2044_);
return v___x_2049_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(lean_object* v_inst_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
if (lean_obj_tag(v_x_2051_) == 0)
{
lean_object* v_k_2053_; lean_object* v_v_2054_; lean_object* v_l_2055_; lean_object* v_r_2056_; lean_object* v___y_2058_; lean_object* v___y_2064_; 
v_k_2053_ = lean_ctor_get(v_x_2051_, 1);
v_v_2054_ = lean_ctor_get(v_x_2051_, 2);
v_l_2055_ = lean_ctor_get(v_x_2051_, 3);
v_r_2056_ = lean_ctor_get(v_x_2051_, 4);
if (lean_obj_tag(v_l_2055_) == 0)
{
lean_object* v_size_2071_; 
v_size_2071_ = lean_ctor_get(v_l_2055_, 0);
v___y_2064_ = v_size_2071_;
goto v___jp_2063_;
}
else
{
lean_object* v___x_2072_; 
v___x_2072_ = lean_unsigned_to_nat(0u);
v___y_2064_ = v___x_2072_;
goto v___jp_2063_;
}
v___jp_2057_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = lean_nat_sub(v_x_2052_, v___y_2058_);
lean_dec(v_x_2052_);
v___x_2060_ = lean_unsigned_to_nat(1u);
v___x_2061_ = lean_nat_sub(v___x_2059_, v___x_2060_);
lean_dec(v___x_2059_);
v_x_2051_ = v_r_2056_;
v_x_2052_ = v___x_2061_;
goto _start;
}
v___jp_2063_:
{
uint8_t v___x_2065_; 
v___x_2065_ = lean_nat_dec_lt(v_x_2052_, v___y_2064_);
if (v___x_2065_ == 0)
{
uint8_t v___x_2066_; 
v___x_2066_ = lean_nat_dec_eq(v_x_2052_, v___y_2064_);
if (v___x_2066_ == 0)
{
if (lean_obj_tag(v_l_2055_) == 0)
{
lean_object* v_size_2067_; 
v_size_2067_ = lean_ctor_get(v_l_2055_, 0);
v___y_2058_ = v_size_2067_;
goto v___jp_2057_;
}
else
{
lean_object* v___x_2068_; 
v___x_2068_ = lean_unsigned_to_nat(0u);
v___y_2058_ = v___x_2068_;
goto v___jp_2057_;
}
}
else
{
lean_object* v___x_2069_; 
lean_dec(v_x_2052_);
lean_inc(v_v_2054_);
lean_inc(v_k_2053_);
v___x_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2069_, 0, v_k_2053_);
lean_ctor_set(v___x_2069_, 1, v_v_2054_);
return v___x_2069_;
}
}
else
{
v_x_2051_ = v_l_2055_;
goto _start;
}
}
}
else
{
lean_object* v___x_2073_; lean_object* v___x_2074_; 
lean_dec(v_x_2052_);
v___x_2073_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2);
v___x_2074_ = l_panic___redArg(v_inst_2050_, v___x_2073_);
return v___x_2074_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_2075_, lean_object* v_x_2076_, lean_object* v_x_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2075_, v_x_2076_, v_x_2077_);
lean_dec(v_x_2076_);
lean_dec_ref(v_inst_2075_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(lean_object* v_00_u03b1_2079_, lean_object* v_00_u03b2_2080_, lean_object* v_inst_2081_, lean_object* v_x_2082_, lean_object* v_x_2083_){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2081_, v_x_2082_, v_x_2083_);
return v___x_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_2085_, lean_object* v_00_u03b2_2086_, lean_object* v_inst_2087_, lean_object* v_x_2088_, lean_object* v_x_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(v_00_u03b1_2085_, v_00_u03b2_2086_, v_inst_2087_, v_x_2088_, v_x_2089_);
lean_dec(v_x_2088_);
lean_dec_ref(v_inst_2087_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object* v_x_2091_, lean_object* v_x_2092_, lean_object* v_x_2093_){
_start:
{
if (lean_obj_tag(v_x_2091_) == 0)
{
lean_object* v_k_2094_; lean_object* v_v_2095_; lean_object* v_l_2096_; lean_object* v_r_2097_; lean_object* v___y_2099_; lean_object* v___y_2105_; 
v_k_2094_ = lean_ctor_get(v_x_2091_, 1);
v_v_2095_ = lean_ctor_get(v_x_2091_, 2);
v_l_2096_ = lean_ctor_get(v_x_2091_, 3);
v_r_2097_ = lean_ctor_get(v_x_2091_, 4);
if (lean_obj_tag(v_l_2096_) == 0)
{
lean_object* v_size_2112_; 
v_size_2112_ = lean_ctor_get(v_l_2096_, 0);
v___y_2105_ = v_size_2112_;
goto v___jp_2104_;
}
else
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_unsigned_to_nat(0u);
v___y_2105_ = v___x_2113_;
goto v___jp_2104_;
}
v___jp_2098_:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2100_ = lean_nat_sub(v_x_2092_, v___y_2099_);
lean_dec(v_x_2092_);
v___x_2101_ = lean_unsigned_to_nat(1u);
v___x_2102_ = lean_nat_sub(v___x_2100_, v___x_2101_);
lean_dec(v___x_2100_);
v_x_2091_ = v_r_2097_;
v_x_2092_ = v___x_2102_;
goto _start;
}
v___jp_2104_:
{
uint8_t v___x_2106_; 
v___x_2106_ = lean_nat_dec_lt(v_x_2092_, v___y_2105_);
if (v___x_2106_ == 0)
{
uint8_t v___x_2107_; 
v___x_2107_ = lean_nat_dec_eq(v_x_2092_, v___y_2105_);
if (v___x_2107_ == 0)
{
if (lean_obj_tag(v_l_2096_) == 0)
{
lean_object* v_size_2108_; 
v_size_2108_ = lean_ctor_get(v_l_2096_, 0);
v___y_2099_ = v_size_2108_;
goto v___jp_2098_;
}
else
{
lean_object* v___x_2109_; 
v___x_2109_ = lean_unsigned_to_nat(0u);
v___y_2099_ = v___x_2109_;
goto v___jp_2098_;
}
}
else
{
lean_object* v___x_2110_; 
lean_dec(v_x_2092_);
lean_inc(v_v_2095_);
lean_inc(v_k_2094_);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v_k_2094_);
lean_ctor_set(v___x_2110_, 1, v_v_2095_);
return v___x_2110_;
}
}
else
{
v_x_2091_ = v_l_2096_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2092_);
lean_inc_ref(v_x_2093_);
return v_x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg___boxed(lean_object* v_x_2114_, lean_object* v_x_2115_, lean_object* v_x_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2114_, v_x_2115_, v_x_2116_);
lean_dec_ref(v_x_2116_);
lean_dec(v_x_2114_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD(lean_object* v_00_u03b1_2118_, lean_object* v_00_u03b2_2119_, lean_object* v_x_2120_, lean_object* v_x_2121_, lean_object* v_x_2122_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2120_, v_x_2121_, v_x_2122_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___boxed(lean_object* v_00_u03b1_2124_, lean_object* v_00_u03b2_2125_, lean_object* v_x_2126_, lean_object* v_x_2127_, lean_object* v_x_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD(v_00_u03b1_2124_, v_00_u03b2_2125_, v_x_2126_, v_x_2127_, v_x_2128_);
lean_dec_ref(v_x_2128_);
lean_dec(v_x_2126_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object* v_x_2130_, lean_object* v_x_2131_){
_start:
{
lean_object* v_k_2132_; lean_object* v_l_2133_; lean_object* v_r_2134_; lean_object* v___y_2136_; lean_object* v___y_2142_; 
v_k_2132_ = lean_ctor_get(v_x_2130_, 1);
v_l_2133_ = lean_ctor_get(v_x_2130_, 3);
v_r_2134_ = lean_ctor_get(v_x_2130_, 4);
if (lean_obj_tag(v_l_2133_) == 0)
{
lean_object* v_size_2148_; 
v_size_2148_ = lean_ctor_get(v_l_2133_, 0);
v___y_2142_ = v_size_2148_;
goto v___jp_2141_;
}
else
{
lean_object* v___x_2149_; 
v___x_2149_ = lean_unsigned_to_nat(0u);
v___y_2142_ = v___x_2149_;
goto v___jp_2141_;
}
v___jp_2135_:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_nat_sub(v_x_2131_, v___y_2136_);
lean_dec(v_x_2131_);
v___x_2138_ = lean_unsigned_to_nat(1u);
v___x_2139_ = lean_nat_sub(v___x_2137_, v___x_2138_);
lean_dec(v___x_2137_);
v_x_2130_ = v_r_2134_;
v_x_2131_ = v___x_2139_;
goto _start;
}
v___jp_2141_:
{
uint8_t v___x_2143_; 
v___x_2143_ = lean_nat_dec_lt(v_x_2131_, v___y_2142_);
if (v___x_2143_ == 0)
{
uint8_t v___x_2144_; 
v___x_2144_ = lean_nat_dec_eq(v_x_2131_, v___y_2142_);
if (v___x_2144_ == 0)
{
if (lean_obj_tag(v_l_2133_) == 0)
{
lean_object* v_size_2145_; 
v_size_2145_ = lean_ctor_get(v_l_2133_, 0);
v___y_2136_ = v_size_2145_;
goto v___jp_2135_;
}
else
{
lean_object* v___x_2146_; 
v___x_2146_ = lean_unsigned_to_nat(0u);
v___y_2136_ = v___x_2146_;
goto v___jp_2135_;
}
}
else
{
lean_dec(v_x_2131_);
lean_inc(v_k_2132_);
return v_k_2132_;
}
}
else
{
v_x_2130_ = v_l_2133_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg___boxed(lean_object* v_x_2150_, lean_object* v_x_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2150_, v_x_2151_);
lean_dec(v_x_2150_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx(lean_object* v_00_u03b1_2153_, lean_object* v_00_u03b2_2154_, lean_object* v_x_2155_, lean_object* v_x_2156_, lean_object* v_x_2157_, lean_object* v_x_2158_){
_start:
{
lean_object* v___x_2159_; 
v___x_2159_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2155_, v_x_2157_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___boxed(lean_object* v_00_u03b1_2160_, lean_object* v_00_u03b2_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx(v_00_u03b1_2160_, v_00_u03b2_2161_, v_x_2162_, v_x_2163_, v_x_2164_, v_x_2165_);
lean_dec(v_x_2162_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object* v_x_2167_, lean_object* v_x_2168_){
_start:
{
if (lean_obj_tag(v_x_2167_) == 0)
{
lean_object* v_k_2169_; lean_object* v_l_2170_; lean_object* v_r_2171_; lean_object* v___y_2173_; lean_object* v___y_2179_; 
v_k_2169_ = lean_ctor_get(v_x_2167_, 1);
v_l_2170_ = lean_ctor_get(v_x_2167_, 3);
v_r_2171_ = lean_ctor_get(v_x_2167_, 4);
if (lean_obj_tag(v_l_2170_) == 0)
{
lean_object* v_size_2186_; 
v_size_2186_ = lean_ctor_get(v_l_2170_, 0);
v___y_2179_ = v_size_2186_;
goto v___jp_2178_;
}
else
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_unsigned_to_nat(0u);
v___y_2179_ = v___x_2187_;
goto v___jp_2178_;
}
v___jp_2172_:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2174_ = lean_nat_sub(v_x_2168_, v___y_2173_);
lean_dec(v_x_2168_);
v___x_2175_ = lean_unsigned_to_nat(1u);
v___x_2176_ = lean_nat_sub(v___x_2174_, v___x_2175_);
lean_dec(v___x_2174_);
v_x_2167_ = v_r_2171_;
v_x_2168_ = v___x_2176_;
goto _start;
}
v___jp_2178_:
{
uint8_t v___x_2180_; 
v___x_2180_ = lean_nat_dec_lt(v_x_2168_, v___y_2179_);
if (v___x_2180_ == 0)
{
uint8_t v___x_2181_; 
v___x_2181_ = lean_nat_dec_eq(v_x_2168_, v___y_2179_);
if (v___x_2181_ == 0)
{
if (lean_obj_tag(v_l_2170_) == 0)
{
lean_object* v_size_2182_; 
v_size_2182_ = lean_ctor_get(v_l_2170_, 0);
v___y_2173_ = v_size_2182_;
goto v___jp_2172_;
}
else
{
lean_object* v___x_2183_; 
v___x_2183_ = lean_unsigned_to_nat(0u);
v___y_2173_ = v___x_2183_;
goto v___jp_2172_;
}
}
else
{
lean_object* v___x_2184_; 
lean_dec(v_x_2168_);
lean_inc(v_k_2169_);
v___x_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2184_, 0, v_k_2169_);
return v___x_2184_;
}
}
else
{
v_x_2167_ = v_l_2170_;
goto _start;
}
}
}
else
{
lean_object* v___x_2188_; 
lean_dec(v_x_2168_);
v___x_2188_ = lean_box(0);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg___boxed(lean_object* v_x_2189_, lean_object* v_x_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2189_, v_x_2190_);
lean_dec(v_x_2189_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(lean_object* v_00_u03b1_2192_, lean_object* v_00_u03b2_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2194_, v_x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_2197_, lean_object* v_00_u03b2_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(v_00_u03b1_2197_, v_00_u03b2_2198_, v_x_2199_, v_x_2200_);
lean_dec(v_x_2199_);
return v_res_2201_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2203_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_2204_ = lean_unsigned_to_nat(16u);
v___x_2205_ = lean_unsigned_to_nat(503u);
v___x_2206_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0));
v___x_2207_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_2208_ = l_mkPanicMessageWithDecl(v___x_2207_, v___x_2206_, v___x_2205_, v___x_2204_, v___x_2203_);
return v___x_2208_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object* v_inst_2209_, lean_object* v_x_2210_, lean_object* v_x_2211_){
_start:
{
if (lean_obj_tag(v_x_2210_) == 0)
{
lean_object* v_k_2212_; lean_object* v_l_2213_; lean_object* v_r_2214_; lean_object* v___y_2216_; lean_object* v___y_2222_; 
v_k_2212_ = lean_ctor_get(v_x_2210_, 1);
v_l_2213_ = lean_ctor_get(v_x_2210_, 3);
v_r_2214_ = lean_ctor_get(v_x_2210_, 4);
if (lean_obj_tag(v_l_2213_) == 0)
{
lean_object* v_size_2228_; 
v_size_2228_ = lean_ctor_get(v_l_2213_, 0);
v___y_2222_ = v_size_2228_;
goto v___jp_2221_;
}
else
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_unsigned_to_nat(0u);
v___y_2222_ = v___x_2229_;
goto v___jp_2221_;
}
v___jp_2215_:
{
lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2217_ = lean_nat_sub(v_x_2211_, v___y_2216_);
lean_dec(v_x_2211_);
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_nat_sub(v___x_2217_, v___x_2218_);
lean_dec(v___x_2217_);
v_x_2210_ = v_r_2214_;
v_x_2211_ = v___x_2219_;
goto _start;
}
v___jp_2221_:
{
uint8_t v___x_2223_; 
v___x_2223_ = lean_nat_dec_lt(v_x_2211_, v___y_2222_);
if (v___x_2223_ == 0)
{
uint8_t v___x_2224_; 
v___x_2224_ = lean_nat_dec_eq(v_x_2211_, v___y_2222_);
if (v___x_2224_ == 0)
{
if (lean_obj_tag(v_l_2213_) == 0)
{
lean_object* v_size_2225_; 
v_size_2225_ = lean_ctor_get(v_l_2213_, 0);
v___y_2216_ = v_size_2225_;
goto v___jp_2215_;
}
else
{
lean_object* v___x_2226_; 
v___x_2226_ = lean_unsigned_to_nat(0u);
v___y_2216_ = v___x_2226_;
goto v___jp_2215_;
}
}
else
{
lean_dec(v_x_2211_);
lean_inc(v_k_2212_);
return v_k_2212_;
}
}
else
{
v_x_2210_ = v_l_2213_;
goto _start;
}
}
}
else
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
lean_dec(v_x_2211_);
v___x_2230_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1);
v___x_2231_ = l_panic___redArg(v_inst_2209_, v___x_2230_);
return v___x_2231_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_2232_, lean_object* v_x_2233_, lean_object* v_x_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2232_, v_x_2233_, v_x_2234_);
lean_dec(v_x_2233_);
lean_dec(v_inst_2232_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(lean_object* v_00_u03b1_2236_, lean_object* v_00_u03b2_2237_, lean_object* v_inst_2238_, lean_object* v_x_2239_, lean_object* v_x_2240_){
_start:
{
lean_object* v___x_2241_; 
v___x_2241_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2238_, v_x_2239_, v_x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_2242_, lean_object* v_00_u03b2_2243_, lean_object* v_inst_2244_, lean_object* v_x_2245_, lean_object* v_x_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(v_00_u03b1_2242_, v_00_u03b2_2243_, v_inst_2244_, v_x_2245_, v_x_2246_);
lean_dec(v_x_2245_);
lean_dec(v_inst_2244_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object* v_x_2248_, lean_object* v_x_2249_, lean_object* v_x_2250_){
_start:
{
if (lean_obj_tag(v_x_2248_) == 0)
{
lean_object* v_k_2251_; lean_object* v_l_2252_; lean_object* v_r_2253_; lean_object* v___y_2255_; lean_object* v___y_2261_; 
v_k_2251_ = lean_ctor_get(v_x_2248_, 1);
v_l_2252_ = lean_ctor_get(v_x_2248_, 3);
v_r_2253_ = lean_ctor_get(v_x_2248_, 4);
if (lean_obj_tag(v_l_2252_) == 0)
{
lean_object* v_size_2267_; 
v_size_2267_ = lean_ctor_get(v_l_2252_, 0);
v___y_2261_ = v_size_2267_;
goto v___jp_2260_;
}
else
{
lean_object* v___x_2268_; 
v___x_2268_ = lean_unsigned_to_nat(0u);
v___y_2261_ = v___x_2268_;
goto v___jp_2260_;
}
v___jp_2254_:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2256_ = lean_nat_sub(v_x_2249_, v___y_2255_);
lean_dec(v_x_2249_);
v___x_2257_ = lean_unsigned_to_nat(1u);
v___x_2258_ = lean_nat_sub(v___x_2256_, v___x_2257_);
lean_dec(v___x_2256_);
v_x_2248_ = v_r_2253_;
v_x_2249_ = v___x_2258_;
goto _start;
}
v___jp_2260_:
{
uint8_t v___x_2262_; 
v___x_2262_ = lean_nat_dec_lt(v_x_2249_, v___y_2261_);
if (v___x_2262_ == 0)
{
uint8_t v___x_2263_; 
v___x_2263_ = lean_nat_dec_eq(v_x_2249_, v___y_2261_);
if (v___x_2263_ == 0)
{
if (lean_obj_tag(v_l_2252_) == 0)
{
lean_object* v_size_2264_; 
v_size_2264_ = lean_ctor_get(v_l_2252_, 0);
v___y_2255_ = v_size_2264_;
goto v___jp_2254_;
}
else
{
lean_object* v___x_2265_; 
v___x_2265_ = lean_unsigned_to_nat(0u);
v___y_2255_ = v___x_2265_;
goto v___jp_2254_;
}
}
else
{
lean_dec(v_x_2249_);
lean_inc(v_k_2251_);
return v_k_2251_;
}
}
else
{
v_x_2248_ = v_l_2252_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2249_);
lean_inc(v_x_2250_);
return v_x_2250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg___boxed(lean_object* v_x_2269_, lean_object* v_x_2270_, lean_object* v_x_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2269_, v_x_2270_, v_x_2271_);
lean_dec(v_x_2271_);
lean_dec(v_x_2269_);
return v_res_2272_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD(lean_object* v_00_u03b1_2273_, lean_object* v_00_u03b2_2274_, lean_object* v_x_2275_, lean_object* v_x_2276_, lean_object* v_x_2277_){
_start:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2275_, v_x_2276_, v_x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___boxed(lean_object* v_00_u03b1_2279_, lean_object* v_00_u03b2_2280_, lean_object* v_x_2281_, lean_object* v_x_2282_, lean_object* v_x_2283_){
_start:
{
lean_object* v_res_2284_; 
v_res_2284_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD(v_00_u03b1_2279_, v_00_u03b2_2280_, v_x_2281_, v_x_2282_, v_x_2283_);
lean_dec(v_x_2283_);
lean_dec(v_x_2281_);
return v_res_2284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object* v_inst_2285_, lean_object* v_k_2286_, lean_object* v_best_2287_, lean_object* v_a_2288_){
_start:
{
if (lean_obj_tag(v_a_2288_) == 0)
{
lean_object* v_k_2289_; lean_object* v_v_2290_; lean_object* v_l_2291_; lean_object* v_r_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v_k_2289_ = lean_ctor_get(v_a_2288_, 1);
lean_inc_n(v_k_2289_, 2);
v_v_2290_ = lean_ctor_get(v_a_2288_, 2);
lean_inc(v_v_2290_);
v_l_2291_ = lean_ctor_get(v_a_2288_, 3);
lean_inc(v_l_2291_);
v_r_2292_ = lean_ctor_get(v_a_2288_, 4);
lean_inc(v_r_2292_);
lean_dec_ref_known(v_a_2288_, 5);
lean_inc_ref(v_inst_2285_);
lean_inc(v_k_2286_);
v___x_2293_ = lean_apply_2(v_inst_2285_, v_k_2286_, v_k_2289_);
v___x_2294_ = lean_unbox(v___x_2293_);
switch(v___x_2294_)
{
case 0:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_dec(v_r_2292_);
lean_dec(v_best_2287_);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_k_2289_);
lean_ctor_set(v___x_2295_, 1, v_v_2290_);
v___x_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
v_best_2287_ = v___x_2296_;
v_a_2288_ = v_l_2291_;
goto _start;
}
case 1:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
lean_dec(v_r_2292_);
lean_dec(v_l_2291_);
lean_dec(v_best_2287_);
lean_dec(v_k_2286_);
lean_dec_ref(v_inst_2285_);
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v_k_2289_);
lean_ctor_set(v___x_2298_, 1, v_v_2290_);
v___x_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2298_);
return v___x_2299_;
}
default: 
{
lean_dec(v_l_2291_);
lean_dec(v_v_2290_);
lean_dec(v_k_2289_);
v_a_2288_ = v_r_2292_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2286_);
lean_dec_ref(v_inst_2285_);
return v_best_2287_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go(lean_object* v_00_u03b1_2301_, lean_object* v_00_u03b2_2302_, lean_object* v_inst_2303_, lean_object* v_k_2304_, lean_object* v_best_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2307_; 
v___x_2307_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2303_, v_k_2304_, v_best_2305_, v_a_2306_);
return v___x_2307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___redArg(lean_object* v_inst_2308_, lean_object* v_k_2309_, lean_object* v_a_2310_){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; 
v___x_2311_ = lean_box(0);
v___x_2312_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2308_, v_k_2309_, v___x_2311_, v_a_2310_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f(lean_object* v_00_u03b1_2313_, lean_object* v_00_u03b2_2314_, lean_object* v_inst_2315_, lean_object* v_k_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2318_ = lean_box(0);
v___x_2319_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2315_, v_k_2316_, v___x_2318_, v_a_2317_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object* v_inst_2320_, lean_object* v_k_2321_, lean_object* v_best_2322_, lean_object* v_a_2323_){
_start:
{
if (lean_obj_tag(v_a_2323_) == 0)
{
lean_object* v_k_2324_; lean_object* v_v_2325_; lean_object* v_l_2326_; lean_object* v_r_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; 
v_k_2324_ = lean_ctor_get(v_a_2323_, 1);
lean_inc_n(v_k_2324_, 2);
v_v_2325_ = lean_ctor_get(v_a_2323_, 2);
lean_inc(v_v_2325_);
v_l_2326_ = lean_ctor_get(v_a_2323_, 3);
lean_inc(v_l_2326_);
v_r_2327_ = lean_ctor_get(v_a_2323_, 4);
lean_inc(v_r_2327_);
lean_dec_ref_known(v_a_2323_, 5);
lean_inc_ref(v_inst_2320_);
lean_inc(v_k_2321_);
v___x_2328_ = lean_apply_2(v_inst_2320_, v_k_2321_, v_k_2324_);
v___x_2329_ = lean_unbox(v___x_2328_);
if (v___x_2329_ == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec(v_r_2327_);
lean_dec(v_best_2322_);
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v_k_2324_);
lean_ctor_set(v___x_2330_, 1, v_v_2325_);
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
v_best_2322_ = v___x_2331_;
v_a_2323_ = v_l_2326_;
goto _start;
}
else
{
lean_dec(v_l_2326_);
lean_dec(v_v_2325_);
lean_dec(v_k_2324_);
v_a_2323_ = v_r_2327_;
goto _start;
}
}
else
{
lean_dec(v_k_2321_);
lean_dec_ref(v_inst_2320_);
return v_best_2322_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go(lean_object* v_00_u03b1_2334_, lean_object* v_00_u03b2_2335_, lean_object* v_inst_2336_, lean_object* v_k_2337_, lean_object* v_best_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2336_, v_k_2337_, v_best_2338_, v_a_2339_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___redArg(lean_object* v_inst_2341_, lean_object* v_k_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2344_ = lean_box(0);
v___x_2345_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2341_, v_k_2342_, v___x_2344_, v_a_2343_);
return v___x_2345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f(lean_object* v_00_u03b1_2346_, lean_object* v_00_u03b2_2347_, lean_object* v_inst_2348_, lean_object* v_k_2349_, lean_object* v_a_2350_){
_start:
{
lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2351_ = lean_box(0);
v___x_2352_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2348_, v_k_2349_, v___x_2351_, v_a_2350_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object* v_inst_2353_, lean_object* v_k_2354_, lean_object* v_best_2355_, lean_object* v_a_2356_){
_start:
{
if (lean_obj_tag(v_a_2356_) == 0)
{
lean_object* v_k_2357_; lean_object* v_v_2358_; lean_object* v_l_2359_; lean_object* v_r_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; 
v_k_2357_ = lean_ctor_get(v_a_2356_, 1);
lean_inc_n(v_k_2357_, 2);
v_v_2358_ = lean_ctor_get(v_a_2356_, 2);
lean_inc(v_v_2358_);
v_l_2359_ = lean_ctor_get(v_a_2356_, 3);
lean_inc(v_l_2359_);
v_r_2360_ = lean_ctor_get(v_a_2356_, 4);
lean_inc(v_r_2360_);
lean_dec_ref_known(v_a_2356_, 5);
lean_inc_ref(v_inst_2353_);
lean_inc(v_k_2354_);
v___x_2361_ = lean_apply_2(v_inst_2353_, v_k_2354_, v_k_2357_);
v___x_2362_ = lean_unbox(v___x_2361_);
switch(v___x_2362_)
{
case 0:
{
lean_dec(v_r_2360_);
lean_dec(v_v_2358_);
lean_dec(v_k_2357_);
v_a_2356_ = v_l_2359_;
goto _start;
}
case 1:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
lean_dec(v_r_2360_);
lean_dec(v_l_2359_);
lean_dec(v_best_2355_);
lean_dec(v_k_2354_);
lean_dec_ref(v_inst_2353_);
v___x_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2364_, 0, v_k_2357_);
lean_ctor_set(v___x_2364_, 1, v_v_2358_);
v___x_2365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2364_);
return v___x_2365_;
}
default: 
{
lean_object* v___x_2366_; lean_object* v___x_2367_; 
lean_dec(v_l_2359_);
lean_dec(v_best_2355_);
v___x_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2366_, 0, v_k_2357_);
lean_ctor_set(v___x_2366_, 1, v_v_2358_);
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
v_best_2355_ = v___x_2367_;
v_a_2356_ = v_r_2360_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2354_);
lean_dec_ref(v_inst_2353_);
return v_best_2355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go(lean_object* v_00_u03b1_2369_, lean_object* v_00_u03b2_2370_, lean_object* v_inst_2371_, lean_object* v_k_2372_, lean_object* v_best_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v___x_2375_; 
v___x_2375_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2371_, v_k_2372_, v_best_2373_, v_a_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___redArg(lean_object* v_inst_2376_, lean_object* v_k_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = lean_box(0);
v___x_2380_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2376_, v_k_2377_, v___x_2379_, v_a_2378_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f(lean_object* v_00_u03b1_2381_, lean_object* v_00_u03b2_2382_, lean_object* v_inst_2383_, lean_object* v_k_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = lean_box(0);
v___x_2387_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2383_, v_k_2384_, v___x_2386_, v_a_2385_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object* v_inst_2388_, lean_object* v_k_2389_, lean_object* v_best_2390_, lean_object* v_a_2391_){
_start:
{
if (lean_obj_tag(v_a_2391_) == 0)
{
lean_object* v_k_2392_; lean_object* v_v_2393_; lean_object* v_l_2394_; lean_object* v_r_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v_k_2392_ = lean_ctor_get(v_a_2391_, 1);
lean_inc_n(v_k_2392_, 2);
v_v_2393_ = lean_ctor_get(v_a_2391_, 2);
lean_inc(v_v_2393_);
v_l_2394_ = lean_ctor_get(v_a_2391_, 3);
lean_inc(v_l_2394_);
v_r_2395_ = lean_ctor_get(v_a_2391_, 4);
lean_inc(v_r_2395_);
lean_dec_ref_known(v_a_2391_, 5);
lean_inc_ref(v_inst_2388_);
lean_inc(v_k_2389_);
v___x_2396_ = lean_apply_2(v_inst_2388_, v_k_2389_, v_k_2392_);
v___x_2397_ = lean_unbox(v___x_2396_);
if (v___x_2397_ == 2)
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
lean_dec(v_l_2394_);
lean_dec(v_best_2390_);
v___x_2398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2398_, 0, v_k_2392_);
lean_ctor_set(v___x_2398_, 1, v_v_2393_);
v___x_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2398_);
v_best_2390_ = v___x_2399_;
v_a_2391_ = v_r_2395_;
goto _start;
}
else
{
lean_dec(v_r_2395_);
lean_dec(v_v_2393_);
lean_dec(v_k_2392_);
v_a_2391_ = v_l_2394_;
goto _start;
}
}
else
{
lean_dec(v_k_2389_);
lean_dec_ref(v_inst_2388_);
return v_best_2390_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go(lean_object* v_00_u03b1_2402_, lean_object* v_00_u03b2_2403_, lean_object* v_inst_2404_, lean_object* v_k_2405_, lean_object* v_best_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___x_2408_; 
v___x_2408_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2404_, v_k_2405_, v_best_2406_, v_a_2407_);
return v___x_2408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___redArg(lean_object* v_inst_2409_, lean_object* v_k_2410_, lean_object* v_a_2411_){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = lean_box(0);
v___x_2413_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2409_, v_k_2410_, v___x_2412_, v_a_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f(lean_object* v_00_u03b1_2414_, lean_object* v_00_u03b2_2415_, lean_object* v_inst_2416_, lean_object* v_k_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2419_ = lean_box(0);
v___x_2420_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2416_, v_k_2417_, v___x_2419_, v_a_2418_);
return v___x_2420_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; 
v___x_2424_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2));
v___x_2425_ = lean_unsigned_to_nat(14u);
v___x_2426_ = lean_unsigned_to_nat(22u);
v___x_2427_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1));
v___x_2428_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0));
v___x_2429_ = l_mkPanicMessageWithDecl(v___x_2428_, v___x_2427_, v___x_2426_, v___x_2425_, v___x_2424_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(lean_object* v_inst_2430_, lean_object* v_inst_2431_, lean_object* v_k_2432_, lean_object* v_t_2433_){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2434_ = lean_box(0);
v___x_2435_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2430_, v_k_2432_, v___x_2434_, v_t_2433_);
if (lean_obj_tag(v___x_2435_) == 0)
{
lean_object* v___x_2436_; lean_object* v___x_2437_; 
v___x_2436_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2437_ = l_panic___redArg(v_inst_2431_, v___x_2436_);
return v___x_2437_;
}
else
{
lean_object* v_val_2438_; 
v_val_2438_ = lean_ctor_get(v___x_2435_, 0);
lean_inc(v_val_2438_);
lean_dec_ref_known(v___x_2435_, 1);
return v_val_2438_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___boxed(lean_object* v_inst_2439_, lean_object* v_inst_2440_, lean_object* v_k_2441_, lean_object* v_t_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(v_inst_2439_, v_inst_2440_, v_k_2441_, v_t_2442_);
lean_dec_ref(v_inst_2440_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(lean_object* v_00_u03b1_2444_, lean_object* v_00_u03b2_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_k_2448_, lean_object* v_t_2449_){
_start:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_box(0);
v___x_2451_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2446_, v_k_2448_, v___x_2450_, v_t_2449_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v___x_2452_; lean_object* v___x_2453_; 
v___x_2452_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2453_ = l_panic___redArg(v_inst_2447_, v___x_2452_);
return v___x_2453_;
}
else
{
lean_object* v_val_2454_; 
v_val_2454_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_val_2454_);
lean_dec_ref_known(v___x_2451_, 1);
return v_val_2454_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2455_, lean_object* v_00_u03b2_2456_, lean_object* v_inst_2457_, lean_object* v_inst_2458_, lean_object* v_k_2459_, lean_object* v_t_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(v_00_u03b1_2455_, v_00_u03b2_2456_, v_inst_2457_, v_inst_2458_, v_k_2459_, v_t_2460_);
lean_dec_ref(v_inst_2458_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(lean_object* v_inst_2462_, lean_object* v_inst_2463_, lean_object* v_k_2464_, lean_object* v_t_2465_){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_box(0);
v___x_2467_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2462_, v_k_2464_, v___x_2466_, v_t_2465_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2469_ = l_panic___redArg(v_inst_2463_, v___x_2468_);
return v___x_2469_;
}
else
{
lean_object* v_val_2470_; 
v_val_2470_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_val_2470_);
lean_dec_ref_known(v___x_2467_, 1);
return v_val_2470_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg___boxed(lean_object* v_inst_2471_, lean_object* v_inst_2472_, lean_object* v_k_2473_, lean_object* v_t_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(v_inst_2471_, v_inst_2472_, v_k_2473_, v_t_2474_);
lean_dec_ref(v_inst_2472_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(lean_object* v_00_u03b1_2476_, lean_object* v_00_u03b2_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_k_2480_, lean_object* v_t_2481_){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = lean_box(0);
v___x_2483_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2478_, v_k_2480_, v___x_2482_, v_t_2481_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2485_ = l_panic___redArg(v_inst_2479_, v___x_2484_);
return v___x_2485_;
}
else
{
lean_object* v_val_2486_; 
v_val_2486_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_val_2486_);
lean_dec_ref_known(v___x_2483_, 1);
return v_val_2486_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2487_, lean_object* v_00_u03b2_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_k_2491_, lean_object* v_t_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(v_00_u03b1_2487_, v_00_u03b2_2488_, v_inst_2489_, v_inst_2490_, v_k_2491_, v_t_2492_);
lean_dec_ref(v_inst_2490_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(lean_object* v_inst_2494_, lean_object* v_inst_2495_, lean_object* v_k_2496_, lean_object* v_t_2497_){
_start:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2498_ = lean_box(0);
v___x_2499_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2494_, v_k_2496_, v___x_2498_, v_t_2497_);
if (lean_obj_tag(v___x_2499_) == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2500_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2501_ = l_panic___redArg(v_inst_2495_, v___x_2500_);
return v___x_2501_;
}
else
{
lean_object* v_val_2502_; 
v_val_2502_ = lean_ctor_get(v___x_2499_, 0);
lean_inc(v_val_2502_);
lean_dec_ref_known(v___x_2499_, 1);
return v_val_2502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg___boxed(lean_object* v_inst_2503_, lean_object* v_inst_2504_, lean_object* v_k_2505_, lean_object* v_t_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(v_inst_2503_, v_inst_2504_, v_k_2505_, v_t_2506_);
lean_dec_ref(v_inst_2504_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(lean_object* v_00_u03b1_2508_, lean_object* v_00_u03b2_2509_, lean_object* v_inst_2510_, lean_object* v_inst_2511_, lean_object* v_k_2512_, lean_object* v_t_2513_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2514_ = lean_box(0);
v___x_2515_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2510_, v_k_2512_, v___x_2514_, v_t_2513_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2516_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2517_ = l_panic___redArg(v_inst_2511_, v___x_2516_);
return v___x_2517_;
}
else
{
lean_object* v_val_2518_; 
v_val_2518_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_val_2518_);
lean_dec_ref_known(v___x_2515_, 1);
return v_val_2518_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2519_, lean_object* v_00_u03b2_2520_, lean_object* v_inst_2521_, lean_object* v_inst_2522_, lean_object* v_k_2523_, lean_object* v_t_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(v_00_u03b1_2519_, v_00_u03b2_2520_, v_inst_2521_, v_inst_2522_, v_k_2523_, v_t_2524_);
lean_dec_ref(v_inst_2522_);
return v_res_2525_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(lean_object* v_inst_2526_, lean_object* v_inst_2527_, lean_object* v_k_2528_, lean_object* v_t_2529_){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = lean_box(0);
v___x_2531_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2526_, v_k_2528_, v___x_2530_, v_t_2529_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2533_ = l_panic___redArg(v_inst_2527_, v___x_2532_);
return v___x_2533_;
}
else
{
lean_object* v_val_2534_; 
v_val_2534_ = lean_ctor_get(v___x_2531_, 0);
lean_inc(v_val_2534_);
lean_dec_ref_known(v___x_2531_, 1);
return v_val_2534_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg___boxed(lean_object* v_inst_2535_, lean_object* v_inst_2536_, lean_object* v_k_2537_, lean_object* v_t_2538_){
_start:
{
lean_object* v_res_2539_; 
v_res_2539_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(v_inst_2535_, v_inst_2536_, v_k_2537_, v_t_2538_);
lean_dec_ref(v_inst_2536_);
return v_res_2539_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(lean_object* v_00_u03b1_2540_, lean_object* v_00_u03b2_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_k_2544_, lean_object* v_t_2545_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_box(0);
v___x_2547_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2542_, v_k_2544_, v___x_2546_, v_t_2545_);
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2549_ = l_panic___redArg(v_inst_2543_, v___x_2548_);
return v___x_2549_;
}
else
{
lean_object* v_val_2550_; 
v_val_2550_ = lean_ctor_get(v___x_2547_, 0);
lean_inc(v_val_2550_);
lean_dec_ref_known(v___x_2547_, 1);
return v_val_2550_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2551_, lean_object* v_00_u03b2_2552_, lean_object* v_inst_2553_, lean_object* v_inst_2554_, lean_object* v_k_2555_, lean_object* v_t_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(v_00_u03b1_2551_, v_00_u03b2_2552_, v_inst_2553_, v_inst_2554_, v_k_2555_, v_t_2556_);
lean_dec_ref(v_inst_2554_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(lean_object* v_inst_2558_, lean_object* v_k_2559_, lean_object* v_t_2560_, lean_object* v_fallback_2561_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = lean_box(0);
v___x_2563_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2558_, v_k_2559_, v___x_2562_, v_t_2560_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_inc_ref(v_fallback_2561_);
return v_fallback_2561_;
}
else
{
lean_object* v_val_2564_; 
v_val_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_val_2564_);
lean_dec_ref_known(v___x_2563_, 1);
return v_val_2564_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg___boxed(lean_object* v_inst_2565_, lean_object* v_k_2566_, lean_object* v_t_2567_, lean_object* v_fallback_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(v_inst_2565_, v_k_2566_, v_t_2567_, v_fallback_2568_);
lean_dec_ref(v_fallback_2568_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED(lean_object* v_00_u03b1_2570_, lean_object* v_00_u03b2_2571_, lean_object* v_inst_2572_, lean_object* v_k_2573_, lean_object* v_t_2574_, lean_object* v_fallback_2575_){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_box(0);
v___x_2577_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2572_, v_k_2573_, v___x_2576_, v_t_2574_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_inc_ref(v_fallback_2575_);
return v_fallback_2575_;
}
else
{
lean_object* v_val_2578_; 
v_val_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_val_2578_);
lean_dec_ref_known(v___x_2577_, 1);
return v_val_2578_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___boxed(lean_object* v_00_u03b1_2579_, lean_object* v_00_u03b2_2580_, lean_object* v_inst_2581_, lean_object* v_k_2582_, lean_object* v_t_2583_, lean_object* v_fallback_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_Std_DTreeMap_Internal_Impl_getEntryGED(v_00_u03b1_2579_, v_00_u03b2_2580_, v_inst_2581_, v_k_2582_, v_t_2583_, v_fallback_2584_);
lean_dec_ref(v_fallback_2584_);
return v_res_2585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(lean_object* v_inst_2586_, lean_object* v_k_2587_, lean_object* v_t_2588_, lean_object* v_fallback_2589_){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2590_ = lean_box(0);
v___x_2591_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2586_, v_k_2587_, v___x_2590_, v_t_2588_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_inc_ref(v_fallback_2589_);
return v_fallback_2589_;
}
else
{
lean_object* v_val_2592_; 
v_val_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_val_2592_);
lean_dec_ref_known(v___x_2591_, 1);
return v_val_2592_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg___boxed(lean_object* v_inst_2593_, lean_object* v_k_2594_, lean_object* v_t_2595_, lean_object* v_fallback_2596_){
_start:
{
lean_object* v_res_2597_; 
v_res_2597_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(v_inst_2593_, v_k_2594_, v_t_2595_, v_fallback_2596_);
lean_dec_ref(v_fallback_2596_);
return v_res_2597_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD(lean_object* v_00_u03b1_2598_, lean_object* v_00_u03b2_2599_, lean_object* v_inst_2600_, lean_object* v_k_2601_, lean_object* v_t_2602_, lean_object* v_fallback_2603_){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2604_ = lean_box(0);
v___x_2605_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2600_, v_k_2601_, v___x_2604_, v_t_2602_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_inc_ref(v_fallback_2603_);
return v_fallback_2603_;
}
else
{
lean_object* v_val_2606_; 
v_val_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_val_2606_);
lean_dec_ref_known(v___x_2605_, 1);
return v_val_2606_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___boxed(lean_object* v_00_u03b1_2607_, lean_object* v_00_u03b2_2608_, lean_object* v_inst_2609_, lean_object* v_k_2610_, lean_object* v_t_2611_, lean_object* v_fallback_2612_){
_start:
{
lean_object* v_res_2613_; 
v_res_2613_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD(v_00_u03b1_2607_, v_00_u03b2_2608_, v_inst_2609_, v_k_2610_, v_t_2611_, v_fallback_2612_);
lean_dec_ref(v_fallback_2612_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(lean_object* v_inst_2614_, lean_object* v_k_2615_, lean_object* v_t_2616_, lean_object* v_fallback_2617_){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2618_ = lean_box(0);
v___x_2619_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2614_, v_k_2615_, v___x_2618_, v_t_2616_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_inc_ref(v_fallback_2617_);
return v_fallback_2617_;
}
else
{
lean_object* v_val_2620_; 
v_val_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_val_2620_);
lean_dec_ref_known(v___x_2619_, 1);
return v_val_2620_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg___boxed(lean_object* v_inst_2621_, lean_object* v_k_2622_, lean_object* v_t_2623_, lean_object* v_fallback_2624_){
_start:
{
lean_object* v_res_2625_; 
v_res_2625_ = l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(v_inst_2621_, v_k_2622_, v_t_2623_, v_fallback_2624_);
lean_dec_ref(v_fallback_2624_);
return v_res_2625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED(lean_object* v_00_u03b1_2626_, lean_object* v_00_u03b2_2627_, lean_object* v_inst_2628_, lean_object* v_k_2629_, lean_object* v_t_2630_, lean_object* v_fallback_2631_){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; 
v___x_2632_ = lean_box(0);
v___x_2633_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2628_, v_k_2629_, v___x_2632_, v_t_2630_);
if (lean_obj_tag(v___x_2633_) == 0)
{
lean_inc_ref(v_fallback_2631_);
return v_fallback_2631_;
}
else
{
lean_object* v_val_2634_; 
v_val_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_val_2634_);
lean_dec_ref_known(v___x_2633_, 1);
return v_val_2634_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___boxed(lean_object* v_00_u03b1_2635_, lean_object* v_00_u03b2_2636_, lean_object* v_inst_2637_, lean_object* v_k_2638_, lean_object* v_t_2639_, lean_object* v_fallback_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l_Std_DTreeMap_Internal_Impl_getEntryLED(v_00_u03b1_2635_, v_00_u03b2_2636_, v_inst_2637_, v_k_2638_, v_t_2639_, v_fallback_2640_);
lean_dec_ref(v_fallback_2640_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(lean_object* v_inst_2642_, lean_object* v_k_2643_, lean_object* v_t_2644_, lean_object* v_fallback_2645_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = lean_box(0);
v___x_2647_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2642_, v_k_2643_, v___x_2646_, v_t_2644_);
if (lean_obj_tag(v___x_2647_) == 0)
{
lean_inc_ref(v_fallback_2645_);
return v_fallback_2645_;
}
else
{
lean_object* v_val_2648_; 
v_val_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc(v_val_2648_);
lean_dec_ref_known(v___x_2647_, 1);
return v_val_2648_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg___boxed(lean_object* v_inst_2649_, lean_object* v_k_2650_, lean_object* v_t_2651_, lean_object* v_fallback_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(v_inst_2649_, v_k_2650_, v_t_2651_, v_fallback_2652_);
lean_dec_ref(v_fallback_2652_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD(lean_object* v_00_u03b1_2654_, lean_object* v_00_u03b2_2655_, lean_object* v_inst_2656_, lean_object* v_k_2657_, lean_object* v_t_2658_, lean_object* v_fallback_2659_){
_start:
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_box(0);
v___x_2661_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2656_, v_k_2657_, v___x_2660_, v_t_2658_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_inc_ref(v_fallback_2659_);
return v_fallback_2659_;
}
else
{
lean_object* v_val_2662_; 
v_val_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v___x_2661_, 1);
return v_val_2662_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___boxed(lean_object* v_00_u03b1_2663_, lean_object* v_00_u03b2_2664_, lean_object* v_inst_2665_, lean_object* v_k_2666_, lean_object* v_t_2667_, lean_object* v_fallback_2668_){
_start:
{
lean_object* v_res_2669_; 
v_res_2669_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD(v_00_u03b1_2663_, v_00_u03b2_2664_, v_inst_2665_, v_k_2666_, v_t_2667_, v_fallback_2668_);
lean_dec_ref(v_fallback_2668_);
return v_res_2669_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(lean_object* v_inst_2670_, lean_object* v_k_2671_, lean_object* v_x_2672_){
_start:
{
lean_object* v_k_2673_; lean_object* v_v_2674_; lean_object* v_l_2675_; lean_object* v_r_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_k_2673_ = lean_ctor_get(v_x_2672_, 1);
lean_inc_n(v_k_2673_, 2);
v_v_2674_ = lean_ctor_get(v_x_2672_, 2);
lean_inc(v_v_2674_);
v_l_2675_ = lean_ctor_get(v_x_2672_, 3);
lean_inc(v_l_2675_);
v_r_2676_ = lean_ctor_get(v_x_2672_, 4);
lean_inc(v_r_2676_);
lean_dec(v_x_2672_);
lean_inc_ref(v_inst_2670_);
lean_inc(v_k_2671_);
v___x_2677_ = lean_apply_2(v_inst_2670_, v_k_2671_, v_k_2673_);
v___x_2678_ = lean_unbox(v___x_2677_);
switch(v___x_2678_)
{
case 0:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_dec(v_r_2676_);
v___x_2679_ = lean_box(0);
v___x_2680_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2670_, v_k_2671_, v___x_2679_, v_l_2675_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v___x_2681_; 
v___x_2681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2681_, 0, v_k_2673_);
lean_ctor_set(v___x_2681_, 1, v_v_2674_);
return v___x_2681_;
}
else
{
lean_object* v_val_2682_; 
lean_dec(v_v_2674_);
lean_dec(v_k_2673_);
v_val_2682_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_val_2682_);
lean_dec_ref_known(v___x_2680_, 1);
return v_val_2682_;
}
}
case 1:
{
lean_object* v___x_2683_; 
lean_dec(v_r_2676_);
lean_dec(v_l_2675_);
lean_dec(v_k_2671_);
lean_dec_ref(v_inst_2670_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_k_2673_);
lean_ctor_set(v___x_2683_, 1, v_v_2674_);
return v___x_2683_;
}
default: 
{
lean_dec(v_l_2675_);
lean_dec(v_v_2674_);
lean_dec(v_k_2673_);
v_x_2672_ = v_r_2676_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE(lean_object* v_00_u03b1_2685_, lean_object* v_00_u03b2_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_k_2689_, lean_object* v_x_2690_, lean_object* v_x_2691_, lean_object* v_x_2692_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_inst_2687_, v_k_2689_, v_x_2690_);
return v___x_2693_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0(void){
_start:
{
uint8_t v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = 0;
v___x_2695_ = l_Ordering_ctorIdx(v___x_2694_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object* v_inst_2696_, lean_object* v_k_2697_, lean_object* v_x_2698_){
_start:
{
lean_object* v_k_2699_; lean_object* v_v_2700_; lean_object* v_l_2701_; lean_object* v_r_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; uint8_t v___x_2707_; 
v_k_2699_ = lean_ctor_get(v_x_2698_, 1);
lean_inc_n(v_k_2699_, 2);
v_v_2700_ = lean_ctor_get(v_x_2698_, 2);
lean_inc(v_v_2700_);
v_l_2701_ = lean_ctor_get(v_x_2698_, 3);
lean_inc(v_l_2701_);
v_r_2702_ = lean_ctor_get(v_x_2698_, 4);
lean_inc(v_r_2702_);
lean_dec(v_x_2698_);
lean_inc_ref(v_inst_2696_);
lean_inc(v_k_2697_);
v___x_2703_ = lean_apply_2(v_inst_2696_, v_k_2697_, v_k_2699_);
v___x_2704_ = lean_unbox(v___x_2703_);
v___x_2705_ = l_Ordering_ctorIdx(v___x_2704_);
v___x_2706_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0);
v___x_2707_ = lean_nat_dec_eq(v___x_2705_, v___x_2706_);
lean_dec(v___x_2705_);
if (v___x_2707_ == 0)
{
lean_dec(v_l_2701_);
lean_dec(v_v_2700_);
lean_dec(v_k_2699_);
v_x_2698_ = v_r_2702_;
goto _start;
}
else
{
lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_dec(v_r_2702_);
v___x_2709_ = lean_box(0);
v___x_2710_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2696_, v_k_2697_, v___x_2709_, v_l_2701_);
if (lean_obj_tag(v___x_2710_) == 0)
{
lean_object* v___x_2711_; 
v___x_2711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2711_, 0, v_k_2699_);
lean_ctor_set(v___x_2711_, 1, v_v_2700_);
return v___x_2711_;
}
else
{
lean_object* v_val_2712_; 
lean_dec(v_v_2700_);
lean_dec(v_k_2699_);
v_val_2712_ = lean_ctor_get(v___x_2710_, 0);
lean_inc(v_val_2712_);
lean_dec_ref_known(v___x_2710_, 1);
return v_val_2712_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object* v_00_u03b1_2713_, lean_object* v_00_u03b2_2714_, lean_object* v_inst_2715_, lean_object* v_inst_2716_, lean_object* v_k_2717_, lean_object* v_x_2718_, lean_object* v_x_2719_, lean_object* v_x_2720_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_inst_2715_, v_k_2717_, v_x_2718_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object* v_inst_2722_, lean_object* v_k_2723_, lean_object* v_x_2724_){
_start:
{
lean_object* v_k_2725_; lean_object* v_v_2726_; lean_object* v_l_2727_; lean_object* v_r_2728_; lean_object* v___x_2729_; uint8_t v___x_2730_; 
v_k_2725_ = lean_ctor_get(v_x_2724_, 1);
lean_inc_n(v_k_2725_, 2);
v_v_2726_ = lean_ctor_get(v_x_2724_, 2);
lean_inc(v_v_2726_);
v_l_2727_ = lean_ctor_get(v_x_2724_, 3);
lean_inc(v_l_2727_);
v_r_2728_ = lean_ctor_get(v_x_2724_, 4);
lean_inc(v_r_2728_);
lean_dec(v_x_2724_);
lean_inc_ref(v_inst_2722_);
lean_inc(v_k_2723_);
v___x_2729_ = lean_apply_2(v_inst_2722_, v_k_2723_, v_k_2725_);
v___x_2730_ = lean_unbox(v___x_2729_);
switch(v___x_2730_)
{
case 0:
{
lean_dec(v_r_2728_);
lean_dec(v_v_2726_);
lean_dec(v_k_2725_);
v_x_2724_ = v_l_2727_;
goto _start;
}
case 1:
{
lean_object* v___x_2732_; 
lean_dec(v_r_2728_);
lean_dec(v_l_2727_);
lean_dec(v_k_2723_);
lean_dec_ref(v_inst_2722_);
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_k_2725_);
lean_ctor_set(v___x_2732_, 1, v_v_2726_);
return v___x_2732_;
}
default: 
{
lean_object* v___x_2733_; lean_object* v___x_2734_; 
lean_dec(v_l_2727_);
v___x_2733_ = lean_box(0);
v___x_2734_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2722_, v_k_2723_, v___x_2733_, v_r_2728_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v___x_2735_; 
v___x_2735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2735_, 0, v_k_2725_);
lean_ctor_set(v___x_2735_, 1, v_v_2726_);
return v___x_2735_;
}
else
{
lean_object* v_val_2736_; 
lean_dec(v_v_2726_);
lean_dec(v_k_2725_);
v_val_2736_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_val_2736_);
lean_dec_ref_known(v___x_2734_, 1);
return v_val_2736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object* v_00_u03b1_2737_, lean_object* v_00_u03b2_2738_, lean_object* v_inst_2739_, lean_object* v_inst_2740_, lean_object* v_k_2741_, lean_object* v_x_2742_, lean_object* v_x_2743_, lean_object* v_x_2744_){
_start:
{
lean_object* v___x_2745_; 
v___x_2745_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_inst_2739_, v_k_2741_, v_x_2742_);
return v___x_2745_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0(void){
_start:
{
uint8_t v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = 2;
v___x_2747_ = l_Ordering_ctorIdx(v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object* v_inst_2748_, lean_object* v_k_2749_, lean_object* v_x_2750_){
_start:
{
lean_object* v_k_2751_; lean_object* v_v_2752_; lean_object* v_l_2753_; lean_object* v_r_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; uint8_t v___x_2759_; 
v_k_2751_ = lean_ctor_get(v_x_2750_, 1);
lean_inc_n(v_k_2751_, 2);
v_v_2752_ = lean_ctor_get(v_x_2750_, 2);
lean_inc(v_v_2752_);
v_l_2753_ = lean_ctor_get(v_x_2750_, 3);
lean_inc(v_l_2753_);
v_r_2754_ = lean_ctor_get(v_x_2750_, 4);
lean_inc(v_r_2754_);
lean_dec(v_x_2750_);
lean_inc_ref(v_inst_2748_);
lean_inc(v_k_2749_);
v___x_2755_ = lean_apply_2(v_inst_2748_, v_k_2749_, v_k_2751_);
v___x_2756_ = lean_unbox(v___x_2755_);
v___x_2757_ = l_Ordering_ctorIdx(v___x_2756_);
v___x_2758_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0);
v___x_2759_ = lean_nat_dec_eq(v___x_2757_, v___x_2758_);
lean_dec(v___x_2757_);
if (v___x_2759_ == 0)
{
lean_dec(v_r_2754_);
lean_dec(v_v_2752_);
lean_dec(v_k_2751_);
v_x_2750_ = v_l_2753_;
goto _start;
}
else
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
lean_dec(v_l_2753_);
v___x_2761_ = lean_box(0);
v___x_2762_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2748_, v_k_2749_, v___x_2761_, v_r_2754_);
if (lean_obj_tag(v___x_2762_) == 0)
{
lean_object* v___x_2763_; 
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v_k_2751_);
lean_ctor_set(v___x_2763_, 1, v_v_2752_);
return v___x_2763_;
}
else
{
lean_object* v_val_2764_; 
lean_dec(v_v_2752_);
lean_dec(v_k_2751_);
v_val_2764_ = lean_ctor_get(v___x_2762_, 0);
lean_inc(v_val_2764_);
lean_dec_ref_known(v___x_2762_, 1);
return v_val_2764_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT(lean_object* v_00_u03b1_2765_, lean_object* v_00_u03b2_2766_, lean_object* v_inst_2767_, lean_object* v_inst_2768_, lean_object* v_k_2769_, lean_object* v_x_2770_, lean_object* v_x_2771_, lean_object* v_x_2772_){
_start:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_inst_2767_, v_k_2769_, v_x_2770_);
return v___x_2773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object* v_inst_2774_, lean_object* v_k_2775_, lean_object* v_best_2776_, lean_object* v_a_2777_){
_start:
{
if (lean_obj_tag(v_a_2777_) == 0)
{
lean_object* v_k_2778_; lean_object* v_l_2779_; lean_object* v_r_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v_k_2778_ = lean_ctor_get(v_a_2777_, 1);
lean_inc_n(v_k_2778_, 2);
v_l_2779_ = lean_ctor_get(v_a_2777_, 3);
lean_inc(v_l_2779_);
v_r_2780_ = lean_ctor_get(v_a_2777_, 4);
lean_inc(v_r_2780_);
lean_dec_ref_known(v_a_2777_, 5);
lean_inc_ref(v_inst_2774_);
lean_inc(v_k_2775_);
v___x_2781_ = lean_apply_2(v_inst_2774_, v_k_2775_, v_k_2778_);
v___x_2782_ = lean_unbox(v___x_2781_);
switch(v___x_2782_)
{
case 0:
{
lean_object* v___x_2783_; 
lean_dec(v_r_2780_);
lean_dec(v_best_2776_);
v___x_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2783_, 0, v_k_2778_);
v_best_2776_ = v___x_2783_;
v_a_2777_ = v_l_2779_;
goto _start;
}
case 1:
{
lean_object* v___x_2785_; 
lean_dec(v_r_2780_);
lean_dec(v_l_2779_);
lean_dec(v_best_2776_);
lean_dec(v_k_2775_);
lean_dec_ref(v_inst_2774_);
v___x_2785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2785_, 0, v_k_2778_);
return v___x_2785_;
}
default: 
{
lean_dec(v_l_2779_);
lean_dec(v_k_2778_);
v_a_2777_ = v_r_2780_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2775_);
lean_dec_ref(v_inst_2774_);
return v_best_2776_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(lean_object* v_00_u03b1_2787_, lean_object* v_00_u03b2_2788_, lean_object* v_inst_2789_, lean_object* v_k_2790_, lean_object* v_best_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2789_, v_k_2790_, v_best_2791_, v_a_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___redArg(lean_object* v_inst_2794_, lean_object* v_k_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_box(0);
v___x_2798_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2794_, v_k_2795_, v___x_2797_, v_a_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(lean_object* v_00_u03b1_2799_, lean_object* v_00_u03b2_2800_, lean_object* v_inst_2801_, lean_object* v_k_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = lean_box(0);
v___x_2805_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2801_, v_k_2802_, v___x_2804_, v_a_2803_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object* v_inst_2806_, lean_object* v_k_2807_, lean_object* v_best_2808_, lean_object* v_a_2809_){
_start:
{
if (lean_obj_tag(v_a_2809_) == 0)
{
lean_object* v_k_2810_; lean_object* v_l_2811_; lean_object* v_r_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v_k_2810_ = lean_ctor_get(v_a_2809_, 1);
lean_inc_n(v_k_2810_, 2);
v_l_2811_ = lean_ctor_get(v_a_2809_, 3);
lean_inc(v_l_2811_);
v_r_2812_ = lean_ctor_get(v_a_2809_, 4);
lean_inc(v_r_2812_);
lean_dec_ref_known(v_a_2809_, 5);
lean_inc_ref(v_inst_2806_);
lean_inc(v_k_2807_);
v___x_2813_ = lean_apply_2(v_inst_2806_, v_k_2807_, v_k_2810_);
v___x_2814_ = lean_unbox(v___x_2813_);
if (v___x_2814_ == 0)
{
lean_object* v___x_2815_; 
lean_dec(v_r_2812_);
lean_dec(v_best_2808_);
v___x_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2815_, 0, v_k_2810_);
v_best_2808_ = v___x_2815_;
v_a_2809_ = v_l_2811_;
goto _start;
}
else
{
lean_dec(v_l_2811_);
lean_dec(v_k_2810_);
v_a_2809_ = v_r_2812_;
goto _start;
}
}
else
{
lean_dec(v_k_2807_);
lean_dec_ref(v_inst_2806_);
return v_best_2808_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(lean_object* v_00_u03b1_2818_, lean_object* v_00_u03b2_2819_, lean_object* v_inst_2820_, lean_object* v_k_2821_, lean_object* v_best_2822_, lean_object* v_a_2823_){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2820_, v_k_2821_, v_best_2822_, v_a_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___redArg(lean_object* v_inst_2825_, lean_object* v_k_2826_, lean_object* v_a_2827_){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = lean_box(0);
v___x_2829_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2825_, v_k_2826_, v___x_2828_, v_a_2827_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(lean_object* v_00_u03b1_2830_, lean_object* v_00_u03b2_2831_, lean_object* v_inst_2832_, lean_object* v_k_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2835_ = lean_box(0);
v___x_2836_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2832_, v_k_2833_, v___x_2835_, v_a_2834_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object* v_inst_2837_, lean_object* v_k_2838_, lean_object* v_best_2839_, lean_object* v_a_2840_){
_start:
{
if (lean_obj_tag(v_a_2840_) == 0)
{
lean_object* v_k_2841_; lean_object* v_l_2842_; lean_object* v_r_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_k_2841_ = lean_ctor_get(v_a_2840_, 1);
lean_inc_n(v_k_2841_, 2);
v_l_2842_ = lean_ctor_get(v_a_2840_, 3);
lean_inc(v_l_2842_);
v_r_2843_ = lean_ctor_get(v_a_2840_, 4);
lean_inc(v_r_2843_);
lean_dec_ref_known(v_a_2840_, 5);
lean_inc_ref(v_inst_2837_);
lean_inc(v_k_2838_);
v___x_2844_ = lean_apply_2(v_inst_2837_, v_k_2838_, v_k_2841_);
v___x_2845_ = lean_unbox(v___x_2844_);
switch(v___x_2845_)
{
case 0:
{
lean_dec(v_r_2843_);
lean_dec(v_k_2841_);
v_a_2840_ = v_l_2842_;
goto _start;
}
case 1:
{
lean_object* v___x_2847_; 
lean_dec(v_r_2843_);
lean_dec(v_l_2842_);
lean_dec(v_best_2839_);
lean_dec(v_k_2838_);
lean_dec_ref(v_inst_2837_);
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v_k_2841_);
return v___x_2847_;
}
default: 
{
lean_object* v___x_2848_; 
lean_dec(v_l_2842_);
lean_dec(v_best_2839_);
v___x_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2848_, 0, v_k_2841_);
v_best_2839_ = v___x_2848_;
v_a_2840_ = v_r_2843_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2838_);
lean_dec_ref(v_inst_2837_);
return v_best_2839_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(lean_object* v_00_u03b1_2850_, lean_object* v_00_u03b2_2851_, lean_object* v_inst_2852_, lean_object* v_k_2853_, lean_object* v_best_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2852_, v_k_2853_, v_best_2854_, v_a_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___redArg(lean_object* v_inst_2857_, lean_object* v_k_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_box(0);
v___x_2861_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2857_, v_k_2858_, v___x_2860_, v_a_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(lean_object* v_00_u03b1_2862_, lean_object* v_00_u03b2_2863_, lean_object* v_inst_2864_, lean_object* v_k_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_box(0);
v___x_2868_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2864_, v_k_2865_, v___x_2867_, v_a_2866_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object* v_inst_2869_, lean_object* v_k_2870_, lean_object* v_best_2871_, lean_object* v_a_2872_){
_start:
{
if (lean_obj_tag(v_a_2872_) == 0)
{
lean_object* v_k_2873_; lean_object* v_l_2874_; lean_object* v_r_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v_k_2873_ = lean_ctor_get(v_a_2872_, 1);
lean_inc_n(v_k_2873_, 2);
v_l_2874_ = lean_ctor_get(v_a_2872_, 3);
lean_inc(v_l_2874_);
v_r_2875_ = lean_ctor_get(v_a_2872_, 4);
lean_inc(v_r_2875_);
lean_dec_ref_known(v_a_2872_, 5);
lean_inc_ref(v_inst_2869_);
lean_inc(v_k_2870_);
v___x_2876_ = lean_apply_2(v_inst_2869_, v_k_2870_, v_k_2873_);
v___x_2877_ = lean_unbox(v___x_2876_);
if (v___x_2877_ == 2)
{
lean_object* v___x_2878_; 
lean_dec(v_l_2874_);
lean_dec(v_best_2871_);
v___x_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2878_, 0, v_k_2873_);
v_best_2871_ = v___x_2878_;
v_a_2872_ = v_r_2875_;
goto _start;
}
else
{
lean_dec(v_r_2875_);
lean_dec(v_k_2873_);
v_a_2872_ = v_l_2874_;
goto _start;
}
}
else
{
lean_dec(v_k_2870_);
lean_dec_ref(v_inst_2869_);
return v_best_2871_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(lean_object* v_00_u03b1_2881_, lean_object* v_00_u03b2_2882_, lean_object* v_inst_2883_, lean_object* v_k_2884_, lean_object* v_best_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2883_, v_k_2884_, v_best_2885_, v_a_2886_);
return v___x_2887_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___redArg(lean_object* v_inst_2888_, lean_object* v_k_2889_, lean_object* v_a_2890_){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_box(0);
v___x_2892_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2888_, v_k_2889_, v___x_2891_, v_a_2890_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(lean_object* v_00_u03b1_2893_, lean_object* v_00_u03b2_2894_, lean_object* v_inst_2895_, lean_object* v_k_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2898_ = lean_box(0);
v___x_2899_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2895_, v_k_2896_, v___x_2898_, v_a_2897_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(lean_object* v_inst_2900_, lean_object* v_inst_2901_, lean_object* v_k_2902_, lean_object* v_t_2903_){
_start:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; 
v___x_2904_ = lean_box(0);
v___x_2905_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2900_, v_k_2902_, v___x_2904_, v_t_2903_);
if (lean_obj_tag(v___x_2905_) == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2907_ = l_panic___redArg(v_inst_2901_, v___x_2906_);
return v___x_2907_;
}
else
{
lean_object* v_val_2908_; 
v_val_2908_ = lean_ctor_get(v___x_2905_, 0);
lean_inc(v_val_2908_);
lean_dec_ref_known(v___x_2905_, 1);
return v_val_2908_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg___boxed(lean_object* v_inst_2909_, lean_object* v_inst_2910_, lean_object* v_k_2911_, lean_object* v_t_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(v_inst_2909_, v_inst_2910_, v_k_2911_, v_t_2912_);
lean_dec(v_inst_2910_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object* v_00_u03b1_2914_, lean_object* v_00_u03b2_2915_, lean_object* v_inst_2916_, lean_object* v_inst_2917_, lean_object* v_k_2918_, lean_object* v_t_2919_){
_start:
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
v___x_2920_ = lean_box(0);
v___x_2921_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2916_, v_k_2918_, v___x_2920_, v_t_2919_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v___x_2922_; lean_object* v___x_2923_; 
v___x_2922_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2923_ = l_panic___redArg(v_inst_2917_, v___x_2922_);
return v___x_2923_;
}
else
{
lean_object* v_val_2924_; 
v_val_2924_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_val_2924_);
lean_dec_ref_known(v___x_2921_, 1);
return v_val_2924_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___boxed(lean_object* v_00_u03b1_2925_, lean_object* v_00_u03b2_2926_, lean_object* v_inst_2927_, lean_object* v_inst_2928_, lean_object* v_k_2929_, lean_object* v_t_2930_){
_start:
{
lean_object* v_res_2931_; 
v_res_2931_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(v_00_u03b1_2925_, v_00_u03b2_2926_, v_inst_2927_, v_inst_2928_, v_k_2929_, v_t_2930_);
lean_dec(v_inst_2928_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(lean_object* v_inst_2932_, lean_object* v_inst_2933_, lean_object* v_k_2934_, lean_object* v_t_2935_){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_box(0);
v___x_2937_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2932_, v_k_2934_, v___x_2936_, v_t_2935_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2939_ = l_panic___redArg(v_inst_2933_, v___x_2938_);
return v___x_2939_;
}
else
{
lean_object* v_val_2940_; 
v_val_2940_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_val_2940_);
lean_dec_ref_known(v___x_2937_, 1);
return v_val_2940_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg___boxed(lean_object* v_inst_2941_, lean_object* v_inst_2942_, lean_object* v_k_2943_, lean_object* v_t_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(v_inst_2941_, v_inst_2942_, v_k_2943_, v_t_2944_);
lean_dec(v_inst_2942_);
return v_res_2945_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object* v_00_u03b1_2946_, lean_object* v_00_u03b2_2947_, lean_object* v_inst_2948_, lean_object* v_inst_2949_, lean_object* v_k_2950_, lean_object* v_t_2951_){
_start:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = lean_box(0);
v___x_2953_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2948_, v_k_2950_, v___x_2952_, v_t_2951_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2955_ = l_panic___redArg(v_inst_2949_, v___x_2954_);
return v___x_2955_;
}
else
{
lean_object* v_val_2956_; 
v_val_2956_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_val_2956_);
lean_dec_ref_known(v___x_2953_, 1);
return v_val_2956_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___boxed(lean_object* v_00_u03b1_2957_, lean_object* v_00_u03b2_2958_, lean_object* v_inst_2959_, lean_object* v_inst_2960_, lean_object* v_k_2961_, lean_object* v_t_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(v_00_u03b1_2957_, v_00_u03b2_2958_, v_inst_2959_, v_inst_2960_, v_k_2961_, v_t_2962_);
lean_dec(v_inst_2960_);
return v_res_2963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(lean_object* v_inst_2964_, lean_object* v_inst_2965_, lean_object* v_k_2966_, lean_object* v_t_2967_){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = lean_box(0);
v___x_2969_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2964_, v_k_2966_, v___x_2968_, v_t_2967_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v___x_2970_; lean_object* v___x_2971_; 
v___x_2970_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2971_ = l_panic___redArg(v_inst_2965_, v___x_2970_);
return v___x_2971_;
}
else
{
lean_object* v_val_2972_; 
v_val_2972_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_val_2972_);
lean_dec_ref_known(v___x_2969_, 1);
return v_val_2972_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg___boxed(lean_object* v_inst_2973_, lean_object* v_inst_2974_, lean_object* v_k_2975_, lean_object* v_t_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(v_inst_2973_, v_inst_2974_, v_k_2975_, v_t_2976_);
lean_dec(v_inst_2974_);
return v_res_2977_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object* v_00_u03b1_2978_, lean_object* v_00_u03b2_2979_, lean_object* v_inst_2980_, lean_object* v_inst_2981_, lean_object* v_k_2982_, lean_object* v_t_2983_){
_start:
{
lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2984_ = lean_box(0);
v___x_2985_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2980_, v_k_2982_, v___x_2984_, v_t_2983_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2986_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2987_ = l_panic___redArg(v_inst_2981_, v___x_2986_);
return v___x_2987_;
}
else
{
lean_object* v_val_2988_; 
v_val_2988_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_val_2988_);
lean_dec_ref_known(v___x_2985_, 1);
return v_val_2988_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___boxed(lean_object* v_00_u03b1_2989_, lean_object* v_00_u03b2_2990_, lean_object* v_inst_2991_, lean_object* v_inst_2992_, lean_object* v_k_2993_, lean_object* v_t_2994_){
_start:
{
lean_object* v_res_2995_; 
v_res_2995_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(v_00_u03b1_2989_, v_00_u03b2_2990_, v_inst_2991_, v_inst_2992_, v_k_2993_, v_t_2994_);
lean_dec(v_inst_2992_);
return v_res_2995_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(lean_object* v_inst_2996_, lean_object* v_inst_2997_, lean_object* v_k_2998_, lean_object* v_t_2999_){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_box(0);
v___x_3001_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2996_, v_k_2998_, v___x_3000_, v_t_2999_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3003_ = l_panic___redArg(v_inst_2997_, v___x_3002_);
return v___x_3003_;
}
else
{
lean_object* v_val_3004_; 
v_val_3004_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_val_3004_);
lean_dec_ref_known(v___x_3001_, 1);
return v_val_3004_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg___boxed(lean_object* v_inst_3005_, lean_object* v_inst_3006_, lean_object* v_k_3007_, lean_object* v_t_3008_){
_start:
{
lean_object* v_res_3009_; 
v_res_3009_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(v_inst_3005_, v_inst_3006_, v_k_3007_, v_t_3008_);
lean_dec(v_inst_3006_);
return v_res_3009_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object* v_00_u03b1_3010_, lean_object* v_00_u03b2_3011_, lean_object* v_inst_3012_, lean_object* v_inst_3013_, lean_object* v_k_3014_, lean_object* v_t_3015_){
_start:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_box(0);
v___x_3017_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3012_, v_k_3014_, v___x_3016_, v_t_3015_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3018_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3019_ = l_panic___redArg(v_inst_3013_, v___x_3018_);
return v___x_3019_;
}
else
{
lean_object* v_val_3020_; 
v_val_3020_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_val_3020_);
lean_dec_ref_known(v___x_3017_, 1);
return v_val_3020_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___boxed(lean_object* v_00_u03b1_3021_, lean_object* v_00_u03b2_3022_, lean_object* v_inst_3023_, lean_object* v_inst_3024_, lean_object* v_k_3025_, lean_object* v_t_3026_){
_start:
{
lean_object* v_res_3027_; 
v_res_3027_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(v_00_u03b1_3021_, v_00_u03b2_3022_, v_inst_3023_, v_inst_3024_, v_k_3025_, v_t_3026_);
lean_dec(v_inst_3024_);
return v_res_3027_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(lean_object* v_inst_3028_, lean_object* v_k_3029_, lean_object* v_t_3030_, lean_object* v_fallback_3031_){
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
lean_dec_ref_known(v___x_3033_, 1);
return v_val_3034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg___boxed(lean_object* v_inst_3035_, lean_object* v_k_3036_, lean_object* v_t_3037_, lean_object* v_fallback_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(v_inst_3035_, v_k_3036_, v_t_3037_, v_fallback_3038_);
lean_dec(v_fallback_3038_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED(lean_object* v_00_u03b1_3040_, lean_object* v_00_u03b2_3041_, lean_object* v_inst_3042_, lean_object* v_k_3043_, lean_object* v_t_3044_, lean_object* v_fallback_3045_){
_start:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_box(0);
v___x_3047_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3042_, v_k_3043_, v___x_3046_, v_t_3044_);
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
lean_dec_ref_known(v___x_3047_, 1);
return v_val_3048_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___boxed(lean_object* v_00_u03b1_3049_, lean_object* v_00_u03b2_3050_, lean_object* v_inst_3051_, lean_object* v_k_3052_, lean_object* v_t_3053_, lean_object* v_fallback_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l_Std_DTreeMap_Internal_Impl_getKeyGED(v_00_u03b1_3049_, v_00_u03b2_3050_, v_inst_3051_, v_k_3052_, v_t_3053_, v_fallback_3054_);
lean_dec(v_fallback_3054_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(lean_object* v_inst_3056_, lean_object* v_k_3057_, lean_object* v_t_3058_, lean_object* v_fallback_3059_){
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
lean_dec_ref_known(v___x_3061_, 1);
return v_val_3062_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg___boxed(lean_object* v_inst_3063_, lean_object* v_k_3064_, lean_object* v_t_3065_, lean_object* v_fallback_3066_){
_start:
{
lean_object* v_res_3067_; 
v_res_3067_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(v_inst_3063_, v_k_3064_, v_t_3065_, v_fallback_3066_);
lean_dec(v_fallback_3066_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD(lean_object* v_00_u03b1_3068_, lean_object* v_00_u03b2_3069_, lean_object* v_inst_3070_, lean_object* v_k_3071_, lean_object* v_t_3072_, lean_object* v_fallback_3073_){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_box(0);
v___x_3075_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3070_, v_k_3071_, v___x_3074_, v_t_3072_);
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
lean_dec_ref_known(v___x_3075_, 1);
return v_val_3076_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___boxed(lean_object* v_00_u03b1_3077_, lean_object* v_00_u03b2_3078_, lean_object* v_inst_3079_, lean_object* v_k_3080_, lean_object* v_t_3081_, lean_object* v_fallback_3082_){
_start:
{
lean_object* v_res_3083_; 
v_res_3083_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD(v_00_u03b1_3077_, v_00_u03b2_3078_, v_inst_3079_, v_k_3080_, v_t_3081_, v_fallback_3082_);
lean_dec(v_fallback_3082_);
return v_res_3083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(lean_object* v_inst_3084_, lean_object* v_k_3085_, lean_object* v_t_3086_, lean_object* v_fallback_3087_){
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
lean_dec_ref_known(v___x_3089_, 1);
return v_val_3090_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg___boxed(lean_object* v_inst_3091_, lean_object* v_k_3092_, lean_object* v_t_3093_, lean_object* v_fallback_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(v_inst_3091_, v_k_3092_, v_t_3093_, v_fallback_3094_);
lean_dec(v_fallback_3094_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED(lean_object* v_00_u03b1_3096_, lean_object* v_00_u03b2_3097_, lean_object* v_inst_3098_, lean_object* v_k_3099_, lean_object* v_t_3100_, lean_object* v_fallback_3101_){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3102_ = lean_box(0);
v___x_3103_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3098_, v_k_3099_, v___x_3102_, v_t_3100_);
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
lean_dec_ref_known(v___x_3103_, 1);
return v_val_3104_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___boxed(lean_object* v_00_u03b1_3105_, lean_object* v_00_u03b2_3106_, lean_object* v_inst_3107_, lean_object* v_k_3108_, lean_object* v_t_3109_, lean_object* v_fallback_3110_){
_start:
{
lean_object* v_res_3111_; 
v_res_3111_ = l_Std_DTreeMap_Internal_Impl_getKeyLED(v_00_u03b1_3105_, v_00_u03b2_3106_, v_inst_3107_, v_k_3108_, v_t_3109_, v_fallback_3110_);
lean_dec(v_fallback_3110_);
return v_res_3111_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(lean_object* v_inst_3112_, lean_object* v_k_3113_, lean_object* v_t_3114_, lean_object* v_fallback_3115_){
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
lean_dec_ref_known(v___x_3117_, 1);
return v_val_3118_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg___boxed(lean_object* v_inst_3119_, lean_object* v_k_3120_, lean_object* v_t_3121_, lean_object* v_fallback_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(v_inst_3119_, v_k_3120_, v_t_3121_, v_fallback_3122_);
lean_dec(v_fallback_3122_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD(lean_object* v_00_u03b1_3124_, lean_object* v_00_u03b2_3125_, lean_object* v_inst_3126_, lean_object* v_k_3127_, lean_object* v_t_3128_, lean_object* v_fallback_3129_){
_start:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_box(0);
v___x_3131_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3126_, v_k_3127_, v___x_3130_, v_t_3128_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_inc(v_fallback_3129_);
return v_fallback_3129_;
}
else
{
lean_object* v_val_3132_; 
v_val_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_val_3132_);
lean_dec_ref_known(v___x_3131_, 1);
return v_val_3132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___boxed(lean_object* v_00_u03b1_3133_, lean_object* v_00_u03b2_3134_, lean_object* v_inst_3135_, lean_object* v_k_3136_, lean_object* v_t_3137_, lean_object* v_fallback_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD(v_00_u03b1_3133_, v_00_u03b2_3134_, v_inst_3135_, v_k_3136_, v_t_3137_, v_fallback_3138_);
lean_dec(v_fallback_3138_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object* v_inst_3140_, lean_object* v_k_3141_, lean_object* v_x_3142_){
_start:
{
lean_object* v_k_3143_; lean_object* v_l_3144_; lean_object* v_r_3145_; lean_object* v___x_3146_; uint8_t v___x_3147_; 
v_k_3143_ = lean_ctor_get(v_x_3142_, 1);
lean_inc_n(v_k_3143_, 2);
v_l_3144_ = lean_ctor_get(v_x_3142_, 3);
lean_inc(v_l_3144_);
v_r_3145_ = lean_ctor_get(v_x_3142_, 4);
lean_inc(v_r_3145_);
lean_dec(v_x_3142_);
lean_inc_ref(v_inst_3140_);
lean_inc(v_k_3141_);
v___x_3146_ = lean_apply_2(v_inst_3140_, v_k_3141_, v_k_3143_);
v___x_3147_ = lean_unbox(v___x_3146_);
switch(v___x_3147_)
{
case 0:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
lean_dec(v_r_3145_);
v___x_3148_ = lean_box(0);
v___x_3149_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3140_, v_k_3141_, v___x_3148_, v_l_3144_);
if (lean_obj_tag(v___x_3149_) == 0)
{
return v_k_3143_;
}
else
{
lean_object* v_val_3150_; 
lean_dec(v_k_3143_);
v_val_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_val_3150_);
lean_dec_ref_known(v___x_3149_, 1);
return v_val_3150_;
}
}
case 1:
{
lean_dec(v_r_3145_);
lean_dec(v_l_3144_);
lean_dec(v_k_3141_);
lean_dec_ref(v_inst_3140_);
return v_k_3143_;
}
default: 
{
lean_dec(v_l_3144_);
lean_dec(v_k_3143_);
v_x_3142_ = v_r_3145_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE(lean_object* v_00_u03b1_3152_, lean_object* v_00_u03b2_3153_, lean_object* v_inst_3154_, lean_object* v_inst_3155_, lean_object* v_k_3156_, lean_object* v_x_3157_, lean_object* v_x_3158_, lean_object* v_x_3159_){
_start:
{
lean_object* v___x_3160_; 
v___x_3160_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_inst_3154_, v_k_3156_, v_x_3157_);
return v___x_3160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object* v_inst_3161_, lean_object* v_k_3162_, lean_object* v_x_3163_){
_start:
{
lean_object* v_k_3164_; lean_object* v_l_3165_; lean_object* v_r_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; uint8_t v___x_3171_; 
v_k_3164_ = lean_ctor_get(v_x_3163_, 1);
lean_inc_n(v_k_3164_, 2);
v_l_3165_ = lean_ctor_get(v_x_3163_, 3);
lean_inc(v_l_3165_);
v_r_3166_ = lean_ctor_get(v_x_3163_, 4);
lean_inc(v_r_3166_);
lean_dec(v_x_3163_);
lean_inc_ref(v_inst_3161_);
lean_inc(v_k_3162_);
v___x_3167_ = lean_apply_2(v_inst_3161_, v_k_3162_, v_k_3164_);
v___x_3168_ = lean_unbox(v___x_3167_);
v___x_3169_ = l_Ordering_ctorIdx(v___x_3168_);
v___x_3170_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0);
v___x_3171_ = lean_nat_dec_eq(v___x_3169_, v___x_3170_);
lean_dec(v___x_3169_);
if (v___x_3171_ == 0)
{
lean_dec(v_l_3165_);
lean_dec(v_k_3164_);
v_x_3163_ = v_r_3166_;
goto _start;
}
else
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
lean_dec(v_r_3166_);
v___x_3173_ = lean_box(0);
v___x_3174_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3161_, v_k_3162_, v___x_3173_, v_l_3165_);
if (lean_obj_tag(v___x_3174_) == 0)
{
return v_k_3164_;
}
else
{
lean_object* v_val_3175_; 
lean_dec(v_k_3164_);
v_val_3175_ = lean_ctor_get(v___x_3174_, 0);
lean_inc(v_val_3175_);
lean_dec_ref_known(v___x_3174_, 1);
return v_val_3175_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT(lean_object* v_00_u03b1_3176_, lean_object* v_00_u03b2_3177_, lean_object* v_inst_3178_, lean_object* v_inst_3179_, lean_object* v_k_3180_, lean_object* v_x_3181_, lean_object* v_x_3182_, lean_object* v_x_3183_){
_start:
{
lean_object* v___x_3184_; 
v___x_3184_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_inst_3178_, v_k_3180_, v_x_3181_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object* v_inst_3185_, lean_object* v_k_3186_, lean_object* v_x_3187_){
_start:
{
lean_object* v_k_3188_; lean_object* v_l_3189_; lean_object* v_r_3190_; lean_object* v___x_3191_; uint8_t v___x_3192_; 
v_k_3188_ = lean_ctor_get(v_x_3187_, 1);
lean_inc_n(v_k_3188_, 2);
v_l_3189_ = lean_ctor_get(v_x_3187_, 3);
lean_inc(v_l_3189_);
v_r_3190_ = lean_ctor_get(v_x_3187_, 4);
lean_inc(v_r_3190_);
lean_dec(v_x_3187_);
lean_inc_ref(v_inst_3185_);
lean_inc(v_k_3186_);
v___x_3191_ = lean_apply_2(v_inst_3185_, v_k_3186_, v_k_3188_);
v___x_3192_ = lean_unbox(v___x_3191_);
switch(v___x_3192_)
{
case 0:
{
lean_dec(v_r_3190_);
lean_dec(v_k_3188_);
v_x_3187_ = v_l_3189_;
goto _start;
}
case 1:
{
lean_dec(v_r_3190_);
lean_dec(v_l_3189_);
lean_dec(v_k_3186_);
lean_dec_ref(v_inst_3185_);
return v_k_3188_;
}
default: 
{
lean_object* v___x_3194_; lean_object* v___x_3195_; 
lean_dec(v_l_3189_);
v___x_3194_ = lean_box(0);
v___x_3195_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3185_, v_k_3186_, v___x_3194_, v_r_3190_);
if (lean_obj_tag(v___x_3195_) == 0)
{
return v_k_3188_;
}
else
{
lean_object* v_val_3196_; 
lean_dec(v_k_3188_);
v_val_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_val_3196_);
lean_dec_ref_known(v___x_3195_, 1);
return v_val_3196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE(lean_object* v_00_u03b1_3197_, lean_object* v_00_u03b2_3198_, lean_object* v_inst_3199_, lean_object* v_inst_3200_, lean_object* v_k_3201_, lean_object* v_x_3202_, lean_object* v_x_3203_, lean_object* v_x_3204_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_inst_3199_, v_k_3201_, v_x_3202_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object* v_inst_3206_, lean_object* v_k_3207_, lean_object* v_x_3208_){
_start:
{
lean_object* v_k_3209_; lean_object* v_l_3210_; lean_object* v_r_3211_; lean_object* v___x_3212_; uint8_t v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; uint8_t v___x_3216_; 
v_k_3209_ = lean_ctor_get(v_x_3208_, 1);
lean_inc_n(v_k_3209_, 2);
v_l_3210_ = lean_ctor_get(v_x_3208_, 3);
lean_inc(v_l_3210_);
v_r_3211_ = lean_ctor_get(v_x_3208_, 4);
lean_inc(v_r_3211_);
lean_dec(v_x_3208_);
lean_inc_ref(v_inst_3206_);
lean_inc(v_k_3207_);
v___x_3212_ = lean_apply_2(v_inst_3206_, v_k_3207_, v_k_3209_);
v___x_3213_ = lean_unbox(v___x_3212_);
v___x_3214_ = l_Ordering_ctorIdx(v___x_3213_);
v___x_3215_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0);
v___x_3216_ = lean_nat_dec_eq(v___x_3214_, v___x_3215_);
lean_dec(v___x_3214_);
if (v___x_3216_ == 0)
{
lean_dec(v_r_3211_);
lean_dec(v_k_3209_);
v_x_3208_ = v_l_3210_;
goto _start;
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec(v_l_3210_);
v___x_3218_ = lean_box(0);
v___x_3219_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3206_, v_k_3207_, v___x_3218_, v_r_3211_);
if (lean_obj_tag(v___x_3219_) == 0)
{
return v_k_3209_;
}
else
{
lean_object* v_val_3220_; 
lean_dec(v_k_3209_);
v_val_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_val_3220_);
lean_dec_ref_known(v___x_3219_, 1);
return v_val_3220_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT(lean_object* v_00_u03b1_3221_, lean_object* v_00_u03b2_3222_, lean_object* v_inst_3223_, lean_object* v_inst_3224_, lean_object* v_k_3225_, lean_object* v_x_3226_, lean_object* v_x_3227_, lean_object* v_x_3228_){
_start:
{
lean_object* v___x_3229_; 
v___x_3229_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_inst_3223_, v_k_3225_, v_x_3226_);
return v___x_3229_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object* v_x_3230_){
_start:
{
if (lean_obj_tag(v_x_3230_) == 0)
{
lean_object* v_l_3231_; 
v_l_3231_ = lean_ctor_get(v_x_3230_, 3);
if (lean_obj_tag(v_l_3231_) == 0)
{
v_x_3230_ = v_l_3231_;
goto _start;
}
else
{
lean_object* v_k_3233_; lean_object* v_v_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v_k_3233_ = lean_ctor_get(v_x_3230_, 1);
v_v_3234_ = lean_ctor_get(v_x_3230_, 2);
lean_inc(v_v_3234_);
lean_inc(v_k_3233_);
v___x_3235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3235_, 0, v_k_3233_);
lean_ctor_set(v___x_3235_, 1, v_v_3234_);
v___x_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3235_);
return v___x_3236_;
}
}
else
{
lean_object* v___x_3237_; 
v___x_3237_ = lean_box(0);
return v___x_3237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg___boxed(lean_object* v_x_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3238_);
lean_dec(v_x_3238_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(lean_object* v_00_u03b1_3240_, lean_object* v_00_u03b2_3241_, lean_object* v_x_3242_){
_start:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3242_);
return v___x_3243_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_3244_, lean_object* v_00_u03b2_3245_, lean_object* v_x_3246_){
_start:
{
lean_object* v_res_3247_; 
v_res_3247_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(v_00_u03b1_3244_, v_00_u03b2_3245_, v_x_3246_);
lean_dec(v_x_3246_);
return v_res_3247_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3248_, lean_object* v_h__1_3249_, lean_object* v_h__2_3250_, lean_object* v_h__3_3251_){
_start:
{
if (lean_obj_tag(v_x_3248_) == 0)
{
lean_object* v_l_3252_; 
lean_dec(v_h__1_3249_);
v_l_3252_ = lean_ctor_get(v_x_3248_, 3);
if (lean_obj_tag(v_l_3252_) == 0)
{
lean_object* v_size_3253_; lean_object* v_k_3254_; lean_object* v_v_3255_; lean_object* v_r_3256_; lean_object* v_size_3257_; lean_object* v_k_3258_; lean_object* v_v_3259_; lean_object* v_l_3260_; lean_object* v_r_3261_; lean_object* v___x_3262_; 
lean_inc_ref(v_l_3252_);
lean_dec(v_h__2_3250_);
v_size_3253_ = lean_ctor_get(v_x_3248_, 0);
lean_inc(v_size_3253_);
v_k_3254_ = lean_ctor_get(v_x_3248_, 1);
lean_inc(v_k_3254_);
v_v_3255_ = lean_ctor_get(v_x_3248_, 2);
lean_inc(v_v_3255_);
v_r_3256_ = lean_ctor_get(v_x_3248_, 4);
lean_inc(v_r_3256_);
lean_dec_ref_known(v_x_3248_, 5);
v_size_3257_ = lean_ctor_get(v_l_3252_, 0);
lean_inc(v_size_3257_);
v_k_3258_ = lean_ctor_get(v_l_3252_, 1);
lean_inc(v_k_3258_);
v_v_3259_ = lean_ctor_get(v_l_3252_, 2);
lean_inc(v_v_3259_);
v_l_3260_ = lean_ctor_get(v_l_3252_, 3);
lean_inc(v_l_3260_);
v_r_3261_ = lean_ctor_get(v_l_3252_, 4);
lean_inc(v_r_3261_);
lean_dec_ref_known(v_l_3252_, 5);
v___x_3262_ = lean_apply_9(v_h__3_3251_, v_size_3253_, v_k_3254_, v_v_3255_, v_size_3257_, v_k_3258_, v_v_3259_, v_l_3260_, v_r_3261_, v_r_3256_);
return v___x_3262_;
}
else
{
lean_object* v_size_3263_; lean_object* v_k_3264_; lean_object* v_v_3265_; lean_object* v_r_3266_; lean_object* v___x_3267_; 
lean_dec(v_h__3_3251_);
v_size_3263_ = lean_ctor_get(v_x_3248_, 0);
lean_inc(v_size_3263_);
v_k_3264_ = lean_ctor_get(v_x_3248_, 1);
lean_inc(v_k_3264_);
v_v_3265_ = lean_ctor_get(v_x_3248_, 2);
lean_inc(v_v_3265_);
v_r_3266_ = lean_ctor_get(v_x_3248_, 4);
lean_inc(v_r_3266_);
lean_dec_ref_known(v_x_3248_, 5);
v___x_3267_ = lean_apply_4(v_h__2_3250_, v_size_3263_, v_k_3264_, v_v_3265_, v_r_3266_);
return v___x_3267_;
}
}
else
{
lean_object* v___x_3268_; lean_object* v___x_3269_; 
lean_dec(v_h__3_3251_);
lean_dec(v_h__2_3250_);
v___x_3268_ = lean_box(0);
v___x_3269_ = lean_apply_1(v_h__1_3249_, v___x_3268_);
return v___x_3269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3270_, lean_object* v_00_u03b2_3271_, lean_object* v_motive_3272_, lean_object* v_x_3273_, lean_object* v_h__1_3274_, lean_object* v_h__2_3275_, lean_object* v_h__3_3276_){
_start:
{
if (lean_obj_tag(v_x_3273_) == 0)
{
lean_object* v_l_3277_; 
lean_dec(v_h__1_3274_);
v_l_3277_ = lean_ctor_get(v_x_3273_, 3);
if (lean_obj_tag(v_l_3277_) == 0)
{
lean_object* v_size_3278_; lean_object* v_k_3279_; lean_object* v_v_3280_; lean_object* v_r_3281_; lean_object* v_size_3282_; lean_object* v_k_3283_; lean_object* v_v_3284_; lean_object* v_l_3285_; lean_object* v_r_3286_; lean_object* v___x_3287_; 
lean_inc_ref(v_l_3277_);
lean_dec(v_h__2_3275_);
v_size_3278_ = lean_ctor_get(v_x_3273_, 0);
lean_inc(v_size_3278_);
v_k_3279_ = lean_ctor_get(v_x_3273_, 1);
lean_inc(v_k_3279_);
v_v_3280_ = lean_ctor_get(v_x_3273_, 2);
lean_inc(v_v_3280_);
v_r_3281_ = lean_ctor_get(v_x_3273_, 4);
lean_inc(v_r_3281_);
lean_dec_ref_known(v_x_3273_, 5);
v_size_3282_ = lean_ctor_get(v_l_3277_, 0);
lean_inc(v_size_3282_);
v_k_3283_ = lean_ctor_get(v_l_3277_, 1);
lean_inc(v_k_3283_);
v_v_3284_ = lean_ctor_get(v_l_3277_, 2);
lean_inc(v_v_3284_);
v_l_3285_ = lean_ctor_get(v_l_3277_, 3);
lean_inc(v_l_3285_);
v_r_3286_ = lean_ctor_get(v_l_3277_, 4);
lean_inc(v_r_3286_);
lean_dec_ref_known(v_l_3277_, 5);
v___x_3287_ = lean_apply_9(v_h__3_3276_, v_size_3278_, v_k_3279_, v_v_3280_, v_size_3282_, v_k_3283_, v_v_3284_, v_l_3285_, v_r_3286_, v_r_3281_);
return v___x_3287_;
}
else
{
lean_object* v_size_3288_; lean_object* v_k_3289_; lean_object* v_v_3290_; lean_object* v_r_3291_; lean_object* v___x_3292_; 
lean_dec(v_h__3_3276_);
v_size_3288_ = lean_ctor_get(v_x_3273_, 0);
lean_inc(v_size_3288_);
v_k_3289_ = lean_ctor_get(v_x_3273_, 1);
lean_inc(v_k_3289_);
v_v_3290_ = lean_ctor_get(v_x_3273_, 2);
lean_inc(v_v_3290_);
v_r_3291_ = lean_ctor_get(v_x_3273_, 4);
lean_inc(v_r_3291_);
lean_dec_ref_known(v_x_3273_, 5);
v___x_3292_ = lean_apply_4(v_h__2_3275_, v_size_3288_, v_k_3289_, v_v_3290_, v_r_3291_);
return v___x_3292_;
}
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
lean_dec(v_h__3_3276_);
lean_dec(v_h__2_3275_);
v___x_3293_ = lean_box(0);
v___x_3294_ = lean_apply_1(v_h__1_3274_, v___x_3293_);
return v___x_3294_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object* v_x_3295_){
_start:
{
lean_object* v_l_3296_; 
v_l_3296_ = lean_ctor_get(v_x_3295_, 3);
if (lean_obj_tag(v_l_3296_) == 0)
{
v_x_3295_ = v_l_3296_;
goto _start;
}
else
{
lean_object* v_k_3298_; lean_object* v_v_3299_; lean_object* v___x_3300_; 
v_k_3298_ = lean_ctor_get(v_x_3295_, 1);
v_v_3299_ = lean_ctor_get(v_x_3295_, 2);
lean_inc(v_v_3299_);
lean_inc(v_k_3298_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_k_3298_);
lean_ctor_set(v___x_3300_, 1, v_v_3299_);
return v___x_3300_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg___boxed(lean_object* v_x_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3301_);
lean_dec(v_x_3301_);
return v_res_3302_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry(lean_object* v_00_u03b1_3303_, lean_object* v_00_u03b2_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
lean_object* v___x_3307_; 
v___x_3307_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3305_);
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___boxed(lean_object* v_00_u03b1_3308_, lean_object* v_00_u03b2_3309_, lean_object* v_x_3310_, lean_object* v_x_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry(v_00_u03b1_3308_, v_00_u03b2_3309_, v_x_3310_, v_x_3311_);
lean_dec(v_x_3310_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_3313_, lean_object* v_h__1_3314_, lean_object* v_h__2_3315_){
_start:
{
lean_object* v_l_3316_; 
v_l_3316_ = lean_ctor_get(v_x_3313_, 3);
if (lean_obj_tag(v_l_3316_) == 0)
{
lean_object* v_size_3317_; lean_object* v_k_3318_; lean_object* v_v_3319_; lean_object* v_r_3320_; lean_object* v_size_3321_; lean_object* v_k_3322_; lean_object* v_v_3323_; lean_object* v_l_3324_; lean_object* v_r_3325_; lean_object* v___x_3326_; 
lean_inc_ref(v_l_3316_);
lean_dec(v_h__1_3314_);
v_size_3317_ = lean_ctor_get(v_x_3313_, 0);
lean_inc(v_size_3317_);
v_k_3318_ = lean_ctor_get(v_x_3313_, 1);
lean_inc(v_k_3318_);
v_v_3319_ = lean_ctor_get(v_x_3313_, 2);
lean_inc(v_v_3319_);
v_r_3320_ = lean_ctor_get(v_x_3313_, 4);
lean_inc(v_r_3320_);
lean_dec(v_x_3313_);
v_size_3321_ = lean_ctor_get(v_l_3316_, 0);
lean_inc(v_size_3321_);
v_k_3322_ = lean_ctor_get(v_l_3316_, 1);
lean_inc(v_k_3322_);
v_v_3323_ = lean_ctor_get(v_l_3316_, 2);
lean_inc(v_v_3323_);
v_l_3324_ = lean_ctor_get(v_l_3316_, 3);
lean_inc(v_l_3324_);
v_r_3325_ = lean_ctor_get(v_l_3316_, 4);
lean_inc(v_r_3325_);
lean_dec_ref_known(v_l_3316_, 5);
v___x_3326_ = lean_apply_10(v_h__2_3315_, v_size_3317_, v_k_3318_, v_v_3319_, v_size_3321_, v_k_3322_, v_v_3323_, v_l_3324_, v_r_3325_, v_r_3320_, lean_box(0));
return v___x_3326_;
}
else
{
lean_object* v_size_3327_; lean_object* v_k_3328_; lean_object* v_v_3329_; lean_object* v_r_3330_; lean_object* v___x_3331_; 
lean_dec(v_h__2_3315_);
v_size_3327_ = lean_ctor_get(v_x_3313_, 0);
lean_inc(v_size_3327_);
v_k_3328_ = lean_ctor_get(v_x_3313_, 1);
lean_inc(v_k_3328_);
v_v_3329_ = lean_ctor_get(v_x_3313_, 2);
lean_inc(v_v_3329_);
v_r_3330_ = lean_ctor_get(v_x_3313_, 4);
lean_inc(v_r_3330_);
lean_dec(v_x_3313_);
v___x_3331_ = lean_apply_5(v_h__1_3314_, v_size_3327_, v_k_3328_, v_v_3329_, v_r_3330_, lean_box(0));
return v___x_3331_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_3332_, lean_object* v_00_u03b2_3333_, lean_object* v_motive_3334_, lean_object* v_x_3335_, lean_object* v_x_3336_, lean_object* v_h__1_3337_, lean_object* v_h__2_3338_){
_start:
{
lean_object* v_l_3339_; 
v_l_3339_ = lean_ctor_get(v_x_3335_, 3);
if (lean_obj_tag(v_l_3339_) == 0)
{
lean_object* v_size_3340_; lean_object* v_k_3341_; lean_object* v_v_3342_; lean_object* v_r_3343_; lean_object* v_size_3344_; lean_object* v_k_3345_; lean_object* v_v_3346_; lean_object* v_l_3347_; lean_object* v_r_3348_; lean_object* v___x_3349_; 
lean_inc_ref(v_l_3339_);
lean_dec(v_h__1_3337_);
v_size_3340_ = lean_ctor_get(v_x_3335_, 0);
lean_inc(v_size_3340_);
v_k_3341_ = lean_ctor_get(v_x_3335_, 1);
lean_inc(v_k_3341_);
v_v_3342_ = lean_ctor_get(v_x_3335_, 2);
lean_inc(v_v_3342_);
v_r_3343_ = lean_ctor_get(v_x_3335_, 4);
lean_inc(v_r_3343_);
lean_dec(v_x_3335_);
v_size_3344_ = lean_ctor_get(v_l_3339_, 0);
lean_inc(v_size_3344_);
v_k_3345_ = lean_ctor_get(v_l_3339_, 1);
lean_inc(v_k_3345_);
v_v_3346_ = lean_ctor_get(v_l_3339_, 2);
lean_inc(v_v_3346_);
v_l_3347_ = lean_ctor_get(v_l_3339_, 3);
lean_inc(v_l_3347_);
v_r_3348_ = lean_ctor_get(v_l_3339_, 4);
lean_inc(v_r_3348_);
lean_dec_ref_known(v_l_3339_, 5);
v___x_3349_ = lean_apply_10(v_h__2_3338_, v_size_3340_, v_k_3341_, v_v_3342_, v_size_3344_, v_k_3345_, v_v_3346_, v_l_3347_, v_r_3348_, v_r_3343_, lean_box(0));
return v___x_3349_;
}
else
{
lean_object* v_size_3350_; lean_object* v_k_3351_; lean_object* v_v_3352_; lean_object* v_r_3353_; lean_object* v___x_3354_; 
lean_dec(v_h__2_3338_);
v_size_3350_ = lean_ctor_get(v_x_3335_, 0);
lean_inc(v_size_3350_);
v_k_3351_ = lean_ctor_get(v_x_3335_, 1);
lean_inc(v_k_3351_);
v_v_3352_ = lean_ctor_get(v_x_3335_, 2);
lean_inc(v_v_3352_);
v_r_3353_ = lean_ctor_get(v_x_3335_, 4);
lean_inc(v_r_3353_);
lean_dec(v_x_3335_);
v___x_3354_ = lean_apply_5(v_h__1_3337_, v_size_3350_, v_k_3351_, v_v_3352_, v_r_3353_, lean_box(0));
return v___x_3354_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3356_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3357_ = lean_unsigned_to_nat(13u);
v___x_3358_ = lean_unsigned_to_nat(816u);
v___x_3359_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0));
v___x_3360_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3361_ = l_mkPanicMessageWithDecl(v___x_3360_, v___x_3359_, v___x_3358_, v___x_3357_, v___x_3356_);
return v___x_3361_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object* v_inst_3362_, lean_object* v_x_3363_){
_start:
{
if (lean_obj_tag(v_x_3363_) == 0)
{
lean_object* v_l_3364_; 
v_l_3364_ = lean_ctor_get(v_x_3363_, 3);
if (lean_obj_tag(v_l_3364_) == 0)
{
v_x_3363_ = v_l_3364_;
goto _start;
}
else
{
lean_object* v_k_3366_; lean_object* v_v_3367_; lean_object* v___x_3368_; 
v_k_3366_ = lean_ctor_get(v_x_3363_, 1);
v_v_3367_ = lean_ctor_get(v_x_3363_, 2);
lean_inc(v_v_3367_);
lean_inc(v_k_3366_);
v___x_3368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3368_, 0, v_k_3366_);
lean_ctor_set(v___x_3368_, 1, v_v_3367_);
return v___x_3368_;
}
}
else
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1);
v___x_3370_ = l_panic___redArg(v_inst_3362_, v___x_3369_);
return v___x_3370_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_3371_, lean_object* v_x_3372_){
_start:
{
lean_object* v_res_3373_; 
v_res_3373_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3371_, v_x_3372_);
lean_dec(v_x_3372_);
lean_dec_ref(v_inst_3371_);
return v_res_3373_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(lean_object* v_00_u03b1_3374_, lean_object* v_00_u03b2_3375_, lean_object* v_inst_3376_, lean_object* v_x_3377_){
_start:
{
lean_object* v___x_3378_; 
v___x_3378_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3376_, v_x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_3379_, lean_object* v_00_u03b2_3380_, lean_object* v_inst_3381_, lean_object* v_x_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(v_00_u03b1_3379_, v_00_u03b2_3380_, v_inst_3381_, v_x_3382_);
lean_dec(v_x_3382_);
lean_dec_ref(v_inst_3381_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object* v_x_3384_, lean_object* v_x_3385_){
_start:
{
if (lean_obj_tag(v_x_3384_) == 0)
{
lean_object* v_l_3386_; 
v_l_3386_ = lean_ctor_get(v_x_3384_, 3);
if (lean_obj_tag(v_l_3386_) == 0)
{
v_x_3384_ = v_l_3386_;
goto _start;
}
else
{
lean_object* v_k_3388_; lean_object* v_v_3389_; lean_object* v___x_3390_; 
v_k_3388_ = lean_ctor_get(v_x_3384_, 1);
v_v_3389_ = lean_ctor_get(v_x_3384_, 2);
lean_inc(v_v_3389_);
lean_inc(v_k_3388_);
v___x_3390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3390_, 0, v_k_3388_);
lean_ctor_set(v___x_3390_, 1, v_v_3389_);
return v___x_3390_;
}
}
else
{
lean_inc_ref(v_x_3385_);
return v_x_3385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg___boxed(lean_object* v_x_3391_, lean_object* v_x_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3391_, v_x_3392_);
lean_dec_ref(v_x_3392_);
lean_dec(v_x_3391_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD(lean_object* v_00_u03b1_3394_, lean_object* v_00_u03b2_3395_, lean_object* v_x_3396_, lean_object* v_x_3397_){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3396_, v_x_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___boxed(lean_object* v_00_u03b1_3399_, lean_object* v_00_u03b2_3400_, lean_object* v_x_3401_, lean_object* v_x_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD(v_00_u03b1_3399_, v_00_u03b2_3400_, v_x_3401_, v_x_3402_);
lean_dec_ref(v_x_3402_);
lean_dec(v_x_3401_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_3404_, lean_object* v_x_3405_, lean_object* v_h__1_3406_, lean_object* v_h__2_3407_, lean_object* v_h__3_3408_){
_start:
{
if (lean_obj_tag(v_x_3404_) == 0)
{
lean_object* v_l_3409_; 
lean_dec(v_h__1_3406_);
v_l_3409_ = lean_ctor_get(v_x_3404_, 3);
if (lean_obj_tag(v_l_3409_) == 0)
{
lean_object* v_size_3410_; lean_object* v_k_3411_; lean_object* v_v_3412_; lean_object* v_r_3413_; lean_object* v_size_3414_; lean_object* v_k_3415_; lean_object* v_v_3416_; lean_object* v_l_3417_; lean_object* v_r_3418_; lean_object* v___x_3419_; 
lean_inc_ref(v_l_3409_);
lean_dec(v_h__2_3407_);
v_size_3410_ = lean_ctor_get(v_x_3404_, 0);
lean_inc(v_size_3410_);
v_k_3411_ = lean_ctor_get(v_x_3404_, 1);
lean_inc(v_k_3411_);
v_v_3412_ = lean_ctor_get(v_x_3404_, 2);
lean_inc(v_v_3412_);
v_r_3413_ = lean_ctor_get(v_x_3404_, 4);
lean_inc(v_r_3413_);
lean_dec_ref_known(v_x_3404_, 5);
v_size_3414_ = lean_ctor_get(v_l_3409_, 0);
lean_inc(v_size_3414_);
v_k_3415_ = lean_ctor_get(v_l_3409_, 1);
lean_inc(v_k_3415_);
v_v_3416_ = lean_ctor_get(v_l_3409_, 2);
lean_inc(v_v_3416_);
v_l_3417_ = lean_ctor_get(v_l_3409_, 3);
lean_inc(v_l_3417_);
v_r_3418_ = lean_ctor_get(v_l_3409_, 4);
lean_inc(v_r_3418_);
lean_dec_ref_known(v_l_3409_, 5);
v___x_3419_ = lean_apply_10(v_h__3_3408_, v_size_3410_, v_k_3411_, v_v_3412_, v_size_3414_, v_k_3415_, v_v_3416_, v_l_3417_, v_r_3418_, v_r_3413_, v_x_3405_);
return v___x_3419_;
}
else
{
lean_object* v_size_3420_; lean_object* v_k_3421_; lean_object* v_v_3422_; lean_object* v_r_3423_; lean_object* v___x_3424_; 
lean_dec(v_h__3_3408_);
v_size_3420_ = lean_ctor_get(v_x_3404_, 0);
lean_inc(v_size_3420_);
v_k_3421_ = lean_ctor_get(v_x_3404_, 1);
lean_inc(v_k_3421_);
v_v_3422_ = lean_ctor_get(v_x_3404_, 2);
lean_inc(v_v_3422_);
v_r_3423_ = lean_ctor_get(v_x_3404_, 4);
lean_inc(v_r_3423_);
lean_dec_ref_known(v_x_3404_, 5);
v___x_3424_ = lean_apply_5(v_h__2_3407_, v_size_3420_, v_k_3421_, v_v_3422_, v_r_3423_, v_x_3405_);
return v___x_3424_;
}
}
else
{
lean_object* v___x_3425_; 
lean_dec(v_h__3_3408_);
lean_dec(v_h__2_3407_);
v___x_3425_ = lean_apply_1(v_h__1_3406_, v_x_3405_);
return v___x_3425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_3426_, lean_object* v_00_u03b2_3427_, lean_object* v_motive_3428_, lean_object* v_x_3429_, lean_object* v_x_3430_, lean_object* v_h__1_3431_, lean_object* v_h__2_3432_, lean_object* v_h__3_3433_){
_start:
{
if (lean_obj_tag(v_x_3429_) == 0)
{
lean_object* v_l_3434_; 
lean_dec(v_h__1_3431_);
v_l_3434_ = lean_ctor_get(v_x_3429_, 3);
if (lean_obj_tag(v_l_3434_) == 0)
{
lean_object* v_size_3435_; lean_object* v_k_3436_; lean_object* v_v_3437_; lean_object* v_r_3438_; lean_object* v_size_3439_; lean_object* v_k_3440_; lean_object* v_v_3441_; lean_object* v_l_3442_; lean_object* v_r_3443_; lean_object* v___x_3444_; 
lean_inc_ref(v_l_3434_);
lean_dec(v_h__2_3432_);
v_size_3435_ = lean_ctor_get(v_x_3429_, 0);
lean_inc(v_size_3435_);
v_k_3436_ = lean_ctor_get(v_x_3429_, 1);
lean_inc(v_k_3436_);
v_v_3437_ = lean_ctor_get(v_x_3429_, 2);
lean_inc(v_v_3437_);
v_r_3438_ = lean_ctor_get(v_x_3429_, 4);
lean_inc(v_r_3438_);
lean_dec_ref_known(v_x_3429_, 5);
v_size_3439_ = lean_ctor_get(v_l_3434_, 0);
lean_inc(v_size_3439_);
v_k_3440_ = lean_ctor_get(v_l_3434_, 1);
lean_inc(v_k_3440_);
v_v_3441_ = lean_ctor_get(v_l_3434_, 2);
lean_inc(v_v_3441_);
v_l_3442_ = lean_ctor_get(v_l_3434_, 3);
lean_inc(v_l_3442_);
v_r_3443_ = lean_ctor_get(v_l_3434_, 4);
lean_inc(v_r_3443_);
lean_dec_ref_known(v_l_3434_, 5);
v___x_3444_ = lean_apply_10(v_h__3_3433_, v_size_3435_, v_k_3436_, v_v_3437_, v_size_3439_, v_k_3440_, v_v_3441_, v_l_3442_, v_r_3443_, v_r_3438_, v_x_3430_);
return v___x_3444_;
}
else
{
lean_object* v_size_3445_; lean_object* v_k_3446_; lean_object* v_v_3447_; lean_object* v_r_3448_; lean_object* v___x_3449_; 
lean_dec(v_h__3_3433_);
v_size_3445_ = lean_ctor_get(v_x_3429_, 0);
lean_inc(v_size_3445_);
v_k_3446_ = lean_ctor_get(v_x_3429_, 1);
lean_inc(v_k_3446_);
v_v_3447_ = lean_ctor_get(v_x_3429_, 2);
lean_inc(v_v_3447_);
v_r_3448_ = lean_ctor_get(v_x_3429_, 4);
lean_inc(v_r_3448_);
lean_dec_ref_known(v_x_3429_, 5);
v___x_3449_ = lean_apply_5(v_h__2_3432_, v_size_3445_, v_k_3446_, v_v_3447_, v_r_3448_, v_x_3430_);
return v___x_3449_;
}
}
else
{
lean_object* v___x_3450_; 
lean_dec(v_h__3_3433_);
lean_dec(v_h__2_3432_);
v___x_3450_ = lean_apply_1(v_h__1_3431_, v_x_3430_);
return v___x_3450_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object* v_x_3451_){
_start:
{
if (lean_obj_tag(v_x_3451_) == 0)
{
lean_object* v_r_3452_; 
v_r_3452_ = lean_ctor_get(v_x_3451_, 4);
if (lean_obj_tag(v_r_3452_) == 0)
{
v_x_3451_ = v_r_3452_;
goto _start;
}
else
{
lean_object* v_k_3454_; lean_object* v_v_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_k_3454_ = lean_ctor_get(v_x_3451_, 1);
v_v_3455_ = lean_ctor_get(v_x_3451_, 2);
lean_inc(v_v_3455_);
lean_inc(v_k_3454_);
v___x_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3456_, 0, v_k_3454_);
lean_ctor_set(v___x_3456_, 1, v_v_3455_);
v___x_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
return v___x_3457_;
}
}
else
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_box(0);
return v___x_3458_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg___boxed(lean_object* v_x_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3459_);
lean_dec(v_x_3459_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(lean_object* v_00_u03b1_3461_, lean_object* v_00_u03b2_3462_, lean_object* v_x_3463_){
_start:
{
lean_object* v___x_3464_; 
v___x_3464_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3463_);
return v___x_3464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_3465_, lean_object* v_00_u03b2_3466_, lean_object* v_x_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(v_00_u03b1_3465_, v_00_u03b2_3466_, v_x_3467_);
lean_dec(v_x_3467_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3469_, lean_object* v_h__1_3470_, lean_object* v_h__2_3471_, lean_object* v_h__3_3472_){
_start:
{
if (lean_obj_tag(v_x_3469_) == 0)
{
lean_object* v_r_3473_; 
lean_dec(v_h__1_3470_);
v_r_3473_ = lean_ctor_get(v_x_3469_, 4);
if (lean_obj_tag(v_r_3473_) == 0)
{
lean_object* v_size_3474_; lean_object* v_k_3475_; lean_object* v_v_3476_; lean_object* v_l_3477_; lean_object* v_size_3478_; lean_object* v_k_3479_; lean_object* v_v_3480_; lean_object* v_l_3481_; lean_object* v_r_3482_; lean_object* v___x_3483_; 
lean_inc_ref(v_r_3473_);
lean_dec(v_h__2_3471_);
v_size_3474_ = lean_ctor_get(v_x_3469_, 0);
lean_inc(v_size_3474_);
v_k_3475_ = lean_ctor_get(v_x_3469_, 1);
lean_inc(v_k_3475_);
v_v_3476_ = lean_ctor_get(v_x_3469_, 2);
lean_inc(v_v_3476_);
v_l_3477_ = lean_ctor_get(v_x_3469_, 3);
lean_inc(v_l_3477_);
lean_dec_ref_known(v_x_3469_, 5);
v_size_3478_ = lean_ctor_get(v_r_3473_, 0);
lean_inc(v_size_3478_);
v_k_3479_ = lean_ctor_get(v_r_3473_, 1);
lean_inc(v_k_3479_);
v_v_3480_ = lean_ctor_get(v_r_3473_, 2);
lean_inc(v_v_3480_);
v_l_3481_ = lean_ctor_get(v_r_3473_, 3);
lean_inc(v_l_3481_);
v_r_3482_ = lean_ctor_get(v_r_3473_, 4);
lean_inc(v_r_3482_);
lean_dec_ref_known(v_r_3473_, 5);
v___x_3483_ = lean_apply_9(v_h__3_3472_, v_size_3474_, v_k_3475_, v_v_3476_, v_l_3477_, v_size_3478_, v_k_3479_, v_v_3480_, v_l_3481_, v_r_3482_);
return v___x_3483_;
}
else
{
lean_object* v_size_3484_; lean_object* v_k_3485_; lean_object* v_v_3486_; lean_object* v_l_3487_; lean_object* v___x_3488_; 
lean_dec(v_h__3_3472_);
v_size_3484_ = lean_ctor_get(v_x_3469_, 0);
lean_inc(v_size_3484_);
v_k_3485_ = lean_ctor_get(v_x_3469_, 1);
lean_inc(v_k_3485_);
v_v_3486_ = lean_ctor_get(v_x_3469_, 2);
lean_inc(v_v_3486_);
v_l_3487_ = lean_ctor_get(v_x_3469_, 3);
lean_inc(v_l_3487_);
lean_dec_ref_known(v_x_3469_, 5);
v___x_3488_ = lean_apply_4(v_h__2_3471_, v_size_3484_, v_k_3485_, v_v_3486_, v_l_3487_);
return v___x_3488_;
}
}
else
{
lean_object* v___x_3489_; lean_object* v___x_3490_; 
lean_dec(v_h__3_3472_);
lean_dec(v_h__2_3471_);
v___x_3489_ = lean_box(0);
v___x_3490_ = lean_apply_1(v_h__1_3470_, v___x_3489_);
return v___x_3490_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3491_, lean_object* v_00_u03b2_3492_, lean_object* v_motive_3493_, lean_object* v_x_3494_, lean_object* v_h__1_3495_, lean_object* v_h__2_3496_, lean_object* v_h__3_3497_){
_start:
{
if (lean_obj_tag(v_x_3494_) == 0)
{
lean_object* v_r_3498_; 
lean_dec(v_h__1_3495_);
v_r_3498_ = lean_ctor_get(v_x_3494_, 4);
if (lean_obj_tag(v_r_3498_) == 0)
{
lean_object* v_size_3499_; lean_object* v_k_3500_; lean_object* v_v_3501_; lean_object* v_l_3502_; lean_object* v_size_3503_; lean_object* v_k_3504_; lean_object* v_v_3505_; lean_object* v_l_3506_; lean_object* v_r_3507_; lean_object* v___x_3508_; 
lean_inc_ref(v_r_3498_);
lean_dec(v_h__2_3496_);
v_size_3499_ = lean_ctor_get(v_x_3494_, 0);
lean_inc(v_size_3499_);
v_k_3500_ = lean_ctor_get(v_x_3494_, 1);
lean_inc(v_k_3500_);
v_v_3501_ = lean_ctor_get(v_x_3494_, 2);
lean_inc(v_v_3501_);
v_l_3502_ = lean_ctor_get(v_x_3494_, 3);
lean_inc(v_l_3502_);
lean_dec_ref_known(v_x_3494_, 5);
v_size_3503_ = lean_ctor_get(v_r_3498_, 0);
lean_inc(v_size_3503_);
v_k_3504_ = lean_ctor_get(v_r_3498_, 1);
lean_inc(v_k_3504_);
v_v_3505_ = lean_ctor_get(v_r_3498_, 2);
lean_inc(v_v_3505_);
v_l_3506_ = lean_ctor_get(v_r_3498_, 3);
lean_inc(v_l_3506_);
v_r_3507_ = lean_ctor_get(v_r_3498_, 4);
lean_inc(v_r_3507_);
lean_dec_ref_known(v_r_3498_, 5);
v___x_3508_ = lean_apply_9(v_h__3_3497_, v_size_3499_, v_k_3500_, v_v_3501_, v_l_3502_, v_size_3503_, v_k_3504_, v_v_3505_, v_l_3506_, v_r_3507_);
return v___x_3508_;
}
else
{
lean_object* v_size_3509_; lean_object* v_k_3510_; lean_object* v_v_3511_; lean_object* v_l_3512_; lean_object* v___x_3513_; 
lean_dec(v_h__3_3497_);
v_size_3509_ = lean_ctor_get(v_x_3494_, 0);
lean_inc(v_size_3509_);
v_k_3510_ = lean_ctor_get(v_x_3494_, 1);
lean_inc(v_k_3510_);
v_v_3511_ = lean_ctor_get(v_x_3494_, 2);
lean_inc(v_v_3511_);
v_l_3512_ = lean_ctor_get(v_x_3494_, 3);
lean_inc(v_l_3512_);
lean_dec_ref_known(v_x_3494_, 5);
v___x_3513_ = lean_apply_4(v_h__2_3496_, v_size_3509_, v_k_3510_, v_v_3511_, v_l_3512_);
return v___x_3513_;
}
}
else
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
lean_dec(v_h__3_3497_);
lean_dec(v_h__2_3496_);
v___x_3514_ = lean_box(0);
v___x_3515_ = lean_apply_1(v_h__1_3495_, v___x_3514_);
return v___x_3515_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object* v_x_3516_){
_start:
{
lean_object* v_r_3517_; 
v_r_3517_ = lean_ctor_get(v_x_3516_, 4);
if (lean_obj_tag(v_r_3517_) == 0)
{
v_x_3516_ = v_r_3517_;
goto _start;
}
else
{
lean_object* v_k_3519_; lean_object* v_v_3520_; lean_object* v___x_3521_; 
v_k_3519_ = lean_ctor_get(v_x_3516_, 1);
v_v_3520_ = lean_ctor_get(v_x_3516_, 2);
lean_inc(v_v_3520_);
lean_inc(v_k_3519_);
v___x_3521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3521_, 0, v_k_3519_);
lean_ctor_set(v___x_3521_, 1, v_v_3520_);
return v___x_3521_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg___boxed(lean_object* v_x_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3522_);
lean_dec(v_x_3522_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry(lean_object* v_00_u03b1_3524_, lean_object* v_00_u03b2_3525_, lean_object* v_x_3526_, lean_object* v_x_3527_){
_start:
{
lean_object* v___x_3528_; 
v___x_3528_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3526_);
return v___x_3528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___boxed(lean_object* v_00_u03b1_3529_, lean_object* v_00_u03b2_3530_, lean_object* v_x_3531_, lean_object* v_x_3532_){
_start:
{
lean_object* v_res_3533_; 
v_res_3533_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry(v_00_u03b1_3529_, v_00_u03b2_3530_, v_x_3531_, v_x_3532_);
lean_dec(v_x_3531_);
return v_res_3533_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_3534_, lean_object* v_h__1_3535_, lean_object* v_h__2_3536_){
_start:
{
lean_object* v_r_3537_; 
v_r_3537_ = lean_ctor_get(v_x_3534_, 4);
if (lean_obj_tag(v_r_3537_) == 0)
{
lean_object* v_size_3538_; lean_object* v_k_3539_; lean_object* v_v_3540_; lean_object* v_l_3541_; lean_object* v_size_3542_; lean_object* v_k_3543_; lean_object* v_v_3544_; lean_object* v_l_3545_; lean_object* v_r_3546_; lean_object* v___x_3547_; 
lean_inc_ref(v_r_3537_);
lean_dec(v_h__1_3535_);
v_size_3538_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_size_3538_);
v_k_3539_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_k_3539_);
v_v_3540_ = lean_ctor_get(v_x_3534_, 2);
lean_inc(v_v_3540_);
v_l_3541_ = lean_ctor_get(v_x_3534_, 3);
lean_inc(v_l_3541_);
lean_dec(v_x_3534_);
v_size_3542_ = lean_ctor_get(v_r_3537_, 0);
lean_inc(v_size_3542_);
v_k_3543_ = lean_ctor_get(v_r_3537_, 1);
lean_inc(v_k_3543_);
v_v_3544_ = lean_ctor_get(v_r_3537_, 2);
lean_inc(v_v_3544_);
v_l_3545_ = lean_ctor_get(v_r_3537_, 3);
lean_inc(v_l_3545_);
v_r_3546_ = lean_ctor_get(v_r_3537_, 4);
lean_inc(v_r_3546_);
lean_dec_ref_known(v_r_3537_, 5);
v___x_3547_ = lean_apply_10(v_h__2_3536_, v_size_3538_, v_k_3539_, v_v_3540_, v_l_3541_, v_size_3542_, v_k_3543_, v_v_3544_, v_l_3545_, v_r_3546_, lean_box(0));
return v___x_3547_;
}
else
{
lean_object* v_size_3548_; lean_object* v_k_3549_; lean_object* v_v_3550_; lean_object* v_l_3551_; lean_object* v___x_3552_; 
lean_dec(v_h__2_3536_);
v_size_3548_ = lean_ctor_get(v_x_3534_, 0);
lean_inc(v_size_3548_);
v_k_3549_ = lean_ctor_get(v_x_3534_, 1);
lean_inc(v_k_3549_);
v_v_3550_ = lean_ctor_get(v_x_3534_, 2);
lean_inc(v_v_3550_);
v_l_3551_ = lean_ctor_get(v_x_3534_, 3);
lean_inc(v_l_3551_);
lean_dec(v_x_3534_);
v___x_3552_ = lean_apply_5(v_h__1_3535_, v_size_3548_, v_k_3549_, v_v_3550_, v_l_3551_, lean_box(0));
return v___x_3552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_3553_, lean_object* v_00_u03b2_3554_, lean_object* v_motive_3555_, lean_object* v_x_3556_, lean_object* v_x_3557_, lean_object* v_h__1_3558_, lean_object* v_h__2_3559_){
_start:
{
lean_object* v_r_3560_; 
v_r_3560_ = lean_ctor_get(v_x_3556_, 4);
if (lean_obj_tag(v_r_3560_) == 0)
{
lean_object* v_size_3561_; lean_object* v_k_3562_; lean_object* v_v_3563_; lean_object* v_l_3564_; lean_object* v_size_3565_; lean_object* v_k_3566_; lean_object* v_v_3567_; lean_object* v_l_3568_; lean_object* v_r_3569_; lean_object* v___x_3570_; 
lean_inc_ref(v_r_3560_);
lean_dec(v_h__1_3558_);
v_size_3561_ = lean_ctor_get(v_x_3556_, 0);
lean_inc(v_size_3561_);
v_k_3562_ = lean_ctor_get(v_x_3556_, 1);
lean_inc(v_k_3562_);
v_v_3563_ = lean_ctor_get(v_x_3556_, 2);
lean_inc(v_v_3563_);
v_l_3564_ = lean_ctor_get(v_x_3556_, 3);
lean_inc(v_l_3564_);
lean_dec(v_x_3556_);
v_size_3565_ = lean_ctor_get(v_r_3560_, 0);
lean_inc(v_size_3565_);
v_k_3566_ = lean_ctor_get(v_r_3560_, 1);
lean_inc(v_k_3566_);
v_v_3567_ = lean_ctor_get(v_r_3560_, 2);
lean_inc(v_v_3567_);
v_l_3568_ = lean_ctor_get(v_r_3560_, 3);
lean_inc(v_l_3568_);
v_r_3569_ = lean_ctor_get(v_r_3560_, 4);
lean_inc(v_r_3569_);
lean_dec_ref_known(v_r_3560_, 5);
v___x_3570_ = lean_apply_10(v_h__2_3559_, v_size_3561_, v_k_3562_, v_v_3563_, v_l_3564_, v_size_3565_, v_k_3566_, v_v_3567_, v_l_3568_, v_r_3569_, lean_box(0));
return v___x_3570_;
}
else
{
lean_object* v_size_3571_; lean_object* v_k_3572_; lean_object* v_v_3573_; lean_object* v_l_3574_; lean_object* v___x_3575_; 
lean_dec(v_h__2_3559_);
v_size_3571_ = lean_ctor_get(v_x_3556_, 0);
lean_inc(v_size_3571_);
v_k_3572_ = lean_ctor_get(v_x_3556_, 1);
lean_inc(v_k_3572_);
v_v_3573_ = lean_ctor_get(v_x_3556_, 2);
lean_inc(v_v_3573_);
v_l_3574_ = lean_ctor_get(v_x_3556_, 3);
lean_inc(v_l_3574_);
lean_dec(v_x_3556_);
v___x_3575_ = lean_apply_5(v_h__1_3558_, v_size_3571_, v_k_3572_, v_v_3573_, v_l_3574_, lean_box(0));
return v___x_3575_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3577_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3578_ = lean_unsigned_to_nat(13u);
v___x_3579_ = lean_unsigned_to_nat(839u);
v___x_3580_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0));
v___x_3581_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3582_ = l_mkPanicMessageWithDecl(v___x_3581_, v___x_3580_, v___x_3579_, v___x_3578_, v___x_3577_);
return v___x_3582_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object* v_inst_3583_, lean_object* v_x_3584_){
_start:
{
if (lean_obj_tag(v_x_3584_) == 0)
{
lean_object* v_r_3585_; 
v_r_3585_ = lean_ctor_get(v_x_3584_, 4);
if (lean_obj_tag(v_r_3585_) == 0)
{
v_x_3584_ = v_r_3585_;
goto _start;
}
else
{
lean_object* v_k_3587_; lean_object* v_v_3588_; lean_object* v___x_3589_; 
v_k_3587_ = lean_ctor_get(v_x_3584_, 1);
v_v_3588_ = lean_ctor_get(v_x_3584_, 2);
lean_inc(v_v_3588_);
lean_inc(v_k_3587_);
v___x_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3589_, 0, v_k_3587_);
lean_ctor_set(v___x_3589_, 1, v_v_3588_);
return v___x_3589_;
}
}
else
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1);
v___x_3591_ = l_panic___redArg(v_inst_3583_, v___x_3590_);
return v___x_3591_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_3592_, lean_object* v_x_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3592_, v_x_3593_);
lean_dec(v_x_3593_);
lean_dec_ref(v_inst_3592_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(lean_object* v_00_u03b1_3595_, lean_object* v_00_u03b2_3596_, lean_object* v_inst_3597_, lean_object* v_x_3598_){
_start:
{
lean_object* v___x_3599_; 
v___x_3599_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3597_, v_x_3598_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_3600_, lean_object* v_00_u03b2_3601_, lean_object* v_inst_3602_, lean_object* v_x_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(v_00_u03b1_3600_, v_00_u03b2_3601_, v_inst_3602_, v_x_3603_);
lean_dec(v_x_3603_);
lean_dec_ref(v_inst_3602_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object* v_x_3605_, lean_object* v_x_3606_){
_start:
{
if (lean_obj_tag(v_x_3605_) == 0)
{
lean_object* v_r_3607_; 
v_r_3607_ = lean_ctor_get(v_x_3605_, 4);
if (lean_obj_tag(v_r_3607_) == 0)
{
v_x_3605_ = v_r_3607_;
goto _start;
}
else
{
lean_object* v_k_3609_; lean_object* v_v_3610_; lean_object* v___x_3611_; 
v_k_3609_ = lean_ctor_get(v_x_3605_, 1);
v_v_3610_ = lean_ctor_get(v_x_3605_, 2);
lean_inc(v_v_3610_);
lean_inc(v_k_3609_);
v___x_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3611_, 0, v_k_3609_);
lean_ctor_set(v___x_3611_, 1, v_v_3610_);
return v___x_3611_;
}
}
else
{
lean_inc_ref(v_x_3606_);
return v_x_3606_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg___boxed(lean_object* v_x_3612_, lean_object* v_x_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3612_, v_x_3613_);
lean_dec_ref(v_x_3613_);
lean_dec(v_x_3612_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(lean_object* v_00_u03b1_3615_, lean_object* v_00_u03b2_3616_, lean_object* v_x_3617_, lean_object* v_x_3618_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3617_, v_x_3618_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___boxed(lean_object* v_00_u03b1_3620_, lean_object* v_00_u03b2_3621_, lean_object* v_x_3622_, lean_object* v_x_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(v_00_u03b1_3620_, v_00_u03b2_3621_, v_x_3622_, v_x_3623_);
lean_dec_ref(v_x_3623_);
lean_dec(v_x_3622_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_3625_, lean_object* v_x_3626_, lean_object* v_h__1_3627_, lean_object* v_h__2_3628_, lean_object* v_h__3_3629_){
_start:
{
if (lean_obj_tag(v_x_3625_) == 0)
{
lean_object* v_r_3630_; 
lean_dec(v_h__1_3627_);
v_r_3630_ = lean_ctor_get(v_x_3625_, 4);
if (lean_obj_tag(v_r_3630_) == 0)
{
lean_object* v_size_3631_; lean_object* v_k_3632_; lean_object* v_v_3633_; lean_object* v_l_3634_; lean_object* v_size_3635_; lean_object* v_k_3636_; lean_object* v_v_3637_; lean_object* v_l_3638_; lean_object* v_r_3639_; lean_object* v___x_3640_; 
lean_inc_ref(v_r_3630_);
lean_dec(v_h__2_3628_);
v_size_3631_ = lean_ctor_get(v_x_3625_, 0);
lean_inc(v_size_3631_);
v_k_3632_ = lean_ctor_get(v_x_3625_, 1);
lean_inc(v_k_3632_);
v_v_3633_ = lean_ctor_get(v_x_3625_, 2);
lean_inc(v_v_3633_);
v_l_3634_ = lean_ctor_get(v_x_3625_, 3);
lean_inc(v_l_3634_);
lean_dec_ref_known(v_x_3625_, 5);
v_size_3635_ = lean_ctor_get(v_r_3630_, 0);
lean_inc(v_size_3635_);
v_k_3636_ = lean_ctor_get(v_r_3630_, 1);
lean_inc(v_k_3636_);
v_v_3637_ = lean_ctor_get(v_r_3630_, 2);
lean_inc(v_v_3637_);
v_l_3638_ = lean_ctor_get(v_r_3630_, 3);
lean_inc(v_l_3638_);
v_r_3639_ = lean_ctor_get(v_r_3630_, 4);
lean_inc(v_r_3639_);
lean_dec_ref_known(v_r_3630_, 5);
v___x_3640_ = lean_apply_10(v_h__3_3629_, v_size_3631_, v_k_3632_, v_v_3633_, v_l_3634_, v_size_3635_, v_k_3636_, v_v_3637_, v_l_3638_, v_r_3639_, v_x_3626_);
return v___x_3640_;
}
else
{
lean_object* v_size_3641_; lean_object* v_k_3642_; lean_object* v_v_3643_; lean_object* v_l_3644_; lean_object* v___x_3645_; 
lean_dec(v_h__3_3629_);
v_size_3641_ = lean_ctor_get(v_x_3625_, 0);
lean_inc(v_size_3641_);
v_k_3642_ = lean_ctor_get(v_x_3625_, 1);
lean_inc(v_k_3642_);
v_v_3643_ = lean_ctor_get(v_x_3625_, 2);
lean_inc(v_v_3643_);
v_l_3644_ = lean_ctor_get(v_x_3625_, 3);
lean_inc(v_l_3644_);
lean_dec_ref_known(v_x_3625_, 5);
v___x_3645_ = lean_apply_5(v_h__2_3628_, v_size_3641_, v_k_3642_, v_v_3643_, v_l_3644_, v_x_3626_);
return v___x_3645_;
}
}
else
{
lean_object* v___x_3646_; 
lean_dec(v_h__3_3629_);
lean_dec(v_h__2_3628_);
v___x_3646_ = lean_apply_1(v_h__1_3627_, v_x_3626_);
return v___x_3646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_3647_, lean_object* v_00_u03b2_3648_, lean_object* v_motive_3649_, lean_object* v_x_3650_, lean_object* v_x_3651_, lean_object* v_h__1_3652_, lean_object* v_h__2_3653_, lean_object* v_h__3_3654_){
_start:
{
if (lean_obj_tag(v_x_3650_) == 0)
{
lean_object* v_r_3655_; 
lean_dec(v_h__1_3652_);
v_r_3655_ = lean_ctor_get(v_x_3650_, 4);
if (lean_obj_tag(v_r_3655_) == 0)
{
lean_object* v_size_3656_; lean_object* v_k_3657_; lean_object* v_v_3658_; lean_object* v_l_3659_; lean_object* v_size_3660_; lean_object* v_k_3661_; lean_object* v_v_3662_; lean_object* v_l_3663_; lean_object* v_r_3664_; lean_object* v___x_3665_; 
lean_inc_ref(v_r_3655_);
lean_dec(v_h__2_3653_);
v_size_3656_ = lean_ctor_get(v_x_3650_, 0);
lean_inc(v_size_3656_);
v_k_3657_ = lean_ctor_get(v_x_3650_, 1);
lean_inc(v_k_3657_);
v_v_3658_ = lean_ctor_get(v_x_3650_, 2);
lean_inc(v_v_3658_);
v_l_3659_ = lean_ctor_get(v_x_3650_, 3);
lean_inc(v_l_3659_);
lean_dec_ref_known(v_x_3650_, 5);
v_size_3660_ = lean_ctor_get(v_r_3655_, 0);
lean_inc(v_size_3660_);
v_k_3661_ = lean_ctor_get(v_r_3655_, 1);
lean_inc(v_k_3661_);
v_v_3662_ = lean_ctor_get(v_r_3655_, 2);
lean_inc(v_v_3662_);
v_l_3663_ = lean_ctor_get(v_r_3655_, 3);
lean_inc(v_l_3663_);
v_r_3664_ = lean_ctor_get(v_r_3655_, 4);
lean_inc(v_r_3664_);
lean_dec_ref_known(v_r_3655_, 5);
v___x_3665_ = lean_apply_10(v_h__3_3654_, v_size_3656_, v_k_3657_, v_v_3658_, v_l_3659_, v_size_3660_, v_k_3661_, v_v_3662_, v_l_3663_, v_r_3664_, v_x_3651_);
return v___x_3665_;
}
else
{
lean_object* v_size_3666_; lean_object* v_k_3667_; lean_object* v_v_3668_; lean_object* v_l_3669_; lean_object* v___x_3670_; 
lean_dec(v_h__3_3654_);
v_size_3666_ = lean_ctor_get(v_x_3650_, 0);
lean_inc(v_size_3666_);
v_k_3667_ = lean_ctor_get(v_x_3650_, 1);
lean_inc(v_k_3667_);
v_v_3668_ = lean_ctor_get(v_x_3650_, 2);
lean_inc(v_v_3668_);
v_l_3669_ = lean_ctor_get(v_x_3650_, 3);
lean_inc(v_l_3669_);
lean_dec_ref_known(v_x_3650_, 5);
v___x_3670_ = lean_apply_5(v_h__2_3653_, v_size_3666_, v_k_3667_, v_v_3668_, v_l_3669_, v_x_3651_);
return v___x_3670_;
}
}
else
{
lean_object* v___x_3671_; 
lean_dec(v_h__3_3654_);
lean_dec(v_h__2_3653_);
v___x_3671_ = lean_apply_1(v_h__1_3652_, v_x_3651_);
return v___x_3671_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object* v_x_3672_, lean_object* v_x_3673_){
_start:
{
lean_object* v_k_3674_; lean_object* v_v_3675_; lean_object* v_l_3676_; lean_object* v_r_3677_; lean_object* v___y_3679_; lean_object* v___y_3685_; 
v_k_3674_ = lean_ctor_get(v_x_3672_, 1);
v_v_3675_ = lean_ctor_get(v_x_3672_, 2);
v_l_3676_ = lean_ctor_get(v_x_3672_, 3);
v_r_3677_ = lean_ctor_get(v_x_3672_, 4);
if (lean_obj_tag(v_l_3676_) == 0)
{
lean_object* v_size_3692_; 
v_size_3692_ = lean_ctor_get(v_l_3676_, 0);
v___y_3685_ = v_size_3692_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3693_; 
v___x_3693_ = lean_unsigned_to_nat(0u);
v___y_3685_ = v___x_3693_;
goto v___jp_3684_;
}
v___jp_3678_:
{
lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3680_ = lean_nat_sub(v_x_3673_, v___y_3679_);
lean_dec(v_x_3673_);
v___x_3681_ = lean_unsigned_to_nat(1u);
v___x_3682_ = lean_nat_sub(v___x_3680_, v___x_3681_);
lean_dec(v___x_3680_);
v_x_3672_ = v_r_3677_;
v_x_3673_ = v___x_3682_;
goto _start;
}
v___jp_3684_:
{
uint8_t v___x_3686_; 
v___x_3686_ = lean_nat_dec_lt(v_x_3673_, v___y_3685_);
if (v___x_3686_ == 0)
{
uint8_t v___x_3687_; 
v___x_3687_ = lean_nat_dec_eq(v_x_3673_, v___y_3685_);
if (v___x_3687_ == 0)
{
if (lean_obj_tag(v_l_3676_) == 0)
{
lean_object* v_size_3688_; 
v_size_3688_ = lean_ctor_get(v_l_3676_, 0);
v___y_3679_ = v_size_3688_;
goto v___jp_3678_;
}
else
{
lean_object* v___x_3689_; 
v___x_3689_ = lean_unsigned_to_nat(0u);
v___y_3679_ = v___x_3689_;
goto v___jp_3678_;
}
}
else
{
lean_object* v___x_3690_; 
lean_dec(v_x_3673_);
lean_inc(v_v_3675_);
lean_inc(v_k_3674_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v_k_3674_);
lean_ctor_set(v___x_3690_, 1, v_v_3675_);
return v___x_3690_;
}
}
else
{
v_x_3672_ = v_l_3676_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg___boxed(lean_object* v_x_3694_, lean_object* v_x_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3694_, v_x_3695_);
lean_dec(v_x_3694_);
return v_res_3696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_object* v_00_u03b1_3697_, lean_object* v_00_u03b2_3698_, lean_object* v_x_3699_, lean_object* v_x_3700_, lean_object* v_x_3701_, lean_object* v_x_3702_){
_start:
{
lean_object* v___x_3703_; 
v___x_3703_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3699_, v_x_3701_);
return v___x_3703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_3704_, lean_object* v_00_u03b2_3705_, lean_object* v_x_3706_, lean_object* v_x_3707_, lean_object* v_x_3708_, lean_object* v_x_3709_){
_start:
{
lean_object* v_res_3710_; 
v_res_3710_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(v_00_u03b1_3704_, v_00_u03b2_3705_, v_x_3706_, v_x_3707_, v_x_3708_, v_x_3709_);
lean_dec(v_x_3706_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object* v_x_3711_, lean_object* v_x_3712_){
_start:
{
if (lean_obj_tag(v_x_3711_) == 0)
{
lean_object* v_k_3713_; lean_object* v_v_3714_; lean_object* v_l_3715_; lean_object* v_r_3716_; lean_object* v___y_3718_; lean_object* v___y_3724_; 
v_k_3713_ = lean_ctor_get(v_x_3711_, 1);
v_v_3714_ = lean_ctor_get(v_x_3711_, 2);
v_l_3715_ = lean_ctor_get(v_x_3711_, 3);
v_r_3716_ = lean_ctor_get(v_x_3711_, 4);
if (lean_obj_tag(v_l_3715_) == 0)
{
lean_object* v_size_3732_; 
v_size_3732_ = lean_ctor_get(v_l_3715_, 0);
v___y_3724_ = v_size_3732_;
goto v___jp_3723_;
}
else
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_unsigned_to_nat(0u);
v___y_3724_ = v___x_3733_;
goto v___jp_3723_;
}
v___jp_3717_:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3719_ = lean_nat_sub(v_x_3712_, v___y_3718_);
lean_dec(v_x_3712_);
v___x_3720_ = lean_unsigned_to_nat(1u);
v___x_3721_ = lean_nat_sub(v___x_3719_, v___x_3720_);
lean_dec(v___x_3719_);
v_x_3711_ = v_r_3716_;
v_x_3712_ = v___x_3721_;
goto _start;
}
v___jp_3723_:
{
uint8_t v___x_3725_; 
v___x_3725_ = lean_nat_dec_lt(v_x_3712_, v___y_3724_);
if (v___x_3725_ == 0)
{
uint8_t v___x_3726_; 
v___x_3726_ = lean_nat_dec_eq(v_x_3712_, v___y_3724_);
if (v___x_3726_ == 0)
{
if (lean_obj_tag(v_l_3715_) == 0)
{
lean_object* v_size_3727_; 
v_size_3727_ = lean_ctor_get(v_l_3715_, 0);
v___y_3718_ = v_size_3727_;
goto v___jp_3717_;
}
else
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_unsigned_to_nat(0u);
v___y_3718_ = v___x_3728_;
goto v___jp_3717_;
}
}
else
{
lean_object* v___x_3729_; lean_object* v___x_3730_; 
lean_dec(v_x_3712_);
lean_inc(v_v_3714_);
lean_inc(v_k_3713_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v_k_3713_);
lean_ctor_set(v___x_3729_, 1, v_v_3714_);
v___x_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3729_);
return v___x_3730_;
}
}
else
{
v_x_3711_ = v_l_3715_;
goto _start;
}
}
}
else
{
lean_object* v___x_3734_; 
lean_dec(v_x_3712_);
v___x_3734_ = lean_box(0);
return v___x_3734_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_3735_, lean_object* v_x_3736_){
_start:
{
lean_object* v_res_3737_; 
v_res_3737_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3735_, v_x_3736_);
lean_dec(v_x_3735_);
return v_res_3737_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_3738_, lean_object* v_00_u03b2_3739_, lean_object* v_x_3740_, lean_object* v_x_3741_){
_start:
{
lean_object* v___x_3742_; 
v___x_3742_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3740_, v_x_3741_);
return v___x_3742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_3743_, lean_object* v_00_u03b2_3744_, lean_object* v_x_3745_, lean_object* v_x_3746_){
_start:
{
lean_object* v_res_3747_; 
v_res_3747_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(v_00_u03b1_3743_, v_00_u03b2_3744_, v_x_3745_, v_x_3746_);
lean_dec(v_x_3745_);
return v_res_3747_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v___x_3749_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_3750_ = lean_unsigned_to_nat(16u);
v___x_3751_ = lean_unsigned_to_nat(870u);
v___x_3752_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0));
v___x_3753_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3754_ = l_mkPanicMessageWithDecl(v___x_3753_, v___x_3752_, v___x_3751_, v___x_3750_, v___x_3749_);
return v___x_3754_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object* v_inst_3755_, lean_object* v_x_3756_, lean_object* v_x_3757_){
_start:
{
if (lean_obj_tag(v_x_3756_) == 0)
{
lean_object* v_k_3758_; lean_object* v_v_3759_; lean_object* v_l_3760_; lean_object* v_r_3761_; lean_object* v___y_3763_; lean_object* v___y_3769_; 
v_k_3758_ = lean_ctor_get(v_x_3756_, 1);
v_v_3759_ = lean_ctor_get(v_x_3756_, 2);
v_l_3760_ = lean_ctor_get(v_x_3756_, 3);
v_r_3761_ = lean_ctor_get(v_x_3756_, 4);
if (lean_obj_tag(v_l_3760_) == 0)
{
lean_object* v_size_3776_; 
v_size_3776_ = lean_ctor_get(v_l_3760_, 0);
v___y_3769_ = v_size_3776_;
goto v___jp_3768_;
}
else
{
lean_object* v___x_3777_; 
v___x_3777_ = lean_unsigned_to_nat(0u);
v___y_3769_ = v___x_3777_;
goto v___jp_3768_;
}
v___jp_3762_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3764_ = lean_nat_sub(v_x_3757_, v___y_3763_);
lean_dec(v_x_3757_);
v___x_3765_ = lean_unsigned_to_nat(1u);
v___x_3766_ = lean_nat_sub(v___x_3764_, v___x_3765_);
lean_dec(v___x_3764_);
v_x_3756_ = v_r_3761_;
v_x_3757_ = v___x_3766_;
goto _start;
}
v___jp_3768_:
{
uint8_t v___x_3770_; 
v___x_3770_ = lean_nat_dec_lt(v_x_3757_, v___y_3769_);
if (v___x_3770_ == 0)
{
uint8_t v___x_3771_; 
v___x_3771_ = lean_nat_dec_eq(v_x_3757_, v___y_3769_);
if (v___x_3771_ == 0)
{
if (lean_obj_tag(v_l_3760_) == 0)
{
lean_object* v_size_3772_; 
v_size_3772_ = lean_ctor_get(v_l_3760_, 0);
v___y_3763_ = v_size_3772_;
goto v___jp_3762_;
}
else
{
lean_object* v___x_3773_; 
v___x_3773_ = lean_unsigned_to_nat(0u);
v___y_3763_ = v___x_3773_;
goto v___jp_3762_;
}
}
else
{
lean_object* v___x_3774_; 
lean_dec(v_x_3757_);
lean_inc(v_v_3759_);
lean_inc(v_k_3758_);
v___x_3774_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3774_, 0, v_k_3758_);
lean_ctor_set(v___x_3774_, 1, v_v_3759_);
return v___x_3774_;
}
}
else
{
v_x_3756_ = v_l_3760_;
goto _start;
}
}
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_dec(v_x_3757_);
v___x_3778_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1);
v___x_3779_ = l_panic___redArg(v_inst_3755_, v___x_3778_);
return v___x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_3780_, lean_object* v_x_3781_, lean_object* v_x_3782_){
_start:
{
lean_object* v_res_3783_; 
v_res_3783_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3780_, v_x_3781_, v_x_3782_);
lean_dec(v_x_3781_);
lean_dec_ref(v_inst_3780_);
return v_res_3783_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(lean_object* v_00_u03b1_3784_, lean_object* v_00_u03b2_3785_, lean_object* v_inst_3786_, lean_object* v_x_3787_, lean_object* v_x_3788_){
_start:
{
lean_object* v___x_3789_; 
v___x_3789_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3786_, v_x_3787_, v_x_3788_);
return v___x_3789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_3790_, lean_object* v_00_u03b2_3791_, lean_object* v_inst_3792_, lean_object* v_x_3793_, lean_object* v_x_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(v_00_u03b1_3790_, v_00_u03b2_3791_, v_inst_3792_, v_x_3793_, v_x_3794_);
lean_dec(v_x_3793_);
lean_dec_ref(v_inst_3792_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object* v_x_3796_, lean_object* v_x_3797_, lean_object* v_x_3798_){
_start:
{
if (lean_obj_tag(v_x_3796_) == 0)
{
lean_object* v_k_3799_; lean_object* v_v_3800_; lean_object* v_l_3801_; lean_object* v_r_3802_; lean_object* v___y_3804_; lean_object* v___y_3810_; 
v_k_3799_ = lean_ctor_get(v_x_3796_, 1);
v_v_3800_ = lean_ctor_get(v_x_3796_, 2);
v_l_3801_ = lean_ctor_get(v_x_3796_, 3);
v_r_3802_ = lean_ctor_get(v_x_3796_, 4);
if (lean_obj_tag(v_l_3801_) == 0)
{
lean_object* v_size_3817_; 
v_size_3817_ = lean_ctor_get(v_l_3801_, 0);
v___y_3810_ = v_size_3817_;
goto v___jp_3809_;
}
else
{
lean_object* v___x_3818_; 
v___x_3818_ = lean_unsigned_to_nat(0u);
v___y_3810_ = v___x_3818_;
goto v___jp_3809_;
}
v___jp_3803_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3805_ = lean_nat_sub(v_x_3797_, v___y_3804_);
lean_dec(v_x_3797_);
v___x_3806_ = lean_unsigned_to_nat(1u);
v___x_3807_ = lean_nat_sub(v___x_3805_, v___x_3806_);
lean_dec(v___x_3805_);
v_x_3796_ = v_r_3802_;
v_x_3797_ = v___x_3807_;
goto _start;
}
v___jp_3809_:
{
uint8_t v___x_3811_; 
v___x_3811_ = lean_nat_dec_lt(v_x_3797_, v___y_3810_);
if (v___x_3811_ == 0)
{
uint8_t v___x_3812_; 
v___x_3812_ = lean_nat_dec_eq(v_x_3797_, v___y_3810_);
if (v___x_3812_ == 0)
{
if (lean_obj_tag(v_l_3801_) == 0)
{
lean_object* v_size_3813_; 
v_size_3813_ = lean_ctor_get(v_l_3801_, 0);
v___y_3804_ = v_size_3813_;
goto v___jp_3803_;
}
else
{
lean_object* v___x_3814_; 
v___x_3814_ = lean_unsigned_to_nat(0u);
v___y_3804_ = v___x_3814_;
goto v___jp_3803_;
}
}
else
{
lean_object* v___x_3815_; 
lean_dec(v_x_3797_);
lean_inc(v_v_3800_);
lean_inc(v_k_3799_);
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v_k_3799_);
lean_ctor_set(v___x_3815_, 1, v_v_3800_);
return v___x_3815_;
}
}
else
{
v_x_3796_ = v_l_3801_;
goto _start;
}
}
}
else
{
lean_dec(v_x_3797_);
lean_inc_ref(v_x_3798_);
return v_x_3798_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg___boxed(lean_object* v_x_3819_, lean_object* v_x_3820_, lean_object* v_x_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3819_, v_x_3820_, v_x_3821_);
lean_dec_ref(v_x_3821_);
lean_dec(v_x_3819_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(lean_object* v_00_u03b1_3823_, lean_object* v_00_u03b2_3824_, lean_object* v_x_3825_, lean_object* v_x_3826_, lean_object* v_x_3827_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3825_, v_x_3826_, v_x_3827_);
return v___x_3828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_3829_, lean_object* v_00_u03b2_3830_, lean_object* v_x_3831_, lean_object* v_x_3832_, lean_object* v_x_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(v_00_u03b1_3829_, v_00_u03b2_3830_, v_x_3831_, v_x_3832_, v_x_3833_);
lean_dec_ref(v_x_3833_);
lean_dec(v_x_3831_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object* v_inst_3835_, lean_object* v_k_3836_, lean_object* v_best_3837_, lean_object* v_a_3838_){
_start:
{
if (lean_obj_tag(v_a_3838_) == 0)
{
lean_object* v_k_3839_; lean_object* v_v_3840_; lean_object* v_l_3841_; lean_object* v_r_3842_; lean_object* v___x_3843_; uint8_t v___x_3844_; 
v_k_3839_ = lean_ctor_get(v_a_3838_, 1);
lean_inc_n(v_k_3839_, 2);
v_v_3840_ = lean_ctor_get(v_a_3838_, 2);
lean_inc(v_v_3840_);
v_l_3841_ = lean_ctor_get(v_a_3838_, 3);
lean_inc(v_l_3841_);
v_r_3842_ = lean_ctor_get(v_a_3838_, 4);
lean_inc(v_r_3842_);
lean_dec_ref_known(v_a_3838_, 5);
lean_inc_ref(v_inst_3835_);
lean_inc(v_k_3836_);
v___x_3843_ = lean_apply_2(v_inst_3835_, v_k_3836_, v_k_3839_);
v___x_3844_ = lean_unbox(v___x_3843_);
switch(v___x_3844_)
{
case 0:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
lean_dec(v_r_3842_);
lean_dec(v_best_3837_);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v_k_3839_);
lean_ctor_set(v___x_3845_, 1, v_v_3840_);
v___x_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
v_best_3837_ = v___x_3846_;
v_a_3838_ = v_l_3841_;
goto _start;
}
case 1:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
lean_dec(v_r_3842_);
lean_dec(v_l_3841_);
lean_dec(v_best_3837_);
lean_dec(v_k_3836_);
lean_dec_ref(v_inst_3835_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v_k_3839_);
lean_ctor_set(v___x_3848_, 1, v_v_3840_);
v___x_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
return v___x_3849_;
}
default: 
{
lean_dec(v_l_3841_);
lean_dec(v_v_3840_);
lean_dec(v_k_3839_);
v_a_3838_ = v_r_3842_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3836_);
lean_dec_ref(v_inst_3835_);
return v_best_3837_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(lean_object* v_00_u03b1_3851_, lean_object* v_00_u03b2_3852_, lean_object* v_inst_3853_, lean_object* v_k_3854_, lean_object* v_best_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3853_, v_k_3854_, v_best_3855_, v_a_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___redArg(lean_object* v_inst_3858_, lean_object* v_k_3859_, lean_object* v_a_3860_){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_box(0);
v___x_3862_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3858_, v_k_3859_, v___x_3861_, v_a_3860_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(lean_object* v_00_u03b1_3863_, lean_object* v_00_u03b2_3864_, lean_object* v_inst_3865_, lean_object* v_k_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_box(0);
v___x_3869_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3865_, v_k_3866_, v___x_3868_, v_a_3867_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object* v_inst_3870_, lean_object* v_k_3871_, lean_object* v_best_3872_, lean_object* v_a_3873_){
_start:
{
if (lean_obj_tag(v_a_3873_) == 0)
{
lean_object* v_k_3874_; lean_object* v_v_3875_; lean_object* v_l_3876_; lean_object* v_r_3877_; lean_object* v___x_3878_; uint8_t v___x_3879_; 
v_k_3874_ = lean_ctor_get(v_a_3873_, 1);
lean_inc_n(v_k_3874_, 2);
v_v_3875_ = lean_ctor_get(v_a_3873_, 2);
lean_inc(v_v_3875_);
v_l_3876_ = lean_ctor_get(v_a_3873_, 3);
lean_inc(v_l_3876_);
v_r_3877_ = lean_ctor_get(v_a_3873_, 4);
lean_inc(v_r_3877_);
lean_dec_ref_known(v_a_3873_, 5);
lean_inc_ref(v_inst_3870_);
lean_inc(v_k_3871_);
v___x_3878_ = lean_apply_2(v_inst_3870_, v_k_3871_, v_k_3874_);
v___x_3879_ = lean_unbox(v___x_3878_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; lean_object* v___x_3881_; 
lean_dec(v_r_3877_);
lean_dec(v_best_3872_);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v_k_3874_);
lean_ctor_set(v___x_3880_, 1, v_v_3875_);
v___x_3881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
v_best_3872_ = v___x_3881_;
v_a_3873_ = v_l_3876_;
goto _start;
}
else
{
lean_dec(v_l_3876_);
lean_dec(v_v_3875_);
lean_dec(v_k_3874_);
v_a_3873_ = v_r_3877_;
goto _start;
}
}
else
{
lean_dec(v_k_3871_);
lean_dec_ref(v_inst_3870_);
return v_best_3872_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(lean_object* v_00_u03b1_3884_, lean_object* v_00_u03b2_3885_, lean_object* v_inst_3886_, lean_object* v_k_3887_, lean_object* v_best_3888_, lean_object* v_a_3889_){
_start:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3886_, v_k_3887_, v_best_3888_, v_a_3889_);
return v___x_3890_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___redArg(lean_object* v_inst_3891_, lean_object* v_k_3892_, lean_object* v_a_3893_){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = lean_box(0);
v___x_3895_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3891_, v_k_3892_, v___x_3894_, v_a_3893_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(lean_object* v_00_u03b1_3896_, lean_object* v_00_u03b2_3897_, lean_object* v_inst_3898_, lean_object* v_k_3899_, lean_object* v_a_3900_){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_box(0);
v___x_3902_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3898_, v_k_3899_, v___x_3901_, v_a_3900_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object* v_inst_3903_, lean_object* v_k_3904_, lean_object* v_best_3905_, lean_object* v_a_3906_){
_start:
{
if (lean_obj_tag(v_a_3906_) == 0)
{
lean_object* v_k_3907_; lean_object* v_v_3908_; lean_object* v_l_3909_; lean_object* v_r_3910_; lean_object* v___x_3911_; uint8_t v___x_3912_; 
v_k_3907_ = lean_ctor_get(v_a_3906_, 1);
lean_inc_n(v_k_3907_, 2);
v_v_3908_ = lean_ctor_get(v_a_3906_, 2);
lean_inc(v_v_3908_);
v_l_3909_ = lean_ctor_get(v_a_3906_, 3);
lean_inc(v_l_3909_);
v_r_3910_ = lean_ctor_get(v_a_3906_, 4);
lean_inc(v_r_3910_);
lean_dec_ref_known(v_a_3906_, 5);
lean_inc_ref(v_inst_3903_);
lean_inc(v_k_3904_);
v___x_3911_ = lean_apply_2(v_inst_3903_, v_k_3904_, v_k_3907_);
v___x_3912_ = lean_unbox(v___x_3911_);
switch(v___x_3912_)
{
case 0:
{
lean_dec(v_r_3910_);
lean_dec(v_v_3908_);
lean_dec(v_k_3907_);
v_a_3906_ = v_l_3909_;
goto _start;
}
case 1:
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
lean_dec(v_r_3910_);
lean_dec(v_l_3909_);
lean_dec(v_best_3905_);
lean_dec(v_k_3904_);
lean_dec_ref(v_inst_3903_);
v___x_3914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3914_, 0, v_k_3907_);
lean_ctor_set(v___x_3914_, 1, v_v_3908_);
v___x_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
return v___x_3915_;
}
default: 
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
lean_dec(v_l_3909_);
lean_dec(v_best_3905_);
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v_k_3907_);
lean_ctor_set(v___x_3916_, 1, v_v_3908_);
v___x_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
v_best_3905_ = v___x_3917_;
v_a_3906_ = v_r_3910_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3904_);
lean_dec_ref(v_inst_3903_);
return v_best_3905_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(lean_object* v_00_u03b1_3919_, lean_object* v_00_u03b2_3920_, lean_object* v_inst_3921_, lean_object* v_k_3922_, lean_object* v_best_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3921_, v_k_3922_, v_best_3923_, v_a_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___redArg(lean_object* v_inst_3926_, lean_object* v_k_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = lean_box(0);
v___x_3930_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3926_, v_k_3927_, v___x_3929_, v_a_3928_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(lean_object* v_00_u03b1_3931_, lean_object* v_00_u03b2_3932_, lean_object* v_inst_3933_, lean_object* v_k_3934_, lean_object* v_a_3935_){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = lean_box(0);
v___x_3937_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3933_, v_k_3934_, v___x_3936_, v_a_3935_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object* v_inst_3938_, lean_object* v_k_3939_, lean_object* v_best_3940_, lean_object* v_a_3941_){
_start:
{
if (lean_obj_tag(v_a_3941_) == 0)
{
lean_object* v_k_3942_; lean_object* v_v_3943_; lean_object* v_l_3944_; lean_object* v_r_3945_; lean_object* v___x_3946_; uint8_t v___x_3947_; 
v_k_3942_ = lean_ctor_get(v_a_3941_, 1);
lean_inc_n(v_k_3942_, 2);
v_v_3943_ = lean_ctor_get(v_a_3941_, 2);
lean_inc(v_v_3943_);
v_l_3944_ = lean_ctor_get(v_a_3941_, 3);
lean_inc(v_l_3944_);
v_r_3945_ = lean_ctor_get(v_a_3941_, 4);
lean_inc(v_r_3945_);
lean_dec_ref_known(v_a_3941_, 5);
lean_inc_ref(v_inst_3938_);
lean_inc(v_k_3939_);
v___x_3946_ = lean_apply_2(v_inst_3938_, v_k_3939_, v_k_3942_);
v___x_3947_ = lean_unbox(v___x_3946_);
if (v___x_3947_ == 2)
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
lean_dec(v_l_3944_);
lean_dec(v_best_3940_);
v___x_3948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3948_, 0, v_k_3942_);
lean_ctor_set(v___x_3948_, 1, v_v_3943_);
v___x_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
v_best_3940_ = v___x_3949_;
v_a_3941_ = v_r_3945_;
goto _start;
}
else
{
lean_dec(v_r_3945_);
lean_dec(v_v_3943_);
lean_dec(v_k_3942_);
v_a_3941_ = v_l_3944_;
goto _start;
}
}
else
{
lean_dec(v_k_3939_);
lean_dec_ref(v_inst_3938_);
return v_best_3940_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(lean_object* v_00_u03b1_3952_, lean_object* v_00_u03b2_3953_, lean_object* v_inst_3954_, lean_object* v_k_3955_, lean_object* v_best_3956_, lean_object* v_a_3957_){
_start:
{
lean_object* v___x_3958_; 
v___x_3958_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3954_, v_k_3955_, v_best_3956_, v_a_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___redArg(lean_object* v_inst_3959_, lean_object* v_k_3960_, lean_object* v_a_3961_){
_start:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
v___x_3962_ = lean_box(0);
v___x_3963_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3959_, v_k_3960_, v___x_3962_, v_a_3961_);
return v___x_3963_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(lean_object* v_00_u03b1_3964_, lean_object* v_00_u03b2_3965_, lean_object* v_inst_3966_, lean_object* v_k_3967_, lean_object* v_a_3968_){
_start:
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = lean_box(0);
v___x_3970_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3966_, v_k_3967_, v___x_3969_, v_a_3968_);
return v___x_3970_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(lean_object* v_inst_3971_, lean_object* v_inst_3972_, lean_object* v_k_3973_, lean_object* v_t_3974_){
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
lean_dec_ref_known(v___x_3976_, 1);
return v_val_3979_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg___boxed(lean_object* v_inst_3980_, lean_object* v_inst_3981_, lean_object* v_k_3982_, lean_object* v_t_3983_){
_start:
{
lean_object* v_res_3984_; 
v_res_3984_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(v_inst_3980_, v_inst_3981_, v_k_3982_, v_t_3983_);
lean_dec_ref(v_inst_3981_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object* v_00_u03b1_3985_, lean_object* v_00_u03b2_3986_, lean_object* v_inst_3987_, lean_object* v_inst_3988_, lean_object* v_k_3989_, lean_object* v_t_3990_){
_start:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3991_ = lean_box(0);
v___x_3992_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3987_, v_k_3989_, v___x_3991_, v_t_3990_);
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
lean_dec_ref_known(v___x_3992_, 1);
return v_val_3995_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_3996_, lean_object* v_00_u03b2_3997_, lean_object* v_inst_3998_, lean_object* v_inst_3999_, lean_object* v_k_4000_, lean_object* v_t_4001_){
_start:
{
lean_object* v_res_4002_; 
v_res_4002_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(v_00_u03b1_3996_, v_00_u03b2_3997_, v_inst_3998_, v_inst_3999_, v_k_4000_, v_t_4001_);
lean_dec_ref(v_inst_3999_);
return v_res_4002_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(lean_object* v_inst_4003_, lean_object* v_inst_4004_, lean_object* v_k_4005_, lean_object* v_t_4006_){
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
lean_dec_ref_known(v___x_4008_, 1);
return v_val_4011_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg___boxed(lean_object* v_inst_4012_, lean_object* v_inst_4013_, lean_object* v_k_4014_, lean_object* v_t_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(v_inst_4012_, v_inst_4013_, v_k_4014_, v_t_4015_);
lean_dec_ref(v_inst_4013_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object* v_00_u03b1_4017_, lean_object* v_00_u03b2_4018_, lean_object* v_inst_4019_, lean_object* v_inst_4020_, lean_object* v_k_4021_, lean_object* v_t_4022_){
_start:
{
lean_object* v___x_4023_; lean_object* v___x_4024_; 
v___x_4023_ = lean_box(0);
v___x_4024_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4019_, v_k_4021_, v___x_4023_, v_t_4022_);
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
lean_dec_ref_known(v___x_4024_, 1);
return v_val_4027_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_4028_, lean_object* v_00_u03b2_4029_, lean_object* v_inst_4030_, lean_object* v_inst_4031_, lean_object* v_k_4032_, lean_object* v_t_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(v_00_u03b1_4028_, v_00_u03b2_4029_, v_inst_4030_, v_inst_4031_, v_k_4032_, v_t_4033_);
lean_dec_ref(v_inst_4031_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(lean_object* v_inst_4035_, lean_object* v_inst_4036_, lean_object* v_k_4037_, lean_object* v_t_4038_){
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
lean_dec_ref_known(v___x_4040_, 1);
return v_val_4043_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg___boxed(lean_object* v_inst_4044_, lean_object* v_inst_4045_, lean_object* v_k_4046_, lean_object* v_t_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(v_inst_4044_, v_inst_4045_, v_k_4046_, v_t_4047_);
lean_dec_ref(v_inst_4045_);
return v_res_4048_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object* v_00_u03b1_4049_, lean_object* v_00_u03b2_4050_, lean_object* v_inst_4051_, lean_object* v_inst_4052_, lean_object* v_k_4053_, lean_object* v_t_4054_){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = lean_box(0);
v___x_4056_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4051_, v_k_4053_, v___x_4055_, v_t_4054_);
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
lean_dec_ref_known(v___x_4056_, 1);
return v_val_4059_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_4060_, lean_object* v_00_u03b2_4061_, lean_object* v_inst_4062_, lean_object* v_inst_4063_, lean_object* v_k_4064_, lean_object* v_t_4065_){
_start:
{
lean_object* v_res_4066_; 
v_res_4066_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(v_00_u03b1_4060_, v_00_u03b2_4061_, v_inst_4062_, v_inst_4063_, v_k_4064_, v_t_4065_);
lean_dec_ref(v_inst_4063_);
return v_res_4066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(lean_object* v_inst_4067_, lean_object* v_inst_4068_, lean_object* v_k_4069_, lean_object* v_t_4070_){
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
lean_dec_ref_known(v___x_4072_, 1);
return v_val_4075_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg___boxed(lean_object* v_inst_4076_, lean_object* v_inst_4077_, lean_object* v_k_4078_, lean_object* v_t_4079_){
_start:
{
lean_object* v_res_4080_; 
v_res_4080_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(v_inst_4076_, v_inst_4077_, v_k_4078_, v_t_4079_);
lean_dec_ref(v_inst_4077_);
return v_res_4080_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object* v_00_u03b1_4081_, lean_object* v_00_u03b2_4082_, lean_object* v_inst_4083_, lean_object* v_inst_4084_, lean_object* v_k_4085_, lean_object* v_t_4086_){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = lean_box(0);
v___x_4088_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4083_, v_k_4085_, v___x_4087_, v_t_4086_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4089_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4090_ = l_panic___redArg(v_inst_4084_, v___x_4089_);
return v___x_4090_;
}
else
{
lean_object* v_val_4091_; 
v_val_4091_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_val_4091_);
lean_dec_ref_known(v___x_4088_, 1);
return v_val_4091_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_4092_, lean_object* v_00_u03b2_4093_, lean_object* v_inst_4094_, lean_object* v_inst_4095_, lean_object* v_k_4096_, lean_object* v_t_4097_){
_start:
{
lean_object* v_res_4098_; 
v_res_4098_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(v_00_u03b1_4092_, v_00_u03b2_4093_, v_inst_4094_, v_inst_4095_, v_k_4096_, v_t_4097_);
lean_dec_ref(v_inst_4095_);
return v_res_4098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(lean_object* v_inst_4099_, lean_object* v_k_4100_, lean_object* v_t_4101_, lean_object* v_fallback_4102_){
_start:
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4103_ = lean_box(0);
v___x_4104_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4099_, v_k_4100_, v___x_4103_, v_t_4101_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_inc_ref(v_fallback_4102_);
return v_fallback_4102_;
}
else
{
lean_object* v_val_4105_; 
v_val_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_val_4105_);
lean_dec_ref_known(v___x_4104_, 1);
return v_val_4105_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg___boxed(lean_object* v_inst_4106_, lean_object* v_k_4107_, lean_object* v_t_4108_, lean_object* v_fallback_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(v_inst_4106_, v_k_4107_, v_t_4108_, v_fallback_4109_);
lean_dec_ref(v_fallback_4109_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(lean_object* v_00_u03b1_4111_, lean_object* v_00_u03b2_4112_, lean_object* v_inst_4113_, lean_object* v_k_4114_, lean_object* v_t_4115_, lean_object* v_fallback_4116_){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
v___x_4117_ = lean_box(0);
v___x_4118_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4113_, v_k_4114_, v___x_4117_, v_t_4115_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_inc_ref(v_fallback_4116_);
return v_fallback_4116_;
}
else
{
lean_object* v_val_4119_; 
v_val_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_val_4119_);
lean_dec_ref_known(v___x_4118_, 1);
return v_val_4119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___boxed(lean_object* v_00_u03b1_4120_, lean_object* v_00_u03b2_4121_, lean_object* v_inst_4122_, lean_object* v_k_4123_, lean_object* v_t_4124_, lean_object* v_fallback_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(v_00_u03b1_4120_, v_00_u03b2_4121_, v_inst_4122_, v_k_4123_, v_t_4124_, v_fallback_4125_);
lean_dec_ref(v_fallback_4125_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(lean_object* v_inst_4127_, lean_object* v_k_4128_, lean_object* v_t_4129_, lean_object* v_fallback_4130_){
_start:
{
lean_object* v___x_4131_; lean_object* v___x_4132_; 
v___x_4131_ = lean_box(0);
v___x_4132_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4127_, v_k_4128_, v___x_4131_, v_t_4129_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_inc_ref(v_fallback_4130_);
return v_fallback_4130_;
}
else
{
lean_object* v_val_4133_; 
v_val_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc(v_val_4133_);
lean_dec_ref_known(v___x_4132_, 1);
return v_val_4133_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg___boxed(lean_object* v_inst_4134_, lean_object* v_k_4135_, lean_object* v_t_4136_, lean_object* v_fallback_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(v_inst_4134_, v_k_4135_, v_t_4136_, v_fallback_4137_);
lean_dec_ref(v_fallback_4137_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(lean_object* v_00_u03b1_4139_, lean_object* v_00_u03b2_4140_, lean_object* v_inst_4141_, lean_object* v_k_4142_, lean_object* v_t_4143_, lean_object* v_fallback_4144_){
_start:
{
lean_object* v___x_4145_; lean_object* v___x_4146_; 
v___x_4145_ = lean_box(0);
v___x_4146_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4141_, v_k_4142_, v___x_4145_, v_t_4143_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_inc_ref(v_fallback_4144_);
return v_fallback_4144_;
}
else
{
lean_object* v_val_4147_; 
v_val_4147_ = lean_ctor_get(v___x_4146_, 0);
lean_inc(v_val_4147_);
lean_dec_ref_known(v___x_4146_, 1);
return v_val_4147_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_4148_, lean_object* v_00_u03b2_4149_, lean_object* v_inst_4150_, lean_object* v_k_4151_, lean_object* v_t_4152_, lean_object* v_fallback_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(v_00_u03b1_4148_, v_00_u03b2_4149_, v_inst_4150_, v_k_4151_, v_t_4152_, v_fallback_4153_);
lean_dec_ref(v_fallback_4153_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(lean_object* v_inst_4155_, lean_object* v_k_4156_, lean_object* v_t_4157_, lean_object* v_fallback_4158_){
_start:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4159_ = lean_box(0);
v___x_4160_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4155_, v_k_4156_, v___x_4159_, v_t_4157_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_inc_ref(v_fallback_4158_);
return v_fallback_4158_;
}
else
{
lean_object* v_val_4161_; 
v_val_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_val_4161_);
lean_dec_ref_known(v___x_4160_, 1);
return v_val_4161_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg___boxed(lean_object* v_inst_4162_, lean_object* v_k_4163_, lean_object* v_t_4164_, lean_object* v_fallback_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(v_inst_4162_, v_k_4163_, v_t_4164_, v_fallback_4165_);
lean_dec_ref(v_fallback_4165_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(lean_object* v_00_u03b1_4167_, lean_object* v_00_u03b2_4168_, lean_object* v_inst_4169_, lean_object* v_k_4170_, lean_object* v_t_4171_, lean_object* v_fallback_4172_){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_box(0);
v___x_4174_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4169_, v_k_4170_, v___x_4173_, v_t_4171_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_inc_ref(v_fallback_4172_);
return v_fallback_4172_;
}
else
{
lean_object* v_val_4175_; 
v_val_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc(v_val_4175_);
lean_dec_ref_known(v___x_4174_, 1);
return v_val_4175_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___boxed(lean_object* v_00_u03b1_4176_, lean_object* v_00_u03b2_4177_, lean_object* v_inst_4178_, lean_object* v_k_4179_, lean_object* v_t_4180_, lean_object* v_fallback_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(v_00_u03b1_4176_, v_00_u03b2_4177_, v_inst_4178_, v_k_4179_, v_t_4180_, v_fallback_4181_);
lean_dec_ref(v_fallback_4181_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(lean_object* v_inst_4183_, lean_object* v_k_4184_, lean_object* v_t_4185_, lean_object* v_fallback_4186_){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = lean_box(0);
v___x_4188_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4183_, v_k_4184_, v___x_4187_, v_t_4185_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_inc_ref(v_fallback_4186_);
return v_fallback_4186_;
}
else
{
lean_object* v_val_4189_; 
v_val_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_val_4189_);
lean_dec_ref_known(v___x_4188_, 1);
return v_val_4189_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg___boxed(lean_object* v_inst_4190_, lean_object* v_k_4191_, lean_object* v_t_4192_, lean_object* v_fallback_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(v_inst_4190_, v_k_4191_, v_t_4192_, v_fallback_4193_);
lean_dec_ref(v_fallback_4193_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(lean_object* v_00_u03b1_4195_, lean_object* v_00_u03b2_4196_, lean_object* v_inst_4197_, lean_object* v_k_4198_, lean_object* v_t_4199_, lean_object* v_fallback_4200_){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = lean_box(0);
v___x_4202_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4197_, v_k_4198_, v___x_4201_, v_t_4199_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_inc_ref(v_fallback_4200_);
return v_fallback_4200_;
}
else
{
lean_object* v_val_4203_; 
v_val_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_val_4203_);
lean_dec_ref_known(v___x_4202_, 1);
return v_val_4203_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_4204_, lean_object* v_00_u03b2_4205_, lean_object* v_inst_4206_, lean_object* v_k_4207_, lean_object* v_t_4208_, lean_object* v_fallback_4209_){
_start:
{
lean_object* v_res_4210_; 
v_res_4210_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(v_00_u03b1_4204_, v_00_u03b2_4205_, v_inst_4206_, v_k_4207_, v_t_4208_, v_fallback_4209_);
lean_dec_ref(v_fallback_4209_);
return v_res_4210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object* v_inst_4211_, lean_object* v_k_4212_, lean_object* v_x_4213_){
_start:
{
lean_object* v_k_4214_; lean_object* v_v_4215_; lean_object* v_l_4216_; lean_object* v_r_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; 
v_k_4214_ = lean_ctor_get(v_x_4213_, 1);
lean_inc_n(v_k_4214_, 2);
v_v_4215_ = lean_ctor_get(v_x_4213_, 2);
lean_inc(v_v_4215_);
v_l_4216_ = lean_ctor_get(v_x_4213_, 3);
lean_inc(v_l_4216_);
v_r_4217_ = lean_ctor_get(v_x_4213_, 4);
lean_inc(v_r_4217_);
lean_dec(v_x_4213_);
lean_inc_ref(v_inst_4211_);
lean_inc(v_k_4212_);
v___x_4218_ = lean_apply_2(v_inst_4211_, v_k_4212_, v_k_4214_);
v___x_4219_ = lean_unbox(v___x_4218_);
switch(v___x_4219_)
{
case 0:
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
lean_dec(v_r_4217_);
v___x_4220_ = lean_box(0);
v___x_4221_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4211_, v_k_4212_, v___x_4220_, v_l_4216_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v___x_4222_; 
v___x_4222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4222_, 0, v_k_4214_);
lean_ctor_set(v___x_4222_, 1, v_v_4215_);
return v___x_4222_;
}
else
{
lean_object* v_val_4223_; 
lean_dec(v_v_4215_);
lean_dec(v_k_4214_);
v_val_4223_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_val_4223_);
lean_dec_ref_known(v___x_4221_, 1);
return v_val_4223_;
}
}
case 1:
{
lean_object* v___x_4224_; 
lean_dec(v_r_4217_);
lean_dec(v_l_4216_);
lean_dec(v_k_4212_);
lean_dec_ref(v_inst_4211_);
v___x_4224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4224_, 0, v_k_4214_);
lean_ctor_set(v___x_4224_, 1, v_v_4215_);
return v___x_4224_;
}
default: 
{
lean_dec(v_l_4216_);
lean_dec(v_v_4215_);
lean_dec(v_k_4214_);
v_x_4213_ = v_r_4217_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(lean_object* v_00_u03b1_4226_, lean_object* v_00_u03b2_4227_, lean_object* v_inst_4228_, lean_object* v_inst_4229_, lean_object* v_k_4230_, lean_object* v_x_4231_, lean_object* v_x_4232_, lean_object* v_x_4233_){
_start:
{
lean_object* v___x_4234_; 
v___x_4234_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_inst_4228_, v_k_4230_, v_x_4231_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object* v_inst_4235_, lean_object* v_k_4236_, lean_object* v_x_4237_){
_start:
{
lean_object* v_k_4238_; lean_object* v_v_4239_; lean_object* v_l_4240_; lean_object* v_r_4241_; lean_object* v___x_4242_; uint8_t v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; uint8_t v___x_4246_; 
v_k_4238_ = lean_ctor_get(v_x_4237_, 1);
lean_inc_n(v_k_4238_, 2);
v_v_4239_ = lean_ctor_get(v_x_4237_, 2);
lean_inc(v_v_4239_);
v_l_4240_ = lean_ctor_get(v_x_4237_, 3);
lean_inc(v_l_4240_);
v_r_4241_ = lean_ctor_get(v_x_4237_, 4);
lean_inc(v_r_4241_);
lean_dec(v_x_4237_);
lean_inc_ref(v_inst_4235_);
lean_inc(v_k_4236_);
v___x_4242_ = lean_apply_2(v_inst_4235_, v_k_4236_, v_k_4238_);
v___x_4243_ = lean_unbox(v___x_4242_);
v___x_4244_ = l_Ordering_ctorIdx(v___x_4243_);
v___x_4245_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg___closed__0);
v___x_4246_ = lean_nat_dec_eq(v___x_4244_, v___x_4245_);
lean_dec(v___x_4244_);
if (v___x_4246_ == 0)
{
lean_dec(v_l_4240_);
lean_dec(v_v_4239_);
lean_dec(v_k_4238_);
v_x_4237_ = v_r_4241_;
goto _start;
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
lean_dec(v_r_4241_);
v___x_4248_ = lean_box(0);
v___x_4249_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4235_, v_k_4236_, v___x_4248_, v_l_4240_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v___x_4250_; 
v___x_4250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4250_, 0, v_k_4238_);
lean_ctor_set(v___x_4250_, 1, v_v_4239_);
return v___x_4250_;
}
else
{
lean_object* v_val_4251_; 
lean_dec(v_v_4239_);
lean_dec(v_k_4238_);
v_val_4251_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_val_4251_);
lean_dec_ref_known(v___x_4249_, 1);
return v_val_4251_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(lean_object* v_00_u03b1_4252_, lean_object* v_00_u03b2_4253_, lean_object* v_inst_4254_, lean_object* v_inst_4255_, lean_object* v_k_4256_, lean_object* v_x_4257_, lean_object* v_x_4258_, lean_object* v_x_4259_){
_start:
{
lean_object* v___x_4260_; 
v___x_4260_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_inst_4254_, v_k_4256_, v_x_4257_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object* v_inst_4261_, lean_object* v_k_4262_, lean_object* v_x_4263_){
_start:
{
lean_object* v_k_4264_; lean_object* v_v_4265_; lean_object* v_l_4266_; lean_object* v_r_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v_k_4264_ = lean_ctor_get(v_x_4263_, 1);
lean_inc_n(v_k_4264_, 2);
v_v_4265_ = lean_ctor_get(v_x_4263_, 2);
lean_inc(v_v_4265_);
v_l_4266_ = lean_ctor_get(v_x_4263_, 3);
lean_inc(v_l_4266_);
v_r_4267_ = lean_ctor_get(v_x_4263_, 4);
lean_inc(v_r_4267_);
lean_dec(v_x_4263_);
lean_inc_ref(v_inst_4261_);
lean_inc(v_k_4262_);
v___x_4268_ = lean_apply_2(v_inst_4261_, v_k_4262_, v_k_4264_);
v___x_4269_ = lean_unbox(v___x_4268_);
switch(v___x_4269_)
{
case 0:
{
lean_dec(v_r_4267_);
lean_dec(v_v_4265_);
lean_dec(v_k_4264_);
v_x_4263_ = v_l_4266_;
goto _start;
}
case 1:
{
lean_object* v___x_4271_; 
lean_dec(v_r_4267_);
lean_dec(v_l_4266_);
lean_dec(v_k_4262_);
lean_dec_ref(v_inst_4261_);
v___x_4271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4271_, 0, v_k_4264_);
lean_ctor_set(v___x_4271_, 1, v_v_4265_);
return v___x_4271_;
}
default: 
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_dec(v_l_4266_);
v___x_4272_ = lean_box(0);
v___x_4273_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4261_, v_k_4262_, v___x_4272_, v_r_4267_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v___x_4274_; 
v___x_4274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4274_, 0, v_k_4264_);
lean_ctor_set(v___x_4274_, 1, v_v_4265_);
return v___x_4274_;
}
else
{
lean_object* v_val_4275_; 
lean_dec(v_v_4265_);
lean_dec(v_k_4264_);
v_val_4275_ = lean_ctor_get(v___x_4273_, 0);
lean_inc(v_val_4275_);
lean_dec_ref_known(v___x_4273_, 1);
return v_val_4275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(lean_object* v_00_u03b1_4276_, lean_object* v_00_u03b2_4277_, lean_object* v_inst_4278_, lean_object* v_inst_4279_, lean_object* v_k_4280_, lean_object* v_x_4281_, lean_object* v_x_4282_, lean_object* v_x_4283_){
_start:
{
lean_object* v___x_4284_; 
v___x_4284_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_inst_4278_, v_k_4280_, v_x_4281_);
return v___x_4284_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object* v_inst_4285_, lean_object* v_k_4286_, lean_object* v_x_4287_){
_start:
{
lean_object* v_k_4288_; lean_object* v_v_4289_; lean_object* v_l_4290_; lean_object* v_r_4291_; lean_object* v___x_4292_; uint8_t v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; 
v_k_4288_ = lean_ctor_get(v_x_4287_, 1);
lean_inc_n(v_k_4288_, 2);
v_v_4289_ = lean_ctor_get(v_x_4287_, 2);
lean_inc(v_v_4289_);
v_l_4290_ = lean_ctor_get(v_x_4287_, 3);
lean_inc(v_l_4290_);
v_r_4291_ = lean_ctor_get(v_x_4287_, 4);
lean_inc(v_r_4291_);
lean_dec(v_x_4287_);
lean_inc_ref(v_inst_4285_);
lean_inc(v_k_4286_);
v___x_4292_ = lean_apply_2(v_inst_4285_, v_k_4286_, v_k_4288_);
v___x_4293_ = lean_unbox(v___x_4292_);
v___x_4294_ = l_Ordering_ctorIdx(v___x_4293_);
v___x_4295_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0, &l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg___closed__0);
v___x_4296_ = lean_nat_dec_eq(v___x_4294_, v___x_4295_);
lean_dec(v___x_4294_);
if (v___x_4296_ == 0)
{
lean_dec(v_r_4291_);
lean_dec(v_v_4289_);
lean_dec(v_k_4288_);
v_x_4287_ = v_l_4290_;
goto _start;
}
else
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
lean_dec(v_l_4290_);
v___x_4298_ = lean_box(0);
v___x_4299_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4285_, v_k_4286_, v___x_4298_, v_r_4291_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v___x_4300_; 
v___x_4300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4300_, 0, v_k_4288_);
lean_ctor_set(v___x_4300_, 1, v_v_4289_);
return v___x_4300_;
}
else
{
lean_object* v_val_4301_; 
lean_dec(v_v_4289_);
lean_dec(v_k_4288_);
v_val_4301_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_val_4301_);
lean_dec_ref_known(v___x_4299_, 1);
return v_val_4301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(lean_object* v_00_u03b1_4302_, lean_object* v_00_u03b2_4303_, lean_object* v_inst_4304_, lean_object* v_inst_4305_, lean_object* v_k_4306_, lean_object* v_x_4307_, lean_object* v_x_4308_, lean_object* v_x_4309_){
_start:
{
lean_object* v___x_4310_; 
v___x_4310_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_inst_4304_, v_k_4306_, v_x_4307_);
return v___x_4310_;
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
