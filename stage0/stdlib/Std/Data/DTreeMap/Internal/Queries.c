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
lean_object* lean_obj_tag_nat(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t v_x_204_, lean_object* v_h__1_205_, lean_object* v_h__2_206_, lean_object* v_h__3_207_){
_start:
{
switch(v_x_204_)
{
case 0:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
lean_dec(v_h__3_207_);
lean_dec(v_h__2_206_);
v___x_208_ = lean_box(0);
v___x_209_ = lean_apply_1(v_h__1_205_, v___x_208_);
return v___x_209_;
}
case 1:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
lean_dec(v_h__2_206_);
lean_dec(v_h__1_205_);
v___x_210_ = lean_box(0);
v___x_211_ = lean_apply_1(v_h__3_207_, v___x_210_);
return v___x_211_;
}
default: 
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_dec(v_h__3_207_);
lean_dec(v_h__1_205_);
v___x_212_ = lean_box(0);
v___x_213_ = lean_apply_1(v_h__2_206_, v___x_212_);
return v___x_213_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* v_x_214_, lean_object* v_h__1_215_, lean_object* v_h__2_216_, lean_object* v_h__3_217_){
_start:
{
uint8_t v_x_33__boxed_218_; lean_object* v_res_219_; 
v_x_33__boxed_218_ = lean_unbox(v_x_214_);
v_res_219_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_33__boxed_218_, v_h__1_215_, v_h__2_216_, v_h__3_217_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* v_motive_220_, uint8_t v_x_221_, lean_object* v_h__1_222_, lean_object* v_h__2_223_, lean_object* v_h__3_224_){
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
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* v_motive_231_, lean_object* v_x_232_, lean_object* v_h__1_233_, lean_object* v_h__2_234_, lean_object* v_h__3_235_){
_start:
{
uint8_t v_x_48__boxed_236_; lean_object* v_res_237_; 
v_x_48__boxed_236_ = lean_unbox(v_x_232_);
v_res_237_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_231_, v_x_48__boxed_236_, v_h__1_233_, v_h__2_234_, v_h__3_235_);
return v_res_237_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(lean_object* v_t_238_){
_start:
{
if (lean_obj_tag(v_t_238_) == 0)
{
uint8_t v___x_239_; 
v___x_239_ = 0;
return v___x_239_;
}
else
{
uint8_t v___x_240_; 
v___x_240_ = 1;
return v___x_240_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___redArg___boxed(lean_object* v_t_241_){
_start:
{
uint8_t v_res_242_; lean_object* v_r_243_; 
v_res_242_ = l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(v_t_241_);
lean_dec(v_t_241_);
v_r_243_ = lean_box(v_res_242_);
return v_r_243_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_t_246_){
_start:
{
if (lean_obj_tag(v_t_246_) == 0)
{
uint8_t v___x_247_; 
v___x_247_ = 0;
return v___x_247_;
}
else
{
uint8_t v___x_248_; 
v___x_248_ = 1;
return v___x_248_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___boxed(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_t_251_){
_start:
{
uint8_t v_res_252_; lean_object* v_r_253_; 
v_res_252_ = l_Std_DTreeMap_Internal_Impl_isEmpty(v_00_u03b1_249_, v_00_u03b2_250_, v_t_251_);
lean_dec(v_t_251_);
v_r_253_ = lean_box(v_res_252_);
return v_r_253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object* v_inst_254_, lean_object* v_t_255_, lean_object* v_k_256_){
_start:
{
if (lean_obj_tag(v_t_255_) == 0)
{
lean_object* v_k_257_; lean_object* v_v_258_; lean_object* v_l_259_; lean_object* v_r_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
v_k_257_ = lean_ctor_get(v_t_255_, 1);
lean_inc(v_k_257_);
v_v_258_ = lean_ctor_get(v_t_255_, 2);
lean_inc(v_v_258_);
v_l_259_ = lean_ctor_get(v_t_255_, 3);
lean_inc(v_l_259_);
v_r_260_ = lean_ctor_get(v_t_255_, 4);
lean_inc(v_r_260_);
lean_dec_ref_known(v_t_255_, 5);
lean_inc_ref(v_inst_254_);
lean_inc(v_k_256_);
v___x_261_ = lean_apply_2(v_inst_254_, v_k_256_, v_k_257_);
v___x_262_ = lean_unbox(v___x_261_);
switch(v___x_262_)
{
case 0:
{
lean_dec(v_r_260_);
lean_dec(v_v_258_);
v_t_255_ = v_l_259_;
goto _start;
}
case 1:
{
lean_object* v___x_264_; 
lean_dec(v_r_260_);
lean_dec(v_l_259_);
lean_dec(v_k_256_);
lean_dec_ref(v_inst_254_);
v___x_264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_264_, 0, v_v_258_);
return v___x_264_;
}
default: 
{
lean_dec(v_l_259_);
lean_dec(v_v_258_);
v_t_255_ = v_r_260_;
goto _start;
}
}
}
else
{
lean_object* v___x_266_; 
lean_dec(v_k_256_);
lean_dec_ref(v_inst_254_);
v___x_266_ = lean_box(0);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f(lean_object* v_00_u03b1_267_, lean_object* v_00_u03b2_268_, lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_t_271_, lean_object* v_k_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_inst_269_, v_t_271_, v_k_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get___redArg(lean_object* v_inst_274_, lean_object* v_t_275_, lean_object* v_k_276_){
_start:
{
lean_object* v_k_277_; lean_object* v_v_278_; lean_object* v_l_279_; lean_object* v_r_280_; lean_object* v___x_281_; uint8_t v___x_282_; 
v_k_277_ = lean_ctor_get(v_t_275_, 1);
lean_inc(v_k_277_);
v_v_278_ = lean_ctor_get(v_t_275_, 2);
lean_inc(v_v_278_);
v_l_279_ = lean_ctor_get(v_t_275_, 3);
lean_inc(v_l_279_);
v_r_280_ = lean_ctor_get(v_t_275_, 4);
lean_inc(v_r_280_);
lean_dec(v_t_275_);
lean_inc_ref(v_inst_274_);
lean_inc(v_k_276_);
v___x_281_ = lean_apply_2(v_inst_274_, v_k_276_, v_k_277_);
v___x_282_ = lean_unbox(v___x_281_);
switch(v___x_282_)
{
case 0:
{
lean_dec(v_r_280_);
lean_dec(v_v_278_);
v_t_275_ = v_l_279_;
goto _start;
}
case 1:
{
lean_dec(v_r_280_);
lean_dec(v_l_279_);
lean_dec(v_k_276_);
lean_dec_ref(v_inst_274_);
return v_v_278_;
}
default: 
{
lean_dec(v_l_279_);
lean_dec(v_v_278_);
v_t_275_ = v_r_280_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get(lean_object* v_00_u03b1_285_, lean_object* v_00_u03b2_286_, lean_object* v_inst_287_, lean_object* v_inst_288_, lean_object* v_t_289_, lean_object* v_k_290_, lean_object* v_hlk_291_){
_start:
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_inst_287_, v_t_289_, v_k_290_);
return v___x_292_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_296_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_297_ = lean_unsigned_to_nat(13u);
v___x_298_ = lean_unsigned_to_nat(108u);
v___x_299_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1));
v___x_300_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_301_ = l_mkPanicMessageWithDecl(v___x_300_, v___x_299_, v___x_298_, v___x_297_, v___x_296_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object* v_inst_302_, lean_object* v_t_303_, lean_object* v_k_304_, lean_object* v_inst_305_){
_start:
{
if (lean_obj_tag(v_t_303_) == 0)
{
lean_object* v_k_306_; lean_object* v_v_307_; lean_object* v_l_308_; lean_object* v_r_309_; lean_object* v___x_310_; uint8_t v___x_311_; 
v_k_306_ = lean_ctor_get(v_t_303_, 1);
lean_inc(v_k_306_);
v_v_307_ = lean_ctor_get(v_t_303_, 2);
lean_inc(v_v_307_);
v_l_308_ = lean_ctor_get(v_t_303_, 3);
lean_inc(v_l_308_);
v_r_309_ = lean_ctor_get(v_t_303_, 4);
lean_inc(v_r_309_);
lean_dec_ref_known(v_t_303_, 5);
lean_inc_ref(v_inst_302_);
lean_inc(v_k_304_);
v___x_310_ = lean_apply_2(v_inst_302_, v_k_304_, v_k_306_);
v___x_311_ = lean_unbox(v___x_310_);
switch(v___x_311_)
{
case 0:
{
lean_dec(v_r_309_);
lean_dec(v_v_307_);
v_t_303_ = v_l_308_;
goto _start;
}
case 1:
{
lean_dec(v_r_309_);
lean_dec(v_l_308_);
lean_dec(v_k_304_);
lean_dec_ref(v_inst_302_);
return v_v_307_;
}
default: 
{
lean_dec(v_l_308_);
lean_dec(v_v_307_);
v_t_303_ = v_r_309_;
goto _start;
}
}
}
else
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v_k_304_);
lean_dec_ref(v_inst_302_);
v___x_314_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3);
v___x_315_ = l_panic___redArg(v_inst_305_, v___x_314_);
return v___x_315_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg___boxed(lean_object* v_inst_316_, lean_object* v_t_317_, lean_object* v_k_318_, lean_object* v_inst_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_inst_316_, v_t_317_, v_k_318_, v_inst_319_);
lean_dec(v_inst_319_);
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21(lean_object* v_00_u03b1_321_, lean_object* v_00_u03b2_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_t_325_, lean_object* v_k_326_, lean_object* v_inst_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_inst_323_, v_t_325_, v_k_326_, v_inst_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___boxed(lean_object* v_00_u03b1_329_, lean_object* v_00_u03b2_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_t_333_, lean_object* v_k_334_, lean_object* v_inst_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_DTreeMap_Internal_Impl_get_x21(v_00_u03b1_329_, v_00_u03b2_330_, v_inst_331_, v_inst_332_, v_t_333_, v_k_334_, v_inst_335_);
lean_dec(v_inst_335_);
return v_res_336_;
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
lean_dec_ref_known(v_t_338_, 5);
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
lean_inc_n(v_k_373_, 2);
v_v_374_ = lean_ctor_get(v_t_371_, 2);
lean_inc(v_v_374_);
v_l_375_ = lean_ctor_get(v_t_371_, 3);
lean_inc(v_l_375_);
v_r_376_ = lean_ctor_get(v_t_371_, 4);
lean_inc(v_r_376_);
lean_dec_ref_known(v_t_371_, 5);
lean_inc_ref(v_inst_370_);
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
lean_inc_n(v_k_393_, 2);
v_v_394_ = lean_ctor_get(v_t_391_, 2);
lean_inc(v_v_394_);
v_l_395_ = lean_ctor_get(v_t_391_, 3);
lean_inc(v_l_395_);
v_r_396_ = lean_ctor_get(v_t_391_, 4);
lean_inc(v_r_396_);
lean_dec(v_t_391_);
lean_inc_ref(v_inst_390_);
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
lean_inc_n(v_k_420_, 2);
v_v_421_ = lean_ctor_get(v_t_418_, 2);
lean_inc(v_v_421_);
v_l_422_ = lean_ctor_get(v_t_418_, 3);
lean_inc(v_l_422_);
v_r_423_ = lean_ctor_get(v_t_418_, 4);
lean_inc(v_r_423_);
lean_dec_ref_known(v_t_418_, 5);
lean_inc_ref(v_inst_416_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___boxed(lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_t_433_, lean_object* v_k_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_inst_431_, v_inst_432_, v_t_433_, v_k_434_);
lean_dec_ref(v_inst_432_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_t_440_, lean_object* v_k_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_inst_438_, v_inst_439_, v_t_440_, v_k_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___boxed(lean_object* v_00_u03b1_443_, lean_object* v_00_u03b2_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_t_447_, lean_object* v_k_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21(v_00_u03b1_443_, v_00_u03b2_444_, v_inst_445_, v_inst_446_, v_t_447_, v_k_448_);
lean_dec_ref(v_inst_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(lean_object* v_inst_450_, lean_object* v_t_451_, lean_object* v_k_452_, lean_object* v_fallback_453_){
_start:
{
if (lean_obj_tag(v_t_451_) == 0)
{
lean_object* v_k_454_; lean_object* v_v_455_; lean_object* v_l_456_; lean_object* v_r_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v_k_454_ = lean_ctor_get(v_t_451_, 1);
lean_inc_n(v_k_454_, 2);
v_v_455_ = lean_ctor_get(v_t_451_, 2);
lean_inc(v_v_455_);
v_l_456_ = lean_ctor_get(v_t_451_, 3);
lean_inc(v_l_456_);
v_r_457_ = lean_ctor_get(v_t_451_, 4);
lean_inc(v_r_457_);
lean_dec_ref_known(v_t_451_, 5);
lean_inc_ref(v_inst_450_);
lean_inc(v_k_452_);
v___x_458_ = lean_apply_2(v_inst_450_, v_k_452_, v_k_454_);
v___x_459_ = lean_unbox(v___x_458_);
switch(v___x_459_)
{
case 0:
{
lean_dec(v_r_457_);
lean_dec(v_v_455_);
lean_dec(v_k_454_);
v_t_451_ = v_l_456_;
goto _start;
}
case 1:
{
lean_object* v___x_461_; 
lean_dec(v_r_457_);
lean_dec(v_l_456_);
lean_dec(v_k_452_);
lean_dec_ref(v_inst_450_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v_k_454_);
lean_ctor_set(v___x_461_, 1, v_v_455_);
return v___x_461_;
}
default: 
{
lean_dec(v_l_456_);
lean_dec(v_v_455_);
lean_dec(v_k_454_);
v_t_451_ = v_r_457_;
goto _start;
}
}
}
else
{
lean_dec(v_k_452_);
lean_dec_ref(v_inst_450_);
lean_inc_ref(v_fallback_453_);
return v_fallback_453_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg___boxed(lean_object* v_inst_463_, lean_object* v_t_464_, lean_object* v_k_465_, lean_object* v_fallback_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_463_, v_t_464_, v_k_465_, v_fallback_466_);
lean_dec_ref(v_fallback_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD(lean_object* v_00_u03b1_468_, lean_object* v_00_u03b2_469_, lean_object* v_inst_470_, lean_object* v_t_471_, lean_object* v_k_472_, lean_object* v_fallback_473_){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_470_, v_t_471_, v_k_472_, v_fallback_473_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___boxed(lean_object* v_00_u03b1_475_, lean_object* v_00_u03b2_476_, lean_object* v_inst_477_, lean_object* v_t_478_, lean_object* v_k_479_, lean_object* v_fallback_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Std_DTreeMap_Internal_Impl_getEntryD(v_00_u03b1_475_, v_00_u03b2_476_, v_inst_477_, v_t_478_, v_k_479_, v_fallback_480_);
lean_dec_ref(v_fallback_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object* v_inst_482_, lean_object* v_t_483_, lean_object* v_k_484_){
_start:
{
if (lean_obj_tag(v_t_483_) == 0)
{
lean_object* v_k_485_; lean_object* v_l_486_; lean_object* v_r_487_; lean_object* v___x_488_; uint8_t v___x_489_; 
v_k_485_ = lean_ctor_get(v_t_483_, 1);
lean_inc_n(v_k_485_, 2);
v_l_486_ = lean_ctor_get(v_t_483_, 3);
lean_inc(v_l_486_);
v_r_487_ = lean_ctor_get(v_t_483_, 4);
lean_inc(v_r_487_);
lean_dec_ref_known(v_t_483_, 5);
lean_inc_ref(v_inst_482_);
lean_inc(v_k_484_);
v___x_488_ = lean_apply_2(v_inst_482_, v_k_484_, v_k_485_);
v___x_489_ = lean_unbox(v___x_488_);
switch(v___x_489_)
{
case 0:
{
lean_dec(v_r_487_);
lean_dec(v_k_485_);
v_t_483_ = v_l_486_;
goto _start;
}
case 1:
{
lean_object* v___x_491_; 
lean_dec(v_r_487_);
lean_dec(v_l_486_);
lean_dec(v_k_484_);
lean_dec_ref(v_inst_482_);
v___x_491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_491_, 0, v_k_485_);
return v___x_491_;
}
default: 
{
lean_dec(v_l_486_);
lean_dec(v_k_485_);
v_t_483_ = v_r_487_;
goto _start;
}
}
}
else
{
lean_object* v___x_493_; 
lean_dec(v_k_484_);
lean_dec_ref(v_inst_482_);
v___x_493_ = lean_box(0);
return v___x_493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_inst_496_, lean_object* v_t_497_, lean_object* v_k_498_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_inst_496_, v_t_497_, v_k_498_);
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object* v_inst_500_, lean_object* v_t_501_, lean_object* v_k_502_){
_start:
{
lean_object* v_k_503_; lean_object* v_l_504_; lean_object* v_r_505_; lean_object* v___x_506_; uint8_t v___x_507_; 
v_k_503_ = lean_ctor_get(v_t_501_, 1);
lean_inc_n(v_k_503_, 2);
v_l_504_ = lean_ctor_get(v_t_501_, 3);
lean_inc(v_l_504_);
v_r_505_ = lean_ctor_get(v_t_501_, 4);
lean_inc(v_r_505_);
lean_dec(v_t_501_);
lean_inc_ref(v_inst_500_);
lean_inc(v_k_502_);
v___x_506_ = lean_apply_2(v_inst_500_, v_k_502_, v_k_503_);
v___x_507_ = lean_unbox(v___x_506_);
switch(v___x_507_)
{
case 0:
{
lean_dec(v_r_505_);
lean_dec(v_k_503_);
v_t_501_ = v_l_504_;
goto _start;
}
case 1:
{
lean_dec(v_r_505_);
lean_dec(v_l_504_);
lean_dec(v_k_502_);
lean_dec_ref(v_inst_500_);
return v_k_503_;
}
default: 
{
lean_dec(v_l_504_);
lean_dec(v_k_503_);
v_t_501_ = v_r_505_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey(lean_object* v_00_u03b1_510_, lean_object* v_00_u03b2_511_, lean_object* v_inst_512_, lean_object* v_t_513_, lean_object* v_k_514_, lean_object* v_hlk_515_){
_start:
{
lean_object* v___x_516_; 
v___x_516_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_inst_512_, v_t_513_, v_k_514_);
return v___x_516_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_518_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_519_ = lean_unsigned_to_nat(13u);
v___x_520_ = lean_unsigned_to_nat(186u);
v___x_521_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0));
v___x_522_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_523_ = l_mkPanicMessageWithDecl(v___x_522_, v___x_521_, v___x_520_, v___x_519_, v___x_518_);
return v___x_523_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object* v_inst_524_, lean_object* v_t_525_, lean_object* v_k_526_, lean_object* v_inst_527_){
_start:
{
if (lean_obj_tag(v_t_525_) == 0)
{
lean_object* v_k_528_; lean_object* v_l_529_; lean_object* v_r_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_k_528_ = lean_ctor_get(v_t_525_, 1);
lean_inc_n(v_k_528_, 2);
v_l_529_ = lean_ctor_get(v_t_525_, 3);
lean_inc(v_l_529_);
v_r_530_ = lean_ctor_get(v_t_525_, 4);
lean_inc(v_r_530_);
lean_dec_ref_known(v_t_525_, 5);
lean_inc_ref(v_inst_524_);
lean_inc(v_k_526_);
v___x_531_ = lean_apply_2(v_inst_524_, v_k_526_, v_k_528_);
v___x_532_ = lean_unbox(v___x_531_);
switch(v___x_532_)
{
case 0:
{
lean_dec(v_r_530_);
lean_dec(v_k_528_);
v_t_525_ = v_l_529_;
goto _start;
}
case 1:
{
lean_dec(v_r_530_);
lean_dec(v_l_529_);
lean_dec(v_k_526_);
lean_dec_ref(v_inst_524_);
return v_k_528_;
}
default: 
{
lean_dec(v_l_529_);
lean_dec(v_k_528_);
v_t_525_ = v_r_530_;
goto _start;
}
}
}
else
{
lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v_k_526_);
lean_dec_ref(v_inst_524_);
v___x_535_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1);
v___x_536_ = l_panic___redArg(v_inst_527_, v___x_535_);
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___boxed(lean_object* v_inst_537_, lean_object* v_t_538_, lean_object* v_k_539_, lean_object* v_inst_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_inst_537_, v_t_538_, v_k_539_, v_inst_540_);
lean_dec(v_inst_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21(lean_object* v_00_u03b1_542_, lean_object* v_00_u03b2_543_, lean_object* v_inst_544_, lean_object* v_t_545_, lean_object* v_k_546_, lean_object* v_inst_547_){
_start:
{
lean_object* v___x_548_; 
v___x_548_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_inst_544_, v_t_545_, v_k_546_, v_inst_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___boxed(lean_object* v_00_u03b1_549_, lean_object* v_00_u03b2_550_, lean_object* v_inst_551_, lean_object* v_t_552_, lean_object* v_k_553_, lean_object* v_inst_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Std_DTreeMap_Internal_Impl_getKey_x21(v_00_u03b1_549_, v_00_u03b2_550_, v_inst_551_, v_t_552_, v_k_553_, v_inst_554_);
lean_dec(v_inst_554_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object* v_inst_556_, lean_object* v_t_557_, lean_object* v_k_558_, lean_object* v_fallback_559_){
_start:
{
if (lean_obj_tag(v_t_557_) == 0)
{
lean_object* v_k_560_; lean_object* v_l_561_; lean_object* v_r_562_; lean_object* v___x_563_; uint8_t v___x_564_; 
v_k_560_ = lean_ctor_get(v_t_557_, 1);
lean_inc_n(v_k_560_, 2);
v_l_561_ = lean_ctor_get(v_t_557_, 3);
lean_inc(v_l_561_);
v_r_562_ = lean_ctor_get(v_t_557_, 4);
lean_inc(v_r_562_);
lean_dec_ref_known(v_t_557_, 5);
lean_inc_ref(v_inst_556_);
lean_inc(v_k_558_);
v___x_563_ = lean_apply_2(v_inst_556_, v_k_558_, v_k_560_);
v___x_564_ = lean_unbox(v___x_563_);
switch(v___x_564_)
{
case 0:
{
lean_dec(v_r_562_);
lean_dec(v_k_560_);
v_t_557_ = v_l_561_;
goto _start;
}
case 1:
{
lean_dec(v_r_562_);
lean_dec(v_l_561_);
lean_dec(v_k_558_);
lean_dec_ref(v_inst_556_);
return v_k_560_;
}
default: 
{
lean_dec(v_l_561_);
lean_dec(v_k_560_);
v_t_557_ = v_r_562_;
goto _start;
}
}
}
else
{
lean_dec(v_k_558_);
lean_dec_ref(v_inst_556_);
lean_inc(v_fallback_559_);
return v_fallback_559_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg___boxed(lean_object* v_inst_567_, lean_object* v_t_568_, lean_object* v_k_569_, lean_object* v_fallback_570_){
_start:
{
lean_object* v_res_571_; 
v_res_571_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_567_, v_t_568_, v_k_569_, v_fallback_570_);
lean_dec(v_fallback_570_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD(lean_object* v_00_u03b1_572_, lean_object* v_00_u03b2_573_, lean_object* v_inst_574_, lean_object* v_t_575_, lean_object* v_k_576_, lean_object* v_fallback_577_){
_start:
{
lean_object* v___x_578_; 
v___x_578_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_574_, v_t_575_, v_k_576_, v_fallback_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___boxed(lean_object* v_00_u03b1_579_, lean_object* v_00_u03b2_580_, lean_object* v_inst_581_, lean_object* v_t_582_, lean_object* v_k_583_, lean_object* v_fallback_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Std_DTreeMap_Internal_Impl_getKeyD(v_00_u03b1_579_, v_00_u03b2_580_, v_inst_581_, v_t_582_, v_k_583_, v_fallback_584_);
lean_dec(v_fallback_584_);
return v_res_585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object* v_inst_586_, lean_object* v_t_587_, lean_object* v_k_588_){
_start:
{
if (lean_obj_tag(v_t_587_) == 0)
{
lean_object* v_k_589_; lean_object* v_v_590_; lean_object* v_l_591_; lean_object* v_r_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_k_589_ = lean_ctor_get(v_t_587_, 1);
lean_inc(v_k_589_);
v_v_590_ = lean_ctor_get(v_t_587_, 2);
lean_inc(v_v_590_);
v_l_591_ = lean_ctor_get(v_t_587_, 3);
lean_inc(v_l_591_);
v_r_592_ = lean_ctor_get(v_t_587_, 4);
lean_inc(v_r_592_);
lean_dec_ref_known(v_t_587_, 5);
lean_inc_ref(v_inst_586_);
lean_inc(v_k_588_);
v___x_593_ = lean_apply_2(v_inst_586_, v_k_588_, v_k_589_);
v___x_594_ = lean_unbox(v___x_593_);
switch(v___x_594_)
{
case 0:
{
lean_dec(v_r_592_);
lean_dec(v_v_590_);
v_t_587_ = v_l_591_;
goto _start;
}
case 1:
{
lean_object* v___x_596_; 
lean_dec(v_r_592_);
lean_dec(v_l_591_);
lean_dec(v_k_588_);
lean_dec_ref(v_inst_586_);
v___x_596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_596_, 0, v_v_590_);
return v___x_596_;
}
default: 
{
lean_dec(v_l_591_);
lean_dec(v_v_590_);
v_t_587_ = v_r_592_;
goto _start;
}
}
}
else
{
lean_object* v___x_598_; 
lean_dec(v_k_588_);
lean_dec_ref(v_inst_586_);
v___x_598_ = lean_box(0);
return v___x_598_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f(lean_object* v_00_u03b1_599_, lean_object* v_00_u03b4_600_, lean_object* v_inst_601_, lean_object* v_t_602_, lean_object* v_k_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_inst_601_, v_t_602_, v_k_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object* v_inst_605_, lean_object* v_t_606_, lean_object* v_k_607_){
_start:
{
lean_object* v_k_608_; lean_object* v_v_609_; lean_object* v_l_610_; lean_object* v_r_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v_k_608_ = lean_ctor_get(v_t_606_, 1);
lean_inc(v_k_608_);
v_v_609_ = lean_ctor_get(v_t_606_, 2);
lean_inc(v_v_609_);
v_l_610_ = lean_ctor_get(v_t_606_, 3);
lean_inc(v_l_610_);
v_r_611_ = lean_ctor_get(v_t_606_, 4);
lean_inc(v_r_611_);
lean_dec(v_t_606_);
lean_inc_ref(v_inst_605_);
lean_inc(v_k_607_);
v___x_612_ = lean_apply_2(v_inst_605_, v_k_607_, v_k_608_);
v___x_613_ = lean_unbox(v___x_612_);
switch(v___x_613_)
{
case 0:
{
lean_dec(v_r_611_);
lean_dec(v_v_609_);
v_t_606_ = v_l_610_;
goto _start;
}
case 1:
{
lean_dec(v_r_611_);
lean_dec(v_l_610_);
lean_dec(v_k_607_);
lean_dec_ref(v_inst_605_);
return v_v_609_;
}
default: 
{
lean_dec(v_l_610_);
lean_dec(v_v_609_);
v_t_606_ = v_r_611_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get(lean_object* v_00_u03b1_616_, lean_object* v_00_u03b4_617_, lean_object* v_inst_618_, lean_object* v_t_619_, lean_object* v_k_620_, lean_object* v_hlk_621_){
_start:
{
lean_object* v___x_622_; 
v___x_622_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_inst_618_, v_t_619_, v_k_620_);
return v___x_622_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; 
v___x_624_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_625_ = lean_unsigned_to_nat(13u);
v___x_626_ = lean_unsigned_to_nat(227u);
v___x_627_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0));
v___x_628_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_629_ = l_mkPanicMessageWithDecl(v___x_628_, v___x_627_, v___x_626_, v___x_625_, v___x_624_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object* v_inst_630_, lean_object* v_inst_631_, lean_object* v_t_632_, lean_object* v_k_633_){
_start:
{
if (lean_obj_tag(v_t_632_) == 0)
{
lean_object* v_k_634_; lean_object* v_v_635_; lean_object* v_l_636_; lean_object* v_r_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_k_634_ = lean_ctor_get(v_t_632_, 1);
lean_inc(v_k_634_);
v_v_635_ = lean_ctor_get(v_t_632_, 2);
lean_inc(v_v_635_);
v_l_636_ = lean_ctor_get(v_t_632_, 3);
lean_inc(v_l_636_);
v_r_637_ = lean_ctor_get(v_t_632_, 4);
lean_inc(v_r_637_);
lean_dec_ref_known(v_t_632_, 5);
lean_inc_ref(v_inst_630_);
lean_inc(v_k_633_);
v___x_638_ = lean_apply_2(v_inst_630_, v_k_633_, v_k_634_);
v___x_639_ = lean_unbox(v___x_638_);
switch(v___x_639_)
{
case 0:
{
lean_dec(v_r_637_);
lean_dec(v_v_635_);
v_t_632_ = v_l_636_;
goto _start;
}
case 1:
{
lean_dec(v_r_637_);
lean_dec(v_l_636_);
lean_dec(v_k_633_);
lean_dec_ref(v_inst_630_);
return v_v_635_;
}
default: 
{
lean_dec(v_l_636_);
lean_dec(v_v_635_);
v_t_632_ = v_r_637_;
goto _start;
}
}
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec(v_k_633_);
lean_dec_ref(v_inst_630_);
v___x_642_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1);
v___x_643_ = l_panic___redArg(v_inst_631_, v___x_642_);
return v___x_643_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___boxed(lean_object* v_inst_644_, lean_object* v_inst_645_, lean_object* v_t_646_, lean_object* v_k_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_inst_644_, v_inst_645_, v_t_646_, v_k_647_);
lean_dec(v_inst_645_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21(lean_object* v_00_u03b1_649_, lean_object* v_00_u03b4_650_, lean_object* v_inst_651_, lean_object* v_inst_652_, lean_object* v_t_653_, lean_object* v_k_654_){
_start:
{
lean_object* v___x_655_; 
v___x_655_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_inst_651_, v_inst_652_, v_t_653_, v_k_654_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___boxed(lean_object* v_00_u03b1_656_, lean_object* v_00_u03b4_657_, lean_object* v_inst_658_, lean_object* v_inst_659_, lean_object* v_t_660_, lean_object* v_k_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21(v_00_u03b1_656_, v_00_u03b4_657_, v_inst_658_, v_inst_659_, v_t_660_, v_k_661_);
lean_dec(v_inst_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object* v_inst_663_, lean_object* v_t_664_, lean_object* v_k_665_, lean_object* v_fallback_666_){
_start:
{
if (lean_obj_tag(v_t_664_) == 0)
{
lean_object* v_k_667_; lean_object* v_v_668_; lean_object* v_l_669_; lean_object* v_r_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_k_667_ = lean_ctor_get(v_t_664_, 1);
lean_inc(v_k_667_);
v_v_668_ = lean_ctor_get(v_t_664_, 2);
lean_inc(v_v_668_);
v_l_669_ = lean_ctor_get(v_t_664_, 3);
lean_inc(v_l_669_);
v_r_670_ = lean_ctor_get(v_t_664_, 4);
lean_inc(v_r_670_);
lean_dec_ref_known(v_t_664_, 5);
lean_inc_ref(v_inst_663_);
lean_inc(v_k_665_);
v___x_671_ = lean_apply_2(v_inst_663_, v_k_665_, v_k_667_);
v___x_672_ = lean_unbox(v___x_671_);
switch(v___x_672_)
{
case 0:
{
lean_dec(v_r_670_);
lean_dec(v_v_668_);
v_t_664_ = v_l_669_;
goto _start;
}
case 1:
{
lean_dec(v_r_670_);
lean_dec(v_l_669_);
lean_dec(v_k_665_);
lean_dec_ref(v_inst_663_);
return v_v_668_;
}
default: 
{
lean_dec(v_l_669_);
lean_dec(v_v_668_);
v_t_664_ = v_r_670_;
goto _start;
}
}
}
else
{
lean_dec(v_k_665_);
lean_dec_ref(v_inst_663_);
lean_inc(v_fallback_666_);
return v_fallback_666_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg___boxed(lean_object* v_inst_675_, lean_object* v_t_676_, lean_object* v_k_677_, lean_object* v_fallback_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_675_, v_t_676_, v_k_677_, v_fallback_678_);
lean_dec(v_fallback_678_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD(lean_object* v_00_u03b1_680_, lean_object* v_00_u03b4_681_, lean_object* v_inst_682_, lean_object* v_t_683_, lean_object* v_k_684_, lean_object* v_fallback_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_682_, v_t_683_, v_k_684_, v_fallback_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___boxed(lean_object* v_00_u03b1_687_, lean_object* v_00_u03b4_688_, lean_object* v_inst_689_, lean_object* v_t_690_, lean_object* v_k_691_, lean_object* v_fallback_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Std_DTreeMap_Internal_Impl_Const_getD(v_00_u03b1_687_, v_00_u03b4_688_, v_inst_689_, v_t_690_, v_k_691_, v_fallback_692_);
lean_dec(v_fallback_692_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1(lean_object* v_f_694_, lean_object* v_k_695_, lean_object* v_v_696_, lean_object* v_toBind_697_, lean_object* v___f_698_, lean_object* v_left_699_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_apply_3(v_f_694_, v_left_699_, v_k_695_, v_v_696_);
v___x_701_ = lean_apply_4(v_toBind_697_, lean_box(0), lean_box(0), v___x_700_, v___f_698_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object* v_inst_702_, lean_object* v_f_703_, lean_object* v_init_704_, lean_object* v_x_705_){
_start:
{
if (lean_obj_tag(v_x_705_) == 0)
{
lean_object* v_toBind_706_; lean_object* v_k_707_; lean_object* v_v_708_; lean_object* v_l_709_; lean_object* v_r_710_; lean_object* v___f_711_; lean_object* v___f_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_toBind_706_ = lean_ctor_get(v_inst_702_, 1);
lean_inc_n(v_toBind_706_, 2);
v_k_707_ = lean_ctor_get(v_x_705_, 1);
lean_inc(v_k_707_);
v_v_708_ = lean_ctor_get(v_x_705_, 2);
lean_inc(v_v_708_);
v_l_709_ = lean_ctor_get(v_x_705_, 3);
lean_inc(v_l_709_);
v_r_710_ = lean_ctor_get(v_x_705_, 4);
lean_inc(v_r_710_);
lean_dec_ref_known(v_x_705_, 5);
lean_inc_n(v_f_703_, 2);
lean_inc_ref(v_inst_702_);
v___f_711_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_711_, 0, v_inst_702_);
lean_closure_set(v___f_711_, 1, v_f_703_);
lean_closure_set(v___f_711_, 2, v_r_710_);
v___f_712_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_712_, 0, v_f_703_);
lean_closure_set(v___f_712_, 1, v_k_707_);
lean_closure_set(v___f_712_, 2, v_v_708_);
lean_closure_set(v___f_712_, 3, v_toBind_706_);
lean_closure_set(v___f_712_, 4, v___f_711_);
v___x_713_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_702_, v_f_703_, v_init_704_, v_l_709_);
v___x_714_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_713_, v___f_712_);
return v___x_714_;
}
else
{
lean_object* v_toApplicative_715_; lean_object* v_toPure_716_; lean_object* v___x_717_; 
v_toApplicative_715_ = lean_ctor_get(v_inst_702_, 0);
lean_inc_ref(v_toApplicative_715_);
lean_dec(v_f_703_);
lean_dec_ref(v_inst_702_);
v_toPure_716_ = lean_ctor_get(v_toApplicative_715_, 1);
lean_inc(v_toPure_716_);
lean_dec_ref(v_toApplicative_715_);
v___x_717_ = lean_apply_2(v_toPure_716_, lean_box(0), v_init_704_);
return v___x_717_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0(lean_object* v_inst_718_, lean_object* v_f_719_, lean_object* v_r_720_, lean_object* v_middle_721_){
_start:
{
lean_object* v___x_722_; 
v___x_722_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_718_, v_f_719_, v_middle_721_, v_r_720_);
return v___x_722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM(lean_object* v_00_u03b1_723_, lean_object* v_00_u03b2_724_, lean_object* v_00_u03b4_725_, lean_object* v_m_726_, lean_object* v_inst_727_, lean_object* v_f_728_, lean_object* v_init_729_, lean_object* v_x_730_){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_727_, v_f_728_, v_init_729_, v_x_730_);
return v___x_731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0(lean_object* v_f_732_, lean_object* v_x1_733_, lean_object* v_x2_734_, lean_object* v_x3_735_){
_start:
{
lean_object* v___x_736_; 
v___x_736_ = lean_apply_3(v_f_732_, v_x1_733_, v_x2_734_, v_x3_735_);
return v___x_736_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object* v_f_756_, lean_object* v_init_757_, lean_object* v_t_758_){
_start:
{
lean_object* v___f_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___f_759_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_759_, 0, v_f_756_);
v___x_760_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_761_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_760_, v___f_759_, v_init_757_, v_t_758_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl(lean_object* v_00_u03b1_762_, lean_object* v_00_u03b2_763_, lean_object* v_00_u03b4_764_, lean_object* v_f_765_, lean_object* v_init_766_, lean_object* v_t_767_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_765_, v_init_766_, v_t_767_);
return v___x_768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1(lean_object* v_f_769_, lean_object* v_k_770_, lean_object* v_v_771_, lean_object* v_toBind_772_, lean_object* v___f_773_, lean_object* v_right_774_){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = lean_apply_3(v_f_769_, v_k_770_, v_v_771_, v_right_774_);
v___x_776_ = lean_apply_4(v_toBind_772_, lean_box(0), lean_box(0), v___x_775_, v___f_773_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object* v_inst_777_, lean_object* v_f_778_, lean_object* v_init_779_, lean_object* v_x_780_){
_start:
{
if (lean_obj_tag(v_x_780_) == 0)
{
lean_object* v_toBind_781_; lean_object* v_k_782_; lean_object* v_v_783_; lean_object* v_l_784_; lean_object* v_r_785_; lean_object* v___f_786_; lean_object* v___f_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v_toBind_781_ = lean_ctor_get(v_inst_777_, 1);
lean_inc_n(v_toBind_781_, 2);
v_k_782_ = lean_ctor_get(v_x_780_, 1);
lean_inc(v_k_782_);
v_v_783_ = lean_ctor_get(v_x_780_, 2);
lean_inc(v_v_783_);
v_l_784_ = lean_ctor_get(v_x_780_, 3);
lean_inc(v_l_784_);
v_r_785_ = lean_ctor_get(v_x_780_, 4);
lean_inc(v_r_785_);
lean_dec_ref_known(v_x_780_, 5);
lean_inc_n(v_f_778_, 2);
lean_inc_ref(v_inst_777_);
v___f_786_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_786_, 0, v_inst_777_);
lean_closure_set(v___f_786_, 1, v_f_778_);
lean_closure_set(v___f_786_, 2, v_l_784_);
v___f_787_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_787_, 0, v_f_778_);
lean_closure_set(v___f_787_, 1, v_k_782_);
lean_closure_set(v___f_787_, 2, v_v_783_);
lean_closure_set(v___f_787_, 3, v_toBind_781_);
lean_closure_set(v___f_787_, 4, v___f_786_);
v___x_788_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_777_, v_f_778_, v_init_779_, v_r_785_);
v___x_789_ = lean_apply_4(v_toBind_781_, lean_box(0), lean_box(0), v___x_788_, v___f_787_);
return v___x_789_;
}
else
{
lean_object* v_toApplicative_790_; lean_object* v_toPure_791_; lean_object* v___x_792_; 
v_toApplicative_790_ = lean_ctor_get(v_inst_777_, 0);
lean_inc_ref(v_toApplicative_790_);
lean_dec(v_f_778_);
lean_dec_ref(v_inst_777_);
v_toPure_791_ = lean_ctor_get(v_toApplicative_790_, 1);
lean_inc(v_toPure_791_);
lean_dec_ref(v_toApplicative_790_);
v___x_792_ = lean_apply_2(v_toPure_791_, lean_box(0), v_init_779_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0(lean_object* v_inst_793_, lean_object* v_f_794_, lean_object* v_l_795_, lean_object* v_middle_796_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_793_, v_f_794_, v_middle_796_, v_l_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM(lean_object* v_00_u03b1_798_, lean_object* v_00_u03b2_799_, lean_object* v_00_u03b4_800_, lean_object* v_m_801_, lean_object* v_inst_802_, lean_object* v_f_803_, lean_object* v_init_804_, lean_object* v_x_805_){
_start:
{
lean_object* v___x_806_; 
v___x_806_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_802_, v_f_803_, v_init_804_, v_x_805_);
return v___x_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr___redArg(lean_object* v_f_807_, lean_object* v_init_808_, lean_object* v_t_809_){
_start:
{
lean_object* v___f_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___f_810_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_810_, 0, v_f_807_);
v___x_811_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_812_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_811_, v___f_810_, v_init_808_, v_t_809_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr(lean_object* v_00_u03b1_813_, lean_object* v_00_u03b2_814_, lean_object* v_00_u03b4_815_, lean_object* v_f_816_, lean_object* v_init_817_, lean_object* v_t_818_){
_start:
{
lean_object* v___f_819_; lean_object* v___x_820_; lean_object* v___x_821_; 
v___f_819_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_819_, 0, v_f_816_);
v___x_820_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_821_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_820_, v___f_819_, v_init_817_, v_t_818_);
return v___x_821_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0(lean_object* v_f_822_, lean_object* v_x_823_, lean_object* v_k_824_, lean_object* v_v_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = lean_apply_2(v_f_822_, v_k_824_, v_v_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg(lean_object* v_inst_827_, lean_object* v_f_828_, lean_object* v_t_829_){
_start:
{
lean_object* v___f_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___f_830_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_830_, 0, v_f_828_);
v___x_831_ = lean_box(0);
v___x_832_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_827_, v___f_830_, v___x_831_, v_t_829_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM(lean_object* v_00_u03b1_833_, lean_object* v_00_u03b2_834_, lean_object* v_m_835_, lean_object* v_inst_836_, lean_object* v_f_837_, lean_object* v_t_838_){
_start:
{
lean_object* v___f_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v___f_839_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_839_, 0, v_f_837_);
v___x_840_ = lean_box(0);
v___x_841_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_836_, v___f_839_, v___x_840_, v_t_838_);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0(lean_object* v_toPure_842_, lean_object* v_d_843_){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; 
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_d_843_);
v___x_845_ = lean_apply_2(v_toPure_842_, lean_box(0), v___x_844_);
return v___x_845_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2(lean_object* v___f_846_, lean_object* v_f_847_, lean_object* v_k_848_, lean_object* v_v_849_, lean_object* v_toBind_850_, lean_object* v___f_851_, lean_object* v_____do__lift_852_){
_start:
{
if (lean_obj_tag(v_____do__lift_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
lean_dec(v___f_851_);
lean_dec(v_toBind_850_);
lean_dec(v_v_849_);
lean_dec(v_k_848_);
lean_dec(v_f_847_);
v_a_853_ = lean_ctor_get(v_____do__lift_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v_____do__lift_852_, 1);
v___x_854_ = lean_apply_1(v___f_846_, v_a_853_);
return v___x_854_;
}
else
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
lean_dec(v___f_846_);
v_a_855_ = lean_ctor_get(v_____do__lift_852_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v_____do__lift_852_, 1);
v___x_856_ = lean_apply_3(v_f_847_, v_k_848_, v_v_849_, v_a_855_);
v___x_857_ = lean_apply_4(v_toBind_850_, lean_box(0), lean_box(0), v___x_856_, v___f_851_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object* v_inst_858_, lean_object* v_f_859_, lean_object* v_init_860_, lean_object* v_x_861_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_object* v_toApplicative_862_; lean_object* v_toBind_863_; lean_object* v_toPure_864_; lean_object* v_k_865_; lean_object* v_v_866_; lean_object* v_l_867_; lean_object* v_r_868_; lean_object* v___f_869_; lean_object* v___f_870_; lean_object* v___f_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_toApplicative_862_ = lean_ctor_get(v_inst_858_, 0);
v_toBind_863_ = lean_ctor_get(v_inst_858_, 1);
lean_inc_n(v_toBind_863_, 2);
v_toPure_864_ = lean_ctor_get(v_toApplicative_862_, 1);
v_k_865_ = lean_ctor_get(v_x_861_, 1);
lean_inc(v_k_865_);
v_v_866_ = lean_ctor_get(v_x_861_, 2);
lean_inc(v_v_866_);
v_l_867_ = lean_ctor_get(v_x_861_, 3);
lean_inc(v_l_867_);
v_r_868_ = lean_ctor_get(v_x_861_, 4);
lean_inc(v_r_868_);
lean_dec_ref_known(v_x_861_, 5);
lean_inc(v_toPure_864_);
v___f_869_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0), 2, 1);
lean_closure_set(v___f_869_, 0, v_toPure_864_);
lean_inc_n(v_f_859_, 2);
lean_inc_ref(v_inst_858_);
lean_inc_ref(v___f_869_);
v___f_870_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1), 5, 4);
lean_closure_set(v___f_870_, 0, v___f_869_);
lean_closure_set(v___f_870_, 1, v_inst_858_);
lean_closure_set(v___f_870_, 2, v_f_859_);
lean_closure_set(v___f_870_, 3, v_r_868_);
v___f_871_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2), 7, 6);
lean_closure_set(v___f_871_, 0, v___f_869_);
lean_closure_set(v___f_871_, 1, v_f_859_);
lean_closure_set(v___f_871_, 2, v_k_865_);
lean_closure_set(v___f_871_, 3, v_v_866_);
lean_closure_set(v___f_871_, 4, v_toBind_863_);
lean_closure_set(v___f_871_, 5, v___f_870_);
v___x_872_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_858_, v_f_859_, v_init_860_, v_l_867_);
v___x_873_ = lean_apply_4(v_toBind_863_, lean_box(0), lean_box(0), v___x_872_, v___f_871_);
return v___x_873_;
}
else
{
lean_object* v_toApplicative_874_; lean_object* v_toPure_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_toApplicative_874_ = lean_ctor_get(v_inst_858_, 0);
lean_inc_ref(v_toApplicative_874_);
lean_dec(v_f_859_);
lean_dec_ref(v_inst_858_);
v_toPure_875_ = lean_ctor_get(v_toApplicative_874_, 1);
lean_inc(v_toPure_875_);
lean_dec_ref(v_toApplicative_874_);
v___x_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_876_, 0, v_init_860_);
v___x_877_ = lean_apply_2(v_toPure_875_, lean_box(0), v___x_876_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1(lean_object* v___f_878_, lean_object* v_inst_879_, lean_object* v_f_880_, lean_object* v_r_881_, lean_object* v_____do__lift_882_){
_start:
{
if (lean_obj_tag(v_____do__lift_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; 
lean_dec(v_r_881_);
lean_dec(v_f_880_);
lean_dec_ref(v_inst_879_);
v_a_883_ = lean_ctor_get(v_____do__lift_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v_____do__lift_882_, 1);
v___x_884_ = lean_apply_1(v___f_878_, v_a_883_);
return v___x_884_;
}
else
{
lean_object* v_a_885_; lean_object* v___x_886_; 
lean_dec(v___f_878_);
v_a_885_ = lean_ctor_get(v_____do__lift_882_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v_____do__lift_882_, 1);
v___x_886_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_879_, v_f_880_, v_a_885_, v_r_881_);
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep(lean_object* v_00_u03b1_887_, lean_object* v_00_u03b2_888_, lean_object* v_00_u03b4_889_, lean_object* v_m_890_, lean_object* v_inst_891_, lean_object* v_f_892_, lean_object* v_init_893_, lean_object* v_x_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_891_, v_f_892_, v_init_893_, v_x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0(lean_object* v_toPure_896_, lean_object* v_____do__lift_897_){
_start:
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_ctor_get(v_____do__lift_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v_____do__lift_897_);
v___x_899_ = lean_apply_2(v_toPure_896_, lean_box(0), v_a_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg(lean_object* v_inst_900_, lean_object* v_f_901_, lean_object* v_init_902_, lean_object* v_t_903_){
_start:
{
lean_object* v_toApplicative_904_; lean_object* v_toBind_905_; lean_object* v_toPure_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; 
v_toApplicative_904_ = lean_ctor_get(v_inst_900_, 0);
v_toBind_905_ = lean_ctor_get(v_inst_900_, 1);
lean_inc(v_toBind_905_);
v_toPure_906_ = lean_ctor_get(v_toApplicative_904_, 1);
lean_inc(v_toPure_906_);
v___x_907_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_900_, v_f_901_, v_init_902_, v_t_903_);
v___f_908_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_908_, 0, v_toPure_906_);
v___x_909_ = lean_apply_4(v_toBind_905_, lean_box(0), lean_box(0), v___x_907_, v___f_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn(lean_object* v_00_u03b1_910_, lean_object* v_00_u03b2_911_, lean_object* v_00_u03b4_912_, lean_object* v_m_913_, lean_object* v_inst_914_, lean_object* v_f_915_, lean_object* v_init_916_, lean_object* v_t_917_){
_start:
{
lean_object* v_toApplicative_918_; lean_object* v_toBind_919_; lean_object* v_toPure_920_; lean_object* v___x_921_; lean_object* v___f_922_; lean_object* v___x_923_; 
v_toApplicative_918_ = lean_ctor_get(v_inst_914_, 0);
v_toBind_919_ = lean_ctor_get(v_inst_914_, 1);
lean_inc(v_toBind_919_);
v_toPure_920_ = lean_ctor_get(v_toApplicative_918_, 1);
lean_inc(v_toPure_920_);
v___x_921_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_914_, v_f_915_, v_init_916_, v_t_917_);
v___f_922_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_922_, 0, v_toPure_920_);
v___x_923_ = lean_apply_4(v_toBind_919_, lean_box(0), lean_box(0), v___x_921_, v___f_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_924_, lean_object* v_a_925_, lean_object* v_b_926_, lean_object* v_acc_927_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_928_, 0, v_a_925_);
lean_ctor_set(v___x_928_, 1, v_b_926_);
v___x_929_ = lean_apply_2(v_f_924_, v___x_928_, v_acc_927_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_930_, lean_object* v_00_u03b2_931_, lean_object* v_m_932_, lean_object* v_init_933_, lean_object* v_f_934_){
_start:
{
lean_object* v_toApplicative_935_; lean_object* v_toBind_936_; lean_object* v_toPure_937_; lean_object* v___f_938_; lean_object* v___x_939_; lean_object* v___f_940_; lean_object* v___x_941_; 
v_toApplicative_935_ = lean_ctor_get(v_inst_930_, 0);
v_toBind_936_ = lean_ctor_get(v_inst_930_, 1);
lean_inc(v_toBind_936_);
v_toPure_937_ = lean_ctor_get(v_toApplicative_935_, 1);
lean_inc(v_toPure_937_);
v___f_938_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_938_, 0, v_f_934_);
v___x_939_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_930_, v___f_938_, v_init_933_, v_m_932_);
v___f_940_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_940_, 0, v_toPure_937_);
v___x_941_ = lean_apply_4(v_toBind_936_, lean_box(0), lean_box(0), v___x_939_, v___f_940_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg(lean_object* v_inst_942_){
_start:
{
lean_object* v___f_943_; 
v___f_943_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_943_, 0, v_inst_942_);
return v___f_943_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad(lean_object* v_00_u03b1_944_, lean_object* v_00_u03b2_945_, lean_object* v_m_946_, lean_object* v_inst_947_){
_start:
{
lean_object* v___f_948_; 
v___f_948_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_948_, 0, v_inst_947_);
return v___f_948_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(lean_object* v_p_949_, lean_object* v___x_950_, lean_object* v___x_951_, lean_object* v_a_952_, lean_object* v_b_953_, lean_object* v_acc_954_){
_start:
{
lean_object* v___x_955_; uint8_t v___x_956_; 
v___x_955_ = lean_apply_2(v_p_949_, v_a_952_, v_b_953_);
v___x_956_ = lean_unbox(v___x_955_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; 
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_950_);
return v___x_957_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec_ref(v___x_950_);
v___x_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_958_, 0, v___x_955_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_958_);
lean_ctor_set(v___x_959_, 1, v___x_951_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed(lean_object* v_p_961_, lean_object* v___x_962_, lean_object* v___x_963_, lean_object* v_a_964_, lean_object* v_b_965_, lean_object* v_acc_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(v_p_961_, v___x_962_, v___x_963_, v_a_964_, v_b_965_, v_acc_966_);
lean_dec_ref(v_acc_966_);
return v_res_967_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any___redArg(lean_object* v_t_971_, lean_object* v_p_972_){
_start:
{
lean_object* v___y_974_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___f_982_; lean_object* v___x_983_; lean_object* v_a_984_; 
v___x_979_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_980_ = lean_box(0);
v___x_981_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_982_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_982_, 0, v_p_972_);
lean_closure_set(v___f_982_, 1, v___x_981_);
lean_closure_set(v___f_982_, 2, v___x_980_);
v___x_983_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_979_, v___f_982_, v___x_981_, v_t_971_);
v_a_984_ = lean_ctor_get(v___x_983_, 0);
lean_inc(v_a_984_);
lean_dec(v___x_983_);
v___y_974_ = v_a_984_;
goto v___jp_973_;
v___jp_973_:
{
lean_object* v_fst_975_; 
v_fst_975_ = lean_ctor_get(v___y_974_, 0);
lean_inc(v_fst_975_);
lean_dec_ref(v___y_974_);
if (lean_obj_tag(v_fst_975_) == 0)
{
uint8_t v___x_976_; 
v___x_976_ = 0;
return v___x_976_;
}
else
{
lean_object* v_val_977_; uint8_t v___x_978_; 
v_val_977_ = lean_ctor_get(v_fst_975_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_fst_975_, 1);
v___x_978_ = lean_unbox(v_val_977_);
lean_dec(v_val_977_);
return v___x_978_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___boxed(lean_object* v_t_985_, lean_object* v_p_986_){
_start:
{
uint8_t v_res_987_; lean_object* v_r_988_; 
v_res_987_ = l_Std_DTreeMap_Internal_Impl_any___redArg(v_t_985_, v_p_986_);
v_r_988_ = lean_box(v_res_987_);
return v_r_988_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_any(lean_object* v_00_u03b1_989_, lean_object* v_00_u03b2_990_, lean_object* v_t_991_, lean_object* v_p_992_){
_start:
{
lean_object* v___y_994_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v_a_1004_; 
v___x_999_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1000_ = lean_box(0);
v___x_1001_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1002_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1002_, 0, v_p_992_);
lean_closure_set(v___f_1002_, 1, v___x_1001_);
lean_closure_set(v___f_1002_, 2, v___x_1000_);
v___x_1003_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_999_, v___f_1002_, v___x_1001_, v_t_991_);
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___y_994_ = v_a_1004_;
goto v___jp_993_;
v___jp_993_:
{
lean_object* v_fst_995_; 
v_fst_995_ = lean_ctor_get(v___y_994_, 0);
lean_inc(v_fst_995_);
lean_dec_ref(v___y_994_);
if (lean_obj_tag(v_fst_995_) == 0)
{
uint8_t v___x_996_; 
v___x_996_ = 0;
return v___x_996_;
}
else
{
lean_object* v_val_997_; uint8_t v___x_998_; 
v_val_997_ = lean_ctor_get(v_fst_995_, 0);
lean_inc(v_val_997_);
lean_dec_ref_known(v_fst_995_, 1);
v___x_998_ = lean_unbox(v_val_997_);
lean_dec(v_val_997_);
return v___x_998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___boxed(lean_object* v_00_u03b1_1005_, lean_object* v_00_u03b2_1006_, lean_object* v_t_1007_, lean_object* v_p_1008_){
_start:
{
uint8_t v_res_1009_; lean_object* v_r_1010_; 
v_res_1009_ = l_Std_DTreeMap_Internal_Impl_any(v_00_u03b1_1005_, v_00_u03b2_1006_, v_t_1007_, v_p_1008_);
v_r_1010_ = lean_box(v_res_1009_);
return v_r_1010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(lean_object* v_p_1011_, lean_object* v___x_1012_, lean_object* v___x_1013_, lean_object* v_a_1014_, lean_object* v_b_1015_, lean_object* v_acc_1016_){
_start:
{
lean_object* v___x_1017_; uint8_t v___x_1018_; 
v___x_1017_ = lean_apply_2(v_p_1011_, v_a_1014_, v_b_1015_);
v___x_1018_ = lean_unbox(v___x_1017_);
if (v___x_1018_ == 0)
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; 
lean_dec_ref(v___x_1013_);
v___x_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1017_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v___x_1012_);
v___x_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
return v___x_1021_;
}
else
{
lean_object* v___x_1022_; 
v___x_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1013_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed(lean_object* v_p_1023_, lean_object* v___x_1024_, lean_object* v___x_1025_, lean_object* v_a_1026_, lean_object* v_b_1027_, lean_object* v_acc_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(v_p_1023_, v___x_1024_, v___x_1025_, v_a_1026_, v_b_1027_, v_acc_1028_);
lean_dec_ref(v_acc_1028_);
return v_res_1029_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all___redArg(lean_object* v_t_1030_, lean_object* v_p_1031_){
_start:
{
lean_object* v___y_1033_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___f_1041_; lean_object* v___x_1042_; lean_object* v_a_1043_; 
v___x_1038_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1039_ = lean_box(0);
v___x_1040_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1041_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1041_, 0, v_p_1031_);
lean_closure_set(v___f_1041_, 1, v___x_1039_);
lean_closure_set(v___f_1041_, 2, v___x_1040_);
v___x_1042_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1038_, v___f_1041_, v___x_1040_, v_t_1030_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
v___y_1033_ = v_a_1043_;
goto v___jp_1032_;
v___jp_1032_:
{
lean_object* v_fst_1034_; 
v_fst_1034_ = lean_ctor_get(v___y_1033_, 0);
lean_inc(v_fst_1034_);
lean_dec_ref(v___y_1033_);
if (lean_obj_tag(v_fst_1034_) == 0)
{
uint8_t v___x_1035_; 
v___x_1035_ = 1;
return v___x_1035_;
}
else
{
lean_object* v_val_1036_; uint8_t v___x_1037_; 
v_val_1036_ = lean_ctor_get(v_fst_1034_, 0);
lean_inc(v_val_1036_);
lean_dec_ref_known(v_fst_1034_, 1);
v___x_1037_ = lean_unbox(v_val_1036_);
lean_dec(v_val_1036_);
return v___x_1037_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___boxed(lean_object* v_t_1044_, lean_object* v_p_1045_){
_start:
{
uint8_t v_res_1046_; lean_object* v_r_1047_; 
v_res_1046_ = l_Std_DTreeMap_Internal_Impl_all___redArg(v_t_1044_, v_p_1045_);
v_r_1047_ = lean_box(v_res_1046_);
return v_r_1047_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_all(lean_object* v_00_u03b1_1048_, lean_object* v_00_u03b2_1049_, lean_object* v_t_1050_, lean_object* v_p_1051_){
_start:
{
lean_object* v___y_1053_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___f_1061_; lean_object* v___x_1062_; lean_object* v_a_1063_; 
v___x_1058_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1059_ = lean_box(0);
v___x_1060_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1061_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1061_, 0, v_p_1051_);
lean_closure_set(v___f_1061_, 1, v___x_1059_);
lean_closure_set(v___f_1061_, 2, v___x_1060_);
v___x_1062_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1058_, v___f_1061_, v___x_1060_, v_t_1050_);
v_a_1063_ = lean_ctor_get(v___x_1062_, 0);
lean_inc(v_a_1063_);
lean_dec(v___x_1062_);
v___y_1053_ = v_a_1063_;
goto v___jp_1052_;
v___jp_1052_:
{
lean_object* v_fst_1054_; 
v_fst_1054_ = lean_ctor_get(v___y_1053_, 0);
lean_inc(v_fst_1054_);
lean_dec_ref(v___y_1053_);
if (lean_obj_tag(v_fst_1054_) == 0)
{
uint8_t v___x_1055_; 
v___x_1055_ = 1;
return v___x_1055_;
}
else
{
lean_object* v_val_1056_; uint8_t v___x_1057_; 
v_val_1056_ = lean_ctor_get(v_fst_1054_, 0);
lean_inc(v_val_1056_);
lean_dec_ref_known(v_fst_1054_, 1);
v___x_1057_ = lean_unbox(v_val_1056_);
lean_dec(v_val_1056_);
return v___x_1057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___boxed(lean_object* v_00_u03b1_1064_, lean_object* v_00_u03b2_1065_, lean_object* v_t_1066_, lean_object* v_p_1067_){
_start:
{
uint8_t v_res_1068_; lean_object* v_r_1069_; 
v_res_1068_ = l_Std_DTreeMap_Internal_Impl_all(v_00_u03b1_1064_, v_00_u03b2_1065_, v_t_1066_, v_p_1067_);
v_r_1069_ = lean_box(v_res_1068_);
return v_r_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(lean_object* v_x1_1070_, lean_object* v_x2_1071_, lean_object* v_x3_1072_){
_start:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v_x1_1070_);
lean_ctor_set(v___x_1073_, 1, v_x3_1072_);
return v___x_1073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0___boxed(lean_object* v_x1_1074_, lean_object* v_x2_1075_, lean_object* v_x3_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(v_x1_1074_, v_x2_1075_, v_x3_1076_);
lean_dec(v_x2_1075_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg(lean_object* v_t_1079_){
_start:
{
lean_object* v___f_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___f_1080_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1081_ = lean_box(0);
v___x_1082_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1083_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1082_, v___f_1080_, v___x_1081_, v_t_1079_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys(lean_object* v_00_u03b1_1084_, lean_object* v_00_u03b2_1085_, lean_object* v_t_1086_){
_start:
{
lean_object* v___f_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; 
v___f_1087_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1088_ = lean_box(0);
v___x_1089_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1090_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1089_, v___f_1087_, v___x_1088_, v_t_1086_);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(lean_object* v_l_1091_, lean_object* v_k_1092_, lean_object* v_x_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_array_push(v_l_1091_, v_k_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0___boxed(lean_object* v_l_1095_, lean_object* v_k_1096_, lean_object* v_x_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(v_l_1095_, v_k_1096_, v_x_1097_);
lean_dec(v_x_1097_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg(lean_object* v_t_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___y_1103_; 
v___f_1101_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray(lean_object* v_00_u03b1_1108_, lean_object* v_00_u03b2_1109_, lean_object* v_t_1110_){
_start:
{
lean_object* v___f_1111_; lean_object* v___y_1113_; 
v___f_1111_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(lean_object* v_x1_1118_, lean_object* v_x2_1119_, lean_object* v_x3_1120_){
_start:
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1121_, 0, v_x2_1119_);
lean_ctor_set(v___x_1121_, 1, v_x3_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0___boxed(lean_object* v_x1_1122_, lean_object* v_x2_1123_, lean_object* v_x3_1124_){
_start:
{
lean_object* v_res_1125_; 
v_res_1125_ = l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(v_x1_1122_, v_x2_1123_, v_x3_1124_);
lean_dec(v_x1_1122_);
return v_res_1125_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg(lean_object* v_t_1127_){
_start:
{
lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___f_1128_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1129_ = lean_box(0);
v___x_1130_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1131_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1130_, v___f_1128_, v___x_1129_, v_t_1127_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values(lean_object* v_00_u03b1_1132_, lean_object* v_00_u03b2_1133_, lean_object* v_t_1134_){
_start:
{
lean_object* v___f_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___f_1135_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1136_ = lean_box(0);
v___x_1137_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1138_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1137_, v___f_1135_, v___x_1136_, v_t_1134_);
return v___x_1138_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(lean_object* v_l_1139_, lean_object* v_x_1140_, lean_object* v_v_1141_){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_array_push(v_l_1139_, v_v_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0___boxed(lean_object* v_l_1143_, lean_object* v_x_1144_, lean_object* v_v_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(v_l_1143_, v_x_1144_, v_v_1145_);
lean_dec(v_x_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg(lean_object* v_t_1148_){
_start:
{
lean_object* v___f_1149_; lean_object* v___y_1151_; 
v___f_1149_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1148_) == 0)
{
lean_object* v_size_1154_; 
v_size_1154_ = lean_ctor_get(v_t_1148_, 0);
lean_inc(v_size_1154_);
v___y_1151_ = v_size_1154_;
goto v___jp_1150_;
}
else
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_unsigned_to_nat(0u);
v___y_1151_ = v___x_1155_;
goto v___jp_1150_;
}
v___jp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_mk_empty_array_with_capacity(v___y_1151_);
lean_dec(v___y_1151_);
v___x_1153_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1149_, v___x_1152_, v_t_1148_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray(lean_object* v_00_u03b1_1156_, lean_object* v_00_u03b2_1157_, lean_object* v_t_1158_){
_start:
{
lean_object* v___f_1159_; lean_object* v___y_1161_; 
v___f_1159_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1158_) == 0)
{
lean_object* v_size_1164_; 
v_size_1164_ = lean_ctor_get(v_t_1158_, 0);
lean_inc(v_size_1164_);
v___y_1161_ = v_size_1164_;
goto v___jp_1160_;
}
else
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_unsigned_to_nat(0u);
v___y_1161_ = v___x_1165_;
goto v___jp_1160_;
}
v___jp_1160_:
{
lean_object* v___x_1162_; lean_object* v___x_1163_; 
v___x_1162_ = lean_mk_empty_array_with_capacity(v___y_1161_);
lean_dec(v___y_1161_);
v___x_1163_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1159_, v___x_1162_, v_t_1158_);
return v___x_1163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg___lam__0(lean_object* v_x1_1166_, lean_object* v_x2_1167_, lean_object* v_x3_1168_){
_start:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v_x1_1166_);
lean_ctor_set(v___x_1169_, 1, v_x2_1167_);
v___x_1170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v_x3_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg(lean_object* v_t_1172_){
_start:
{
lean_object* v___f_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v___f_1173_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1174_ = lean_box(0);
v___x_1175_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1176_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1175_, v___f_1173_, v___x_1174_, v_t_1172_);
return v___x_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList(lean_object* v_00_u03b1_1177_, lean_object* v_00_u03b2_1178_, lean_object* v_t_1179_){
_start:
{
lean_object* v___f_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
v___f_1180_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1181_ = lean_box(0);
v___x_1182_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1183_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1182_, v___f_1180_, v___x_1181_, v_t_1179_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg___lam__0(lean_object* v_l_1184_, lean_object* v_k_1185_, lean_object* v_v_1186_){
_start:
{
lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1187_, 0, v_k_1185_);
lean_ctor_set(v___x_1187_, 1, v_v_1186_);
v___x_1188_ = lean_array_push(v_l_1184_, v___x_1187_);
return v___x_1188_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg(lean_object* v_t_1190_){
_start:
{
lean_object* v___f_1191_; lean_object* v___y_1193_; 
v___f_1191_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1190_) == 0)
{
lean_object* v_size_1196_; 
v_size_1196_ = lean_ctor_get(v_t_1190_, 0);
lean_inc(v_size_1196_);
v___y_1193_ = v_size_1196_;
goto v___jp_1192_;
}
else
{
lean_object* v___x_1197_; 
v___x_1197_ = lean_unsigned_to_nat(0u);
v___y_1193_ = v___x_1197_;
goto v___jp_1192_;
}
v___jp_1192_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1194_ = lean_mk_empty_array_with_capacity(v___y_1193_);
lean_dec(v___y_1193_);
v___x_1195_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1191_, v___x_1194_, v_t_1190_);
return v___x_1195_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray(lean_object* v_00_u03b1_1198_, lean_object* v_00_u03b2_1199_, lean_object* v_t_1200_){
_start:
{
lean_object* v___f_1201_; lean_object* v___y_1203_; 
v___f_1201_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1200_) == 0)
{
lean_object* v_size_1206_; 
v_size_1206_ = lean_ctor_get(v_t_1200_, 0);
lean_inc(v_size_1206_);
v___y_1203_ = v_size_1206_;
goto v___jp_1202_;
}
else
{
lean_object* v___x_1207_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
v___y_1203_ = v___x_1207_;
goto v___jp_1202_;
}
v___jp_1202_:
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1204_ = lean_mk_empty_array_with_capacity(v___y_1203_);
lean_dec(v___y_1203_);
v___x_1205_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1201_, v___x_1204_, v_t_1200_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___lam__0(lean_object* v_x1_1208_, lean_object* v_x2_1209_, lean_object* v_x3_1210_){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1211_, 0, v_x1_1208_);
lean_ctor_set(v___x_1211_, 1, v_x2_1209_);
v___x_1212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1211_);
lean_ctor_set(v___x_1212_, 1, v_x3_1210_);
return v___x_1212_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg(lean_object* v_t_1214_){
_start:
{
lean_object* v___f_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; 
v___f_1215_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1216_ = lean_box(0);
v___x_1217_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1218_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1217_, v___f_1215_, v___x_1216_, v_t_1214_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList(lean_object* v_00_u03b1_1219_, lean_object* v_00_u03b2_1220_, lean_object* v_t_1221_){
_start:
{
lean_object* v___f_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___f_1222_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1223_ = lean_box(0);
v___x_1224_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1225_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1224_, v___f_1222_, v___x_1223_, v_t_1221_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___lam__0(lean_object* v_l_1226_, lean_object* v_k_1227_, lean_object* v_v_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v_k_1227_);
lean_ctor_set(v___x_1229_, 1, v_v_1228_);
v___x_1230_ = lean_array_push(v_l_1226_, v___x_1229_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg(lean_object* v_t_1232_){
_start:
{
lean_object* v___f_1233_; lean_object* v___y_1235_; 
v___f_1233_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1232_) == 0)
{
lean_object* v_size_1238_; 
v_size_1238_ = lean_ctor_get(v_t_1232_, 0);
lean_inc(v_size_1238_);
v___y_1235_ = v_size_1238_;
goto v___jp_1234_;
}
else
{
lean_object* v___x_1239_; 
v___x_1239_ = lean_unsigned_to_nat(0u);
v___y_1235_ = v___x_1239_;
goto v___jp_1234_;
}
v___jp_1234_:
{
lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1236_ = lean_mk_empty_array_with_capacity(v___y_1235_);
lean_dec(v___y_1235_);
v___x_1237_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1233_, v___x_1236_, v_t_1232_);
return v___x_1237_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray(lean_object* v_00_u03b1_1240_, lean_object* v_00_u03b2_1241_, lean_object* v_t_1242_){
_start:
{
lean_object* v___f_1243_; lean_object* v___y_1245_; 
v___f_1243_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1242_) == 0)
{
lean_object* v_size_1248_; 
v_size_1248_ = lean_ctor_get(v_t_1242_, 0);
lean_inc(v_size_1248_);
v___y_1245_ = v_size_1248_;
goto v___jp_1244_;
}
else
{
lean_object* v___x_1249_; 
v___x_1249_ = lean_unsigned_to_nat(0u);
v___y_1245_ = v___x_1249_;
goto v___jp_1244_;
}
v___jp_1244_:
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_mk_empty_array_with_capacity(v___y_1245_);
lean_dec(v___y_1245_);
v___x_1247_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1243_, v___x_1246_, v_t_1242_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object* v_x_1250_){
_start:
{
if (lean_obj_tag(v_x_1250_) == 0)
{
lean_object* v_l_1251_; 
v_l_1251_ = lean_ctor_get(v_x_1250_, 3);
if (lean_obj_tag(v_l_1251_) == 0)
{
v_x_1250_ = v_l_1251_;
goto _start;
}
else
{
lean_object* v_k_1253_; lean_object* v_v_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v_k_1253_ = lean_ctor_get(v_x_1250_, 1);
v_v_1254_ = lean_ctor_get(v_x_1250_, 2);
lean_inc(v_v_1254_);
lean_inc(v_k_1253_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_k_1253_);
lean_ctor_set(v___x_1255_, 1, v_v_1254_);
v___x_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1255_);
return v___x_1256_;
}
}
else
{
lean_object* v___x_1257_; 
v___x_1257_ = lean_box(0);
return v___x_1257_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg___boxed(lean_object* v_x_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1258_);
lean_dec(v_x_1258_);
return v_res_1259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f(lean_object* v_00_u03b1_1260_, lean_object* v_00_u03b2_1261_, lean_object* v_x_1262_){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1262_);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___boxed(lean_object* v_00_u03b1_1264_, lean_object* v_00_u03b2_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f(v_00_u03b1_1264_, v_00_u03b2_1265_, v_x_1266_);
lean_dec(v_x_1266_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1268_, lean_object* v_h__1_1269_, lean_object* v_h__2_1270_, lean_object* v_h__3_1271_){
_start:
{
if (lean_obj_tag(v_x_1268_) == 0)
{
lean_object* v_l_1272_; 
lean_dec(v_h__1_1269_);
v_l_1272_ = lean_ctor_get(v_x_1268_, 3);
if (lean_obj_tag(v_l_1272_) == 0)
{
lean_object* v_size_1273_; lean_object* v_k_1274_; lean_object* v_v_1275_; lean_object* v_r_1276_; lean_object* v_size_1277_; lean_object* v_k_1278_; lean_object* v_v_1279_; lean_object* v_l_1280_; lean_object* v_r_1281_; lean_object* v___x_1282_; 
lean_inc_ref(v_l_1272_);
lean_dec(v_h__2_1270_);
v_size_1273_ = lean_ctor_get(v_x_1268_, 0);
lean_inc(v_size_1273_);
v_k_1274_ = lean_ctor_get(v_x_1268_, 1);
lean_inc(v_k_1274_);
v_v_1275_ = lean_ctor_get(v_x_1268_, 2);
lean_inc(v_v_1275_);
v_r_1276_ = lean_ctor_get(v_x_1268_, 4);
lean_inc(v_r_1276_);
lean_dec_ref_known(v_x_1268_, 5);
v_size_1277_ = lean_ctor_get(v_l_1272_, 0);
lean_inc(v_size_1277_);
v_k_1278_ = lean_ctor_get(v_l_1272_, 1);
lean_inc(v_k_1278_);
v_v_1279_ = lean_ctor_get(v_l_1272_, 2);
lean_inc(v_v_1279_);
v_l_1280_ = lean_ctor_get(v_l_1272_, 3);
lean_inc(v_l_1280_);
v_r_1281_ = lean_ctor_get(v_l_1272_, 4);
lean_inc(v_r_1281_);
lean_dec_ref_known(v_l_1272_, 5);
v___x_1282_ = lean_apply_9(v_h__3_1271_, v_size_1273_, v_k_1274_, v_v_1275_, v_size_1277_, v_k_1278_, v_v_1279_, v_l_1280_, v_r_1281_, v_r_1276_);
return v___x_1282_;
}
else
{
lean_object* v_size_1283_; lean_object* v_k_1284_; lean_object* v_v_1285_; lean_object* v_r_1286_; lean_object* v___x_1287_; 
lean_dec(v_h__3_1271_);
v_size_1283_ = lean_ctor_get(v_x_1268_, 0);
lean_inc(v_size_1283_);
v_k_1284_ = lean_ctor_get(v_x_1268_, 1);
lean_inc(v_k_1284_);
v_v_1285_ = lean_ctor_get(v_x_1268_, 2);
lean_inc(v_v_1285_);
v_r_1286_ = lean_ctor_get(v_x_1268_, 4);
lean_inc(v_r_1286_);
lean_dec_ref_known(v_x_1268_, 5);
v___x_1287_ = lean_apply_4(v_h__2_1270_, v_size_1283_, v_k_1284_, v_v_1285_, v_r_1286_);
return v___x_1287_;
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
lean_dec(v_h__3_1271_);
lean_dec(v_h__2_1270_);
v___x_1288_ = lean_box(0);
v___x_1289_ = lean_apply_1(v_h__1_1269_, v___x_1288_);
return v___x_1289_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1290_, lean_object* v_00_u03b2_1291_, lean_object* v_motive_1292_, lean_object* v_x_1293_, lean_object* v_h__1_1294_, lean_object* v_h__2_1295_, lean_object* v_h__3_1296_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg(lean_object* v_x_1315_){
_start:
{
lean_object* v_l_1316_; 
v_l_1316_ = lean_ctor_get(v_x_1315_, 3);
if (lean_obj_tag(v_l_1316_) == 0)
{
v_x_1315_ = v_l_1316_;
goto _start;
}
else
{
lean_object* v_k_1318_; lean_object* v_v_1319_; lean_object* v___x_1320_; 
v_k_1318_ = lean_ctor_get(v_x_1315_, 1);
v_v_1319_ = lean_ctor_get(v_x_1315_, 2);
lean_inc(v_v_1319_);
lean_inc(v_k_1318_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v_k_1318_);
lean_ctor_set(v___x_1320_, 1, v_v_1319_);
return v___x_1320_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg___boxed(lean_object* v_x_1321_){
_start:
{
lean_object* v_res_1322_; 
v_res_1322_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1321_);
lean_dec(v_x_1321_);
return v_res_1322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry(lean_object* v_00_u03b1_1323_, lean_object* v_00_u03b2_1324_, lean_object* v_x_1325_, lean_object* v_x_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1325_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___boxed(lean_object* v_00_u03b1_1328_, lean_object* v_00_u03b2_1329_, lean_object* v_x_1330_, lean_object* v_x_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_Std_DTreeMap_Internal_Impl_minEntry(v_00_u03b1_1328_, v_00_u03b2_1329_, v_x_1330_, v_x_1331_);
lean_dec(v_x_1330_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1333_, lean_object* v_h__1_1334_, lean_object* v_h__2_1335_){
_start:
{
lean_object* v_l_1336_; 
v_l_1336_ = lean_ctor_get(v_x_1333_, 3);
if (lean_obj_tag(v_l_1336_) == 0)
{
lean_object* v_size_1337_; lean_object* v_k_1338_; lean_object* v_v_1339_; lean_object* v_r_1340_; lean_object* v_size_1341_; lean_object* v_k_1342_; lean_object* v_v_1343_; lean_object* v_l_1344_; lean_object* v_r_1345_; lean_object* v___x_1346_; 
lean_inc_ref(v_l_1336_);
lean_dec(v_h__1_1334_);
v_size_1337_ = lean_ctor_get(v_x_1333_, 0);
lean_inc(v_size_1337_);
v_k_1338_ = lean_ctor_get(v_x_1333_, 1);
lean_inc(v_k_1338_);
v_v_1339_ = lean_ctor_get(v_x_1333_, 2);
lean_inc(v_v_1339_);
v_r_1340_ = lean_ctor_get(v_x_1333_, 4);
lean_inc(v_r_1340_);
lean_dec(v_x_1333_);
v_size_1341_ = lean_ctor_get(v_l_1336_, 0);
lean_inc(v_size_1341_);
v_k_1342_ = lean_ctor_get(v_l_1336_, 1);
lean_inc(v_k_1342_);
v_v_1343_ = lean_ctor_get(v_l_1336_, 2);
lean_inc(v_v_1343_);
v_l_1344_ = lean_ctor_get(v_l_1336_, 3);
lean_inc(v_l_1344_);
v_r_1345_ = lean_ctor_get(v_l_1336_, 4);
lean_inc(v_r_1345_);
lean_dec_ref_known(v_l_1336_, 5);
v___x_1346_ = lean_apply_10(v_h__2_1335_, v_size_1337_, v_k_1338_, v_v_1339_, v_size_1341_, v_k_1342_, v_v_1343_, v_l_1344_, v_r_1345_, v_r_1340_, lean_box(0));
return v___x_1346_;
}
else
{
lean_object* v_size_1347_; lean_object* v_k_1348_; lean_object* v_v_1349_; lean_object* v_r_1350_; lean_object* v___x_1351_; 
lean_dec(v_h__2_1335_);
v_size_1347_ = lean_ctor_get(v_x_1333_, 0);
lean_inc(v_size_1347_);
v_k_1348_ = lean_ctor_get(v_x_1333_, 1);
lean_inc(v_k_1348_);
v_v_1349_ = lean_ctor_get(v_x_1333_, 2);
lean_inc(v_v_1349_);
v_r_1350_ = lean_ctor_get(v_x_1333_, 4);
lean_inc(v_r_1350_);
lean_dec(v_x_1333_);
v___x_1351_ = lean_apply_5(v_h__1_1334_, v_size_1347_, v_k_1348_, v_v_1349_, v_r_1350_, lean_box(0));
return v___x_1351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1352_, lean_object* v_00_u03b2_1353_, lean_object* v_motive_1354_, lean_object* v_x_1355_, lean_object* v_x_1356_, lean_object* v_h__1_1357_, lean_object* v_h__2_1358_){
_start:
{
lean_object* v_l_1359_; 
v_l_1359_ = lean_ctor_get(v_x_1355_, 3);
if (lean_obj_tag(v_l_1359_) == 0)
{
lean_object* v_size_1360_; lean_object* v_k_1361_; lean_object* v_v_1362_; lean_object* v_r_1363_; lean_object* v_size_1364_; lean_object* v_k_1365_; lean_object* v_v_1366_; lean_object* v_l_1367_; lean_object* v_r_1368_; lean_object* v___x_1369_; 
lean_inc_ref(v_l_1359_);
lean_dec(v_h__1_1357_);
v_size_1360_ = lean_ctor_get(v_x_1355_, 0);
lean_inc(v_size_1360_);
v_k_1361_ = lean_ctor_get(v_x_1355_, 1);
lean_inc(v_k_1361_);
v_v_1362_ = lean_ctor_get(v_x_1355_, 2);
lean_inc(v_v_1362_);
v_r_1363_ = lean_ctor_get(v_x_1355_, 4);
lean_inc(v_r_1363_);
lean_dec(v_x_1355_);
v_size_1364_ = lean_ctor_get(v_l_1359_, 0);
lean_inc(v_size_1364_);
v_k_1365_ = lean_ctor_get(v_l_1359_, 1);
lean_inc(v_k_1365_);
v_v_1366_ = lean_ctor_get(v_l_1359_, 2);
lean_inc(v_v_1366_);
v_l_1367_ = lean_ctor_get(v_l_1359_, 3);
lean_inc(v_l_1367_);
v_r_1368_ = lean_ctor_get(v_l_1359_, 4);
lean_inc(v_r_1368_);
lean_dec_ref_known(v_l_1359_, 5);
v___x_1369_ = lean_apply_10(v_h__2_1358_, v_size_1360_, v_k_1361_, v_v_1362_, v_size_1364_, v_k_1365_, v_v_1366_, v_l_1367_, v_r_1368_, v_r_1363_, lean_box(0));
return v___x_1369_;
}
else
{
lean_object* v_size_1370_; lean_object* v_k_1371_; lean_object* v_v_1372_; lean_object* v_r_1373_; lean_object* v___x_1374_; 
lean_dec(v_h__2_1358_);
v_size_1370_ = lean_ctor_get(v_x_1355_, 0);
lean_inc(v_size_1370_);
v_k_1371_ = lean_ctor_get(v_x_1355_, 1);
lean_inc(v_k_1371_);
v_v_1372_ = lean_ctor_get(v_x_1355_, 2);
lean_inc(v_v_1372_);
v_r_1373_ = lean_ctor_get(v_x_1355_, 4);
lean_inc(v_r_1373_);
lean_dec(v_x_1355_);
v___x_1374_ = lean_apply_5(v_h__1_1357_, v_size_1370_, v_k_1371_, v_v_1372_, v_r_1373_, lean_box(0));
return v___x_1374_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1377_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1378_ = lean_unsigned_to_nat(13u);
v___x_1379_ = lean_unsigned_to_nat(367u);
v___x_1380_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0));
v___x_1381_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1382_ = l_mkPanicMessageWithDecl(v___x_1381_, v___x_1380_, v___x_1379_, v___x_1378_, v___x_1377_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object* v_inst_1383_, lean_object* v_x_1384_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_object* v_l_1385_; 
v_l_1385_ = lean_ctor_get(v_x_1384_, 3);
if (lean_obj_tag(v_l_1385_) == 0)
{
v_x_1384_ = v_l_1385_;
goto _start;
}
else
{
lean_object* v_k_1387_; lean_object* v_v_1388_; lean_object* v___x_1389_; 
v_k_1387_ = lean_ctor_get(v_x_1384_, 1);
v_v_1388_ = lean_ctor_get(v_x_1384_, 2);
lean_inc(v_v_1388_);
lean_inc(v_k_1387_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_k_1387_);
lean_ctor_set(v___x_1389_, 1, v_v_1388_);
return v___x_1389_;
}
}
else
{
lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1390_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2);
v___x_1391_ = l_panic___redArg(v_inst_1383_, v___x_1390_);
return v___x_1391_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___boxed(lean_object* v_inst_1392_, lean_object* v_x_1393_){
_start:
{
lean_object* v_res_1394_; 
v_res_1394_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1392_, v_x_1393_);
lean_dec(v_x_1393_);
lean_dec_ref(v_inst_1392_);
return v_res_1394_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21(lean_object* v_00_u03b1_1395_, lean_object* v_00_u03b2_1396_, lean_object* v_inst_1397_, lean_object* v_x_1398_){
_start:
{
lean_object* v___x_1399_; 
v___x_1399_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1397_, v_x_1398_);
return v___x_1399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___boxed(lean_object* v_00_u03b1_1400_, lean_object* v_00_u03b2_1401_, lean_object* v_inst_1402_, lean_object* v_x_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21(v_00_u03b1_1400_, v_00_u03b2_1401_, v_inst_1402_, v_x_1403_);
lean_dec(v_x_1403_);
lean_dec_ref(v_inst_1402_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object* v_x_1405_, lean_object* v_x_1406_){
_start:
{
if (lean_obj_tag(v_x_1405_) == 0)
{
lean_object* v_l_1407_; 
v_l_1407_ = lean_ctor_get(v_x_1405_, 3);
if (lean_obj_tag(v_l_1407_) == 0)
{
v_x_1405_ = v_l_1407_;
goto _start;
}
else
{
lean_object* v_k_1409_; lean_object* v_v_1410_; lean_object* v___x_1411_; 
v_k_1409_ = lean_ctor_get(v_x_1405_, 1);
v_v_1410_ = lean_ctor_get(v_x_1405_, 2);
lean_inc(v_v_1410_);
lean_inc(v_k_1409_);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_k_1409_);
lean_ctor_set(v___x_1411_, 1, v_v_1410_);
return v___x_1411_;
}
}
else
{
lean_inc_ref(v_x_1406_);
return v_x_1406_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg___boxed(lean_object* v_x_1412_, lean_object* v_x_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1412_, v_x_1413_);
lean_dec_ref(v_x_1413_);
lean_dec(v_x_1412_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD(lean_object* v_00_u03b1_1415_, lean_object* v_00_u03b2_1416_, lean_object* v_x_1417_, lean_object* v_x_1418_){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1417_, v_x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___boxed(lean_object* v_00_u03b1_1420_, lean_object* v_00_u03b2_1421_, lean_object* v_x_1422_, lean_object* v_x_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Std_DTreeMap_Internal_Impl_minEntryD(v_00_u03b1_1420_, v_00_u03b2_1421_, v_x_1422_, v_x_1423_);
lean_dec_ref(v_x_1423_);
lean_dec(v_x_1422_);
return v_res_1424_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1425_, lean_object* v_x_1426_, lean_object* v_h__1_1427_, lean_object* v_h__2_1428_, lean_object* v_h__3_1429_){
_start:
{
if (lean_obj_tag(v_x_1425_) == 0)
{
lean_object* v_l_1430_; 
lean_dec(v_h__1_1427_);
v_l_1430_ = lean_ctor_get(v_x_1425_, 3);
if (lean_obj_tag(v_l_1430_) == 0)
{
lean_object* v_size_1431_; lean_object* v_k_1432_; lean_object* v_v_1433_; lean_object* v_r_1434_; lean_object* v_size_1435_; lean_object* v_k_1436_; lean_object* v_v_1437_; lean_object* v_l_1438_; lean_object* v_r_1439_; lean_object* v___x_1440_; 
lean_inc_ref(v_l_1430_);
lean_dec(v_h__2_1428_);
v_size_1431_ = lean_ctor_get(v_x_1425_, 0);
lean_inc(v_size_1431_);
v_k_1432_ = lean_ctor_get(v_x_1425_, 1);
lean_inc(v_k_1432_);
v_v_1433_ = lean_ctor_get(v_x_1425_, 2);
lean_inc(v_v_1433_);
v_r_1434_ = lean_ctor_get(v_x_1425_, 4);
lean_inc(v_r_1434_);
lean_dec_ref_known(v_x_1425_, 5);
v_size_1435_ = lean_ctor_get(v_l_1430_, 0);
lean_inc(v_size_1435_);
v_k_1436_ = lean_ctor_get(v_l_1430_, 1);
lean_inc(v_k_1436_);
v_v_1437_ = lean_ctor_get(v_l_1430_, 2);
lean_inc(v_v_1437_);
v_l_1438_ = lean_ctor_get(v_l_1430_, 3);
lean_inc(v_l_1438_);
v_r_1439_ = lean_ctor_get(v_l_1430_, 4);
lean_inc(v_r_1439_);
lean_dec_ref_known(v_l_1430_, 5);
v___x_1440_ = lean_apply_10(v_h__3_1429_, v_size_1431_, v_k_1432_, v_v_1433_, v_size_1435_, v_k_1436_, v_v_1437_, v_l_1438_, v_r_1439_, v_r_1434_, v_x_1426_);
return v___x_1440_;
}
else
{
lean_object* v_size_1441_; lean_object* v_k_1442_; lean_object* v_v_1443_; lean_object* v_r_1444_; lean_object* v___x_1445_; 
lean_dec(v_h__3_1429_);
v_size_1441_ = lean_ctor_get(v_x_1425_, 0);
lean_inc(v_size_1441_);
v_k_1442_ = lean_ctor_get(v_x_1425_, 1);
lean_inc(v_k_1442_);
v_v_1443_ = lean_ctor_get(v_x_1425_, 2);
lean_inc(v_v_1443_);
v_r_1444_ = lean_ctor_get(v_x_1425_, 4);
lean_inc(v_r_1444_);
lean_dec_ref_known(v_x_1425_, 5);
v___x_1445_ = lean_apply_5(v_h__2_1428_, v_size_1441_, v_k_1442_, v_v_1443_, v_r_1444_, v_x_1426_);
return v___x_1445_;
}
}
else
{
lean_object* v___x_1446_; 
lean_dec(v_h__3_1429_);
lean_dec(v_h__2_1428_);
v___x_1446_ = lean_apply_1(v_h__1_1427_, v_x_1426_);
return v___x_1446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1447_, lean_object* v_00_u03b2_1448_, lean_object* v_motive_1449_, lean_object* v_x_1450_, lean_object* v_x_1451_, lean_object* v_h__1_1452_, lean_object* v_h__2_1453_, lean_object* v_h__3_1454_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object* v_x_1472_){
_start:
{
if (lean_obj_tag(v_x_1472_) == 0)
{
lean_object* v_r_1473_; 
v_r_1473_ = lean_ctor_get(v_x_1472_, 4);
if (lean_obj_tag(v_r_1473_) == 0)
{
v_x_1472_ = v_r_1473_;
goto _start;
}
else
{
lean_object* v_k_1475_; lean_object* v_v_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_k_1475_ = lean_ctor_get(v_x_1472_, 1);
v_v_1476_ = lean_ctor_get(v_x_1472_, 2);
lean_inc(v_v_1476_);
lean_inc(v_k_1475_);
v___x_1477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1477_, 0, v_k_1475_);
lean_ctor_set(v___x_1477_, 1, v_v_1476_);
v___x_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
else
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_box(0);
return v___x_1479_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg___boxed(lean_object* v_x_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1480_);
lean_dec(v_x_1480_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(lean_object* v_00_u03b1_1482_, lean_object* v_00_u03b2_1483_, lean_object* v_x_1484_){
_start:
{
lean_object* v___x_1485_; 
v___x_1485_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1484_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1486_, lean_object* v_00_u03b2_1487_, lean_object* v_x_1488_){
_start:
{
lean_object* v_res_1489_; 
v_res_1489_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(v_00_u03b1_1486_, v_00_u03b2_1487_, v_x_1488_);
lean_dec(v_x_1488_);
return v_res_1489_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1490_, lean_object* v_h__1_1491_, lean_object* v_h__2_1492_, lean_object* v_h__3_1493_){
_start:
{
if (lean_obj_tag(v_x_1490_) == 0)
{
lean_object* v_r_1494_; 
lean_dec(v_h__1_1491_);
v_r_1494_ = lean_ctor_get(v_x_1490_, 4);
if (lean_obj_tag(v_r_1494_) == 0)
{
lean_object* v_size_1495_; lean_object* v_k_1496_; lean_object* v_v_1497_; lean_object* v_l_1498_; lean_object* v_size_1499_; lean_object* v_k_1500_; lean_object* v_v_1501_; lean_object* v_l_1502_; lean_object* v_r_1503_; lean_object* v___x_1504_; 
lean_inc_ref(v_r_1494_);
lean_dec(v_h__2_1492_);
v_size_1495_ = lean_ctor_get(v_x_1490_, 0);
lean_inc(v_size_1495_);
v_k_1496_ = lean_ctor_get(v_x_1490_, 1);
lean_inc(v_k_1496_);
v_v_1497_ = lean_ctor_get(v_x_1490_, 2);
lean_inc(v_v_1497_);
v_l_1498_ = lean_ctor_get(v_x_1490_, 3);
lean_inc(v_l_1498_);
lean_dec_ref_known(v_x_1490_, 5);
v_size_1499_ = lean_ctor_get(v_r_1494_, 0);
lean_inc(v_size_1499_);
v_k_1500_ = lean_ctor_get(v_r_1494_, 1);
lean_inc(v_k_1500_);
v_v_1501_ = lean_ctor_get(v_r_1494_, 2);
lean_inc(v_v_1501_);
v_l_1502_ = lean_ctor_get(v_r_1494_, 3);
lean_inc(v_l_1502_);
v_r_1503_ = lean_ctor_get(v_r_1494_, 4);
lean_inc(v_r_1503_);
lean_dec_ref_known(v_r_1494_, 5);
v___x_1504_ = lean_apply_9(v_h__3_1493_, v_size_1495_, v_k_1496_, v_v_1497_, v_l_1498_, v_size_1499_, v_k_1500_, v_v_1501_, v_l_1502_, v_r_1503_);
return v___x_1504_;
}
else
{
lean_object* v_size_1505_; lean_object* v_k_1506_; lean_object* v_v_1507_; lean_object* v_l_1508_; lean_object* v___x_1509_; 
lean_dec(v_h__3_1493_);
v_size_1505_ = lean_ctor_get(v_x_1490_, 0);
lean_inc(v_size_1505_);
v_k_1506_ = lean_ctor_get(v_x_1490_, 1);
lean_inc(v_k_1506_);
v_v_1507_ = lean_ctor_get(v_x_1490_, 2);
lean_inc(v_v_1507_);
v_l_1508_ = lean_ctor_get(v_x_1490_, 3);
lean_inc(v_l_1508_);
lean_dec_ref_known(v_x_1490_, 5);
v___x_1509_ = lean_apply_4(v_h__2_1492_, v_size_1505_, v_k_1506_, v_v_1507_, v_l_1508_);
return v___x_1509_;
}
}
else
{
lean_object* v___x_1510_; lean_object* v___x_1511_; 
lean_dec(v_h__3_1493_);
lean_dec(v_h__2_1492_);
v___x_1510_ = lean_box(0);
v___x_1511_ = lean_apply_1(v_h__1_1491_, v___x_1510_);
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1512_, lean_object* v_00_u03b2_1513_, lean_object* v_motive_1514_, lean_object* v_x_1515_, lean_object* v_h__1_1516_, lean_object* v_h__2_1517_, lean_object* v_h__3_1518_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object* v_x_1537_){
_start:
{
lean_object* v_r_1538_; 
v_r_1538_ = lean_ctor_get(v_x_1537_, 4);
if (lean_obj_tag(v_r_1538_) == 0)
{
v_x_1537_ = v_r_1538_;
goto _start;
}
else
{
lean_object* v_k_1540_; lean_object* v_v_1541_; lean_object* v___x_1542_; 
v_k_1540_ = lean_ctor_get(v_x_1537_, 1);
v_v_1541_ = lean_ctor_get(v_x_1537_, 2);
lean_inc(v_v_1541_);
lean_inc(v_k_1540_);
v___x_1542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1542_, 0, v_k_1540_);
lean_ctor_set(v___x_1542_, 1, v_v_1541_);
return v___x_1542_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg___boxed(lean_object* v_x_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1543_);
lean_dec(v_x_1543_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry(lean_object* v_00_u03b1_1545_, lean_object* v_00_u03b2_1546_, lean_object* v_x_1547_, lean_object* v_x_1548_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___boxed(lean_object* v_00_u03b1_1550_, lean_object* v_00_u03b2_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Std_DTreeMap_Internal_Impl_maxEntry(v_00_u03b1_1550_, v_00_u03b2_1551_, v_x_1552_, v_x_1553_);
lean_dec(v_x_1552_);
return v_res_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1555_, lean_object* v_h__1_1556_, lean_object* v_h__2_1557_){
_start:
{
lean_object* v_r_1558_; 
v_r_1558_ = lean_ctor_get(v_x_1555_, 4);
if (lean_obj_tag(v_r_1558_) == 0)
{
lean_object* v_size_1559_; lean_object* v_k_1560_; lean_object* v_v_1561_; lean_object* v_l_1562_; lean_object* v_size_1563_; lean_object* v_k_1564_; lean_object* v_v_1565_; lean_object* v_l_1566_; lean_object* v_r_1567_; lean_object* v___x_1568_; 
lean_inc_ref(v_r_1558_);
lean_dec(v_h__1_1556_);
v_size_1559_ = lean_ctor_get(v_x_1555_, 0);
lean_inc(v_size_1559_);
v_k_1560_ = lean_ctor_get(v_x_1555_, 1);
lean_inc(v_k_1560_);
v_v_1561_ = lean_ctor_get(v_x_1555_, 2);
lean_inc(v_v_1561_);
v_l_1562_ = lean_ctor_get(v_x_1555_, 3);
lean_inc(v_l_1562_);
lean_dec(v_x_1555_);
v_size_1563_ = lean_ctor_get(v_r_1558_, 0);
lean_inc(v_size_1563_);
v_k_1564_ = lean_ctor_get(v_r_1558_, 1);
lean_inc(v_k_1564_);
v_v_1565_ = lean_ctor_get(v_r_1558_, 2);
lean_inc(v_v_1565_);
v_l_1566_ = lean_ctor_get(v_r_1558_, 3);
lean_inc(v_l_1566_);
v_r_1567_ = lean_ctor_get(v_r_1558_, 4);
lean_inc(v_r_1567_);
lean_dec_ref_known(v_r_1558_, 5);
v___x_1568_ = lean_apply_10(v_h__2_1557_, v_size_1559_, v_k_1560_, v_v_1561_, v_l_1562_, v_size_1563_, v_k_1564_, v_v_1565_, v_l_1566_, v_r_1567_, lean_box(0));
return v___x_1568_;
}
else
{
lean_object* v_size_1569_; lean_object* v_k_1570_; lean_object* v_v_1571_; lean_object* v_l_1572_; lean_object* v___x_1573_; 
lean_dec(v_h__2_1557_);
v_size_1569_ = lean_ctor_get(v_x_1555_, 0);
lean_inc(v_size_1569_);
v_k_1570_ = lean_ctor_get(v_x_1555_, 1);
lean_inc(v_k_1570_);
v_v_1571_ = lean_ctor_get(v_x_1555_, 2);
lean_inc(v_v_1571_);
v_l_1572_ = lean_ctor_get(v_x_1555_, 3);
lean_inc(v_l_1572_);
lean_dec(v_x_1555_);
v___x_1573_ = lean_apply_5(v_h__1_1556_, v_size_1569_, v_k_1570_, v_v_1571_, v_l_1572_, lean_box(0));
return v___x_1573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1574_, lean_object* v_00_u03b2_1575_, lean_object* v_motive_1576_, lean_object* v_x_1577_, lean_object* v_x_1578_, lean_object* v_h__1_1579_, lean_object* v_h__2_1580_){
_start:
{
lean_object* v_r_1581_; 
v_r_1581_ = lean_ctor_get(v_x_1577_, 4);
if (lean_obj_tag(v_r_1581_) == 0)
{
lean_object* v_size_1582_; lean_object* v_k_1583_; lean_object* v_v_1584_; lean_object* v_l_1585_; lean_object* v_size_1586_; lean_object* v_k_1587_; lean_object* v_v_1588_; lean_object* v_l_1589_; lean_object* v_r_1590_; lean_object* v___x_1591_; 
lean_inc_ref(v_r_1581_);
lean_dec(v_h__1_1579_);
v_size_1582_ = lean_ctor_get(v_x_1577_, 0);
lean_inc(v_size_1582_);
v_k_1583_ = lean_ctor_get(v_x_1577_, 1);
lean_inc(v_k_1583_);
v_v_1584_ = lean_ctor_get(v_x_1577_, 2);
lean_inc(v_v_1584_);
v_l_1585_ = lean_ctor_get(v_x_1577_, 3);
lean_inc(v_l_1585_);
lean_dec(v_x_1577_);
v_size_1586_ = lean_ctor_get(v_r_1581_, 0);
lean_inc(v_size_1586_);
v_k_1587_ = lean_ctor_get(v_r_1581_, 1);
lean_inc(v_k_1587_);
v_v_1588_ = lean_ctor_get(v_r_1581_, 2);
lean_inc(v_v_1588_);
v_l_1589_ = lean_ctor_get(v_r_1581_, 3);
lean_inc(v_l_1589_);
v_r_1590_ = lean_ctor_get(v_r_1581_, 4);
lean_inc(v_r_1590_);
lean_dec_ref_known(v_r_1581_, 5);
v___x_1591_ = lean_apply_10(v_h__2_1580_, v_size_1582_, v_k_1583_, v_v_1584_, v_l_1585_, v_size_1586_, v_k_1587_, v_v_1588_, v_l_1589_, v_r_1590_, lean_box(0));
return v___x_1591_;
}
else
{
lean_object* v_size_1592_; lean_object* v_k_1593_; lean_object* v_v_1594_; lean_object* v_l_1595_; lean_object* v___x_1596_; 
lean_dec(v_h__2_1580_);
v_size_1592_ = lean_ctor_get(v_x_1577_, 0);
lean_inc(v_size_1592_);
v_k_1593_ = lean_ctor_get(v_x_1577_, 1);
lean_inc(v_k_1593_);
v_v_1594_ = lean_ctor_get(v_x_1577_, 2);
lean_inc(v_v_1594_);
v_l_1595_ = lean_ctor_get(v_x_1577_, 3);
lean_inc(v_l_1595_);
lean_dec(v_x_1577_);
v___x_1596_ = lean_apply_5(v_h__1_1579_, v_size_1592_, v_k_1593_, v_v_1594_, v_l_1595_, lean_box(0));
return v___x_1596_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1598_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1599_ = lean_unsigned_to_nat(13u);
v___x_1600_ = lean_unsigned_to_nat(390u);
v___x_1601_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0));
v___x_1602_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1603_ = l_mkPanicMessageWithDecl(v___x_1602_, v___x_1601_, v___x_1600_, v___x_1599_, v___x_1598_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object* v_inst_1604_, lean_object* v_x_1605_){
_start:
{
if (lean_obj_tag(v_x_1605_) == 0)
{
lean_object* v_r_1606_; 
v_r_1606_ = lean_ctor_get(v_x_1605_, 4);
if (lean_obj_tag(v_r_1606_) == 0)
{
v_x_1605_ = v_r_1606_;
goto _start;
}
else
{
lean_object* v_k_1608_; lean_object* v_v_1609_; lean_object* v___x_1610_; 
v_k_1608_ = lean_ctor_get(v_x_1605_, 1);
v_v_1609_ = lean_ctor_get(v_x_1605_, 2);
lean_inc(v_v_1609_);
lean_inc(v_k_1608_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_k_1608_);
lean_ctor_set(v___x_1610_, 1, v_v_1609_);
return v___x_1610_;
}
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1611_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1);
v___x_1612_ = l_panic___redArg(v_inst_1604_, v___x_1611_);
return v___x_1612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___boxed(lean_object* v_inst_1613_, lean_object* v_x_1614_){
_start:
{
lean_object* v_res_1615_; 
v_res_1615_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1613_, v_x_1614_);
lean_dec(v_x_1614_);
lean_dec_ref(v_inst_1613_);
return v_res_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21(lean_object* v_00_u03b1_1616_, lean_object* v_00_u03b2_1617_, lean_object* v_inst_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1618_, v_x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___boxed(lean_object* v_00_u03b1_1621_, lean_object* v_00_u03b2_1622_, lean_object* v_inst_1623_, lean_object* v_x_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21(v_00_u03b1_1621_, v_00_u03b2_1622_, v_inst_1623_, v_x_1624_);
lean_dec(v_x_1624_);
lean_dec_ref(v_inst_1623_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
if (lean_obj_tag(v_x_1626_) == 0)
{
lean_object* v_r_1628_; 
v_r_1628_ = lean_ctor_get(v_x_1626_, 4);
if (lean_obj_tag(v_r_1628_) == 0)
{
v_x_1626_ = v_r_1628_;
goto _start;
}
else
{
lean_object* v_k_1630_; lean_object* v_v_1631_; lean_object* v___x_1632_; 
v_k_1630_ = lean_ctor_get(v_x_1626_, 1);
v_v_1631_ = lean_ctor_get(v_x_1626_, 2);
lean_inc(v_v_1631_);
lean_inc(v_k_1630_);
v___x_1632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1632_, 0, v_k_1630_);
lean_ctor_set(v___x_1632_, 1, v_v_1631_);
return v___x_1632_;
}
}
else
{
lean_inc_ref(v_x_1627_);
return v_x_1627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg___boxed(lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v_res_1635_; 
v_res_1635_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1633_, v_x_1634_);
lean_dec_ref(v_x_1634_);
lean_dec(v_x_1633_);
return v_res_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD(lean_object* v_00_u03b1_1636_, lean_object* v_00_u03b2_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1638_, v_x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___boxed(lean_object* v_00_u03b1_1641_, lean_object* v_00_u03b2_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Std_DTreeMap_Internal_Impl_maxEntryD(v_00_u03b1_1641_, v_00_u03b2_1642_, v_x_1643_, v_x_1644_);
lean_dec_ref(v_x_1644_);
lean_dec(v_x_1643_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1646_, lean_object* v_x_1647_, lean_object* v_h__1_1648_, lean_object* v_h__2_1649_, lean_object* v_h__3_1650_){
_start:
{
if (lean_obj_tag(v_x_1646_) == 0)
{
lean_object* v_r_1651_; 
lean_dec(v_h__1_1648_);
v_r_1651_ = lean_ctor_get(v_x_1646_, 4);
if (lean_obj_tag(v_r_1651_) == 0)
{
lean_object* v_size_1652_; lean_object* v_k_1653_; lean_object* v_v_1654_; lean_object* v_l_1655_; lean_object* v_size_1656_; lean_object* v_k_1657_; lean_object* v_v_1658_; lean_object* v_l_1659_; lean_object* v_r_1660_; lean_object* v___x_1661_; 
lean_inc_ref(v_r_1651_);
lean_dec(v_h__2_1649_);
v_size_1652_ = lean_ctor_get(v_x_1646_, 0);
lean_inc(v_size_1652_);
v_k_1653_ = lean_ctor_get(v_x_1646_, 1);
lean_inc(v_k_1653_);
v_v_1654_ = lean_ctor_get(v_x_1646_, 2);
lean_inc(v_v_1654_);
v_l_1655_ = lean_ctor_get(v_x_1646_, 3);
lean_inc(v_l_1655_);
lean_dec_ref_known(v_x_1646_, 5);
v_size_1656_ = lean_ctor_get(v_r_1651_, 0);
lean_inc(v_size_1656_);
v_k_1657_ = lean_ctor_get(v_r_1651_, 1);
lean_inc(v_k_1657_);
v_v_1658_ = lean_ctor_get(v_r_1651_, 2);
lean_inc(v_v_1658_);
v_l_1659_ = lean_ctor_get(v_r_1651_, 3);
lean_inc(v_l_1659_);
v_r_1660_ = lean_ctor_get(v_r_1651_, 4);
lean_inc(v_r_1660_);
lean_dec_ref_known(v_r_1651_, 5);
v___x_1661_ = lean_apply_10(v_h__3_1650_, v_size_1652_, v_k_1653_, v_v_1654_, v_l_1655_, v_size_1656_, v_k_1657_, v_v_1658_, v_l_1659_, v_r_1660_, v_x_1647_);
return v___x_1661_;
}
else
{
lean_object* v_size_1662_; lean_object* v_k_1663_; lean_object* v_v_1664_; lean_object* v_l_1665_; lean_object* v___x_1666_; 
lean_dec(v_h__3_1650_);
v_size_1662_ = lean_ctor_get(v_x_1646_, 0);
lean_inc(v_size_1662_);
v_k_1663_ = lean_ctor_get(v_x_1646_, 1);
lean_inc(v_k_1663_);
v_v_1664_ = lean_ctor_get(v_x_1646_, 2);
lean_inc(v_v_1664_);
v_l_1665_ = lean_ctor_get(v_x_1646_, 3);
lean_inc(v_l_1665_);
lean_dec_ref_known(v_x_1646_, 5);
v___x_1666_ = lean_apply_5(v_h__2_1649_, v_size_1662_, v_k_1663_, v_v_1664_, v_l_1665_, v_x_1647_);
return v___x_1666_;
}
}
else
{
lean_object* v___x_1667_; 
lean_dec(v_h__3_1650_);
lean_dec(v_h__2_1649_);
v___x_1667_ = lean_apply_1(v_h__1_1648_, v_x_1647_);
return v___x_1667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1668_, lean_object* v_00_u03b2_1669_, lean_object* v_motive_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v_h__1_1673_, lean_object* v_h__2_1674_, lean_object* v_h__3_1675_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object* v_x_1693_){
_start:
{
if (lean_obj_tag(v_x_1693_) == 0)
{
lean_object* v_l_1694_; 
v_l_1694_ = lean_ctor_get(v_x_1693_, 3);
if (lean_obj_tag(v_l_1694_) == 0)
{
v_x_1693_ = v_l_1694_;
goto _start;
}
else
{
lean_object* v_k_1696_; lean_object* v___x_1697_; 
v_k_1696_ = lean_ctor_get(v_x_1693_, 1);
lean_inc(v_k_1696_);
v___x_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1697_, 0, v_k_1696_);
return v___x_1697_;
}
}
else
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_box(0);
return v___x_1698_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg___boxed(lean_object* v_x_1699_){
_start:
{
lean_object* v_res_1700_; 
v_res_1700_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1699_);
lean_dec(v_x_1699_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f(lean_object* v_00_u03b1_1701_, lean_object* v_00_u03b2_1702_, lean_object* v_x_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___boxed(lean_object* v_00_u03b1_1705_, lean_object* v_00_u03b2_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v_res_1708_; 
v_res_1708_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f(v_00_u03b1_1705_, v_00_u03b2_1706_, v_x_1707_);
lean_dec(v_x_1707_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object* v_x_1709_){
_start:
{
lean_object* v_l_1710_; 
v_l_1710_ = lean_ctor_get(v_x_1709_, 3);
if (lean_obj_tag(v_l_1710_) == 0)
{
v_x_1709_ = v_l_1710_;
goto _start;
}
else
{
lean_object* v_k_1712_; 
v_k_1712_ = lean_ctor_get(v_x_1709_, 1);
lean_inc(v_k_1712_);
return v_k_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg___boxed(lean_object* v_x_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1713_);
lean_dec(v_x_1713_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey(lean_object* v_00_u03b1_1715_, lean_object* v_00_u03b2_1716_, lean_object* v_x_1717_, lean_object* v_x_1718_){
_start:
{
lean_object* v___x_1719_; 
v___x_1719_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1717_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___boxed(lean_object* v_00_u03b1_1720_, lean_object* v_00_u03b2_1721_, lean_object* v_x_1722_, lean_object* v_x_1723_){
_start:
{
lean_object* v_res_1724_; 
v_res_1724_ = l_Std_DTreeMap_Internal_Impl_minKey(v_00_u03b1_1720_, v_00_u03b2_1721_, v_x_1722_, v_x_1723_);
lean_dec(v_x_1722_);
return v_res_1724_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; 
v___x_1726_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1727_ = lean_unsigned_to_nat(13u);
v___x_1728_ = lean_unsigned_to_nat(413u);
v___x_1729_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0));
v___x_1730_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1731_ = l_mkPanicMessageWithDecl(v___x_1730_, v___x_1729_, v___x_1728_, v___x_1727_, v___x_1726_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object* v_inst_1732_, lean_object* v_x_1733_){
_start:
{
if (lean_obj_tag(v_x_1733_) == 0)
{
lean_object* v_l_1734_; 
v_l_1734_ = lean_ctor_get(v_x_1733_, 3);
if (lean_obj_tag(v_l_1734_) == 0)
{
v_x_1733_ = v_l_1734_;
goto _start;
}
else
{
lean_object* v_k_1736_; 
v_k_1736_ = lean_ctor_get(v_x_1733_, 1);
lean_inc(v_k_1736_);
return v_k_1736_;
}
}
else
{
lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1737_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1);
v___x_1738_ = l_panic___redArg(v_inst_1732_, v___x_1737_);
return v___x_1738_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___boxed(lean_object* v_inst_1739_, lean_object* v_x_1740_){
_start:
{
lean_object* v_res_1741_; 
v_res_1741_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1739_, v_x_1740_);
lean_dec(v_x_1740_);
lean_dec(v_inst_1739_);
return v_res_1741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21(lean_object* v_00_u03b1_1742_, lean_object* v_00_u03b2_1743_, lean_object* v_inst_1744_, lean_object* v_x_1745_){
_start:
{
lean_object* v___x_1746_; 
v___x_1746_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1744_, v_x_1745_);
return v___x_1746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___boxed(lean_object* v_00_u03b1_1747_, lean_object* v_00_u03b2_1748_, lean_object* v_inst_1749_, lean_object* v_x_1750_){
_start:
{
lean_object* v_res_1751_; 
v_res_1751_ = l_Std_DTreeMap_Internal_Impl_minKey_x21(v_00_u03b1_1747_, v_00_u03b2_1748_, v_inst_1749_, v_x_1750_);
lean_dec(v_x_1750_);
lean_dec(v_inst_1749_);
return v_res_1751_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
if (lean_obj_tag(v_x_1752_) == 0)
{
lean_object* v_l_1754_; 
v_l_1754_ = lean_ctor_get(v_x_1752_, 3);
if (lean_obj_tag(v_l_1754_) == 0)
{
v_x_1752_ = v_l_1754_;
goto _start;
}
else
{
lean_object* v_k_1756_; 
v_k_1756_ = lean_ctor_get(v_x_1752_, 1);
lean_inc(v_k_1756_);
return v_k_1756_;
}
}
else
{
lean_inc(v_x_1753_);
return v_x_1753_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg___boxed(lean_object* v_x_1757_, lean_object* v_x_1758_){
_start:
{
lean_object* v_res_1759_; 
v_res_1759_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1757_, v_x_1758_);
lean_dec(v_x_1758_);
lean_dec(v_x_1757_);
return v_res_1759_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD(lean_object* v_00_u03b1_1760_, lean_object* v_00_u03b2_1761_, lean_object* v_x_1762_, lean_object* v_x_1763_){
_start:
{
lean_object* v___x_1764_; 
v___x_1764_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1762_, v_x_1763_);
return v___x_1764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___boxed(lean_object* v_00_u03b1_1765_, lean_object* v_00_u03b2_1766_, lean_object* v_x_1767_, lean_object* v_x_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_Std_DTreeMap_Internal_Impl_minKeyD(v_00_u03b1_1765_, v_00_u03b2_1766_, v_x_1767_, v_x_1768_);
lean_dec(v_x_1768_);
lean_dec(v_x_1767_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1770_, lean_object* v_x_1771_, lean_object* v_h__1_1772_, lean_object* v_h__2_1773_, lean_object* v_h__3_1774_){
_start:
{
if (lean_obj_tag(v_x_1770_) == 0)
{
lean_object* v_l_1775_; 
lean_dec(v_h__1_1772_);
v_l_1775_ = lean_ctor_get(v_x_1770_, 3);
if (lean_obj_tag(v_l_1775_) == 0)
{
lean_object* v_size_1776_; lean_object* v_k_1777_; lean_object* v_v_1778_; lean_object* v_r_1779_; lean_object* v_size_1780_; lean_object* v_k_1781_; lean_object* v_v_1782_; lean_object* v_l_1783_; lean_object* v_r_1784_; lean_object* v___x_1785_; 
lean_inc_ref(v_l_1775_);
lean_dec(v_h__2_1773_);
v_size_1776_ = lean_ctor_get(v_x_1770_, 0);
lean_inc(v_size_1776_);
v_k_1777_ = lean_ctor_get(v_x_1770_, 1);
lean_inc(v_k_1777_);
v_v_1778_ = lean_ctor_get(v_x_1770_, 2);
lean_inc(v_v_1778_);
v_r_1779_ = lean_ctor_get(v_x_1770_, 4);
lean_inc(v_r_1779_);
lean_dec_ref_known(v_x_1770_, 5);
v_size_1780_ = lean_ctor_get(v_l_1775_, 0);
lean_inc(v_size_1780_);
v_k_1781_ = lean_ctor_get(v_l_1775_, 1);
lean_inc(v_k_1781_);
v_v_1782_ = lean_ctor_get(v_l_1775_, 2);
lean_inc(v_v_1782_);
v_l_1783_ = lean_ctor_get(v_l_1775_, 3);
lean_inc(v_l_1783_);
v_r_1784_ = lean_ctor_get(v_l_1775_, 4);
lean_inc(v_r_1784_);
lean_dec_ref_known(v_l_1775_, 5);
v___x_1785_ = lean_apply_10(v_h__3_1774_, v_size_1776_, v_k_1777_, v_v_1778_, v_size_1780_, v_k_1781_, v_v_1782_, v_l_1783_, v_r_1784_, v_r_1779_, v_x_1771_);
return v___x_1785_;
}
else
{
lean_object* v_size_1786_; lean_object* v_k_1787_; lean_object* v_v_1788_; lean_object* v_r_1789_; lean_object* v___x_1790_; 
lean_dec(v_h__3_1774_);
v_size_1786_ = lean_ctor_get(v_x_1770_, 0);
lean_inc(v_size_1786_);
v_k_1787_ = lean_ctor_get(v_x_1770_, 1);
lean_inc(v_k_1787_);
v_v_1788_ = lean_ctor_get(v_x_1770_, 2);
lean_inc(v_v_1788_);
v_r_1789_ = lean_ctor_get(v_x_1770_, 4);
lean_inc(v_r_1789_);
lean_dec_ref_known(v_x_1770_, 5);
v___x_1790_ = lean_apply_5(v_h__2_1773_, v_size_1786_, v_k_1787_, v_v_1788_, v_r_1789_, v_x_1771_);
return v___x_1790_;
}
}
else
{
lean_object* v___x_1791_; 
lean_dec(v_h__3_1774_);
lean_dec(v_h__2_1773_);
v___x_1791_ = lean_apply_1(v_h__1_1772_, v_x_1771_);
return v___x_1791_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1792_, lean_object* v_00_u03b2_1793_, lean_object* v_motive_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_, lean_object* v_h__1_1797_, lean_object* v_h__2_1798_, lean_object* v_h__3_1799_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object* v_x_1817_){
_start:
{
if (lean_obj_tag(v_x_1817_) == 0)
{
lean_object* v_r_1818_; 
v_r_1818_ = lean_ctor_get(v_x_1817_, 4);
if (lean_obj_tag(v_r_1818_) == 0)
{
v_x_1817_ = v_r_1818_;
goto _start;
}
else
{
lean_object* v_k_1820_; lean_object* v___x_1821_; 
v_k_1820_ = lean_ctor_get(v_x_1817_, 1);
lean_inc(v_k_1820_);
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v_k_1820_);
return v___x_1821_;
}
}
else
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_box(0);
return v___x_1822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg___boxed(lean_object* v_x_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1823_);
lean_dec(v_x_1823_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f(lean_object* v_00_u03b1_1825_, lean_object* v_00_u03b2_1826_, lean_object* v_x_1827_){
_start:
{
lean_object* v___x_1828_; 
v___x_1828_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___boxed(lean_object* v_00_u03b1_1829_, lean_object* v_00_u03b2_1830_, lean_object* v_x_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f(v_00_u03b1_1829_, v_00_u03b2_1830_, v_x_1831_);
lean_dec(v_x_1831_);
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object* v_x_1833_){
_start:
{
lean_object* v_r_1834_; 
v_r_1834_ = lean_ctor_get(v_x_1833_, 4);
if (lean_obj_tag(v_r_1834_) == 0)
{
v_x_1833_ = v_r_1834_;
goto _start;
}
else
{
lean_object* v_k_1836_; 
v_k_1836_ = lean_ctor_get(v_x_1833_, 1);
lean_inc(v_k_1836_);
return v_k_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg___boxed(lean_object* v_x_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1837_);
lean_dec(v_x_1837_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey(lean_object* v_00_u03b1_1839_, lean_object* v_00_u03b2_1840_, lean_object* v_x_1841_, lean_object* v_x_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___boxed(lean_object* v_00_u03b1_1844_, lean_object* v_00_u03b2_1845_, lean_object* v_x_1846_, lean_object* v_x_1847_){
_start:
{
lean_object* v_res_1848_; 
v_res_1848_ = l_Std_DTreeMap_Internal_Impl_maxKey(v_00_u03b1_1844_, v_00_u03b2_1845_, v_x_1846_, v_x_1847_);
lean_dec(v_x_1846_);
return v_res_1848_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1850_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1851_ = lean_unsigned_to_nat(13u);
v___x_1852_ = lean_unsigned_to_nat(436u);
v___x_1853_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0));
v___x_1854_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1855_ = l_mkPanicMessageWithDecl(v___x_1854_, v___x_1853_, v___x_1852_, v___x_1851_, v___x_1850_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object* v_inst_1856_, lean_object* v_x_1857_){
_start:
{
if (lean_obj_tag(v_x_1857_) == 0)
{
lean_object* v_r_1858_; 
v_r_1858_ = lean_ctor_get(v_x_1857_, 4);
if (lean_obj_tag(v_r_1858_) == 0)
{
v_x_1857_ = v_r_1858_;
goto _start;
}
else
{
lean_object* v_k_1860_; 
v_k_1860_ = lean_ctor_get(v_x_1857_, 1);
lean_inc(v_k_1860_);
return v_k_1860_;
}
}
else
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1);
v___x_1862_ = l_panic___redArg(v_inst_1856_, v___x_1861_);
return v___x_1862_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___boxed(lean_object* v_inst_1863_, lean_object* v_x_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1863_, v_x_1864_);
lean_dec(v_x_1864_);
lean_dec(v_inst_1863_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21(lean_object* v_00_u03b1_1866_, lean_object* v_00_u03b2_1867_, lean_object* v_inst_1868_, lean_object* v_x_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1868_, v_x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___boxed(lean_object* v_00_u03b1_1871_, lean_object* v_00_u03b2_1872_, lean_object* v_inst_1873_, lean_object* v_x_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21(v_00_u03b1_1871_, v_00_u03b2_1872_, v_inst_1873_, v_x_1874_);
lean_dec(v_x_1874_);
lean_dec(v_inst_1873_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object* v_x_1876_, lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1876_) == 0)
{
lean_object* v_r_1878_; 
v_r_1878_ = lean_ctor_get(v_x_1876_, 4);
if (lean_obj_tag(v_r_1878_) == 0)
{
v_x_1876_ = v_r_1878_;
goto _start;
}
else
{
lean_object* v_k_1880_; 
v_k_1880_ = lean_ctor_get(v_x_1876_, 1);
lean_inc(v_k_1880_);
return v_k_1880_;
}
}
else
{
lean_inc(v_x_1877_);
return v_x_1877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg___boxed(lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1881_, v_x_1882_);
lean_dec(v_x_1882_);
lean_dec(v_x_1881_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD(lean_object* v_00_u03b1_1884_, lean_object* v_00_u03b2_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1886_, v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___boxed(lean_object* v_00_u03b1_1889_, lean_object* v_00_u03b2_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Std_DTreeMap_Internal_Impl_maxKeyD(v_00_u03b1_1889_, v_00_u03b2_1890_, v_x_1891_, v_x_1892_);
lean_dec(v_x_1892_);
lean_dec(v_x_1891_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1894_, lean_object* v_x_1895_, lean_object* v_h__1_1896_, lean_object* v_h__2_1897_, lean_object* v_h__3_1898_){
_start:
{
if (lean_obj_tag(v_x_1894_) == 0)
{
lean_object* v_r_1899_; 
lean_dec(v_h__1_1896_);
v_r_1899_ = lean_ctor_get(v_x_1894_, 4);
if (lean_obj_tag(v_r_1899_) == 0)
{
lean_object* v_size_1900_; lean_object* v_k_1901_; lean_object* v_v_1902_; lean_object* v_l_1903_; lean_object* v_size_1904_; lean_object* v_k_1905_; lean_object* v_v_1906_; lean_object* v_l_1907_; lean_object* v_r_1908_; lean_object* v___x_1909_; 
lean_inc_ref(v_r_1899_);
lean_dec(v_h__2_1897_);
v_size_1900_ = lean_ctor_get(v_x_1894_, 0);
lean_inc(v_size_1900_);
v_k_1901_ = lean_ctor_get(v_x_1894_, 1);
lean_inc(v_k_1901_);
v_v_1902_ = lean_ctor_get(v_x_1894_, 2);
lean_inc(v_v_1902_);
v_l_1903_ = lean_ctor_get(v_x_1894_, 3);
lean_inc(v_l_1903_);
lean_dec_ref_known(v_x_1894_, 5);
v_size_1904_ = lean_ctor_get(v_r_1899_, 0);
lean_inc(v_size_1904_);
v_k_1905_ = lean_ctor_get(v_r_1899_, 1);
lean_inc(v_k_1905_);
v_v_1906_ = lean_ctor_get(v_r_1899_, 2);
lean_inc(v_v_1906_);
v_l_1907_ = lean_ctor_get(v_r_1899_, 3);
lean_inc(v_l_1907_);
v_r_1908_ = lean_ctor_get(v_r_1899_, 4);
lean_inc(v_r_1908_);
lean_dec_ref_known(v_r_1899_, 5);
v___x_1909_ = lean_apply_10(v_h__3_1898_, v_size_1900_, v_k_1901_, v_v_1902_, v_l_1903_, v_size_1904_, v_k_1905_, v_v_1906_, v_l_1907_, v_r_1908_, v_x_1895_);
return v___x_1909_;
}
else
{
lean_object* v_size_1910_; lean_object* v_k_1911_; lean_object* v_v_1912_; lean_object* v_l_1913_; lean_object* v___x_1914_; 
lean_dec(v_h__3_1898_);
v_size_1910_ = lean_ctor_get(v_x_1894_, 0);
lean_inc(v_size_1910_);
v_k_1911_ = lean_ctor_get(v_x_1894_, 1);
lean_inc(v_k_1911_);
v_v_1912_ = lean_ctor_get(v_x_1894_, 2);
lean_inc(v_v_1912_);
v_l_1913_ = lean_ctor_get(v_x_1894_, 3);
lean_inc(v_l_1913_);
lean_dec_ref_known(v_x_1894_, 5);
v___x_1914_ = lean_apply_5(v_h__2_1897_, v_size_1910_, v_k_1911_, v_v_1912_, v_l_1913_, v_x_1895_);
return v___x_1914_;
}
}
else
{
lean_object* v___x_1915_; 
lean_dec(v_h__3_1898_);
lean_dec(v_h__2_1897_);
v___x_1915_ = lean_apply_1(v_h__1_1896_, v_x_1895_);
return v___x_1915_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1916_, lean_object* v_00_u03b2_1917_, lean_object* v_motive_1918_, lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v_h__1_1921_, lean_object* v_h__2_1922_, lean_object* v_h__3_1923_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object* v_x_1941_, lean_object* v_x_1942_){
_start:
{
lean_object* v_k_1943_; lean_object* v_v_1944_; lean_object* v_l_1945_; lean_object* v_r_1946_; lean_object* v___y_1948_; lean_object* v___y_1954_; 
v_k_1943_ = lean_ctor_get(v_x_1941_, 1);
v_v_1944_ = lean_ctor_get(v_x_1941_, 2);
v_l_1945_ = lean_ctor_get(v_x_1941_, 3);
v_r_1946_ = lean_ctor_get(v_x_1941_, 4);
if (lean_obj_tag(v_l_1945_) == 0)
{
lean_object* v_size_1961_; 
v_size_1961_ = lean_ctor_get(v_l_1945_, 0);
v___y_1954_ = v_size_1961_;
goto v___jp_1953_;
}
else
{
lean_object* v___x_1962_; 
v___x_1962_ = lean_unsigned_to_nat(0u);
v___y_1954_ = v___x_1962_;
goto v___jp_1953_;
}
v___jp_1947_:
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
v___x_1949_ = lean_nat_sub(v_x_1942_, v___y_1948_);
lean_dec(v_x_1942_);
v___x_1950_ = lean_unsigned_to_nat(1u);
v___x_1951_ = lean_nat_sub(v___x_1949_, v___x_1950_);
lean_dec(v___x_1949_);
v_x_1941_ = v_r_1946_;
v_x_1942_ = v___x_1951_;
goto _start;
}
v___jp_1953_:
{
uint8_t v___x_1955_; 
v___x_1955_ = lean_nat_dec_lt(v_x_1942_, v___y_1954_);
if (v___x_1955_ == 0)
{
uint8_t v___x_1956_; 
v___x_1956_ = lean_nat_dec_eq(v_x_1942_, v___y_1954_);
if (v___x_1956_ == 0)
{
if (lean_obj_tag(v_l_1945_) == 0)
{
lean_object* v_size_1957_; 
v_size_1957_ = lean_ctor_get(v_l_1945_, 0);
v___y_1948_ = v_size_1957_;
goto v___jp_1947_;
}
else
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_unsigned_to_nat(0u);
v___y_1948_ = v___x_1958_;
goto v___jp_1947_;
}
}
else
{
lean_object* v___x_1959_; 
lean_dec(v_x_1942_);
lean_inc(v_v_1944_);
lean_inc(v_k_1943_);
v___x_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1959_, 0, v_k_1943_);
lean_ctor_set(v___x_1959_, 1, v_v_1944_);
return v___x_1959_;
}
}
else
{
v_x_1941_ = v_l_1945_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg___boxed(lean_object* v_x_1963_, lean_object* v_x_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1963_, v_x_1964_);
lean_dec(v_x_1963_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx(lean_object* v_00_u03b1_1966_, lean_object* v_00_u03b2_1967_, lean_object* v_x_1968_, lean_object* v_x_1969_, lean_object* v_x_1970_, lean_object* v_x_1971_){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1968_, v_x_1970_);
return v___x_1972_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___boxed(lean_object* v_00_u03b1_1973_, lean_object* v_00_u03b2_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx(v_00_u03b1_1973_, v_00_u03b2_1974_, v_x_1975_, v_x_1976_, v_x_1977_, v_x_1978_);
lean_dec(v_x_1975_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object* v_x_1980_, lean_object* v_x_1981_){
_start:
{
if (lean_obj_tag(v_x_1980_) == 0)
{
lean_object* v_k_1982_; lean_object* v_v_1983_; lean_object* v_l_1984_; lean_object* v_r_1985_; lean_object* v___y_1987_; lean_object* v___y_1993_; 
v_k_1982_ = lean_ctor_get(v_x_1980_, 1);
v_v_1983_ = lean_ctor_get(v_x_1980_, 2);
v_l_1984_ = lean_ctor_get(v_x_1980_, 3);
v_r_1985_ = lean_ctor_get(v_x_1980_, 4);
if (lean_obj_tag(v_l_1984_) == 0)
{
lean_object* v_size_2001_; 
v_size_2001_ = lean_ctor_get(v_l_1984_, 0);
v___y_1993_ = v_size_2001_;
goto v___jp_1992_;
}
else
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_unsigned_to_nat(0u);
v___y_1993_ = v___x_2002_;
goto v___jp_1992_;
}
v___jp_1986_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = lean_nat_sub(v_x_1981_, v___y_1987_);
lean_dec(v_x_1981_);
v___x_1989_ = lean_unsigned_to_nat(1u);
v___x_1990_ = lean_nat_sub(v___x_1988_, v___x_1989_);
lean_dec(v___x_1988_);
v_x_1980_ = v_r_1985_;
v_x_1981_ = v___x_1990_;
goto _start;
}
v___jp_1992_:
{
uint8_t v___x_1994_; 
v___x_1994_ = lean_nat_dec_lt(v_x_1981_, v___y_1993_);
if (v___x_1994_ == 0)
{
uint8_t v___x_1995_; 
v___x_1995_ = lean_nat_dec_eq(v_x_1981_, v___y_1993_);
if (v___x_1995_ == 0)
{
if (lean_obj_tag(v_l_1984_) == 0)
{
lean_object* v_size_1996_; 
v_size_1996_ = lean_ctor_get(v_l_1984_, 0);
v___y_1987_ = v_size_1996_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_unsigned_to_nat(0u);
v___y_1987_ = v___x_1997_;
goto v___jp_1986_;
}
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; 
lean_dec(v_x_1981_);
lean_inc(v_v_1983_);
lean_inc(v_k_1982_);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v_k_1982_);
lean_ctor_set(v___x_1998_, 1, v_v_1983_);
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
return v___x_1999_;
}
}
else
{
v_x_1980_ = v_l_1984_;
goto _start;
}
}
}
else
{
lean_object* v___x_2003_; 
lean_dec(v_x_1981_);
v___x_2003_ = lean_box(0);
return v___x_2003_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_2004_, lean_object* v_x_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_2004_, v_x_2005_);
lean_dec(v_x_2004_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(lean_object* v_00_u03b1_2007_, lean_object* v_00_u03b2_2008_, lean_object* v_x_2009_, lean_object* v_x_2010_){
_start:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_2009_, v_x_2010_);
return v___x_2011_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_2012_, lean_object* v_00_u03b2_2013_, lean_object* v_x_2014_, lean_object* v_x_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(v_00_u03b1_2012_, v_00_u03b2_2013_, v_x_2014_, v_x_2015_);
lean_dec(v_x_2014_);
return v_res_2016_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2019_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_2020_ = lean_unsigned_to_nat(16u);
v___x_2021_ = lean_unsigned_to_nat(467u);
v___x_2022_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0));
v___x_2023_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_2024_ = l_mkPanicMessageWithDecl(v___x_2023_, v___x_2022_, v___x_2021_, v___x_2020_, v___x_2019_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(lean_object* v_inst_2025_, lean_object* v_x_2026_, lean_object* v_x_2027_){
_start:
{
if (lean_obj_tag(v_x_2026_) == 0)
{
lean_object* v_k_2028_; lean_object* v_v_2029_; lean_object* v_l_2030_; lean_object* v_r_2031_; lean_object* v___y_2033_; lean_object* v___y_2039_; 
v_k_2028_ = lean_ctor_get(v_x_2026_, 1);
v_v_2029_ = lean_ctor_get(v_x_2026_, 2);
v_l_2030_ = lean_ctor_get(v_x_2026_, 3);
v_r_2031_ = lean_ctor_get(v_x_2026_, 4);
if (lean_obj_tag(v_l_2030_) == 0)
{
lean_object* v_size_2046_; 
v_size_2046_ = lean_ctor_get(v_l_2030_, 0);
v___y_2039_ = v_size_2046_;
goto v___jp_2038_;
}
else
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_unsigned_to_nat(0u);
v___y_2039_ = v___x_2047_;
goto v___jp_2038_;
}
v___jp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2034_ = lean_nat_sub(v_x_2027_, v___y_2033_);
lean_dec(v_x_2027_);
v___x_2035_ = lean_unsigned_to_nat(1u);
v___x_2036_ = lean_nat_sub(v___x_2034_, v___x_2035_);
lean_dec(v___x_2034_);
v_x_2026_ = v_r_2031_;
v_x_2027_ = v___x_2036_;
goto _start;
}
v___jp_2038_:
{
uint8_t v___x_2040_; 
v___x_2040_ = lean_nat_dec_lt(v_x_2027_, v___y_2039_);
if (v___x_2040_ == 0)
{
uint8_t v___x_2041_; 
v___x_2041_ = lean_nat_dec_eq(v_x_2027_, v___y_2039_);
if (v___x_2041_ == 0)
{
if (lean_obj_tag(v_l_2030_) == 0)
{
lean_object* v_size_2042_; 
v_size_2042_ = lean_ctor_get(v_l_2030_, 0);
v___y_2033_ = v_size_2042_;
goto v___jp_2032_;
}
else
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_unsigned_to_nat(0u);
v___y_2033_ = v___x_2043_;
goto v___jp_2032_;
}
}
else
{
lean_object* v___x_2044_; 
lean_dec(v_x_2027_);
lean_inc(v_v_2029_);
lean_inc(v_k_2028_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v_k_2028_);
lean_ctor_set(v___x_2044_, 1, v_v_2029_);
return v___x_2044_;
}
}
else
{
v_x_2026_ = v_l_2030_;
goto _start;
}
}
}
else
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
lean_dec(v_x_2027_);
v___x_2048_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2);
v___x_2049_ = l_panic___redArg(v_inst_2025_, v___x_2048_);
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_2050_, lean_object* v_x_2051_, lean_object* v_x_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2050_, v_x_2051_, v_x_2052_);
lean_dec(v_x_2051_);
lean_dec_ref(v_inst_2050_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(lean_object* v_00_u03b1_2054_, lean_object* v_00_u03b2_2055_, lean_object* v_inst_2056_, lean_object* v_x_2057_, lean_object* v_x_2058_){
_start:
{
lean_object* v___x_2059_; 
v___x_2059_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2056_, v_x_2057_, v_x_2058_);
return v___x_2059_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_2060_, lean_object* v_00_u03b2_2061_, lean_object* v_inst_2062_, lean_object* v_x_2063_, lean_object* v_x_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(v_00_u03b1_2060_, v_00_u03b2_2061_, v_inst_2062_, v_x_2063_, v_x_2064_);
lean_dec(v_x_2063_);
lean_dec_ref(v_inst_2062_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object* v_x_2066_, lean_object* v_x_2067_, lean_object* v_x_2068_){
_start:
{
if (lean_obj_tag(v_x_2066_) == 0)
{
lean_object* v_k_2069_; lean_object* v_v_2070_; lean_object* v_l_2071_; lean_object* v_r_2072_; lean_object* v___y_2074_; lean_object* v___y_2080_; 
v_k_2069_ = lean_ctor_get(v_x_2066_, 1);
v_v_2070_ = lean_ctor_get(v_x_2066_, 2);
v_l_2071_ = lean_ctor_get(v_x_2066_, 3);
v_r_2072_ = lean_ctor_get(v_x_2066_, 4);
if (lean_obj_tag(v_l_2071_) == 0)
{
lean_object* v_size_2087_; 
v_size_2087_ = lean_ctor_get(v_l_2071_, 0);
v___y_2080_ = v_size_2087_;
goto v___jp_2079_;
}
else
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_unsigned_to_nat(0u);
v___y_2080_ = v___x_2088_;
goto v___jp_2079_;
}
v___jp_2073_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; 
v___x_2075_ = lean_nat_sub(v_x_2067_, v___y_2074_);
lean_dec(v_x_2067_);
v___x_2076_ = lean_unsigned_to_nat(1u);
v___x_2077_ = lean_nat_sub(v___x_2075_, v___x_2076_);
lean_dec(v___x_2075_);
v_x_2066_ = v_r_2072_;
v_x_2067_ = v___x_2077_;
goto _start;
}
v___jp_2079_:
{
uint8_t v___x_2081_; 
v___x_2081_ = lean_nat_dec_lt(v_x_2067_, v___y_2080_);
if (v___x_2081_ == 0)
{
uint8_t v___x_2082_; 
v___x_2082_ = lean_nat_dec_eq(v_x_2067_, v___y_2080_);
if (v___x_2082_ == 0)
{
if (lean_obj_tag(v_l_2071_) == 0)
{
lean_object* v_size_2083_; 
v_size_2083_ = lean_ctor_get(v_l_2071_, 0);
v___y_2074_ = v_size_2083_;
goto v___jp_2073_;
}
else
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_unsigned_to_nat(0u);
v___y_2074_ = v___x_2084_;
goto v___jp_2073_;
}
}
else
{
lean_object* v___x_2085_; 
lean_dec(v_x_2067_);
lean_inc(v_v_2070_);
lean_inc(v_k_2069_);
v___x_2085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2085_, 0, v_k_2069_);
lean_ctor_set(v___x_2085_, 1, v_v_2070_);
return v___x_2085_;
}
}
else
{
v_x_2066_ = v_l_2071_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2067_);
lean_inc_ref(v_x_2068_);
return v_x_2068_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg___boxed(lean_object* v_x_2089_, lean_object* v_x_2090_, lean_object* v_x_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2089_, v_x_2090_, v_x_2091_);
lean_dec_ref(v_x_2091_);
lean_dec(v_x_2089_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD(lean_object* v_00_u03b1_2093_, lean_object* v_00_u03b2_2094_, lean_object* v_x_2095_, lean_object* v_x_2096_, lean_object* v_x_2097_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2095_, v_x_2096_, v_x_2097_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___boxed(lean_object* v_00_u03b1_2099_, lean_object* v_00_u03b2_2100_, lean_object* v_x_2101_, lean_object* v_x_2102_, lean_object* v_x_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD(v_00_u03b1_2099_, v_00_u03b2_2100_, v_x_2101_, v_x_2102_, v_x_2103_);
lean_dec_ref(v_x_2103_);
lean_dec(v_x_2101_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object* v_x_2105_, lean_object* v_x_2106_){
_start:
{
lean_object* v_k_2107_; lean_object* v_l_2108_; lean_object* v_r_2109_; lean_object* v___y_2111_; lean_object* v___y_2117_; 
v_k_2107_ = lean_ctor_get(v_x_2105_, 1);
v_l_2108_ = lean_ctor_get(v_x_2105_, 3);
v_r_2109_ = lean_ctor_get(v_x_2105_, 4);
if (lean_obj_tag(v_l_2108_) == 0)
{
lean_object* v_size_2123_; 
v_size_2123_ = lean_ctor_get(v_l_2108_, 0);
v___y_2117_ = v_size_2123_;
goto v___jp_2116_;
}
else
{
lean_object* v___x_2124_; 
v___x_2124_ = lean_unsigned_to_nat(0u);
v___y_2117_ = v___x_2124_;
goto v___jp_2116_;
}
v___jp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_nat_sub(v_x_2106_, v___y_2111_);
lean_dec(v_x_2106_);
v___x_2113_ = lean_unsigned_to_nat(1u);
v___x_2114_ = lean_nat_sub(v___x_2112_, v___x_2113_);
lean_dec(v___x_2112_);
v_x_2105_ = v_r_2109_;
v_x_2106_ = v___x_2114_;
goto _start;
}
v___jp_2116_:
{
uint8_t v___x_2118_; 
v___x_2118_ = lean_nat_dec_lt(v_x_2106_, v___y_2117_);
if (v___x_2118_ == 0)
{
uint8_t v___x_2119_; 
v___x_2119_ = lean_nat_dec_eq(v_x_2106_, v___y_2117_);
if (v___x_2119_ == 0)
{
if (lean_obj_tag(v_l_2108_) == 0)
{
lean_object* v_size_2120_; 
v_size_2120_ = lean_ctor_get(v_l_2108_, 0);
v___y_2111_ = v_size_2120_;
goto v___jp_2110_;
}
else
{
lean_object* v___x_2121_; 
v___x_2121_ = lean_unsigned_to_nat(0u);
v___y_2111_ = v___x_2121_;
goto v___jp_2110_;
}
}
else
{
lean_dec(v_x_2106_);
lean_inc(v_k_2107_);
return v_k_2107_;
}
}
else
{
v_x_2105_ = v_l_2108_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg___boxed(lean_object* v_x_2125_, lean_object* v_x_2126_){
_start:
{
lean_object* v_res_2127_; 
v_res_2127_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2125_, v_x_2126_);
lean_dec(v_x_2125_);
return v_res_2127_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx(lean_object* v_00_u03b1_2128_, lean_object* v_00_u03b2_2129_, lean_object* v_x_2130_, lean_object* v_x_2131_, lean_object* v_x_2132_, lean_object* v_x_2133_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2130_, v_x_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_00_u03b2_2136_, lean_object* v_x_2137_, lean_object* v_x_2138_, lean_object* v_x_2139_, lean_object* v_x_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx(v_00_u03b1_2135_, v_00_u03b2_2136_, v_x_2137_, v_x_2138_, v_x_2139_, v_x_2140_);
lean_dec(v_x_2137_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object* v_x_2142_, lean_object* v_x_2143_){
_start:
{
if (lean_obj_tag(v_x_2142_) == 0)
{
lean_object* v_k_2144_; lean_object* v_l_2145_; lean_object* v_r_2146_; lean_object* v___y_2148_; lean_object* v___y_2154_; 
v_k_2144_ = lean_ctor_get(v_x_2142_, 1);
v_l_2145_ = lean_ctor_get(v_x_2142_, 3);
v_r_2146_ = lean_ctor_get(v_x_2142_, 4);
if (lean_obj_tag(v_l_2145_) == 0)
{
lean_object* v_size_2161_; 
v_size_2161_ = lean_ctor_get(v_l_2145_, 0);
v___y_2154_ = v_size_2161_;
goto v___jp_2153_;
}
else
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_unsigned_to_nat(0u);
v___y_2154_ = v___x_2162_;
goto v___jp_2153_;
}
v___jp_2147_:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2149_ = lean_nat_sub(v_x_2143_, v___y_2148_);
lean_dec(v_x_2143_);
v___x_2150_ = lean_unsigned_to_nat(1u);
v___x_2151_ = lean_nat_sub(v___x_2149_, v___x_2150_);
lean_dec(v___x_2149_);
v_x_2142_ = v_r_2146_;
v_x_2143_ = v___x_2151_;
goto _start;
}
v___jp_2153_:
{
uint8_t v___x_2155_; 
v___x_2155_ = lean_nat_dec_lt(v_x_2143_, v___y_2154_);
if (v___x_2155_ == 0)
{
uint8_t v___x_2156_; 
v___x_2156_ = lean_nat_dec_eq(v_x_2143_, v___y_2154_);
if (v___x_2156_ == 0)
{
if (lean_obj_tag(v_l_2145_) == 0)
{
lean_object* v_size_2157_; 
v_size_2157_ = lean_ctor_get(v_l_2145_, 0);
v___y_2148_ = v_size_2157_;
goto v___jp_2147_;
}
else
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_unsigned_to_nat(0u);
v___y_2148_ = v___x_2158_;
goto v___jp_2147_;
}
}
else
{
lean_object* v___x_2159_; 
lean_dec(v_x_2143_);
lean_inc(v_k_2144_);
v___x_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2159_, 0, v_k_2144_);
return v___x_2159_;
}
}
else
{
v_x_2142_ = v_l_2145_;
goto _start;
}
}
}
else
{
lean_object* v___x_2163_; 
lean_dec(v_x_2143_);
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg___boxed(lean_object* v_x_2164_, lean_object* v_x_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2164_, v_x_2165_);
lean_dec(v_x_2164_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(lean_object* v_00_u03b1_2167_, lean_object* v_00_u03b2_2168_, lean_object* v_x_2169_, lean_object* v_x_2170_){
_start:
{
lean_object* v___x_2171_; 
v___x_2171_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2169_, v_x_2170_);
return v___x_2171_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_2172_, lean_object* v_00_u03b2_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_){
_start:
{
lean_object* v_res_2176_; 
v_res_2176_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(v_00_u03b1_2172_, v_00_u03b2_2173_, v_x_2174_, v_x_2175_);
lean_dec(v_x_2174_);
return v_res_2176_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; 
v___x_2178_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_2179_ = lean_unsigned_to_nat(16u);
v___x_2180_ = lean_unsigned_to_nat(503u);
v___x_2181_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0));
v___x_2182_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_2183_ = l_mkPanicMessageWithDecl(v___x_2182_, v___x_2181_, v___x_2180_, v___x_2179_, v___x_2178_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object* v_inst_2184_, lean_object* v_x_2185_, lean_object* v_x_2186_){
_start:
{
if (lean_obj_tag(v_x_2185_) == 0)
{
lean_object* v_k_2187_; lean_object* v_l_2188_; lean_object* v_r_2189_; lean_object* v___y_2191_; lean_object* v___y_2197_; 
v_k_2187_ = lean_ctor_get(v_x_2185_, 1);
v_l_2188_ = lean_ctor_get(v_x_2185_, 3);
v_r_2189_ = lean_ctor_get(v_x_2185_, 4);
if (lean_obj_tag(v_l_2188_) == 0)
{
lean_object* v_size_2203_; 
v_size_2203_ = lean_ctor_get(v_l_2188_, 0);
v___y_2197_ = v_size_2203_;
goto v___jp_2196_;
}
else
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_unsigned_to_nat(0u);
v___y_2197_ = v___x_2204_;
goto v___jp_2196_;
}
v___jp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; 
v___x_2192_ = lean_nat_sub(v_x_2186_, v___y_2191_);
lean_dec(v_x_2186_);
v___x_2193_ = lean_unsigned_to_nat(1u);
v___x_2194_ = lean_nat_sub(v___x_2192_, v___x_2193_);
lean_dec(v___x_2192_);
v_x_2185_ = v_r_2189_;
v_x_2186_ = v___x_2194_;
goto _start;
}
v___jp_2196_:
{
uint8_t v___x_2198_; 
v___x_2198_ = lean_nat_dec_lt(v_x_2186_, v___y_2197_);
if (v___x_2198_ == 0)
{
uint8_t v___x_2199_; 
v___x_2199_ = lean_nat_dec_eq(v_x_2186_, v___y_2197_);
if (v___x_2199_ == 0)
{
if (lean_obj_tag(v_l_2188_) == 0)
{
lean_object* v_size_2200_; 
v_size_2200_ = lean_ctor_get(v_l_2188_, 0);
v___y_2191_ = v_size_2200_;
goto v___jp_2190_;
}
else
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_unsigned_to_nat(0u);
v___y_2191_ = v___x_2201_;
goto v___jp_2190_;
}
}
else
{
lean_dec(v_x_2186_);
lean_inc(v_k_2187_);
return v_k_2187_;
}
}
else
{
v_x_2185_ = v_l_2188_;
goto _start;
}
}
}
else
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_dec(v_x_2186_);
v___x_2205_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1);
v___x_2206_ = l_panic___redArg(v_inst_2184_, v___x_2205_);
return v___x_2206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_2207_, lean_object* v_x_2208_, lean_object* v_x_2209_){
_start:
{
lean_object* v_res_2210_; 
v_res_2210_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2207_, v_x_2208_, v_x_2209_);
lean_dec(v_x_2208_);
lean_dec(v_inst_2207_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(lean_object* v_00_u03b1_2211_, lean_object* v_00_u03b2_2212_, lean_object* v_inst_2213_, lean_object* v_x_2214_, lean_object* v_x_2215_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2213_, v_x_2214_, v_x_2215_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_2217_, lean_object* v_00_u03b2_2218_, lean_object* v_inst_2219_, lean_object* v_x_2220_, lean_object* v_x_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(v_00_u03b1_2217_, v_00_u03b2_2218_, v_inst_2219_, v_x_2220_, v_x_2221_);
lean_dec(v_x_2220_);
lean_dec(v_inst_2219_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object* v_x_2223_, lean_object* v_x_2224_, lean_object* v_x_2225_){
_start:
{
if (lean_obj_tag(v_x_2223_) == 0)
{
lean_object* v_k_2226_; lean_object* v_l_2227_; lean_object* v_r_2228_; lean_object* v___y_2230_; lean_object* v___y_2236_; 
v_k_2226_ = lean_ctor_get(v_x_2223_, 1);
v_l_2227_ = lean_ctor_get(v_x_2223_, 3);
v_r_2228_ = lean_ctor_get(v_x_2223_, 4);
if (lean_obj_tag(v_l_2227_) == 0)
{
lean_object* v_size_2242_; 
v_size_2242_ = lean_ctor_get(v_l_2227_, 0);
v___y_2236_ = v_size_2242_;
goto v___jp_2235_;
}
else
{
lean_object* v___x_2243_; 
v___x_2243_ = lean_unsigned_to_nat(0u);
v___y_2236_ = v___x_2243_;
goto v___jp_2235_;
}
v___jp_2229_:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = lean_nat_sub(v_x_2224_, v___y_2230_);
lean_dec(v_x_2224_);
v___x_2232_ = lean_unsigned_to_nat(1u);
v___x_2233_ = lean_nat_sub(v___x_2231_, v___x_2232_);
lean_dec(v___x_2231_);
v_x_2223_ = v_r_2228_;
v_x_2224_ = v___x_2233_;
goto _start;
}
v___jp_2235_:
{
uint8_t v___x_2237_; 
v___x_2237_ = lean_nat_dec_lt(v_x_2224_, v___y_2236_);
if (v___x_2237_ == 0)
{
uint8_t v___x_2238_; 
v___x_2238_ = lean_nat_dec_eq(v_x_2224_, v___y_2236_);
if (v___x_2238_ == 0)
{
if (lean_obj_tag(v_l_2227_) == 0)
{
lean_object* v_size_2239_; 
v_size_2239_ = lean_ctor_get(v_l_2227_, 0);
v___y_2230_ = v_size_2239_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2240_; 
v___x_2240_ = lean_unsigned_to_nat(0u);
v___y_2230_ = v___x_2240_;
goto v___jp_2229_;
}
}
else
{
lean_dec(v_x_2224_);
lean_inc(v_k_2226_);
return v_k_2226_;
}
}
else
{
v_x_2223_ = v_l_2227_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2224_);
lean_inc(v_x_2225_);
return v_x_2225_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg___boxed(lean_object* v_x_2244_, lean_object* v_x_2245_, lean_object* v_x_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2244_, v_x_2245_, v_x_2246_);
lean_dec(v_x_2246_);
lean_dec(v_x_2244_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD(lean_object* v_00_u03b1_2248_, lean_object* v_00_u03b2_2249_, lean_object* v_x_2250_, lean_object* v_x_2251_, lean_object* v_x_2252_){
_start:
{
lean_object* v___x_2253_; 
v___x_2253_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2250_, v_x_2251_, v_x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___boxed(lean_object* v_00_u03b1_2254_, lean_object* v_00_u03b2_2255_, lean_object* v_x_2256_, lean_object* v_x_2257_, lean_object* v_x_2258_){
_start:
{
lean_object* v_res_2259_; 
v_res_2259_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD(v_00_u03b1_2254_, v_00_u03b2_2255_, v_x_2256_, v_x_2257_, v_x_2258_);
lean_dec(v_x_2258_);
lean_dec(v_x_2256_);
return v_res_2259_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object* v_inst_2260_, lean_object* v_k_2261_, lean_object* v_best_2262_, lean_object* v_a_2263_){
_start:
{
if (lean_obj_tag(v_a_2263_) == 0)
{
lean_object* v_k_2264_; lean_object* v_v_2265_; lean_object* v_l_2266_; lean_object* v_r_2267_; lean_object* v___x_2268_; uint8_t v___x_2269_; 
v_k_2264_ = lean_ctor_get(v_a_2263_, 1);
lean_inc_n(v_k_2264_, 2);
v_v_2265_ = lean_ctor_get(v_a_2263_, 2);
lean_inc(v_v_2265_);
v_l_2266_ = lean_ctor_get(v_a_2263_, 3);
lean_inc(v_l_2266_);
v_r_2267_ = lean_ctor_get(v_a_2263_, 4);
lean_inc(v_r_2267_);
lean_dec_ref_known(v_a_2263_, 5);
lean_inc_ref(v_inst_2260_);
lean_inc(v_k_2261_);
v___x_2268_ = lean_apply_2(v_inst_2260_, v_k_2261_, v_k_2264_);
v___x_2269_ = lean_unbox(v___x_2268_);
switch(v___x_2269_)
{
case 0:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
lean_dec(v_r_2267_);
lean_dec(v_best_2262_);
v___x_2270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2270_, 0, v_k_2264_);
lean_ctor_set(v___x_2270_, 1, v_v_2265_);
v___x_2271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
v_best_2262_ = v___x_2271_;
v_a_2263_ = v_l_2266_;
goto _start;
}
case 1:
{
lean_object* v___x_2273_; lean_object* v___x_2274_; 
lean_dec(v_r_2267_);
lean_dec(v_l_2266_);
lean_dec(v_best_2262_);
lean_dec(v_k_2261_);
lean_dec_ref(v_inst_2260_);
v___x_2273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2273_, 0, v_k_2264_);
lean_ctor_set(v___x_2273_, 1, v_v_2265_);
v___x_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
return v___x_2274_;
}
default: 
{
lean_dec(v_l_2266_);
lean_dec(v_v_2265_);
lean_dec(v_k_2264_);
v_a_2263_ = v_r_2267_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2261_);
lean_dec_ref(v_inst_2260_);
return v_best_2262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go(lean_object* v_00_u03b1_2276_, lean_object* v_00_u03b2_2277_, lean_object* v_inst_2278_, lean_object* v_k_2279_, lean_object* v_best_2280_, lean_object* v_a_2281_){
_start:
{
lean_object* v___x_2282_; 
v___x_2282_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2278_, v_k_2279_, v_best_2280_, v_a_2281_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___redArg(lean_object* v_inst_2283_, lean_object* v_k_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_box(0);
v___x_2287_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2283_, v_k_2284_, v___x_2286_, v_a_2285_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f(lean_object* v_00_u03b1_2288_, lean_object* v_00_u03b2_2289_, lean_object* v_inst_2290_, lean_object* v_k_2291_, lean_object* v_a_2292_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2293_ = lean_box(0);
v___x_2294_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2290_, v_k_2291_, v___x_2293_, v_a_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object* v_inst_2295_, lean_object* v_k_2296_, lean_object* v_best_2297_, lean_object* v_a_2298_){
_start:
{
if (lean_obj_tag(v_a_2298_) == 0)
{
lean_object* v_k_2299_; lean_object* v_v_2300_; lean_object* v_l_2301_; lean_object* v_r_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; 
v_k_2299_ = lean_ctor_get(v_a_2298_, 1);
lean_inc_n(v_k_2299_, 2);
v_v_2300_ = lean_ctor_get(v_a_2298_, 2);
lean_inc(v_v_2300_);
v_l_2301_ = lean_ctor_get(v_a_2298_, 3);
lean_inc(v_l_2301_);
v_r_2302_ = lean_ctor_get(v_a_2298_, 4);
lean_inc(v_r_2302_);
lean_dec_ref_known(v_a_2298_, 5);
lean_inc_ref(v_inst_2295_);
lean_inc(v_k_2296_);
v___x_2303_ = lean_apply_2(v_inst_2295_, v_k_2296_, v_k_2299_);
v___x_2304_ = lean_unbox(v___x_2303_);
if (v___x_2304_ == 0)
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
lean_dec(v_r_2302_);
lean_dec(v_best_2297_);
v___x_2305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2305_, 0, v_k_2299_);
lean_ctor_set(v___x_2305_, 1, v_v_2300_);
v___x_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2305_);
v_best_2297_ = v___x_2306_;
v_a_2298_ = v_l_2301_;
goto _start;
}
else
{
lean_dec(v_l_2301_);
lean_dec(v_v_2300_);
lean_dec(v_k_2299_);
v_a_2298_ = v_r_2302_;
goto _start;
}
}
else
{
lean_dec(v_k_2296_);
lean_dec_ref(v_inst_2295_);
return v_best_2297_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go(lean_object* v_00_u03b1_2309_, lean_object* v_00_u03b2_2310_, lean_object* v_inst_2311_, lean_object* v_k_2312_, lean_object* v_best_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v___x_2315_; 
v___x_2315_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2311_, v_k_2312_, v_best_2313_, v_a_2314_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___redArg(lean_object* v_inst_2316_, lean_object* v_k_2317_, lean_object* v_a_2318_){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
v___x_2319_ = lean_box(0);
v___x_2320_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2316_, v_k_2317_, v___x_2319_, v_a_2318_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f(lean_object* v_00_u03b1_2321_, lean_object* v_00_u03b2_2322_, lean_object* v_inst_2323_, lean_object* v_k_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2326_ = lean_box(0);
v___x_2327_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2323_, v_k_2324_, v___x_2326_, v_a_2325_);
return v___x_2327_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object* v_inst_2328_, lean_object* v_k_2329_, lean_object* v_best_2330_, lean_object* v_a_2331_){
_start:
{
if (lean_obj_tag(v_a_2331_) == 0)
{
lean_object* v_k_2332_; lean_object* v_v_2333_; lean_object* v_l_2334_; lean_object* v_r_2335_; lean_object* v___x_2336_; uint8_t v___x_2337_; 
v_k_2332_ = lean_ctor_get(v_a_2331_, 1);
lean_inc_n(v_k_2332_, 2);
v_v_2333_ = lean_ctor_get(v_a_2331_, 2);
lean_inc(v_v_2333_);
v_l_2334_ = lean_ctor_get(v_a_2331_, 3);
lean_inc(v_l_2334_);
v_r_2335_ = lean_ctor_get(v_a_2331_, 4);
lean_inc(v_r_2335_);
lean_dec_ref_known(v_a_2331_, 5);
lean_inc_ref(v_inst_2328_);
lean_inc(v_k_2329_);
v___x_2336_ = lean_apply_2(v_inst_2328_, v_k_2329_, v_k_2332_);
v___x_2337_ = lean_unbox(v___x_2336_);
switch(v___x_2337_)
{
case 0:
{
lean_dec(v_r_2335_);
lean_dec(v_v_2333_);
lean_dec(v_k_2332_);
v_a_2331_ = v_l_2334_;
goto _start;
}
case 1:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; 
lean_dec(v_r_2335_);
lean_dec(v_l_2334_);
lean_dec(v_best_2330_);
lean_dec(v_k_2329_);
lean_dec_ref(v_inst_2328_);
v___x_2339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2339_, 0, v_k_2332_);
lean_ctor_set(v___x_2339_, 1, v_v_2333_);
v___x_2340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2339_);
return v___x_2340_;
}
default: 
{
lean_object* v___x_2341_; lean_object* v___x_2342_; 
lean_dec(v_l_2334_);
lean_dec(v_best_2330_);
v___x_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2341_, 0, v_k_2332_);
lean_ctor_set(v___x_2341_, 1, v_v_2333_);
v___x_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
v_best_2330_ = v___x_2342_;
v_a_2331_ = v_r_2335_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2329_);
lean_dec_ref(v_inst_2328_);
return v_best_2330_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go(lean_object* v_00_u03b1_2344_, lean_object* v_00_u03b2_2345_, lean_object* v_inst_2346_, lean_object* v_k_2347_, lean_object* v_best_2348_, lean_object* v_a_2349_){
_start:
{
lean_object* v___x_2350_; 
v___x_2350_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2346_, v_k_2347_, v_best_2348_, v_a_2349_);
return v___x_2350_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___redArg(lean_object* v_inst_2351_, lean_object* v_k_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; 
v___x_2354_ = lean_box(0);
v___x_2355_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2351_, v_k_2352_, v___x_2354_, v_a_2353_);
return v___x_2355_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f(lean_object* v_00_u03b1_2356_, lean_object* v_00_u03b2_2357_, lean_object* v_inst_2358_, lean_object* v_k_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_box(0);
v___x_2362_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2358_, v_k_2359_, v___x_2361_, v_a_2360_);
return v___x_2362_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object* v_inst_2363_, lean_object* v_k_2364_, lean_object* v_best_2365_, lean_object* v_a_2366_){
_start:
{
if (lean_obj_tag(v_a_2366_) == 0)
{
lean_object* v_k_2367_; lean_object* v_v_2368_; lean_object* v_l_2369_; lean_object* v_r_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_k_2367_ = lean_ctor_get(v_a_2366_, 1);
lean_inc_n(v_k_2367_, 2);
v_v_2368_ = lean_ctor_get(v_a_2366_, 2);
lean_inc(v_v_2368_);
v_l_2369_ = lean_ctor_get(v_a_2366_, 3);
lean_inc(v_l_2369_);
v_r_2370_ = lean_ctor_get(v_a_2366_, 4);
lean_inc(v_r_2370_);
lean_dec_ref_known(v_a_2366_, 5);
lean_inc_ref(v_inst_2363_);
lean_inc(v_k_2364_);
v___x_2371_ = lean_apply_2(v_inst_2363_, v_k_2364_, v_k_2367_);
v___x_2372_ = lean_unbox(v___x_2371_);
if (v___x_2372_ == 2)
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
lean_dec(v_l_2369_);
lean_dec(v_best_2365_);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v_k_2367_);
lean_ctor_set(v___x_2373_, 1, v_v_2368_);
v___x_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
v_best_2365_ = v___x_2374_;
v_a_2366_ = v_r_2370_;
goto _start;
}
else
{
lean_dec(v_r_2370_);
lean_dec(v_v_2368_);
lean_dec(v_k_2367_);
v_a_2366_ = v_l_2369_;
goto _start;
}
}
else
{
lean_dec(v_k_2364_);
lean_dec_ref(v_inst_2363_);
return v_best_2365_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go(lean_object* v_00_u03b1_2377_, lean_object* v_00_u03b2_2378_, lean_object* v_inst_2379_, lean_object* v_k_2380_, lean_object* v_best_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___x_2383_; 
v___x_2383_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2379_, v_k_2380_, v_best_2381_, v_a_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___redArg(lean_object* v_inst_2384_, lean_object* v_k_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = lean_box(0);
v___x_2388_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2384_, v_k_2385_, v___x_2387_, v_a_2386_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f(lean_object* v_00_u03b1_2389_, lean_object* v_00_u03b2_2390_, lean_object* v_inst_2391_, lean_object* v_k_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = lean_box(0);
v___x_2395_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2391_, v_k_2392_, v___x_2394_, v_a_2393_);
return v___x_2395_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2399_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2));
v___x_2400_ = lean_unsigned_to_nat(14u);
v___x_2401_ = lean_unsigned_to_nat(22u);
v___x_2402_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1));
v___x_2403_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0));
v___x_2404_ = l_mkPanicMessageWithDecl(v___x_2403_, v___x_2402_, v___x_2401_, v___x_2400_, v___x_2399_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(lean_object* v_inst_2405_, lean_object* v_inst_2406_, lean_object* v_k_2407_, lean_object* v_t_2408_){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; 
v___x_2409_ = lean_box(0);
v___x_2410_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2405_, v_k_2407_, v___x_2409_, v_t_2408_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
v___x_2411_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2412_ = l_panic___redArg(v_inst_2406_, v___x_2411_);
return v___x_2412_;
}
else
{
lean_object* v_val_2413_; 
v_val_2413_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_val_2413_);
lean_dec_ref_known(v___x_2410_, 1);
return v_val_2413_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___boxed(lean_object* v_inst_2414_, lean_object* v_inst_2415_, lean_object* v_k_2416_, lean_object* v_t_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(v_inst_2414_, v_inst_2415_, v_k_2416_, v_t_2417_);
lean_dec_ref(v_inst_2415_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(lean_object* v_00_u03b1_2419_, lean_object* v_00_u03b2_2420_, lean_object* v_inst_2421_, lean_object* v_inst_2422_, lean_object* v_k_2423_, lean_object* v_t_2424_){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_box(0);
v___x_2426_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2421_, v_k_2423_, v___x_2425_, v_t_2424_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
v___x_2427_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2428_ = l_panic___redArg(v_inst_2422_, v___x_2427_);
return v___x_2428_;
}
else
{
lean_object* v_val_2429_; 
v_val_2429_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_val_2429_);
lean_dec_ref_known(v___x_2426_, 1);
return v_val_2429_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2430_, lean_object* v_00_u03b2_2431_, lean_object* v_inst_2432_, lean_object* v_inst_2433_, lean_object* v_k_2434_, lean_object* v_t_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(v_00_u03b1_2430_, v_00_u03b2_2431_, v_inst_2432_, v_inst_2433_, v_k_2434_, v_t_2435_);
lean_dec_ref(v_inst_2433_);
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(lean_object* v_inst_2437_, lean_object* v_inst_2438_, lean_object* v_k_2439_, lean_object* v_t_2440_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_box(0);
v___x_2442_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2437_, v_k_2439_, v___x_2441_, v_t_2440_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2443_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2444_ = l_panic___redArg(v_inst_2438_, v___x_2443_);
return v___x_2444_;
}
else
{
lean_object* v_val_2445_; 
v_val_2445_ = lean_ctor_get(v___x_2442_, 0);
lean_inc(v_val_2445_);
lean_dec_ref_known(v___x_2442_, 1);
return v_val_2445_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg___boxed(lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_k_2448_, lean_object* v_t_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(v_inst_2446_, v_inst_2447_, v_k_2448_, v_t_2449_);
lean_dec_ref(v_inst_2447_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(lean_object* v_00_u03b1_2451_, lean_object* v_00_u03b2_2452_, lean_object* v_inst_2453_, lean_object* v_inst_2454_, lean_object* v_k_2455_, lean_object* v_t_2456_){
_start:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = lean_box(0);
v___x_2458_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2453_, v_k_2455_, v___x_2457_, v_t_2456_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2459_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2460_ = l_panic___redArg(v_inst_2454_, v___x_2459_);
return v___x_2460_;
}
else
{
lean_object* v_val_2461_; 
v_val_2461_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_val_2461_);
lean_dec_ref_known(v___x_2458_, 1);
return v_val_2461_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2462_, lean_object* v_00_u03b2_2463_, lean_object* v_inst_2464_, lean_object* v_inst_2465_, lean_object* v_k_2466_, lean_object* v_t_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(v_00_u03b1_2462_, v_00_u03b2_2463_, v_inst_2464_, v_inst_2465_, v_k_2466_, v_t_2467_);
lean_dec_ref(v_inst_2465_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(lean_object* v_inst_2469_, lean_object* v_inst_2470_, lean_object* v_k_2471_, lean_object* v_t_2472_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_box(0);
v___x_2474_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2469_, v_k_2471_, v___x_2473_, v_t_2472_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2475_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2476_ = l_panic___redArg(v_inst_2470_, v___x_2475_);
return v___x_2476_;
}
else
{
lean_object* v_val_2477_; 
v_val_2477_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_val_2477_);
lean_dec_ref_known(v___x_2474_, 1);
return v_val_2477_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg___boxed(lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_k_2480_, lean_object* v_t_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(v_inst_2478_, v_inst_2479_, v_k_2480_, v_t_2481_);
lean_dec_ref(v_inst_2479_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(lean_object* v_00_u03b1_2483_, lean_object* v_00_u03b2_2484_, lean_object* v_inst_2485_, lean_object* v_inst_2486_, lean_object* v_k_2487_, lean_object* v_t_2488_){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_box(0);
v___x_2490_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2485_, v_k_2487_, v___x_2489_, v_t_2488_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2491_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2492_ = l_panic___redArg(v_inst_2486_, v___x_2491_);
return v___x_2492_;
}
else
{
lean_object* v_val_2493_; 
v_val_2493_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_val_2493_);
lean_dec_ref_known(v___x_2490_, 1);
return v_val_2493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2494_, lean_object* v_00_u03b2_2495_, lean_object* v_inst_2496_, lean_object* v_inst_2497_, lean_object* v_k_2498_, lean_object* v_t_2499_){
_start:
{
lean_object* v_res_2500_; 
v_res_2500_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(v_00_u03b1_2494_, v_00_u03b2_2495_, v_inst_2496_, v_inst_2497_, v_k_2498_, v_t_2499_);
lean_dec_ref(v_inst_2497_);
return v_res_2500_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(lean_object* v_inst_2501_, lean_object* v_inst_2502_, lean_object* v_k_2503_, lean_object* v_t_2504_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = lean_box(0);
v___x_2506_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2501_, v_k_2503_, v___x_2505_, v_t_2504_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2508_ = l_panic___redArg(v_inst_2502_, v___x_2507_);
return v___x_2508_;
}
else
{
lean_object* v_val_2509_; 
v_val_2509_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_val_2509_);
lean_dec_ref_known(v___x_2506_, 1);
return v_val_2509_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg___boxed(lean_object* v_inst_2510_, lean_object* v_inst_2511_, lean_object* v_k_2512_, lean_object* v_t_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(v_inst_2510_, v_inst_2511_, v_k_2512_, v_t_2513_);
lean_dec_ref(v_inst_2511_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(lean_object* v_00_u03b1_2515_, lean_object* v_00_u03b2_2516_, lean_object* v_inst_2517_, lean_object* v_inst_2518_, lean_object* v_k_2519_, lean_object* v_t_2520_){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_box(0);
v___x_2522_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2517_, v_k_2519_, v___x_2521_, v_t_2520_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2523_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2524_ = l_panic___redArg(v_inst_2518_, v___x_2523_);
return v___x_2524_;
}
else
{
lean_object* v_val_2525_; 
v_val_2525_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_val_2525_);
lean_dec_ref_known(v___x_2522_, 1);
return v_val_2525_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2526_, lean_object* v_00_u03b2_2527_, lean_object* v_inst_2528_, lean_object* v_inst_2529_, lean_object* v_k_2530_, lean_object* v_t_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(v_00_u03b1_2526_, v_00_u03b2_2527_, v_inst_2528_, v_inst_2529_, v_k_2530_, v_t_2531_);
lean_dec_ref(v_inst_2529_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(lean_object* v_inst_2533_, lean_object* v_k_2534_, lean_object* v_t_2535_, lean_object* v_fallback_2536_){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_box(0);
v___x_2538_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2533_, v_k_2534_, v___x_2537_, v_t_2535_);
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
lean_dec_ref_known(v___x_2538_, 1);
return v_val_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg___boxed(lean_object* v_inst_2540_, lean_object* v_k_2541_, lean_object* v_t_2542_, lean_object* v_fallback_2543_){
_start:
{
lean_object* v_res_2544_; 
v_res_2544_ = l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(v_inst_2540_, v_k_2541_, v_t_2542_, v_fallback_2543_);
lean_dec_ref(v_fallback_2543_);
return v_res_2544_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED(lean_object* v_00_u03b1_2545_, lean_object* v_00_u03b2_2546_, lean_object* v_inst_2547_, lean_object* v_k_2548_, lean_object* v_t_2549_, lean_object* v_fallback_2550_){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_box(0);
v___x_2552_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2547_, v_k_2548_, v___x_2551_, v_t_2549_);
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
lean_dec_ref_known(v___x_2552_, 1);
return v_val_2553_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___boxed(lean_object* v_00_u03b1_2554_, lean_object* v_00_u03b2_2555_, lean_object* v_inst_2556_, lean_object* v_k_2557_, lean_object* v_t_2558_, lean_object* v_fallback_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Std_DTreeMap_Internal_Impl_getEntryGED(v_00_u03b1_2554_, v_00_u03b2_2555_, v_inst_2556_, v_k_2557_, v_t_2558_, v_fallback_2559_);
lean_dec_ref(v_fallback_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(lean_object* v_inst_2561_, lean_object* v_k_2562_, lean_object* v_t_2563_, lean_object* v_fallback_2564_){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_box(0);
v___x_2566_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2561_, v_k_2562_, v___x_2565_, v_t_2563_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_inc_ref(v_fallback_2564_);
return v_fallback_2564_;
}
else
{
lean_object* v_val_2567_; 
v_val_2567_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_val_2567_);
lean_dec_ref_known(v___x_2566_, 1);
return v_val_2567_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg___boxed(lean_object* v_inst_2568_, lean_object* v_k_2569_, lean_object* v_t_2570_, lean_object* v_fallback_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(v_inst_2568_, v_k_2569_, v_t_2570_, v_fallback_2571_);
lean_dec_ref(v_fallback_2571_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD(lean_object* v_00_u03b1_2573_, lean_object* v_00_u03b2_2574_, lean_object* v_inst_2575_, lean_object* v_k_2576_, lean_object* v_t_2577_, lean_object* v_fallback_2578_){
_start:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2579_ = lean_box(0);
v___x_2580_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2575_, v_k_2576_, v___x_2579_, v_t_2577_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_inc_ref(v_fallback_2578_);
return v_fallback_2578_;
}
else
{
lean_object* v_val_2581_; 
v_val_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_val_2581_);
lean_dec_ref_known(v___x_2580_, 1);
return v_val_2581_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___boxed(lean_object* v_00_u03b1_2582_, lean_object* v_00_u03b2_2583_, lean_object* v_inst_2584_, lean_object* v_k_2585_, lean_object* v_t_2586_, lean_object* v_fallback_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD(v_00_u03b1_2582_, v_00_u03b2_2583_, v_inst_2584_, v_k_2585_, v_t_2586_, v_fallback_2587_);
lean_dec_ref(v_fallback_2587_);
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(lean_object* v_inst_2589_, lean_object* v_k_2590_, lean_object* v_t_2591_, lean_object* v_fallback_2592_){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_box(0);
v___x_2594_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2589_, v_k_2590_, v___x_2593_, v_t_2591_);
if (lean_obj_tag(v___x_2594_) == 0)
{
lean_inc_ref(v_fallback_2592_);
return v_fallback_2592_;
}
else
{
lean_object* v_val_2595_; 
v_val_2595_ = lean_ctor_get(v___x_2594_, 0);
lean_inc(v_val_2595_);
lean_dec_ref_known(v___x_2594_, 1);
return v_val_2595_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg___boxed(lean_object* v_inst_2596_, lean_object* v_k_2597_, lean_object* v_t_2598_, lean_object* v_fallback_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(v_inst_2596_, v_k_2597_, v_t_2598_, v_fallback_2599_);
lean_dec_ref(v_fallback_2599_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED(lean_object* v_00_u03b1_2601_, lean_object* v_00_u03b2_2602_, lean_object* v_inst_2603_, lean_object* v_k_2604_, lean_object* v_t_2605_, lean_object* v_fallback_2606_){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2607_ = lean_box(0);
v___x_2608_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2603_, v_k_2604_, v___x_2607_, v_t_2605_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_inc_ref(v_fallback_2606_);
return v_fallback_2606_;
}
else
{
lean_object* v_val_2609_; 
v_val_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_val_2609_);
lean_dec_ref_known(v___x_2608_, 1);
return v_val_2609_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___boxed(lean_object* v_00_u03b1_2610_, lean_object* v_00_u03b2_2611_, lean_object* v_inst_2612_, lean_object* v_k_2613_, lean_object* v_t_2614_, lean_object* v_fallback_2615_){
_start:
{
lean_object* v_res_2616_; 
v_res_2616_ = l_Std_DTreeMap_Internal_Impl_getEntryLED(v_00_u03b1_2610_, v_00_u03b2_2611_, v_inst_2612_, v_k_2613_, v_t_2614_, v_fallback_2615_);
lean_dec_ref(v_fallback_2615_);
return v_res_2616_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(lean_object* v_inst_2617_, lean_object* v_k_2618_, lean_object* v_t_2619_, lean_object* v_fallback_2620_){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_box(0);
v___x_2622_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2617_, v_k_2618_, v___x_2621_, v_t_2619_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_inc_ref(v_fallback_2620_);
return v_fallback_2620_;
}
else
{
lean_object* v_val_2623_; 
v_val_2623_ = lean_ctor_get(v___x_2622_, 0);
lean_inc(v_val_2623_);
lean_dec_ref_known(v___x_2622_, 1);
return v_val_2623_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg___boxed(lean_object* v_inst_2624_, lean_object* v_k_2625_, lean_object* v_t_2626_, lean_object* v_fallback_2627_){
_start:
{
lean_object* v_res_2628_; 
v_res_2628_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(v_inst_2624_, v_k_2625_, v_t_2626_, v_fallback_2627_);
lean_dec_ref(v_fallback_2627_);
return v_res_2628_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD(lean_object* v_00_u03b1_2629_, lean_object* v_00_u03b2_2630_, lean_object* v_inst_2631_, lean_object* v_k_2632_, lean_object* v_t_2633_, lean_object* v_fallback_2634_){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2635_ = lean_box(0);
v___x_2636_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2631_, v_k_2632_, v___x_2635_, v_t_2633_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_inc_ref(v_fallback_2634_);
return v_fallback_2634_;
}
else
{
lean_object* v_val_2637_; 
v_val_2637_ = lean_ctor_get(v___x_2636_, 0);
lean_inc(v_val_2637_);
lean_dec_ref_known(v___x_2636_, 1);
return v_val_2637_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___boxed(lean_object* v_00_u03b1_2638_, lean_object* v_00_u03b2_2639_, lean_object* v_inst_2640_, lean_object* v_k_2641_, lean_object* v_t_2642_, lean_object* v_fallback_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD(v_00_u03b1_2638_, v_00_u03b2_2639_, v_inst_2640_, v_k_2641_, v_t_2642_, v_fallback_2643_);
lean_dec_ref(v_fallback_2643_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(lean_object* v_inst_2645_, lean_object* v_k_2646_, lean_object* v_x_2647_){
_start:
{
lean_object* v_k_2648_; lean_object* v_v_2649_; lean_object* v_l_2650_; lean_object* v_r_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; 
v_k_2648_ = lean_ctor_get(v_x_2647_, 1);
lean_inc_n(v_k_2648_, 2);
v_v_2649_ = lean_ctor_get(v_x_2647_, 2);
lean_inc(v_v_2649_);
v_l_2650_ = lean_ctor_get(v_x_2647_, 3);
lean_inc(v_l_2650_);
v_r_2651_ = lean_ctor_get(v_x_2647_, 4);
lean_inc(v_r_2651_);
lean_dec(v_x_2647_);
lean_inc_ref(v_inst_2645_);
lean_inc(v_k_2646_);
v___x_2652_ = lean_apply_2(v_inst_2645_, v_k_2646_, v_k_2648_);
v___x_2653_ = lean_unbox(v___x_2652_);
switch(v___x_2653_)
{
case 0:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec(v_r_2651_);
v___x_2654_ = lean_box(0);
v___x_2655_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2645_, v_k_2646_, v___x_2654_, v_l_2650_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v___x_2656_; 
v___x_2656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2656_, 0, v_k_2648_);
lean_ctor_set(v___x_2656_, 1, v_v_2649_);
return v___x_2656_;
}
else
{
lean_object* v_val_2657_; 
lean_dec(v_v_2649_);
lean_dec(v_k_2648_);
v_val_2657_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_val_2657_);
lean_dec_ref_known(v___x_2655_, 1);
return v_val_2657_;
}
}
case 1:
{
lean_object* v___x_2658_; 
lean_dec(v_r_2651_);
lean_dec(v_l_2650_);
lean_dec(v_k_2646_);
lean_dec_ref(v_inst_2645_);
v___x_2658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2658_, 0, v_k_2648_);
lean_ctor_set(v___x_2658_, 1, v_v_2649_);
return v___x_2658_;
}
default: 
{
lean_dec(v_l_2650_);
lean_dec(v_v_2649_);
lean_dec(v_k_2648_);
v_x_2647_ = v_r_2651_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE(lean_object* v_00_u03b1_2660_, lean_object* v_00_u03b2_2661_, lean_object* v_inst_2662_, lean_object* v_inst_2663_, lean_object* v_k_2664_, lean_object* v_x_2665_, lean_object* v_x_2666_, lean_object* v_x_2667_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_inst_2662_, v_k_2664_, v_x_2665_);
return v___x_2668_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object* v_inst_2669_, lean_object* v_k_2670_, lean_object* v_x_2671_){
_start:
{
lean_object* v_k_2672_; lean_object* v_v_2673_; lean_object* v_l_2674_; lean_object* v_r_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; uint8_t v___x_2679_; 
v_k_2672_ = lean_ctor_get(v_x_2671_, 1);
lean_inc_n(v_k_2672_, 2);
v_v_2673_ = lean_ctor_get(v_x_2671_, 2);
lean_inc(v_v_2673_);
v_l_2674_ = lean_ctor_get(v_x_2671_, 3);
lean_inc(v_l_2674_);
v_r_2675_ = lean_ctor_get(v_x_2671_, 4);
lean_inc(v_r_2675_);
lean_dec(v_x_2671_);
lean_inc_ref(v_inst_2669_);
lean_inc(v_k_2670_);
v___x_2676_ = lean_apply_2(v_inst_2669_, v_k_2670_, v_k_2672_);
v___x_2677_ = lean_obj_tag_nat(v___x_2676_);
v___x_2678_ = lean_unsigned_to_nat(0u);
v___x_2679_ = lean_nat_dec_eq(v___x_2677_, v___x_2678_);
if (v___x_2679_ == 0)
{
lean_dec(v_l_2674_);
lean_dec(v_v_2673_);
lean_dec(v_k_2672_);
v_x_2671_ = v_r_2675_;
goto _start;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; 
lean_dec(v_r_2675_);
v___x_2681_ = lean_box(0);
v___x_2682_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2669_, v_k_2670_, v___x_2681_, v_l_2674_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2683_; 
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_k_2672_);
lean_ctor_set(v___x_2683_, 1, v_v_2673_);
return v___x_2683_;
}
else
{
lean_object* v_val_2684_; 
lean_dec(v_v_2673_);
lean_dec(v_k_2672_);
v_val_2684_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_val_2684_);
lean_dec_ref_known(v___x_2682_, 1);
return v_val_2684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object* v_00_u03b1_2685_, lean_object* v_00_u03b2_2686_, lean_object* v_inst_2687_, lean_object* v_inst_2688_, lean_object* v_k_2689_, lean_object* v_x_2690_, lean_object* v_x_2691_, lean_object* v_x_2692_){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_inst_2687_, v_k_2689_, v_x_2690_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object* v_inst_2694_, lean_object* v_k_2695_, lean_object* v_x_2696_){
_start:
{
lean_object* v_k_2697_; lean_object* v_v_2698_; lean_object* v_l_2699_; lean_object* v_r_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; 
v_k_2697_ = lean_ctor_get(v_x_2696_, 1);
lean_inc_n(v_k_2697_, 2);
v_v_2698_ = lean_ctor_get(v_x_2696_, 2);
lean_inc(v_v_2698_);
v_l_2699_ = lean_ctor_get(v_x_2696_, 3);
lean_inc(v_l_2699_);
v_r_2700_ = lean_ctor_get(v_x_2696_, 4);
lean_inc(v_r_2700_);
lean_dec(v_x_2696_);
lean_inc_ref(v_inst_2694_);
lean_inc(v_k_2695_);
v___x_2701_ = lean_apply_2(v_inst_2694_, v_k_2695_, v_k_2697_);
v___x_2702_ = lean_unbox(v___x_2701_);
switch(v___x_2702_)
{
case 0:
{
lean_dec(v_r_2700_);
lean_dec(v_v_2698_);
lean_dec(v_k_2697_);
v_x_2696_ = v_l_2699_;
goto _start;
}
case 1:
{
lean_object* v___x_2704_; 
lean_dec(v_r_2700_);
lean_dec(v_l_2699_);
lean_dec(v_k_2695_);
lean_dec_ref(v_inst_2694_);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v_k_2697_);
lean_ctor_set(v___x_2704_, 1, v_v_2698_);
return v___x_2704_;
}
default: 
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
lean_dec(v_l_2699_);
v___x_2705_ = lean_box(0);
v___x_2706_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2694_, v_k_2695_, v___x_2705_, v_r_2700_);
if (lean_obj_tag(v___x_2706_) == 0)
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v_k_2697_);
lean_ctor_set(v___x_2707_, 1, v_v_2698_);
return v___x_2707_;
}
else
{
lean_object* v_val_2708_; 
lean_dec(v_v_2698_);
lean_dec(v_k_2697_);
v_val_2708_ = lean_ctor_get(v___x_2706_, 0);
lean_inc(v_val_2708_);
lean_dec_ref_known(v___x_2706_, 1);
return v_val_2708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object* v_00_u03b1_2709_, lean_object* v_00_u03b2_2710_, lean_object* v_inst_2711_, lean_object* v_inst_2712_, lean_object* v_k_2713_, lean_object* v_x_2714_, lean_object* v_x_2715_, lean_object* v_x_2716_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_inst_2711_, v_k_2713_, v_x_2714_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object* v_inst_2718_, lean_object* v_k_2719_, lean_object* v_x_2720_){
_start:
{
lean_object* v_k_2721_; lean_object* v_v_2722_; lean_object* v_l_2723_; lean_object* v_r_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v_k_2721_ = lean_ctor_get(v_x_2720_, 1);
lean_inc_n(v_k_2721_, 2);
v_v_2722_ = lean_ctor_get(v_x_2720_, 2);
lean_inc(v_v_2722_);
v_l_2723_ = lean_ctor_get(v_x_2720_, 3);
lean_inc(v_l_2723_);
v_r_2724_ = lean_ctor_get(v_x_2720_, 4);
lean_inc(v_r_2724_);
lean_dec(v_x_2720_);
lean_inc_ref(v_inst_2718_);
lean_inc(v_k_2719_);
v___x_2725_ = lean_apply_2(v_inst_2718_, v_k_2719_, v_k_2721_);
v___x_2726_ = lean_obj_tag_nat(v___x_2725_);
v___x_2727_ = lean_unsigned_to_nat(2u);
v___x_2728_ = lean_nat_dec_eq(v___x_2726_, v___x_2727_);
if (v___x_2728_ == 0)
{
lean_dec(v_r_2724_);
lean_dec(v_v_2722_);
lean_dec(v_k_2721_);
v_x_2720_ = v_l_2723_;
goto _start;
}
else
{
lean_object* v___x_2730_; lean_object* v___x_2731_; 
lean_dec(v_l_2723_);
v___x_2730_ = lean_box(0);
v___x_2731_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2718_, v_k_2719_, v___x_2730_, v_r_2724_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v___x_2732_; 
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_k_2721_);
lean_ctor_set(v___x_2732_, 1, v_v_2722_);
return v___x_2732_;
}
else
{
lean_object* v_val_2733_; 
lean_dec(v_v_2722_);
lean_dec(v_k_2721_);
v_val_2733_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_val_2733_);
lean_dec_ref_known(v___x_2731_, 1);
return v_val_2733_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT(lean_object* v_00_u03b1_2734_, lean_object* v_00_u03b2_2735_, lean_object* v_inst_2736_, lean_object* v_inst_2737_, lean_object* v_k_2738_, lean_object* v_x_2739_, lean_object* v_x_2740_, lean_object* v_x_2741_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_inst_2736_, v_k_2738_, v_x_2739_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object* v_inst_2743_, lean_object* v_k_2744_, lean_object* v_best_2745_, lean_object* v_a_2746_){
_start:
{
if (lean_obj_tag(v_a_2746_) == 0)
{
lean_object* v_k_2747_; lean_object* v_l_2748_; lean_object* v_r_2749_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v_k_2747_ = lean_ctor_get(v_a_2746_, 1);
lean_inc_n(v_k_2747_, 2);
v_l_2748_ = lean_ctor_get(v_a_2746_, 3);
lean_inc(v_l_2748_);
v_r_2749_ = lean_ctor_get(v_a_2746_, 4);
lean_inc(v_r_2749_);
lean_dec_ref_known(v_a_2746_, 5);
lean_inc_ref(v_inst_2743_);
lean_inc(v_k_2744_);
v___x_2750_ = lean_apply_2(v_inst_2743_, v_k_2744_, v_k_2747_);
v___x_2751_ = lean_unbox(v___x_2750_);
switch(v___x_2751_)
{
case 0:
{
lean_object* v___x_2752_; 
lean_dec(v_r_2749_);
lean_dec(v_best_2745_);
v___x_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2752_, 0, v_k_2747_);
v_best_2745_ = v___x_2752_;
v_a_2746_ = v_l_2748_;
goto _start;
}
case 1:
{
lean_object* v___x_2754_; 
lean_dec(v_r_2749_);
lean_dec(v_l_2748_);
lean_dec(v_best_2745_);
lean_dec(v_k_2744_);
lean_dec_ref(v_inst_2743_);
v___x_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_k_2747_);
return v___x_2754_;
}
default: 
{
lean_dec(v_l_2748_);
lean_dec(v_k_2747_);
v_a_2746_ = v_r_2749_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2744_);
lean_dec_ref(v_inst_2743_);
return v_best_2745_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(lean_object* v_00_u03b1_2756_, lean_object* v_00_u03b2_2757_, lean_object* v_inst_2758_, lean_object* v_k_2759_, lean_object* v_best_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v___x_2762_; 
v___x_2762_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2758_, v_k_2759_, v_best_2760_, v_a_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___redArg(lean_object* v_inst_2763_, lean_object* v_k_2764_, lean_object* v_a_2765_){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_box(0);
v___x_2767_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2763_, v_k_2764_, v___x_2766_, v_a_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(lean_object* v_00_u03b1_2768_, lean_object* v_00_u03b2_2769_, lean_object* v_inst_2770_, lean_object* v_k_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = lean_box(0);
v___x_2774_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2770_, v_k_2771_, v___x_2773_, v_a_2772_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object* v_inst_2775_, lean_object* v_k_2776_, lean_object* v_best_2777_, lean_object* v_a_2778_){
_start:
{
if (lean_obj_tag(v_a_2778_) == 0)
{
lean_object* v_k_2779_; lean_object* v_l_2780_; lean_object* v_r_2781_; lean_object* v___x_2782_; uint8_t v___x_2783_; 
v_k_2779_ = lean_ctor_get(v_a_2778_, 1);
lean_inc_n(v_k_2779_, 2);
v_l_2780_ = lean_ctor_get(v_a_2778_, 3);
lean_inc(v_l_2780_);
v_r_2781_ = lean_ctor_get(v_a_2778_, 4);
lean_inc(v_r_2781_);
lean_dec_ref_known(v_a_2778_, 5);
lean_inc_ref(v_inst_2775_);
lean_inc(v_k_2776_);
v___x_2782_ = lean_apply_2(v_inst_2775_, v_k_2776_, v_k_2779_);
v___x_2783_ = lean_unbox(v___x_2782_);
if (v___x_2783_ == 0)
{
lean_object* v___x_2784_; 
lean_dec(v_r_2781_);
lean_dec(v_best_2777_);
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v_k_2779_);
v_best_2777_ = v___x_2784_;
v_a_2778_ = v_l_2780_;
goto _start;
}
else
{
lean_dec(v_l_2780_);
lean_dec(v_k_2779_);
v_a_2778_ = v_r_2781_;
goto _start;
}
}
else
{
lean_dec(v_k_2776_);
lean_dec_ref(v_inst_2775_);
return v_best_2777_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(lean_object* v_00_u03b1_2787_, lean_object* v_00_u03b2_2788_, lean_object* v_inst_2789_, lean_object* v_k_2790_, lean_object* v_best_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___x_2793_; 
v___x_2793_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2789_, v_k_2790_, v_best_2791_, v_a_2792_);
return v___x_2793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___redArg(lean_object* v_inst_2794_, lean_object* v_k_2795_, lean_object* v_a_2796_){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_box(0);
v___x_2798_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2794_, v_k_2795_, v___x_2797_, v_a_2796_);
return v___x_2798_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(lean_object* v_00_u03b1_2799_, lean_object* v_00_u03b2_2800_, lean_object* v_inst_2801_, lean_object* v_k_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = lean_box(0);
v___x_2805_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2801_, v_k_2802_, v___x_2804_, v_a_2803_);
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object* v_inst_2806_, lean_object* v_k_2807_, lean_object* v_best_2808_, lean_object* v_a_2809_){
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
switch(v___x_2814_)
{
case 0:
{
lean_dec(v_r_2812_);
lean_dec(v_k_2810_);
v_a_2809_ = v_l_2811_;
goto _start;
}
case 1:
{
lean_object* v___x_2816_; 
lean_dec(v_r_2812_);
lean_dec(v_l_2811_);
lean_dec(v_best_2808_);
lean_dec(v_k_2807_);
lean_dec_ref(v_inst_2806_);
v___x_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2816_, 0, v_k_2810_);
return v___x_2816_;
}
default: 
{
lean_object* v___x_2817_; 
lean_dec(v_l_2811_);
lean_dec(v_best_2808_);
v___x_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2817_, 0, v_k_2810_);
v_best_2808_ = v___x_2817_;
v_a_2809_ = v_r_2812_;
goto _start;
}
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(lean_object* v_00_u03b1_2819_, lean_object* v_00_u03b2_2820_, lean_object* v_inst_2821_, lean_object* v_k_2822_, lean_object* v_best_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v___x_2825_; 
v___x_2825_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2821_, v_k_2822_, v_best_2823_, v_a_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___redArg(lean_object* v_inst_2826_, lean_object* v_k_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = lean_box(0);
v___x_2830_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2826_, v_k_2827_, v___x_2829_, v_a_2828_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(lean_object* v_00_u03b1_2831_, lean_object* v_00_u03b2_2832_, lean_object* v_inst_2833_, lean_object* v_k_2834_, lean_object* v_a_2835_){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2836_ = lean_box(0);
v___x_2837_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2833_, v_k_2834_, v___x_2836_, v_a_2835_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object* v_inst_2838_, lean_object* v_k_2839_, lean_object* v_best_2840_, lean_object* v_a_2841_){
_start:
{
if (lean_obj_tag(v_a_2841_) == 0)
{
lean_object* v_k_2842_; lean_object* v_l_2843_; lean_object* v_r_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v_k_2842_ = lean_ctor_get(v_a_2841_, 1);
lean_inc_n(v_k_2842_, 2);
v_l_2843_ = lean_ctor_get(v_a_2841_, 3);
lean_inc(v_l_2843_);
v_r_2844_ = lean_ctor_get(v_a_2841_, 4);
lean_inc(v_r_2844_);
lean_dec_ref_known(v_a_2841_, 5);
lean_inc_ref(v_inst_2838_);
lean_inc(v_k_2839_);
v___x_2845_ = lean_apply_2(v_inst_2838_, v_k_2839_, v_k_2842_);
v___x_2846_ = lean_unbox(v___x_2845_);
if (v___x_2846_ == 2)
{
lean_object* v___x_2847_; 
lean_dec(v_l_2843_);
lean_dec(v_best_2840_);
v___x_2847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2847_, 0, v_k_2842_);
v_best_2840_ = v___x_2847_;
v_a_2841_ = v_r_2844_;
goto _start;
}
else
{
lean_dec(v_r_2844_);
lean_dec(v_k_2842_);
v_a_2841_ = v_l_2843_;
goto _start;
}
}
else
{
lean_dec(v_k_2839_);
lean_dec_ref(v_inst_2838_);
return v_best_2840_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(lean_object* v_00_u03b1_2850_, lean_object* v_00_u03b2_2851_, lean_object* v_inst_2852_, lean_object* v_k_2853_, lean_object* v_best_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2856_; 
v___x_2856_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2852_, v_k_2853_, v_best_2854_, v_a_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___redArg(lean_object* v_inst_2857_, lean_object* v_k_2858_, lean_object* v_a_2859_){
_start:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; 
v___x_2860_ = lean_box(0);
v___x_2861_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2857_, v_k_2858_, v___x_2860_, v_a_2859_);
return v___x_2861_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(lean_object* v_00_u03b1_2862_, lean_object* v_00_u03b2_2863_, lean_object* v_inst_2864_, lean_object* v_k_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; 
v___x_2867_ = lean_box(0);
v___x_2868_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2864_, v_k_2865_, v___x_2867_, v_a_2866_);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(lean_object* v_inst_2869_, lean_object* v_inst_2870_, lean_object* v_k_2871_, lean_object* v_t_2872_){
_start:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; 
v___x_2873_ = lean_box(0);
v___x_2874_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2869_, v_k_2871_, v___x_2873_, v_t_2872_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2875_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2876_ = l_panic___redArg(v_inst_2870_, v___x_2875_);
return v___x_2876_;
}
else
{
lean_object* v_val_2877_; 
v_val_2877_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_val_2877_);
lean_dec_ref_known(v___x_2874_, 1);
return v_val_2877_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg___boxed(lean_object* v_inst_2878_, lean_object* v_inst_2879_, lean_object* v_k_2880_, lean_object* v_t_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(v_inst_2878_, v_inst_2879_, v_k_2880_, v_t_2881_);
lean_dec(v_inst_2879_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object* v_00_u03b1_2883_, lean_object* v_00_u03b2_2884_, lean_object* v_inst_2885_, lean_object* v_inst_2886_, lean_object* v_k_2887_, lean_object* v_t_2888_){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_box(0);
v___x_2890_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2885_, v_k_2887_, v___x_2889_, v_t_2888_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2892_ = l_panic___redArg(v_inst_2886_, v___x_2891_);
return v___x_2892_;
}
else
{
lean_object* v_val_2893_; 
v_val_2893_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_val_2893_);
lean_dec_ref_known(v___x_2890_, 1);
return v_val_2893_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___boxed(lean_object* v_00_u03b1_2894_, lean_object* v_00_u03b2_2895_, lean_object* v_inst_2896_, lean_object* v_inst_2897_, lean_object* v_k_2898_, lean_object* v_t_2899_){
_start:
{
lean_object* v_res_2900_; 
v_res_2900_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(v_00_u03b1_2894_, v_00_u03b2_2895_, v_inst_2896_, v_inst_2897_, v_k_2898_, v_t_2899_);
lean_dec(v_inst_2897_);
return v_res_2900_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(lean_object* v_inst_2901_, lean_object* v_inst_2902_, lean_object* v_k_2903_, lean_object* v_t_2904_){
_start:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = lean_box(0);
v___x_2906_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2901_, v_k_2903_, v___x_2905_, v_t_2904_);
if (lean_obj_tag(v___x_2906_) == 0)
{
lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2907_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2908_ = l_panic___redArg(v_inst_2902_, v___x_2907_);
return v___x_2908_;
}
else
{
lean_object* v_val_2909_; 
v_val_2909_ = lean_ctor_get(v___x_2906_, 0);
lean_inc(v_val_2909_);
lean_dec_ref_known(v___x_2906_, 1);
return v_val_2909_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg___boxed(lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_k_2912_, lean_object* v_t_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(v_inst_2910_, v_inst_2911_, v_k_2912_, v_t_2913_);
lean_dec(v_inst_2911_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object* v_00_u03b1_2915_, lean_object* v_00_u03b2_2916_, lean_object* v_inst_2917_, lean_object* v_inst_2918_, lean_object* v_k_2919_, lean_object* v_t_2920_){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_box(0);
v___x_2922_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2917_, v_k_2919_, v___x_2921_, v_t_2920_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2924_ = l_panic___redArg(v_inst_2918_, v___x_2923_);
return v___x_2924_;
}
else
{
lean_object* v_val_2925_; 
v_val_2925_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_val_2925_);
lean_dec_ref_known(v___x_2922_, 1);
return v_val_2925_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___boxed(lean_object* v_00_u03b1_2926_, lean_object* v_00_u03b2_2927_, lean_object* v_inst_2928_, lean_object* v_inst_2929_, lean_object* v_k_2930_, lean_object* v_t_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(v_00_u03b1_2926_, v_00_u03b2_2927_, v_inst_2928_, v_inst_2929_, v_k_2930_, v_t_2931_);
lean_dec(v_inst_2929_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(lean_object* v_inst_2933_, lean_object* v_inst_2934_, lean_object* v_k_2935_, lean_object* v_t_2936_){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_box(0);
v___x_2938_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2933_, v_k_2935_, v___x_2937_, v_t_2936_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2939_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2940_ = l_panic___redArg(v_inst_2934_, v___x_2939_);
return v___x_2940_;
}
else
{
lean_object* v_val_2941_; 
v_val_2941_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_val_2941_);
lean_dec_ref_known(v___x_2938_, 1);
return v_val_2941_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg___boxed(lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_k_2944_, lean_object* v_t_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(v_inst_2942_, v_inst_2943_, v_k_2944_, v_t_2945_);
lean_dec(v_inst_2943_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object* v_00_u03b1_2947_, lean_object* v_00_u03b2_2948_, lean_object* v_inst_2949_, lean_object* v_inst_2950_, lean_object* v_k_2951_, lean_object* v_t_2952_){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_box(0);
v___x_2954_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2949_, v_k_2951_, v___x_2953_, v_t_2952_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2955_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2956_ = l_panic___redArg(v_inst_2950_, v___x_2955_);
return v___x_2956_;
}
else
{
lean_object* v_val_2957_; 
v_val_2957_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_val_2957_);
lean_dec_ref_known(v___x_2954_, 1);
return v_val_2957_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___boxed(lean_object* v_00_u03b1_2958_, lean_object* v_00_u03b2_2959_, lean_object* v_inst_2960_, lean_object* v_inst_2961_, lean_object* v_k_2962_, lean_object* v_t_2963_){
_start:
{
lean_object* v_res_2964_; 
v_res_2964_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(v_00_u03b1_2958_, v_00_u03b2_2959_, v_inst_2960_, v_inst_2961_, v_k_2962_, v_t_2963_);
lean_dec(v_inst_2961_);
return v_res_2964_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(lean_object* v_inst_2965_, lean_object* v_inst_2966_, lean_object* v_k_2967_, lean_object* v_t_2968_){
_start:
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_box(0);
v___x_2970_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2965_, v_k_2967_, v___x_2969_, v_t_2968_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2972_ = l_panic___redArg(v_inst_2966_, v___x_2971_);
return v___x_2972_;
}
else
{
lean_object* v_val_2973_; 
v_val_2973_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_val_2973_);
lean_dec_ref_known(v___x_2970_, 1);
return v_val_2973_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg___boxed(lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_k_2976_, lean_object* v_t_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(v_inst_2974_, v_inst_2975_, v_k_2976_, v_t_2977_);
lean_dec(v_inst_2975_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object* v_00_u03b1_2979_, lean_object* v_00_u03b2_2980_, lean_object* v_inst_2981_, lean_object* v_inst_2982_, lean_object* v_k_2983_, lean_object* v_t_2984_){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_box(0);
v___x_2986_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2981_, v_k_2983_, v___x_2985_, v_t_2984_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2988_ = l_panic___redArg(v_inst_2982_, v___x_2987_);
return v___x_2988_;
}
else
{
lean_object* v_val_2989_; 
v_val_2989_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_val_2989_);
lean_dec_ref_known(v___x_2986_, 1);
return v_val_2989_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___boxed(lean_object* v_00_u03b1_2990_, lean_object* v_00_u03b2_2991_, lean_object* v_inst_2992_, lean_object* v_inst_2993_, lean_object* v_k_2994_, lean_object* v_t_2995_){
_start:
{
lean_object* v_res_2996_; 
v_res_2996_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(v_00_u03b1_2990_, v_00_u03b2_2991_, v_inst_2992_, v_inst_2993_, v_k_2994_, v_t_2995_);
lean_dec(v_inst_2993_);
return v_res_2996_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(lean_object* v_inst_2997_, lean_object* v_k_2998_, lean_object* v_t_2999_, lean_object* v_fallback_3000_){
_start:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_box(0);
v___x_3002_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2997_, v_k_2998_, v___x_3001_, v_t_2999_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_inc(v_fallback_3000_);
return v_fallback_3000_;
}
else
{
lean_object* v_val_3003_; 
v_val_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_val_3003_);
lean_dec_ref_known(v___x_3002_, 1);
return v_val_3003_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg___boxed(lean_object* v_inst_3004_, lean_object* v_k_3005_, lean_object* v_t_3006_, lean_object* v_fallback_3007_){
_start:
{
lean_object* v_res_3008_; 
v_res_3008_ = l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(v_inst_3004_, v_k_3005_, v_t_3006_, v_fallback_3007_);
lean_dec(v_fallback_3007_);
return v_res_3008_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED(lean_object* v_00_u03b1_3009_, lean_object* v_00_u03b2_3010_, lean_object* v_inst_3011_, lean_object* v_k_3012_, lean_object* v_t_3013_, lean_object* v_fallback_3014_){
_start:
{
lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3015_ = lean_box(0);
v___x_3016_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3011_, v_k_3012_, v___x_3015_, v_t_3013_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_inc(v_fallback_3014_);
return v_fallback_3014_;
}
else
{
lean_object* v_val_3017_; 
v_val_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_val_3017_);
lean_dec_ref_known(v___x_3016_, 1);
return v_val_3017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___boxed(lean_object* v_00_u03b1_3018_, lean_object* v_00_u03b2_3019_, lean_object* v_inst_3020_, lean_object* v_k_3021_, lean_object* v_t_3022_, lean_object* v_fallback_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Std_DTreeMap_Internal_Impl_getKeyGED(v_00_u03b1_3018_, v_00_u03b2_3019_, v_inst_3020_, v_k_3021_, v_t_3022_, v_fallback_3023_);
lean_dec(v_fallback_3023_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(lean_object* v_inst_3025_, lean_object* v_k_3026_, lean_object* v_t_3027_, lean_object* v_fallback_3028_){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_box(0);
v___x_3030_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3025_, v_k_3026_, v___x_3029_, v_t_3027_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_inc(v_fallback_3028_);
return v_fallback_3028_;
}
else
{
lean_object* v_val_3031_; 
v_val_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_val_3031_);
lean_dec_ref_known(v___x_3030_, 1);
return v_val_3031_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg___boxed(lean_object* v_inst_3032_, lean_object* v_k_3033_, lean_object* v_t_3034_, lean_object* v_fallback_3035_){
_start:
{
lean_object* v_res_3036_; 
v_res_3036_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(v_inst_3032_, v_k_3033_, v_t_3034_, v_fallback_3035_);
lean_dec(v_fallback_3035_);
return v_res_3036_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD(lean_object* v_00_u03b1_3037_, lean_object* v_00_u03b2_3038_, lean_object* v_inst_3039_, lean_object* v_k_3040_, lean_object* v_t_3041_, lean_object* v_fallback_3042_){
_start:
{
lean_object* v___x_3043_; lean_object* v___x_3044_; 
v___x_3043_ = lean_box(0);
v___x_3044_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3039_, v_k_3040_, v___x_3043_, v_t_3041_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_inc(v_fallback_3042_);
return v_fallback_3042_;
}
else
{
lean_object* v_val_3045_; 
v_val_3045_ = lean_ctor_get(v___x_3044_, 0);
lean_inc(v_val_3045_);
lean_dec_ref_known(v___x_3044_, 1);
return v_val_3045_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___boxed(lean_object* v_00_u03b1_3046_, lean_object* v_00_u03b2_3047_, lean_object* v_inst_3048_, lean_object* v_k_3049_, lean_object* v_t_3050_, lean_object* v_fallback_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD(v_00_u03b1_3046_, v_00_u03b2_3047_, v_inst_3048_, v_k_3049_, v_t_3050_, v_fallback_3051_);
lean_dec(v_fallback_3051_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(lean_object* v_inst_3053_, lean_object* v_k_3054_, lean_object* v_t_3055_, lean_object* v_fallback_3056_){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_box(0);
v___x_3058_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3053_, v_k_3054_, v___x_3057_, v_t_3055_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_inc(v_fallback_3056_);
return v_fallback_3056_;
}
else
{
lean_object* v_val_3059_; 
v_val_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_val_3059_);
lean_dec_ref_known(v___x_3058_, 1);
return v_val_3059_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg___boxed(lean_object* v_inst_3060_, lean_object* v_k_3061_, lean_object* v_t_3062_, lean_object* v_fallback_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(v_inst_3060_, v_k_3061_, v_t_3062_, v_fallback_3063_);
lean_dec(v_fallback_3063_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED(lean_object* v_00_u03b1_3065_, lean_object* v_00_u03b2_3066_, lean_object* v_inst_3067_, lean_object* v_k_3068_, lean_object* v_t_3069_, lean_object* v_fallback_3070_){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; 
v___x_3071_ = lean_box(0);
v___x_3072_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3067_, v_k_3068_, v___x_3071_, v_t_3069_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_inc(v_fallback_3070_);
return v_fallback_3070_;
}
else
{
lean_object* v_val_3073_; 
v_val_3073_ = lean_ctor_get(v___x_3072_, 0);
lean_inc(v_val_3073_);
lean_dec_ref_known(v___x_3072_, 1);
return v_val_3073_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___boxed(lean_object* v_00_u03b1_3074_, lean_object* v_00_u03b2_3075_, lean_object* v_inst_3076_, lean_object* v_k_3077_, lean_object* v_t_3078_, lean_object* v_fallback_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Std_DTreeMap_Internal_Impl_getKeyLED(v_00_u03b1_3074_, v_00_u03b2_3075_, v_inst_3076_, v_k_3077_, v_t_3078_, v_fallback_3079_);
lean_dec(v_fallback_3079_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(lean_object* v_inst_3081_, lean_object* v_k_3082_, lean_object* v_t_3083_, lean_object* v_fallback_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = lean_box(0);
v___x_3086_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3081_, v_k_3082_, v___x_3085_, v_t_3083_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_inc(v_fallback_3084_);
return v_fallback_3084_;
}
else
{
lean_object* v_val_3087_; 
v_val_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc(v_val_3087_);
lean_dec_ref_known(v___x_3086_, 1);
return v_val_3087_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg___boxed(lean_object* v_inst_3088_, lean_object* v_k_3089_, lean_object* v_t_3090_, lean_object* v_fallback_3091_){
_start:
{
lean_object* v_res_3092_; 
v_res_3092_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(v_inst_3088_, v_k_3089_, v_t_3090_, v_fallback_3091_);
lean_dec(v_fallback_3091_);
return v_res_3092_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD(lean_object* v_00_u03b1_3093_, lean_object* v_00_u03b2_3094_, lean_object* v_inst_3095_, lean_object* v_k_3096_, lean_object* v_t_3097_, lean_object* v_fallback_3098_){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_box(0);
v___x_3100_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3095_, v_k_3096_, v___x_3099_, v_t_3097_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_inc(v_fallback_3098_);
return v_fallback_3098_;
}
else
{
lean_object* v_val_3101_; 
v_val_3101_ = lean_ctor_get(v___x_3100_, 0);
lean_inc(v_val_3101_);
lean_dec_ref_known(v___x_3100_, 1);
return v_val_3101_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___boxed(lean_object* v_00_u03b1_3102_, lean_object* v_00_u03b2_3103_, lean_object* v_inst_3104_, lean_object* v_k_3105_, lean_object* v_t_3106_, lean_object* v_fallback_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD(v_00_u03b1_3102_, v_00_u03b2_3103_, v_inst_3104_, v_k_3105_, v_t_3106_, v_fallback_3107_);
lean_dec(v_fallback_3107_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object* v_inst_3109_, lean_object* v_k_3110_, lean_object* v_x_3111_){
_start:
{
lean_object* v_k_3112_; lean_object* v_l_3113_; lean_object* v_r_3114_; lean_object* v___x_3115_; uint8_t v___x_3116_; 
v_k_3112_ = lean_ctor_get(v_x_3111_, 1);
lean_inc_n(v_k_3112_, 2);
v_l_3113_ = lean_ctor_get(v_x_3111_, 3);
lean_inc(v_l_3113_);
v_r_3114_ = lean_ctor_get(v_x_3111_, 4);
lean_inc(v_r_3114_);
lean_dec(v_x_3111_);
lean_inc_ref(v_inst_3109_);
lean_inc(v_k_3110_);
v___x_3115_ = lean_apply_2(v_inst_3109_, v_k_3110_, v_k_3112_);
v___x_3116_ = lean_unbox(v___x_3115_);
switch(v___x_3116_)
{
case 0:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; 
lean_dec(v_r_3114_);
v___x_3117_ = lean_box(0);
v___x_3118_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3109_, v_k_3110_, v___x_3117_, v_l_3113_);
if (lean_obj_tag(v___x_3118_) == 0)
{
return v_k_3112_;
}
else
{
lean_object* v_val_3119_; 
lean_dec(v_k_3112_);
v_val_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_val_3119_);
lean_dec_ref_known(v___x_3118_, 1);
return v_val_3119_;
}
}
case 1:
{
lean_dec(v_r_3114_);
lean_dec(v_l_3113_);
lean_dec(v_k_3110_);
lean_dec_ref(v_inst_3109_);
return v_k_3112_;
}
default: 
{
lean_dec(v_l_3113_);
lean_dec(v_k_3112_);
v_x_3111_ = v_r_3114_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE(lean_object* v_00_u03b1_3121_, lean_object* v_00_u03b2_3122_, lean_object* v_inst_3123_, lean_object* v_inst_3124_, lean_object* v_k_3125_, lean_object* v_x_3126_, lean_object* v_x_3127_, lean_object* v_x_3128_){
_start:
{
lean_object* v___x_3129_; 
v___x_3129_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_inst_3123_, v_k_3125_, v_x_3126_);
return v___x_3129_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object* v_inst_3130_, lean_object* v_k_3131_, lean_object* v_x_3132_){
_start:
{
lean_object* v_k_3133_; lean_object* v_l_3134_; lean_object* v_r_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v_k_3133_ = lean_ctor_get(v_x_3132_, 1);
lean_inc_n(v_k_3133_, 2);
v_l_3134_ = lean_ctor_get(v_x_3132_, 3);
lean_inc(v_l_3134_);
v_r_3135_ = lean_ctor_get(v_x_3132_, 4);
lean_inc(v_r_3135_);
lean_dec(v_x_3132_);
lean_inc_ref(v_inst_3130_);
lean_inc(v_k_3131_);
v___x_3136_ = lean_apply_2(v_inst_3130_, v_k_3131_, v_k_3133_);
v___x_3137_ = lean_obj_tag_nat(v___x_3136_);
v___x_3138_ = lean_unsigned_to_nat(0u);
v___x_3139_ = lean_nat_dec_eq(v___x_3137_, v___x_3138_);
if (v___x_3139_ == 0)
{
lean_dec(v_l_3134_);
lean_dec(v_k_3133_);
v_x_3132_ = v_r_3135_;
goto _start;
}
else
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
lean_dec(v_r_3135_);
v___x_3141_ = lean_box(0);
v___x_3142_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3130_, v_k_3131_, v___x_3141_, v_l_3134_);
if (lean_obj_tag(v___x_3142_) == 0)
{
return v_k_3133_;
}
else
{
lean_object* v_val_3143_; 
lean_dec(v_k_3133_);
v_val_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_val_3143_);
lean_dec_ref_known(v___x_3142_, 1);
return v_val_3143_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT(lean_object* v_00_u03b1_3144_, lean_object* v_00_u03b2_3145_, lean_object* v_inst_3146_, lean_object* v_inst_3147_, lean_object* v_k_3148_, lean_object* v_x_3149_, lean_object* v_x_3150_, lean_object* v_x_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_inst_3146_, v_k_3148_, v_x_3149_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object* v_inst_3153_, lean_object* v_k_3154_, lean_object* v_x_3155_){
_start:
{
lean_object* v_k_3156_; lean_object* v_l_3157_; lean_object* v_r_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
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
switch(v___x_3160_)
{
case 0:
{
lean_dec(v_r_3158_);
lean_dec(v_k_3156_);
v_x_3155_ = v_l_3157_;
goto _start;
}
case 1:
{
lean_dec(v_r_3158_);
lean_dec(v_l_3157_);
lean_dec(v_k_3154_);
lean_dec_ref(v_inst_3153_);
return v_k_3156_;
}
default: 
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
lean_dec(v_l_3157_);
v___x_3162_ = lean_box(0);
v___x_3163_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3153_, v_k_3154_, v___x_3162_, v_r_3158_);
if (lean_obj_tag(v___x_3163_) == 0)
{
return v_k_3156_;
}
else
{
lean_object* v_val_3164_; 
lean_dec(v_k_3156_);
v_val_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_val_3164_);
lean_dec_ref_known(v___x_3163_, 1);
return v_val_3164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE(lean_object* v_00_u03b1_3165_, lean_object* v_00_u03b2_3166_, lean_object* v_inst_3167_, lean_object* v_inst_3168_, lean_object* v_k_3169_, lean_object* v_x_3170_, lean_object* v_x_3171_, lean_object* v_x_3172_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_inst_3167_, v_k_3169_, v_x_3170_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object* v_inst_3174_, lean_object* v_k_3175_, lean_object* v_x_3176_){
_start:
{
lean_object* v_k_3177_; lean_object* v_l_3178_; lean_object* v_r_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v_k_3177_ = lean_ctor_get(v_x_3176_, 1);
lean_inc_n(v_k_3177_, 2);
v_l_3178_ = lean_ctor_get(v_x_3176_, 3);
lean_inc(v_l_3178_);
v_r_3179_ = lean_ctor_get(v_x_3176_, 4);
lean_inc(v_r_3179_);
lean_dec(v_x_3176_);
lean_inc_ref(v_inst_3174_);
lean_inc(v_k_3175_);
v___x_3180_ = lean_apply_2(v_inst_3174_, v_k_3175_, v_k_3177_);
v___x_3181_ = lean_obj_tag_nat(v___x_3180_);
v___x_3182_ = lean_unsigned_to_nat(2u);
v___x_3183_ = lean_nat_dec_eq(v___x_3181_, v___x_3182_);
if (v___x_3183_ == 0)
{
lean_dec(v_r_3179_);
lean_dec(v_k_3177_);
v_x_3176_ = v_l_3178_;
goto _start;
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
lean_dec(v_l_3178_);
v___x_3185_ = lean_box(0);
v___x_3186_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3174_, v_k_3175_, v___x_3185_, v_r_3179_);
if (lean_obj_tag(v___x_3186_) == 0)
{
return v_k_3177_;
}
else
{
lean_object* v_val_3187_; 
lean_dec(v_k_3177_);
v_val_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc(v_val_3187_);
lean_dec_ref_known(v___x_3186_, 1);
return v_val_3187_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT(lean_object* v_00_u03b1_3188_, lean_object* v_00_u03b2_3189_, lean_object* v_inst_3190_, lean_object* v_inst_3191_, lean_object* v_k_3192_, lean_object* v_x_3193_, lean_object* v_x_3194_, lean_object* v_x_3195_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_inst_3190_, v_k_3192_, v_x_3193_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object* v_x_3197_){
_start:
{
if (lean_obj_tag(v_x_3197_) == 0)
{
lean_object* v_l_3198_; 
v_l_3198_ = lean_ctor_get(v_x_3197_, 3);
if (lean_obj_tag(v_l_3198_) == 0)
{
v_x_3197_ = v_l_3198_;
goto _start;
}
else
{
lean_object* v_k_3200_; lean_object* v_v_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v_k_3200_ = lean_ctor_get(v_x_3197_, 1);
v_v_3201_ = lean_ctor_get(v_x_3197_, 2);
lean_inc(v_v_3201_);
lean_inc(v_k_3200_);
v___x_3202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3202_, 0, v_k_3200_);
lean_ctor_set(v___x_3202_, 1, v_v_3201_);
v___x_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3203_, 0, v___x_3202_);
return v___x_3203_;
}
}
else
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_box(0);
return v___x_3204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg___boxed(lean_object* v_x_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3205_);
lean_dec(v_x_3205_);
return v_res_3206_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(lean_object* v_00_u03b1_3207_, lean_object* v_00_u03b2_3208_, lean_object* v_x_3209_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_3211_, lean_object* v_00_u03b2_3212_, lean_object* v_x_3213_){
_start:
{
lean_object* v_res_3214_; 
v_res_3214_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(v_00_u03b1_3211_, v_00_u03b2_3212_, v_x_3213_);
lean_dec(v_x_3213_);
return v_res_3214_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3215_, lean_object* v_h__1_3216_, lean_object* v_h__2_3217_, lean_object* v_h__3_3218_){
_start:
{
if (lean_obj_tag(v_x_3215_) == 0)
{
lean_object* v_l_3219_; 
lean_dec(v_h__1_3216_);
v_l_3219_ = lean_ctor_get(v_x_3215_, 3);
if (lean_obj_tag(v_l_3219_) == 0)
{
lean_object* v_size_3220_; lean_object* v_k_3221_; lean_object* v_v_3222_; lean_object* v_r_3223_; lean_object* v_size_3224_; lean_object* v_k_3225_; lean_object* v_v_3226_; lean_object* v_l_3227_; lean_object* v_r_3228_; lean_object* v___x_3229_; 
lean_inc_ref(v_l_3219_);
lean_dec(v_h__2_3217_);
v_size_3220_ = lean_ctor_get(v_x_3215_, 0);
lean_inc(v_size_3220_);
v_k_3221_ = lean_ctor_get(v_x_3215_, 1);
lean_inc(v_k_3221_);
v_v_3222_ = lean_ctor_get(v_x_3215_, 2);
lean_inc(v_v_3222_);
v_r_3223_ = lean_ctor_get(v_x_3215_, 4);
lean_inc(v_r_3223_);
lean_dec_ref_known(v_x_3215_, 5);
v_size_3224_ = lean_ctor_get(v_l_3219_, 0);
lean_inc(v_size_3224_);
v_k_3225_ = lean_ctor_get(v_l_3219_, 1);
lean_inc(v_k_3225_);
v_v_3226_ = lean_ctor_get(v_l_3219_, 2);
lean_inc(v_v_3226_);
v_l_3227_ = lean_ctor_get(v_l_3219_, 3);
lean_inc(v_l_3227_);
v_r_3228_ = lean_ctor_get(v_l_3219_, 4);
lean_inc(v_r_3228_);
lean_dec_ref_known(v_l_3219_, 5);
v___x_3229_ = lean_apply_9(v_h__3_3218_, v_size_3220_, v_k_3221_, v_v_3222_, v_size_3224_, v_k_3225_, v_v_3226_, v_l_3227_, v_r_3228_, v_r_3223_);
return v___x_3229_;
}
else
{
lean_object* v_size_3230_; lean_object* v_k_3231_; lean_object* v_v_3232_; lean_object* v_r_3233_; lean_object* v___x_3234_; 
lean_dec(v_h__3_3218_);
v_size_3230_ = lean_ctor_get(v_x_3215_, 0);
lean_inc(v_size_3230_);
v_k_3231_ = lean_ctor_get(v_x_3215_, 1);
lean_inc(v_k_3231_);
v_v_3232_ = lean_ctor_get(v_x_3215_, 2);
lean_inc(v_v_3232_);
v_r_3233_ = lean_ctor_get(v_x_3215_, 4);
lean_inc(v_r_3233_);
lean_dec_ref_known(v_x_3215_, 5);
v___x_3234_ = lean_apply_4(v_h__2_3217_, v_size_3230_, v_k_3231_, v_v_3232_, v_r_3233_);
return v___x_3234_;
}
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
lean_dec(v_h__3_3218_);
lean_dec(v_h__2_3217_);
v___x_3235_ = lean_box(0);
v___x_3236_ = lean_apply_1(v_h__1_3216_, v___x_3235_);
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3237_, lean_object* v_00_u03b2_3238_, lean_object* v_motive_3239_, lean_object* v_x_3240_, lean_object* v_h__1_3241_, lean_object* v_h__2_3242_, lean_object* v_h__3_3243_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object* v_x_3262_){
_start:
{
lean_object* v_l_3263_; 
v_l_3263_ = lean_ctor_get(v_x_3262_, 3);
if (lean_obj_tag(v_l_3263_) == 0)
{
v_x_3262_ = v_l_3263_;
goto _start;
}
else
{
lean_object* v_k_3265_; lean_object* v_v_3266_; lean_object* v___x_3267_; 
v_k_3265_ = lean_ctor_get(v_x_3262_, 1);
v_v_3266_ = lean_ctor_get(v_x_3262_, 2);
lean_inc(v_v_3266_);
lean_inc(v_k_3265_);
v___x_3267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3267_, 0, v_k_3265_);
lean_ctor_set(v___x_3267_, 1, v_v_3266_);
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg___boxed(lean_object* v_x_3268_){
_start:
{
lean_object* v_res_3269_; 
v_res_3269_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3268_);
lean_dec(v_x_3268_);
return v_res_3269_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry(lean_object* v_00_u03b1_3270_, lean_object* v_00_u03b2_3271_, lean_object* v_x_3272_, lean_object* v_x_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3272_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___boxed(lean_object* v_00_u03b1_3275_, lean_object* v_00_u03b2_3276_, lean_object* v_x_3277_, lean_object* v_x_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry(v_00_u03b1_3275_, v_00_u03b2_3276_, v_x_3277_, v_x_3278_);
lean_dec(v_x_3277_);
return v_res_3279_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_3280_, lean_object* v_h__1_3281_, lean_object* v_h__2_3282_){
_start:
{
lean_object* v_l_3283_; 
v_l_3283_ = lean_ctor_get(v_x_3280_, 3);
if (lean_obj_tag(v_l_3283_) == 0)
{
lean_object* v_size_3284_; lean_object* v_k_3285_; lean_object* v_v_3286_; lean_object* v_r_3287_; lean_object* v_size_3288_; lean_object* v_k_3289_; lean_object* v_v_3290_; lean_object* v_l_3291_; lean_object* v_r_3292_; lean_object* v___x_3293_; 
lean_inc_ref(v_l_3283_);
lean_dec(v_h__1_3281_);
v_size_3284_ = lean_ctor_get(v_x_3280_, 0);
lean_inc(v_size_3284_);
v_k_3285_ = lean_ctor_get(v_x_3280_, 1);
lean_inc(v_k_3285_);
v_v_3286_ = lean_ctor_get(v_x_3280_, 2);
lean_inc(v_v_3286_);
v_r_3287_ = lean_ctor_get(v_x_3280_, 4);
lean_inc(v_r_3287_);
lean_dec(v_x_3280_);
v_size_3288_ = lean_ctor_get(v_l_3283_, 0);
lean_inc(v_size_3288_);
v_k_3289_ = lean_ctor_get(v_l_3283_, 1);
lean_inc(v_k_3289_);
v_v_3290_ = lean_ctor_get(v_l_3283_, 2);
lean_inc(v_v_3290_);
v_l_3291_ = lean_ctor_get(v_l_3283_, 3);
lean_inc(v_l_3291_);
v_r_3292_ = lean_ctor_get(v_l_3283_, 4);
lean_inc(v_r_3292_);
lean_dec_ref_known(v_l_3283_, 5);
v___x_3293_ = lean_apply_10(v_h__2_3282_, v_size_3284_, v_k_3285_, v_v_3286_, v_size_3288_, v_k_3289_, v_v_3290_, v_l_3291_, v_r_3292_, v_r_3287_, lean_box(0));
return v___x_3293_;
}
else
{
lean_object* v_size_3294_; lean_object* v_k_3295_; lean_object* v_v_3296_; lean_object* v_r_3297_; lean_object* v___x_3298_; 
lean_dec(v_h__2_3282_);
v_size_3294_ = lean_ctor_get(v_x_3280_, 0);
lean_inc(v_size_3294_);
v_k_3295_ = lean_ctor_get(v_x_3280_, 1);
lean_inc(v_k_3295_);
v_v_3296_ = lean_ctor_get(v_x_3280_, 2);
lean_inc(v_v_3296_);
v_r_3297_ = lean_ctor_get(v_x_3280_, 4);
lean_inc(v_r_3297_);
lean_dec(v_x_3280_);
v___x_3298_ = lean_apply_5(v_h__1_3281_, v_size_3294_, v_k_3295_, v_v_3296_, v_r_3297_, lean_box(0));
return v___x_3298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_3299_, lean_object* v_00_u03b2_3300_, lean_object* v_motive_3301_, lean_object* v_x_3302_, lean_object* v_x_3303_, lean_object* v_h__1_3304_, lean_object* v_h__2_3305_){
_start:
{
lean_object* v_l_3306_; 
v_l_3306_ = lean_ctor_get(v_x_3302_, 3);
if (lean_obj_tag(v_l_3306_) == 0)
{
lean_object* v_size_3307_; lean_object* v_k_3308_; lean_object* v_v_3309_; lean_object* v_r_3310_; lean_object* v_size_3311_; lean_object* v_k_3312_; lean_object* v_v_3313_; lean_object* v_l_3314_; lean_object* v_r_3315_; lean_object* v___x_3316_; 
lean_inc_ref(v_l_3306_);
lean_dec(v_h__1_3304_);
v_size_3307_ = lean_ctor_get(v_x_3302_, 0);
lean_inc(v_size_3307_);
v_k_3308_ = lean_ctor_get(v_x_3302_, 1);
lean_inc(v_k_3308_);
v_v_3309_ = lean_ctor_get(v_x_3302_, 2);
lean_inc(v_v_3309_);
v_r_3310_ = lean_ctor_get(v_x_3302_, 4);
lean_inc(v_r_3310_);
lean_dec(v_x_3302_);
v_size_3311_ = lean_ctor_get(v_l_3306_, 0);
lean_inc(v_size_3311_);
v_k_3312_ = lean_ctor_get(v_l_3306_, 1);
lean_inc(v_k_3312_);
v_v_3313_ = lean_ctor_get(v_l_3306_, 2);
lean_inc(v_v_3313_);
v_l_3314_ = lean_ctor_get(v_l_3306_, 3);
lean_inc(v_l_3314_);
v_r_3315_ = lean_ctor_get(v_l_3306_, 4);
lean_inc(v_r_3315_);
lean_dec_ref_known(v_l_3306_, 5);
v___x_3316_ = lean_apply_10(v_h__2_3305_, v_size_3307_, v_k_3308_, v_v_3309_, v_size_3311_, v_k_3312_, v_v_3313_, v_l_3314_, v_r_3315_, v_r_3310_, lean_box(0));
return v___x_3316_;
}
else
{
lean_object* v_size_3317_; lean_object* v_k_3318_; lean_object* v_v_3319_; lean_object* v_r_3320_; lean_object* v___x_3321_; 
lean_dec(v_h__2_3305_);
v_size_3317_ = lean_ctor_get(v_x_3302_, 0);
lean_inc(v_size_3317_);
v_k_3318_ = lean_ctor_get(v_x_3302_, 1);
lean_inc(v_k_3318_);
v_v_3319_ = lean_ctor_get(v_x_3302_, 2);
lean_inc(v_v_3319_);
v_r_3320_ = lean_ctor_get(v_x_3302_, 4);
lean_inc(v_r_3320_);
lean_dec(v_x_3302_);
v___x_3321_ = lean_apply_5(v_h__1_3304_, v_size_3317_, v_k_3318_, v_v_3319_, v_r_3320_, lean_box(0));
return v___x_3321_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v___x_3323_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3324_ = lean_unsigned_to_nat(13u);
v___x_3325_ = lean_unsigned_to_nat(816u);
v___x_3326_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0));
v___x_3327_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3328_ = l_mkPanicMessageWithDecl(v___x_3327_, v___x_3326_, v___x_3325_, v___x_3324_, v___x_3323_);
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object* v_inst_3329_, lean_object* v_x_3330_){
_start:
{
if (lean_obj_tag(v_x_3330_) == 0)
{
lean_object* v_l_3331_; 
v_l_3331_ = lean_ctor_get(v_x_3330_, 3);
if (lean_obj_tag(v_l_3331_) == 0)
{
v_x_3330_ = v_l_3331_;
goto _start;
}
else
{
lean_object* v_k_3333_; lean_object* v_v_3334_; lean_object* v___x_3335_; 
v_k_3333_ = lean_ctor_get(v_x_3330_, 1);
v_v_3334_ = lean_ctor_get(v_x_3330_, 2);
lean_inc(v_v_3334_);
lean_inc(v_k_3333_);
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v_k_3333_);
lean_ctor_set(v___x_3335_, 1, v_v_3334_);
return v___x_3335_;
}
}
else
{
lean_object* v___x_3336_; lean_object* v___x_3337_; 
v___x_3336_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1);
v___x_3337_ = l_panic___redArg(v_inst_3329_, v___x_3336_);
return v___x_3337_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_3338_, lean_object* v_x_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3338_, v_x_3339_);
lean_dec(v_x_3339_);
lean_dec_ref(v_inst_3338_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(lean_object* v_00_u03b1_3341_, lean_object* v_00_u03b2_3342_, lean_object* v_inst_3343_, lean_object* v_x_3344_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3343_, v_x_3344_);
return v___x_3345_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_3346_, lean_object* v_00_u03b2_3347_, lean_object* v_inst_3348_, lean_object* v_x_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(v_00_u03b1_3346_, v_00_u03b2_3347_, v_inst_3348_, v_x_3349_);
lean_dec(v_x_3349_);
lean_dec_ref(v_inst_3348_);
return v_res_3350_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object* v_x_3351_, lean_object* v_x_3352_){
_start:
{
if (lean_obj_tag(v_x_3351_) == 0)
{
lean_object* v_l_3353_; 
v_l_3353_ = lean_ctor_get(v_x_3351_, 3);
if (lean_obj_tag(v_l_3353_) == 0)
{
v_x_3351_ = v_l_3353_;
goto _start;
}
else
{
lean_object* v_k_3355_; lean_object* v_v_3356_; lean_object* v___x_3357_; 
v_k_3355_ = lean_ctor_get(v_x_3351_, 1);
v_v_3356_ = lean_ctor_get(v_x_3351_, 2);
lean_inc(v_v_3356_);
lean_inc(v_k_3355_);
v___x_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3357_, 0, v_k_3355_);
lean_ctor_set(v___x_3357_, 1, v_v_3356_);
return v___x_3357_;
}
}
else
{
lean_inc_ref(v_x_3352_);
return v_x_3352_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg___boxed(lean_object* v_x_3358_, lean_object* v_x_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3358_, v_x_3359_);
lean_dec_ref(v_x_3359_);
lean_dec(v_x_3358_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD(lean_object* v_00_u03b1_3361_, lean_object* v_00_u03b2_3362_, lean_object* v_x_3363_, lean_object* v_x_3364_){
_start:
{
lean_object* v___x_3365_; 
v___x_3365_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3363_, v_x_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___boxed(lean_object* v_00_u03b1_3366_, lean_object* v_00_u03b2_3367_, lean_object* v_x_3368_, lean_object* v_x_3369_){
_start:
{
lean_object* v_res_3370_; 
v_res_3370_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD(v_00_u03b1_3366_, v_00_u03b2_3367_, v_x_3368_, v_x_3369_);
lean_dec_ref(v_x_3369_);
lean_dec(v_x_3368_);
return v_res_3370_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_3371_, lean_object* v_x_3372_, lean_object* v_h__1_3373_, lean_object* v_h__2_3374_, lean_object* v_h__3_3375_){
_start:
{
if (lean_obj_tag(v_x_3371_) == 0)
{
lean_object* v_l_3376_; 
lean_dec(v_h__1_3373_);
v_l_3376_ = lean_ctor_get(v_x_3371_, 3);
if (lean_obj_tag(v_l_3376_) == 0)
{
lean_object* v_size_3377_; lean_object* v_k_3378_; lean_object* v_v_3379_; lean_object* v_r_3380_; lean_object* v_size_3381_; lean_object* v_k_3382_; lean_object* v_v_3383_; lean_object* v_l_3384_; lean_object* v_r_3385_; lean_object* v___x_3386_; 
lean_inc_ref(v_l_3376_);
lean_dec(v_h__2_3374_);
v_size_3377_ = lean_ctor_get(v_x_3371_, 0);
lean_inc(v_size_3377_);
v_k_3378_ = lean_ctor_get(v_x_3371_, 1);
lean_inc(v_k_3378_);
v_v_3379_ = lean_ctor_get(v_x_3371_, 2);
lean_inc(v_v_3379_);
v_r_3380_ = lean_ctor_get(v_x_3371_, 4);
lean_inc(v_r_3380_);
lean_dec_ref_known(v_x_3371_, 5);
v_size_3381_ = lean_ctor_get(v_l_3376_, 0);
lean_inc(v_size_3381_);
v_k_3382_ = lean_ctor_get(v_l_3376_, 1);
lean_inc(v_k_3382_);
v_v_3383_ = lean_ctor_get(v_l_3376_, 2);
lean_inc(v_v_3383_);
v_l_3384_ = lean_ctor_get(v_l_3376_, 3);
lean_inc(v_l_3384_);
v_r_3385_ = lean_ctor_get(v_l_3376_, 4);
lean_inc(v_r_3385_);
lean_dec_ref_known(v_l_3376_, 5);
v___x_3386_ = lean_apply_10(v_h__3_3375_, v_size_3377_, v_k_3378_, v_v_3379_, v_size_3381_, v_k_3382_, v_v_3383_, v_l_3384_, v_r_3385_, v_r_3380_, v_x_3372_);
return v___x_3386_;
}
else
{
lean_object* v_size_3387_; lean_object* v_k_3388_; lean_object* v_v_3389_; lean_object* v_r_3390_; lean_object* v___x_3391_; 
lean_dec(v_h__3_3375_);
v_size_3387_ = lean_ctor_get(v_x_3371_, 0);
lean_inc(v_size_3387_);
v_k_3388_ = lean_ctor_get(v_x_3371_, 1);
lean_inc(v_k_3388_);
v_v_3389_ = lean_ctor_get(v_x_3371_, 2);
lean_inc(v_v_3389_);
v_r_3390_ = lean_ctor_get(v_x_3371_, 4);
lean_inc(v_r_3390_);
lean_dec_ref_known(v_x_3371_, 5);
v___x_3391_ = lean_apply_5(v_h__2_3374_, v_size_3387_, v_k_3388_, v_v_3389_, v_r_3390_, v_x_3372_);
return v___x_3391_;
}
}
else
{
lean_object* v___x_3392_; 
lean_dec(v_h__3_3375_);
lean_dec(v_h__2_3374_);
v___x_3392_ = lean_apply_1(v_h__1_3373_, v_x_3372_);
return v___x_3392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_3393_, lean_object* v_00_u03b2_3394_, lean_object* v_motive_3395_, lean_object* v_x_3396_, lean_object* v_x_3397_, lean_object* v_h__1_3398_, lean_object* v_h__2_3399_, lean_object* v_h__3_3400_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object* v_x_3418_){
_start:
{
if (lean_obj_tag(v_x_3418_) == 0)
{
lean_object* v_r_3419_; 
v_r_3419_ = lean_ctor_get(v_x_3418_, 4);
if (lean_obj_tag(v_r_3419_) == 0)
{
v_x_3418_ = v_r_3419_;
goto _start;
}
else
{
lean_object* v_k_3421_; lean_object* v_v_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v_k_3421_ = lean_ctor_get(v_x_3418_, 1);
v_v_3422_ = lean_ctor_get(v_x_3418_, 2);
lean_inc(v_v_3422_);
lean_inc(v_k_3421_);
v___x_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3423_, 0, v_k_3421_);
lean_ctor_set(v___x_3423_, 1, v_v_3422_);
v___x_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3424_, 0, v___x_3423_);
return v___x_3424_;
}
}
else
{
lean_object* v___x_3425_; 
v___x_3425_ = lean_box(0);
return v___x_3425_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg___boxed(lean_object* v_x_3426_){
_start:
{
lean_object* v_res_3427_; 
v_res_3427_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3426_);
lean_dec(v_x_3426_);
return v_res_3427_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(lean_object* v_00_u03b1_3428_, lean_object* v_00_u03b2_3429_, lean_object* v_x_3430_){
_start:
{
lean_object* v___x_3431_; 
v___x_3431_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3430_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_3432_, lean_object* v_00_u03b2_3433_, lean_object* v_x_3434_){
_start:
{
lean_object* v_res_3435_; 
v_res_3435_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(v_00_u03b1_3432_, v_00_u03b2_3433_, v_x_3434_);
lean_dec(v_x_3434_);
return v_res_3435_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3436_, lean_object* v_h__1_3437_, lean_object* v_h__2_3438_, lean_object* v_h__3_3439_){
_start:
{
if (lean_obj_tag(v_x_3436_) == 0)
{
lean_object* v_r_3440_; 
lean_dec(v_h__1_3437_);
v_r_3440_ = lean_ctor_get(v_x_3436_, 4);
if (lean_obj_tag(v_r_3440_) == 0)
{
lean_object* v_size_3441_; lean_object* v_k_3442_; lean_object* v_v_3443_; lean_object* v_l_3444_; lean_object* v_size_3445_; lean_object* v_k_3446_; lean_object* v_v_3447_; lean_object* v_l_3448_; lean_object* v_r_3449_; lean_object* v___x_3450_; 
lean_inc_ref(v_r_3440_);
lean_dec(v_h__2_3438_);
v_size_3441_ = lean_ctor_get(v_x_3436_, 0);
lean_inc(v_size_3441_);
v_k_3442_ = lean_ctor_get(v_x_3436_, 1);
lean_inc(v_k_3442_);
v_v_3443_ = lean_ctor_get(v_x_3436_, 2);
lean_inc(v_v_3443_);
v_l_3444_ = lean_ctor_get(v_x_3436_, 3);
lean_inc(v_l_3444_);
lean_dec_ref_known(v_x_3436_, 5);
v_size_3445_ = lean_ctor_get(v_r_3440_, 0);
lean_inc(v_size_3445_);
v_k_3446_ = lean_ctor_get(v_r_3440_, 1);
lean_inc(v_k_3446_);
v_v_3447_ = lean_ctor_get(v_r_3440_, 2);
lean_inc(v_v_3447_);
v_l_3448_ = lean_ctor_get(v_r_3440_, 3);
lean_inc(v_l_3448_);
v_r_3449_ = lean_ctor_get(v_r_3440_, 4);
lean_inc(v_r_3449_);
lean_dec_ref_known(v_r_3440_, 5);
v___x_3450_ = lean_apply_9(v_h__3_3439_, v_size_3441_, v_k_3442_, v_v_3443_, v_l_3444_, v_size_3445_, v_k_3446_, v_v_3447_, v_l_3448_, v_r_3449_);
return v___x_3450_;
}
else
{
lean_object* v_size_3451_; lean_object* v_k_3452_; lean_object* v_v_3453_; lean_object* v_l_3454_; lean_object* v___x_3455_; 
lean_dec(v_h__3_3439_);
v_size_3451_ = lean_ctor_get(v_x_3436_, 0);
lean_inc(v_size_3451_);
v_k_3452_ = lean_ctor_get(v_x_3436_, 1);
lean_inc(v_k_3452_);
v_v_3453_ = lean_ctor_get(v_x_3436_, 2);
lean_inc(v_v_3453_);
v_l_3454_ = lean_ctor_get(v_x_3436_, 3);
lean_inc(v_l_3454_);
lean_dec_ref_known(v_x_3436_, 5);
v___x_3455_ = lean_apply_4(v_h__2_3438_, v_size_3451_, v_k_3452_, v_v_3453_, v_l_3454_);
return v___x_3455_;
}
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_dec(v_h__3_3439_);
lean_dec(v_h__2_3438_);
v___x_3456_ = lean_box(0);
v___x_3457_ = lean_apply_1(v_h__1_3437_, v___x_3456_);
return v___x_3457_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3458_, lean_object* v_00_u03b2_3459_, lean_object* v_motive_3460_, lean_object* v_x_3461_, lean_object* v_h__1_3462_, lean_object* v_h__2_3463_, lean_object* v_h__3_3464_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object* v_x_3483_){
_start:
{
lean_object* v_r_3484_; 
v_r_3484_ = lean_ctor_get(v_x_3483_, 4);
if (lean_obj_tag(v_r_3484_) == 0)
{
v_x_3483_ = v_r_3484_;
goto _start;
}
else
{
lean_object* v_k_3486_; lean_object* v_v_3487_; lean_object* v___x_3488_; 
v_k_3486_ = lean_ctor_get(v_x_3483_, 1);
v_v_3487_ = lean_ctor_get(v_x_3483_, 2);
lean_inc(v_v_3487_);
lean_inc(v_k_3486_);
v___x_3488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3488_, 0, v_k_3486_);
lean_ctor_set(v___x_3488_, 1, v_v_3487_);
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg___boxed(lean_object* v_x_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3489_);
lean_dec(v_x_3489_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry(lean_object* v_00_u03b1_3491_, lean_object* v_00_u03b2_3492_, lean_object* v_x_3493_, lean_object* v_x_3494_){
_start:
{
lean_object* v___x_3495_; 
v___x_3495_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3493_);
return v___x_3495_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___boxed(lean_object* v_00_u03b1_3496_, lean_object* v_00_u03b2_3497_, lean_object* v_x_3498_, lean_object* v_x_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry(v_00_u03b1_3496_, v_00_u03b2_3497_, v_x_3498_, v_x_3499_);
lean_dec(v_x_3498_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_3501_, lean_object* v_h__1_3502_, lean_object* v_h__2_3503_){
_start:
{
lean_object* v_r_3504_; 
v_r_3504_ = lean_ctor_get(v_x_3501_, 4);
if (lean_obj_tag(v_r_3504_) == 0)
{
lean_object* v_size_3505_; lean_object* v_k_3506_; lean_object* v_v_3507_; lean_object* v_l_3508_; lean_object* v_size_3509_; lean_object* v_k_3510_; lean_object* v_v_3511_; lean_object* v_l_3512_; lean_object* v_r_3513_; lean_object* v___x_3514_; 
lean_inc_ref(v_r_3504_);
lean_dec(v_h__1_3502_);
v_size_3505_ = lean_ctor_get(v_x_3501_, 0);
lean_inc(v_size_3505_);
v_k_3506_ = lean_ctor_get(v_x_3501_, 1);
lean_inc(v_k_3506_);
v_v_3507_ = lean_ctor_get(v_x_3501_, 2);
lean_inc(v_v_3507_);
v_l_3508_ = lean_ctor_get(v_x_3501_, 3);
lean_inc(v_l_3508_);
lean_dec(v_x_3501_);
v_size_3509_ = lean_ctor_get(v_r_3504_, 0);
lean_inc(v_size_3509_);
v_k_3510_ = lean_ctor_get(v_r_3504_, 1);
lean_inc(v_k_3510_);
v_v_3511_ = lean_ctor_get(v_r_3504_, 2);
lean_inc(v_v_3511_);
v_l_3512_ = lean_ctor_get(v_r_3504_, 3);
lean_inc(v_l_3512_);
v_r_3513_ = lean_ctor_get(v_r_3504_, 4);
lean_inc(v_r_3513_);
lean_dec_ref_known(v_r_3504_, 5);
v___x_3514_ = lean_apply_10(v_h__2_3503_, v_size_3505_, v_k_3506_, v_v_3507_, v_l_3508_, v_size_3509_, v_k_3510_, v_v_3511_, v_l_3512_, v_r_3513_, lean_box(0));
return v___x_3514_;
}
else
{
lean_object* v_size_3515_; lean_object* v_k_3516_; lean_object* v_v_3517_; lean_object* v_l_3518_; lean_object* v___x_3519_; 
lean_dec(v_h__2_3503_);
v_size_3515_ = lean_ctor_get(v_x_3501_, 0);
lean_inc(v_size_3515_);
v_k_3516_ = lean_ctor_get(v_x_3501_, 1);
lean_inc(v_k_3516_);
v_v_3517_ = lean_ctor_get(v_x_3501_, 2);
lean_inc(v_v_3517_);
v_l_3518_ = lean_ctor_get(v_x_3501_, 3);
lean_inc(v_l_3518_);
lean_dec(v_x_3501_);
v___x_3519_ = lean_apply_5(v_h__1_3502_, v_size_3515_, v_k_3516_, v_v_3517_, v_l_3518_, lean_box(0));
return v___x_3519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_3520_, lean_object* v_00_u03b2_3521_, lean_object* v_motive_3522_, lean_object* v_x_3523_, lean_object* v_x_3524_, lean_object* v_h__1_3525_, lean_object* v_h__2_3526_){
_start:
{
lean_object* v_r_3527_; 
v_r_3527_ = lean_ctor_get(v_x_3523_, 4);
if (lean_obj_tag(v_r_3527_) == 0)
{
lean_object* v_size_3528_; lean_object* v_k_3529_; lean_object* v_v_3530_; lean_object* v_l_3531_; lean_object* v_size_3532_; lean_object* v_k_3533_; lean_object* v_v_3534_; lean_object* v_l_3535_; lean_object* v_r_3536_; lean_object* v___x_3537_; 
lean_inc_ref(v_r_3527_);
lean_dec(v_h__1_3525_);
v_size_3528_ = lean_ctor_get(v_x_3523_, 0);
lean_inc(v_size_3528_);
v_k_3529_ = lean_ctor_get(v_x_3523_, 1);
lean_inc(v_k_3529_);
v_v_3530_ = lean_ctor_get(v_x_3523_, 2);
lean_inc(v_v_3530_);
v_l_3531_ = lean_ctor_get(v_x_3523_, 3);
lean_inc(v_l_3531_);
lean_dec(v_x_3523_);
v_size_3532_ = lean_ctor_get(v_r_3527_, 0);
lean_inc(v_size_3532_);
v_k_3533_ = lean_ctor_get(v_r_3527_, 1);
lean_inc(v_k_3533_);
v_v_3534_ = lean_ctor_get(v_r_3527_, 2);
lean_inc(v_v_3534_);
v_l_3535_ = lean_ctor_get(v_r_3527_, 3);
lean_inc(v_l_3535_);
v_r_3536_ = lean_ctor_get(v_r_3527_, 4);
lean_inc(v_r_3536_);
lean_dec_ref_known(v_r_3527_, 5);
v___x_3537_ = lean_apply_10(v_h__2_3526_, v_size_3528_, v_k_3529_, v_v_3530_, v_l_3531_, v_size_3532_, v_k_3533_, v_v_3534_, v_l_3535_, v_r_3536_, lean_box(0));
return v___x_3537_;
}
else
{
lean_object* v_size_3538_; lean_object* v_k_3539_; lean_object* v_v_3540_; lean_object* v_l_3541_; lean_object* v___x_3542_; 
lean_dec(v_h__2_3526_);
v_size_3538_ = lean_ctor_get(v_x_3523_, 0);
lean_inc(v_size_3538_);
v_k_3539_ = lean_ctor_get(v_x_3523_, 1);
lean_inc(v_k_3539_);
v_v_3540_ = lean_ctor_get(v_x_3523_, 2);
lean_inc(v_v_3540_);
v_l_3541_ = lean_ctor_get(v_x_3523_, 3);
lean_inc(v_l_3541_);
lean_dec(v_x_3523_);
v___x_3542_ = lean_apply_5(v_h__1_3525_, v_size_3538_, v_k_3539_, v_v_3540_, v_l_3541_, lean_box(0));
return v___x_3542_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3544_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3545_ = lean_unsigned_to_nat(13u);
v___x_3546_ = lean_unsigned_to_nat(839u);
v___x_3547_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0));
v___x_3548_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3549_ = l_mkPanicMessageWithDecl(v___x_3548_, v___x_3547_, v___x_3546_, v___x_3545_, v___x_3544_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object* v_inst_3550_, lean_object* v_x_3551_){
_start:
{
if (lean_obj_tag(v_x_3551_) == 0)
{
lean_object* v_r_3552_; 
v_r_3552_ = lean_ctor_get(v_x_3551_, 4);
if (lean_obj_tag(v_r_3552_) == 0)
{
v_x_3551_ = v_r_3552_;
goto _start;
}
else
{
lean_object* v_k_3554_; lean_object* v_v_3555_; lean_object* v___x_3556_; 
v_k_3554_ = lean_ctor_get(v_x_3551_, 1);
v_v_3555_ = lean_ctor_get(v_x_3551_, 2);
lean_inc(v_v_3555_);
lean_inc(v_k_3554_);
v___x_3556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3556_, 0, v_k_3554_);
lean_ctor_set(v___x_3556_, 1, v_v_3555_);
return v___x_3556_;
}
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1);
v___x_3558_ = l_panic___redArg(v_inst_3550_, v___x_3557_);
return v___x_3558_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_3559_, lean_object* v_x_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3559_, v_x_3560_);
lean_dec(v_x_3560_);
lean_dec_ref(v_inst_3559_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(lean_object* v_00_u03b1_3562_, lean_object* v_00_u03b2_3563_, lean_object* v_inst_3564_, lean_object* v_x_3565_){
_start:
{
lean_object* v___x_3566_; 
v___x_3566_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3564_, v_x_3565_);
return v___x_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_3567_, lean_object* v_00_u03b2_3568_, lean_object* v_inst_3569_, lean_object* v_x_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(v_00_u03b1_3567_, v_00_u03b2_3568_, v_inst_3569_, v_x_3570_);
lean_dec(v_x_3570_);
lean_dec_ref(v_inst_3569_);
return v_res_3571_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object* v_x_3572_, lean_object* v_x_3573_){
_start:
{
if (lean_obj_tag(v_x_3572_) == 0)
{
lean_object* v_r_3574_; 
v_r_3574_ = lean_ctor_get(v_x_3572_, 4);
if (lean_obj_tag(v_r_3574_) == 0)
{
v_x_3572_ = v_r_3574_;
goto _start;
}
else
{
lean_object* v_k_3576_; lean_object* v_v_3577_; lean_object* v___x_3578_; 
v_k_3576_ = lean_ctor_get(v_x_3572_, 1);
v_v_3577_ = lean_ctor_get(v_x_3572_, 2);
lean_inc(v_v_3577_);
lean_inc(v_k_3576_);
v___x_3578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3578_, 0, v_k_3576_);
lean_ctor_set(v___x_3578_, 1, v_v_3577_);
return v___x_3578_;
}
}
else
{
lean_inc_ref(v_x_3573_);
return v_x_3573_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg___boxed(lean_object* v_x_3579_, lean_object* v_x_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3579_, v_x_3580_);
lean_dec_ref(v_x_3580_);
lean_dec(v_x_3579_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(lean_object* v_00_u03b1_3582_, lean_object* v_00_u03b2_3583_, lean_object* v_x_3584_, lean_object* v_x_3585_){
_start:
{
lean_object* v___x_3586_; 
v___x_3586_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3584_, v_x_3585_);
return v___x_3586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___boxed(lean_object* v_00_u03b1_3587_, lean_object* v_00_u03b2_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_){
_start:
{
lean_object* v_res_3591_; 
v_res_3591_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(v_00_u03b1_3587_, v_00_u03b2_3588_, v_x_3589_, v_x_3590_);
lean_dec_ref(v_x_3590_);
lean_dec(v_x_3589_);
return v_res_3591_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_3592_, lean_object* v_x_3593_, lean_object* v_h__1_3594_, lean_object* v_h__2_3595_, lean_object* v_h__3_3596_){
_start:
{
if (lean_obj_tag(v_x_3592_) == 0)
{
lean_object* v_r_3597_; 
lean_dec(v_h__1_3594_);
v_r_3597_ = lean_ctor_get(v_x_3592_, 4);
if (lean_obj_tag(v_r_3597_) == 0)
{
lean_object* v_size_3598_; lean_object* v_k_3599_; lean_object* v_v_3600_; lean_object* v_l_3601_; lean_object* v_size_3602_; lean_object* v_k_3603_; lean_object* v_v_3604_; lean_object* v_l_3605_; lean_object* v_r_3606_; lean_object* v___x_3607_; 
lean_inc_ref(v_r_3597_);
lean_dec(v_h__2_3595_);
v_size_3598_ = lean_ctor_get(v_x_3592_, 0);
lean_inc(v_size_3598_);
v_k_3599_ = lean_ctor_get(v_x_3592_, 1);
lean_inc(v_k_3599_);
v_v_3600_ = lean_ctor_get(v_x_3592_, 2);
lean_inc(v_v_3600_);
v_l_3601_ = lean_ctor_get(v_x_3592_, 3);
lean_inc(v_l_3601_);
lean_dec_ref_known(v_x_3592_, 5);
v_size_3602_ = lean_ctor_get(v_r_3597_, 0);
lean_inc(v_size_3602_);
v_k_3603_ = lean_ctor_get(v_r_3597_, 1);
lean_inc(v_k_3603_);
v_v_3604_ = lean_ctor_get(v_r_3597_, 2);
lean_inc(v_v_3604_);
v_l_3605_ = lean_ctor_get(v_r_3597_, 3);
lean_inc(v_l_3605_);
v_r_3606_ = lean_ctor_get(v_r_3597_, 4);
lean_inc(v_r_3606_);
lean_dec_ref_known(v_r_3597_, 5);
v___x_3607_ = lean_apply_10(v_h__3_3596_, v_size_3598_, v_k_3599_, v_v_3600_, v_l_3601_, v_size_3602_, v_k_3603_, v_v_3604_, v_l_3605_, v_r_3606_, v_x_3593_);
return v___x_3607_;
}
else
{
lean_object* v_size_3608_; lean_object* v_k_3609_; lean_object* v_v_3610_; lean_object* v_l_3611_; lean_object* v___x_3612_; 
lean_dec(v_h__3_3596_);
v_size_3608_ = lean_ctor_get(v_x_3592_, 0);
lean_inc(v_size_3608_);
v_k_3609_ = lean_ctor_get(v_x_3592_, 1);
lean_inc(v_k_3609_);
v_v_3610_ = lean_ctor_get(v_x_3592_, 2);
lean_inc(v_v_3610_);
v_l_3611_ = lean_ctor_get(v_x_3592_, 3);
lean_inc(v_l_3611_);
lean_dec_ref_known(v_x_3592_, 5);
v___x_3612_ = lean_apply_5(v_h__2_3595_, v_size_3608_, v_k_3609_, v_v_3610_, v_l_3611_, v_x_3593_);
return v___x_3612_;
}
}
else
{
lean_object* v___x_3613_; 
lean_dec(v_h__3_3596_);
lean_dec(v_h__2_3595_);
v___x_3613_ = lean_apply_1(v_h__1_3594_, v_x_3593_);
return v___x_3613_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_3614_, lean_object* v_00_u03b2_3615_, lean_object* v_motive_3616_, lean_object* v_x_3617_, lean_object* v_x_3618_, lean_object* v_h__1_3619_, lean_object* v_h__2_3620_, lean_object* v_h__3_3621_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object* v_x_3639_, lean_object* v_x_3640_){
_start:
{
lean_object* v_k_3641_; lean_object* v_v_3642_; lean_object* v_l_3643_; lean_object* v_r_3644_; lean_object* v___y_3646_; lean_object* v___y_3652_; 
v_k_3641_ = lean_ctor_get(v_x_3639_, 1);
v_v_3642_ = lean_ctor_get(v_x_3639_, 2);
v_l_3643_ = lean_ctor_get(v_x_3639_, 3);
v_r_3644_ = lean_ctor_get(v_x_3639_, 4);
if (lean_obj_tag(v_l_3643_) == 0)
{
lean_object* v_size_3659_; 
v_size_3659_ = lean_ctor_get(v_l_3643_, 0);
v___y_3652_ = v_size_3659_;
goto v___jp_3651_;
}
else
{
lean_object* v___x_3660_; 
v___x_3660_ = lean_unsigned_to_nat(0u);
v___y_3652_ = v___x_3660_;
goto v___jp_3651_;
}
v___jp_3645_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = lean_nat_sub(v_x_3640_, v___y_3646_);
lean_dec(v_x_3640_);
v___x_3648_ = lean_unsigned_to_nat(1u);
v___x_3649_ = lean_nat_sub(v___x_3647_, v___x_3648_);
lean_dec(v___x_3647_);
v_x_3639_ = v_r_3644_;
v_x_3640_ = v___x_3649_;
goto _start;
}
v___jp_3651_:
{
uint8_t v___x_3653_; 
v___x_3653_ = lean_nat_dec_lt(v_x_3640_, v___y_3652_);
if (v___x_3653_ == 0)
{
uint8_t v___x_3654_; 
v___x_3654_ = lean_nat_dec_eq(v_x_3640_, v___y_3652_);
if (v___x_3654_ == 0)
{
if (lean_obj_tag(v_l_3643_) == 0)
{
lean_object* v_size_3655_; 
v_size_3655_ = lean_ctor_get(v_l_3643_, 0);
v___y_3646_ = v_size_3655_;
goto v___jp_3645_;
}
else
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_unsigned_to_nat(0u);
v___y_3646_ = v___x_3656_;
goto v___jp_3645_;
}
}
else
{
lean_object* v___x_3657_; 
lean_dec(v_x_3640_);
lean_inc(v_v_3642_);
lean_inc(v_k_3641_);
v___x_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3657_, 0, v_k_3641_);
lean_ctor_set(v___x_3657_, 1, v_v_3642_);
return v___x_3657_;
}
}
else
{
v_x_3639_ = v_l_3643_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg___boxed(lean_object* v_x_3661_, lean_object* v_x_3662_){
_start:
{
lean_object* v_res_3663_; 
v_res_3663_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3661_, v_x_3662_);
lean_dec(v_x_3661_);
return v_res_3663_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_object* v_00_u03b1_3664_, lean_object* v_00_u03b2_3665_, lean_object* v_x_3666_, lean_object* v_x_3667_, lean_object* v_x_3668_, lean_object* v_x_3669_){
_start:
{
lean_object* v___x_3670_; 
v___x_3670_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3666_, v_x_3668_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_3671_, lean_object* v_00_u03b2_3672_, lean_object* v_x_3673_, lean_object* v_x_3674_, lean_object* v_x_3675_, lean_object* v_x_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(v_00_u03b1_3671_, v_00_u03b2_3672_, v_x_3673_, v_x_3674_, v_x_3675_, v_x_3676_);
lean_dec(v_x_3673_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object* v_x_3678_, lean_object* v_x_3679_){
_start:
{
if (lean_obj_tag(v_x_3678_) == 0)
{
lean_object* v_k_3680_; lean_object* v_v_3681_; lean_object* v_l_3682_; lean_object* v_r_3683_; lean_object* v___y_3685_; lean_object* v___y_3691_; 
v_k_3680_ = lean_ctor_get(v_x_3678_, 1);
v_v_3681_ = lean_ctor_get(v_x_3678_, 2);
v_l_3682_ = lean_ctor_get(v_x_3678_, 3);
v_r_3683_ = lean_ctor_get(v_x_3678_, 4);
if (lean_obj_tag(v_l_3682_) == 0)
{
lean_object* v_size_3699_; 
v_size_3699_ = lean_ctor_get(v_l_3682_, 0);
v___y_3691_ = v_size_3699_;
goto v___jp_3690_;
}
else
{
lean_object* v___x_3700_; 
v___x_3700_ = lean_unsigned_to_nat(0u);
v___y_3691_ = v___x_3700_;
goto v___jp_3690_;
}
v___jp_3684_:
{
lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v___x_3686_ = lean_nat_sub(v_x_3679_, v___y_3685_);
lean_dec(v_x_3679_);
v___x_3687_ = lean_unsigned_to_nat(1u);
v___x_3688_ = lean_nat_sub(v___x_3686_, v___x_3687_);
lean_dec(v___x_3686_);
v_x_3678_ = v_r_3683_;
v_x_3679_ = v___x_3688_;
goto _start;
}
v___jp_3690_:
{
uint8_t v___x_3692_; 
v___x_3692_ = lean_nat_dec_lt(v_x_3679_, v___y_3691_);
if (v___x_3692_ == 0)
{
uint8_t v___x_3693_; 
v___x_3693_ = lean_nat_dec_eq(v_x_3679_, v___y_3691_);
if (v___x_3693_ == 0)
{
if (lean_obj_tag(v_l_3682_) == 0)
{
lean_object* v_size_3694_; 
v_size_3694_ = lean_ctor_get(v_l_3682_, 0);
v___y_3685_ = v_size_3694_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3695_; 
v___x_3695_ = lean_unsigned_to_nat(0u);
v___y_3685_ = v___x_3695_;
goto v___jp_3684_;
}
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; 
lean_dec(v_x_3679_);
lean_inc(v_v_3681_);
lean_inc(v_k_3680_);
v___x_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3696_, 0, v_k_3680_);
lean_ctor_set(v___x_3696_, 1, v_v_3681_);
v___x_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3696_);
return v___x_3697_;
}
}
else
{
v_x_3678_ = v_l_3682_;
goto _start;
}
}
}
else
{
lean_object* v___x_3701_; 
lean_dec(v_x_3679_);
v___x_3701_ = lean_box(0);
return v___x_3701_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_3702_, lean_object* v_x_3703_){
_start:
{
lean_object* v_res_3704_; 
v_res_3704_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3702_, v_x_3703_);
lean_dec(v_x_3702_);
return v_res_3704_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_3705_, lean_object* v_00_u03b2_3706_, lean_object* v_x_3707_, lean_object* v_x_3708_){
_start:
{
lean_object* v___x_3709_; 
v___x_3709_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3707_, v_x_3708_);
return v___x_3709_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_3710_, lean_object* v_00_u03b2_3711_, lean_object* v_x_3712_, lean_object* v_x_3713_){
_start:
{
lean_object* v_res_3714_; 
v_res_3714_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(v_00_u03b1_3710_, v_00_u03b2_3711_, v_x_3712_, v_x_3713_);
lean_dec(v_x_3712_);
return v_res_3714_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; 
v___x_3716_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_3717_ = lean_unsigned_to_nat(16u);
v___x_3718_ = lean_unsigned_to_nat(870u);
v___x_3719_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0));
v___x_3720_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3721_ = l_mkPanicMessageWithDecl(v___x_3720_, v___x_3719_, v___x_3718_, v___x_3717_, v___x_3716_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object* v_inst_3722_, lean_object* v_x_3723_, lean_object* v_x_3724_){
_start:
{
if (lean_obj_tag(v_x_3723_) == 0)
{
lean_object* v_k_3725_; lean_object* v_v_3726_; lean_object* v_l_3727_; lean_object* v_r_3728_; lean_object* v___y_3730_; lean_object* v___y_3736_; 
v_k_3725_ = lean_ctor_get(v_x_3723_, 1);
v_v_3726_ = lean_ctor_get(v_x_3723_, 2);
v_l_3727_ = lean_ctor_get(v_x_3723_, 3);
v_r_3728_ = lean_ctor_get(v_x_3723_, 4);
if (lean_obj_tag(v_l_3727_) == 0)
{
lean_object* v_size_3743_; 
v_size_3743_ = lean_ctor_get(v_l_3727_, 0);
v___y_3736_ = v_size_3743_;
goto v___jp_3735_;
}
else
{
lean_object* v___x_3744_; 
v___x_3744_ = lean_unsigned_to_nat(0u);
v___y_3736_ = v___x_3744_;
goto v___jp_3735_;
}
v___jp_3729_:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3731_ = lean_nat_sub(v_x_3724_, v___y_3730_);
lean_dec(v_x_3724_);
v___x_3732_ = lean_unsigned_to_nat(1u);
v___x_3733_ = lean_nat_sub(v___x_3731_, v___x_3732_);
lean_dec(v___x_3731_);
v_x_3723_ = v_r_3728_;
v_x_3724_ = v___x_3733_;
goto _start;
}
v___jp_3735_:
{
uint8_t v___x_3737_; 
v___x_3737_ = lean_nat_dec_lt(v_x_3724_, v___y_3736_);
if (v___x_3737_ == 0)
{
uint8_t v___x_3738_; 
v___x_3738_ = lean_nat_dec_eq(v_x_3724_, v___y_3736_);
if (v___x_3738_ == 0)
{
if (lean_obj_tag(v_l_3727_) == 0)
{
lean_object* v_size_3739_; 
v_size_3739_ = lean_ctor_get(v_l_3727_, 0);
v___y_3730_ = v_size_3739_;
goto v___jp_3729_;
}
else
{
lean_object* v___x_3740_; 
v___x_3740_ = lean_unsigned_to_nat(0u);
v___y_3730_ = v___x_3740_;
goto v___jp_3729_;
}
}
else
{
lean_object* v___x_3741_; 
lean_dec(v_x_3724_);
lean_inc(v_v_3726_);
lean_inc(v_k_3725_);
v___x_3741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3741_, 0, v_k_3725_);
lean_ctor_set(v___x_3741_, 1, v_v_3726_);
return v___x_3741_;
}
}
else
{
v_x_3723_ = v_l_3727_;
goto _start;
}
}
}
else
{
lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec(v_x_3724_);
v___x_3745_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1);
v___x_3746_ = l_panic___redArg(v_inst_3722_, v___x_3745_);
return v___x_3746_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_3747_, lean_object* v_x_3748_, lean_object* v_x_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3747_, v_x_3748_, v_x_3749_);
lean_dec(v_x_3748_);
lean_dec_ref(v_inst_3747_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(lean_object* v_00_u03b1_3751_, lean_object* v_00_u03b2_3752_, lean_object* v_inst_3753_, lean_object* v_x_3754_, lean_object* v_x_3755_){
_start:
{
lean_object* v___x_3756_; 
v___x_3756_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3753_, v_x_3754_, v_x_3755_);
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_3757_, lean_object* v_00_u03b2_3758_, lean_object* v_inst_3759_, lean_object* v_x_3760_, lean_object* v_x_3761_){
_start:
{
lean_object* v_res_3762_; 
v_res_3762_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(v_00_u03b1_3757_, v_00_u03b2_3758_, v_inst_3759_, v_x_3760_, v_x_3761_);
lean_dec(v_x_3760_);
lean_dec_ref(v_inst_3759_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object* v_x_3763_, lean_object* v_x_3764_, lean_object* v_x_3765_){
_start:
{
if (lean_obj_tag(v_x_3763_) == 0)
{
lean_object* v_k_3766_; lean_object* v_v_3767_; lean_object* v_l_3768_; lean_object* v_r_3769_; lean_object* v___y_3771_; lean_object* v___y_3777_; 
v_k_3766_ = lean_ctor_get(v_x_3763_, 1);
v_v_3767_ = lean_ctor_get(v_x_3763_, 2);
v_l_3768_ = lean_ctor_get(v_x_3763_, 3);
v_r_3769_ = lean_ctor_get(v_x_3763_, 4);
if (lean_obj_tag(v_l_3768_) == 0)
{
lean_object* v_size_3784_; 
v_size_3784_ = lean_ctor_get(v_l_3768_, 0);
v___y_3777_ = v_size_3784_;
goto v___jp_3776_;
}
else
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_unsigned_to_nat(0u);
v___y_3777_ = v___x_3785_;
goto v___jp_3776_;
}
v___jp_3770_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; 
v___x_3772_ = lean_nat_sub(v_x_3764_, v___y_3771_);
lean_dec(v_x_3764_);
v___x_3773_ = lean_unsigned_to_nat(1u);
v___x_3774_ = lean_nat_sub(v___x_3772_, v___x_3773_);
lean_dec(v___x_3772_);
v_x_3763_ = v_r_3769_;
v_x_3764_ = v___x_3774_;
goto _start;
}
v___jp_3776_:
{
uint8_t v___x_3778_; 
v___x_3778_ = lean_nat_dec_lt(v_x_3764_, v___y_3777_);
if (v___x_3778_ == 0)
{
uint8_t v___x_3779_; 
v___x_3779_ = lean_nat_dec_eq(v_x_3764_, v___y_3777_);
if (v___x_3779_ == 0)
{
if (lean_obj_tag(v_l_3768_) == 0)
{
lean_object* v_size_3780_; 
v_size_3780_ = lean_ctor_get(v_l_3768_, 0);
v___y_3771_ = v_size_3780_;
goto v___jp_3770_;
}
else
{
lean_object* v___x_3781_; 
v___x_3781_ = lean_unsigned_to_nat(0u);
v___y_3771_ = v___x_3781_;
goto v___jp_3770_;
}
}
else
{
lean_object* v___x_3782_; 
lean_dec(v_x_3764_);
lean_inc(v_v_3767_);
lean_inc(v_k_3766_);
v___x_3782_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3782_, 0, v_k_3766_);
lean_ctor_set(v___x_3782_, 1, v_v_3767_);
return v___x_3782_;
}
}
else
{
v_x_3763_ = v_l_3768_;
goto _start;
}
}
}
else
{
lean_dec(v_x_3764_);
lean_inc_ref(v_x_3765_);
return v_x_3765_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg___boxed(lean_object* v_x_3786_, lean_object* v_x_3787_, lean_object* v_x_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3786_, v_x_3787_, v_x_3788_);
lean_dec_ref(v_x_3788_);
lean_dec(v_x_3786_);
return v_res_3789_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(lean_object* v_00_u03b1_3790_, lean_object* v_00_u03b2_3791_, lean_object* v_x_3792_, lean_object* v_x_3793_, lean_object* v_x_3794_){
_start:
{
lean_object* v___x_3795_; 
v___x_3795_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3792_, v_x_3793_, v_x_3794_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_3796_, lean_object* v_00_u03b2_3797_, lean_object* v_x_3798_, lean_object* v_x_3799_, lean_object* v_x_3800_){
_start:
{
lean_object* v_res_3801_; 
v_res_3801_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(v_00_u03b1_3796_, v_00_u03b2_3797_, v_x_3798_, v_x_3799_, v_x_3800_);
lean_dec_ref(v_x_3800_);
lean_dec(v_x_3798_);
return v_res_3801_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object* v_inst_3802_, lean_object* v_k_3803_, lean_object* v_best_3804_, lean_object* v_a_3805_){
_start:
{
if (lean_obj_tag(v_a_3805_) == 0)
{
lean_object* v_k_3806_; lean_object* v_v_3807_; lean_object* v_l_3808_; lean_object* v_r_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v_k_3806_ = lean_ctor_get(v_a_3805_, 1);
lean_inc_n(v_k_3806_, 2);
v_v_3807_ = lean_ctor_get(v_a_3805_, 2);
lean_inc(v_v_3807_);
v_l_3808_ = lean_ctor_get(v_a_3805_, 3);
lean_inc(v_l_3808_);
v_r_3809_ = lean_ctor_get(v_a_3805_, 4);
lean_inc(v_r_3809_);
lean_dec_ref_known(v_a_3805_, 5);
lean_inc_ref(v_inst_3802_);
lean_inc(v_k_3803_);
v___x_3810_ = lean_apply_2(v_inst_3802_, v_k_3803_, v_k_3806_);
v___x_3811_ = lean_unbox(v___x_3810_);
switch(v___x_3811_)
{
case 0:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
lean_dec(v_r_3809_);
lean_dec(v_best_3804_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v_k_3806_);
lean_ctor_set(v___x_3812_, 1, v_v_3807_);
v___x_3813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3812_);
v_best_3804_ = v___x_3813_;
v_a_3805_ = v_l_3808_;
goto _start;
}
case 1:
{
lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_dec(v_r_3809_);
lean_dec(v_l_3808_);
lean_dec(v_best_3804_);
lean_dec(v_k_3803_);
lean_dec_ref(v_inst_3802_);
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v_k_3806_);
lean_ctor_set(v___x_3815_, 1, v_v_3807_);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3815_);
return v___x_3816_;
}
default: 
{
lean_dec(v_l_3808_);
lean_dec(v_v_3807_);
lean_dec(v_k_3806_);
v_a_3805_ = v_r_3809_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3803_);
lean_dec_ref(v_inst_3802_);
return v_best_3804_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(lean_object* v_00_u03b1_3818_, lean_object* v_00_u03b2_3819_, lean_object* v_inst_3820_, lean_object* v_k_3821_, lean_object* v_best_3822_, lean_object* v_a_3823_){
_start:
{
lean_object* v___x_3824_; 
v___x_3824_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3820_, v_k_3821_, v_best_3822_, v_a_3823_);
return v___x_3824_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___redArg(lean_object* v_inst_3825_, lean_object* v_k_3826_, lean_object* v_a_3827_){
_start:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3828_ = lean_box(0);
v___x_3829_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3825_, v_k_3826_, v___x_3828_, v_a_3827_);
return v___x_3829_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(lean_object* v_00_u03b1_3830_, lean_object* v_00_u03b2_3831_, lean_object* v_inst_3832_, lean_object* v_k_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3835_ = lean_box(0);
v___x_3836_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3832_, v_k_3833_, v___x_3835_, v_a_3834_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object* v_inst_3837_, lean_object* v_k_3838_, lean_object* v_best_3839_, lean_object* v_a_3840_){
_start:
{
if (lean_obj_tag(v_a_3840_) == 0)
{
lean_object* v_k_3841_; lean_object* v_v_3842_; lean_object* v_l_3843_; lean_object* v_r_3844_; lean_object* v___x_3845_; uint8_t v___x_3846_; 
v_k_3841_ = lean_ctor_get(v_a_3840_, 1);
lean_inc_n(v_k_3841_, 2);
v_v_3842_ = lean_ctor_get(v_a_3840_, 2);
lean_inc(v_v_3842_);
v_l_3843_ = lean_ctor_get(v_a_3840_, 3);
lean_inc(v_l_3843_);
v_r_3844_ = lean_ctor_get(v_a_3840_, 4);
lean_inc(v_r_3844_);
lean_dec_ref_known(v_a_3840_, 5);
lean_inc_ref(v_inst_3837_);
lean_inc(v_k_3838_);
v___x_3845_ = lean_apply_2(v_inst_3837_, v_k_3838_, v_k_3841_);
v___x_3846_ = lean_unbox(v___x_3845_);
if (v___x_3846_ == 0)
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
lean_dec(v_r_3844_);
lean_dec(v_best_3839_);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v_k_3841_);
lean_ctor_set(v___x_3847_, 1, v_v_3842_);
v___x_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
v_best_3839_ = v___x_3848_;
v_a_3840_ = v_l_3843_;
goto _start;
}
else
{
lean_dec(v_l_3843_);
lean_dec(v_v_3842_);
lean_dec(v_k_3841_);
v_a_3840_ = v_r_3844_;
goto _start;
}
}
else
{
lean_dec(v_k_3838_);
lean_dec_ref(v_inst_3837_);
return v_best_3839_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(lean_object* v_00_u03b1_3851_, lean_object* v_00_u03b2_3852_, lean_object* v_inst_3853_, lean_object* v_k_3854_, lean_object* v_best_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3853_, v_k_3854_, v_best_3855_, v_a_3856_);
return v___x_3857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___redArg(lean_object* v_inst_3858_, lean_object* v_k_3859_, lean_object* v_a_3860_){
_start:
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
v___x_3861_ = lean_box(0);
v___x_3862_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3858_, v_k_3859_, v___x_3861_, v_a_3860_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(lean_object* v_00_u03b1_3863_, lean_object* v_00_u03b2_3864_, lean_object* v_inst_3865_, lean_object* v_k_3866_, lean_object* v_a_3867_){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_box(0);
v___x_3869_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3865_, v_k_3866_, v___x_3868_, v_a_3867_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object* v_inst_3870_, lean_object* v_k_3871_, lean_object* v_best_3872_, lean_object* v_a_3873_){
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
switch(v___x_3879_)
{
case 0:
{
lean_dec(v_r_3877_);
lean_dec(v_v_3875_);
lean_dec(v_k_3874_);
v_a_3873_ = v_l_3876_;
goto _start;
}
case 1:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
lean_dec(v_r_3877_);
lean_dec(v_l_3876_);
lean_dec(v_best_3872_);
lean_dec(v_k_3871_);
lean_dec_ref(v_inst_3870_);
v___x_3881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3881_, 0, v_k_3874_);
lean_ctor_set(v___x_3881_, 1, v_v_3875_);
v___x_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
return v___x_3882_;
}
default: 
{
lean_object* v___x_3883_; lean_object* v___x_3884_; 
lean_dec(v_l_3876_);
lean_dec(v_best_3872_);
v___x_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3883_, 0, v_k_3874_);
lean_ctor_set(v___x_3883_, 1, v_v_3875_);
v___x_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___x_3883_);
v_best_3872_ = v___x_3884_;
v_a_3873_ = v_r_3877_;
goto _start;
}
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(lean_object* v_00_u03b1_3886_, lean_object* v_00_u03b2_3887_, lean_object* v_inst_3888_, lean_object* v_k_3889_, lean_object* v_best_3890_, lean_object* v_a_3891_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3888_, v_k_3889_, v_best_3890_, v_a_3891_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___redArg(lean_object* v_inst_3893_, lean_object* v_k_3894_, lean_object* v_a_3895_){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = lean_box(0);
v___x_3897_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3893_, v_k_3894_, v___x_3896_, v_a_3895_);
return v___x_3897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(lean_object* v_00_u03b1_3898_, lean_object* v_00_u03b2_3899_, lean_object* v_inst_3900_, lean_object* v_k_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_box(0);
v___x_3904_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3900_, v_k_3901_, v___x_3903_, v_a_3902_);
return v___x_3904_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object* v_inst_3905_, lean_object* v_k_3906_, lean_object* v_best_3907_, lean_object* v_a_3908_){
_start:
{
if (lean_obj_tag(v_a_3908_) == 0)
{
lean_object* v_k_3909_; lean_object* v_v_3910_; lean_object* v_l_3911_; lean_object* v_r_3912_; lean_object* v___x_3913_; uint8_t v___x_3914_; 
v_k_3909_ = lean_ctor_get(v_a_3908_, 1);
lean_inc_n(v_k_3909_, 2);
v_v_3910_ = lean_ctor_get(v_a_3908_, 2);
lean_inc(v_v_3910_);
v_l_3911_ = lean_ctor_get(v_a_3908_, 3);
lean_inc(v_l_3911_);
v_r_3912_ = lean_ctor_get(v_a_3908_, 4);
lean_inc(v_r_3912_);
lean_dec_ref_known(v_a_3908_, 5);
lean_inc_ref(v_inst_3905_);
lean_inc(v_k_3906_);
v___x_3913_ = lean_apply_2(v_inst_3905_, v_k_3906_, v_k_3909_);
v___x_3914_ = lean_unbox(v___x_3913_);
if (v___x_3914_ == 2)
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
lean_dec(v_l_3911_);
lean_dec(v_best_3907_);
v___x_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3915_, 0, v_k_3909_);
lean_ctor_set(v___x_3915_, 1, v_v_3910_);
v___x_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
v_best_3907_ = v___x_3916_;
v_a_3908_ = v_r_3912_;
goto _start;
}
else
{
lean_dec(v_r_3912_);
lean_dec(v_v_3910_);
lean_dec(v_k_3909_);
v_a_3908_ = v_l_3911_;
goto _start;
}
}
else
{
lean_dec(v_k_3906_);
lean_dec_ref(v_inst_3905_);
return v_best_3907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(lean_object* v_00_u03b1_3919_, lean_object* v_00_u03b2_3920_, lean_object* v_inst_3921_, lean_object* v_k_3922_, lean_object* v_best_3923_, lean_object* v_a_3924_){
_start:
{
lean_object* v___x_3925_; 
v___x_3925_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3921_, v_k_3922_, v_best_3923_, v_a_3924_);
return v___x_3925_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___redArg(lean_object* v_inst_3926_, lean_object* v_k_3927_, lean_object* v_a_3928_){
_start:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
v___x_3929_ = lean_box(0);
v___x_3930_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3926_, v_k_3927_, v___x_3929_, v_a_3928_);
return v___x_3930_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(lean_object* v_00_u03b1_3931_, lean_object* v_00_u03b2_3932_, lean_object* v_inst_3933_, lean_object* v_k_3934_, lean_object* v_a_3935_){
_start:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
v___x_3936_ = lean_box(0);
v___x_3937_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3933_, v_k_3934_, v___x_3936_, v_a_3935_);
return v___x_3937_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(lean_object* v_inst_3938_, lean_object* v_inst_3939_, lean_object* v_k_3940_, lean_object* v_t_3941_){
_start:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = lean_box(0);
v___x_3943_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3938_, v_k_3940_, v___x_3942_, v_t_3941_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3944_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3945_ = l_panic___redArg(v_inst_3939_, v___x_3944_);
return v___x_3945_;
}
else
{
lean_object* v_val_3946_; 
v_val_3946_ = lean_ctor_get(v___x_3943_, 0);
lean_inc(v_val_3946_);
lean_dec_ref_known(v___x_3943_, 1);
return v_val_3946_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg___boxed(lean_object* v_inst_3947_, lean_object* v_inst_3948_, lean_object* v_k_3949_, lean_object* v_t_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(v_inst_3947_, v_inst_3948_, v_k_3949_, v_t_3950_);
lean_dec_ref(v_inst_3948_);
return v_res_3951_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object* v_00_u03b1_3952_, lean_object* v_00_u03b2_3953_, lean_object* v_inst_3954_, lean_object* v_inst_3955_, lean_object* v_k_3956_, lean_object* v_t_3957_){
_start:
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = lean_box(0);
v___x_3959_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3954_, v_k_3956_, v___x_3958_, v_t_3957_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v___x_3960_; lean_object* v___x_3961_; 
v___x_3960_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3961_ = l_panic___redArg(v_inst_3955_, v___x_3960_);
return v___x_3961_;
}
else
{
lean_object* v_val_3962_; 
v_val_3962_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_val_3962_);
lean_dec_ref_known(v___x_3959_, 1);
return v_val_3962_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_3963_, lean_object* v_00_u03b2_3964_, lean_object* v_inst_3965_, lean_object* v_inst_3966_, lean_object* v_k_3967_, lean_object* v_t_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(v_00_u03b1_3963_, v_00_u03b2_3964_, v_inst_3965_, v_inst_3966_, v_k_3967_, v_t_3968_);
lean_dec_ref(v_inst_3966_);
return v_res_3969_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(lean_object* v_inst_3970_, lean_object* v_inst_3971_, lean_object* v_k_3972_, lean_object* v_t_3973_){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = lean_box(0);
v___x_3975_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3970_, v_k_3972_, v___x_3974_, v_t_3973_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3976_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3977_ = l_panic___redArg(v_inst_3971_, v___x_3976_);
return v___x_3977_;
}
else
{
lean_object* v_val_3978_; 
v_val_3978_ = lean_ctor_get(v___x_3975_, 0);
lean_inc(v_val_3978_);
lean_dec_ref_known(v___x_3975_, 1);
return v_val_3978_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg___boxed(lean_object* v_inst_3979_, lean_object* v_inst_3980_, lean_object* v_k_3981_, lean_object* v_t_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(v_inst_3979_, v_inst_3980_, v_k_3981_, v_t_3982_);
lean_dec_ref(v_inst_3980_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object* v_00_u03b1_3984_, lean_object* v_00_u03b2_3985_, lean_object* v_inst_3986_, lean_object* v_inst_3987_, lean_object* v_k_3988_, lean_object* v_t_3989_){
_start:
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = lean_box(0);
v___x_3991_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3986_, v_k_3988_, v___x_3990_, v_t_3989_);
if (lean_obj_tag(v___x_3991_) == 0)
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3993_ = l_panic___redArg(v_inst_3987_, v___x_3992_);
return v___x_3993_;
}
else
{
lean_object* v_val_3994_; 
v_val_3994_ = lean_ctor_get(v___x_3991_, 0);
lean_inc(v_val_3994_);
lean_dec_ref_known(v___x_3991_, 1);
return v_val_3994_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_3995_, lean_object* v_00_u03b2_3996_, lean_object* v_inst_3997_, lean_object* v_inst_3998_, lean_object* v_k_3999_, lean_object* v_t_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(v_00_u03b1_3995_, v_00_u03b2_3996_, v_inst_3997_, v_inst_3998_, v_k_3999_, v_t_4000_);
lean_dec_ref(v_inst_3998_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(lean_object* v_inst_4002_, lean_object* v_inst_4003_, lean_object* v_k_4004_, lean_object* v_t_4005_){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = lean_box(0);
v___x_4007_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4002_, v_k_4004_, v___x_4006_, v_t_4005_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4009_ = l_panic___redArg(v_inst_4003_, v___x_4008_);
return v___x_4009_;
}
else
{
lean_object* v_val_4010_; 
v_val_4010_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_val_4010_);
lean_dec_ref_known(v___x_4007_, 1);
return v_val_4010_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg___boxed(lean_object* v_inst_4011_, lean_object* v_inst_4012_, lean_object* v_k_4013_, lean_object* v_t_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(v_inst_4011_, v_inst_4012_, v_k_4013_, v_t_4014_);
lean_dec_ref(v_inst_4012_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object* v_00_u03b1_4016_, lean_object* v_00_u03b2_4017_, lean_object* v_inst_4018_, lean_object* v_inst_4019_, lean_object* v_k_4020_, lean_object* v_t_4021_){
_start:
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4022_ = lean_box(0);
v___x_4023_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4018_, v_k_4020_, v___x_4022_, v_t_4021_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4025_ = l_panic___redArg(v_inst_4019_, v___x_4024_);
return v___x_4025_;
}
else
{
lean_object* v_val_4026_; 
v_val_4026_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_val_4026_);
lean_dec_ref_known(v___x_4023_, 1);
return v_val_4026_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_4027_, lean_object* v_00_u03b2_4028_, lean_object* v_inst_4029_, lean_object* v_inst_4030_, lean_object* v_k_4031_, lean_object* v_t_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(v_00_u03b1_4027_, v_00_u03b2_4028_, v_inst_4029_, v_inst_4030_, v_k_4031_, v_t_4032_);
lean_dec_ref(v_inst_4030_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(lean_object* v_inst_4034_, lean_object* v_inst_4035_, lean_object* v_k_4036_, lean_object* v_t_4037_){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = lean_box(0);
v___x_4039_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4034_, v_k_4036_, v___x_4038_, v_t_4037_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4041_ = l_panic___redArg(v_inst_4035_, v___x_4040_);
return v___x_4041_;
}
else
{
lean_object* v_val_4042_; 
v_val_4042_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_val_4042_);
lean_dec_ref_known(v___x_4039_, 1);
return v_val_4042_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg___boxed(lean_object* v_inst_4043_, lean_object* v_inst_4044_, lean_object* v_k_4045_, lean_object* v_t_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(v_inst_4043_, v_inst_4044_, v_k_4045_, v_t_4046_);
lean_dec_ref(v_inst_4044_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object* v_00_u03b1_4048_, lean_object* v_00_u03b2_4049_, lean_object* v_inst_4050_, lean_object* v_inst_4051_, lean_object* v_k_4052_, lean_object* v_t_4053_){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_box(0);
v___x_4055_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4050_, v_k_4052_, v___x_4054_, v_t_4053_);
if (lean_obj_tag(v___x_4055_) == 0)
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4056_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4057_ = l_panic___redArg(v_inst_4051_, v___x_4056_);
return v___x_4057_;
}
else
{
lean_object* v_val_4058_; 
v_val_4058_ = lean_ctor_get(v___x_4055_, 0);
lean_inc(v_val_4058_);
lean_dec_ref_known(v___x_4055_, 1);
return v_val_4058_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_4059_, lean_object* v_00_u03b2_4060_, lean_object* v_inst_4061_, lean_object* v_inst_4062_, lean_object* v_k_4063_, lean_object* v_t_4064_){
_start:
{
lean_object* v_res_4065_; 
v_res_4065_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(v_00_u03b1_4059_, v_00_u03b2_4060_, v_inst_4061_, v_inst_4062_, v_k_4063_, v_t_4064_);
lean_dec_ref(v_inst_4062_);
return v_res_4065_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(lean_object* v_inst_4066_, lean_object* v_k_4067_, lean_object* v_t_4068_, lean_object* v_fallback_4069_){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = lean_box(0);
v___x_4071_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4066_, v_k_4067_, v___x_4070_, v_t_4068_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_inc_ref(v_fallback_4069_);
return v_fallback_4069_;
}
else
{
lean_object* v_val_4072_; 
v_val_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_val_4072_);
lean_dec_ref_known(v___x_4071_, 1);
return v_val_4072_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg___boxed(lean_object* v_inst_4073_, lean_object* v_k_4074_, lean_object* v_t_4075_, lean_object* v_fallback_4076_){
_start:
{
lean_object* v_res_4077_; 
v_res_4077_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(v_inst_4073_, v_k_4074_, v_t_4075_, v_fallback_4076_);
lean_dec_ref(v_fallback_4076_);
return v_res_4077_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(lean_object* v_00_u03b1_4078_, lean_object* v_00_u03b2_4079_, lean_object* v_inst_4080_, lean_object* v_k_4081_, lean_object* v_t_4082_, lean_object* v_fallback_4083_){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = lean_box(0);
v___x_4085_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4080_, v_k_4081_, v___x_4084_, v_t_4082_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_inc_ref(v_fallback_4083_);
return v_fallback_4083_;
}
else
{
lean_object* v_val_4086_; 
v_val_4086_ = lean_ctor_get(v___x_4085_, 0);
lean_inc(v_val_4086_);
lean_dec_ref_known(v___x_4085_, 1);
return v_val_4086_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___boxed(lean_object* v_00_u03b1_4087_, lean_object* v_00_u03b2_4088_, lean_object* v_inst_4089_, lean_object* v_k_4090_, lean_object* v_t_4091_, lean_object* v_fallback_4092_){
_start:
{
lean_object* v_res_4093_; 
v_res_4093_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(v_00_u03b1_4087_, v_00_u03b2_4088_, v_inst_4089_, v_k_4090_, v_t_4091_, v_fallback_4092_);
lean_dec_ref(v_fallback_4092_);
return v_res_4093_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(lean_object* v_inst_4094_, lean_object* v_k_4095_, lean_object* v_t_4096_, lean_object* v_fallback_4097_){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4098_ = lean_box(0);
v___x_4099_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4094_, v_k_4095_, v___x_4098_, v_t_4096_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_inc_ref(v_fallback_4097_);
return v_fallback_4097_;
}
else
{
lean_object* v_val_4100_; 
v_val_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_val_4100_);
lean_dec_ref_known(v___x_4099_, 1);
return v_val_4100_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg___boxed(lean_object* v_inst_4101_, lean_object* v_k_4102_, lean_object* v_t_4103_, lean_object* v_fallback_4104_){
_start:
{
lean_object* v_res_4105_; 
v_res_4105_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(v_inst_4101_, v_k_4102_, v_t_4103_, v_fallback_4104_);
lean_dec_ref(v_fallback_4104_);
return v_res_4105_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(lean_object* v_00_u03b1_4106_, lean_object* v_00_u03b2_4107_, lean_object* v_inst_4108_, lean_object* v_k_4109_, lean_object* v_t_4110_, lean_object* v_fallback_4111_){
_start:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_box(0);
v___x_4113_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4108_, v_k_4109_, v___x_4112_, v_t_4110_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_inc_ref(v_fallback_4111_);
return v_fallback_4111_;
}
else
{
lean_object* v_val_4114_; 
v_val_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc(v_val_4114_);
lean_dec_ref_known(v___x_4113_, 1);
return v_val_4114_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_4115_, lean_object* v_00_u03b2_4116_, lean_object* v_inst_4117_, lean_object* v_k_4118_, lean_object* v_t_4119_, lean_object* v_fallback_4120_){
_start:
{
lean_object* v_res_4121_; 
v_res_4121_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(v_00_u03b1_4115_, v_00_u03b2_4116_, v_inst_4117_, v_k_4118_, v_t_4119_, v_fallback_4120_);
lean_dec_ref(v_fallback_4120_);
return v_res_4121_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(lean_object* v_inst_4122_, lean_object* v_k_4123_, lean_object* v_t_4124_, lean_object* v_fallback_4125_){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_box(0);
v___x_4127_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4122_, v_k_4123_, v___x_4126_, v_t_4124_);
if (lean_obj_tag(v___x_4127_) == 0)
{
lean_inc_ref(v_fallback_4125_);
return v_fallback_4125_;
}
else
{
lean_object* v_val_4128_; 
v_val_4128_ = lean_ctor_get(v___x_4127_, 0);
lean_inc(v_val_4128_);
lean_dec_ref_known(v___x_4127_, 1);
return v_val_4128_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg___boxed(lean_object* v_inst_4129_, lean_object* v_k_4130_, lean_object* v_t_4131_, lean_object* v_fallback_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(v_inst_4129_, v_k_4130_, v_t_4131_, v_fallback_4132_);
lean_dec_ref(v_fallback_4132_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(lean_object* v_00_u03b1_4134_, lean_object* v_00_u03b2_4135_, lean_object* v_inst_4136_, lean_object* v_k_4137_, lean_object* v_t_4138_, lean_object* v_fallback_4139_){
_start:
{
lean_object* v___x_4140_; lean_object* v___x_4141_; 
v___x_4140_ = lean_box(0);
v___x_4141_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4136_, v_k_4137_, v___x_4140_, v_t_4138_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_inc_ref(v_fallback_4139_);
return v_fallback_4139_;
}
else
{
lean_object* v_val_4142_; 
v_val_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_val_4142_);
lean_dec_ref_known(v___x_4141_, 1);
return v_val_4142_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___boxed(lean_object* v_00_u03b1_4143_, lean_object* v_00_u03b2_4144_, lean_object* v_inst_4145_, lean_object* v_k_4146_, lean_object* v_t_4147_, lean_object* v_fallback_4148_){
_start:
{
lean_object* v_res_4149_; 
v_res_4149_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(v_00_u03b1_4143_, v_00_u03b2_4144_, v_inst_4145_, v_k_4146_, v_t_4147_, v_fallback_4148_);
lean_dec_ref(v_fallback_4148_);
return v_res_4149_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(lean_object* v_inst_4150_, lean_object* v_k_4151_, lean_object* v_t_4152_, lean_object* v_fallback_4153_){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = lean_box(0);
v___x_4155_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4150_, v_k_4151_, v___x_4154_, v_t_4152_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_inc_ref(v_fallback_4153_);
return v_fallback_4153_;
}
else
{
lean_object* v_val_4156_; 
v_val_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_val_4156_);
lean_dec_ref_known(v___x_4155_, 1);
return v_val_4156_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg___boxed(lean_object* v_inst_4157_, lean_object* v_k_4158_, lean_object* v_t_4159_, lean_object* v_fallback_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(v_inst_4157_, v_k_4158_, v_t_4159_, v_fallback_4160_);
lean_dec_ref(v_fallback_4160_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(lean_object* v_00_u03b1_4162_, lean_object* v_00_u03b2_4163_, lean_object* v_inst_4164_, lean_object* v_k_4165_, lean_object* v_t_4166_, lean_object* v_fallback_4167_){
_start:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4168_ = lean_box(0);
v___x_4169_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4164_, v_k_4165_, v___x_4168_, v_t_4166_);
if (lean_obj_tag(v___x_4169_) == 0)
{
lean_inc_ref(v_fallback_4167_);
return v_fallback_4167_;
}
else
{
lean_object* v_val_4170_; 
v_val_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc(v_val_4170_);
lean_dec_ref_known(v___x_4169_, 1);
return v_val_4170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_4171_, lean_object* v_00_u03b2_4172_, lean_object* v_inst_4173_, lean_object* v_k_4174_, lean_object* v_t_4175_, lean_object* v_fallback_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(v_00_u03b1_4171_, v_00_u03b2_4172_, v_inst_4173_, v_k_4174_, v_t_4175_, v_fallback_4176_);
lean_dec_ref(v_fallback_4176_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object* v_inst_4178_, lean_object* v_k_4179_, lean_object* v_x_4180_){
_start:
{
lean_object* v_k_4181_; lean_object* v_v_4182_; lean_object* v_l_4183_; lean_object* v_r_4184_; lean_object* v___x_4185_; uint8_t v___x_4186_; 
v_k_4181_ = lean_ctor_get(v_x_4180_, 1);
lean_inc_n(v_k_4181_, 2);
v_v_4182_ = lean_ctor_get(v_x_4180_, 2);
lean_inc(v_v_4182_);
v_l_4183_ = lean_ctor_get(v_x_4180_, 3);
lean_inc(v_l_4183_);
v_r_4184_ = lean_ctor_get(v_x_4180_, 4);
lean_inc(v_r_4184_);
lean_dec(v_x_4180_);
lean_inc_ref(v_inst_4178_);
lean_inc(v_k_4179_);
v___x_4185_ = lean_apply_2(v_inst_4178_, v_k_4179_, v_k_4181_);
v___x_4186_ = lean_unbox(v___x_4185_);
switch(v___x_4186_)
{
case 0:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
lean_dec(v_r_4184_);
v___x_4187_ = lean_box(0);
v___x_4188_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4178_, v_k_4179_, v___x_4187_, v_l_4183_);
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v___x_4189_; 
v___x_4189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4189_, 0, v_k_4181_);
lean_ctor_set(v___x_4189_, 1, v_v_4182_);
return v___x_4189_;
}
else
{
lean_object* v_val_4190_; 
lean_dec(v_v_4182_);
lean_dec(v_k_4181_);
v_val_4190_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_val_4190_);
lean_dec_ref_known(v___x_4188_, 1);
return v_val_4190_;
}
}
case 1:
{
lean_object* v___x_4191_; 
lean_dec(v_r_4184_);
lean_dec(v_l_4183_);
lean_dec(v_k_4179_);
lean_dec_ref(v_inst_4178_);
v___x_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4191_, 0, v_k_4181_);
lean_ctor_set(v___x_4191_, 1, v_v_4182_);
return v___x_4191_;
}
default: 
{
lean_dec(v_l_4183_);
lean_dec(v_v_4182_);
lean_dec(v_k_4181_);
v_x_4180_ = v_r_4184_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(lean_object* v_00_u03b1_4193_, lean_object* v_00_u03b2_4194_, lean_object* v_inst_4195_, lean_object* v_inst_4196_, lean_object* v_k_4197_, lean_object* v_x_4198_, lean_object* v_x_4199_, lean_object* v_x_4200_){
_start:
{
lean_object* v___x_4201_; 
v___x_4201_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_inst_4195_, v_k_4197_, v_x_4198_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object* v_inst_4202_, lean_object* v_k_4203_, lean_object* v_x_4204_){
_start:
{
lean_object* v_k_4205_; lean_object* v_v_4206_; lean_object* v_l_4207_; lean_object* v_r_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; 
v_k_4205_ = lean_ctor_get(v_x_4204_, 1);
lean_inc_n(v_k_4205_, 2);
v_v_4206_ = lean_ctor_get(v_x_4204_, 2);
lean_inc(v_v_4206_);
v_l_4207_ = lean_ctor_get(v_x_4204_, 3);
lean_inc(v_l_4207_);
v_r_4208_ = lean_ctor_get(v_x_4204_, 4);
lean_inc(v_r_4208_);
lean_dec(v_x_4204_);
lean_inc_ref(v_inst_4202_);
lean_inc(v_k_4203_);
v___x_4209_ = lean_apply_2(v_inst_4202_, v_k_4203_, v_k_4205_);
v___x_4210_ = lean_obj_tag_nat(v___x_4209_);
v___x_4211_ = lean_unsigned_to_nat(0u);
v___x_4212_ = lean_nat_dec_eq(v___x_4210_, v___x_4211_);
if (v___x_4212_ == 0)
{
lean_dec(v_l_4207_);
lean_dec(v_v_4206_);
lean_dec(v_k_4205_);
v_x_4204_ = v_r_4208_;
goto _start;
}
else
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
lean_dec(v_r_4208_);
v___x_4214_ = lean_box(0);
v___x_4215_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4202_, v_k_4203_, v___x_4214_, v_l_4207_);
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v___x_4216_; 
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v_k_4205_);
lean_ctor_set(v___x_4216_, 1, v_v_4206_);
return v___x_4216_;
}
else
{
lean_object* v_val_4217_; 
lean_dec(v_v_4206_);
lean_dec(v_k_4205_);
v_val_4217_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_val_4217_);
lean_dec_ref_known(v___x_4215_, 1);
return v_val_4217_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(lean_object* v_00_u03b1_4218_, lean_object* v_00_u03b2_4219_, lean_object* v_inst_4220_, lean_object* v_inst_4221_, lean_object* v_k_4222_, lean_object* v_x_4223_, lean_object* v_x_4224_, lean_object* v_x_4225_){
_start:
{
lean_object* v___x_4226_; 
v___x_4226_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_inst_4220_, v_k_4222_, v_x_4223_);
return v___x_4226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object* v_inst_4227_, lean_object* v_k_4228_, lean_object* v_x_4229_){
_start:
{
lean_object* v_k_4230_; lean_object* v_v_4231_; lean_object* v_l_4232_; lean_object* v_r_4233_; lean_object* v___x_4234_; uint8_t v___x_4235_; 
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
switch(v___x_4235_)
{
case 0:
{
lean_dec(v_r_4233_);
lean_dec(v_v_4231_);
lean_dec(v_k_4230_);
v_x_4229_ = v_l_4232_;
goto _start;
}
case 1:
{
lean_object* v___x_4237_; 
lean_dec(v_r_4233_);
lean_dec(v_l_4232_);
lean_dec(v_k_4228_);
lean_dec_ref(v_inst_4227_);
v___x_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4237_, 0, v_k_4230_);
lean_ctor_set(v___x_4237_, 1, v_v_4231_);
return v___x_4237_;
}
default: 
{
lean_object* v___x_4238_; lean_object* v___x_4239_; 
lean_dec(v_l_4232_);
v___x_4238_ = lean_box(0);
v___x_4239_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4227_, v_k_4228_, v___x_4238_, v_r_4233_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_object* v___x_4240_; 
v___x_4240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4240_, 0, v_k_4230_);
lean_ctor_set(v___x_4240_, 1, v_v_4231_);
return v___x_4240_;
}
else
{
lean_object* v_val_4241_; 
lean_dec(v_v_4231_);
lean_dec(v_k_4230_);
v_val_4241_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_val_4241_);
lean_dec_ref_known(v___x_4239_, 1);
return v_val_4241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(lean_object* v_00_u03b1_4242_, lean_object* v_00_u03b2_4243_, lean_object* v_inst_4244_, lean_object* v_inst_4245_, lean_object* v_k_4246_, lean_object* v_x_4247_, lean_object* v_x_4248_, lean_object* v_x_4249_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_inst_4244_, v_k_4246_, v_x_4247_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object* v_inst_4251_, lean_object* v_k_4252_, lean_object* v_x_4253_){
_start:
{
lean_object* v_k_4254_; lean_object* v_v_4255_; lean_object* v_l_4256_; lean_object* v_r_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; uint8_t v___x_4261_; 
v_k_4254_ = lean_ctor_get(v_x_4253_, 1);
lean_inc_n(v_k_4254_, 2);
v_v_4255_ = lean_ctor_get(v_x_4253_, 2);
lean_inc(v_v_4255_);
v_l_4256_ = lean_ctor_get(v_x_4253_, 3);
lean_inc(v_l_4256_);
v_r_4257_ = lean_ctor_get(v_x_4253_, 4);
lean_inc(v_r_4257_);
lean_dec(v_x_4253_);
lean_inc_ref(v_inst_4251_);
lean_inc(v_k_4252_);
v___x_4258_ = lean_apply_2(v_inst_4251_, v_k_4252_, v_k_4254_);
v___x_4259_ = lean_obj_tag_nat(v___x_4258_);
v___x_4260_ = lean_unsigned_to_nat(2u);
v___x_4261_ = lean_nat_dec_eq(v___x_4259_, v___x_4260_);
if (v___x_4261_ == 0)
{
lean_dec(v_r_4257_);
lean_dec(v_v_4255_);
lean_dec(v_k_4254_);
v_x_4253_ = v_l_4256_;
goto _start;
}
else
{
lean_object* v___x_4263_; lean_object* v___x_4264_; 
lean_dec(v_l_4256_);
v___x_4263_ = lean_box(0);
v___x_4264_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4251_, v_k_4252_, v___x_4263_, v_r_4257_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v___x_4265_; 
v___x_4265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4265_, 0, v_k_4254_);
lean_ctor_set(v___x_4265_, 1, v_v_4255_);
return v___x_4265_;
}
else
{
lean_object* v_val_4266_; 
lean_dec(v_v_4255_);
lean_dec(v_k_4254_);
v_val_4266_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_val_4266_);
lean_dec_ref_known(v___x_4264_, 1);
return v_val_4266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(lean_object* v_00_u03b1_4267_, lean_object* v_00_u03b2_4268_, lean_object* v_inst_4269_, lean_object* v_inst_4270_, lean_object* v_k_4271_, lean_object* v_x_4272_, lean_object* v_x_4273_, lean_object* v_x_4274_){
_start:
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_inst_4269_, v_k_4271_, v_x_4272_);
return v___x_4275_;
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
