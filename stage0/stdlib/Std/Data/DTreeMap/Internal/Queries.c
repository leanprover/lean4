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
lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall___redArg(){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(0);
return v___x_2_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_instCoeTypeForall___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3_;
v_res_3_ = l_Std_DTreeMap_Internal_Impl_instCoeTypeForall___redArg();
stack->m_obj
 = v_res_3_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall___redArg___boxed(lean_object* v___dummy_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Std_DTreeMap_Internal_Impl_instCoeTypeForall___redArg();
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instCoeTypeForall(lean_object* v_00_u03b1_6_){
_start:
{
lean_object* v___x_7_; 
v___x_7_ = lean_box(0);
return v___x_7_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__5));
v___x_52_ = l_String_toRawSubstring_x27(v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1(lean_object* v_x_75_, lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_78_; uint8_t v___x_79_; 
v___x_78_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5));
lean_inc(v_x_75_);
v___x_79_ = l_Lean_Syntax_isOfKind(v_x_75_, v___x_78_);
if (v___x_79_ == 0)
{
lean_object* v___x_80_; lean_object* v___x_81_; 
lean_dec(v_x_75_);
v___x_80_ = lean_box(1);
v___x_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v_a_77_);
return v___x_81_;
}
else
{
lean_object* v_quotContext_82_; lean_object* v_currMacroScope_83_; lean_object* v_ref_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; uint8_t v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_quotContext_82_ = lean_ctor_get(v_a_76_, 1);
v_currMacroScope_83_ = lean_ctor_get(v_a_76_, 2);
v_ref_84_ = lean_ctor_get(v_a_76_, 5);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = l_Lean_Syntax_getArg(v_x_75_, v___x_85_);
v___x_87_ = lean_unsigned_to_nat(2u);
v___x_88_ = l_Lean_Syntax_getArg(v_x_75_, v___x_87_);
lean_dec(v_x_75_);
v___x_89_ = 0;
v___x_90_ = l_Lean_SourceInfo_fromRef(v_ref_84_, v___x_89_);
v___x_91_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4));
v___x_92_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6, &l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6_once, _init_l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__6);
v___x_93_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__7));
lean_inc(v_currMacroScope_83_);
lean_inc(v_quotContext_82_);
v___x_94_ = l_Lean_addMacroScope(v_quotContext_82_, v___x_93_, v_currMacroScope_83_);
v___x_95_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__12));
lean_inc_n(v___x_90_, 2);
v___x_96_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_96_, 0, v___x_90_);
lean_ctor_set(v___x_96_, 1, v___x_92_);
lean_ctor_set(v___x_96_, 2, v___x_94_);
lean_ctor_set(v___x_96_, 3, v___x_95_);
v___x_97_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__14));
v___x_98_ = l_Lean_Syntax_node2(v___x_90_, v___x_97_, v___x_86_, v___x_88_);
v___x_99_ = l_Lean_Syntax_node2(v___x_90_, v___x_91_, v___x_96_, v___x_98_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_a_77_);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___boxed(lean_object* v_x_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1(v_x_101_, v_a_102_, v_a_103_);
lean_dec_ref(v_a_102_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(lean_object* v_x_108_, lean_object* v_a_109_, lean_object* v_a_110_){
_start:
{
lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_111_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______macroRules__Std__DTreeMap__Internal__Impl__term___x7em____1___closed__4));
lean_inc(v_x_108_);
v___x_112_ = l_Lean_Syntax_isOfKind(v_x_108_, v___x_111_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; 
lean_dec(v_x_108_);
v___x_113_ = lean_box(0);
v___x_114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_a_110_);
return v___x_114_;
}
else
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = l_Lean_Syntax_getArg(v_x_108_, v___x_115_);
v___x_117_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___closed__1));
lean_inc(v___x_116_);
v___x_118_ = l_Lean_Syntax_isOfKind(v___x_116_, v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; lean_object* v___x_120_; 
lean_dec(v___x_116_);
lean_dec(v_x_108_);
v___x_119_ = lean_box(0);
v___x_120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v_a_110_);
return v___x_120_;
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_121_ = lean_unsigned_to_nat(1u);
v___x_122_ = l_Lean_Syntax_getArg(v_x_108_, v___x_121_);
lean_dec(v_x_108_);
v___x_123_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_122_);
v___x_124_ = l_Lean_Syntax_matchesNull(v___x_122_, v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v___x_126_; 
lean_dec(v___x_122_);
lean_dec(v___x_116_);
v___x_125_ = lean_box(0);
v___x_126_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_126_, 0, v___x_125_);
lean_ctor_set(v___x_126_, 1, v_a_110_);
return v___x_126_;
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v_ref_129_; uint8_t v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_127_ = l_Lean_Syntax_getArg(v___x_122_, v___x_115_);
v___x_128_ = l_Lean_Syntax_getArg(v___x_122_, v___x_121_);
lean_dec(v___x_122_);
v_ref_129_ = l_Lean_replaceRef(v___x_116_, v_a_109_);
lean_dec(v___x_116_);
v___x_130_ = 0;
v___x_131_ = l_Lean_SourceInfo_fromRef(v_ref_129_, v___x_130_);
lean_dec(v_ref_129_);
v___x_132_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__5));
v___x_133_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_term___x7em___00__closed__8));
lean_inc(v___x_131_);
v___x_134_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_131_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = l_Lean_Syntax_node3(v___x_131_, v___x_132_, v___x_127_, v___x_134_, v___x_128_);
v___x_136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_136_, 0, v___x_135_);
lean_ctor_set(v___x_136_, 1, v_a_110_);
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1___boxed(lean_object* v_x_137_, lean_object* v_a_138_, lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Std_DTreeMap_Internal_Impl___aux__Std__Data__DTreeMap__Internal__Queries______unexpand__Std__DTreeMap__Internal__Impl__Equiv__1(v_x_137_, v_a_138_, v_a_139_);
lean_dec(v_a_138_);
return v_res_140_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains___redArg(lean_object* v_inst_141_, lean_object* v_k_142_, lean_object* v_t_143_){
_start:
{
if (lean_obj_tag(v_t_143_) == 0)
{
lean_object* v_k_144_; lean_object* v_l_145_; lean_object* v_r_146_; lean_object* v___x_147_; uint8_t v___x_148_; 
v_k_144_ = lean_ctor_get(v_t_143_, 1);
lean_inc(v_k_144_);
v_l_145_ = lean_ctor_get(v_t_143_, 3);
lean_inc(v_l_145_);
v_r_146_ = lean_ctor_get(v_t_143_, 4);
lean_inc(v_r_146_);
lean_dec_ref_known(v_t_143_, 5);
lean_inc_ref(v_inst_141_);
lean_inc(v_k_142_);
v___x_147_ = lean_apply_2(v_inst_141_, v_k_142_, v_k_144_);
v___x_148_ = lean_unbox(v___x_147_);
switch(v___x_148_)
{
case 0:
{
lean_dec(v_r_146_);
v_t_143_ = v_l_145_;
goto _start;
}
case 1:
{
uint8_t v___x_150_; 
lean_dec(v_r_146_);
lean_dec(v_l_145_);
lean_dec(v_k_142_);
lean_dec_ref(v_inst_141_);
v___x_150_ = 1;
return v___x_150_;
}
default: 
{
lean_dec(v_l_145_);
v_t_143_ = v_r_146_;
goto _start;
}
}
}
else
{
uint8_t v___x_152_; 
lean_dec(v_k_142_);
lean_dec_ref(v_inst_141_);
v___x_152_ = 0;
return v___x_152_;
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_141_ = stack[0].m_obj;
lean_object* v_k_142_ = stack[1].m_obj;
lean_object* v_t_143_ = stack[2].m_obj;
uint8_t v_res_153_;
v_res_153_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_141_, v_k_142_, v_t_143_);
stack->m_num = v_res_153_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___redArg___boxed(lean_object* v_inst_154_, lean_object* v_k_155_, lean_object* v_t_156_){
_start:
{
uint8_t v_res_157_; lean_object* v_r_158_; 
v_res_157_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_154_, v_k_155_, v_t_156_);
v_r_158_ = lean_box(v_res_157_);
return v_r_158_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_contains(lean_object* v_00_u03b1_159_, lean_object* v_00_u03b2_160_, lean_object* v_inst_161_, lean_object* v_k_162_, lean_object* v_t_163_){
_start:
{
uint8_t v___x_164_; 
v___x_164_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_161_, v_k_162_, v_t_163_);
return v___x_164_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_161_ = stack[2].m_obj;
lean_object* v_k_162_ = stack[3].m_obj;
lean_object* v_t_163_ = stack[4].m_obj;
uint8_t v_res_165_;
v_res_165_ = l_Std_DTreeMap_Internal_Impl_contains(lean_box(0), lean_box(0), v_inst_161_, v_k_162_, v_t_163_);
stack->m_num = v_res_165_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___boxed(lean_object* v_00_u03b1_166_, lean_object* v_00_u03b2_167_, lean_object* v_inst_168_, lean_object* v_k_169_, lean_object* v_t_170_){
_start:
{
uint8_t v_res_171_; lean_object* v_r_172_; 
v_res_171_ = l_Std_DTreeMap_Internal_Impl_contains(v_00_u03b1_166_, v_00_u03b2_167_, v_inst_168_, v_k_169_, v_t_170_);
v_r_172_ = lean_box(v_res_171_);
return v_r_172_;
}
}
lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___redArg(){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lean_box(0);
return v___x_174_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_175_;
v_res_175_ = l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___redArg();
stack->m_obj
 = v_res_175_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___redArg___boxed(lean_object* v___dummy_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___redArg();
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(lean_object* v_00_u03b1_178_, lean_object* v_00_u03b2_179_, lean_object* v_inst_180_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = lean_box(0);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd___boxed(lean_object* v_00_u03b1_182_, lean_object* v_00_u03b2_183_, lean_object* v_inst_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_DTreeMap_Internal_Impl_instMembershipOfOrd(v_00_u03b1_182_, v_00_u03b2_183_, v_inst_184_);
lean_dec_ref(v_inst_184_);
return v_res_185_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(lean_object* v_inst_186_, lean_object* v_m_187_, lean_object* v_a_188_){
_start:
{
uint8_t v___x_189_; 
v___x_189_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_186_, v_a_188_, v_m_187_);
return v___x_189_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_186_ = stack[0].m_obj;
lean_object* v_m_187_ = stack[1].m_obj;
lean_object* v_a_188_ = stack[2].m_obj;
uint8_t v_res_190_;
v_res_190_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(v_inst_186_, v_m_187_, v_a_188_);
stack->m_num = v_res_190_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg___boxed(lean_object* v_inst_191_, lean_object* v_m_192_, lean_object* v_a_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem___redArg(v_inst_191_, v_m_192_, v_a_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_instDecidableMem(lean_object* v_00_u03b1_196_, lean_object* v_00_u03b2_197_, lean_object* v_inst_198_, lean_object* v_m_199_, lean_object* v_a_200_){
_start:
{
uint8_t v___x_201_; 
v___x_201_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(v_inst_198_, v_a_200_, v_m_199_);
return v___x_201_;
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_instDecidableMem_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_198_ = stack[2].m_obj;
lean_object* v_m_199_ = stack[3].m_obj;
lean_object* v_a_200_ = stack[4].m_obj;
uint8_t v_res_202_;
v_res_202_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem(lean_box(0), lean_box(0), v_inst_198_, v_m_199_, v_a_200_);
stack->m_num = v_res_202_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instDecidableMem___boxed(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_inst_205_, lean_object* v_m_206_, lean_object* v_a_207_){
_start:
{
uint8_t v_res_208_; lean_object* v_r_209_; 
v_res_208_ = l_Std_DTreeMap_Internal_Impl_instDecidableMem(v_00_u03b1_203_, v_00_u03b2_204_, v_inst_205_, v_m_206_, v_a_207_);
v_r_209_ = lean_box(v_res_208_);
return v_r_209_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(uint8_t v_x_210_, lean_object* v_h__1_211_, lean_object* v_h__2_212_, lean_object* v_h__3_213_){
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
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_210_ = stack[0].m_num;
lean_object* v_h__1_211_ = stack[1].m_obj;
lean_object* v_h__2_212_ = stack[2].m_obj;
lean_object* v_h__3_213_ = stack[3].m_obj;
lean_object* v_res_220_;
v_res_220_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_210_, v_h__1_211_, v_h__2_212_, v_h__3_213_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg___boxed(lean_object* v_x_221_, lean_object* v_h__1_222_, lean_object* v_h__2_223_, lean_object* v_h__3_224_){
_start:
{
uint8_t v_x_33__boxed_225_; lean_object* v_res_226_; 
v_x_33__boxed_225_ = lean_unbox(v_x_221_);
v_res_226_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___redArg(v_x_33__boxed_225_, v_h__1_222_, v_h__2_223_, v_h__3_224_);
return v_res_226_;
}
}
lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_object* v_motive_227_, uint8_t v_x_228_, lean_object* v_h__1_229_, lean_object* v_h__2_230_, lean_object* v_h__3_231_){
_start:
{
switch(v_x_228_)
{
case 0:
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_h__3_231_);
lean_dec(v_h__2_230_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_apply_1(v_h__1_229_, v___x_232_);
return v___x_233_;
}
case 1:
{
lean_object* v___x_234_; lean_object* v___x_235_; 
lean_dec(v_h__2_230_);
lean_dec(v_h__1_229_);
v___x_234_ = lean_box(0);
v___x_235_ = lean_apply_1(v_h__3_231_, v___x_234_);
return v___x_235_;
}
default: 
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_h__3_231_);
lean_dec(v_h__1_229_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_apply_1(v_h__2_230_, v___x_236_);
return v___x_237_;
}
}
}
}
LEAN_EXPORT void l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_228_ = stack[1].m_num;
lean_object* v_h__1_229_ = stack[2].m_obj;
lean_object* v_h__2_230_ = stack[3].m_obj;
lean_object* v_h__3_231_ = stack[4].m_obj;
lean_object* v_res_238_;
v_res_238_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(lean_box(0), v_x_228_, v_h__1_229_, v_h__2_230_, v_h__3_231_);
stack->m_obj
 = v_res_238_;
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter___boxed(lean_object* v_motive_239_, lean_object* v_x_240_, lean_object* v_h__1_241_, lean_object* v_h__2_242_, lean_object* v_h__3_243_){
_start:
{
uint8_t v_x_56__boxed_244_; lean_object* v_res_245_; 
v_x_56__boxed_244_ = lean_unbox(v_x_240_);
v_res_245_ = l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_contains_match__1_splitter(v_motive_239_, v_x_56__boxed_244_, v_h__1_241_, v_h__2_242_, v_h__3_243_);
return v_res_245_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(lean_object* v_t_246_){
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
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_isEmpty___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_246_ = stack[0].m_obj;
uint8_t v_res_249_;
v_res_249_ = l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(v_t_246_);
stack->m_num = v_res_249_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___redArg___boxed(lean_object* v_t_250_){
_start:
{
uint8_t v_res_251_; lean_object* v_r_252_; 
v_res_251_ = l_Std_DTreeMap_Internal_Impl_isEmpty___redArg(v_t_250_);
lean_dec(v_t_250_);
v_r_252_ = lean_box(v_res_251_);
return v_r_252_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_isEmpty(lean_object* v_00_u03b1_253_, lean_object* v_00_u03b2_254_, lean_object* v_t_255_){
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
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_isEmpty_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_255_ = stack[2].m_obj;
uint8_t v_res_258_;
v_res_258_ = l_Std_DTreeMap_Internal_Impl_isEmpty(lean_box(0), lean_box(0), v_t_255_);
stack->m_num = v_res_258_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_isEmpty___boxed(lean_object* v_00_u03b1_259_, lean_object* v_00_u03b2_260_, lean_object* v_t_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Std_DTreeMap_Internal_Impl_isEmpty(v_00_u03b1_259_, v_00_u03b2_260_, v_t_261_);
lean_dec(v_t_261_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(lean_object* v_inst_264_, lean_object* v_t_265_, lean_object* v_k_266_){
_start:
{
if (lean_obj_tag(v_t_265_) == 0)
{
lean_object* v_k_267_; lean_object* v_v_268_; lean_object* v_l_269_; lean_object* v_r_270_; lean_object* v___x_271_; uint8_t v___x_272_; 
v_k_267_ = lean_ctor_get(v_t_265_, 1);
lean_inc(v_k_267_);
v_v_268_ = lean_ctor_get(v_t_265_, 2);
lean_inc(v_v_268_);
v_l_269_ = lean_ctor_get(v_t_265_, 3);
lean_inc(v_l_269_);
v_r_270_ = lean_ctor_get(v_t_265_, 4);
lean_inc(v_r_270_);
lean_dec_ref_known(v_t_265_, 5);
lean_inc_ref(v_inst_264_);
lean_inc(v_k_266_);
v___x_271_ = lean_apply_2(v_inst_264_, v_k_266_, v_k_267_);
v___x_272_ = lean_unbox(v___x_271_);
switch(v___x_272_)
{
case 0:
{
lean_dec(v_r_270_);
lean_dec(v_v_268_);
v_t_265_ = v_l_269_;
goto _start;
}
case 1:
{
lean_object* v___x_274_; 
lean_dec(v_r_270_);
lean_dec(v_l_269_);
lean_dec(v_k_266_);
lean_dec_ref(v_inst_264_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v_v_268_);
return v___x_274_;
}
default: 
{
lean_dec(v_l_269_);
lean_dec(v_v_268_);
v_t_265_ = v_r_270_;
goto _start;
}
}
}
else
{
lean_object* v___x_276_; 
lean_dec(v_k_266_);
lean_dec_ref(v_inst_264_);
v___x_276_ = lean_box(0);
return v___x_276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x3f(lean_object* v_00_u03b1_277_, lean_object* v_00_u03b2_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_t_281_, lean_object* v_k_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_Std_DTreeMap_Internal_Impl_get_x3f___redArg(v_inst_279_, v_t_281_, v_k_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get___redArg(lean_object* v_inst_284_, lean_object* v_t_285_, lean_object* v_k_286_){
_start:
{
lean_object* v_k_287_; lean_object* v_v_288_; lean_object* v_l_289_; lean_object* v_r_290_; lean_object* v___x_291_; uint8_t v___x_292_; 
v_k_287_ = lean_ctor_get(v_t_285_, 1);
lean_inc(v_k_287_);
v_v_288_ = lean_ctor_get(v_t_285_, 2);
lean_inc(v_v_288_);
v_l_289_ = lean_ctor_get(v_t_285_, 3);
lean_inc(v_l_289_);
v_r_290_ = lean_ctor_get(v_t_285_, 4);
lean_inc(v_r_290_);
lean_dec(v_t_285_);
lean_inc_ref(v_inst_284_);
lean_inc(v_k_286_);
v___x_291_ = lean_apply_2(v_inst_284_, v_k_286_, v_k_287_);
v___x_292_ = lean_unbox(v___x_291_);
switch(v___x_292_)
{
case 0:
{
lean_dec(v_r_290_);
lean_dec(v_v_288_);
v_t_285_ = v_l_289_;
goto _start;
}
case 1:
{
lean_dec(v_r_290_);
lean_dec(v_l_289_);
lean_dec(v_k_286_);
lean_dec_ref(v_inst_284_);
return v_v_288_;
}
default: 
{
lean_dec(v_l_289_);
lean_dec(v_v_288_);
v_t_285_ = v_r_290_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get(lean_object* v_00_u03b1_295_, lean_object* v_00_u03b2_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_t_299_, lean_object* v_k_300_, lean_object* v_hlk_301_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Std_DTreeMap_Internal_Impl_get___redArg(v_inst_297_, v_t_299_, v_k_300_);
return v___x_302_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_306_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_307_ = lean_unsigned_to_nat(13u);
v___x_308_ = lean_unsigned_to_nat(108u);
v___x_309_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__1));
v___x_310_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_311_ = l_mkPanicMessageWithDecl(v___x_310_, v___x_309_, v___x_308_, v___x_307_, v___x_306_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg(lean_object* v_inst_312_, lean_object* v_t_313_, lean_object* v_k_314_, lean_object* v_inst_315_){
_start:
{
if (lean_obj_tag(v_t_313_) == 0)
{
lean_object* v_k_316_; lean_object* v_v_317_; lean_object* v_l_318_; lean_object* v_r_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v_k_316_ = lean_ctor_get(v_t_313_, 1);
lean_inc(v_k_316_);
v_v_317_ = lean_ctor_get(v_t_313_, 2);
lean_inc(v_v_317_);
v_l_318_ = lean_ctor_get(v_t_313_, 3);
lean_inc(v_l_318_);
v_r_319_ = lean_ctor_get(v_t_313_, 4);
lean_inc(v_r_319_);
lean_dec_ref_known(v_t_313_, 5);
lean_inc_ref(v_inst_312_);
lean_inc(v_k_314_);
v___x_320_ = lean_apply_2(v_inst_312_, v_k_314_, v_k_316_);
v___x_321_ = lean_unbox(v___x_320_);
switch(v___x_321_)
{
case 0:
{
lean_dec(v_r_319_);
lean_dec(v_v_317_);
v_t_313_ = v_l_318_;
goto _start;
}
case 1:
{
lean_dec(v_r_319_);
lean_dec(v_l_318_);
lean_dec(v_k_314_);
lean_dec_ref(v_inst_312_);
return v_v_317_;
}
default: 
{
lean_dec(v_l_318_);
lean_dec(v_v_317_);
v_t_313_ = v_r_319_;
goto _start;
}
}
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v_k_314_);
lean_dec_ref(v_inst_312_);
v___x_324_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__3);
v___x_325_ = l_panic___redArg(v_inst_315_, v___x_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___redArg___boxed(lean_object* v_inst_326_, lean_object* v_t_327_, lean_object* v_k_328_, lean_object* v_inst_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_inst_326_, v_t_327_, v_k_328_, v_inst_329_);
lean_dec(v_inst_329_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21(lean_object* v_00_u03b1_331_, lean_object* v_00_u03b2_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_t_335_, lean_object* v_k_336_, lean_object* v_inst_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Std_DTreeMap_Internal_Impl_get_x21___redArg(v_inst_333_, v_t_335_, v_k_336_, v_inst_337_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_get_x21___boxed(lean_object* v_00_u03b1_339_, lean_object* v_00_u03b2_340_, lean_object* v_inst_341_, lean_object* v_inst_342_, lean_object* v_t_343_, lean_object* v_k_344_, lean_object* v_inst_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Std_DTreeMap_Internal_Impl_get_x21(v_00_u03b1_339_, v_00_u03b2_340_, v_inst_341_, v_inst_342_, v_t_343_, v_k_344_, v_inst_345_);
lean_dec(v_inst_345_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg(lean_object* v_inst_347_, lean_object* v_t_348_, lean_object* v_k_349_, lean_object* v_fallback_350_){
_start:
{
if (lean_obj_tag(v_t_348_) == 0)
{
lean_object* v_k_351_; lean_object* v_v_352_; lean_object* v_l_353_; lean_object* v_r_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v_k_351_ = lean_ctor_get(v_t_348_, 1);
lean_inc(v_k_351_);
v_v_352_ = lean_ctor_get(v_t_348_, 2);
lean_inc(v_v_352_);
v_l_353_ = lean_ctor_get(v_t_348_, 3);
lean_inc(v_l_353_);
v_r_354_ = lean_ctor_get(v_t_348_, 4);
lean_inc(v_r_354_);
lean_dec_ref_known(v_t_348_, 5);
lean_inc_ref(v_inst_347_);
lean_inc(v_k_349_);
v___x_355_ = lean_apply_2(v_inst_347_, v_k_349_, v_k_351_);
v___x_356_ = lean_unbox(v___x_355_);
switch(v___x_356_)
{
case 0:
{
lean_dec(v_r_354_);
lean_dec(v_v_352_);
v_t_348_ = v_l_353_;
goto _start;
}
case 1:
{
lean_dec(v_r_354_);
lean_dec(v_l_353_);
lean_dec(v_k_349_);
lean_dec_ref(v_inst_347_);
return v_v_352_;
}
default: 
{
lean_dec(v_l_353_);
lean_dec(v_v_352_);
v_t_348_ = v_r_354_;
goto _start;
}
}
}
else
{
lean_dec(v_k_349_);
lean_dec_ref(v_inst_347_);
lean_inc(v_fallback_350_);
return v_fallback_350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___redArg___boxed(lean_object* v_inst_359_, lean_object* v_t_360_, lean_object* v_k_361_, lean_object* v_fallback_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_inst_359_, v_t_360_, v_k_361_, v_fallback_362_);
lean_dec(v_fallback_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_inst_366_, lean_object* v_inst_367_, lean_object* v_t_368_, lean_object* v_k_369_, lean_object* v_fallback_370_){
_start:
{
lean_object* v___x_371_; 
v___x_371_ = l_Std_DTreeMap_Internal_Impl_getD___redArg(v_inst_366_, v_t_368_, v_k_369_, v_fallback_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getD___boxed(lean_object* v_00_u03b1_372_, lean_object* v_00_u03b2_373_, lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_t_376_, lean_object* v_k_377_, lean_object* v_fallback_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Std_DTreeMap_Internal_Impl_getD(v_00_u03b1_372_, v_00_u03b2_373_, v_inst_374_, v_inst_375_, v_t_376_, v_k_377_, v_fallback_378_);
lean_dec(v_fallback_378_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(lean_object* v_inst_380_, lean_object* v_t_381_, lean_object* v_k_382_){
_start:
{
if (lean_obj_tag(v_t_381_) == 0)
{
lean_object* v_k_383_; lean_object* v_v_384_; lean_object* v_l_385_; lean_object* v_r_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_k_383_ = lean_ctor_get(v_t_381_, 1);
lean_inc_n(v_k_383_, 2);
v_v_384_ = lean_ctor_get(v_t_381_, 2);
lean_inc(v_v_384_);
v_l_385_ = lean_ctor_get(v_t_381_, 3);
lean_inc(v_l_385_);
v_r_386_ = lean_ctor_get(v_t_381_, 4);
lean_inc(v_r_386_);
lean_dec_ref_known(v_t_381_, 5);
lean_inc_ref(v_inst_380_);
lean_inc(v_k_382_);
v___x_387_ = lean_apply_2(v_inst_380_, v_k_382_, v_k_383_);
v___x_388_ = lean_unbox(v___x_387_);
switch(v___x_388_)
{
case 0:
{
lean_dec(v_r_386_);
lean_dec(v_v_384_);
lean_dec(v_k_383_);
v_t_381_ = v_l_385_;
goto _start;
}
case 1:
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v_r_386_);
lean_dec(v_l_385_);
lean_dec(v_k_382_);
lean_dec_ref(v_inst_380_);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_k_383_);
lean_ctor_set(v___x_390_, 1, v_v_384_);
v___x_391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
default: 
{
lean_dec(v_l_385_);
lean_dec(v_v_384_);
lean_dec(v_k_383_);
v_t_381_ = v_r_386_;
goto _start;
}
}
}
else
{
lean_object* v___x_393_; 
lean_dec(v_k_382_);
lean_dec_ref(v_inst_380_);
v___x_393_ = lean_box(0);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x3f(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_inst_396_, lean_object* v_t_397_, lean_object* v_k_398_){
_start:
{
lean_object* v___x_399_; 
v___x_399_ = l_Std_DTreeMap_Internal_Impl_getEntry_x3f___redArg(v_inst_396_, v_t_397_, v_k_398_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry___redArg(lean_object* v_inst_400_, lean_object* v_t_401_, lean_object* v_k_402_){
_start:
{
lean_object* v_k_403_; lean_object* v_v_404_; lean_object* v_l_405_; lean_object* v_r_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_k_403_ = lean_ctor_get(v_t_401_, 1);
lean_inc_n(v_k_403_, 2);
v_v_404_ = lean_ctor_get(v_t_401_, 2);
lean_inc(v_v_404_);
v_l_405_ = lean_ctor_get(v_t_401_, 3);
lean_inc(v_l_405_);
v_r_406_ = lean_ctor_get(v_t_401_, 4);
lean_inc(v_r_406_);
lean_dec(v_t_401_);
lean_inc_ref(v_inst_400_);
lean_inc(v_k_402_);
v___x_407_ = lean_apply_2(v_inst_400_, v_k_402_, v_k_403_);
v___x_408_ = lean_unbox(v___x_407_);
switch(v___x_408_)
{
case 0:
{
lean_dec(v_r_406_);
lean_dec(v_v_404_);
lean_dec(v_k_403_);
v_t_401_ = v_l_405_;
goto _start;
}
case 1:
{
lean_object* v___x_410_; 
lean_dec(v_r_406_);
lean_dec(v_l_405_);
lean_dec(v_k_402_);
lean_dec_ref(v_inst_400_);
v___x_410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_410_, 0, v_k_403_);
lean_ctor_set(v___x_410_, 1, v_v_404_);
return v___x_410_;
}
default: 
{
lean_dec(v_l_405_);
lean_dec(v_v_404_);
lean_dec(v_k_403_);
v_t_401_ = v_r_406_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry(lean_object* v_00_u03b1_412_, lean_object* v_00_u03b2_413_, lean_object* v_inst_414_, lean_object* v_t_415_, lean_object* v_k_416_, lean_object* v_hlk_417_){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Std_DTreeMap_Internal_Impl_getEntry___redArg(v_inst_414_, v_t_415_, v_k_416_);
return v___x_418_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_420_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_421_ = lean_unsigned_to_nat(13u);
v___x_422_ = lean_unsigned_to_nat(147u);
v___x_423_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__0));
v___x_424_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_425_ = l_mkPanicMessageWithDecl(v___x_424_, v___x_423_, v___x_422_, v___x_421_, v___x_420_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_t_428_, lean_object* v_k_429_){
_start:
{
if (lean_obj_tag(v_t_428_) == 0)
{
lean_object* v_k_430_; lean_object* v_v_431_; lean_object* v_l_432_; lean_object* v_r_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_k_430_ = lean_ctor_get(v_t_428_, 1);
lean_inc_n(v_k_430_, 2);
v_v_431_ = lean_ctor_get(v_t_428_, 2);
lean_inc(v_v_431_);
v_l_432_ = lean_ctor_get(v_t_428_, 3);
lean_inc(v_l_432_);
v_r_433_ = lean_ctor_get(v_t_428_, 4);
lean_inc(v_r_433_);
lean_dec_ref_known(v_t_428_, 5);
lean_inc_ref(v_inst_426_);
lean_inc(v_k_429_);
v___x_434_ = lean_apply_2(v_inst_426_, v_k_429_, v_k_430_);
v___x_435_ = lean_unbox(v___x_434_);
switch(v___x_435_)
{
case 0:
{
lean_dec(v_r_433_);
lean_dec(v_v_431_);
lean_dec(v_k_430_);
v_t_428_ = v_l_432_;
goto _start;
}
case 1:
{
lean_object* v___x_437_; 
lean_dec(v_r_433_);
lean_dec(v_l_432_);
lean_dec(v_k_429_);
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
v_t_428_ = v_r_433_;
goto _start;
}
}
}
else
{
lean_object* v___x_439_; lean_object* v___x_440_; 
lean_dec(v_k_429_);
lean_dec_ref(v_inst_426_);
v___x_439_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___closed__1);
v___x_440_ = l_panic___redArg(v_inst_427_, v___x_439_);
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg___boxed(lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_t_443_, lean_object* v_k_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_inst_441_, v_inst_442_, v_t_443_, v_k_444_);
lean_dec_ref(v_inst_442_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21(lean_object* v_00_u03b1_446_, lean_object* v_00_u03b2_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_t_450_, lean_object* v_k_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21___redArg(v_inst_448_, v_inst_449_, v_t_450_, v_k_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntry_x21___boxed(lean_object* v_00_u03b1_453_, lean_object* v_00_u03b2_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_t_457_, lean_object* v_k_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Std_DTreeMap_Internal_Impl_getEntry_x21(v_00_u03b1_453_, v_00_u03b2_454_, v_inst_455_, v_inst_456_, v_t_457_, v_k_458_);
lean_dec_ref(v_inst_456_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(lean_object* v_inst_460_, lean_object* v_t_461_, lean_object* v_k_462_, lean_object* v_fallback_463_){
_start:
{
if (lean_obj_tag(v_t_461_) == 0)
{
lean_object* v_k_464_; lean_object* v_v_465_; lean_object* v_l_466_; lean_object* v_r_467_; lean_object* v___x_468_; uint8_t v___x_469_; 
v_k_464_ = lean_ctor_get(v_t_461_, 1);
lean_inc_n(v_k_464_, 2);
v_v_465_ = lean_ctor_get(v_t_461_, 2);
lean_inc(v_v_465_);
v_l_466_ = lean_ctor_get(v_t_461_, 3);
lean_inc(v_l_466_);
v_r_467_ = lean_ctor_get(v_t_461_, 4);
lean_inc(v_r_467_);
lean_dec_ref_known(v_t_461_, 5);
lean_inc_ref(v_inst_460_);
lean_inc(v_k_462_);
v___x_468_ = lean_apply_2(v_inst_460_, v_k_462_, v_k_464_);
v___x_469_ = lean_unbox(v___x_468_);
switch(v___x_469_)
{
case 0:
{
lean_dec(v_r_467_);
lean_dec(v_v_465_);
lean_dec(v_k_464_);
v_t_461_ = v_l_466_;
goto _start;
}
case 1:
{
lean_object* v___x_471_; 
lean_dec(v_r_467_);
lean_dec(v_l_466_);
lean_dec(v_k_462_);
lean_dec_ref(v_inst_460_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v_k_464_);
lean_ctor_set(v___x_471_, 1, v_v_465_);
return v___x_471_;
}
default: 
{
lean_dec(v_l_466_);
lean_dec(v_v_465_);
lean_dec(v_k_464_);
v_t_461_ = v_r_467_;
goto _start;
}
}
}
else
{
lean_dec(v_k_462_);
lean_dec_ref(v_inst_460_);
lean_inc_ref(v_fallback_463_);
return v_fallback_463_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___redArg___boxed(lean_object* v_inst_473_, lean_object* v_t_474_, lean_object* v_k_475_, lean_object* v_fallback_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_473_, v_t_474_, v_k_475_, v_fallback_476_);
lean_dec_ref(v_fallback_476_);
return v_res_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD(lean_object* v_00_u03b1_478_, lean_object* v_00_u03b2_479_, lean_object* v_inst_480_, lean_object* v_t_481_, lean_object* v_k_482_, lean_object* v_fallback_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = l_Std_DTreeMap_Internal_Impl_getEntryD___redArg(v_inst_480_, v_t_481_, v_k_482_, v_fallback_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryD___boxed(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b2_486_, lean_object* v_inst_487_, lean_object* v_t_488_, lean_object* v_k_489_, lean_object* v_fallback_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_DTreeMap_Internal_Impl_getEntryD(v_00_u03b1_485_, v_00_u03b2_486_, v_inst_487_, v_t_488_, v_k_489_, v_fallback_490_);
lean_dec_ref(v_fallback_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(lean_object* v_inst_492_, lean_object* v_t_493_, lean_object* v_k_494_){
_start:
{
if (lean_obj_tag(v_t_493_) == 0)
{
lean_object* v_k_495_; lean_object* v_l_496_; lean_object* v_r_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_k_495_ = lean_ctor_get(v_t_493_, 1);
lean_inc_n(v_k_495_, 2);
v_l_496_ = lean_ctor_get(v_t_493_, 3);
lean_inc(v_l_496_);
v_r_497_ = lean_ctor_get(v_t_493_, 4);
lean_inc(v_r_497_);
lean_dec_ref_known(v_t_493_, 5);
lean_inc_ref(v_inst_492_);
lean_inc(v_k_494_);
v___x_498_ = lean_apply_2(v_inst_492_, v_k_494_, v_k_495_);
v___x_499_ = lean_unbox(v___x_498_);
switch(v___x_499_)
{
case 0:
{
lean_dec(v_r_497_);
lean_dec(v_k_495_);
v_t_493_ = v_l_496_;
goto _start;
}
case 1:
{
lean_object* v___x_501_; 
lean_dec(v_r_497_);
lean_dec(v_l_496_);
lean_dec(v_k_494_);
lean_dec_ref(v_inst_492_);
v___x_501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_501_, 0, v_k_495_);
return v___x_501_;
}
default: 
{
lean_dec(v_l_496_);
lean_dec(v_k_495_);
v_t_493_ = v_r_497_;
goto _start;
}
}
}
else
{
lean_object* v___x_503_; 
lean_dec(v_k_494_);
lean_dec_ref(v_inst_492_);
v___x_503_ = lean_box(0);
return v___x_503_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x3f(lean_object* v_00_u03b1_504_, lean_object* v_00_u03b2_505_, lean_object* v_inst_506_, lean_object* v_t_507_, lean_object* v_k_508_){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = l_Std_DTreeMap_Internal_Impl_getKey_x3f___redArg(v_inst_506_, v_t_507_, v_k_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey___redArg(lean_object* v_inst_510_, lean_object* v_t_511_, lean_object* v_k_512_){
_start:
{
lean_object* v_k_513_; lean_object* v_l_514_; lean_object* v_r_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
v_k_513_ = lean_ctor_get(v_t_511_, 1);
lean_inc_n(v_k_513_, 2);
v_l_514_ = lean_ctor_get(v_t_511_, 3);
lean_inc(v_l_514_);
v_r_515_ = lean_ctor_get(v_t_511_, 4);
lean_inc(v_r_515_);
lean_dec(v_t_511_);
lean_inc_ref(v_inst_510_);
lean_inc(v_k_512_);
v___x_516_ = lean_apply_2(v_inst_510_, v_k_512_, v_k_513_);
v___x_517_ = lean_unbox(v___x_516_);
switch(v___x_517_)
{
case 0:
{
lean_dec(v_r_515_);
lean_dec(v_k_513_);
v_t_511_ = v_l_514_;
goto _start;
}
case 1:
{
lean_dec(v_r_515_);
lean_dec(v_l_514_);
lean_dec(v_k_512_);
lean_dec_ref(v_inst_510_);
return v_k_513_;
}
default: 
{
lean_dec(v_l_514_);
lean_dec(v_k_513_);
v_t_511_ = v_r_515_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey(lean_object* v_00_u03b1_520_, lean_object* v_00_u03b2_521_, lean_object* v_inst_522_, lean_object* v_t_523_, lean_object* v_k_524_, lean_object* v_hlk_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Std_DTreeMap_Internal_Impl_getKey___redArg(v_inst_522_, v_t_523_, v_k_524_);
return v___x_526_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_528_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_529_ = lean_unsigned_to_nat(13u);
v___x_530_ = lean_unsigned_to_nat(186u);
v___x_531_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__0));
v___x_532_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_533_ = l_mkPanicMessageWithDecl(v___x_532_, v___x_531_, v___x_530_, v___x_529_, v___x_528_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(lean_object* v_inst_534_, lean_object* v_t_535_, lean_object* v_k_536_, lean_object* v_inst_537_){
_start:
{
if (lean_obj_tag(v_t_535_) == 0)
{
lean_object* v_k_538_; lean_object* v_l_539_; lean_object* v_r_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v_k_538_ = lean_ctor_get(v_t_535_, 1);
lean_inc_n(v_k_538_, 2);
v_l_539_ = lean_ctor_get(v_t_535_, 3);
lean_inc(v_l_539_);
v_r_540_ = lean_ctor_get(v_t_535_, 4);
lean_inc(v_r_540_);
lean_dec_ref_known(v_t_535_, 5);
lean_inc_ref(v_inst_534_);
lean_inc(v_k_536_);
v___x_541_ = lean_apply_2(v_inst_534_, v_k_536_, v_k_538_);
v___x_542_ = lean_unbox(v___x_541_);
switch(v___x_542_)
{
case 0:
{
lean_dec(v_r_540_);
lean_dec(v_k_538_);
v_t_535_ = v_l_539_;
goto _start;
}
case 1:
{
lean_dec(v_r_540_);
lean_dec(v_l_539_);
lean_dec(v_k_536_);
lean_dec_ref(v_inst_534_);
return v_k_538_;
}
default: 
{
lean_dec(v_l_539_);
lean_dec(v_k_538_);
v_t_535_ = v_r_540_;
goto _start;
}
}
}
else
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_dec(v_k_536_);
lean_dec_ref(v_inst_534_);
v___x_545_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___closed__1);
v___x_546_ = l_panic___redArg(v_inst_537_, v___x_545_);
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg___boxed(lean_object* v_inst_547_, lean_object* v_t_548_, lean_object* v_k_549_, lean_object* v_inst_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_inst_547_, v_t_548_, v_k_549_, v_inst_550_);
lean_dec(v_inst_550_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21(lean_object* v_00_u03b1_552_, lean_object* v_00_u03b2_553_, lean_object* v_inst_554_, lean_object* v_t_555_, lean_object* v_k_556_, lean_object* v_inst_557_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Std_DTreeMap_Internal_Impl_getKey_x21___redArg(v_inst_554_, v_t_555_, v_k_556_, v_inst_557_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKey_x21___boxed(lean_object* v_00_u03b1_559_, lean_object* v_00_u03b2_560_, lean_object* v_inst_561_, lean_object* v_t_562_, lean_object* v_k_563_, lean_object* v_inst_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Std_DTreeMap_Internal_Impl_getKey_x21(v_00_u03b1_559_, v_00_u03b2_560_, v_inst_561_, v_t_562_, v_k_563_, v_inst_564_);
lean_dec(v_inst_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(lean_object* v_inst_566_, lean_object* v_t_567_, lean_object* v_k_568_, lean_object* v_fallback_569_){
_start:
{
if (lean_obj_tag(v_t_567_) == 0)
{
lean_object* v_k_570_; lean_object* v_l_571_; lean_object* v_r_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v_k_570_ = lean_ctor_get(v_t_567_, 1);
lean_inc_n(v_k_570_, 2);
v_l_571_ = lean_ctor_get(v_t_567_, 3);
lean_inc(v_l_571_);
v_r_572_ = lean_ctor_get(v_t_567_, 4);
lean_inc(v_r_572_);
lean_dec_ref_known(v_t_567_, 5);
lean_inc_ref(v_inst_566_);
lean_inc(v_k_568_);
v___x_573_ = lean_apply_2(v_inst_566_, v_k_568_, v_k_570_);
v___x_574_ = lean_unbox(v___x_573_);
switch(v___x_574_)
{
case 0:
{
lean_dec(v_r_572_);
lean_dec(v_k_570_);
v_t_567_ = v_l_571_;
goto _start;
}
case 1:
{
lean_dec(v_r_572_);
lean_dec(v_l_571_);
lean_dec(v_k_568_);
lean_dec_ref(v_inst_566_);
return v_k_570_;
}
default: 
{
lean_dec(v_l_571_);
lean_dec(v_k_570_);
v_t_567_ = v_r_572_;
goto _start;
}
}
}
else
{
lean_dec(v_k_568_);
lean_dec_ref(v_inst_566_);
lean_inc(v_fallback_569_);
return v_fallback_569_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___redArg___boxed(lean_object* v_inst_577_, lean_object* v_t_578_, lean_object* v_k_579_, lean_object* v_fallback_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_577_, v_t_578_, v_k_579_, v_fallback_580_);
lean_dec(v_fallback_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD(lean_object* v_00_u03b1_582_, lean_object* v_00_u03b2_583_, lean_object* v_inst_584_, lean_object* v_t_585_, lean_object* v_k_586_, lean_object* v_fallback_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Std_DTreeMap_Internal_Impl_getKeyD___redArg(v_inst_584_, v_t_585_, v_k_586_, v_fallback_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyD___boxed(lean_object* v_00_u03b1_589_, lean_object* v_00_u03b2_590_, lean_object* v_inst_591_, lean_object* v_t_592_, lean_object* v_k_593_, lean_object* v_fallback_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Std_DTreeMap_Internal_Impl_getKeyD(v_00_u03b1_589_, v_00_u03b2_590_, v_inst_591_, v_t_592_, v_k_593_, v_fallback_594_);
lean_dec(v_fallback_594_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object* v_inst_596_, lean_object* v_t_597_, lean_object* v_k_598_){
_start:
{
if (lean_obj_tag(v_t_597_) == 0)
{
lean_object* v_k_599_; lean_object* v_v_600_; lean_object* v_l_601_; lean_object* v_r_602_; lean_object* v___x_603_; uint8_t v___x_604_; 
v_k_599_ = lean_ctor_get(v_t_597_, 1);
lean_inc(v_k_599_);
v_v_600_ = lean_ctor_get(v_t_597_, 2);
lean_inc(v_v_600_);
v_l_601_ = lean_ctor_get(v_t_597_, 3);
lean_inc(v_l_601_);
v_r_602_ = lean_ctor_get(v_t_597_, 4);
lean_inc(v_r_602_);
lean_dec_ref_known(v_t_597_, 5);
lean_inc_ref(v_inst_596_);
lean_inc(v_k_598_);
v___x_603_ = lean_apply_2(v_inst_596_, v_k_598_, v_k_599_);
v___x_604_ = lean_unbox(v___x_603_);
switch(v___x_604_)
{
case 0:
{
lean_dec(v_r_602_);
lean_dec(v_v_600_);
v_t_597_ = v_l_601_;
goto _start;
}
case 1:
{
lean_object* v___x_606_; 
lean_dec(v_r_602_);
lean_dec(v_l_601_);
lean_dec(v_k_598_);
lean_dec_ref(v_inst_596_);
v___x_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_606_, 0, v_v_600_);
return v___x_606_;
}
default: 
{
lean_dec(v_l_601_);
lean_dec(v_v_600_);
v_t_597_ = v_r_602_;
goto _start;
}
}
}
else
{
lean_object* v___x_608_; 
lean_dec(v_k_598_);
lean_dec_ref(v_inst_596_);
v___x_608_ = lean_box(0);
return v___x_608_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f(lean_object* v_00_u03b1_609_, lean_object* v_00_u03b4_610_, lean_object* v_inst_611_, lean_object* v_t_612_, lean_object* v_k_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v_inst_611_, v_t_612_, v_k_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get___redArg(lean_object* v_inst_615_, lean_object* v_t_616_, lean_object* v_k_617_){
_start:
{
lean_object* v_k_618_; lean_object* v_v_619_; lean_object* v_l_620_; lean_object* v_r_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_k_618_ = lean_ctor_get(v_t_616_, 1);
lean_inc(v_k_618_);
v_v_619_ = lean_ctor_get(v_t_616_, 2);
lean_inc(v_v_619_);
v_l_620_ = lean_ctor_get(v_t_616_, 3);
lean_inc(v_l_620_);
v_r_621_ = lean_ctor_get(v_t_616_, 4);
lean_inc(v_r_621_);
lean_dec(v_t_616_);
lean_inc_ref(v_inst_615_);
lean_inc(v_k_617_);
v___x_622_ = lean_apply_2(v_inst_615_, v_k_617_, v_k_618_);
v___x_623_ = lean_unbox(v___x_622_);
switch(v___x_623_)
{
case 0:
{
lean_dec(v_r_621_);
lean_dec(v_v_619_);
v_t_616_ = v_l_620_;
goto _start;
}
case 1:
{
lean_dec(v_r_621_);
lean_dec(v_l_620_);
lean_dec(v_k_617_);
lean_dec_ref(v_inst_615_);
return v_v_619_;
}
default: 
{
lean_dec(v_l_620_);
lean_dec(v_v_619_);
v_t_616_ = v_r_621_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get(lean_object* v_00_u03b1_626_, lean_object* v_00_u03b4_627_, lean_object* v_inst_628_, lean_object* v_t_629_, lean_object* v_k_630_, lean_object* v_hlk_631_){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = l_Std_DTreeMap_Internal_Impl_Const_get___redArg(v_inst_628_, v_t_629_, v_k_630_);
return v___x_632_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; 
v___x_634_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__2));
v___x_635_ = lean_unsigned_to_nat(13u);
v___x_636_ = lean_unsigned_to_nat(227u);
v___x_637_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__0));
v___x_638_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_639_ = l_mkPanicMessageWithDecl(v___x_638_, v___x_637_, v___x_636_, v___x_635_, v___x_634_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(lean_object* v_inst_640_, lean_object* v_inst_641_, lean_object* v_t_642_, lean_object* v_k_643_){
_start:
{
if (lean_obj_tag(v_t_642_) == 0)
{
lean_object* v_k_644_; lean_object* v_v_645_; lean_object* v_l_646_; lean_object* v_r_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_k_644_ = lean_ctor_get(v_t_642_, 1);
lean_inc(v_k_644_);
v_v_645_ = lean_ctor_get(v_t_642_, 2);
lean_inc(v_v_645_);
v_l_646_ = lean_ctor_get(v_t_642_, 3);
lean_inc(v_l_646_);
v_r_647_ = lean_ctor_get(v_t_642_, 4);
lean_inc(v_r_647_);
lean_dec_ref_known(v_t_642_, 5);
lean_inc_ref(v_inst_640_);
lean_inc(v_k_643_);
v___x_648_ = lean_apply_2(v_inst_640_, v_k_643_, v_k_644_);
v___x_649_ = lean_unbox(v___x_648_);
switch(v___x_649_)
{
case 0:
{
lean_dec(v_r_647_);
lean_dec(v_v_645_);
v_t_642_ = v_l_646_;
goto _start;
}
case 1:
{
lean_dec(v_r_647_);
lean_dec(v_l_646_);
lean_dec(v_k_643_);
lean_dec_ref(v_inst_640_);
return v_v_645_;
}
default: 
{
lean_dec(v_l_646_);
lean_dec(v_v_645_);
v_t_642_ = v_r_647_;
goto _start;
}
}
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_k_643_);
lean_dec_ref(v_inst_640_);
v___x_652_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___closed__1);
v___x_653_ = l_panic___redArg(v_inst_641_, v___x_652_);
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg___boxed(lean_object* v_inst_654_, lean_object* v_inst_655_, lean_object* v_t_656_, lean_object* v_k_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_inst_654_, v_inst_655_, v_t_656_, v_k_657_);
lean_dec(v_inst_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21(lean_object* v_00_u03b1_659_, lean_object* v_00_u03b4_660_, lean_object* v_inst_661_, lean_object* v_inst_662_, lean_object* v_t_663_, lean_object* v_k_664_){
_start:
{
lean_object* v___x_665_; 
v___x_665_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___redArg(v_inst_661_, v_inst_662_, v_t_663_, v_k_664_);
return v___x_665_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___boxed(lean_object* v_00_u03b1_666_, lean_object* v_00_u03b4_667_, lean_object* v_inst_668_, lean_object* v_inst_669_, lean_object* v_t_670_, lean_object* v_k_671_){
_start:
{
lean_object* v_res_672_; 
v_res_672_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21(v_00_u03b1_666_, v_00_u03b4_667_, v_inst_668_, v_inst_669_, v_t_670_, v_k_671_);
lean_dec(v_inst_669_);
return v_res_672_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(lean_object* v_inst_673_, lean_object* v_t_674_, lean_object* v_k_675_, lean_object* v_fallback_676_){
_start:
{
if (lean_obj_tag(v_t_674_) == 0)
{
lean_object* v_k_677_; lean_object* v_v_678_; lean_object* v_l_679_; lean_object* v_r_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_k_677_ = lean_ctor_get(v_t_674_, 1);
lean_inc(v_k_677_);
v_v_678_ = lean_ctor_get(v_t_674_, 2);
lean_inc(v_v_678_);
v_l_679_ = lean_ctor_get(v_t_674_, 3);
lean_inc(v_l_679_);
v_r_680_ = lean_ctor_get(v_t_674_, 4);
lean_inc(v_r_680_);
lean_dec_ref_known(v_t_674_, 5);
lean_inc_ref(v_inst_673_);
lean_inc(v_k_675_);
v___x_681_ = lean_apply_2(v_inst_673_, v_k_675_, v_k_677_);
v___x_682_ = lean_unbox(v___x_681_);
switch(v___x_682_)
{
case 0:
{
lean_dec(v_r_680_);
lean_dec(v_v_678_);
v_t_674_ = v_l_679_;
goto _start;
}
case 1:
{
lean_dec(v_r_680_);
lean_dec(v_l_679_);
lean_dec(v_k_675_);
lean_dec_ref(v_inst_673_);
return v_v_678_;
}
default: 
{
lean_dec(v_l_679_);
lean_dec(v_v_678_);
v_t_674_ = v_r_680_;
goto _start;
}
}
}
else
{
lean_dec(v_k_675_);
lean_dec_ref(v_inst_673_);
lean_inc(v_fallback_676_);
return v_fallback_676_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___redArg___boxed(lean_object* v_inst_685_, lean_object* v_t_686_, lean_object* v_k_687_, lean_object* v_fallback_688_){
_start:
{
lean_object* v_res_689_; 
v_res_689_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_685_, v_t_686_, v_k_687_, v_fallback_688_);
lean_dec(v_fallback_688_);
return v_res_689_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD(lean_object* v_00_u03b1_690_, lean_object* v_00_u03b4_691_, lean_object* v_inst_692_, lean_object* v_t_693_, lean_object* v_k_694_, lean_object* v_fallback_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_Std_DTreeMap_Internal_Impl_Const_getD___redArg(v_inst_692_, v_t_693_, v_k_694_, v_fallback_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___boxed(lean_object* v_00_u03b1_697_, lean_object* v_00_u03b4_698_, lean_object* v_inst_699_, lean_object* v_t_700_, lean_object* v_k_701_, lean_object* v_fallback_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_Std_DTreeMap_Internal_Impl_Const_getD(v_00_u03b1_697_, v_00_u03b4_698_, v_inst_699_, v_t_700_, v_k_701_, v_fallback_702_);
lean_dec(v_fallback_702_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1(lean_object* v_f_704_, lean_object* v_k_705_, lean_object* v_v_706_, lean_object* v_toBind_707_, lean_object* v___f_708_, lean_object* v_left_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_apply_3(v_f_704_, v_left_709_, v_k_705_, v_v_706_);
v___x_711_ = lean_apply_4(v_toBind_707_, lean_box(0), lean_box(0), v___x_710_, v___f_708_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg(lean_object* v_inst_712_, lean_object* v_f_713_, lean_object* v_init_714_, lean_object* v_x_715_){
_start:
{
if (lean_obj_tag(v_x_715_) == 0)
{
lean_object* v_toBind_716_; lean_object* v_k_717_; lean_object* v_v_718_; lean_object* v_l_719_; lean_object* v_r_720_; lean_object* v___f_721_; lean_object* v___f_722_; lean_object* v___x_723_; lean_object* v___x_724_; 
v_toBind_716_ = lean_ctor_get(v_inst_712_, 1);
lean_inc_n(v_toBind_716_, 2);
v_k_717_ = lean_ctor_get(v_x_715_, 1);
lean_inc(v_k_717_);
v_v_718_ = lean_ctor_get(v_x_715_, 2);
lean_inc(v_v_718_);
v_l_719_ = lean_ctor_get(v_x_715_, 3);
lean_inc(v_l_719_);
v_r_720_ = lean_ctor_get(v_x_715_, 4);
lean_inc(v_r_720_);
lean_dec_ref_known(v_x_715_, 5);
lean_inc_n(v_f_713_, 2);
lean_inc_ref(v_inst_712_);
v___f_721_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_721_, 0, v_inst_712_);
lean_closure_set(v___f_721_, 1, v_f_713_);
lean_closure_set(v___f_721_, 2, v_r_720_);
v___f_722_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_722_, 0, v_f_713_);
lean_closure_set(v___f_722_, 1, v_k_717_);
lean_closure_set(v___f_722_, 2, v_v_718_);
lean_closure_set(v___f_722_, 3, v_toBind_716_);
lean_closure_set(v___f_722_, 4, v___f_721_);
v___x_723_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_712_, v_f_713_, v_init_714_, v_l_719_);
v___x_724_ = lean_apply_4(v_toBind_716_, lean_box(0), lean_box(0), v___x_723_, v___f_722_);
return v___x_724_;
}
else
{
lean_object* v_toApplicative_725_; lean_object* v_toPure_726_; lean_object* v___x_727_; 
v_toApplicative_725_ = lean_ctor_get(v_inst_712_, 0);
lean_inc_ref(v_toApplicative_725_);
lean_dec(v_f_713_);
lean_dec_ref(v_inst_712_);
v_toPure_726_ = lean_ctor_get(v_toApplicative_725_, 1);
lean_inc(v_toPure_726_);
lean_dec_ref(v_toApplicative_725_);
v___x_727_ = lean_apply_2(v_toPure_726_, lean_box(0), v_init_714_);
return v___x_727_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___redArg___lam__0(lean_object* v_inst_728_, lean_object* v_f_729_, lean_object* v_r_730_, lean_object* v_middle_731_){
_start:
{
lean_object* v___x_732_; 
v___x_732_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_728_, v_f_729_, v_middle_731_, v_r_730_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM(lean_object* v_00_u03b1_733_, lean_object* v_00_u03b2_734_, lean_object* v_00_u03b4_735_, lean_object* v_m_736_, lean_object* v_inst_737_, lean_object* v_f_738_, lean_object* v_init_739_, lean_object* v_x_740_){
_start:
{
lean_object* v___x_741_; 
v___x_741_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_737_, v_f_738_, v_init_739_, v_x_740_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0(lean_object* v_f_742_, lean_object* v_x1_743_, lean_object* v_x2_744_, lean_object* v_x3_745_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = lean_apply_3(v_f_742_, v_x1_743_, v_x2_744_, v_x3_745_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___redArg(lean_object* v_f_766_, lean_object* v_init_767_, lean_object* v_t_768_){
_start:
{
lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___f_769_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_769_, 0, v_f_766_);
v___x_770_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_771_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v___x_770_, v___f_769_, v_init_767_, v_t_768_);
return v___x_771_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl(lean_object* v_00_u03b1_772_, lean_object* v_00_u03b2_773_, lean_object* v_00_u03b4_774_, lean_object* v_f_775_, lean_object* v_init_776_, lean_object* v_t_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v_f_775_, v_init_776_, v_t_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1(lean_object* v_f_779_, lean_object* v_k_780_, lean_object* v_v_781_, lean_object* v_toBind_782_, lean_object* v___f_783_, lean_object* v_right_784_){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = lean_apply_3(v_f_779_, v_k_780_, v_v_781_, v_right_784_);
v___x_786_ = lean_apply_4(v_toBind_782_, lean_box(0), lean_box(0), v___x_785_, v___f_783_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object* v_inst_787_, lean_object* v_f_788_, lean_object* v_init_789_, lean_object* v_x_790_){
_start:
{
if (lean_obj_tag(v_x_790_) == 0)
{
lean_object* v_toBind_791_; lean_object* v_k_792_; lean_object* v_v_793_; lean_object* v_l_794_; lean_object* v_r_795_; lean_object* v___f_796_; lean_object* v___f_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v_toBind_791_ = lean_ctor_get(v_inst_787_, 1);
lean_inc_n(v_toBind_791_, 2);
v_k_792_ = lean_ctor_get(v_x_790_, 1);
lean_inc(v_k_792_);
v_v_793_ = lean_ctor_get(v_x_790_, 2);
lean_inc(v_v_793_);
v_l_794_ = lean_ctor_get(v_x_790_, 3);
lean_inc(v_l_794_);
v_r_795_ = lean_ctor_get(v_x_790_, 4);
lean_inc(v_r_795_);
lean_dec_ref_known(v_x_790_, 5);
lean_inc_n(v_f_788_, 2);
lean_inc_ref(v_inst_787_);
v___f_796_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0), 4, 3);
lean_closure_set(v___f_796_, 0, v_inst_787_);
lean_closure_set(v___f_796_, 1, v_f_788_);
lean_closure_set(v___f_796_, 2, v_l_794_);
v___f_797_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_797_, 0, v_f_788_);
lean_closure_set(v___f_797_, 1, v_k_792_);
lean_closure_set(v___f_797_, 2, v_v_793_);
lean_closure_set(v___f_797_, 3, v_toBind_791_);
lean_closure_set(v___f_797_, 4, v___f_796_);
v___x_798_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_787_, v_f_788_, v_init_789_, v_r_795_);
v___x_799_ = lean_apply_4(v_toBind_791_, lean_box(0), lean_box(0), v___x_798_, v___f_797_);
return v___x_799_;
}
else
{
lean_object* v_toApplicative_800_; lean_object* v_toPure_801_; lean_object* v___x_802_; 
v_toApplicative_800_ = lean_ctor_get(v_inst_787_, 0);
lean_inc_ref(v_toApplicative_800_);
lean_dec(v_f_788_);
lean_dec_ref(v_inst_787_);
v_toPure_801_ = lean_ctor_get(v_toApplicative_800_, 1);
lean_inc(v_toPure_801_);
lean_dec_ref(v_toApplicative_800_);
v___x_802_ = lean_apply_2(v_toPure_801_, lean_box(0), v_init_789_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg___lam__0(lean_object* v_inst_803_, lean_object* v_f_804_, lean_object* v_l_805_, lean_object* v_middle_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_803_, v_f_804_, v_middle_806_, v_l_805_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM(lean_object* v_00_u03b1_808_, lean_object* v_00_u03b2_809_, lean_object* v_00_u03b4_810_, lean_object* v_m_811_, lean_object* v_inst_812_, lean_object* v_f_813_, lean_object* v_init_814_, lean_object* v_x_815_){
_start:
{
lean_object* v___x_816_; 
v___x_816_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v_inst_812_, v_f_813_, v_init_814_, v_x_815_);
return v___x_816_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr___redArg(lean_object* v_f_817_, lean_object* v_init_818_, lean_object* v_t_819_){
_start:
{
lean_object* v___f_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___f_820_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_820_, 0, v_f_817_);
v___x_821_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_822_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_821_, v___f_820_, v_init_818_, v_t_819_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldr(lean_object* v_00_u03b1_823_, lean_object* v_00_u03b2_824_, lean_object* v_00_u03b4_825_, lean_object* v_f_826_, lean_object* v_init_827_, lean_object* v_t_828_){
_start:
{
lean_object* v___f_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___f_829_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___lam__0), 4, 1);
lean_closure_set(v___f_829_, 0, v_f_826_);
v___x_830_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_831_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_830_, v___f_829_, v_init_827_, v_t_828_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0(lean_object* v_f_832_, lean_object* v_x_833_, lean_object* v_k_834_, lean_object* v_v_835_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = lean_apply_2(v_f_832_, v_k_834_, v_v_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM___redArg(lean_object* v_inst_837_, lean_object* v_f_838_, lean_object* v_t_839_){
_start:
{
lean_object* v___f_840_; lean_object* v___x_841_; lean_object* v___x_842_; 
v___f_840_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_840_, 0, v_f_838_);
v___x_841_ = lean_box(0);
v___x_842_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_837_, v___f_840_, v___x_841_, v_t_839_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forM(lean_object* v_00_u03b1_843_, lean_object* v_00_u03b2_844_, lean_object* v_m_845_, lean_object* v_inst_846_, lean_object* v_f_847_, lean_object* v_t_848_){
_start:
{
lean_object* v___f_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___f_849_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forM___redArg___lam__0), 4, 1);
lean_closure_set(v___f_849_, 0, v_f_847_);
v___x_850_ = lean_box(0);
v___x_851_ = l_Std_DTreeMap_Internal_Impl_foldlM___redArg(v_inst_846_, v___f_849_, v___x_850_, v_t_848_);
return v___x_851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0(lean_object* v_toPure_852_, lean_object* v_d_853_){
_start:
{
lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v_d_853_);
v___x_855_ = lean_apply_2(v_toPure_852_, lean_box(0), v___x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2(lean_object* v___f_856_, lean_object* v_f_857_, lean_object* v_k_858_, lean_object* v_v_859_, lean_object* v_toBind_860_, lean_object* v___f_861_, lean_object* v_____do__lift_862_){
_start:
{
if (lean_obj_tag(v_____do__lift_862_) == 0)
{
lean_object* v_a_863_; lean_object* v___x_864_; 
lean_dec(v___f_861_);
lean_dec(v_toBind_860_);
lean_dec(v_v_859_);
lean_dec(v_k_858_);
lean_dec(v_f_857_);
v_a_863_ = lean_ctor_get(v_____do__lift_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v_____do__lift_862_, 1);
v___x_864_ = lean_apply_1(v___f_856_, v_a_863_);
return v___x_864_;
}
else
{
lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v___x_867_; 
lean_dec(v___f_856_);
v_a_865_ = lean_ctor_get(v_____do__lift_862_, 0);
lean_inc(v_a_865_);
lean_dec_ref_known(v_____do__lift_862_, 1);
v___x_866_ = lean_apply_3(v_f_857_, v_k_858_, v_v_859_, v_a_865_);
v___x_867_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v___x_866_, v___f_861_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object* v_inst_868_, lean_object* v_f_869_, lean_object* v_init_870_, lean_object* v_x_871_){
_start:
{
if (lean_obj_tag(v_x_871_) == 0)
{
lean_object* v_toApplicative_872_; lean_object* v_toBind_873_; lean_object* v_toPure_874_; lean_object* v_k_875_; lean_object* v_v_876_; lean_object* v_l_877_; lean_object* v_r_878_; lean_object* v___f_879_; lean_object* v___f_880_; lean_object* v___f_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_toApplicative_872_ = lean_ctor_get(v_inst_868_, 0);
v_toBind_873_ = lean_ctor_get(v_inst_868_, 1);
lean_inc_n(v_toBind_873_, 2);
v_toPure_874_ = lean_ctor_get(v_toApplicative_872_, 1);
v_k_875_ = lean_ctor_get(v_x_871_, 1);
lean_inc(v_k_875_);
v_v_876_ = lean_ctor_get(v_x_871_, 2);
lean_inc(v_v_876_);
v_l_877_ = lean_ctor_get(v_x_871_, 3);
lean_inc(v_l_877_);
v_r_878_ = lean_ctor_get(v_x_871_, 4);
lean_inc(v_r_878_);
lean_dec_ref_known(v_x_871_, 5);
lean_inc(v_toPure_874_);
v___f_879_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__0), 2, 1);
lean_closure_set(v___f_879_, 0, v_toPure_874_);
lean_inc_n(v_f_869_, 2);
lean_inc_ref(v_inst_868_);
lean_inc_ref(v___f_879_);
v___f_880_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1), 5, 4);
lean_closure_set(v___f_880_, 0, v___f_879_);
lean_closure_set(v___f_880_, 1, v_inst_868_);
lean_closure_set(v___f_880_, 2, v_f_869_);
lean_closure_set(v___f_880_, 3, v_r_878_);
v___f_881_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__2), 7, 6);
lean_closure_set(v___f_881_, 0, v___f_879_);
lean_closure_set(v___f_881_, 1, v_f_869_);
lean_closure_set(v___f_881_, 2, v_k_875_);
lean_closure_set(v___f_881_, 3, v_v_876_);
lean_closure_set(v___f_881_, 4, v_toBind_873_);
lean_closure_set(v___f_881_, 5, v___f_880_);
v___x_882_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_868_, v_f_869_, v_init_870_, v_l_877_);
v___x_883_ = lean_apply_4(v_toBind_873_, lean_box(0), lean_box(0), v___x_882_, v___f_881_);
return v___x_883_;
}
else
{
lean_object* v_toApplicative_884_; lean_object* v_toPure_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_toApplicative_884_ = lean_ctor_get(v_inst_868_, 0);
lean_inc_ref(v_toApplicative_884_);
lean_dec(v_f_869_);
lean_dec_ref(v_inst_868_);
v_toPure_885_ = lean_ctor_get(v_toApplicative_884_, 1);
lean_inc(v_toPure_885_);
lean_dec_ref(v_toApplicative_884_);
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v_init_870_);
v___x_887_ = lean_apply_2(v_toPure_885_, lean_box(0), v___x_886_);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg___lam__1(lean_object* v___f_888_, lean_object* v_inst_889_, lean_object* v_f_890_, lean_object* v_r_891_, lean_object* v_____do__lift_892_){
_start:
{
if (lean_obj_tag(v_____do__lift_892_) == 0)
{
lean_object* v_a_893_; lean_object* v___x_894_; 
lean_dec(v_r_891_);
lean_dec(v_f_890_);
lean_dec_ref(v_inst_889_);
v_a_893_ = lean_ctor_get(v_____do__lift_892_, 0);
lean_inc(v_a_893_);
lean_dec_ref_known(v_____do__lift_892_, 1);
v___x_894_ = lean_apply_1(v___f_888_, v_a_893_);
return v___x_894_;
}
else
{
lean_object* v_a_895_; lean_object* v___x_896_; 
lean_dec(v___f_888_);
v_a_895_ = lean_ctor_get(v_____do__lift_892_, 0);
lean_inc(v_a_895_);
lean_dec_ref_known(v_____do__lift_892_, 1);
v___x_896_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_889_, v_f_890_, v_a_895_, v_r_891_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep(lean_object* v_00_u03b1_897_, lean_object* v_00_u03b2_898_, lean_object* v_00_u03b4_899_, lean_object* v_m_900_, lean_object* v_inst_901_, lean_object* v_f_902_, lean_object* v_init_903_, lean_object* v_x_904_){
_start:
{
lean_object* v___x_905_; 
v___x_905_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_901_, v_f_902_, v_init_903_, v_x_904_);
return v___x_905_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0(lean_object* v_toPure_906_, lean_object* v_____do__lift_907_){
_start:
{
lean_object* v_a_908_; lean_object* v___x_909_; 
v_a_908_ = lean_ctor_get(v_____do__lift_907_, 0);
lean_inc(v_a_908_);
lean_dec_ref(v_____do__lift_907_);
v___x_909_ = lean_apply_2(v_toPure_906_, lean_box(0), v_a_908_);
return v___x_909_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn___redArg(lean_object* v_inst_910_, lean_object* v_f_911_, lean_object* v_init_912_, lean_object* v_t_913_){
_start:
{
lean_object* v_toApplicative_914_; lean_object* v_toBind_915_; lean_object* v_toPure_916_; lean_object* v___x_917_; lean_object* v___f_918_; lean_object* v___x_919_; 
v_toApplicative_914_ = lean_ctor_get(v_inst_910_, 0);
v_toBind_915_ = lean_ctor_get(v_inst_910_, 1);
lean_inc(v_toBind_915_);
v_toPure_916_ = lean_ctor_get(v_toApplicative_914_, 1);
lean_inc(v_toPure_916_);
v___x_917_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_910_, v_f_911_, v_init_912_, v_t_913_);
v___f_918_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_918_, 0, v_toPure_916_);
v___x_919_ = lean_apply_4(v_toBind_915_, lean_box(0), lean_box(0), v___x_917_, v___f_918_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forIn(lean_object* v_00_u03b1_920_, lean_object* v_00_u03b2_921_, lean_object* v_00_u03b4_922_, lean_object* v_m_923_, lean_object* v_inst_924_, lean_object* v_f_925_, lean_object* v_init_926_, lean_object* v_t_927_){
_start:
{
lean_object* v_toApplicative_928_; lean_object* v_toBind_929_; lean_object* v_toPure_930_; lean_object* v___x_931_; lean_object* v___f_932_; lean_object* v___x_933_; 
v_toApplicative_928_ = lean_ctor_get(v_inst_924_, 0);
v_toBind_929_ = lean_ctor_get(v_inst_924_, 1);
lean_inc(v_toBind_929_);
v_toPure_930_ = lean_ctor_get(v_toApplicative_928_, 1);
lean_inc(v_toPure_930_);
v___x_931_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_924_, v_f_925_, v_init_926_, v_t_927_);
v___f_932_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_932_, 0, v_toPure_930_);
v___x_933_ = lean_apply_4(v_toBind_929_, lean_box(0), lean_box(0), v___x_931_, v___f_932_);
return v___x_933_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0(lean_object* v_f_934_, lean_object* v_a_935_, lean_object* v_b_936_, lean_object* v_acc_937_){
_start:
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v_a_935_);
lean_ctor_set(v___x_938_, 1, v_b_936_);
v___x_939_ = lean_apply_2(v_f_934_, v___x_938_, v_acc_937_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2(lean_object* v_inst_940_, lean_object* v_00_u03b2_941_, lean_object* v_m_942_, lean_object* v_init_943_, lean_object* v_f_944_){
_start:
{
lean_object* v_toApplicative_945_; lean_object* v_toBind_946_; lean_object* v_toPure_947_; lean_object* v___f_948_; lean_object* v___x_949_; lean_object* v___f_950_; lean_object* v___x_951_; 
v_toApplicative_945_ = lean_ctor_get(v_inst_940_, 0);
v_toBind_946_ = lean_ctor_get(v_inst_940_, 1);
lean_inc(v_toBind_946_);
v_toPure_947_ = lean_ctor_get(v_toApplicative_945_, 1);
lean_inc(v_toPure_947_);
v___f_948_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__0), 4, 1);
lean_closure_set(v___f_948_, 0, v_f_944_);
v___x_949_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v_inst_940_, v___f_948_, v_init_943_, v_m_942_);
v___f_950_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_forIn___redArg___lam__0), 2, 1);
lean_closure_set(v___f_950_, 0, v_toPure_947_);
v___x_951_ = lean_apply_4(v_toBind_946_, lean_box(0), lean_box(0), v___x_949_, v___f_950_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg(lean_object* v_inst_952_){
_start:
{
lean_object* v___f_953_; 
v___f_953_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_953_, 0, v_inst_952_);
return v___f_953_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad(lean_object* v_00_u03b1_954_, lean_object* v_00_u03b2_955_, lean_object* v_m_956_, lean_object* v_inst_957_){
_start:
{
lean_object* v___f_958_; 
v___f_958_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_instForInSigmaOfMonad___redArg___lam__2), 5, 1);
lean_closure_set(v___f_958_, 0, v_inst_957_);
return v___f_958_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(lean_object* v_p_959_, lean_object* v___x_960_, lean_object* v___x_961_, lean_object* v_a_962_, lean_object* v_b_963_, lean_object* v_acc_964_){
_start:
{
lean_object* v___x_965_; uint8_t v___x_966_; 
v___x_965_ = lean_apply_2(v_p_959_, v_a_962_, v_b_963_);
v___x_966_ = lean_unbox(v___x_965_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; 
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_960_);
return v___x_967_;
}
else
{
lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec_ref(v___x_960_);
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_965_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_961_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed(lean_object* v_p_971_, lean_object* v___x_972_, lean_object* v___x_973_, lean_object* v_a_974_, lean_object* v_b_975_, lean_object* v_acc_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0(v_p_971_, v___x_972_, v___x_973_, v_a_974_, v_b_975_, v_acc_976_);
lean_dec_ref(v_acc_976_);
return v_res_977_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_any___redArg(lean_object* v_t_981_, lean_object* v_p_982_){
_start:
{
lean_object* v___y_984_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___f_992_; lean_object* v___x_993_; lean_object* v_a_994_; 
v___x_989_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_990_ = lean_box(0);
v___x_991_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_992_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_992_, 0, v_p_982_);
lean_closure_set(v___f_992_, 1, v___x_991_);
lean_closure_set(v___f_992_, 2, v___x_990_);
v___x_993_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_989_, v___f_992_, v___x_991_, v_t_981_);
v_a_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_a_994_);
lean_dec(v___x_993_);
v___y_984_ = v_a_994_;
goto v___jp_983_;
v___jp_983_:
{
lean_object* v_fst_985_; 
v_fst_985_ = lean_ctor_get(v___y_984_, 0);
lean_inc(v_fst_985_);
lean_dec_ref(v___y_984_);
if (lean_obj_tag(v_fst_985_) == 0)
{
uint8_t v___x_986_; 
v___x_986_ = 0;
return v___x_986_;
}
else
{
lean_object* v_val_987_; uint8_t v___x_988_; 
v_val_987_ = lean_ctor_get(v_fst_985_, 0);
lean_inc(v_val_987_);
lean_dec_ref_known(v_fst_985_, 1);
v___x_988_ = lean_unbox(v_val_987_);
lean_dec(v_val_987_);
return v___x_988_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_981_ = stack[0].m_obj;
lean_object* v_p_982_ = stack[1].m_obj;
uint8_t v_res_995_;
v_res_995_ = l_Std_DTreeMap_Internal_Impl_any___redArg(v_t_981_, v_p_982_);
stack->m_num = v_res_995_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___redArg___boxed(lean_object* v_t_996_, lean_object* v_p_997_){
_start:
{
uint8_t v_res_998_; lean_object* v_r_999_; 
v_res_998_ = l_Std_DTreeMap_Internal_Impl_any___redArg(v_t_996_, v_p_997_);
v_r_999_ = lean_box(v_res_998_);
return v_r_999_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_any(lean_object* v_00_u03b1_1000_, lean_object* v_00_u03b2_1001_, lean_object* v_t_1002_, lean_object* v_p_1003_){
_start:
{
lean_object* v___y_1005_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___f_1013_; lean_object* v___x_1014_; lean_object* v_a_1015_; 
v___x_1010_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1011_ = lean_box(0);
v___x_1012_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1013_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_any___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1013_, 0, v_p_1003_);
lean_closure_set(v___f_1013_, 1, v___x_1012_);
lean_closure_set(v___f_1013_, 2, v___x_1011_);
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
v___x_1007_ = 0;
return v___x_1007_;
}
else
{
lean_object* v_val_1008_; uint8_t v___x_1009_; 
v_val_1008_ = lean_ctor_get(v_fst_1006_, 0);
lean_inc(v_val_1008_);
lean_dec_ref_known(v_fst_1006_, 1);
v___x_1009_ = lean_unbox(v_val_1008_);
lean_dec(v_val_1008_);
return v___x_1009_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1002_ = stack[2].m_obj;
lean_object* v_p_1003_ = stack[3].m_obj;
uint8_t v_res_1016_;
v_res_1016_ = l_Std_DTreeMap_Internal_Impl_any(lean_box(0), lean_box(0), v_t_1002_, v_p_1003_);
stack->m_num = v_res_1016_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_any___boxed(lean_object* v_00_u03b1_1017_, lean_object* v_00_u03b2_1018_, lean_object* v_t_1019_, lean_object* v_p_1020_){
_start:
{
uint8_t v_res_1021_; lean_object* v_r_1022_; 
v_res_1021_ = l_Std_DTreeMap_Internal_Impl_any(v_00_u03b1_1017_, v_00_u03b2_1018_, v_t_1019_, v_p_1020_);
v_r_1022_ = lean_box(v_res_1021_);
return v_r_1022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(lean_object* v_p_1023_, lean_object* v___x_1024_, lean_object* v___x_1025_, lean_object* v_a_1026_, lean_object* v_b_1027_, lean_object* v_acc_1028_){
_start:
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
v___x_1029_ = lean_apply_2(v_p_1023_, v_a_1026_, v_b_1027_);
v___x_1030_ = lean_unbox(v___x_1029_);
if (v___x_1030_ == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_dec_ref(v___x_1025_);
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1029_);
v___x_1032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
lean_ctor_set(v___x_1032_, 1, v___x_1024_);
v___x_1033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
else
{
lean_object* v___x_1034_; 
v___x_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1034_, 0, v___x_1025_);
return v___x_1034_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed(lean_object* v_p_1035_, lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v_a_1038_, lean_object* v_b_1039_, lean_object* v_acc_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0(v_p_1035_, v___x_1036_, v___x_1037_, v_a_1038_, v_b_1039_, v_acc_1040_);
lean_dec_ref(v_acc_1040_);
return v_res_1041_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_all___redArg(lean_object* v_t_1042_, lean_object* v_p_1043_){
_start:
{
lean_object* v___y_1045_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___f_1053_; lean_object* v___x_1054_; lean_object* v_a_1055_; 
v___x_1050_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1051_ = lean_box(0);
v___x_1052_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1053_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1053_, 0, v_p_1043_);
lean_closure_set(v___f_1053_, 1, v___x_1051_);
lean_closure_set(v___f_1053_, 2, v___x_1052_);
v___x_1054_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1050_, v___f_1053_, v___x_1052_, v_t_1042_);
v_a_1055_ = lean_ctor_get(v___x_1054_, 0);
lean_inc(v_a_1055_);
lean_dec(v___x_1054_);
v___y_1045_ = v_a_1055_;
goto v___jp_1044_;
v___jp_1044_:
{
lean_object* v_fst_1046_; 
v_fst_1046_ = lean_ctor_get(v___y_1045_, 0);
lean_inc(v_fst_1046_);
lean_dec_ref(v___y_1045_);
if (lean_obj_tag(v_fst_1046_) == 0)
{
uint8_t v___x_1047_; 
v___x_1047_ = 1;
return v___x_1047_;
}
else
{
lean_object* v_val_1048_; uint8_t v___x_1049_; 
v_val_1048_ = lean_ctor_get(v_fst_1046_, 0);
lean_inc(v_val_1048_);
lean_dec_ref_known(v_fst_1046_, 1);
v___x_1049_ = lean_unbox(v_val_1048_);
lean_dec(v_val_1048_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1042_ = stack[0].m_obj;
lean_object* v_p_1043_ = stack[1].m_obj;
uint8_t v_res_1056_;
v_res_1056_ = l_Std_DTreeMap_Internal_Impl_all___redArg(v_t_1042_, v_p_1043_);
stack->m_num = v_res_1056_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___redArg___boxed(lean_object* v_t_1057_, lean_object* v_p_1058_){
_start:
{
uint8_t v_res_1059_; lean_object* v_r_1060_; 
v_res_1059_ = l_Std_DTreeMap_Internal_Impl_all___redArg(v_t_1057_, v_p_1058_);
v_r_1060_ = lean_box(v_res_1059_);
return v_r_1060_;
}
}
uint8_t l_Std_DTreeMap_Internal_Impl_all(lean_object* v_00_u03b1_1061_, lean_object* v_00_u03b2_1062_, lean_object* v_t_1063_, lean_object* v_p_1064_){
_start:
{
lean_object* v___y_1066_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; lean_object* v_a_1076_; 
v___x_1071_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1072_ = lean_box(0);
v___x_1073_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_any___redArg___closed__0));
v___f_1074_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_all___redArg___lam__0___boxed), 6, 3);
lean_closure_set(v___f_1074_, 0, v_p_1064_);
lean_closure_set(v___f_1074_, 1, v___x_1072_);
lean_closure_set(v___f_1074_, 2, v___x_1073_);
v___x_1075_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_1071_, v___f_1074_, v___x_1073_, v_t_1063_);
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec(v___x_1075_);
v___y_1066_ = v_a_1076_;
goto v___jp_1065_;
v___jp_1065_:
{
lean_object* v_fst_1067_; 
v_fst_1067_ = lean_ctor_get(v___y_1066_, 0);
lean_inc(v_fst_1067_);
lean_dec_ref(v___y_1066_);
if (lean_obj_tag(v_fst_1067_) == 0)
{
uint8_t v___x_1068_; 
v___x_1068_ = 1;
return v___x_1068_;
}
else
{
lean_object* v_val_1069_; uint8_t v___x_1070_; 
v_val_1069_ = lean_ctor_get(v_fst_1067_, 0);
lean_inc(v_val_1069_);
lean_dec_ref_known(v_fst_1067_, 1);
v___x_1070_ = lean_unbox(v_val_1069_);
lean_dec(v_val_1069_);
return v___x_1070_;
}
}
}
}
LEAN_EXPORT void l_Std_DTreeMap_Internal_Impl_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_1063_ = stack[2].m_obj;
lean_object* v_p_1064_ = stack[3].m_obj;
uint8_t v_res_1077_;
v_res_1077_ = l_Std_DTreeMap_Internal_Impl_all(lean_box(0), lean_box(0), v_t_1063_, v_p_1064_);
stack->m_num = v_res_1077_;
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_all___boxed(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_t_1080_, lean_object* v_p_1081_){
_start:
{
uint8_t v_res_1082_; lean_object* v_r_1083_; 
v_res_1082_ = l_Std_DTreeMap_Internal_Impl_all(v_00_u03b1_1078_, v_00_u03b2_1079_, v_t_1080_, v_p_1081_);
v_r_1083_ = lean_box(v_res_1082_);
return v_r_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(lean_object* v_x1_1084_, lean_object* v_x2_1085_, lean_object* v_x3_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1087_, 0, v_x1_1084_);
lean_ctor_set(v___x_1087_, 1, v_x3_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0___boxed(lean_object* v_x1_1088_, lean_object* v_x2_1089_, lean_object* v_x3_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_DTreeMap_Internal_Impl_keys___redArg___lam__0(v_x1_1088_, v_x2_1089_, v_x3_1090_);
lean_dec(v_x2_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys___redArg(lean_object* v_t_1093_){
_start:
{
lean_object* v___f_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___f_1094_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1095_ = lean_box(0);
v___x_1096_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1097_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1096_, v___f_1094_, v___x_1095_, v_t_1093_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keys(lean_object* v_00_u03b1_1098_, lean_object* v_00_u03b2_1099_, lean_object* v_t_1100_){
_start:
{
lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___f_1101_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keys___redArg___closed__0));
v___x_1102_ = lean_box(0);
v___x_1103_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1104_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1103_, v___f_1101_, v___x_1102_, v_t_1100_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(lean_object* v_l_1105_, lean_object* v_k_1106_, lean_object* v_x_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = lean_array_push(v_l_1105_, v_k_1106_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0___boxed(lean_object* v_l_1109_, lean_object* v_k_1110_, lean_object* v_x_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Std_DTreeMap_Internal_Impl_keysArray___redArg___lam__0(v_l_1109_, v_k_1110_, v_x_1111_);
lean_dec(v_x_1111_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray___redArg(lean_object* v_t_1114_){
_start:
{
lean_object* v___f_1115_; lean_object* v___y_1117_; 
v___f_1115_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1114_) == 0)
{
lean_object* v_size_1120_; 
v_size_1120_ = lean_ctor_get(v_t_1114_, 0);
lean_inc(v_size_1120_);
v___y_1117_ = v_size_1120_;
goto v___jp_1116_;
}
else
{
lean_object* v___x_1121_; 
v___x_1121_ = lean_unsigned_to_nat(0u);
v___y_1117_ = v___x_1121_;
goto v___jp_1116_;
}
v___jp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = lean_mk_empty_array_with_capacity(v___y_1117_);
lean_dec(v___y_1117_);
v___x_1119_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1115_, v___x_1118_, v_t_1114_);
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keysArray(lean_object* v_00_u03b1_1122_, lean_object* v_00_u03b2_1123_, lean_object* v_t_1124_){
_start:
{
lean_object* v___f_1125_; lean_object* v___y_1127_; 
v___f_1125_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keysArray___redArg___closed__0));
if (lean_obj_tag(v_t_1124_) == 0)
{
lean_object* v_size_1130_; 
v_size_1130_ = lean_ctor_get(v_t_1124_, 0);
lean_inc(v_size_1130_);
v___y_1127_ = v_size_1130_;
goto v___jp_1126_;
}
else
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_unsigned_to_nat(0u);
v___y_1127_ = v___x_1131_;
goto v___jp_1126_;
}
v___jp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_mk_empty_array_with_capacity(v___y_1127_);
lean_dec(v___y_1127_);
v___x_1129_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1125_, v___x_1128_, v_t_1124_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(lean_object* v_x1_1132_, lean_object* v_x2_1133_, lean_object* v_x3_1134_){
_start:
{
lean_object* v___x_1135_; 
v___x_1135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_x2_1133_);
lean_ctor_set(v___x_1135_, 1, v_x3_1134_);
return v___x_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0___boxed(lean_object* v_x1_1136_, lean_object* v_x2_1137_, lean_object* v_x3_1138_){
_start:
{
lean_object* v_res_1139_; 
v_res_1139_ = l_Std_DTreeMap_Internal_Impl_values___redArg___lam__0(v_x1_1136_, v_x2_1137_, v_x3_1138_);
lean_dec(v_x1_1136_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values___redArg(lean_object* v_t_1141_){
_start:
{
lean_object* v___f_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___f_1142_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1143_ = lean_box(0);
v___x_1144_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1145_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1144_, v___f_1142_, v___x_1143_, v_t_1141_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_values(lean_object* v_00_u03b1_1146_, lean_object* v_00_u03b2_1147_, lean_object* v_t_1148_){
_start:
{
lean_object* v___f_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___f_1149_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_values___redArg___closed__0));
v___x_1150_ = lean_box(0);
v___x_1151_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1152_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1151_, v___f_1149_, v___x_1150_, v_t_1148_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(lean_object* v_l_1153_, lean_object* v_x_1154_, lean_object* v_v_1155_){
_start:
{
lean_object* v___x_1156_; 
v___x_1156_ = lean_array_push(v_l_1153_, v_v_1155_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0___boxed(lean_object* v_l_1157_, lean_object* v_x_1158_, lean_object* v_v_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___lam__0(v_l_1157_, v_x_1158_, v_v_1159_);
lean_dec(v_x_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray___redArg(lean_object* v_t_1162_){
_start:
{
lean_object* v___f_1163_; lean_object* v___y_1165_; 
v___f_1163_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1162_) == 0)
{
lean_object* v_size_1168_; 
v_size_1168_ = lean_ctor_get(v_t_1162_, 0);
lean_inc(v_size_1168_);
v___y_1165_ = v_size_1168_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1169_; 
v___x_1169_ = lean_unsigned_to_nat(0u);
v___y_1165_ = v___x_1169_;
goto v___jp_1164_;
}
v___jp_1164_:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = lean_mk_empty_array_with_capacity(v___y_1165_);
lean_dec(v___y_1165_);
v___x_1167_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1163_, v___x_1166_, v_t_1162_);
return v___x_1167_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_valuesArray(lean_object* v_00_u03b1_1170_, lean_object* v_00_u03b2_1171_, lean_object* v_t_1172_){
_start:
{
lean_object* v___f_1173_; lean_object* v___y_1175_; 
v___f_1173_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_valuesArray___redArg___closed__0));
if (lean_obj_tag(v_t_1172_) == 0)
{
lean_object* v_size_1178_; 
v_size_1178_ = lean_ctor_get(v_t_1172_, 0);
lean_inc(v_size_1178_);
v___y_1175_ = v_size_1178_;
goto v___jp_1174_;
}
else
{
lean_object* v___x_1179_; 
v___x_1179_ = lean_unsigned_to_nat(0u);
v___y_1175_ = v___x_1179_;
goto v___jp_1174_;
}
v___jp_1174_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
v___x_1176_ = lean_mk_empty_array_with_capacity(v___y_1175_);
lean_dec(v___y_1175_);
v___x_1177_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1173_, v___x_1176_, v_t_1172_);
return v___x_1177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg___lam__0(lean_object* v_x1_1180_, lean_object* v_x2_1181_, lean_object* v_x3_1182_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1183_, 0, v_x1_1180_);
lean_ctor_set(v___x_1183_, 1, v_x2_1181_);
v___x_1184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v_x3_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList___redArg(lean_object* v_t_1186_){
_start:
{
lean_object* v___f_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___f_1187_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1188_ = lean_box(0);
v___x_1189_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1190_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1189_, v___f_1187_, v___x_1188_, v_t_1186_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toList(lean_object* v_00_u03b1_1191_, lean_object* v_00_u03b2_1192_, lean_object* v_t_1193_){
_start:
{
lean_object* v___f_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___f_1194_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toList___redArg___closed__0));
v___x_1195_ = lean_box(0);
v___x_1196_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1197_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1196_, v___f_1194_, v___x_1195_, v_t_1193_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg___lam__0(lean_object* v_l_1198_, lean_object* v_k_1199_, lean_object* v_v_1200_){
_start:
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v_k_1199_);
lean_ctor_set(v___x_1201_, 1, v_v_1200_);
v___x_1202_ = lean_array_push(v_l_1198_, v___x_1201_);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray___redArg(lean_object* v_t_1204_){
_start:
{
lean_object* v___f_1205_; lean_object* v___y_1207_; 
v___f_1205_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1204_) == 0)
{
lean_object* v_size_1210_; 
v_size_1210_ = lean_ctor_get(v_t_1204_, 0);
lean_inc(v_size_1210_);
v___y_1207_ = v_size_1210_;
goto v___jp_1206_;
}
else
{
lean_object* v___x_1211_; 
v___x_1211_ = lean_unsigned_to_nat(0u);
v___y_1207_ = v___x_1211_;
goto v___jp_1206_;
}
v___jp_1206_:
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
v___x_1208_ = lean_mk_empty_array_with_capacity(v___y_1207_);
lean_dec(v___y_1207_);
v___x_1209_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1205_, v___x_1208_, v_t_1204_);
return v___x_1209_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_toArray(lean_object* v_00_u03b1_1212_, lean_object* v_00_u03b2_1213_, lean_object* v_t_1214_){
_start:
{
lean_object* v___f_1215_; lean_object* v___y_1217_; 
v___f_1215_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1214_) == 0)
{
lean_object* v_size_1220_; 
v_size_1220_ = lean_ctor_get(v_t_1214_, 0);
lean_inc(v_size_1220_);
v___y_1217_ = v_size_1220_;
goto v___jp_1216_;
}
else
{
lean_object* v___x_1221_; 
v___x_1221_ = lean_unsigned_to_nat(0u);
v___y_1217_ = v___x_1221_;
goto v___jp_1216_;
}
v___jp_1216_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1218_ = lean_mk_empty_array_with_capacity(v___y_1217_);
lean_dec(v___y_1217_);
v___x_1219_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1215_, v___x_1218_, v_t_1214_);
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___lam__0(lean_object* v_x1_1222_, lean_object* v_x2_1223_, lean_object* v_x3_1224_){
_start:
{
lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v_x1_1222_);
lean_ctor_set(v___x_1225_, 1, v_x2_1223_);
v___x_1226_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1226_, 0, v___x_1225_);
lean_ctor_set(v___x_1226_, 1, v_x3_1224_);
return v___x_1226_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList___redArg(lean_object* v_t_1228_){
_start:
{
lean_object* v___f_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___f_1229_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1230_ = lean_box(0);
v___x_1231_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1232_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1231_, v___f_1229_, v___x_1230_, v_t_1228_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toList(lean_object* v_00_u03b1_1233_, lean_object* v_00_u03b2_1234_, lean_object* v_t_1235_){
_start:
{
lean_object* v___f_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v___f_1236_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toList___redArg___closed__0));
v___x_1237_ = lean_box(0);
v___x_1238_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldl___redArg___closed__9));
v___x_1239_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_1238_, v___f_1236_, v___x_1237_, v_t_1235_);
return v___x_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___lam__0(lean_object* v_l_1240_, lean_object* v_k_1241_, lean_object* v_v_1242_){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v_k_1241_);
lean_ctor_set(v___x_1243_, 1, v_v_1242_);
v___x_1244_ = lean_array_push(v_l_1240_, v___x_1243_);
return v___x_1244_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg(lean_object* v_t_1246_){
_start:
{
lean_object* v___f_1247_; lean_object* v___y_1249_; 
v___f_1247_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1246_) == 0)
{
lean_object* v_size_1252_; 
v_size_1252_ = lean_ctor_get(v_t_1246_, 0);
lean_inc(v_size_1252_);
v___y_1249_ = v_size_1252_;
goto v___jp_1248_;
}
else
{
lean_object* v___x_1253_; 
v___x_1253_ = lean_unsigned_to_nat(0u);
v___y_1249_ = v___x_1253_;
goto v___jp_1248_;
}
v___jp_1248_:
{
lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1250_ = lean_mk_empty_array_with_capacity(v___y_1249_);
lean_dec(v___y_1249_);
v___x_1251_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1247_, v___x_1250_, v_t_1246_);
return v___x_1251_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_toArray(lean_object* v_00_u03b1_1254_, lean_object* v_00_u03b2_1255_, lean_object* v_t_1256_){
_start:
{
lean_object* v___f_1257_; lean_object* v___y_1259_; 
v___f_1257_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_toArray___redArg___closed__0));
if (lean_obj_tag(v_t_1256_) == 0)
{
lean_object* v_size_1262_; 
v_size_1262_ = lean_ctor_get(v_t_1256_, 0);
lean_inc(v_size_1262_);
v___y_1259_ = v_size_1262_;
goto v___jp_1258_;
}
else
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_unsigned_to_nat(0u);
v___y_1259_ = v___x_1263_;
goto v___jp_1258_;
}
v___jp_1258_:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_mk_empty_array_with_capacity(v___y_1259_);
lean_dec(v___y_1259_);
v___x_1261_ = l_Std_DTreeMap_Internal_Impl_foldl___redArg(v___f_1257_, v___x_1260_, v_t_1256_);
return v___x_1261_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(lean_object* v_x_1264_){
_start:
{
if (lean_obj_tag(v_x_1264_) == 0)
{
lean_object* v_l_1265_; 
v_l_1265_ = lean_ctor_get(v_x_1264_, 3);
if (lean_obj_tag(v_l_1265_) == 0)
{
v_x_1264_ = v_l_1265_;
goto _start;
}
else
{
lean_object* v_k_1267_; lean_object* v_v_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; 
v_k_1267_ = lean_ctor_get(v_x_1264_, 1);
v_v_1268_ = lean_ctor_get(v_x_1264_, 2);
lean_inc(v_v_1268_);
lean_inc(v_k_1267_);
v___x_1269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1269_, 0, v_k_1267_);
lean_ctor_set(v___x_1269_, 1, v_v_1268_);
v___x_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1270_, 0, v___x_1269_);
return v___x_1270_;
}
}
else
{
lean_object* v___x_1271_; 
v___x_1271_ = lean_box(0);
return v___x_1271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg___boxed(lean_object* v_x_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1272_);
lean_dec(v_x_1272_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f(lean_object* v_00_u03b1_1274_, lean_object* v_00_u03b2_1275_, lean_object* v_x_1276_){
_start:
{
lean_object* v___x_1277_; 
v___x_1277_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f___redArg(v_x_1276_);
return v___x_1277_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x3f___boxed(lean_object* v_00_u03b1_1278_, lean_object* v_00_u03b2_1279_, lean_object* v_x_1280_){
_start:
{
lean_object* v_res_1281_; 
v_res_1281_ = l_Std_DTreeMap_Internal_Impl_minEntry_x3f(v_00_u03b1_1278_, v_00_u03b2_1279_, v_x_1280_);
lean_dec(v_x_1280_);
return v_res_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1282_, lean_object* v_h__1_1283_, lean_object* v_h__2_1284_, lean_object* v_h__3_1285_){
_start:
{
if (lean_obj_tag(v_x_1282_) == 0)
{
lean_object* v_l_1286_; 
lean_dec(v_h__1_1283_);
v_l_1286_ = lean_ctor_get(v_x_1282_, 3);
if (lean_obj_tag(v_l_1286_) == 0)
{
lean_object* v_size_1287_; lean_object* v_k_1288_; lean_object* v_v_1289_; lean_object* v_r_1290_; lean_object* v_size_1291_; lean_object* v_k_1292_; lean_object* v_v_1293_; lean_object* v_l_1294_; lean_object* v_r_1295_; lean_object* v___x_1296_; 
lean_inc_ref(v_l_1286_);
lean_dec(v_h__2_1284_);
v_size_1287_ = lean_ctor_get(v_x_1282_, 0);
lean_inc(v_size_1287_);
v_k_1288_ = lean_ctor_get(v_x_1282_, 1);
lean_inc(v_k_1288_);
v_v_1289_ = lean_ctor_get(v_x_1282_, 2);
lean_inc(v_v_1289_);
v_r_1290_ = lean_ctor_get(v_x_1282_, 4);
lean_inc(v_r_1290_);
lean_dec_ref_known(v_x_1282_, 5);
v_size_1291_ = lean_ctor_get(v_l_1286_, 0);
lean_inc(v_size_1291_);
v_k_1292_ = lean_ctor_get(v_l_1286_, 1);
lean_inc(v_k_1292_);
v_v_1293_ = lean_ctor_get(v_l_1286_, 2);
lean_inc(v_v_1293_);
v_l_1294_ = lean_ctor_get(v_l_1286_, 3);
lean_inc(v_l_1294_);
v_r_1295_ = lean_ctor_get(v_l_1286_, 4);
lean_inc(v_r_1295_);
lean_dec_ref_known(v_l_1286_, 5);
v___x_1296_ = lean_apply_9(v_h__3_1285_, v_size_1287_, v_k_1288_, v_v_1289_, v_size_1291_, v_k_1292_, v_v_1293_, v_l_1294_, v_r_1295_, v_r_1290_);
return v___x_1296_;
}
else
{
lean_object* v_size_1297_; lean_object* v_k_1298_; lean_object* v_v_1299_; lean_object* v_r_1300_; lean_object* v___x_1301_; 
lean_dec(v_h__3_1285_);
v_size_1297_ = lean_ctor_get(v_x_1282_, 0);
lean_inc(v_size_1297_);
v_k_1298_ = lean_ctor_get(v_x_1282_, 1);
lean_inc(v_k_1298_);
v_v_1299_ = lean_ctor_get(v_x_1282_, 2);
lean_inc(v_v_1299_);
v_r_1300_ = lean_ctor_get(v_x_1282_, 4);
lean_inc(v_r_1300_);
lean_dec_ref_known(v_x_1282_, 5);
v___x_1301_ = lean_apply_4(v_h__2_1284_, v_size_1297_, v_k_1298_, v_v_1299_, v_r_1300_);
return v___x_1301_;
}
}
else
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
lean_dec(v_h__3_1285_);
lean_dec(v_h__2_1284_);
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_apply_1(v_h__1_1283_, v___x_1302_);
return v___x_1303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1304_, lean_object* v_00_u03b2_1305_, lean_object* v_motive_1306_, lean_object* v_x_1307_, lean_object* v_h__1_1308_, lean_object* v_h__2_1309_, lean_object* v_h__3_1310_){
_start:
{
if (lean_obj_tag(v_x_1307_) == 0)
{
lean_object* v_l_1311_; 
lean_dec(v_h__1_1308_);
v_l_1311_ = lean_ctor_get(v_x_1307_, 3);
if (lean_obj_tag(v_l_1311_) == 0)
{
lean_object* v_size_1312_; lean_object* v_k_1313_; lean_object* v_v_1314_; lean_object* v_r_1315_; lean_object* v_size_1316_; lean_object* v_k_1317_; lean_object* v_v_1318_; lean_object* v_l_1319_; lean_object* v_r_1320_; lean_object* v___x_1321_; 
lean_inc_ref(v_l_1311_);
lean_dec(v_h__2_1309_);
v_size_1312_ = lean_ctor_get(v_x_1307_, 0);
lean_inc(v_size_1312_);
v_k_1313_ = lean_ctor_get(v_x_1307_, 1);
lean_inc(v_k_1313_);
v_v_1314_ = lean_ctor_get(v_x_1307_, 2);
lean_inc(v_v_1314_);
v_r_1315_ = lean_ctor_get(v_x_1307_, 4);
lean_inc(v_r_1315_);
lean_dec_ref_known(v_x_1307_, 5);
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
lean_dec_ref_known(v_l_1311_, 5);
v___x_1321_ = lean_apply_9(v_h__3_1310_, v_size_1312_, v_k_1313_, v_v_1314_, v_size_1316_, v_k_1317_, v_v_1318_, v_l_1319_, v_r_1320_, v_r_1315_);
return v___x_1321_;
}
else
{
lean_object* v_size_1322_; lean_object* v_k_1323_; lean_object* v_v_1324_; lean_object* v_r_1325_; lean_object* v___x_1326_; 
lean_dec(v_h__3_1310_);
v_size_1322_ = lean_ctor_get(v_x_1307_, 0);
lean_inc(v_size_1322_);
v_k_1323_ = lean_ctor_get(v_x_1307_, 1);
lean_inc(v_k_1323_);
v_v_1324_ = lean_ctor_get(v_x_1307_, 2);
lean_inc(v_v_1324_);
v_r_1325_ = lean_ctor_get(v_x_1307_, 4);
lean_inc(v_r_1325_);
lean_dec_ref_known(v_x_1307_, 5);
v___x_1326_ = lean_apply_4(v_h__2_1309_, v_size_1322_, v_k_1323_, v_v_1324_, v_r_1325_);
return v___x_1326_;
}
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; 
lean_dec(v_h__3_1310_);
lean_dec(v_h__2_1309_);
v___x_1327_ = lean_box(0);
v___x_1328_ = lean_apply_1(v_h__1_1308_, v___x_1327_);
return v___x_1328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg(lean_object* v_x_1329_){
_start:
{
lean_object* v_l_1330_; 
v_l_1330_ = lean_ctor_get(v_x_1329_, 3);
if (lean_obj_tag(v_l_1330_) == 0)
{
v_x_1329_ = v_l_1330_;
goto _start;
}
else
{
lean_object* v_k_1332_; lean_object* v_v_1333_; lean_object* v___x_1334_; 
v_k_1332_ = lean_ctor_get(v_x_1329_, 1);
v_v_1333_ = lean_ctor_get(v_x_1329_, 2);
lean_inc(v_v_1333_);
lean_inc(v_k_1332_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v_k_1332_);
lean_ctor_set(v___x_1334_, 1, v_v_1333_);
return v___x_1334_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___redArg___boxed(lean_object* v_x_1335_){
_start:
{
lean_object* v_res_1336_; 
v_res_1336_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1335_);
lean_dec(v_x_1335_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry(lean_object* v_00_u03b1_1337_, lean_object* v_00_u03b2_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_){
_start:
{
lean_object* v___x_1341_; 
v___x_1341_ = l_Std_DTreeMap_Internal_Impl_minEntry___redArg(v_x_1339_);
return v___x_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry___boxed(lean_object* v_00_u03b1_1342_, lean_object* v_00_u03b2_1343_, lean_object* v_x_1344_, lean_object* v_x_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_DTreeMap_Internal_Impl_minEntry(v_00_u03b1_1342_, v_00_u03b2_1343_, v_x_1344_, v_x_1345_);
lean_dec(v_x_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter___redArg(lean_object* v_x_1347_, lean_object* v_h__1_1348_, lean_object* v_h__2_1349_){
_start:
{
lean_object* v_l_1350_; 
v_l_1350_ = lean_ctor_get(v_x_1347_, 3);
if (lean_obj_tag(v_l_1350_) == 0)
{
lean_object* v_size_1351_; lean_object* v_k_1352_; lean_object* v_v_1353_; lean_object* v_r_1354_; lean_object* v_size_1355_; lean_object* v_k_1356_; lean_object* v_v_1357_; lean_object* v_l_1358_; lean_object* v_r_1359_; lean_object* v___x_1360_; 
lean_inc_ref(v_l_1350_);
lean_dec(v_h__1_1348_);
v_size_1351_ = lean_ctor_get(v_x_1347_, 0);
lean_inc(v_size_1351_);
v_k_1352_ = lean_ctor_get(v_x_1347_, 1);
lean_inc(v_k_1352_);
v_v_1353_ = lean_ctor_get(v_x_1347_, 2);
lean_inc(v_v_1353_);
v_r_1354_ = lean_ctor_get(v_x_1347_, 4);
lean_inc(v_r_1354_);
lean_dec(v_x_1347_);
v_size_1355_ = lean_ctor_get(v_l_1350_, 0);
lean_inc(v_size_1355_);
v_k_1356_ = lean_ctor_get(v_l_1350_, 1);
lean_inc(v_k_1356_);
v_v_1357_ = lean_ctor_get(v_l_1350_, 2);
lean_inc(v_v_1357_);
v_l_1358_ = lean_ctor_get(v_l_1350_, 3);
lean_inc(v_l_1358_);
v_r_1359_ = lean_ctor_get(v_l_1350_, 4);
lean_inc(v_r_1359_);
lean_dec_ref_known(v_l_1350_, 5);
v___x_1360_ = lean_apply_10(v_h__2_1349_, v_size_1351_, v_k_1352_, v_v_1353_, v_size_1355_, v_k_1356_, v_v_1357_, v_l_1358_, v_r_1359_, v_r_1354_, lean_box(0));
return v___x_1360_;
}
else
{
lean_object* v_size_1361_; lean_object* v_k_1362_; lean_object* v_v_1363_; lean_object* v_r_1364_; lean_object* v___x_1365_; 
lean_dec(v_h__2_1349_);
v_size_1361_ = lean_ctor_get(v_x_1347_, 0);
lean_inc(v_size_1361_);
v_k_1362_ = lean_ctor_get(v_x_1347_, 1);
lean_inc(v_k_1362_);
v_v_1363_ = lean_ctor_get(v_x_1347_, 2);
lean_inc(v_v_1363_);
v_r_1364_ = lean_ctor_get(v_x_1347_, 4);
lean_inc(v_r_1364_);
lean_dec(v_x_1347_);
v___x_1365_ = lean_apply_5(v_h__1_1348_, v_size_1361_, v_k_1362_, v_v_1363_, v_r_1364_, lean_box(0));
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntry_match__1_splitter(lean_object* v_00_u03b1_1366_, lean_object* v_00_u03b2_1367_, lean_object* v_motive_1368_, lean_object* v_x_1369_, lean_object* v_x_1370_, lean_object* v_h__1_1371_, lean_object* v_h__2_1372_){
_start:
{
lean_object* v_l_1373_; 
v_l_1373_ = lean_ctor_get(v_x_1369_, 3);
if (lean_obj_tag(v_l_1373_) == 0)
{
lean_object* v_size_1374_; lean_object* v_k_1375_; lean_object* v_v_1376_; lean_object* v_r_1377_; lean_object* v_size_1378_; lean_object* v_k_1379_; lean_object* v_v_1380_; lean_object* v_l_1381_; lean_object* v_r_1382_; lean_object* v___x_1383_; 
lean_inc_ref(v_l_1373_);
lean_dec(v_h__1_1371_);
v_size_1374_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_size_1374_);
v_k_1375_ = lean_ctor_get(v_x_1369_, 1);
lean_inc(v_k_1375_);
v_v_1376_ = lean_ctor_get(v_x_1369_, 2);
lean_inc(v_v_1376_);
v_r_1377_ = lean_ctor_get(v_x_1369_, 4);
lean_inc(v_r_1377_);
lean_dec(v_x_1369_);
v_size_1378_ = lean_ctor_get(v_l_1373_, 0);
lean_inc(v_size_1378_);
v_k_1379_ = lean_ctor_get(v_l_1373_, 1);
lean_inc(v_k_1379_);
v_v_1380_ = lean_ctor_get(v_l_1373_, 2);
lean_inc(v_v_1380_);
v_l_1381_ = lean_ctor_get(v_l_1373_, 3);
lean_inc(v_l_1381_);
v_r_1382_ = lean_ctor_get(v_l_1373_, 4);
lean_inc(v_r_1382_);
lean_dec_ref_known(v_l_1373_, 5);
v___x_1383_ = lean_apply_10(v_h__2_1372_, v_size_1374_, v_k_1375_, v_v_1376_, v_size_1378_, v_k_1379_, v_v_1380_, v_l_1381_, v_r_1382_, v_r_1377_, lean_box(0));
return v___x_1383_;
}
else
{
lean_object* v_size_1384_; lean_object* v_k_1385_; lean_object* v_v_1386_; lean_object* v_r_1387_; lean_object* v___x_1388_; 
lean_dec(v_h__2_1372_);
v_size_1384_ = lean_ctor_get(v_x_1369_, 0);
lean_inc(v_size_1384_);
v_k_1385_ = lean_ctor_get(v_x_1369_, 1);
lean_inc(v_k_1385_);
v_v_1386_ = lean_ctor_get(v_x_1369_, 2);
lean_inc(v_v_1386_);
v_r_1387_ = lean_ctor_get(v_x_1369_, 4);
lean_inc(v_r_1387_);
lean_dec(v_x_1369_);
v___x_1388_ = lean_apply_5(v_h__1_1371_, v_size_1384_, v_k_1385_, v_v_1386_, v_r_1387_, lean_box(0));
return v___x_1388_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1391_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1392_ = lean_unsigned_to_nat(13u);
v___x_1393_ = lean_unsigned_to_nat(367u);
v___x_1394_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__0));
v___x_1395_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1396_ = l_mkPanicMessageWithDecl(v___x_1395_, v___x_1394_, v___x_1393_, v___x_1392_, v___x_1391_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(lean_object* v_inst_1397_, lean_object* v_x_1398_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v_l_1399_; 
v_l_1399_ = lean_ctor_get(v_x_1398_, 3);
if (lean_obj_tag(v_l_1399_) == 0)
{
v_x_1398_ = v_l_1399_;
goto _start;
}
else
{
lean_object* v_k_1401_; lean_object* v_v_1402_; lean_object* v___x_1403_; 
v_k_1401_ = lean_ctor_get(v_x_1398_, 1);
v_v_1402_ = lean_ctor_get(v_x_1398_, 2);
lean_inc(v_v_1402_);
lean_inc(v_k_1401_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_k_1401_);
lean_ctor_set(v___x_1403_, 1, v_v_1402_);
return v___x_1403_;
}
}
else
{
lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___x_1404_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__2);
v___x_1405_ = l_panic___redArg(v_inst_1397_, v___x_1404_);
return v___x_1405_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___boxed(lean_object* v_inst_1406_, lean_object* v_x_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1406_, v_x_1407_);
lean_dec(v_x_1407_);
lean_dec_ref(v_inst_1406_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21(lean_object* v_00_u03b1_1409_, lean_object* v_00_u03b2_1410_, lean_object* v_inst_1411_, lean_object* v_x_1412_){
_start:
{
lean_object* v___x_1413_; 
v___x_1413_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg(v_inst_1411_, v_x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntry_x21___boxed(lean_object* v_00_u03b1_1414_, lean_object* v_00_u03b2_1415_, lean_object* v_inst_1416_, lean_object* v_x_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Std_DTreeMap_Internal_Impl_minEntry_x21(v_00_u03b1_1414_, v_00_u03b2_1415_, v_inst_1416_, v_x_1417_);
lean_dec(v_x_1417_);
lean_dec_ref(v_inst_1416_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(lean_object* v_x_1419_, lean_object* v_x_1420_){
_start:
{
if (lean_obj_tag(v_x_1419_) == 0)
{
lean_object* v_l_1421_; 
v_l_1421_ = lean_ctor_get(v_x_1419_, 3);
if (lean_obj_tag(v_l_1421_) == 0)
{
v_x_1419_ = v_l_1421_;
goto _start;
}
else
{
lean_object* v_k_1423_; lean_object* v_v_1424_; lean_object* v___x_1425_; 
v_k_1423_ = lean_ctor_get(v_x_1419_, 1);
v_v_1424_ = lean_ctor_get(v_x_1419_, 2);
lean_inc(v_v_1424_);
lean_inc(v_k_1423_);
v___x_1425_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1425_, 0, v_k_1423_);
lean_ctor_set(v___x_1425_, 1, v_v_1424_);
return v___x_1425_;
}
}
else
{
lean_inc_ref(v_x_1420_);
return v_x_1420_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___redArg___boxed(lean_object* v_x_1426_, lean_object* v_x_1427_){
_start:
{
lean_object* v_res_1428_; 
v_res_1428_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1426_, v_x_1427_);
lean_dec_ref(v_x_1427_);
lean_dec(v_x_1426_);
return v_res_1428_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD(lean_object* v_00_u03b1_1429_, lean_object* v_00_u03b2_1430_, lean_object* v_x_1431_, lean_object* v_x_1432_){
_start:
{
lean_object* v___x_1433_; 
v___x_1433_ = l_Std_DTreeMap_Internal_Impl_minEntryD___redArg(v_x_1431_, v_x_1432_);
return v___x_1433_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minEntryD___boxed(lean_object* v_00_u03b1_1434_, lean_object* v_00_u03b2_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_Std_DTreeMap_Internal_Impl_minEntryD(v_00_u03b1_1434_, v_00_u03b2_1435_, v_x_1436_, v_x_1437_);
lean_dec_ref(v_x_1437_);
lean_dec(v_x_1436_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter___redArg(lean_object* v_x_1439_, lean_object* v_x_1440_, lean_object* v_h__1_1441_, lean_object* v_h__2_1442_, lean_object* v_h__3_1443_){
_start:
{
if (lean_obj_tag(v_x_1439_) == 0)
{
lean_object* v_l_1444_; 
lean_dec(v_h__1_1441_);
v_l_1444_ = lean_ctor_get(v_x_1439_, 3);
if (lean_obj_tag(v_l_1444_) == 0)
{
lean_object* v_size_1445_; lean_object* v_k_1446_; lean_object* v_v_1447_; lean_object* v_r_1448_; lean_object* v_size_1449_; lean_object* v_k_1450_; lean_object* v_v_1451_; lean_object* v_l_1452_; lean_object* v_r_1453_; lean_object* v___x_1454_; 
lean_inc_ref(v_l_1444_);
lean_dec(v_h__2_1442_);
v_size_1445_ = lean_ctor_get(v_x_1439_, 0);
lean_inc(v_size_1445_);
v_k_1446_ = lean_ctor_get(v_x_1439_, 1);
lean_inc(v_k_1446_);
v_v_1447_ = lean_ctor_get(v_x_1439_, 2);
lean_inc(v_v_1447_);
v_r_1448_ = lean_ctor_get(v_x_1439_, 4);
lean_inc(v_r_1448_);
lean_dec_ref_known(v_x_1439_, 5);
v_size_1449_ = lean_ctor_get(v_l_1444_, 0);
lean_inc(v_size_1449_);
v_k_1450_ = lean_ctor_get(v_l_1444_, 1);
lean_inc(v_k_1450_);
v_v_1451_ = lean_ctor_get(v_l_1444_, 2);
lean_inc(v_v_1451_);
v_l_1452_ = lean_ctor_get(v_l_1444_, 3);
lean_inc(v_l_1452_);
v_r_1453_ = lean_ctor_get(v_l_1444_, 4);
lean_inc(v_r_1453_);
lean_dec_ref_known(v_l_1444_, 5);
v___x_1454_ = lean_apply_10(v_h__3_1443_, v_size_1445_, v_k_1446_, v_v_1447_, v_size_1449_, v_k_1450_, v_v_1451_, v_l_1452_, v_r_1453_, v_r_1448_, v_x_1440_);
return v___x_1454_;
}
else
{
lean_object* v_size_1455_; lean_object* v_k_1456_; lean_object* v_v_1457_; lean_object* v_r_1458_; lean_object* v___x_1459_; 
lean_dec(v_h__3_1443_);
v_size_1455_ = lean_ctor_get(v_x_1439_, 0);
lean_inc(v_size_1455_);
v_k_1456_ = lean_ctor_get(v_x_1439_, 1);
lean_inc(v_k_1456_);
v_v_1457_ = lean_ctor_get(v_x_1439_, 2);
lean_inc(v_v_1457_);
v_r_1458_ = lean_ctor_get(v_x_1439_, 4);
lean_inc(v_r_1458_);
lean_dec_ref_known(v_x_1439_, 5);
v___x_1459_ = lean_apply_5(v_h__2_1442_, v_size_1455_, v_k_1456_, v_v_1457_, v_r_1458_, v_x_1440_);
return v___x_1459_;
}
}
else
{
lean_object* v___x_1460_; 
lean_dec(v_h__3_1443_);
lean_dec(v_h__2_1442_);
v___x_1460_ = lean_apply_1(v_h__1_1441_, v_x_1440_);
return v___x_1460_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minEntryD_match__1_splitter(lean_object* v_00_u03b1_1461_, lean_object* v_00_u03b2_1462_, lean_object* v_motive_1463_, lean_object* v_x_1464_, lean_object* v_x_1465_, lean_object* v_h__1_1466_, lean_object* v_h__2_1467_, lean_object* v_h__3_1468_){
_start:
{
if (lean_obj_tag(v_x_1464_) == 0)
{
lean_object* v_l_1469_; 
lean_dec(v_h__1_1466_);
v_l_1469_ = lean_ctor_get(v_x_1464_, 3);
if (lean_obj_tag(v_l_1469_) == 0)
{
lean_object* v_size_1470_; lean_object* v_k_1471_; lean_object* v_v_1472_; lean_object* v_r_1473_; lean_object* v_size_1474_; lean_object* v_k_1475_; lean_object* v_v_1476_; lean_object* v_l_1477_; lean_object* v_r_1478_; lean_object* v___x_1479_; 
lean_inc_ref(v_l_1469_);
lean_dec(v_h__2_1467_);
v_size_1470_ = lean_ctor_get(v_x_1464_, 0);
lean_inc(v_size_1470_);
v_k_1471_ = lean_ctor_get(v_x_1464_, 1);
lean_inc(v_k_1471_);
v_v_1472_ = lean_ctor_get(v_x_1464_, 2);
lean_inc(v_v_1472_);
v_r_1473_ = lean_ctor_get(v_x_1464_, 4);
lean_inc(v_r_1473_);
lean_dec_ref_known(v_x_1464_, 5);
v_size_1474_ = lean_ctor_get(v_l_1469_, 0);
lean_inc(v_size_1474_);
v_k_1475_ = lean_ctor_get(v_l_1469_, 1);
lean_inc(v_k_1475_);
v_v_1476_ = lean_ctor_get(v_l_1469_, 2);
lean_inc(v_v_1476_);
v_l_1477_ = lean_ctor_get(v_l_1469_, 3);
lean_inc(v_l_1477_);
v_r_1478_ = lean_ctor_get(v_l_1469_, 4);
lean_inc(v_r_1478_);
lean_dec_ref_known(v_l_1469_, 5);
v___x_1479_ = lean_apply_10(v_h__3_1468_, v_size_1470_, v_k_1471_, v_v_1472_, v_size_1474_, v_k_1475_, v_v_1476_, v_l_1477_, v_r_1478_, v_r_1473_, v_x_1465_);
return v___x_1479_;
}
else
{
lean_object* v_size_1480_; lean_object* v_k_1481_; lean_object* v_v_1482_; lean_object* v_r_1483_; lean_object* v___x_1484_; 
lean_dec(v_h__3_1468_);
v_size_1480_ = lean_ctor_get(v_x_1464_, 0);
lean_inc(v_size_1480_);
v_k_1481_ = lean_ctor_get(v_x_1464_, 1);
lean_inc(v_k_1481_);
v_v_1482_ = lean_ctor_get(v_x_1464_, 2);
lean_inc(v_v_1482_);
v_r_1483_ = lean_ctor_get(v_x_1464_, 4);
lean_inc(v_r_1483_);
lean_dec_ref_known(v_x_1464_, 5);
v___x_1484_ = lean_apply_5(v_h__2_1467_, v_size_1480_, v_k_1481_, v_v_1482_, v_r_1483_, v_x_1465_);
return v___x_1484_;
}
}
else
{
lean_object* v___x_1485_; 
lean_dec(v_h__3_1468_);
lean_dec(v_h__2_1467_);
v___x_1485_ = lean_apply_1(v_h__1_1466_, v_x_1465_);
return v___x_1485_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(lean_object* v_x_1486_){
_start:
{
if (lean_obj_tag(v_x_1486_) == 0)
{
lean_object* v_r_1487_; 
v_r_1487_ = lean_ctor_get(v_x_1486_, 4);
if (lean_obj_tag(v_r_1487_) == 0)
{
v_x_1486_ = v_r_1487_;
goto _start;
}
else
{
lean_object* v_k_1489_; lean_object* v_v_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; 
v_k_1489_ = lean_ctor_get(v_x_1486_, 1);
v_v_1490_ = lean_ctor_get(v_x_1486_, 2);
lean_inc(v_v_1490_);
lean_inc(v_k_1489_);
v___x_1491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1491_, 0, v_k_1489_);
lean_ctor_set(v___x_1491_, 1, v_v_1490_);
v___x_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
return v___x_1492_;
}
}
else
{
lean_object* v___x_1493_; 
v___x_1493_ = lean_box(0);
return v___x_1493_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg___boxed(lean_object* v_x_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1494_);
lean_dec(v_x_1494_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(lean_object* v_00_u03b1_1496_, lean_object* v_00_u03b2_1497_, lean_object* v_x_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___redArg(v_x_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x3f___boxed(lean_object* v_00_u03b1_1500_, lean_object* v_00_u03b2_1501_, lean_object* v_x_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x3f(v_00_u03b1_1500_, v_00_u03b2_1501_, v_x_1502_);
lean_dec(v_x_1502_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_1504_, lean_object* v_h__1_1505_, lean_object* v_h__2_1506_, lean_object* v_h__3_1507_){
_start:
{
if (lean_obj_tag(v_x_1504_) == 0)
{
lean_object* v_r_1508_; 
lean_dec(v_h__1_1505_);
v_r_1508_ = lean_ctor_get(v_x_1504_, 4);
if (lean_obj_tag(v_r_1508_) == 0)
{
lean_object* v_size_1509_; lean_object* v_k_1510_; lean_object* v_v_1511_; lean_object* v_l_1512_; lean_object* v_size_1513_; lean_object* v_k_1514_; lean_object* v_v_1515_; lean_object* v_l_1516_; lean_object* v_r_1517_; lean_object* v___x_1518_; 
lean_inc_ref(v_r_1508_);
lean_dec(v_h__2_1506_);
v_size_1509_ = lean_ctor_get(v_x_1504_, 0);
lean_inc(v_size_1509_);
v_k_1510_ = lean_ctor_get(v_x_1504_, 1);
lean_inc(v_k_1510_);
v_v_1511_ = lean_ctor_get(v_x_1504_, 2);
lean_inc(v_v_1511_);
v_l_1512_ = lean_ctor_get(v_x_1504_, 3);
lean_inc(v_l_1512_);
lean_dec_ref_known(v_x_1504_, 5);
v_size_1513_ = lean_ctor_get(v_r_1508_, 0);
lean_inc(v_size_1513_);
v_k_1514_ = lean_ctor_get(v_r_1508_, 1);
lean_inc(v_k_1514_);
v_v_1515_ = lean_ctor_get(v_r_1508_, 2);
lean_inc(v_v_1515_);
v_l_1516_ = lean_ctor_get(v_r_1508_, 3);
lean_inc(v_l_1516_);
v_r_1517_ = lean_ctor_get(v_r_1508_, 4);
lean_inc(v_r_1517_);
lean_dec_ref_known(v_r_1508_, 5);
v___x_1518_ = lean_apply_9(v_h__3_1507_, v_size_1509_, v_k_1510_, v_v_1511_, v_l_1512_, v_size_1513_, v_k_1514_, v_v_1515_, v_l_1516_, v_r_1517_);
return v___x_1518_;
}
else
{
lean_object* v_size_1519_; lean_object* v_k_1520_; lean_object* v_v_1521_; lean_object* v_l_1522_; lean_object* v___x_1523_; 
lean_dec(v_h__3_1507_);
v_size_1519_ = lean_ctor_get(v_x_1504_, 0);
lean_inc(v_size_1519_);
v_k_1520_ = lean_ctor_get(v_x_1504_, 1);
lean_inc(v_k_1520_);
v_v_1521_ = lean_ctor_get(v_x_1504_, 2);
lean_inc(v_v_1521_);
v_l_1522_ = lean_ctor_get(v_x_1504_, 3);
lean_inc(v_l_1522_);
lean_dec_ref_known(v_x_1504_, 5);
v___x_1523_ = lean_apply_4(v_h__2_1506_, v_size_1519_, v_k_1520_, v_v_1521_, v_l_1522_);
return v___x_1523_;
}
}
else
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v_h__3_1507_);
lean_dec(v_h__2_1506_);
v___x_1524_ = lean_box(0);
v___x_1525_ = lean_apply_1(v_h__1_1505_, v___x_1524_);
return v___x_1525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_1526_, lean_object* v_00_u03b2_1527_, lean_object* v_motive_1528_, lean_object* v_x_1529_, lean_object* v_h__1_1530_, lean_object* v_h__2_1531_, lean_object* v_h__3_1532_){
_start:
{
if (lean_obj_tag(v_x_1529_) == 0)
{
lean_object* v_r_1533_; 
lean_dec(v_h__1_1530_);
v_r_1533_ = lean_ctor_get(v_x_1529_, 4);
if (lean_obj_tag(v_r_1533_) == 0)
{
lean_object* v_size_1534_; lean_object* v_k_1535_; lean_object* v_v_1536_; lean_object* v_l_1537_; lean_object* v_size_1538_; lean_object* v_k_1539_; lean_object* v_v_1540_; lean_object* v_l_1541_; lean_object* v_r_1542_; lean_object* v___x_1543_; 
lean_inc_ref(v_r_1533_);
lean_dec(v_h__2_1531_);
v_size_1534_ = lean_ctor_get(v_x_1529_, 0);
lean_inc(v_size_1534_);
v_k_1535_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_k_1535_);
v_v_1536_ = lean_ctor_get(v_x_1529_, 2);
lean_inc(v_v_1536_);
v_l_1537_ = lean_ctor_get(v_x_1529_, 3);
lean_inc(v_l_1537_);
lean_dec_ref_known(v_x_1529_, 5);
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
lean_dec_ref_known(v_r_1533_, 5);
v___x_1543_ = lean_apply_9(v_h__3_1532_, v_size_1534_, v_k_1535_, v_v_1536_, v_l_1537_, v_size_1538_, v_k_1539_, v_v_1540_, v_l_1541_, v_r_1542_);
return v___x_1543_;
}
else
{
lean_object* v_size_1544_; lean_object* v_k_1545_; lean_object* v_v_1546_; lean_object* v_l_1547_; lean_object* v___x_1548_; 
lean_dec(v_h__3_1532_);
v_size_1544_ = lean_ctor_get(v_x_1529_, 0);
lean_inc(v_size_1544_);
v_k_1545_ = lean_ctor_get(v_x_1529_, 1);
lean_inc(v_k_1545_);
v_v_1546_ = lean_ctor_get(v_x_1529_, 2);
lean_inc(v_v_1546_);
v_l_1547_ = lean_ctor_get(v_x_1529_, 3);
lean_inc(v_l_1547_);
lean_dec_ref_known(v_x_1529_, 5);
v___x_1548_ = lean_apply_4(v_h__2_1531_, v_size_1544_, v_k_1545_, v_v_1546_, v_l_1547_);
return v___x_1548_;
}
}
else
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec(v_h__3_1532_);
lean_dec(v_h__2_1531_);
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_apply_1(v_h__1_1530_, v___x_1549_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(lean_object* v_x_1551_){
_start:
{
lean_object* v_r_1552_; 
v_r_1552_ = lean_ctor_get(v_x_1551_, 4);
if (lean_obj_tag(v_r_1552_) == 0)
{
v_x_1551_ = v_r_1552_;
goto _start;
}
else
{
lean_object* v_k_1554_; lean_object* v_v_1555_; lean_object* v___x_1556_; 
v_k_1554_ = lean_ctor_get(v_x_1551_, 1);
v_v_1555_ = lean_ctor_get(v_x_1551_, 2);
lean_inc(v_v_1555_);
lean_inc(v_k_1554_);
v___x_1556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1556_, 0, v_k_1554_);
lean_ctor_set(v___x_1556_, 1, v_v_1555_);
return v___x_1556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___redArg___boxed(lean_object* v_x_1557_){
_start:
{
lean_object* v_res_1558_; 
v_res_1558_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1557_);
lean_dec(v_x_1557_);
return v_res_1558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry(lean_object* v_00_u03b1_1559_, lean_object* v_00_u03b2_1560_, lean_object* v_x_1561_, lean_object* v_x_1562_){
_start:
{
lean_object* v___x_1563_; 
v___x_1563_ = l_Std_DTreeMap_Internal_Impl_maxEntry___redArg(v_x_1561_);
return v___x_1563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry___boxed(lean_object* v_00_u03b1_1564_, lean_object* v_00_u03b2_1565_, lean_object* v_x_1566_, lean_object* v_x_1567_){
_start:
{
lean_object* v_res_1568_; 
v_res_1568_ = l_Std_DTreeMap_Internal_Impl_maxEntry(v_00_u03b1_1564_, v_00_u03b2_1565_, v_x_1566_, v_x_1567_);
lean_dec(v_x_1566_);
return v_res_1568_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter___redArg(lean_object* v_x_1569_, lean_object* v_h__1_1570_, lean_object* v_h__2_1571_){
_start:
{
lean_object* v_r_1572_; 
v_r_1572_ = lean_ctor_get(v_x_1569_, 4);
if (lean_obj_tag(v_r_1572_) == 0)
{
lean_object* v_size_1573_; lean_object* v_k_1574_; lean_object* v_v_1575_; lean_object* v_l_1576_; lean_object* v_size_1577_; lean_object* v_k_1578_; lean_object* v_v_1579_; lean_object* v_l_1580_; lean_object* v_r_1581_; lean_object* v___x_1582_; 
lean_inc_ref(v_r_1572_);
lean_dec(v_h__1_1570_);
v_size_1573_ = lean_ctor_get(v_x_1569_, 0);
lean_inc(v_size_1573_);
v_k_1574_ = lean_ctor_get(v_x_1569_, 1);
lean_inc(v_k_1574_);
v_v_1575_ = lean_ctor_get(v_x_1569_, 2);
lean_inc(v_v_1575_);
v_l_1576_ = lean_ctor_get(v_x_1569_, 3);
lean_inc(v_l_1576_);
lean_dec(v_x_1569_);
v_size_1577_ = lean_ctor_get(v_r_1572_, 0);
lean_inc(v_size_1577_);
v_k_1578_ = lean_ctor_get(v_r_1572_, 1);
lean_inc(v_k_1578_);
v_v_1579_ = lean_ctor_get(v_r_1572_, 2);
lean_inc(v_v_1579_);
v_l_1580_ = lean_ctor_get(v_r_1572_, 3);
lean_inc(v_l_1580_);
v_r_1581_ = lean_ctor_get(v_r_1572_, 4);
lean_inc(v_r_1581_);
lean_dec_ref_known(v_r_1572_, 5);
v___x_1582_ = lean_apply_10(v_h__2_1571_, v_size_1573_, v_k_1574_, v_v_1575_, v_l_1576_, v_size_1577_, v_k_1578_, v_v_1579_, v_l_1580_, v_r_1581_, lean_box(0));
return v___x_1582_;
}
else
{
lean_object* v_size_1583_; lean_object* v_k_1584_; lean_object* v_v_1585_; lean_object* v_l_1586_; lean_object* v___x_1587_; 
lean_dec(v_h__2_1571_);
v_size_1583_ = lean_ctor_get(v_x_1569_, 0);
lean_inc(v_size_1583_);
v_k_1584_ = lean_ctor_get(v_x_1569_, 1);
lean_inc(v_k_1584_);
v_v_1585_ = lean_ctor_get(v_x_1569_, 2);
lean_inc(v_v_1585_);
v_l_1586_ = lean_ctor_get(v_x_1569_, 3);
lean_inc(v_l_1586_);
lean_dec(v_x_1569_);
v___x_1587_ = lean_apply_5(v_h__1_1570_, v_size_1583_, v_k_1584_, v_v_1585_, v_l_1586_, lean_box(0));
return v___x_1587_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntry_match__1_splitter(lean_object* v_00_u03b1_1588_, lean_object* v_00_u03b2_1589_, lean_object* v_motive_1590_, lean_object* v_x_1591_, lean_object* v_x_1592_, lean_object* v_h__1_1593_, lean_object* v_h__2_1594_){
_start:
{
lean_object* v_r_1595_; 
v_r_1595_ = lean_ctor_get(v_x_1591_, 4);
if (lean_obj_tag(v_r_1595_) == 0)
{
lean_object* v_size_1596_; lean_object* v_k_1597_; lean_object* v_v_1598_; lean_object* v_l_1599_; lean_object* v_size_1600_; lean_object* v_k_1601_; lean_object* v_v_1602_; lean_object* v_l_1603_; lean_object* v_r_1604_; lean_object* v___x_1605_; 
lean_inc_ref(v_r_1595_);
lean_dec(v_h__1_1593_);
v_size_1596_ = lean_ctor_get(v_x_1591_, 0);
lean_inc(v_size_1596_);
v_k_1597_ = lean_ctor_get(v_x_1591_, 1);
lean_inc(v_k_1597_);
v_v_1598_ = lean_ctor_get(v_x_1591_, 2);
lean_inc(v_v_1598_);
v_l_1599_ = lean_ctor_get(v_x_1591_, 3);
lean_inc(v_l_1599_);
lean_dec(v_x_1591_);
v_size_1600_ = lean_ctor_get(v_r_1595_, 0);
lean_inc(v_size_1600_);
v_k_1601_ = lean_ctor_get(v_r_1595_, 1);
lean_inc(v_k_1601_);
v_v_1602_ = lean_ctor_get(v_r_1595_, 2);
lean_inc(v_v_1602_);
v_l_1603_ = lean_ctor_get(v_r_1595_, 3);
lean_inc(v_l_1603_);
v_r_1604_ = lean_ctor_get(v_r_1595_, 4);
lean_inc(v_r_1604_);
lean_dec_ref_known(v_r_1595_, 5);
v___x_1605_ = lean_apply_10(v_h__2_1594_, v_size_1596_, v_k_1597_, v_v_1598_, v_l_1599_, v_size_1600_, v_k_1601_, v_v_1602_, v_l_1603_, v_r_1604_, lean_box(0));
return v___x_1605_;
}
else
{
lean_object* v_size_1606_; lean_object* v_k_1607_; lean_object* v_v_1608_; lean_object* v_l_1609_; lean_object* v___x_1610_; 
lean_dec(v_h__2_1594_);
v_size_1606_ = lean_ctor_get(v_x_1591_, 0);
lean_inc(v_size_1606_);
v_k_1607_ = lean_ctor_get(v_x_1591_, 1);
lean_inc(v_k_1607_);
v_v_1608_ = lean_ctor_get(v_x_1591_, 2);
lean_inc(v_v_1608_);
v_l_1609_ = lean_ctor_get(v_x_1591_, 3);
lean_inc(v_l_1609_);
lean_dec(v_x_1591_);
v___x_1610_ = lean_apply_5(v_h__1_1593_, v_size_1606_, v_k_1607_, v_v_1608_, v_l_1609_, lean_box(0));
return v___x_1610_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1612_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1613_ = lean_unsigned_to_nat(13u);
v___x_1614_ = lean_unsigned_to_nat(390u);
v___x_1615_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__0));
v___x_1616_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1617_ = l_mkPanicMessageWithDecl(v___x_1616_, v___x_1615_, v___x_1614_, v___x_1613_, v___x_1612_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(lean_object* v_inst_1618_, lean_object* v_x_1619_){
_start:
{
if (lean_obj_tag(v_x_1619_) == 0)
{
lean_object* v_r_1620_; 
v_r_1620_ = lean_ctor_get(v_x_1619_, 4);
if (lean_obj_tag(v_r_1620_) == 0)
{
v_x_1619_ = v_r_1620_;
goto _start;
}
else
{
lean_object* v_k_1622_; lean_object* v_v_1623_; lean_object* v___x_1624_; 
v_k_1622_ = lean_ctor_get(v_x_1619_, 1);
v_v_1623_ = lean_ctor_get(v_x_1619_, 2);
lean_inc(v_v_1623_);
lean_inc(v_k_1622_);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v_k_1622_);
lean_ctor_set(v___x_1624_, 1, v_v_1623_);
return v___x_1624_;
}
}
else
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1625_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___closed__1);
v___x_1626_ = l_panic___redArg(v_inst_1618_, v___x_1625_);
return v___x_1626_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg___boxed(lean_object* v_inst_1627_, lean_object* v_x_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1627_, v_x_1628_);
lean_dec(v_x_1628_);
lean_dec_ref(v_inst_1627_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21(lean_object* v_00_u03b1_1630_, lean_object* v_00_u03b2_1631_, lean_object* v_inst_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21___redArg(v_inst_1632_, v_x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntry_x21___boxed(lean_object* v_00_u03b1_1635_, lean_object* v_00_u03b2_1636_, lean_object* v_inst_1637_, lean_object* v_x_1638_){
_start:
{
lean_object* v_res_1639_; 
v_res_1639_ = l_Std_DTreeMap_Internal_Impl_maxEntry_x21(v_00_u03b1_1635_, v_00_u03b2_1636_, v_inst_1637_, v_x_1638_);
lean_dec(v_x_1638_);
lean_dec_ref(v_inst_1637_);
return v_res_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
if (lean_obj_tag(v_x_1640_) == 0)
{
lean_object* v_r_1642_; 
v_r_1642_ = lean_ctor_get(v_x_1640_, 4);
if (lean_obj_tag(v_r_1642_) == 0)
{
v_x_1640_ = v_r_1642_;
goto _start;
}
else
{
lean_object* v_k_1644_; lean_object* v_v_1645_; lean_object* v___x_1646_; 
v_k_1644_ = lean_ctor_get(v_x_1640_, 1);
v_v_1645_ = lean_ctor_get(v_x_1640_, 2);
lean_inc(v_v_1645_);
lean_inc(v_k_1644_);
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v_k_1644_);
lean_ctor_set(v___x_1646_, 1, v_v_1645_);
return v___x_1646_;
}
}
else
{
lean_inc_ref(v_x_1641_);
return v_x_1641_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg___boxed(lean_object* v_x_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1647_, v_x_1648_);
lean_dec_ref(v_x_1648_);
lean_dec(v_x_1647_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD(lean_object* v_00_u03b1_1650_, lean_object* v_00_u03b2_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Std_DTreeMap_Internal_Impl_maxEntryD___redArg(v_x_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxEntryD___boxed(lean_object* v_00_u03b1_1655_, lean_object* v_00_u03b2_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l_Std_DTreeMap_Internal_Impl_maxEntryD(v_00_u03b1_1655_, v_00_u03b2_1656_, v_x_1657_, v_x_1658_);
lean_dec_ref(v_x_1658_);
lean_dec(v_x_1657_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter___redArg(lean_object* v_x_1660_, lean_object* v_x_1661_, lean_object* v_h__1_1662_, lean_object* v_h__2_1663_, lean_object* v_h__3_1664_){
_start:
{
if (lean_obj_tag(v_x_1660_) == 0)
{
lean_object* v_r_1665_; 
lean_dec(v_h__1_1662_);
v_r_1665_ = lean_ctor_get(v_x_1660_, 4);
if (lean_obj_tag(v_r_1665_) == 0)
{
lean_object* v_size_1666_; lean_object* v_k_1667_; lean_object* v_v_1668_; lean_object* v_l_1669_; lean_object* v_size_1670_; lean_object* v_k_1671_; lean_object* v_v_1672_; lean_object* v_l_1673_; lean_object* v_r_1674_; lean_object* v___x_1675_; 
lean_inc_ref(v_r_1665_);
lean_dec(v_h__2_1663_);
v_size_1666_ = lean_ctor_get(v_x_1660_, 0);
lean_inc(v_size_1666_);
v_k_1667_ = lean_ctor_get(v_x_1660_, 1);
lean_inc(v_k_1667_);
v_v_1668_ = lean_ctor_get(v_x_1660_, 2);
lean_inc(v_v_1668_);
v_l_1669_ = lean_ctor_get(v_x_1660_, 3);
lean_inc(v_l_1669_);
lean_dec_ref_known(v_x_1660_, 5);
v_size_1670_ = lean_ctor_get(v_r_1665_, 0);
lean_inc(v_size_1670_);
v_k_1671_ = lean_ctor_get(v_r_1665_, 1);
lean_inc(v_k_1671_);
v_v_1672_ = lean_ctor_get(v_r_1665_, 2);
lean_inc(v_v_1672_);
v_l_1673_ = lean_ctor_get(v_r_1665_, 3);
lean_inc(v_l_1673_);
v_r_1674_ = lean_ctor_get(v_r_1665_, 4);
lean_inc(v_r_1674_);
lean_dec_ref_known(v_r_1665_, 5);
v___x_1675_ = lean_apply_10(v_h__3_1664_, v_size_1666_, v_k_1667_, v_v_1668_, v_l_1669_, v_size_1670_, v_k_1671_, v_v_1672_, v_l_1673_, v_r_1674_, v_x_1661_);
return v___x_1675_;
}
else
{
lean_object* v_size_1676_; lean_object* v_k_1677_; lean_object* v_v_1678_; lean_object* v_l_1679_; lean_object* v___x_1680_; 
lean_dec(v_h__3_1664_);
v_size_1676_ = lean_ctor_get(v_x_1660_, 0);
lean_inc(v_size_1676_);
v_k_1677_ = lean_ctor_get(v_x_1660_, 1);
lean_inc(v_k_1677_);
v_v_1678_ = lean_ctor_get(v_x_1660_, 2);
lean_inc(v_v_1678_);
v_l_1679_ = lean_ctor_get(v_x_1660_, 3);
lean_inc(v_l_1679_);
lean_dec_ref_known(v_x_1660_, 5);
v___x_1680_ = lean_apply_5(v_h__2_1663_, v_size_1676_, v_k_1677_, v_v_1678_, v_l_1679_, v_x_1661_);
return v___x_1680_;
}
}
else
{
lean_object* v___x_1681_; 
lean_dec(v_h__3_1664_);
lean_dec(v_h__2_1663_);
v___x_1681_ = lean_apply_1(v_h__1_1662_, v_x_1661_);
return v___x_1681_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_1682_, lean_object* v_00_u03b2_1683_, lean_object* v_motive_1684_, lean_object* v_x_1685_, lean_object* v_x_1686_, lean_object* v_h__1_1687_, lean_object* v_h__2_1688_, lean_object* v_h__3_1689_){
_start:
{
if (lean_obj_tag(v_x_1685_) == 0)
{
lean_object* v_r_1690_; 
lean_dec(v_h__1_1687_);
v_r_1690_ = lean_ctor_get(v_x_1685_, 4);
if (lean_obj_tag(v_r_1690_) == 0)
{
lean_object* v_size_1691_; lean_object* v_k_1692_; lean_object* v_v_1693_; lean_object* v_l_1694_; lean_object* v_size_1695_; lean_object* v_k_1696_; lean_object* v_v_1697_; lean_object* v_l_1698_; lean_object* v_r_1699_; lean_object* v___x_1700_; 
lean_inc_ref(v_r_1690_);
lean_dec(v_h__2_1688_);
v_size_1691_ = lean_ctor_get(v_x_1685_, 0);
lean_inc(v_size_1691_);
v_k_1692_ = lean_ctor_get(v_x_1685_, 1);
lean_inc(v_k_1692_);
v_v_1693_ = lean_ctor_get(v_x_1685_, 2);
lean_inc(v_v_1693_);
v_l_1694_ = lean_ctor_get(v_x_1685_, 3);
lean_inc(v_l_1694_);
lean_dec_ref_known(v_x_1685_, 5);
v_size_1695_ = lean_ctor_get(v_r_1690_, 0);
lean_inc(v_size_1695_);
v_k_1696_ = lean_ctor_get(v_r_1690_, 1);
lean_inc(v_k_1696_);
v_v_1697_ = lean_ctor_get(v_r_1690_, 2);
lean_inc(v_v_1697_);
v_l_1698_ = lean_ctor_get(v_r_1690_, 3);
lean_inc(v_l_1698_);
v_r_1699_ = lean_ctor_get(v_r_1690_, 4);
lean_inc(v_r_1699_);
lean_dec_ref_known(v_r_1690_, 5);
v___x_1700_ = lean_apply_10(v_h__3_1689_, v_size_1691_, v_k_1692_, v_v_1693_, v_l_1694_, v_size_1695_, v_k_1696_, v_v_1697_, v_l_1698_, v_r_1699_, v_x_1686_);
return v___x_1700_;
}
else
{
lean_object* v_size_1701_; lean_object* v_k_1702_; lean_object* v_v_1703_; lean_object* v_l_1704_; lean_object* v___x_1705_; 
lean_dec(v_h__3_1689_);
v_size_1701_ = lean_ctor_get(v_x_1685_, 0);
lean_inc(v_size_1701_);
v_k_1702_ = lean_ctor_get(v_x_1685_, 1);
lean_inc(v_k_1702_);
v_v_1703_ = lean_ctor_get(v_x_1685_, 2);
lean_inc(v_v_1703_);
v_l_1704_ = lean_ctor_get(v_x_1685_, 3);
lean_inc(v_l_1704_);
lean_dec_ref_known(v_x_1685_, 5);
v___x_1705_ = lean_apply_5(v_h__2_1688_, v_size_1701_, v_k_1702_, v_v_1703_, v_l_1704_, v_x_1686_);
return v___x_1705_;
}
}
else
{
lean_object* v___x_1706_; 
lean_dec(v_h__3_1689_);
lean_dec(v_h__2_1688_);
v___x_1706_ = lean_apply_1(v_h__1_1687_, v_x_1686_);
return v___x_1706_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(lean_object* v_x_1707_){
_start:
{
if (lean_obj_tag(v_x_1707_) == 0)
{
lean_object* v_l_1708_; 
v_l_1708_ = lean_ctor_get(v_x_1707_, 3);
if (lean_obj_tag(v_l_1708_) == 0)
{
v_x_1707_ = v_l_1708_;
goto _start;
}
else
{
lean_object* v_k_1710_; lean_object* v___x_1711_; 
v_k_1710_ = lean_ctor_get(v_x_1707_, 1);
lean_inc(v_k_1710_);
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_k_1710_);
return v___x_1711_;
}
}
else
{
lean_object* v___x_1712_; 
v___x_1712_ = lean_box(0);
return v___x_1712_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg___boxed(lean_object* v_x_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1713_);
lean_dec(v_x_1713_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f(lean_object* v_00_u03b1_1715_, lean_object* v_00_u03b2_1716_, lean_object* v_x_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f___redArg(v_x_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x3f___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_00_u03b2_1720_, lean_object* v_x_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_Std_DTreeMap_Internal_Impl_minKey_x3f(v_00_u03b1_1719_, v_00_u03b2_1720_, v_x_1721_);
lean_dec(v_x_1721_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg(lean_object* v_x_1723_){
_start:
{
lean_object* v_l_1724_; 
v_l_1724_ = lean_ctor_get(v_x_1723_, 3);
if (lean_obj_tag(v_l_1724_) == 0)
{
v_x_1723_ = v_l_1724_;
goto _start;
}
else
{
lean_object* v_k_1726_; 
v_k_1726_ = lean_ctor_get(v_x_1723_, 1);
lean_inc(v_k_1726_);
return v_k_1726_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___redArg___boxed(lean_object* v_x_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1727_);
lean_dec(v_x_1727_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey(lean_object* v_00_u03b1_1729_, lean_object* v_00_u03b2_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_){
_start:
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Std_DTreeMap_Internal_Impl_minKey___redArg(v_x_1731_);
return v___x_1733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey___boxed(lean_object* v_00_u03b1_1734_, lean_object* v_00_u03b2_1735_, lean_object* v_x_1736_, lean_object* v_x_1737_){
_start:
{
lean_object* v_res_1738_; 
v_res_1738_ = l_Std_DTreeMap_Internal_Impl_minKey(v_00_u03b1_1734_, v_00_u03b2_1735_, v_x_1736_, v_x_1737_);
lean_dec(v_x_1736_);
return v_res_1738_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1740_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1741_ = lean_unsigned_to_nat(13u);
v___x_1742_ = lean_unsigned_to_nat(413u);
v___x_1743_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__0));
v___x_1744_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1745_ = l_mkPanicMessageWithDecl(v___x_1744_, v___x_1743_, v___x_1742_, v___x_1741_, v___x_1740_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(lean_object* v_inst_1746_, lean_object* v_x_1747_){
_start:
{
if (lean_obj_tag(v_x_1747_) == 0)
{
lean_object* v_l_1748_; 
v_l_1748_ = lean_ctor_get(v_x_1747_, 3);
if (lean_obj_tag(v_l_1748_) == 0)
{
v_x_1747_ = v_l_1748_;
goto _start;
}
else
{
lean_object* v_k_1750_; 
v_k_1750_ = lean_ctor_get(v_x_1747_, 1);
lean_inc(v_k_1750_);
return v_k_1750_;
}
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; 
v___x_1751_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___closed__1);
v___x_1752_ = l_panic___redArg(v_inst_1746_, v___x_1751_);
return v___x_1752_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg___boxed(lean_object* v_inst_1753_, lean_object* v_x_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1753_, v_x_1754_);
lean_dec(v_x_1754_);
lean_dec(v_inst_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21(lean_object* v_00_u03b1_1756_, lean_object* v_00_u03b2_1757_, lean_object* v_inst_1758_, lean_object* v_x_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_Std_DTreeMap_Internal_Impl_minKey_x21___redArg(v_inst_1758_, v_x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKey_x21___boxed(lean_object* v_00_u03b1_1761_, lean_object* v_00_u03b2_1762_, lean_object* v_inst_1763_, lean_object* v_x_1764_){
_start:
{
lean_object* v_res_1765_; 
v_res_1765_ = l_Std_DTreeMap_Internal_Impl_minKey_x21(v_00_u03b1_1761_, v_00_u03b2_1762_, v_inst_1763_, v_x_1764_);
lean_dec(v_x_1764_);
lean_dec(v_inst_1763_);
return v_res_1765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(lean_object* v_x_1766_, lean_object* v_x_1767_){
_start:
{
if (lean_obj_tag(v_x_1766_) == 0)
{
lean_object* v_l_1768_; 
v_l_1768_ = lean_ctor_get(v_x_1766_, 3);
if (lean_obj_tag(v_l_1768_) == 0)
{
v_x_1766_ = v_l_1768_;
goto _start;
}
else
{
lean_object* v_k_1770_; 
v_k_1770_ = lean_ctor_get(v_x_1766_, 1);
lean_inc(v_k_1770_);
return v_k_1770_;
}
}
else
{
lean_inc(v_x_1767_);
return v_x_1767_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___redArg___boxed(lean_object* v_x_1771_, lean_object* v_x_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1771_, v_x_1772_);
lean_dec(v_x_1772_);
lean_dec(v_x_1771_);
return v_res_1773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD(lean_object* v_00_u03b1_1774_, lean_object* v_00_u03b2_1775_, lean_object* v_x_1776_, lean_object* v_x_1777_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Std_DTreeMap_Internal_Impl_minKeyD___redArg(v_x_1776_, v_x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_minKeyD___boxed(lean_object* v_00_u03b1_1779_, lean_object* v_00_u03b2_1780_, lean_object* v_x_1781_, lean_object* v_x_1782_){
_start:
{
lean_object* v_res_1783_; 
v_res_1783_ = l_Std_DTreeMap_Internal_Impl_minKeyD(v_00_u03b1_1779_, v_00_u03b2_1780_, v_x_1781_, v_x_1782_);
lean_dec(v_x_1782_);
lean_dec(v_x_1781_);
return v_res_1783_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter___redArg(lean_object* v_x_1784_, lean_object* v_x_1785_, lean_object* v_h__1_1786_, lean_object* v_h__2_1787_, lean_object* v_h__3_1788_){
_start:
{
if (lean_obj_tag(v_x_1784_) == 0)
{
lean_object* v_l_1789_; 
lean_dec(v_h__1_1786_);
v_l_1789_ = lean_ctor_get(v_x_1784_, 3);
if (lean_obj_tag(v_l_1789_) == 0)
{
lean_object* v_size_1790_; lean_object* v_k_1791_; lean_object* v_v_1792_; lean_object* v_r_1793_; lean_object* v_size_1794_; lean_object* v_k_1795_; lean_object* v_v_1796_; lean_object* v_l_1797_; lean_object* v_r_1798_; lean_object* v___x_1799_; 
lean_inc_ref(v_l_1789_);
lean_dec(v_h__2_1787_);
v_size_1790_ = lean_ctor_get(v_x_1784_, 0);
lean_inc(v_size_1790_);
v_k_1791_ = lean_ctor_get(v_x_1784_, 1);
lean_inc(v_k_1791_);
v_v_1792_ = lean_ctor_get(v_x_1784_, 2);
lean_inc(v_v_1792_);
v_r_1793_ = lean_ctor_get(v_x_1784_, 4);
lean_inc(v_r_1793_);
lean_dec_ref_known(v_x_1784_, 5);
v_size_1794_ = lean_ctor_get(v_l_1789_, 0);
lean_inc(v_size_1794_);
v_k_1795_ = lean_ctor_get(v_l_1789_, 1);
lean_inc(v_k_1795_);
v_v_1796_ = lean_ctor_get(v_l_1789_, 2);
lean_inc(v_v_1796_);
v_l_1797_ = lean_ctor_get(v_l_1789_, 3);
lean_inc(v_l_1797_);
v_r_1798_ = lean_ctor_get(v_l_1789_, 4);
lean_inc(v_r_1798_);
lean_dec_ref_known(v_l_1789_, 5);
v___x_1799_ = lean_apply_10(v_h__3_1788_, v_size_1790_, v_k_1791_, v_v_1792_, v_size_1794_, v_k_1795_, v_v_1796_, v_l_1797_, v_r_1798_, v_r_1793_, v_x_1785_);
return v___x_1799_;
}
else
{
lean_object* v_size_1800_; lean_object* v_k_1801_; lean_object* v_v_1802_; lean_object* v_r_1803_; lean_object* v___x_1804_; 
lean_dec(v_h__3_1788_);
v_size_1800_ = lean_ctor_get(v_x_1784_, 0);
lean_inc(v_size_1800_);
v_k_1801_ = lean_ctor_get(v_x_1784_, 1);
lean_inc(v_k_1801_);
v_v_1802_ = lean_ctor_get(v_x_1784_, 2);
lean_inc(v_v_1802_);
v_r_1803_ = lean_ctor_get(v_x_1784_, 4);
lean_inc(v_r_1803_);
lean_dec_ref_known(v_x_1784_, 5);
v___x_1804_ = lean_apply_5(v_h__2_1787_, v_size_1800_, v_k_1801_, v_v_1802_, v_r_1803_, v_x_1785_);
return v___x_1804_;
}
}
else
{
lean_object* v___x_1805_; 
lean_dec(v_h__3_1788_);
lean_dec(v_h__2_1787_);
v___x_1805_ = lean_apply_1(v_h__1_1786_, v_x_1785_);
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_minKeyD_match__1_splitter(lean_object* v_00_u03b1_1806_, lean_object* v_00_u03b2_1807_, lean_object* v_motive_1808_, lean_object* v_x_1809_, lean_object* v_x_1810_, lean_object* v_h__1_1811_, lean_object* v_h__2_1812_, lean_object* v_h__3_1813_){
_start:
{
if (lean_obj_tag(v_x_1809_) == 0)
{
lean_object* v_l_1814_; 
lean_dec(v_h__1_1811_);
v_l_1814_ = lean_ctor_get(v_x_1809_, 3);
if (lean_obj_tag(v_l_1814_) == 0)
{
lean_object* v_size_1815_; lean_object* v_k_1816_; lean_object* v_v_1817_; lean_object* v_r_1818_; lean_object* v_size_1819_; lean_object* v_k_1820_; lean_object* v_v_1821_; lean_object* v_l_1822_; lean_object* v_r_1823_; lean_object* v___x_1824_; 
lean_inc_ref(v_l_1814_);
lean_dec(v_h__2_1812_);
v_size_1815_ = lean_ctor_get(v_x_1809_, 0);
lean_inc(v_size_1815_);
v_k_1816_ = lean_ctor_get(v_x_1809_, 1);
lean_inc(v_k_1816_);
v_v_1817_ = lean_ctor_get(v_x_1809_, 2);
lean_inc(v_v_1817_);
v_r_1818_ = lean_ctor_get(v_x_1809_, 4);
lean_inc(v_r_1818_);
lean_dec_ref_known(v_x_1809_, 5);
v_size_1819_ = lean_ctor_get(v_l_1814_, 0);
lean_inc(v_size_1819_);
v_k_1820_ = lean_ctor_get(v_l_1814_, 1);
lean_inc(v_k_1820_);
v_v_1821_ = lean_ctor_get(v_l_1814_, 2);
lean_inc(v_v_1821_);
v_l_1822_ = lean_ctor_get(v_l_1814_, 3);
lean_inc(v_l_1822_);
v_r_1823_ = lean_ctor_get(v_l_1814_, 4);
lean_inc(v_r_1823_);
lean_dec_ref_known(v_l_1814_, 5);
v___x_1824_ = lean_apply_10(v_h__3_1813_, v_size_1815_, v_k_1816_, v_v_1817_, v_size_1819_, v_k_1820_, v_v_1821_, v_l_1822_, v_r_1823_, v_r_1818_, v_x_1810_);
return v___x_1824_;
}
else
{
lean_object* v_size_1825_; lean_object* v_k_1826_; lean_object* v_v_1827_; lean_object* v_r_1828_; lean_object* v___x_1829_; 
lean_dec(v_h__3_1813_);
v_size_1825_ = lean_ctor_get(v_x_1809_, 0);
lean_inc(v_size_1825_);
v_k_1826_ = lean_ctor_get(v_x_1809_, 1);
lean_inc(v_k_1826_);
v_v_1827_ = lean_ctor_get(v_x_1809_, 2);
lean_inc(v_v_1827_);
v_r_1828_ = lean_ctor_get(v_x_1809_, 4);
lean_inc(v_r_1828_);
lean_dec_ref_known(v_x_1809_, 5);
v___x_1829_ = lean_apply_5(v_h__2_1812_, v_size_1825_, v_k_1826_, v_v_1827_, v_r_1828_, v_x_1810_);
return v___x_1829_;
}
}
else
{
lean_object* v___x_1830_; 
lean_dec(v_h__3_1813_);
lean_dec(v_h__2_1812_);
v___x_1830_ = lean_apply_1(v_h__1_1811_, v_x_1810_);
return v___x_1830_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(lean_object* v_x_1831_){
_start:
{
if (lean_obj_tag(v_x_1831_) == 0)
{
lean_object* v_r_1832_; 
v_r_1832_ = lean_ctor_get(v_x_1831_, 4);
if (lean_obj_tag(v_r_1832_) == 0)
{
v_x_1831_ = v_r_1832_;
goto _start;
}
else
{
lean_object* v_k_1834_; lean_object* v___x_1835_; 
v_k_1834_ = lean_ctor_get(v_x_1831_, 1);
lean_inc(v_k_1834_);
v___x_1835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1835_, 0, v_k_1834_);
return v___x_1835_;
}
}
else
{
lean_object* v___x_1836_; 
v___x_1836_ = lean_box(0);
return v___x_1836_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg___boxed(lean_object* v_x_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1837_);
lean_dec(v_x_1837_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f(lean_object* v_00_u03b1_1839_, lean_object* v_00_u03b2_1840_, lean_object* v_x_1841_){
_start:
{
lean_object* v___x_1842_; 
v___x_1842_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f___redArg(v_x_1841_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x3f___boxed(lean_object* v_00_u03b1_1843_, lean_object* v_00_u03b2_1844_, lean_object* v_x_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Std_DTreeMap_Internal_Impl_maxKey_x3f(v_00_u03b1_1843_, v_00_u03b2_1844_, v_x_1845_);
lean_dec(v_x_1845_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg(lean_object* v_x_1847_){
_start:
{
lean_object* v_r_1848_; 
v_r_1848_ = lean_ctor_get(v_x_1847_, 4);
if (lean_obj_tag(v_r_1848_) == 0)
{
v_x_1847_ = v_r_1848_;
goto _start;
}
else
{
lean_object* v_k_1850_; 
v_k_1850_ = lean_ctor_get(v_x_1847_, 1);
lean_inc(v_k_1850_);
return v_k_1850_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___redArg___boxed(lean_object* v_x_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1851_);
lean_dec(v_x_1851_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey(lean_object* v_00_u03b1_1853_, lean_object* v_00_u03b2_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Std_DTreeMap_Internal_Impl_maxKey___redArg(v_x_1855_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey___boxed(lean_object* v_00_u03b1_1858_, lean_object* v_00_u03b2_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Std_DTreeMap_Internal_Impl_maxKey(v_00_u03b1_1858_, v_00_u03b2_1859_, v_x_1860_, v_x_1861_);
lean_dec(v_x_1860_);
return v_res_1862_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1864_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_1865_ = lean_unsigned_to_nat(13u);
v___x_1866_ = lean_unsigned_to_nat(436u);
v___x_1867_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__0));
v___x_1868_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_1869_ = l_mkPanicMessageWithDecl(v___x_1868_, v___x_1867_, v___x_1866_, v___x_1865_, v___x_1864_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(lean_object* v_inst_1870_, lean_object* v_x_1871_){
_start:
{
if (lean_obj_tag(v_x_1871_) == 0)
{
lean_object* v_r_1872_; 
v_r_1872_ = lean_ctor_get(v_x_1871_, 4);
if (lean_obj_tag(v_r_1872_) == 0)
{
v_x_1871_ = v_r_1872_;
goto _start;
}
else
{
lean_object* v_k_1874_; 
v_k_1874_ = lean_ctor_get(v_x_1871_, 1);
lean_inc(v_k_1874_);
return v_k_1874_;
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___closed__1);
v___x_1876_ = l_panic___redArg(v_inst_1870_, v___x_1875_);
return v___x_1876_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg___boxed(lean_object* v_inst_1877_, lean_object* v_x_1878_){
_start:
{
lean_object* v_res_1879_; 
v_res_1879_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1877_, v_x_1878_);
lean_dec(v_x_1878_);
lean_dec(v_inst_1877_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21(lean_object* v_00_u03b1_1880_, lean_object* v_00_u03b2_1881_, lean_object* v_inst_1882_, lean_object* v_x_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21___redArg(v_inst_1882_, v_x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKey_x21___boxed(lean_object* v_00_u03b1_1885_, lean_object* v_00_u03b2_1886_, lean_object* v_inst_1887_, lean_object* v_x_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Std_DTreeMap_Internal_Impl_maxKey_x21(v_00_u03b1_1885_, v_00_u03b2_1886_, v_inst_1887_, v_x_1888_);
lean_dec(v_x_1888_);
lean_dec(v_inst_1887_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(lean_object* v_x_1890_, lean_object* v_x_1891_){
_start:
{
if (lean_obj_tag(v_x_1890_) == 0)
{
lean_object* v_r_1892_; 
v_r_1892_ = lean_ctor_get(v_x_1890_, 4);
if (lean_obj_tag(v_r_1892_) == 0)
{
v_x_1890_ = v_r_1892_;
goto _start;
}
else
{
lean_object* v_k_1894_; 
v_k_1894_ = lean_ctor_get(v_x_1890_, 1);
lean_inc(v_k_1894_);
return v_k_1894_;
}
}
else
{
lean_inc(v_x_1891_);
return v_x_1891_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg___boxed(lean_object* v_x_1895_, lean_object* v_x_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1895_, v_x_1896_);
lean_dec(v_x_1896_);
lean_dec(v_x_1895_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD(lean_object* v_00_u03b1_1898_, lean_object* v_00_u03b2_1899_, lean_object* v_x_1900_, lean_object* v_x_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l_Std_DTreeMap_Internal_Impl_maxKeyD___redArg(v_x_1900_, v_x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_maxKeyD___boxed(lean_object* v_00_u03b1_1903_, lean_object* v_00_u03b2_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_Std_DTreeMap_Internal_Impl_maxKeyD(v_00_u03b1_1903_, v_00_u03b2_1904_, v_x_1905_, v_x_1906_);
lean_dec(v_x_1906_);
lean_dec(v_x_1905_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter___redArg(lean_object* v_x_1908_, lean_object* v_x_1909_, lean_object* v_h__1_1910_, lean_object* v_h__2_1911_, lean_object* v_h__3_1912_){
_start:
{
if (lean_obj_tag(v_x_1908_) == 0)
{
lean_object* v_r_1913_; 
lean_dec(v_h__1_1910_);
v_r_1913_ = lean_ctor_get(v_x_1908_, 4);
if (lean_obj_tag(v_r_1913_) == 0)
{
lean_object* v_size_1914_; lean_object* v_k_1915_; lean_object* v_v_1916_; lean_object* v_l_1917_; lean_object* v_size_1918_; lean_object* v_k_1919_; lean_object* v_v_1920_; lean_object* v_l_1921_; lean_object* v_r_1922_; lean_object* v___x_1923_; 
lean_inc_ref(v_r_1913_);
lean_dec(v_h__2_1911_);
v_size_1914_ = lean_ctor_get(v_x_1908_, 0);
lean_inc(v_size_1914_);
v_k_1915_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_k_1915_);
v_v_1916_ = lean_ctor_get(v_x_1908_, 2);
lean_inc(v_v_1916_);
v_l_1917_ = lean_ctor_get(v_x_1908_, 3);
lean_inc(v_l_1917_);
lean_dec_ref_known(v_x_1908_, 5);
v_size_1918_ = lean_ctor_get(v_r_1913_, 0);
lean_inc(v_size_1918_);
v_k_1919_ = lean_ctor_get(v_r_1913_, 1);
lean_inc(v_k_1919_);
v_v_1920_ = lean_ctor_get(v_r_1913_, 2);
lean_inc(v_v_1920_);
v_l_1921_ = lean_ctor_get(v_r_1913_, 3);
lean_inc(v_l_1921_);
v_r_1922_ = lean_ctor_get(v_r_1913_, 4);
lean_inc(v_r_1922_);
lean_dec_ref_known(v_r_1913_, 5);
v___x_1923_ = lean_apply_10(v_h__3_1912_, v_size_1914_, v_k_1915_, v_v_1916_, v_l_1917_, v_size_1918_, v_k_1919_, v_v_1920_, v_l_1921_, v_r_1922_, v_x_1909_);
return v___x_1923_;
}
else
{
lean_object* v_size_1924_; lean_object* v_k_1925_; lean_object* v_v_1926_; lean_object* v_l_1927_; lean_object* v___x_1928_; 
lean_dec(v_h__3_1912_);
v_size_1924_ = lean_ctor_get(v_x_1908_, 0);
lean_inc(v_size_1924_);
v_k_1925_ = lean_ctor_get(v_x_1908_, 1);
lean_inc(v_k_1925_);
v_v_1926_ = lean_ctor_get(v_x_1908_, 2);
lean_inc(v_v_1926_);
v_l_1927_ = lean_ctor_get(v_x_1908_, 3);
lean_inc(v_l_1927_);
lean_dec_ref_known(v_x_1908_, 5);
v___x_1928_ = lean_apply_5(v_h__2_1911_, v_size_1924_, v_k_1925_, v_v_1926_, v_l_1927_, v_x_1909_);
return v___x_1928_;
}
}
else
{
lean_object* v___x_1929_; 
lean_dec(v_h__3_1912_);
lean_dec(v_h__2_1911_);
v___x_1929_ = lean_apply_1(v_h__1_1910_, v_x_1909_);
return v___x_1929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_maxKeyD_match__1_splitter(lean_object* v_00_u03b1_1930_, lean_object* v_00_u03b2_1931_, lean_object* v_motive_1932_, lean_object* v_x_1933_, lean_object* v_x_1934_, lean_object* v_h__1_1935_, lean_object* v_h__2_1936_, lean_object* v_h__3_1937_){
_start:
{
if (lean_obj_tag(v_x_1933_) == 0)
{
lean_object* v_r_1938_; 
lean_dec(v_h__1_1935_);
v_r_1938_ = lean_ctor_get(v_x_1933_, 4);
if (lean_obj_tag(v_r_1938_) == 0)
{
lean_object* v_size_1939_; lean_object* v_k_1940_; lean_object* v_v_1941_; lean_object* v_l_1942_; lean_object* v_size_1943_; lean_object* v_k_1944_; lean_object* v_v_1945_; lean_object* v_l_1946_; lean_object* v_r_1947_; lean_object* v___x_1948_; 
lean_inc_ref(v_r_1938_);
lean_dec(v_h__2_1936_);
v_size_1939_ = lean_ctor_get(v_x_1933_, 0);
lean_inc(v_size_1939_);
v_k_1940_ = lean_ctor_get(v_x_1933_, 1);
lean_inc(v_k_1940_);
v_v_1941_ = lean_ctor_get(v_x_1933_, 2);
lean_inc(v_v_1941_);
v_l_1942_ = lean_ctor_get(v_x_1933_, 3);
lean_inc(v_l_1942_);
lean_dec_ref_known(v_x_1933_, 5);
v_size_1943_ = lean_ctor_get(v_r_1938_, 0);
lean_inc(v_size_1943_);
v_k_1944_ = lean_ctor_get(v_r_1938_, 1);
lean_inc(v_k_1944_);
v_v_1945_ = lean_ctor_get(v_r_1938_, 2);
lean_inc(v_v_1945_);
v_l_1946_ = lean_ctor_get(v_r_1938_, 3);
lean_inc(v_l_1946_);
v_r_1947_ = lean_ctor_get(v_r_1938_, 4);
lean_inc(v_r_1947_);
lean_dec_ref_known(v_r_1938_, 5);
v___x_1948_ = lean_apply_10(v_h__3_1937_, v_size_1939_, v_k_1940_, v_v_1941_, v_l_1942_, v_size_1943_, v_k_1944_, v_v_1945_, v_l_1946_, v_r_1947_, v_x_1934_);
return v___x_1948_;
}
else
{
lean_object* v_size_1949_; lean_object* v_k_1950_; lean_object* v_v_1951_; lean_object* v_l_1952_; lean_object* v___x_1953_; 
lean_dec(v_h__3_1937_);
v_size_1949_ = lean_ctor_get(v_x_1933_, 0);
lean_inc(v_size_1949_);
v_k_1950_ = lean_ctor_get(v_x_1933_, 1);
lean_inc(v_k_1950_);
v_v_1951_ = lean_ctor_get(v_x_1933_, 2);
lean_inc(v_v_1951_);
v_l_1952_ = lean_ctor_get(v_x_1933_, 3);
lean_inc(v_l_1952_);
lean_dec_ref_known(v_x_1933_, 5);
v___x_1953_ = lean_apply_5(v_h__2_1936_, v_size_1949_, v_k_1950_, v_v_1951_, v_l_1952_, v_x_1934_);
return v___x_1953_;
}
}
else
{
lean_object* v___x_1954_; 
lean_dec(v_h__3_1937_);
lean_dec(v_h__2_1936_);
v___x_1954_ = lean_apply_1(v_h__1_1935_, v_x_1934_);
return v___x_1954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(lean_object* v_x_1955_, lean_object* v_x_1956_){
_start:
{
lean_object* v_k_1957_; lean_object* v_v_1958_; lean_object* v_l_1959_; lean_object* v_r_1960_; lean_object* v___y_1962_; lean_object* v___y_1968_; 
v_k_1957_ = lean_ctor_get(v_x_1955_, 1);
v_v_1958_ = lean_ctor_get(v_x_1955_, 2);
v_l_1959_ = lean_ctor_get(v_x_1955_, 3);
v_r_1960_ = lean_ctor_get(v_x_1955_, 4);
if (lean_obj_tag(v_l_1959_) == 0)
{
lean_object* v_size_1975_; 
v_size_1975_ = lean_ctor_get(v_l_1959_, 0);
v___y_1968_ = v_size_1975_;
goto v___jp_1967_;
}
else
{
lean_object* v___x_1976_; 
v___x_1976_ = lean_unsigned_to_nat(0u);
v___y_1968_ = v___x_1976_;
goto v___jp_1967_;
}
v___jp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = lean_nat_sub(v_x_1956_, v___y_1962_);
lean_dec(v_x_1956_);
v___x_1964_ = lean_unsigned_to_nat(1u);
v___x_1965_ = lean_nat_sub(v___x_1963_, v___x_1964_);
lean_dec(v___x_1963_);
v_x_1955_ = v_r_1960_;
v_x_1956_ = v___x_1965_;
goto _start;
}
v___jp_1967_:
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_nat_dec_lt(v_x_1956_, v___y_1968_);
if (v___x_1969_ == 0)
{
uint8_t v___x_1970_; 
v___x_1970_ = lean_nat_dec_eq(v_x_1956_, v___y_1968_);
if (v___x_1970_ == 0)
{
if (lean_obj_tag(v_l_1959_) == 0)
{
lean_object* v_size_1971_; 
v_size_1971_ = lean_ctor_get(v_l_1959_, 0);
v___y_1962_ = v_size_1971_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_unsigned_to_nat(0u);
v___y_1962_ = v___x_1972_;
goto v___jp_1961_;
}
}
else
{
lean_object* v___x_1973_; 
lean_dec(v_x_1956_);
lean_inc(v_v_1958_);
lean_inc(v_k_1957_);
v___x_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1973_, 0, v_k_1957_);
lean_ctor_set(v___x_1973_, 1, v_v_1958_);
return v___x_1973_;
}
}
else
{
v_x_1955_ = v_l_1959_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg___boxed(lean_object* v_x_1977_, lean_object* v_x_1978_){
_start:
{
lean_object* v_res_1979_; 
v_res_1979_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1977_, v_x_1978_);
lean_dec(v_x_1977_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx(lean_object* v_00_u03b1_1980_, lean_object* v_00_u03b2_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_, lean_object* v_x_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx___redArg(v_x_1982_, v_x_1984_);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx___boxed(lean_object* v_00_u03b1_1987_, lean_object* v_00_u03b2_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_){
_start:
{
lean_object* v_res_1993_; 
v_res_1993_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx(v_00_u03b1_1987_, v_00_u03b2_1988_, v_x_1989_, v_x_1990_, v_x_1991_, v_x_1992_);
lean_dec(v_x_1989_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(lean_object* v_x_1994_, lean_object* v_x_1995_){
_start:
{
if (lean_obj_tag(v_x_1994_) == 0)
{
lean_object* v_k_1996_; lean_object* v_v_1997_; lean_object* v_l_1998_; lean_object* v_r_1999_; lean_object* v___y_2001_; lean_object* v___y_2007_; 
v_k_1996_ = lean_ctor_get(v_x_1994_, 1);
v_v_1997_ = lean_ctor_get(v_x_1994_, 2);
v_l_1998_ = lean_ctor_get(v_x_1994_, 3);
v_r_1999_ = lean_ctor_get(v_x_1994_, 4);
if (lean_obj_tag(v_l_1998_) == 0)
{
lean_object* v_size_2015_; 
v_size_2015_ = lean_ctor_get(v_l_1998_, 0);
v___y_2007_ = v_size_2015_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_unsigned_to_nat(0u);
v___y_2007_ = v___x_2016_;
goto v___jp_2006_;
}
v___jp_2000_:
{
lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2002_ = lean_nat_sub(v_x_1995_, v___y_2001_);
lean_dec(v_x_1995_);
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_sub(v___x_2002_, v___x_2003_);
lean_dec(v___x_2002_);
v_x_1994_ = v_r_1999_;
v_x_1995_ = v___x_2004_;
goto _start;
}
v___jp_2006_:
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_nat_dec_lt(v_x_1995_, v___y_2007_);
if (v___x_2008_ == 0)
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_nat_dec_eq(v_x_1995_, v___y_2007_);
if (v___x_2009_ == 0)
{
if (lean_obj_tag(v_l_1998_) == 0)
{
lean_object* v_size_2010_; 
v_size_2010_ = lean_ctor_get(v_l_1998_, 0);
v___y_2001_ = v_size_2010_;
goto v___jp_2000_;
}
else
{
lean_object* v___x_2011_; 
v___x_2011_ = lean_unsigned_to_nat(0u);
v___y_2001_ = v___x_2011_;
goto v___jp_2000_;
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_x_1995_);
lean_inc(v_v_1997_);
lean_inc(v_k_1996_);
v___x_2012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2012_, 0, v_k_1996_);
lean_ctor_set(v___x_2012_, 1, v_v_1997_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
return v___x_2013_;
}
}
else
{
v_x_1994_ = v_l_1998_;
goto _start;
}
}
}
else
{
lean_object* v___x_2017_; 
lean_dec(v_x_1995_);
v___x_2017_ = lean_box(0);
return v___x_2017_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_2018_, lean_object* v_x_2019_){
_start:
{
lean_object* v_res_2020_; 
v_res_2020_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_2018_, v_x_2019_);
lean_dec(v_x_2018_);
return v_res_2020_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(lean_object* v_00_u03b1_2021_, lean_object* v_00_u03b2_2022_, lean_object* v_x_2023_, lean_object* v_x_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___redArg(v_x_2023_, v_x_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_2026_, lean_object* v_00_u03b2_2027_, lean_object* v_x_2028_, lean_object* v_x_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x3f(v_00_u03b1_2026_, v_00_u03b2_2027_, v_x_2028_, v_x_2029_);
lean_dec(v_x_2028_);
return v_res_2030_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2(void){
_start:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2033_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_2034_ = lean_unsigned_to_nat(16u);
v___x_2035_ = lean_unsigned_to_nat(467u);
v___x_2036_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__0));
v___x_2037_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_2038_ = l_mkPanicMessageWithDecl(v___x_2037_, v___x_2036_, v___x_2035_, v___x_2034_, v___x_2033_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(lean_object* v_inst_2039_, lean_object* v_x_2040_, lean_object* v_x_2041_){
_start:
{
if (lean_obj_tag(v_x_2040_) == 0)
{
lean_object* v_k_2042_; lean_object* v_v_2043_; lean_object* v_l_2044_; lean_object* v_r_2045_; lean_object* v___y_2047_; lean_object* v___y_2053_; 
v_k_2042_ = lean_ctor_get(v_x_2040_, 1);
v_v_2043_ = lean_ctor_get(v_x_2040_, 2);
v_l_2044_ = lean_ctor_get(v_x_2040_, 3);
v_r_2045_ = lean_ctor_get(v_x_2040_, 4);
if (lean_obj_tag(v_l_2044_) == 0)
{
lean_object* v_size_2060_; 
v_size_2060_ = lean_ctor_get(v_l_2044_, 0);
v___y_2053_ = v_size_2060_;
goto v___jp_2052_;
}
else
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_unsigned_to_nat(0u);
v___y_2053_ = v___x_2061_;
goto v___jp_2052_;
}
v___jp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = lean_nat_sub(v_x_2041_, v___y_2047_);
lean_dec(v_x_2041_);
v___x_2049_ = lean_unsigned_to_nat(1u);
v___x_2050_ = lean_nat_sub(v___x_2048_, v___x_2049_);
lean_dec(v___x_2048_);
v_x_2040_ = v_r_2045_;
v_x_2041_ = v___x_2050_;
goto _start;
}
v___jp_2052_:
{
uint8_t v___x_2054_; 
v___x_2054_ = lean_nat_dec_lt(v_x_2041_, v___y_2053_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = lean_nat_dec_eq(v_x_2041_, v___y_2053_);
if (v___x_2055_ == 0)
{
if (lean_obj_tag(v_l_2044_) == 0)
{
lean_object* v_size_2056_; 
v_size_2056_ = lean_ctor_get(v_l_2044_, 0);
v___y_2047_ = v_size_2056_;
goto v___jp_2046_;
}
else
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_unsigned_to_nat(0u);
v___y_2047_ = v___x_2057_;
goto v___jp_2046_;
}
}
else
{
lean_object* v___x_2058_; 
lean_dec(v_x_2041_);
lean_inc(v_v_2043_);
lean_inc(v_k_2042_);
v___x_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2058_, 0, v_k_2042_);
lean_ctor_set(v___x_2058_, 1, v_v_2043_);
return v___x_2058_;
}
}
else
{
v_x_2040_ = v_l_2044_;
goto _start;
}
}
}
else
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec(v_x_2041_);
v___x_2062_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2, &l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2_once, _init_l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__2);
v___x_2063_ = l_panic___redArg(v_inst_2039_, v___x_2062_);
return v___x_2063_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_2064_, lean_object* v_x_2065_, lean_object* v_x_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2064_, v_x_2065_, v_x_2066_);
lean_dec(v_x_2065_);
lean_dec_ref(v_inst_2064_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(lean_object* v_00_u03b1_2068_, lean_object* v_00_u03b2_2069_, lean_object* v_inst_2070_, lean_object* v_x_2071_, lean_object* v_x_2072_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg(v_inst_2070_, v_x_2071_, v_x_2072_);
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_2074_, lean_object* v_00_u03b2_2075_, lean_object* v_inst_2076_, lean_object* v_x_2077_, lean_object* v_x_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21(v_00_u03b1_2074_, v_00_u03b2_2075_, v_inst_2076_, v_x_2077_, v_x_2078_);
lean_dec(v_x_2077_);
lean_dec_ref(v_inst_2076_);
return v_res_2079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(lean_object* v_x_2080_, lean_object* v_x_2081_, lean_object* v_x_2082_){
_start:
{
if (lean_obj_tag(v_x_2080_) == 0)
{
lean_object* v_k_2083_; lean_object* v_v_2084_; lean_object* v_l_2085_; lean_object* v_r_2086_; lean_object* v___y_2088_; lean_object* v___y_2094_; 
v_k_2083_ = lean_ctor_get(v_x_2080_, 1);
v_v_2084_ = lean_ctor_get(v_x_2080_, 2);
v_l_2085_ = lean_ctor_get(v_x_2080_, 3);
v_r_2086_ = lean_ctor_get(v_x_2080_, 4);
if (lean_obj_tag(v_l_2085_) == 0)
{
lean_object* v_size_2101_; 
v_size_2101_ = lean_ctor_get(v_l_2085_, 0);
v___y_2094_ = v_size_2101_;
goto v___jp_2093_;
}
else
{
lean_object* v___x_2102_; 
v___x_2102_ = lean_unsigned_to_nat(0u);
v___y_2094_ = v___x_2102_;
goto v___jp_2093_;
}
v___jp_2087_:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = lean_nat_sub(v_x_2081_, v___y_2088_);
lean_dec(v_x_2081_);
v___x_2090_ = lean_unsigned_to_nat(1u);
v___x_2091_ = lean_nat_sub(v___x_2089_, v___x_2090_);
lean_dec(v___x_2089_);
v_x_2080_ = v_r_2086_;
v_x_2081_ = v___x_2091_;
goto _start;
}
v___jp_2093_:
{
uint8_t v___x_2095_; 
v___x_2095_ = lean_nat_dec_lt(v_x_2081_, v___y_2094_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_nat_dec_eq(v_x_2081_, v___y_2094_);
if (v___x_2096_ == 0)
{
if (lean_obj_tag(v_l_2085_) == 0)
{
lean_object* v_size_2097_; 
v_size_2097_ = lean_ctor_get(v_l_2085_, 0);
v___y_2088_ = v_size_2097_;
goto v___jp_2087_;
}
else
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_unsigned_to_nat(0u);
v___y_2088_ = v___x_2098_;
goto v___jp_2087_;
}
}
else
{
lean_object* v___x_2099_; 
lean_dec(v_x_2081_);
lean_inc(v_v_2084_);
lean_inc(v_k_2083_);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v_k_2083_);
lean_ctor_set(v___x_2099_, 1, v_v_2084_);
return v___x_2099_;
}
}
else
{
v_x_2080_ = v_l_2085_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2081_);
lean_inc_ref(v_x_2082_);
return v_x_2082_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg___boxed(lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v_x_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2103_, v_x_2104_, v_x_2105_);
lean_dec_ref(v_x_2105_);
lean_dec(v_x_2103_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD(lean_object* v_00_u03b1_2107_, lean_object* v_00_u03b2_2108_, lean_object* v_x_2109_, lean_object* v_x_2110_, lean_object* v_x_2111_){
_start:
{
lean_object* v___x_2112_; 
v___x_2112_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD___redArg(v_x_2109_, v_x_2110_, v_x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_entryAtIdxD___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_00_u03b2_2114_, lean_object* v_x_2115_, lean_object* v_x_2116_, lean_object* v_x_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_Std_DTreeMap_Internal_Impl_entryAtIdxD(v_00_u03b1_2113_, v_00_u03b2_2114_, v_x_2115_, v_x_2116_, v_x_2117_);
lean_dec_ref(v_x_2117_);
lean_dec(v_x_2115_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(lean_object* v_x_2119_, lean_object* v_x_2120_){
_start:
{
lean_object* v_k_2121_; lean_object* v_l_2122_; lean_object* v_r_2123_; lean_object* v___y_2125_; lean_object* v___y_2131_; 
v_k_2121_ = lean_ctor_get(v_x_2119_, 1);
v_l_2122_ = lean_ctor_get(v_x_2119_, 3);
v_r_2123_ = lean_ctor_get(v_x_2119_, 4);
if (lean_obj_tag(v_l_2122_) == 0)
{
lean_object* v_size_2137_; 
v_size_2137_ = lean_ctor_get(v_l_2122_, 0);
v___y_2131_ = v_size_2137_;
goto v___jp_2130_;
}
else
{
lean_object* v___x_2138_; 
v___x_2138_ = lean_unsigned_to_nat(0u);
v___y_2131_ = v___x_2138_;
goto v___jp_2130_;
}
v___jp_2124_:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = lean_nat_sub(v_x_2120_, v___y_2125_);
lean_dec(v_x_2120_);
v___x_2127_ = lean_unsigned_to_nat(1u);
v___x_2128_ = lean_nat_sub(v___x_2126_, v___x_2127_);
lean_dec(v___x_2126_);
v_x_2119_ = v_r_2123_;
v_x_2120_ = v___x_2128_;
goto _start;
}
v___jp_2130_:
{
uint8_t v___x_2132_; 
v___x_2132_ = lean_nat_dec_lt(v_x_2120_, v___y_2131_);
if (v___x_2132_ == 0)
{
uint8_t v___x_2133_; 
v___x_2133_ = lean_nat_dec_eq(v_x_2120_, v___y_2131_);
if (v___x_2133_ == 0)
{
if (lean_obj_tag(v_l_2122_) == 0)
{
lean_object* v_size_2134_; 
v_size_2134_ = lean_ctor_get(v_l_2122_, 0);
v___y_2125_ = v_size_2134_;
goto v___jp_2124_;
}
else
{
lean_object* v___x_2135_; 
v___x_2135_ = lean_unsigned_to_nat(0u);
v___y_2125_ = v___x_2135_;
goto v___jp_2124_;
}
}
else
{
lean_dec(v_x_2120_);
lean_inc(v_k_2121_);
return v_k_2121_;
}
}
else
{
v_x_2119_ = v_l_2122_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg___boxed(lean_object* v_x_2139_, lean_object* v_x_2140_){
_start:
{
lean_object* v_res_2141_; 
v_res_2141_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2139_, v_x_2140_);
lean_dec(v_x_2139_);
return v_res_2141_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx(lean_object* v_00_u03b1_2142_, lean_object* v_00_u03b2_2143_, lean_object* v_x_2144_, lean_object* v_x_2145_, lean_object* v_x_2146_, lean_object* v_x_2147_){
_start:
{
lean_object* v___x_2148_; 
v___x_2148_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx___redArg(v_x_2144_, v_x_2146_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx___boxed(lean_object* v_00_u03b1_2149_, lean_object* v_00_u03b2_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_, lean_object* v_x_2153_, lean_object* v_x_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx(v_00_u03b1_2149_, v_00_u03b2_2150_, v_x_2151_, v_x_2152_, v_x_2153_, v_x_2154_);
lean_dec(v_x_2151_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(lean_object* v_x_2156_, lean_object* v_x_2157_){
_start:
{
if (lean_obj_tag(v_x_2156_) == 0)
{
lean_object* v_k_2158_; lean_object* v_l_2159_; lean_object* v_r_2160_; lean_object* v___y_2162_; lean_object* v___y_2168_; 
v_k_2158_ = lean_ctor_get(v_x_2156_, 1);
v_l_2159_ = lean_ctor_get(v_x_2156_, 3);
v_r_2160_ = lean_ctor_get(v_x_2156_, 4);
if (lean_obj_tag(v_l_2159_) == 0)
{
lean_object* v_size_2175_; 
v_size_2175_ = lean_ctor_get(v_l_2159_, 0);
v___y_2168_ = v_size_2175_;
goto v___jp_2167_;
}
else
{
lean_object* v___x_2176_; 
v___x_2176_ = lean_unsigned_to_nat(0u);
v___y_2168_ = v___x_2176_;
goto v___jp_2167_;
}
v___jp_2161_:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = lean_nat_sub(v_x_2157_, v___y_2162_);
lean_dec(v_x_2157_);
v___x_2164_ = lean_unsigned_to_nat(1u);
v___x_2165_ = lean_nat_sub(v___x_2163_, v___x_2164_);
lean_dec(v___x_2163_);
v_x_2156_ = v_r_2160_;
v_x_2157_ = v___x_2165_;
goto _start;
}
v___jp_2167_:
{
uint8_t v___x_2169_; 
v___x_2169_ = lean_nat_dec_lt(v_x_2157_, v___y_2168_);
if (v___x_2169_ == 0)
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_nat_dec_eq(v_x_2157_, v___y_2168_);
if (v___x_2170_ == 0)
{
if (lean_obj_tag(v_l_2159_) == 0)
{
lean_object* v_size_2171_; 
v_size_2171_ = lean_ctor_get(v_l_2159_, 0);
v___y_2162_ = v_size_2171_;
goto v___jp_2161_;
}
else
{
lean_object* v___x_2172_; 
v___x_2172_ = lean_unsigned_to_nat(0u);
v___y_2162_ = v___x_2172_;
goto v___jp_2161_;
}
}
else
{
lean_object* v___x_2173_; 
lean_dec(v_x_2157_);
lean_inc(v_k_2158_);
v___x_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2173_, 0, v_k_2158_);
return v___x_2173_;
}
}
else
{
v_x_2156_ = v_l_2159_;
goto _start;
}
}
}
else
{
lean_object* v___x_2177_; 
lean_dec(v_x_2157_);
v___x_2177_ = lean_box(0);
return v___x_2177_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg___boxed(lean_object* v_x_2178_, lean_object* v_x_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2178_, v_x_2179_);
lean_dec(v_x_2178_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(lean_object* v_00_u03b1_2181_, lean_object* v_00_u03b2_2182_, lean_object* v_x_2183_, lean_object* v_x_2184_){
_start:
{
lean_object* v___x_2185_; 
v___x_2185_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___redArg(v_x_2183_, v_x_2184_);
return v___x_2185_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f___boxed(lean_object* v_00_u03b1_2186_, lean_object* v_00_u03b2_2187_, lean_object* v_x_2188_, lean_object* v_x_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x3f(v_00_u03b1_2186_, v_00_u03b2_2187_, v_x_2188_, v_x_2189_);
lean_dec(v_x_2188_);
return v_res_2190_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; 
v___x_2192_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_2193_ = lean_unsigned_to_nat(16u);
v___x_2194_ = lean_unsigned_to_nat(503u);
v___x_2195_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__0));
v___x_2196_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_2197_ = l_mkPanicMessageWithDecl(v___x_2196_, v___x_2195_, v___x_2194_, v___x_2193_, v___x_2192_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(lean_object* v_inst_2198_, lean_object* v_x_2199_, lean_object* v_x_2200_){
_start:
{
if (lean_obj_tag(v_x_2199_) == 0)
{
lean_object* v_k_2201_; lean_object* v_l_2202_; lean_object* v_r_2203_; lean_object* v___y_2205_; lean_object* v___y_2211_; 
v_k_2201_ = lean_ctor_get(v_x_2199_, 1);
v_l_2202_ = lean_ctor_get(v_x_2199_, 3);
v_r_2203_ = lean_ctor_get(v_x_2199_, 4);
if (lean_obj_tag(v_l_2202_) == 0)
{
lean_object* v_size_2217_; 
v_size_2217_ = lean_ctor_get(v_l_2202_, 0);
v___y_2211_ = v_size_2217_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_unsigned_to_nat(0u);
v___y_2211_ = v___x_2218_;
goto v___jp_2210_;
}
v___jp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2206_ = lean_nat_sub(v_x_2200_, v___y_2205_);
lean_dec(v_x_2200_);
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_nat_sub(v___x_2206_, v___x_2207_);
lean_dec(v___x_2206_);
v_x_2199_ = v_r_2203_;
v_x_2200_ = v___x_2208_;
goto _start;
}
v___jp_2210_:
{
uint8_t v___x_2212_; 
v___x_2212_ = lean_nat_dec_lt(v_x_2200_, v___y_2211_);
if (v___x_2212_ == 0)
{
uint8_t v___x_2213_; 
v___x_2213_ = lean_nat_dec_eq(v_x_2200_, v___y_2211_);
if (v___x_2213_ == 0)
{
if (lean_obj_tag(v_l_2202_) == 0)
{
lean_object* v_size_2214_; 
v_size_2214_ = lean_ctor_get(v_l_2202_, 0);
v___y_2205_ = v_size_2214_;
goto v___jp_2204_;
}
else
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_unsigned_to_nat(0u);
v___y_2205_ = v___x_2215_;
goto v___jp_2204_;
}
}
else
{
lean_dec(v_x_2200_);
lean_inc(v_k_2201_);
return v_k_2201_;
}
}
else
{
v_x_2199_ = v_l_2202_;
goto _start;
}
}
}
else
{
lean_object* v___x_2219_; lean_object* v___x_2220_; 
lean_dec(v_x_2200_);
v___x_2219_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___closed__1);
v___x_2220_ = l_panic___redArg(v_inst_2198_, v___x_2219_);
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg___boxed(lean_object* v_inst_2221_, lean_object* v_x_2222_, lean_object* v_x_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2221_, v_x_2222_, v_x_2223_);
lean_dec(v_x_2222_);
lean_dec(v_inst_2221_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(lean_object* v_00_u03b1_2225_, lean_object* v_00_u03b2_2226_, lean_object* v_inst_2227_, lean_object* v_x_2228_, lean_object* v_x_2229_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___redArg(v_inst_2227_, v_x_2228_, v_x_2229_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_00_u03b2_2232_, lean_object* v_inst_2233_, lean_object* v_x_2234_, lean_object* v_x_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_Std_DTreeMap_Internal_Impl_keyAtIdx_x21(v_00_u03b1_2231_, v_00_u03b2_2232_, v_inst_2233_, v_x_2234_, v_x_2235_);
lean_dec(v_x_2234_);
lean_dec(v_inst_2233_);
return v_res_2236_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(lean_object* v_x_2237_, lean_object* v_x_2238_, lean_object* v_x_2239_){
_start:
{
if (lean_obj_tag(v_x_2237_) == 0)
{
lean_object* v_k_2240_; lean_object* v_l_2241_; lean_object* v_r_2242_; lean_object* v___y_2244_; lean_object* v___y_2250_; 
v_k_2240_ = lean_ctor_get(v_x_2237_, 1);
v_l_2241_ = lean_ctor_get(v_x_2237_, 3);
v_r_2242_ = lean_ctor_get(v_x_2237_, 4);
if (lean_obj_tag(v_l_2241_) == 0)
{
lean_object* v_size_2256_; 
v_size_2256_ = lean_ctor_get(v_l_2241_, 0);
v___y_2250_ = v_size_2256_;
goto v___jp_2249_;
}
else
{
lean_object* v___x_2257_; 
v___x_2257_ = lean_unsigned_to_nat(0u);
v___y_2250_ = v___x_2257_;
goto v___jp_2249_;
}
v___jp_2243_:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_nat_sub(v_x_2238_, v___y_2244_);
lean_dec(v_x_2238_);
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = lean_nat_sub(v___x_2245_, v___x_2246_);
lean_dec(v___x_2245_);
v_x_2237_ = v_r_2242_;
v_x_2238_ = v___x_2247_;
goto _start;
}
v___jp_2249_:
{
uint8_t v___x_2251_; 
v___x_2251_ = lean_nat_dec_lt(v_x_2238_, v___y_2250_);
if (v___x_2251_ == 0)
{
uint8_t v___x_2252_; 
v___x_2252_ = lean_nat_dec_eq(v_x_2238_, v___y_2250_);
if (v___x_2252_ == 0)
{
if (lean_obj_tag(v_l_2241_) == 0)
{
lean_object* v_size_2253_; 
v_size_2253_ = lean_ctor_get(v_l_2241_, 0);
v___y_2244_ = v_size_2253_;
goto v___jp_2243_;
}
else
{
lean_object* v___x_2254_; 
v___x_2254_ = lean_unsigned_to_nat(0u);
v___y_2244_ = v___x_2254_;
goto v___jp_2243_;
}
}
else
{
lean_dec(v_x_2238_);
lean_inc(v_k_2240_);
return v_k_2240_;
}
}
else
{
v_x_2237_ = v_l_2241_;
goto _start;
}
}
}
else
{
lean_dec(v_x_2238_);
lean_inc(v_x_2239_);
return v_x_2239_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg___boxed(lean_object* v_x_2258_, lean_object* v_x_2259_, lean_object* v_x_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2258_, v_x_2259_, v_x_2260_);
lean_dec(v_x_2260_);
lean_dec(v_x_2258_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD(lean_object* v_00_u03b1_2262_, lean_object* v_00_u03b2_2263_, lean_object* v_x_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_){
_start:
{
lean_object* v___x_2267_; 
v___x_2267_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD___redArg(v_x_2264_, v_x_2265_, v_x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_keyAtIdxD___boxed(lean_object* v_00_u03b1_2268_, lean_object* v_00_u03b2_2269_, lean_object* v_x_2270_, lean_object* v_x_2271_, lean_object* v_x_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Std_DTreeMap_Internal_Impl_keyAtIdxD(v_00_u03b1_2268_, v_00_u03b2_2269_, v_x_2270_, v_x_2271_, v_x_2272_);
lean_dec(v_x_2272_);
lean_dec(v_x_2270_);
return v_res_2273_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(lean_object* v_inst_2274_, lean_object* v_k_2275_, lean_object* v_best_2276_, lean_object* v_a_2277_){
_start:
{
if (lean_obj_tag(v_a_2277_) == 0)
{
lean_object* v_k_2278_; lean_object* v_v_2279_; lean_object* v_l_2280_; lean_object* v_r_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_k_2278_ = lean_ctor_get(v_a_2277_, 1);
lean_inc_n(v_k_2278_, 2);
v_v_2279_ = lean_ctor_get(v_a_2277_, 2);
lean_inc(v_v_2279_);
v_l_2280_ = lean_ctor_get(v_a_2277_, 3);
lean_inc(v_l_2280_);
v_r_2281_ = lean_ctor_get(v_a_2277_, 4);
lean_inc(v_r_2281_);
lean_dec_ref_known(v_a_2277_, 5);
lean_inc_ref(v_inst_2274_);
lean_inc(v_k_2275_);
v___x_2282_ = lean_apply_2(v_inst_2274_, v_k_2275_, v_k_2278_);
v___x_2283_ = lean_unbox(v___x_2282_);
switch(v___x_2283_)
{
case 0:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
lean_dec(v_r_2281_);
lean_dec(v_best_2276_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v_k_2278_);
lean_ctor_set(v___x_2284_, 1, v_v_2279_);
v___x_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
v_best_2276_ = v___x_2285_;
v_a_2277_ = v_l_2280_;
goto _start;
}
case 1:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
lean_dec(v_r_2281_);
lean_dec(v_l_2280_);
lean_dec(v_best_2276_);
lean_dec(v_k_2275_);
lean_dec_ref(v_inst_2274_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_k_2278_);
lean_ctor_set(v___x_2287_, 1, v_v_2279_);
v___x_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2287_);
return v___x_2288_;
}
default: 
{
lean_dec(v_l_2280_);
lean_dec(v_v_2279_);
lean_dec(v_k_2278_);
v_a_2277_ = v_r_2281_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2275_);
lean_dec_ref(v_inst_2274_);
return v_best_2276_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go(lean_object* v_00_u03b1_2290_, lean_object* v_00_u03b2_2291_, lean_object* v_inst_2292_, lean_object* v_k_2293_, lean_object* v_best_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2296_; 
v___x_2296_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2292_, v_k_2293_, v_best_2294_, v_a_2295_);
return v___x_2296_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f___redArg(lean_object* v_inst_2297_, lean_object* v_k_2298_, lean_object* v_a_2299_){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; 
v___x_2300_ = lean_box(0);
v___x_2301_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2297_, v_k_2298_, v___x_2300_, v_a_2299_);
return v___x_2301_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f(lean_object* v_00_u03b1_2302_, lean_object* v_00_u03b2_2303_, lean_object* v_inst_2304_, lean_object* v_k_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2307_ = lean_box(0);
v___x_2308_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2304_, v_k_2305_, v___x_2307_, v_a_2306_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(lean_object* v_inst_2309_, lean_object* v_k_2310_, lean_object* v_best_2311_, lean_object* v_a_2312_){
_start:
{
if (lean_obj_tag(v_a_2312_) == 0)
{
lean_object* v_k_2313_; lean_object* v_v_2314_; lean_object* v_l_2315_; lean_object* v_r_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; 
v_k_2313_ = lean_ctor_get(v_a_2312_, 1);
lean_inc_n(v_k_2313_, 2);
v_v_2314_ = lean_ctor_get(v_a_2312_, 2);
lean_inc(v_v_2314_);
v_l_2315_ = lean_ctor_get(v_a_2312_, 3);
lean_inc(v_l_2315_);
v_r_2316_ = lean_ctor_get(v_a_2312_, 4);
lean_inc(v_r_2316_);
lean_dec_ref_known(v_a_2312_, 5);
lean_inc_ref(v_inst_2309_);
lean_inc(v_k_2310_);
v___x_2317_ = lean_apply_2(v_inst_2309_, v_k_2310_, v_k_2313_);
v___x_2318_ = lean_unbox(v___x_2317_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; lean_object* v___x_2320_; 
lean_dec(v_r_2316_);
lean_dec(v_best_2311_);
v___x_2319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2319_, 0, v_k_2313_);
lean_ctor_set(v___x_2319_, 1, v_v_2314_);
v___x_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
v_best_2311_ = v___x_2320_;
v_a_2312_ = v_l_2315_;
goto _start;
}
else
{
lean_dec(v_l_2315_);
lean_dec(v_v_2314_);
lean_dec(v_k_2313_);
v_a_2312_ = v_r_2316_;
goto _start;
}
}
else
{
lean_dec(v_k_2310_);
lean_dec_ref(v_inst_2309_);
return v_best_2311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go(lean_object* v_00_u03b1_2323_, lean_object* v_00_u03b2_2324_, lean_object* v_inst_2325_, lean_object* v_k_2326_, lean_object* v_best_2327_, lean_object* v_a_2328_){
_start:
{
lean_object* v___x_2329_; 
v___x_2329_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2325_, v_k_2326_, v_best_2327_, v_a_2328_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f___redArg(lean_object* v_inst_2330_, lean_object* v_k_2331_, lean_object* v_a_2332_){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = lean_box(0);
v___x_2334_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2330_, v_k_2331_, v___x_2333_, v_a_2332_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f(lean_object* v_00_u03b1_2335_, lean_object* v_00_u03b2_2336_, lean_object* v_inst_2337_, lean_object* v_k_2338_, lean_object* v_a_2339_){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; 
v___x_2340_ = lean_box(0);
v___x_2341_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2337_, v_k_2338_, v___x_2340_, v_a_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(lean_object* v_inst_2342_, lean_object* v_k_2343_, lean_object* v_best_2344_, lean_object* v_a_2345_){
_start:
{
if (lean_obj_tag(v_a_2345_) == 0)
{
lean_object* v_k_2346_; lean_object* v_v_2347_; lean_object* v_l_2348_; lean_object* v_r_2349_; lean_object* v___x_2350_; uint8_t v___x_2351_; 
v_k_2346_ = lean_ctor_get(v_a_2345_, 1);
lean_inc_n(v_k_2346_, 2);
v_v_2347_ = lean_ctor_get(v_a_2345_, 2);
lean_inc(v_v_2347_);
v_l_2348_ = lean_ctor_get(v_a_2345_, 3);
lean_inc(v_l_2348_);
v_r_2349_ = lean_ctor_get(v_a_2345_, 4);
lean_inc(v_r_2349_);
lean_dec_ref_known(v_a_2345_, 5);
lean_inc_ref(v_inst_2342_);
lean_inc(v_k_2343_);
v___x_2350_ = lean_apply_2(v_inst_2342_, v_k_2343_, v_k_2346_);
v___x_2351_ = lean_unbox(v___x_2350_);
switch(v___x_2351_)
{
case 0:
{
lean_dec(v_r_2349_);
lean_dec(v_v_2347_);
lean_dec(v_k_2346_);
v_a_2345_ = v_l_2348_;
goto _start;
}
case 1:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
lean_dec(v_r_2349_);
lean_dec(v_l_2348_);
lean_dec(v_best_2344_);
lean_dec(v_k_2343_);
lean_dec_ref(v_inst_2342_);
v___x_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2353_, 0, v_k_2346_);
lean_ctor_set(v___x_2353_, 1, v_v_2347_);
v___x_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
return v___x_2354_;
}
default: 
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
lean_dec(v_l_2348_);
lean_dec(v_best_2344_);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v_k_2346_);
lean_ctor_set(v___x_2355_, 1, v_v_2347_);
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
v_best_2344_ = v___x_2356_;
v_a_2345_ = v_r_2349_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2343_);
lean_dec_ref(v_inst_2342_);
return v_best_2344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go(lean_object* v_00_u03b1_2358_, lean_object* v_00_u03b2_2359_, lean_object* v_inst_2360_, lean_object* v_k_2361_, lean_object* v_best_2362_, lean_object* v_a_2363_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2360_, v_k_2361_, v_best_2362_, v_a_2363_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f___redArg(lean_object* v_inst_2365_, lean_object* v_k_2366_, lean_object* v_a_2367_){
_start:
{
lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2368_ = lean_box(0);
v___x_2369_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2365_, v_k_2366_, v___x_2368_, v_a_2367_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f(lean_object* v_00_u03b1_2370_, lean_object* v_00_u03b2_2371_, lean_object* v_inst_2372_, lean_object* v_k_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2375_ = lean_box(0);
v___x_2376_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2372_, v_k_2373_, v___x_2375_, v_a_2374_);
return v___x_2376_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(lean_object* v_inst_2377_, lean_object* v_k_2378_, lean_object* v_best_2379_, lean_object* v_a_2380_){
_start:
{
if (lean_obj_tag(v_a_2380_) == 0)
{
lean_object* v_k_2381_; lean_object* v_v_2382_; lean_object* v_l_2383_; lean_object* v_r_2384_; lean_object* v___x_2385_; uint8_t v___x_2386_; 
v_k_2381_ = lean_ctor_get(v_a_2380_, 1);
lean_inc_n(v_k_2381_, 2);
v_v_2382_ = lean_ctor_get(v_a_2380_, 2);
lean_inc(v_v_2382_);
v_l_2383_ = lean_ctor_get(v_a_2380_, 3);
lean_inc(v_l_2383_);
v_r_2384_ = lean_ctor_get(v_a_2380_, 4);
lean_inc(v_r_2384_);
lean_dec_ref_known(v_a_2380_, 5);
lean_inc_ref(v_inst_2377_);
lean_inc(v_k_2378_);
v___x_2385_ = lean_apply_2(v_inst_2377_, v_k_2378_, v_k_2381_);
v___x_2386_ = lean_unbox(v___x_2385_);
if (v___x_2386_ == 2)
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
lean_dec(v_l_2383_);
lean_dec(v_best_2379_);
v___x_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2387_, 0, v_k_2381_);
lean_ctor_set(v___x_2387_, 1, v_v_2382_);
v___x_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2388_, 0, v___x_2387_);
v_best_2379_ = v___x_2388_;
v_a_2380_ = v_r_2384_;
goto _start;
}
else
{
lean_dec(v_r_2384_);
lean_dec(v_v_2382_);
lean_dec(v_k_2381_);
v_a_2380_ = v_l_2383_;
goto _start;
}
}
else
{
lean_dec(v_k_2378_);
lean_dec_ref(v_inst_2377_);
return v_best_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go(lean_object* v_00_u03b1_2391_, lean_object* v_00_u03b2_2392_, lean_object* v_inst_2393_, lean_object* v_k_2394_, lean_object* v_best_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v___x_2397_; 
v___x_2397_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2393_, v_k_2394_, v_best_2395_, v_a_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f___redArg(lean_object* v_inst_2398_, lean_object* v_k_2399_, lean_object* v_a_2400_){
_start:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2401_ = lean_box(0);
v___x_2402_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2398_, v_k_2399_, v___x_2401_, v_a_2400_);
return v___x_2402_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f(lean_object* v_00_u03b1_2403_, lean_object* v_00_u03b2_2404_, lean_object* v_inst_2405_, lean_object* v_k_2406_, lean_object* v_a_2407_){
_start:
{
lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2408_ = lean_box(0);
v___x_2409_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2405_, v_k_2406_, v___x_2408_, v_a_2407_);
return v___x_2409_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2413_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__2));
v___x_2414_ = lean_unsigned_to_nat(14u);
v___x_2415_ = lean_unsigned_to_nat(22u);
v___x_2416_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__1));
v___x_2417_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__0));
v___x_2418_ = l_mkPanicMessageWithDecl(v___x_2417_, v___x_2416_, v___x_2415_, v___x_2414_, v___x_2413_);
return v___x_2418_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(lean_object* v_inst_2419_, lean_object* v_inst_2420_, lean_object* v_k_2421_, lean_object* v_t_2422_){
_start:
{
lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2423_ = lean_box(0);
v___x_2424_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2419_, v_k_2421_, v___x_2423_, v_t_2422_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2425_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2426_ = l_panic___redArg(v_inst_2420_, v___x_2425_);
return v___x_2426_;
}
else
{
lean_object* v_val_2427_; 
v_val_2427_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_val_2427_);
lean_dec_ref_known(v___x_2424_, 1);
return v_val_2427_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___boxed(lean_object* v_inst_2428_, lean_object* v_inst_2429_, lean_object* v_k_2430_, lean_object* v_t_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg(v_inst_2428_, v_inst_2429_, v_k_2430_, v_t_2431_);
lean_dec_ref(v_inst_2429_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(lean_object* v_00_u03b1_2433_, lean_object* v_00_u03b2_2434_, lean_object* v_inst_2435_, lean_object* v_inst_2436_, lean_object* v_k_2437_, lean_object* v_t_2438_){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; 
v___x_2439_ = lean_box(0);
v___x_2440_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2435_, v_k_2437_, v___x_2439_, v_t_2438_);
if (lean_obj_tag(v___x_2440_) == 0)
{
lean_object* v___x_2441_; lean_object* v___x_2442_; 
v___x_2441_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2442_ = l_panic___redArg(v_inst_2436_, v___x_2441_);
return v___x_2442_;
}
else
{
lean_object* v_val_2443_; 
v_val_2443_ = lean_ctor_get(v___x_2440_, 0);
lean_inc(v_val_2443_);
lean_dec_ref_known(v___x_2440_, 1);
return v_val_2443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___boxed(lean_object* v_00_u03b1_2444_, lean_object* v_00_u03b2_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_, lean_object* v_k_2448_, lean_object* v_t_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x21(v_00_u03b1_2444_, v_00_u03b2_2445_, v_inst_2446_, v_inst_2447_, v_k_2448_, v_t_2449_);
lean_dec_ref(v_inst_2447_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(lean_object* v_inst_2451_, lean_object* v_inst_2452_, lean_object* v_k_2453_, lean_object* v_t_2454_){
_start:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; 
v___x_2455_ = lean_box(0);
v___x_2456_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2451_, v_k_2453_, v___x_2455_, v_t_2454_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2458_ = l_panic___redArg(v_inst_2452_, v___x_2457_);
return v___x_2458_;
}
else
{
lean_object* v_val_2459_; 
v_val_2459_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_val_2459_);
lean_dec_ref_known(v___x_2456_, 1);
return v_val_2459_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg___boxed(lean_object* v_inst_2460_, lean_object* v_inst_2461_, lean_object* v_k_2462_, lean_object* v_t_2463_){
_start:
{
lean_object* v_res_2464_; 
v_res_2464_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___redArg(v_inst_2460_, v_inst_2461_, v_k_2462_, v_t_2463_);
lean_dec_ref(v_inst_2461_);
return v_res_2464_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(lean_object* v_00_u03b1_2465_, lean_object* v_00_u03b2_2466_, lean_object* v_inst_2467_, lean_object* v_inst_2468_, lean_object* v_k_2469_, lean_object* v_t_2470_){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = lean_box(0);
v___x_2472_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2467_, v_k_2469_, v___x_2471_, v_t_2470_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v___x_2473_; lean_object* v___x_2474_; 
v___x_2473_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2474_ = l_panic___redArg(v_inst_2468_, v___x_2473_);
return v___x_2474_;
}
else
{
lean_object* v_val_2475_; 
v_val_2475_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_val_2475_);
lean_dec_ref_known(v___x_2472_, 1);
return v_val_2475_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT_x21___boxed(lean_object* v_00_u03b1_2476_, lean_object* v_00_u03b2_2477_, lean_object* v_inst_2478_, lean_object* v_inst_2479_, lean_object* v_k_2480_, lean_object* v_t_2481_){
_start:
{
lean_object* v_res_2482_; 
v_res_2482_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x21(v_00_u03b1_2476_, v_00_u03b2_2477_, v_inst_2478_, v_inst_2479_, v_k_2480_, v_t_2481_);
lean_dec_ref(v_inst_2479_);
return v_res_2482_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(lean_object* v_inst_2483_, lean_object* v_inst_2484_, lean_object* v_k_2485_, lean_object* v_t_2486_){
_start:
{
lean_object* v___x_2487_; lean_object* v___x_2488_; 
v___x_2487_ = lean_box(0);
v___x_2488_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2483_, v_k_2485_, v___x_2487_, v_t_2486_);
if (lean_obj_tag(v___x_2488_) == 0)
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2490_ = l_panic___redArg(v_inst_2484_, v___x_2489_);
return v___x_2490_;
}
else
{
lean_object* v_val_2491_; 
v_val_2491_ = lean_ctor_get(v___x_2488_, 0);
lean_inc(v_val_2491_);
lean_dec_ref_known(v___x_2488_, 1);
return v_val_2491_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg___boxed(lean_object* v_inst_2492_, lean_object* v_inst_2493_, lean_object* v_k_2494_, lean_object* v_t_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___redArg(v_inst_2492_, v_inst_2493_, v_k_2494_, v_t_2495_);
lean_dec_ref(v_inst_2493_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(lean_object* v_00_u03b1_2497_, lean_object* v_00_u03b2_2498_, lean_object* v_inst_2499_, lean_object* v_inst_2500_, lean_object* v_k_2501_, lean_object* v_t_2502_){
_start:
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2503_ = lean_box(0);
v___x_2504_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2499_, v_k_2501_, v___x_2503_, v_t_2502_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2506_ = l_panic___redArg(v_inst_2500_, v___x_2505_);
return v___x_2506_;
}
else
{
lean_object* v_val_2507_; 
v_val_2507_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_val_2507_);
lean_dec_ref_known(v___x_2504_, 1);
return v_val_2507_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE_x21___boxed(lean_object* v_00_u03b1_2508_, lean_object* v_00_u03b2_2509_, lean_object* v_inst_2510_, lean_object* v_inst_2511_, lean_object* v_k_2512_, lean_object* v_t_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x21(v_00_u03b1_2508_, v_00_u03b2_2509_, v_inst_2510_, v_inst_2511_, v_k_2512_, v_t_2513_);
lean_dec_ref(v_inst_2511_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(lean_object* v_inst_2515_, lean_object* v_inst_2516_, lean_object* v_k_2517_, lean_object* v_t_2518_){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; 
v___x_2519_ = lean_box(0);
v___x_2520_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2515_, v_k_2517_, v___x_2519_, v_t_2518_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2522_ = l_panic___redArg(v_inst_2516_, v___x_2521_);
return v___x_2522_;
}
else
{
lean_object* v_val_2523_; 
v_val_2523_ = lean_ctor_get(v___x_2520_, 0);
lean_inc(v_val_2523_);
lean_dec_ref_known(v___x_2520_, 1);
return v_val_2523_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg___boxed(lean_object* v_inst_2524_, lean_object* v_inst_2525_, lean_object* v_k_2526_, lean_object* v_t_2527_){
_start:
{
lean_object* v_res_2528_; 
v_res_2528_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___redArg(v_inst_2524_, v_inst_2525_, v_k_2526_, v_t_2527_);
lean_dec_ref(v_inst_2525_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(lean_object* v_00_u03b1_2529_, lean_object* v_00_u03b2_2530_, lean_object* v_inst_2531_, lean_object* v_inst_2532_, lean_object* v_k_2533_, lean_object* v_t_2534_){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_box(0);
v___x_2536_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2531_, v_k_2533_, v___x_2535_, v_t_2534_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2538_ = l_panic___redArg(v_inst_2532_, v___x_2537_);
return v___x_2538_;
}
else
{
lean_object* v_val_2539_; 
v_val_2539_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_val_2539_);
lean_dec_ref_known(v___x_2536_, 1);
return v_val_2539_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT_x21___boxed(lean_object* v_00_u03b1_2540_, lean_object* v_00_u03b2_2541_, lean_object* v_inst_2542_, lean_object* v_inst_2543_, lean_object* v_k_2544_, lean_object* v_t_2545_){
_start:
{
lean_object* v_res_2546_; 
v_res_2546_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x21(v_00_u03b1_2540_, v_00_u03b2_2541_, v_inst_2542_, v_inst_2543_, v_k_2544_, v_t_2545_);
lean_dec_ref(v_inst_2543_);
return v_res_2546_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(lean_object* v_inst_2547_, lean_object* v_k_2548_, lean_object* v_t_2549_, lean_object* v_fallback_2550_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg___boxed(lean_object* v_inst_2554_, lean_object* v_k_2555_, lean_object* v_t_2556_, lean_object* v_fallback_2557_){
_start:
{
lean_object* v_res_2558_; 
v_res_2558_ = l_Std_DTreeMap_Internal_Impl_getEntryGED___redArg(v_inst_2554_, v_k_2555_, v_t_2556_, v_fallback_2557_);
lean_dec_ref(v_fallback_2557_);
return v_res_2558_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED(lean_object* v_00_u03b1_2559_, lean_object* v_00_u03b2_2560_, lean_object* v_inst_2561_, lean_object* v_k_2562_, lean_object* v_t_2563_, lean_object* v_fallback_2564_){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_box(0);
v___x_2566_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2561_, v_k_2562_, v___x_2565_, v_t_2563_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGED___boxed(lean_object* v_00_u03b1_2568_, lean_object* v_00_u03b2_2569_, lean_object* v_inst_2570_, lean_object* v_k_2571_, lean_object* v_t_2572_, lean_object* v_fallback_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Std_DTreeMap_Internal_Impl_getEntryGED(v_00_u03b1_2568_, v_00_u03b2_2569_, v_inst_2570_, v_k_2571_, v_t_2572_, v_fallback_2573_);
lean_dec_ref(v_fallback_2573_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(lean_object* v_inst_2575_, lean_object* v_k_2576_, lean_object* v_t_2577_, lean_object* v_fallback_2578_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg___boxed(lean_object* v_inst_2582_, lean_object* v_k_2583_, lean_object* v_t_2584_, lean_object* v_fallback_2585_){
_start:
{
lean_object* v_res_2586_; 
v_res_2586_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD___redArg(v_inst_2582_, v_k_2583_, v_t_2584_, v_fallback_2585_);
lean_dec_ref(v_fallback_2585_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD(lean_object* v_00_u03b1_2587_, lean_object* v_00_u03b2_2588_, lean_object* v_inst_2589_, lean_object* v_k_2590_, lean_object* v_t_2591_, lean_object* v_fallback_2592_){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2593_ = lean_box(0);
v___x_2594_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2589_, v_k_2590_, v___x_2593_, v_t_2591_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGTD___boxed(lean_object* v_00_u03b1_2596_, lean_object* v_00_u03b2_2597_, lean_object* v_inst_2598_, lean_object* v_k_2599_, lean_object* v_t_2600_, lean_object* v_fallback_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Std_DTreeMap_Internal_Impl_getEntryGTD(v_00_u03b1_2596_, v_00_u03b2_2597_, v_inst_2598_, v_k_2599_, v_t_2600_, v_fallback_2601_);
lean_dec_ref(v_fallback_2601_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(lean_object* v_inst_2603_, lean_object* v_k_2604_, lean_object* v_t_2605_, lean_object* v_fallback_2606_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg___boxed(lean_object* v_inst_2610_, lean_object* v_k_2611_, lean_object* v_t_2612_, lean_object* v_fallback_2613_){
_start:
{
lean_object* v_res_2614_; 
v_res_2614_ = l_Std_DTreeMap_Internal_Impl_getEntryLED___redArg(v_inst_2610_, v_k_2611_, v_t_2612_, v_fallback_2613_);
lean_dec_ref(v_fallback_2613_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED(lean_object* v_00_u03b1_2615_, lean_object* v_00_u03b2_2616_, lean_object* v_inst_2617_, lean_object* v_k_2618_, lean_object* v_t_2619_, lean_object* v_fallback_2620_){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_box(0);
v___x_2622_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2617_, v_k_2618_, v___x_2621_, v_t_2619_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLED___boxed(lean_object* v_00_u03b1_2624_, lean_object* v_00_u03b2_2625_, lean_object* v_inst_2626_, lean_object* v_k_2627_, lean_object* v_t_2628_, lean_object* v_fallback_2629_){
_start:
{
lean_object* v_res_2630_; 
v_res_2630_ = l_Std_DTreeMap_Internal_Impl_getEntryLED(v_00_u03b1_2624_, v_00_u03b2_2625_, v_inst_2626_, v_k_2627_, v_t_2628_, v_fallback_2629_);
lean_dec_ref(v_fallback_2629_);
return v_res_2630_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(lean_object* v_inst_2631_, lean_object* v_k_2632_, lean_object* v_t_2633_, lean_object* v_fallback_2634_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg___boxed(lean_object* v_inst_2638_, lean_object* v_k_2639_, lean_object* v_t_2640_, lean_object* v_fallback_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD___redArg(v_inst_2638_, v_k_2639_, v_t_2640_, v_fallback_2641_);
lean_dec_ref(v_fallback_2641_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD(lean_object* v_00_u03b1_2643_, lean_object* v_00_u03b2_2644_, lean_object* v_inst_2645_, lean_object* v_k_2646_, lean_object* v_t_2647_, lean_object* v_fallback_2648_){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_box(0);
v___x_2650_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2645_, v_k_2646_, v___x_2649_, v_t_2647_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_inc_ref(v_fallback_2648_);
return v_fallback_2648_;
}
else
{
lean_object* v_val_2651_; 
v_val_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_val_2651_);
lean_dec_ref_known(v___x_2650_, 1);
return v_val_2651_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLTD___boxed(lean_object* v_00_u03b1_2652_, lean_object* v_00_u03b2_2653_, lean_object* v_inst_2654_, lean_object* v_k_2655_, lean_object* v_t_2656_, lean_object* v_fallback_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l_Std_DTreeMap_Internal_Impl_getEntryLTD(v_00_u03b1_2652_, v_00_u03b2_2653_, v_inst_2654_, v_k_2655_, v_t_2656_, v_fallback_2657_);
lean_dec_ref(v_fallback_2657_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(lean_object* v_inst_2659_, lean_object* v_k_2660_, lean_object* v_x_2661_){
_start:
{
lean_object* v_k_2662_; lean_object* v_v_2663_; lean_object* v_l_2664_; lean_object* v_r_2665_; lean_object* v___x_2666_; uint8_t v___x_2667_; 
v_k_2662_ = lean_ctor_get(v_x_2661_, 1);
lean_inc_n(v_k_2662_, 2);
v_v_2663_ = lean_ctor_get(v_x_2661_, 2);
lean_inc(v_v_2663_);
v_l_2664_ = lean_ctor_get(v_x_2661_, 3);
lean_inc(v_l_2664_);
v_r_2665_ = lean_ctor_get(v_x_2661_, 4);
lean_inc(v_r_2665_);
lean_dec(v_x_2661_);
lean_inc_ref(v_inst_2659_);
lean_inc(v_k_2660_);
v___x_2666_ = lean_apply_2(v_inst_2659_, v_k_2660_, v_k_2662_);
v___x_2667_ = lean_unbox(v___x_2666_);
switch(v___x_2667_)
{
case 0:
{
lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec(v_r_2665_);
v___x_2668_ = lean_box(0);
v___x_2669_ = l_Std_DTreeMap_Internal_Impl_getEntryGE_x3f_go___redArg(v_inst_2659_, v_k_2660_, v___x_2668_, v_l_2664_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v___x_2670_; 
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v_k_2662_);
lean_ctor_set(v___x_2670_, 1, v_v_2663_);
return v___x_2670_;
}
else
{
lean_object* v_val_2671_; 
lean_dec(v_v_2663_);
lean_dec(v_k_2662_);
v_val_2671_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_val_2671_);
lean_dec_ref_known(v___x_2669_, 1);
return v_val_2671_;
}
}
case 1:
{
lean_object* v___x_2672_; 
lean_dec(v_r_2665_);
lean_dec(v_l_2664_);
lean_dec(v_k_2660_);
lean_dec_ref(v_inst_2659_);
v___x_2672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2672_, 0, v_k_2662_);
lean_ctor_set(v___x_2672_, 1, v_v_2663_);
return v___x_2672_;
}
default: 
{
lean_dec(v_l_2664_);
lean_dec(v_v_2663_);
lean_dec(v_k_2662_);
v_x_2661_ = v_r_2665_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGE(lean_object* v_00_u03b1_2674_, lean_object* v_00_u03b2_2675_, lean_object* v_inst_2676_, lean_object* v_inst_2677_, lean_object* v_k_2678_, lean_object* v_x_2679_, lean_object* v_x_2680_, lean_object* v_x_2681_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l_Std_DTreeMap_Internal_Impl_getEntryGE___redArg(v_inst_2676_, v_k_2678_, v_x_2679_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(lean_object* v_inst_2683_, lean_object* v_k_2684_, lean_object* v_x_2685_){
_start:
{
lean_object* v_k_2686_; lean_object* v_v_2687_; lean_object* v_l_2688_; lean_object* v_r_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v_k_2686_ = lean_ctor_get(v_x_2685_, 1);
lean_inc_n(v_k_2686_, 2);
v_v_2687_ = lean_ctor_get(v_x_2685_, 2);
lean_inc(v_v_2687_);
v_l_2688_ = lean_ctor_get(v_x_2685_, 3);
lean_inc(v_l_2688_);
v_r_2689_ = lean_ctor_get(v_x_2685_, 4);
lean_inc(v_r_2689_);
lean_dec(v_x_2685_);
lean_inc_ref(v_inst_2683_);
lean_inc(v_k_2684_);
v___x_2690_ = lean_apply_2(v_inst_2683_, v_k_2684_, v_k_2686_);
v___x_2691_ = lean_obj_tag_nat(v___x_2690_);
v___x_2692_ = lean_unsigned_to_nat(0u);
v___x_2693_ = lean_nat_dec_eq(v___x_2691_, v___x_2692_);
if (v___x_2693_ == 0)
{
lean_dec(v_l_2688_);
lean_dec(v_v_2687_);
lean_dec(v_k_2686_);
v_x_2685_ = v_r_2689_;
goto _start;
}
else
{
lean_object* v___x_2695_; lean_object* v___x_2696_; 
lean_dec(v_r_2689_);
v___x_2695_ = lean_box(0);
v___x_2696_ = l_Std_DTreeMap_Internal_Impl_getEntryGT_x3f_go___redArg(v_inst_2683_, v_k_2684_, v___x_2695_, v_l_2688_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v_k_2686_);
lean_ctor_set(v___x_2697_, 1, v_v_2687_);
return v___x_2697_;
}
else
{
lean_object* v_val_2698_; 
lean_dec(v_v_2687_);
lean_dec(v_k_2686_);
v_val_2698_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_val_2698_);
lean_dec_ref_known(v___x_2696_, 1);
return v_val_2698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryGT(lean_object* v_00_u03b1_2699_, lean_object* v_00_u03b2_2700_, lean_object* v_inst_2701_, lean_object* v_inst_2702_, lean_object* v_k_2703_, lean_object* v_x_2704_, lean_object* v_x_2705_, lean_object* v_x_2706_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Std_DTreeMap_Internal_Impl_getEntryGT___redArg(v_inst_2701_, v_k_2703_, v_x_2704_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(lean_object* v_inst_2708_, lean_object* v_k_2709_, lean_object* v_x_2710_){
_start:
{
lean_object* v_k_2711_; lean_object* v_v_2712_; lean_object* v_l_2713_; lean_object* v_r_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v_k_2711_ = lean_ctor_get(v_x_2710_, 1);
lean_inc_n(v_k_2711_, 2);
v_v_2712_ = lean_ctor_get(v_x_2710_, 2);
lean_inc(v_v_2712_);
v_l_2713_ = lean_ctor_get(v_x_2710_, 3);
lean_inc(v_l_2713_);
v_r_2714_ = lean_ctor_get(v_x_2710_, 4);
lean_inc(v_r_2714_);
lean_dec(v_x_2710_);
lean_inc_ref(v_inst_2708_);
lean_inc(v_k_2709_);
v___x_2715_ = lean_apply_2(v_inst_2708_, v_k_2709_, v_k_2711_);
v___x_2716_ = lean_unbox(v___x_2715_);
switch(v___x_2716_)
{
case 0:
{
lean_dec(v_r_2714_);
lean_dec(v_v_2712_);
lean_dec(v_k_2711_);
v_x_2710_ = v_l_2713_;
goto _start;
}
case 1:
{
lean_object* v___x_2718_; 
lean_dec(v_r_2714_);
lean_dec(v_l_2713_);
lean_dec(v_k_2709_);
lean_dec_ref(v_inst_2708_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_k_2711_);
lean_ctor_set(v___x_2718_, 1, v_v_2712_);
return v___x_2718_;
}
default: 
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec(v_l_2713_);
v___x_2719_ = lean_box(0);
v___x_2720_ = l_Std_DTreeMap_Internal_Impl_getEntryLE_x3f_go___redArg(v_inst_2708_, v_k_2709_, v___x_2719_, v_r_2714_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_k_2711_);
lean_ctor_set(v___x_2721_, 1, v_v_2712_);
return v___x_2721_;
}
else
{
lean_object* v_val_2722_; 
lean_dec(v_v_2712_);
lean_dec(v_k_2711_);
v_val_2722_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_val_2722_);
lean_dec_ref_known(v___x_2720_, 1);
return v_val_2722_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLE(lean_object* v_00_u03b1_2723_, lean_object* v_00_u03b2_2724_, lean_object* v_inst_2725_, lean_object* v_inst_2726_, lean_object* v_k_2727_, lean_object* v_x_2728_, lean_object* v_x_2729_, lean_object* v_x_2730_){
_start:
{
lean_object* v___x_2731_; 
v___x_2731_ = l_Std_DTreeMap_Internal_Impl_getEntryLE___redArg(v_inst_2725_, v_k_2727_, v_x_2728_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(lean_object* v_inst_2732_, lean_object* v_k_2733_, lean_object* v_x_2734_){
_start:
{
lean_object* v_k_2735_; lean_object* v_v_2736_; lean_object* v_l_2737_; lean_object* v_r_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; uint8_t v___x_2742_; 
v_k_2735_ = lean_ctor_get(v_x_2734_, 1);
lean_inc_n(v_k_2735_, 2);
v_v_2736_ = lean_ctor_get(v_x_2734_, 2);
lean_inc(v_v_2736_);
v_l_2737_ = lean_ctor_get(v_x_2734_, 3);
lean_inc(v_l_2737_);
v_r_2738_ = lean_ctor_get(v_x_2734_, 4);
lean_inc(v_r_2738_);
lean_dec(v_x_2734_);
lean_inc_ref(v_inst_2732_);
lean_inc(v_k_2733_);
v___x_2739_ = lean_apply_2(v_inst_2732_, v_k_2733_, v_k_2735_);
v___x_2740_ = lean_obj_tag_nat(v___x_2739_);
v___x_2741_ = lean_unsigned_to_nat(2u);
v___x_2742_ = lean_nat_dec_eq(v___x_2740_, v___x_2741_);
if (v___x_2742_ == 0)
{
lean_dec(v_r_2738_);
lean_dec(v_v_2736_);
lean_dec(v_k_2735_);
v_x_2734_ = v_l_2737_;
goto _start;
}
else
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
lean_dec(v_l_2737_);
v___x_2744_ = lean_box(0);
v___x_2745_ = l_Std_DTreeMap_Internal_Impl_getEntryLT_x3f_go___redArg(v_inst_2732_, v_k_2733_, v___x_2744_, v_r_2738_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v___x_2746_; 
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v_k_2735_);
lean_ctor_set(v___x_2746_, 1, v_v_2736_);
return v___x_2746_;
}
else
{
lean_object* v_val_2747_; 
lean_dec(v_v_2736_);
lean_dec(v_k_2735_);
v_val_2747_ = lean_ctor_get(v___x_2745_, 0);
lean_inc(v_val_2747_);
lean_dec_ref_known(v___x_2745_, 1);
return v_val_2747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getEntryLT(lean_object* v_00_u03b1_2748_, lean_object* v_00_u03b2_2749_, lean_object* v_inst_2750_, lean_object* v_inst_2751_, lean_object* v_k_2752_, lean_object* v_x_2753_, lean_object* v_x_2754_, lean_object* v_x_2755_){
_start:
{
lean_object* v___x_2756_; 
v___x_2756_ = l_Std_DTreeMap_Internal_Impl_getEntryLT___redArg(v_inst_2750_, v_k_2752_, v_x_2753_);
return v___x_2756_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(lean_object* v_inst_2757_, lean_object* v_k_2758_, lean_object* v_best_2759_, lean_object* v_a_2760_){
_start:
{
if (lean_obj_tag(v_a_2760_) == 0)
{
lean_object* v_k_2761_; lean_object* v_l_2762_; lean_object* v_r_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_k_2761_ = lean_ctor_get(v_a_2760_, 1);
lean_inc_n(v_k_2761_, 2);
v_l_2762_ = lean_ctor_get(v_a_2760_, 3);
lean_inc(v_l_2762_);
v_r_2763_ = lean_ctor_get(v_a_2760_, 4);
lean_inc(v_r_2763_);
lean_dec_ref_known(v_a_2760_, 5);
lean_inc_ref(v_inst_2757_);
lean_inc(v_k_2758_);
v___x_2764_ = lean_apply_2(v_inst_2757_, v_k_2758_, v_k_2761_);
v___x_2765_ = lean_unbox(v___x_2764_);
switch(v___x_2765_)
{
case 0:
{
lean_object* v___x_2766_; 
lean_dec(v_r_2763_);
lean_dec(v_best_2759_);
v___x_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_k_2761_);
v_best_2759_ = v___x_2766_;
v_a_2760_ = v_l_2762_;
goto _start;
}
case 1:
{
lean_object* v___x_2768_; 
lean_dec(v_r_2763_);
lean_dec(v_l_2762_);
lean_dec(v_best_2759_);
lean_dec(v_k_2758_);
lean_dec_ref(v_inst_2757_);
v___x_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2768_, 0, v_k_2761_);
return v___x_2768_;
}
default: 
{
lean_dec(v_l_2762_);
lean_dec(v_k_2761_);
v_a_2760_ = v_r_2763_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2758_);
lean_dec_ref(v_inst_2757_);
return v_best_2759_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go(lean_object* v_00_u03b1_2770_, lean_object* v_00_u03b2_2771_, lean_object* v_inst_2772_, lean_object* v_k_2773_, lean_object* v_best_2774_, lean_object* v_a_2775_){
_start:
{
lean_object* v___x_2776_; 
v___x_2776_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2772_, v_k_2773_, v_best_2774_, v_a_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f___redArg(lean_object* v_inst_2777_, lean_object* v_k_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_box(0);
v___x_2781_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2777_, v_k_2778_, v___x_2780_, v_a_2779_);
return v___x_2781_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f(lean_object* v_00_u03b1_2782_, lean_object* v_00_u03b2_2783_, lean_object* v_inst_2784_, lean_object* v_k_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_box(0);
v___x_2788_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2784_, v_k_2785_, v___x_2787_, v_a_2786_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(lean_object* v_inst_2789_, lean_object* v_k_2790_, lean_object* v_best_2791_, lean_object* v_a_2792_){
_start:
{
if (lean_obj_tag(v_a_2792_) == 0)
{
lean_object* v_k_2793_; lean_object* v_l_2794_; lean_object* v_r_2795_; lean_object* v___x_2796_; uint8_t v___x_2797_; 
v_k_2793_ = lean_ctor_get(v_a_2792_, 1);
lean_inc_n(v_k_2793_, 2);
v_l_2794_ = lean_ctor_get(v_a_2792_, 3);
lean_inc(v_l_2794_);
v_r_2795_ = lean_ctor_get(v_a_2792_, 4);
lean_inc(v_r_2795_);
lean_dec_ref_known(v_a_2792_, 5);
lean_inc_ref(v_inst_2789_);
lean_inc(v_k_2790_);
v___x_2796_ = lean_apply_2(v_inst_2789_, v_k_2790_, v_k_2793_);
v___x_2797_ = lean_unbox(v___x_2796_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2798_; 
lean_dec(v_r_2795_);
lean_dec(v_best_2791_);
v___x_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2798_, 0, v_k_2793_);
v_best_2791_ = v___x_2798_;
v_a_2792_ = v_l_2794_;
goto _start;
}
else
{
lean_dec(v_l_2794_);
lean_dec(v_k_2793_);
v_a_2792_ = v_r_2795_;
goto _start;
}
}
else
{
lean_dec(v_k_2790_);
lean_dec_ref(v_inst_2789_);
return v_best_2791_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go(lean_object* v_00_u03b1_2801_, lean_object* v_00_u03b2_2802_, lean_object* v_inst_2803_, lean_object* v_k_2804_, lean_object* v_best_2805_, lean_object* v_a_2806_){
_start:
{
lean_object* v___x_2807_; 
v___x_2807_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2803_, v_k_2804_, v_best_2805_, v_a_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f___redArg(lean_object* v_inst_2808_, lean_object* v_k_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2811_ = lean_box(0);
v___x_2812_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2808_, v_k_2809_, v___x_2811_, v_a_2810_);
return v___x_2812_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f(lean_object* v_00_u03b1_2813_, lean_object* v_00_u03b2_2814_, lean_object* v_inst_2815_, lean_object* v_k_2816_, lean_object* v_a_2817_){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = lean_box(0);
v___x_2819_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2815_, v_k_2816_, v___x_2818_, v_a_2817_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(lean_object* v_inst_2820_, lean_object* v_k_2821_, lean_object* v_best_2822_, lean_object* v_a_2823_){
_start:
{
if (lean_obj_tag(v_a_2823_) == 0)
{
lean_object* v_k_2824_; lean_object* v_l_2825_; lean_object* v_r_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_k_2824_ = lean_ctor_get(v_a_2823_, 1);
lean_inc_n(v_k_2824_, 2);
v_l_2825_ = lean_ctor_get(v_a_2823_, 3);
lean_inc(v_l_2825_);
v_r_2826_ = lean_ctor_get(v_a_2823_, 4);
lean_inc(v_r_2826_);
lean_dec_ref_known(v_a_2823_, 5);
lean_inc_ref(v_inst_2820_);
lean_inc(v_k_2821_);
v___x_2827_ = lean_apply_2(v_inst_2820_, v_k_2821_, v_k_2824_);
v___x_2828_ = lean_unbox(v___x_2827_);
switch(v___x_2828_)
{
case 0:
{
lean_dec(v_r_2826_);
lean_dec(v_k_2824_);
v_a_2823_ = v_l_2825_;
goto _start;
}
case 1:
{
lean_object* v___x_2830_; 
lean_dec(v_r_2826_);
lean_dec(v_l_2825_);
lean_dec(v_best_2822_);
lean_dec(v_k_2821_);
lean_dec_ref(v_inst_2820_);
v___x_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2830_, 0, v_k_2824_);
return v___x_2830_;
}
default: 
{
lean_object* v___x_2831_; 
lean_dec(v_l_2825_);
lean_dec(v_best_2822_);
v___x_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2831_, 0, v_k_2824_);
v_best_2822_ = v___x_2831_;
v_a_2823_ = v_r_2826_;
goto _start;
}
}
}
else
{
lean_dec(v_k_2821_);
lean_dec_ref(v_inst_2820_);
return v_best_2822_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go(lean_object* v_00_u03b1_2833_, lean_object* v_00_u03b2_2834_, lean_object* v_inst_2835_, lean_object* v_k_2836_, lean_object* v_best_2837_, lean_object* v_a_2838_){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2835_, v_k_2836_, v_best_2837_, v_a_2838_);
return v___x_2839_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f___redArg(lean_object* v_inst_2840_, lean_object* v_k_2841_, lean_object* v_a_2842_){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = lean_box(0);
v___x_2844_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2840_, v_k_2841_, v___x_2843_, v_a_2842_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f(lean_object* v_00_u03b1_2845_, lean_object* v_00_u03b2_2846_, lean_object* v_inst_2847_, lean_object* v_k_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2850_ = lean_box(0);
v___x_2851_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2847_, v_k_2848_, v___x_2850_, v_a_2849_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(lean_object* v_inst_2852_, lean_object* v_k_2853_, lean_object* v_best_2854_, lean_object* v_a_2855_){
_start:
{
if (lean_obj_tag(v_a_2855_) == 0)
{
lean_object* v_k_2856_; lean_object* v_l_2857_; lean_object* v_r_2858_; lean_object* v___x_2859_; uint8_t v___x_2860_; 
v_k_2856_ = lean_ctor_get(v_a_2855_, 1);
lean_inc_n(v_k_2856_, 2);
v_l_2857_ = lean_ctor_get(v_a_2855_, 3);
lean_inc(v_l_2857_);
v_r_2858_ = lean_ctor_get(v_a_2855_, 4);
lean_inc(v_r_2858_);
lean_dec_ref_known(v_a_2855_, 5);
lean_inc_ref(v_inst_2852_);
lean_inc(v_k_2853_);
v___x_2859_ = lean_apply_2(v_inst_2852_, v_k_2853_, v_k_2856_);
v___x_2860_ = lean_unbox(v___x_2859_);
if (v___x_2860_ == 2)
{
lean_object* v___x_2861_; 
lean_dec(v_l_2857_);
lean_dec(v_best_2854_);
v___x_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2861_, 0, v_k_2856_);
v_best_2854_ = v___x_2861_;
v_a_2855_ = v_r_2858_;
goto _start;
}
else
{
lean_dec(v_r_2858_);
lean_dec(v_k_2856_);
v_a_2855_ = v_l_2857_;
goto _start;
}
}
else
{
lean_dec(v_k_2853_);
lean_dec_ref(v_inst_2852_);
return v_best_2854_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go(lean_object* v_00_u03b1_2864_, lean_object* v_00_u03b2_2865_, lean_object* v_inst_2866_, lean_object* v_k_2867_, lean_object* v_best_2868_, lean_object* v_a_2869_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2866_, v_k_2867_, v_best_2868_, v_a_2869_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f___redArg(lean_object* v_inst_2871_, lean_object* v_k_2872_, lean_object* v_a_2873_){
_start:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; 
v___x_2874_ = lean_box(0);
v___x_2875_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2871_, v_k_2872_, v___x_2874_, v_a_2873_);
return v___x_2875_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f(lean_object* v_00_u03b1_2876_, lean_object* v_00_u03b2_2877_, lean_object* v_inst_2878_, lean_object* v_k_2879_, lean_object* v_a_2880_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2881_ = lean_box(0);
v___x_2882_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2878_, v_k_2879_, v___x_2881_, v_a_2880_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_k_2885_, lean_object* v_t_2886_){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = lean_box(0);
v___x_2888_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2883_, v_k_2885_, v___x_2887_, v_t_2886_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2890_ = l_panic___redArg(v_inst_2884_, v___x_2889_);
return v___x_2890_;
}
else
{
lean_object* v_val_2891_; 
v_val_2891_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_val_2891_);
lean_dec_ref_known(v___x_2888_, 1);
return v_val_2891_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg___boxed(lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_k_2894_, lean_object* v_t_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___redArg(v_inst_2892_, v_inst_2893_, v_k_2894_, v_t_2895_);
lean_dec(v_inst_2893_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(lean_object* v_00_u03b1_2897_, lean_object* v_00_u03b2_2898_, lean_object* v_inst_2899_, lean_object* v_inst_2900_, lean_object* v_k_2901_, lean_object* v_t_2902_){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_box(0);
v___x_2904_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_2899_, v_k_2901_, v___x_2903_, v_t_2902_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2905_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2906_ = l_panic___redArg(v_inst_2900_, v___x_2905_);
return v___x_2906_;
}
else
{
lean_object* v_val_2907_; 
v_val_2907_ = lean_ctor_get(v___x_2904_, 0);
lean_inc(v_val_2907_);
lean_dec_ref_known(v___x_2904_, 1);
return v_val_2907_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE_x21___boxed(lean_object* v_00_u03b1_2908_, lean_object* v_00_u03b2_2909_, lean_object* v_inst_2910_, lean_object* v_inst_2911_, lean_object* v_k_2912_, lean_object* v_t_2913_){
_start:
{
lean_object* v_res_2914_; 
v_res_2914_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x21(v_00_u03b1_2908_, v_00_u03b2_2909_, v_inst_2910_, v_inst_2911_, v_k_2912_, v_t_2913_);
lean_dec(v_inst_2911_);
return v_res_2914_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(lean_object* v_inst_2915_, lean_object* v_inst_2916_, lean_object* v_k_2917_, lean_object* v_t_2918_){
_start:
{
lean_object* v___x_2919_; lean_object* v___x_2920_; 
v___x_2919_ = lean_box(0);
v___x_2920_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2915_, v_k_2917_, v___x_2919_, v_t_2918_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2922_ = l_panic___redArg(v_inst_2916_, v___x_2921_);
return v___x_2922_;
}
else
{
lean_object* v_val_2923_; 
v_val_2923_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_val_2923_);
lean_dec_ref_known(v___x_2920_, 1);
return v_val_2923_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg___boxed(lean_object* v_inst_2924_, lean_object* v_inst_2925_, lean_object* v_k_2926_, lean_object* v_t_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___redArg(v_inst_2924_, v_inst_2925_, v_k_2926_, v_t_2927_);
lean_dec(v_inst_2925_);
return v_res_2928_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(lean_object* v_00_u03b1_2929_, lean_object* v_00_u03b2_2930_, lean_object* v_inst_2931_, lean_object* v_inst_2932_, lean_object* v_k_2933_, lean_object* v_t_2934_){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = lean_box(0);
v___x_2936_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_2931_, v_k_2933_, v___x_2935_, v_t_2934_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2938_ = l_panic___redArg(v_inst_2932_, v___x_2937_);
return v___x_2938_;
}
else
{
lean_object* v_val_2939_; 
v_val_2939_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_val_2939_);
lean_dec_ref_known(v___x_2936_, 1);
return v_val_2939_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT_x21___boxed(lean_object* v_00_u03b1_2940_, lean_object* v_00_u03b2_2941_, lean_object* v_inst_2942_, lean_object* v_inst_2943_, lean_object* v_k_2944_, lean_object* v_t_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x21(v_00_u03b1_2940_, v_00_u03b2_2941_, v_inst_2942_, v_inst_2943_, v_k_2944_, v_t_2945_);
lean_dec(v_inst_2943_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(lean_object* v_inst_2947_, lean_object* v_inst_2948_, lean_object* v_k_2949_, lean_object* v_t_2950_){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = lean_box(0);
v___x_2952_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2947_, v_k_2949_, v___x_2951_, v_t_2950_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2954_ = l_panic___redArg(v_inst_2948_, v___x_2953_);
return v___x_2954_;
}
else
{
lean_object* v_val_2955_; 
v_val_2955_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_val_2955_);
lean_dec_ref_known(v___x_2952_, 1);
return v_val_2955_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg___boxed(lean_object* v_inst_2956_, lean_object* v_inst_2957_, lean_object* v_k_2958_, lean_object* v_t_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___redArg(v_inst_2956_, v_inst_2957_, v_k_2958_, v_t_2959_);
lean_dec(v_inst_2957_);
return v_res_2960_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(lean_object* v_00_u03b1_2961_, lean_object* v_00_u03b2_2962_, lean_object* v_inst_2963_, lean_object* v_inst_2964_, lean_object* v_k_2965_, lean_object* v_t_2966_){
_start:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2967_ = lean_box(0);
v___x_2968_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_2963_, v_k_2965_, v___x_2967_, v_t_2966_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2969_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2970_ = l_panic___redArg(v_inst_2964_, v___x_2969_);
return v___x_2970_;
}
else
{
lean_object* v_val_2971_; 
v_val_2971_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_val_2971_);
lean_dec_ref_known(v___x_2968_, 1);
return v_val_2971_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE_x21___boxed(lean_object* v_00_u03b1_2972_, lean_object* v_00_u03b2_2973_, lean_object* v_inst_2974_, lean_object* v_inst_2975_, lean_object* v_k_2976_, lean_object* v_t_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x21(v_00_u03b1_2972_, v_00_u03b2_2973_, v_inst_2974_, v_inst_2975_, v_k_2976_, v_t_2977_);
lean_dec(v_inst_2975_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(lean_object* v_inst_2979_, lean_object* v_inst_2980_, lean_object* v_k_2981_, lean_object* v_t_2982_){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = lean_box(0);
v___x_2984_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2979_, v_k_2981_, v___x_2983_, v_t_2982_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_2986_ = l_panic___redArg(v_inst_2980_, v___x_2985_);
return v___x_2986_;
}
else
{
lean_object* v_val_2987_; 
v_val_2987_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_val_2987_);
lean_dec_ref_known(v___x_2984_, 1);
return v_val_2987_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg___boxed(lean_object* v_inst_2988_, lean_object* v_inst_2989_, lean_object* v_k_2990_, lean_object* v_t_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___redArg(v_inst_2988_, v_inst_2989_, v_k_2990_, v_t_2991_);
lean_dec(v_inst_2989_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(lean_object* v_00_u03b1_2993_, lean_object* v_00_u03b2_2994_, lean_object* v_inst_2995_, lean_object* v_inst_2996_, lean_object* v_k_2997_, lean_object* v_t_2998_){
_start:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; 
v___x_2999_ = lean_box(0);
v___x_3000_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_2995_, v_k_2997_, v___x_2999_, v_t_2998_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3002_ = l_panic___redArg(v_inst_2996_, v___x_3001_);
return v___x_3002_;
}
else
{
lean_object* v_val_3003_; 
v_val_3003_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_val_3003_);
lean_dec_ref_known(v___x_3000_, 1);
return v_val_3003_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT_x21___boxed(lean_object* v_00_u03b1_3004_, lean_object* v_00_u03b2_3005_, lean_object* v_inst_3006_, lean_object* v_inst_3007_, lean_object* v_k_3008_, lean_object* v_t_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x21(v_00_u03b1_3004_, v_00_u03b2_3005_, v_inst_3006_, v_inst_3007_, v_k_3008_, v_t_3009_);
lean_dec(v_inst_3007_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(lean_object* v_inst_3011_, lean_object* v_k_3012_, lean_object* v_t_3013_, lean_object* v_fallback_3014_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg___boxed(lean_object* v_inst_3018_, lean_object* v_k_3019_, lean_object* v_t_3020_, lean_object* v_fallback_3021_){
_start:
{
lean_object* v_res_3022_; 
v_res_3022_ = l_Std_DTreeMap_Internal_Impl_getKeyGED___redArg(v_inst_3018_, v_k_3019_, v_t_3020_, v_fallback_3021_);
lean_dec(v_fallback_3021_);
return v_res_3022_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED(lean_object* v_00_u03b1_3023_, lean_object* v_00_u03b2_3024_, lean_object* v_inst_3025_, lean_object* v_k_3026_, lean_object* v_t_3027_, lean_object* v_fallback_3028_){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3029_ = lean_box(0);
v___x_3030_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3025_, v_k_3026_, v___x_3029_, v_t_3027_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGED___boxed(lean_object* v_00_u03b1_3032_, lean_object* v_00_u03b2_3033_, lean_object* v_inst_3034_, lean_object* v_k_3035_, lean_object* v_t_3036_, lean_object* v_fallback_3037_){
_start:
{
lean_object* v_res_3038_; 
v_res_3038_ = l_Std_DTreeMap_Internal_Impl_getKeyGED(v_00_u03b1_3032_, v_00_u03b2_3033_, v_inst_3034_, v_k_3035_, v_t_3036_, v_fallback_3037_);
lean_dec(v_fallback_3037_);
return v_res_3038_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(lean_object* v_inst_3039_, lean_object* v_k_3040_, lean_object* v_t_3041_, lean_object* v_fallback_3042_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg___boxed(lean_object* v_inst_3046_, lean_object* v_k_3047_, lean_object* v_t_3048_, lean_object* v_fallback_3049_){
_start:
{
lean_object* v_res_3050_; 
v_res_3050_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD___redArg(v_inst_3046_, v_k_3047_, v_t_3048_, v_fallback_3049_);
lean_dec(v_fallback_3049_);
return v_res_3050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD(lean_object* v_00_u03b1_3051_, lean_object* v_00_u03b2_3052_, lean_object* v_inst_3053_, lean_object* v_k_3054_, lean_object* v_t_3055_, lean_object* v_fallback_3056_){
_start:
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
v___x_3057_ = lean_box(0);
v___x_3058_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3053_, v_k_3054_, v___x_3057_, v_t_3055_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGTD___boxed(lean_object* v_00_u03b1_3060_, lean_object* v_00_u03b2_3061_, lean_object* v_inst_3062_, lean_object* v_k_3063_, lean_object* v_t_3064_, lean_object* v_fallback_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l_Std_DTreeMap_Internal_Impl_getKeyGTD(v_00_u03b1_3060_, v_00_u03b2_3061_, v_inst_3062_, v_k_3063_, v_t_3064_, v_fallback_3065_);
lean_dec(v_fallback_3065_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(lean_object* v_inst_3067_, lean_object* v_k_3068_, lean_object* v_t_3069_, lean_object* v_fallback_3070_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg___boxed(lean_object* v_inst_3074_, lean_object* v_k_3075_, lean_object* v_t_3076_, lean_object* v_fallback_3077_){
_start:
{
lean_object* v_res_3078_; 
v_res_3078_ = l_Std_DTreeMap_Internal_Impl_getKeyLED___redArg(v_inst_3074_, v_k_3075_, v_t_3076_, v_fallback_3077_);
lean_dec(v_fallback_3077_);
return v_res_3078_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED(lean_object* v_00_u03b1_3079_, lean_object* v_00_u03b2_3080_, lean_object* v_inst_3081_, lean_object* v_k_3082_, lean_object* v_t_3083_, lean_object* v_fallback_3084_){
_start:
{
lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = lean_box(0);
v___x_3086_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3081_, v_k_3082_, v___x_3085_, v_t_3083_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLED___boxed(lean_object* v_00_u03b1_3088_, lean_object* v_00_u03b2_3089_, lean_object* v_inst_3090_, lean_object* v_k_3091_, lean_object* v_t_3092_, lean_object* v_fallback_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_Std_DTreeMap_Internal_Impl_getKeyLED(v_00_u03b1_3088_, v_00_u03b2_3089_, v_inst_3090_, v_k_3091_, v_t_3092_, v_fallback_3093_);
lean_dec(v_fallback_3093_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(lean_object* v_inst_3095_, lean_object* v_k_3096_, lean_object* v_t_3097_, lean_object* v_fallback_3098_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg___boxed(lean_object* v_inst_3102_, lean_object* v_k_3103_, lean_object* v_t_3104_, lean_object* v_fallback_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD___redArg(v_inst_3102_, v_k_3103_, v_t_3104_, v_fallback_3105_);
lean_dec(v_fallback_3105_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD(lean_object* v_00_u03b1_3107_, lean_object* v_00_u03b2_3108_, lean_object* v_inst_3109_, lean_object* v_k_3110_, lean_object* v_t_3111_, lean_object* v_fallback_3112_){
_start:
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3113_ = lean_box(0);
v___x_3114_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3109_, v_k_3110_, v___x_3113_, v_t_3111_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_inc(v_fallback_3112_);
return v_fallback_3112_;
}
else
{
lean_object* v_val_3115_; 
v_val_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_val_3115_);
lean_dec_ref_known(v___x_3114_, 1);
return v_val_3115_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLTD___boxed(lean_object* v_00_u03b1_3116_, lean_object* v_00_u03b2_3117_, lean_object* v_inst_3118_, lean_object* v_k_3119_, lean_object* v_t_3120_, lean_object* v_fallback_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_Std_DTreeMap_Internal_Impl_getKeyLTD(v_00_u03b1_3116_, v_00_u03b2_3117_, v_inst_3118_, v_k_3119_, v_t_3120_, v_fallback_3121_);
lean_dec(v_fallback_3121_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(lean_object* v_inst_3123_, lean_object* v_k_3124_, lean_object* v_x_3125_){
_start:
{
lean_object* v_k_3126_; lean_object* v_l_3127_; lean_object* v_r_3128_; lean_object* v___x_3129_; uint8_t v___x_3130_; 
v_k_3126_ = lean_ctor_get(v_x_3125_, 1);
lean_inc_n(v_k_3126_, 2);
v_l_3127_ = lean_ctor_get(v_x_3125_, 3);
lean_inc(v_l_3127_);
v_r_3128_ = lean_ctor_get(v_x_3125_, 4);
lean_inc(v_r_3128_);
lean_dec(v_x_3125_);
lean_inc_ref(v_inst_3123_);
lean_inc(v_k_3124_);
v___x_3129_ = lean_apply_2(v_inst_3123_, v_k_3124_, v_k_3126_);
v___x_3130_ = lean_unbox(v___x_3129_);
switch(v___x_3130_)
{
case 0:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; 
lean_dec(v_r_3128_);
v___x_3131_ = lean_box(0);
v___x_3132_ = l_Std_DTreeMap_Internal_Impl_getKeyGE_x3f_go___redArg(v_inst_3123_, v_k_3124_, v___x_3131_, v_l_3127_);
if (lean_obj_tag(v___x_3132_) == 0)
{
return v_k_3126_;
}
else
{
lean_object* v_val_3133_; 
lean_dec(v_k_3126_);
v_val_3133_ = lean_ctor_get(v___x_3132_, 0);
lean_inc(v_val_3133_);
lean_dec_ref_known(v___x_3132_, 1);
return v_val_3133_;
}
}
case 1:
{
lean_dec(v_r_3128_);
lean_dec(v_l_3127_);
lean_dec(v_k_3124_);
lean_dec_ref(v_inst_3123_);
return v_k_3126_;
}
default: 
{
lean_dec(v_l_3127_);
lean_dec(v_k_3126_);
v_x_3125_ = v_r_3128_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGE(lean_object* v_00_u03b1_3135_, lean_object* v_00_u03b2_3136_, lean_object* v_inst_3137_, lean_object* v_inst_3138_, lean_object* v_k_3139_, lean_object* v_x_3140_, lean_object* v_x_3141_, lean_object* v_x_3142_){
_start:
{
lean_object* v___x_3143_; 
v___x_3143_ = l_Std_DTreeMap_Internal_Impl_getKeyGE___redArg(v_inst_3137_, v_k_3139_, v_x_3140_);
return v___x_3143_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(lean_object* v_inst_3144_, lean_object* v_k_3145_, lean_object* v_x_3146_){
_start:
{
lean_object* v_k_3147_; lean_object* v_l_3148_; lean_object* v_r_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; uint8_t v___x_3153_; 
v_k_3147_ = lean_ctor_get(v_x_3146_, 1);
lean_inc_n(v_k_3147_, 2);
v_l_3148_ = lean_ctor_get(v_x_3146_, 3);
lean_inc(v_l_3148_);
v_r_3149_ = lean_ctor_get(v_x_3146_, 4);
lean_inc(v_r_3149_);
lean_dec(v_x_3146_);
lean_inc_ref(v_inst_3144_);
lean_inc(v_k_3145_);
v___x_3150_ = lean_apply_2(v_inst_3144_, v_k_3145_, v_k_3147_);
v___x_3151_ = lean_obj_tag_nat(v___x_3150_);
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = lean_nat_dec_eq(v___x_3151_, v___x_3152_);
if (v___x_3153_ == 0)
{
lean_dec(v_l_3148_);
lean_dec(v_k_3147_);
v_x_3146_ = v_r_3149_;
goto _start;
}
else
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
lean_dec(v_r_3149_);
v___x_3155_ = lean_box(0);
v___x_3156_ = l_Std_DTreeMap_Internal_Impl_getKeyGT_x3f_go___redArg(v_inst_3144_, v_k_3145_, v___x_3155_, v_l_3148_);
if (lean_obj_tag(v___x_3156_) == 0)
{
return v_k_3147_;
}
else
{
lean_object* v_val_3157_; 
lean_dec(v_k_3147_);
v_val_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_val_3157_);
lean_dec_ref_known(v___x_3156_, 1);
return v_val_3157_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyGT(lean_object* v_00_u03b1_3158_, lean_object* v_00_u03b2_3159_, lean_object* v_inst_3160_, lean_object* v_inst_3161_, lean_object* v_k_3162_, lean_object* v_x_3163_, lean_object* v_x_3164_, lean_object* v_x_3165_){
_start:
{
lean_object* v___x_3166_; 
v___x_3166_ = l_Std_DTreeMap_Internal_Impl_getKeyGT___redArg(v_inst_3160_, v_k_3162_, v_x_3163_);
return v___x_3166_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(lean_object* v_inst_3167_, lean_object* v_k_3168_, lean_object* v_x_3169_){
_start:
{
lean_object* v_k_3170_; lean_object* v_l_3171_; lean_object* v_r_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_k_3170_ = lean_ctor_get(v_x_3169_, 1);
lean_inc_n(v_k_3170_, 2);
v_l_3171_ = lean_ctor_get(v_x_3169_, 3);
lean_inc(v_l_3171_);
v_r_3172_ = lean_ctor_get(v_x_3169_, 4);
lean_inc(v_r_3172_);
lean_dec(v_x_3169_);
lean_inc_ref(v_inst_3167_);
lean_inc(v_k_3168_);
v___x_3173_ = lean_apply_2(v_inst_3167_, v_k_3168_, v_k_3170_);
v___x_3174_ = lean_unbox(v___x_3173_);
switch(v___x_3174_)
{
case 0:
{
lean_dec(v_r_3172_);
lean_dec(v_k_3170_);
v_x_3169_ = v_l_3171_;
goto _start;
}
case 1:
{
lean_dec(v_r_3172_);
lean_dec(v_l_3171_);
lean_dec(v_k_3168_);
lean_dec_ref(v_inst_3167_);
return v_k_3170_;
}
default: 
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
lean_dec(v_l_3171_);
v___x_3176_ = lean_box(0);
v___x_3177_ = l_Std_DTreeMap_Internal_Impl_getKeyLE_x3f_go___redArg(v_inst_3167_, v_k_3168_, v___x_3176_, v_r_3172_);
if (lean_obj_tag(v___x_3177_) == 0)
{
return v_k_3170_;
}
else
{
lean_object* v_val_3178_; 
lean_dec(v_k_3170_);
v_val_3178_ = lean_ctor_get(v___x_3177_, 0);
lean_inc(v_val_3178_);
lean_dec_ref_known(v___x_3177_, 1);
return v_val_3178_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLE(lean_object* v_00_u03b1_3179_, lean_object* v_00_u03b2_3180_, lean_object* v_inst_3181_, lean_object* v_inst_3182_, lean_object* v_k_3183_, lean_object* v_x_3184_, lean_object* v_x_3185_, lean_object* v_x_3186_){
_start:
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Std_DTreeMap_Internal_Impl_getKeyLE___redArg(v_inst_3181_, v_k_3183_, v_x_3184_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(lean_object* v_inst_3188_, lean_object* v_k_3189_, lean_object* v_x_3190_){
_start:
{
lean_object* v_k_3191_; lean_object* v_l_3192_; lean_object* v_r_3193_; lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; uint8_t v___x_3197_; 
v_k_3191_ = lean_ctor_get(v_x_3190_, 1);
lean_inc_n(v_k_3191_, 2);
v_l_3192_ = lean_ctor_get(v_x_3190_, 3);
lean_inc(v_l_3192_);
v_r_3193_ = lean_ctor_get(v_x_3190_, 4);
lean_inc(v_r_3193_);
lean_dec(v_x_3190_);
lean_inc_ref(v_inst_3188_);
lean_inc(v_k_3189_);
v___x_3194_ = lean_apply_2(v_inst_3188_, v_k_3189_, v_k_3191_);
v___x_3195_ = lean_obj_tag_nat(v___x_3194_);
v___x_3196_ = lean_unsigned_to_nat(2u);
v___x_3197_ = lean_nat_dec_eq(v___x_3195_, v___x_3196_);
if (v___x_3197_ == 0)
{
lean_dec(v_r_3193_);
lean_dec(v_k_3191_);
v_x_3190_ = v_l_3192_;
goto _start;
}
else
{
lean_object* v___x_3199_; lean_object* v___x_3200_; 
lean_dec(v_l_3192_);
v___x_3199_ = lean_box(0);
v___x_3200_ = l_Std_DTreeMap_Internal_Impl_getKeyLT_x3f_go___redArg(v_inst_3188_, v_k_3189_, v___x_3199_, v_r_3193_);
if (lean_obj_tag(v___x_3200_) == 0)
{
return v_k_3191_;
}
else
{
lean_object* v_val_3201_; 
lean_dec(v_k_3191_);
v_val_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_val_3201_);
lean_dec_ref_known(v___x_3200_, 1);
return v_val_3201_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_getKeyLT(lean_object* v_00_u03b1_3202_, lean_object* v_00_u03b2_3203_, lean_object* v_inst_3204_, lean_object* v_inst_3205_, lean_object* v_k_3206_, lean_object* v_x_3207_, lean_object* v_x_3208_, lean_object* v_x_3209_){
_start:
{
lean_object* v___x_3210_; 
v___x_3210_ = l_Std_DTreeMap_Internal_Impl_getKeyLT___redArg(v_inst_3204_, v_k_3206_, v_x_3207_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(lean_object* v_x_3211_){
_start:
{
if (lean_obj_tag(v_x_3211_) == 0)
{
lean_object* v_l_3212_; 
v_l_3212_ = lean_ctor_get(v_x_3211_, 3);
if (lean_obj_tag(v_l_3212_) == 0)
{
v_x_3211_ = v_l_3212_;
goto _start;
}
else
{
lean_object* v_k_3214_; lean_object* v_v_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v_k_3214_ = lean_ctor_get(v_x_3211_, 1);
v_v_3215_ = lean_ctor_get(v_x_3211_, 2);
lean_inc(v_v_3215_);
lean_inc(v_k_3214_);
v___x_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3216_, 0, v_k_3214_);
lean_ctor_set(v___x_3216_, 1, v_v_3215_);
v___x_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
}
else
{
lean_object* v___x_3218_; 
v___x_3218_ = lean_box(0);
return v___x_3218_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg___boxed(lean_object* v_x_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3219_);
lean_dec(v_x_3219_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(lean_object* v_00_u03b1_3221_, lean_object* v_00_u03b2_3222_, lean_object* v_x_3223_){
_start:
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___redArg(v_x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f___boxed(lean_object* v_00_u03b1_3225_, lean_object* v_00_u03b2_3226_, lean_object* v_x_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x3f(v_00_u03b1_3225_, v_00_u03b2_3226_, v_x_3227_);
lean_dec(v_x_3227_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3229_, lean_object* v_h__1_3230_, lean_object* v_h__2_3231_, lean_object* v_h__3_3232_){
_start:
{
if (lean_obj_tag(v_x_3229_) == 0)
{
lean_object* v_l_3233_; 
lean_dec(v_h__1_3230_);
v_l_3233_ = lean_ctor_get(v_x_3229_, 3);
if (lean_obj_tag(v_l_3233_) == 0)
{
lean_object* v_size_3234_; lean_object* v_k_3235_; lean_object* v_v_3236_; lean_object* v_r_3237_; lean_object* v_size_3238_; lean_object* v_k_3239_; lean_object* v_v_3240_; lean_object* v_l_3241_; lean_object* v_r_3242_; lean_object* v___x_3243_; 
lean_inc_ref(v_l_3233_);
lean_dec(v_h__2_3231_);
v_size_3234_ = lean_ctor_get(v_x_3229_, 0);
lean_inc(v_size_3234_);
v_k_3235_ = lean_ctor_get(v_x_3229_, 1);
lean_inc(v_k_3235_);
v_v_3236_ = lean_ctor_get(v_x_3229_, 2);
lean_inc(v_v_3236_);
v_r_3237_ = lean_ctor_get(v_x_3229_, 4);
lean_inc(v_r_3237_);
lean_dec_ref_known(v_x_3229_, 5);
v_size_3238_ = lean_ctor_get(v_l_3233_, 0);
lean_inc(v_size_3238_);
v_k_3239_ = lean_ctor_get(v_l_3233_, 1);
lean_inc(v_k_3239_);
v_v_3240_ = lean_ctor_get(v_l_3233_, 2);
lean_inc(v_v_3240_);
v_l_3241_ = lean_ctor_get(v_l_3233_, 3);
lean_inc(v_l_3241_);
v_r_3242_ = lean_ctor_get(v_l_3233_, 4);
lean_inc(v_r_3242_);
lean_dec_ref_known(v_l_3233_, 5);
v___x_3243_ = lean_apply_9(v_h__3_3232_, v_size_3234_, v_k_3235_, v_v_3236_, v_size_3238_, v_k_3239_, v_v_3240_, v_l_3241_, v_r_3242_, v_r_3237_);
return v___x_3243_;
}
else
{
lean_object* v_size_3244_; lean_object* v_k_3245_; lean_object* v_v_3246_; lean_object* v_r_3247_; lean_object* v___x_3248_; 
lean_dec(v_h__3_3232_);
v_size_3244_ = lean_ctor_get(v_x_3229_, 0);
lean_inc(v_size_3244_);
v_k_3245_ = lean_ctor_get(v_x_3229_, 1);
lean_inc(v_k_3245_);
v_v_3246_ = lean_ctor_get(v_x_3229_, 2);
lean_inc(v_v_3246_);
v_r_3247_ = lean_ctor_get(v_x_3229_, 4);
lean_inc(v_r_3247_);
lean_dec_ref_known(v_x_3229_, 5);
v___x_3248_ = lean_apply_4(v_h__2_3231_, v_size_3244_, v_k_3245_, v_v_3246_, v_r_3247_);
return v___x_3248_;
}
}
else
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
lean_dec(v_h__3_3232_);
lean_dec(v_h__2_3231_);
v___x_3249_ = lean_box(0);
v___x_3250_ = lean_apply_1(v_h__1_3230_, v___x_3249_);
return v___x_3250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3251_, lean_object* v_00_u03b2_3252_, lean_object* v_motive_3253_, lean_object* v_x_3254_, lean_object* v_h__1_3255_, lean_object* v_h__2_3256_, lean_object* v_h__3_3257_){
_start:
{
if (lean_obj_tag(v_x_3254_) == 0)
{
lean_object* v_l_3258_; 
lean_dec(v_h__1_3255_);
v_l_3258_ = lean_ctor_get(v_x_3254_, 3);
if (lean_obj_tag(v_l_3258_) == 0)
{
lean_object* v_size_3259_; lean_object* v_k_3260_; lean_object* v_v_3261_; lean_object* v_r_3262_; lean_object* v_size_3263_; lean_object* v_k_3264_; lean_object* v_v_3265_; lean_object* v_l_3266_; lean_object* v_r_3267_; lean_object* v___x_3268_; 
lean_inc_ref(v_l_3258_);
lean_dec(v_h__2_3256_);
v_size_3259_ = lean_ctor_get(v_x_3254_, 0);
lean_inc(v_size_3259_);
v_k_3260_ = lean_ctor_get(v_x_3254_, 1);
lean_inc(v_k_3260_);
v_v_3261_ = lean_ctor_get(v_x_3254_, 2);
lean_inc(v_v_3261_);
v_r_3262_ = lean_ctor_get(v_x_3254_, 4);
lean_inc(v_r_3262_);
lean_dec_ref_known(v_x_3254_, 5);
v_size_3263_ = lean_ctor_get(v_l_3258_, 0);
lean_inc(v_size_3263_);
v_k_3264_ = lean_ctor_get(v_l_3258_, 1);
lean_inc(v_k_3264_);
v_v_3265_ = lean_ctor_get(v_l_3258_, 2);
lean_inc(v_v_3265_);
v_l_3266_ = lean_ctor_get(v_l_3258_, 3);
lean_inc(v_l_3266_);
v_r_3267_ = lean_ctor_get(v_l_3258_, 4);
lean_inc(v_r_3267_);
lean_dec_ref_known(v_l_3258_, 5);
v___x_3268_ = lean_apply_9(v_h__3_3257_, v_size_3259_, v_k_3260_, v_v_3261_, v_size_3263_, v_k_3264_, v_v_3265_, v_l_3266_, v_r_3267_, v_r_3262_);
return v___x_3268_;
}
else
{
lean_object* v_size_3269_; lean_object* v_k_3270_; lean_object* v_v_3271_; lean_object* v_r_3272_; lean_object* v___x_3273_; 
lean_dec(v_h__3_3257_);
v_size_3269_ = lean_ctor_get(v_x_3254_, 0);
lean_inc(v_size_3269_);
v_k_3270_ = lean_ctor_get(v_x_3254_, 1);
lean_inc(v_k_3270_);
v_v_3271_ = lean_ctor_get(v_x_3254_, 2);
lean_inc(v_v_3271_);
v_r_3272_ = lean_ctor_get(v_x_3254_, 4);
lean_inc(v_r_3272_);
lean_dec_ref_known(v_x_3254_, 5);
v___x_3273_ = lean_apply_4(v_h__2_3256_, v_size_3269_, v_k_3270_, v_v_3271_, v_r_3272_);
return v___x_3273_;
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec(v_h__3_3257_);
lean_dec(v_h__2_3256_);
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_apply_1(v_h__1_3255_, v___x_3274_);
return v___x_3275_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(lean_object* v_x_3276_){
_start:
{
lean_object* v_l_3277_; 
v_l_3277_ = lean_ctor_get(v_x_3276_, 3);
if (lean_obj_tag(v_l_3277_) == 0)
{
v_x_3276_ = v_l_3277_;
goto _start;
}
else
{
lean_object* v_k_3279_; lean_object* v_v_3280_; lean_object* v___x_3281_; 
v_k_3279_ = lean_ctor_get(v_x_3276_, 1);
v_v_3280_ = lean_ctor_get(v_x_3276_, 2);
lean_inc(v_v_3280_);
lean_inc(v_k_3279_);
v___x_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3281_, 0, v_k_3279_);
lean_ctor_set(v___x_3281_, 1, v_v_3280_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg___boxed(lean_object* v_x_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3282_);
lean_dec(v_x_3282_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry(lean_object* v_00_u03b1_3284_, lean_object* v_00_u03b2_3285_, lean_object* v_x_3286_, lean_object* v_x_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry___redArg(v_x_3286_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry___boxed(lean_object* v_00_u03b1_3289_, lean_object* v_00_u03b2_3290_, lean_object* v_x_3291_, lean_object* v_x_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry(v_00_u03b1_3289_, v_00_u03b2_3290_, v_x_3291_, v_x_3292_);
lean_dec(v_x_3291_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter___redArg(lean_object* v_x_3294_, lean_object* v_h__1_3295_, lean_object* v_h__2_3296_){
_start:
{
lean_object* v_l_3297_; 
v_l_3297_ = lean_ctor_get(v_x_3294_, 3);
if (lean_obj_tag(v_l_3297_) == 0)
{
lean_object* v_size_3298_; lean_object* v_k_3299_; lean_object* v_v_3300_; lean_object* v_r_3301_; lean_object* v_size_3302_; lean_object* v_k_3303_; lean_object* v_v_3304_; lean_object* v_l_3305_; lean_object* v_r_3306_; lean_object* v___x_3307_; 
lean_inc_ref(v_l_3297_);
lean_dec(v_h__1_3295_);
v_size_3298_ = lean_ctor_get(v_x_3294_, 0);
lean_inc(v_size_3298_);
v_k_3299_ = lean_ctor_get(v_x_3294_, 1);
lean_inc(v_k_3299_);
v_v_3300_ = lean_ctor_get(v_x_3294_, 2);
lean_inc(v_v_3300_);
v_r_3301_ = lean_ctor_get(v_x_3294_, 4);
lean_inc(v_r_3301_);
lean_dec(v_x_3294_);
v_size_3302_ = lean_ctor_get(v_l_3297_, 0);
lean_inc(v_size_3302_);
v_k_3303_ = lean_ctor_get(v_l_3297_, 1);
lean_inc(v_k_3303_);
v_v_3304_ = lean_ctor_get(v_l_3297_, 2);
lean_inc(v_v_3304_);
v_l_3305_ = lean_ctor_get(v_l_3297_, 3);
lean_inc(v_l_3305_);
v_r_3306_ = lean_ctor_get(v_l_3297_, 4);
lean_inc(v_r_3306_);
lean_dec_ref_known(v_l_3297_, 5);
v___x_3307_ = lean_apply_10(v_h__2_3296_, v_size_3298_, v_k_3299_, v_v_3300_, v_size_3302_, v_k_3303_, v_v_3304_, v_l_3305_, v_r_3306_, v_r_3301_, lean_box(0));
return v___x_3307_;
}
else
{
lean_object* v_size_3308_; lean_object* v_k_3309_; lean_object* v_v_3310_; lean_object* v_r_3311_; lean_object* v___x_3312_; 
lean_dec(v_h__2_3296_);
v_size_3308_ = lean_ctor_get(v_x_3294_, 0);
lean_inc(v_size_3308_);
v_k_3309_ = lean_ctor_get(v_x_3294_, 1);
lean_inc(v_k_3309_);
v_v_3310_ = lean_ctor_get(v_x_3294_, 2);
lean_inc(v_v_3310_);
v_r_3311_ = lean_ctor_get(v_x_3294_, 4);
lean_inc(v_r_3311_);
lean_dec(v_x_3294_);
v___x_3312_ = lean_apply_5(v_h__1_3295_, v_size_3308_, v_k_3309_, v_v_3310_, v_r_3311_, lean_box(0));
return v___x_3312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntry_match__1_splitter(lean_object* v_00_u03b1_3313_, lean_object* v_00_u03b2_3314_, lean_object* v_motive_3315_, lean_object* v_x_3316_, lean_object* v_x_3317_, lean_object* v_h__1_3318_, lean_object* v_h__2_3319_){
_start:
{
lean_object* v_l_3320_; 
v_l_3320_ = lean_ctor_get(v_x_3316_, 3);
if (lean_obj_tag(v_l_3320_) == 0)
{
lean_object* v_size_3321_; lean_object* v_k_3322_; lean_object* v_v_3323_; lean_object* v_r_3324_; lean_object* v_size_3325_; lean_object* v_k_3326_; lean_object* v_v_3327_; lean_object* v_l_3328_; lean_object* v_r_3329_; lean_object* v___x_3330_; 
lean_inc_ref(v_l_3320_);
lean_dec(v_h__1_3318_);
v_size_3321_ = lean_ctor_get(v_x_3316_, 0);
lean_inc(v_size_3321_);
v_k_3322_ = lean_ctor_get(v_x_3316_, 1);
lean_inc(v_k_3322_);
v_v_3323_ = lean_ctor_get(v_x_3316_, 2);
lean_inc(v_v_3323_);
v_r_3324_ = lean_ctor_get(v_x_3316_, 4);
lean_inc(v_r_3324_);
lean_dec(v_x_3316_);
v_size_3325_ = lean_ctor_get(v_l_3320_, 0);
lean_inc(v_size_3325_);
v_k_3326_ = lean_ctor_get(v_l_3320_, 1);
lean_inc(v_k_3326_);
v_v_3327_ = lean_ctor_get(v_l_3320_, 2);
lean_inc(v_v_3327_);
v_l_3328_ = lean_ctor_get(v_l_3320_, 3);
lean_inc(v_l_3328_);
v_r_3329_ = lean_ctor_get(v_l_3320_, 4);
lean_inc(v_r_3329_);
lean_dec_ref_known(v_l_3320_, 5);
v___x_3330_ = lean_apply_10(v_h__2_3319_, v_size_3321_, v_k_3322_, v_v_3323_, v_size_3325_, v_k_3326_, v_v_3327_, v_l_3328_, v_r_3329_, v_r_3324_, lean_box(0));
return v___x_3330_;
}
else
{
lean_object* v_size_3331_; lean_object* v_k_3332_; lean_object* v_v_3333_; lean_object* v_r_3334_; lean_object* v___x_3335_; 
lean_dec(v_h__2_3319_);
v_size_3331_ = lean_ctor_get(v_x_3316_, 0);
lean_inc(v_size_3331_);
v_k_3332_ = lean_ctor_get(v_x_3316_, 1);
lean_inc(v_k_3332_);
v_v_3333_ = lean_ctor_get(v_x_3316_, 2);
lean_inc(v_v_3333_);
v_r_3334_ = lean_ctor_get(v_x_3316_, 4);
lean_inc(v_r_3334_);
lean_dec(v_x_3316_);
v___x_3335_ = lean_apply_5(v_h__1_3318_, v_size_3331_, v_k_3332_, v_v_3333_, v_r_3334_, lean_box(0));
return v___x_3335_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; 
v___x_3337_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3338_ = lean_unsigned_to_nat(13u);
v___x_3339_ = lean_unsigned_to_nat(816u);
v___x_3340_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__0));
v___x_3341_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3342_ = l_mkPanicMessageWithDecl(v___x_3341_, v___x_3340_, v___x_3339_, v___x_3338_, v___x_3337_);
return v___x_3342_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(lean_object* v_inst_3343_, lean_object* v_x_3344_){
_start:
{
if (lean_obj_tag(v_x_3344_) == 0)
{
lean_object* v_l_3345_; 
v_l_3345_ = lean_ctor_get(v_x_3344_, 3);
if (lean_obj_tag(v_l_3345_) == 0)
{
v_x_3344_ = v_l_3345_;
goto _start;
}
else
{
lean_object* v_k_3347_; lean_object* v_v_3348_; lean_object* v___x_3349_; 
v_k_3347_ = lean_ctor_get(v_x_3344_, 1);
v_v_3348_ = lean_ctor_get(v_x_3344_, 2);
lean_inc(v_v_3348_);
lean_inc(v_k_3347_);
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v_k_3347_);
lean_ctor_set(v___x_3349_, 1, v_v_3348_);
return v___x_3349_;
}
}
else
{
lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3350_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___closed__1);
v___x_3351_ = l_panic___redArg(v_inst_3343_, v___x_3350_);
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg___boxed(lean_object* v_inst_3352_, lean_object* v_x_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3352_, v_x_3353_);
lean_dec(v_x_3353_);
lean_dec_ref(v_inst_3352_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(lean_object* v_00_u03b1_3355_, lean_object* v_00_u03b2_3356_, lean_object* v_inst_3357_, lean_object* v_x_3358_){
_start:
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___redArg(v_inst_3357_, v_x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21___boxed(lean_object* v_00_u03b1_3360_, lean_object* v_00_u03b2_3361_, lean_object* v_inst_3362_, lean_object* v_x_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l_Std_DTreeMap_Internal_Impl_Const_minEntry_x21(v_00_u03b1_3360_, v_00_u03b2_3361_, v_inst_3362_, v_x_3363_);
lean_dec(v_x_3363_);
lean_dec_ref(v_inst_3362_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(lean_object* v_x_3365_, lean_object* v_x_3366_){
_start:
{
if (lean_obj_tag(v_x_3365_) == 0)
{
lean_object* v_l_3367_; 
v_l_3367_ = lean_ctor_get(v_x_3365_, 3);
if (lean_obj_tag(v_l_3367_) == 0)
{
v_x_3365_ = v_l_3367_;
goto _start;
}
else
{
lean_object* v_k_3369_; lean_object* v_v_3370_; lean_object* v___x_3371_; 
v_k_3369_ = lean_ctor_get(v_x_3365_, 1);
v_v_3370_ = lean_ctor_get(v_x_3365_, 2);
lean_inc(v_v_3370_);
lean_inc(v_k_3369_);
v___x_3371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3371_, 0, v_k_3369_);
lean_ctor_set(v___x_3371_, 1, v_v_3370_);
return v___x_3371_;
}
}
else
{
lean_inc_ref(v_x_3366_);
return v_x_3366_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg___boxed(lean_object* v_x_3372_, lean_object* v_x_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3372_, v_x_3373_);
lean_dec_ref(v_x_3373_);
lean_dec(v_x_3372_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD(lean_object* v_00_u03b1_3375_, lean_object* v_00_u03b2_3376_, lean_object* v_x_3377_, lean_object* v_x_3378_){
_start:
{
lean_object* v___x_3379_; 
v___x_3379_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD___redArg(v_x_3377_, v_x_3378_);
return v___x_3379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_minEntryD___boxed(lean_object* v_00_u03b1_3380_, lean_object* v_00_u03b2_3381_, lean_object* v_x_3382_, lean_object* v_x_3383_){
_start:
{
lean_object* v_res_3384_; 
v_res_3384_ = l_Std_DTreeMap_Internal_Impl_Const_minEntryD(v_00_u03b1_3380_, v_00_u03b2_3381_, v_x_3382_, v_x_3383_);
lean_dec_ref(v_x_3383_);
lean_dec(v_x_3382_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter___redArg(lean_object* v_x_3385_, lean_object* v_x_3386_, lean_object* v_h__1_3387_, lean_object* v_h__2_3388_, lean_object* v_h__3_3389_){
_start:
{
if (lean_obj_tag(v_x_3385_) == 0)
{
lean_object* v_l_3390_; 
lean_dec(v_h__1_3387_);
v_l_3390_ = lean_ctor_get(v_x_3385_, 3);
if (lean_obj_tag(v_l_3390_) == 0)
{
lean_object* v_size_3391_; lean_object* v_k_3392_; lean_object* v_v_3393_; lean_object* v_r_3394_; lean_object* v_size_3395_; lean_object* v_k_3396_; lean_object* v_v_3397_; lean_object* v_l_3398_; lean_object* v_r_3399_; lean_object* v___x_3400_; 
lean_inc_ref(v_l_3390_);
lean_dec(v_h__2_3388_);
v_size_3391_ = lean_ctor_get(v_x_3385_, 0);
lean_inc(v_size_3391_);
v_k_3392_ = lean_ctor_get(v_x_3385_, 1);
lean_inc(v_k_3392_);
v_v_3393_ = lean_ctor_get(v_x_3385_, 2);
lean_inc(v_v_3393_);
v_r_3394_ = lean_ctor_get(v_x_3385_, 4);
lean_inc(v_r_3394_);
lean_dec_ref_known(v_x_3385_, 5);
v_size_3395_ = lean_ctor_get(v_l_3390_, 0);
lean_inc(v_size_3395_);
v_k_3396_ = lean_ctor_get(v_l_3390_, 1);
lean_inc(v_k_3396_);
v_v_3397_ = lean_ctor_get(v_l_3390_, 2);
lean_inc(v_v_3397_);
v_l_3398_ = lean_ctor_get(v_l_3390_, 3);
lean_inc(v_l_3398_);
v_r_3399_ = lean_ctor_get(v_l_3390_, 4);
lean_inc(v_r_3399_);
lean_dec_ref_known(v_l_3390_, 5);
v___x_3400_ = lean_apply_10(v_h__3_3389_, v_size_3391_, v_k_3392_, v_v_3393_, v_size_3395_, v_k_3396_, v_v_3397_, v_l_3398_, v_r_3399_, v_r_3394_, v_x_3386_);
return v___x_3400_;
}
else
{
lean_object* v_size_3401_; lean_object* v_k_3402_; lean_object* v_v_3403_; lean_object* v_r_3404_; lean_object* v___x_3405_; 
lean_dec(v_h__3_3389_);
v_size_3401_ = lean_ctor_get(v_x_3385_, 0);
lean_inc(v_size_3401_);
v_k_3402_ = lean_ctor_get(v_x_3385_, 1);
lean_inc(v_k_3402_);
v_v_3403_ = lean_ctor_get(v_x_3385_, 2);
lean_inc(v_v_3403_);
v_r_3404_ = lean_ctor_get(v_x_3385_, 4);
lean_inc(v_r_3404_);
lean_dec_ref_known(v_x_3385_, 5);
v___x_3405_ = lean_apply_5(v_h__2_3388_, v_size_3401_, v_k_3402_, v_v_3403_, v_r_3404_, v_x_3386_);
return v___x_3405_;
}
}
else
{
lean_object* v___x_3406_; 
lean_dec(v_h__3_3389_);
lean_dec(v_h__2_3388_);
v___x_3406_ = lean_apply_1(v_h__1_3387_, v_x_3386_);
return v___x_3406_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_minEntryD_match__1_splitter(lean_object* v_00_u03b1_3407_, lean_object* v_00_u03b2_3408_, lean_object* v_motive_3409_, lean_object* v_x_3410_, lean_object* v_x_3411_, lean_object* v_h__1_3412_, lean_object* v_h__2_3413_, lean_object* v_h__3_3414_){
_start:
{
if (lean_obj_tag(v_x_3410_) == 0)
{
lean_object* v_l_3415_; 
lean_dec(v_h__1_3412_);
v_l_3415_ = lean_ctor_get(v_x_3410_, 3);
if (lean_obj_tag(v_l_3415_) == 0)
{
lean_object* v_size_3416_; lean_object* v_k_3417_; lean_object* v_v_3418_; lean_object* v_r_3419_; lean_object* v_size_3420_; lean_object* v_k_3421_; lean_object* v_v_3422_; lean_object* v_l_3423_; lean_object* v_r_3424_; lean_object* v___x_3425_; 
lean_inc_ref(v_l_3415_);
lean_dec(v_h__2_3413_);
v_size_3416_ = lean_ctor_get(v_x_3410_, 0);
lean_inc(v_size_3416_);
v_k_3417_ = lean_ctor_get(v_x_3410_, 1);
lean_inc(v_k_3417_);
v_v_3418_ = lean_ctor_get(v_x_3410_, 2);
lean_inc(v_v_3418_);
v_r_3419_ = lean_ctor_get(v_x_3410_, 4);
lean_inc(v_r_3419_);
lean_dec_ref_known(v_x_3410_, 5);
v_size_3420_ = lean_ctor_get(v_l_3415_, 0);
lean_inc(v_size_3420_);
v_k_3421_ = lean_ctor_get(v_l_3415_, 1);
lean_inc(v_k_3421_);
v_v_3422_ = lean_ctor_get(v_l_3415_, 2);
lean_inc(v_v_3422_);
v_l_3423_ = lean_ctor_get(v_l_3415_, 3);
lean_inc(v_l_3423_);
v_r_3424_ = lean_ctor_get(v_l_3415_, 4);
lean_inc(v_r_3424_);
lean_dec_ref_known(v_l_3415_, 5);
v___x_3425_ = lean_apply_10(v_h__3_3414_, v_size_3416_, v_k_3417_, v_v_3418_, v_size_3420_, v_k_3421_, v_v_3422_, v_l_3423_, v_r_3424_, v_r_3419_, v_x_3411_);
return v___x_3425_;
}
else
{
lean_object* v_size_3426_; lean_object* v_k_3427_; lean_object* v_v_3428_; lean_object* v_r_3429_; lean_object* v___x_3430_; 
lean_dec(v_h__3_3414_);
v_size_3426_ = lean_ctor_get(v_x_3410_, 0);
lean_inc(v_size_3426_);
v_k_3427_ = lean_ctor_get(v_x_3410_, 1);
lean_inc(v_k_3427_);
v_v_3428_ = lean_ctor_get(v_x_3410_, 2);
lean_inc(v_v_3428_);
v_r_3429_ = lean_ctor_get(v_x_3410_, 4);
lean_inc(v_r_3429_);
lean_dec_ref_known(v_x_3410_, 5);
v___x_3430_ = lean_apply_5(v_h__2_3413_, v_size_3426_, v_k_3427_, v_v_3428_, v_r_3429_, v_x_3411_);
return v___x_3430_;
}
}
else
{
lean_object* v___x_3431_; 
lean_dec(v_h__3_3414_);
lean_dec(v_h__2_3413_);
v___x_3431_ = lean_apply_1(v_h__1_3412_, v_x_3411_);
return v___x_3431_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(lean_object* v_x_3432_){
_start:
{
if (lean_obj_tag(v_x_3432_) == 0)
{
lean_object* v_r_3433_; 
v_r_3433_ = lean_ctor_get(v_x_3432_, 4);
if (lean_obj_tag(v_r_3433_) == 0)
{
v_x_3432_ = v_r_3433_;
goto _start;
}
else
{
lean_object* v_k_3435_; lean_object* v_v_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v_k_3435_ = lean_ctor_get(v_x_3432_, 1);
v_v_3436_ = lean_ctor_get(v_x_3432_, 2);
lean_inc(v_v_3436_);
lean_inc(v_k_3435_);
v___x_3437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3437_, 0, v_k_3435_);
lean_ctor_set(v___x_3437_, 1, v_v_3436_);
v___x_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
}
else
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_box(0);
return v___x_3439_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg___boxed(lean_object* v_x_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3440_);
lean_dec(v_x_3440_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(lean_object* v_00_u03b1_3442_, lean_object* v_00_u03b2_3443_, lean_object* v_x_3444_){
_start:
{
lean_object* v___x_3445_; 
v___x_3445_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___redArg(v_x_3444_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f___boxed(lean_object* v_00_u03b1_3446_, lean_object* v_00_u03b2_3447_, lean_object* v_x_3448_){
_start:
{
lean_object* v_res_3449_; 
v_res_3449_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f(v_00_u03b1_3446_, v_00_u03b2_3447_, v_x_3448_);
lean_dec(v_x_3448_);
return v_res_3449_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter___redArg(lean_object* v_x_3450_, lean_object* v_h__1_3451_, lean_object* v_h__2_3452_, lean_object* v_h__3_3453_){
_start:
{
if (lean_obj_tag(v_x_3450_) == 0)
{
lean_object* v_r_3454_; 
lean_dec(v_h__1_3451_);
v_r_3454_ = lean_ctor_get(v_x_3450_, 4);
if (lean_obj_tag(v_r_3454_) == 0)
{
lean_object* v_size_3455_; lean_object* v_k_3456_; lean_object* v_v_3457_; lean_object* v_l_3458_; lean_object* v_size_3459_; lean_object* v_k_3460_; lean_object* v_v_3461_; lean_object* v_l_3462_; lean_object* v_r_3463_; lean_object* v___x_3464_; 
lean_inc_ref(v_r_3454_);
lean_dec(v_h__2_3452_);
v_size_3455_ = lean_ctor_get(v_x_3450_, 0);
lean_inc(v_size_3455_);
v_k_3456_ = lean_ctor_get(v_x_3450_, 1);
lean_inc(v_k_3456_);
v_v_3457_ = lean_ctor_get(v_x_3450_, 2);
lean_inc(v_v_3457_);
v_l_3458_ = lean_ctor_get(v_x_3450_, 3);
lean_inc(v_l_3458_);
lean_dec_ref_known(v_x_3450_, 5);
v_size_3459_ = lean_ctor_get(v_r_3454_, 0);
lean_inc(v_size_3459_);
v_k_3460_ = lean_ctor_get(v_r_3454_, 1);
lean_inc(v_k_3460_);
v_v_3461_ = lean_ctor_get(v_r_3454_, 2);
lean_inc(v_v_3461_);
v_l_3462_ = lean_ctor_get(v_r_3454_, 3);
lean_inc(v_l_3462_);
v_r_3463_ = lean_ctor_get(v_r_3454_, 4);
lean_inc(v_r_3463_);
lean_dec_ref_known(v_r_3454_, 5);
v___x_3464_ = lean_apply_9(v_h__3_3453_, v_size_3455_, v_k_3456_, v_v_3457_, v_l_3458_, v_size_3459_, v_k_3460_, v_v_3461_, v_l_3462_, v_r_3463_);
return v___x_3464_;
}
else
{
lean_object* v_size_3465_; lean_object* v_k_3466_; lean_object* v_v_3467_; lean_object* v_l_3468_; lean_object* v___x_3469_; 
lean_dec(v_h__3_3453_);
v_size_3465_ = lean_ctor_get(v_x_3450_, 0);
lean_inc(v_size_3465_);
v_k_3466_ = lean_ctor_get(v_x_3450_, 1);
lean_inc(v_k_3466_);
v_v_3467_ = lean_ctor_get(v_x_3450_, 2);
lean_inc(v_v_3467_);
v_l_3468_ = lean_ctor_get(v_x_3450_, 3);
lean_inc(v_l_3468_);
lean_dec_ref_known(v_x_3450_, 5);
v___x_3469_ = lean_apply_4(v_h__2_3452_, v_size_3465_, v_k_3466_, v_v_3467_, v_l_3468_);
return v___x_3469_;
}
}
else
{
lean_object* v___x_3470_; lean_object* v___x_3471_; 
lean_dec(v_h__3_3453_);
lean_dec(v_h__2_3452_);
v___x_3470_ = lean_box(0);
v___x_3471_ = lean_apply_1(v_h__1_3451_, v___x_3470_);
return v___x_3471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_x3f_match__1_splitter(lean_object* v_00_u03b1_3472_, lean_object* v_00_u03b2_3473_, lean_object* v_motive_3474_, lean_object* v_x_3475_, lean_object* v_h__1_3476_, lean_object* v_h__2_3477_, lean_object* v_h__3_3478_){
_start:
{
if (lean_obj_tag(v_x_3475_) == 0)
{
lean_object* v_r_3479_; 
lean_dec(v_h__1_3476_);
v_r_3479_ = lean_ctor_get(v_x_3475_, 4);
if (lean_obj_tag(v_r_3479_) == 0)
{
lean_object* v_size_3480_; lean_object* v_k_3481_; lean_object* v_v_3482_; lean_object* v_l_3483_; lean_object* v_size_3484_; lean_object* v_k_3485_; lean_object* v_v_3486_; lean_object* v_l_3487_; lean_object* v_r_3488_; lean_object* v___x_3489_; 
lean_inc_ref(v_r_3479_);
lean_dec(v_h__2_3477_);
v_size_3480_ = lean_ctor_get(v_x_3475_, 0);
lean_inc(v_size_3480_);
v_k_3481_ = lean_ctor_get(v_x_3475_, 1);
lean_inc(v_k_3481_);
v_v_3482_ = lean_ctor_get(v_x_3475_, 2);
lean_inc(v_v_3482_);
v_l_3483_ = lean_ctor_get(v_x_3475_, 3);
lean_inc(v_l_3483_);
lean_dec_ref_known(v_x_3475_, 5);
v_size_3484_ = lean_ctor_get(v_r_3479_, 0);
lean_inc(v_size_3484_);
v_k_3485_ = lean_ctor_get(v_r_3479_, 1);
lean_inc(v_k_3485_);
v_v_3486_ = lean_ctor_get(v_r_3479_, 2);
lean_inc(v_v_3486_);
v_l_3487_ = lean_ctor_get(v_r_3479_, 3);
lean_inc(v_l_3487_);
v_r_3488_ = lean_ctor_get(v_r_3479_, 4);
lean_inc(v_r_3488_);
lean_dec_ref_known(v_r_3479_, 5);
v___x_3489_ = lean_apply_9(v_h__3_3478_, v_size_3480_, v_k_3481_, v_v_3482_, v_l_3483_, v_size_3484_, v_k_3485_, v_v_3486_, v_l_3487_, v_r_3488_);
return v___x_3489_;
}
else
{
lean_object* v_size_3490_; lean_object* v_k_3491_; lean_object* v_v_3492_; lean_object* v_l_3493_; lean_object* v___x_3494_; 
lean_dec(v_h__3_3478_);
v_size_3490_ = lean_ctor_get(v_x_3475_, 0);
lean_inc(v_size_3490_);
v_k_3491_ = lean_ctor_get(v_x_3475_, 1);
lean_inc(v_k_3491_);
v_v_3492_ = lean_ctor_get(v_x_3475_, 2);
lean_inc(v_v_3492_);
v_l_3493_ = lean_ctor_get(v_x_3475_, 3);
lean_inc(v_l_3493_);
lean_dec_ref_known(v_x_3475_, 5);
v___x_3494_ = lean_apply_4(v_h__2_3477_, v_size_3490_, v_k_3491_, v_v_3492_, v_l_3493_);
return v___x_3494_;
}
}
else
{
lean_object* v___x_3495_; lean_object* v___x_3496_; 
lean_dec(v_h__3_3478_);
lean_dec(v_h__2_3477_);
v___x_3495_ = lean_box(0);
v___x_3496_ = lean_apply_1(v_h__1_3476_, v___x_3495_);
return v___x_3496_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(lean_object* v_x_3497_){
_start:
{
lean_object* v_r_3498_; 
v_r_3498_ = lean_ctor_get(v_x_3497_, 4);
if (lean_obj_tag(v_r_3498_) == 0)
{
v_x_3497_ = v_r_3498_;
goto _start;
}
else
{
lean_object* v_k_3500_; lean_object* v_v_3501_; lean_object* v___x_3502_; 
v_k_3500_ = lean_ctor_get(v_x_3497_, 1);
v_v_3501_ = lean_ctor_get(v_x_3497_, 2);
lean_inc(v_v_3501_);
lean_inc(v_k_3500_);
v___x_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3502_, 0, v_k_3500_);
lean_ctor_set(v___x_3502_, 1, v_v_3501_);
return v___x_3502_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg___boxed(lean_object* v_x_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3503_);
lean_dec(v_x_3503_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry(lean_object* v_00_u03b1_3505_, lean_object* v_00_u03b2_3506_, lean_object* v_x_3507_, lean_object* v_x_3508_){
_start:
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry___redArg(v_x_3507_);
return v___x_3509_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry___boxed(lean_object* v_00_u03b1_3510_, lean_object* v_00_u03b2_3511_, lean_object* v_x_3512_, lean_object* v_x_3513_){
_start:
{
lean_object* v_res_3514_; 
v_res_3514_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry(v_00_u03b1_3510_, v_00_u03b2_3511_, v_x_3512_, v_x_3513_);
lean_dec(v_x_3512_);
return v_res_3514_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter___redArg(lean_object* v_x_3515_, lean_object* v_h__1_3516_, lean_object* v_h__2_3517_){
_start:
{
lean_object* v_r_3518_; 
v_r_3518_ = lean_ctor_get(v_x_3515_, 4);
if (lean_obj_tag(v_r_3518_) == 0)
{
lean_object* v_size_3519_; lean_object* v_k_3520_; lean_object* v_v_3521_; lean_object* v_l_3522_; lean_object* v_size_3523_; lean_object* v_k_3524_; lean_object* v_v_3525_; lean_object* v_l_3526_; lean_object* v_r_3527_; lean_object* v___x_3528_; 
lean_inc_ref(v_r_3518_);
lean_dec(v_h__1_3516_);
v_size_3519_ = lean_ctor_get(v_x_3515_, 0);
lean_inc(v_size_3519_);
v_k_3520_ = lean_ctor_get(v_x_3515_, 1);
lean_inc(v_k_3520_);
v_v_3521_ = lean_ctor_get(v_x_3515_, 2);
lean_inc(v_v_3521_);
v_l_3522_ = lean_ctor_get(v_x_3515_, 3);
lean_inc(v_l_3522_);
lean_dec(v_x_3515_);
v_size_3523_ = lean_ctor_get(v_r_3518_, 0);
lean_inc(v_size_3523_);
v_k_3524_ = lean_ctor_get(v_r_3518_, 1);
lean_inc(v_k_3524_);
v_v_3525_ = lean_ctor_get(v_r_3518_, 2);
lean_inc(v_v_3525_);
v_l_3526_ = lean_ctor_get(v_r_3518_, 3);
lean_inc(v_l_3526_);
v_r_3527_ = lean_ctor_get(v_r_3518_, 4);
lean_inc(v_r_3527_);
lean_dec_ref_known(v_r_3518_, 5);
v___x_3528_ = lean_apply_10(v_h__2_3517_, v_size_3519_, v_k_3520_, v_v_3521_, v_l_3522_, v_size_3523_, v_k_3524_, v_v_3525_, v_l_3526_, v_r_3527_, lean_box(0));
return v___x_3528_;
}
else
{
lean_object* v_size_3529_; lean_object* v_k_3530_; lean_object* v_v_3531_; lean_object* v_l_3532_; lean_object* v___x_3533_; 
lean_dec(v_h__2_3517_);
v_size_3529_ = lean_ctor_get(v_x_3515_, 0);
lean_inc(v_size_3529_);
v_k_3530_ = lean_ctor_get(v_x_3515_, 1);
lean_inc(v_k_3530_);
v_v_3531_ = lean_ctor_get(v_x_3515_, 2);
lean_inc(v_v_3531_);
v_l_3532_ = lean_ctor_get(v_x_3515_, 3);
lean_inc(v_l_3532_);
lean_dec(v_x_3515_);
v___x_3533_ = lean_apply_5(v_h__1_3516_, v_size_3529_, v_k_3530_, v_v_3531_, v_l_3532_, lean_box(0));
return v___x_3533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntry_match__1_splitter(lean_object* v_00_u03b1_3534_, lean_object* v_00_u03b2_3535_, lean_object* v_motive_3536_, lean_object* v_x_3537_, lean_object* v_x_3538_, lean_object* v_h__1_3539_, lean_object* v_h__2_3540_){
_start:
{
lean_object* v_r_3541_; 
v_r_3541_ = lean_ctor_get(v_x_3537_, 4);
if (lean_obj_tag(v_r_3541_) == 0)
{
lean_object* v_size_3542_; lean_object* v_k_3543_; lean_object* v_v_3544_; lean_object* v_l_3545_; lean_object* v_size_3546_; lean_object* v_k_3547_; lean_object* v_v_3548_; lean_object* v_l_3549_; lean_object* v_r_3550_; lean_object* v___x_3551_; 
lean_inc_ref(v_r_3541_);
lean_dec(v_h__1_3539_);
v_size_3542_ = lean_ctor_get(v_x_3537_, 0);
lean_inc(v_size_3542_);
v_k_3543_ = lean_ctor_get(v_x_3537_, 1);
lean_inc(v_k_3543_);
v_v_3544_ = lean_ctor_get(v_x_3537_, 2);
lean_inc(v_v_3544_);
v_l_3545_ = lean_ctor_get(v_x_3537_, 3);
lean_inc(v_l_3545_);
lean_dec(v_x_3537_);
v_size_3546_ = lean_ctor_get(v_r_3541_, 0);
lean_inc(v_size_3546_);
v_k_3547_ = lean_ctor_get(v_r_3541_, 1);
lean_inc(v_k_3547_);
v_v_3548_ = lean_ctor_get(v_r_3541_, 2);
lean_inc(v_v_3548_);
v_l_3549_ = lean_ctor_get(v_r_3541_, 3);
lean_inc(v_l_3549_);
v_r_3550_ = lean_ctor_get(v_r_3541_, 4);
lean_inc(v_r_3550_);
lean_dec_ref_known(v_r_3541_, 5);
v___x_3551_ = lean_apply_10(v_h__2_3540_, v_size_3542_, v_k_3543_, v_v_3544_, v_l_3545_, v_size_3546_, v_k_3547_, v_v_3548_, v_l_3549_, v_r_3550_, lean_box(0));
return v___x_3551_;
}
else
{
lean_object* v_size_3552_; lean_object* v_k_3553_; lean_object* v_v_3554_; lean_object* v_l_3555_; lean_object* v___x_3556_; 
lean_dec(v_h__2_3540_);
v_size_3552_ = lean_ctor_get(v_x_3537_, 0);
lean_inc(v_size_3552_);
v_k_3553_ = lean_ctor_get(v_x_3537_, 1);
lean_inc(v_k_3553_);
v_v_3554_ = lean_ctor_get(v_x_3537_, 2);
lean_inc(v_v_3554_);
v_l_3555_ = lean_ctor_get(v_x_3537_, 3);
lean_inc(v_l_3555_);
lean_dec(v_x_3537_);
v___x_3556_ = lean_apply_5(v_h__1_3539_, v_size_3552_, v_k_3553_, v_v_3554_, v_l_3555_, lean_box(0));
return v___x_3556_;
}
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3558_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_minEntry_x21___redArg___closed__1));
v___x_3559_ = lean_unsigned_to_nat(13u);
v___x_3560_ = lean_unsigned_to_nat(839u);
v___x_3561_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__0));
v___x_3562_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3563_ = l_mkPanicMessageWithDecl(v___x_3562_, v___x_3561_, v___x_3560_, v___x_3559_, v___x_3558_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(lean_object* v_inst_3564_, lean_object* v_x_3565_){
_start:
{
if (lean_obj_tag(v_x_3565_) == 0)
{
lean_object* v_r_3566_; 
v_r_3566_ = lean_ctor_get(v_x_3565_, 4);
if (lean_obj_tag(v_r_3566_) == 0)
{
v_x_3565_ = v_r_3566_;
goto _start;
}
else
{
lean_object* v_k_3568_; lean_object* v_v_3569_; lean_object* v___x_3570_; 
v_k_3568_ = lean_ctor_get(v_x_3565_, 1);
v_v_3569_ = lean_ctor_get(v_x_3565_, 2);
lean_inc(v_v_3569_);
lean_inc(v_k_3568_);
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_k_3568_);
lean_ctor_set(v___x_3570_, 1, v_v_3569_);
return v___x_3570_;
}
}
else
{
lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3571_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___closed__1);
v___x_3572_ = l_panic___redArg(v_inst_3564_, v___x_3571_);
return v___x_3572_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg___boxed(lean_object* v_inst_3573_, lean_object* v_x_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3573_, v_x_3574_);
lean_dec(v_x_3574_);
lean_dec_ref(v_inst_3573_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(lean_object* v_00_u03b1_3576_, lean_object* v_00_u03b2_3577_, lean_object* v_inst_3578_, lean_object* v_x_3579_){
_start:
{
lean_object* v___x_3580_; 
v___x_3580_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___redArg(v_inst_3578_, v_x_3579_);
return v___x_3580_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21___boxed(lean_object* v_00_u03b1_3581_, lean_object* v_00_u03b2_3582_, lean_object* v_inst_3583_, lean_object* v_x_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntry_x21(v_00_u03b1_3581_, v_00_u03b2_3582_, v_inst_3583_, v_x_3584_);
lean_dec(v_x_3584_);
lean_dec_ref(v_inst_3583_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(lean_object* v_x_3586_, lean_object* v_x_3587_){
_start:
{
if (lean_obj_tag(v_x_3586_) == 0)
{
lean_object* v_r_3588_; 
v_r_3588_ = lean_ctor_get(v_x_3586_, 4);
if (lean_obj_tag(v_r_3588_) == 0)
{
v_x_3586_ = v_r_3588_;
goto _start;
}
else
{
lean_object* v_k_3590_; lean_object* v_v_3591_; lean_object* v___x_3592_; 
v_k_3590_ = lean_ctor_get(v_x_3586_, 1);
v_v_3591_ = lean_ctor_get(v_x_3586_, 2);
lean_inc(v_v_3591_);
lean_inc(v_k_3590_);
v___x_3592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3592_, 0, v_k_3590_);
lean_ctor_set(v___x_3592_, 1, v_v_3591_);
return v___x_3592_;
}
}
else
{
lean_inc_ref(v_x_3587_);
return v_x_3587_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg___boxed(lean_object* v_x_3593_, lean_object* v_x_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3593_, v_x_3594_);
lean_dec_ref(v_x_3594_);
lean_dec(v_x_3593_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(lean_object* v_00_u03b1_3596_, lean_object* v_00_u03b2_3597_, lean_object* v_x_3598_, lean_object* v_x_3599_){
_start:
{
lean_object* v___x_3600_; 
v___x_3600_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___redArg(v_x_3598_, v_x_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_maxEntryD___boxed(lean_object* v_00_u03b1_3601_, lean_object* v_00_u03b2_3602_, lean_object* v_x_3603_, lean_object* v_x_3604_){
_start:
{
lean_object* v_res_3605_; 
v_res_3605_ = l_Std_DTreeMap_Internal_Impl_Const_maxEntryD(v_00_u03b1_3601_, v_00_u03b2_3602_, v_x_3603_, v_x_3604_);
lean_dec_ref(v_x_3604_);
lean_dec(v_x_3603_);
return v_res_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter___redArg(lean_object* v_x_3606_, lean_object* v_x_3607_, lean_object* v_h__1_3608_, lean_object* v_h__2_3609_, lean_object* v_h__3_3610_){
_start:
{
if (lean_obj_tag(v_x_3606_) == 0)
{
lean_object* v_r_3611_; 
lean_dec(v_h__1_3608_);
v_r_3611_ = lean_ctor_get(v_x_3606_, 4);
if (lean_obj_tag(v_r_3611_) == 0)
{
lean_object* v_size_3612_; lean_object* v_k_3613_; lean_object* v_v_3614_; lean_object* v_l_3615_; lean_object* v_size_3616_; lean_object* v_k_3617_; lean_object* v_v_3618_; lean_object* v_l_3619_; lean_object* v_r_3620_; lean_object* v___x_3621_; 
lean_inc_ref(v_r_3611_);
lean_dec(v_h__2_3609_);
v_size_3612_ = lean_ctor_get(v_x_3606_, 0);
lean_inc(v_size_3612_);
v_k_3613_ = lean_ctor_get(v_x_3606_, 1);
lean_inc(v_k_3613_);
v_v_3614_ = lean_ctor_get(v_x_3606_, 2);
lean_inc(v_v_3614_);
v_l_3615_ = lean_ctor_get(v_x_3606_, 3);
lean_inc(v_l_3615_);
lean_dec_ref_known(v_x_3606_, 5);
v_size_3616_ = lean_ctor_get(v_r_3611_, 0);
lean_inc(v_size_3616_);
v_k_3617_ = lean_ctor_get(v_r_3611_, 1);
lean_inc(v_k_3617_);
v_v_3618_ = lean_ctor_get(v_r_3611_, 2);
lean_inc(v_v_3618_);
v_l_3619_ = lean_ctor_get(v_r_3611_, 3);
lean_inc(v_l_3619_);
v_r_3620_ = lean_ctor_get(v_r_3611_, 4);
lean_inc(v_r_3620_);
lean_dec_ref_known(v_r_3611_, 5);
v___x_3621_ = lean_apply_10(v_h__3_3610_, v_size_3612_, v_k_3613_, v_v_3614_, v_l_3615_, v_size_3616_, v_k_3617_, v_v_3618_, v_l_3619_, v_r_3620_, v_x_3607_);
return v___x_3621_;
}
else
{
lean_object* v_size_3622_; lean_object* v_k_3623_; lean_object* v_v_3624_; lean_object* v_l_3625_; lean_object* v___x_3626_; 
lean_dec(v_h__3_3610_);
v_size_3622_ = lean_ctor_get(v_x_3606_, 0);
lean_inc(v_size_3622_);
v_k_3623_ = lean_ctor_get(v_x_3606_, 1);
lean_inc(v_k_3623_);
v_v_3624_ = lean_ctor_get(v_x_3606_, 2);
lean_inc(v_v_3624_);
v_l_3625_ = lean_ctor_get(v_x_3606_, 3);
lean_inc(v_l_3625_);
lean_dec_ref_known(v_x_3606_, 5);
v___x_3626_ = lean_apply_5(v_h__2_3609_, v_size_3622_, v_k_3623_, v_v_3624_, v_l_3625_, v_x_3607_);
return v___x_3626_;
}
}
else
{
lean_object* v___x_3627_; 
lean_dec(v_h__3_3610_);
lean_dec(v_h__2_3609_);
v___x_3627_ = lean_apply_1(v_h__1_3608_, v_x_3607_);
return v___x_3627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DTreeMap_Internal_Queries_0__Std_DTreeMap_Internal_Impl_Const_maxEntryD_match__1_splitter(lean_object* v_00_u03b1_3628_, lean_object* v_00_u03b2_3629_, lean_object* v_motive_3630_, lean_object* v_x_3631_, lean_object* v_x_3632_, lean_object* v_h__1_3633_, lean_object* v_h__2_3634_, lean_object* v_h__3_3635_){
_start:
{
if (lean_obj_tag(v_x_3631_) == 0)
{
lean_object* v_r_3636_; 
lean_dec(v_h__1_3633_);
v_r_3636_ = lean_ctor_get(v_x_3631_, 4);
if (lean_obj_tag(v_r_3636_) == 0)
{
lean_object* v_size_3637_; lean_object* v_k_3638_; lean_object* v_v_3639_; lean_object* v_l_3640_; lean_object* v_size_3641_; lean_object* v_k_3642_; lean_object* v_v_3643_; lean_object* v_l_3644_; lean_object* v_r_3645_; lean_object* v___x_3646_; 
lean_inc_ref(v_r_3636_);
lean_dec(v_h__2_3634_);
v_size_3637_ = lean_ctor_get(v_x_3631_, 0);
lean_inc(v_size_3637_);
v_k_3638_ = lean_ctor_get(v_x_3631_, 1);
lean_inc(v_k_3638_);
v_v_3639_ = lean_ctor_get(v_x_3631_, 2);
lean_inc(v_v_3639_);
v_l_3640_ = lean_ctor_get(v_x_3631_, 3);
lean_inc(v_l_3640_);
lean_dec_ref_known(v_x_3631_, 5);
v_size_3641_ = lean_ctor_get(v_r_3636_, 0);
lean_inc(v_size_3641_);
v_k_3642_ = lean_ctor_get(v_r_3636_, 1);
lean_inc(v_k_3642_);
v_v_3643_ = lean_ctor_get(v_r_3636_, 2);
lean_inc(v_v_3643_);
v_l_3644_ = lean_ctor_get(v_r_3636_, 3);
lean_inc(v_l_3644_);
v_r_3645_ = lean_ctor_get(v_r_3636_, 4);
lean_inc(v_r_3645_);
lean_dec_ref_known(v_r_3636_, 5);
v___x_3646_ = lean_apply_10(v_h__3_3635_, v_size_3637_, v_k_3638_, v_v_3639_, v_l_3640_, v_size_3641_, v_k_3642_, v_v_3643_, v_l_3644_, v_r_3645_, v_x_3632_);
return v___x_3646_;
}
else
{
lean_object* v_size_3647_; lean_object* v_k_3648_; lean_object* v_v_3649_; lean_object* v_l_3650_; lean_object* v___x_3651_; 
lean_dec(v_h__3_3635_);
v_size_3647_ = lean_ctor_get(v_x_3631_, 0);
lean_inc(v_size_3647_);
v_k_3648_ = lean_ctor_get(v_x_3631_, 1);
lean_inc(v_k_3648_);
v_v_3649_ = lean_ctor_get(v_x_3631_, 2);
lean_inc(v_v_3649_);
v_l_3650_ = lean_ctor_get(v_x_3631_, 3);
lean_inc(v_l_3650_);
lean_dec_ref_known(v_x_3631_, 5);
v___x_3651_ = lean_apply_5(v_h__2_3634_, v_size_3647_, v_k_3648_, v_v_3649_, v_l_3650_, v_x_3632_);
return v___x_3651_;
}
}
else
{
lean_object* v___x_3652_; 
lean_dec(v_h__3_3635_);
lean_dec(v_h__2_3634_);
v___x_3652_ = lean_apply_1(v_h__1_3633_, v_x_3632_);
return v___x_3652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(lean_object* v_x_3653_, lean_object* v_x_3654_){
_start:
{
lean_object* v_k_3655_; lean_object* v_v_3656_; lean_object* v_l_3657_; lean_object* v_r_3658_; lean_object* v___y_3660_; lean_object* v___y_3666_; 
v_k_3655_ = lean_ctor_get(v_x_3653_, 1);
v_v_3656_ = lean_ctor_get(v_x_3653_, 2);
v_l_3657_ = lean_ctor_get(v_x_3653_, 3);
v_r_3658_ = lean_ctor_get(v_x_3653_, 4);
if (lean_obj_tag(v_l_3657_) == 0)
{
lean_object* v_size_3673_; 
v_size_3673_ = lean_ctor_get(v_l_3657_, 0);
v___y_3666_ = v_size_3673_;
goto v___jp_3665_;
}
else
{
lean_object* v___x_3674_; 
v___x_3674_ = lean_unsigned_to_nat(0u);
v___y_3666_ = v___x_3674_;
goto v___jp_3665_;
}
v___jp_3659_:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = lean_nat_sub(v_x_3654_, v___y_3660_);
lean_dec(v_x_3654_);
v___x_3662_ = lean_unsigned_to_nat(1u);
v___x_3663_ = lean_nat_sub(v___x_3661_, v___x_3662_);
lean_dec(v___x_3661_);
v_x_3653_ = v_r_3658_;
v_x_3654_ = v___x_3663_;
goto _start;
}
v___jp_3665_:
{
uint8_t v___x_3667_; 
v___x_3667_ = lean_nat_dec_lt(v_x_3654_, v___y_3666_);
if (v___x_3667_ == 0)
{
uint8_t v___x_3668_; 
v___x_3668_ = lean_nat_dec_eq(v_x_3654_, v___y_3666_);
if (v___x_3668_ == 0)
{
if (lean_obj_tag(v_l_3657_) == 0)
{
lean_object* v_size_3669_; 
v_size_3669_ = lean_ctor_get(v_l_3657_, 0);
v___y_3660_ = v_size_3669_;
goto v___jp_3659_;
}
else
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_unsigned_to_nat(0u);
v___y_3660_ = v___x_3670_;
goto v___jp_3659_;
}
}
else
{
lean_object* v___x_3671_; 
lean_dec(v_x_3654_);
lean_inc(v_v_3656_);
lean_inc(v_k_3655_);
v___x_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3671_, 0, v_k_3655_);
lean_ctor_set(v___x_3671_, 1, v_v_3656_);
return v___x_3671_;
}
}
else
{
v_x_3653_ = v_l_3657_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg___boxed(lean_object* v_x_3675_, lean_object* v_x_3676_){
_start:
{
lean_object* v_res_3677_; 
v_res_3677_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3675_, v_x_3676_);
lean_dec(v_x_3675_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(lean_object* v_00_u03b1_3678_, lean_object* v_00_u03b2_3679_, lean_object* v_x_3680_, lean_object* v_x_3681_, lean_object* v_x_3682_, lean_object* v_x_3683_){
_start:
{
lean_object* v___x_3684_; 
v___x_3684_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___redArg(v_x_3680_, v_x_3682_);
return v___x_3684_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx___boxed(lean_object* v_00_u03b1_3685_, lean_object* v_00_u03b2_3686_, lean_object* v_x_3687_, lean_object* v_x_3688_, lean_object* v_x_3689_, lean_object* v_x_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx(v_00_u03b1_3685_, v_00_u03b2_3686_, v_x_3687_, v_x_3688_, v_x_3689_, v_x_3690_);
lean_dec(v_x_3687_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(lean_object* v_x_3692_, lean_object* v_x_3693_){
_start:
{
if (lean_obj_tag(v_x_3692_) == 0)
{
lean_object* v_k_3694_; lean_object* v_v_3695_; lean_object* v_l_3696_; lean_object* v_r_3697_; lean_object* v___y_3699_; lean_object* v___y_3705_; 
v_k_3694_ = lean_ctor_get(v_x_3692_, 1);
v_v_3695_ = lean_ctor_get(v_x_3692_, 2);
v_l_3696_ = lean_ctor_get(v_x_3692_, 3);
v_r_3697_ = lean_ctor_get(v_x_3692_, 4);
if (lean_obj_tag(v_l_3696_) == 0)
{
lean_object* v_size_3713_; 
v_size_3713_ = lean_ctor_get(v_l_3696_, 0);
v___y_3705_ = v_size_3713_;
goto v___jp_3704_;
}
else
{
lean_object* v___x_3714_; 
v___x_3714_ = lean_unsigned_to_nat(0u);
v___y_3705_ = v___x_3714_;
goto v___jp_3704_;
}
v___jp_3698_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3700_ = lean_nat_sub(v_x_3693_, v___y_3699_);
lean_dec(v_x_3693_);
v___x_3701_ = lean_unsigned_to_nat(1u);
v___x_3702_ = lean_nat_sub(v___x_3700_, v___x_3701_);
lean_dec(v___x_3700_);
v_x_3692_ = v_r_3697_;
v_x_3693_ = v___x_3702_;
goto _start;
}
v___jp_3704_:
{
uint8_t v___x_3706_; 
v___x_3706_ = lean_nat_dec_lt(v_x_3693_, v___y_3705_);
if (v___x_3706_ == 0)
{
uint8_t v___x_3707_; 
v___x_3707_ = lean_nat_dec_eq(v_x_3693_, v___y_3705_);
if (v___x_3707_ == 0)
{
if (lean_obj_tag(v_l_3696_) == 0)
{
lean_object* v_size_3708_; 
v_size_3708_ = lean_ctor_get(v_l_3696_, 0);
v___y_3699_ = v_size_3708_;
goto v___jp_3698_;
}
else
{
lean_object* v___x_3709_; 
v___x_3709_ = lean_unsigned_to_nat(0u);
v___y_3699_ = v___x_3709_;
goto v___jp_3698_;
}
}
else
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
lean_dec(v_x_3693_);
lean_inc(v_v_3695_);
lean_inc(v_k_3694_);
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v_k_3694_);
lean_ctor_set(v___x_3710_, 1, v_v_3695_);
v___x_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
return v___x_3711_;
}
}
else
{
v_x_3692_ = v_l_3696_;
goto _start;
}
}
}
else
{
lean_object* v___x_3715_; 
lean_dec(v_x_3693_);
v___x_3715_ = lean_box(0);
return v___x_3715_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg___boxed(lean_object* v_x_3716_, lean_object* v_x_3717_){
_start:
{
lean_object* v_res_3718_; 
v_res_3718_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3716_, v_x_3717_);
lean_dec(v_x_3716_);
return v_res_3718_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(lean_object* v_00_u03b1_3719_, lean_object* v_00_u03b2_3720_, lean_object* v_x_3721_, lean_object* v_x_3722_){
_start:
{
lean_object* v___x_3723_; 
v___x_3723_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___redArg(v_x_3721_, v_x_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f___boxed(lean_object* v_00_u03b1_3724_, lean_object* v_00_u03b2_3725_, lean_object* v_x_3726_, lean_object* v_x_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x3f(v_00_u03b1_3724_, v_00_u03b2_3725_, v_x_3726_, v_x_3727_);
lean_dec(v_x_3726_);
return v_res_3728_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3730_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_entryAtIdx_x21___redArg___closed__1));
v___x_3731_ = lean_unsigned_to_nat(16u);
v___x_3732_ = lean_unsigned_to_nat(870u);
v___x_3733_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__0));
v___x_3734_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_get_x21___redArg___closed__0));
v___x_3735_ = l_mkPanicMessageWithDecl(v___x_3734_, v___x_3733_, v___x_3732_, v___x_3731_, v___x_3730_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(lean_object* v_inst_3736_, lean_object* v_x_3737_, lean_object* v_x_3738_){
_start:
{
if (lean_obj_tag(v_x_3737_) == 0)
{
lean_object* v_k_3739_; lean_object* v_v_3740_; lean_object* v_l_3741_; lean_object* v_r_3742_; lean_object* v___y_3744_; lean_object* v___y_3750_; 
v_k_3739_ = lean_ctor_get(v_x_3737_, 1);
v_v_3740_ = lean_ctor_get(v_x_3737_, 2);
v_l_3741_ = lean_ctor_get(v_x_3737_, 3);
v_r_3742_ = lean_ctor_get(v_x_3737_, 4);
if (lean_obj_tag(v_l_3741_) == 0)
{
lean_object* v_size_3757_; 
v_size_3757_ = lean_ctor_get(v_l_3741_, 0);
v___y_3750_ = v_size_3757_;
goto v___jp_3749_;
}
else
{
lean_object* v___x_3758_; 
v___x_3758_ = lean_unsigned_to_nat(0u);
v___y_3750_ = v___x_3758_;
goto v___jp_3749_;
}
v___jp_3743_:
{
lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v___x_3745_ = lean_nat_sub(v_x_3738_, v___y_3744_);
lean_dec(v_x_3738_);
v___x_3746_ = lean_unsigned_to_nat(1u);
v___x_3747_ = lean_nat_sub(v___x_3745_, v___x_3746_);
lean_dec(v___x_3745_);
v_x_3737_ = v_r_3742_;
v_x_3738_ = v___x_3747_;
goto _start;
}
v___jp_3749_:
{
uint8_t v___x_3751_; 
v___x_3751_ = lean_nat_dec_lt(v_x_3738_, v___y_3750_);
if (v___x_3751_ == 0)
{
uint8_t v___x_3752_; 
v___x_3752_ = lean_nat_dec_eq(v_x_3738_, v___y_3750_);
if (v___x_3752_ == 0)
{
if (lean_obj_tag(v_l_3741_) == 0)
{
lean_object* v_size_3753_; 
v_size_3753_ = lean_ctor_get(v_l_3741_, 0);
v___y_3744_ = v_size_3753_;
goto v___jp_3743_;
}
else
{
lean_object* v___x_3754_; 
v___x_3754_ = lean_unsigned_to_nat(0u);
v___y_3744_ = v___x_3754_;
goto v___jp_3743_;
}
}
else
{
lean_object* v___x_3755_; 
lean_dec(v_x_3738_);
lean_inc(v_v_3740_);
lean_inc(v_k_3739_);
v___x_3755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3755_, 0, v_k_3739_);
lean_ctor_set(v___x_3755_, 1, v_v_3740_);
return v___x_3755_;
}
}
else
{
v_x_3737_ = v_l_3741_;
goto _start;
}
}
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_dec(v_x_3738_);
v___x_3759_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1, &l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1_once, _init_l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___closed__1);
v___x_3760_ = l_panic___redArg(v_inst_3736_, v___x_3759_);
return v___x_3760_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg___boxed(lean_object* v_inst_3761_, lean_object* v_x_3762_, lean_object* v_x_3763_){
_start:
{
lean_object* v_res_3764_; 
v_res_3764_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3761_, v_x_3762_, v_x_3763_);
lean_dec(v_x_3762_);
lean_dec_ref(v_inst_3761_);
return v_res_3764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(lean_object* v_00_u03b1_3765_, lean_object* v_00_u03b2_3766_, lean_object* v_inst_3767_, lean_object* v_x_3768_, lean_object* v_x_3769_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___redArg(v_inst_3767_, v_x_3768_, v_x_3769_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21___boxed(lean_object* v_00_u03b1_3771_, lean_object* v_00_u03b2_3772_, lean_object* v_inst_3773_, lean_object* v_x_3774_, lean_object* v_x_3775_){
_start:
{
lean_object* v_res_3776_; 
v_res_3776_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdx_x21(v_00_u03b1_3771_, v_00_u03b2_3772_, v_inst_3773_, v_x_3774_, v_x_3775_);
lean_dec(v_x_3774_);
lean_dec_ref(v_inst_3773_);
return v_res_3776_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(lean_object* v_x_3777_, lean_object* v_x_3778_, lean_object* v_x_3779_){
_start:
{
if (lean_obj_tag(v_x_3777_) == 0)
{
lean_object* v_k_3780_; lean_object* v_v_3781_; lean_object* v_l_3782_; lean_object* v_r_3783_; lean_object* v___y_3785_; lean_object* v___y_3791_; 
v_k_3780_ = lean_ctor_get(v_x_3777_, 1);
v_v_3781_ = lean_ctor_get(v_x_3777_, 2);
v_l_3782_ = lean_ctor_get(v_x_3777_, 3);
v_r_3783_ = lean_ctor_get(v_x_3777_, 4);
if (lean_obj_tag(v_l_3782_) == 0)
{
lean_object* v_size_3798_; 
v_size_3798_ = lean_ctor_get(v_l_3782_, 0);
v___y_3791_ = v_size_3798_;
goto v___jp_3790_;
}
else
{
lean_object* v___x_3799_; 
v___x_3799_ = lean_unsigned_to_nat(0u);
v___y_3791_ = v___x_3799_;
goto v___jp_3790_;
}
v___jp_3784_:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3786_ = lean_nat_sub(v_x_3778_, v___y_3785_);
lean_dec(v_x_3778_);
v___x_3787_ = lean_unsigned_to_nat(1u);
v___x_3788_ = lean_nat_sub(v___x_3786_, v___x_3787_);
lean_dec(v___x_3786_);
v_x_3777_ = v_r_3783_;
v_x_3778_ = v___x_3788_;
goto _start;
}
v___jp_3790_:
{
uint8_t v___x_3792_; 
v___x_3792_ = lean_nat_dec_lt(v_x_3778_, v___y_3791_);
if (v___x_3792_ == 0)
{
uint8_t v___x_3793_; 
v___x_3793_ = lean_nat_dec_eq(v_x_3778_, v___y_3791_);
if (v___x_3793_ == 0)
{
if (lean_obj_tag(v_l_3782_) == 0)
{
lean_object* v_size_3794_; 
v_size_3794_ = lean_ctor_get(v_l_3782_, 0);
v___y_3785_ = v_size_3794_;
goto v___jp_3784_;
}
else
{
lean_object* v___x_3795_; 
v___x_3795_ = lean_unsigned_to_nat(0u);
v___y_3785_ = v___x_3795_;
goto v___jp_3784_;
}
}
else
{
lean_object* v___x_3796_; 
lean_dec(v_x_3778_);
lean_inc(v_v_3781_);
lean_inc(v_k_3780_);
v___x_3796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3796_, 0, v_k_3780_);
lean_ctor_set(v___x_3796_, 1, v_v_3781_);
return v___x_3796_;
}
}
else
{
v_x_3777_ = v_l_3782_;
goto _start;
}
}
}
else
{
lean_dec(v_x_3778_);
lean_inc_ref(v_x_3779_);
return v_x_3779_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg___boxed(lean_object* v_x_3800_, lean_object* v_x_3801_, lean_object* v_x_3802_){
_start:
{
lean_object* v_res_3803_; 
v_res_3803_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3800_, v_x_3801_, v_x_3802_);
lean_dec_ref(v_x_3802_);
lean_dec(v_x_3800_);
return v_res_3803_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(lean_object* v_00_u03b1_3804_, lean_object* v_00_u03b2_3805_, lean_object* v_x_3806_, lean_object* v_x_3807_, lean_object* v_x_3808_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___redArg(v_x_3806_, v_x_3807_, v_x_3808_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD___boxed(lean_object* v_00_u03b1_3810_, lean_object* v_00_u03b2_3811_, lean_object* v_x_3812_, lean_object* v_x_3813_, lean_object* v_x_3814_){
_start:
{
lean_object* v_res_3815_; 
v_res_3815_ = l_Std_DTreeMap_Internal_Impl_Const_entryAtIdxD(v_00_u03b1_3810_, v_00_u03b2_3811_, v_x_3812_, v_x_3813_, v_x_3814_);
lean_dec_ref(v_x_3814_);
lean_dec(v_x_3812_);
return v_res_3815_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(lean_object* v_inst_3816_, lean_object* v_k_3817_, lean_object* v_best_3818_, lean_object* v_a_3819_){
_start:
{
if (lean_obj_tag(v_a_3819_) == 0)
{
lean_object* v_k_3820_; lean_object* v_v_3821_; lean_object* v_l_3822_; lean_object* v_r_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_k_3820_ = lean_ctor_get(v_a_3819_, 1);
lean_inc_n(v_k_3820_, 2);
v_v_3821_ = lean_ctor_get(v_a_3819_, 2);
lean_inc(v_v_3821_);
v_l_3822_ = lean_ctor_get(v_a_3819_, 3);
lean_inc(v_l_3822_);
v_r_3823_ = lean_ctor_get(v_a_3819_, 4);
lean_inc(v_r_3823_);
lean_dec_ref_known(v_a_3819_, 5);
lean_inc_ref(v_inst_3816_);
lean_inc(v_k_3817_);
v___x_3824_ = lean_apply_2(v_inst_3816_, v_k_3817_, v_k_3820_);
v___x_3825_ = lean_unbox(v___x_3824_);
switch(v___x_3825_)
{
case 0:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
lean_dec(v_r_3823_);
lean_dec(v_best_3818_);
v___x_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3826_, 0, v_k_3820_);
lean_ctor_set(v___x_3826_, 1, v_v_3821_);
v___x_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
v_best_3818_ = v___x_3827_;
v_a_3819_ = v_l_3822_;
goto _start;
}
case 1:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; 
lean_dec(v_r_3823_);
lean_dec(v_l_3822_);
lean_dec(v_best_3818_);
lean_dec(v_k_3817_);
lean_dec_ref(v_inst_3816_);
v___x_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3829_, 0, v_k_3820_);
lean_ctor_set(v___x_3829_, 1, v_v_3821_);
v___x_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3830_, 0, v___x_3829_);
return v___x_3830_;
}
default: 
{
lean_dec(v_l_3822_);
lean_dec(v_v_3821_);
lean_dec(v_k_3820_);
v_a_3819_ = v_r_3823_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3817_);
lean_dec_ref(v_inst_3816_);
return v_best_3818_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go(lean_object* v_00_u03b1_3832_, lean_object* v_00_u03b2_3833_, lean_object* v_inst_3834_, lean_object* v_k_3835_, lean_object* v_best_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3834_, v_k_3835_, v_best_3836_, v_a_3837_);
return v___x_3838_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f___redArg(lean_object* v_inst_3839_, lean_object* v_k_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v___x_3842_; lean_object* v___x_3843_; 
v___x_3842_ = lean_box(0);
v___x_3843_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3839_, v_k_3840_, v___x_3842_, v_a_3841_);
return v___x_3843_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f(lean_object* v_00_u03b1_3844_, lean_object* v_00_u03b2_3845_, lean_object* v_inst_3846_, lean_object* v_k_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; 
v___x_3849_ = lean_box(0);
v___x_3850_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3846_, v_k_3847_, v___x_3849_, v_a_3848_);
return v___x_3850_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(lean_object* v_inst_3851_, lean_object* v_k_3852_, lean_object* v_best_3853_, lean_object* v_a_3854_){
_start:
{
if (lean_obj_tag(v_a_3854_) == 0)
{
lean_object* v_k_3855_; lean_object* v_v_3856_; lean_object* v_l_3857_; lean_object* v_r_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; 
v_k_3855_ = lean_ctor_get(v_a_3854_, 1);
lean_inc_n(v_k_3855_, 2);
v_v_3856_ = lean_ctor_get(v_a_3854_, 2);
lean_inc(v_v_3856_);
v_l_3857_ = lean_ctor_get(v_a_3854_, 3);
lean_inc(v_l_3857_);
v_r_3858_ = lean_ctor_get(v_a_3854_, 4);
lean_inc(v_r_3858_);
lean_dec_ref_known(v_a_3854_, 5);
lean_inc_ref(v_inst_3851_);
lean_inc(v_k_3852_);
v___x_3859_ = lean_apply_2(v_inst_3851_, v_k_3852_, v_k_3855_);
v___x_3860_ = lean_unbox(v___x_3859_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; lean_object* v___x_3862_; 
lean_dec(v_r_3858_);
lean_dec(v_best_3853_);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v_k_3855_);
lean_ctor_set(v___x_3861_, 1, v_v_3856_);
v___x_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3862_, 0, v___x_3861_);
v_best_3853_ = v___x_3862_;
v_a_3854_ = v_l_3857_;
goto _start;
}
else
{
lean_dec(v_l_3857_);
lean_dec(v_v_3856_);
lean_dec(v_k_3855_);
v_a_3854_ = v_r_3858_;
goto _start;
}
}
else
{
lean_dec(v_k_3852_);
lean_dec_ref(v_inst_3851_);
return v_best_3853_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go(lean_object* v_00_u03b1_3865_, lean_object* v_00_u03b2_3866_, lean_object* v_inst_3867_, lean_object* v_k_3868_, lean_object* v_best_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v___x_3871_; 
v___x_3871_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3867_, v_k_3868_, v_best_3869_, v_a_3870_);
return v___x_3871_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f___redArg(lean_object* v_inst_3872_, lean_object* v_k_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_box(0);
v___x_3876_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3872_, v_k_3873_, v___x_3875_, v_a_3874_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f(lean_object* v_00_u03b1_3877_, lean_object* v_00_u03b2_3878_, lean_object* v_inst_3879_, lean_object* v_k_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = lean_box(0);
v___x_3883_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3879_, v_k_3880_, v___x_3882_, v_a_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(lean_object* v_inst_3884_, lean_object* v_k_3885_, lean_object* v_best_3886_, lean_object* v_a_3887_){
_start:
{
if (lean_obj_tag(v_a_3887_) == 0)
{
lean_object* v_k_3888_; lean_object* v_v_3889_; lean_object* v_l_3890_; lean_object* v_r_3891_; lean_object* v___x_3892_; uint8_t v___x_3893_; 
v_k_3888_ = lean_ctor_get(v_a_3887_, 1);
lean_inc_n(v_k_3888_, 2);
v_v_3889_ = lean_ctor_get(v_a_3887_, 2);
lean_inc(v_v_3889_);
v_l_3890_ = lean_ctor_get(v_a_3887_, 3);
lean_inc(v_l_3890_);
v_r_3891_ = lean_ctor_get(v_a_3887_, 4);
lean_inc(v_r_3891_);
lean_dec_ref_known(v_a_3887_, 5);
lean_inc_ref(v_inst_3884_);
lean_inc(v_k_3885_);
v___x_3892_ = lean_apply_2(v_inst_3884_, v_k_3885_, v_k_3888_);
v___x_3893_ = lean_unbox(v___x_3892_);
switch(v___x_3893_)
{
case 0:
{
lean_dec(v_r_3891_);
lean_dec(v_v_3889_);
lean_dec(v_k_3888_);
v_a_3887_ = v_l_3890_;
goto _start;
}
case 1:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
lean_dec(v_r_3891_);
lean_dec(v_l_3890_);
lean_dec(v_best_3886_);
lean_dec(v_k_3885_);
lean_dec_ref(v_inst_3884_);
v___x_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3895_, 0, v_k_3888_);
lean_ctor_set(v___x_3895_, 1, v_v_3889_);
v___x_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
return v___x_3896_;
}
default: 
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
lean_dec(v_l_3890_);
lean_dec(v_best_3886_);
v___x_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3897_, 0, v_k_3888_);
lean_ctor_set(v___x_3897_, 1, v_v_3889_);
v___x_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
v_best_3886_ = v___x_3898_;
v_a_3887_ = v_r_3891_;
goto _start;
}
}
}
else
{
lean_dec(v_k_3885_);
lean_dec_ref(v_inst_3884_);
return v_best_3886_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go(lean_object* v_00_u03b1_3900_, lean_object* v_00_u03b2_3901_, lean_object* v_inst_3902_, lean_object* v_k_3903_, lean_object* v_best_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3902_, v_k_3903_, v_best_3904_, v_a_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f___redArg(lean_object* v_inst_3907_, lean_object* v_k_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v___x_3910_; lean_object* v___x_3911_; 
v___x_3910_ = lean_box(0);
v___x_3911_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3907_, v_k_3908_, v___x_3910_, v_a_3909_);
return v___x_3911_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f(lean_object* v_00_u03b1_3912_, lean_object* v_00_u03b2_3913_, lean_object* v_inst_3914_, lean_object* v_k_3915_, lean_object* v_a_3916_){
_start:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3917_ = lean_box(0);
v___x_3918_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_3914_, v_k_3915_, v___x_3917_, v_a_3916_);
return v___x_3918_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(lean_object* v_inst_3919_, lean_object* v_k_3920_, lean_object* v_best_3921_, lean_object* v_a_3922_){
_start:
{
if (lean_obj_tag(v_a_3922_) == 0)
{
lean_object* v_k_3923_; lean_object* v_v_3924_; lean_object* v_l_3925_; lean_object* v_r_3926_; lean_object* v___x_3927_; uint8_t v___x_3928_; 
v_k_3923_ = lean_ctor_get(v_a_3922_, 1);
lean_inc_n(v_k_3923_, 2);
v_v_3924_ = lean_ctor_get(v_a_3922_, 2);
lean_inc(v_v_3924_);
v_l_3925_ = lean_ctor_get(v_a_3922_, 3);
lean_inc(v_l_3925_);
v_r_3926_ = lean_ctor_get(v_a_3922_, 4);
lean_inc(v_r_3926_);
lean_dec_ref_known(v_a_3922_, 5);
lean_inc_ref(v_inst_3919_);
lean_inc(v_k_3920_);
v___x_3927_ = lean_apply_2(v_inst_3919_, v_k_3920_, v_k_3923_);
v___x_3928_ = lean_unbox(v___x_3927_);
if (v___x_3928_ == 2)
{
lean_object* v___x_3929_; lean_object* v___x_3930_; 
lean_dec(v_l_3925_);
lean_dec(v_best_3921_);
v___x_3929_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3929_, 0, v_k_3923_);
lean_ctor_set(v___x_3929_, 1, v_v_3924_);
v___x_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3929_);
v_best_3921_ = v___x_3930_;
v_a_3922_ = v_r_3926_;
goto _start;
}
else
{
lean_dec(v_r_3926_);
lean_dec(v_v_3924_);
lean_dec(v_k_3923_);
v_a_3922_ = v_l_3925_;
goto _start;
}
}
else
{
lean_dec(v_k_3920_);
lean_dec_ref(v_inst_3919_);
return v_best_3921_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go(lean_object* v_00_u03b1_3933_, lean_object* v_00_u03b2_3934_, lean_object* v_inst_3935_, lean_object* v_k_3936_, lean_object* v_best_3937_, lean_object* v_a_3938_){
_start:
{
lean_object* v___x_3939_; 
v___x_3939_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3935_, v_k_3936_, v_best_3937_, v_a_3938_);
return v___x_3939_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f___redArg(lean_object* v_inst_3940_, lean_object* v_k_3941_, lean_object* v_a_3942_){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3943_ = lean_box(0);
v___x_3944_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3940_, v_k_3941_, v___x_3943_, v_a_3942_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f(lean_object* v_00_u03b1_3945_, lean_object* v_00_u03b2_3946_, lean_object* v_inst_3947_, lean_object* v_k_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
v___x_3950_ = lean_box(0);
v___x_3951_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_3947_, v_k_3948_, v___x_3950_, v_a_3949_);
return v___x_3951_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(lean_object* v_inst_3952_, lean_object* v_inst_3953_, lean_object* v_k_3954_, lean_object* v_t_3955_){
_start:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
v___x_3956_ = lean_box(0);
v___x_3957_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3952_, v_k_3954_, v___x_3956_, v_t_3955_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v___x_3958_; lean_object* v___x_3959_; 
v___x_3958_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3959_ = l_panic___redArg(v_inst_3953_, v___x_3958_);
return v___x_3959_;
}
else
{
lean_object* v_val_3960_; 
v_val_3960_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_val_3960_);
lean_dec_ref_known(v___x_3957_, 1);
return v_val_3960_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg___boxed(lean_object* v_inst_3961_, lean_object* v_inst_3962_, lean_object* v_k_3963_, lean_object* v_t_3964_){
_start:
{
lean_object* v_res_3965_; 
v_res_3965_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___redArg(v_inst_3961_, v_inst_3962_, v_k_3963_, v_t_3964_);
lean_dec_ref(v_inst_3962_);
return v_res_3965_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(lean_object* v_00_u03b1_3966_, lean_object* v_00_u03b2_3967_, lean_object* v_inst_3968_, lean_object* v_inst_3969_, lean_object* v_k_3970_, lean_object* v_t_3971_){
_start:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = lean_box(0);
v___x_3973_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_3968_, v_k_3970_, v___x_3972_, v_t_3971_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3975_ = l_panic___redArg(v_inst_3969_, v___x_3974_);
return v___x_3975_;
}
else
{
lean_object* v_val_3976_; 
v_val_3976_ = lean_ctor_get(v___x_3973_, 0);
lean_inc(v_val_3976_);
lean_dec_ref_known(v___x_3973_, 1);
return v_val_3976_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21___boxed(lean_object* v_00_u03b1_3977_, lean_object* v_00_u03b2_3978_, lean_object* v_inst_3979_, lean_object* v_inst_3980_, lean_object* v_k_3981_, lean_object* v_t_3982_){
_start:
{
lean_object* v_res_3983_; 
v_res_3983_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x21(v_00_u03b1_3977_, v_00_u03b2_3978_, v_inst_3979_, v_inst_3980_, v_k_3981_, v_t_3982_);
lean_dec_ref(v_inst_3980_);
return v_res_3983_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(lean_object* v_inst_3984_, lean_object* v_inst_3985_, lean_object* v_k_3986_, lean_object* v_t_3987_){
_start:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = lean_box(0);
v___x_3989_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_3984_, v_k_3986_, v___x_3988_, v_t_3987_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3990_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_3991_ = l_panic___redArg(v_inst_3985_, v___x_3990_);
return v___x_3991_;
}
else
{
lean_object* v_val_3992_; 
v_val_3992_ = lean_ctor_get(v___x_3989_, 0);
lean_inc(v_val_3992_);
lean_dec_ref_known(v___x_3989_, 1);
return v_val_3992_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg___boxed(lean_object* v_inst_3993_, lean_object* v_inst_3994_, lean_object* v_k_3995_, lean_object* v_t_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___redArg(v_inst_3993_, v_inst_3994_, v_k_3995_, v_t_3996_);
lean_dec_ref(v_inst_3994_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(lean_object* v_00_u03b1_3998_, lean_object* v_00_u03b2_3999_, lean_object* v_inst_4000_, lean_object* v_inst_4001_, lean_object* v_k_4002_, lean_object* v_t_4003_){
_start:
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = lean_box(0);
v___x_4005_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4000_, v_k_4002_, v___x_4004_, v_t_4003_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v___x_4006_; lean_object* v___x_4007_; 
v___x_4006_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4007_ = l_panic___redArg(v_inst_4001_, v___x_4006_);
return v___x_4007_;
}
else
{
lean_object* v_val_4008_; 
v_val_4008_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_val_4008_);
lean_dec_ref_known(v___x_4005_, 1);
return v_val_4008_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21___boxed(lean_object* v_00_u03b1_4009_, lean_object* v_00_u03b2_4010_, lean_object* v_inst_4011_, lean_object* v_inst_4012_, lean_object* v_k_4013_, lean_object* v_t_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x21(v_00_u03b1_4009_, v_00_u03b2_4010_, v_inst_4011_, v_inst_4012_, v_k_4013_, v_t_4014_);
lean_dec_ref(v_inst_4012_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(lean_object* v_inst_4016_, lean_object* v_inst_4017_, lean_object* v_k_4018_, lean_object* v_t_4019_){
_start:
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = lean_box(0);
v___x_4021_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4016_, v_k_4018_, v___x_4020_, v_t_4019_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4022_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4023_ = l_panic___redArg(v_inst_4017_, v___x_4022_);
return v___x_4023_;
}
else
{
lean_object* v_val_4024_; 
v_val_4024_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_val_4024_);
lean_dec_ref_known(v___x_4021_, 1);
return v_val_4024_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg___boxed(lean_object* v_inst_4025_, lean_object* v_inst_4026_, lean_object* v_k_4027_, lean_object* v_t_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___redArg(v_inst_4025_, v_inst_4026_, v_k_4027_, v_t_4028_);
lean_dec_ref(v_inst_4026_);
return v_res_4029_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(lean_object* v_00_u03b1_4030_, lean_object* v_00_u03b2_4031_, lean_object* v_inst_4032_, lean_object* v_inst_4033_, lean_object* v_k_4034_, lean_object* v_t_4035_){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = lean_box(0);
v___x_4037_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4032_, v_k_4034_, v___x_4036_, v_t_4035_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4039_ = l_panic___redArg(v_inst_4033_, v___x_4038_);
return v___x_4039_;
}
else
{
lean_object* v_val_4040_; 
v_val_4040_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_val_4040_);
lean_dec_ref_known(v___x_4037_, 1);
return v_val_4040_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21___boxed(lean_object* v_00_u03b1_4041_, lean_object* v_00_u03b2_4042_, lean_object* v_inst_4043_, lean_object* v_inst_4044_, lean_object* v_k_4045_, lean_object* v_t_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x21(v_00_u03b1_4041_, v_00_u03b2_4042_, v_inst_4043_, v_inst_4044_, v_k_4045_, v_t_4046_);
lean_dec_ref(v_inst_4044_);
return v_res_4047_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(lean_object* v_inst_4048_, lean_object* v_inst_4049_, lean_object* v_k_4050_, lean_object* v_t_4051_){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = lean_box(0);
v___x_4053_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4048_, v_k_4050_, v___x_4052_, v_t_4051_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4055_ = l_panic___redArg(v_inst_4049_, v___x_4054_);
return v___x_4055_;
}
else
{
lean_object* v_val_4056_; 
v_val_4056_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_val_4056_);
lean_dec_ref_known(v___x_4053_, 1);
return v_val_4056_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg___boxed(lean_object* v_inst_4057_, lean_object* v_inst_4058_, lean_object* v_k_4059_, lean_object* v_t_4060_){
_start:
{
lean_object* v_res_4061_; 
v_res_4061_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___redArg(v_inst_4057_, v_inst_4058_, v_k_4059_, v_t_4060_);
lean_dec_ref(v_inst_4058_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(lean_object* v_00_u03b1_4062_, lean_object* v_00_u03b2_4063_, lean_object* v_inst_4064_, lean_object* v_inst_4065_, lean_object* v_k_4066_, lean_object* v_t_4067_){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = lean_box(0);
v___x_4069_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4064_, v_k_4066_, v___x_4068_, v_t_4067_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3, &l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_getEntryGE_x21___redArg___closed__3);
v___x_4071_ = l_panic___redArg(v_inst_4065_, v___x_4070_);
return v___x_4071_;
}
else
{
lean_object* v_val_4072_; 
v_val_4072_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_val_4072_);
lean_dec_ref_known(v___x_4069_, 1);
return v_val_4072_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21___boxed(lean_object* v_00_u03b1_4073_, lean_object* v_00_u03b2_4074_, lean_object* v_inst_4075_, lean_object* v_inst_4076_, lean_object* v_k_4077_, lean_object* v_t_4078_){
_start:
{
lean_object* v_res_4079_; 
v_res_4079_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x21(v_00_u03b1_4073_, v_00_u03b2_4074_, v_inst_4075_, v_inst_4076_, v_k_4077_, v_t_4078_);
lean_dec_ref(v_inst_4076_);
return v_res_4079_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(lean_object* v_inst_4080_, lean_object* v_k_4081_, lean_object* v_t_4082_, lean_object* v_fallback_4083_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg___boxed(lean_object* v_inst_4087_, lean_object* v_k_4088_, lean_object* v_t_4089_, lean_object* v_fallback_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___redArg(v_inst_4087_, v_k_4088_, v_t_4089_, v_fallback_4090_);
lean_dec_ref(v_fallback_4090_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(lean_object* v_00_u03b1_4092_, lean_object* v_00_u03b2_4093_, lean_object* v_inst_4094_, lean_object* v_k_4095_, lean_object* v_t_4096_, lean_object* v_fallback_4097_){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; 
v___x_4098_ = lean_box(0);
v___x_4099_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4094_, v_k_4095_, v___x_4098_, v_t_4096_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGED___boxed(lean_object* v_00_u03b1_4101_, lean_object* v_00_u03b2_4102_, lean_object* v_inst_4103_, lean_object* v_k_4104_, lean_object* v_t_4105_, lean_object* v_fallback_4106_){
_start:
{
lean_object* v_res_4107_; 
v_res_4107_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGED(v_00_u03b1_4101_, v_00_u03b2_4102_, v_inst_4103_, v_k_4104_, v_t_4105_, v_fallback_4106_);
lean_dec_ref(v_fallback_4106_);
return v_res_4107_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(lean_object* v_inst_4108_, lean_object* v_k_4109_, lean_object* v_t_4110_, lean_object* v_fallback_4111_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg___boxed(lean_object* v_inst_4115_, lean_object* v_k_4116_, lean_object* v_t_4117_, lean_object* v_fallback_4118_){
_start:
{
lean_object* v_res_4119_; 
v_res_4119_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___redArg(v_inst_4115_, v_k_4116_, v_t_4117_, v_fallback_4118_);
lean_dec_ref(v_fallback_4118_);
return v_res_4119_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(lean_object* v_00_u03b1_4120_, lean_object* v_00_u03b2_4121_, lean_object* v_inst_4122_, lean_object* v_k_4123_, lean_object* v_t_4124_, lean_object* v_fallback_4125_){
_start:
{
lean_object* v___x_4126_; lean_object* v___x_4127_; 
v___x_4126_ = lean_box(0);
v___x_4127_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4122_, v_k_4123_, v___x_4126_, v_t_4124_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD___boxed(lean_object* v_00_u03b1_4129_, lean_object* v_00_u03b2_4130_, lean_object* v_inst_4131_, lean_object* v_k_4132_, lean_object* v_t_4133_, lean_object* v_fallback_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGTD(v_00_u03b1_4129_, v_00_u03b2_4130_, v_inst_4131_, v_k_4132_, v_t_4133_, v_fallback_4134_);
lean_dec_ref(v_fallback_4134_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(lean_object* v_inst_4136_, lean_object* v_k_4137_, lean_object* v_t_4138_, lean_object* v_fallback_4139_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg___boxed(lean_object* v_inst_4143_, lean_object* v_k_4144_, lean_object* v_t_4145_, lean_object* v_fallback_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___redArg(v_inst_4143_, v_k_4144_, v_t_4145_, v_fallback_4146_);
lean_dec_ref(v_fallback_4146_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(lean_object* v_00_u03b1_4148_, lean_object* v_00_u03b2_4149_, lean_object* v_inst_4150_, lean_object* v_k_4151_, lean_object* v_t_4152_, lean_object* v_fallback_4153_){
_start:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4154_ = lean_box(0);
v___x_4155_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4150_, v_k_4151_, v___x_4154_, v_t_4152_);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLED___boxed(lean_object* v_00_u03b1_4157_, lean_object* v_00_u03b2_4158_, lean_object* v_inst_4159_, lean_object* v_k_4160_, lean_object* v_t_4161_, lean_object* v_fallback_4162_){
_start:
{
lean_object* v_res_4163_; 
v_res_4163_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLED(v_00_u03b1_4157_, v_00_u03b2_4158_, v_inst_4159_, v_k_4160_, v_t_4161_, v_fallback_4162_);
lean_dec_ref(v_fallback_4162_);
return v_res_4163_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(lean_object* v_inst_4164_, lean_object* v_k_4165_, lean_object* v_t_4166_, lean_object* v_fallback_4167_){
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg___boxed(lean_object* v_inst_4171_, lean_object* v_k_4172_, lean_object* v_t_4173_, lean_object* v_fallback_4174_){
_start:
{
lean_object* v_res_4175_; 
v_res_4175_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___redArg(v_inst_4171_, v_k_4172_, v_t_4173_, v_fallback_4174_);
lean_dec_ref(v_fallback_4174_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(lean_object* v_00_u03b1_4176_, lean_object* v_00_u03b2_4177_, lean_object* v_inst_4178_, lean_object* v_k_4179_, lean_object* v_t_4180_, lean_object* v_fallback_4181_){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; 
v___x_4182_ = lean_box(0);
v___x_4183_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4178_, v_k_4179_, v___x_4182_, v_t_4180_);
if (lean_obj_tag(v___x_4183_) == 0)
{
lean_inc_ref(v_fallback_4181_);
return v_fallback_4181_;
}
else
{
lean_object* v_val_4184_; 
v_val_4184_ = lean_ctor_get(v___x_4183_, 0);
lean_inc(v_val_4184_);
lean_dec_ref_known(v___x_4183_, 1);
return v_val_4184_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD___boxed(lean_object* v_00_u03b1_4185_, lean_object* v_00_u03b2_4186_, lean_object* v_inst_4187_, lean_object* v_k_4188_, lean_object* v_t_4189_, lean_object* v_fallback_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLTD(v_00_u03b1_4185_, v_00_u03b2_4186_, v_inst_4187_, v_k_4188_, v_t_4189_, v_fallback_4190_);
lean_dec_ref(v_fallback_4190_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(lean_object* v_inst_4192_, lean_object* v_k_4193_, lean_object* v_x_4194_){
_start:
{
lean_object* v_k_4195_; lean_object* v_v_4196_; lean_object* v_l_4197_; lean_object* v_r_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; 
v_k_4195_ = lean_ctor_get(v_x_4194_, 1);
lean_inc_n(v_k_4195_, 2);
v_v_4196_ = lean_ctor_get(v_x_4194_, 2);
lean_inc(v_v_4196_);
v_l_4197_ = lean_ctor_get(v_x_4194_, 3);
lean_inc(v_l_4197_);
v_r_4198_ = lean_ctor_get(v_x_4194_, 4);
lean_inc(v_r_4198_);
lean_dec(v_x_4194_);
lean_inc_ref(v_inst_4192_);
lean_inc(v_k_4193_);
v___x_4199_ = lean_apply_2(v_inst_4192_, v_k_4193_, v_k_4195_);
v___x_4200_ = lean_unbox(v___x_4199_);
switch(v___x_4200_)
{
case 0:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
lean_dec(v_r_4198_);
v___x_4201_ = lean_box(0);
v___x_4202_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE_x3f_go___redArg(v_inst_4192_, v_k_4193_, v___x_4201_, v_l_4197_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v___x_4203_; 
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v_k_4195_);
lean_ctor_set(v___x_4203_, 1, v_v_4196_);
return v___x_4203_;
}
else
{
lean_object* v_val_4204_; 
lean_dec(v_v_4196_);
lean_dec(v_k_4195_);
v_val_4204_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_val_4204_);
lean_dec_ref_known(v___x_4202_, 1);
return v_val_4204_;
}
}
case 1:
{
lean_object* v___x_4205_; 
lean_dec(v_r_4198_);
lean_dec(v_l_4197_);
lean_dec(v_k_4193_);
lean_dec_ref(v_inst_4192_);
v___x_4205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4205_, 0, v_k_4195_);
lean_ctor_set(v___x_4205_, 1, v_v_4196_);
return v___x_4205_;
}
default: 
{
lean_dec(v_l_4197_);
lean_dec(v_v_4196_);
lean_dec(v_k_4195_);
v_x_4194_ = v_r_4198_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGE(lean_object* v_00_u03b1_4207_, lean_object* v_00_u03b2_4208_, lean_object* v_inst_4209_, lean_object* v_inst_4210_, lean_object* v_k_4211_, lean_object* v_x_4212_, lean_object* v_x_4213_, lean_object* v_x_4214_){
_start:
{
lean_object* v___x_4215_; 
v___x_4215_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGE___redArg(v_inst_4209_, v_k_4211_, v_x_4212_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(lean_object* v_inst_4216_, lean_object* v_k_4217_, lean_object* v_x_4218_){
_start:
{
lean_object* v_k_4219_; lean_object* v_v_4220_; lean_object* v_l_4221_; lean_object* v_r_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; 
v_k_4219_ = lean_ctor_get(v_x_4218_, 1);
lean_inc_n(v_k_4219_, 2);
v_v_4220_ = lean_ctor_get(v_x_4218_, 2);
lean_inc(v_v_4220_);
v_l_4221_ = lean_ctor_get(v_x_4218_, 3);
lean_inc(v_l_4221_);
v_r_4222_ = lean_ctor_get(v_x_4218_, 4);
lean_inc(v_r_4222_);
lean_dec(v_x_4218_);
lean_inc_ref(v_inst_4216_);
lean_inc(v_k_4217_);
v___x_4223_ = lean_apply_2(v_inst_4216_, v_k_4217_, v_k_4219_);
v___x_4224_ = lean_obj_tag_nat(v___x_4223_);
v___x_4225_ = lean_unsigned_to_nat(0u);
v___x_4226_ = lean_nat_dec_eq(v___x_4224_, v___x_4225_);
if (v___x_4226_ == 0)
{
lean_dec(v_l_4221_);
lean_dec(v_v_4220_);
lean_dec(v_k_4219_);
v_x_4218_ = v_r_4222_;
goto _start;
}
else
{
lean_object* v___x_4228_; lean_object* v___x_4229_; 
lean_dec(v_r_4222_);
v___x_4228_ = lean_box(0);
v___x_4229_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT_x3f_go___redArg(v_inst_4216_, v_k_4217_, v___x_4228_, v_l_4221_);
if (lean_obj_tag(v___x_4229_) == 0)
{
lean_object* v___x_4230_; 
v___x_4230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4230_, 0, v_k_4219_);
lean_ctor_set(v___x_4230_, 1, v_v_4220_);
return v___x_4230_;
}
else
{
lean_object* v_val_4231_; 
lean_dec(v_v_4220_);
lean_dec(v_k_4219_);
v_val_4231_ = lean_ctor_get(v___x_4229_, 0);
lean_inc(v_val_4231_);
lean_dec_ref_known(v___x_4229_, 1);
return v_val_4231_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryGT(lean_object* v_00_u03b1_4232_, lean_object* v_00_u03b2_4233_, lean_object* v_inst_4234_, lean_object* v_inst_4235_, lean_object* v_k_4236_, lean_object* v_x_4237_, lean_object* v_x_4238_, lean_object* v_x_4239_){
_start:
{
lean_object* v___x_4240_; 
v___x_4240_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryGT___redArg(v_inst_4234_, v_k_4236_, v_x_4237_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(lean_object* v_inst_4241_, lean_object* v_k_4242_, lean_object* v_x_4243_){
_start:
{
lean_object* v_k_4244_; lean_object* v_v_4245_; lean_object* v_l_4246_; lean_object* v_r_4247_; lean_object* v___x_4248_; uint8_t v___x_4249_; 
v_k_4244_ = lean_ctor_get(v_x_4243_, 1);
lean_inc_n(v_k_4244_, 2);
v_v_4245_ = lean_ctor_get(v_x_4243_, 2);
lean_inc(v_v_4245_);
v_l_4246_ = lean_ctor_get(v_x_4243_, 3);
lean_inc(v_l_4246_);
v_r_4247_ = lean_ctor_get(v_x_4243_, 4);
lean_inc(v_r_4247_);
lean_dec(v_x_4243_);
lean_inc_ref(v_inst_4241_);
lean_inc(v_k_4242_);
v___x_4248_ = lean_apply_2(v_inst_4241_, v_k_4242_, v_k_4244_);
v___x_4249_ = lean_unbox(v___x_4248_);
switch(v___x_4249_)
{
case 0:
{
lean_dec(v_r_4247_);
lean_dec(v_v_4245_);
lean_dec(v_k_4244_);
v_x_4243_ = v_l_4246_;
goto _start;
}
case 1:
{
lean_object* v___x_4251_; 
lean_dec(v_r_4247_);
lean_dec(v_l_4246_);
lean_dec(v_k_4242_);
lean_dec_ref(v_inst_4241_);
v___x_4251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4251_, 0, v_k_4244_);
lean_ctor_set(v___x_4251_, 1, v_v_4245_);
return v___x_4251_;
}
default: 
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
lean_dec(v_l_4246_);
v___x_4252_ = lean_box(0);
v___x_4253_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE_x3f_go___redArg(v_inst_4241_, v_k_4242_, v___x_4252_, v_r_4247_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v___x_4254_; 
v___x_4254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4254_, 0, v_k_4244_);
lean_ctor_set(v___x_4254_, 1, v_v_4245_);
return v___x_4254_;
}
else
{
lean_object* v_val_4255_; 
lean_dec(v_v_4245_);
lean_dec(v_k_4244_);
v_val_4255_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_val_4255_);
lean_dec_ref_known(v___x_4253_, 1);
return v_val_4255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLE(lean_object* v_00_u03b1_4256_, lean_object* v_00_u03b2_4257_, lean_object* v_inst_4258_, lean_object* v_inst_4259_, lean_object* v_k_4260_, lean_object* v_x_4261_, lean_object* v_x_4262_, lean_object* v_x_4263_){
_start:
{
lean_object* v___x_4264_; 
v___x_4264_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLE___redArg(v_inst_4258_, v_k_4260_, v_x_4261_);
return v___x_4264_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(lean_object* v_inst_4265_, lean_object* v_k_4266_, lean_object* v_x_4267_){
_start:
{
lean_object* v_k_4268_; lean_object* v_v_4269_; lean_object* v_l_4270_; lean_object* v_r_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; uint8_t v___x_4275_; 
v_k_4268_ = lean_ctor_get(v_x_4267_, 1);
lean_inc_n(v_k_4268_, 2);
v_v_4269_ = lean_ctor_get(v_x_4267_, 2);
lean_inc(v_v_4269_);
v_l_4270_ = lean_ctor_get(v_x_4267_, 3);
lean_inc(v_l_4270_);
v_r_4271_ = lean_ctor_get(v_x_4267_, 4);
lean_inc(v_r_4271_);
lean_dec(v_x_4267_);
lean_inc_ref(v_inst_4265_);
lean_inc(v_k_4266_);
v___x_4272_ = lean_apply_2(v_inst_4265_, v_k_4266_, v_k_4268_);
v___x_4273_ = lean_obj_tag_nat(v___x_4272_);
v___x_4274_ = lean_unsigned_to_nat(2u);
v___x_4275_ = lean_nat_dec_eq(v___x_4273_, v___x_4274_);
if (v___x_4275_ == 0)
{
lean_dec(v_r_4271_);
lean_dec(v_v_4269_);
lean_dec(v_k_4268_);
v_x_4267_ = v_l_4270_;
goto _start;
}
else
{
lean_object* v___x_4277_; lean_object* v___x_4278_; 
lean_dec(v_l_4270_);
v___x_4277_ = lean_box(0);
v___x_4278_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT_x3f_go___redArg(v_inst_4265_, v_k_4266_, v___x_4277_, v_r_4271_);
if (lean_obj_tag(v___x_4278_) == 0)
{
lean_object* v___x_4279_; 
v___x_4279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4279_, 0, v_k_4268_);
lean_ctor_set(v___x_4279_, 1, v_v_4269_);
return v___x_4279_;
}
else
{
lean_object* v_val_4280_; 
lean_dec(v_v_4269_);
lean_dec(v_k_4268_);
v_val_4280_ = lean_ctor_get(v___x_4278_, 0);
lean_inc(v_val_4280_);
lean_dec_ref_known(v___x_4278_, 1);
return v_val_4280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getEntryLT(lean_object* v_00_u03b1_4281_, lean_object* v_00_u03b2_4282_, lean_object* v_inst_4283_, lean_object* v_inst_4284_, lean_object* v_k_4285_, lean_object* v_x_4286_, lean_object* v_x_4287_, lean_object* v_x_4288_){
_start:
{
lean_object* v___x_4289_; 
v___x_4289_ = l_Std_DTreeMap_Internal_Impl_Const_getEntryLT___redArg(v_inst_4283_, v_k_4285_, v_x_4286_);
return v___x_4289_;
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
