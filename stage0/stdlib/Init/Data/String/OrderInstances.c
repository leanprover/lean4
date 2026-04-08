// Lean compiler output
// Module: Init.Data.String.OrderInstances
// Imports: public import Init.Data.String.Defs public import Init.Grind.ToInt public import Init.Data.Order.Classes import Init.Data.Order.PackageFactories import Init.Omega public import Init.Data.Order.PackageFactories
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
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Int_ofNat___boxed(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_instDecidableLeRaw___boxed(lean_object*, lean_object*);
lean_object* l_String_instDecidableLtRaw___boxed(lean_object*, lean_object*);
lean_object* l_Std_FactoryInstances_instOrdOfDecidableLE___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqRaw___boxed(lean_object*, lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_instDecidableLePos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_instDecidableEqPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_instDecidableLtPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_instDecidableLePos__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_instDecidableEqPos___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_String_instDecidableLtPos__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_String_Internal_tacticOrder___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_String_Internal_tacticOrder___closed__0 = (const lean_object*)&l_String_Internal_tacticOrder___closed__0_value;
static const lean_string_object l_String_Internal_tacticOrder___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_String_Internal_tacticOrder___closed__1 = (const lean_object*)&l_String_Internal_tacticOrder___closed__1_value;
static const lean_string_object l_String_Internal_tacticOrder___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tacticOrder"};
static const lean_object* l_String_Internal_tacticOrder___closed__2 = (const lean_object*)&l_String_Internal_tacticOrder___closed__2_value;
static const lean_ctor_object l_String_Internal_tacticOrder___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Internal_tacticOrder___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal_tacticOrder___closed__3_value_aux_0),((lean_object*)&l_String_Internal_tacticOrder___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 129, 74, 87, 236, 194, 167, 197)}};
static const lean_ctor_object l_String_Internal_tacticOrder___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal_tacticOrder___closed__3_value_aux_1),((lean_object*)&l_String_Internal_tacticOrder___closed__2_value),LEAN_SCALAR_PTR_LITERAL(241, 218, 229, 106, 179, 251, 249, 12)}};
static const lean_object* l_String_Internal_tacticOrder___closed__3 = (const lean_object*)&l_String_Internal_tacticOrder___closed__3_value;
static const lean_string_object l_String_Internal_tacticOrder___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "order"};
static const lean_object* l_String_Internal_tacticOrder___closed__4 = (const lean_object*)&l_String_Internal_tacticOrder___closed__4_value;
static const lean_ctor_object l_String_Internal_tacticOrder___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_String_Internal_tacticOrder___closed__4_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_String_Internal_tacticOrder___closed__5 = (const lean_object*)&l_String_Internal_tacticOrder___closed__5_value;
static const lean_ctor_object l_String_Internal_tacticOrder___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_String_Internal_tacticOrder___closed__3_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__5_value)}};
static const lean_object* l_String_Internal_tacticOrder___closed__6 = (const lean_object*)&l_String_Internal_tacticOrder___closed__6_value;
LEAN_EXPORT const lean_object* l_String_Internal_tacticOrder = (const lean_object*)&l_String_Internal_tacticOrder___closed__6_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeqBracketed"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__3 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__3_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(142, 80, 121, 250, 245, 54, 71, 145)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__5 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__5_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__6 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__6_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__7 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__7_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__8 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__8_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__10 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__10_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11_value;
static lean_once_cell_t l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__13 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__13_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__14 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__14_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Pos.Raw.lt_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__16 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__16_value;
static lean_once_cell_t l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Pos"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Raw"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "lt_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(6, 235, 182, 83, 236, 144, 113, 47)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(61, 22, 22, 180, 152, 141, 124, 220)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(22, 104, 170, 151, 29, 132, 183, 208)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 230, 80, 37, 136, 222, 125, 174)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(192, 160, 30, 114, 46, 165, 46, 109)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(127, 212, 0, 129, 78, 185, 20, 99)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__23 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__23_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__24 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__24_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__25 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__25_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Pos.Raw.le_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__26 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__26_value;
static lean_once_cell_t l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "le_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(6, 235, 182, 83, 236, 144, 113, 47)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(61, 22, 22, 180, 152, 141, 124, 220)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(197, 104, 48, 82, 230, 119, 117, 161)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 230, 80, 37, 136, 222, 125, 174)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(192, 160, 30, 114, 46, 165, 46, 109)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(124, 93, 1, 49, 222, 183, 184, 222)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__30_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__31 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__31_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__31_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__32 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__32_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "String.Pos.lt_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__33 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__33_value;
static lean_once_cell_t l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 230, 80, 37, 136, 222, 125, 174)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(188, 72, 8, 238, 89, 167, 244, 71)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__36 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__36_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__36_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__37 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__37_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "String.Pos.le_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__38 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__38_value;
static lean_once_cell_t l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 230, 80, 37, 136, 222, 125, 174)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(63, 229, 232, 27, 101, 214, 182, 89)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__41 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__41_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__41_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__42 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__42_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Slice.Pos.lt_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__43 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__43_value;
static lean_once_cell_t l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Slice"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(173, 4, 120, 222, 71, 205, 160, 113)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(216, 52, 85, 20, 23, 200, 218, 224)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(119, 222, 139, 215, 104, 127, 150, 22)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(84, 178, 198, 6, 19, 246, 168, 69)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(21, 101, 147, 105, 116, 117, 171, 195)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(206, 35, 44, 114, 210, 123, 55, 220)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__47_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__48 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__48_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__48_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__49 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__49_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Slice.Pos.le_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__50 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__50_value;
static lean_once_cell_t l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(173, 4, 120, 222, 71, 205, 160, 113)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(216, 52, 85, 20, 23, 200, 218, 224)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(36, 206, 195, 65, 19, 225, 88, 107)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(84, 178, 198, 6, 19, 246, 168, 69)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(21, 101, 147, 105, 116, 117, 171, 195)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(205, 125, 46, 185, 29, 165, 72, 167)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__53_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__54 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__54_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__54_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__55 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__55_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Pos.Raw.ext_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__56 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__56_value;
static lean_once_cell_t l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ext_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(6, 235, 182, 83, 236, 144, 113, 47)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(61, 22, 22, 180, 152, 141, 124, 220)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(67, 182, 123, 255, 102, 79, 234, 143)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 230, 80, 37, 136, 222, 125, 174)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(192, 160, 30, 114, 46, 165, 46, 109)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(82, 6, 239, 233, 154, 76, 228, 104)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__60_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__61 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__61_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__61_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__62 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__62_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "String.Pos.ext_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__63 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__63_value;
static lean_once_cell_t l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(207, 230, 80, 37, 136, 222, 125, 174)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(105, 140, 41, 144, 4, 105, 95, 120)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__66 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__66_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__66_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__67 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__67_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Slice.Pos.ext_iff"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__68 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__68_value;
static lean_once_cell_t l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(173, 4, 120, 222, 71, 205, 160, 113)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(216, 52, 85, 20, 23, 200, 218, 224)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(250, 206, 127, 208, 120, 178, 156, 46)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal_tacticOrder___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(84, 178, 198, 6, 19, 246, 168, 69)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(21, 101, 147, 105, 116, 117, 171, 195)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__58_value),LEAN_SCALAR_PTR_LITERAL(75, 203, 33, 166, 182, 189, 1, 233)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__71_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__72 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__72_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__72_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__73 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__73_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__74 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__74_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "location"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__75 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__75_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__75_value),LEAN_SCALAR_PTR_LITERAL(124, 82, 43, 228, 241, 102, 135, 24)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "at"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__77 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__77_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "locationWildcard"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__78 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__78_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__78_value),LEAN_SCALAR_PTR_LITERAL(134, 218, 71, 35, 220, 118, 132, 17)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__80 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__80_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__81 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__81_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__82_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "tacticTry_"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__82 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__82_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__82_value),LEAN_SCALAR_PTR_LITERAL(34, 109, 187, 155, 23, 130, 33, 152)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "try"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__84 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__84_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__85 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__85_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__85_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__87 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__87_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__87_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "omega"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__89 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__89_value;
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_0),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_1),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value_aux_2),((lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__89_value),LEAN_SCALAR_PTR_LITERAL(138, 49, 229, 237, 137, 52, 176, 206)}};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90_value;
static const lean_string_object l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__91 = (const lean_object*)&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__91_value;
LEAN_EXPORT lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_String_Pos_Raw_instToIntCiOfNatInt_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_ofNat___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
LEAN_EXPORT const lean_object* l_String_Pos_Raw_instToIntCiOfNatInt = (const lean_object*)&l_String_Pos_Raw_instToIntCiOfNatInt_value;
LEAN_EXPORT lean_object* l_String_Pos_Raw_instTransLe;
LEAN_EXPORT lean_object* l_String_Pos_Raw_instLinearOrderPackage___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_instLinearOrderPackage___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_instLinearOrderPackage___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_Raw_instLinearOrderPackage___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Pos_Raw_instLinearOrderPackage___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Pos_Raw_instLinearOrderPackage___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Pos_Raw_instLinearOrderPackage___closed__0 = (const lean_object*)&l_String_Pos_Raw_instLinearOrderPackage___closed__0_value;
static const lean_closure_object l_String_Pos_Raw_instLinearOrderPackage___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Pos_Raw_instLinearOrderPackage___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Pos_Raw_instLinearOrderPackage___closed__1 = (const lean_object*)&l_String_Pos_Raw_instLinearOrderPackage___closed__1_value;
static const lean_closure_object l_String_Pos_Raw_instLinearOrderPackage___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instDecidableLeRaw___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Pos_Raw_instLinearOrderPackage___closed__2 = (const lean_object*)&l_String_Pos_Raw_instLinearOrderPackage___closed__2_value;
static lean_once_cell_t l_String_Pos_Raw_instLinearOrderPackage___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Pos_Raw_instLinearOrderPackage___closed__3;
static const lean_closure_object l_String_Pos_Raw_instLinearOrderPackage___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_instDecidableLtRaw___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Pos_Raw_instLinearOrderPackage___closed__4 = (const lean_object*)&l_String_Pos_Raw_instLinearOrderPackage___closed__4_value;
static const lean_closure_object l_String_Pos_Raw_instLinearOrderPackage___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_FactoryInstances_instOrdOfDecidableLE___redArg___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_String_Pos_Raw_instLinearOrderPackage___closed__2_value)} };
static const lean_object* l_String_Pos_Raw_instLinearOrderPackage___closed__5 = (const lean_object*)&l_String_Pos_Raw_instLinearOrderPackage___closed__5_value;
static lean_once_cell_t l_String_Pos_Raw_instLinearOrderPackage___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Pos_Raw_instLinearOrderPackage___closed__6;
static lean_once_cell_t l_String_Pos_Raw_instLinearOrderPackage___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Pos_Raw_instLinearOrderPackage___closed__7;
static lean_once_cell_t l_String_Pos_Raw_instLinearOrderPackage___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Pos_Raw_instLinearOrderPackage___closed__8;
LEAN_EXPORT lean_object* l_String_Pos_Raw_instLinearOrderPackage;
LEAN_EXPORT lean_object* l_String_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instTransLe(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instTransLe___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Pos_instLinearOrderPackage(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instTransLe(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instTransLe___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_instLinearOrderPackage(lean_object*);
static lean_object* _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12(void){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Array_mkArray0(lean_box(0));
return v___x_42_;
}
}
static lean_object* _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_51_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__16));
v___x_52_ = l_String_toRawSubstring_x27(v___x_51_);
return v___x_52_;
}
}
static lean_object* _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27(void){
_start:
{
lean_object* v___x_73_; lean_object* v___x_74_; 
v___x_73_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__26));
v___x_74_ = l_String_toRawSubstring_x27(v___x_73_);
return v___x_74_;
}
}
static lean_object* _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__33));
v___x_93_ = l_String_toRawSubstring_x27(v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__38));
v___x_106_ = l_String_toRawSubstring_x27(v___x_105_);
return v___x_106_;
}
}
static lean_object* _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__43));
v___x_119_ = l_String_toRawSubstring_x27(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__50));
v___x_138_ = l_String_toRawSubstring_x27(v___x_137_);
return v___x_138_;
}
}
static lean_object* _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__56));
v___x_156_ = l_String_toRawSubstring_x27(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__63));
v___x_175_ = l_String_toRawSubstring_x27(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69(void){
_start:
{
lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_187_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__68));
v___x_188_ = l_String_toRawSubstring_x27(v___x_187_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1(lean_object* v_x_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = ((lean_object*)(l_String_Internal_tacticOrder___closed__3));
v___x_250_ = l_Lean_Syntax_isOfKind(v_x_246_, v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_251_ = lean_box(1);
v___x_252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v_a_248_);
return v___x_252_;
}
else
{
lean_object* v_quotContext_253_; lean_object* v_currMacroScope_254_; lean_object* v_ref_255_; uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v_quotContext_253_ = lean_ctor_get(v_a_247_, 1);
v_currMacroScope_254_ = lean_ctor_get(v_a_247_, 2);
v_ref_255_ = lean_ctor_get(v_a_247_, 5);
v___x_256_ = 0;
v___x_257_ = l_Lean_SourceInfo_fromRef(v_ref_255_, v___x_256_);
v___x_258_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__4));
v___x_259_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__5));
lean_inc_n(v___x_257_, 43);
v___x_260_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_257_);
lean_ctor_set(v___x_260_, 1, v___x_259_);
v___x_261_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__7));
v___x_262_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__8));
v___x_263_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__9));
v___x_264_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_257_);
lean_ctor_set(v___x_264_, 1, v___x_262_);
v___x_265_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__11));
v___x_266_ = lean_obj_once(&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12, &l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12_once, _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__12);
v___x_267_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_267_, 0, v___x_257_);
lean_ctor_set(v___x_267_, 1, v___x_261_);
lean_ctor_set(v___x_267_, 2, v___x_266_);
lean_inc_ref_n(v___x_267_, 20);
v___x_268_ = l_Lean_Syntax_node1(v___x_257_, v___x_265_, v___x_267_);
v___x_269_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__13));
v___x_270_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_270_, 0, v___x_257_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__15));
v___x_272_ = lean_obj_once(&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17, &l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17_once, _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__17);
v___x_273_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__21));
lean_inc_n(v_currMacroScope_254_, 9);
lean_inc_n(v_quotContext_253_, 9);
v___x_274_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_273_, v_currMacroScope_254_);
v___x_275_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__24));
v___x_276_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_276_, 0, v___x_257_);
lean_ctor_set(v___x_276_, 1, v___x_272_);
lean_ctor_set(v___x_276_, 2, v___x_274_);
lean_ctor_set(v___x_276_, 3, v___x_275_);
v___x_277_ = l_Lean_Syntax_node3(v___x_257_, v___x_271_, v___x_267_, v___x_267_, v___x_276_);
v___x_278_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__25));
v___x_279_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_257_);
lean_ctor_set(v___x_279_, 1, v___x_278_);
v___x_280_ = lean_obj_once(&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27, &l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27_once, _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__27);
v___x_281_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__29));
v___x_282_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_281_, v_currMacroScope_254_);
v___x_283_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__32));
v___x_284_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_284_, 0, v___x_257_);
lean_ctor_set(v___x_284_, 1, v___x_280_);
lean_ctor_set(v___x_284_, 2, v___x_282_);
lean_ctor_set(v___x_284_, 3, v___x_283_);
v___x_285_ = l_Lean_Syntax_node3(v___x_257_, v___x_271_, v___x_267_, v___x_267_, v___x_284_);
v___x_286_ = lean_obj_once(&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34, &l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34_once, _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__34);
v___x_287_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__35));
v___x_288_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_287_, v_currMacroScope_254_);
v___x_289_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__37));
v___x_290_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_290_, 0, v___x_257_);
lean_ctor_set(v___x_290_, 1, v___x_286_);
lean_ctor_set(v___x_290_, 2, v___x_288_);
lean_ctor_set(v___x_290_, 3, v___x_289_);
v___x_291_ = l_Lean_Syntax_node3(v___x_257_, v___x_271_, v___x_267_, v___x_267_, v___x_290_);
v___x_292_ = lean_obj_once(&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39, &l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39_once, _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__39);
v___x_293_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__40));
v___x_294_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_293_, v_currMacroScope_254_);
v___x_295_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__42));
v___x_296_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_296_, 0, v___x_257_);
lean_ctor_set(v___x_296_, 1, v___x_292_);
lean_ctor_set(v___x_296_, 2, v___x_294_);
lean_ctor_set(v___x_296_, 3, v___x_295_);
v___x_297_ = l_Lean_Syntax_node3(v___x_257_, v___x_271_, v___x_267_, v___x_267_, v___x_296_);
v___x_298_ = lean_obj_once(&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44, &l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44_once, _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__44);
v___x_299_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__46));
v___x_300_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_299_, v_currMacroScope_254_);
v___x_301_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__49));
v___x_302_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_302_, 0, v___x_257_);
lean_ctor_set(v___x_302_, 1, v___x_298_);
lean_ctor_set(v___x_302_, 2, v___x_300_);
lean_ctor_set(v___x_302_, 3, v___x_301_);
v___x_303_ = l_Lean_Syntax_node3(v___x_257_, v___x_271_, v___x_267_, v___x_267_, v___x_302_);
v___x_304_ = lean_obj_once(&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51, &l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51_once, _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__51);
v___x_305_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__52));
v___x_306_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_305_, v_currMacroScope_254_);
v___x_307_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__55));
v___x_308_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_308_, 0, v___x_257_);
lean_ctor_set(v___x_308_, 1, v___x_304_);
lean_ctor_set(v___x_308_, 2, v___x_306_);
lean_ctor_set(v___x_308_, 3, v___x_307_);
v___x_309_ = l_Lean_Syntax_node3(v___x_257_, v___x_271_, v___x_267_, v___x_267_, v___x_308_);
v___x_310_ = lean_obj_once(&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57, &l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57_once, _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__57);
v___x_311_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__59));
v___x_312_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_311_, v_currMacroScope_254_);
v___x_313_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__62));
v___x_314_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_314_, 0, v___x_257_);
lean_ctor_set(v___x_314_, 1, v___x_310_);
lean_ctor_set(v___x_314_, 2, v___x_312_);
lean_ctor_set(v___x_314_, 3, v___x_313_);
v___x_315_ = l_Lean_Syntax_node3(v___x_257_, v___x_271_, v___x_267_, v___x_267_, v___x_314_);
v___x_316_ = lean_obj_once(&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64, &l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64_once, _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__64);
v___x_317_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__65));
v___x_318_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_317_, v_currMacroScope_254_);
v___x_319_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__67));
v___x_320_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_320_, 0, v___x_257_);
lean_ctor_set(v___x_320_, 1, v___x_316_);
lean_ctor_set(v___x_320_, 2, v___x_318_);
lean_ctor_set(v___x_320_, 3, v___x_319_);
v___x_321_ = l_Lean_Syntax_node3(v___x_257_, v___x_271_, v___x_267_, v___x_267_, v___x_320_);
v___x_322_ = lean_obj_once(&l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69, &l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69_once, _init_l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__69);
v___x_323_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__70));
v___x_324_ = l_Lean_addMacroScope(v_quotContext_253_, v___x_323_, v_currMacroScope_254_);
v___x_325_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__73));
v___x_326_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_326_, 0, v___x_257_);
lean_ctor_set(v___x_326_, 1, v___x_322_);
lean_ctor_set(v___x_326_, 2, v___x_324_);
lean_ctor_set(v___x_326_, 3, v___x_325_);
v___x_327_ = l_Lean_Syntax_node3(v___x_257_, v___x_271_, v___x_267_, v___x_267_, v___x_326_);
v___x_328_ = lean_unsigned_to_nat(17u);
v___x_329_ = lean_mk_empty_array_with_capacity(v___x_328_);
v___x_330_ = lean_array_push(v___x_329_, v___x_277_);
lean_inc_ref_n(v___x_279_, 7);
v___x_331_ = lean_array_push(v___x_330_, v___x_279_);
v___x_332_ = lean_array_push(v___x_331_, v___x_285_);
v___x_333_ = lean_array_push(v___x_332_, v___x_279_);
v___x_334_ = lean_array_push(v___x_333_, v___x_291_);
v___x_335_ = lean_array_push(v___x_334_, v___x_279_);
v___x_336_ = lean_array_push(v___x_335_, v___x_297_);
v___x_337_ = lean_array_push(v___x_336_, v___x_279_);
v___x_338_ = lean_array_push(v___x_337_, v___x_303_);
v___x_339_ = lean_array_push(v___x_338_, v___x_279_);
v___x_340_ = lean_array_push(v___x_339_, v___x_309_);
v___x_341_ = lean_array_push(v___x_340_, v___x_279_);
v___x_342_ = lean_array_push(v___x_341_, v___x_315_);
v___x_343_ = lean_array_push(v___x_342_, v___x_279_);
v___x_344_ = lean_array_push(v___x_343_, v___x_321_);
v___x_345_ = lean_array_push(v___x_344_, v___x_279_);
v___x_346_ = lean_array_push(v___x_345_, v___x_327_);
v___x_347_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_347_, 0, v___x_257_);
lean_ctor_set(v___x_347_, 1, v___x_261_);
lean_ctor_set(v___x_347_, 2, v___x_346_);
v___x_348_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__74));
v___x_349_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_349_, 0, v___x_257_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
v___x_350_ = l_Lean_Syntax_node3(v___x_257_, v___x_261_, v___x_270_, v___x_347_, v___x_349_);
v___x_351_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__76));
v___x_352_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__77));
v___x_353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_257_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__79));
v___x_355_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__80));
v___x_356_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_356_, 0, v___x_257_);
lean_ctor_set(v___x_356_, 1, v___x_355_);
v___x_357_ = l_Lean_Syntax_node1(v___x_257_, v___x_354_, v___x_356_);
v___x_358_ = l_Lean_Syntax_node2(v___x_257_, v___x_351_, v___x_353_, v___x_357_);
v___x_359_ = l_Lean_Syntax_node1(v___x_257_, v___x_261_, v___x_358_);
lean_inc(v___x_268_);
v___x_360_ = l_Lean_Syntax_node6(v___x_257_, v___x_263_, v___x_264_, v___x_268_, v___x_267_, v___x_267_, v___x_350_, v___x_359_);
v___x_361_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__81));
v___x_362_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_362_, 0, v___x_257_);
lean_ctor_set(v___x_362_, 1, v___x_361_);
v___x_363_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__83));
v___x_364_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__84));
v___x_365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_257_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__86));
v___x_367_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__88));
v___x_368_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__89));
v___x_369_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__90));
v___x_370_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_257_);
lean_ctor_set(v___x_370_, 1, v___x_368_);
v___x_371_ = l_Lean_Syntax_node2(v___x_257_, v___x_369_, v___x_370_, v___x_268_);
v___x_372_ = l_Lean_Syntax_node1(v___x_257_, v___x_261_, v___x_371_);
v___x_373_ = l_Lean_Syntax_node1(v___x_257_, v___x_367_, v___x_372_);
v___x_374_ = l_Lean_Syntax_node1(v___x_257_, v___x_366_, v___x_373_);
v___x_375_ = l_Lean_Syntax_node2(v___x_257_, v___x_363_, v___x_365_, v___x_374_);
v___x_376_ = l_Lean_Syntax_node3(v___x_257_, v___x_261_, v___x_360_, v___x_362_, v___x_375_);
v___x_377_ = ((lean_object*)(l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___closed__91));
v___x_378_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_257_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = l_Lean_Syntax_node3(v___x_257_, v___x_258_, v___x_260_, v___x_376_, v___x_378_);
v___x_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_380_, 0, v___x_379_);
lean_ctor_set(v___x_380_, 1, v_a_248_);
return v___x_380_;
}
}
}
LEAN_EXPORT lean_object* l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1___boxed(lean_object* v_x_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_String_Internal___aux__Init__Data__String__OrderInstances______macroRules__String__Internal__tacticOrder__1(v_x_381_, v_a_382_, v_a_383_);
lean_dec_ref(v_a_382_);
return v_res_384_;
}
}
static lean_object* _init_l_String_Pos_Raw_instTransLe(void){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = lean_box(0);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_instLinearOrderPackage___lam__0(lean_object* v_a_387_, lean_object* v_b_388_){
_start:
{
uint8_t v___x_389_; 
v___x_389_ = lean_nat_dec_le(v_a_387_, v_b_388_);
if (v___x_389_ == 0)
{
lean_inc(v_b_388_);
return v_b_388_;
}
else
{
lean_inc(v_a_387_);
return v_a_387_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_instLinearOrderPackage___lam__0___boxed(lean_object* v_a_390_, lean_object* v_b_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_String_Pos_Raw_instLinearOrderPackage___lam__0(v_a_390_, v_b_391_);
lean_dec(v_b_391_);
lean_dec(v_a_390_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_instLinearOrderPackage___lam__1(lean_object* v_a_393_, lean_object* v_b_394_){
_start:
{
uint8_t v___x_395_; 
v___x_395_ = lean_nat_dec_le(v_b_394_, v_a_393_);
if (v___x_395_ == 0)
{
lean_inc(v_b_394_);
return v_b_394_;
}
else
{
lean_inc(v_a_393_);
return v_a_393_;
}
}
}
LEAN_EXPORT lean_object* l_String_Pos_Raw_instLinearOrderPackage___lam__1___boxed(lean_object* v_a_396_, lean_object* v_b_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_String_Pos_Raw_instLinearOrderPackage___lam__1(v_a_396_, v_b_397_);
lean_dec(v_b_397_);
lean_dec(v_a_396_);
return v_res_398_;
}
}
static lean_object* _init_l_String_Pos_Raw_instLinearOrderPackage___closed__3(void){
_start:
{
lean_object* v___x_402_; lean_object* v___f_403_; 
v___x_402_ = lean_alloc_closure((void*)(l_instDecidableEqRaw___boxed), 2, 0);
v___f_403_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_403_, 0, v___x_402_);
return v___f_403_;
}
}
static lean_object* _init_l_String_Pos_Raw_instLinearOrderPackage___closed__6(void){
_start:
{
lean_object* v___x_407_; lean_object* v_this_408_; lean_object* v___f_409_; lean_object* v_this_410_; lean_object* v_this_411_; lean_object* v___x_412_; 
v___x_407_ = ((lean_object*)(l_String_Pos_Raw_instLinearOrderPackage___closed__4));
v_this_408_ = ((lean_object*)(l_String_Pos_Raw_instLinearOrderPackage___closed__2));
v___f_409_ = lean_obj_once(&l_String_Pos_Raw_instLinearOrderPackage___closed__3, &l_String_Pos_Raw_instLinearOrderPackage___closed__3_once, _init_l_String_Pos_Raw_instLinearOrderPackage___closed__3);
v_this_410_ = lean_box(0);
v_this_411_ = lean_box(0);
v___x_412_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_412_, 0, v_this_411_);
lean_ctor_set(v___x_412_, 1, v_this_410_);
lean_ctor_set(v___x_412_, 2, v___f_409_);
lean_ctor_set(v___x_412_, 3, v_this_408_);
lean_ctor_set(v___x_412_, 4, v___x_407_);
return v___x_412_;
}
}
static lean_object* _init_l_String_Pos_Raw_instLinearOrderPackage___closed__7(void){
_start:
{
lean_object* v___f_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___f_413_ = ((lean_object*)(l_String_Pos_Raw_instLinearOrderPackage___closed__5));
v___x_414_ = lean_obj_once(&l_String_Pos_Raw_instLinearOrderPackage___closed__6, &l_String_Pos_Raw_instLinearOrderPackage___closed__6_once, _init_l_String_Pos_Raw_instLinearOrderPackage___closed__6);
v___x_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___f_413_);
return v___x_415_;
}
}
static lean_object* _init_l_String_Pos_Raw_instLinearOrderPackage___closed__8(void){
_start:
{
lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v___f_416_ = ((lean_object*)(l_String_Pos_Raw_instLinearOrderPackage___closed__1));
v___f_417_ = ((lean_object*)(l_String_Pos_Raw_instLinearOrderPackage___closed__0));
v___x_418_ = lean_obj_once(&l_String_Pos_Raw_instLinearOrderPackage___closed__7, &l_String_Pos_Raw_instLinearOrderPackage___closed__7_once, _init_l_String_Pos_Raw_instLinearOrderPackage___closed__7);
v___x_419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v___f_417_);
lean_ctor_set(v___x_419_, 2, v___f_416_);
return v___x_419_;
}
}
static lean_object* _init_l_String_Pos_Raw_instLinearOrderPackage(void){
_start:
{
lean_object* v___x_420_; 
v___x_420_ = lean_obj_once(&l_String_Pos_Raw_instLinearOrderPackage___closed__8, &l_String_Pos_Raw_instLinearOrderPackage___closed__8_once, _init_l_String_Pos_Raw_instLinearOrderPackage___closed__8);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize(lean_object* v_s_421_){
_start:
{
lean_object* v___f_422_; 
v___f_422_ = lean_alloc_closure((void*)(l_Int_ofNat___boxed), 1, 0);
return v___f_422_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize___boxed(lean_object* v_s_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_String_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize(v_s_423_);
lean_dec_ref(v_s_423_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instTransLe(lean_object* v_s_425_){
_start:
{
lean_object* v___x_426_; 
v___x_426_ = lean_box(0);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instTransLe___boxed(lean_object* v_s_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_String_Pos_instTransLe(v_s_427_);
lean_dec_ref(v_s_427_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_String_Pos_instLinearOrderPackage(lean_object* v_s_429_){
_start:
{
lean_object* v___f_430_; lean_object* v___f_431_; lean_object* v_this_432_; lean_object* v_this_433_; lean_object* v_this_434_; lean_object* v___x_435_; lean_object* v___f_436_; lean_object* v___x_437_; lean_object* v___f_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; 
v___f_430_ = ((lean_object*)(l_String_Pos_Raw_instLinearOrderPackage___closed__0));
v___f_431_ = ((lean_object*)(l_String_Pos_Raw_instLinearOrderPackage___closed__1));
v_this_432_ = lean_box(0);
lean_inc_ref_n(v_s_429_, 2);
v_this_433_ = lean_alloc_closure((void*)(l_String_instDecidableLePos___boxed), 3, 1);
lean_closure_set(v_this_433_, 0, v_s_429_);
v_this_434_ = lean_box(0);
v___x_435_ = lean_alloc_closure((void*)(l_String_instDecidableEqPos___boxed), 3, 1);
lean_closure_set(v___x_435_, 0, v_s_429_);
v___f_436_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_436_, 0, v___x_435_);
v___x_437_ = lean_alloc_closure((void*)(l_String_instDecidableLtPos___boxed), 3, 1);
lean_closure_set(v___x_437_, 0, v_s_429_);
lean_inc_ref(v_this_433_);
v___f_438_ = lean_alloc_closure((void*)(l_Std_FactoryInstances_instOrdOfDecidableLE___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_438_, 0, v_this_433_);
v___x_439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_439_, 0, v_this_432_);
lean_ctor_set(v___x_439_, 1, v_this_434_);
lean_ctor_set(v___x_439_, 2, v___f_436_);
lean_ctor_set(v___x_439_, 3, v_this_433_);
lean_ctor_set(v___x_439_, 4, v___x_437_);
v___x_440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___f_438_);
v___x_441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_441_, 0, v___x_440_);
lean_ctor_set(v___x_441_, 1, v___f_430_);
lean_ctor_set(v___x_441_, 2, v___f_431_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize(lean_object* v_s_442_){
_start:
{
lean_object* v___f_443_; 
v___f_443_ = lean_alloc_closure((void*)(l_Int_ofNat___boxed), 1, 0);
return v___f_443_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize___boxed(lean_object* v_s_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_String_Slice_Pos_instToIntCoOfNatIntHAddCastUtf8ByteSize(v_s_444_);
lean_dec_ref(v_s_444_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instTransLe(lean_object* v_s_446_){
_start:
{
lean_object* v___x_447_; 
v___x_447_ = lean_box(0);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instTransLe___boxed(lean_object* v_s_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_String_Slice_Pos_instTransLe(v_s_448_);
lean_dec_ref(v_s_448_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_instLinearOrderPackage(lean_object* v_s_450_){
_start:
{
lean_object* v___f_451_; lean_object* v___f_452_; lean_object* v_this_453_; lean_object* v_this_454_; lean_object* v_this_455_; lean_object* v___x_456_; lean_object* v___f_457_; lean_object* v___x_458_; lean_object* v___f_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___f_451_ = ((lean_object*)(l_String_Pos_Raw_instLinearOrderPackage___closed__0));
v___f_452_ = ((lean_object*)(l_String_Pos_Raw_instLinearOrderPackage___closed__1));
v_this_453_ = lean_box(0);
lean_inc_ref_n(v_s_450_, 2);
v_this_454_ = lean_alloc_closure((void*)(l_String_instDecidableLePos__1___boxed), 3, 1);
lean_closure_set(v_this_454_, 0, v_s_450_);
v_this_455_ = lean_box(0);
v___x_456_ = lean_alloc_closure((void*)(l_String_Slice_instDecidableEqPos___boxed), 3, 1);
lean_closure_set(v___x_456_, 0, v_s_450_);
v___f_457_ = lean_alloc_closure((void*)(l_instBEqOfDecidableEq___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_457_, 0, v___x_456_);
v___x_458_ = lean_alloc_closure((void*)(l_String_instDecidableLtPos__1___boxed), 3, 1);
lean_closure_set(v___x_458_, 0, v_s_450_);
lean_inc_ref(v_this_454_);
v___f_459_ = lean_alloc_closure((void*)(l_Std_FactoryInstances_instOrdOfDecidableLE___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_459_, 0, v_this_454_);
v___x_460_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_460_, 0, v_this_453_);
lean_ctor_set(v___x_460_, 1, v_this_455_);
lean_ctor_set(v___x_460_, 2, v___f_457_);
lean_ctor_set(v___x_460_, 3, v_this_454_);
lean_ctor_set(v___x_460_, 4, v___x_458_);
v___x_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v___f_459_);
v___x_462_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_462_, 0, v___x_461_);
lean_ctor_set(v___x_462_, 1, v___f_451_);
lean_ctor_set(v___x_462_, 2, v___f_452_);
return v___x_462_;
}
}
lean_object* runtime_initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_OrderInstances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_Pos_Raw_instTransLe = _init_l_String_Pos_Raw_instTransLe();
l_String_Pos_Raw_instLinearOrderPackage = _init_l_String_Pos_Raw_instLinearOrderPackage();
lean_mark_persistent(l_String_Pos_Raw_instLinearOrderPackage);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_OrderInstances(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Grind_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_Order_Classes(uint8_t builtin);
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Init_Data_Order_PackageFactories(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_Classes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Order_PackageFactories(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_OrderInstances(builtin);
}
#ifdef __cplusplus
}
#endif
